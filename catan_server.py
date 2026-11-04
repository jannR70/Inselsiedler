#!/usr/bin/env python3
"""Catan-Server: python catan_server.py [port]  ->  http://<deine-ip>:8000
Unterstützt mehrere Räume (Lobbies / Spiele gleichzeitig).
Liegt neben catan3d.html und liefert diese Datei auch aus. Keine Abhängigkeiten."""
import json, math, os, random, secrets, socket, sys, threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

RES = ["wood", "brick", "wool", "grain", "ore"]
TILES = ["wood"] * 4 + ["wool"] * 4 + ["grain"] * 4 + ["brick"] * 3 + ["ore"] * 3 + ["desert"]
NUMS = [2, 3, 3, 4, 4, 5, 5, 6, 6, 8, 8, 9, 9, 10, 10, 11, 11, 12]
COST = {"road": {"wood": 1, "brick": 1},
        "settlement": {"wood": 1, "brick": 1, "wool": 1, "grain": 1},
        "city": {"grain": 2, "ore": 3}}
COLORS = ["#e5484d", "#3b82f6", "#f5f5f5", "#f08a24"]
WIN = 10
lock = threading.Condition()

# ---------- Geometrie (Ecken und Kanten des Brettes) ----------
def geometry():
    V, vk, E, ek, th = [], {}, [], {}, []
    for q in range(-2, 3):
        for r in range(-2, 3):
            if abs(q + r) > 2:
                continue
            cx, cy = math.sqrt(3) * (q + r / 2), 1.5 * r
            ids = []
            for k in range(6):
                a = math.radians(60 * k - 30)
                p = (round(cx + math.cos(a), 3), round(cy + math.sin(a), 3))
                if p not in vk:
                    vk[p] = len(V); V.append(p)
                ids.append(vk[p])
            for k in range(6):
                e = tuple(sorted((ids[k], ids[(k + 1) % 6])))
                if e not in ek:
                    ek[e] = len(E); E.append(e)
            th.append((cx, cy, ids))
    return V, E, th

V, E, TH = geometry()
VADJ = {i: set() for i in range(len(V))}
for a, b in E:
    VADJ[a].add(b); VADJ[b].add(a)

# Dict von Raum-ID -> Spielzustand (G)
GAMES = {}

def create_game_state(room_id):
    for _ in range(500):
        types = TILES[:]; random.shuffle(types)
        nums = NUMS[:]; random.shuffle(nums); it = iter(nums)
        tn = [None if t == "desert" else next(it) for t in types]
        hot = lambda i: tn[i] in (6, 8)
        if not any(hot(i) and hot(j) for i in range(19) for j in range(i)
                   if len(set(TH[i][2]) & set(TH[j][2])) == 2):
            break
    return {
        "room_id": room_id,
        "phase": "lobby", "players": [], "vown": {}, "eown": {}, "cur": 0,
        "rolled": False, "dice": None, "need_robber": False, "stage": "settlement",
        "last": None, "setup_i": 0, "seq": [], "ver": 0, "winner": None,
        "log": ["Warte auf Spieler …"],
        "robber": types.index("desert"),
        "board": {"V": V, "E": E, "tiles": [{"type": types[i], "num": tn[i], "x": TH[i][0],
                 "y": TH[i][1], "v": TH[i][2]} for i in range(19)]}
    }

def get_open_game():
    for g in GAMES.values():
        if g["phase"] == "lobby" and len(g["players"]) < 4:
            return g
    new_id = f"Room-{len(GAMES) + 1}"
    g = create_game_state(new_id)
    GAMES[new_id] = g
    return g

def bump(g):
    g["ver"] += 1; lock.notify_all()

def say(g, m):
    g["log"].append(m); g["log"] = g["log"][-30:]

# ---------- Regeln ----------
def vp(g, pid):
    return sum(1 if t == "s" else 2 for (o, t) in g["vown"].values() if o == pid)

def cards(p):
    return sum(p["res"].values())

def afford(p, c):
    return all(p["res"][k] >= n for k, n in COST[c].items())

def pay(p, c):
    for k, n in COST[c].items():
        p["res"][k] -= n

def road_vertices(g, pid):
    s = set()
    for e, o in g["eown"].items():
        if o == pid:
            s |= set(E[e])
    return s

def settle_spots(g, pid):
    free = [v for v in range(len(V)) if v not in g["vown"] and not (VADJ[v] & g["vown"].keys())]
    if g["phase"] == "setup":
        return free
    mine = road_vertices(g, pid)
    return [v for v in free if v in mine]

def road_ok(g, pid, e):
    if e in g["eown"]:
        return False
    if g["phase"] == "setup":
        return g["last"] in E[e]
    mine = road_vertices(g, pid)
    for v in E[e]:
        o = g["vown"].get(v)
        if (o and o[0] == pid) or (o is None and v in mine):
            return True
    return False

def legal(g, pid):
    p = g["players"][pid]
    if g["phase"] == "setup" and pid == g["cur"]:
        if g["stage"] == "settlement":
            return {"settlement": settle_spots(g, pid)}
        return {"road": [e for e in range(len(E)) if road_ok(g, pid, e)]}
    if g["phase"] != "play" or pid != g["cur"] or not g["rolled"]:
        return {}
    if g["need_robber"]:
        return {"robber": [i for i in range(19) if i != g["robber"]]}
    return {
        "road": [e for e in range(len(E)) if road_ok(g, pid, e)] if afford(p, "road") else [],
        "settlement": settle_spots(g, pid) if afford(p, "settlement") else [],
        "city": [v for v, (o, t) in g["vown"].items() if o == pid and t == "s"] if afford(p, "city") else [],
    }

def hint(g, pid):
    if g["phase"] == "over":
        return f"{g['players'][g['winner']]['name']} hat gewonnen!"
    if pid != g["cur"]:
        return f"{g['players'][g['cur']]['name']} ist am Zug."
    if g["phase"] == "setup":
        return "Setze eine Siedlung." if g["stage"] == "settlement" else "Setze eine Straße an deine neue Siedlung."
    if not g["rolled"]:
        return "Du bist dran: würfle."
    if g["need_robber"]:
        return "Versetze den Räuber auf ein markiertes Feld."
    return "Baue, tausche oder beende deinen Zug."

def distribute(g, n):
    for i, t in enumerate(g["board"]["tiles"]):
        if t["num"] != n or i == g["robber"]:
            continue
        for v in t["v"]:
            o = g["vown"].get(v)
            if o:
                g["players"][o[0]]["res"][t["type"]] += 1 if o[1] == "s" else 2

def steal(g, pid):
    t = g["board"]["tiles"][g["robber"]]
    victims = {g["vown"][v][0] for v in t["v"] if v in g["vown"]} - {pid}
    victims = [x for x in victims if cards(g["players"][x]) > 0]
    if not victims:
        return
    x = random.choice(victims); hand = g["players"][x]
    k = random.choice([r for r in RES for _ in range(hand["res"][r])])
    hand["res"][k] -= 1; g["players"][pid]["res"][k] += 1
    say(g, f"{g['players'][pid]['name']} stiehlt eine Karte von {hand['name']}.")

def start(g):
    n = len(g["players"])
    g.update(phase="setup", seq=list(range(n)) + list(range(n))[::-1], setup_i=0, stage="settlement")
    g["cur"] = g["seq"][0]
    say(g, "Das Spiel beginnt. Reihum je zwei Siedlungen mit Straße.")

def act(g, pid, a):
    t = a.get("type"); p = g["players"][pid]
    if g["phase"] == "lobby":
        if t == "start" and pid == 0:
            return start(g)
        return "Nur der erste Spieler kann starten."
    if g["phase"] == "over" or pid != g["cur"]:
        return "Du bist nicht am Zug."
    i = a.get("id")
    if t in ("settlement", "road", "city", "robber"):
        if i not in legal(g, pid).get(t, []):
            return "Das geht dort nicht."
        setup = g["phase"] == "setup"
        if t == "settlement":
            if not setup: pay(p, t)
            g["vown"][i] = (pid, "s")
            if setup:
                g["last"] = i; g["stage"] = "road"
                if g["setup_i"] >= len(g["players"]):
                    for tile in g["board"]["tiles"]:
                        if i in tile["v"] and tile["type"] != "desert":
                            p["res"][tile["type"]] += 1
        elif t == "city":
            pay(p, t); g["vown"][i] = (pid, "c")
        elif t == "road":
            if not setup: pay(p, t)
            g["eown"][i] = pid
            if setup:
                g["setup_i"] += 1
                if g["setup_i"] >= len(g["seq"]):
                    g.update(phase="play", cur=0, rolled=False); say(g, "Die Aufbauphase ist vorbei.")
                else:
                    g["cur"] = g["seq"][g["setup_i"]]; g["stage"] = "settlement"
        else:
            g["robber"] = i; g["need_robber"] = False; steal(g, pid)
        if vp(g, pid) >= WIN:
            g.update(phase="over", winner=pid); say(g, f"{p['name']} gewinnt mit {vp(g, pid)} Punkten!")
    elif t == "roll":
        if g["phase"] != "play" or g["rolled"]:
            return "Du hast schon gewürfelt."
        d = [random.randint(1, 6), random.randint(1, 6)]; n = sum(d)
        g["dice"] = d; g["rolled"] = True; say(g, f"{p['name']} würfelt {n}.")
        if n == 7:
            for q in g["players"]:
                c = cards(q)
                if c > 7:
                    for _ in range(c // 2):
                        k = random.choice([r for r in RES for _ in range(q["res"][r])]); q["res"][k] -= 1
                    say(g, f"{q['name']} wirft {c // 2} Karten ab.")
            g["need_robber"] = True
        else:
            distribute(g, n)
    elif t == "end":
        if g["phase"] != "play" or not g["rolled"] or g["need_robber"]:
            return "Erst würfeln und den Räuber versetzen."
        g["cur"] = (g["cur"] + 1) % len(g["players"]); g["rolled"] = False
    elif t == "trade":
        give, get = a.get("give"), a.get("get")
        if g["phase"] != "play" or not g["rolled"] or g["need_robber"]:
            return "Jetzt nicht möglich."
        if give not in RES or get not in RES or give == get or p["res"][give] < 4:
            return "Du brauchst 4 gleiche Karten."
        p["res"][give] -= 4; p["res"][get] += 1; say(g, f"{p['name']} tauscht 4:1 mit der Bank.")
    else:
        return "Unbekannte Aktion."

def find_game_by_token(token):
    for g in GAMES.values():
        for i, p in enumerate(g["players"]):
            if p["token"] == token:
                return g, i
    return None, None

def snapshot(g, token):
    if not g:
        return {"error": "Raum nicht gefunden"}
    pid = next((i for i, p in enumerate(g["players"]) if p["token"] == token), None)
    d = {"ver": g["ver"], "phase": g["phase"], "me": pid, "board": g["board"], "robber": g["robber"],
         "cur": g["cur"], "rolled": g["rolled"], "need_robber": g["need_robber"], "dice": g["dice"],
         "win": WIN, "log": g["log"][-8:], "room_id": g["room_id"],
         "players": [{"name": p["name"], "color": p["color"], "vp": vp(g, i), "cards": cards(p)}
                     for i, p in enumerate(g["players"])],
         "vown": [{"v": v, "p": o[0], "t": o[1]} for v, o in g["vown"].items()],
         "eown": [{"e": e, "p": o} for e, o in g["eown"].items()]}
    if pid is not None:
        d["res"] = g["players"][pid]["res"]
        if g["phase"] in ("setup", "play"):
            d["legal"] = legal(g, pid); d["hint"] = hint(g, pid)
    return d

# ---------- HTTP ----------
class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass

    def send(self, code, body, ct="application/json"):
        b = body if isinstance(body, bytes) else json.dumps(body).encode()
        self.send_response(code); self.send_header("Content-Type", ct + "; charset=utf-8")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self):
        u = urlparse(self.path); q = parse_qs(u.query)
        if u.path == "/state":
            ver = int(q.get("v", ["-1"])[0]); tok = q.get("t", [""])[0]
            with lock:
                g, _ = find_game_by_token(tok)
                if not g:
                    return self.send(200, {"error": "Ungültiges Token oder Spiel nicht gefunden"})
                lock.wait_for(lambda: g["ver"] > ver, timeout=20)
                return self.send(200, snapshot(g, tok))
        f = os.path.join(os.path.dirname(os.path.abspath(__file__)), "catan3d.html")
        try:
            self.send(200, open(f, "rb").read(), "text/html")
        except OSError:
            self.send(404, b"catan3d.html fehlt neben catan_server.py", "text/plain")

    def do_POST(self):
        try:
            a = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")
        except ValueError:
            return self.send(400, {"error": "Ungültige Anfrage"})
        with lock:
            if self.path == "/join":
                name = str(a.get("name", "")).strip()[:16]
                if not name: return self.send(200, {"error": "Bitte einen Namen eingeben."})
                g = get_open_game()
                tok = secrets.token_hex(8)
                g["players"].append({"name": name, "token": tok, "color": COLORS[len(g["players"])],
                                     "res": {k: 0 for k in RES}})
                say(g, f"{name} ist beigetreten."); bump(g)
                return self.send(200, {"token": tok, "room_id": g["room_id"]})
            if self.path == "/act":
                tok = a.get("token")
                g, pid = find_game_by_token(tok)
                if g is None or pid is None: return self.send(200, {"error": "Unbekannter Spieler."})
                err = act(g, pid, a)
                if err: return self.send(200, {"error": err})
                bump(g)
                return self.send(200, {"ok": True})
        self.send(404, {"error": "?"})

def local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); s.connect(("8.8.8.8", 80))
        return s.getsockname()[0]
    except OSError:
        return "localhost"

if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    get_open_game()
    srv = ThreadingHTTPServer(("0.0.0.0", port), H); srv.daemon_threads = True
    print(f"Catan läuft mit Multi-Lobby System: http://localhost:{port} | im Netzwerk: http://{local_ip()}:{port}")
    try: srv.serve_forever()
    except KeyboardInterrupt: pass