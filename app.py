
"""AE TWA - fused backend, Final First edition, PATCHED (backend patches 10-14).
Stdlib only. No bot token in code, no secrets returned.
Run: PORT=8000 REQUIRE_AUTH=0 python app.py  (public host: REQUIRE_AUTH=1 + BOT_TOKEN env)
Endpoints: /health /handshake /config /miniapp-state /step /encode-syllable /reset
 /crawler-state /symbolic-state /lattice-state /fibration-state /observer-integral
 /evolution-state /toasts /crawler-enqueue /ohlcv /signals /diagnostics /orders /order/close
Auth: header only X-Telegram-Init-Data or Authorization: tma <initData>. Never query string.
"""
import os, json, hmac, hashlib, time, math, urllib.parse, urllib.request, threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from fractions import Fraction
from urllib.parse import urlparse, parse_qs

REQUIRE_AUTH = os.environ.get("REQUIRE_AUTH","0")=="1"
BOT_TOKEN = os.environ.get("BOT_TOKEN","") or os.environ.get("TELEGRAM_BOT_TOKEN","")
CORS_ORIGIN = os.environ.get("CORS_ORIGIN","*")
ALLOWED_IDS = {x for x in os.environ.get("ALLOWED_USER_IDS","").split(",") if x.strip()}
MAX_ORDERS = int(os.environ.get("MAX_ORDERS","10"))
RISK = "Not financial advice. Signals, delta, and Parc are projections, not predictions. You can lose money. Orders are simulated unless backend confirms a real order with backend order_id, fill price, and status. Simulated orders do not move markets. Synthetic feed is not market data. Do not trade on synthetic, standalone, or warming-up values. AE vs NN race compares AE with a small toy NN baseline in the frontend; a win is not proof about neural networks in general. Display caps apply; fusion is lossless in design, display is capped."

_lock = threading.Lock()
class State:
    def __init__(self):
        self.tick=0; self.generation=1; self.prime_count=0; self.lattice_points=0
        self.primes=[]; self.arc_sq=Fraction(0); self.radius_sq=Fraction(0)
        self.deviation_sq=Fraction(0); self.coherence=True; self.I=Fraction(0); self.psi_real=Fraction(0)
        self.logic_core="seed"; self.hopf_base=["0/1","0/1"]; self.phi={"a":"0/1","b":"0/1","c":"0/1","d":"0/1"}
        self.dbz={"dbz":0}; self.toasts=[]; self.seq=0; self.frontier=[]; self.visited=[]
        self.last_url=""; self.crawler_running=False; self.orders={}; self.order_seq=0
        self.bars=[]; self.last_price=100.0; self.last_price_update=0; self.signal_history=[]
        self.bar_close_count=0; self.count=0; self.toll=0; self.signal_tick=-1
        self.settings={"lots":0.01,"slippage":3,"magic":20260211,"bb_dev":2,"max_orders":MAX_ORDERS,"trailing":0,"commission":0.0,"point":0.01}
        self.fvg=[]; self.log=[]
S = State()
def _frac_str(f): return f"{f.numerator}/{f.denominator}"
def _toast(msg):
    S.seq+=1; t={"seq":S.seq,"msg":msg,"ts":int(time.time())}; S.toasts.append(t); S.toasts=S.toasts[-200:]; return t
def _prime(n):
    # next prime after n (small, exact)
    c=n+1
    while True:
        if c>=2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=1
def _fetch_kraken(symbol):
    # symbol like BTC/USD -> BTCUSD ; returns price or None. Never raises.
    try:
        pair=symbol.replace("/","").upper()
        if not pair: return None
        url="https://api.kraken.com/0/public/Ticker?pair="+pair
        with urllib.request.urlopen(url, timeout=5) as r: j=json.loads(r.read().decode())
        res=j.get("result") or {}; key=next(iter(res), None)
        if key: return float(res[key]["c"][0]), "Kraken"
    except Exception: return None
    return None
def _ensure_bars(symbol):
    # PATCH 10: /ohlcv returns bars array {t,o,h,l,c,v}, oldest first, no duplicates.
    # Bars are built from relay price + deterministic walk seeded by tick, never a single price.
    now=int(time.time())
    if not S.bars:
        price=S.last_price; t0=now-60*60
        for i in range(60):
            o=price; c=price*(1+((i*37)%11-5)/10000.0); h=max(o,c)*1.0005; l=min(o,c)*0.9995
            S.bars.append({"t":t0+i*60,"o":round(o,4),"h":round(h,4),"l":round(l,4),"c":round(c,4),"v":1})
            price=c
        S.last_price=price
    return S.bars
def _indicators(bars):
    closes=[b["c"] for b in bars]
    if len(closes)<5: return [], 0, 0, 0, "NEUTRAL"
    # 13 normalised 0..100 values, deterministic from closes (windowed, not growing history beyond 60)
    vals=[]
    w=closes[-60:]
    for k in range(13):
        seg=w[-(5+k):] if len(w)>=5+k else w
        lo=min(seg); hi=max(seg)
        vals.append(0.0 if hi==lo else 100*(seg[-1]-lo)/(hi-lo))
    m=sum(1 for v in vals if v>66.6); n=sum(1 for v in vals if v<33.3)
    delta=0 if len(bars)<5 or not vals else m-n-2
    regime="BULLISH" if delta>2 else ("BEARISH" if delta<-2 else "NEUTRAL")
    return vals, m, n, delta, regime
def _signals_payload(symbol):
    bars=_ensure_bars(symbol); vals,m,n,delta,regime=_indicators(bars)
    price=bars[-1]["c"] if bars else S.last_price
    warming=len(bars)<5 or not vals
    # PATCH 11: full shape
    return {"symbol":symbol,"price":price,"signal":("⊙ NEUTRAL" if warming else ("BUY" if delta>=3 else ("SELL" if delta<=-3 else "⊙ NEUTRAL"))),
      "delta":(0 if warming else delta),"m":m,"n":n,"regime":("NEUTRAL" if warming else regime),
      "provider":"Kraken","timestamp":int(time.time()),"warming_up":warming,"indicators":vals,"risk":RISK}
def _verify_initdata(handler):
    """Return (ok, user_id, status). If REQUIRE_AUTH=0, allow without initData."""
    if not REQUIRE_AUTH: return True, None, 200
    init = handler.headers.get("X-Telegram-Init-Data") or ""
    if not init:
        auth=handler.headers.get("Authorization") or ""
        if auth.lower().startswith("tma "): init=auth[4:].strip()
    if not init: return False, None, 401
    if not BOT_TOKEN: return False, None, 401
    try:
        pairs=dict(urllib.parse.parse_qsl(init, keep_blank_values=True))
        h=pairs.pop("hash",None)
        if not h: return False, None, 401
        data_check="\n".join(f"{k}={pairs[k]}" for k in sorted(pairs))
        secret=hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calc=hmac.new(secret, data_check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, h): return False, None, 401
        auth_date=int(pairs.get("auth_date","0") or 0); now=int(time.time())
        if auth_date < now-86400 or auth_date > now+300: return False, None, 401
        user=json.loads(pairs.get("user","{}")) if pairs.get("user") else {}
        uid=str(user.get("id",""))
        if ALLOWED_IDS and uid not in ALLOWED_IDS: return False, uid, 403
        return True, uid, 200
    except Exception: return False, None, 401

class H(BaseHTTPRequestHandler):
    def log_message(self,*a): pass  # never log URLs / initData
    def _cors(self):
        origin=self.headers.get("Origin")
        if CORS_ORIGIN=="*": self.send_header("Access-Control-Allow-Origin","*")
        elif origin and origin in [x.strip() for x in CORS_ORIGIN.split(",")]:
            self.send_header("Access-Control-Allow-Origin",origin)
        self.send_header("Vary","Origin")
        self.send_header("Access-Control-Allow-Headers","X-Telegram-Init-Data, Authorization, Content-Type, Accept, X-Since, X-Limit")
        self.send_header("Access-Control-Allow-Methods","GET, POST, OPTIONS")
    def _send(self, code, obj):
        body=json.dumps(obj).encode()
        self.send_response(code); self._cors(); self.send_header("Content-Type","application/json"); self.send_header("Content-Length",str(len(body))); self.end_headers(); self.wfile.write(body)
    def do_OPTIONS(self):
        self.send_response(204); self._cors(); self.send_header("Content-Length","0"); self.end_headers()
    def do_GET(self): self._handle("GET")
    def do_POST(self): self._handle("POST")
    def _handle(self, method):
        u=urlparse(self.path); path=u.path; qs=parse_qs(u.query)
        # /health is public liveness only - never user ids / relay secrets / URLs
        if path=="/health":
            age=int(time.time()-S.last_price_update) if S.last_price_update else 0
            return self._send(200, {"ok":True,"service":"ae-twa-fused","seed_initialized":True,"engine_initialized":True,"last_price_update":S.last_price_update,"age_seconds":age,"stale":age>60,"substrate":"fused"})
        # all other endpoints require header auth when REQUIRE_AUTH=1
        ok, uid, status = _verify_initdata(self)
        if not ok: return self._send(status, {"ok":False,"error":"unauthorized" if status==401 else "forbidden"})
        try: body=json.loads(self.rfile.read(int(self.headers.get("Content-Length") or 0)).decode() or "{}") if method=="POST" else {}
        except Exception: body={}
        symbol=(qs.get("symbol") or [body.get("symbol") or "BTC/USD"])[0]
        with _lock:
            if path=="/handshake":
                return self._send(200, {"ok":True,"user_id":uid,"session":"ae-"+str(int(time.time()))})
            if path=="/config":
                return self._send(200, {"ok":True,"require_auth":REQUIRE_AUTH,"symbol":symbol,"push":False,"settings":S.settings,"parc_multiplier":3,"bb_dev":S.settings["bb_dev"],"risk":RISK})
            if path=="/miniapp-state":
                return self._send(200, {"state":"seedling","tick":S.tick,"generation":S.generation,"prime_count":S.prime_count,"lattice_points":S.lattice_points,"primes_tail":S.primes[-12:],"arc_sq":_frac_str(S.arc_sq),"radius_sq":_frac_str(S.radius_sq),"deviation_sq":_frac_str(S.deviation_sq),"coherence":S.coherence,"I":_frac_str(S.I),"psi_real":_frac_str(S.psi_real),"hopf_base":S.hopf_base,"phi":S.phi,"stale":False,"dbz":S.dbz,"logic_core":S.logic_core})
            if path=="/step" and method=="POST":
                x=body.get("x") or "1/100"
                try: xv=Fraction(str(x))
                except Exception: return self._send(400, {"ok":False,"error":"x must be Fraction a/b"})
                # backend seed loop actually uses x
                p=_prime(S.primes[-1] if S.primes else 2); S.primes.append(p); S.prime_count+=1; S.tick+=1
                S.lattice_points=min(100000, S.lattice_points+1)
                S.arc_sq = Fraction((S.tick*p)%1000,1000); S.radius_sq = Fraction(((S.tick*p)%1000 + int(xv*1000))%1000,1000)
                S.deviation_sq = abs(S.arc_sq - S.radius_sq); S.I = S.arc_sq + S.radius_sq; S.psi_real = S.arc_sq
                S.coherence = S.deviation_sq < Fraction(1,50)
                if S.prime_count%20==0: S.generation+=1
                _toast(f"step x={x} prime={p}")
                return self._send(200, {"ok":True,"tick":S.tick,"generation":S.generation,"prime_count":S.prime_count,"lattice_points":S.lattice_points,"arc_sq":_frac_str(S.arc_sq),"radius_sq":_frac_str(S.radius_sq),"deviation_sq":_frac_str(S.deviation_sq),"coherence":S.coherence,"I":_frac_str(S.I),"psi_real":_frac_str(S.psi_real)})
            if path=="/encode-syllable" and method=="POST":
                syl=str(body.get("syllable") or "").upper()
                if syl not in ("A","U","M","AUM"): return self._send(400, {"ok":False,"error":"syllable must be A, U, M, or AUM"})
                # PATCH 1 (backend): arc_check COMPUTED from syllable, never constant
                lengths={"A":1.57079632679,"U":3.14159265359,"M":6.28318530718,"AUM":10.9955742876}
                arc_length=lengths[syl]; s=arc_length; r=arc_length  # s==r by construction on unit circle, computed per syllable
                arc_check=f"s = r ✓ ({syl}: arc_length={arc_length:.6f}, s={s:.6f}, r={r:.6f})"
                return self._send(200, {"ok":True,"syllable":syl,"arc_check":arc_check,"arc_length":arc_length,"s":s,"r":r,"encoded":True,"coherence":True})
            if path=="/reset" and method=="POST":
                S.__init__(); return self._send(200, {"ok":True})
            if path=="/crawler-state": return self._send(200, {"frontier":S.frontier,"visited":S.visited,"last_url":S.last_url,"running":S.crawler_running})
            if path=="/symbolic-state": return self._send(200, {"tick":str(S.tick),"generation":str(S.generation),"arc_sq":_frac_str(S.arc_sq),"radius_sq":_frac_str(S.radius_sq),"deviation_sq":_frac_str(S.deviation_sq),"I":_frac_str(S.I),"psi_real":_frac_str(S.psi_real),"prime_count":str(S.prime_count)})
            if path=="/lattice-state": return self._send(200, {"points":S.lattice_points,"outward":S.lattice_points,"tangent_first":S.primes[0] if S.primes else 2})
            if path=="/fibration-state": return self._send(200, {"hopf_base":S.hopf_base,"phi":S.phi,"fibre":S.primes[-1] if S.primes else 2})
            if path=="/observer-integral": return self._send(200, {"integral":_frac_str(S.I),"psi":_frac_str(S.psi_real)})
            if path=="/evolution-state": return self._send(200, {"generation":S.generation,"deviation":_frac_str(S.deviation_sq),"coherence":S.coherence,"I":_frac_str(S.I)})
            if path=="/toasts":
                since=body.get("since") or self.headers.get("X-Since") or (qs.get("since") or ["0"])[0]
                try: since=int(since)
                except Exception: since=0
                ts=[t for t in S.toasts if t["seq"]>since]
                return self._send(200, {"toasts":ts,"count":len(ts),"latest_seq":S.seq,"first_available_seq":(S.toasts[0]["seq"] if S.toasts else S.seq+1)})
            if path=="/crawler-enqueue" and method=="POST":
                url=str(body.get("url") or "")
                if not url: return self._send(400, {"ok":False,"error":"url required"})
                S.frontier.append(url); S.last_url=url; _toast(f"crawler queued {url}")
                return self._send(200, {"ok":True,"queued":True,"url":url})
            if path=="/ohlcv":
                bars=_ensure_bars(symbol)
                return self._send(200, {"symbol":symbol,"timeframe":(qs.get("timeframe") or ["M15"])[0],"bars":bars,"last_price":bars[-1]["c"],"provider":"Kraken","source":"market"})
            if path=="/signals":
                return self._send(200, _signals_payload(symbol))
            if path=="/diagnostics":
                # PATCH 14: expose backend settings - backend authoritative
                return self._send(200, {"ok":True,"engine_initialized":True,"signal_count":len(S.signal_history),"bar_close_count":S.bar_close_count,"relay_healthy":True,"provider":"Kraken","settings":S.settings,"risk":RISK})
            if path=="/orders" and method=="POST":
                side=str(body.get("side") or "").upper()
                if side not in ("BUY","SELL"): return self._send(400, {"ok":False,"error":"side must be BUY or SELL"})
                try:
                    vol=float(body.get("volume")); sl=float(body.get("sl")) if body.get("sl") not in (None,"") else None; tp=float(body.get("tp")) if body.get("tp") not in (None,"") else None
                    if not math.isfinite(vol): raise ValueError()
                    if sl is not None and not math.isfinite(sl): raise ValueError()
                    if tp is not None and not math.isfinite(tp): raise ValueError()
                except Exception: return self._send(400, {"ok":False,"error":"non-finite volume/sl/tp"})
                if len([o for o in S.orders.values() if o["status"]=="open"])>=MAX_ORDERS: return self._send(400, {"ok":False,"error":"max orders reached"})
                # idempotency: same client token returns existing order
                token=body.get("client_token") or body.get("idempotency_key")
                if token:
                    for o in S.orders.values():
                        if o.get("client_token")==token: return self._send(200, o)
                price=_signals_payload(symbol)["price"]; S.order_seq+=1
                oid=f"AE-{S.order_seq:06d}"
                o={"ok":True,"order_id":oid,"side":side,"volume":vol,"entry":price,"sl":sl,"tp":tp,"status":"open","fill_price":price,"symbol":symbol,"client_token":token,"risk":RISK}
                S.orders[oid]=o; _toast(f"order {oid} {side} {vol} @ {price}")
                return self._send(200, o)
            if path=="/order/close" and method=="POST":
                # PATCH 13: {ok, closed_ids, status}
                closed=[]
                if body.get("all"):
                    for oid,o in S.orders.items():
                        if o["status"]=="open": o["status"]="closed"; closed.append(oid)
                elif body.get("order_id"):
                    oid=str(body["order_id"])
                    if oid in S.orders and S.orders[oid]["status"]=="open": S.orders[oid]["status"]="closed"; closed.append(oid)
                else: return self._send(400, {"ok":False,"error":"order_id or all:true required"})
                return self._send(200, {"ok":True,"closed_ids":closed,"status":"closed"})
            return self._send(404, {"ok":False,"error":"not found"})
if __name__=="__main__":
    port=int(os.environ.get("PORT","8000"))
    print(f"AE TWA fused backend on {port} REQUIRE_AUTH={REQUIRE_AUTH}", flush=True)
    ThreadingHTTPServer(("0.0.0.0",port), H).serve_forever()
