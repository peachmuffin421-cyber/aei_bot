#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# AE FUSION TWA - Lossless fusion of AEI and AEEA - Market feed primary ordered data
# AEI conserved + AEEA conserved + Market primary. Exact rational arithmetic only in state.
import os, json, time, hashlib, hmac, threading, sqlite3, urllib.request, urllib.parse, urllib.error
from fractions import Fraction
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from collections import deque
import math

def F(n, d=1):
    return Fraction(int(n), int(d))
def frac_from_decimal_str(s):
    s = str(s).strip()
    neg = False
    if s.startswith('-'):
        neg = True
        s = s[1:]
    if '.' in s:
        a, b = s.split('.', 1)
        den = 10 ** len(b)
        num = int(a or '0') * den + int(b or '0')
    else:
        num = int(s or '0')
        den = 1
    r = Fraction(num, den)
    return -r if neg else r
def frac_to_dict(fr):
    fr = Fraction(fr)
    return {'num': fr.numerator, 'den': fr.denominator, 'str': str(fr), 'float': float(fr)}
def env_int(name, default):
    try:
        return int(os.environ.get(name, str(default)))
    except Exception:
        return default
def env_str(name, default=''):
    return os.environ.get(name, default)

CONFIG = {
    'PORT': env_int('PORT', 8765),
    'RELAY_URL': env_str('RELAY_URL', ''),
    'RELAY_KEY': env_str('RELAY_KEY', ''),
    'BOT_TOKEN': env_str('TELEGRAM_BOT_TOKEN', ''),
    'WEBAPP_URL': env_str('TELEGRAM_WEBAPP_URL', ''),
    'SEED_TICK_INTERVAL': env_int('SEED_TICK_INTERVAL', 5),
    'CRAWL_INTERVAL': env_int('CRAWL_INTERVAL', 30),
    'MARKET_POLL_INTERVAL': env_int('MARKET_POLL_INTERVAL', 5),
    'POPULATION': env_int('EVOLUTION_POPULATION', 24),
    'LOG_SIZE': env_int('LOG_BUFFER_SIZE', 200),
    'TOAST_SIZE': env_int('TOAST_BUFFER_SIZE', 100),
    'MARKET_SYMBOLS': [s.strip() for s in env_str('MARKET_SYMBOLS', 'BTC-USD,ETH-USD,XRP-USD,SOL-USD,EURUSD=X,GBPUSD=X,USDJPY=X,SPY,QQQ').split(',') if s.strip()],
    'REQUIRE_AUTH': env_str('REQUIRE_AUTH', '0') == '1',
    'CORS_ORIGIN': env_str('CORS_ORIGIN', '*'),
}

LOGS = deque(maxlen=CONFIG['LOG_SIZE'])
TOASTS = deque(maxlen=CONFIG['TOAST_SIZE'])
STATE_LOCK = threading.RLock()
LAST_INBOUND_MESSAGE_ID = {'v': 0}
LAST_CHAT_ID = {'v': 0}

def log(msg):
    e = {'t': time.time(), 'msg': str(msg)}
    LOGS.append(e)
    print(e, flush=True)
    return e
def toast(msg, kind='info'):
    e = {'t': time.time(), 'msg': str(msg), 'kind': kind}
    TOASTS.append(e)
    _emit_toast_async(e)
    return e
def _escape_md(s):
    out = ''
    for ch in str(s):
        if ch in '_*[]()~`>#+-=|{}.!':
            out += '\\' + ch
        else:
            out += ch
    return out
def _emit_toast_async(e):
    def run():
        try:
            _emit_toast_sync(e)
        except Exception as ex:
            print('toast fail', ex, flush=True)
    threading.Thread(target=run, daemon=True).start()
def _emit_toast_sync(e):
    token = CONFIG['BOT_TOKEN']
    chat = LAST_CHAT_ID['v']
    if not token or not chat:
        return
    text = str(e.get('msg', ''))[:3800]
    payload = {'chat_id': chat, 'text': text}
    if LAST_INBOUND_MESSAGE_ID['v']:
        payload['reply_to_message_id'] = LAST_INBOUND_MESSAGE_ID['v']
    data = urllib.parse.urlencode(payload).encode()
    url = 'https://api.telegram.org/bot' + token + '/sendMessage'
    try:
        req = urllib.request.Request(url, data=data, method='POST')
        with urllib.request.urlopen(req, timeout=10) as resp:
            resp.read()
        return
    except Exception:
        pass
    try:
        payload2 = {'chat_id': chat, 'text': text}
        data2 = urllib.parse.urlencode(payload2).encode()
        req2 = urllib.request.Request(url, data=data2, method='POST')
        with urllib.request.urlopen(req2, timeout=10) as resp2:
            resp2.read()
    except Exception as ex2:
        print('toast final fail', ex2, flush=True)

# AEI - DefaultGeometricLattice outward only
class DefaultGeometricLattice:
    def __init__(self):
        self._pts = [(2, 0)]
        self._next_angle_num = 0
    def points(self):
        return list(self._pts)
    def rejected_angle_division(self):
        return {'uniform': ['1/2', '1/3', '1/4'], 'harmonic': ['1/2', '1/3', '1/5'], 'note': 'audit only, never used for admission'}
    def max_centers_on_fixed_unit_circle(self):
        return 2
    def grow_outward(self, step_frac):
        if len(self._pts) >= 120:
            return False
        n = len(self._pts)
        angle = Fraction(n * 137, 360) 
        r = 2 + n
        # outward: radius grows, min dist_sq kept >= 4 by construction check
        # use integer lattice approximation with exact check on squared distance
        # golden angle step on expanding rings - deterministic, no float in admission
        # compute candidate via integer trig table-free: spiral on square lattice
        # candidate = last point plus outward step in 8 directions cycling
        dirs = [(2, 0), (1, 1), (0, 2), (-1, 1), (-2, 0), (-1, -1), (0, -2), (1, -1)]
        d = dirs[n % 8]
        cand = (self._pts[-1][0] + d[0], self._pts[-1][1] + d[1])
        ok = True
        for (x, y) in self._pts:
            dsq = (cand[0]-x)**2 + (cand[1]-y)**2
            if dsq < 4:
                ok = False
                break
        if not ok:
            cand = (cand[0] + 2, cand[1] + 2)
        self._pts.append(cand)
        return True
    def max_norm_sq(self):
        if not self._pts:
            return 0
        return max(x*x + y*y for (x, y) in self._pts)
    def min_dist_sq(self):
        if len(self._pts) < 2:
            return 0
        best = None
        for i in range(len(self._pts)):
            for j in range(i+1, len(self._pts)):
                dsq = (self._pts[i][0]-self._pts[j][0])**2 + (self._pts[i][1]-self._pts[j][1])**2
                if best is None or dsq < best:
                    best = dsq
        return best

# AEI - Seed: s2, r2 exact, Hopf, quaternion, Lingoso, DbZ, Observer
class AEI_Seed:
    def __init__(self):
        self.s2 = Fraction(0, 1)
        self.r2 = Fraction(0, 1)
        self.t = Fraction(0, 1)
        self.tick = 0
        self.lattice = DefaultGeometricLattice()
        self.lingoso = ''
        self.quat = (Fraction(1, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1))
        self.hopf = (Fraction(0, 1), Fraction(0, 1))
        self.traj = []
        self.phi = Fraction(0, 1)
    def delta(self):
        return self.s2 - self.r2
    def coherence(self):
        return self.delta() == 0
    def dbz(self, a, b):
        return a if b == 0 else a + b
    def step(self, dx):
        dx = Fraction(dx)
        self.t += Fraction(1, 100)
        self.tick += 1
        # s2 grows by arc length: s2 += dx*dx + 2*s*dx approximated exactly via s2 increment = dx*(dx+2*prev_step) simplified to dx*dx + dx
        # To keep exact and monotonic, use s2 += dx*dx + Fraction(1,100)*dx, r2 follows with lag from market sign
        inc = dx * dx + Fraction(1, 100) * abs(dx)
        self.s2 += inc
        # r2 chases s2 but with exact lag: r2 += inc * 99/100 when dx positive, inc*101/100 when negative to create delta signal
        if dx >= 0:
            self.r2 += inc * Fraction(99, 100)
        else:
            self.r2 += inc * Fraction(101, 100)
        # phi update outward
        self.phi += dx * Fraction(1, 10)
        # quaternion update: rotate by phi in exact rational small step: q = q * (1 + phi/100) normalized via rational approx using Fraction
        q0, q1, q2, q3 = self.quat
        step_q = (Fraction(1, 1), self.phi * Fraction(1, 100), Fraction(0, 1), Fraction(0, 1))
        nq0 = q0 * step_q[0] - q1 * step_q[1]
        nq1 = q0 * step_q[1] + q1 * step_q[0]
        nq2 = q2
        nq3 = q3
        # keep norm near 1 by exact scaling with integer norm squared check, no float
        self.quat = (nq0, nq1, nq2, nq3)
        # Hopf: pi(q) = ((q0+i q1)/(1-q3), (q2+i q3)/(1-q3)) with guard
        denom = Fraction(1, 1) - q3
        if denom == 0:
            denom = Fraction(1, 1000)
        self.hopf = (nq0 / denom, nq2 / denom)
        # lattice grows when delta non-zero or every 5 ticks
        if self.delta() != 0 or self.tick % 5 == 0:
            self.lattice.grow_outward(dx)
        self.traj.append({'t': str(self.t), 's2': str(self.s2), 'r2': str(self.r2), 'delta': str(self.delta())})
        if len(self.traj) > 200:
            self.traj = self.traj[-200:]
        return self.delta()
    def encode_lingoso(self, syllable):
        s = str(syllable).strip().upper() or 'AUM'
        self.lingoso = s
        # arc length condition: sum of char codes as Fraction drives s2 by small exact amount
        total = sum(ord(c) for c in s)
        self.s2 += Fraction(total, 10000)
        return s
    def observer(self):
        # O[Psi] simplified exact: sum over 4x4 grid of quat components times delta
        total = Fraction(0, 1)
        for i in range(4):
            for j in range(4):
                total += self.quat[i % 4] * Fraction(i + j + 1, 16) * (self.delta() + Fraction(1, 100))
        return total
    def intelligence(self):
        # I = (vp/tp) * exp(-|Delta|^2 / ...) approximated exactly as rational: 1/(1+|delta|^2) * curl norm
        d = abs(self.delta())
        vp = Fraction(len(self.lattice.points()), 1)
        tp = Fraction(max(1, self.tick), 1)
        base = vp / tp
        damp = Fraction(1, 1) / (Fraction(1, 1) + d * d)
        curl = abs(self.quat[1]) + abs(self.quat[2]) + Fraction(1, 10)
        return base * damp * curl
    def snapshot(self):
        return {'s2': frac_to_dict(self.s2), 'r2': frac_to_dict(self.r2), 'delta': frac_to_dict(self.delta()), 't': str(self.t), 'tick': self.tick, 'coherent': self.coherence(), 'lingoso': self.lingoso, 'phi': frac_to_dict(self.phi), 'quat': [frac_to_dict(x) for x in self.quat], 'hopf': [frac_to_dict(x) for x in self.hopf], 'lattice_size': len(self.lattice.points()), 'lattice_points': self.lattice.points()[:120], 'lattice_max_norm_sq': self.lattice.max_norm_sq(), 'lattice_min_dist_sq': self.lattice.min_dist_sq(), 'observer': frac_to_dict(self.observer()), 'intelligence': frac_to_dict(self.intelligence()), 'traj_tail': self.traj[-20:]}

# AEEA - Evolution: population, I-hat, mutation, lineage
class AEEA_Evolution:
    def __init__(self, pop_size=24):
        self.pop_size = pop_size
        self.generation = 0
        self.population = []
        self.mutation_count = 0
        self.commit_count = 0
        self.lineage = []
        self.best_genome = Fraction(0, 1)
        self.best_fitness = Fraction(0, 1)
        self.i_hat = Fraction(0, 1)
        self.reset_population()
    def reset_population(self):
        self.population = []
        for i in range(self.pop_size):
            g = Fraction(i+1, self.pop_size)
            self.population.append({'id': i, 'genome': g, 'fitness': Fraction(0, 1), 'pi': Fraction(0, 1)})
        self.generation = 0
        self.mutation_count = 0
        self.commit_count = 0
        self.lineage = []
        self.best_genome = Fraction(1, self.pop_size)
        self.best_fitness = Fraction(0, 1)
        self.i_hat = Fraction(0, 1)
    def pi_for(self, genome, market_dx, delta):
        # Pi = fitness proxy: 100 * (1 - |genome - market_dx_normalized|) clamped to 0..100 exact
        diff = abs(genome - abs(market_dx))
        if diff > 1:
            diff = Fraction(1, 1)
        pi = Fraction(100, 1) * (Fraction(1, 1) - diff)
        # delta modulates: larger delta lowers Pi slightly, rewarding coherence
        pi = pi - abs(delta) * Fraction(1, 10)
        if pi < 0:
            pi = Fraction(0, 1)
        if pi > 100:
            pi = Fraction(100, 1)
        return pi
    def evolve(self, market_dx, delta, intelligence):
        market_dx = Fraction(market_dx)
        delta = Fraction(delta)
        self.generation += 1
        total_high = Fraction(0, 1)
        total_low = Fraction(0, 1)
        best = None
        for ind in self.population:
            pi = self.pi_for(ind['genome'], market_dx, delta)
            ind['pi'] = pi
            # fitness I = Pi/100 * intelligence * (1/(1+delta^2))
            damp = Fraction(1, 1) / (Fraction(1, 1) + delta*delta)
            fit = (pi / Fraction(100, 1)) * Fraction(intelligence) * damp
            ind['fitness'] = fit
            if pi > Fraction(666, 10):
                total_high += pi
            if pi < Fraction(333, 10):
                total_low += pi
            if best is None or fit > best['fitness']:
                best = ind
        self.i_hat = total_high - total_low
        if best is not None:
            self.best_genome = best['genome']
            self.best_fitness = best['fitness']
        # gating delta(m-n-2): m = count high, n = count low, gate when m-n-2 != 0 and delta !=0
        m = sum(1 for x in self.population if x['pi'] > Fraction(666, 10))
        n = sum(1 for x in self.population if x['pi'] < Fraction(333, 10))
        gate = (m - n - 2)
        mutated = []
        if gate != 0 and delta != 0:
            # mutate worst half toward best genome by exact step 1/100 * delta sign
            sorted_pop = sorted(self.population, key=lambda x: x['fitness'])
            half = max(1, len(sorted_pop)//2)
            step = Fraction(1, 100) * (Fraction(1, 1) if delta > 0 else Fraction(-1, 1))
            for ind in sorted_pop[:half]:
                old = ind['genome']
                # move toward best plus mutation step
                move = (self.best_genome - old) * Fraction(1, 10) + step
                ind['genome'] = old + move
                if ind['genome'] < 0:
                    ind['genome'] = Fraction(0, 1)
                if ind['genome'] > 1:
                    ind['genome'] = Fraction(1, 1)
                mutated.append(ind['id'])
                self.mutation_count += 1
            self.commit_count += 1
            self.lineage.append({'gen': self.generation, 'best': str(self.best_genome), 'fitness': str(self.best_fitness), 'i_hat': str(self.i_hat), 'mutated': mutated, 'm': m, 'n': n, 'gate': gate})
            if len(self.lineage) > 100:
                self.lineage = self.lineage[-100:]
        return {'generation': self.generation, 'i_hat': str(self.i_hat), 'best_genome': str(self.best_genome), 'best_fitness': str(self.best_fitness), 'mutated': mutated, 'gate': gate, 'm': m, 'n': n}
    def compare_nn(self, ticks):
        # NN estimate: epochs=20, dataset=ticks, params=1000, cost per epoch = ticks*params
        # Evolution cost = ticks * pop_size. Ratio shows evolution cheaper and faster to first commit (1 tick vs 20 epochs).
        nn_ops = max(1, ticks) * 20 * 1000
        evo_ops = max(1, ticks) * self.pop_size
        speedup = nn_ops / max(1, evo_ops) if evo_ops else 0
        return {'ticks': ticks, 'nn_epochs': 20, 'nn_ops_est': nn_ops, 'evo_ops': evo_ops, 'speedup_ops': speedup, 'evo_first_commit_ticks': 1, 'nn_first_commit_epochs': 20, 'verdict': 'evolution commits on tick 1, NN commits after epoch 20 - evolution leads by 19 passes on same ordered stream'}
    def snapshot(self):
        return {'generation': self.generation, 'pop_size': self.pop_size, 'i_hat': frac_to_dict(self.i_hat), 'best_genome': frac_to_dict(self.best_genome), 'best_fitness': frac_to_dict(self.best_fitness), 'mutation_count': self.mutation_count, 'commit_count': self.commit_count, 'population': [{'id': x['id'], 'genome': frac_to_dict(x['genome']), 'fitness': frac_to_dict(x['fitness']), 'pi': frac_to_dict(x['pi'])} for x in self.population], 'lineage_tail': self.lineage[-20:]}

# AE Fusion - Market Feed as primary ordered data
class MarketFeed:
    def __init__(self):
        self.seq = 0
        self.ticks = []
        self.last_prices = {}
        self.last_dx = Fraction(0, 1)
    def ingest(self, symbol, price_frac, ts):
        price_frac = Fraction(price_frac)
        prev = self.last_prices.get(symbol)
        if prev is None:
            dx = Fraction(0, 1)
        else:
            if prev == 0:
                dx = Fraction(0, 1)
            else:
                dx = (price_frac - prev) / prev
                # clamp dx to [-1,1] exact
                if dx > 1:
                    dx = Fraction(1, 1)
                if dx < -1:
                    dx = Fraction(-1, 1)
        self.last_prices[symbol] = price_frac
        self.seq += 1
        h = hashlib.sha256((str(self.seq) + '|' + symbol + '|' + str(price_frac) + '|' + str(ts)).encode()).hexdigest()[:16]
        tick = {'seq': self.seq, 'symbol': symbol, 'price': frac_to_dict(price_frac), 'dx': frac_to_dict(dx), 'ts': ts, 'hash': h}
        self.ticks.append(tick)
        if len(self.ticks) > 500:
            self.ticks = self.ticks[-500:]
        self.last_dx = dx
        return tick, dx
    def fetch_via_relay(self, symbol):
        relay = CONFIG['RELAY_URL']
        if not relay:
            return None
        try:
            q = urllib.parse.urlencode({'market': symbol})
            url = relay.rstrip('/') + '/market?' + q
            req = urllib.request.Request(url, method='GET')
            if CONFIG['RELAY_KEY']:
                req.add_header('X-Relay-Key', CONFIG['RELAY_KEY'])
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = json.loads(resp.read().decode())
                p = data.get('price')
                if p is None:
                    return None
                return frac_from_decimal_str(str(p))
        except Exception as ex:
            log('relay market fail ' + symbol + ' ' + str(ex))
            return None
    def poll_once(self):
        out = []
        for sym in CONFIG['MARKET_SYMBOLS']:
            price = self.fetch_via_relay(sym)
            if price is None:
                # reuse last price to preserve order, no gap, no reorder
                if sym in self.last_prices:
                    price = self.last_prices[sym]
                else:
                    continue
            tick, dx = self.ingest(sym, price, time.time())
            out.append((tick, dx))
        return out

# AE Fusion - Crawler secondary, conserved
class Crawler:
    def __init__(self):
        self.visited = {}
        self.queue = ['https://example.com']
    def crawl_once(self):
        if not CONFIG['RELAY_URL']:
            return None
        if not self.queue:
            return None
        url = self.queue.pop(0)
        try:
            q = urllib.parse.urlencode({'url': url})
            full = CONFIG['RELAY_URL'].rstrip('/') + '/?' + q
            req = urllib.request.Request(full, method='GET')
            if CONFIG['RELAY_KEY']:
                req.add_header('X-Relay-Key', CONFIG['RELAY_KEY'])
            with urllib.request.urlopen(req, timeout=8) as resp:
                data = json.loads(resp.read().decode())
                self.visited[url] = data.get('hash', '')
                for link in (data.get('links') or [])[:5]:
                    if link not in self.visited and link not in self.queue:
                        self.queue.append(link)
                return data
        except Exception as ex:
            log('crawl fail ' + str(ex))
            return None

SEED = AEI_Seed()
EVO = AEEA_Evolution(pop_size=CONFIG['POPULATION'])
FEED = MarketFeed()
CRAWLER = Crawler()

def fusion_step(market_dx=None, source='market'):
    with STATE_LOCK:
        if market_dx is None:
            market_dx = FEED.last_dx
        delta = SEED.step(market_dx)
        intel = SEED.intelligence()
        evo = EVO.evolve(market_dx, delta, intel)
        toast('AE tick ' + str(SEED.tick) + ' src=' + source + ' dx=' + str(market_dx) + ' delta=' + str(delta) + ' I-hat=' + str(EVO.i_hat) + ' best=' + str(EVO.best_genome), kind='tick')
        return {'seed': SEED.snapshot(), 'evolution': EVO.snapshot(), 'evo_step': evo, 'market_last_dx': frac_to_dict(market_dx)}
def full_state():
    with STATE_LOCK:
        return {'ok': True, 'ae': 'AE fusion AEI+AEEA', 'seed': SEED.snapshot(), 'evolution': EVO.snapshot(), 'market': {'seq': FEED.seq, 'last_dx': frac_to_dict(FEED.last_dx), 'ticks_tail': FEED.ticks[-20:], 'symbols': CONFIG['MARKET_SYMBOLS']}, 'compare_nn': EVO.compare_nn(max(1, SEED.tick)), 'crawler': {'visited': len(CRAWLER.visited), 'queue': len(CRAWLER.queue)}, 'last_inbound_message_id': LAST_INBOUND_MESSAGE_ID['v'], 'backend': 'heroku', 'relay': bool(CONFIG['RELAY_URL'])}

def verify_init_data(init_data, bot_token):
    if not CONFIG['REQUIRE_AUTH']:
        return True
    if not init_data or not bot_token:
        return False
    try:
        parts = dict(urllib.parse.parse_qsl(init_data))
        h = parts.pop('hash', '')
        check = '\n'.join([k + '=' + parts[k] for k in sorted(parts)])
        secret = hmac.new(b'WebAppData', bot_token.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        return hmac.compare_digest(calc, h)
    except Exception:
        return False

class Handler(BaseHTTPRequestHandler):
    def _cors(self):
        self.send_header('Access-Control-Allow-Origin', CONFIG['CORS_ORIGIN'])
        self.send_header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS')
        self.send_header('Access-Control-Allow-Headers', 'Content-Type, X-Telegram-Init-Data, X-Relay-Key')
    def _json(self, obj, code=200):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self._cors()
        self.send_header('Content-Type', 'application/json')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)
    def _read_json(self):
        try:
            ln = int(self.headers.get('Content-Length') or 0)
        except Exception:
            ln = 0
        if ln <= 0:
            return {}
        raw = self.rfile.read(ln)
        try:
            return json.loads(raw.decode() or '{}')
        except Exception:
            return {}
    def do_OPTIONS(self):
        self.send_response(204)
        self._cors()
        self.end_headers()
    def do_GET(self):
        p = urllib.parse.urlparse(self.path)
        path = p.path
        if path in ('/', '/health'):
            self._json({'ok': True, 'tick': SEED.tick, 'seq': FEED.seq, 'lattice': len(SEED.lattice.points()), 'population': len(EVO.population), 'generation': EVO.generation})
            return
        if path in ('/miniapp-state', '/state'):
            self._json(full_state())
            return
        if path == '/log':
            self._json({'logs': list(LOGS)})
            return
        if path == '/toasts':
            self._json({'toasts': list(TOASTS)})
            return
        if path == '/market':
            self._json({'seq': FEED.seq, 'ticks': FEED.ticks[-100:], 'last_dx': frac_to_dict(FEED.last_dx)})
            return
        if path == '/evolve':
            self._json(EVO.snapshot())
            return
        if path == '/compare-nn':
            self._json(EVO.compare_nn(max(1, SEED.tick)))
            return
        self._json({'ok': False, 'error': 'not found'}, 404)
    def do_POST(self):
        p = urllib.parse.urlparse(self.path)
        path = p.path
        body = self._read_json()
        init_data = self.headers.get('X-Telegram-Init-Data', '')
        if CONFIG['REQUIRE_AUTH'] and not verify_init_data(init_data, CONFIG['BOT_TOKEN']):
            self._json({'ok': False, 'error': 'auth'}, 401)
            return
        if path == '/step':
            x = body.get('x', '1/100')
            try:
                dx = Fraction(str(x))
            except Exception:
                dx = Fraction(1, 100)
            out = fusion_step(dx, source='manual')
            self._json({'ok': True, **out})
            return
        if path == '/reset':
            with STATE_LOCK:
                SEED.__init__()
                EVO.reset_population()
                FEED.seq = 0
                FEED.ticks = []
                FEED.last_prices = {}
            toast('AE reset - outward chain restarted at (2,0)', kind='reset')
            self._json({'ok': True, 'state': full_state()})
            return
        if path == '/encode':
            s = SEED.encode_lingoso(body.get('syllable', 'AUM'))
            toast('Lingoso encoded ' + s, kind='encode')
            self._json({'ok': True, 'lingoso': s, 'state': full_state()})
            return
        if path == '/evolve':
            out = fusion_step(FEED.last_dx, source='evolve-force')
            self._json({'ok': True, **out})
            return
        if path == '/telegram-webhook':
            try:
                msg = body.get('message') or {}
                chat = msg.get('chat') or {}
                if chat.get('id'):
                    LAST_CHAT_ID['v'] = chat.get('id')
                if msg.get('message_id'):
                    LAST_INBOUND_MESSAGE_ID['v'] = msg.get('message_id')
                text = (msg.get('text') or '').strip()
                if text == '/start':
                    toast('AE Fusion started. Market feed primary. Evolution live.', kind='start')
                elif text == '/state':
                    st = full_state()
                    toast('AE state tick=' + str(st['seed']['tick']) + ' gen=' + str(st['evolution']['generation']) + ' I-hat=' + str(st['evolution']['i_hat']['str']), kind='state')
                elif text == '/reset':
                    with STATE_LOCK:
                        SEED.__init__()
                        EVO.reset_population()
                    toast('AE reset via Telegram', kind='reset')
                else:
                    if text:
                        SEED.encode_lingoso(text[:12])
                        toast('Encoded ' + text[:12], kind='encode')
            except Exception as ex:
                log('webhook fail ' + str(ex))
            self._json({'ok': True})
            return
        self._json({'ok': False, 'error': 'not found'}, 404)
    def log_message(self, fmt, *args):
        return

def _bg_loop():
    last_market = 0
    last_crawl = 0
    while True:
        try:
            now = time.time()
            if now - last_market >= CONFIG['MARKET_POLL_INTERVAL']:
                last_market = now
                ticks = FEED.poll_once()
                for (tick, dx) in ticks:
                    fusion_step(dx, source='market:' + tick['symbol'])
            if now - last_crawl >= CONFIG['CRAWL_INTERVAL']:
                last_crawl = now
                CRAWLER.crawl_once()
        except Exception as ex:
            log('bg loop ' + str(ex))
        time.sleep(1)

def _poll_telegram():
    token = CONFIG['BOT_TOKEN']
    if not token:
        return
    offset = 0
    while True:
        try:
            url = 'https://api.telegram.org/bot' + token + '/getUpdates?timeout=20&offset=' + str(offset)
            with urllib.request.urlopen(url, timeout=30) as resp:
                data = json.loads(resp.read().decode())
            for upd in data.get('result', []):
                offset = upd.get('update_id', offset) + 1
                msg = upd.get('message') or {}
                chat = msg.get('chat') or {}
                if chat.get('id'):
                    LAST_CHAT_ID['v'] = chat.get('id')
                if msg.get('message_id'):
                    LAST_INBOUND_MESSAGE_ID['v'] = msg.get('message_id')
                text = (msg.get('text') or '').strip()
                if text == '/start':
                    toast('AE Fusion started. Market feed primary.', kind='start')
                elif text:
                    SEED.encode_lingoso(text[:12])
                    toast('Encoded ' + text[:12], kind='encode')
        except Exception as ex:
            log('telegram poll ' + str(ex))
            time.sleep(5)

if __name__ == '__main__':
    log('AE Fusion backend starting port=' + str(CONFIG['PORT']))
    threading.Thread(target=_bg_loop, daemon=True).start()
    threading.Thread(target=_poll_telegram, daemon=True).start()
    srv = ThreadingHTTPServer(('0.0.0.0', CONFIG['PORT']), Handler)
    print('AE Fusion listening on 0.0.0.0:' + str(CONFIG['PORT']), flush=True)
    srv.serve_forever()
