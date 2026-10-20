#!/usr/bin/env python3
"""Claude's check of the formulas and numbers stated in paper-A3-v5-en.tex.

Identities are checked as polynomials (tiny dict-based expansion, no sympy);
positivity claims (8),(10) by expanding after the stated substitution and
checking every coefficient is nonnegative with positive constant term.
Counts are recomputed from the two-stage rule.
"""
import csv
import random
import sys
from collections import defaultdict
from fractions import Fraction
from math import gcd, pi, sqrt
from pathlib import Path


class P:
    """Multivariate polynomial with rational coefficients."""
    def __init__(self, terms=None):
        self.t = {k: v for k, v in (terms or {}).items() if v != 0}

    @staticmethod
    def var(name):
        return P({((name, 1),): 1})

    @staticmethod
    def const(c):
        return P({(): Fraction(c)})

    @staticmethod
    def lift(x):
        return x if isinstance(x, P) else P.const(x)

    def __add__(self, o):
        o = P.lift(o); d = defaultdict(Fraction, self.t)
        for k, v in o.t.items():
            d[k] += v
        return P(d)
    __radd__ = __add__

    def __neg__(self):
        return P({k: -v for k, v in self.t.items()})

    def __sub__(self, o):
        return self + (-P.lift(o))

    def __rsub__(self, o):
        return P.lift(o) - self

    def __mul__(self, o):
        o = P.lift(o); d = defaultdict(Fraction)
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                e = defaultdict(int)
                for n, p in k1 + k2:
                    e[n] += p
                d[tuple(sorted(e.items()))] += v1 * v2
        return P(d)
    __rmul__ = __mul__

    def __pow__(self, n):
        r = P.const(1)
        for _ in range(n):
            r = r * self
        return r

    def is_zero(self):
        return not self.t

    def nonneg_coeffs_pos_const(self):
        return all(v >= 0 for v in self.t.values()) and self.t.get((), 0) > 0


V = P.var
results = []


def check(name, ok):
    results.append((name, bool(ok)))


def R(z):
    x, y = z
    return (-y, x + y)


def Rinv(z):
    x, y = z
    return (x + y, -x)


def add(*zs):
    return (sum((z[0] for z in zs), P.const(0)), sum((z[1] for z in zs), P.const(0)))


def scale(c, z):
    return (c * z[0], c * z[1])


def zeq(a, b):
    return (P.lift(a[0]) - b[0]).is_zero() and (P.lift(a[1]) - b[1]).is_zero()


def norm(k, l):
    return k * k + k * l + l * l


def G(u, v, k, l):  # u e + v f, e=(k,l), f=(-l,k+l)
    return (u * k - v * l, u * l + v * (k + l))


# --- (6) endpoint identities and G(W) ---
s, r, w, q, eps = V('s'), V('r'), V('w'), V('q'), V('eps')
# AR rows: k = q l + eps (eps=+-1 checked separately), Q = q(k+l)+l
for e in (1, -1):
    l = V('l'); k = q * l + e; T = norm(k, l); Q = q * (k + l) + l
    check(f'AR kQ=qT+el e={e}', (k * Q - (q * T + e * l)).is_zero())
    check(f'AR lQ=T-e(k+l) e={e}', (l * Q - (T - e * (k + l))).is_zero())
l = V('l')
k = q * l + 1; Q = q * (k + l) + l
check('AR A G(W)=(1,Q)', zeq(G(1, q, k, l), (P.const(1), Q)))
k = q * l - 1; Q = q * (k + l) + l
check('AR B G(W)=(Q-1,1)', zeq(G(q + 1, -1, k, l), (Q - 1, P.const(1))))
rows = [  # (name, l, k, Q, start, W, lhs rel)
    ('second+ B', s * r + 1, None, 'r', lambda k, l: s * (3 * k + l) + k, 'B', lambda: (3 * s + 1, -s), lambda k, l, Q: r * Q + (3 * k + l)),
    ('second- A', s * r - 1, None, 'r', lambda k, l: s * (2 * k + 3 * l) + k + l, 'A', lambda: (s, 2 * s + 1), lambda k, l, Q: r * Q - (2 * k + 3 * l)),
    ('diag+ B', s * w + 1, None, 'w1', lambda k, l: s * (2 * k + l) + k, 'B', lambda: (2 * s + 1, -s), lambda k, l, Q: w * Q + (2 * k + l)),
    ('diag- A', s * w - 1, None, 'w1', lambda k, l: s * (k + 2 * l) + k + l, 'A', lambda: (s, s + 1), lambda k, l, Q: w * Q - (k + 2 * l)),
    ('fold+ A', s * w + 1, None, 'w2', lambda k, l: s * (2 * k + 3 * l) - k - l, 'A', lambda: (s, 2 * s - 1), lambda k, l, Q: w * Q + (2 * k + 3 * l)),
    ('fold- B', s * w - 1, None, 'w2', lambda k, l: s * (3 * k + l) - k, 'B', lambda: (3 * s - 1, -s), lambda k, l, Q: w * Q - (3 * k + l)),
]
for name, l, _, kind, Qf, start, Wf, rel in rows:
    k = {'r': 2 * l + r, 'w1': l + w, 'w2': 2 * l - w}[kind]
    T = norm(k, l); Q = Qf(k, l); W = Wf()
    check(f'(6) {name}', (rel(k, l, Q) - T).is_zero())
    target = (P.const(1), Q) if start == 'A' else (Q, P.const(1))
    check(f'G(W) {name}', zeq(G(W[0], W[1], k, l), target))

# --- AR B containment bounds ---
l = V('l'); k = q * l - 1; T = norm(k, l)
check('ARB T-k(q+1)-l', (T - k * (q + 1) - l - (k * (k - q - 1) + k * l + l * l - l)).is_zero())
check('ARB k-q-1', (k - q - 1 - (q * (l - 1) - 2)).is_zero())

# --- outer region: six quantities, collisions (7), T-b ---
l = V('l'); k = q * l + r; T = norm(k, l)
a = (q - 4) * k + (q + 2) * l - 1; b = (q + 2) * k + 6 * l - 1
six = [
    (2 * T - k - l - l * b, (q * q - 4) * l * l + 3 * q * r * l + 2 * r * r - q * l - r),
    ((q + 2) * T - k * b, (q - 4) * k * l + (q + 2) * l * l + k),
    ((q + 2) * T - k * b - k - l, (q - 4) * k * l + (q + 2) * l * l - l),
    (l * b - T, k * (l - r) + 5 * l * l - l),
    (k * b - (q + 1) * T, (4 * q - 1) * l * l + (q + 5) * r * l + r * r - q * l - r),
    (l * b - T - k, k * (l - r - 1) + 5 * l * l - l),
]
for i, (x, y) in enumerate(six, 1):
    check(f'outer quantity {i}', (x - y).is_zero())
e, f = (k, l), (-l, k + l)
check('(7a)', zeq((P.const(1), a), add(R((P.const(0), b)), scale(q + 2, e), scale(-6, f))))
check('(7b)', zeq((a, P.const(0)), add(R((b, P.const(1))), scale(q - 4, e), scale(-(q + 2), f))))
check('outer T-b', (T - b - (k * (k - q - 2) + l * (k + l - 6) + 1)).is_zero())
check('outer T-k-l-la = kb-(q+1)T', (T - k - l - l * a - (k * b - (q + 1) * T)).is_zero())
# appendix B uses: 2T-lb = F1+k+l, T-la = F5+k+l
check('appB 2T-lb=F1+k+l', (2 * T - l * b - (six[0][0] + k + l)).is_zero())
check('appB T-la=F5+k+l', (T - l * a - (six[4][0] + k + l)).is_zero())
# numeric positivity of the six for sample admissible params (q>=3, 2<=r<=l-2)
pos_ok = True
for qq in range(3, 9):
    for ll in range(4, 30):
        for rr in range(2, ll - 1):
            kk = qq * ll + rr; TT = norm(kk, ll); bb = (qq + 2) * kk + 6 * ll - 1
            vals = [2*TT-kk-ll-ll*bb, (qq+2)*TT-kk*bb, (qq+2)*TT-kk*bb-kk-ll, ll*bb-TT, kk*bb-(qq+1)*TT, ll*bb-TT-kk]
            pos_ok &= all(v > 0 for v in vals)
check('outer six positive on samples', pos_ok)

# --- positive-side fans (8),(9) ---
S, D, E = V('S'), V('D'), V('E')
for c, smin, per in ((1, 2, 3), (2, 1, 2)):
    s_ = S + smin; w_ = D + E + 4; d_ = D + 2; l = s_ * w_ + d_; k = c * l + w_; T = norm(k, l)
    a = (c + 1) * s_ * k + (s_ - 5) * l - 1; b = (c * s_ + 5) * k + (c + 1) * s_ * l - 1
    nine = [a, b - a, T - b, (c * s_ + c + 2) * T - (k * b + k + l), ((c + 1) * s_ + c + 3) * T - ((k + l) * b + k),
            k * b - l - (c * s_ + c + 1) * T, (k + l) * b - ((c + 1) * s_ + c + 2) * T,
            T - (w_ * a + (c + 1) * k + l), (s_ + 2) * T - (k + l + l * b)]
    for i, x in enumerate(nine, 1):
        check(f'(8) c={c} P{i} coeffs', x.nonneg_coeffs_pos_const())
    e, f = (k, l), (-l, k + l)
    check(f'(9a) c={c}', zeq((P.const(0), a), add(Rinv((P.const(1), b)), scale(-(c * s_ + 5), e), scale((c + 1) * s_, f))))
    check(f'(9b) c={c}', zeq((a, P.const(1)), add(Rinv((b, P.const(0))), scale(s_ - 5, e), scale(c * s_ + 5, f))))

# --- negative-side fan (10),(11) ---
s_ = S + 2; w_ = D + E + 4; d_ = D + 2; l = s_ * w_ + d_; k = 2 * l - w_; T = norm(k, l)
a = (2 * s_ - 5) * k + 3 * s_ * l - 1; b = 3 * s_ * k + (s_ + 5) * l - 1
eight = [a, b - a, T - b, (s_ + 2) * T - (k + l + l * b), (3 * s_ + 3) * T - ((k + l) * b + k),
         l * b - k - (s_ + 1) * T, (k + l) * b - (3 * s_ + 2) * T, T - (w_ * a + 2 * k + 3 * l)]
for i, x in enumerate(eight, 1):
    check(f'(10) M{i} coeffs', x.nonneg_coeffs_pos_const())
e, f = (k, l), (-l, k + l)
check('(11a)', zeq((P.const(1), a), add(R((P.const(0), b)), scale(3 * s_, e), scale(-(s_ + 5), f))))
check('(11b)', zeq((a, P.const(0)), add(R((b, P.const(1))), scale(2 * s_ - 5, e), scale(-3 * s_, f))))
check('neg k(s+1)-1-2sl', (k * (s_ + 1) - 1 - 2 * s_ * l - ((s_ - 1) * w_ + 2 * d_ - 1)).is_zero())


# --- counts from the rule ---
def rule(k, l):
    if gcd(k, l) > 1:
        return False
    m = min(l, k - l)
    if m == 1:
        return True
    qq = k // m
    if qq >= 3:
        return k % m in (1, m - 1)
    rr = k - 2 * m
    return rr == 1 or m % rr in (1, rr - 1)


def pts(tmax, primitive=True):
    out = []
    kmax = int(sqrt(tmax)) + 2
    for k in range(2, kmax + 1):
        for l in range(1, k):
            T = norm(k, l)
            if T <= tmax and (not primitive or gcd(k, l) == 1):
                out.append((T, k, l))
    return out


prim673 = pts(673)
check('70 primitive with T<399 all positive', sum(1 for T, k, l in prim673 if T < 399) == 70 and all(rule(k, l) for T, k, l in prim673 if T < 399))
negs = sorted((T, k, l) for T, k, l in prim673 if not rule(k, l))
check('123 primitive T<=673', len(prim673) == 123)
check('7 negatives T<=673 listed', [(k, l) for T, k, l in negs] == [(17, 5), (18, 5), (19, 7), (22, 5), (17, 12), (23, 5), (21, 8)])
check('(17,5) T=399', norm(17, 5) == 399)
p5000 = pts(5000)
check('921 primitive T<=5000 (602/319)', len(p5000) == 921 and sum(rule(k, l) for _, k, l in p5000) == 602)
p7000 = [x for x in pts(7000) if x[0] > 5000]
check('360 primitive 5000<T<=7000 (171/189)', len(p7000) == 360 and sum(rule(k, l) for _, k, l in p7000) == 171)
all700 = pts(700, primitive=False)
prim700 = [x for x in all700 if gcd(x[1], x[2]) == 1]
check('R004 T<=700: 127 primitive (120/7), 103 nonprimitive',
      len(prim700) == 127 and sum(rule(k, l) for _, k, l in prim700) == 120 and len(all700) - len(prim700) == 103)
if '--big' in sys.argv:
    X = 10 ** 7; Dn = Pn = 0
    for k in range(2, int(sqrt(X)) + 2):
        for l in range(1, k):
            if norm(k, l) > X:
                break
            if gcd(k, l) == 1:
                Dn += 1; Pn += rule(k, l)
    check('X=1e7: 1,837,762 primitive, 81,946 positive', Dn == 1837762 and Pn == 81946)
    check('D(X) ~ X/(pi sqrt3)', abs(Dn - X / (pi * sqrt(3))) < 50 * sqrt(X) * 16)

# --- census table vs counts.csv ---
here = Path(__file__).resolve()
root = here.parent.parent
tex = (root / 'historical-paper-A3-v5-en.tex').read_text()
csvp = root / 'historical-counts-v3.csv'
rows_tex = {}
import re
for m_ in re.finditer(r'^(\d+) & ([\d,]+) & (\d+) \\\\$', tex, re.M):
    rows_tex[int(m_.group(1))] = (int(m_.group(2).replace(',', '')), int(m_.group(3)))
with open(csvp) as fh:
    rd = list(csv.DictReader(fh))
print('csv columns:', list(rd[0].keys()))
check('71 census rows', len(rows_tex) == 71)
check('census totals 120,622,224 / 816', sum(v[0] for v in rows_tex.values()) == 120622224 and sum(v[1] for v in rows_tex.values()) == 816)

for name, ok in results:
    print(('PASS ' if ok else 'FAIL ') + name)
print(f'{sum(o for _, o in results)}/{len(results)} PASS')
