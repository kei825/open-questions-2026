#!/usr/bin/env python3
"""Exact count of the critical points of d^2 for the planar example (implementation 1 of 2).

Only Python integers and fractions.Fraction are used (no floating point, no sympy).
The script proves that the example has EXACTLY 12 critical points on the torus:
10 that are not orbit intersections (real roots of the degree-10 polynomial F of
Gronchi-Bau-Grassi 2023, eq. (41), in t = tan(f1/2)) and 2 intersections.

Logic (see README, section Proof):
  * A critical point with X1 != X2 satisfies (35) and (36) of the paper (the two tangent
    vectors are parallel and orthogonal to X1 - X2), and conversely.  (35),(36) are
    equivalent to (38),(39), which are linear in (cos f2, sin f2).
  * If mu != 0 and beta != 0, (38),(39) have exactly one solution (cos f2, sin f2), and it lies
    on the unit circle iff (41) holds, i.e. iff F(t) = 0.
  * mu = 0 means f1 in {0, pi}; then (39) reads delta = 0, which fails (checked below).
  * beta = 0 (with mu != 0) forces cos f2 = -e2 and delta = e2*mu, hence F = alpha^2 (delta-e2 mu)^2 = 0;
    so t would be a common root of F and of beta's numerator: excluded by gcd = 1.
  * Intersections X1 = X2: same polar angle f1 = f2 + omega and p1(1+e2 cos(f1-omega)) = p2(1+e1 cos f1),
    a quadratic Iq(t) = 0 with two real roots (f1 = pi is checked separately).
  * gcd(F, Iq) = 1, so the two sets are disjoint.
"""
from fractions import Fraction as Fr
import time

T0 = time.time()
# ---------------------------------------------------------------- polynomial arithmetic
# a polynomial is a list of Fractions, lowest degree first, no trailing zeros
def norm(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p
def add(p, q):
    n = max(len(p), len(q))
    return norm([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])
def neg(p): return [-c for c in p]
def sub(p, q): return add(p, neg(q))
def mul(p, q):
    if not p or not q: return []
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a == 0: continue
        for j, b in enumerate(q):
            r[i + j] += a * b
    return norm(r)
def smul(c, p): return norm([c * x for x in p])
def deg(p): return len(p) - 1
def divmod_(p, q):
    p = list(p); out = [Fr(0)] * max(1, len(p) - len(q) + 1)
    while p and len(p) >= len(q):
        c = p[-1] / q[-1]; k = len(p) - len(q)
        out[k] = c
        p = sub(p, [Fr(0)] * k + smul(c, q))
    return norm(out), p
def deriv(p): return norm([i * p[i] for i in range(1, len(p))])
def ev(p, x):
    r = Fr(0)
    for c in reversed(p): r = r * x + c
    return r
def gcd(p, q):
    while q:
        p, q = q, divmod_(p, q)[1]
    return smul(1 / p[-1], p)
def sgn(x): return (x > 0) - (x < 0)
def dec(q, digits=25):
    """exact decimal expansion (truncated) of a Fraction, without floating point"""
    q = Fr(q); sign = "-" if q < 0 else ""; q = abs(q)
    ip = q.numerator // q.denominator; rem = q - ip
    return f"{sign}{ip}.{(rem.numerator * 10**digits) // rem.denominator:0{digits}d}"

# ---------------------------------------------------------------- the example
p1, e1 = Fr(1), Fr(493, 500)
p2, e2 = Fr(113, 500), Fr(4983, 5000)
tau = Fr(89, 4000)                         # tan(omega/2)
cw = (1 - tau**2) / (1 + tau**2)           # cos omega
sw = 2 * tau / (1 + tau**2)                # sin omega
print("p1 =", p1, " e1 =", e1, " p2 =", p2, " e2 =", e2, " tan(omega/2) =", tau)
print("cos omega =", cw, " sin omega =", sw)

t = [Fr(0), Fr(1)]
one = [Fr(1)]
den = add(one, mul(t, t))                  # 1 + t^2
C1 = sub(one, mul(t, t))                   # (1 + t^2) cos f1
S1 = smul(2, t)                            # (1 + t^2) sin f1
# alpha = sin(omega - f1) + e1 sin(omega), beta = cos(omega - f1) + e1 cos(omega)
A = add(sub(smul(sw, C1), smul(cw, S1)), smul(e1 * sw, den))          # alpha * den
B = add(add(smul(cw, C1), smul(sw, S1)), smul(e1 * cw, den))          # beta  * den
M = smul(p1 * e1 * e2, S1)                                            # mu    * den
D = add(smul(p1 * e1, mul(S1, den)), smul(p2 * e2, mul(add(den, smul(e1, C1)), A)))  # delta * den^2
# (41): (alpha^2+beta^2) delta^2 - 2 e2 alpha^2 delta mu + mu^2 (e2^2 alpha^2 - beta^2) = 0, times den^6
F12 = add(sub(mul(add(mul(A, A), mul(B, B)), mul(D, D)),
              smul(2 * e2, mul(mul(mul(A, A), mul(D, M)), den))),
          mul(mul(mul(M, M), sub(smul(e2**2, mul(A, A)), mul(B, B))), mul(den, den)))
F, r = divmod_(F12, den)
assert r == [], "den does not divide F12"
print("deg F12 =", deg(F12), "; F12 = (1+t^2) * F with deg F =", deg(F))
assert deg(F) == 10

# ---------------------------------------------------------------- Sturm sequence
def sturm_seq(p):
    seq = [p, deriv(p)]
    while True:
        r = divmod_(seq[-2], seq[-1])[1]
        if not r: break
        seq.append(neg(r))
    return seq
def var(signs):
    s = [x for x in signs if x != 0]
    return sum(1 for a, b in zip(s, s[1:]) if a != b)
def V_at(seq, x): return var([sgn(ev(q, x)) for q in seq])
def V_inf(seq, side):  # side=+1 : +inf, -1 : -inf
    return var([sgn(q[-1]) * (side ** deg(q)) for q in seq])
seq = sturm_seq(F)
nreal = V_inf(seq, -1) - V_inf(seq, +1)
print("Sturm sequence length:", len(seq), "; number of distinct real roots of F:", nreal)
assert nreal == 10
g = gcd(F, deriv(F))
print("gcd(F, F') has degree", deg(g), "(F is squarefree)")
assert deg(g) == 0

# ---------------------------------------------------------------- side conditions
print("F(0) =", "nonzero" if ev(F, 0) != 0 else "ZERO", "(so sin f1 != 0, i.e. mu != 0, at every root)")
assert ev(F, 0) != 0
gB = gcd(F, B)
print("gcd(F, beta*den) has degree", deg(gB), "(so beta != 0 at every root)")
assert deg(gB) == 0
# mu = 0 cases: f1 = 0 and f1 = pi.  (39) becomes delta = 0.
for name, c1, s1 in (("f1 = 0", Fr(1), Fr(0)), ("f1 = pi", Fr(-1), Fr(0))):
    alpha = sw * c1 - cw * s1 + e1 * sw
    delta = p1 * e1 * s1 + p2 * e2 * (1 + e1 * c1) * alpha
    print(f"  {name}: delta = {delta}  (nonzero: no critical point with X1 != X2 there)")
    assert delta != 0
# intersections
Iq = sub(smul(p1, add(den, smul(e2, add(smul(cw, C1), smul(sw, S1))))), smul(p2, add(den, smul(e1, C1))))
print("Iq(t) =", " + ".join(f"({c})*t^{i}" for i, c in enumerate(Iq)))
assert deg(Iq) == 2
disc = Iq[1]**2 - 4 * Iq[2] * Iq[0]
print("discriminant of Iq > 0:", disc > 0, "; leading coefficient nonzero:", Iq[2] != 0)
assert disc > 0 and Iq[2] != 0
# f1 = pi (t = infinity) is not an intersection: p1 (1 + e2 cos(pi - omega)) != p2 (1 - e1)
assert p1 * (1 - e2 * cw) != p2 * (1 - e1)
gI = gcd(F, Iq)
print("gcd(F, Iq) has degree", deg(gI), "(no root of F is an intersection)")
assert deg(gI) == 0
print("=> exactly 10 non-intersection critical points + exactly 2 intersections = 12 critical points")

# ---------------------------------------------------------------- isolate the roots exactly
def isolate(seq, lo, hi, n_expected):
    out, stack = [], [(lo, hi)]
    while stack:
        a, b = stack.pop()
        k = V_at(seq, a) - V_at(seq, b)       # number of roots in (a, b]
        if k == 0: continue
        if k == 1 and ev(seq[0], b) != 0:
            out.append((a, b)); continue
        m = (a + b) / 2
        stack += [(a, m), (m, b)]
    out.sort()
    assert len(out) == n_expected
    return out
bound = 1 + max(abs(c / F[-1]) for c in F[:-1])        # Cauchy bound
ivs = isolate(seq, -bound, bound, 10)
def refine(p, a, b, width):
    sa = sgn(ev(p, a))
    while b - a > width:
        m = (a + b) / 2; sm = sgn(ev(p, m))
        if sm == 0: return m, m
        if sm == sa: a = m
        else: b = m
    return a, b
W = Fr(1, 10**40)
print("\nIsolating intervals of relative width < 1e-40 with exact rational endpoints, t = tan(f1/2)\n(lower endpoint shown, truncated to 25 decimals):")
roots = []
for a, b in ivs:
    a, b = refine(F, a, b, W * max(1, abs(a)))
    assert sgn(ev(F, a)) * sgn(ev(F, b)) <= 0
    roots.append((a, b))
    print("  F  root: t =", dec(a), "...")
iroots = []
sI = sturm_seq(Iq)
for a, b in isolate(sI, -bound * 10, bound * 10, 2):
    a, b = refine(Iq, a, b, W * max(1, abs(a)))
    iroots.append((a, b))
    print("  Iq root: t =", dec(a), "...")
# the 12 values of t are pairwise distinct (intervals pairwise disjoint)
allv = sorted(roots + iroots)
assert all(allv[i][1] < allv[i + 1][0] for i in range(11))
print("the 12 isolating intervals are pairwise disjoint")

# the intervals used in the Lean proof contain these roots, one each
lean = [("I", Fr(-217, 5), Fr(-433, 10)), ("F", Fr(-191, 5), Fr(-381, 10)), ("I", Fr(-293, 10), Fr(-146, 5)),
        ("F", Fr(-489, 50), Fr(-977, 100)), ("F", Fr(-377, 50), Fr(-753, 100)), ("F", Fr(-131, 10000), Fr(-13, 1000)),
        ("F", Fr(89, 2000), Fr(223, 5000)), ("F", Fr(69, 5), Fr(139, 10)), ("F", Fr(237, 10), Fr(119, 5)),
        ("F", Fr(192, 5), Fr(77, 2)), ("F", Fr(198), Fr(199)), ("F", Fr(1990000), Fr(2000000))]
for kind, a, b in lean:
    src = roots if kind == "F" else iroots
    inside = [r for r in src if a <= r[0] and r[1] <= b]
    assert len(inside) == 1
print("each interval of the Lean proof contains exactly one of these roots")
with open(__file__.replace("sturm_count.py", "roots.txt"), "w") as fh:
    for kind, (a, b) in [("F", r) for r in roots] + [("I", r) for r in iroots]:
        fh.write(f"{kind} {a.numerator}/{a.denominator} {b.numerator}/{b.denominator}\n")
print("wrote roots.txt;  elapsed %.1f s" % (time.time() - T0))
