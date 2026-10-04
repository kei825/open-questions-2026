#!/usr/bin/env python3
"""Independent rigorous count of the critical points of d^2 on the whole torus (implementation 2 of 2).

Method: branch and prune with interval arithmetic + the Krawczyk test, directly on the gradient of
d^2 in half-angle coordinates.  Nothing from implementation 1 (the univariate polynomial F of the
paper, eq. (41)) is used.

* Coordinates.  The torus (f1, f2) is covered by 4 charts.  For each angle we use
  t = tan(f/2) on |f| <= pi/2 ("chart 0") or t = tan((f - pi)/2) on |f - pi| <= pi/2 ("chart pi"),
  always with t in [-1, 1].  Then cos f, sin f are rational in t.
* The squared distance d2(t, s) is a rational function; G1 = d d2/dt, G2 = d d2/ds are computed
  exactly with sympy (rational arithmetic), and multiplied by the positive factors Q1^3 Q2, Q1 Q2^3
  (Q_i = 1 + t_i^2 + e_i (+-)(1 - t_i^2) > 0) to give polynomials N1, N2 with rational coefficients.
  The zeros of (N1, N2) in a chart are exactly the critical points of d^2 in that chart, and at a zero
  the Jacobian of (N1, N2) is diag(positive) x (Hessian of d^2 in (t, s)), whose signature is the
  Morse type (minimum / maximum / saddle).
* Interval arithmetic: every number is an integer multiple of 2^-PREC (dyadic), intervals are pairs
  of Python integers, products are rounded outward.  This is exact rigorous arithmetic: no floating
  point is used anywhere in the decision procedure.
* A box is discarded when the interval value of N1 or N2 excludes 0.  A box X with midpoint m is
  certified to contain exactly one zero when the Krawczyk operator
      K(X) = m - Y N(m) + (I - Y J(X)) (X - m)
  satisfies K(X) inside the interior of X (Y: any matrix, here a rounded inverse of J(m)).
  Certified boxes come from a subdivision, so their interiors are disjoint and the zeros found are
  pairwise distinct; boxes on chart boundaries are handled by checking that no zero lies on
  t = +-1 (the bisection would not terminate otherwise).
* Output: the number of critical points on the whole torus, with type and a tiny enclosure for each.
"""
import sys, time
from fractions import Fraction as Fr
import sympy as sp

T0 = time.time()
PREC = 192                       # dyadic precision (bits)
ONE = 1 << PREC

# ------------------------------------------------------------------ dyadic intervals
def fr_lo(q):  # largest dyadic <= q
    q = Fr(q); return (q.numerator << PREC) // q.denominator
def fr_hi(q):
    q = Fr(q); return -((-q.numerator << PREC) // q.denominator)
def I(q): return (fr_lo(q), fr_hi(q))
def iadd(a, b): return (a[0] + b[0], a[1] + b[1])
def isub(a, b): return (a[0] - b[1], a[1] - b[0])
def imul(a, b):
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(p) >> PREC, -((-max(p)) >> PREC))
def contains0(a): return a[0] <= 0 <= a[1]
def ipoly2(P, X, Y):
    """Interval Horner evaluation of P = {deg_t: {deg_s: dyadic-interval coeff}} on box X x Y."""
    acc = (0, 0)
    for i in range(len(P) - 1, -1, -1):
        row = P[i]
        r = (0, 0)
        for j in range(len(row) - 1, -1, -1):
            r = iadd(imul(r, Y), row[j])
        acc = iadd(imul(acc, X), r)
    return acc

# ------------------------------------------------------------------ the example, exact
R = sp.Rational
p1, e1, p2, e2 = R(1), R(493, 500), R(113, 500), R(4983, 5000)
tau = R(89, 4000); cw = (1 - tau**2) / (1 + tau**2); sw = 2 * tau / (1 + tau**2)
t, s = sp.symbols('t s', real=True)

def chart_polys(sig1, sig2):
    """sig = +1 for chart 0 (f = 2 atan t), -1 for chart pi (f = pi + 2 atan t)."""
    c1 = sig1 * (1 - t**2) / (1 + t**2); s1 = sig1 * 2 * t / (1 + t**2)
    c2 = sig2 * (1 - s**2) / (1 + s**2); s2 = sig2 * 2 * s / (1 + s**2)
    r1 = p1 / (1 + e1 * c1); r2 = p2 / (1 + e2 * c2)
    x1, y1 = r1 * c1, r1 * s1
    x2, y2 = r2 * (c2 * cw - s2 * sw), r2 * (s2 * cw + c2 * sw)
    d2 = (x1 - x2)**2 + (y1 - y2)**2
    Q1 = 1 + t**2 + e1 * sig1 * (1 - t**2); Q2 = 1 + s**2 + e2 * sig2 * (1 - s**2)
    out = []
    for var, mult in ((t, Q1**3 * Q2), (s, Q1 * Q2**3)):
        N = sp.cancel(sp.together(sp.diff(d2, var) * mult))
        num, den = sp.fraction(N)
        assert den.is_number and den > 0, den
        out.append(sp.Poly(sp.expand(num / den), t, s))
    return out, d2

def to_table(P):
    """sympy Poly in t,s -> nested list of dyadic intervals, plus exact Fraction table."""
    dt = P.degree(t); ds = P.degree(s)
    tab = [[Fr(0)] * (ds + 1) for _ in range(dt + 1)]
    for (i, j), c in P.terms():
        tab[i][j] = Fr(int(c.p), int(c.q))
    itab = [[I(c) for c in row] for row in tab]
    return tab, itab

def deriv_tab(tab, wrt):
    if wrt == 0:
        return [[i * c for c in tab[i]] for i in range(1, len(tab))] or [[Fr(0)]]
    return [[j * row[j] for j in range(1, len(row))] or [Fr(0)] for row in tab]

def epoly2(tab, x, y):
    acc = Fr(0)
    for row in reversed(tab):
        r = Fr(0)
        for c in reversed(row): r = r * y + c
        acc = acc * x + r
    return acc

# ------------------------------------------------------------------ Krawczyk
def krawczyk(F, J, X, Y):
    """F = (tab1, tab2) exact tables, J = 2x2 interval tables. X, Y dyadic intervals.
    Returns ('unique', K) / ('none', None) / ('unknown', None)."""
    mx = (X[0] + X[1]) // 2; my = (Y[0] + Y[1]) // 2           # dyadic midpoint (integer scaled)
    m = (Fr(mx, ONE), Fr(my, ONE))
    Fm = [epoly2(F[k], *m) for k in range(2)]
    Jm = [[epoly2(J[k][l][0], *m) for l in range(2)] for k in range(2)]
    det = Jm[0][0] * Jm[1][1] - Jm[0][1] * Jm[1][0]
    if det == 0: return ('unknown', None)
    Yinv = [[Jm[1][1] / det, -Jm[0][1] / det], [-Jm[1][0] / det, Jm[0][0] / det]]
    # round the preconditioner to dyadics (any matrix is allowed)
    Yd = [[fr_lo(Yinv[k][l]) for l in range(2)] for k in range(2)]
    Yi = [[(v, v) for v in row] for row in Yd]
    JX = [[ipoly2(J[k][l][1], X, Y) for l in range(2)] for k in range(2)]
    dX = (isub(X, (mx, mx)), isub(Y, (my, my)))
    Fmi = [I(Fm[0]), I(Fm[1])]
    K = []
    for k in range(2):
        yF = iadd(imul(Yi[k][0], Fmi[0]), imul(Yi[k][1], Fmi[1]))
        acc = isub(((mx, my)[k],) * 2, yF)
        for l in range(2):
            # (I - Y J(X))_{k l}
            YJ = iadd(imul(Yi[k][0], JX[0][l]), imul(Yi[k][1], JX[1][l]))
            Ikl = isub(((ONE if k == l else 0),) * 2, YJ)
            acc = iadd(acc, imul(Ikl, dX[l]))
        K.append(acc)
    B = (X, Y)
    if all(B[k][0] < K[k][0] and K[k][1] < B[k][1] for k in range(2)):
        return ('unique', K)
    if any(K[k][1] < B[k][0] or K[k][0] > B[k][1] for k in range(2)):
        return ('none', None)
    return ('unknown', None)

def classify(J, K):
    """Sign of det and of J11 over the (tiny) certified box K."""
    JX = [[ipoly2(J[k][l][1], K[0], K[1]) for l in range(2)] for k in range(2)]
    det = isub(imul(JX[0][0], JX[1][1]), imul(JX[0][1], JX[1][0]))
    if det[1] < 0: return 'saddle'
    if det[0] > 0:
        if JX[0][0][0] > 0: return 'min'
        if JX[0][0][1] < 0: return 'max'
    return None

# ------------------------------------------------------------------ branch and prune
def run_chart(sig1, sig2, stats):
    (P1, P2), d2 = chart_polys(sig1, sig2)
    tab1, itab1 = to_table(P1); tab2, itab2 = to_table(P2)
    F = (tab1, tab2)
    J = []
    for tab in (tab1, tab2):
        row = []
        for wrt in (0, 1):
            dt = deriv_tab(tab, wrt)
            row.append((dt, [[I(c) for c in r] for r in dt]))
        J.append(row)
    found = []
    # start slightly larger than [-1,1]^2 is not needed: charts overlap only on f = +-pi/2,
    # and we check below that no zero lies near t = +-1 or s = +-1.
    stack = [((-ONE, ONE), (-ONE, ONE), 0)]
    # bisection points slightly off-centre to avoid hitting a zero exactly
    while stack:
        X, Y, depth = stack.pop()
        stats['boxes'] += 1
        v1 = ipoly2(itab1, X, Y)
        if not contains0(v1): continue
        v2 = ipoly2(itab2, X, Y)
        if not contains0(v2): continue
        wX, wY = X[1] - X[0], Y[1] - Y[0]
        if max(wX, wY) < ONE >> 6:
            st, K = krawczyk(F, J, X, Y)
            if st == 'none': continue
            if st == 'unique':
                # contract a few times to get a tiny enclosure for classification / reporting
                for _ in range(8):
                    st2, K2 = krawczyk(F, J, K[0], K[1])
                    if st2 != 'unique': break
                    K = K2
                typ = classify(J, K)
                found.append((K, typ))
                continue
        if depth > 400:
            raise RuntimeError("no convergence near box %s" % ((X, Y),))
        if wX >= wY:
            m = X[0] + (wX * 1000003) // 2000000
            stack += [((X[0], m), Y, depth + 1), ((m, X[1]), Y, depth + 1)]
        else:
            m = Y[0] + (wY * 1000003) // 2000000
            stack += [(X, (Y[0], m), depth + 1), (X, (m, Y[1]), depth + 1)]
    return found, d2

def dec(q, digits=12):
    """exact decimal string of a Fraction (no floats)."""
    q = Fr(q); sign = '-' if q < 0 else ''; q = abs(q)
    ip = q.numerator // q.denominator; rem = q - ip
    frac = (rem.numerator * 10**digits) // rem.denominator
    return f"{sign}{ip}.{frac:0{digits}d}"

total = []
stats = {'boxes': 0}
for sig1 in (+1, -1):
    for sig2 in (+1, -1):
        found, d2 = run_chart(sig1, sig2, stats)
        for K, typ in found:
            tlo, thi = Fr(K[0][0], ONE), Fr(K[0][1], ONE)
            slo, shi = Fr(K[1][0], ONE), Fr(K[1][1], ONE)
            # no zero on a chart boundary
            assert -1 < tlo and thi < 1 and -1 < slo and shi < 1
            total.append((sig1, sig2, (tlo, thi), (slo, shi), typ))
        print(f"chart (f1 {'0' if sig1 > 0 else 'pi'}, f2 {'0' if sig2 > 0 else 'pi'}): "
              f"{len(found)} certified zeros; boxes so far {stats['boxes']}; {time.time() - T0:.0f} s",
              flush=True)

print("\nCertified critical points (t, s are the chart coordinates; enclosures have width < 1e-40):")
import mpmath as mp   # only for printing angles in degrees, not used in any decision
mp.mp.dps = 30
rows = []
for sig1, sig2, (tlo, thi), (slo, shi), typ in total:
    def ang(sig, q):
        f = 2 * mp.atan(mp.mpf(q.numerator) / q.denominator) + (0 if sig > 0 else mp.pi)
        f = (f + mp.pi) % (2 * mp.pi) - mp.pi
        return mp.degrees(f)
    rows.append((ang(sig1, tlo), ang(sig2, slo), typ, thi - tlo, shi - slo))
rows.sort()
for f1, f2, typ, wt, ws in rows:
    assert wt < Fr(1, 10**40) and ws < Fr(1, 10**40)
    print(f"  f1 = {mp.nstr(f1, 15):>20} deg   f2 = {mp.nstr(f2, 15):>20} deg   {typ}")
cnt = {k: sum(1 for r in rows if r[2] == k) for k in ('min', 'max', 'saddle')}
print(f"\nTOTAL: {len(rows)} critical points on the torus; types {cnt}; "
      f"unclassified: {sum(1 for r in rows if r[2] is None)}")
print(f"Euler characteristic check: min - saddle + max = {cnt['min'] - cnt['saddle'] + cnt['max']} (torus: 0)")
print(f"boxes examined: {stats['boxes']}; elapsed {time.time() - T0:.1f} s")
