#!/usr/bin/env python3
"""Exact (fractions) re-check of the counterexamples to Bushaw-Cody-Leffler Question 5.3.

Run:  python3 check.py        (well under a minute)
"""
from fractions import Fraction as Fr
from itertools import combinations

def dist(u, v, n, cyc):
    d = abs(u - v)
    return min(d, n - d) if cyc else d

def E(A, n, cyc, g=lambda r: Fr(1, r)):
    return sum(g(dist(u, v, n, cyc)) for u, v in combinations(sorted(A), 2))

def perts(A, n, cyc):
    S, out = set(A), set()
    for u in A:
        for v in ([(u - 1) % n, (u + 1) % n] if cyc else [u - 1, u + 1]):
            if (cyc or 0 <= v < n) and v not in S:
                out.add(tuple(sorted((S - {u}) | {v})))
    return sorted(out)

def report(name, n, A, cyc, g=lambda r: Fr(1, r), brute=True, better=None):
    eA = E(A, n, cyc, g)
    eP = {B: E(B, n, cyc, g) for B in perts(A, n, cyc)}
    print(f"{name}: {'C' if cyc else 'P'}_{n}, A = {A}, E(A) = {eA} ~ {float(eA):.6f}")
    print(f"  {len(eP)} perturbations, min E = {min(eP.values())} ~ {float(min(eP.values())):.6f};"
          f" strict local min: {all(e > eA for e in eP.values())};"
          f" weak (<=): {all(e >= eA for e in eP.values())}")
    if brute:
        best = min(E(B, n, cyc, g) for B in combinations(range(n), len(A)))
        arg = [B for B in combinations(range(n), len(A)) if E(B, n, cyc, g) == best]
        print(f"  global min (exhaustive) = {best} ~ {float(best):.6f}, attained by {arg}")
    if better:
        print(f"  E{better} = {E(better, n, cyc, g)}")
    return eA, eP

# The examples proved in Lean
report("cycle", 32, (0, 7, 16, 23), True, brute=False, better=(0, 8, 16, 24))
report("path", 13, (0, 1, 3, 6, 8, 10, 12), False)
report("path, literal reading", 10, (0, 1, 3, 6, 8, 9), False)
g8 = {1: 57, 2: 31, 3: 10, 4: 0}
report("cycle, g = (57,31,10,0)", 8, (0, 1, 4, 5), True, g=lambda r: Fr(g8[r]))

# The family C_{4x}, A = {0, x-1, 2x, 3x-1}
print("family C_{4x}, A = {0, x-1, 2x, 3x-1}:")
for x in range(3, 41):
    n, A = 4 * x, (0, x - 1, 2 * x, 3 * x - 1)
    eA = E(A, n, True)
    strict = all(E(B, n, True) > eA for B in perts(A, n, True))
    worse = eA > E((0, x, 2 * x, 3 * x), n, True)
    print(f"  x={x:2d}: strict local min {strict}, worse than maximally even {worse}")
    assert strict == (x >= 8) and worse
