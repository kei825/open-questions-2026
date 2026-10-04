#!/usr/bin/env python3
"""Independent check (plain Python, no dependencies) of the parity obstruction for
Morris's 50-pc hexachordal ring, plus the analogous rings for windows of size 3, 4, 5.

Run:  python3 check.py        (about a minute; the k = 5 search dominates)
"""
import random, sys
from itertools import combinations

def orbit(s):
    """All 24 TnI images (transpositions, inversions) of a pitch-class set."""
    return {frozenset((sg * p + t) % 12 for p in s) for sg in (1, -1) for t in range(12)}

def classes(k):
    seen, out = set(), []
    for c in combinations(range(12), k):
        s = frozenset(c)
        if s in seen:
            continue
        orb = orbit(s)
        seen |= orb
        out.append(orb)
    return out

# (a)+(b): 50 hexachordal classes, parity of #odd pcs is constant on each, 25 are odd
hexa = classes(6)
par = []
for orb in hexa:
    ps = {sum(p % 2 for p in s) % 2 for s in orb}
    assert len(ps) == 1, "parity is not a TnI invariant"
    par.append(ps.pop())
print("hexachordal TnI classes:", len(hexa))
print("classes with an odd number of odd pitch classes:", sum(par))
assert len(hexa) == 50 and sum(par) == 25

# (c): sum over the windows of (#odd pcs) = 6 * (#odd pcs in the ring), always even;
# check it on random rings
for _ in range(1000):
    x = [random.randrange(12) for _ in range(50)]
    tot = sum(sum(x[(i + k) % 50] % 2 for k in range(6)) for i in range(50))
    assert tot == 6 * sum(v % 2 for v in x) and tot % 2 == 0
print("double counting identity checked on 1000 random rings")

# For comparison: rings for windows of size k = 3, 4, 5 DO exist (no parity obstruction:
# for k odd the parity is not an invariant, for k = 4 the number of odd classes is even).
def find_ring(k, limit=2_000_000):
    cls = classes(k)
    idx = {}
    for i, orb in enumerate(cls):
        for s in orb:
            idx[s] = i
    n = len(cls)
    sys.setrecursionlimit(10000)
    seq, used, nodes = [0, 1, 2, 3, 4, 5][: k - 1], set(), [0]
    def win(j):
        return frozenset(seq[(j + t) % n] for t in range(k))
    def dfs():
        nodes[0] += 1
        if nodes[0] > limit:
            return False
        if len(seq) == n:
            new = []
            for j in range(n - k + 1, n):
                w = win(j)
                if len(w) < k or idx[w] in used or idx[w] in new:
                    return False
                new.append(idx[w])
            return True
        for p in random.sample(range(12), 12):
            w = frozenset(seq[-(k - 1):] + [p])
            if len(w) < k or idx[w] in used:
                continue
            used.add(idx[w]); seq.append(p)
            if dfs():
                return True
            seq.pop(); used.discard(idx[w])
        return False
    return (seq, n) if dfs() else (None, n)

random.seed(1)
for k in (3, 4, 5):
    for attempt in range(20):
        ring, n = find_ring(k)
        if ring:
            # re-check the ring independently of the search
            cl = classes(k)
            wins = [frozenset(ring[(j + t) % n] for t in range(k)) for j in range(n)]
            assert all(len(w) == k for w in wins)
            hit = {next(i for i, orb in enumerate(cl) if w in orb) for w in wins}
            assert len(hit) == n
            print(f"k={k}: {n} classes, ring of length {n}:", " ".join(map(str, ring)))
            break
    else:
        print(f"k={k}: not found within the search budget")
