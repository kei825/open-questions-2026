#!/usr/bin/env python3
"""Arithmetic facts used in the proof (README, Steps 1-6), recomputed by
plain brute force, independently of the search routine in ds_cnf.py.
Standard library only."""
import itertools
import math

v, k, lam = 243, 121, 60
n = k - lam
MOD = (3, 9, 9)
G = list(itertools.product(*[range(m) for m in MOD]))

ok = True


def claim(text, cond):
    global ok
    ok &= bool(cond)
    print(("OK   " if cond else "FAIL ") + text)


claim("admissible: lam(v-1) = k(k-1)", lam * (v - 1) == k * (k - 1))
claim("n = 61 is prime", n == 61 and all(n % p for p in range(2, 8)))
claim("multiplier theorem: 61 | n, gcd(61,v)=1, 61 > lam",
      n % 61 == 0 and math.gcd(61, v) == 1 and 61 > lam)
claim("McFarland-Rice: gcd(k, v) = 1", math.gcd(k, v) == 1)
claim("61 = 1 mod 3 and 61 = 7 mod 9", 61 % 3 == 1 and 61 % 9 == 7)

# orbits of x -> 61x
seen, sizes = set(), []
for g in G:
    if g in seen:
        continue
    orb, h = [], g
    while h not in seen:
        seen.add(h)
        orb.append(h)
        h = tuple((61 * a) % m for a, m in zip(h, MOD))
    sizes.append(len(orb))
claim("orbits: 27 fixed points + 72 of size 3 (99 in total)",
      sizes.count(1) == 27 and sizes.count(3) == 72 and len(sizes) == 99)
fixed = {g for g in G if tuple((61 * a) % m for a, m in zip(g, MOD)) == g}
G3 = {g for g in G if all((3 * a) % m == 0 for a, m in zip(g, MOD))}
claim("fixed points of 61 = G[3]", fixed == G3)
# every 3-orbit lies in one coset of 3G; G[3] is the union of cosets (a,0,0)
claim("each orbit {g,7g,4g} lies in one coset of 3G",
      all(tuple(x % 3 for x in g) ==
          tuple(((61 * a) % m) % 3 for a, m in zip(g, MOD)) for g in G))
claim("G[3] = union of the three cosets (a,0,0) of 3G",
      G3 == {g for g in G if g[1] % 3 == 0 and g[2] % 3 == 0})

# number of cyclic quotients: elements of order 3 and 9
def order(g):
    o = 1
    while any((o * a) % m for a, m in zip(g, MOD)):
        o += 1
    return o
o3 = sum(1 for g in G if order(g) == 3)
o9 = sum(1 for g in G if order(g) == 9)
claim("26 elements of order 3, 216 of order 9 -> 13 + 36 = 49 cyclic quotients",
      o3 == 26 and o9 == 216 and o3 // 2 + o9 // 6 == 49)

# admissible Z3 images: brute force
z3 = sorted((a, b, k - a - b) for a in range(82) for b in range(82)
            if 0 <= k - a - b <= 81
            and a * a + b * b + (k - a - b) ** 2 == n + lam * 81)
claim("Z3 images = the 6 permutations of (36,40,45)",
      z3 == sorted(itertools.permutations((36, 40, 45))))

# admissible Z9 images invariant under j -> 7j: brute force over
# c0=a, c3=c, c6=d, c1=c4=c7=b, c2=c5=c8=e (all <= 27)
z9 = []
for a, c, d, b in itertools.product(range(28), repeat=4):
    r = k - a - c - d - 3 * b
    if r % 3 or not 0 <= r // 3 <= 27:
        continue
    e = r // 3
    vec = [a, b, e, c, b, e, d, b, e]
    if all(sum(vec[j] * vec[(j + s) % 9] for j in range(9)) ==
           lam * 27 + (n if s == 0 else 0) for s in range(9)):
        z9.append(tuple(vec))
try:
    import ds_cnf
    same = sorted(z9) == sorted(ds_cnf.allowed_vectors(9, 27, k, lam, n, 7))
except ImportError:
    same = None
claim("Z9 images: exactly 12 (c0,c3,c6 a permutation of 9,13,18; the "
      "orbits {1,4,7},{2,5,8} take 12 and 15); same list as ds_cnf.py: %s"
      % same,
      len(z9) == 12 and same is not False and
      all(sorted((x[0], x[3], x[6])) == [9, 13, 18] and
          sorted((x[1], x[2])) == [12, 15] for x in z9))
print("ALL OK" if ok else "SOME CHECK FAILED")
