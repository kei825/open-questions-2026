#!/usr/bin/env python3
"""
Two independent checks about the images of a 61-invariant (243,121,60)
difference set D of G = Z3 x Z9 x Z9 in G/3G = Z3^3.

1. A second enumeration of the images (different method from
   enum_images.c): with the multiplier constraint E(x) = 0 mod 3 off the
   line L = {(0,0,0),(1,0,0),(2,0,0)}, every plane-sum vector of a direction
   d is a permutation of (36,40,45) whose "40" sits on the unique plane
   whose residue mod 3 is 1.  We simply loop over all ways to put 36/45 on
   the other two planes (2^13) and over the 3 choices of the residue-1
   point of L, invert, and keep what passes the direct check.  To stay
   honest we do NOT rely on this argument for completeness: the result is
   compared with the output of enum_images.c (complete 6^13 search).

2. Symmetry: build explicit automorphisms of G (random homomorphisms that
   turn out to be bijective), together with the translations by G[3]
   (which preserve 61-invariance, since 61*g = g on G[3]).  Each of them
   maps 61-invariant difference sets to 61-invariant difference sets, hence
   permutes the possible images.  We compute the induced permutation group
   on the image set and its orbits.

Usage: orbit_check.py images864.txt
"""
import itertools
import random
import sys

MOD = (3, 9, 9)
G = list(itertools.product(range(3), range(9), range(9)))
Z33 = list(itertools.product(range(3), repeat=3))   # index 9a+3b+c


def check_E(E):
    if any(e < 0 or e > 9 for e in E) or sum(E) != 121:
        return False
    for s in Z33:
        c = 0
        for i, x in enumerate(Z33):
            y = tuple((a + b) % 3 for a, b in zip(x, s))
            c += E[i] * E[9 * y[0] + 3 * y[1] + y[2]]
        if c != (601 if s == (0, 0, 0) else 540):
            return False
    return True


def fast_enum():
    dirs = [d for d in Z33 if any(d) and next(x for x in d if x) == 1]
    assert len(dirs) == 13
    L = [(0, 0, 0), (1, 0, 0), (2, 0, 0)]
    sols = set()
    for special in L:              # the point of L with E = 1 mod 3
        planes40 = []
        for d in dirs:
            planes40.append(sum(a * b for a, b in zip(d, special)) % 3)
        for bits in range(1 << 13):
            acc = [0] * 27
            for i, d in enumerate(dirs):
                j40 = planes40[i]
                others = [j for j in range(3) if j != j40]
                P = {j40: 40}
                if (bits >> i) & 1:
                    P[others[0]], P[others[1]] = 36, 45
                else:
                    P[others[0]], P[others[1]] = 45, 36
                for xi, x in enumerate(Z33):
                    acc[xi] += P[sum(a * b for a, b in zip(d, x)) % 3]
            if any((a - 484) % 9 for a in acc):
                continue
            E = tuple((a - 484) // 9 for a in acc)
            if check_E(E) and all(E[i] % 3 == 0 for i in range(27) if i % 9):
                sols.add(E)
    return sols


def add(g, h):
    return tuple((a + b) % m for a, b, m in zip(g, h, MOD))


def smul(c, g):
    return tuple((c * a) % m for a, m in zip(g, MOD))


def random_automorphism(rng):
    G3 = [g for g in G if smul(3, g) == (0, 0, 0)]
    while True:
        h1 = rng.choice(G3)          # image of (1,0,0): must have order | 3
        h2 = rng.choice(G)
        h3 = rng.choice(G)
        f = {}
        for g in G:
            f[g] = add(add(smul(g[0], h1), smul(g[1], h2)), smul(g[2], h3))
        if len(set(f.values())) == 243:
            # homomorphism check (well-definedness): f(g+h) = f(g)+f(h)
            for _ in range(200):
                a, b = rng.choice(G), rng.choice(G)
                assert f[add(a, b)] == add(f[a], f[b])
            return f


def induced(f):
    """Induced permutation of Z3^3 = G/3G (as index list), checked to be
    well defined on every coset."""
    perm = [None] * 27
    for g in G:
        x = 9 * (g[0] % 3) + 3 * (g[1] % 3) + g[2] % 3
        y = f[g]
        yi = 9 * (y[0] % 3) + 3 * (y[1] % 3) + y[2] % 3
        assert perm[x] is None or perm[x] == yi
        perm[x] = yi
    return tuple(perm)


def act(perm, E):
    out = [0] * 27
    for x in range(27):
        out[perm[x]] = E[x]
    return tuple(out)


def main():
    sols_c = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
    S = set(sols_c)
    print("enum_images.c: %d images (%d distinct), all pass direct check: %s"
          % (len(sols_c), len(S), all(check_E(E) for E in S)))
    F = fast_enum()
    print("second enumeration: %d images; identical sets: %s" % (len(F), F == S))

    rng = random.Random(2026)
    gens = []
    for _ in range(40):
        gens.append(induced(random_automorphism(rng)))
    # translation by (1,0,0) in G[3]: x -> x + e1 on G/3G
    tr = tuple(9 * ((x // 9 + 1) % 3) + x % 9 for x in range(27))
    gens.append(tr)
    # group generated (as permutations of Z3^3)
    ident = tuple(range(27))
    grp = {ident}
    frontier = [ident]
    while frontier:
        nf = []
        for p in frontier:
            for g in gens:
                q = tuple(g[p[x]] for x in range(27))
                if q not in grp:
                    grp.add(q)
                    nf.append(q)
        frontier = nf
    print("group generated by 40 random automorphisms + translation by e1, "
          "acting on G/3G: order %d" % len(grp))
    # it must permute the image set
    closed = all(act(g, E) in S for g in gens for E in S)
    print("generators map the image set into itself: %s" % closed)
    # orbits
    left = set(S)
    orbit_sizes = []
    while left:
        E0 = min(left)
        orb = {act(g, E0) for g in grp}
        orbit_sizes.append(len(orb))
        left -= orb
    print("orbits on the image set: %d, sizes %s" % (len(orbit_sizes), orbit_sizes))
    E0 = min(S)
    stab = sum(1 for g in grp if act(g, E0) == E0)
    print("representative (lexicographically smallest) E0 =", list(E0))
    print("stabilizer order of E0 in the group: %d" % stab)


if __name__ == "__main__":
    main()
