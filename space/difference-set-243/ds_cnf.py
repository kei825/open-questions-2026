#!/usr/bin/env python3
"""
CNF generator for (v,k,lambda) difference sets in an abelian group
G = Z_{m1} x ... x Z_{mr}, written from scratch for this folder.

Encoding (see README.md, section "Proof", for why it is sound):

  * One Boolean variable per orbit of the numerical multiplier  g -> t*g
    (D is assumed to be the translate fixed by t; McFarland-Rice).
  * For every cyclic quotient G/H (H = kernel of a nontrivial character),
    the image of D is a vector (c_0, ..., c_{e-1}) of coset counts.  It must
    be one of the integer vectors that satisfy
        sum_j c_j = k,
        sum_j c_j c_{j+s} = lambda*|H| + n*[s = 0]      (s in Z_e),
        0 <= c_j <= |H|,   c_{t*j} = c_j.
    These vectors are enumerated exhaustively (allowed_vectors) and the
    choice is encoded with selector variables; coset counts are encoded
    with totalizers (Bailleux-Boufkhad), in both directions.
  * Optionally, the image of D in G/pG is fixed to a given vector
    (used to fix one representative of the 864 images in G/3G).

Taking all cyclic quotients together is equivalent to D being a difference
set (Fourier inversion), so a model of the CNF decodes to a difference set
and an actual t-invariant difference set extends to a model.

Usage:
  ds_cnf.py --moduli 3,9,9 --v 243 --k 121 --lam 60 --t 61 \
            [--fix-p 3 --fix-image image.json] [--max-e 81] \
            --out out.cnf [--meta out.json]
"""
import argparse
import itertools
import json
import math
import sys


# ---------------------------------------------------------------- group ---

def elements(moduli):
    return list(itertools.product(*[range(m) for m in moduli]))


def mul(t, g, moduli):
    return tuple((t * x) % m for x, m in zip(g, moduli))


def multiplier_orbits(moduli, t):
    """Orbits of g -> t*g on G (t must be coprime to |G|)."""
    seen = {}
    orbits = []
    for g in elements(moduli):
        if g in seen:
            continue
        orb = []
        h = g
        while h not in seen:
            seen[h] = len(orbits)
            orb.append(h)
            h = mul(t, h, moduli)
        orbits.append(orb)
    return orbits, seen


def cyclic_quotients(moduli):
    """All subgroups H with G/H cyclic and nontrivial, each given by a
    surjection phi: G -> Z_e (phi(g) labels the coset of g).
    Enumerated via characters chi_a(g) = exp(2 pi i sum a_i g_i / m_i);
    one representative per kernel."""
    M = 1
    for m in moduli:
        M = M * m // math.gcd(M, m)
    G = elements(moduli)
    seen = set()
    out = []
    for a in elements(moduli):
        if not any(a):
            continue
        vals = [sum(ai * gi * (M // mi) for ai, gi, mi in zip(a, g, moduli)) % M
                for g in G]
        image = sorted(set(vals))
        e = len(image)
        d = M // e
        assert all(x % d == 0 for x in image)
        ker = frozenset(i for i, x in enumerate(vals) if x == 0)
        if ker in seen:
            continue
        seen.add(ker)
        out.append((e, [x // d for x in vals]))
    return out


# ------------------------------------------------- allowed image vectors ---

def allowed_vectors(e, cap, k, lam, n, t):
    """All c in Z^e with 0<=c_j<=cap, sum c = k, c_{tj}=c_j and
    autocorrelation sum_j c_j c_{j+s} = lam*cap + n*[s==0].
    (cap = |H| = v/e.)"""
    # orbits of j -> t*j on Z_e
    orb_of = [-1] * e
    orbs = []
    for j in range(e):
        if orb_of[j] >= 0:
            continue
        o = []
        x = j
        while orb_of[x] < 0:
            orb_of[x] = len(orbs)
            o.append(x)
            x = (t * x) % e
        orbs.append(o)
    sizes = [len(o) for o in orbs]
    target_sq = n + lam * cap
    r = len(orbs)
    # suffix sums of sizes, for pruning
    suf = [0] * (r + 1)
    for i in range(r - 1, -1, -1):
        suf[i] = suf[i + 1] + sizes[i]
    res = []
    vals = [0] * r

    def rec(i, s, sq):
        if i == r:
            if s != k or sq != target_sq:
                return
            c = [vals[orb_of[j]] for j in range(e)]
            for sh in range(1, e):
                if sum(c[j] * c[(j + sh) % e] for j in range(e)) != lam * cap:
                    return
            res.append(tuple(c))
            return
        rem = k - s
        remsq = target_sq - sq
        if rem < 0 or remsq < 0 or rem > cap * suf[i]:
            return
        # Cauchy-Schwarz: sum of squares of the remaining suf[i] entries
        # is at least rem^2 / suf[i]
        if rem * rem > remsq * suf[i]:
            return
        for x in range(cap + 1):
            vals[i] = x
            rec(i + 1, s + sizes[i] * x, sq + sizes[i] * x * x)

    rec(0, 0, 0)
    return res


# ------------------------------------------------------------------- CNF ---

class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        # repeated orbit variables in a totalizer can produce a repeated
        # literal (e.g. -x -x r); remove repeats so the DIMACS is clean
        cl = list(dict.fromkeys(cl))
        if any(-l in cl for l in cl):
            return  # tautology (cannot occur in this encoding, kept for safety)
        self.clauses.append(cl)

    def totalizer(self, lits):
        """Return outputs o[1..m] (as list o[0..m-1]) with
        o[i-1] <-> (number of true literals in `lits`) >= i.
        `lits` is a multiset (repeats allowed)."""
        if len(lits) == 1:
            return [lits[0]]
        h = len(lits) // 2
        a = self.totalizer(lits[:h])
        b = self.totalizer(lits[h:])
        p, q = len(a), len(b)
        r = [self.new() for _ in range(p + q)]
        A = lambda i: a[i - 1]
        B = lambda j: b[j - 1]
        R = lambda m: r[m - 1]
        # upward: a>=i and b>=j  ->  r>=i+j
        for i in range(p + 1):
            for j in range(q + 1):
                if i + j == 0:
                    continue
                cl = [R(i + j)]
                if i:
                    cl.append(-A(i))
                if j:
                    cl.append(-B(j))
                self.add(cl)
        # downward: a<i+1 and b<j+1  ->  r<i+j+1
        for i in range(p + 1):
            for j in range(q + 1):
                if i + j + 1 > p + q:
                    continue
                cl = [-R(i + j + 1)]
                if i < p:
                    cl.append(A(i + 1))
                if j < q:
                    cl.append(B(j + 1))
                self.add(cl)
        return r

    def count_equals(self, outs, c, guard=None):
        """Clauses forcing (count == c), each optionally guarded by literal
        `guard` (guard -> count == c)."""
        g = [] if guard is None else [-guard]
        if c >= 1:
            self.add(g + [outs[c - 1]])
        if c < len(outs):
            self.add(g + [-outs[c]])

    def write(self, path, comments=()):
        with open(path, "w") as f:
            for cm in comments:
                f.write("c %s\n" % cm)
            f.write("p cnf %d %d\n" % (self.nv, len(self.clauses)))
            for cl in self.clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")


def build(moduli, v, k, lam, t, fix_p=None, fix_image=None, max_e=None,
          log=sys.stderr):
    n = k - lam
    G = elements(moduli)
    assert len(G) == v, "group order != v"
    assert lam * (v - 1) == k * (k - 1), "not admissible parameters"
    idx = {g: i for i, g in enumerate(G)}
    orbits, orb_of = multiplier_orbits(moduli, t)
    cnf = CNF()
    ovar = [cnf.new() for _ in orbits]           # variables 1..#orbits
    lit_of = [ovar[orb_of[g]] for g in G]        # element index -> literal
    print("orbits of x -> %d x: %d (sizes %s)" % (
        t, len(orbits), dict(sorted(
            {s: sum(1 for o in orbits if len(o) == s)
             for s in set(len(o) for o in orbits)}.items()))), file=log)

    # |D| = k
    cnf.count_equals(cnf.totalizer(lit_of[:]), k)

    quots = cyclic_quotients(moduli)
    cache = {}
    used = 0
    summary = {}
    for e, phi in quots:
        if max_e is not None and e > max_e:
            continue
        cap = v // e
        if e not in cache:
            cache[e] = allowed_vectors(e, cap, k, lam, n, t % e)
            print("  quotient order %d: %d allowed image vectors" %
                  (e, len(cache[e])), file=log)
        allowed = cache[e]
        used += 1
        summary[e] = summary.get(e, 0) + 1
        if not allowed:
            cnf.add([])  # no image possible -> trivially UNSAT
            continue
        cosets = [[] for _ in range(e)]
        for i, lab in enumerate(phi):
            cosets[lab].append(lit_of[i])
        outs = [cnf.totalizer(cs) for cs in cosets]
        sel = [cnf.new() for _ in allowed]
        cnf.add(sel)                              # at least one vector
        for s, vec in zip(sel, allowed):
            for j in range(e):
                cnf.count_equals(outs[j], vec[j], guard=s)
    print("cyclic quotients used: %s (total %d)" % (
        dict(sorted(summary.items())), used), file=log)

    if fix_image is not None:
        # image in G/pG: coset label = (g_i mod gcd(p, m_i))_i
        mods = [math.gcd(fix_p, m) for m in moduli]
        labels = list(itertools.product(*[range(x) for x in mods]))
        assert len(fix_image) == len(labels)
        cos = {lab: [] for lab in labels}
        for i, g in enumerate(G):
            cos[tuple(x % y for x, y in zip(g, mods))].append(lit_of[i])
        for lab, c in zip(labels, fix_image):
            cnf.count_equals(cnf.totalizer(cos[lab]), c)
    return cnf, orbits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--moduli", required=True)
    ap.add_argument("--v", type=int, required=True)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--lam", type=int, required=True)
    ap.add_argument("--t", type=int, default=1,
                    help="numerical multiplier (1 = none)")
    ap.add_argument("--fix-p", type=int)
    ap.add_argument("--fix-image", help="JSON list (or file) of coset counts")
    ap.add_argument("--max-e", type=int,
                    help="only use cyclic quotients of order <= this "
                         "(gives a relaxation: UNSAT still proves nonexistence)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--meta")
    a = ap.parse_args()
    moduli = [int(x) for x in a.moduli.split(",")]
    img = None
    if a.fix_image:
        s = a.fix_image
        img = json.loads(s) if s.lstrip().startswith("[") else json.load(open(s))
    cnf, orbits = build(moduli, a.v, a.k, a.lam, a.t, a.fix_p, img, a.max_e)
    cnf.write(a.out, comments=[
        "DS(%d,%d,%d) in Z%s, multiplier %d, fix_p=%s image=%s max_e=%s" % (
            a.v, a.k, a.lam, "xZ".join(map(str, moduli)), a.t, a.fix_p,
            json.dumps(img) if img else None, a.max_e)])
    print("wrote %s: %d vars, %d clauses" % (a.out, cnf.nv, len(cnf.clauses)),
          file=sys.stderr)
    if a.meta:
        json.dump({"moduli": moduli, "orbits": orbits}, open(a.meta, "w"))


if __name__ == "__main__":
    main()
