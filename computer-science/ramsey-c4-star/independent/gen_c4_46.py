#!/usr/bin/env python3
"""Independent CNF generator for: "no C4-free graph on 46 vertices has minimum degree >= 7".

Written from scratch (without looking at the earlier csfork scripts).  Pure Python 3, no
dependencies.  Output is deterministic, so the sha256 of each CNF is reproducible.

Encoding
--------
* One Boolean variable per unordered pair {i,j} of the 46 vertices (1035 variables):
  var(i,j) is true iff ij is an edge.
* C4-freeness: for every 4-set and each of its 3 cyclic orders (a,b,c,d) the clause
  (-ab | -bc | -cd | -da).  This is the literal statement "G contains no 4-cycle".
* Degree: for every vertex, "at least 7 incident edges" (Sinz sequential counter on the
  negated literals, i.e. at most 38 of the 45 non-edges).  With --exact also "at most 7"
  (this is the derived lemma that G must be 7-regular; it is not needed for soundness of
  an UNSAT answer -- it only adds clauses implied by the lemma).
* WLOG structure (unit clauses, see README "Proof"; shown for delta=7, the code is generic
  in --delta with blocks of size delta-2 / delta-1): N(0) = {1..7}; inside N(0) the edges
  are exactly the matching (1,2),(3,4) [and (5,6) when m=3]; the private second neighbours
  of u in N(0) are a consecutive block (5 vertices if u is matched, 6 if not), blocks in the
  order u = 1..7, starting at vertex 8; the remaining vertices (2 when m=3, none when m=2)
  are "free".  Every pair with an endpoint in {0..7} is fixed by unit clauses.
  With --no-fix the structure units are omitted (then the formula is exactly the original
  statement; useful only as a sanity check of the base encoding on smaller n).
* Symmetry breaking (optional, --lex consec|all|none): for vertices a<b in the same block
  (or both free) require row(a) <=_lex row(b), where row(v) is the 0/1 vector
  (x_{v,j})_{j not in {a,b}} in increasing j.  This is exactly the lex-leader constraint
  x <=_lex x∘(a b) for the variable order (i,j) lexicographic with i<j (see VERIFY.md).

Other options (all sound; see VERIFY.md):
  --lex first     only the first consecutive pair of each block (weaker subset)
  --lex-max       row(a) >=_lex row(b) instead (lex-max representative)
  --tri           every vertex has at most one incident edge lying in no triangle
                  (valid once the m=2 case is refuted: then m(v)=3 for every v)
  --free-case K   m=3 only: fix the neighbourhood of free vertex 44 (cases K=0..7),
                  an elementary WLOG used instead of lex
  --delta D, -n N, --no-fix   generic parameters for the small-case validation

Usage: gen_c4_46.py --m 3 [--lex consec] [--exact] [-n 46] > out.cnf
"""
import argparse
import itertools
import sys


class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.clauses.append(list(cl))


def at_most_seq(cnf, xs, k):
    """Sinz sequential counter: at most k of the literals xs are true (k >= 1)."""
    n = len(xs)
    if k >= n:
        return
    if k == 0:
        for x in xs:
            cnf.add([-x])
        return
    s = [[cnf.new() for _ in range(k)] for _ in range(n - 1)]  # s[i][j]: >= j+1 true among x0..xi
    cnf.add([-xs[0], s[0][0]])
    for j in range(1, k):
        cnf.add([-s[0][j]])
    for i in range(1, n - 1):
        cnf.add([-xs[i], s[i][0]])
        cnf.add([-s[i - 1][0], s[i][0]])
        for j in range(1, k):
            cnf.add([-xs[i], -s[i - 1][j - 1], s[i][j]])
            cnf.add([-s[i - 1][j], s[i][j]])
        cnf.add([-xs[i], -s[i - 1][k - 1]])
    cnf.add([-xs[n - 1], -s[n - 2][k - 1]])


def lex_leq(cnf, A, B):
    """A <=_lex B (lists of literals, same length), with prefix-equality auxiliaries."""
    eq_prev = None  # None means "true" (empty prefix is equal)
    for k, (a, b) in enumerate(zip(A, B)):
        pre = [] if eq_prev is None else [-eq_prev]
        cnf.add(pre + [-a, b])  # prefix equal -> a <= b
        if k == len(A) - 1:
            break
        e = cnf.new()  # e -> nothing; (prefix equal and a == b) -> e
        cnf.add(pre + [a, b, e])
        cnf.add(pre + [-a, -b, e])
        eq_prev = e


def triangle_gadget(cnf, V, e, n):
    """Every vertex has at most one incident edge that lies in no triangle."""
    bad = {}
    for (i, j), x in list(V.items()):
        t = cnf.new()
        ys = []
        for w in range(n):
            if w in (i, j):
                continue
            y = cnf.new()
            cnf.add([-y, e(i, w)])
            cnf.add([-y, e(j, w)])
            ys.append(y)
        cnf.add([-t] + ys)          # t -> edge ij lies in some triangle ijw
        b = cnf.new()
        cnf.add([-x, t, b])         # edge ij present and t false -> b
        bad[(i, j)] = b
    for v in range(n):
        at_most_seq(cnf, [bad[(min(v, u), max(v, u))] for u in range(n) if u != v], 1)


def structure(n, m, D=7):
    """Return (matched, blocks, free) for the WLOG layout; blocks[u] = private vertices of u."""
    matched = set(range(1, 2 * m + 1))
    blocks = {}
    nxt = D + 1
    for u in range(1, D + 1):
        size = D - 2 if u in matched else D - 1
        blocks[u] = list(range(nxt, nxt + size))
        nxt += size
    if nxt > n:
        raise SystemExit(f"layout needs {nxt} vertices > n={n}")
    free = list(range(nxt, n))
    return matched, blocks, free


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", type=int, default=46)
    ap.add_argument("--m", type=int, required=True, help="number of edges inside N(0)")
    ap.add_argument("--delta", type=int, default=7, help="minimum degree")
    ap.add_argument("--lex", choices=["none", "first", "consec", "all"], default="consec",
                    help="first = only the first consecutive pair of each block (a weaker subset)")
    ap.add_argument("--exact", action="store_true", help="also add deg <= delta (7-regularity lemma)")
    ap.add_argument("--no-fix", action="store_true")
    ap.add_argument("--lex-max", action="store_true",
                    help="use row(a) >=_lex row(b) instead (lex-max representative; equally sound)")
    ap.add_argument("--free-case", type=int, choices=range(8), default=None,
                    help="m=3: fix the neighbourhood of the first free vertex (case 0..7), "
                         "an elementary WLOG used instead of --lex")
    ap.add_argument("--tri", action="store_true",
                    help="every vertex has at most one incident edge that lies in no triangle "
                         "(valid for D=7, n=46 once the m=2 case is refuted: then m(v)=3 for all v)")
    args = ap.parse_args()
    n, m, D = args.n, args.m, args.delta

    cnf = CNF()
    V = {}
    for i in range(n):
        for j in range(i + 1, n):
            V[(i, j)] = cnf.new()

    def e(i, j):
        return V[(i, j)] if i < j else V[(j, i)]

    # C4-freeness
    for a, b, c, d in itertools.combinations(range(n), 4):
        for (p, q, r, s) in ((a, b, c, d), (a, b, d, c), (a, c, b, d)):
            cnf.add([-e(p, q), -e(q, r), -e(r, s), -e(s, p)])

    # degree constraints
    for v in range(n):
        inc = [e(v, w) for w in range(n) if w != v]
        at_most_seq(cnf, [-x for x in inc], (n - 1) - D)  # at least D edges
        if args.exact:
            at_most_seq(cnf, inc, D)

    if not args.no_fix:
        assert 2 * m <= D
        matched, blocks, free = structure(n, m, D)
        adj = {v: set() for v in range(D + 1)}
        for u in range(1, D + 1):
            adj[0].add(u); adj[u].add(0)
        for t in range(m):
            a, b = 2 * t + 1, 2 * t + 2
            adj[a].add(b); adj[b].add(a)
        for u in range(1, D + 1):
            adj[u].update(blocks[u])
        for v in range(D + 1):
            assert len(adj[v]) == D
        for v in range(D + 1):
            for w in range(n):
                if w != v:
                    cnf.add([e(v, w)] if w in adj[v] else [-e(v, w)])

    if args.tri:
        triangle_gadget(cnf, V, e, n)

    if args.free_case is not None:
        # m=3 only.  The first free vertex f (=44) has at most one neighbour in each block
        # (two in block P(u) would give a C4 with u) and degree exactly 7, so either
        #   case 0: f is adjacent to one vertex of each of the 7 blocks and not to the other
        #           free vertex g, or
        #   case j (1..7): f ~ g and f has one neighbour in each block except P(j).
        # Permuting each block (an element of H, which fixes f and g) we may assume that
        # f's neighbour in a block is the first vertex of that block.
        assert m == 3 and D == 7 and n == 46 and len(free) == 2
        f, g = free
        nb = {blocks[u][0] for u in range(1, D + 1) if u != args.free_case}
        if args.free_case != 0:
            nb.add(g)
        for w in range(n):
            if w != f:
                cnf.add([e(f, w)] if w in nb else [-e(f, w)])

    if args.lex != "none" and not args.no_fix:
        groups = [blocks[u] for u in range(1, D + 1)] + ([free] if len(free) > 1 else [])
        for g in groups:
            if args.lex == "consec":
                pairs = list(zip(g, g[1:]))
            elif args.lex == "first":
                pairs = [(g[0], g[1])]
            else:
                pairs = list(itertools.combinations(g, 2))
            for a, b in pairs:
                cols = [j for j in range(n) if j not in (a, b)]
                A, B = [e(a, j) for j in cols], [e(b, j) for j in cols]
                lex_leq(cnf, B, A) if args.lex_max else lex_leq(cnf, A, B)

    out = sys.stdout
    out.write(f"c gen_c4_46.py n={n} m={m} delta={D} lex={args.lex} exact={args.exact} fix={not args.no_fix}"
              + (" tri=True" if args.tri else "") + (" lex_max=True" if args.lex_max else "")
              + (f" free_case={args.free_case}" if args.free_case is not None else "") + "\n")
    out.write(f"p cnf {cnf.nv} {len(cnf.clauses)}\n")
    for cl in cnf.clauses:
        out.write(" ".join(map(str, cl)) + " 0\n")


if __name__ == "__main__":
    main()
