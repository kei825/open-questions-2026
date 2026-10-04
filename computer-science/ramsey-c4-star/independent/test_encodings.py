#!/usr/bin/env python3
"""Exhaustive tests of the two gadgets used by gen_c4_46.py.

For every assignment of the primary literals we check that the gadget is satisfiable
(over its auxiliary variables)  <=>  the intended predicate holds.  Satisfiability over the
auxiliaries is decided by brute force when there are at most 10 of them, otherwise by a SAT
call (python-sat, Minisat22) under assumptions.

Run with:  python3 test_encodings.py  (needs python-sat)
"""
import itertools
from gen_c4_46 import CNF, at_most_seq, lex_leq, triangle_gadget


def satisfiable_with(cnf, fixed):
    aux = [v for v in range(1, cnf.nv + 1) if v not in fixed]
    if len(aux) <= 10:
        for bits in itertools.product([False, True], repeat=len(aux)):
            val = dict(fixed)
            val.update(zip(aux, bits))
            if all(any((l > 0) == val[abs(l)] for l in cl) for cl in cnf.clauses):
                return True
        return False
    from pysat.solvers import Minisat22
    with Minisat22(bootstrap_with=cnf.clauses) as s:
        return s.solve(assumptions=[v if b else -v for v, b in fixed.items()])


def test_at_most():
    for n in range(1, 9):
        for k in range(0, n + 1):
            for signs in ([1] * n, [(-1) ** i for i in range(n)]):
                cnf = CNF()
                xs = [cnf.new() * s for s in signs]
                at_most_seq(cnf, xs, k)
                prim = [abs(x) for x in xs]
                for bits in itertools.product([False, True], repeat=n):
                    fixed = dict(zip(prim, bits))
                    true_lits = sum(1 for x in xs if (x > 0) == fixed[abs(x)])
                    assert satisfiable_with(cnf, fixed) == (true_lits <= k), (n, k, signs, bits)
        print(f"at_most_seq ok n={n} k=0..{n}", flush=True)


def test_lex():
    for L in range(1, 7):
        cnf = CNF()
        A = [cnf.new() for _ in range(L)]
        B = [cnf.new() for _ in range(L)]
        lex_leq(cnf, A, B)
        for bits in itertools.product([False, True], repeat=2 * L):
            fixed = dict(zip(A + B, bits))
            a = [int(fixed[x]) for x in A]
            b = [int(fixed[x]) for x in B]
            assert satisfiable_with(cnf, fixed) == (a <= b), (L, a, b)
        print(f"lex_leq ok L={L}", flush=True)


def test_triangle():
    for n in (4, 5, 6):
        cnf = CNF()
        V = {(i, j): cnf.new() for i in range(n) for j in range(i + 1, n)}
        e = lambda i, j: V[(min(i, j), max(i, j))]
        triangle_gadget(cnf, V, e, n)
        for bits in itertools.product([False, True], repeat=len(V)):
            adj = {p for p, b in zip(V, bits) if b}
            ed = lambda i, j: (min(i, j), max(i, j)) in adj
            ok = all(sum(1 for u in range(n) if u != v and ed(u, v)
                         and not any(ed(u, w) and ed(v, w) for w in range(n) if w not in (u, v))) <= 1
                     for v in range(n))
            assert satisfiable_with(cnf, dict(zip(V.values(), bits))) == ok, (n, adj)
        print(f"triangle_gadget ok n={n}", flush=True)


if __name__ == "__main__":
    test_at_most()
    test_lex()
    test_triangle()
    print("all gadget tests passed")
