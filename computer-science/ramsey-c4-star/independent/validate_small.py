#!/usr/bin/env python3
"""Sanity check of gen_c4_46.py on smaller parameters where the answer can also be obtained
without the WLOG structure.

For minimum degree D and n vertices with n <= 1 + (D+1)D - 2*floor((D+1)/2) - 1 every such
graph is D-regular (same counting argument as for D=7, n=46), and every vertex v has
m(v) >= ceil((1 + D*D - n)/2) edges inside N(v), m(v) <= floor(D/2).
We compare
  (a) the plain formula (--no-fix): "C4-free, n vertices, min degree >= D", and
  (b) the OR over the allowed m of the structured formula (with and without lex constraints).
They must agree.  Satisfying assignments are decoded and checked independently.

Usage: validate_small.py <cadical binary> [time limit per call, s] [time limit for the plain formula, s]
"""
import subprocess
import sys
import os
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, "gen_c4_46.py")
CAD = sys.argv[1]
TL = int(sys.argv[2]) if len(sys.argv) > 2 else 600
TL_PLAIN = int(sys.argv[3]) if len(sys.argv) > 3 else TL


def solve(n, D, extra, tl=None):
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        subprocess.run([sys.executable, GEN, "-n", str(n), "--delta", str(D)] + extra, stdout=f, check=True)
        path = f.name
    r = subprocess.run([CAD, "-q", "-t", str(tl or TL), path], capture_output=True, text=True)
    os.unlink(path)
    status = next((l for l in r.stdout.splitlines() if l.startswith("s ")), "s UNKNOWN")
    if status == "s SATISFIABLE":
        vals = set()
        for l in r.stdout.splitlines():
            if l.startswith("v "):
                vals.update(int(t) for t in l.split()[1:] if int(t) > 0)
        check_graph(n, D, vals)
    return status[2:]


def check_graph(n, D, vals):
    idx = 0
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            idx += 1
            if idx in vals:
                adj[i].add(j); adj[j].add(i)
    assert min(len(a) for a in adj) >= D, "decoded graph violates min degree"
    for i in range(n):
        for j in range(i + 1, n):
            assert len(adj[i] & adj[j]) <= 1, "decoded graph contains a C4"


def main():
    cases = [(4, n) for n in range(12, 17)] + [(5, n) for n in range(20, 25)] + [(6, n) for n in range(30, 37)]
    for D, n in cases:
        lim = 1 + (D + 1) * D - 2 * ((D + 1) // 2)
        assert n < lim
        mlo = max(0, -(-(1 + D * D - n) // 2))
        ms = list(range(mlo, D // 2 + 1))
        plain = solve(n, D, ["--m", "0", "--no-fix", "--lex", "none"], TL_PLAIN)
        res = {}
        for lex in ("none", "first", "consec", "all"):
            sts = [solve(n, D, ["--m", str(m), "--lex", lex]) for m in ms if D + 1 + sum(
                D - 2 if u <= 2 * m else D - 1 for u in range(1, D + 1)) <= n]
            res[lex] = "SATISFIABLE" if "SATISFIABLE" in sts else ("UNSATISFIABLE" if all(s == "UNSATISFIABLE" for s in sts) else "UNKNOWN")
        ok = len({plain, *res.values()} - {"UNKNOWN"}) <= 1
        print(f"D={D} n={n} m in {ms}: plain={plain} structured(lex none/first/consec/all)="
              f"{res['none']}/{res['first']}/{res['consec']}/{res['all']} {'OK' if ok else 'MISMATCH'}", flush=True)


if __name__ == "__main__":
    main()
