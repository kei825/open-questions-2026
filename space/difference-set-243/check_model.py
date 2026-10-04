#!/usr/bin/env python3
"""Decode a SAT model produced for a ds_cnf.py instance and check, by
counting all differences directly, whether it is a (v,k,lambda) difference
set.  Also usable on an explicit set (--set JSON) to test a known example.

  check_model.py --meta x.json --model solver_output.txt --lam 60
  check_model.py --moduli 3,3,3 --set '[[0,0,0],...]' --lam 6
"""
import argparse
import itertools
import json
import sys
from collections import Counter


def is_difference_set(D, moduli, lam):
    D = [tuple(d) for d in D]
    assert len(set(D)) == len(D)
    cnt = Counter()
    for x in D:
        for y in D:
            if x != y:
                cnt[tuple((a - b) % m for a, b, m in zip(x, y, moduli))] += 1
    nonzero = [g for g in itertools.product(*[range(m) for m in moduli])
               if any(g)]
    return all(cnt[g] == lam for g in nonzero), len(D)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--meta")
    ap.add_argument("--model")
    ap.add_argument("--moduli")
    ap.add_argument("--set")
    ap.add_argument("--lam", type=int, required=True)
    a = ap.parse_args()
    if a.set:
        moduli = [int(x) for x in a.moduli.split(",")]
        D = json.loads(a.set)
    else:
        meta = json.load(open(a.meta))
        moduli = meta["moduli"]
        true = set()
        for line in open(a.model):
            if line.startswith("v "):
                true.update(int(x) for x in line[2:].split() if int(x) > 0)
        D = [g for i, orb in enumerate(meta["orbits"]) if (i + 1) in true
             for g in orb]
    ok, size = is_difference_set(D, moduli, a.lam)
    print("|D| = %d, difference set with lambda=%d: %s" % (size, a.lam, ok))
    if a.model and ok:
        print("D =", json.dumps(sorted(D)))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
