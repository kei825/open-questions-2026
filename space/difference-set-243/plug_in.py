#!/usr/bin/env python3
"""Soundness test of the encoding on a KNOWN difference set: append unit
clauses fixing the orbit variables to a given set D and write a new CNF.
If the encoding is sound (every t-invariant difference set extends to a
model), the result must be SAT.

  plug_in.py base.cnf base.json '<JSON list of elements>' out.cnf
"""
import json
import sys

base, meta, dset, out = sys.argv[1:5]
meta = json.load(open(meta))
D = {tuple(g) for g in json.loads(dset if dset.lstrip().startswith("[")
                                     else open(dset).read())}
units = []
for i, orb in enumerate(meta["orbits"]):
    inside = [tuple(g) in D for g in orb]
    if all(inside):
        units.append(i + 1)
    elif not any(inside):
        units.append(-(i + 1))
    else:
        sys.exit("D is not a union of multiplier orbits")
lines = open(base).read().splitlines()
hdr = next(i for i, l in enumerate(lines) if l.startswith("p cnf"))
_, _, nv, nc = lines[hdr].split()
lines[hdr] = "p cnf %s %d" % (nv, int(nc) + len(units))
with open(out, "w") as f:
    f.write("\n".join(lines) + "\n")
    for u in units:
        f.write("%d 0\n" % u)
print("fixed %d orbit variables (%d in D)" % (len(units), sum(u > 0 for u in units)))
