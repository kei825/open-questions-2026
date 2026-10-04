#!/usr/bin/env python3
"""
Symmetry-free check: for every image E in a list (one line of 27 numbers
per image, as printed by enum_images.c), build the CNF with that image of
D in G/3G fixed and run CaDiCaL on it.  Writes one result line per image:
    <index> <status> <seconds>
and skips indices already present in the log (so it can be resumed).

  run_sweep.py images.txt sweep.log --cadical PATH [--start 0 --step 1]
"""
import argparse
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("images")
    ap.add_argument("log")
    ap.add_argument("--cadical", required=True)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--step", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=3600)
    a = ap.parse_args()
    imgs = [l.split() for l in open(a.images) if l.strip()]
    done = set()
    if os.path.exists(a.log):
        done = {int(l.split()[0]) for l in open(a.log) if l.strip()}
    tmpdir = tempfile.mkdtemp(prefix="sweep", dir=os.path.dirname(os.path.abspath(a.log)))
    for i in range(a.start, len(imgs), a.step):
        if i in done:
            continue
        cnf = os.path.join(tmpdir, "img%d.cnf" % i)
        subprocess.run([sys.executable, os.path.join(HERE, "ds_cnf.py"),
                        "--moduli", "3,9,9", "--v", "243", "--k", "121",
                        "--lam", "60", "--t", "61", "--fix-p", "3",
                        "--fix-image", "[" + ",".join(imgs[i]) + "]",
                        "--out", cnf], check=True, stderr=subprocess.DEVNULL)
        t0 = time.time()
        r = subprocess.run([a.cadical, "-q", "-t", str(a.timeout), cnf],
                           stdout=subprocess.PIPE, text=True)
        dt = time.time() - t0
        st = "UNKNOWN"
        for line in r.stdout.splitlines():
            if line.startswith("s "):
                st = line[2:].strip()
        os.remove(cnf)
        with open(a.log, "a") as f:
            f.write("%d %s %.2f\n" % (i, st, dt))
    os.rmdir(tmpdir)


if __name__ == "__main__":
    main()
