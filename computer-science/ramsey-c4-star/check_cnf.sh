#!/usr/bin/env bash
# Solve one CNF with CaDiCaL, keep a DRAT proof, check it with drat-trim (which also emits an
# LRAT proof), then check that LRAT proof with the formally verified checker cake_lpr.
#
#   CADICAL=... DRAT_TRIM=... CAKE_LPR=... ./check_cnf.sh formula.cnf [workdir]
#
# Proof files are large (up to ~0.5 GB) and are written to the work directory, not the repo.
set -euo pipefail
cnf=$1
work=${2:-.}
base=$work/$(basename "${cnf%.cnf}")
: "${CADICAL:=cadical}" "${DRAT_TRIM:=drat-trim}" "${CAKE_LPR:=cake_lpr}"

echo "== $cnf"
sha256sum "$cnf"
"$CADICAL" --version | sed 's/^/cadical /'
t0=$(date +%s)
set +e
"$CADICAL" -q "$cnf" "$base.drat" > "$base.solve.out"
rc=$?
set -e
t1=$(date +%s)
grep '^s ' "$base.solve.out"
echo "cadical exit=$rc time=$((t1 - t0))s"
[ "$rc" = 20 ] || { echo "not UNSAT, stop"; exit 1; }
sha256sum "$base.drat"

"$DRAT_TRIM" "$cnf" "$base.drat" -t 50000 -L "$base.lrat" | tr '\r' '\n' > "$base.dt.out" || true
t2=$(date +%s)
grep -E '^s ' "$base.dt.out"
echo "drat-trim time=$((t2 - t1))s"
grep -q '^s VERIFIED' "$base.dt.out" || { echo "drat-trim failed"; exit 1; }
sha256sum "$base.lrat"

"$CAKE_LPR" --CML_HEAP_SIZE=1700 --CML_STACK_SIZE=100 "$cnf" "$base.lrat" | tee "$base.cake.out"
t3=$(date +%s)
echo "cake_lpr time=$((t3 - t2))s"
grep -q '^s VERIFIED UNSAT' "$base.cake.out" || { echo "cake_lpr failed"; exit 1; }
echo "== $cnf: UNSAT certified (drat-trim + cake_lpr)"
