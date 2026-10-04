#!/bin/bash
# Control experiments: the same generator (ds_cnf.py) and solver on cases
# whose answer is known (La Jolla Difference Set Repository).
#   CADICAL=/path/to/cadical PY=python3 ./controls.sh WORKDIR
# Prints one line per case: name, expected, obtained (+ direct check of models).
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:?workdir}
CAD=${CADICAL:?set CADICAL}
PY=${PY:-python3}
TL=${TL:-3600}
mkdir -p "$W" && cd "$W" || exit 1

run() {   # name expected lam timeout -- generator args
  local name=$1 exp=$2 lam=$3 tl=$4; shift 4
  "$PY" "$HERE/ds_cnf.py" "$@" --out "$name.cnf" --meta "$name.json" 2> "$name.gen"
  local t0=$(date +%s.%N)
  "$CAD" -q -t "$tl" "$name.cnf" > "$name.out"
  local dt=$(echo "$(date +%s.%N) - $t0" | bc)
  local st=$(grep '^s ' "$name.out" | cut -c3-); st=${st:-UNKNOWN}
  local chk=""
  if [ "$st" = SATISFIABLE ]; then
    chk=" | model: $("$PY" "$HERE/check_model.py" --meta "$name.json" --model "$name.out" --lam "$lam" | head -1)"
  fi
  printf "%-26s expected %-6s got %-15s %8.1fs  [%s]%s\n" "$name" "$exp" "$st" "$dt" \
    "$(tail -1 "$name.gen" | sed 's/^wrote [^:]*: //')" "$chk"
}

# small cyclic difference sets, multiplier acting nontrivially
run "(7,3,1)[7]"            Yes 1 60 --moduli 7  --v 7  --k 3 --lam 1 --t 2
run "(11,5,2)[11]"          Yes 2 60 --moduli 11 --v 11 --k 5 --lam 2 --t 3
run "(13,4,1)[13]"          Yes 1 60 --moduli 13 --v 13 --k 4 --lam 1 --t 3
run "(21,5,1)[21]"          Yes 1 60 --moduli 21 --v 21 --k 5 --lam 1 --t 2
run "(19,9,4)[19]"          Yes 4 60 --moduli 19 --v 19 --k 9 --lam 4 --t 5
# (27,13,6): the same shape of problem one size down (multiplier 7 = n)
run "(27,13,6)[3,3,3]"      Yes 6 60 --moduli 3,3,3 --v 27 --k 13 --lam 6 --t 7
run "(27,13,6)[3,9]"        No  6 60 --moduli 3,9   --v 27 --k 13 --lam 6 --t 7
run "(27,13,6)[27]"         No  6 60 --moduli 27    --v 27 --k 13 --lam 6 --t 7
# (243,121,60) in the other six abelian groups of order 243
run "(243,121,60)[3,3,3,9]" No  60 $TL --moduli 3,3,3,9 --v 243 --k 121 --lam 60 --t 61
run "(243,121,60)[3,3,27]"  No  60 $TL --moduli 3,3,27  --v 243 --k 121 --lam 60 --t 61
run "(243,121,60)[9,27]"    No  60 $TL --moduli 9,27    --v 243 --k 121 --lam 60 --t 61
run "(243,121,60)[3,81]"    No  60 $TL --moduli 3,81    --v 243 --k 121 --lam 60 --t 61
run "(243,121,60)[243]"     No  60 $TL --moduli 243     --v 243 --k 121 --lam 60 --t 61
run "(243,121,60)[3^5]"     Yes 60 $TL --moduli 3,3,3,3,3 --v 243 --k 121 --lam 60 --t 61

# soundness of the encoding on known difference sets: fixing D to a known
# example (La Jolla data, known_sets.json) must give SAT
plug() {  # name base key lam
  local name=$1 base=$2 key=$3 lam=$4
  "$PY" -c "import json,sys; print(json.dumps(json.load(open('$HERE/known_sets.json'))[sys.argv[1]]))" "$key" > "$name.set"
  "$PY" "$HERE/check_model.py" --moduli "$("$PY" -c "import json; print(','.join(map(str,json.load(open('$base.json'))['moduli'])))")" --set "$(cat "$name.set")" --lam "$lam" | sed "s/^/$name known set: /"
  "$PY" "$HERE/plug_in.py" "$base.cnf" "$base.json" "$name.set" "$name.cnf" > /dev/null
  printf "%-26s expected SAT    got %s\n" "$name" "$("$CAD" -q "$name.cnf" | grep '^s ' | cut -c3-)"
}
plug "plug(27,13,6)[3,3,3]"   "(27,13,6)[3,3,3]"   "DS(27,13,6,[3,3,3])"        6
plug "plug(243,121,60)[3^5]"  "(243,121,60)[3^5]"  "DS(243,121,60,[3,3,3,3,3])" 60
