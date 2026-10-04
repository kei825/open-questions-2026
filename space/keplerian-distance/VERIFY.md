# VERIFY — Keplerian distance, 12 critical points

Run on 2026-10-04 on a desktop PC (WSL2, Linux 6.6, x86-64). All Python runs used 1 core under
a 1 GB memory limit; Lean used `--threads=2` under `MEM=6G`.

| tool | version |
|---|---|
| Lean | 4.33.1 (commit 819816b2e0a3) |
| Mathlib | v4.33.1 (git 0df444a360ea), from the Lake project a local clone of google-deepmind/formal-conjectures (same Mathlib) |
| Python | 3.12.3, sympy 1.14.0, mpmath 1.3.0, numpy 2.5.3 |

`KeplerianDistance.lean` sha256 prefix: `9a646f2675e44c02` (654 lines).

## 1. Lean 4 proof (existence of 12 distinct critical points, 2 of them intersections)

```sh
# from the repository root (after `lake exe cache get`)
lake env lean --threads=2 \
  -DautoImplicit=false -DrelaxedAutoImplicit=false \
  space/keplerian-distance/KeplerianDistance.lean
```

Output (the file ends with `#print axioms`; there are no errors and no warnings):

```
'OpenQuestions.KeplerianDistance.twelve_critical_points' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Wall time: 43.91 s. Forbidden constructs:

```sh
grep -nE 'sorry|admit|native_decide|^axiom| axiom ' KeplerianDistance.lean   # -> no output
```

## 2. Implementation 1: exact Sturm count (integers and fractions only)

```sh
cd space/keplerian-distance/verify
python3 sturm_count.py
```

```
p1 = 1  e1 = 493/500  p2 = 113/500  e2 = 4983/5000  tan(omega/2) = 89/4000
cos omega = 15992079/16007921  sin omega = 712000/16007921
deg F12 = 12 ; F12 = (1+t^2) * F with deg F = 10
Sturm sequence length: 11 ; number of distinct real roots of F: 10
gcd(F, F') has degree 0 (F is squarefree)
F(0) = nonzero (so sin f1 != 0, i.e. mu != 0, at every root)
gcd(F, beta*den) has degree 0 (so beta != 0 at every root)
  f1 = 0: delta = 49414890153519/1250618828125000  (nonzero: no critical point with X1 != X2 there)
  f1 = pi: delta = -2455587519/1250618828125000  (nonzero: no critical point with X1 != X2 there)
Iq(t) = (6190173925361/4001980250000)*t^0 + (7095792/80039605)*t^1 + (4891501639/4001980250000)*t^2
discriminant of Iq > 0: True ; leading coefficient nonzero: True
gcd(F, Iq) has degree 0 (no root of F is an intersection)
=> exactly 10 non-intersection critical points + exactly 2 intersections = 12 critical points

Isolating intervals of relative width < 1e-40 with exact rational endpoints, t = tan(f1/2)
(lower endpoint shown, truncated to 25 decimals):
  F  root: t = -38.1341086179190596805185676 ...
  F  root: t = -9.7788974853126782712775826 ...
  F  root: t = -7.5334335460779580562599346 ...
  F  root: t = -0.0130350636225232620644832 ...
  F  root: t = 0.0445446006620978110694851 ...
  F  root: t = 13.8510940352028300960288348 ...
  F  root: t = 23.7116046896652323096060724 ...
  F  root: t = 38.4148773211412944535881696 ...
  F  root: t = 198.1736104506165534083445144 ...
  F  root: t = 1998077.2527447613575638317045059 ...
  Iq root: t = -43.3172462605872197762888449 ...
  Iq root: t = -29.2145908283055557127719693 ...
the 12 isolating intervals are pairwise disjoint
each interval of the Lean proof contains exactly one of these roots
wrote roots.txt;  elapsed 0.7 s
```

Wall time: 0.77 s.

## 3. Implementation 2: interval Krawczyk branch-and-prune on the whole torus

Independent of implementation 1: it differentiates `d²` itself (no use of the paper's (38)–(41)).
The decision procedure uses only dyadic rationals (Python integers). mpmath is used only to print the angles.

```sh
python3 krawczyk_torus.py
```

```
chart (f1 0, f2 0): 1 certified zeros; boxes so far 211; 0 s
chart (f1 0, f2 pi): 1 certified zeros; boxes so far 746; 1 s
chart (f1 pi, f2 0): 1 certified zeros; boxes so far 859; 1 s
chart (f1 pi, f2 pi): 9 certified zeros; boxes so far 6696; 4 s

Certified critical points (t, s are the chart coordinates; enclosures have width < 1e-40):
  f1 =    -177.355067124183 deg   f2 =     -179.90430869007 deg   min
  f1 =    -176.995726204402 deg   f2 =    -179.338039149893 deg   saddle
  f1 =    -176.079122341806 deg   f2 =    -178.628363907693 deg   min
  f1 =    -168.322343409411 deg   f2 =     174.575166122704 deg   saddle
  f1 =    -164.877341987326 deg   f2 =    -172.907587177142 deg   saddle
  f1 =    -1.49362367104119 deg   f2 =    -6.59139961174004 deg   min
  f1 =     5.10106313979102 deg   f2 =     -179.99993444301 deg   max
  f1 =      171.74122399525 deg   f2 =    -176.249342880565 deg   saddle
  f1 =     175.170141563774 deg   f2 =     177.985564257976 deg   saddle
  f1 =     177.017674050525 deg   f2 =     179.048349137723 deg   min
  f1 =     179.421766671313 deg   f2 =     179.845573930691 deg   saddle
  f1 =     179.999942649085 deg   f2 =    -5.09798904805397 deg   max

TOTAL: 12 critical points on the torus; types {'min': 4, 'max': 2, 'saddle': 6}; unclassified: 0
Euler characteristic check: min - saddle + max = 0 (torus: 0)
boxes examined: 6696; elapsed 4.0 s
```

Wall time: 4.67 s.

## 4. Table and figures

```sh
python3 make_figures.py
```

```
| # | type | intersection? | f₁ (deg) | f₂ (deg) | u₁ (deg) | u₂ (deg) | d |
|---|---|---|---|---|---|---|---|
| 1 | minimum | yes | -177.3550671 | -179.9043087 | 210.7479203 | 182.3185657 | 0 |
| 2 | minimum | yes | -176.0791223 | -178.6283639 | 224.3600686 | 212.3524426 | 0 |
| 3 | saddle | no | -176.9957262 | -179.3380391 | 214.6901736 | 195.9378639 | 0.2456321306 |
| 4 | minimum | no | -1.493623671 | -6.591399612 | 359.8745877 | 359.7276985 | 0.3901875046 |
| 5 | saddle | no | -164.877342 | -172.9075872 | 295.37248 | 292.6821105 | 1.991839745 |
| 6 | minimum | no | 177.0176741 | 179.0483491 | 145.5483171 | 157.2421732 | 5.324456206 |
| 7 | saddle | no | 175.1701416 | 177.9855643 | 126.6590866 | 133.8479943 | 5.377161697 |
| 8 | saddle | no | 179.4217667 | 179.8455739 | 173.1212374 | 176.2591298 | 5.958788711 |
| 9 | saddle | no | -168.3223434 | 174.5751661 | 281.2252745 | 82.11399649 | 7.328247738 |
| 10 | saddle | no | 171.741224 | -176.2493429 | 98.61636322 | 256.8600182 | 10.4136729 |
| 11 | maximum | no | 5.10106314 | -179.9999344 | 0.4285683242 | 180.0015886 | 66.97460844 |
| 12 | maximum | no | 179.9999426 | -5.097989048 | 179.9993169 | 359.789487 | 71.54187578 |
wrote orbits.svg, torus.svg, verify/table.md
```

Wall time: 0.48 s. Output: `../orbits.svg`, `../torus.svg`, `table.md`
(presentation only, floating point allowed).

## Agreement

* The 12 angles from implementation 2 match those from the roots of implementation 1. Example:
  f₁ = 179.421766671313° and f₂ = 179.845573930691° from Krawczyk; f₁ = 179.4217667° and f₂ = 179.8455739° in the table.
* `sturm_count.py` checks that each of the 12 rational intervals used in the Lean proof contains
  exactly one of the exactly isolated roots.
* The types (4 minima, 2 maxima, 6 saddles) agree between the certified interval Hessians (implementation 2)
  and the 40-digit Hessians of `make_figures.py`.
