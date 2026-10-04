# VERIFY: R(C4, K_{1,39}) = 46

This file is the technical companion of `README.md`: the full proof of the reduction, the
soundness proof of the symmetry breaking, what each CNF says, how to reproduce every run,
and the hashes of all formulas and proofs.

Date of the checks: 2026-10-04. Machine: x86_64 Linux (WSL2). Every run used one core under a
2 GB memory limit (systemd scope, MemoryMax=2G).

---

## 1. The statement that is checked

`R(C4, K_{1,39}) <= 46` is equivalent to

> **(S)** There is no simple graph on 46 vertices that contains no 4-cycle `C4` and has
> minimum degree at least 7.

(A 2-colouring of `K_46` is a graph `G` (red) and its complement (blue). Blue contains
`K_{1,39}` iff some vertex has at least 39 blue edges, i.e. red degree at most `45 - 39 = 6`.
So "no red `C4` and no blue `K_{1,39}`" means "`G` is C4-free and `δ(G) >= 7`".)
The lower bound `R(C4, K_{1,39}) >= 46` is known (DS1 lists 46–47), so (S) gives `= 46`.

"Contains a 4-cycle" means: there are four distinct vertices `a, b, c, d` with edges
`ab, bc, cd, da`. Equivalently, two distinct vertices have at least two common neighbours.

## 2. The reduction (hand proof; also checked in Lean, see §7)

Let `G` be C4-free on `n` vertices with `δ(G) >= δ`. Fix a vertex `v` of degree `d` and write
`N = N(v)`.

**Lemma 1 (N(v) spans a matching).** Every `u ∈ N` has at most one neighbour in `N`.
*Proof.* If `u` had neighbours `w ≠ w'` in `N`, then `v–w–u–w'–v` is a 4-cycle. ∎
So the edges inside `N` form a matching; let `m(v)` be its size, `m(v) <= ⌊d/2⌋`, and exactly
`2m(v)` vertices of `N` are matched.

**Lemma 2 (private second neighbourhoods).** For `u ∈ N` let
`P(u) = N(u) \ ({v} ∪ N)`. For distinct `u, u' ∈ N`, `P(u) ∩ P(u') = ∅`.
*Proof.* A common `w` would give the 4-cycle `u–w–u'–v–u` (`w ≠ v` because `w ∉ {v} ∪ N`). ∎

By definition the sets `{v}`, `N`, `P(u)` (`u ∈ N`) are pairwise disjoint. Since
`N(u) ⊆ {v} ∪ (N(u) ∩ N) ∪ P(u)` and `|N(u) ∩ N| <= 1` (Lemma 1),

    |P(u)| >= deg(u) - 1 - [u is matched in N]  >=  δ - 1 - [u is matched],

and therefore

    n  >=  1 + d + Σ_{u∈N} |P(u)|  >=  1 + d + d(δ-1) - 2m(v)  =  1 + dδ - 2m(v).      (*)

**Now `n = 46`, `δ = 7`.**

* *7-regular.* From (*) and `m(v) <= ⌊d/2⌋`: `46 >= 1 + 7d - 2⌊d/2⌋ >= 1 + 6d`. If `d >= 8`
  this is `>= 49`, impossible. Hence every vertex has degree exactly 7.
* *`m(v) ∈ {2, 3}`.* With `d = 7`: `46 >= 50 - 2m(v)`, so `m(v) >= 2`; and `m(v) <= 3`.
* *Exact sizes.* Since all degrees are 7, `|P(u)| = 5` if `u` is matched and `6` if not, and
  `N(u) = {v} ∪ (N(u)∩N) ∪ P(u)` exactly. The vertices outside `{v} ∪ N ∪ ⋃P(u)` ("free"
  vertices) number `46 - (50 - 2m) = 2m - 4`: none if `m = 2`, two if `m = 3`. A free vertex
  is adjacent neither to `v` (not in `N`) nor to any `u ∈ N` (else it would lie in `P(u)`).

**The fixed layout (WLOG).** Pick any vertex as `v` and let `m = m(v) ∈ {2, 3}`. Rename the
vertices by a bijection onto `{0, …, 45}`:

* `v ↦ 0`; the matching edges in `N(v)` ↦ `(1,2), (3,4)` and, if `m = 3`, `(5,6)`; the
  unmatched neighbours ↦ the remaining labels up to 7;
* `P(1), P(2), …, P(7)` ↦ consecutive blocks starting at 8 (sizes 5 for matched, 6 for
  unmatched `u`), in this order; the free vertices ↦ the last labels.

| m | blocks P(1)…P(7) | free |
|---|---|---|
| 3 | 8–12, 13–17, 18–22, 23–27, 28–32, 33–37, 38–43 | 44, 45 |
| 2 | 8–12, 13–17, 18–22, 23–27, 28–33, 34–39, 40–45 | — |

This is a relabelling (the parts partition the vertex set), so the renamed graph is
isomorphic to `G` and still C4-free with `δ >= 7`. In it, **every pair with an endpoint in
`{0,…,7}` has a determined value**: `N(0) = {1..7}`, and for `u ∈ {1..7}`,
`N(u) = {0} ∪ {partner of u} ∪ P(u)`. These are the unit clauses of both CNF families.

Hence: if the CNF "C4-free ∧ δ >= 7 ∧ units of the layout for m" is unsatisfiable for both
`m = 2` and `m = 3`, then (S) holds.

**Every vertex has m(v) = 3 (used only by an optional strengthening).** The `m = 2` formula
is unsatisfiable *without any symmetry breaking* (§5). Since `v` was arbitrary, no vertex
of a counterexample has `m(v) = 2`; so every vertex has `m(v) = 3`, i.e. exactly 6 of its 7
edges lie in a triangle (each edge lies in at most one triangle in a C4-free graph). The
option `--tri` of the independent generator adds the consequence "every vertex has at most
one incident edge that lies in no triangle".

## 3. Soundness of the symmetry breaking (lex-leader)

Let `H` be the group of permutations of `{0,…,45}` that fix `0,…,7` pointwise and map every
block `P(u)` onto itself and the free set onto itself. For `h ∈ H` and a graph `G` in the
fixed layout, `h(G)` is again in the layout (a vertex of block `P(u)` stays in `P(u)`, so its
adjacency to `0..7` is unchanged), and is C4-free with `δ >= 7`. So `H` maps solutions of
the base formula (without lex constraints) to solutions.

Order the edge variables by `(i, j)` lexicographically, `i < j`, and let `x(G)` be the 0/1
vector. Let `G*` be the element of the orbit `{h(G) : h ∈ H}` with lexicographically
**smallest** `x`. For any `σ ∈ H`, `σ(G*)` is in the same orbit, so `x(G*) <=_lex x(σ(G*))`.

**Claim.** For a transposition `σ = (a b)`, `a < b` in the same block,
`x(G) <=_lex x(σ(G))` holds iff `row_a <=_lex row_b`, where `row_v` is the vector
`(x_{v,j})_{j ∉ {a,b}}` in increasing `j`.

*Proof.* `x(σG)_{ij} = x_{σ(i)σ(j)}`. Positions not involving exactly one of `a, b` are
unchanged, and so is `{a,b}`. For `j ∉ {a,b}` the positions `{a,j}` and `{b,j}` swap values.
In the `(i,j)` order, the earliest position at which `x` and `x(σG)` can differ is the one
belonging to the smallest `j` with `x_{a,j} ≠ x_{b,j}`: for `j < a` the positions are
`(j,a) < (j,b)` (row `j < a`); for `j > a` the position `(a,j)` (row `a`) precedes `(b,j)` or
`(j,b)`. At that first position `x` holds `x_{a,j}` and `x(σG)` holds `x_{b,j}`. So
`x <=_lex x(σG)` iff at the first `j` where the rows differ, `x_{a,j} = 0 < 1 = x_{b,j}`. ∎

Therefore `G*` satisfies `row_a <=_lex row_b` for **every** pair `a < b` in a common block or
both free (and a fortiori for any subset of these pairs). Both generators impose such a
subset:

* independent `gen_c4_46.py --lex consec`: consecutive pairs `(a, a+1)` inside each block and
  the free pair, comparing rows over all columns `j ∉ {a, a+1}`;
* original `add_lex.py`: the same consecutive pairs; it compares `x` with `x∘σ` over all 1035
  positions in `(i,j)` order, skipping positions where both sides are the same variable —
  by the Claim this is the same constraint.

Both encode `A <=_lex B` with prefix-equality auxiliaries `e_k`: `e_{k-1} → (¬A_k ∨ B_k)`,
`(e_{k-1} ∧ A_k = B_k) → e_k`. This is equisatisfiable with `A <=_lex B` (if the prefix
equals, `e` is forced true and the next position is constrained; at the first difference
`A_k = 0, B_k = 1`, after which `e` may be false and nothing more is required). The
independent gadget is checked exhaustively for lengths 1–6 in `independent/test_encodings.py`.

So adding the lex constraints never removes the canonical representative of an orbit:
UNSAT with lex ⇒ UNSAT without lex. As an independent confirmation, the `m = 2` case is
also solved and certified with **no** symmetry breaking at all (§5); for `m = 3` see §5.

## 4. The CNF families

### 4.1 Independent generator (`independent/gen_c4_46.py`, written without looking at the earlier scripts)

* variables `1..1035`: edge `{i,j}` (`i<j`, `(i,j)` lexicographic);
* C4: for every 4-set and each of its 3 cyclic orders, `(¬ab ∨ ¬bc ∨ ¬cd ∨ ¬da)`;
* degree: for **every** vertex, "at least 7" (Sinz sequential counter on the negated
  literals). Option `--exact` also adds "at most 7" (justified by 7-regularity, §2);
* the layout of §2 as unit clauses on all pairs touching `0..7`;
* `--lex consec|all|none` (§3); `--tri` (§2, last paragraph).

Gadget tests (`independent/test_encodings.py`): sequential counter for all `n <= 8`, all `k`;
lex for lengths 1–6; triangle gadget on all graphs with 4–6 vertices.

Small-case validation (`independent/validate_small.py`): for minimum degree `D ∈ {4,5,6}` and
`n` in the range where the same counting argument forces `D`-regularity, the structured
formulas (OR over the admissible `m`, with lex none / consec / all) agree with the plain
formula "C4-free, `n` vertices, `δ >= D`" whenever the latter finishes, and every model found
is decoded and checked to be C4-free with `δ >= D`. Results: see §6.

### 4.2 Original generator (`original/c4_struct_gen.py` + `original/add_lex.py`, by the survey researcher)

Copied verbatim from the survey's working files
(also printed in Appendix A of that directory's `science.md`).
Same layout; degree "exactly 7" only for vertices `8..45` (vertices `0..7` are fully fixed);
lex constraints for consecutive pairs in the classes printed on stderr. The command lines are
in §8. The regenerated files match the md5 values recorded in the survey report
(`195bebf7afde…` for m = 2, `8fdfa39dd785…` for m = 3).

## 5. Results

All proofs: CaDiCaL 3.0.1 writes a binary DRAT proof; `drat-trim` (unverified, fast) checks
it and writes an LRAT proof; `cake_lpr` (CakeML, formally verified LRAT checker) checks the
LRAT proof against the original CNF. CaDiCaL and drat-trim are deterministic here: rerunning
gives byte-identical proofs (confirmed for the files below).

| CNF | sha256 (CNF) | cadical | DRAT sha256 (size) | drat-trim | LRAT sha256 (size) | cake_lpr |
|---|---|---|---|---|---|---|
| independent m=2, no symmetry breaking (`--m 2 --lex none`) | `c6c7bb04…` | UNSAT 1 s | `12a3b8f5…` | VERIFIED 1 s | `7ebed88a…` | VERIFIED UNSAT 3 s |
| independent m=2, lex (`--m 2`) | `9eddf1da…` | UNSAT 1 s | `71cce2ca…` (4.1 MB) | VERIFIED 1 s | `ac2a74cf…` (4.4 MB) | VERIFIED UNSAT 2 s |
| independent m=3, lex (`--m 3`) | `4011c662…` | UNSAT 67 s | `f0badad8…` (103 MB) | VERIFIED 174 s | `6482123a…` (482 MB) | VERIFIED UNSAT 22 s |
| original m=2 (`l2.cnf`) | `ecc53f79…` | UNSAT 1 s | `7337383b…` | VERIFIED 1 s | `f0694238…` | VERIFIED UNSAT 3 s |
| original m=3 (`l3.cnf`) | `c421c884…` | UNSAT 61 s | `522dc645…` | VERIFIED 117 s | `53c921ed…` | VERIFIED UNSAT 18 s |

Full hashes are in §9. Negative controls: `cake_lpr` rejects a truncated LRAT proof
("empty clause not derived") and rejects the m=2 proof against the m=3 formula.

Further runs (no proofs kept):

| formula | solver | result |
|---|---|---|
| independent m=3, lex-max instead of lex-min (`--m 3 --lex-max`, sha256 `4d6f312b…`) | CaDiCaL 3.0.1 | UNSAT 66 s |
| independent m=3, lex + "at most 7" (`--m 3 --exact`, `90c3f617…`) | CaDiCaL 3.0.1 | UNSAT 50 s |
| independent m=3, lex (`4011c662…`) | CaDiCaL 2.1.2 / Kissat 4.0.4 | UNSAT 71 s / 40 s |
| original m=3 (`c421c884…`) | CaDiCaL 2.1.2 / Kissat 4.0.4 | UNSAT 103 s / 48 s |

Attempts to do the `m = 3` case **without** (or with much weaker) symmetry breaking did not
finish within the budget (one core, a few hours in total):

| formula | limit | result |
|---|---|---|
| m=3, no lex, `--exact` (`4d4508a5…`) | stopped at 1047 s (12.3 M conflicts) | unknown |
| m=3, no lex, `--exact --tri` (uses "every vertex has m(v)=3", `df1e46e0…`) | 3600 s (24.5 M conflicts) | unknown |
| m=3, no lex, `--exact --tri --free-case 0` (one of 8 elementary WLOG cases for the neighbourhood of free vertex 44, `20b46d26…`) | 900 s | unknown |
| m=3, only the first lex pair of each block (`--lex first`, 8 of the 30 consecutive-pair constraints, `66bf8a34…`) | 1800 s | unknown |

So the `m = 3` case depends on the lex-leader argument of §3. The argument is the standard one
(Crawford, Ginsberg, Luks, Roy 1996: the lexicographically least member of each orbit
satisfies all lex-leader constraints of any set of group elements, for one fixed variable
order) and is spelled out for this formula in §3.

## 6. Small-case validation output

Command: `python3 independent/validate_small.py <cadical 3.0.1> 120 60` (120 s per structured
call, 60 s for the plain formula). `OK` = no two decided answers disagree. Every model found
was decoded and checked (C4-free, minimum degree `>= D`).

```
D=4 n=12 m in []: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=4 n=13 m in [2]: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=4 n=14 m in [2]: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=4 n=15 m in [1, 2]: plain=SATISFIABLE structured(lex none/first/consec/all)=SATISFIABLE/SATISFIABLE/SATISFIABLE/SATISFIABLE OK
D=4 n=16 m in [1, 2]: plain=SATISFIABLE structured(lex none/first/consec/all)=SATISFIABLE/SATISFIABLE/SATISFIABLE/SATISFIABLE OK
D=5 n=20 m in []: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=5 n=21 m in []: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=5 n=22 m in [2]: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=5 n=23 m in [2]: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=5 n=24 m in [1, 2]: plain=UNKNOWN structured(lex none/first/consec/all)=UNKNOWN/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=6 n=30 m in []: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=6 n=31 m in [3]: plain=UNKNOWN structured(lex none/first/consec/all)=UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=6 n=32 m in [3]: plain=UNKNOWN structured(lex none/first/consec/all)=UNKNOWN/UNSATISFIABLE/UNSATISFIABLE/UNSATISFIABLE OK
D=6 n=33 m in [2, 3]: plain=UNKNOWN structured(lex none/first/consec/all)=UNKNOWN/UNKNOWN/UNSATISFIABLE/UNSATISFIABLE OK
D=6 n=34 m in [2, 3]: plain=SATISFIABLE structured(lex none/first/consec/all)=SATISFIABLE/SATISFIABLE/SATISFIABLE/SATISFIABLE OK
D=6 n=35 m in [1, 2, 3]: plain=UNKNOWN structured(lex none/first/consec/all)=SATISFIABLE/SATISFIABLE/SATISFIABLE/SATISFIABLE OK
D=6 n=36 m in [1, 2, 3]: plain=UNKNOWN structured(lex none/first/consec/all)=UNKNOWN/SATISFIABLE/SATISFIABLE/SATISFIABLE OK
```

Consistency with the known Turán numbers `ex(n; C4)` (OEIS A006855): a C4-free graph with
minimum degree `D` on `n` vertices has at least `nD/2` edges, so it is impossible when
`nD/2 > ex(n; C4)`. Every case the structured formulas decide agrees:

| D | n | nD/2 | ex(n; C4) | so |
|---|---|---|---|---|
| 4 | 12 | 24 | 21 | impossible |
| 4 | 13 | 26 | 24 | impossible |
| 4 | 14 | 28 | 27 | impossible |
| 4 | 15 | 30 | 30 | possible |
| 4 | 16 | 32 | 33 | possible |
| 5 | 20 | 50 | 46 | impossible |
| 5 | 21 | 52.5 | 50 | impossible |
| 5 | 22 | 55 | 52 | impossible |
| 5 | 23 | 57.5 | 56 | impossible |
| 5 | 24 | 60 | 59 | impossible |
| 6 | 30 | 90 | 85 | impossible |
| 6 | 31 | 93 | 90 | impossible |
| 6 | 32 | 96 | 92 | impossible |
| 6 | 33 | 99 | 96 | impossible |
| 6 | 34 | 102 | 102 | possible |
| 6 | 35 | 105 | 106 | possible |
| 6 | 36 | 108 | 110 | possible |

All "impossible" rows came out UNSAT and all "possible" rows (D=4: n=15, 16; D=6: n=34, 35, 36)
came out SAT (with lex, and also without lex where it finished). In particular the lex
constraints never removed all solutions of a satisfiable instance.

## 7. Lean

`lean/C4StarReduction.lean` proves, for any `G : SimpleGraph (Fin 46)` that is C4-free (in the
literal form `∀ a b c d, a ≠ c → b ≠ d → ¬(ab ∧ bc ∧ cd ∧ da)`) with `δ >= 7`, and any `v`:
`deg v = 7`, every neighbour of `v` has at most one neighbour in `N(v)`, and the number of
edges inside `N(v)` is 2 or 3. `#print axioms` reports only `propext, Classical.choice,
Quot.sound` (no `sorry`, `native_decide`, or extra axioms). Checked with Lean 4.33.1 and the
Mathlib revision pinned by `formal-conjectures` (`0df444a3…`):

```sh
# from the repository root (after `lake exe cache get`)
lake env lean --threads=2 \
  -DautoImplicit=false -DrelaxedAutoImplicit=false \
  computer-science/ramsey-c4-star/lean/C4StarReduction.lean
```

Not formalised: the relabelling into the fixed layout (the step "these unit clauses are
WLOG") and the correspondence between the Lean graph and the DIMACS variables. Those are
covered by the hand proof in §2 and by the small-case validation.

## 8. Reproduction

Tools used (any recent versions should do):

* CaDiCaL 3.0.1 (built from source);
  cross-checks with CaDiCaL 2.1.2 (shipped with the Lean toolchain) and Kissat 4.0.4
  (`git clone https://github.com/arminbiere/kissat`, commit `8af8e56f`).
* drat-trim (from
  `https://github.com/marijnheule/drat-trim`).
* cake_lpr: `git clone https://github.com/tanyongkiam/cake_lpr` (commit `a36874a8`,
  2026-07-22), `make cake_lpr` (gcc compiles the shipped `cake_lpr.S`). Its built-in example
  prints `s VERIFIED UNSAT`.

```sh
D=computer-science/ramsey-c4-star
W=/path/to/workdir            # proofs go here (up to ~0.5 GB each), not into the repo
export CADICAL=... DRAT_TRIM=... CAKE_LPR=...

# independent formulas
python3 $D/independent/gen_c4_46.py --m 2 --lex none > $W/ind_m2_none.cnf
python3 $D/independent/gen_c4_46.py --m 2            > $W/ind_m2_consec.cnf
python3 $D/independent/gen_c4_46.py --m 3            > $W/ind_m3_consec.cnf
for f in ind_m2_none ind_m2_consec ind_m3_consec; do $D/check_cnf.sh $W/$f.cnf $W; done

# original formulas
cd $W
python3 $D/original/c4_struct_gen.py 46 7 3 > orig_b3.cnf 2> orig_c3.txt
python3 $D/original/add_lex.py orig_b3.cnf 46 "$(cat orig_c3.txt)" > orig_l3.cnf
python3 $D/original/c4_struct_gen.py 46 7 2 > orig_b2.cnf 2> orig_c2.txt
python3 $D/original/add_lex.py orig_b2.cnf 46 "$(cat orig_c2.txt)" > orig_l2.cnf
for f in orig_l2 orig_l3; do $D/check_cnf.sh $W/$f.cnf $W; done

# tests
python3 $D/independent/test_encodings.py
python3 $D/independent/validate_small.py $CADICAL 120 60   # ~1.5 h
```

Wall-clock total for the certified runs above: about 8 minutes on one core.

## 9. Full hashes (sha256)

```
# formulas (regenerated by the commands in §8)
c6c7bb046e556f2bd3458dd346eda90a346318570fba0d8e9ba0be9b47d79df6  ind_m2_none.cnf        (gen_c4_46.py --m 2 --lex none)
9eddf1da80a73c6a744efd1aa8b9cb5c6583c89746800d1a168dc30cdfcc0821  ind_m2_consec.cnf      (gen_c4_46.py --m 2)
4011c6624a87a0dd368e21530c89472c67cb99ff1005ba9d779494316c8fbe11  ind_m3_consec.cnf      (gen_c4_46.py --m 3)
ecc53f79b03e8650f15ab177352ef522b86594b0c82c7f023b1e5e2963c8e828  orig_l2.cnf            (md5 195bebf7afdef9d9d06706477588da8e)
c421c884540f87d1de86377ca85ad10b0b26b46028e4725fc789c1f0401f7381  orig_l3.cnf            (md5 8fdfa39dd7853c4585e6f80574960fbd)
4d6f312b8c3d87b8e14dde8d072fa08c886a7f100230347a723e7aef64162575  ind_m3_lexmax.cnf      (--m 3 --lex-max)
90c3f6170ef83d11ae98bfe451f9cf15ae3082ef3fdffee36fdb328019844e5c  ind_m3_consec_exact.cnf (--m 3 --exact)
66bf8a34c6268d99f8c2dc170511ef41cef9710e1f0f2d877fb76aed6b2f23b5  ind_m3_first.cnf       (--m 3 --lex first)
4d4508a5686831738d2b62663e594749232ee53cb1cb1fe947ab856e833f9380  ind_m3_none_exact.cnf  (--m 3 --lex none --exact)
df1e46e01e24d196df655cb33bd1b65016136b8b7969397b2f2d9c8a19b7b894  ind_m3_none_exact_tri.cnf (--m 3 --lex none --exact --tri)
20b46d26abcd0d4639e1aa4a21f607f930abc358203d3f004011426ea56361ff  fc0.cnf                (--m 3 --lex none --exact --tri --free-case 0)

# proofs (CaDiCaL 3.0.1 binary DRAT; LRAT written by drat-trim -L), sizes in bytes
12a3b8f5558c5b0b5738cbc078b351a81d81c63221cdaee651a7e5ceafc8c6c1  ind_m2_none.drat      4051148
7ebed88a44023628236bc6e239f6c28d78c48249827a4608f9aa485ba15a4e7b  ind_m2_none.lrat      4436057
71cce2cab75f37056b5941358ca9a71f97c651e31b60580210613c42dbda963d  ind_m2_consec.drat    4083588
ac2a74cfd55056dc1262387447db82603b4fbbd7e515f85619b4a862e75a8d41  ind_m2_consec.lrat    4433047
f0badad885fdfc1ce319961b8a9d87b092cad98962bb7620319b3f8e68df3c71  ind_m3_consec.drat    102672318
6482123a8c611f6750bea07aa4615671c5205267b9e3ae04c6313c0d45b528d7  ind_m3_consec.lrat    481707231
7337383bc0bf0f028bf06c877579c7cf1e120f8df89449d38a920a505fdeeafd  orig_l2.drat
f0694238be1e3d904e3edca174b82a00d8144cd00f3cc05781ee52a6adcc8a75  orig_l2.lrat
522dc645468db9c4495e3c921d41314a88edee5077f0e67c6c91c89841de9350  orig_l3.drat          72275807
53c921edbd0a25e4bd5f3428a72b368e4280d426f0d832fe6c301ae48b7b707a  orig_l3.lrat          345551027
```

## 10. Trust base

What one has to believe for `R(C4, K_{1,39}) = 46`:

1. the known lower bound (a 45-vertex C4-free graph with `δ = 6`, cited in DS1);
2. the reduction of §2 (short hand proof; the counting part is also machine-checked in Lean);
3. that the unit clauses express the layout of §2 and the clause sets express "C4-free" and
   "`δ >= 7`" (two generators written independently, gadget tests, small-case validation);
4. the soundness of the lex constraints (§3) for the `m = 3` case — not needed for `m = 2`;
5. `cake_lpr` (formally verified in HOL4/CakeML down to machine code) and its DIMACS parser,
   plus the C compiler/assembler used to build it from `cake_lpr.S`.

The SAT solver and drat-trim are **not** trusted: their output is re-checked by `cake_lpr`.
