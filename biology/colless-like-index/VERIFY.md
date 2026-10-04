# Verification record — Colless-like index conjecture (Mir–Rosselló–Rotger 2018)

Date: 2026-10-04

## Result

`CollessLikeIndex.lean` compiles with **no errors and no warnings**. It has no `sorry`, `admit`,
`native_decide`, `decide` or `axiom`.

| Theorem | Content |
|---|---|
| `OpenQuestions.CollessLikeIndex.mir_rossello_rotger_conjecture` | `∀ f : ℕ → ℕ, ∀ D : List ℝ → ℝ, IsDissimilarity D → ¬ Sound D (fun n => (f n : ℝ))` |
| `OpenQuestions.CollessLikeIndex.not_sound_rat` | the same for every `f : ℕ → ℚ` (no sign condition) |
| `OpenQuestions.CollessLikeIndex.not_sound_of_fsize_eq` | Lemma 10 of the paper ("only if" part): two non-isomorphic fully symmetric trees with the same f-size make `C_{D,f}` unsound. Here `D` only has to vanish on constant non-empty lists |
| `OpenQuestions.CollessLikeIndex.exists_ws_collision` | for every `g : ℕ → ℤ` there are two different words over `{2,3,4,6}` with the same `g`-size |
| `OpenQuestions.CollessLikeIndex.not_iso_FS` | `FS w₁` and `FS w₂` are not isomorphic when `w₁ ≠ w₂` (letters positive) |
| `OpenQuestions.CollessLikeIndex.sound_iff` | sanity check: fully symmetric trees always have index 0, so `Sound` only asks for the converse (as in the paper) |
| (unnamed `example`) | Example 11 of the paper: `δ_f(FS_{2,2,2,7}) = δ_f(FS_{14,4})` for `f(n) = an² + bn + c` |

`#print axioms` output (taken from the compile log):

```
'OpenQuestions.CollessLikeIndex.mir_rossello_rotger_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.CollessLikeIndex.not_sound_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.CollessLikeIndex.exists_ws_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuestions.CollessLikeIndex.sound_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Environment and command

- Lean 4.33.1 (`leanprover/lean4:v4.33.1`, commit 819816b2e0a3), Mathlib `v4.33.1`. The project used
  is a local clone of google-deepmind/formal-conjectures (same Mathlib).
- Command:

```
# from the repository root (after `lake exe cache get`)
lake env lean --threads=2 -DautoImplicit=false -DrelaxedAutoImplicit=false \
  biology/colless-like-index/CollessLikeIndex.lean
```

- Exit code 0. Wall-clock time 27 s.
- File: 561 lines. SHA-256 `10339380d23b5cb081302e578290713661e2d6ce9b494920ae5354e5d7d94d36`.

## How the definitions match the paper

| Paper (arXiv:1805.01329) | Lean |
|---|---|
| tree = rooted, finite, unordered, **no out-degree-1 nodes** (Materials, "Notations and conventions") | `RTree.node : List RTree → RTree`, with `Valid` (no node with exactly one child). Order of children is removed by `Iso` |
| isomorphism of rooted trees | `Iso`: a bijection `Fin ts.length ≃ Fin us.length` between the children with isomorphic partners |
| `δ_f(T) = Σ_v f(deg v)` | `fsize f` (`f : ℕ → ℝ`), recursion `δ_f(T₁⋆…⋆T_k) = Σ δ_f(T_i) + f(k)` |
| dissimilarity `D` on non-empty real sequences: `D ≥ 0`, symmetric, `D = 0` iff all entries are equal | `IsDissimilarity D` for `D : List ℝ → ℝ`. The value `D []` is never used |
| `C_{D,f}(T) = Σ_{v internal} D(δ_f(T_{v₁}), …, δ_f(T_{v_k}))` (Definition 4) | `colless D f`. Leaves contribute 0 |
| fully symmetric: every internal node has pairwise isomorphic child subtrees | `FullySym` |
| sound: `C_{D,f}(T) = 0 ⇔ T` fully symmetric, for every `T ∈ T*` (Definition 9) | `Sound D f := ∀ T, Valid T → (colless D f T = 0 ↔ FullySym T)` |
| `FS_{n₁,…,n_k}` | `FS [n₁, …, n_k]` |

Remarks:
- The main theorem quantifies over **every** dissimilarity `D`. Inside the proof only one property is
  used: `D` vanishes on constant non-empty lists (`not_sound_of_fsize_eq`). So the result also holds
  without non-negativity, symmetry, or the "only if" part.
- The counterexample tree `node [FS w₁, FS w₂]` has no node with one child. So the result holds
  whether or not out-degree-1 nodes are allowed, and the value `f(1)` never matters.
- The paper also defines `C_{D,f}` for leaf-labelled phylogenetic trees as the value on their shape.
  Labelling the leaves of the counterexample in any way gives the labelled version.

## Proof structure in the Lean file

1. `fsize_FS_cons`: `δ_f(FS (k :: w)) = f(k) + k · δ_f(FS w)` (Example 3 of the paper).
2. `colless_FS`: fully symmetric trees have index 0 when `D` vanishes on constant lists.
3. `HasNode T d k` ("T has a node of out-degree k at depth d") is an inductive predicate.
   `HasNode.of_iso` shows that isomorphisms preserve it. `hasNode_FS_iff` and `hasNode_FS` compute
   it for `FS w`, which gives `not_iso_FS`.
4. `not_sound_of_fsize_eq`: Lemma 10.
5. `ws_bound`: `|δ_g(FS w)| ≤ M (2·prod w − 1)` for letters `≥ 2`, where `M` bounds `|g|` at 0 and
   at the letters.
6. `word n S T`: for `S, T ⊆ {0,…,2n−1}` with `|S| = |T| = n`, letter `i` is
   `(1 + [i∈S])·(2 + [i∈T]) ∈ {2,3,4,6}`. Then `word_prod` gives product `12ⁿ`, `word_inj` gives
   injectivity, and there are `C(2n,n)²` such words.
7. `exists_card_gt`: `2·(2M·12ⁿ) + 1 < C(2n,n)²` for some `n`. This uses Mathlib's
   `Nat.four_pow_le_two_mul_add_one_mul_central_binom` (`4ⁿ ≤ (2n+1)·C(2n,n)`) and
   `tendsto_pow_const_div_const_pow_of_one_lt` (`n²/(4/3)ⁿ → 0`).
8. `exists_ws_collision`: pigeonhole with `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`. The map
   sends `(S,T)` into `Finset.Icc (−2M·12ⁿ) (2M·12ⁿ) ⊂ ℤ`.
9. `not_sound_rat`: clear the denominators of `f(0), f(2), f(3), f(4), f(6)`.
   `mir_rossello_rotger_conjecture` is the special case `f : ℕ → ℕ`.

## Independent numerical checks (Python, 1 GB memory limit, 1 core)

- Example 11: for both `FS_{2,2,2,7}` and `FS_{14,4}`, the coefficients of `(a, b, c)` are
  `(420, 70, 71)`.
- The construction finds real collisions quickly:
  - `f ≡ 1` (node count): `FS_{4,2,6,3}` and `FS_{6,3,2,4}` both have 205 nodes.
  - `f = (3,0,7,1,5,0,2)` on `0..6`: `FS_{4,4,3,3}` and `FS_{4,2,3,6}` both have f-size 521.
- The `n` that the Lean proof's crude bound requires: `n = 20, 26, 29, 38, 72` for
  `M = 1, 5, 10, 100, 10⁶`. Actual collisions appear much earlier (`n = 2` above).
