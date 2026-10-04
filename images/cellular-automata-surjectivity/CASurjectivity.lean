import Mathlib

/-!
# A surjective, truly five-site, non-slice-permutive binary 2D cellular automaton

This file answers (affirmatively) the second open question of

  H. Fukś, A. Skelton, *Classification of two-dimensional binary cellular automata
  with respect to surjectivity*, Proc. CSC-2012, pp. 51–57, arXiv:1208.0771, §6:

  "A related question is whether there exist any truly two-dimensional five-site
   binary rule which is surjective yet not slice permutive?"

## The example

Neighbourhood: the L pentomino `N = {(0,0), (1,0), (2,0), (3,0), (0,1)}`.
Writing `a = x(i,j)`, `b = x(i+1,j)`, `c = x(i+2,j)`, `d = x(i+3,j)`, `e = x(i,j+1)`,
the local rule is `f(a,b,c,d,e) = g(a xor e, b, c, d)` where

* `g(0,b,c,d) = if b then ¬c else (c ∨ d)`,
* `g(1,b,c,d) = if b then (¬c ∧ ¬d) else c`.

Its truth table (input bit index `a + 2b + 4c + 8d + 16e`) is `0x3a3c353c`.

## Proof outline

* `dependsOn_all`, `not_permutive`: finite checks on the 32-row truth table.
  The rule depends on all five sites and is permutive in *no* site, so in
  particular it is not slice permutive (the sliceable sites are `a`, `d`, `e`,
  see `sliceable_iff`).
* `row`: the "bottom row" lemma. Output row `j` only reads input rows `j` and `j+1`.
  For any finite sequence of switch values `e_i` (coming from row `j+1`) and any
  finite target word `y`, there is a row `r` with `f(r_i, r_{i+1}, r_{i+2}, r_{i+3}, e_i) = y_i`.
  This is a statement about an 8-state nondeterministic automaton (states = windows
  `(r_i, r_{i+1}, r_{i+2})`); it follows from four "good" window sets that are closed under
  the subset construction (`good_step`, checked by `decide`).
* `rect`: every finite rectangle of the target has a preimage, built row by row
  from the top down.
* `F_surjective`: compactness of `{0,1}^(ℤ×ℤ)` (Tychonoff) and continuity of the
  global map turn finite preimages into a global preimage.
-/

namespace OpenQuestions.CASurjectivity

/-- A configuration: a black-and-white image on the infinite grid `ℤ × ℤ`. -/
abbrev Config := ℤ × ℤ → Bool

/-! ## General definitions (following Fukś–Skelton §2–3) for five-site rules -/

/-- The global map of the cellular automaton with neighbourhood `N` (a list of five offsets)
and local rule `f`: `F(x)_p = f(x_{p + N 0}, …, x_{p + N 4})`. -/
def globalMap (N : Fin 5 → ℤ × ℤ) (f : (Fin 5 → Bool) → Bool) (x : Config) : Config :=
  fun p => f (fun k => x (p + N k))

/-- `f` is permutive with respect to site `k`: whatever the values at the other sites,
the map `t ↦ f([t, b])` is injective. -/
def Permutive (f : (Fin 5 → Bool) → Bool) (k : Fin 5) : Prop :=
  ∀ v : Fin 5 → Bool, Function.Injective fun t => f (Function.update v k t)

/-- `f` truly depends on site `k`. -/
def DependsOn (f : (Fin 5 → Bool) → Bool) (k : Fin 5) : Prop :=
  ∃ v : Fin 5 → Bool, f (Function.update v k false) ≠ f (Function.update v k true)

/-- Site `k` of `N` can be sliced off: there is a line through `N k` (with rational
coefficients, as in the paper) such that all other sites lie strictly on one side of it.
Equivalently, a linear functional `u` that is strictly positive on `N j - N k` for `j ≠ k`. -/
def Sliceable (N : Fin 5 → ℤ × ℤ) (k : Fin 5) : Prop :=
  ∃ u : ℚ × ℚ, ∀ j : Fin 5, j ≠ k →
    0 < u.1 * (((N j).1 - (N k).1 : ℤ) : ℚ) + u.2 * (((N j).2 - (N k).2 : ℤ) : ℚ)

/-- Slice permutive: permutive with respect to some sliceable site. -/
def SlicePermutive (N : Fin 5 → ℤ × ℤ) (f : (Fin 5 → Bool) → Bool) : Prop :=
  ∃ k, Sliceable N k ∧ Permutive f k

/-- The neighbourhood is contiguous (every site has a lattice neighbour in `N`). -/
def Contiguous (N : Fin 5 → ℤ × ℤ) : Prop :=
  ∀ i, ∃ j, N j - N i ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ))

/-- The neighbourhood is truly two-dimensional (not contained in a line). -/
def NotCollinear (N : Fin 5 → ℤ × ℤ) : Prop :=
  ∃ i j k, ((N j).1 - (N i).1) * ((N k).2 - (N i).2)
    - ((N j).2 - (N i).2) * ((N k).1 - (N i).1) ≠ 0

/-! ## The example -/

/-- The L-pentomino neighbourhood, in the order `a, b, c, d, e`. -/
def nbhd : Fin 5 → ℤ × ℤ := ![(0, 0), (1, 0), (2, 0), (3, 0), (0, 1)]

/-- Auxiliary 4-input function. -/
def g (s b c d : Bool) : Bool :=
  if s then (if b then !c && !d else c) else (if b then !c else c || d)

/-- The local rule `f(a,b,c,d,e) = g(a xor e, b, c, d)`. -/
def rule (a b c d e : Bool) : Bool := g (xor a e) b c d

/-- The local rule as a function of the neighbourhood values. -/
def localRule (v : Fin 5 → Bool) : Bool := rule (v 0) (v 1) (v 2) (v 3) (v 4)

/-- The global map of the example. -/
def F : Config → Config := globalMap nbhd localRule

/-- The truth table of the rule is `0x3a3c353c`. -/
theorem rule_truthTable : ∀ a b c d e : Bool,
    rule a b c d e =
      Nat.testBit 0x3a3c353c (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat) := by
  decide

theorem F_apply (x : Config) (i j : ℤ) :
    F x (i, j) = rule (x (i, j)) (x (i + 1, j)) (x (i + 2, j)) (x (i + 3, j)) (x (i, j + 1)) := by
  simp [F, globalMap, localRule, nbhd]

/-! ### The neighbourhood -/

theorem nbhd_injective : Function.Injective nbhd := by decide

theorem nbhd_contiguous : Contiguous nbhd := by
  unfold Contiguous; decide

theorem nbhd_notCollinear : NotCollinear nbhd := ⟨0, 1, 4, by decide⟩

theorem sliceable_0 : Sliceable nbhd 0 := by
  refine ⟨(1, 1), fun j hj => ?_⟩
  fin_cases j <;> simp [nbhd] at hj ⊢

theorem sliceable_3 : Sliceable nbhd 3 := by
  refine ⟨(-1, 1), fun j hj => ?_⟩
  fin_cases j <;> simp [nbhd] at hj ⊢
  norm_num

theorem sliceable_4 : Sliceable nbhd 4 := by
  refine ⟨(0, -1), fun j hj => ?_⟩
  fin_cases j <;> simp [nbhd] at hj ⊢

theorem not_sliceable_1 : ¬ Sliceable nbhd 1 := by
  rintro ⟨u, hu⟩
  have h0 := hu 0 (by decide)
  have h2 := hu 2 (by decide)
  simp [nbhd] at h0 h2
  linarith

theorem not_sliceable_2 : ¬ Sliceable nbhd 2 := by
  rintro ⟨u, hu⟩
  have h1 := hu 1 (by decide)
  have h3 := hu 3 (by decide)
  simp [nbhd] at h1 h3
  linarith

/-- The sliceable sites are exactly `a`, `d`, `e` (the vertices of the convex hull). -/
theorem sliceable_iff (k : Fin 5) : Sliceable nbhd k ↔ k = 0 ∨ k = 3 ∨ k = 4 := by
  constructor
  · intro h
    fin_cases k
    · left; rfl
    · exact absurd h not_sliceable_1
    · exact absurd h not_sliceable_2
    · right; left; rfl
    · right; right; rfl
  · rintro (rfl | rfl | rfl)
    exacts [sliceable_0, sliceable_3, sliceable_4]

/-! ### Dependence and (non-)permutivity: finite checks -/

theorem dependsOn_all : ∀ k, DependsOn localRule k := by
  intro k
  fin_cases k
  · exact ⟨![false, false, false, true, false], by decide⟩
  · exact ⟨![false, false, false, false, false], by decide⟩
  · exact ⟨![false, false, false, false, false], by decide⟩
  · exact ⟨![false, false, false, false, false], by decide⟩
  · exact ⟨![false, false, false, true, false], by decide⟩

theorem not_permutive_of {k : Fin 5} (v : Fin 5 → Bool)
    (h : localRule (Function.update v k false) = localRule (Function.update v k true)) :
    ¬ Permutive localRule k :=
  fun hk => Bool.false_ne_true (hk v h)

/-- The rule is permutive with respect to no site at all. -/
theorem not_permutive : ∀ k, ¬ Permutive localRule k := by
  intro k
  fin_cases k
  · exact not_permutive_of ![false, false, false, false, false] (by decide)
  · exact not_permutive_of ![false, false, false, true, false] (by decide)
  · exact not_permutive_of ![false, false, false, true, false] (by decide)
  · exact not_permutive_of ![false, false, false, false, true] (by decide)
  · exact not_permutive_of ![false, false, false, false, false] (by decide)

theorem not_slicePermutive : ¬ SlicePermutive nbhd localRule :=
  fun ⟨k, _, hk⟩ => not_permutive k hk

/-! ### The row lemma (an 8-state automaton argument) -/

/-- Four sets of windows `(a, b, c)` = `(r_i, r_{i+1}, r_{i+2})`. As 8-bit masks
(bit `a + 2b + 4c`) they are `153, 102, 169, 86`: the minimal subsets reachable from the
full set in the subset construction. -/
def good (k : Fin 4) (a b c : Bool) : Bool :=
  match k.val with
  | 0 => a == b
  | 1 => a != b
  | 2 => if c then a else a == b
  | _ => !(if c then a else a == b)

/-- Closure of the good sets under the subset construction: for every good set `k` and
every input letter (switch `e`, target `y`), the successor set contains a good set `k'`. -/
theorem good_step : ∀ k : Fin 4, ∀ e y : Bool, ∃ k' : Fin 4, ∀ b c d : Bool,
    good k' b c d = true → ∃ a : Bool, good k a b c = true ∧ rule a b c d e = y := by
  decide

theorem good_nonempty : ∀ k : Fin 4, ∃ a b c : Bool, good k a b c = true := by
  decide

theorem row_aux (e y : ℕ → Bool) : ∀ N : ℕ, ∃ k : Fin 4, ∀ a b c : Bool, good k a b c = true →
    ∃ r : ℕ → Bool, r N = a ∧ r (N + 1) = b ∧ r (N + 2) = c ∧
      ∀ i < N, rule (r i) (r (i + 1)) (r (i + 2)) (r (i + 3)) (e i) = y i := by
  intro N
  induction N with
  | zero =>
    refine ⟨0, fun a b c _ => ⟨fun n => if n = 0 then a else if n = 1 then b else c,
      by simp, by simp, by simp, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨k', hk'⟩ := good_step k (e N) (y N)
    refine ⟨k', fun b c d hbcd => ?_⟩
    obtain ⟨a, ha, hrule⟩ := hk' b c d hbcd
    obtain ⟨r, hr0, hr1, hr2, hr⟩ := hk a b c ha
    refine ⟨fun n => if n = N + 3 then d else r n, ?_, ?_, ?_, ?_⟩
    · show (if N + 1 = N + 3 then d else r (N + 1)) = b
      rw [if_neg (by omega)]; exact hr1
    · show (if N + 1 + 1 = N + 3 then d else r (N + 1 + 1)) = c
      rw [if_neg (by omega)]; exact hr2
    · show (if N + 1 + 2 = N + 3 then d else r (N + 1 + 2)) = d
      rw [if_pos (by omega)]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hEq
      · show rule (if i = N + 3 then d else r i) (if i + 1 = N + 3 then d else r (i + 1))
          (if i + 2 = N + 3 then d else r (i + 2)) (if i + 3 = N + 3 then d else r (i + 3))
          (e i) = y i
        rw [if_neg (show i ≠ N + 3 by omega), if_neg (show i + 1 ≠ N + 3 by omega),
          if_neg (show i + 2 ≠ N + 3 by omega), if_neg (show i + 3 ≠ N + 3 by omega)]
        exact hr i hi
      · rw [hEq]
        show rule (if N = N + 3 then d else r N) (if N + 1 = N + 3 then d else r (N + 1))
          (if N + 2 = N + 3 then d else r (N + 2)) (if N + 3 = N + 3 then d else r (N + 3))
          (e N) = y N
        rw [if_neg (show N ≠ N + 3 by omega), if_neg (show N + 1 ≠ N + 3 by omega),
          if_neg (show N + 2 ≠ N + 3 by omega), if_pos rfl, hr0, hr1, hr2]
        exact hrule

/-- **Row lemma.** For any switch sequence `e` and target `y`, and any length `N`, there is a
row `r` whose image under the switched 1D rule matches `y` on `[0, N)`. -/
theorem row (e y : ℕ → Bool) (N : ℕ) :
    ∃ r : ℕ → Bool, ∀ i < N, rule (r i) (r (i + 1)) (r (i + 2)) (r (i + 3)) (e i) = y i := by
  obtain ⟨k, hk⟩ := row_aux e y N
  obtain ⟨a, b, c, h⟩ := good_nonempty k
  obtain ⟨r, -, -, -, hr⟩ := hk a b c h
  exact ⟨r, hr⟩

/-! ### Finite rectangles have preimages -/

/-- Replace row `j0` of `x'` by the (shifted) row `r`. -/
def stack (r : ℕ → Bool) (x' : Config) (i0 j0 : ℤ) : Config :=
  fun p => if p.2 = j0 then r (p.1 - i0).toNat else x' p

theorem rect (y : Config) (i0 : ℤ) (N : ℕ) : ∀ (M : ℕ) (j0 : ℤ), ∃ x : Config,
    ∀ i < N, ∀ j < M, F x (i0 + i, j0 + j) = y (i0 + i, j0 + j) := by
  intro M
  induction M with
  | zero => intro j0; exact ⟨fun _ => false, fun i _ j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ M ih =>
    intro j0
    obtain ⟨x', hx'⟩ := ih (j0 + 1)
    obtain ⟨r, hr⟩ := row (fun k => x' (i0 + k, j0 + 1)) (fun k => y (i0 + k, j0)) N
    refine ⟨stack r x' i0 j0, ?_⟩
    intro i hi j hj
    rcases j with _ | j
    · -- the bottom row `j0`: use the row lemma
      have hj0 : j0 + ((0 : ℕ) : ℤ) = j0 := by simp
      rw [hj0, F_apply]
      have e : ∀ t : ℕ, stack r x' i0 j0 (i0 + i + t, j0) = r (i + t) := by
        intro t; unfold stack; rw [if_pos rfl]; congr 1; omega
      have e0 := e 0
      have e1 := e 1
      have e2 := e 2
      have e3 := e 3
      simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at e0 e1 e2 e3
      have e4 : stack r x' i0 j0 (i0 + i, j0 + 1) = x' (i0 + i, j0 + 1) := by
        unfold stack; rw [if_neg (by omega)]
      rw [e0, e1, e2, e3, e4]
      exact hr i hi
    · -- the upper rows are unchanged: use the induction hypothesis
      have key := hx' i hi j (by omega)
      have hj1 : j0 + ((j + 1 : ℕ) : ℤ) = j0 + 1 + j := by push_cast; ring
      rw [hj1, F_apply]
      rw [F_apply] at key
      unfold stack
      simp only [show j0 + 1 + (j : ℤ) ≠ j0 by omega, show j0 + 1 + (j : ℤ) + 1 ≠ j0 by omega,
        if_false]
      exact key

/-! ### Compactness: from finite preimages to a global preimage -/

theorem F_continuous_at (p : ℤ × ℤ) : Continuous fun x : Config => F x p := by
  have : (fun x : Config => F x p) =
      (fun v : Fin 5 → Bool => localRule v) ∘ (fun x k => x (p + nbhd k)) := rfl
  rw [this]
  exact continuous_of_discreteTopology.comp (continuous_pi fun k => continuous_apply _)

/-- **Main theorem.** The global map of the example is surjective. -/
theorem F_surjective : Function.Surjective F := by
  intro y
  let box : ℕ → Set (ℤ × ℤ) := fun n =>
    {p | -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n ∧ -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n}
  let t : ℕ → Set Config := fun n => ⋂ p ∈ box n, {x | F x p = y p}
  have hcl : ∀ n, IsClosed (t n) := fun n =>
    isClosed_biInter fun p _ => isClosed_eq (F_continuous_at p) continuous_const
  have hmono : ∀ n, t (n + 1) ⊆ t n := by
    intro n x hx
    simp only [t, box, Set.mem_iInter, Set.mem_ofPred_eq] at hx ⊢
    intro p hp
    exact hx p (by push_cast; omega)
  have hne : ∀ n, (t n).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := rect y (-(n : ℤ)) (2 * n + 1) (2 * n + 1) (-(n : ℤ))
    refine ⟨x, ?_⟩
    simp only [t, box, Set.mem_iInter, Set.mem_ofPred_eq]
    rintro ⟨p1, p2⟩ hp
    simp only at hp
    have h := hx (p1 + n).toNat (by omega) (p2 + n).toNat (by omega)
    have e1 : -(n : ℤ) + ((p1 + n).toNat : ℤ) = p1 := by omega
    have e2 : -(n : ℤ) + ((p2 + n).toNat : ℤ) = p2 := by omega
    rw [e1, e2] at h
    exact h
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    t hmono hne (hcl 0).isCompact hcl
  refine ⟨x, funext fun p => ?_⟩
  have h := Set.mem_iInter.1 hx (p.1.natAbs + p.2.natAbs)
  simp only [t, box, Set.mem_iInter, Set.mem_ofPred_eq] at h
  exact h p (by omega)

/-- **Answer to the Fukś–Skelton question.** There is a truly two-dimensional, contiguous
five-site binary cellular automaton whose rule depends on all five sites, which is
surjective, and which is not slice permutive. -/
theorem answer :
    ∃ (N : Fin 5 → ℤ × ℤ) (f : (Fin 5 → Bool) → Bool),
      Function.Injective N ∧ Contiguous N ∧ NotCollinear N ∧
      (∀ k, DependsOn f k) ∧ Function.Surjective (globalMap N f) ∧ ¬ SlicePermutive N f :=
  ⟨nbhd, localRule, nbhd_injective, nbhd_contiguous, nbhd_notCollinear, dependsOn_all,
    F_surjective, not_slicePermutive⟩

end OpenQuestions.CASurjectivity

#print axioms OpenQuestions.CASurjectivity.answer
#print axioms OpenQuestions.CASurjectivity.F_surjective
#print axioms OpenQuestions.CASurjectivity.not_permutive
#print axioms OpenQuestions.CASurjectivity.sliceable_iff
#print axioms OpenQuestions.CASurjectivity.rule_truthTable
