/-
# Local minimizers of the energy on paths and cycles need not be global minimizers

N. Bushaw, B. Cody, C. Leffler, "Sets of vertices with extremal energy",
arXiv:2407.18785 (Discrete Math. 348 (2025) 114466), Question 5.3:

> Suppose g is a strictly decreasing convex function (or for concreteness take g(r) = 1/r)
> and let G be either a path P_n or a cycle C_n on n vertices. Is every local minimizer of
> E_g on G also a global minimizer of E_g? If A is a set of vertices of G, does it follow
> that Descending Local Search(G, E_g, A) is a minimizer of E_g?

Definitions from the paper (Definitions 1.1, 1.2 and the algorithm on p. 4):
* `E_g(A) = ∑_{{u,v} ⊆ A} g(d(u,v))`, with `d` the graph distance;
* `B` is a *perturbation* of `A` if `B = (A \ {u}) ∪ {v}` with `u ∈ A`, `v ∉ A`, `uv` an edge;
* `A` is a *local minimizer* if `E_g(A) = min {E_g(B) : B a perturbation of A}`;
* `A` is a (global) *minimizer* if `E_g(A) = min {E_g(B) : |B| = |A|}`.

The paper says "clearly every minimizer is a local minimizer", and its Descending Local
Search stops exactly when `E_g(L(i)) ≥ E_g(X)` for every perturbation; so the intended
meaning of "local minimizer" is `E_g(A) ≤ E_g(B)` for all perturbations `B`
(`IsLocalMin`).  We refute the question in this reading with *strict* local minimizers
(every perturbation has strictly larger energy), and also in the literal reading
"`E_g(A)` equals the minimum over the perturbations" (`IsLocalMinLiteral`).

Answers (all for `g(r) = 1/r` unless stated otherwise):
* cycle `C_32`, `A = {0, 7, 16, 23}`: strict local minimizer, not a minimizer
  (`cycle32_counterexample`);
* path `P_13`, `A = {0, 1, 3, 6, 8, 10, 12}`: strict local minimizer, not a minimizer
  (`path13_counterexample`);
* path `P_10`, `A = {0, 1, 3, 6, 8, 9}`: local minimizer in the literal reading, not a
  minimizer (`path10_literal_counterexample`);
* cycle `C_8` with the strictly decreasing, strictly convex `g = (57, 31, 10, 0)`,
  `A = {0, 1, 4, 5}` (`cycle8_general_g_counterexample`);
* the infinite family `C_{4x}`, `A = {0, x-1, 2x, 3x-1}`, `x ≥ 8`
  (`cycle_family_counterexample`);
* Descending Local Search started at any of these `A` returns `A` (`dls_of_isLocalMin`,
  `cycle32_dls`, `path13_dls`).
-/
import Mathlib

namespace OpenQuestions.MaximallyEvenEnergy

open Finset

/-! ## Definitions -/

/-- Distance in the path `P_n` with vertices `0, 1, …, n-1`: `|u - v|`. -/
def pathDist {n : ℕ} (u v : Fin n) : ℕ := ((u : ℕ) - v) + ((v : ℕ) - u)

/-- Distance in the cycle `C_n` with vertices `0, 1, …, n-1`: `min (|u - v|, n - |u - v|)`. -/
def cycleDist {n : ℕ} (u v : Fin n) : ℕ := min (pathDist u v) (n - pathDist u v)

/-- The energy `E_g(A) = ∑_{u < v in A} g (d u v)`. -/
def energy {n : ℕ} (g : ℕ → ℚ) (d : Fin n → Fin n → ℕ) (A : Finset (Fin n)) : ℚ :=
  ∑ u ∈ A, ∑ v ∈ A, if u < v then g (d u v) else 0

/-- `g(r) = 1/r`. -/
def inv (r : ℕ) : ℚ := 1 / r

/-- `B` is a perturbation of `A`: one vertex of `A` moves to an adjacent vertex outside `A`
(adjacent = at graph distance `1`). -/
def IsPerturbation {n : ℕ} (d : Fin n → Fin n → ℕ) (A B : Finset (Fin n)) : Prop :=
  ∃ u ∈ A, ∃ v, v ∉ A ∧ d u v = 1 ∧ B = insert v (A.erase u)

/-- Local minimizer (Definition 1.2, intended reading): no perturbation has smaller value. -/
def IsLocalMin {n : ℕ} (d : Fin n → Fin n → ℕ) (F : Finset (Fin n) → ℚ) (A : Finset (Fin n)) :
    Prop :=
  ∀ B, IsPerturbation d A B → F A ≤ F B

/-- Strict local minimizer: every perturbation has strictly larger value. -/
def IsStrictLocalMin {n : ℕ} (d : Fin n → Fin n → ℕ) (F : Finset (Fin n) → ℚ)
    (A : Finset (Fin n)) : Prop :=
  ∀ B, IsPerturbation d A B → F A < F B

/-- Local minimizer, literal reading of Definition 1.2: `F A` *equals* the minimum of `F`
over the perturbations of `A`. -/
def IsLocalMinLiteral {n : ℕ} (d : Fin n → Fin n → ℕ) (F : Finset (Fin n) → ℚ)
    (A : Finset (Fin n)) : Prop :=
  (∀ B, IsPerturbation d A B → F A ≤ F B) ∧ ∃ B, IsPerturbation d A B ∧ F B = F A

/-- Global minimizer (Definition 1.1). -/
def IsGlobalMin {n : ℕ} (F : Finset (Fin n) → ℚ) (A : Finset (Fin n)) : Prop :=
  ∀ B : Finset (Fin n), B.card = A.card → F A ≤ F B

lemma IsStrictLocalMin.isLocalMin {n : ℕ} {d : Fin n → Fin n → ℕ} {F : Finset (Fin n) → ℚ}
    {A : Finset (Fin n)} (h : IsStrictLocalMin d F A) : IsLocalMin d F A :=
  fun B hB => (h B hB).le

lemma not_isGlobalMin_of_lt {n : ℕ} {F : Finset (Fin n) → ℚ} {A B : Finset (Fin n)}
    (hcard : B.card = A.card) (hlt : F B < F A) : ¬ IsGlobalMin F A :=
  fun h => absurd (h B hcard) (not_le.mpr hlt)

/-! ## Descending Local Search

The algorithm of the paper (p. 4): with `X = A`, let `L` be the list of all perturbations
of `X`; if `F (L i) < F X` for some `i`, move to `L j` for the least such `j` and repeat;
otherwise return `X`.  We model "the list of all perturbations" by an arbitrary function
`L` whose lists consist of perturbations (any order), and add a fuel parameter `k` (the
real algorithm terminates since `F` strictly decreases at each step). -/

/-- Descending Local Search with fuel `k`. -/
def dls {n : ℕ} (L : Finset (Fin n) → List (Finset (Fin n))) (F : Finset (Fin n) → ℚ) :
    ℕ → Finset (Fin n) → Finset (Fin n)
  | 0, X => X
  | k + 1, X =>
    match (L X).find? (fun B => decide (F B < F X)) with
    | some B => dls L F k B
    | none => X

/-- Started at a local minimizer, Descending Local Search returns its input (for any
ordering of the perturbations and any amount of fuel). -/
theorem dls_of_isLocalMin {n : ℕ} {d : Fin n → Fin n → ℕ} {F : Finset (Fin n) → ℚ}
    {A : Finset (Fin n)} (L : Finset (Fin n) → List (Finset (Fin n)))
    (hL : ∀ B ∈ L A, IsPerturbation d A B) (hA : IsLocalMin d F A) (k : ℕ) :
    dls L F k A = A := by
  cases k with
  | zero => rfl
  | succ k =>
    have hnone : (L A).find? (fun B => decide (F B < F A)) = none := by
      rw [List.find?_eq_none]
      intro B hB
      simpa using hA B (hL B hB)
    simp only [dls, hnone]

/-! ## Four-point sets -/

lemma energy_four_val {n : ℕ} (g : ℕ → ℚ) (d : Fin n → Fin n → ℕ) {a b c e : Fin n}
    (h₁ : a < b) (h₂ : b < c) (h₃ : c < e) {r1 r2 r3 r4 r5 r6 : ℕ}
    (e₁ : d a b = r1) (e₂ : d a c = r2) (e₃ : d a e = r3) (e₄ : d b c = r4)
    (e₅ : d b e = r5) (e₆ : d c e = r6) :
    energy g d {a, b, c, e} = g r1 + g r2 + g r3 + g r4 + g r5 + g r6 := by
  have h₄ := h₁.trans h₂
  have h₅ := h₂.trans h₃
  have h₆ := h₄.trans h₃
  rw [← e₁, ← e₂, ← e₃, ← e₄, ← e₅, ← e₆]
  simp [energy, sum_insert, h₁, h₂, h₃, h₄, h₅, h₆, h₁.ne, h₂.ne, h₃.ne, h₄.ne, h₅.ne, h₆.ne,
    not_lt_of_gt h₁, not_lt_of_gt h₂, not_lt_of_gt h₃, not_lt_of_gt h₄, not_lt_of_gt h₅,
    not_lt_of_gt h₆]
  ring

lemma card_four {n : ℕ} {a b c e : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < e) :
    ({a, b, c, e} : Finset (Fin n)).card = 4 := by
  have h₄ := h₁.trans h₂
  have h₅ := h₂.trans h₃
  have h₆ := h₄.trans h₃
  rw [card_insert_of_notMem (by simp [h₁.ne, h₄.ne, h₆.ne]),
    card_insert_of_notMem (by simp [h₂.ne, h₅.ne]),
    card_insert_of_notMem (by simp [h₃.ne]), card_singleton]

/-! ## The cycle `C_32` -/

/-- `{0, 7, 16, 23}` in `C_32`. -/
def A32 : Finset (Fin 32) := {0, 7, 16, 23}

/-- The maximally even set `{0, 8, 16, 24}` in `C_32`. -/
def M32 : Finset (Fin 32) := {0, 8, 16, 24}

theorem energy_A32 : energy inv cycleDist A32 = 319 / 504 := by decide +kernel

theorem energy_M32 : energy inv cycleDist M32 = 5 / 8 := by decide +kernel

lemma A32_check : ∀ u ∈ A32, ∀ v : Fin 32, v ∉ A32 → cycleDist u v = 1 →
    319 / 504 < energy inv cycleDist (insert v (A32.erase u)) := by
  decide +kernel

/-- The smallest energy of a perturbation of `A32` is `3191/5040`. -/
lemma A32_min_check : ∀ u ∈ A32, ∀ v : Fin 32, v ∉ A32 → cycleDist u v = 1 →
    3191 / 5040 ≤ energy inv cycleDist (insert v (A32.erase u)) := by
  decide +kernel

theorem cycle32_strictLocalMin : IsStrictLocalMin cycleDist (energy inv cycleDist) A32 := by
  rintro B ⟨u, hu, v, hv, hd, rfl⟩
  rw [energy_A32]
  exact A32_check u hu v hv hd

theorem cycle32_not_globalMin : ¬ IsGlobalMin (energy inv cycleDist) A32 :=
  not_isGlobalMin_of_lt (B := M32) (by decide) (by rw [energy_A32, energy_M32]; norm_num)

/-- **Question 5.3 (first part), cycle, `g(r) = 1/r`: negative.** -/
theorem cycle32_counterexample :
    IsStrictLocalMin cycleDist (energy inv cycleDist) A32 ∧
      IsLocalMin cycleDist (energy inv cycleDist) A32 ∧
      ¬ IsGlobalMin (energy inv cycleDist) A32 :=
  ⟨cycle32_strictLocalMin, cycle32_strictLocalMin.isLocalMin, cycle32_not_globalMin⟩

/-- **Question 5.3 (second part), cycle: negative.** Descending Local Search started at
`A32` returns `A32`, which is not a minimizer. -/
theorem cycle32_dls (L : Finset (Fin 32) → List (Finset (Fin 32)))
    (hL : ∀ B ∈ L A32, IsPerturbation cycleDist A32 B) (k : ℕ) :
    dls L (energy inv cycleDist) k A32 = A32 ∧ ¬ IsGlobalMin (energy inv cycleDist) A32 :=
  ⟨dls_of_isLocalMin L hL cycle32_strictLocalMin.isLocalMin k, cycle32_not_globalMin⟩

/-! ## The path `P_13` -/

/-- `{0, 1, 3, 6, 8, 10, 12}` in `P_13`. -/
def A13 : Finset (Fin 13) := {0, 1, 3, 6, 8, 10, 12}

/-- `{0, 2, 4, 6, 8, 10, 12}` in `P_13` (the minimizer). -/
def M13 : Finset (Fin 13) := {0, 2, 4, 6, 8, 10, 12}

theorem energy_A13 : energy inv pathDist A13 = 32195 / 5544 := by decide +kernel

theorem energy_M13 : energy inv pathDist M13 = 223 / 40 := by decide +kernel

lemma A13_check : ∀ u ∈ A13, ∀ v : Fin 13, v ∉ A13 → pathDist u v = 1 →
    32195 / 5544 < energy inv pathDist (insert v (A13.erase u)) := by
  decide +kernel

/-- The smallest energy of a perturbation of `A13` is `20137/3465`. -/
lemma A13_min_check : ∀ u ∈ A13, ∀ v : Fin 13, v ∉ A13 → pathDist u v = 1 →
    20137 / 3465 ≤ energy inv pathDist (insert v (A13.erase u)) := by
  decide +kernel

theorem path13_strictLocalMin : IsStrictLocalMin pathDist (energy inv pathDist) A13 := by
  rintro B ⟨u, hu, v, hv, hd, rfl⟩
  rw [energy_A13]
  exact A13_check u hu v hv hd

theorem path13_not_globalMin : ¬ IsGlobalMin (energy inv pathDist) A13 :=
  not_isGlobalMin_of_lt (B := M13) (by decide) (by rw [energy_A13, energy_M13]; norm_num)

/-- **Question 5.3 (first part), path, `g(r) = 1/r`: negative.** -/
theorem path13_counterexample :
    IsStrictLocalMin pathDist (energy inv pathDist) A13 ∧
      IsLocalMin pathDist (energy inv pathDist) A13 ∧
      ¬ IsGlobalMin (energy inv pathDist) A13 :=
  ⟨path13_strictLocalMin, path13_strictLocalMin.isLocalMin, path13_not_globalMin⟩

/-- **Question 5.3 (second part), path: negative.** -/
theorem path13_dls (L : Finset (Fin 13) → List (Finset (Fin 13)))
    (hL : ∀ B ∈ L A13, IsPerturbation pathDist A13 B) (k : ℕ) :
    dls L (energy inv pathDist) k A13 = A13 ∧ ¬ IsGlobalMin (energy inv pathDist) A13 :=
  ⟨dls_of_isLocalMin L hL path13_strictLocalMin.isLocalMin k, path13_not_globalMin⟩

/-! ## The path `P_10`: the literal reading of Definition 1.2 -/

/-- `{0, 1, 3, 6, 8, 9}` in `P_10`. -/
def A10 : Finset (Fin 10) := {0, 1, 3, 6, 8, 9}

/-- `{0, 1, 3, 5, 7, 9}` in `P_10` (a minimizer). -/
def M10 : Finset (Fin 10) := {0, 1, 3, 5, 7, 9}

theorem energy_A10 : energy inv pathDist A10 = 6599 / 1260 := by decide +kernel

theorem energy_M10 : energy inv pathDist M10 = 12589 / 2520 := by decide +kernel

lemma A10_check : ∀ u ∈ A10, ∀ v : Fin 10, v ∉ A10 → pathDist u v = 1 →
    6599 / 1260 ≤ energy inv pathDist (insert v (A10.erase u)) := by
  decide +kernel

/-- Moving `6` to `5` gives the same energy. -/
theorem energy_A10_pert : energy inv pathDist (insert 5 (A10.erase 6)) = 6599 / 1260 := by
  decide +kernel

/-- **Question 5.3, literal reading of "local minimizer": still negative.** -/
theorem path10_literal_counterexample :
    IsLocalMinLiteral pathDist (energy inv pathDist) A10 ∧
      ¬ IsGlobalMin (energy inv pathDist) A10 := by
  refine ⟨⟨?_, insert 5 (A10.erase 6), ⟨6, by decide, 5, by decide, by decide, rfl⟩, ?_⟩, ?_⟩
  · rintro B ⟨u, hu, v, hv, hd, rfl⟩
    rw [energy_A10]
    exact A10_check u hu v hv hd
  · rw [energy_A10_pert, energy_A10]
  · exact not_isGlobalMin_of_lt (B := M10) (by decide)
      (by rw [energy_A10, energy_M10]; norm_num)

/-! ## The cycle `C_8` with another strictly decreasing strictly convex `g` -/

/-- `g(1) = 57`, `g(2) = 31`, `g(3) = 10`, `g(4) = 0`. -/
def g8 (r : ℕ) : ℚ :=
  match r with
  | 1 => 57
  | 2 => 31
  | 3 => 10
  | _ => 0

/-- `g8` is strictly decreasing on `{1, …, 4} = {1, …, diam C_8}`. -/
theorem g8_strictAnti : g8 1 > g8 2 ∧ g8 2 > g8 3 ∧ g8 3 > g8 4 := by norm_num [g8]

/-- `g8` is strictly convex on `{1, …, 4}` (its successive differences strictly increase). -/
theorem g8_strictConvex :
    g8 2 - g8 1 < g8 3 - g8 2 ∧ g8 3 - g8 2 < g8 4 - g8 3 := by norm_num [g8]

/-- `{0, 1, 4, 5}` in `C_8`. -/
def A8 : Finset (Fin 8) := {0, 1, 4, 5}

/-- The maximally even set `{0, 2, 4, 6}` in `C_8`. -/
def M8 : Finset (Fin 8) := {0, 2, 4, 6}

theorem energy_A8 : energy g8 cycleDist A8 = 134 := by decide +kernel

theorem energy_M8 : energy g8 cycleDist M8 = 124 := by decide +kernel

lemma A8_check : ∀ u ∈ A8, ∀ v : Fin 8, v ∉ A8 → cycleDist u v = 1 →
    energy g8 cycleDist (insert v (A8.erase u)) = 139 := by
  decide +kernel

/-- **Question 5.3 for a general strictly decreasing convex `g` on a cycle: negative.** -/
theorem cycle8_general_g_counterexample :
    IsStrictLocalMin cycleDist (energy g8 cycleDist) A8 ∧
      ¬ IsGlobalMin (energy g8 cycleDist) A8 := by
  refine ⟨?_, not_isGlobalMin_of_lt (B := M8) (by decide)
    (by rw [energy_A8, energy_M8]; norm_num)⟩
  rintro B ⟨u, hu, v, hv, hd, rfl⟩
  rw [energy_A8, A8_check u hu v hv hd]
  norm_num

/-! ## An infinite family on cycles: `C_{4x}`, `A = {0, x-1, 2x, 3x-1}`, `x = m + 8 ≥ 8`

The Lean code of this section was generated by `gen_family.py` (same folder). -/

/-- The set `{0, m + 7, 2 * m + 16, 3 * m + 23}` in `C_{4(m+8)}`. -/
def famA (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 7, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 23, by omega⟩}

theorem energy_famA (m : ℕ) : energy inv cycleDist (famA m) =
    1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7) := by
  unfold famA
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 7) (r2 := 2 * m + 16) (r3 := m + 9) (r4 := m + 9) (r5 := 2 * m + 16) (r6 := m + 7) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{0, m + 8, 2 * m + 16, 3 * m + 24}` in `C_{4(m+8)}`. -/
def famM (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 8, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 24, by omega⟩}

theorem energy_famM (m : ℕ) : energy inv cycleDist (famM m) =
    1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) + 1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) := by
  unfold famM
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 8) (r2 := 2 * m + 16) (r3 := m + 8) (r4 := m + 8) (r5 := 2 * m + 16) (r6 := m + 8) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{1, m + 7, 2 * m + 16, 3 * m + 23}` in `C_{4(m+8)}`. -/
def famP1 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨1, by omega⟩, ⟨m + 7, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 23, by omega⟩}

theorem energy_famP1 (m : ℕ) : energy inv cycleDist (famP1 m) =
    1 / ((m : ℚ) + 6) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 10) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7) := by
  unfold famP1
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 6) (r2 := 2 * m + 15) (r3 := m + 10) (r4 := m + 9) (r5 := 2 * m + 16) (r6 := m + 7) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{m + 7, 2 * m + 16, 3 * m + 23, 4 * m + 31}` in `C_{4(m+8)}`. -/
def famP2 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨m + 7, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 23, by omega⟩, ⟨4 * m + 31, by omega⟩}

theorem energy_famP2 (m : ℕ) : energy inv cycleDist (famP2 m) =
    1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) + 1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 8) := by
  unfold famP2
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 9) (r2 := 2 * m + 16) (r3 := m + 8) (r4 := m + 7) (r5 := 2 * m + 15) (r6 := m + 8) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{0, m + 6, 2 * m + 16, 3 * m + 23}` in `C_{4(m+8)}`. -/
def famP3 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 6, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 23, by omega⟩}

theorem energy_famP3 (m : ℕ) : energy inv cycleDist (famP3 m) =
    1 / ((m : ℚ) + 6) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 10) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 7) := by
  unfold famP3
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 6) (r2 := 2 * m + 16) (r3 := m + 9) (r4 := m + 10) (r5 := 2 * m + 15) (r6 := m + 7) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{0, m + 8, 2 * m + 16, 3 * m + 23}` in `C_{4(m+8)}`. -/
def famP4 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 8, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 23, by omega⟩}

theorem energy_famP4 (m : ℕ) : energy inv cycleDist (famP4 m) =
    1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 7) := by
  unfold famP4
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 8) (r2 := 2 * m + 16) (r3 := m + 9) (r4 := m + 8) (r5 := 2 * m + 15) (r6 := m + 7) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{0, m + 7, 2 * m + 15, 3 * m + 23}` in `C_{4(m+8)}`. -/
def famP5 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 7, by omega⟩, ⟨2 * m + 15, by omega⟩, ⟨3 * m + 23, by omega⟩}

theorem energy_famP5 (m : ℕ) : energy inv cycleDist (famP5 m) =
    1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) := by
  unfold famP5
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 7) (r2 := 2 * m + 15) (r3 := m + 9) (r4 := m + 8) (r5 := 2 * m + 16) (r6 := m + 8) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{0, m + 7, 2 * m + 17, 3 * m + 23}` in `C_{4(m+8)}`. -/
def famP6 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 7, by omega⟩, ⟨2 * m + 17, by omega⟩, ⟨3 * m + 23, by omega⟩}

theorem energy_famP6 (m : ℕ) : energy inv cycleDist (famP6 m) =
    1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 10) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 6) := by
  unfold famP6
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 7) (r2 := 2 * m + 15) (r3 := m + 9) (r4 := m + 10) (r5 := 2 * m + 16) (r6 := m + 6) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{0, m + 7, 2 * m + 16, 3 * m + 22}` in `C_{4(m+8)}`. -/
def famP7 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 7, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 22, by omega⟩}

theorem energy_famP7 (m : ℕ) : energy inv cycleDist (famP7 m) =
    1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 10) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 6) := by
  unfold famP7
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 7) (r2 := 2 * m + 16) (r3 := m + 10) (r4 := m + 9) (r5 := 2 * m + 15) (r6 := m + 6) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- The set `{0, m + 7, 2 * m + 16, 3 * m + 24}` in `C_{4(m+8)}`. -/
def famP8 (m : ℕ) : Finset (Fin (4 * (m + 8))) := {⟨0, by omega⟩, ⟨m + 7, by omega⟩, ⟨2 * m + 16, by omega⟩, ⟨3 * m + 24, by omega⟩}

theorem energy_famP8 (m : ℕ) : energy inv cycleDist (famP8 m) =
    1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 8) := by
  unfold famP8
  refine (energy_four_val inv cycleDist ?_ ?_ ?_ (r1 := m + 7) (r2 := 2 * m + 16) (r3 := m + 8) (r4 := m + 9) (r5 := 2 * m + 15) (r6 := m + 8) ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  all_goals first
    | exact Fin.mk_lt_mk.2 (by omega)
    | (simp only [cycleDist, pathDist]; omega)
    | (simp only [inv]; push_cast; ring)

/-- Perturbation 1 of `famA` has larger energy. -/
theorem famA_lt_famP1 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP1 m) := by
  rw [energy_famA, energy_famP1, ← sub_pos]
  have key : (1 / ((m : ℚ) + 6) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 10) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 4 + 56 * (m : ℚ) ^ 3 + 943 * (m : ℚ) ^ 2 + 6384 * (m : ℚ) + 15300) / (4 * (m : ℚ) ^ 6 + 190 * (m : ℚ) ^ 5 + 3740 * (m : ℚ) ^ 4 + 39050 * (m : ℚ) ^ 3 + 228096 * (m : ℚ) ^ 2 + 706680 * (m : ℚ) + 907200) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Perturbation 2 of `famA` has larger energy. -/
theorem famA_lt_famP2 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP2 m) := by
  rw [energy_famA, energy_famP2, ← sub_pos]
  have key : (1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) + 1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 8)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 2 + 8 * (m : ℚ) + 3) / (4 * (m : ℚ) ^ 4 + 126 * (m : ℚ) ^ 3 + 1484 * (m : ℚ) ^ 2 + 7746 * (m : ℚ) + 15120) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Perturbation 3 of `famA` has larger energy. -/
theorem famA_lt_famP3 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP3 m) := by
  rw [energy_famA, energy_famP3, ← sub_pos]
  have key : (1 / ((m : ℚ) + 6) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 10) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 7)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 4 + 56 * (m : ℚ) ^ 3 + 943 * (m : ℚ) ^ 2 + 6384 * (m : ℚ) + 15300) / (4 * (m : ℚ) ^ 6 + 190 * (m : ℚ) ^ 5 + 3740 * (m : ℚ) ^ 4 + 39050 * (m : ℚ) ^ 3 + 228096 * (m : ℚ) ^ 2 + 706680 * (m : ℚ) + 907200) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Perturbation 4 of `famA` has larger energy. -/
theorem famA_lt_famP4 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP4 m) := by
  rw [energy_famA, energy_famP4, ← sub_pos]
  have key : (1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 7)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 2 + 8 * (m : ℚ) + 3) / (4 * (m : ℚ) ^ 4 + 126 * (m : ℚ) ^ 3 + 1484 * (m : ℚ) ^ 2 + 7746 * (m : ℚ) + 15120) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Perturbation 5 of `famA` has larger energy. -/
theorem famA_lt_famP5 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP5 m) := by
  rw [energy_famA, energy_famP5, ← sub_pos]
  have key : (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 2 + 8 * (m : ℚ) + 3) / (4 * (m : ℚ) ^ 4 + 126 * (m : ℚ) ^ 3 + 1484 * (m : ℚ) ^ 2 + 7746 * (m : ℚ) + 15120) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Perturbation 6 of `famA` has larger energy. -/
theorem famA_lt_famP6 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP6 m) := by
  rw [energy_famA, energy_famP6, ← sub_pos]
  have key : (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 10) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 6)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 4 + 56 * (m : ℚ) ^ 3 + 943 * (m : ℚ) ^ 2 + 6384 * (m : ℚ) + 15300) / (4 * (m : ℚ) ^ 6 + 190 * (m : ℚ) ^ 5 + 3740 * (m : ℚ) ^ 4 + 39050 * (m : ℚ) ^ 3 + 228096 * (m : ℚ) ^ 2 + 706680 * (m : ℚ) + 907200) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Perturbation 7 of `famA` has larger energy. -/
theorem famA_lt_famP7 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP7 m) := by
  rw [energy_famA, energy_famP7, ← sub_pos]
  have key : (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 10) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 6)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 4 + 56 * (m : ℚ) ^ 3 + 943 * (m : ℚ) ^ 2 + 6384 * (m : ℚ) + 15300) / (4 * (m : ℚ) ^ 6 + 190 * (m : ℚ) ^ 5 + 3740 * (m : ℚ) ^ 4 + 39050 * (m : ℚ) ^ 3 + 228096 * (m : ℚ) ^ 2 + 706680 * (m : ℚ) + 907200) := by
    field_simp
    ring
  rw [key]
  positivity

/-- Perturbation 8 of `famA` has larger energy. -/
theorem famA_lt_famP8 (m : ℕ) : energy inv cycleDist (famA m) < energy inv cycleDist (famP8 m) := by
  rw [energy_famA, energy_famP8, ← sub_pos]
  have key : (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 15) + 1 / ((m : ℚ) + 8)) - (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) =
      (1 * (m : ℚ) ^ 2 + 8 * (m : ℚ) + 3) / (4 * (m : ℚ) ^ 4 + 126 * (m : ℚ) ^ 3 + 1484 * (m : ℚ) ^ 2 + 7746 * (m : ℚ) + 15120) := by
    field_simp
    ring
  rw [key]
  positivity

/-- The maximally even set has smaller energy than `famA`. -/
theorem famM_lt_famA (m : ℕ) : energy inv cycleDist (famM m) < energy inv cycleDist (famA m) := by
  rw [energy_famM, energy_famA, ← sub_pos]
  have key : (1 / ((m : ℚ) + 7) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 9) + 1 / ((m : ℚ) + 9) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 7)) - (1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8) + 1 / ((m : ℚ) + 8) + 1 / (2 * (m : ℚ) + 16) + 1 / ((m : ℚ) + 8)) =
      (4) / (1 * (m : ℚ) ^ 3 + 24 * (m : ℚ) ^ 2 + 191 * (m : ℚ) + 504) := by
    field_simp
    ring
  rw [key]
  positivity


/-- Identifies `insert v ((famA m).erase u)` with one of `famP1`, …, `famP8`. -/
macro "fam_ext" : tactic => `(tactic| (
  ext ⟨w, hw⟩
  simp only [famA, famP1, famP2, famP3, famP4, famP5, famP6, famP7, famP8, mem_insert,
    mem_erase, mem_singleton, Fin.mk.injEq, ne_eq]
  omega))

/-- For every `x = m + 8 ≥ 8`, the set `{0, x-1, 2x, 3x-1}` is a strict local minimizer of
`E_g` (`g(r) = 1/r`) on `C_{4x}`, but not a minimizer. -/
theorem cycle_family_counterexample (m : ℕ) :
    IsStrictLocalMin cycleDist (energy inv cycleDist) (famA m) ∧
      ¬ IsGlobalMin (energy inv cycleDist) (famA m) := by
  constructor
  · rintro B ⟨⟨u, hu'⟩, hu, ⟨v, hv'⟩, hv, hd, rfl⟩
    simp only [famA, mem_insert, mem_singleton, Fin.mk.injEq] at hu hv
    simp only [cycleDist, pathDist] at hd
    rcases hu with rfl | rfl | rfl | rfl
    · rcases (by omega : v = 1 ∨ v = 4 * m + 31) with rfl | rfl
      · convert famA_lt_famP1 m using 2; fam_ext
      · convert famA_lt_famP2 m using 2; fam_ext
    · rcases (by omega : v = m + 6 ∨ v = m + 8) with rfl | rfl
      · convert famA_lt_famP3 m using 2; fam_ext
      · convert famA_lt_famP4 m using 2; fam_ext
    · rcases (by omega : v = 2 * m + 15 ∨ v = 2 * m + 17) with rfl | rfl
      · convert famA_lt_famP5 m using 2; fam_ext
      · convert famA_lt_famP6 m using 2; fam_ext
    · rcases (by omega : v = 3 * m + 22 ∨ v = 3 * m + 24) with rfl | rfl
      · convert famA_lt_famP7 m using 2; fam_ext
      · convert famA_lt_famP8 m using 2; fam_ext
  · refine not_isGlobalMin_of_lt (B := famM m) ?_ (famM_lt_famA m)
    unfold famA famM
    rw [card_four (Fin.mk_lt_mk.2 (by omega)) (Fin.mk_lt_mk.2 (by omega))
        (Fin.mk_lt_mk.2 (by omega)),
      card_four (Fin.mk_lt_mk.2 (by omega)) (Fin.mk_lt_mk.2 (by omega))
        (Fin.mk_lt_mk.2 (by omega))]

/-- Descending Local Search started at a member of the family returns it unchanged. -/
theorem cycle_family_dls (m : ℕ) (L : Finset (Fin (4 * (m + 8))) → List (Finset (Fin (4 * (m + 8)))))
    (hL : ∀ B ∈ L (famA m), IsPerturbation cycleDist (famA m) B) (k : ℕ) :
    dls L (energy inv cycleDist) k (famA m) = famA m ∧
      ¬ IsGlobalMin (energy inv cycleDist) (famA m) :=
  ⟨dls_of_isLocalMin L hL (cycle_family_counterexample m).1.isLocalMin k,
    (cycle_family_counterexample m).2⟩

end OpenQuestions.MaximallyEvenEnergy

#print axioms OpenQuestions.MaximallyEvenEnergy.cycle32_counterexample
#print axioms OpenQuestions.MaximallyEvenEnergy.cycle32_dls
#print axioms OpenQuestions.MaximallyEvenEnergy.path13_counterexample
#print axioms OpenQuestions.MaximallyEvenEnergy.path13_dls
#print axioms OpenQuestions.MaximallyEvenEnergy.path10_literal_counterexample
#print axioms OpenQuestions.MaximallyEvenEnergy.cycle8_general_g_counterexample
#print axioms OpenQuestions.MaximallyEvenEnergy.cycle_family_counterexample
#print axioms OpenQuestions.MaximallyEvenEnergy.cycle_family_dls
