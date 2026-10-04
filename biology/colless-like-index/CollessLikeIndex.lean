import Mathlib

/-!
# No integer-valued weight makes a Colless-like index sound

A. Mir, F. Rosselló, L. Rotger, *Sound Colless-like balance indices for multifurcating trees*,
PLoS ONE 13(9): e0203401 (2018), arXiv:1805.01329.

Conjecture (end of the paper): no function `f : ℕ → ℕ` makes the Colless-like index `C_{D,f}`
sound.  We prove it, in fact for every `f : ℕ → ℚ` (no sign condition), and for every
dissimilarity `D`.

Conventions (as in the paper):
* a *tree* is a finite rooted unordered tree; we represent it by `RTree.node children`, where the
  order of the children is irrelevant up to the isomorphism `Iso`;
* the paper's trees have no node of out-degree 1 (`Valid`);
* `fsize f T = ∑_v f (outdeg v)`, the `f`-size;
* `colless D f T = ∑_{internal v} D (f-sizes of the subtrees rooted at the children of v)`;
* `FullySym T`: at every node, the subtrees rooted at the children are pairwise isomorphic;
* `Sound D f`: for every valid tree, `colless D f T = 0 ↔ FullySym T`.
-/

namespace OpenQuestions.CollessLikeIndex

/-! ## Trees -/

/-- Finite rooted trees, given by their (ordered) list of children.  A leaf is `node []`. -/
inductive RTree : Type
  | node : List RTree → RTree

open RTree

/-- Rooted-tree isomorphism: a bijection between the children such that corresponding
children are isomorphic. -/
inductive Iso : RTree → RTree → Prop
  | mk {ts us : List RTree} (e : Fin ts.length ≃ Fin us.length)
      (h : ∀ i : Fin ts.length, Iso ts[i] us[e i]) : Iso (node ts) (node us)

/-- The trees considered in the paper: no node has out-degree `1`. -/
inductive Valid : RTree → Prop
  | mk (ts : List RTree) : ts.length ≠ 1 → (∀ t ∈ ts, Valid t) → Valid (node ts)

/-- Fully symmetric trees: at every node the subtrees rooted at the children are pairwise
isomorphic. -/
inductive FullySym : RTree → Prop
  | mk (ts : List RTree) : (∀ t ∈ ts, ∀ u ∈ ts, Iso t u) → (∀ t ∈ ts, FullySym t) →
      FullySym (node ts)

mutual
/-- The `f`-size `δ_f(T) = ∑_{v ∈ V(T)} f(outdeg v)`. -/
def fsize (f : ℕ → ℝ) : RTree → ℝ
  | node ts => f ts.length + fsizeL f ts
/-- Sum of the `f`-sizes of a list of trees. -/
def fsizeL (f : ℕ → ℝ) : List RTree → ℝ
  | [] => 0
  | t :: ts => fsize f t + fsizeL f ts
end

mutual
/-- The Colless-like index `C_{D,f}(T) = ∑_{v internal} D(δ_f(T_{v_1}), …, δ_f(T_{v_k}))`,
where `v_1, …, v_k` are the children of `v`. -/
def colless (D : List ℝ → ℝ) (f : ℕ → ℝ) : RTree → ℝ
  | node ts => (if ts = [] then 0 else D (ts.map (fsize f))) + collessL D f ts
/-- Sum of the Colless-like indices of a list of trees. -/
def collessL (D : List ℝ → ℝ) (f : ℕ → ℝ) : List RTree → ℝ
  | [] => 0
  | t :: ts => colless D f t + collessL D f ts
end

/-- A dissimilarity (paper, before Definition 4): non-negative, symmetric, and zero exactly on
constant (non-empty) sequences. -/
structure IsDissimilarity (D : List ℝ → ℝ) : Prop where
  nonneg : ∀ l, 0 ≤ D l
  perm : ∀ l l' : List ℝ, l.Perm l' → D l = D l'
  eq_zero_iff : ∀ l : List ℝ, l ≠ [] → (D l = 0 ↔ ∀ x ∈ l, ∀ y ∈ l, x = y)

/-- Definition 9 of the paper. -/
def Sound (D : List ℝ → ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ T : RTree, Valid T → (colless D f T = 0 ↔ FullySym T)

/-! ## Sanity check: the easy direction of soundness holds for every `D` and `f`

As stated before Definition 9 of the paper, every fully symmetric tree has index `0`; so
soundness is really about the converse.  (This part is not needed for the main theorem.) -/

lemma fsizeL_eq_sum (f : ℕ → ℝ) :
    ∀ ts : List RTree, fsizeL f ts = ∑ i : Fin ts.length, fsize f ts[i] := by
  intro ts
  induction ts with
  | nil => simp [fsizeL]
  | cons t ts ih =>
    rw [fsizeL, ih]
    exact (Fin.sum_univ_succ (n := ts.length) (fun i => fsize f (t :: ts)[i])).symm

/-- The `f`-size is an isomorphism invariant. -/
lemma fsize_iso (f : ℕ → ℝ) {s t : RTree} (h : Iso s t) : fsize f s = fsize f t := by
  induction h with
  | @mk ts us e _ ih =>
    have hlen : ts.length = us.length := by simpa using Fintype.card_congr e
    simp only [fsize, fsizeL_eq_sum]
    rw [Fintype.sum_equiv e _ (fun j => fsize f us[j]) ih, hlen]

lemma collessL_eq_zero (D : List ℝ → ℝ) (f : ℕ → ℝ) :
    ∀ ts : List RTree, (∀ t ∈ ts, colless D f t = 0) → collessL D f ts = 0 := by
  intro ts
  induction ts with
  | nil => simp [collessL]
  | cons t ts ih =>
    intro h
    rw [collessL, h t (by simp), ih (fun u hu => h u (by simp [hu]))]
    simp

theorem colless_eq_zero_of_fullySym (D : List ℝ → ℝ)
    (hD : ∀ l : List ℝ, l ≠ [] → (∀ x ∈ l, ∀ y ∈ l, x = y) → D l = 0)
    (f : ℕ → ℝ) {T : RTree} (hT : FullySym T) : colless D f T = 0 := by
  induction hT with
  | mk ts hiso _ ih =>
    rw [colless, collessL_eq_zero D f ts ih, add_zero]
    split_ifs with h
    · rfl
    · apply hD _ (by simpa using h)
      intro x hx y hy
      simp only [List.mem_map] at hx hy
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨u, hu, rfl⟩ := hy
      exact fsize_iso f (hiso t ht u hu)

/-- Hence `Sound D f` only asks for the converse implication. -/
theorem sound_iff (D : List ℝ → ℝ) (hD : IsDissimilarity D) (f : ℕ → ℝ) :
    Sound D f ↔ ∀ T : RTree, Valid T → colless D f T = 0 → FullySym T :=
  ⟨fun h T hv h0 => (h T hv).1 h0, fun h T hv =>
    ⟨h T hv, colless_eq_zero_of_fullySym D (fun l hl hc => (hD.eq_zero_iff l hl).2 hc) f⟩⟩

/-! ## Fully symmetric trees `FS_{k₁,…,k_h}` -/

/-- `FS w` for `w = [k₁, …, k_h]`: the root has `k₁` children, each of which is `FS [k₂,…,k_h]`. -/
def FS : List ℕ → RTree
  | [] => node []
  | k :: w => node (List.replicate k (FS w))

lemma fsizeL_replicate (f : ℕ → ℝ) (k : ℕ) (t : RTree) :
    fsizeL f (List.replicate k t) = k * fsize f t := by
  induction k with
  | zero => simp [fsizeL]
  | succ k ih => simp [List.replicate_succ, fsizeL, ih]; ring

lemma collessL_replicate (D : List ℝ → ℝ) (f : ℕ → ℝ) (k : ℕ) (t : RTree) :
    collessL D f (List.replicate k t) = k * colless D f t := by
  induction k with
  | zero => simp [collessL]
  | succ k ih => simp [List.replicate_succ, collessL, ih]; ring

/-- Example 3 of the paper, in recursive form. -/
lemma fsize_FS_nil (f : ℕ → ℝ) : fsize f (FS []) = f 0 := by
  simp [FS, fsize, fsizeL]

lemma fsize_FS_cons (f : ℕ → ℝ) (k : ℕ) (w : List ℕ) :
    fsize f (FS (k :: w)) = f k + k * fsize f (FS w) := by
  simp [FS, fsize, fsizeL_replicate]

/-- Sanity check: Example 11 of the paper. -/
example (a b c : ℝ) :
    fsize (fun n => a * n ^ 2 + b * n + c) (FS [2, 2, 2, 7]) =
      fsize (fun n => a * n ^ 2 + b * n + c) (FS [14, 4]) := by
  simp only [fsize_FS_cons, fsize_FS_nil]; push_cast; ring

/-- Fully symmetric trees have Colless-like index `0` (for any `D` vanishing on constant
sequences). -/
lemma colless_FS (D : List ℝ → ℝ)
    (hD : ∀ l : List ℝ, l ≠ [] → (∀ x ∈ l, ∀ y ∈ l, x = y) → D l = 0)
    (f : ℕ → ℝ) (w : List ℕ) : colless D f (FS w) = 0 := by
  induction w with
  | nil => simp [FS, colless, collessL]
  | cons k w ih =>
    simp only [FS, colless, collessL_replicate]
    rw [ih]
    split_ifs with h
    · simp
    · rw [hD _ (by simpa using h)]
      · simp
      · intro x hx y hy
        simp only [List.map_replicate, List.mem_replicate] at hx hy
        rw [hx.2, hy.2]

lemma valid_FS (w : List ℕ) (hw : ∀ k ∈ w, 2 ≤ k) : Valid (FS w) := by
  induction w with
  | nil => exact Valid.mk [] (by simp) (by simp)
  | cons k w ih =>
    refine Valid.mk _ ?_ ?_
    · have := hw k (by simp); simp; omega
    · intro t ht
      rw [List.mem_replicate] at ht
      rw [ht.2]
      exact ih (fun j hj => hw j (by simp [hj]))

/-! ## An isomorphism invariant: which out-degrees occur at which depth -/

/-- `HasNode T d k`: the tree `T` has a node at depth `d` with out-degree `k`. -/
inductive HasNode : RTree → ℕ → ℕ → Prop
  | root (ts : List RTree) : HasNode (node ts) 0 ts.length
  | child (ts : List RTree) (i : Fin ts.length) {d k : ℕ} :
      HasNode ts[i] d k → HasNode (node ts) (d + 1) k

lemma HasNode.of_iso {s t : RTree} (h : Iso s t) :
    ∀ {d k : ℕ}, HasNode s d k → HasNode t d k := by
  induction h with
  | @mk ts us e _ ih =>
    intro d k hs
    cases hs with
    | root =>
      have : ts.length = us.length := by simpa using Fintype.card_congr e
      rw [this]; exact HasNode.root us
    | @child _ i d' k' h' => exact HasNode.child us (e i) (ih i h')

/-- The out-degree of the nodes at depth `d` of `FS w` (it is `0` at depth `w.length`). -/
def lvl (w : List ℕ) (d : ℕ) : ℕ := (w ++ [0]).getD d 0

lemma hasNode_FS_iff (w : List ℕ) :
    ∀ d k, HasNode (FS w) d k → d ≤ w.length ∧ k = lvl w d := by
  induction w with
  | nil =>
    intro d k h
    rw [FS] at h
    cases h with
    | root => simp [lvl]
    | @child _ i d' k' _ => exact absurd i.2 (by simp)
  | cons a w ih =>
    intro d k h
    rw [FS] at h
    cases h with
    | root => simp [lvl]
    | @child _ i d' k' h' =>
      simp only [Fin.getElem_fin, List.getElem_replicate] at h'
      have := ih _ _ h'
      refine ⟨by simp; omega, ?_⟩
      rw [this.2]; simp [lvl]

lemma hasNode_FS (w : List ℕ) (hw : ∀ k ∈ w, 0 < k) :
    ∀ d, d ≤ w.length → HasNode (FS w) d (lvl w d) := by
  induction w with
  | nil =>
    intro d hd
    have : d = 0 := by simpa using hd
    subst this; rw [FS]; exact HasNode.root []
  | cons a w ih =>
    intro d hd
    rw [FS]
    cases d with
    | zero =>
      have := HasNode.root (List.replicate a (FS w))
      simpa [lvl] using this
    | succ d =>
      have ha : 0 < a := hw a (by simp)
      have := HasNode.child (List.replicate a (FS w)) ⟨0, by simpa using ha⟩
        (d := d) (k := lvl w d)
        (by simpa using ih (fun j hj => hw j (by simp [hj])) d (by simpa using hd))
      simpa [lvl] using this

/-- Fully symmetric trees with different level sequences are not isomorphic. -/
lemma not_iso_FS {w₁ w₂ : List ℕ} (h₁ : ∀ k ∈ w₁, 0 < k) (h₂ : ∀ k ∈ w₂, 0 < k)
    (hne : w₁ ≠ w₂) : ¬ Iso (FS w₁) (FS w₂) := by
  intro hiso
  have key : ∀ d, d ≤ w₁.length → d ≤ w₂.length ∧ lvl w₁ d = lvl w₂ d := fun d hd =>
    hasNode_FS_iff w₂ d _ (HasNode.of_iso hiso (hasNode_FS w₁ h₁ d hd))
  -- `lvl w d = 0` exactly at `d = w.length` (for `d ≤ w.length`)
  have lvl_pos : ∀ (w : List ℕ), (∀ k ∈ w, 0 < k) → ∀ d, d < w.length → 0 < lvl w d := by
    intro w hw d hd
    have : lvl w d = w[d] := by simp [lvl, List.getD_eq_getElem?_getD, List.getElem?_append_left hd, hd]
    rw [this]; exact hw _ (List.getElem_mem hd)
  have lvl_len : ∀ w : List ℕ, lvl w w.length = 0 := by intro w; simp [lvl]
  obtain ⟨hle, hl⟩ := key w₁.length le_rfl
  have hlen : w₁.length = w₂.length := by
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have := lvl_pos w₂ h₂ _ hlt; rw [← hl, lvl_len] at this; omega
    · exact heq
  apply hne
  apply List.ext_getElem hlen
  intro d hd₁ hd₂
  have := (key d hd₁.le).2
  simpa [lvl, List.getD_eq_getElem?_getD, List.getElem?_append_left hd₁,
    List.getElem?_append_left hd₂, hd₁, hd₂] using this

/-! ## Lemma 10 of the paper ("only if" part) -/

/-- If two non-isomorphic fully symmetric trees have the same `f`-size, then `C_{D,f}` is not
sound: the tree whose root has exactly these two subtrees has index `0` but is not fully
symmetric. -/
theorem not_sound_of_fsize_eq (D : List ℝ → ℝ)
    (hD : ∀ l : List ℝ, l ≠ [] → (∀ x ∈ l, ∀ y ∈ l, x = y) → D l = 0)
    (f : ℕ → ℝ) {w₁ w₂ : List ℕ} (hne : w₁ ≠ w₂)
    (h₁ : ∀ k ∈ w₁, 2 ≤ k) (h₂ : ∀ k ∈ w₂, 2 ≤ k)
    (heq : fsize f (FS w₁) = fsize f (FS w₂)) : ¬ Sound D f := by
  intro hS
  have hv : Valid (node [FS w₁, FS w₂]) := by
    refine Valid.mk _ (by simp) ?_
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact valid_FS _ h₁
    · exact valid_FS _ h₂
  have h0 : colless D f (node [FS w₁, FS w₂]) = 0 := by
    have hDx : D [fsize f (FS w₁), fsize f (FS w₂)] = 0 := by
      apply hD _ (by simp)
      intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [heq]
    simp [colless, collessL, colless_FS D hD, hDx]
  have hfs : FullySym (node [FS w₁, FS w₂]) := (hS _ hv).1 h0
  cases hfs with
  | mk _ hiso _ =>
    exact not_iso_FS (fun k hk => by have := h₁ k hk; omega)
      (fun k hk => by have := h₂ k hk; omega) hne (hiso _ (by simp) _ (by simp))

/-! ## Integer sizes of words -/

/-- The `g`-size of `FS w` for an integer-valued weight `g`. -/
def ws (g : ℕ → ℤ) : List ℕ → ℤ
  | [] => g 0
  | k :: w => g k + k * ws g w

/-- The four out-degrees used in the construction. -/
def Letter (k : ℕ) : Prop := k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6

lemma Letter.two_le {k : ℕ} (h : Letter k) : 2 ≤ k := by
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

/-- `|δ_g(FS w)| ≤ M (2 k₁⋯k_h - 1)`: the internal nodes are fewer than the leaves. -/
lemma ws_bound (g : ℕ → ℤ) (M : ℤ) (hM : ∀ k, k = 0 ∨ Letter k → |g k| ≤ M) :
    ∀ w : List ℕ, (∀ k ∈ w, Letter k) → |ws g w| ≤ M * (2 * (w.prod : ℤ) - 1) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 (Or.inl rfl))
  intro w
  induction w with
  | nil => intro _; simpa [ws] using hM 0 (Or.inl rfl)
  | cons k w ih =>
    intro hw
    have hk : Letter k := hw k (by simp)
    have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk.two_le
    have ihw := ih (fun j hj => hw j (by simp [hj]))
    have hgk := hM k (Or.inr hk)
    simp only [ws, List.prod_cons, Nat.cast_mul]
    have hP : (1 : ℤ) ≤ (w.prod : ℤ) := by
      have : 0 < w.prod := List.prod_pos (fun j hj => by have := (hw j (by simp [hj])).two_le; omega)
      exact_mod_cast this
    calc |g k + (k : ℤ) * ws g w| ≤ |g k| + (k : ℤ) * |ws g w| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ k)]
      _ ≤ M + (k : ℤ) * (M * (2 * (w.prod : ℤ) - 1)) := by
          gcongr
      _ ≤ M * (2 * ((k : ℤ) * (w.prod : ℤ)) - 1) := by
          nlinarith [mul_nonneg hM0 (by linarith : (0 : ℤ) ≤ (k : ℤ) - 2)]

/-! ## A large family of words with the same product `12ⁿ`

For `S, T ⊆ {0, …, 2n-1}` with `|S| = |T| = n`, the word `word n S T` has `i`-th letter
`(1 + [i ∈ S]) (2 + [i ∈ T]) ∈ {2, 3, 4, 6}`.  Its product is `2ⁿ · 2ⁿ · 3ⁿ = 12ⁿ`, and there are
`C(2n, n)² ≥ 16ⁿ / (2n+1)²` such words. -/

/-- The word attached to `(S, T)`. -/
def word (n : ℕ) (S T : Finset ℕ) : List ℕ :=
  (List.range (2 * n)).map fun i => (if i ∈ S then 2 else 1) * (if i ∈ T then 3 else 2)

lemma word_letter (n : ℕ) (S T : Finset ℕ) : ∀ k ∈ word n S T, Letter k := by
  intro k hk
  simp only [word, List.mem_map, List.mem_range] at hk
  obtain ⟨i, _, rfl⟩ := hk
  unfold Letter
  split_ifs <;> simp

lemma list_prod_range_map (m : ℕ) (h : ℕ → ℕ) :
    ((List.range m).map h).prod = ∏ i ∈ Finset.range m, h i := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.prod_append, ih,
      Finset.prod_range_succ]; simp

lemma word_prod (n : ℕ) {S T : Finset ℕ} (hS : S ∈ Finset.powersetCard n (Finset.range (2 * n)))
    (hT : T ∈ Finset.powersetCard n (Finset.range (2 * n))) :
    (word n S T).prod = 12 ^ n := by
  rw [Finset.mem_powersetCard] at hS hT
  rw [word, list_prod_range_map, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.inter_eq_right.2 hS.1, Finset.prod_const, hS.2, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 hT.1, hT.2]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range (2 * n))
    (fun i => i ∈ T)
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hT.1, hT.2, Finset.card_range] at hc
  have : (Finset.filter (fun i => i ∉ T) (Finset.range (2 * n))).card = n := by omega
  rw [this, show (12 : ℕ) = 2 * 3 * 2 by norm_num, mul_pow, mul_pow]
  ring

lemma word_inj (n : ℕ) {S T S' T' : Finset ℕ}
    (hS : S ⊆ Finset.range (2 * n)) (hT : T ⊆ Finset.range (2 * n))
    (hS' : S' ⊆ Finset.range (2 * n)) (hT' : T' ⊆ Finset.range (2 * n))
    (h : word n S T = word n S' T') : S = S' ∧ T = T' := by
  rw [word, word, List.map_inj_left] at h
  have key : ∀ i < 2 * n, (i ∈ S ↔ i ∈ S') ∧ (i ∈ T ↔ i ∈ T') := by
    intro i hi
    have := h i (List.mem_range.2 hi)
    by_cases a : i ∈ S <;> by_cases b : i ∈ T <;> by_cases c : i ∈ S' <;> by_cases d : i ∈ T' <;>
      simp_all
  constructor
  · ext i
    constructor
    · intro hi; exact (key i (Finset.mem_range.1 (hS hi))).1.1 hi
    · intro hi; exact (key i (Finset.mem_range.1 (hS' hi))).1.2 hi
  · ext i
    constructor
    · intro hi; exact (key i (Finset.mem_range.1 (hT hi))).2.1 hi
    · intro hi; exact (key i (Finset.mem_range.1 (hT' hi))).2.2 hi

/-! ## Exponential beats polynomial -/

lemma exists_pow_lt (K : ℕ) : ∃ n : ℕ, K * (2 * n + 1) ^ 2 * 3 ^ n < 4 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 4 / 3)
  have hpos : (0 : ℝ) < 1 / (9 * ((K : ℝ) + 1)) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hpos))
  refine ⟨N + 1, ?_⟩
  have h1 := hN (N + 1) (by omega)
  set n := N + 1 with hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by rw [hn]; push_cast; linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  have h43 : (0 : ℝ) < (4 / 3) ^ n := by positivity
  have h2 : 9 * ((K : ℝ) + 1) * (n : ℝ) ^ 2 < (4 / 3) ^ n := by
    rw [div_lt_div_iff₀ h43 (by positivity)] at h1
    linarith
  have h3 : ((4 : ℝ) / 3) ^ n * 3 ^ n = 4 ^ n := by rw [← mul_pow]; norm_num
  have h4 : (2 * (n : ℝ) + 1) ^ 2 ≤ 9 * (n : ℝ) ^ 2 := by nlinarith
  have h3n : (0 : ℝ) < 3 ^ n := by positivity
  have hK : (0 : ℝ) ≤ K := K.cast_nonneg
  have : (K : ℝ) * (2 * n + 1) ^ 2 * 3 ^ n < 4 ^ n := by
    rw [← h3]
    have : (K : ℝ) * (2 * n + 1) ^ 2 ≤ 9 * ((K : ℝ) + 1) * (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    have := lt_of_le_of_lt this h2
    exact mul_lt_mul_of_pos_right this h3n
  exact_mod_cast this

lemma exists_card_gt (M : ℕ) : ∃ n : ℕ, 2 * (2 * M * 12 ^ n) + 1 < n.centralBinom ^ 2 := by
  obtain ⟨n, hn⟩ := exists_pow_lt (4 * M + 1)
  refine ⟨n, ?_⟩
  have hc := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have hc2 : 16 ^ n ≤ (2 * n + 1) ^ 2 * n.centralBinom ^ 2 := by
    calc 16 ^ n = (4 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ ((2 * n + 1) * n.centralBinom) ^ 2 := Nat.pow_le_pow_left hc 2
      _ = _ := by ring
  have h12 : 2 * (2 * M * 12 ^ n) + 1 ≤ (4 * M + 1) * 12 ^ n := by
    have : 1 ≤ 12 ^ n := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  have hlt : (2 * (2 * M * 12 ^ n) + 1) * (2 * n + 1) ^ 2 < (2 * n + 1) ^ 2 * n.centralBinom ^ 2 := by
    calc (2 * (2 * M * 12 ^ n) + 1) * (2 * n + 1) ^ 2
        ≤ (4 * M + 1) * 12 ^ n * (2 * n + 1) ^ 2 := Nat.mul_le_mul_right _ h12
      _ = (4 * M + 1) * (2 * n + 1) ^ 2 * 3 ^ n * 4 ^ n := by
          rw [show (12 : ℕ) = 3 * 4 by norm_num, mul_pow]; ring
      _ < 4 ^ n * 4 ^ n := Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ = 16 ^ n := by rw [← mul_pow]; norm_num
      _ ≤ _ := hc2
  rw [mul_comm] at hlt
  exact Nat.lt_of_mul_lt_mul_left hlt

/-! ## The pigeonhole step -/

/-- For every integer-valued weight there are two different words over `{2,3,4,6}` whose
fully symmetric trees have the same size. -/
theorem exists_ws_collision (g : ℕ → ℤ) :
    ∃ w₁ w₂ : List ℕ, w₁ ≠ w₂ ∧ (∀ k ∈ w₁, Letter k) ∧ (∀ k ∈ w₂, Letter k) ∧
      ws g w₁ = ws g w₂ := by
  set M : ℕ := (g 0).natAbs + (g 2).natAbs + (g 3).natAbs + (g 4).natAbs + (g 6).natAbs with hMdef
  have hM : ∀ k, k = 0 ∨ Letter k → |g k| ≤ (M : ℤ) := by
    intro k hk
    rw [Int.abs_eq_natAbs]
    have : (g k).natAbs ≤ M := by
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
    exact_mod_cast this
  obtain ⟨n, hn⟩ := exists_card_gt M
  set P := Finset.powersetCard n (Finset.range (2 * n))
  set B : ℕ := 2 * M * 12 ^ n
  have hcard : (Finset.Icc (-(B : ℤ)) B).card < (P ×ˢ P).card := by
    rw [Int.card_Icc, Finset.card_product, Finset.card_powersetCard, Finset.card_range,
      ← Nat.centralBinom_eq_two_mul_choose, ← pow_two]
    omega
  have hmaps : ∀ p ∈ P ×ˢ P, ws g (word n p.1 p.2) ∈ Finset.Icc (-(B : ℤ)) B := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hb := ws_bound g M hM _ (word_letter n p.1 p.2)
    rw [word_prod n hp.1 hp.2] at hb
    have : (M : ℤ) * (2 * ((12 ^ n : ℕ) : ℤ) - 1) ≤ B := by
      have : (0 : ℤ) ≤ M := M.cast_nonneg
      simp only [B]; push_cast; nlinarith
    rw [Finset.mem_Icc]
    constructor <;> [linarith [neg_abs_le (ws g (word n p.1 p.2))];
      linarith [le_abs_self (ws g (word n p.1 p.2))]]
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  refine ⟨word n x.1 x.2, word n y.1 y.2, ?_, word_letter _ _ _, word_letter _ _ _, hfxy⟩
  intro hw
  rw [Finset.mem_product] at hx hy
  have hsub : ∀ {S}, S ∈ P → S ⊆ Finset.range (2 * n) := fun h => (Finset.mem_powersetCard.1 h).1
  obtain ⟨h1, h2⟩ := word_inj n (hsub hx.1) (hsub hx.2) (hsub hy.1) (hsub hy.2) hw
  exact hxy (Prod.ext h1 h2)

/-! ## Main theorems -/

lemma fsize_FS_scale (f : ℕ → ℝ) (g : ℕ → ℤ) (d : ℝ)
    (hfg : ∀ k, k = 0 ∨ Letter k → d * f k = g k) :
    ∀ w : List ℕ, (∀ k ∈ w, Letter k) → d * fsize f (FS w) = ws g w := by
  intro w
  induction w with
  | nil => intro _; rw [fsize_FS_nil, ws]; exact hfg 0 (Or.inl rfl)
  | cons k w ih =>
    intro hw
    rw [fsize_FS_cons, ws, mul_add, hfg k (Or.inr (hw k (by simp)))]
    push_cast
    rw [← ih (fun j hj => hw j (by simp [hj]))]
    ring

/-- **Main theorem (rational weights).**  For every `f : ℕ → ℚ` and every dissimilarity `D`,
the Colless-like index `C_{D,f}` is not sound. -/
theorem not_sound_rat (f : ℕ → ℚ) (D : List ℝ → ℝ) (hD : IsDissimilarity D) :
    ¬ Sound D (fun n => (f n : ℝ)) := by
  set d : ℕ := (f 0).den * (f 2).den * (f 3).den * (f 4).den * (f 6).den with hd
  have hd0 : 0 < d := by positivity
  have hint : ∀ k, k = 0 ∨ Letter k → ∃ z : ℤ, f k * d = z := by
    have aux : ∀ (q : ℚ) (m : ℕ), d = q.den * m → ∃ z : ℤ, q * d = z := by
      intro q m hm
      refine ⟨q.num * m, ?_⟩
      rw [hm]; push_cast
      rw [← mul_assoc, Rat.mul_den_eq_num]
    intro k hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact aux _ ((f 2).den * (f 3).den * (f 4).den * (f 6).den) (by rw [hd]; ring)
    · exact aux _ ((f 0).den * (f 3).den * (f 4).den * (f 6).den) (by rw [hd]; ring)
    · exact aux _ ((f 0).den * (f 2).den * (f 4).den * (f 6).den) (by rw [hd]; ring)
    · exact aux _ ((f 0).den * (f 2).den * (f 3).den * (f 6).den) (by rw [hd]; ring)
    · exact aux _ ((f 0).den * (f 2).den * (f 3).den * (f 4).den) (by rw [hd]; ring)
  let g : ℕ → ℤ := fun k => ⌊f k * d⌋
  have hfg : ∀ k, k = 0 ∨ Letter k → (d : ℝ) * (f k : ℝ) = g k := by
    intro k hk
    obtain ⟨z, hz⟩ := hint k hk
    have : ((g k : ℤ) : ℚ) = f k * d := by simp only [g, hz, Int.floor_intCast]
    have : ((d : ℚ) * f k : ℚ) = (g k : ℚ) := by rw [this, mul_comm]
    exact_mod_cast this
  obtain ⟨w₁, w₂, hne, h₁, h₂, heq⟩ := exists_ws_collision g
  have hs := fsize_FS_scale _ g d hfg
  have hfeq : fsize (fun n => (f n : ℝ)) (FS w₁) = fsize (fun n => (f n : ℝ)) (FS w₂) := by
    have e := (hs w₁ h₁).trans (heq ▸ (hs w₂ h₂).symm)
    exact mul_left_cancel₀ (by positivity) e
  refine not_sound_of_fsize_eq D (fun l hl hc => (hD.eq_zero_iff l hl).2 hc) _ hne
    (fun k hk => (h₁ k hk).two_le) (fun k hk => (h₂ k hk).two_le) hfeq

/-- **The Mir–Rosselló–Rotger conjecture (2018).**  No function `f : ℕ → ℕ` makes a
Colless-like index `C_{D,f}` sound, whatever the dissimilarity `D`. -/
theorem mir_rossello_rotger_conjecture :
    ∀ f : ℕ → ℕ, ∀ D : List ℝ → ℝ, IsDissimilarity D → ¬ Sound D (fun n => (f n : ℝ)) := by
  intro f D hD
  have := not_sound_rat (fun n => (f n : ℚ)) D hD
  simpa using this

end OpenQuestions.CollessLikeIndex

#print axioms OpenQuestions.CollessLikeIndex.mir_rossello_rotger_conjecture
#print axioms OpenQuestions.CollessLikeIndex.not_sound_rat
#print axioms OpenQuestions.CollessLikeIndex.exists_ws_collision
#print axioms OpenQuestions.CollessLikeIndex.sound_iff
