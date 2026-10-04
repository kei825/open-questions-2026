/-
Reduction step for R(C4, K_{1,39}) = 46, checked in Lean 4 + Mathlib.

Claim (the part *not* done by the SAT solver): let G be a graph on 46 vertices with no
4-cycle and minimum degree >= 7.  Then for every vertex v
  * deg v = 7                       (G is 7-regular),
  * every neighbour u of v has at most one neighbour inside N(v)  (N(v) spans a matching),
  * the number m(v) of edges inside N(v) satisfies 2 <= m(v) <= 3.

The SAT part (no such graph exists once the structure around one vertex is fixed) is
certified outside Lean by drat-trim and the verified checker cake_lpr; see ../VERIFY.md.
No `sorry`, `native_decide` or `axiom` is used.
-/
import Mathlib

open Finset

namespace RamseyC4Star

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- "G contains no 4-cycle", in the literal form used by the CNF: there are no vertices
a, b, c, d with a ≠ c, b ≠ d and edges ab, bc, cd, da (the other distinctness conditions
follow from irreflexivity). -/
def C4Free : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

variable {G}

/-- Two distinct vertices have at most one common neighbour. -/
lemma common_le_one (h : C4Free G) {a c : V} (hac : a ≠ c) :
    #(G.neighborFinset a ∩ G.neighborFinset c) ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  by_contra hxy
  simp only [mem_inter, SimpleGraph.mem_neighborFinset] at hx hy
  exact h a x c y hac hxy hx.1 (G.adj_symm hx.2) hy.2 (G.adj_symm hy.1)

/-- The private second neighbourhood of `u ∈ N(v)`. -/
def P (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V) : Finset V :=
  G.neighborFinset u \ insert v (G.neighborFinset v)

/-- `T v = ∑_{u ∈ N(v)} |N(u) ∩ N(v)|` (twice the number of edges inside N(v)). -/
def T (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  ∑ u ∈ G.neighborFinset v, #(G.neighborFinset u ∩ G.neighborFinset v)

lemma P_disjoint (h : C4Free G) (v : V) :
    ((G.neighborFinset v : Finset V) : Set V).PairwiseDisjoint (P G v) := by
  intro u hu u' hu' huu'
  simp only [SimpleGraph.coe_neighborFinset, SimpleGraph.mem_neighborSet] at hu hu'
  rw [Function.onFun, disjoint_left]
  intro w hw hw'
  simp only [P, mem_sdiff, mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hw hw'
  exact h u w u' v huu' hw.2.1 hw.1 (G.adj_symm hw'.1) (G.adj_symm hu') hu

lemma deg_le_P (v u : V) :
    G.degree u ≤ #(P G v u) + 1 + #(G.neighborFinset u ∩ G.neighborFinset v) := by
  have h1 : G.neighborFinset u ⊆ P G v u ∪ insert v (G.neighborFinset u ∩ G.neighborFinset v) := by
    intro w hw
    by_cases hwv : w ∈ insert v (G.neighborFinset v)
    · apply mem_union_right
      rcases mem_insert.1 hwv with h | h
      · exact mem_insert.2 (Or.inl h)
      · exact mem_insert.2 (Or.inr (mem_inter.2 ⟨hw, h⟩))
    · exact mem_union_left _ (mem_sdiff.2 ⟨hw, hwv⟩)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc #(G.neighborFinset u)
      ≤ #(P G v u ∪ insert v (G.neighborFinset u ∩ G.neighborFinset v)) := card_le_card h1
    _ ≤ #(P G v u) + #(insert v (G.neighborFinset u ∩ G.neighborFinset v)) := card_union_le _ _
    _ ≤ #(P G v u) + (#(G.neighborFinset u ∩ G.neighborFinset v) + 1) := by
        gcongr; exact card_insert_le _ _
    _ = _ := by ring

/-- Counting: `deg(v) * δ + 1 ≤ |V| + T(v)`. -/
lemma key (h : C4Free G) (δ : ℕ) (hdeg : ∀ w, δ ≤ G.degree w) (v : V) :
    G.degree v * δ + 1 ≤ Fintype.card V + T G v := by
  unfold T
  set N := G.neighborFinset v
  have hvN : v ∉ N := by simp [N]
  have hdisj : Disjoint (insert v N) (N.biUnion (P G v)) := by
    rw [disjoint_left]
    intro w hw hw'
    obtain ⟨u, -, hu⟩ := mem_biUnion.1 hw'
    exact (mem_sdiff.1 hu).2 hw
  have hcard : #(insert v N) + #(N.biUnion (P G v)) ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hdisj]; exact card_le_univ _
  have hpd : (N : Set V).PairwiseDisjoint (P G v) := P_disjoint h v
  rw [card_insert_of_notMem hvN, card_biUnion hpd] at hcard
  have hsum : ∑ u ∈ N, G.degree u ≤ ∑ u ∈ N, (#(P G v u) + 1 + #(G.neighborFinset u ∩ N)) :=
    sum_le_sum fun u _ => deg_le_P v u
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, mul_one] at hsum
  have hlow : #N * δ ≤ ∑ u ∈ N, G.degree u := by
    calc #N * δ = ∑ _u ∈ N, δ := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum fun u _ => hdeg u
  have hNd : #N = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
  rw [← hNd]
  omega

lemma T_le (h : C4Free G) (v : V) : T G v ≤ G.degree v := by
  unfold T
  calc ∑ u ∈ G.neighborFinset v, #(G.neighborFinset u ∩ G.neighborFinset v)
      ≤ ∑ _u ∈ G.neighborFinset v, 1 := by
        apply sum_le_sum
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        exact common_le_one h (G.ne_of_adj hu).symm
    _ = G.degree v := by simp

/-- `T v` is twice the number of edges inside `N(v)`, counted as pairs `u < w`. -/
lemma T_eq_two_mul [LinearOrder V] (v : V) :
    T G v = 2 * #((G.neighborFinset v ×ˢ G.neighborFinset v).filter
      (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)) := by
  set N := G.neighborFinset v
  have hT : T G v = #((N ×ˢ N).filter (fun p => G.Adj p.1 p.2)) := by
    unfold T
    rw [card_filter, sum_product]
    refine sum_congr rfl fun u _ => ?_
    rw [← card_filter]
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborFinset, N, and_comm]
  have hsplit : (N ×ˢ N).filter (fun p => G.Adj p.1 p.2) =
      (N ×ˢ N).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2) ∪
      (N ×ˢ N).filter (fun p => p.2 < p.1 ∧ G.Adj p.1 p.2) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_union, mem_product]
    constructor
    · rintro ⟨hab, hadj⟩
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exact Or.inl ⟨hab, hlt, hadj⟩
      · exact absurd hadj (heq ▸ G.irrefl)
      · exact Or.inr ⟨hab, hgt, hadj⟩
    · rintro (⟨hab, -, hadj⟩ | ⟨hab, -, hadj⟩) <;> exact ⟨hab, hadj⟩
  have hdisj : Disjoint ((N ×ˢ N).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2))
      ((N ×ˢ N).filter (fun p => p.2 < p.1 ∧ G.Adj p.1 p.2)) := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [mem_filter] at h1 h2
    exact lt_asymm h1.2.1 h2.2.1
  have hswap : #((N ×ˢ N).filter (fun p => p.2 < p.1 ∧ G.Adj p.1 p.2)) =
      #((N ×ˢ N).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)) := by
    apply card_nbij' Prod.swap Prod.swap
    · rintro ⟨a, b⟩ hp
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.1, G.adj_symm hp.2.2⟩
    · rintro ⟨a, b⟩ hp
      simp only [coe_filter, mem_product, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.1, G.adj_symm hp.2.2⟩
    · intro p _; simp
    · intro p _; simp
  rw [hT, hsplit, card_union_of_disjoint hdisj, hswap]
  ring

/-- Main theorem: the reduction used to build the two CNFs (m = 2 and m = 3). -/
theorem reduction (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj] (h : C4Free G)
    (hdeg : ∀ w, 7 ≤ G.degree w) (v : Fin 46) :
    G.degree v = 7 ∧
    (∀ u ∈ G.neighborFinset v, #(G.neighborFinset u ∩ G.neighborFinset v) ≤ 1) ∧
    2 ≤ #((G.neighborFinset v ×ˢ G.neighborFinset v).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)) ∧
    #((G.neighborFinset v ×ˢ G.neighborFinset v).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)) ≤ 3 := by
  have hk := key h 7 hdeg v
  have ht := T_le h v
  have h2 := T_eq_two_mul (G := G) v
  have hd := hdeg v
  simp only [Fintype.card_fin] at hk
  refine ⟨by omega, ?_, by omega, by omega⟩
  intro u hu
  rw [SimpleGraph.mem_neighborFinset] at hu
  exact common_le_one h (G.ne_of_adj hu).symm

end RamseyC4Star
