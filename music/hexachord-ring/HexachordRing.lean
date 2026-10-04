/-
# Morris's 50-pitch-class hexachordal ring does not exist

R. Morris, "Mathematics and the Twelve-Tone System: Past, Present, and Future"
(MCM 2007 talk, p. 15; also Perspectives of New Music 45(2) (2007) 76–107) asks:

> Another open question is if there exist 50-pc rings that imbricate an instance of
> each of the 50 hexachordal set-classes?

A *50-pc ring* is a cyclic sequence `x 0, x 1, …, x 49` of pitch classes (elements of
`ZMod 12`).  It *imbricates* the 50 windows `W i = {x i, x (i+1), …, x (i+5)}` (indices
mod 50).  The question asks for a ring in which every window is a hexachord (six distinct
pitch classes) and the 50 windows lie in 50 different TnI set-classes (so each of the 50
hexachordal set-classes occurs exactly once).

We prove that no such ring exists (`no_hexachordal_ring`, and `no_ring_imbricating_all_classes`
for the literal wording "every class occurs among the windows").

Proof idea (a parity argument):
* (a) the parity of the number of odd pitch classes in a hexachord is a TnI invariant
  (`oddCount_parity_of_TnIEquiv`);
* (b) of the 50 hexachordal TnI classes exactly 25 are "odd" (`card_classes`,
  `classes_distinct`, `exists_rep`, `card_odd_classes`);
* (c) in any ring, `∑ i, #(odd pcs in W i) = 6 * #(odd pcs in the ring)` is even, so an even
  number of windows are odd; but a ring meeting all 50 classes would have 25 odd windows.

The finite facts (b) are checked by `decide +kernel` on boolean functions of 12-bit masks
(kernel reduction only; no `native_decide`, no extra axioms).
-/
import Mathlib

namespace OpenQuestions.HexachordRing

open Finset

/-! ## The statement -/

/-- The `i`-th window of the ring `x`: the pitch classes at positions `i, i+1, …, i+5`
(positions are taken mod 50, since `Fin 50` addition wraps around). -/
def window (x : Fin 50 → ZMod 12) (i : Fin 50) : Finset (ZMod 12) :=
  univ.image fun k : Fin 6 => x (i + Fin.castLE (by norm_num) k)

/-- Two pitch-class sets are TnI-equivalent (same set-class) if one is obtained from the
other by a transposition `p ↦ p + t` possibly preceded by the inversion `p ↦ -p`. -/
def TnIEquiv (S T : Finset (ZMod 12)) : Prop :=
  ∃ s t : ZMod 12, (s = 1 ∨ s = -1) ∧ S.image (fun p => s * p + t) = T

/-- The number of odd pitch classes (1, 3, 5, 7, 9, 11) in a set. -/
def oddCount (S : Finset (ZMod 12)) : ℕ :=
  (S.filter fun p => p.val % 2 = 1).card

/-! ## Transformations -/

/-- `sign false = 1`, `sign true = -1`. -/
def sign (b : Bool) : ZMod 12 := if b then -1 else 1

/-- The TnI operation `p ↦ ±p + t`. -/
def aff (b : Bool) (t : ZMod 12) (p : ZMod 12) : ZMod 12 := sign b * p + t

lemma sign_mul_sign (b : Bool) : sign b * sign b = 1 := by
  cases b <;> decide

lemma sign_eq (b : Bool) : sign b = 1 ∨ sign b = -1 := by
  cases b <;> simp [sign]

lemma aff_injective (b : Bool) (t : ZMod 12) : Function.Injective (aff b t) := by
  intro p q h
  have h' : sign b * (sign b * p + t) = sign b * (sign b * q + t) := by
    simp only [aff] at h; rw [h]
  have e : ∀ r : ZMod 12, sign b * (sign b * r + t) = r + sign b * t := by
    intro r; rw [mul_add, ← mul_assoc, sign_mul_sign, one_mul]
  rw [e, e] at h'
  exact add_right_cancel h'

/-- If `S` and `T` are both carried onto the same set `R` by TnI operations, then `S` and
`T` are TnI-equivalent. -/
lemma tniEquiv_of_common {S T R : Finset (ZMod 12)} {b₁ b₂ : Bool} {t₁ t₂ : ZMod 12}
    (h₁ : S.image (aff b₁ t₁) = R) (h₂ : T.image (aff b₂ t₂) = R) : TnIEquiv S T := by
  refine ⟨sign b₂ * sign b₁, sign b₂ * (t₁ - t₂), ?_, ?_⟩
  · cases b₁ <;> cases b₂ <;> simp [sign]
  · set g : ZMod 12 → ZMod 12 := fun q => sign b₂ * (q - t₂) with hg
    have e₁ : S.image (fun p => sign b₂ * sign b₁ * p + sign b₂ * (t₁ - t₂))
        = (S.image (aff b₁ t₁)).image g := by
      rw [image_image]; congr 1; funext p; simp only [hg, aff, Function.comp]; ring
    have e₂ : (T.image (aff b₂ t₂)).image g = T := by
      rw [image_image]
      conv_rhs => rw [← image_id (s := T)]
      congr 1; funext q
      simp only [hg, aff, Function.comp, id]
      rw [add_sub_cancel_right, ← mul_assoc, sign_mul_sign, one_mul]
    rw [e₁, h₁, ← h₂, e₂]

/-! ## (a) Parity is a TnI invariant -/

lemma val_parity (s t p : ZMod 12) (hs : s = 1 ∨ s = -1) :
    (s * p + t).val % 2 = (p.val + t.val) % 2 := by
  rcases hs with rfl | rfl <;> revert p t <;> decide

theorem oddCount_parity_of_TnIEquiv {S T : Finset (ZMod 12)} (hS : S.card = 6)
    (h : TnIEquiv S T) : oddCount S % 2 = oddCount T % 2 := by
  obtain ⟨s, t, hs, rfl⟩ := h
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  have hinj : Function.Injective fun p : ZMod 12 => s * p + t := by
    intro p q h
    have h' : s * (s * p + t - t) = s * (s * q + t - t) := by
      simp only at h; rw [h]
    simpa [← mul_assoc, hs2] using h'
  unfold oddCount
  rw [filter_image, card_image_of_injective _ hinj]
  simp only [val_parity s t _ hs]
  rcases Nat.mod_two_eq_zero_or_one t.val with ht | ht
  · have : ∀ p : ZMod 12, (p.val + t.val) % 2 = 1 ↔ p.val % 2 = 1 := by intro p; omega
    simp only [this]
  · have : ∀ p : ZMod 12, (p.val + t.val) % 2 = 1 ↔ ¬ p.val % 2 = 1 := by intro p; omega
    simp only [this]
    have := card_filter_add_card_filter_not (s := S) (fun p : ZMod 12 => p.val % 2 = 1)
    omega

/-! ## (b) The 50 hexachordal set-classes: a finite certificate

A pitch-class set `S` is encoded by its 12-bit mask `∑ p ∈ S, 2 ^ p`.  Each class is
represented by its *prime mask*: the smallest mask among the 24 TnI images of its members.
The finite checks below are stated on natural numbers (so that the kernel evaluates them
quickly with `decide`), and then transported to finsets of `ZMod 12`. -/

/-- The 50 prime masks (sorted). -/
def primeMasks : List ℕ :=
  [63, 95, 111, 119, 159, 175, 183, 187, 189, 207, 215, 219, 231, 287, 303, 311, 315, 317,
   335, 343, 347, 349, 359, 363, 365, 371, 399, 407, 411, 423, 427, 455, 591, 599, 603, 605,
   615, 619, 663, 667, 679, 683, 685, 691, 693, 715, 717, 723, 819, 1365]

/-- The `c`-th prime mask. -/
def primeMask (c : ℕ) : ℕ := primeMasks.getD c 0

/-- The pitch-class set with mask `m`. -/
def ofMask (m : ℕ) : Finset (ZMod 12) := univ.filter fun p => m.testBit p.val

/-- The representative hexachord of class `c`. -/
def rep (c : Fin 50) : Finset (ZMod 12) := ofMask (primeMask c)

/-- The 12-bit mask of a pitch-class set. -/
def mask (S : Finset (ZMod 12)) : ℕ := ∑ p ∈ S, 2 ^ p.val

/-- Number of set bits among the 12 low bits. -/
def bits (m : ℕ) : ℕ := ((range 12).filter fun i => m.testBit i).card

/-- Number of set bits in odd positions among the 12 low bits. -/
def oddBits (m : ℕ) : ℕ := ((range 12).filter fun i => i % 2 = 1 ∧ m.testBit i).card

/-- `aff b t` on `{0, …, 11}`. -/
def affN (b : Bool) (t i : ℕ) : ℕ := if b then (12 - i + t) % 12 else (i + t) % 12

/-- Rotation of a 12-bit mask by `t` (the transposition `p ↦ p + t`). -/
def rot (m t : ℕ) : ℕ := ((m <<< t) ||| (m >>> (12 - t))) &&& 4095

/-- The mask of `-S` (the inversion `p ↦ -p`). -/
def negMask (m : ℕ) : ℕ :=
  (List.range 12).foldl
    (fun acc p => if m.testBit p then acc ||| (1 <<< ((12 - p) % 12)) else acc) 0

/-- A certificate for the set with mask `m`: the index of its prime form and a TnI operation
`(b, t)` carrying it there.  This is only a hint for the kernel: `GoodN` re-checks it, so a
wrong hint could only make `decide` fail, never prove something false. -/
def cert (m : ℕ) : ℕ × Bool × ℕ :=
  let n := negMask m
  let cands := (List.range 12).flatMap fun t => [(rot m t, (false, t)), (rot n t, (true, t))]
  let best := cands.foldl (fun acc x => if x.1 < acc.1 then x else acc) (4096, (false, 0))
  (primeMasks.idxOf best.1, best.2)

/-- What the certificate `w = (c, b, t)` must satisfy for the mask `m`: the operation
`aff b t` maps the set with mask `m` into the representative `c`, and both have the same
parity of odd pitch classes. -/
def GoodN (m : ℕ) (w : ℕ × Bool × ℕ) : Prop :=
  w.1 < 50 ∧ w.2.2 < 12 ∧
    (∀ i < 12, m.testBit i = true → (primeMask w.1).testBit (affN w.2.1 w.2.2 i) = true) ∧
    oddBits m % 2 = oddBits (primeMask w.1) % 2

/-- `GoodN` as a boolean function (what the kernel actually evaluates). -/
def goodB (m : ℕ) (w : ℕ × Bool × ℕ) : Bool :=
  decide (w.1 < 50) && decide (w.2.2 < 12) &&
    (List.range 12).all (fun i => !(m.testBit i) || (primeMask w.1).testBit (affN w.2.1 w.2.2 i)) &&
    (oddBits m % 2 == oddBits (primeMask w.1) % 2)

lemma goodB_sound {m : ℕ} {w : ℕ × Bool × ℕ} (h : goodB m w = true) : GoodN m w := by
  simp only [goodB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  refine ⟨h₁, h₂, fun i hi hb => ?_, h₄⟩
  rcases h₃ i hi with h | h
  · rw [hb] at h; exact absurd h Bool.noConfusion
  · exact h

/-- The certificate check for the masks `256 * a + b`, `b < 256`.  (The `2 ^ 12` masks are
split into 16 chunks so that each kernel computation stays small.) -/
def chunkB (a : ℕ) : Bool :=
  (List.range 256).all fun b => !(bits (256 * a + b) == 6) || goodB (256 * a + b) (cert (256 * a + b))

theorem chunk_0 : chunkB 0 = true := by decide +kernel
theorem chunk_1 : chunkB 1 = true := by decide +kernel
theorem chunk_2 : chunkB 2 = true := by decide +kernel
theorem chunk_3 : chunkB 3 = true := by decide +kernel
theorem chunk_4 : chunkB 4 = true := by decide +kernel
theorem chunk_5 : chunkB 5 = true := by decide +kernel
theorem chunk_6 : chunkB 6 = true := by decide +kernel
theorem chunk_7 : chunkB 7 = true := by decide +kernel
theorem chunk_8 : chunkB 8 = true := by decide +kernel
theorem chunk_9 : chunkB 9 = true := by decide +kernel
theorem chunk_10 : chunkB 10 = true := by decide +kernel
theorem chunk_11 : chunkB 11 = true := by decide +kernel
theorem chunk_12 : chunkB 12 = true := by decide +kernel
theorem chunk_13 : chunkB 13 = true := by decide +kernel
theorem chunk_14 : chunkB 14 = true := by decide +kernel
theorem chunk_15 : chunkB 15 = true := by decide +kernel

theorem cover_checkN (m : ℕ) (hm : m < 4096) (h : bits m = 6) : GoodN m (cert m) := by
  have key : chunkB (m / 256) = true := by
    have hk : m / 256 < 16 := by omega
    generalize m / 256 = k at hk
    interval_cases k
    exacts [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7,
      chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15]
  simp only [chunkB, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at key
  have := key (m % 256) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at this
  rcases this with h' | h'
  · exact absurd h h'
  · exact goodB_sound h'

/-! ### From masks to finsets -/

lemma mem_ofMask {m : ℕ} {p : ZMod 12} : p ∈ ofMask m ↔ m.testBit p.val = true := by
  simp [ofMask]

lemma aff_val_check : ∀ b : Bool, ∀ i : ℕ, i < 12 → ∀ t : ℕ, t < 12 →
    (aff b (t : ZMod 12) (i : ZMod 12)).val = affN b t i := by
  decide +kernel

lemma aff_val (b : Bool) (t : ZMod 12) (p : ZMod 12) :
    (aff b t p).val = affN b t.val p.val := by
  have := aff_val_check b p.val (ZMod.val_lt p) t.val (ZMod.val_lt t)
  rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this

lemma image_val_filter_ofMask (m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((ofMask m).filter fun p => P p.val).image ZMod.val
      = (range 12).filter fun i => P i ∧ m.testBit i := by
  ext i
  simp only [mem_image, mem_filter, mem_range, mem_ofMask]
  constructor
  · rintro ⟨p, ⟨hp, hP⟩, rfl⟩
    exact ⟨ZMod.val_lt p, hP, hp⟩
  · rintro ⟨hi, hP, hb⟩
    refine ⟨(i : ZMod 12), ⟨?_, ?_⟩, ZMod.val_cast_of_lt hi⟩ <;> rwa [ZMod.val_cast_of_lt hi]

lemma card_ofMask (m : ℕ) : (ofMask m).card = bits m := by
  have := image_val_filter_ofMask m (fun _ => True)
  simp only [filter_true_of_mem (fun _ _ => trivial), true_and] at this
  rw [bits, ← this, card_image_of_injective _ (ZMod.val_injective 12)]

lemma oddCount_ofMask (m : ℕ) : oddCount (ofMask m) = oddBits m := by
  rw [oddCount, oddBits, ← image_val_filter_ofMask m (fun i => i % 2 = 1),
    card_image_of_injective _ (ZMod.val_injective 12)]

lemma testBit_mask (S : Finset (ZMod 12)) (p : ZMod 12) :
    (mask S).testBit p.val = true ↔ p ∈ S := by
  have e : mask S = ∑ i ∈ S.image ZMod.val, 2 ^ i := by
    rw [mask, sum_image (fun a _ b _ h => ZMod.val_injective 12 h)]
  rw [e, ← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow,
    mem_image]
  constructor
  · rintro ⟨q, hq, hqp⟩; rwa [← ZMod.val_injective 12 hqp]
  · intro hp; exact ⟨p, hp, rfl⟩

lemma ofMask_mask (S : Finset (ZMod 12)) : ofMask (mask S) = S := by
  ext p; rw [mem_ofMask, testBit_mask]

lemma mask_lt (S : Finset (ZMod 12)) : mask S < 4096 := by
  have h : mask S ≤ ∑ p : ZMod 12, 2 ^ p.val := sum_le_sum_of_subset (subset_univ S)
  have h' : ∑ p : ZMod 12, 2 ^ p.val = 4095 := by decide
  omega

theorem card_rep (c : Fin 50) : (rep c).card = 6 := by
  rw [rep, card_ofMask]; revert c; decide +kernel

/-! ### The class statements -/

/-- Every hexachord is carried onto one of the 50 representatives, with the same parity. -/
theorem exists_class (S : Finset (ZMod 12)) (h : S.card = 6) :
    ∃ c : Fin 50, (∃ b t, S.image (aff b t) = rep c) ∧
      oddCount S % 2 = oddCount (rep c) % 2 := by
  have hS := ofMask_mask S
  have hbits : bits (mask S) = 6 := by rw [← card_ofMask, hS, h]
  have hgood := cover_checkN (mask S) (mask_lt S) hbits
  generalize cert (mask S) = w at hgood
  obtain ⟨c, b, t⟩ := w
  obtain ⟨hc, ht, h₁, h₂⟩ := hgood
  refine ⟨⟨c, hc⟩, ⟨b, (t : ZMod 12), ?_⟩, ?_⟩
  · apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
      have := h₁ p.val (ZMod.val_lt p) ((testBit_mask S p).2 hp)
      rw [rep, mem_ofMask, aff_val, ZMod.val_cast_of_lt ht]
      exact this
    · rw [card_rep, card_image_of_injective _ (aff_injective _ _), h]
  · rw [rep, oddCount_ofMask, ← hS, oddCount_ofMask]
    exact h₂

/-- Every hexachord belongs to the class of one of the 50 representatives. -/
theorem exists_rep (S : Finset (ZMod 12)) (h : S.card = 6) :
    ∃ c : Fin 50, TnIEquiv (rep c) S := by
  obtain ⟨c, ⟨b, t, hbt⟩, -⟩ := exists_class S h
  exact ⟨c, tniEquiv_of_common (b₁ := false) (t₁ := 0)
    (by rw [show aff false 0 = id from funext fun p => by simp [aff, sign]]; simp) hbt⟩

/-- Every representative is a hexachord. -/
theorem card_classes (c : Fin 50) : (rep c).card = 6 := card_rep c

/-! ### The 50 representatives are pairwise inequivalent -/

/-- The mask of the image of the set with mask `m` under `aff b t`, computed on `ℕ`. -/
def imgMask (b : Bool) (t m : ℕ) : ℕ :=
  ∑ i ∈ (range 12).filter (fun i => m.testBit i), 2 ^ affN b t i

lemma testBit_sum_two_pow (T : Finset ℕ) (k : ℕ) :
    (∑ j ∈ T, 2 ^ j).testBit k = true ↔ k ∈ T := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

lemma affN_lt (b : Bool) (t i : ℕ) : affN b t i < 12 := by
  unfold affN; split <;> exact Nat.mod_lt _ (by norm_num)

lemma affN_inj {b : Bool} {t i i' : ℕ} (hi : i < 12) (hi' : i' < 12)
    (h : affN b t i = affN b t i') : i = i' := by
  cases b <;> simp only [affN, Bool.false_eq_true, if_true, if_false] at h <;> omega

lemma imgMask_eq (b : Bool) (t m : ℕ) :
    imgMask b t m = ∑ j ∈ ((range 12).filter fun i => m.testBit i).image (affN b t), 2 ^ j := by
  rw [imgMask, sum_image]
  intro i hi i' hi' h
  simp only [coe_filter, mem_range] at hi hi'
  exact affN_inj hi.1 hi'.1 h

lemma testBit_imgMask (b : Bool) (t m k : ℕ) :
    (imgMask b t m).testBit k = true ↔ ∃ i, i < 12 ∧ m.testBit i = true ∧ affN b t i = k := by
  rw [imgMask_eq, testBit_sum_two_pow, mem_image]
  simp only [mem_filter, mem_range, and_assoc]

lemma imgMask_lt (b : Bool) (t m : ℕ) : imgMask b t m < 4096 := by
  rw [imgMask_eq]
  have hsub : ((range 12).filter fun i => m.testBit i).image (affN b t) ⊆ range 12 := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := mem_image.1 hj
    exact mem_range.2 (affN_lt b t i)
  have h := sum_le_sum_of_subset (f := fun j => 2 ^ j) hsub
  have h' : ∑ j ∈ range 12, 2 ^ j = 4095 := by decide
  omega

lemma image_ofMask (b : Bool) (t : ZMod 12) (m : ℕ) :
    (ofMask m).image (aff b t) = ofMask (imgMask b t.val m) := by
  ext p
  rw [mem_image, mem_ofMask, testBit_imgMask]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.val, ZMod.val_lt q, mem_ofMask.1 hq, (aff_val b t q).symm⟩
  · rintro ⟨i, hi, hb, he⟩
    refine ⟨(i : ZMod 12), mem_ofMask.2 (by rwa [ZMod.val_cast_of_lt hi]), ?_⟩
    apply ZMod.val_injective 12
    rw [aff_val, ZMod.val_cast_of_lt hi, he]

lemma eq_of_ofMask_eq {m m' : ℕ} (hm : m < 4096) (hm' : m' < 4096)
    (h : ofMask m = ofMask m') : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrArg (fun S => (i : ZMod 12) ∈ S) h
    simp only [mem_ofMask, ZMod.val_cast_of_lt hi, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  · have h12 : (4096 : ℕ) ≤ 2 ^ i :=
      calc (4096 : ℕ) = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

lemma primeMask_lt : ∀ c : ℕ, c < 50 → primeMask c < 4096 := by decide

/-- The certificate check that no TnI image of a representative `c` (with `c / 10 = k`) has
the mask of another representative `c'` (split into 5 blocks). -/
def orbitB (k : ℕ) : Bool :=
  (List.range 10).all fun j => [false, true].all fun b => (List.range 12).all fun t =>
    (List.range 50).all fun c' => (10 * k + j == c') || (imgMask b t (primeMask (10 * k + j)) != primeMask c')

theorem orbit_0 : orbitB 0 = true := by decide +kernel
theorem orbit_1 : orbitB 1 = true := by decide +kernel
theorem orbit_2 : orbitB 2 = true := by decide +kernel
theorem orbit_3 : orbitB 3 = true := by decide +kernel
theorem orbit_4 : orbitB 4 = true := by decide +kernel

lemma orbit_check (c c' : ℕ) (hc : c < 50) (hc' : c' < 50) (h : c ≠ c') (b : Bool) (t : ℕ)
    (ht : t < 12) : imgMask b t (primeMask c) ≠ primeMask c' := by
  have key : orbitB (c / 10) = true := by
    have hk : c / 10 < 5 := by omega
    generalize c / 10 = k at hk
    interval_cases k
    exacts [orbit_0, orbit_1, orbit_2, orbit_3, orbit_4]
  simp only [orbitB, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, List.mem_cons, List.not_mem_nil, or_false] at key
  have := key (c % 10) (Nat.mod_lt _ (by norm_num)) b (by cases b <;> simp) t ht c' hc'
  rw [Nat.div_add_mod] at this
  rcases this with h' | h'
  · exact absurd h' h
  · exact h'

/-- The 50 representatives lie in 50 different set-classes. -/
theorem classes_distinct (c c' : Fin 50) (h : c ≠ c') : ¬ TnIEquiv (rep c) (rep c') := by
  rintro ⟨s, t, hs, he⟩
  have hs' : ∃ b, sign b = s := by
    rcases hs with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨b, rfl⟩ := hs'
  have he' : (rep c).image (aff b t) = rep c' := he
  rw [rep, rep, image_ofMask] at he'
  exact orbit_check c c' c.isLt c'.isLt (fun e => h (Fin.ext e)) b t.val (ZMod.val_lt t)
    (eq_of_ofMask_eq (imgMask_lt _ _ _) (primeMask_lt c' c'.isLt) he')

/-- Exactly 25 of the 50 classes are odd. -/
theorem card_odd_classes :
    (univ.filter fun c : Fin 50 => oddCount (rep c) % 2 = 1).card = 25 := by
  simp only [rep, oddCount_ofMask]
  decide +kernel

/-! ## (c) Double counting in the ring -/

/-- Indicator of an odd pitch class. -/
def oddInd (p : ZMod 12) : ℕ := if p.val % 2 = 1 then 1 else 0

lemma oddCount_window (x : Fin 50 → ZMod 12) (i : Fin 50) (h : (window x i).card = 6) :
    oddCount (window x i) = ∑ k : Fin 6, oddInd (x (i + Fin.castLE (by norm_num) k)) := by
  set g : Fin 6 → ZMod 12 := fun k => x (i + Fin.castLE (by norm_num) k) with hg
  have hinj : Set.InjOn g (univ : Finset (Fin 6)) := by
    apply card_image_iff.mp
    simpa [window, hg] using h
  unfold oddCount window
  rw [← hg, filter_image, card_image_of_injOn (hinj.mono (by simp)), card_filter]
  rfl

lemma sum_oddCount (x : Fin 50 → ZMod 12) (h : ∀ i, (window x i).card = 6) :
    ∑ i, oddCount (window x i) = 6 * ∑ i, oddInd (x i) := by
  simp_rw [oddCount_window x _ (h _)]
  rw [sum_comm]
  have e : ∀ k : Fin 6, ∑ i : Fin 50, oddInd (x (i + Fin.castLE (by norm_num) k))
      = ∑ i : Fin 50, oddInd (x i) := fun k =>
    Equiv.sum_comp (Equiv.addRight (Fin.castLE (by norm_num) k)) (fun i => oddInd (x i))
  simp_rw [e]
  simp

/-! ## The theorem -/

/-- **Morris's question has a negative answer.** There is no ring of 50 pitch classes whose
50 windows of 6 consecutive pitch classes are hexachords lying in 50 pairwise different
TnI set-classes (i.e. that imbricates each of the 50 hexachordal set-classes once). -/
theorem no_hexachordal_ring :
    ¬ ∃ x : Fin 50 → ZMod 12,
      (∀ i, (window x i).card = 6) ∧
      (∀ i j, i ≠ j → ¬ TnIEquiv (window x i) (window x j)) := by
  rintro ⟨x, hcard, hneq⟩
  choose f hf using fun i => exists_class (window x i) (hcard i)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    obtain ⟨⟨b₁, t₁, h₁⟩, -⟩ := hf i
    obtain ⟨⟨b₂, t₂, h₂⟩, -⟩ := hf j
    rw [hij] at h₁
    exact hneq i j hne (tniEquiv_of_common h₁ h₂)
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  -- the parities of the windows are the parities of all 50 classes, 25 of which are odd
  have h25 : ∑ i, oddCount (window x i) % 2 = 25 := by
    rw [Finset.sum_congr rfl fun i _ => (hf i).2,
      hbij.sum_comp (fun c => oddCount (rep c) % 2)]
    decide +kernel
  -- but the total number of odd entries over all windows is even
  have hsum := sum_oddCount x hcard
  have hmod := Finset.sum_nat_mod (univ : Finset (Fin 50)) 2 fun i => oddCount (window x i)
  rw [h25, hsum] at hmod
  omega

/-! ## The same statement in Morris's words

"A 50-pc ring that imbricates an instance of each of the 50 hexachordal set-classes": every
hexachord is TnI-equivalent to one of the 50 windows.  Here we do not assume that the
windows are hexachords; this follows. -/

lemma TnIEquiv.exists_aff {S T : Finset (ZMod 12)} (h : TnIEquiv S T) :
    ∃ b t, S.image (aff b t) = T := by
  obtain ⟨s, t, hs, he⟩ := h
  rcases hs with rfl | rfl
  · exact ⟨false, t, by
      rw [show aff false t = fun p => 1 * p + t from funext fun p => by simp [aff, sign]]
      exact he⟩
  · exact ⟨true, t, by
      rw [show aff true t = fun p => -1 * p + t from funext fun p => by simp [aff, sign]]
      exact he⟩

lemma aff_comp (b t b' t') : aff b t ∘ aff b' t' = aff (xor b b') (sign b * t' + t) := by
  funext p
  cases b <;> cases b' <;> simp [aff, sign] <;> ring

/-- **Morris's question, as worded: negative.** No ring of 50 pitch classes has, among its
50 windows of 6 consecutive pitch classes, a member of every hexachordal set-class. -/
theorem no_ring_imbricating_all_classes :
    ¬ ∃ x : Fin 50 → ZMod 12,
      ∀ S : Finset (ZMod 12), S.card = 6 → ∃ i, TnIEquiv S (window x i) := by
  rintro ⟨x, hx⟩
  choose g hg using fun c : Fin 50 => hx (rep c) (card_rep c)
  have hinj : Function.Injective g := by
    intro c c' hcc
    by_contra hne
    obtain ⟨b₁, t₁, h₁⟩ := (hg c).exists_aff
    obtain ⟨b₂, t₂, h₂⟩ := (hg c').exists_aff
    rw [hcc] at h₁
    exact classes_distinct c c' hne (tniEquiv_of_common h₁ h₂)
  have hbij : Function.Bijective g := Finite.injective_iff_bijective.mp hinj
  apply no_hexachordal_ring
  refine ⟨x, fun i => ?_, fun i j hij hW => ?_⟩
  · obtain ⟨c, rfl⟩ := hbij.2 i
    obtain ⟨b, t, h⟩ := (hg c).exists_aff
    rw [← h, card_image_of_injective _ (aff_injective _ _), card_rep]
  · obtain ⟨c, rfl⟩ := hbij.2 i
    obtain ⟨c', rfl⟩ := hbij.2 j
    obtain ⟨b₁, t₁, h₁⟩ := (hg c).exists_aff
    obtain ⟨b₂, t₂, h₂⟩ := (hg c').exists_aff
    obtain ⟨b, t, h⟩ := hW.exists_aff
    have h₃ : (rep c).image (aff (xor b b₁) (sign b * t₁ + t)) = window x (g c') := by
      rw [← aff_comp, ← image_image, h₁, h]
    exact classes_distinct c c' (fun e => hij (by rw [e])) (tniEquiv_of_common h₃ h₂)

end OpenQuestions.HexachordRing

#print axioms OpenQuestions.HexachordRing.no_hexachordal_ring
#print axioms OpenQuestions.HexachordRing.no_ring_imbricating_all_classes
#print axioms OpenQuestions.HexachordRing.classes_distinct
#print axioms OpenQuestions.HexachordRing.exists_rep
#print axioms OpenQuestions.HexachordRing.card_odd_classes
#print axioms OpenQuestions.HexachordRing.oddCount_parity_of_TnIEquiv
