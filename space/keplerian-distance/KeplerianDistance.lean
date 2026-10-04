import Mathlib

/-!
# Twelve critical points of the Keplerian distance for two coplanar confocal ellipses

Gronchi, Baù and Grassi (Celest. Mech. Dyn. Astron. 135:48 (2023), arXiv:2305.13900, §7)
prove that the squared distance `d²` between the points of two coplanar ellipses with a
common focus has at most `12` critical points, and conjecture that `10` is the true maximum
("we got at most 10 critical points that we think is the maximum number").

This file proves that `12` is attained, so the planar conjecture is false and the maximum in
the planar case is exactly `12`.

## The example

Both conics have their focus at the origin and are parametrised by the true anomaly:
`X(f) = p / (1 + e cos f) · (cos (f + ϖ), sin (f + ϖ))`, where `ϖ` is the direction of the
pericentre.

* orbit 1: `p₁ = 1`, `e₁ = 493/500`, `ϖ₁ = 0`;
* orbit 2: `p₂ = 113/500`, `e₂ = 4983/5000`, `ϖ₂ = ω = 2 arctan (89/4000)`.

`sqDist (f₁, f₂) = |X₁(f₁) - X₂(f₂)|²` is the function `d²` of the paper, lifted from the
torus to `ℝ²`.

## Main result

`twelve_critical_points`: there are `P : Fin 12 → ℝ × ℝ` such that
* every `P i` is a critical point: `HasFDerivAt sqDist 0 (P i)`;
* the twelve points are pairwise distinct on the torus `(ℝ/2πℤ)²`;
* `d² = 0` exactly at `P 0` and `P 2` (the two orbit intersections); the other ten
  critical points are not intersections.

## Method

Write `t = tan (f₁/2)`, so `cos f₁ = (1-t²)/(1+t²)`, `sin f₁ = 2t/(1+t²)`.
* Non-intersection critical points: the paper's equations (38), (39) are linear in
  `(cos f₂, sin f₂)`; solving them gives `cos f₂ = -δ/μ`, `sin f₂ = -α (cos f₂ + e₂)/β`, and
  the condition `cos² f₂ + sin² f₂ = 1` is the paper's (41). After clearing denominators
  (41) is the polynomial `Fq t = 0`. We find ten rational intervals where `Fq` changes sign
  (intermediate value theorem), define `f₂` as the argument of `cos f₂ + i sin f₂`, and check
  by exact algebra that both partial derivatives vanish.
* Intersections: `X₁(f₁) = X₂(f₁ - ω)` iff the quadratic `Iq t` vanishes; it has two roots,
  again located by sign changes.
* Distinctness: the twelve values of `t` lie in pairwise disjoint intervals and
  `f₁ = 2 arctan t ∈ (-π, π)`.
-/

namespace OpenQuestions.KeplerianDistance

open Real

noncomputable section

/-! ## The two orbits and the squared distance -/

/-- Point with true anomaly `f` on the conic with focus at the origin, parameter `p`,
eccentricity `e` and pericentre direction `ϖ`. -/
def orbitPoint (p e ϖ f : ℝ) : ℝ × ℝ :=
  (p / (1 + e * cos f) * cos (f + ϖ), p / (1 + e * cos f) * sin (f + ϖ))

def p₁ : ℝ := 1
def e₁ : ℝ := 493 / 500
def p₂ : ℝ := 113 / 500
def e₂ : ℝ := 4983 / 5000
/-- `tan (ω / 2)`. -/
def τ : ℝ := 89 / 4000
/-- Angle between the two pericentres. -/
def ω : ℝ := 2 * arctan τ

/-- First orbit. -/
def X₁ (f : ℝ) : ℝ × ℝ := orbitPoint p₁ e₁ 0 f
/-- Second orbit. -/
def X₂ (f : ℝ) : ℝ × ℝ := orbitPoint p₂ e₂ ω f

/-- The squared distance `d²(f₁, f₂) = |X₁(f₁) - X₂(f₂)|²`. -/
def sqDist (q : ℝ × ℝ) : ℝ :=
  ((X₁ q.1).1 - (X₂ q.2).1) ^ 2 + ((X₁ q.1).2 - (X₂ q.2).2) ^ 2

/-! ## Derivatives -/

/-- Velocity `∂X/∂f`. -/
def vel (p e ϖ f : ℝ) : ℝ × ℝ :=
  (p / (1 + e * cos f) ^ 2 * (-sin (f + ϖ) - e * sin ϖ),
   p / (1 + e * cos f) ^ 2 * (cos (f + ϖ) + e * cos ϖ))

lemma one_add_mul_cos_pos {e : ℝ} (h0 : 0 ≤ e) (h1 : e < 1) (x : ℝ) : 0 < 1 + e * cos x := by
  nlinarith [neg_one_le_cos x, cos_le_one x]

lemma hasDerivAt_orbitPoint_fst (p e ϖ f : ℝ) (h : 1 + e * cos f ≠ 0) :
    HasDerivAt (fun f => (orbitPoint p e ϖ f).1) (vel p e ϖ f).1 f := by
  have h1 : HasDerivAt (fun f => 1 + e * cos f) (e * -sin f) f :=
    ((hasDerivAt_cos f).const_mul e).const_add 1
  have h2 : HasDerivAt (fun f => p / (1 + e * cos f))
      ((0 * (1 + e * cos f) - p * (e * -sin f)) / (1 + e * cos f) ^ 2) f :=
    (hasDerivAt_const f p).div h1 h
  have h3 : HasDerivAt (fun f => cos (f + ϖ)) (-sin (f + ϖ)) f := by
    simpa [Function.comp_def] using (hasDerivAt_cos (f + ϖ)).comp f ((hasDerivAt_id f).add_const ϖ)
  show HasDerivAt (fun f => p / (1 + e * cos f) * cos (f + ϖ)) _ f
  refine (h2.mul h3).congr_deriv ?_
  simp only [vel]
  rw [show e * sin ϖ = e * sin ϖ * (sin f ^ 2 + cos f ^ 2) by rw [sin_sq_add_cos_sq, mul_one]]
  rw [sin_add, cos_add]
  field_simp
  ring

lemma hasDerivAt_orbitPoint_snd (p e ϖ f : ℝ) (h : 1 + e * cos f ≠ 0) :
    HasDerivAt (fun f => (orbitPoint p e ϖ f).2) (vel p e ϖ f).2 f := by
  have h1 : HasDerivAt (fun f => 1 + e * cos f) (e * -sin f) f :=
    ((hasDerivAt_cos f).const_mul e).const_add 1
  have h2 : HasDerivAt (fun f => p / (1 + e * cos f))
      ((0 * (1 + e * cos f) - p * (e * -sin f)) / (1 + e * cos f) ^ 2) f :=
    (hasDerivAt_const f p).div h1 h
  have h3 : HasDerivAt (fun f => sin (f + ϖ)) (cos (f + ϖ)) f := by
    simpa [Function.comp_def] using (hasDerivAt_sin (f + ϖ)).comp f ((hasDerivAt_id f).add_const ϖ)
  show HasDerivAt (fun f => p / (1 + e * cos f) * sin (f + ϖ)) _ f
  refine (h2.mul h3).congr_deriv ?_
  simp only [vel]
  rw [show e * cos ϖ = e * cos ϖ * (sin f ^ 2 + cos f ^ 2) by rw [sin_sq_add_cos_sq, mul_one]]
  rw [sin_add, cos_add]
  field_simp
  ring

lemma e₁_pos : 0 ≤ e₁ := by norm_num [e₁]
lemma e₁_lt : e₁ < 1 := by norm_num [e₁]
lemma e₂_pos : 0 ≤ e₂ := by norm_num [e₂]
lemma e₂_lt : e₂ < 1 := by norm_num [e₂]

/-- The derivative of `d²` at `(f, g)`. -/
lemma hasFDerivAt_sqDist (f g : ℝ) :
    HasFDerivAt sqDist
      ((2 * (((X₁ f).1 - (X₂ g).1) * (vel p₁ e₁ 0 f).1 +
          ((X₁ f).2 - (X₂ g).2) * (vel p₁ e₁ 0 f).2)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
        (2 * (((X₁ f).1 - (X₂ g).1) * (vel p₂ e₂ ω g).1 +
          ((X₁ f).2 - (X₂ g).2) * (vel p₂ e₂ ω g).2)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (f, g) := by
  have hf := (one_add_mul_cos_pos e₁_pos e₁_lt f).ne'
  have hg := (one_add_mul_cos_pos e₂_pos e₂_lt g).ne'
  have ax := (hasDerivAt_orbitPoint_fst p₁ e₁ 0 f hf).comp_hasFDerivAt (𝕜 := ℝ) (f := Prod.fst) (f, g)
    (hasFDerivAt_fst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) _ (f, g))
  have ay := (hasDerivAt_orbitPoint_snd p₁ e₁ 0 f hf).comp_hasFDerivAt (𝕜 := ℝ) (f := Prod.fst) (f, g)
    (hasFDerivAt_fst : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) _ (f, g))
  have bx := (hasDerivAt_orbitPoint_fst p₂ e₂ ω g hg).comp_hasFDerivAt (𝕜 := ℝ) (f := Prod.snd) (f, g)
    (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ (f, g))
  have by' := (hasDerivAt_orbitPoint_snd p₂ e₂ ω g hg).comp_hasFDerivAt (𝕜 := ℝ) (f := Prod.snd) (f, g)
    (hasFDerivAt_snd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ (f, g))
  have H := ((ax.sub bx).pow 2).add ((ay.sub by').pow 2)
  refine H.congr_fderiv ?_
  ext <;> simp [X₁, X₂] <;> ring

lemma hasFDerivAt_sqDist_zero {f g : ℝ}
    (h1 : ((X₁ f).1 - (X₂ g).1) * (vel p₁ e₁ 0 f).1 + ((X₁ f).2 - (X₂ g).2) * (vel p₁ e₁ 0 f).2 = 0)
    (h2 : ((X₁ f).1 - (X₂ g).1) * (vel p₂ e₂ ω g).1 + ((X₁ f).2 - (X₂ g).2) * (vel p₂ e₂ ω g).2 = 0) :
    HasFDerivAt sqDist (0 : ℝ × ℝ →L[ℝ] ℝ) (f, g) := by
  have H := hasFDerivAt_sqDist f g
  rw [h1, h2] at H
  simpa using H

/-! ## Half-angle substitution -/

lemma cos_two_arctan (t : ℝ) : cos (2 * arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  rw [cos_two_mul, cos_sq_arctan]
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp
  ring

lemma sin_two_arctan (t : ℝ) : sin (2 * arctan t) = 2 * t / (1 + t ^ 2) := by
  rw [sin_two_mul, sin_arctan, cos_arctan]
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hs := Real.sq_sqrt h.le
  have hs' : √(1 + t ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  field_simp
  rw [hs]

/-- `cos ω`. -/
def cw : ℝ := (1 - τ ^ 2) / (1 + τ ^ 2)
/-- `sin ω`. -/
def sw : ℝ := 2 * τ / (1 + τ ^ 2)

lemma cos_ω : cos ω = cw := cos_two_arctan τ
lemma sin_ω : sin ω = sw := sin_two_arctan τ

/-! ## The algebraic core

If `(cos f₁, sin f₁, cos f₂, sin f₂) = (c1, s1, c2, s2)` satisfy the paper's equations (38)
(tangents parallel) and (37) (relative position orthogonal to the first tangent), then both
partial derivatives of `d²` vanish. -/

lemma key_alg (c1 s1 c2 s2 : ℝ) (h1 : c1 ^ 2 + s1 ^ 2 = 1) (hd1 : 0 < 1 + e₁ * c1)
    (hd2 : 0 < 1 + e₂ * c2)
    (L1 : (sw * c1 - cw * s1 + e₁ * sw) * (c2 + e₂) + (cw * c1 + sw * s1 + e₁ * cw) * s2 = 0)
    (L2 : p₂ * (1 + e₁ * c1) * ((sw * c1 - cw * s1 + e₁ * sw) * c2 +
      (cw * c1 + sw * s1 + e₁ * cw) * s2) = p₁ * e₁ * s1 * (1 + e₂ * c2)) :
    (p₁ / (1 + e₁ * c1) * c1 - p₂ / (1 + e₂ * c2) * (c2 * cw - s2 * sw)) * (-s1) +
      (p₁ / (1 + e₁ * c1) * s1 - p₂ / (1 + e₂ * c2) * (s2 * cw + c2 * sw)) * (c1 + e₁) = 0 ∧
    (p₁ / (1 + e₁ * c1) * c1 - p₂ / (1 + e₂ * c2) * (c2 * cw - s2 * sw)) *
        (-(s2 * cw + c2 * sw) - e₂ * sw) +
      (p₁ / (1 + e₁ * c1) * s1 - p₂ / (1 + e₂ * c2) * (s2 * cw + c2 * sw)) *
        ((c2 * cw - s2 * sw) + e₂ * cw) = 0 := by
  set V1 := p₁ / (1 + e₁ * c1) * c1 - p₂ / (1 + e₂ * c2) * (c2 * cw - s2 * sw) with hV1
  set V2 := p₁ / (1 + e₁ * c1) * s1 - p₂ / (1 + e₂ * c2) * (s2 * cw + c2 * sw) with hV2
  have hN1 : V1 * (-s1) + V2 * (c1 + e₁) = 0 := by
    have : V1 * (-s1) + V2 * (c1 + e₁) =
        (p₁ * e₁ * s1 * (1 + e₂ * c2) - p₂ * (1 + e₁ * c1) * ((sw * c1 - cw * s1 + e₁ * sw) * c2 +
          (cw * c1 + sw * s1 + e₁ * cw) * s2)) / ((1 + e₁ * c1) * (1 + e₂ * c2)) := by
      rw [hV1, hV2]
      field_simp
      ring
    rw [this, L2, sub_self, zero_div]
  refine ⟨hN1, ?_⟩
  set b1 := -(s2 * cw + c2 * sw) - e₂ * sw
  set b2 := (c2 * cw - s2 * sw) + e₂ * cw
  have hT : 0 < (-s1) ^ 2 + (c1 + e₁) ^ 2 := by
    have : -1 ≤ c1 := by nlinarith [sq_nonneg s1, sq_nonneg (c1 + 1)]
    have he : e₁ < 1 := by norm_num [e₁]
    nlinarith
  have hcross : (-s1) * b2 - (c1 + e₁) * b1 = 0 := by
    rw [← L1]
    ring
  have hid : (V1 * b1 + V2 * b2) * ((-s1) ^ 2 + (c1 + e₁) ^ 2) =
      (V1 * (-s1) + V2 * (c1 + e₁)) * ((-s1) * b1 + (c1 + e₁) * b2) -
        (V1 * (c1 + e₁) - V2 * (-s1)) * ((-s1) * b2 - (c1 + e₁) * b1) := by
    ring
  rw [hN1, hcross] at hid
  simp only [zero_mul, mul_zero, sub_zero] at hid
  rcases mul_eq_zero.1 hid with h | h
  · exact h
  · exact absurd h hT.ne'

/-! ## Polynomials in `t = tan (f₁ / 2)` -/

def den (t : ℝ) : ℝ := 1 + t ^ 2
/-- `α · (1 + t²)` with `α = sin (ω - f₁) + e₁ sin ω`. -/
def Aq (t : ℝ) : ℝ := sw * (1 - t ^ 2) - cw * (2 * t) + e₁ * sw * den t
/-- `β · (1 + t²)` with `β = cos (ω - f₁) + e₁ cos ω`. -/
def Bq (t : ℝ) : ℝ := cw * (1 - t ^ 2) + sw * (2 * t) + e₁ * cw * den t
/-- `μ · (1 + t²)` with `μ = p₁ e₁ e₂ sin f₁`. -/
def Mq (t : ℝ) : ℝ := p₁ * e₁ * e₂ * (2 * t)
/-- `δ · (1 + t²)²`. -/
def Dq (t : ℝ) : ℝ := p₁ * e₁ * (2 * t) * den t + p₂ * e₂ * (den t + e₁ * (1 - t ^ 2)) * Aq t
/-- The left side of the paper's (41), times `(1 + t²)⁶`. -/
def Fq (t : ℝ) : ℝ :=
  (Aq t ^ 2 + Bq t ^ 2) * Dq t ^ 2 - 2 * e₂ * Aq t ^ 2 * Dq t * Mq t * den t +
    Mq t ^ 2 * (e₂ ^ 2 * Aq t ^ 2 - Bq t ^ 2) * den t ^ 2
/-- Intersection condition `p₁ (1 + e₂ cos (f₁ - ω)) = p₂ (1 + e₁ cos f₁)`, times `1 + t²`. -/
def Iq (t : ℝ) : ℝ :=
  p₁ * (den t + e₂ * (cw * (1 - t ^ 2) + sw * (2 * t))) - p₂ * (den t + e₁ * (1 - t ^ 2))

/-- `cos f₂ = -δ/μ` (paper's (39)). -/
def cosF2 (t : ℝ) : ℝ := -Dq t / (Mq t * den t)
/-- `sin f₂ = -α (cos f₂ + e₂) / β` (paper's (38)). -/
def sinF2 (t : ℝ) : ℝ := -Aq t * (cosF2 t + e₂) / Bq t
/-- The angle `f₂` with these cosine and sine. -/
def F2 (t : ℝ) : ℝ := Complex.arg ⟨cosF2 t, sinF2 t⟩

lemma circle_identity (A B D M n e : ℝ) (hM : M ≠ 0) (hB : B ≠ 0) (hn : n ≠ 0) :
    (-D / (M * n)) ^ 2 + (-A * (-D / (M * n) + e) / B) ^ 2 - 1 =
      ((A ^ 2 + B ^ 2) * D ^ 2 - 2 * e * A ^ 2 * D * M * n + M ^ 2 * (e ^ 2 * A ^ 2 - B ^ 2) * n ^ 2) /
        (M ^ 2 * B ^ 2 * n ^ 2) := by
  field_simp
  ring

/-- Each root `t ≠ 0` of `Fq` with `Bq t ≠ 0` gives a critical point of `d²`. -/
lemma noninter_crit (t : ℝ) (hF : Fq t = 0) (ht : t ≠ 0) (hB : Bq t ≠ 0) :
    HasFDerivAt sqDist (0 : ℝ × ℝ →L[ℝ] ℝ) (2 * arctan t, F2 t) := by
  have hn : den t ≠ 0 := by unfold den; positivity
  have hM : Mq t ≠ 0 := by
    unfold Mq; norm_num [p₁, e₁, e₂]; exact ht
  have hcirc : cosF2 t ^ 2 + sinF2 t ^ 2 = 1 := by
    have h := circle_identity (Aq t) (Bq t) (Dq t) (Mq t) (den t) e₂ hM hB hn
    simp only [Fq] at hF
    rw [hF, zero_div] at h
    unfold sinF2 cosF2
    linarith
  set z : ℂ := ⟨cosF2 t, sinF2 t⟩ with hzdef
  have hnorm : ‖z‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp [z, hcirc]
  have hz : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  have hcg : cos (F2 t) = cosF2 t := by
    rw [F2, ← hzdef, Complex.cos_arg hz, hnorm]
    simp [z]
  have hsg : sin (F2 t) = sinF2 t := by
    rw [F2, ← hzdef, Complex.sin_arg, hnorm]
    simp [z]
  have hc2 : -1 ≤ cosF2 t := by nlinarith [sq_nonneg (sinF2 t), sq_nonneg (cosF2 t + 1)]
  have hd2 : 0 < 1 + e₂ * cosF2 t := by
    have : e₂ < 1 := e₂_lt
    have : 0 ≤ e₂ := e₂_pos
    nlinarith
  have hd1 : 0 < 1 + e₁ * ((1 - t ^ 2) / (1 + t ^ 2)) := by
    rw [← cos_two_arctan]
    exact one_add_mul_cos_pos e₁_pos e₁_lt _
  have h1 : ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
    have : (0 : ℝ) < 1 + t ^ 2 := by positivity
    field_simp
    ring
  have hn' : (1 + t ^ 2) ≠ 0 := by positivity
  have hα : sw * ((1 - t ^ 2) / (1 + t ^ 2)) - cw * (2 * t / (1 + t ^ 2)) + e₁ * sw =
      Aq t / (1 + t ^ 2) := by
    unfold Aq den
    field_simp
  have hβ : cw * ((1 - t ^ 2) / (1 + t ^ 2)) + sw * (2 * t / (1 + t ^ 2)) + e₁ * cw =
      Bq t / (1 + t ^ 2) := by
    unfold Bq den
    field_simp
  have L1 : (sw * ((1 - t ^ 2) / (1 + t ^ 2)) - cw * (2 * t / (1 + t ^ 2)) + e₁ * sw) *
        (cosF2 t + e₂) + (cw * ((1 - t ^ 2) / (1 + t ^ 2)) + sw * (2 * t / (1 + t ^ 2)) + e₁ * cw) *
        sinF2 t = 0 := by
    rw [hα, hβ]
    unfold sinF2
    field_simp
    ring
  have L2 : p₂ * (1 + e₁ * ((1 - t ^ 2) / (1 + t ^ 2))) *
        ((sw * ((1 - t ^ 2) / (1 + t ^ 2)) - cw * (2 * t / (1 + t ^ 2)) + e₁ * sw) * cosF2 t +
          (cw * ((1 - t ^ 2) / (1 + t ^ 2)) + sw * (2 * t / (1 + t ^ 2)) + e₁ * cw) * sinF2 t) =
        p₁ * e₁ * (2 * t / (1 + t ^ 2)) * (1 + e₂ * cosF2 t) := by
    have : (sw * ((1 - t ^ 2) / (1 + t ^ 2)) - cw * (2 * t / (1 + t ^ 2)) + e₁ * sw) * cosF2 t +
          (cw * ((1 - t ^ 2) / (1 + t ^ 2)) + sw * (2 * t / (1 + t ^ 2)) + e₁ * cw) * sinF2 t =
        -(sw * ((1 - t ^ 2) / (1 + t ^ 2)) - cw * (2 * t / (1 + t ^ 2)) + e₁ * sw) * e₂ := by
      linear_combination L1
    rw [this, hα]
    have hp1 : p₁ ≠ 0 := by norm_num [p₁]
    have he1 : e₁ ≠ 0 := by norm_num [e₁]
    have he2 : e₂ ≠ 0 := by norm_num [e₂]
    unfold cosF2 Dq Mq den
    field_simp
    ring
  obtain ⟨k1, k2⟩ := key_alg _ _ _ _ h1 hd1 hd2 L1 L2
  apply hasFDerivAt_sqDist_zero
  · simp only [X₁, X₂, orbitPoint, vel, add_zero, sin_zero, cos_zero, mul_zero, sub_zero,
      mul_one]
    rw [cos_add, sin_add (F2 t), hcg, hsg, cos_two_arctan, sin_two_arctan, cos_ω, sin_ω]
    linear_combination (p₁ / (1 + e₁ * ((1 - t ^ 2) / (1 + t ^ 2))) ^ 2) * k1
  · simp only [X₁, X₂, orbitPoint, vel, add_zero]
    rw [cos_add, sin_add (F2 t), hcg, hsg, cos_two_arctan, sin_two_arctan, cos_ω, sin_ω]
    linear_combination (p₂ / (1 + e₂ * cosF2 t) ^ 2) * k2

/-! ## Intersections -/

lemma inter_point (t : ℝ) (hI : Iq t = 0) : X₁ (2 * arctan t) = X₂ (2 * arctan t - ω) := by
  have hp1 := one_add_mul_cos_pos e₁_pos e₁_lt (2 * arctan t)
  have hp2 := one_add_mul_cos_pos e₂_pos e₂_lt (2 * arctan t - ω)
  have hr : p₂ / (1 + e₂ * cos (2 * arctan t - ω)) = p₁ / (1 + e₁ * cos (2 * arctan t)) := by
    rw [div_eq_div_iff hp2.ne' hp1.ne']
    rw [cos_sub, cos_two_arctan, sin_two_arctan, cos_ω, sin_ω]
    have hn : (1 + t ^ 2) ≠ 0 := by positivity
    simp only [Iq, den] at hI
    field_simp
    linear_combination (-1 : ℝ) * hI
  simp only [X₁, X₂, orbitPoint, add_zero, sub_add_cancel, hr]

lemma inter_crit (t : ℝ) (hI : Iq t = 0) :
    HasFDerivAt sqDist (0 : ℝ × ℝ →L[ℝ] ℝ) (2 * arctan t, 2 * arctan t - ω) := by
  apply hasFDerivAt_sqDist_zero <;> rw [inter_point t hI] <;> ring

lemma sqDist_inter (t : ℝ) (hI : Iq t = 0) : sqDist (2 * arctan t, 2 * arctan t - ω) = 0 := by
  simp only [sqDist]
  rw [inter_point t hI]
  ring

/-- If `Iq t ≠ 0`, the point of the first orbit with `f₁ = 2 arctan t` is not on the second. -/
lemma sqDist_ne_zero (t g : ℝ) (hI : Iq t ≠ 0) : sqDist (2 * arctan t, g) ≠ 0 := by
  intro h
  simp only [sqDist] at h
  have hx : (X₁ (2 * arctan t)).1 = (X₂ g).1 := by
    nlinarith [sq_nonneg ((X₁ (2 * arctan t)).1 - (X₂ g).1),
      sq_nonneg ((X₁ (2 * arctan t)).2 - (X₂ g).2)]
  have hy : (X₁ (2 * arctan t)).2 = (X₂ g).2 := by
    nlinarith [sq_nonneg ((X₁ (2 * arctan t)).1 - (X₂ g).1),
      sq_nonneg ((X₁ (2 * arctan t)).2 - (X₂ g).2)]
  simp only [X₁, X₂, orbitPoint, add_zero] at hx hy
  set f := 2 * arctan t with hf
  have hp1 := one_add_mul_cos_pos e₁_pos e₁_lt f
  have hp2 := one_add_mul_cos_pos e₂_pos e₂_lt g
  set r1 := p₁ / (1 + e₁ * cos f) with hr1def
  set r2 := p₂ / (1 + e₂ * cos g) with hr2def
  have hr1 : 0 < r1 := div_pos (by norm_num [p₁]) hp1
  have hr2 : 0 < r2 := div_pos (by norm_num [p₂]) hp2
  have hsq : r1 ^ 2 = r2 ^ 2 := by
    have e1 : r1 ^ 2 = (r1 * cos f) ^ 2 + (r1 * sin f) ^ 2 := by
      linear_combination (-r1 ^ 2) * sin_sq_add_cos_sq f
    have e2 : r2 ^ 2 = (r2 * cos (g + ω)) ^ 2 + (r2 * sin (g + ω)) ^ 2 := by
      linear_combination (-r2 ^ 2) * sin_sq_add_cos_sq (g + ω)
    rw [e1, e2, hx, hy]
  have hr : r1 = r2 := by
    have : (r1 - r2) * (r1 + r2) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  have hc : cos f = cos (g + ω) := by
    rw [hr] at hx
    exact mul_left_cancel₀ hr2.ne' hx
  have hs : sin f = sin (g + ω) := by
    rw [hr] at hy
    exact mul_left_cancel₀ hr2.ne' hy
  have hcg : cos g = cos f * cw + sin f * sw := by
    have : cos g = cos ((g + ω) - ω) := by ring_nf
    rw [this, cos_sub, ← hc, ← hs, cos_ω, sin_ω]
  rw [hr1def, hr2def, div_eq_div_iff hp1.ne' hp2.ne', hcg, hf, cos_two_arctan,
    sin_two_arctan] at hr
  apply hI
  have hn : (1 + t ^ 2) ≠ 0 := by positivity
  simp only [Iq, den]
  field_simp at hr
  linear_combination hr

/-! ## Locating the roots -/

lemma Fq_cont : Continuous Fq := by
  unfold Fq Dq Aq Bq Mq den
  fun_prop

lemma Iq_cont : Continuous Iq := by
  unfold Iq den
  fun_prop

/-- Intermediate value theorem in the form used below. -/
lemma exists_root_of_sign {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    (h : φ a * φ b < 0) : ∃ t ∈ Set.Icc a b, φ t = 0 := by
  rcases le_or_gt (φ a) 0 with ha | ha
  · have hb : 0 ≤ φ b := by
      by_contra hb
      have hb' := lt_of_not_ge hb
      nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb'.le]
    exact intermediate_value_Icc hab hφ.continuousOn ⟨ha, hb⟩
  · have hb : φ b ≤ 0 := by
      by_contra hb
      have hb' := lt_of_not_ge hb
      nlinarith [mul_pos ha hb']
    exact intermediate_value_Icc' hab hφ.continuousOn ⟨hb, ha.le⟩

lemma Bq_eq (t : ℝ) : Bq t = -111944553 / 8003960500 * t ^ 2 + 1424000 / 16007921 * t +
    15880134447 / 8003960500 := by
  simp only [Bq, den, cw, sw, τ, e₁]
  ring

lemma Iq_eq (t : ℝ) : Iq t = 4891501639 / 4001980250000 * t ^ 2 + 7095792 / 80039605 * t +
    6190173925361 / 4001980250000 := by
  simp only [Iq, den, cw, sw, τ, e₁, e₂, p₁, p₂]
  ring

/-! ## Main theorem -/

/-- **Twelve critical points.** For the two coplanar confocal ellipses above, `d²` has twelve
distinct critical points on the torus; exactly two of them (`P 0`, `P 2`) are intersections of
the orbits. Hence the maximum number of critical points in the planar case is `12`
(the upper bound `12` is Gronchi–Baù–Grassi 2023, §7), and their conjectured maximum `10`
is exceeded. -/
theorem twelve_critical_points :
    ∃ P : Fin 12 → ℝ × ℝ,
      (∀ i, HasFDerivAt sqDist (0 : ℝ × ℝ →L[ℝ] ℝ) (P i)) ∧
      (∀ i j : Fin 12, ∀ m n : ℤ,
        P i = ((P j).1 + 2 * π * m, (P j).2 + 2 * π * n) → i = j) ∧
      (∀ i, sqDist (P i) = 0 ↔ (i = 0 ∨ i = 2)) := by
  obtain ⟨t0, h0, z0⟩ := exists_root_of_sign Iq_cont (a := -217/5) (b := -433/10) (by norm_num)
    (by norm_num [Iq_eq])
  obtain ⟨t1, h1, z1⟩ := exists_root_of_sign Fq_cont (a := -191/5) (b := -381/10) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t2, h2, z2⟩ := exists_root_of_sign Iq_cont (a := -293/10) (b := -146/5) (by norm_num)
    (by norm_num [Iq_eq])
  obtain ⟨t3, h3, z3⟩ := exists_root_of_sign Fq_cont (a := -489/50) (b := -977/100) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t4, h4, z4⟩ := exists_root_of_sign Fq_cont (a := -377/50) (b := -753/100) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t5, h5, z5⟩ := exists_root_of_sign Fq_cont (a := -131/10000) (b := -13/1000) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t6, h6, z6⟩ := exists_root_of_sign Fq_cont (a := 89/2000) (b := 223/5000) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t7, h7, z7⟩ := exists_root_of_sign Fq_cont (a := 69/5) (b := 139/10) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t8, h8, z8⟩ := exists_root_of_sign Fq_cont (a := 237/10) (b := 119/5) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t9, h9, z9⟩ := exists_root_of_sign Fq_cont (a := 192/5) (b := 77/2) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t10, h10, z10⟩ := exists_root_of_sign Fq_cont (a := 198) (b := 199) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  obtain ⟨t11, h11, z11⟩ := exists_root_of_sign Fq_cont (a := 1990000) (b := 2000000) (by norm_num)
    (by norm_num [Fq, Aq, Bq, Dq, Mq, den, cw, sw, τ, p₁, e₁, p₂, e₂])
  let T : Fin 12 → ℝ := ![t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]
  let P : Fin 12 → ℝ × ℝ := ![(2 * arctan t0, 2 * arctan t0 - ω),
    (2 * arctan t1, F2 t1),
    (2 * arctan t2, 2 * arctan t2 - ω),
    (2 * arctan t3, F2 t3),
    (2 * arctan t4, F2 t4),
    (2 * arctan t5, F2 t5),
    (2 * arctan t6, F2 t6),
    (2 * arctan t7, F2 t7),
    (2 * arctan t8, F2 t8),
    (2 * arctan t9, F2 t9),
    (2 * arctan t10, F2 t10),
    (2 * arctan t11, F2 t11)]
  have hfst : ∀ i, (P i).1 = 2 * arctan (T i) := by
    intro i
    fin_cases i <;> rfl
  have hT : StrictMono T := by
    refine Fin.strictMono_iff_lt_succ.2 ?_
    intro i
    fin_cases i <;> simp [T] <;>
      linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2, h11.1, h11.2]
  have n1 : t1 ≠ 0 := by
    intro h; rw [h] at h1; norm_num at h1
  have b1 : Bq t1 ≠ 0 := by
    have : Bq t1 < 0 := by
      rw [Bq_eq]; nlinarith [h1.1, h1.2, mul_nonneg (sub_nonneg.2 h1.1) (sub_nonneg.2 h1.2)]
    exact this.ne
  have i1 : Iq t1 ≠ 0 := by
    have : Iq t1 < 0 := by
      rw [Iq_eq]; nlinarith [h1.1, h1.2, mul_nonneg (sub_nonneg.2 h1.1) (sub_nonneg.2 h1.2)]
    exact this.ne
  have n3 : t3 ≠ 0 := by
    intro h; rw [h] at h3; norm_num at h3
  have b3 : Bq t3 ≠ 0 := by
    have : Bq t3 < 0 := by
      rw [Bq_eq]; nlinarith [h3.1, h3.2, mul_nonneg (sub_nonneg.2 h3.1) (sub_nonneg.2 h3.2)]
    exact this.ne
  have i3 : Iq t3 ≠ 0 := by
    have : Iq t3 > 0 := by
      rw [Iq_eq]; nlinarith [h3.1, h3.2, mul_nonneg (sub_nonneg.2 h3.1) (sub_nonneg.2 h3.2)]
    exact this.ne'
  have n4 : t4 ≠ 0 := by
    intro h; rw [h] at h4; norm_num at h4
  have b4 : Bq t4 ≠ 0 := by
    have : Bq t4 > 0 := by
      rw [Bq_eq]; nlinarith [h4.1, h4.2, mul_nonneg (sub_nonneg.2 h4.1) (sub_nonneg.2 h4.2)]
    exact this.ne'
  have i4 : Iq t4 ≠ 0 := by
    have : Iq t4 > 0 := by
      rw [Iq_eq]; nlinarith [h4.1, h4.2, mul_nonneg (sub_nonneg.2 h4.1) (sub_nonneg.2 h4.2)]
    exact this.ne'
  have n5 : t5 ≠ 0 := by
    intro h; rw [h] at h5; norm_num at h5
  have b5 : Bq t5 ≠ 0 := by
    have : Bq t5 > 0 := by
      rw [Bq_eq]; nlinarith [h5.1, h5.2, mul_nonneg (sub_nonneg.2 h5.1) (sub_nonneg.2 h5.2)]
    exact this.ne'
  have i5 : Iq t5 ≠ 0 := by
    have : Iq t5 > 0 := by
      rw [Iq_eq]; nlinarith [h5.1, h5.2, mul_nonneg (sub_nonneg.2 h5.1) (sub_nonneg.2 h5.2)]
    exact this.ne'
  have n6 : t6 ≠ 0 := by
    intro h; rw [h] at h6; norm_num at h6
  have b6 : Bq t6 ≠ 0 := by
    have : Bq t6 > 0 := by
      rw [Bq_eq]; nlinarith [h6.1, h6.2, mul_nonneg (sub_nonneg.2 h6.1) (sub_nonneg.2 h6.2)]
    exact this.ne'
  have i6 : Iq t6 ≠ 0 := by
    have : Iq t6 > 0 := by
      rw [Iq_eq]; nlinarith [h6.1, h6.2, mul_nonneg (sub_nonneg.2 h6.1) (sub_nonneg.2 h6.2)]
    exact this.ne'
  have n7 : t7 ≠ 0 := by
    intro h; rw [h] at h7; norm_num at h7
  have b7 : Bq t7 ≠ 0 := by
    have : Bq t7 > 0 := by
      rw [Bq_eq]; nlinarith [h7.1, h7.2, mul_nonneg (sub_nonneg.2 h7.1) (sub_nonneg.2 h7.2)]
    exact this.ne'
  have i7 : Iq t7 ≠ 0 := by
    have : Iq t7 > 0 := by
      rw [Iq_eq]; nlinarith [h7.1, h7.2, mul_nonneg (sub_nonneg.2 h7.1) (sub_nonneg.2 h7.2)]
    exact this.ne'
  have n8 : t8 ≠ 0 := by
    intro h; rw [h] at h8; norm_num at h8
  have b8 : Bq t8 ≠ 0 := by
    have : Bq t8 < 0 := by
      rw [Bq_eq]; nlinarith [h8.1, h8.2, mul_nonneg (sub_nonneg.2 h8.1) (sub_nonneg.2 h8.2)]
    exact this.ne
  have i8 : Iq t8 ≠ 0 := by
    have : Iq t8 > 0 := by
      rw [Iq_eq]; nlinarith [h8.1, h8.2, mul_nonneg (sub_nonneg.2 h8.1) (sub_nonneg.2 h8.2)]
    exact this.ne'
  have n9 : t9 ≠ 0 := by
    intro h; rw [h] at h9; norm_num at h9
  have b9 : Bq t9 ≠ 0 := by
    have : Bq t9 < 0 := by
      rw [Bq_eq]; nlinarith [h9.1, h9.2, mul_nonneg (sub_nonneg.2 h9.1) (sub_nonneg.2 h9.2)]
    exact this.ne
  have i9 : Iq t9 ≠ 0 := by
    have : Iq t9 > 0 := by
      rw [Iq_eq]; nlinarith [h9.1, h9.2, mul_nonneg (sub_nonneg.2 h9.1) (sub_nonneg.2 h9.2)]
    exact this.ne'
  have n10 : t10 ≠ 0 := by
    intro h; rw [h] at h10; norm_num at h10
  have b10 : Bq t10 ≠ 0 := by
    have : Bq t10 < 0 := by
      rw [Bq_eq]; nlinarith [h10.1, h10.2, mul_nonneg (sub_nonneg.2 h10.1) (sub_nonneg.2 h10.2)]
    exact this.ne
  have i10 : Iq t10 ≠ 0 := by
    have : Iq t10 > 0 := by
      rw [Iq_eq]; nlinarith [h10.1, h10.2, mul_nonneg (sub_nonneg.2 h10.1) (sub_nonneg.2 h10.2)]
    exact this.ne'
  have n11 : t11 ≠ 0 := by
    intro h; rw [h] at h11; norm_num at h11
  have b11 : Bq t11 ≠ 0 := by
    have : Bq t11 < 0 := by
      rw [Bq_eq]; nlinarith [h11.1, h11.2, mul_nonneg (sub_nonneg.2 h11.1) (sub_nonneg.2 h11.2)]
    exact this.ne
  have i11 : Iq t11 ≠ 0 := by
    have : Iq t11 > 0 := by
      rw [Iq_eq]; nlinarith [h11.1, h11.2, mul_nonneg (sub_nonneg.2 h11.1) (sub_nonneg.2 h11.2)]
    exact this.ne'
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact inter_crit t0 z0
    · exact noninter_crit t1 z1 n1 b1
    · exact inter_crit t2 z2
    · exact noninter_crit t3 z3 n3 b3
    · exact noninter_crit t4 z4 n4 b4
    · exact noninter_crit t5 z5 n5 b5
    · exact noninter_crit t6 z6 n6 b6
    · exact noninter_crit t7 z7 n7 b7
    · exact noninter_crit t8 z8 n8 b8
    · exact noninter_crit t9 z9 n9 b9
    · exact noninter_crit t10 z10 n10 b10
    · exact noninter_crit t11 z11 n11 b11
  · intro i j m n hij
    have h1 := congrArg Prod.fst hij
    simp only [hfst] at h1
    have a1 := neg_pi_div_two_lt_arctan (T i)
    have a2 := arctan_lt_pi_div_two (T i)
    have a3 := neg_pi_div_two_lt_arctan (T j)
    have a4 := arctan_lt_pi_div_two (T j)
    have hm1 : (m : ℝ) < 1 := by nlinarith [pi_pos]
    have hm2 : (-1 : ℝ) < m := by nlinarith [pi_pos]
    have hm : m = 0 := by
      have : m < 1 := by exact_mod_cast hm1
      have : -1 < m := by exact_mod_cast hm2
      omega
    subst hm
    simp only [Int.cast_zero, mul_zero, add_zero] at h1
    exact hT.injective (arctan_injective (by linarith))
  · intro i
    fin_cases i
    · simp [P, sqDist_inter t0 z0]
    · simp [P, sqDist_ne_zero t1 _ i1]
    · simp [P, sqDist_inter t2 z2]
    · simp [P, sqDist_ne_zero t3 _ i3]
    · simp [P, sqDist_ne_zero t4 _ i4]
    · simp [P, sqDist_ne_zero t5 _ i5]
    · simp [P, sqDist_ne_zero t6 _ i6]
    · simp [P, sqDist_ne_zero t7 _ i7]
    · simp [P, sqDist_ne_zero t8 _ i8]
    · simp [P, sqDist_ne_zero t9 _ i9]
    · simp [P, sqDist_ne_zero t10 _ i10]
    · simp [P, sqDist_ne_zero t11 _ i11]

end

end OpenQuestions.KeplerianDistance

#print axioms OpenQuestions.KeplerianDistance.twelve_critical_points
