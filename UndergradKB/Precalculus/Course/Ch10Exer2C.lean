import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 10.3
(trigonometric equations, right triangles, identities)

Reciprocal functions are written `(cos θ)⁻¹`, `(sin θ)⁻¹`, `cos θ / sin θ`. -/

namespace UndergradKB.Precalculus.Course

open Real

/-- tangent equations with nonzero right side: `tan θ = tan a` exactly when `θ = a + πk`. -/
private lemma tan_iff {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    tan θ = tan a ↔ ∃ k : ℤ, θ = a + π * k := by
  constructor
  · intro h
    have ha : tan a ≠ 0 := by rw [tan_eq_sin_div_cos]; exact div_ne_zero hs hc
    have hθ : cos θ ≠ 0 := fun h0 => ha (h ▸ tan_eq_zero_of_cos_eq_zero h0)
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hθ hc] at h
    have : sin (θ - a) = 0 := by rw [sin_sub]; linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp this
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [mul_comm]; exact tan_add_int_mul_pi a k

/-- cotangent equations: `cos θ / sin θ = cos a / sin a` exactly when `θ = a + πk`. -/
private lemma cot_iff {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    cos θ / sin θ = cos a / sin a ↔ ∃ k : ℤ, θ = a + π * k := by
  have e : ∀ x : ℝ, cos x / sin x = (tan x)⁻¹ := fun x => by rw [tan_eq_sin_div_cos, inv_div]
  rw [e, e, inv_inj]
  exact tan_iff hc hs

/-! ## Trigonometric equations -/

/-- Stitz-Zeager Exercise 10.3.46: `cot θ = √3/3` exactly when `θ = π/3 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.46, p. 772"]
theorem exer_10_3_46 (θ : ℝ) : cos θ / sin θ = √3 / 3 ↔ ∃ k : ℤ, θ = π / 3 + π * k := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  have hc : cos (π / 3) ≠ 0 := by rw [cos_pi_div_three]; norm_num
  have hs : sin (π / 3) ≠ 0 := by rw [sin_pi_div_three]; positivity
  have e : √3 / 3 = cos (π / 3) / sin (π / 3) := by
    rw [cos_pi_div_three, sin_pi_div_three]; field_simp; nlinarith [h3]
  rw [e]; exact cot_iff hc hs

/-- Stitz-Zeager Exercise 10.3.53: `csc θ = -1/2` never happens. -/
@[kb "stitzzeager2013" "Exercise 10.3.53, p. 772"]
theorem exer_10_3_53 : ¬ ∃ θ : ℝ, sin θ ≠ 0 ∧ (sin θ)⁻¹ = -1 / 2 := by
  rintro ⟨θ, hs, h⟩
  have h2 : sin θ = -2 := by
    have := congrArg (fun x => x⁻¹) h
    simp only [inv_inv] at this
    rw [this]; norm_num
  have := neg_one_le_sin θ
  linarith

/-- Stitz-Zeager Exercise 10.3.55: `tan θ = -√3` exactly when `θ = 2π/3 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.55, p. 772"]
theorem exer_10_3_55 (θ : ℝ) : tan θ = -√3 ↔ ∃ k : ℤ, θ = 2 * π / 3 + π * k := by
  have h : 2 * π / 3 = π - π / 3 := by ring
  have hp : 0 < √3 := by positivity
  have hc : cos (2 * π / 3) ≠ 0 := by rw [h, cos_pi_sub, cos_pi_div_three]; norm_num
  have hs : sin (2 * π / 3) ≠ 0 := by rw [h, sin_pi_sub, sin_pi_div_three]; positivity
  have ht : tan (2 * π / 3) = -√3 := by
    rw [h, tan_eq_sin_div_cos, sin_pi_sub, cos_pi_sub, sin_pi_div_three, cos_pi_div_three]
    field_simp
  rw [← ht]; exact tan_iff hc hs

/-- Stitz-Zeager Exercise 10.3.58: `cot t = 1` exactly when `t = π/4 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.58, p. 772"]
theorem exer_10_3_58 (t : ℝ) : cos t / sin t = 1 ↔ ∃ k : ℤ, t = π / 4 + π * k := by
  have hp : 0 < √2 := by positivity
  have hc : cos (π / 4) ≠ 0 := by rw [cos_pi_div_four]; positivity
  have hs : sin (π / 4) ≠ 0 := by rw [sin_pi_div_four]; positivity
  have e : (1 : ℝ) = cos (π / 4) / sin (π / 4) := by
    rw [cos_pi_div_four, sin_pi_div_four]; field_simp
  rw [e]; exact cot_iff hc hs

/-- Stitz-Zeager Exercise 10.3.59: `tan t = √3/3` exactly when `t = π/6 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.59, p. 772"]
theorem exer_10_3_59 (t : ℝ) : tan t = √3 / 3 ↔ ∃ k : ℤ, t = π / 6 + π * k := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  have hc : cos (π / 6) ≠ 0 := by rw [cos_pi_div_six]; positivity
  have hs : sin (π / 6) ≠ 0 := by rw [sin_pi_div_six]; norm_num
  have e : √3 / 3 = tan (π / 6) := by
    rw [tan_eq_sin_div_cos, cos_pi_div_six, sin_pi_div_six]; field_simp; nlinarith [h3]
  rw [e]; exact tan_iff hc hs

/-- Stitz-Zeager Exercise 10.3.60: `sec t = -2√3/3` exactly when `t = 5π/6 + 2πk` or `t = 7π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.60, p. 772"]
theorem exer_10_3_60 (t : ℝ) :
    (cos t)⁻¹ = -(2 * √3 / 3) ↔ ∃ k : ℤ, t = 5 * π / 6 + 2 * π * k ∨ t = 7 * π / 6 + 2 * π * k := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  have h56 : cos (5 * π / 6) = -(√3 / 2) := by
    rw [show 5 * π / 6 = π - π / 6 by ring, cos_pi_sub, cos_pi_div_six]
  have e : (cos t)⁻¹ = -(2 * √3 / 3) ↔ cos (5 * π / 6) = cos t := by
    rw [inv_eq_iff_eq_inv, h56]
    have : (-(2 * √3 / 3))⁻¹ = -(√3 / 2) := by field_simp; nlinarith [h3]
    rw [this]; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.3.61: `csc t = 0` never happens (for `t` where `csc t` is defined). -/
@[kb "stitzzeager2013" "Exercise 10.3.61, p. 772"]
theorem exer_10_3_61 : ¬ ∃ t : ℝ, sin t ≠ 0 ∧ (sin t)⁻¹ = 0 := by
  rintro ⟨t, hs, h⟩
  exact hs (inv_eq_zero.mp h)

/-- Stitz-Zeager Exercise 10.3.62: `cot t = -√3` exactly when `t = 5π/6 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.62, p. 772"]
theorem exer_10_3_62 (t : ℝ) : cos t / sin t = -√3 ↔ ∃ k : ℤ, t = 5 * π / 6 + π * k := by
  have h : 5 * π / 6 = π - π / 6 := by ring
  have hp : 0 < √3 := by positivity
  have hc : cos (5 * π / 6) ≠ 0 := by rw [h, cos_pi_sub, cos_pi_div_six]; simp
  have hs : sin (5 * π / 6) ≠ 0 := by rw [h, sin_pi_sub, sin_pi_div_six]; norm_num
  have e : -√3 = cos (5 * π / 6) / sin (5 * π / 6) := by
    rw [h, sin_pi_sub, cos_pi_sub, sin_pi_div_six, cos_pi_div_six]; field_simp
  rw [e]; exact cot_iff hc hs

/-- Stitz-Zeager Exercise 10.3.63: `tan t = -√3/3` exactly when `t = 5π/6 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.63, p. 772"]
theorem exer_10_3_63 (t : ℝ) : tan t = -(√3 / 3) ↔ ∃ k : ℤ, t = 5 * π / 6 + π * k := by
  have h : 5 * π / 6 = π - π / 6 := by ring
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  have hc : cos (5 * π / 6) ≠ 0 := by rw [h, cos_pi_sub, cos_pi_div_six]; simp
  have hs : sin (5 * π / 6) ≠ 0 := by rw [h, sin_pi_sub, sin_pi_div_six]; norm_num
  have e : -(√3 / 3) = tan (5 * π / 6) := by
    rw [h, tan_eq_sin_div_cos, sin_pi_sub, cos_pi_sub, sin_pi_div_six, cos_pi_div_six]
    field_simp; nlinarith [h3]
  rw [e]; exact tan_iff hc hs

/-- Stitz-Zeager Exercise 10.3.64: `sec t = 2√3/3` exactly when `t = π/6 + 2πk` or `t = 11π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.64, p. 772"]
theorem exer_10_3_64 (t : ℝ) :
    (cos t)⁻¹ = 2 * √3 / 3 ↔ ∃ k : ℤ, t = π / 6 + 2 * π * k ∨ t = 11 * π / 6 + 2 * π * k := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  have e : (cos t)⁻¹ = 2 * √3 / 3 ↔ cos (π / 6) = cos t := by
    rw [inv_eq_iff_eq_inv, cos_pi_div_six]
    have : (2 * √3 / 3)⁻¹ = √3 / 2 := by field_simp; nlinarith [h3]
    rw [this]; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.3.65: `csc t = 2√3/3` exactly when `t = π/3 + 2πk` or `t = 2π/3 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.65, p. 772"]
theorem exer_10_3_65 (t : ℝ) :
    (sin t)⁻¹ = 2 * √3 / 3 ↔ ∃ k : ℤ, t = π / 3 + 2 * π * k ∨ t = 2 * π / 3 + 2 * π * k := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  have e : (sin t)⁻¹ = 2 * √3 / 3 ↔ sin (π / 3) = sin t := by
    rw [inv_eq_iff_eq_inv, sin_pi_div_three]
    have : (2 * √3 / 3)⁻¹ = √3 / 2 := by field_simp; nlinarith [h3]
    rw [this]; exact eq_comm
  rw [e, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩

end UndergradKB.Precalculus.Course
