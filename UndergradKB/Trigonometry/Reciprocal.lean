import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import UndergradKB.Common.Attr

/-! # Reciprocal trigonometric functions (Corral §1.2, §3.1; OpenStax §7.2, §8.2, §9.1)

Mathlib has `Real.cot` but no secant or cosecant, so we define `sec` and `csc` as `(cos x)⁻¹` and
`(sin x)⁻¹`. With Lean's convention `y / 0 = 0`, several of the book's "wherever defined" statements hold
without hypotheses; where they do not we add the natural nonvanishing hypothesis.
-/

namespace UndergradKB.Trigonometry

open Real

/-- Secant, the reciprocal of cosine (Mathlib has no secant). -/
noncomputable def sec (x : ℝ) : ℝ := (cos x)⁻¹

/-- Cosecant, the reciprocal of sine (Mathlib has no cosecant). -/
noncomputable def csc (x : ℝ) : ℝ := (sin x)⁻¹

/-- `sec x = 1 / cos x` (TR-044). -/
@[kb "corraltrig" "Box §1.2, p. 15"]
theorem sec_eq_one_div_cos (x : ℝ) : sec x = 1 / cos x := by simp [sec]

/-- `csc x = 1 / sin x` (TR-044). -/
theorem csc_eq_one_div_sin (x : ℝ) : csc x = 1 / sin x := by simp [csc]

/-- `cot x = 1 / tan x` (TR-044). -/
theorem cot_eq_one_div_tan (x : ℝ) : cot x = 1 / tan x := by
  rw [one_div, tan_inv_eq_cot]

/-- `cos x = 1 / sec x` (TR-044). -/
theorem cos_eq_one_div_sec (x : ℝ) : cos x = 1 / sec x := by simp [sec]

/-- `sin x = 1 / csc x` (TR-044). -/
theorem sin_eq_one_div_csc (x : ℝ) : sin x = 1 / csc x := by simp [csc]

/-- `tan x = 1 / cot x` (TR-044). -/
theorem tan_eq_one_div_cot (x : ℝ) : tan x = 1 / cot x := by
  rw [one_div, cot_inv_eq_tan]

/-- Secant is the reciprocal of cosine, `cos x * sec x = 1` when `cos x ≠ 0` (TR-047). -/
@[kb "corraltrig" "Box §3.1, p. 73"]
theorem cos_mul_sec (x : ℝ) (h : cos x ≠ 0) : cos x * sec x = 1 := by
  simp [sec, h]

/-- Cosecant is the reciprocal of sine, `sin x * csc x = 1` when `sin x ≠ 0` (TR-047). -/
theorem sin_mul_csc (x : ℝ) (h : sin x ≠ 0) : sin x * csc x = 1 := by
  simp [csc, h]

/-- Cotangent is the reciprocal of tangent, `tan x * cot x = 1` when `sin x ≠ 0` and `cos x ≠ 0`
(TR-047). -/
theorem tan_mul_cot (x : ℝ) (hs : sin x ≠ 0) (hc : cos x ≠ 0) : tan x * cot x = 1 := by
  rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin]; field_simp

/-- Secant is even (TR-042, TR-043). -/
@[kb "openstaxalgtrig2e" "Box §7.4, p. 734"]
theorem sec_neg (x : ℝ) : sec (-x) = sec x := by simp [sec]

/-- Cosecant is odd (TR-042, TR-043). -/
theorem csc_neg (x : ℝ) : csc (-x) = - csc x := by simp [csc]

/-- Cotangent is odd (TR-042, TR-043). -/
theorem cot_neg (x : ℝ) : cot (-x) = - cot x := by
  simp [cot_eq_cos_div_sin, div_neg]

/-- `1 + tan² x = sec² x` when `cos x ≠ 0` (TR-053). -/
@[kb "corraltrig" "Eq 3.10, p. 75"]
theorem one_add_tan_sq_eq_sec_sq (x : ℝ) (h : cos x ≠ 0) : 1 + tan x ^ 2 = sec x ^ 2 := by
  rw [tan_eq_sin_div_cos, sec]
  field_simp
  linear_combination sin_sq_add_cos_sq x

/-- `cot² x + 1 = csc² x` when `sin x ≠ 0` (TR-054). -/
@[kb "corraltrig" "Eq 3.11, p. 75"]
theorem cot_sq_add_one_eq_csc_sq (x : ℝ) (h : sin x ≠ 0) : cot x ^ 2 + 1 = csc x ^ 2 := by
  rw [cot_eq_cos_div_sin, csc]
  field_simp
  linear_combination cos_sq_add_sin_sq x

/-- `tan (x + π/2) = - cot x` for every real `x` (TR-030). -/
@[kb "corraltrig" "Box §1.5, p. 40"]
theorem tan_add_pi_div_two (x : ℝ) : tan (x + π / 2) = - cot x := by
  rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
    div_neg]

/-- `tan (x - π/2) = - cot x` for every real `x` (TR-031). -/
@[kb "corraltrig" "Box §1.5, p. 42"]
theorem tan_sub_pi_div_two (x : ℝ) : tan (x - π / 2) = - cot x := by
  rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two,
    neg_div]

/-- `cot x = - tan (x + π/2)` (TR-117). -/
@[kb "corraltrig" "Box §5.1, p. 114"]
theorem cot_eq_neg_tan_add_pi_div_two (x : ℝ) : cot x = - tan (x + π / 2) := by
  rw [tan_add_pi_div_two, neg_neg]

/-- Cofunction identity `sec (π/2 - x) = csc x` for all real `x` (TR-045, TR-046). -/
@[kb "corraltrig" "Thm 1.2, p. 19"]
theorem sec_pi_div_two_sub (x : ℝ) : sec (π / 2 - x) = csc x := by
  rw [sec, csc, Real.cos_pi_div_two_sub]

/-- Cofunction identity `csc (π/2 - x) = sec x` (TR-045, TR-046). -/
theorem csc_pi_div_two_sub (x : ℝ) : csc (π / 2 - x) = sec x := by
  rw [sec, csc, Real.sin_pi_div_two_sub]

/-- Cofunction identity `cot (π/2 - x) = tan x` (TR-045, TR-046). -/
theorem cot_pi_div_two_sub (x : ℝ) : cot (π / 2 - x) = tan x := by
  rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

/-- Cofunction identity `tan (π/2 - x) = cot x` (TR-045, TR-046). -/
theorem tan_pi_div_two_sub_eq_cot (x : ℝ) : tan (π / 2 - x) = cot x := by
  rw [tan_pi_div_two_sub, tan_inv_eq_cot]

/-- Secant has period `2π` (TR-122). -/
@[kb "corraltrig" "Example 5.3, p. 117"]
theorem sec_periodic : Function.Periodic sec (2 * π) := fun x => by simp [sec]

/-- Cosecant has period `2π` (TR-122). -/
theorem csc_periodic : Function.Periodic csc (2 * π) := fun x => by simp [csc]

/-- Cotangent has period `π` (TR-122). -/
theorem cot_periodic : Function.Periodic cot π := fun x => by
  simp [cot_eq_cos_div_sin]

/-- `sec (x + π) = - sec x`. -/
theorem sec_add_pi (x : ℝ) : sec (x + π) = - sec x := by simp [sec]

/-- `csc (x + π) = - csc x`. -/
theorem csc_add_pi (x : ℝ) : csc (x + π) = - csc x := by simp [csc]

/-- `|sec x| ≥ 1` when `cos x ≠ 0` (TR-131). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 775"]
theorem one_le_abs_sec (x : ℝ) (h : cos x ≠ 0) : 1 ≤ |sec x| := by
  rw [sec, abs_inv]
  exact (one_le_inv₀ (abs_pos.2 h)).2 (abs_cos_le_one x)

/-- `|csc x| ≥ 1` when `sin x ≠ 0` (TR-131). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 776"]
theorem one_le_abs_csc (x : ℝ) (h : sin x ≠ 0) : 1 ≤ |csc x| := by
  rw [csc, abs_inv]
  exact (one_le_inv₀ (abs_pos.2 h)).2 (abs_sin_le_one x)

/-- `sec x = 0 ↔ cos x = 0` (domain of secant, TR-131). -/
theorem sec_eq_zero_iff (x : ℝ) : sec x = 0 ↔ cos x = 0 := by simp [sec]

/-- `csc x = 0 ↔ sin x = 0` (domain of cosecant, TR-131). -/
theorem csc_eq_zero_iff (x : ℝ) : csc x = 0 ↔ sin x = 0 := by simp [csc]

/-- Cotangent is strictly decreasing on `(0, π)` (TR-132). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 783"]
theorem cot_strictAntiOn : StrictAntiOn cot (Set.Ioo 0 π) := by
  intro x hx y hy hxy
  rw [← tan_pi_div_two_sub_eq_cot, ← tan_pi_div_two_sub_eq_cot]
  apply strictMonoOn_tan
  · constructor <;> linarith [hy.1, hy.2]
  · constructor <;> linarith [hx.1, hx.2]
  · linarith

/-- `cot (x + π) = cot x` (TR-132). -/
@[kb "openstaxalgtrig2e" "Box §8.2, p. 782"]
theorem cot_add_pi (x : ℝ) : cot (x + π) = cot x := cot_periodic x

section RightTriangle

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- In a right triangle with the right angle at `p₂`, the cosecant of the acute angle at `p₃` is the
hypotenuse over the opposite side (TR-016). -/
@[kb "corraltrig" "Table 1.2, p. 15"]
theorem csc_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : csc (∠ p₂ p₃ p₁) = dist p₁ p₃ / dist p₁ p₂ := by
  rw [csc, sin_angle_of_angle_eq_pi_div_two h h0, inv_div]

/-- Secant of the acute angle at `p₃` is hypotenuse over adjacent side (TR-016). -/
theorem sec_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    sec (∠ p₂ p₃ p₁) = dist p₁ p₃ / dist p₃ p₂ := by
  rw [sec, cos_angle_of_angle_eq_pi_div_two h, inv_div]

/-- Cotangent of the acute angle at `p₃` is adjacent over opposite side (TR-016). -/
theorem cot_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    cot (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₂ := by
  rw [← tan_inv_eq_cot, tan_angle_of_angle_eq_pi_div_two h, inv_div]

end RightTriangle

/-- `sec (π/3) = 2` (TR-018). -/
@[kb "corraltrig" "Ex 1.7, p. 18"]
theorem sec_pi_div_three : sec (π / 3) = 2 := by simp [sec]

/-- `csc (π/6) = 2` (TR-018). -/
theorem csc_pi_div_six : csc (π / 6) = 2 := by simp [csc]

/-- `sec (π/4) = √2` (TR-018). -/
theorem sec_pi_div_four : sec (π / 4) = √2 := by
  have : (0:ℝ) < √2 := by positivity
  rw [sec, cos_pi_div_four]; field_simp; simp

/-- `csc (π/4) = √2` (TR-018). -/
theorem csc_pi_div_four : csc (π / 4) = √2 := by
  have : (0:ℝ) < √2 := by positivity
  rw [csc, sin_pi_div_four]; field_simp; simp

/-- `cot (π/4) = 1` (TR-018). -/
theorem cot_pi_div_four : cot (π / 4) = 1 := by
  rw [cot_eq_cos_div_sin, cos_pi_div_four, sin_pi_div_four]
  have : (0:ℝ) < √2 := by positivity
  field_simp

/-- `sec (π/6) = 2 √3 / 3` (TR-018). -/
theorem sec_pi_div_six : sec (π / 6) = 2 * √3 / 3 := by
  have : (0:ℝ) < √3 := by positivity
  rw [sec, cos_pi_div_six]; field_simp; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- `csc (π/3) = 2 √3 / 3` (TR-018). -/
theorem csc_pi_div_three : csc (π / 3) = 2 * √3 / 3 := by
  have : (0:ℝ) < √3 := by positivity
  rw [csc, sin_pi_div_three]; field_simp; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- `cot (π/6) = √3` (TR-018). -/
theorem cot_pi_div_six : cot (π / 6) = √3 := by
  rw [cot_eq_cos_div_sin, cos_pi_div_six, sin_pi_div_six]; field_simp

/-- `cot (π/3) = √3 / 3` (TR-018). -/
theorem cot_pi_div_three : cot (π / 3) = √3 / 3 := by
  rw [cot_eq_cos_div_sin, cos_pi_div_three, sin_pi_div_three]
  have : (0:ℝ) < √3 := by positivity
  field_simp; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

/-- `cot (π/2) = 0` (TR-026). -/
@[kb "corraltrig" "Ex 1.23, p. 36"]
theorem cot_pi_div_two : cot (π / 2) = 0 := by simp [cot_eq_cos_div_sin]

/-- `csc (π/2) = 1` (TR-026). -/
theorem csc_pi_div_two : csc (π / 2) = 1 := by simp [csc]

/-- All six functions at `π/6`, `π/4`, `π/3` (TR-018, TR-027). -/
@[kb "corraltrig" "Table 1.3, p. 37"]
theorem six_functions_special_values :
    (tan (π / 6) = √3 / 3 ∧ cot (π / 6) = √3 ∧ sec (π / 6) = 2 * √3 / 3 ∧ csc (π / 6) = 2) ∧
    (tan (π / 4) = 1 ∧ cot (π / 4) = 1 ∧ sec (π / 4) = √2 ∧ csc (π / 4) = √2) ∧
    (tan (π / 3) = √3 ∧ cot (π / 3) = √3 / 3 ∧ sec (π / 3) = 2 ∧ csc (π / 3) = 2 * √3 / 3) := by
  refine ⟨⟨?_, cot_pi_div_six, sec_pi_div_six, csc_pi_div_six⟩,
    ⟨tan_pi_div_four, cot_pi_div_four, sec_pi_div_four, csc_pi_div_four⟩,
    ⟨tan_pi_div_three, cot_pi_div_three, sec_pi_div_three, csc_pi_div_three⟩⟩
  rw [tan_pi_div_six]
  have : (0:ℝ) < √3 := by positivity
  field_simp; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

end UndergradKB.Trigonometry
