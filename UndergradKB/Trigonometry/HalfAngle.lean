import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-! # Tangent half-angle formulas (Corral §3.3, OpenStax §9.3)

Mathlib has the sine and cosine half-angle formulas (`Real.cos_sq_half`, `Real.sin_sq_half`) but not those for
the tangent and cotangent. In Mathlib `tan x = sin x / cos x` and `cot x = cos x / sin x` with `y / 0 = 0`;
with that convention the formulas below hold for every real `θ` (where the book's formula is undefined both
sides are `0`), so they are stated without hypotheses.
-/

namespace UndergradKB.Trigonometry

open Real

/-- `tan (θ/2) = sin θ / (1 + cos θ)`. -/
@[kb "corraltrig" "Eq 3.35, p. 88"]
theorem tan_half_eq_sin_div_one_add_cos (θ : ℝ) : tan (θ / 2) = sin θ / (1 + cos θ) := by
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  rw [mul_div_cancel_left₀ x two_ne_zero, tan_eq_sin_div_cos, sin_two_mul, cos_two_mul]
  rcases eq_or_ne (cos x) 0 with h | h
  · simp [h]
  · field_simp; ring

/-- `tan (θ/2) = (1 - cos θ) / sin θ`. -/
@[kb "corraltrig" "Eq 3.34, p. 88"]
theorem tan_half_eq_one_sub_cos_div_sin (θ : ℝ) : tan (θ / 2) = (1 - cos θ) / sin θ := by
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  rw [mul_div_cancel_left₀ x two_ne_zero, tan_eq_sin_div_cos, sin_two_mul, cos_two_mul]
  rcases eq_or_ne (cos x) 0 with h | h
  · simp [h]
  rcases eq_or_ne (sin x) 0 with h' | h'
  · simp [h']
  have hc : 1 - (2 * cos x ^ 2 - 1) = 2 * sin x ^ 2 := by
    linear_combination (-2) * sin_sq_add_cos_sq x
  rw [hc]; field_simp

/-- `tan² (θ/2) = (1 - cos θ) / (1 + cos θ)` (Corral Eq 3.30; OpenStax §9.3 in the form
`tan² t = (1 - cos 2t) / (1 + cos 2t)`). -/
@[kb "corraltrig" "Eq 3.30, p. 87"]
theorem tan_sq_half (θ : ℝ) : tan (θ / 2) ^ 2 = (1 - cos θ) / (1 + cos θ) := by
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  rw [mul_div_cancel_left₀ x two_ne_zero, tan_eq_sin_div_cos, cos_two_mul]
  rcases eq_or_ne (cos x) 0 with h | h
  · simp [h]
  · have hc : 1 - (2 * cos x ^ 2 - 1) = 2 * sin x ^ 2 := by
      linear_combination (-2) * sin_sq_add_cos_sq x
    have hd : 1 + (2 * cos x ^ 2 - 1) = 2 * cos x ^ 2 := by ring
    rw [hc, hd]; field_simp

/-- The reduction formula for the square of the tangent, OpenStax form. -/
@[kb "openstaxalgtrig2e" "§9.3 Reduction formulas, p. 842"]
theorem tan_sq_eq_one_sub_cos_two_mul_div (t : ℝ) :
    tan t ^ 2 = (1 - cos (2 * t)) / (1 + cos (2 * t)) := by
  have := tan_sq_half (2 * t)
  rwa [mul_div_cancel_left₀ t two_ne_zero] at this

/-- `tan (θ/2) = ± √((1 - cos θ)/(1 + cos θ))`, the sign being that of `tan (θ/2)`: stated with the absolute
value. -/
@[kb "corraltrig" "Eq 3.33, p. 88"]
theorem abs_tan_half (θ : ℝ) : |tan (θ / 2)| = √((1 - cos θ) / (1 + cos θ)) := by
  rw [← tan_sq_half, Real.sqrt_sq_eq_abs]

/-- The OpenStax half-angle formulas for the tangent: the root form (stated with the absolute value) and the
two root-free forms. -/
@[kb "openstaxalgtrig2e" "§9.3 Half-angle formulas, p. 844"]
theorem tan_half_formulas (α : ℝ) :
    |tan (α / 2)| = √((1 - cos α) / (1 + cos α)) ∧ tan (α / 2) = sin α / (1 + cos α) ∧
      tan (α / 2) = (1 - cos α) / sin α :=
  ⟨abs_tan_half α, tan_half_eq_sin_div_one_add_cos α, tan_half_eq_one_sub_cos_div_sin α⟩

/-- `cot (θ/2) = sin θ / (1 - cos θ)`. -/
@[kb "corraltrig" "Eq 3.36, p. 88"]
theorem cot_half_eq_sin_div_one_sub_cos (θ : ℝ) : cot (θ / 2) = sin θ / (1 - cos θ) := by
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  rw [mul_div_cancel_left₀ x two_ne_zero, cot_eq_cos_div_sin, sin_two_mul, cos_two_mul]
  rcases eq_or_ne (sin x) 0 with h | h
  · simp [h]
  · have hc : 1 - (2 * cos x ^ 2 - 1) = 2 * sin x ^ 2 := by
      linear_combination (-2) * sin_sq_add_cos_sq x
    rw [hc]; field_simp

/-- `cot (θ/2) = (1 + cos θ) / sin θ`. -/
@[kb "corraltrig" "Eq 3.36, p. 88"]
theorem cot_half_eq_one_add_cos_div_sin (θ : ℝ) : cot (θ / 2) = (1 + cos θ) / sin θ := by
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  rw [mul_div_cancel_left₀ x two_ne_zero, cot_eq_cos_div_sin, sin_two_mul, cos_two_mul]
  rcases eq_or_ne (sin x) 0 with h | h
  · simp [h]
  rcases eq_or_ne (cos x) 0 with h' | h'
  · simp [h']
  field_simp; ring

end UndergradKB.Trigonometry
