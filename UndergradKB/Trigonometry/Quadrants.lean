import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Common.Attr
import UndergradKB.Trigonometry.PolarCurves

/-! # Quadrants, reference angles and special values (Corral §1.4; OpenStax §7.3, §10.3)

Signs of sine, cosine and tangent by quadrant, the reference angle of an angle in `[0, 2π)` and the relation
of the trigonometric values to those of the reference angle, the polar-coordinate conventions for negative
and zero radius, and the values of sine and cosine at the multiples of `π/6` and `π/4` beyond the first
quadrant.
-/

namespace UndergradKB.Trigonometry

open Real

/-! ### Signs by quadrant -/

/-- First quadrant: sine, cosine and tangent are all positive. (TR-025) -/
@[kb "corraltrig" "Box §1.4, p. 39"]
theorem quadrant_one_signs {θ : ℝ} (h₁ : 0 < θ) (h₂ : θ < π / 2) :
    0 < sin θ ∧ 0 < cos θ ∧ 0 < tan θ := by
  have hs := sin_pos_of_pos_of_lt_pi h₁ (by linarith [pi_pos])
  have hc := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h₂⟩
  exact ⟨hs, hc, by rw [tan_eq_sin_div_cos]; positivity⟩

/-- Second quadrant: sine is positive, cosine and tangent are negative. (TR-025) -/
theorem quadrant_two_signs {θ : ℝ} (h₁ : π / 2 < θ) (h₂ : θ < π) :
    0 < sin θ ∧ cos θ < 0 ∧ tan θ < 0 := by
  have hs := sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) h₂
  have hc := cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith [pi_pos])
  exact ⟨hs, hc, by rw [tan_eq_sin_div_cos]; exact div_neg_of_pos_of_neg hs hc⟩

/-- Third quadrant: sine and cosine are negative, tangent is positive. (TR-025) -/
theorem quadrant_three_signs {θ : ℝ} (h₁ : π < θ) (h₂ : θ < 3 * π / 2) :
    sin θ < 0 ∧ cos θ < 0 ∧ 0 < tan θ := by
  have hs := sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith [pi_pos])
  have hc := cos_pos_of_mem_Ioo (x := θ - π) ⟨by linarith [pi_pos], by linarith⟩
  rw [sin_sub_pi] at hs
  rw [cos_sub_pi] at hc
  exact ⟨by linarith, by linarith, by rw [tan_eq_sin_div_cos]; exact div_pos_of_neg_of_neg (by linarith) (by linarith)⟩

/-- Fourth quadrant: sine and tangent are negative, cosine is positive. (TR-025) -/
theorem quadrant_four_signs {θ : ℝ} (h₁ : 3 * π / 2 < θ) (h₂ : θ < 2 * π) :
    sin θ < 0 ∧ 0 < cos θ ∧ tan θ < 0 := by
  have hs := sin_neg_of_neg_of_neg_pi_lt (x := θ - 2 * π) (by linarith) (by linarith [pi_pos])
  have hc := cos_pos_of_mem_Ioo (x := θ - 2 * π) ⟨by linarith, by linarith [pi_pos]⟩
  rw [sin_sub_two_pi] at hs
  rw [cos_sub_two_pi] at hc
  exact ⟨hs, hc, by rw [tan_eq_sin_div_cos]; exact div_neg_of_neg_of_pos hs hc⟩

/-! ### Reference angles -/

/-- The reference angle of `θ ∈ [0, 2π)`: the acute angle between the terminal side and the horizontal axis,
given by `θ`, `π - θ`, `θ - π`, `2π - θ` in quadrants I to IV. (TR-029) -/
noncomputable def refAngle (θ : ℝ) : ℝ :=
  if θ ≤ π / 2 then θ else if θ ≤ π then π - θ else if θ ≤ 3 * π / 2 then θ - π else 2 * π - θ

/-- The reference angle of an angle in `[0, 2π)` lies in `[0, π/2]`. (TR-040) -/
@[kb "openstaxalgtrig2e" "Box §7.3, p. 721"]
theorem refAngle_mem_Icc {θ : ℝ} (h : θ ∈ Set.Ico 0 (2 * π)) : refAngle θ ∈ Set.Icc 0 (π / 2) := by
  obtain ⟨h₀, h₁⟩ := h
  have := pi_pos
  unfold refAngle
  split_ifs with a b c <;> constructor <;> linarith

/-- Sine and cosine of an angle in `[0, 2π)` have the same absolute values as those of its reference angle
(equal up to the sign determined by the quadrant). (TR-041) -/
@[kb "openstaxalgtrig2e" "Box §7.3, p. 722"]
theorem abs_sin_cos_eq_refAngle {θ : ℝ} (h : θ ∈ Set.Ico 0 (2 * π)) :
    |sin θ| = sin (refAngle θ) ∧ |cos θ| = cos (refAngle θ) := by
  obtain ⟨h₀, h₁⟩ := h
  have hp := pi_pos
  unfold refAngle
  split_ifs with a b c
  · rw [abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h₀ (by linarith)),
      abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith, a⟩)]
    exact ⟨rfl, rfl⟩
  · have hc := cos_nonneg_of_mem_Icc (x := π - θ) ⟨by linarith, by linarith⟩
    rw [cos_pi_sub] at hc
    rw [abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h₀ b), abs_of_nonpos (by linarith), sin_pi_sub,
      cos_pi_sub]
    exact ⟨rfl, by ring⟩
  · have hs := sin_nonneg_of_nonneg_of_le_pi (x := θ - π) (by linarith) (by linarith)
    have hc := cos_nonneg_of_mem_Icc (x := θ - π) ⟨by linarith, by linarith⟩
    rw [sin_sub_pi] at hs ⊢
    rw [cos_sub_pi] at hc ⊢
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    exact ⟨rfl, rfl⟩
  · have hs := sin_nonneg_of_nonneg_of_le_pi (x := 2 * π - θ) (by linarith) (by linarith)
    have hc := cos_nonneg_of_mem_Icc (x := 2 * π - θ) ⟨by linarith, by linarith⟩
    rw [sin_two_pi_sub] at hs ⊢
    rw [cos_two_pi_sub] at hc ⊢
    rw [abs_of_nonpos (by linarith), abs_of_nonneg hc]
    exact ⟨rfl, rfl⟩

/-! ### Polar conventions -/

/-- A negative radius `-r` at angle `θ` is the point with radius `r` at angle `θ + π`. (TR-195) -/
@[kb "corraltrig" "Box §6.4, p. 154"]
theorem polarPoint_neg_eq_add_pi (r θ : ℝ) : polarPoint (-r) θ = polarPoint r (θ + π) := by
  apply Complex.ext <;> simp [polarPoint_re, polarPoint_im, cos_add_pi, sin_add_pi]

/-- Adding a full turn to the angle does not change the point. (TR-195) -/
theorem polarPoint_add_two_pi (r θ : ℝ) : polarPoint r (θ + 2 * π) = polarPoint r θ := by
  apply Complex.ext <;> simp [polarPoint_re, polarPoint_im, cos_add_two_pi, sin_add_two_pi]

/-- Radius zero is the origin, whatever the angle. (TR-195) -/
theorem polarPoint_zero_radius (θ : ℝ) : polarPoint 0 θ = 0 := by
  apply Complex.ext <;> simp [polarPoint_re, polarPoint_im]

/-- For `(x, y)` with polar coordinates `(r, θ)`, `x² + y² = r²`. (TR-197) -/
@[kb "corraltrig" "Box §6.4, p. 157 (6.10)"]
theorem polarPoint_sq_add_sq (r θ : ℝ) :
    (polarPoint r θ).re ^ 2 + (polarPoint r θ).im ^ 2 = r ^ 2 := by
  rw [polarPoint_re, polarPoint_im]
  have := sin_sq_add_cos_sq θ
  linear_combination r ^ 2 * this

/-- For `r ≠ 0`, `tan θ = y / x` for the point `(x, y)` with polar coordinates `(r, θ)` (no hypothesis on
`cos θ` is needed since both sides are `0` when it vanishes). (TR-197) -/
theorem tan_eq_im_div_re {r θ : ℝ} (hr : r ≠ 0) :
    tan θ = (polarPoint r θ).im / (polarPoint r θ).re := by
  rw [polarPoint_re, polarPoint_im, tan_eq_sin_div_cos, mul_div_mul_left _ _ hr]

/-! ### Values beyond the first quadrant -/

/-- Sine and cosine at `2π/3`, `3π/4`, `5π/6` (second quadrant). (TR-027) -/
@[kb "corraltrig" "Table 1.3, p. 37"]
theorem sin_cos_second_quadrant :
    (sin (2 * π / 3) = √3 / 2 ∧ cos (2 * π / 3) = -(1 / 2)) ∧
    (sin (3 * π / 4) = √2 / 2 ∧ cos (3 * π / 4) = -(√2 / 2)) ∧
    (sin (5 * π / 6) = 1 / 2 ∧ cos (5 * π / 6) = -(√3 / 2)) := by
  have e₁ : 2 * π / 3 = π - π / 3 := by ring
  have e₂ : 3 * π / 4 = π - π / 4 := by ring
  have e₃ : 5 * π / 6 = π - π / 6 := by ring
  rw [e₁, e₂, e₃]
  simp [sin_pi_sub, cos_pi_sub, sin_pi_div_three, cos_pi_div_three, sin_pi_div_four, cos_pi_div_four,
    sin_pi_div_six, cos_pi_div_six]

/-- Sine and cosine at `7π/6`, `5π/4`, `4π/3` (third quadrant). (TR-027) -/
theorem sin_cos_third_quadrant :
    (sin (7 * π / 6) = -(1 / 2) ∧ cos (7 * π / 6) = -(√3 / 2)) ∧
    (sin (5 * π / 4) = -(√2 / 2) ∧ cos (5 * π / 4) = -(√2 / 2)) ∧
    (sin (4 * π / 3) = -(√3 / 2) ∧ cos (4 * π / 3) = -(1 / 2)) := by
  have e₁ : 7 * π / 6 = π / 6 + π := by ring
  have e₂ : 5 * π / 4 = π / 4 + π := by ring
  have e₃ : 4 * π / 3 = π / 3 + π := by ring
  rw [e₁, e₂, e₃]
  simp [sin_add_pi, cos_add_pi, sin_pi_div_three, cos_pi_div_three, sin_pi_div_four, cos_pi_div_four,
    sin_pi_div_six, cos_pi_div_six]

/-- Sine and cosine at `5π/3`, `7π/4`, `11π/6` (fourth quadrant). (TR-027) -/
theorem sin_cos_fourth_quadrant :
    (sin (5 * π / 3) = -(√3 / 2) ∧ cos (5 * π / 3) = 1 / 2) ∧
    (sin (7 * π / 4) = -(√2 / 2) ∧ cos (7 * π / 4) = √2 / 2) ∧
    (sin (11 * π / 6) = -(1 / 2) ∧ cos (11 * π / 6) = √3 / 2) := by
  have e₁ : 5 * π / 3 = 2 * π - π / 3 := by ring
  have e₂ : 7 * π / 4 = 2 * π - π / 4 := by ring
  have e₃ : 11 * π / 6 = 2 * π - π / 6 := by ring
  rw [e₁, e₂, e₃]
  simp [sin_two_pi_sub, cos_two_pi_sub, sin_pi_div_three, cos_pi_div_three, sin_pi_div_four,
    cos_pi_div_four, sin_pi_div_six, cos_pi_div_six]

end UndergradKB.Trigonometry
