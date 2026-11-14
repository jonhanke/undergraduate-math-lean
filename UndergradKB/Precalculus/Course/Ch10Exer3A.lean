import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 10.1 and 10.2 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 10.1 -/

/-- Stitz-Zeager Exercise 10.1.45: the arc of length `5π/6` on the unit circle ends in Quadrant II. -/
@[kb "stitzzeager2013" "Exercise 10.1.45, p. 722"]
theorem exer_10_1_45 : π / 2 < 5 * π / 6 ∧ 5 * π / 6 < π := by
  have := Real.pi_pos
  constructor <;> linarith

/-- Stitz-Zeager Exercise 10.1.46: the arc of length `-π` ends on the negative `x`-axis, at `(-1, 0)`. -/
@[kb "stitzzeager2013" "Exercise 10.1.46, p. 722"]
theorem exer_10_1_46 : cos (-π) = -1 ∧ sin (-π) = 0 := by
  simp

/-- Stitz-Zeager Exercise 10.1.47: the arc of length `6` (a bit less than one revolution) ends in
Quadrant IV. -/
@[kb "stitzzeager2013" "Exercise 10.1.47, p. 722"]
theorem exer_10_1_47 : 3 * π / 2 < 6 ∧ (6 : ℝ) < 2 * π := by
  have := Real.pi_gt_three
  have := Real.pi_lt_four
  constructor <;> linarith

/-- Stitz-Zeager Exercise 10.1.48: the arc of length `-2` (clockwise) ends in Quadrant III. -/
@[kb "stitzzeager2013" "Exercise 10.1.48, p. 722"]
theorem exer_10_1_48 : -π < (-2 : ℝ) ∧ (-2 : ℝ) < -(π / 2) := by
  have := Real.pi_gt_three
  have := Real.pi_lt_four
  constructor <;> linarith

/-- Stitz-Zeager Exercise 10.1.49: the arc of length `12` makes between one and two revolutions, and
ends in Quadrant IV (it lies in `(2π + 3π/2, 2π + 2π)`). -/
@[kb "stitzzeager2013" "Exercise 10.1.49, p. 722"]
theorem exer_10_1_49 : 2 * π < 12 ∧ (12 : ℝ) < 4 * π ∧ 2 * π + 3 * π / 2 < 12 := by
  have := Real.pi_gt_d2
  have := Real.pi_lt_d2
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## Section 10.2 -/

/-- Stitz-Zeager Exercise 10.2.55: right triangle with a `30°` angle and adjacent leg `1`:
the other acute angle is `60°`, the opposite leg is `√3/3` and the hypotenuse `2√3/3`. -/
@[kb "stitzzeager2013" "Exercise 10.2.55, p. 749"]
theorem exer_10_2_55 : π / 2 - π / 6 = π / 3 ∧ 1 * tan (π / 6) = √3 / 3 ∧
    1 / cos (π / 6) = 2 * √3 / 3 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hp : (0 : ℝ) < √3 := by positivity
  refine ⟨by ring, ?_, ?_⟩
  · rw [one_mul, Real.tan_pi_div_six]
    field_simp <;> nlinarith
  · rw [Real.cos_pi_div_six]
    field_simp <;> nlinarith

/-- Stitz-Zeager Exercise 10.2.56: right triangle with a `45°` angle and a leg `3`: the other acute
angle is `45°`, the other leg is `3` and the hypotenuse is `3√2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.56, p. 749"]
theorem exer_10_2_56 : π / 2 - π / 4 = π / 4 ∧ 3 * tan (π / 4) = 3 ∧ 3 / cos (π / 4) = 3 * √2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : (0 : ℝ) < √2 := by positivity
  refine ⟨by ring, ?_, ?_⟩
  · rw [Real.tan_pi_div_four]; ring
  · rw [Real.cos_pi_div_four]
    field_simp <;> nlinarith

end UndergradKB.Precalculus.Course
