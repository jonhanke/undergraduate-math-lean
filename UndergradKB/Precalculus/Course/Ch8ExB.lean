import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

/-- Stitz-Zeager Example 8.4.2(1c): with batteries `0` V and `10` V the mesh-current system has
the unique solution `(-45/4, -25/2, -65/4, -10)`. -/
@[kb "stitzzeager2013" "Example 8.4.2, p. 617"]
theorem ex_8_4_2_1_c (i1 i2 i3 i4 : ℝ) :
    (2 * i1 - i2 - i4 = 0 ∧ -i1 + 3 * i2 - i3 - i4 = 0 ∧ -i2 + 2 * i3 - i4 = -10 ∧
        -i1 - i2 - i3 + 4 * i4 = 0) ↔
      (i1 = -45 / 4 ∧ i2 = -25 / 2 ∧ i3 = -65 / 4 ∧ i4 = -10) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.4.2(1d): with both batteries at `10` V the unique solution is
`(5, 0, -5, 0)`. -/
@[kb "stitzzeager2013" "Example 8.4.2, p. 617"]
theorem ex_8_4_2_1_d (i1 i2 i3 i4 : ℝ) :
    (2 * i1 - i2 - i4 = 10 ∧ -i1 + 3 * i2 - i3 - i4 = 0 ∧ -i2 + 2 * i3 - i4 = -10 ∧
        -i1 - i2 - i3 + 4 * i4 = 0) ↔
      (i1 = 5 ∧ i2 = 0 ∧ i3 = -5 ∧ i4 = 0) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.4.2(2): with `V₁ = 10`, `V₂ = 5` and the mesh currents
`(85/8, 25/4, 25/8, 5)`, the resistances satisfy the general circuit system exactly when
`R1 = 16/9 - 7 R3 / 9`, `R2 = 7 R3 / 2 + 3 R6 / 2 - 4`, `R4 = 8/5 - 3 R6 / 5` and `R5 = 1`
(`R3`, `R6` free). -/
@[kb "stitzzeager2013" "Example 8.4.2, p. 617"]
theorem ex_8_4_2_2_system (R1 R2 R3 R4 R5 R6 : ℝ) :
    ((R1 + R3) * (85 / 8) - R3 * (25 / 4) - R1 * 5 = 10 ∧
      -R3 * (85 / 8) + (R2 + R3 + R4) * (25 / 4) - R4 * (25 / 8) - R2 * 5 = 0 ∧
      -R4 * (25 / 4) + (R4 + R6) * (25 / 8) - R6 * 5 = -5 ∧
      -R1 * (85 / 8) - R2 * (25 / 4) - R6 * (25 / 8) + (R1 + R2 + R5 + R6) * 5 = 0) ↔
    (R1 = 16 / 9 - 7 / 9 * R3 ∧ R2 = 7 / 2 * R3 + 3 / 2 * R6 - 4 ∧ R4 = 8 / 5 - 3 / 5 * R6 ∧
      R5 = 1) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, ?_, by linarith, ?_⟩
    · have hR4 : R4 = 8 / 5 - 3 / 5 * R6 := by linarith
      subst hR4; linarith
    · have hR1 : R1 = 16 / 9 - 7 / 9 * R3 := by linarith
      have hR4 : R4 = 8 / 5 - 3 / 5 * R6 := by linarith
      have hR2 : R2 = 7 / 2 * R3 + 3 / 2 * R6 - 4 := by subst hR4; linarith
      subst hR1 hR2; linarith
  · rintro ⟨h1, h2, h4, h5⟩
    subst h1 h2 h4 h5
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Stitz-Zeager Example 8.4.2(2): for resistances of that form, all six are positive exactly
when `0 < R3 < 16/7`, `0 < R6 < 8/3` and `7 R3 / 2 + 3 R6 / 2 - 4 > 0`. -/
@[kb "stitzzeager2013" "Example 8.4.2, p. 617"]
theorem ex_8_4_2_2_region (R1 R2 R3 R4 R5 R6 : ℝ) (h1 : R1 = 16 / 9 - 7 / 9 * R3)
    (h2 : R2 = 7 / 2 * R3 + 3 / 2 * R6 - 4) (h4 : R4 = 8 / 5 - 3 / 5 * R6) (h5 : R5 = 1) :
    (0 < R1 ∧ 0 < R2 ∧ 0 < R3 ∧ 0 < R4 ∧ 0 < R5 ∧ 0 < R6) ↔
      (0 < R3 ∧ R3 < 16 / 7 ∧ 0 < R6 ∧ R6 < 8 / 3 ∧ 0 < 7 / 2 * R3 + 3 / 2 * R6 - 4) := by
  subst h1 h2 h4 h5
  constructor
  · rintro ⟨a, b, c, d, _, f⟩
    exact ⟨c, by linarith, f, by linarith, b⟩
  · rintro ⟨a, b, c, d, e⟩
    exact ⟨by linarith, e, a, by linarith, by norm_num, c⟩

/-- Stitz-Zeager Example 8.7.2(2): `y + 4 e^(2x) = 1, y² + 2 e^x = 1` has exactly the two real
solutions `(-ln 2, 0)` and `(ln((√5-1)/4), (√5-1)/2)`. -/
@[kb "stitzzeager2013" "Example 8.7.2, p. 651"]
theorem ex_8_7_2_2 (x y : ℝ) :
    (y + 4 * Real.exp (2 * x) = 1 ∧ y ^ 2 + 2 * Real.exp x = 1) ↔
      ((x = -Real.log 2 ∧ y = 0) ∨
        (x = Real.log ((Real.sqrt 5 - 1) / 4) ∧ y = (Real.sqrt 5 - 1) / 2)) := by
  have key : ∀ t : ℝ, Real.exp (2 * t) = Real.exp t ^ 2 := fun t => by
    rw [two_mul, Real.exp_add]; ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    rw [key] at h1
    have hu := Real.exp_pos x
    have hy : y = 1 - 4 * Real.exp x ^ 2 := by linarith
    rw [hy] at h2
    have hf : Real.exp x * (2 * Real.exp x - 1) * (4 * Real.exp x ^ 2 + 2 * Real.exp x - 1) = 0 := by
      linear_combination (1 / 2) * h2
    rcases mul_eq_zero.1 hf with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hu.ne'
      · have hex : Real.exp x = 1 / 2 := by linarith
        left
        refine ⟨?_, by rw [hy, hex]; norm_num⟩
        rw [← Real.log_exp x, hex, one_div, Real.log_inv]
    · right
      have h' : (Real.exp x - (Real.sqrt 5 - 1) / 4) * (Real.exp x + (Real.sqrt 5 + 1) / 4) = 0 := by
        nlinarith
      have hpos : 0 < Real.exp x + (Real.sqrt 5 + 1) / 4 := by linarith
      have hex : Real.exp x = (Real.sqrt 5 - 1) / 4 := by
        rcases mul_eq_zero.1 h' with h | h
        · linarith
        · linarith
      refine ⟨?_, ?_⟩
      · rw [← Real.log_exp x, hex]
      · rw [hy, hex]; nlinarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hex : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      rw [key, hex]; norm_num
    · have hex : Real.exp (Real.log ((Real.sqrt 5 - 1) / 4)) = (Real.sqrt 5 - 1) / 4 :=
        Real.exp_log (by linarith)
      rw [key, hex]
      constructor <;> nlinarith

/-- Stitz-Zeager Example 8.7.2(3): `z (x-2) = x, y z = y, (x-2)² + y² = 1` has exactly the two
solutions `(1, 0, -1)` and `(3, 0, 3)`. -/
@[kb "stitzzeager2013" "Example 8.7.2, p. 651"]
theorem ex_8_7_2_3 (x y z : ℝ) :
    (z * (x - 2) = x ∧ y * z = y ∧ (x - 2) ^ 2 + y ^ 2 = 1) ↔
      ((x = 1 ∧ y = 0 ∧ z = -1) ∨ (x = 3 ∧ y = 0 ∧ z = 3)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hy : y * (z - 1) = 0 := by linarith
    rcases mul_eq_zero.1 hy with hy | hz
    · subst hy
      have : (x - 1) * (x - 3) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left
        have hx : x = 1 := by linarith
        subst hx
        exact ⟨rfl, rfl, by linarith⟩
      · right
        have hx : x = 3 := by linarith
        subst hx
        exact ⟨rfl, rfl, by linarith⟩
    · have : z = 1 := by linarith
      subst this
      linarith
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

end UndergradKB.Precalculus.Course
