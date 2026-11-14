import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 6.3 (equations) -/

namespace UndergradKB.Precalculus.Course

private theorem x6w7e_rpow_eq {a c x : ℝ} (ha : 0 < a) (hc : 0 < c) :
    a ^ x = c ↔ x * Real.log a = Real.log c := by
  constructor
  · intro h
    have := congrArg Real.log h
    rwa [Real.log_rpow ha] at this
  · intro h
    calc a ^ x = Real.exp (Real.log a * x) := Real.rpow_def_of_pos ha x
      _ = Real.exp (Real.log c) := by rw [mul_comm, h]
      _ = c := Real.exp_log hc

private theorem x6w7e_exp_eq {y c : ℝ} (hc : 0 < c) : Real.exp y = c ↔ y = Real.log c := by
  constructor
  · intro h; rw [← h, Real.log_exp]
  · intro h; rw [h, Real.exp_log hc]

private theorem x6w7e_log_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a = b ↔ Real.log a = Real.log b :=
  ⟨fun h => by rw [h], fun h => Real.log_injOn_pos (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb) h⟩

/-- Stitz-Zeager Exercise 6.3.2: `3^(x-1) = 27` holds exactly for `x = 4`. -/
@[kb "stitzzeager2013" "Exercise 6.3.2, p. 468"]
theorem exer_6_3_2 : ∀ x : ℝ, (3 : ℝ) ^ (x - 1) = 27 ↔ x = 4 := by
  intro x
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  rw [x6w7e_rpow_eq (by norm_num) (by norm_num), h27]
  constructor
  · intro h; exact mul_right_cancel₀ hL.ne' (show x * Real.log 3 = 4 * Real.log 3 by linarith)
  · rintro rfl; ring

/-- Stitz-Zeager Exercise 6.3.3: `5^(2x-1) = 125` holds exactly for `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 6.3.3, p. 468"]
theorem exer_6_3_3 : ∀ x : ℝ, (5 : ℝ) ^ (2 * x - 1) = 125 ↔ x = 2 := by
  intro x
  have hL : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have h : Real.log 125 = 3 * Real.log 5 := by
    rw [show (125 : ℝ) = 5 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  rw [x6w7e_rpow_eq (by norm_num) (by norm_num), h]
  constructor
  · intro h; exact mul_right_cancel₀ hL.ne' (show x * Real.log 5 = 2 * Real.log 5 by linarith)
  · rintro rfl; ring

/-- Stitz-Zeager Exercise 6.3.4: `4^(2x) = 1/2` holds exactly for `x = -1/4`. -/
@[kb "stitzzeager2013" "Exercise 6.3.4, p. 468"]
theorem exer_6_3_4 : ∀ x : ℝ, (4 : ℝ) ^ (2 * x) = 1 / 2 ↔ x = -1 / 4 := by
  intro x
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [x6w7e_rpow_eq (by norm_num) (by norm_num), h4, one_div, Real.log_inv]
  constructor
  · intro h; exact mul_right_cancel₀ hL.ne' (show x * Real.log 2 = -1 / 4 * Real.log 2 by linarith)
  · rintro rfl; ring

/-- Stitz-Zeager Exercise 6.3.5: `8^x = 1/128` holds exactly for `x = -7/3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.5, p. 468"]
theorem exer_6_3_5 : ∀ x : ℝ, (8 : ℝ) ^ x = 1 / 128 ↔ x = -7 / 3 := by
  intro x
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; push_cast; ring
  rw [x6w7e_rpow_eq (by norm_num) (by norm_num), h8, one_div, Real.log_inv, h128]
  constructor
  · intro h; exact mul_right_cancel₀ hL.ne' (show x * Real.log 2 = -7 / 3 * Real.log 2 by linarith)
  · rintro rfl; ring

/-- Stitz-Zeager Exercise 6.3.8: `9 · 3^(7x) = (1/9)^(2x)` holds exactly for `x = -2/11`. -/
@[kb "stitzzeager2013" "Exercise 6.3.8, p. 468"]
theorem exer_6_3_8 : ∀ x : ℝ, 9 * (3 : ℝ) ^ (7 * x) = (1 / 9 : ℝ) ^ (2 * x) ↔ x = -2 / 11 := by
  intro x
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hp1 : 0 < (3 : ℝ) ^ (7 * x) := Real.rpow_pos_of_pos (by norm_num) _
  have hp2 : 0 < (1 / 9 : ℝ) ^ (2 * x) := Real.rpow_pos_of_pos (by norm_num) _
  rw [x6w7e_log_eq (by positivity) hp2, Real.log_mul (by norm_num) hp1.ne', Real.log_rpow (by norm_num),
    Real.log_rpow (by norm_num), one_div, Real.log_inv, h9]
  constructor
  · intro h; exact mul_right_cancel₀ hL.ne' (show x * Real.log 3 = -2 / 11 * Real.log 3 by linarith)
  · rintro rfl; ring

/-- Stitz-Zeager Exercise 6.3.10: `5^(-x) = 2` holds exactly for `x = -ln(2)/ln(5)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.10, p. 468"]
theorem exer_6_3_10 : ∀ x : ℝ, (5 : ℝ) ^ (-x) = 2 ↔ x = -Real.log 2 / Real.log 5 := by
  intro x
  have hL : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [x6w7e_rpow_eq (by norm_num) (by norm_num), eq_div_iff hL.ne']
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.11: `5^x = -2` has no real solution. -/
@[kb "stitzzeager2013" "Exercise 6.3.11, p. 468"]
theorem exer_6_3_11 : ∀ x : ℝ, (5 : ℝ) ^ x ≠ -2 := by
  intro x h
  have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5) x
  linarith

/-- Stitz-Zeager Exercise 6.3.12: `3^(x-1) = 29` holds exactly for `x = (ln 29 + ln 3)/ln 3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.12, p. 468"]
theorem exer_6_3_12 : ∀ x : ℝ, (3 : ℝ) ^ (x - 1) = 29 ↔
    x = (Real.log 29 + Real.log 3) / Real.log 3 := by
  intro x
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [x6w7e_rpow_eq (by norm_num) (by norm_num), eq_div_iff hL.ne']
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.13: `(1.005)^(12x) = 3` holds exactly for `x = ln 3 / (12 ln 1.005)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.13, p. 468"]
theorem exer_6_3_13 : ∀ x : ℝ, (1.005 : ℝ) ^ (12 * x) = 3 ↔
    x = Real.log 3 / (12 * Real.log 1.005) := by
  intro x
  have hL : 0 < Real.log 1.005 := Real.log_pos (by norm_num)
  rw [x6w7e_rpow_eq (by norm_num) (by norm_num), eq_div_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.14: `e^(-5730 k) = 1/2` holds exactly for `k = ln(2)/5730`. -/
@[kb "stitzzeager2013" "Exercise 6.3.14, p. 468"]
theorem exer_6_3_14 : ∀ k : ℝ, Real.exp (-5730 * k) = 1 / 2 ↔ k = Real.log 2 / 5730 := by
  intro k
  rw [x6w7e_exp_eq (by norm_num), one_div, Real.log_inv, eq_div_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.16: `500(1 - e^(2x)) = 250` holds exactly for `x = -(1/2) ln 2`. -/
@[kb "stitzzeager2013" "Exercise 6.3.16, p. 468"]
theorem exer_6_3_16 : ∀ x : ℝ, 500 * (1 - Real.exp (2 * x)) = 250 ↔ x = -(1 / 2) * Real.log 2 := by
  intro x
  have key : 500 * (1 - Real.exp (2 * x)) = 250 ↔ Real.exp (2 * x) = 1 / 2 := by
    constructor <;> intro h <;> linarith
  rw [key, x6w7e_exp_eq (by norm_num), one_div, Real.log_inv]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.17: `70 + 90 e^(-0.1t) = 75` holds exactly for `t = 10 ln 18`. -/
@[kb "stitzzeager2013" "Exercise 6.3.17, p. 468"]
theorem exer_6_3_17 : ∀ t : ℝ, 70 + 90 * Real.exp (-0.1 * t) = 75 ↔ t = 10 * Real.log 18 := by
  intro t
  have key : 70 + 90 * Real.exp (-0.1 * t) = 75 ↔ Real.exp (-0.1 * t) = 1 / 18 := by
    constructor <;> intro h <;> linarith
  rw [key, x6w7e_exp_eq (by norm_num), one_div, Real.log_inv]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.18: `30 - 6 e^(-0.1x) = 20` holds exactly for `x = -10 ln(5/3)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.18, p. 468"]
theorem exer_6_3_18 : ∀ x : ℝ, 30 - 6 * Real.exp (-0.1 * x) = 20 ↔ x = -10 * Real.log (5 / 3) := by
  intro x
  have key : 30 - 6 * Real.exp (-0.1 * x) = 20 ↔ Real.exp (-0.1 * x) = 5 / 3 := by
    constructor <;> intro h <;> linarith
  rw [key, x6w7e_exp_eq (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.20: `5000/(1 + 2e^(-3t)) = 2500` holds exactly for `t = ln(2)/3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.20, p. 468"]
theorem exer_6_3_20 : ∀ t : ℝ, 5000 / (1 + 2 * Real.exp (-3 * t)) = 2500 ↔ t = Real.log 2 / 3 := by
  intro t
  have hp : 0 < 1 + 2 * Real.exp (-3 * t) := by positivity
  have key : 5000 / (1 + 2 * Real.exp (-3 * t)) = 2500 ↔ Real.exp (-3 * t) = 1 / 2 := by
    rw [div_eq_iff hp.ne']
    constructor <;> intro h <;> linarith
  rw [key, x6w7e_exp_eq (by norm_num), one_div, Real.log_inv, eq_div_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.21: `150/(1 + 29e^(-0.8t)) = 75` holds exactly for `t = (5/4) ln 29`. -/
@[kb "stitzzeager2013" "Exercise 6.3.21, p. 468"]
theorem exer_6_3_21 : ∀ t : ℝ, 150 / (1 + 29 * Real.exp (-0.8 * t)) = 75 ↔ t = 5 / 4 * Real.log 29 := by
  intro t
  have hp : 0 < 1 + 29 * Real.exp (-0.8 * t) := by positivity
  have key : 150 / (1 + 29 * Real.exp (-0.8 * t)) = 75 ↔ Real.exp (-0.8 * t) = 1 / 29 := by
    rw [div_eq_iff hp.ne']
    constructor <;> intro h <;> linarith
  rw [key, x6w7e_exp_eq (by norm_num), one_div, Real.log_inv]
  constructor <;> intro h <;> linarith

end UndergradKB.Precalculus.Course
