import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 6.1 (rewriting, values) -/

namespace UndergradKB.Precalculus.Course

open Set

private theorem x6w7a_lg {b c a : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (hc : 0 < c) (h : b ^ a = c) :
    Real.logb b c = a := (Real.logb_eq_iff_rpow_eq hb hb1 hc).2 h

/-! ## Section 6.1: rewriting exponential and logarithmic equations -/

/-- Stitz-Zeager Exercise 6.1.6: `10^(-3) = 0.001` is equivalent to `log(0.001) = -3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.6, p. 441"]
theorem exer_6_1_6 : (10 : ℝ) ^ (-3 : ℝ) = 0.001 ∧ Real.logb 10 0.001 = -3 := by
  have h : (10 : ℝ) ^ (-3 : ℝ) = 0.001 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  exact ⟨h, x6w7a_lg (by norm_num) (by norm_num) (by norm_num) h⟩

/-- Stitz-Zeager Exercise 6.1.7: `e⁰ = 1` is equivalent to `ln(1) = 0`. -/
@[kb "stitzzeager2013" "Exercise 6.1.7, p. 441"]
theorem exer_6_1_7 : Real.exp 0 = 1 ∧ Real.log 1 = 0 := ⟨Real.exp_zero, Real.log_one⟩

/-- Stitz-Zeager Exercise 6.1.8: `log₅(25) = 2` is equivalent to `5² = 25`. -/
@[kb "stitzzeager2013" "Exercise 6.1.8, p. 441"]
theorem exer_6_1_8 : Real.logb 5 25 = 2 ∧ (5 : ℝ) ^ (2 : ℝ) = 25 := by
  have h : (5 : ℝ) ^ (2 : ℝ) = 25 := by norm_num
  exact ⟨x6w7a_lg (by norm_num) (by norm_num) (by norm_num) h, h⟩

/-- Stitz-Zeager Exercise 6.1.10: `log₃(1/81) = -4` is equivalent to `3^(-4) = 1/81`. -/
@[kb "stitzzeager2013" "Exercise 6.1.10, p. 441"]
theorem exer_6_1_10 : Real.logb 3 (1 / 81) = -4 ∧ (3 : ℝ) ^ (-4 : ℝ) = 1 / 81 := by
  have h : (3 : ℝ) ^ (-4 : ℝ) = 1 / 81 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  exact ⟨x6w7a_lg (by norm_num) (by norm_num) (by norm_num) h, h⟩

/-- Stitz-Zeager Exercise 6.1.11: `log_{3/4}(4/3) = -1` is equivalent to `(3/4)^(-1) = 4/3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.11, p. 441"]
theorem exer_6_1_11 : Real.logb (3 / 4) (4 / 3) = -1 ∧ (3 / 4 : ℝ) ^ (-1 : ℝ) = 4 / 3 := by
  have h : (3 / 4 : ℝ) ^ (-1 : ℝ) = 4 / 3 := by
    rw [Real.rpow_neg_one]; norm_num
  exact ⟨x6w7a_lg (by norm_num) (by norm_num) (by norm_num) h, h⟩

/-- Stitz-Zeager Exercise 6.1.12: `log(100) = 2` is equivalent to `10² = 100`. -/
@[kb "stitzzeager2013" "Exercise 6.1.12, p. 441"]
theorem exer_6_1_12 : Real.logb 10 100 = 2 ∧ (10 : ℝ) ^ (2 : ℝ) = 100 := by
  have h : (10 : ℝ) ^ (2 : ℝ) = 100 := by norm_num
  exact ⟨x6w7a_lg (by norm_num) (by norm_num) (by norm_num) h, h⟩

/-- Stitz-Zeager Exercise 6.1.13: `log(0.1) = -1` is equivalent to `10^(-1) = 0.1`. -/
@[kb "stitzzeager2013" "Exercise 6.1.13, p. 441"]
theorem exer_6_1_13 : Real.logb 10 0.1 = -1 ∧ (10 : ℝ) ^ (-1 : ℝ) = 0.1 := by
  have h : (10 : ℝ) ^ (-1 : ℝ) = 0.1 := by
    rw [Real.rpow_neg_one]; norm_num
  exact ⟨x6w7a_lg (by norm_num) (by norm_num) (by norm_num) h, h⟩

/-- Stitz-Zeager Exercise 6.1.14: `ln(e) = 1` is equivalent to `e¹ = e`. -/
@[kb "stitzzeager2013" "Exercise 6.1.14, p. 441"]
theorem exer_6_1_14 : Real.log (Real.exp 1) = 1 ∧ Real.exp 1 = Real.exp 1 := ⟨Real.log_exp 1, rfl⟩

/-- Stitz-Zeager Exercise 6.1.15: `ln(1/√e) = -1/2` is equivalent to `e^(-1/2) = 1/√e`. -/
@[kb "stitzzeager2013" "Exercise 6.1.15, p. 441"]
theorem exer_6_1_15 :
    Real.log (1 / Real.sqrt (Real.exp 1)) = -1 / 2 ∧ Real.exp (-1 / 2) = 1 / Real.sqrt (Real.exp 1) := by
  have h : Real.exp (-1 / 2) = 1 / Real.sqrt (Real.exp 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul, one_div, ← Real.exp_neg]; ring_nf
  refine ⟨?_, h⟩
  rw [← h, Real.log_exp]

/-! ## Section 6.1: evaluating logarithms -/

/-- Stitz-Zeager Exercise 6.1.16: `log₃(27) = 3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.16, p. 441"]
theorem exer_6_1_16 : Real.logb 3 27 = 3 :=
  x6w7a_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 6.1.17: `log₆(216) = 3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.17, p. 441"]
theorem exer_6_1_17 : Real.logb 6 216 = 3 :=
  x6w7a_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 6.1.18: `log₂(32) = 5`. -/
@[kb "stitzzeager2013" "Exercise 6.1.18, p. 441"]
theorem exer_6_1_18 : Real.logb 2 32 = 5 :=
  x6w7a_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 6.1.20: `log₈(4) = 2/3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.20, p. 441"]
theorem exer_6_1_20 : Real.logb 8 4 = 2 / 3 := by
  refine x6w7a_lg (by norm_num) (by norm_num) (by norm_num) ?_
  rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.1.21: `log₃₆(216) = 3/2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.21, p. 441"]
theorem exer_6_1_21 : Real.logb 36 216 = 3 / 2 := by
  refine x6w7a_lg (by norm_num) (by norm_num) (by norm_num) ?_
  rw [show (36 : ℝ) = 6 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.1.22: `log_{1/5}(625) = -4`. -/
@[kb "stitzzeager2013" "Exercise 6.1.22, p. 441"]
theorem exer_6_1_22 : Real.logb (1 / 5) 625 = -4 := by
  refine x6w7a_lg (by norm_num) (by norm_num) (by norm_num) ?_
  rw [Real.rpow_neg (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.1.23: `log_{1/6}(216) = -3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.23, p. 441"]
theorem exer_6_1_23 : Real.logb (1 / 6) 216 = -3 := by
  refine x6w7a_lg (by norm_num) (by norm_num) (by norm_num) ?_
  rw [Real.rpow_neg (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.1.24: `log₃₆(36) = 1`. -/
@[kb "stitzzeager2013" "Exercise 6.1.24, p. 441"]
theorem exer_6_1_24 : Real.logb 36 36 = 1 := Real.logb_self_eq_one (by norm_num)

/-- Stitz-Zeager Exercise 6.1.26: `log(0.01) = -2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.26, p. 441"]
theorem exer_6_1_26 : Real.logb 10 0.01 = -2 := by
  refine x6w7a_lg (by norm_num) (by norm_num) (by norm_num) ?_
  rw [Real.rpow_neg (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.1.27: `ln(e³) = 3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.27, p. 441"]
theorem exer_6_1_27 : Real.log (Real.exp 1 ^ 3) = 3 := by
  rw [Real.log_pow]; simp

/-- Stitz-Zeager Exercise 6.1.29: `log₆(1) = 0`. -/
@[kb "stitzzeager2013" "Exercise 6.1.29, p. 441"]
theorem exer_6_1_29 : Real.logb 6 1 = 0 := Real.logb_one

/-- Stitz-Zeager Exercise 6.1.30: `log₁₃(√13) = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.30, p. 441"]
theorem exer_6_1_30 : Real.logb 13 (Real.sqrt 13) = 1 / 2 := by
  refine x6w7a_lg (by norm_num) (by norm_num) (by positivity) ?_
  rw [Real.sqrt_eq_rpow]

/-- Stitz-Zeager Exercise 6.1.31: `log₃₆(⁴√36) = 1/4`. -/
@[kb "stitzzeager2013" "Exercise 6.1.31, p. 441"]
theorem exer_6_1_31 : Real.logb 36 ((36 : ℝ) ^ (1 / 4 : ℝ)) = 1 / 4 :=
  x6w7a_lg (by norm_num) (by norm_num) (by positivity) rfl

/-- Stitz-Zeager Exercise 6.1.33: `36^(log₃₆(216)) = 216`. -/
@[kb "stitzzeager2013" "Exercise 6.1.33, p. 441"]
theorem exer_6_1_33 : (36 : ℝ) ^ (Real.logb 36 216) = 216 :=
  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 6.1.34: `log₃₆(36^216) = 216`. -/
@[kb "stitzzeager2013" "Exercise 6.1.34, p. 441"]
theorem exer_6_1_34 : Real.logb 36 ((36 : ℝ) ^ (216 : ℝ)) = 216 := by
  rw [Real.logb_rpow (by norm_num) (by norm_num)]

/-- Stitz-Zeager Exercise 6.1.35: `ln(e⁵) = 5`. -/
@[kb "stitzzeager2013" "Exercise 6.1.35, p. 441"]
theorem exer_6_1_35 : Real.log (Real.exp 1 ^ 5) = 5 := by
  rw [Real.log_pow]; simp

/-- Stitz-Zeager Exercise 6.1.37: `log(∛(10⁵)) = 5/3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.37, p. 441"]
theorem exer_6_1_37 : Real.logb 10 (((10 : ℝ) ^ (5 : ℕ)) ^ (1 / 3 : ℝ)) = 5 / 3 := by
  refine x6w7a_lg (by norm_num) (by norm_num) (by positivity) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.1.38: `ln(1/√e) = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.38, p. 441"]
theorem exer_6_1_38 : Real.log (1 / Real.sqrt (Real.exp 1)) = -1 / 2 := exer_6_1_15.1

/-- Stitz-Zeager Exercise 6.1.39: `log₅(3^(log₃ 5)) = 1`. -/
@[kb "stitzzeager2013" "Exercise 6.1.39, p. 441"]
theorem exer_6_1_39 : Real.logb 5 ((3 : ℝ) ^ (Real.logb 3 5)) = 1 := by
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  exact Real.logb_self_eq_one (by norm_num)

/-- Stitz-Zeager Exercise 6.1.40: `log(e^(ln 100)) = 2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.40, p. 441"]
theorem exer_6_1_40 : Real.logb 10 (Real.exp (Real.log 100)) = 2 := by
  rw [Real.exp_log (by norm_num)]
  exact x6w7a_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 6.1.41: `log₂(3^(-log₃ 2)) = -1`. -/
@[kb "stitzzeager2013" "Exercise 6.1.41, p. 441"]
theorem exer_6_1_41 : Real.logb 2 ((3 : ℝ) ^ (-Real.logb 3 2)) = -1 := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  rw [Real.logb_inv, Real.logb_self_eq_one (by norm_num)]

/-- Stitz-Zeager Exercise 6.1.42: `ln(4^(26 log 1)) = 0`. -/
@[kb "stitzzeager2013" "Exercise 6.1.42, p. 441"]
theorem exer_6_1_42 : Real.log ((4 : ℝ) ^ (26 * Real.logb 10 1)) = 0 := by
  simp

end UndergradKB.Precalculus.Course
