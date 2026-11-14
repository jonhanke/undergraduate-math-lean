import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers, Sections 6.1 and 6.2 -/

namespace UndergradKB.Precalculus.Course

open Set Real

/-! ## Helpers -/

private theorem logb_zpow_aux {a b x : ℝ} (ha : 1 < a) (m n : ℤ) (hm : m ≠ 0) (hb : b = a ^ m)
    (hx : x = a ^ n) : logb b x = n / m := by
  subst hb hx
  have h0 : 0 < a := by linarith
  have h1 : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  rw [Real.logb, Real.log_zpow, Real.log_zpow]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp

/-! ## Section 6.1 -/

/-- Stitz-Zeager Exercise 6.1.1: `2³ = 8` is equivalent to `log₂ 8 = 3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.1, p. 441"]
theorem exer_6_1_1 : (2 : ℝ) ^ (3 : ℝ) = 8 ∧ logb 2 8 = 3 := by
  have h := logb_zpow_aux (a := 2) (b := 2) (x := 8) (by norm_num) 1 3 one_ne_zero (by norm_num)
    (by norm_num)
  refine ⟨?_, by simpa using h⟩
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

/-- Stitz-Zeager Exercise 6.1.2: `5⁻³ = 1/125` is equivalent to `log₅ (1/125) = -3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.2, p. 441"]
theorem exer_6_1_2 : (5 : ℝ) ^ (-3 : ℝ) = 1 / 125 ∧ logb 5 (1 / 125) = -3 := by
  have h := logb_zpow_aux (a := 5) (b := 5) (x := 1 / 125) (by norm_num) 1 (-3) one_ne_zero
    (by norm_num) (by norm_num)
  refine ⟨?_, by simpa using h⟩
  rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num

/-- Stitz-Zeager Exercise 6.1.3: `4^(5/2) = 32` is equivalent to `log₄ 32 = 5/2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.3, p. 441"]
theorem exer_6_1_3 : (4 : ℝ) ^ ((5 : ℝ) / 2) = 32 ∧ logb 4 32 = 5 / 2 := by
  have h := logb_zpow_aux (a := 2) (b := 4) (x := 32) (by norm_num) 2 5 (by norm_num)
    (by norm_num) (by norm_num)
  have h' : logb 4 32 = 5 / 2 := by simpa using h
  refine ⟨?_, h'⟩
  rw [← h']
  exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 6.1.4: `(1/3)^(-2) = 9` is equivalent to `log_{1/3} 9 = -2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.4, p. 441"]
theorem exer_6_1_4 : ((1 : ℝ) / 3) ^ (-2 : ℝ) = 9 ∧ logb (1 / 3) 9 = -2 := by
  have h := logb_zpow_aux (a := 3) (b := 1 / 3) (x := 9) (by norm_num) (-1) 2 (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨?_, by rw [h]; norm_num⟩
  rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num

/-- Stitz-Zeager Exercise 6.1.5: `(4/25)^(-1/2) = 5/2` is equivalent to `log_{4/25} (5/2) = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.5, p. 441"]
theorem exer_6_1_5 : ((4 : ℝ) / 25) ^ (-1 / 2 : ℝ) = 5 / 2 ∧ logb (4 / 25) (5 / 2) = -1 / 2 := by
  have h := logb_zpow_aux (a := 5 / 2) (b := 4 / 25) (x := 5 / 2) (by norm_num) (-2) 1
    (by norm_num) (by norm_num) (by norm_num)
  have h' : logb (4 / 25) (5 / 2) = -1 / 2 := by
    rw [h]; norm_num
  refine ⟨?_, h'⟩
  rw [← h']
  exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 6.1.9: `25^(1/2) = 5` is equivalent to `log₂₅ 5 = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.9, p. 441"]
theorem exer_6_1_9 : (25 : ℝ) ^ ((1 : ℝ) / 2) = 5 ∧ logb 25 5 = 1 / 2 := by
  have h := logb_zpow_aux (a := 5) (b := 25) (x := 5) (by norm_num) 2 1 (by norm_num)
    (by norm_num) (by norm_num)
  have h' : logb 25 5 = 1 / 2 := by simpa using h
  refine ⟨?_, h'⟩
  rw [← h']
  exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercises 6.1.19, 6.1.20, 6.1.21, 6.1.22: `log₆ (1/36) = -2`, `log₈ 4 = 2/3`,
`log₃₆ 216 = 3/2`, `log_{1/5} 625 = -4`. -/
@[kb "stitzzeager2013" "Exercise 6.1.19, p. 441"]
theorem exer_6_1_19_to_22 : logb 6 (1 / 36) = -2 ∧ logb 8 4 = 2 / 3 ∧ logb 36 216 = 3 / 2 ∧
    logb (1 / 5) 625 = -4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := logb_zpow_aux (a := 6) (b := 6) (x := 1 / 36) (by norm_num) 1 (-2) one_ne_zero
      (by norm_num) (by norm_num)
    simpa using h
  · have h := logb_zpow_aux (a := 2) (b := 8) (x := 4) (by norm_num) 3 2 (by norm_num)
      (by norm_num) (by norm_num)
    simpa using h
  · have h := logb_zpow_aux (a := 6) (b := 36) (x := 216) (by norm_num) 2 3 (by norm_num)
      (by norm_num) (by norm_num)
    simpa using h
  · have h := logb_zpow_aux (a := 5) (b := 1 / 5) (x := 625) (by norm_num) (-1) 4 (by norm_num)
      (by norm_num) (by norm_num)
    rw [h]; norm_num

/-- Stitz-Zeager Exercises 6.1.25, 6.1.26, 6.1.27: `log (1/1000000) = -6`, `log 0.01 = -2`,
`ln (e³) = 3`. -/
@[kb "stitzzeager2013" "Exercise 6.1.25, p. 441"]
theorem exer_6_1_25_to_27 : logb 10 (1 / 1000000) = -6 ∧ logb 10 0.01 = -2 ∧
    Real.log (exp 3) = 3 := by
  refine ⟨?_, ?_, Real.log_exp 3⟩
  · have h := logb_zpow_aux (a := 10) (b := 10) (x := 1 / 1000000) (by norm_num) 1 (-6)
      one_ne_zero (by norm_num) (by norm_num)
    simpa using h
  · have h := logb_zpow_aux (a := 10) (b := 10) (x := 0.01) (by norm_num) 1 (-2)
      one_ne_zero (by norm_num) (by norm_num)
    simpa using h

/-- Stitz-Zeager Exercises 6.1.28, 6.1.30, 6.1.31: `log₄ 8 = 3/2`, `log₁₃ √13 = 1/2`, and
`log₃₆` of the fourth root of `36` equals `1/4`. -/
@[kb "stitzzeager2013" "Exercise 6.1.28, p. 441"]
theorem exer_6_1_28_30_31 : logb 4 8 = 3 / 2 ∧ logb 13 (Real.sqrt 13) = 1 / 2 ∧
    logb 36 ((36 : ℝ) ^ ((1 : ℝ) / 4)) = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := logb_zpow_aux (a := 2) (b := 4) (x := 8) (by norm_num) 2 3 (by norm_num)
      (by norm_num) (by norm_num)
    simpa using h
  · rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos (by norm_num),
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  · rw [Real.logb_rpow_eq_mul_logb_of_pos (by norm_num), Real.logb_self_eq_one (by norm_num)]
    norm_num

/-- Stitz-Zeager Exercises 6.1.32, 6.1.33, 6.1.39, 6.1.41: `7^(log₇ 3) = 3`, `36^(log₃₆ 216) = 216`,
`log₅ (3^(log₃ 5)) = 1` and `log₂ (3^(-log₃ 2)) = -1`. -/
@[kb "stitzzeager2013" "Exercise 6.1.32, p. 441"]
theorem exer_6_1_32_33_39_41 : (7 : ℝ) ^ (logb 7 3) = 3 ∧ (36 : ℝ) ^ (logb 36 216) = 216 ∧
    logb 5 ((3 : ℝ) ^ (logb 3 5)) = 1 ∧ logb 2 ((3 : ℝ) ^ (-logb 3 2)) = -1 := by
  refine ⟨Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), ?_, ?_⟩
  · rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.logb_self_eq_one (by norm_num)]
  · rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.logb_inv, Real.logb_self_eq_one (by norm_num)]

/-- Stitz-Zeager Exercises 6.1.36, 6.1.37, 6.1.40: with the common logarithm, `log` of the ninth root of
`10¹¹` is `11/9`, `log` of the cube root of `10⁵` is `5/3`, and `log (e^(ln 100)) = 2`. -/
@[kb "stitzzeager2013" "Exercise 6.1.36, p. 441"]
theorem exer_6_1_36_37_40 : logb 10 ((10 : ℝ) ^ ((11 : ℝ) / 9)) = 11 / 9 ∧
    logb 10 ((10 : ℝ) ^ ((5 : ℝ) / 3)) = 5 / 3 ∧ logb 10 (exp (Real.log 100)) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.logb_rpow (by norm_num) (by norm_num)]
  · rw [Real.logb_rpow (by norm_num) (by norm_num)]
  · rw [Real.exp_log (by norm_num)]
    have h := logb_zpow_aux (a := 10) (b := 10) (x := 100) (by norm_num) 1 2
      one_ne_zero (by norm_num) (by norm_num)
    simpa using h

/-- Stitz-Zeager Exercises 6.1.43, 6.1.44, 6.1.45: the domains (where the argument is positive) of
`ln (x²+1)`, `log₇ (4x+8)`, `ln (4x-20)` are `ℝ`, `(-2, ∞)`, `(5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.43, p. 441"]
theorem exer_6_1_43_to_45 : {x : ℝ | 0 < x ^ 2 + 1} = univ ∧ {x : ℝ | 0 < 4 * x + 8} = Ioi (-2) ∧
    {x : ℝ | 0 < 4 * x - 20} = Ioi 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp only [mem_ofPred_eq, mem_univ, mem_Ioi, iff_true]
  · positivity
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercises 6.1.46, 6.1.47, 6.1.48: domains of `log (x²+9x+18)`, `log ((x+2)/(x²-1))`,
`log ((x²+9x+18)/(4x-20))` are `(-∞,-6) ∪ (-3,∞)`, `(-2,-1) ∪ (1,∞)`, `(-6,-3) ∪ (5,∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.46, p. 441"]
theorem exer_6_1_46_47_48 :
    {x : ℝ | 0 < x ^ 2 + 9 * x + 18} = Iio (-6) ∪ Ioi (-3) ∧
    {x : ℝ | 0 < (x + 2) / (x ^ 2 - 1)} = Ioo (-2) (-1) ∪ Ioi 1 ∧
    {x : ℝ | 0 < (x ^ 2 + 9 * x + 18) / (4 * x - 20)} = Ioo (-6) (-3) ∪ Ioi 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, mem_Ioo]
  · constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (by linarith [hc.1] : (0 : ℝ) ≤ x + 6) (by linarith [hc.2] : (0 : ℝ) ≤ -3 - x)]
    · rintro (h | h)
      · nlinarith [mul_pos (by linarith : (0 : ℝ) < -(x + 3)) (by linarith : (0 : ℝ) < -(x + 6))]
      · nlinarith [mul_pos (by linarith : (0 : ℝ) < x + 3) (by linarith : (0 : ℝ) < x + 6)]
  · rw [div_pos_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have : x < -1 ∨ 1 < x := by
          by_contra hc
          push Not at hc
          nlinarith [mul_nonneg (by linarith [hc.1] : (0 : ℝ) ≤ x + 1) (by linarith [hc.2] : (0 : ℝ) ≤ 1 - x)]
        rcases this with h | h
        · exact Or.inl ⟨by linarith, h⟩
        · exact Or.inr h
      · nlinarith
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl ⟨by linarith, by nlinarith⟩
      · exact Or.inl ⟨by linarith, by nlinarith⟩
  · rw [div_pos_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · right; linarith
      · left
        constructor
        · by_contra hc
          push Not at hc
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -(x + 3)) (by linarith : (0 : ℝ) ≤ -(x + 6))]
        · by_contra hc
          push Not at hc
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x + 3) (by linarith : (0 : ℝ) ≤ x + 6)]
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inr ⟨by nlinarith, by linarith⟩
      · exact Or.inl ⟨by nlinarith, by linarith⟩

/-- Stitz-Zeager Exercises 6.1.49, 6.1.50: the domain of `ln (7-x) + ln (x-4)` is `(4, 7)`, and that of
`ln (4x-20) + ln (x²+9x+18)` is `(5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.49, p. 442"]
theorem exer_6_1_49_50 : {x : ℝ | 0 < 7 - x ∧ 0 < x - 4} = Ioo 4 7 ∧
    {x : ℝ | 0 < 4 * x - 20 ∧ 0 < x ^ 2 + 9 * x + 18} = Ioi 5 := by
  refine ⟨?_, ?_⟩ <;> ext x <;> simp only [mem_ofPred_eq, mem_Ioo, mem_Ioi]
  · constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  · constructor
    · rintro ⟨h1, h2⟩; linarith
    · intro h; exact ⟨by linarith, by nlinarith⟩

/-- Stitz-Zeager Exercise 6.1.53: the domain of `log₉ (|x+3| - 4)` is `(-∞, -7) ∪ (1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.53, p. 442"]
theorem exer_6_1_53 : {x : ℝ | 0 < |x + 3| - 4} = Iio (-7) ∪ Ioi 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]
  constructor
  · intro h
    rcases le_or_gt 0 (x + 3) with h0 | h0
    · rw [abs_of_nonneg h0] at h; right; linarith
    · rw [abs_of_neg h0] at h; left; linarith
  · rintro (h | h)
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith

/-- Stitz-Zeager Exercise 6.1.54: the domain of `ln (√(x-4) - 3)` is `(13, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.54, p. 442"]
theorem exer_6_1_54 : {x : ℝ | 0 ≤ x - 4 ∧ 0 < Real.sqrt (x - 4) - 3} = Ioi 13 := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioi]
  constructor
  · rintro ⟨h0, h⟩
    have : 3 < Real.sqrt (x - 4) := by linarith
    have := (Real.lt_sqrt (by norm_num)).1 this
    linarith
  · intro h
    refine ⟨by linarith, ?_⟩
    have : (3 : ℝ) < Real.sqrt (x - 4) := (Real.lt_sqrt (by norm_num)).2 (by linarith)
    linarith

/-- Stitz-Zeager Exercise 6.1.55: the domain of `1 / (3 - log₅ x)` (where `x > 0` and the denominator is
nonzero) is `(0, 125) ∪ (125, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.55, p. 442"]
theorem exer_6_1_55 : {x : ℝ | 0 < x ∧ 3 - logb 5 x ≠ 0} = Ioo 0 125 ∪ Ioi 125 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨hx, h⟩
    have hne : x ≠ 125 := by
      rintro rfl
      apply h
      have := logb_zpow_aux (a := 5) (b := 5) (x := 125) (by norm_num) 1 3 one_ne_zero
        (by norm_num) (by norm_num)
      rw [this]; norm_num
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact Or.inl ⟨hx, h1⟩
    · exact Or.inr h1
  · intro h
    have hx : 0 < x := by rcases h with ⟨h1, _⟩ | h <;> linarith
    refine ⟨hx, fun h0 => ?_⟩
    have h3 : logb 5 x = 3 := by linarith
    have : x = 125 := by
      have := (Real.logb_eq_iff_rpow_eq (by norm_num : (0 : ℝ) < 5) (by norm_num) hx).1 h3
      rw [← this]
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rcases h with ⟨_, h2⟩ | h2 <;> linarith

/-- Stitz-Zeager Exercise 6.1.57: the domain of `ln (-2x³ - x² + 13x - 6)` is
`(-∞, -3) ∪ (1/2, 2)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.57, p. 442"]
theorem exer_6_1_57 : {x : ℝ | 0 < -2 * x ^ 3 - x ^ 2 + 13 * x - 6} = Iio (-3) ∪ Ioo (1 / 2) 2 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo]
  have key : -2 * x ^ 3 - x ^ 2 + 13 * x - 6 = (2 - x) * (2 * x - 1) * (x + 3) := by ring
  rw [key]
  constructor
  · intro h
    rcases lt_or_ge x (-3) with h1 | h1
    · exact Or.inl h1
    · right
      rcases le_or_gt x (1 / 2) with h2 | h2
      · exfalso
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - x)
          (by linarith : (0 : ℝ) ≤ 1 / 2 - x)) (by linarith : (0 : ℝ) ≤ x + 3)]
      · rcases lt_or_ge x 2 with h3 | h3
        · exact ⟨h2, h3⟩
        · exfalso
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2)
            (by linarith : (0 : ℝ) ≤ 2 * x - 1)) (by linarith : (0 : ℝ) ≤ x + 3)]
  · rintro (h | ⟨h1, h2⟩)
    · nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < 2 - x) (by linarith : (0 : ℝ) < 1 - 2 * x))
        (by linarith : (0 : ℝ) < -(x + 3))]
    · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- Stitz-Zeager Exercises 6.1.71, 6.1.72: `f(x) = 3^(x+2) - 4` has inverse `log₃ (x+4) - 2`, and
`f(x) = log₄ (x-1)` has inverse `4^x + 1` (compositions both ways on the natural domains). -/
@[kb "stitzzeager2013" "Exercise 6.1.71, p. 442"]
theorem exer_6_1_71_72 :
    ((∀ x : ℝ, logb 3 ((3 : ℝ) ^ (x + 2) - 4 + 4) - 2 = x) ∧
      ∀ y : ℝ, -4 < y → (3 : ℝ) ^ (logb 3 (y + 4) - 2 + 2) - 4 = y) ∧
    ((∀ x : ℝ, 1 < x → (4 : ℝ) ^ (logb 4 (x - 1)) + 1 = x) ∧
      ∀ y : ℝ, logb 4 ((4 : ℝ) ^ y + 1 - 1) = y) := by
  refine ⟨⟨fun x => ?_, fun y hy => ?_⟩, ⟨fun x hx => ?_, fun y => ?_⟩⟩
  · rw [sub_add_cancel, Real.logb_rpow (by norm_num) (by norm_num)]; ring
  · rw [sub_add_cancel, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  · rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  · rw [add_sub_cancel_right, Real.logb_rpow (by norm_num) (by norm_num)]

/-- Stitz-Zeager Exercises 6.1.73, 6.1.74: `f(x) = -2^(-x) + 1` has inverse `-log₂ (1-x)`, and
`f(x) = 5 log x - 2` has inverse `10^((x+2)/5)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.73, p. 442"]
theorem exer_6_1_73_74 :
    ((∀ x : ℝ, -logb 2 (1 - (-(2 : ℝ) ^ (-x) + 1)) = x) ∧
      ∀ y : ℝ, y < 1 → -(2 : ℝ) ^ (-(-logb 2 (1 - y))) + 1 = y) ∧
    ((∀ x : ℝ, 0 < x → (10 : ℝ) ^ ((5 * logb 10 x - 2 + 2) / 5) = x) ∧
      ∀ y : ℝ, 5 * logb 10 ((10 : ℝ) ^ ((y + 2) / 5)) - 2 = y) := by
  refine ⟨⟨fun x => ?_, fun y hy => ?_⟩, ⟨fun x hx => ?_, fun y => ?_⟩⟩
  · have : 1 - (-(2 : ℝ) ^ (-x) + 1) = (2 : ℝ) ^ (-x) := by ring
    rw [this, Real.logb_rpow (by norm_num) (by norm_num)]; ring
  · rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  · have : (5 * logb 10 x - 2 + 2) / 5 = logb 10 x := by ring
    rw [this, Real.rpow_logb (by norm_num) (by norm_num) hx]
  · rw [Real.logb_rpow (by norm_num) (by norm_num)]; ring

/-- Stitz-Zeager Exercise 6.1.75: with `M(x) = log (x / 0.001)`, `M(0.001) = 0`, `M(80000)` is between
`7.9` and `7.95`, and a reading with magnitude `6.7` is ten times a reading with magnitude `5.7`. -/
@[kb "stitzzeager2013" "Exercise 6.1.75, p. 443"]
theorem exer_6_1_75 :
    let M : ℝ → ℝ := fun x => logb 10 (x / 0.001)
    M 0.001 = 0 ∧ (7.9 < M 80000 ∧ M 80000 < 7.95) ∧
      ∀ x y : ℝ, 0 < x → 0 < y → M x = 6.7 → M y = 5.7 → x = 10 * y := by
  intro M
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · simp only [M]; rw [div_self (by norm_num)]; simp
  · simp only [M]
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    have h : ((10 : ℝ) ^ (79 / 10 : ℝ)) ^ 10 = 10 ^ 79 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    refine lt_of_pow_lt_pow_left₀ 10 (by norm_num) ?_
    rw [show (7.9 : ℝ) = 79 / 10 by norm_num, h]; norm_num
  · simp only [M]
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    have h : ((10 : ℝ) ^ (159 / 20 : ℝ)) ^ 20 = 10 ^ 159 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    refine lt_of_pow_lt_pow_left₀ 20 (by positivity) ?_
    rw [show (7.95 : ℝ) = 159 / 20 by norm_num, h]; norm_num
  · intro x y hx hy hxM hyM
    simp only [M] at hxM hyM
    have h1 := (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity)).1 hxM
    have h2 := (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity)).1 hyM
    have h3 : (10 : ℝ) ^ (6.7 : ℝ) = 10 * (10 : ℝ) ^ (5.7 : ℝ) := by
      rw [show (6.7 : ℝ) = 1 + 5.7 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one]
    have : x / 0.001 = 10 * (y / 0.001) := by rw [← h1, ← h2, h3]
    field_simp at this
    linarith

/-- Stitz-Zeager Exercise 6.1.76: with `L(I) = 10 log (I / 10⁻¹²)`, `L(10⁻⁶) = 60`, `L(1) = 120`, and
for positive `I`, `L(I) = 115` exactly when `I = 10^(-1/2)`, which lies between `0.316` and `0.317`. -/
@[kb "stitzzeager2013" "Exercise 6.1.76, p. 443"]
theorem exer_6_1_76 :
    let L : ℝ → ℝ := fun I => 10 * logb 10 (I / 10 ^ (-12 : ℤ))
    L (10 ^ (-6 : ℤ)) = 60 ∧ L 1 = 120 ∧
      (∀ I : ℝ, 0 < I → (L I = 115 ↔ I = (10 : ℝ) ^ (-1 / 2 : ℝ))) ∧
      (0.316 < (10 : ℝ) ^ (-1 / 2 : ℝ) ∧ (10 : ℝ) ^ (-1 / 2 : ℝ) < 0.317) := by
  intro L
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [L]
    have h := logb_zpow_aux (a := 10) (b := 10) (x := 10 ^ (-6 : ℤ) / 10 ^ (-12 : ℤ))
      (by norm_num) 1 6 one_ne_zero (by norm_num) (by rw [← zpow_sub₀ (by norm_num)]; norm_num)
    rw [h]; norm_num
  · simp only [L]
    have h := logb_zpow_aux (a := 10) (b := 10) (x := 1 / 10 ^ (-12 : ℤ))
      (by norm_num) 1 12 one_ne_zero (by norm_num) (by norm_num)
    rw [h]; norm_num
  · intro I hI
    simp only [L]
    have hpos : (0 : ℝ) < I / 10 ^ (-12 : ℤ) := by positivity
    have e : 10 * logb 10 (I / 10 ^ (-12 : ℤ)) = 115 ↔ logb 10 (I / 10 ^ (-12 : ℤ)) = 23 / 2 := by
      constructor <;> intro h <;> linarith
    rw [e, Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hpos]
    have h12 : (10 : ℝ) ^ (23 / 2 : ℝ) = 10 ^ (-1 / 2 : ℝ) / 10 ^ (-12 : ℤ) := by
      rw [eq_div_iff (by positivity), ← Real.rpow_intCast (10 : ℝ) (-12),
        ← Real.rpow_add (by norm_num)]
      norm_num
    rw [h12, div_left_inj' (by positivity)]
    exact eq_comm
  · have h : (10 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 10)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]; norm_num
    rw [h]
    have hs : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
    have h1 : Real.sqrt 10 < 1 / 0.316 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have h2 : 1 / 0.317 < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    constructor
    · rw [lt_inv_comm₀ (by norm_num) hs]; linarith
    · rw [inv_lt_comm₀ hs (by norm_num)]; linarith

/-- Stitz-Zeager Exercise 6.1.77: with `pH = -log [H⁺]`, pure water (`[H⁺] = 10⁻⁷`) has pH `7`, and a
solution of pH `0.7` has `[H⁺] = 10^(-0.7)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.77, p. 444"]
theorem exer_6_1_77 :
    (-logb 10 ((10 : ℝ) ^ (-7 : ℤ)) = 7) ∧
      ∀ h : ℝ, 0 < h → (-logb 10 h = 7 / 10 ↔ h = (10 : ℝ) ^ (-7 / 10 : ℝ)) := by
  refine ⟨?_, fun h hh => ?_⟩
  · have := logb_zpow_aux (a := 10) (b := 10) (x := 10 ^ (-7 : ℤ)) (by norm_num) 1 (-7)
      one_ne_zero (by norm_num) rfl
    rw [this]; norm_num
  · have e : -logb 10 h = 7 / 10 ↔ logb 10 h = -7 / 10 := by
      constructor <;> intro h' <;> linarith
    rw [e, Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hh]
    exact eq_comm

/-- Stitz-Zeager Exercise 6.1.78: `log_b 1 = 0` and `log_b b = 1` for `b > 0`, `b ≠ 1`. -/
@[kb "stitzzeager2013" "Exercise 6.1.78, p. 444"]
theorem exer_6_1_78 (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) : logb b 1 = 0 ∧ logb b b = 1 :=
  ⟨Real.logb_one, by rw [Real.logb]; exact div_self (Real.log_ne_zero_of_pos_of_ne_one hb hb1)⟩

/-- Stitz-Zeager Exercise 6.1.79: `π ^ e < e ^ π`. -/
@[kb "stitzzeager2013" "Exercise 6.1.79, p. 444"]
theorem exer_6_1_79 : Real.pi ^ (exp 1) < exp Real.pi := by
  have he : 0 < exp 1 := exp_pos 1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hne : Real.pi / exp 1 ≠ 1 := by
    intro h
    have : Real.pi = exp 1 := by field_simp at h; exact h
    have h3 : 3 < Real.pi := Real.pi_gt_three
    have := Real.exp_one_lt_three
    linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hpi he) hne
  rw [Real.log_div hpi.ne' he.ne', Real.log_exp] at h
  rw [Real.rpow_def_of_pos hpi]
  apply Real.exp_lt_exp.2
  have : Real.log Real.pi < Real.pi / exp 1 := by linarith
  rw [lt_div_iff₀ he] at this
  exact this

end UndergradKB.Precalculus.Course
