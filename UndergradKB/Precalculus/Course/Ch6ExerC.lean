import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers, Section 6.3 -/

namespace UndergradKB.Precalculus.Course

open Set Real

/-! ## Helpers -/

private theorem rpow_eq_iff_aux {a c u : ℝ} (ha : 1 < a) (hc : 0 < c) : a ^ u = c ↔ u = logb a c :=
  ((Real.logb_eq_iff_rpow_eq (by linarith) (by linarith) hc).symm).trans eq_comm

private theorem pow_inj_aux {a u v : ℝ} (ha : 1 < a) : a ^ u = a ^ v ↔ u = v := by
  rw [rpow_eq_iff_aux ha (Real.rpow_pos_of_pos (by linarith) v), Real.logb_rpow (by linarith)
    (by linarith)]

private theorem pow_zpow_iff_aux {a : ℝ} (ha : 1 < a) (n : ℤ) (c : ℝ) (hc : c = a ^ n) (u : ℝ) :
    a ^ u = c ↔ u = n := by
  subst hc
  rw [← Real.rpow_intCast, pow_inj_aux ha]

private theorem base_rw_aux {a c : ℝ} (ha : 0 < a) (n : ℤ) (hc : c = a ^ n) (u : ℝ) :
    c ^ u = a ^ ((n : ℝ) * u) := by
  subst hc
  rw [← Real.rpow_intCast, ← Real.rpow_mul ha.le]

private theorem exp_eq_iff_aux {u c : ℝ} (hc : 0 < c) : exp u = c ↔ u = Real.log c :=
  ⟨fun h => by rw [← h, Real.log_exp], fun h => by rw [h, Real.exp_log hc]⟩

private theorem exp_two_mul_aux (x : ℝ) : exp (2 * x) = exp x ^ 2 := by
  rw [show 2 * x = x + x by ring, Real.exp_add]; ring

/-! ## Section 6.3 -/

/-- Stitz-Zeager Exercises 6.3.1 - 6.3.5: `2^(4x) = 8` iff `x = 3/4`; `3^(x-1) = 27` iff `x = 4`;
`5^(2x-1) = 125` iff `x = 2`; `4^(2x) = 1/2` iff `x = -1/4`; `8^x = 1/128` iff `x = -7/3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.1, p. 468"]
theorem exer_6_3_1_to_5 :
    (∀ x : ℝ, (2 : ℝ) ^ (4 * x) = 8 ↔ x = 3 / 4) ∧ (∀ x : ℝ, (3 : ℝ) ^ (x - 1) = 27 ↔ x = 4) ∧
    (∀ x : ℝ, (5 : ℝ) ^ (2 * x - 1) = 125 ↔ x = 2) ∧
    (∀ x : ℝ, (4 : ℝ) ^ (2 * x) = 1 / 2 ↔ x = -1 / 4) ∧
    (∀ x : ℝ, (8 : ℝ) ^ x = 1 / 128 ↔ x = -7 / 3) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [pow_zpow_iff_aux (by norm_num) 3 8 (by norm_num)]; push_cast; constructor <;> intro h <;> linarith
  · rw [pow_zpow_iff_aux (by norm_num) 3 27 (by norm_num)]; push_cast; constructor <;> intro h <;> linarith
  · rw [pow_zpow_iff_aux (by norm_num) 3 125 (by norm_num)]; push_cast; constructor <;> intro h <;> linarith
  · rw [base_rw_aux (a := 2) (by norm_num) 2 (by norm_num), pow_zpow_iff_aux (by norm_num) (-1) (1 / 2)
      (by norm_num)]
    push_cast; constructor <;> intro h <;> linarith
  · rw [base_rw_aux (a := 2) (by norm_num) 3 (by norm_num), pow_zpow_iff_aux (by norm_num) (-7) (1 / 128)
      (by norm_num)]
    push_cast; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.6: `2^(x³-x) = 1` holds exactly for `x = -1, 0, 1`. -/
@[kb "stitzzeager2013" "Exercise 6.3.6, p. 468"]
theorem exer_6_3_6 (x : ℝ) : (2 : ℝ) ^ (x ^ 3 - x) = 1 ↔ x = -1 ∨ x = 0 ∨ x = 1 := by
  rw [pow_zpow_iff_aux (by norm_num) 0 1 (by norm_num)]
  push_cast
  constructor
  · intro h
    have : x * ((x - 1) * (x + 1)) = 0 := by linarith [h, show x * ((x - 1) * (x + 1)) = x ^ 3 - x by ring]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact Or.inr (Or.inl h0)
    · rcases mul_eq_zero.1 h0 with h1 | h1
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl (by linarith)
  · rintro (h | h | h) <;> subst h <;> norm_num

/-- Stitz-Zeager Exercises 6.3.7, 6.3.8: `3^(7x) = 81^(4-2x)` iff `x = 16/15`;
`9 · 3^(7x) = (1/9)^(2x)` iff `x = -2/11`. -/
@[kb "stitzzeager2013" "Exercise 6.3.7, p. 468"]
theorem exer_6_3_7_8 :
    (∀ x : ℝ, (3 : ℝ) ^ (7 * x) = 81 ^ (4 - 2 * x) ↔ x = 16 / 15) ∧
    (∀ x : ℝ, 9 * (3 : ℝ) ^ (7 * x) = (1 / 9) ^ (2 * x) ↔ x = -2 / 11) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [base_rw_aux (a := 3) (c := 81) (by norm_num) 4 (by norm_num), pow_inj_aux (by norm_num)]
    push_cast; constructor <;> intro h <;> linarith
  · have h9 : (9 : ℝ) * (3 : ℝ) ^ (7 * x) = (3 : ℝ) ^ (2 + 7 * x) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_two]; norm_num
    rw [h9, base_rw_aux (a := 3) (c := 1 / 9) (by norm_num) (-2) (by norm_num),
      pow_inj_aux (by norm_num)]
    push_cast; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercises 6.3.9 - 6.3.12: `3^(2x) = 5` iff `x = ln 5 / (2 ln 3)`; `5^(-x) = 2` iff
`x = -ln 2 / ln 5`; `5^x = -2` has no solution; `3^(x-1) = 29` iff `x = (ln 29 + ln 3) / ln 3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.9, p. 468"]
theorem exer_6_3_9_to_12 :
    (∀ x : ℝ, (3 : ℝ) ^ (2 * x) = 5 ↔ x = Real.log 5 / (2 * Real.log 3)) ∧
    (∀ x : ℝ, (5 : ℝ) ^ (-x) = 2 ↔ x = -Real.log 2 / Real.log 5) ∧
    (∀ x : ℝ, (5 : ℝ) ^ x ≠ -2) ∧
    (∀ x : ℝ, (3 : ℝ) ^ (x - 1) = 29 ↔ x = (Real.log 29 + Real.log 3) / Real.log 3) := by
  have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h5 : Real.log 5 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [rpow_eq_iff_aux (by norm_num) (by norm_num), Real.logb]
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; field_simp at h ⊢; linarith
  · rw [rpow_eq_iff_aux (by norm_num) (by norm_num), Real.logb]
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; field_simp at h ⊢; linarith
  · exact (neg_neg_of_pos (by norm_num : (0 : ℝ) < 2) |>.trans (Real.rpow_pos_of_pos (by norm_num) x)).ne'
  · rw [rpow_eq_iff_aux (by norm_num) (by norm_num), Real.logb]
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; field_simp at h ⊢; linarith

/-- Stitz-Zeager Exercises 6.3.15, 6.3.16, 6.3.17: `2000 e^(0.1t) = 4000` iff `t = 10 ln 2`;
`500 (1 - e^(2x)) = 250` iff `x = -(1/2) ln 2`; `70 + 90 e^(-0.1t) = 75` iff `t = 10 ln 18`. -/
@[kb "stitzzeager2013" "Exercise 6.3.15, p. 468"]
theorem exer_6_3_15_16_17 :
    (∀ t : ℝ, 2000 * exp (0.1 * t) = 4000 ↔ t = 10 * Real.log 2) ∧
    (∀ x : ℝ, 500 * (1 - exp (2 * x)) = 250 ↔ x = -(1 / 2) * Real.log 2) ∧
    (∀ t : ℝ, 70 + 90 * exp (-0.1 * t) = 75 ↔ t = 10 * Real.log 18) := by
  refine ⟨fun t => ?_, fun x => ?_, fun t => ?_⟩
  · rw [show 2000 * exp (0.1 * t) = 4000 ↔ exp (0.1 * t) = 2 by
      constructor <;> intro h <;> linarith, exp_eq_iff_aux (by norm_num)]
    constructor <;> intro h <;> linarith
  · rw [show 500 * (1 - exp (2 * x)) = 250 ↔ exp (2 * x) = 1 / 2 by
      constructor <;> intro h <;> linarith, exp_eq_iff_aux (by norm_num), one_div, Real.log_inv]
    constructor <;> intro h <;> linarith
  · rw [show 70 + 90 * exp (-0.1 * t) = 75 ↔ exp (-0.1 * t) = 1 / 18 by
      constructor <;> intro h <;> linarith, exp_eq_iff_aux (by norm_num), one_div, Real.log_inv]
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercises 6.3.19, 6.3.20: `100 e^x / (e^x + 2) = 50` iff `x = ln 2`;
`5000 / (1 + 2 e^(-3t)) = 2500` iff `t = (1/3) ln 2`. -/
@[kb "stitzzeager2013" "Exercise 6.3.19, p. 468"]
theorem exer_6_3_19_20 :
    (∀ x : ℝ, 100 * exp x / (exp x + 2) = 50 ↔ x = Real.log 2) ∧
    (∀ t : ℝ, 5000 / (1 + 2 * exp (-3 * t)) = 2500 ↔ t = 1 / 3 * Real.log 2) := by
  refine ⟨fun x => ?_, fun t => ?_⟩
  · have hp := Real.exp_pos x
    rw [div_eq_iff (by positivity)]
    rw [show 100 * exp x = 50 * (exp x + 2) ↔ exp x = 2 by constructor <;> intro h <;> linarith,
      exp_eq_iff_aux (by norm_num)]
  · have hp := Real.exp_pos (-3 * t)
    rw [div_eq_iff (by positivity)]
    rw [show 5000 = 2500 * (1 + 2 * exp (-3 * t)) ↔ exp (-3 * t) = 1 / 2 by
      constructor <;> intro h <;> linarith, exp_eq_iff_aux (by norm_num), one_div, Real.log_inv]
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercises 6.3.23, 6.3.24: `e^(2x) = 2 e^x` iff `x = ln 2`;
`7 e^(2x) = 28 e^(-6x)` iff `x = (1/4) ln 2`. -/
@[kb "stitzzeager2013" "Exercise 6.3.23, p. 468"]
theorem exer_6_3_23_24 :
    (∀ x : ℝ, exp (2 * x) = 2 * exp x ↔ x = Real.log 2) ∧
    (∀ x : ℝ, 7 * exp (2 * x) = 28 * exp (-6 * x) ↔ x = 1 / 4 * Real.log 2) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hp := Real.exp_pos x
    rw [exp_two_mul_aux, ← exp_eq_iff_aux (by norm_num : (0 : ℝ) < 2) (u := x)]
    constructor
    · intro h; nlinarith
    · intro h; rw [h]; ring
  · have e8 : exp (8 * x) = exp (2 * x) * exp (6 * x) := by rw [← Real.exp_add]; ring_nf
    have e6 : exp (-6 * x) * exp (6 * x) = 1 := by rw [← Real.exp_add]; simp
    have hp := Real.exp_pos (6 * x)
    have hq := Real.exp_pos (-6 * x)
    have key : 7 * exp (2 * x) = 28 * exp (-6 * x) ↔ exp (8 * x) = 4 := by
      constructor
      · intro h; rw [e8]; nlinarith
      · intro h; rw [e8] at h; nlinarith
    rw [key, exp_eq_iff_aux (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercises 6.3.28, 6.3.29: `e^(2x) - 3e^x - 10 = 0` iff `x = ln 5`;
`e^(2x) = e^x + 6` iff `x = ln 3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.28, p. 468"]
theorem exer_6_3_28_29 :
    (∀ x : ℝ, exp (2 * x) - 3 * exp x - 10 = 0 ↔ x = Real.log 5) ∧
    (∀ x : ℝ, exp (2 * x) = exp x + 6 ↔ x = Real.log 3) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hp := Real.exp_pos x
    rw [← exp_eq_iff_aux (by norm_num : (0 : ℝ) < 5) (u := x), exp_two_mul_aux]
    constructor
    · intro h; nlinarith
    · intro h; rw [h]; norm_num
  · have hp := Real.exp_pos x
    rw [← exp_eq_iff_aux (by norm_num : (0 : ℝ) < 3) (u := x), exp_two_mul_aux]
    constructor
    · intro h; nlinarith
    · intro h; rw [h]; norm_num

/-- Stitz-Zeager Exercise 6.3.30: `4^x + 2^x = 12` iff `x = ln 3 / ln 2`. -/
@[kb "stitzzeager2013" "Exercise 6.3.30, p. 468"]
theorem exer_6_3_30 (x : ℝ) : (4 : ℝ) ^ x + 2 ^ x = 12 ↔ x = Real.log 3 / Real.log 2 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hp : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have h4 : (4 : ℝ) ^ x = ((2 : ℝ) ^ x) ^ 2 := by
    rw [base_rw_aux (a := 2) (c := 4) (by norm_num) 2 (by norm_num), mul_comm]
    push_cast
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  rw [h4, ← Real.logb, ← rpow_eq_iff_aux (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 3) (u := x)]
  constructor
  · intro h; nlinarith
  · intro h; rw [h]; norm_num

/-- Stitz-Zeager Exercises 6.3.31, 6.3.32, 6.3.33: `e^x - 3e^(-x) = 2` iff `x = ln 3`;
`e^x + 15e^(-x) = 8` iff `x = ln 3` or `x = ln 5`; `3^x + 25 · 3^(-x) = 10` iff `x = ln 5 / ln 3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.31, p. 468"]
theorem exer_6_3_31_32_33 :
    (∀ x : ℝ, exp x - 3 * exp (-x) = 2 ↔ x = Real.log 3) ∧
    (∀ x : ℝ, exp x + 15 * exp (-x) = 8 ↔ x = Real.log 3 ∨ x = Real.log 5) ∧
    (∀ x : ℝ, (3 : ℝ) ^ x + 25 * (3 : ℝ) ^ (-x) = 10 ↔ x = Real.log 5 / Real.log 3) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have hp := Real.exp_pos x
    have e : exp x * exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [← exp_eq_iff_aux (by norm_num : (0 : ℝ) < 3) (u := x)]
    constructor
    · intro h; nlinarith
    · intro h; rw [h] at e ⊢; nlinarith
  · have hp := Real.exp_pos x
    have e : exp x * exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [← exp_eq_iff_aux (by norm_num : (0 : ℝ) < 3) (u := x),
      ← exp_eq_iff_aux (by norm_num : (0 : ℝ) < 5) (u := x)]
    constructor
    · intro h
      have : (exp x - 3) * (exp x - 5) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] at e ⊢ <;> nlinarith
  · have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hp : (0 : ℝ) < (3 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
    have e : (3 : ℝ) ^ x * (3 : ℝ) ^ (-x) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    rw [← Real.logb, ← rpow_eq_iff_aux (by norm_num : (1 : ℝ) < 3) (by norm_num : (0 : ℝ) < 5) (u := x)]
    constructor
    · intro h; nlinarith
    · intro h; rw [h] at e ⊢; nlinarith

/-- Stitz-Zeager Exercises 6.3.34, 6.3.36, 6.3.37, 6.3.39: solution sets of inequalities,
`e^x > 53` is `(ln 53, ∞)`; `2^(x³-x) < 1` is `(-∞, -1) ∪ (0, 1)`;
`25 (4/5)^x ≥ 10` is `(-∞, ln(2/5) / ln(4/5)]`; `70 + 90 e^(-0.1t) ≤ 75` is `[10 ln 18, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.34, p. 468"]
theorem exer_6_3_34_36_37_39 :
    {x : ℝ | 53 < exp x} = Ioi (Real.log 53) ∧
    {x : ℝ | (2 : ℝ) ^ (x ^ 3 - x) < 1} = Iio (-1) ∪ Ioo 0 1 ∧
    {x : ℝ | 10 ≤ 25 * ((4 : ℝ) / 5) ^ x} = Iic (Real.log (2 / 5) / Real.log (4 / 5)) ∧
    {t : ℝ | 70 + 90 * exp (-0.1 * t) ≤ 75} = Ici (10 * Real.log 18) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Ioi]
    exact (Real.log_lt_iff_lt_exp (by norm_num)).symm
  · ext x
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo]
    have e : (2 : ℝ) ^ (x ^ 3 - x) < 1 ↔ x ^ 3 - x < 0 := by
      rw [← Real.rpow_zero (2 : ℝ), Real.rpow_lt_rpow_left_iff (by norm_num)]
    rw [e]
    have key : x ^ 3 - x = x * ((x - 1) * (x + 1)) := by ring
    rw [key]
    constructor
    · intro h
      rcases lt_or_ge x (-1) with h1 | h1
      · exact Or.inl h1
      · right
        rcases lt_trichotomy x 0 with h2 | h2 | h2
        · exfalso
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ -x) (by linarith : (0 : ℝ) ≤ 1 - x))
            (by linarith : (0 : ℝ) ≤ x + 1)]
        · subst h2; norm_num at h
        · refine ⟨h2, ?_⟩
          by_contra hc
          push Not at hc
          nlinarith [mul_nonneg (mul_nonneg h2.le (by linarith : (0 : ℝ) ≤ x - 1))
            (by linarith : (0 : ℝ) ≤ x + 1)]
    · rintro (h | ⟨h1, h2⟩)
      · nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < -x) (by linarith : (0 : ℝ) < 1 - x))
          (by linarith : (0 : ℝ) < -(x + 1))]
      · nlinarith [mul_pos (mul_pos h1 (by linarith : (0 : ℝ) < 1 - x)) (by linarith : (0 : ℝ) < x + 1)]
  · ext x
    simp only [mem_ofPred_eq, mem_Iic]
    have hl : Real.log (4 / 5) < 0 := Real.log_neg (by norm_num) (by norm_num)
    have e : 10 ≤ 25 * ((4 : ℝ) / 5) ^ x ↔ 2 / 5 ≤ ((4 : ℝ) / 5) ^ x := by
      constructor <;> intro h <;> linarith
    rw [e, Real.rpow_def_of_pos (by norm_num), ← Real.log_le_iff_le_exp (by norm_num),
      le_div_iff_of_neg hl]
    constructor <;> intro h <;> linarith
  · ext x
    simp only [mem_ofPred_eq, mem_Ici]
    have e : 70 + 90 * exp (-0.1 * x) ≤ 75 ↔ exp (-0.1 * x) ≤ 1 / 18 := by
      constructor <;> intro h <;> linarith
    rw [e, ← Real.le_log_iff_exp_le (by norm_num), one_div, Real.log_inv]
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.47: the inverse of `f(x) = (e^x - e^(-x)) / 2` is
`f⁻¹(x) = ln (x + √(x²+1))`: the compositions are the identity on all of `ℝ`, both ways. -/
@[kb "stitzzeager2013" "Exercise 6.3.47, p. 468"]
theorem exer_6_3_47 :
    let f : ℝ → ℝ := fun x => (exp x - exp (-x)) / 2
    (∀ x : ℝ, Real.log (f x + Real.sqrt (f x ^ 2 + 1)) = x) ∧
      ∀ y : ℝ, f (Real.log (y + Real.sqrt (y ^ 2 + 1))) = y := by
  intro f
  refine ⟨fun x => ?_, fun y => ?_⟩
  · have e : exp x * exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have hs : Real.sqrt (f x ^ 2 + 1) = (exp x + exp (-x)) / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      simp only [f]
      nlinarith [e]
    rw [hs]
    have : f x + (exp x + exp (-x)) / 2 = exp x := by simp only [f]; ring
    rw [this, Real.log_exp]
  · have hs : 0 < Real.sqrt (y ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
    have hsq : Real.sqrt (y ^ 2 + 1) ^ 2 = y ^ 2 + 1 := Real.sq_sqrt (by positivity)
    have hpos : 0 < y + Real.sqrt (y ^ 2 + 1) := by
      nlinarith [sq_nonneg (y + Real.sqrt (y ^ 2 + 1)), abs_nonneg y, sq_abs y, le_abs_self y,
        neg_abs_le y]
    have hinv : (y + Real.sqrt (y ^ 2 + 1))⁻¹ = Real.sqrt (y ^ 2 + 1) - y := by
      rw [inv_eq_one_div, div_eq_iff hpos.ne']
      nlinarith [hsq]
    simp only [f]
    rw [Real.exp_log hpos, Real.exp_neg, Real.exp_log hpos, hinv]
    ring

end UndergradKB.Precalculus.Course
