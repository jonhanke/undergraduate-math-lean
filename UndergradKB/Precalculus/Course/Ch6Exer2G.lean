import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 6.4 -/

namespace UndergradKB.Precalculus.Course

open Set

private theorem x6w7g_logb_inj {b x y : ℝ} (hb : 1 < b) (hx : 0 < x) (hy : 0 < y)
    (h : Real.logb b x = Real.logb b y) : x = y :=
  Real.logb_injOn_pos hb (mem_Ioi.2 hx) (mem_Ioi.2 hy) h

private theorem x6w7g_log_inj {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : Real.log x = Real.log y) : x = y :=
  Real.log_injOn_pos (mem_Ioi.2 hx) (mem_Ioi.2 hy) h

/-- Stitz-Zeager Exercise 6.4.2: `log₂(x³) = log₂(x)` holds exactly for `x = 1` (in the domain `x > 0`). -/
@[kb "stitzzeager2013" "Exercise 6.4.2, p. 478"]
theorem exer_6_4_2 : {x : ℝ | 0 < x ^ 3 ∧ 0 < x ∧ Real.logb 2 (x ^ 3) = Real.logb 2 x} = {1} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have := x6w7g_logb_inj (by norm_num) h1 h2 h3
    have h : x * (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 6.4.3: `ln(8 - x²) = ln(2 - x)` holds exactly for `x = -2`. -/
@[kb "stitzzeager2013" "Exercise 6.4.3, p. 478"]
theorem exer_6_4_3 :
    {x : ℝ | 0 < 8 - x ^ 2 ∧ 0 < 2 - x ∧ Real.log (8 - x ^ 2) = Real.log (2 - x)} = {-2} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have := x6w7g_log_inj h1 h2 h3
    have h : (x - 3) * (x + 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 6.4.4: `log₅(18 - x²) = log₅(6 - x)` holds exactly for `x = -3` or `x = 4`. -/
@[kb "stitzzeager2013" "Exercise 6.4.4, p. 478"]
theorem exer_6_4_4 :
    {x : ℝ | 0 < 18 - x ^ 2 ∧ 0 < 6 - x ∧ Real.logb 5 (18 - x ^ 2) = Real.logb 5 (6 - x)} = {-3, 4} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have := x6w7g_logb_inj (by norm_num) h1 h2 h3
    have h : (x - 4) * (x + 3) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 6.4.6: `log_{1/2}(2x-1) = -3` holds exactly for `x = 9/2`. -/
@[kb "stitzzeager2013" "Exercise 6.4.6, p. 478"]
theorem exer_6_4_6 : {x : ℝ | 0 < 2 * x - 1 ∧ Real.logb (1 / 2) (2 * x - 1) = -3} = {9 / 2} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  have h8 : (1 / 2 : ℝ) ^ (-3 : ℝ) = 8 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  constructor
  · rintro ⟨h1, h2⟩
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1, h8] at h2
    linarith
  · rintro rfl
    refine ⟨by norm_num, ?_⟩
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num), h8]; norm_num

/-- Stitz-Zeager Exercise 6.4.7: `ln(x² - 99) = 0` holds exactly for `x = ±10`. -/
@[kb "stitzzeager2013" "Exercise 6.4.7, p. 478"]
theorem exer_6_4_7 : {x : ℝ | 0 < x ^ 2 - 99 ∧ Real.log (x ^ 2 - 99) = 0} = {10, -10} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases Real.log_eq_zero.1 h2 with h | h | h
    · linarith
    · have : (x - 10) * (x + 10) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 6.4.8: `log(x² - 3x) = 1` holds exactly for `x = -2` or `x = 5`. -/
@[kb "stitzzeager2013" "Exercise 6.4.8, p. 478"]
theorem exer_6_4_8 : {x : ℝ | 0 < x ^ 2 - 3 * x ∧ Real.logb 10 (x ^ 2 - 3 * x) = 1} = {-2, 5} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1, Real.rpow_one] at h2
    have : (x + 2) * (x - 5) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl)
    · refine ⟨by norm_num, ?_⟩
      rw [show ((-2 : ℝ) ^ 2 - 3 * (-2)) = 10 by norm_num]; exact Real.logb_self_eq_one (by norm_num)
    · refine ⟨by norm_num, ?_⟩
      rw [show ((5 : ℝ) ^ 2 - 3 * 5) = 10 by norm_num]; exact Real.logb_self_eq_one (by norm_num)

/-- Stitz-Zeager Exercise 6.4.11: `-log(x) = 5.4` holds exactly for `x = 10^(-5.4)`. -/
@[kb "stitzzeager2013" "Exercise 6.4.11, p. 478"]
theorem exer_6_4_11 : {x : ℝ | 0 < x ∧ -Real.logb 10 x = 5.4} = {(10 : ℝ) ^ (-5.4 : ℝ)} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have : Real.logb 10 x = -5.4 := by linarith
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1] at this
    exact this.symm
  · rintro rfl
    refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
    rw [Real.logb_rpow (by norm_num) (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.4.12: `10 log(x / 10^(-12)) = 150` holds exactly for `x = 10³`. -/
@[kb "stitzzeager2013" "Exercise 6.4.12, p. 478"]
theorem exer_6_4_12 :
    {x : ℝ | 0 < x / (10 : ℝ) ^ (-12 : ℤ) ∧ 10 * Real.logb 10 (x / (10 : ℝ) ^ (-12 : ℤ)) = 150} = {1000} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  have h12 : (10 : ℝ) ^ (-12 : ℤ) = 1 / 10 ^ 12 := by rw [zpow_neg]; norm_num
  rw [h12]
  constructor
  · rintro ⟨h1, h2⟩
    have : Real.logb 10 (x / (1 / 10 ^ 12)) = 15 := by linarith
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1] at this
    norm_num at this
    linarith
  · rintro rfl
    refine ⟨by norm_num, ?_⟩
    rw [show (1000 : ℝ) / (1 / 10 ^ 12) = (10 : ℝ) ^ (15 : ℝ) by norm_num,
      Real.logb_rpow (by norm_num) (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.4.13: `6 - 3 log₅(2x) = 0` holds exactly for `x = 25/2`. -/
@[kb "stitzzeager2013" "Exercise 6.4.13, p. 478"]
theorem exer_6_4_13 : {x : ℝ | 0 < 2 * x ∧ 6 - 3 * Real.logb 5 (2 * x) = 0} = {25 / 2} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have : Real.logb 5 (2 * x) = 2 := by linarith
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1] at this
    norm_num at this; linarith
  · rintro rfl
    refine ⟨by norm_num, ?_⟩
    rw [show (2 * (25 / 2 : ℝ)) = (5 : ℝ) ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
    norm_num

/-- Stitz-Zeager Exercise 6.4.14: `3 ln(x) - 2 = 1 - ln(x)` holds exactly for `x = e^(3/4)`. -/
@[kb "stitzzeager2013" "Exercise 6.4.14, p. 478"]
theorem exer_6_4_14 :
    {x : ℝ | 0 < x ∧ 3 * Real.log x - 2 = 1 - Real.log x} = {Real.exp (3 / 4)} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have : Real.log x = 3 / 4 := by linarith
    rw [← this, Real.exp_log h1]
  · rintro rfl
    refine ⟨Real.exp_pos _, ?_⟩
    rw [Real.log_exp]; ring

/-- Stitz-Zeager Exercise 6.4.16: `log₅(2x+1) + log₅(x+2) = 1` holds exactly for `x = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 6.4.16, p. 478"]
theorem exer_6_4_16 :
    {x : ℝ | 0 < 2 * x + 1 ∧ 0 < x + 2 ∧ Real.logb 5 (2 * x + 1) + Real.logb 5 (x + 2) = 1} = {1 / 2} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [← Real.logb_mul h1.ne' h2.ne', Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (mul_pos h1 h2),
      Real.rpow_one] at h3
    have : (2 * x - 1) * (x + 3) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  · rintro rfl
    refine ⟨by norm_num, by norm_num, ?_⟩
    rw [← Real.logb_mul (by norm_num) (by norm_num), show (2 * (1 / 2 : ℝ) + 1) * (1 / 2 + 2) = 5 by norm_num]
    exact Real.logb_self_eq_one (by norm_num)

/-- Stitz-Zeager Exercise 6.4.17: `log₁₆₉(3x+7) - log₁₆₉(5x-9) = 1/2` holds exactly for `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 6.4.17, p. 478"]
theorem exer_6_4_17 :
    {x : ℝ | 0 < 3 * x + 7 ∧ 0 < 5 * x - 9 ∧
      Real.logb 169 (3 * x + 7) - Real.logb 169 (5 * x - 9) = 1 / 2} = {2} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  have h13 : (169 : ℝ) ^ (1 / 2 : ℝ) = 13 := by
    rw [← Real.sqrt_eq_rpow, show (169 : ℝ) = 13 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [← Real.logb_div h1.ne' h2.ne', Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (div_pos h1 h2),
      h13] at h3
    rw [eq_div_iff h2.ne'] at h3
    linarith
  · rintro rfl
    refine ⟨by norm_num, by norm_num, ?_⟩
    rw [← Real.logb_div (by norm_num) (by norm_num), show (3 * 2 + 7 : ℝ) / (5 * 2 - 9) = 169 ^ (1 / 2 : ℝ) by
      rw [h13]; norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

/-- Stitz-Zeager Exercise 6.4.19: `2 log₇(x) = log₇(2) + log₇(x+12)` holds exactly for `x = 6`. -/
@[kb "stitzzeager2013" "Exercise 6.4.19, p. 478"]
theorem exer_6_4_19 :
    {x : ℝ | 0 < x ∧ 0 < x + 12 ∧ 2 * Real.logb 7 x = Real.logb 7 2 + Real.logb 7 (x + 12)} = {6} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e : Real.logb 7 (x ^ 2) = Real.logb 7 (2 * (x + 12)) := by
      rw [Real.logb_pow, Real.logb_mul (by norm_num) h2.ne']; push_cast; linarith
    have := x6w7g_logb_inj (by norm_num) (by positivity) (by positivity) e
    have h : (x - 6) * (x + 4) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  · rintro rfl
    refine ⟨by norm_num, by norm_num, ?_⟩
    rw [← Real.logb_mul (by norm_num) (by norm_num), show (2 * (6 + 12) : ℝ) = 6 ^ 2 by norm_num, Real.logb_pow]
    push_cast; ring

/-- Stitz-Zeager Exercise 6.4.20: `log(x) - log(2) = log(x+8) - log(x+2)` holds exactly for `x = 4`. -/
@[kb "stitzzeager2013" "Exercise 6.4.20, p. 478"]
theorem exer_6_4_20 :
    {x : ℝ | 0 < x ∧ 0 < x + 8 ∧ 0 < x + 2 ∧
      Real.logb 10 x - Real.logb 10 2 = Real.logb 10 (x + 8) - Real.logb 10 (x + 2)} = {4} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [← Real.logb_div h1.ne' (by norm_num), ← Real.logb_div h2.ne' h3.ne'] at h4
    have := x6w7g_logb_inj (by norm_num) (by positivity) (by positivity) h4
    rw [div_eq_div_iff (by norm_num) h3.ne'] at this
    have h : (x - 4) * (x + 4) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith
  · rintro rfl
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    rw [← Real.logb_div (by norm_num) (by norm_num), ← Real.logb_div (by norm_num) (by norm_num)]
    norm_num

/-- Stitz-Zeager Exercise 6.4.22: `ln(ln(x)) = 3` holds exactly for `x = e^(e³)`. -/
@[kb "stitzzeager2013" "Exercise 6.4.22, p. 478"]
theorem exer_6_4_22 :
    {x : ℝ | 0 < x ∧ 0 < Real.log x ∧ Real.log (Real.log x) = 3} = {Real.exp (Real.exp 3)} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have : Real.log x = Real.exp 3 := by rw [← h3, Real.exp_log h2]
    rw [← this, Real.exp_log h1]
  · rintro rfl
    rw [Real.log_exp, Real.log_exp]
    exact ⟨Real.exp_pos _, Real.exp_pos _, rfl⟩

/-- Stitz-Zeager Exercise 6.4.23: `(log x)² = 2 log x + 15` holds exactly for `x = 10^(-3)` or `x = 10⁵`. -/
@[kb "stitzzeager2013" "Exercise 6.4.23, p. 478"]
theorem exer_6_4_23 :
    {x : ℝ | 0 < x ∧ (Real.logb 10 x) ^ 2 = 2 * Real.logb 10 x + 15} = {(10 : ℝ) ^ (-3 : ℝ), (10 : ℝ) ^ (5 : ℝ)} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have h : (Real.logb 10 x - 5) * (Real.logb 10 x + 3) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · right
      have : Real.logb 10 x = 5 := by linarith
      rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1] at this
      exact this.symm
    · left
      have : Real.logb 10 x = -3 := by linarith
      rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1] at this
      exact this.symm
  · rintro (rfl | rfl)
    · refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
      rw [Real.logb_rpow (by norm_num) (by norm_num)]; norm_num
    · refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
      rw [Real.logb_rpow (by norm_num) (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.4.24: `ln(x²) = (ln x)²` holds exactly for `x = 1` or `x = e²` (with `x > 0`). -/
@[kb "stitzzeager2013" "Exercise 6.4.24, p. 478"]
theorem exer_6_4_24 :
    {x : ℝ | 0 < x ∧ Real.log (x ^ 2) = (Real.log x) ^ 2} = {1, Real.exp 2} := by
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Real.log_pow] at h2
    push_cast at h2
    have h : Real.log x * (Real.log x - 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 h with h | h
    · left; rw [← Real.exp_log h1, h, Real.exp_zero]
    · right; rw [← Real.exp_log h1, show Real.log x = 2 by linarith]
  · rintro (rfl | rfl)
    · simp
    · refine ⟨Real.exp_pos _, ?_⟩
      rw [Real.log_pow, Real.log_exp]; push_cast; ring

/-- Stitz-Zeager Exercise 6.4.26: `x ln(x) - x > 0` has solution set `(e, ∞)` (in the domain `x > 0`). -/
@[kb "stitzzeager2013" "Exercise 6.4.26, p. 478"]
theorem exer_6_4_26 : {x : ℝ | 0 < x ∧ 0 < x * Real.log x - x} = Ioi (Real.exp 1) := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioi]
  constructor
  · rintro ⟨h1, h2⟩
    have : 1 < Real.log x := by
      by_contra hc; push Not at hc; nlinarith
    exact (Real.lt_log_iff_exp_lt h1).1 this
  · intro h
    have h1 : 0 < x := lt_trans (Real.exp_pos 1) h
    have : 1 < Real.log x := (Real.lt_log_iff_exp_lt h1).2 h
    exact ⟨h1, by nlinarith⟩

/-- Stitz-Zeager Exercise 6.4.29: `2.3 < -log(x) < 5.4` has solution set `(10^(-5.4), 10^(-2.3))`. -/
@[kb "stitzzeager2013" "Exercise 6.4.29, p. 478"]
theorem exer_6_4_29 :
    {x : ℝ | 0 < x ∧ 2.3 < -Real.logb 10 x ∧ -Real.logb 10 x < 5.4} =
      Ioo ((10 : ℝ) ^ (-5.4 : ℝ)) ((10 : ℝ) ^ (-2.3 : ℝ)) := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(Real.lt_logb_iff_rpow_lt (by norm_num) h1).1 (by linarith),
      (Real.logb_lt_iff_lt_rpow (by norm_num) h1).1 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    have hx : 0 < x := lt_trans (Real.rpow_pos_of_pos (by norm_num) _) h1
    exact ⟨hx, by linarith [(Real.logb_lt_iff_lt_rpow (by norm_num) hx).2 h2],
      by linarith [(Real.lt_logb_iff_rpow_lt (by norm_num) hx).2 h1]⟩

/-- Stitz-Zeager Exercise 6.4.30: `ln(x²) ≤ (ln x)²` has solution set `(0, 1] ∪ [e², ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.4.30, p. 478"]
theorem exer_6_4_30 :
    {x : ℝ | 0 < x ∧ Real.log (x ^ 2) ≤ (Real.log x) ^ 2} = Ioc 0 1 ∪ Ici (Real.exp 2) := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ioc, mem_Ici]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Real.log_pow] at h2
    push_cast at h2
    have h : 0 ≤ Real.log x * (Real.log x - 2) := by nlinarith
    rcases le_or_gt (Real.log x) 0 with hl | hl
    · left; exact ⟨h1, (Real.log_nonpos_iff h1.le).1 hl⟩
    · right
      have : 2 ≤ Real.log x := by
        by_contra hc; push Not at hc; nlinarith
      exact (Real.le_log_iff_exp_le h1).1 this
  · rintro (⟨h1, h2⟩ | h)
    · refine ⟨h1, ?_⟩
      have := (Real.log_nonpos_iff h1.le).2 h2
      rw [Real.log_pow]; push_cast; nlinarith
    · have h1 : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) h
      refine ⟨h1, ?_⟩
      have : 2 ≤ Real.log x := (Real.le_log_iff_exp_le h1).2 h
      rw [Real.log_pow]; push_cast; nlinarith

/-- Stitz-Zeager Exercise 6.4.33: `ln(x²+1) ≥ 5` has solution set `(-∞, -√(e⁵-1)] ∪ [√(e⁵-1), ∞)`, where
`12.14 < √(e⁵-1) < 12.15`. -/
@[kb "stitzzeager2013" "Exercise 6.4.33, p. 478"]
theorem exer_6_4_33 :
    {x : ℝ | 5 ≤ Real.log (x ^ 2 + 1)} =
      Iic (-Real.sqrt (Real.exp 5 - 1)) ∪ Ici (Real.sqrt (Real.exp 5 - 1)) ∧
    12.14 < Real.sqrt (Real.exp 5 - 1) ∧ Real.sqrt (Real.exp 5 - 1) < 12.15 := by
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have hlo := Real.exp_one_gt_d9
  have hhi := Real.exp_one_lt_d9
  have hpos : 0 < Real.exp 5 - 1 := by
    have : Real.exp 5 > 1 := by simpa using Real.exp_lt_exp.2 (by norm_num : (0 : ℝ) < 5)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici]
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hs := Real.sq_sqrt hpos.le
    constructor
    · intro h
      by_contra hc; push Not at hc
      have : x ^ 2 < Real.sqrt (Real.exp 5 - 1) ^ 2 := by
        have := abs_lt.2 ⟨by linarith [hc.1], hc.2⟩
        nlinarith [abs_nonneg x, sq_abs x]
      nlinarith
    · rintro (h | h)
      · nlinarith [Real.sqrt_nonneg (Real.exp 5 - 1)]
      · nlinarith [Real.sqrt_nonneg (Real.exp 5 - 1)]
  · rw [Real.lt_sqrt (by norm_num), h5]
    have : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ hlo (by norm_num) (by norm_num)
    norm_num at this ⊢; linarith
  · rw [Real.sqrt_lt' (by norm_num), h5]
    have : Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 := pow_lt_pow_left₀ hhi (by positivity) (by norm_num)
    norm_num at this ⊢; linarith

/-- Stitz-Zeager Exercise 6.4.35: `ln(2x+1) < 3` has solution set `-1/2 < x < (e³-1)/2`. -/
@[kb "stitzzeager2013" "Exercise 6.4.35, p. 479"]
theorem exer_6_4_35 :
    {x : ℝ | 0 < 2 * x + 1 ∧ Real.log (2 * x + 1) < 3} = Ioo (-1 / 2) ((Real.exp 3 - 1) / 2) := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    have := (Real.log_lt_iff_lt_exp h1).1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have hp : 0 < 2 * x + 1 := by linarith
    exact ⟨hp, (Real.log_lt_iff_lt_exp hp).2 (by linarith)⟩

/-- Stitz-Zeager Exercise 6.4.37: for `f(x) = log x/(1 - log x)` (domain `x > 0`, `x ≠ 10`) the function
`f⁻¹(x) = 10^(x/(x+1))` (domain `x ≠ -1`) is a two-sided inverse; the range of `f` is `{y | y ≠ -1}`; and
`f = g ∘ log` with `g(x) = x/(1-x)`, `g⁻¹(y) = y/(1+y)`, `f⁻¹ = 10^(·) ∘ g⁻¹`. -/
@[kb "stitzzeager2013" "Exercise 6.4.37, p. 479"]
theorem exer_6_4_37 (f g : ℝ → ℝ) (hf : f = fun x => Real.logb 10 x / (1 - Real.logb 10 x))
    (hg : g = fun x => x / (1 - x)) :
    (∀ x : ℝ, 0 < x → x ≠ 10 → (10 : ℝ) ^ (f x / (f x + 1)) = x) ∧
    (∀ y : ℝ, y ≠ -1 → f ((10 : ℝ) ^ (y / (y + 1))) = y) ∧
    f '' {x : ℝ | 0 < x ∧ x ≠ 10} = {y | y ≠ -1} ∧
    (∀ x, f x = g (Real.logb 10 x)) ∧ (∀ y : ℝ, y ≠ -1 → g (y / (1 + y)) = y) := by
  subst hf hg
  have h1 : ∀ x : ℝ, 0 < x → x ≠ 10 → 1 - Real.logb 10 x ≠ 0 := by
    intro x hx hx10 h
    apply hx10
    have : Real.logb 10 x = 1 := by linarith
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hx] at this
    simpa using this.symm
  have hA : ∀ x : ℝ, 0 < x → x ≠ 10 →
      (fun x : ℝ => Real.logb 10 x / (1 - Real.logb 10 x)) x /
        ((fun x : ℝ => Real.logb 10 x / (1 - Real.logb 10 x)) x + 1) = Real.logb 10 x := by
    intro x hx hx10
    have h := h1 x hx hx10
    simp only
    have : Real.logb 10 x / (1 - Real.logb 10 x) + 1 = 1 / (1 - Real.logb 10 x) := by
      field_simp; ring
    rw [this]; field_simp
  have hB : ∀ y : ℝ, y ≠ -1 →
      (fun x : ℝ => Real.logb 10 x / (1 - Real.logb 10 x)) ((10 : ℝ) ^ (y / (y + 1))) = y := by
    intro y hy
    have h : y + 1 ≠ 0 := fun h => hy (by linarith)
    simp only
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
    have : 1 - y / (y + 1) = 1 / (y + 1) := by field_simp; ring
    rw [this]; field_simp
  refine ⟨fun x hx hx10 => ?_, hB, ?_, fun x => rfl, fun y hy => ?_⟩
  · rw [hA x hx hx10, Real.rpow_logb (by norm_num) (by norm_num) hx]
  · ext y
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨hx, hx10⟩, rfl⟩ h
      have h' := h1 x hx hx10
      field_simp at h
      linarith
    · intro hy
      refine ⟨(10 : ℝ) ^ (y / (y + 1)), ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩, hB y hy⟩
      intro h10
      have h : y + 1 ≠ 0 := fun h => hy (by linarith)
      have := congrArg (Real.logb 10) h10
      rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
      rw [Real.logb_self_eq_one (by norm_num), div_eq_one_iff_eq h] at this
      linarith
  · have h : 1 + y ≠ 0 := fun h => hy (by linarith)
    simp only
    have : 1 - y / (1 + y) = 1 / (1 + y) := by field_simp; ring
    rw [this]; field_simp

end UndergradKB.Precalculus.Course
