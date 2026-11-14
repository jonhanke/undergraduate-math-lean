import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 6.2 (approximations) and 6.3 (equations) -/

namespace UndergradKB.Precalculus.Course

set_option exponentiation.threshold 2000

/-- `lo < log_b y` from `b^p < y^q`, where `lo = p/q` and `b > 1`. -/
private theorem x6w7d_lt_logb {b y lo : ℝ} (hb : 1 < b) (hy : 0 < y) (p q : ℕ) (hq : 0 < q)
    (hlo : lo = p / q) (h : b ^ p < y ^ q) : lo < Real.logb b y := by
  rw [Real.lt_logb_iff_rpow_lt hb hy, hlo]
  by_contra hc
  push Not at hc
  have h1 : y ^ q ≤ (b ^ ((p : ℝ) / q)) ^ q := pow_le_pow_left₀ hy.le hc q
  have e : (b ^ ((p : ℝ) / q)) ^ q = b ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), div_mul_cancel₀ _ (by positivity)]
    exact Real.rpow_natCast b p
  linarith

/-- `log_b y < hi` from `y^q < b^p`, where `hi = p/q` and `b > 1`. -/
private theorem x6w7d_logb_lt {b y hi : ℝ} (hb : 1 < b) (hy : 0 < y) (p q : ℕ) (hq : 0 < q)
    (hhi : hi = p / q) (h : y ^ q < b ^ p) : Real.logb b y < hi := by
  rw [Real.logb_lt_iff_lt_rpow hb hy, hhi]
  by_contra hc
  push Not at hc
  have h1 : (b ^ ((p : ℝ) / q)) ^ q ≤ y ^ q := pow_le_pow_left₀ (by positivity) hc q
  have e : (b ^ ((p : ℝ) / q)) ^ q = b ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), div_mul_cancel₀ _ (by positivity)]
    exact Real.rpow_natCast b p
  linarith

private theorem x6w7d_logb_inv_base (b y : ℝ) : Real.logb b⁻¹ y = -Real.logb b y := by
  simp only [Real.logb, Real.log_inv, div_neg]

/-- Stitz-Zeager Exercise 6.2.35: `log₅(80) ≈ 2.72271`, so it lies in `(2.72, 2.73)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.35, p. 458"]
theorem exer_6_2_35 : 2.72 < Real.logb 5 80 ∧ Real.logb 5 80 < 2.73 :=
  ⟨x6w7d_lt_logb (by norm_num) (by norm_num) 68 25 (by norm_num) (by norm_num) (by norm_num),
    x6w7d_logb_lt (by norm_num) (by norm_num) 273 100 (by norm_num) (by norm_num) (by norm_num)⟩

/-- Stitz-Zeager Exercise 6.2.36: `log₆(72) ≈ 2.38685`, so it lies in `(2.38, 2.39)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.36, p. 458"]
theorem exer_6_2_36 : 2.38 < Real.logb 6 72 ∧ Real.logb 6 72 < 2.39 :=
  ⟨x6w7d_lt_logb (by norm_num) (by norm_num) 119 50 (by norm_num) (by norm_num) (by norm_num),
    x6w7d_logb_lt (by norm_num) (by norm_num) 239 100 (by norm_num) (by norm_num) (by norm_num)⟩

/-- Stitz-Zeager Exercise 6.2.37: `log₄(1/10) ≈ -1.66096`, so it lies in `(-1.67, -1.66)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.37, p. 458"]
theorem exer_6_2_37 : -1.67 < Real.logb 4 (1 / 10) ∧ Real.logb 4 (1 / 10) < -1.66 := by
  rw [one_div, Real.logb_inv]
  have h1 : 1.66 < Real.logb 4 10 :=
    x6w7d_lt_logb (by norm_num) (by norm_num) 83 50 (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 4 10 < 1.67 :=
    x6w7d_logb_lt (by norm_num) (by norm_num) 167 100 (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith

/-- Stitz-Zeager Exercise 6.2.38: `log_{3/5}(1000) ≈ -13.52273`, so it lies in `(-13.53, -13.52)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.38, p. 458"]
theorem exer_6_2_38 : -13.53 < Real.logb (3 / 5) 1000 ∧ Real.logb (3 / 5) 1000 < -13.52 := by
  rw [show (3 / 5 : ℝ) = (5 / 3)⁻¹ by norm_num, x6w7d_logb_inv_base]
  have h1 : 13.52 < Real.logb (5 / 3) 1000 :=
    x6w7d_lt_logb (by norm_num) (by norm_num) 338 25 (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb (5 / 3) 1000 < 13.53 :=
    x6w7d_logb_lt (by norm_num) (by norm_num) 1353 100 (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith

/-- Stitz-Zeager Exercise 6.2.39: `log_{2/3}(50) ≈ -9.64824`, so it lies in `(-9.65, -9.64)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.39, p. 458"]
theorem exer_6_2_39 : -9.65 < Real.logb (2 / 3) 50 ∧ Real.logb (2 / 3) 50 < -9.64 := by
  rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, x6w7d_logb_inv_base]
  have h1 : 9.64 < Real.logb (3 / 2) 50 :=
    x6w7d_lt_logb (by norm_num) (by norm_num) 241 25 (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb (3 / 2) 50 < 9.65 :=
    x6w7d_logb_lt (by norm_num) (by norm_num) 193 20 (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith

end UndergradKB.Precalculus.Course
