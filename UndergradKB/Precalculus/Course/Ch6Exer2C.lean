import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 6.2 -/

namespace UndergradKB.Precalculus.Course

private theorem x6w7c_lg {b c a : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (hc : 0 < c) (h : b ^ a = c) :
    Real.logb b c = a := (Real.logb_eq_iff_rpow_eq hb hb1 hc).2 h

/-! ## Section 6.2: expanding logarithms -/

/-- Stitz-Zeager Exercise 6.2.2: `log₂(128/(x²+4)) = 7 - log₂(x²+4)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.2, p. 457"]
theorem exer_6_2_2 (x : ℝ) : Real.logb 2 (128 / (x ^ 2 + 4)) = 7 - Real.logb 2 (x ^ 2 + 4) := by
  have hpos : 0 < x ^ 2 + 4 := by positivity
  have h : Real.logb 2 128 = 7 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_div (by norm_num) hpos.ne', h]

/-- Stitz-Zeager Exercise 6.2.3: `log₅((z/25)³) = 3 log₅(z) - 6` for `z > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.2.3, p. 457"]
theorem exer_6_2_3 (z : ℝ) (hz : 0 < z) : Real.logb 5 ((z / 25) ^ 3) = 3 * Real.logb 5 z - 6 := by
  have h : Real.logb 5 25 = 2 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_div hz.ne' (by norm_num), h]; push_cast; ring

/-- Stitz-Zeager Exercise 6.2.5: `ln(√z/(xy)) = (1/2) ln(z) - ln(x) - ln(y)` for positive `x, y, z`. -/
@[kb "stitzzeager2013" "Exercise 6.2.5, p. 457"]
theorem exer_6_2_5 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.log (Real.sqrt z / (x * y)) = 1 / 2 * Real.log z - Real.log x - Real.log y := by
  rw [Real.log_div (Real.sqrt_pos.2 hz).ne' (mul_pos hx hy).ne', Real.log_sqrt hz.le,
    Real.log_mul hx.ne' hy.ne']; ring

/-- Stitz-Zeager Exercise 6.2.7: `log_{√2}(4x³) = 3 log_{√2}(x) + 4` for `x > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.2.7, p. 457"]
theorem exer_6_2_7 (x : ℝ) (hx : 0 < x) :
    Real.logb (Real.sqrt 2) (4 * x ^ 3) = 3 * Real.logb (Real.sqrt 2) x + 4 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h : Real.logb (Real.sqrt 2) 4 = 4 := by
    refine x6w7c_lg (by linarith) (by linarith) (by norm_num) ?_
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 4 := by rw [h2]; norm_num
  rw [Real.logb_mul (by norm_num) (pow_pos hx 3).ne', h, Real.logb_pow]; push_cast; ring

/-- Stitz-Zeager Exercise 6.2.9: `log(1000 x³ y⁵) = 3 + 3 log(x) + 5 log(y)` for `x, y > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.2.9, p. 457"]
theorem exer_6_2_9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb 10 (1000 * x ^ 3 * y ^ 5) = 3 + 3 * Real.logb 10 x + 5 * Real.logb 10 y := by
  have h : Real.logb 10 1000 = 3 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_mul (by positivity) (pow_pos hy 5).ne', Real.logb_mul (by norm_num) (pow_pos hx 3).ne', h,
    Real.logb_pow, Real.logb_pow]; push_cast; ring

/-- Stitz-Zeager Exercise 6.2.10: `log₃(x²/(81 y⁴)) = 2 log₃(x) - 4 - 4 log₃(y)` for `x, y > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.2.10, p. 457"]
theorem exer_6_2_10 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb 3 (x ^ 2 / (81 * y ^ 4)) = 2 * Real.logb 3 x - 4 - 4 * Real.logb 3 y := by
  have h : Real.logb 3 81 = 4 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_div (pow_pos hx 2).ne' (by positivity), Real.logb_mul (by norm_num) (pow_pos hy 4).ne', h,
    Real.logb_pow, Real.logb_pow]; push_cast; ring

/-- Stitz-Zeager Exercise 6.2.11: `ln (xy/(ez))^(1/4) = (1/4) ln x + (1/4) ln y - 1/4 - (1/4) ln z`. -/
@[kb "stitzzeager2013" "Exercise 6.2.11, p. 457"]
theorem exer_6_2_11 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.log ((x * y / (Real.exp 1 * z)) ^ (1 / 4 : ℝ)) =
      1 / 4 * Real.log x + 1 / 4 * Real.log y - 1 / 4 - 1 / 4 * Real.log z := by
  have hez : 0 < Real.exp 1 * z := by positivity
  rw [Real.log_rpow (by positivity), Real.log_div (mul_pos hx hy).ne' hez.ne', Real.log_mul hx.ne' hy.ne',
    Real.log_mul (Real.exp_pos 1).ne' hz.ne', Real.log_exp]; ring

/-- Stitz-Zeager Exercise 6.2.12: `log₆((216/(x³y))⁴) = 12 - 12 log₆(x) - 4 log₆(y)` for `x, y > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.2.12, p. 457"]
theorem exer_6_2_12 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb 6 ((216 / (x ^ 3 * y)) ^ 4) = 12 - 12 * Real.logb 6 x - 4 * Real.logb 6 y := by
  have h : Real.logb 6 216 = 3 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_div (by norm_num) (by positivity), Real.logb_mul (pow_pos hx 3).ne' hy.ne', h,
    Real.logb_pow]; push_cast; ring

/-- Stitz-Zeager Exercise 6.2.13: `log(100 x √y / ∛10) = 5/3 + log(x) + (1/2) log(y)` for `x, y > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.2.13, p. 457"]
theorem exer_6_2_13 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb 10 (100 * x * Real.sqrt y / (10 : ℝ) ^ (1 / 3 : ℝ)) =
      5 / 3 + Real.logb 10 x + 1 / 2 * Real.logb 10 y := by
  have h : Real.logb 10 100 = 2 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 : Real.logb 10 ((10 : ℝ) ^ (1 / 3 : ℝ)) = 1 / 3 := Real.logb_rpow (by norm_num) (by norm_num)
  have hsy : Real.logb 10 (Real.sqrt y) = 1 / 2 * Real.logb 10 y := by
    rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hy]
  have hsp : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hp3 : 0 < (10 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  rw [Real.logb_div (by positivity) hp3.ne', Real.logb_mul (by positivity) hsp.ne',
    Real.logb_mul (by norm_num) hx.ne', h, h3, hsy]; ring

/-- Stitz-Zeager Exercise 6.2.15: `ln(∛x / (10 √(yz))) = (1/3) ln x - ln 10 - (1/2) ln y - (1/2) ln z`
for positive `x, y, z`. -/
@[kb "stitzzeager2013" "Exercise 6.2.15, p. 457"]
theorem exer_6_2_15 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.log (x ^ (1 / 3 : ℝ) / (10 * Real.sqrt (y * z))) =
      1 / 3 * Real.log x - Real.log 10 - 1 / 2 * Real.log y - 1 / 2 * Real.log z := by
  have hyz : 0 < y * z := mul_pos hy hz
  have hs : 0 < Real.sqrt (y * z) := Real.sqrt_pos.2 hyz
  rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hx, Real.log_mul (by norm_num) hs.ne',
    Real.log_sqrt hyz.le, Real.log_mul hy.ne' hz.ne']; ring

/-! ## Section 6.2: condensing logarithms -/

/-- Stitz-Zeager Exercise 6.2.17: `log₂(x) + log₂(y) - log₂(z) = log₂(xy/z)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.17, p. 457"]
theorem exer_6_2_17 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.logb 2 x + Real.logb 2 y - Real.logb 2 z = Real.logb 2 (x * y / z) := by
  rw [Real.logb_div (mul_pos hx hy).ne' hz.ne', Real.logb_mul hx.ne' hy.ne']

/-- Stitz-Zeager Exercise 6.2.19: `(1/2) log₃(x) - 2 log₃(y) - log₃(z) = log₃(√x/(y²z))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.19, p. 457"]
theorem exer_6_2_19 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / 2 * Real.logb 3 x - 2 * Real.logb 3 y - Real.logb 3 z =
      Real.logb 3 (Real.sqrt x / (y ^ 2 * z)) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  rw [Real.logb_div hsx.ne' (by positivity), Real.logb_mul (pow_pos hy 2).ne' hz.ne', Real.logb_pow,
    Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hx]; push_cast; ring

/-- Stitz-Zeager Exercise 6.2.20: `2 ln x - 3 ln y - 4 ln z = ln(x²/(y³z⁴))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.20, p. 457"]
theorem exer_6_2_20 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    2 * Real.log x - 3 * Real.log y - 4 * Real.log z = Real.log (x ^ 2 / (y ^ 3 * z ^ 4)) := by
  rw [Real.log_div (pow_pos hx 2).ne' (by positivity), Real.log_mul (pow_pos hy 3).ne' (pow_pos hz 4).ne',
    Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring

/-- Stitz-Zeager Exercise 6.2.21: `log x - (1/3) log z + (1/2) log y = log(x √y / ∛z)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.21, p. 457"]
theorem exer_6_2_21 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.logb 10 x - 1 / 3 * Real.logb 10 z + 1 / 2 * Real.logb 10 y =
      Real.logb 10 (x * Real.sqrt y / z ^ (1 / 3 : ℝ)) := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hz3 : 0 < z ^ (1 / 3 : ℝ) := by positivity
  rw [Real.logb_div (by positivity) hz3.ne', Real.logb_mul hx.ne' hsy.ne', Real.sqrt_eq_rpow,
    Real.logb_rpow_eq_mul_logb_of_pos hy, Real.logb_rpow_eq_mul_logb_of_pos hz]; ring

/-- Stitz-Zeager Exercise 6.2.22: `-(1/3) ln x - (1/3) ln y + (1/3) ln z = ln((z/(xy))^(1/3))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.22, p. 457"]
theorem exer_6_2_22 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    -(1 / 3) * Real.log x - 1 / 3 * Real.log y + 1 / 3 * Real.log z =
      Real.log ((z / (x * y)) ^ (1 / 3 : ℝ)) := by
  rw [Real.log_rpow (by positivity), Real.log_div hz.ne' (mul_pos hx hy).ne', Real.log_mul hx.ne' hy.ne']
  ring

/-- Stitz-Zeager Exercise 6.2.23: `log₅(x) - 3 = log₅(x/125)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.23, p. 457"]
theorem exer_6_2_23 (x : ℝ) (hx : 0 < x) : Real.logb 5 x - 3 = Real.logb 5 (x / 125) := by
  have h : Real.logb 5 125 = 3 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_div hx.ne' (by norm_num), h]

/-- Stitz-Zeager Exercise 6.2.24: `3 - log(x) = log(1000/x)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.24, p. 457"]
theorem exer_6_2_24 (x : ℝ) (hx : 0 < x) : 3 - Real.logb 10 x = Real.logb 10 (1000 / x) := by
  have h : Real.logb 10 1000 = 3 := x6w7c_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_div (by norm_num) hx.ne', h]

/-- Stitz-Zeager Exercise 6.2.26: `ln(x) + 1/2 = ln(x √e)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.26, p. 457"]
theorem exer_6_2_26 (x : ℝ) (hx : 0 < x) :
    Real.log x + 1 / 2 = Real.log (x * Real.sqrt (Real.exp 1)) := by
  rw [Real.log_mul hx.ne' (Real.sqrt_pos.2 (Real.exp_pos 1)).ne', Real.log_sqrt (Real.exp_pos 1).le,
    Real.log_exp]

/-- Stitz-Zeager Exercise 6.2.27: `log₂(x) + log₄(x) = log₂(x^(3/2))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.27, p. 457"]
theorem exer_6_2_27 (x : ℝ) (hx : 0 < x) :
    Real.logb 2 x + Real.logb 4 x = Real.logb 2 (x ^ (3 / 2 : ℝ)) := by
  rw [Real.logb_rpow_eq_mul_logb_of_pos hx]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp only [Real.logb, h4]
  field_simp
  ring

/-- Stitz-Zeager Exercise 6.2.29: `log₂(x) + log_{1/2}(x-1) = log₂(x/(x-1))` for `x > 1`. -/
@[kb "stitzzeager2013" "Exercise 6.2.29, p. 457"]
theorem exer_6_2_29 (x : ℝ) (hx : 1 < x) :
    Real.logb 2 x + Real.logb (1 / 2) (x - 1) = Real.logb 2 (x / (x - 1)) := by
  have h1 : x - 1 ≠ 0 := by linarith
  rw [Real.logb_div (by linarith) h1]
  simp only [Real.logb, one_div, Real.log_inv, div_neg]
  ring

/-! ## Section 6.2: change of base -/

/-- Stitz-Zeager Exercise 6.2.31: `log₃(x+2) = log(x+2)/log(3)` (common logarithms). -/
@[kb "stitzzeager2013" "Exercise 6.2.31, p. 458"]
theorem exer_6_2_31 (x : ℝ) : Real.logb 3 (x + 2) = Real.logb 10 (x + 2) / Real.logb 10 3 := by
  have h10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp only [Real.logb]
  field_simp

/-- Stitz-Zeager Exercise 6.2.32: `(2/3)^x = e^(x ln(2/3))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.32, p. 458"]
theorem exer_6_2_32 (x : ℝ) : (2 / 3 : ℝ) ^ x = Real.exp (x * Real.log (2 / 3)) := by
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]

/-- Stitz-Zeager Exercise 6.2.33: `log(x²+1) = ln(x²+1)/ln(10)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.33, p. 458"]
theorem exer_6_2_33 (x : ℝ) : Real.logb 10 (x ^ 2 + 1) = Real.log (x ^ 2 + 1) / Real.log 10 := rfl

end UndergradKB.Precalculus.Course
