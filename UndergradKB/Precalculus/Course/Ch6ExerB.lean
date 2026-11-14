import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers, Section 6.2 -/

namespace UndergradKB.Precalculus.Course

open Set Real

/-! ## Helpers -/

private theorem logb_zpow_aux2 {a b x : ℝ} (ha : 1 < a) (m n : ℤ) (hm : m ≠ 0) (hb : b = a ^ m)
    (hx : x = a ^ n) : logb b x = n / m := by
  subst hb hx
  have h0 : 0 < a := by linarith
  have h1 : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  rw [Real.logb, Real.log_zpow, Real.log_zpow]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp

private theorem rpow_div_pow_aux {b : ℝ} (hb : 0 < b) (p q : ℕ) (hq : 0 < q) :
    (b ^ ((p : ℝ) / q)) ^ q = b ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
  have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [div_mul_cancel₀ _ this, Real.rpow_natCast]

private theorem lt_logb_aux {b x : ℝ} (hb : 1 < b) (hx : 0 < x) (p q : ℕ) (hq : 0 < q)
    (h : b ^ p < x ^ q) : (p : ℝ) / q < logb b x := by
  rw [Real.lt_logb_iff_rpow_lt hb hx]
  exact lt_of_pow_lt_pow_left₀ q hx.le (by rw [rpow_div_pow_aux (by linarith) p q hq]; exact h)

private theorem logb_lt_aux {b x : ℝ} (hb : 1 < b) (hx : 0 < x) (p q : ℕ) (hq : 0 < q)
    (h : x ^ q < b ^ p) : logb b x < (p : ℝ) / q := by
  rw [Real.logb_lt_iff_lt_rpow hb hx]
  exact lt_of_pow_lt_pow_left₀ q (by positivity) (by rw [rpow_div_pow_aux (by linarith) p q hq]; exact h)

/-! ## Section 6.2 -/

/-- Stitz-Zeager Exercises 6.2.1, 6.2.2, 6.2.3: `ln (x³y²) = 3 ln x + 2 ln y`,
`log₂ (128/(x²+4)) = 7 - log₂ (x²+4)`, `log₅ ((z/25)³) = 3 log₅ z - 6` (positive variables). -/
@[kb "stitzzeager2013" "Exercise 6.2.1, p. 457"]
theorem exer_6_2_1_to_3 :
    (∀ x y : ℝ, 0 < x → 0 < y → Real.log (x ^ 3 * y ^ 2) = 3 * Real.log x + 2 * Real.log y) ∧
    (∀ x : ℝ, logb 2 (128 / (x ^ 2 + 4)) = 7 - logb 2 (x ^ 2 + 4)) ∧
    (∀ z : ℝ, 0 < z → logb 5 ((z / 25) ^ 3) = 3 * logb 5 z - 6) := by
  refine ⟨fun x y hx hy => ?_, fun x => ?_, fun z hz => ?_⟩
  · rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  · have h := logb_zpow_aux2 (a := 2) (b := 2) (x := 128) (by norm_num) 1 7 one_ne_zero
      (by norm_num) (by norm_num)
    rw [Real.logb_div (by norm_num) (by positivity), show logb 2 128 = 7 by simpa using h]
  · have h5 : Real.log 5 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [Real.logb, Real.log_pow, Real.log_div hz.ne' (by norm_num), show (25 : ℝ) = 5 ^ 2 by norm_num,
      Real.log_pow, Real.logb]
    push_cast
    field_simp
    ring

/-- Stitz-Zeager Exercises 6.2.4, 6.2.5: `log (1.23 × 10³⁷) = log 1.23 + 37` and, for positive `x, y, z`,
`ln (√z / (xy)) = ½ ln z - ln x - ln y`. -/
@[kb "stitzzeager2013" "Exercise 6.2.4, p. 457"]
theorem exer_6_2_4_5 :
    logb 10 (1.23 * 10 ^ 37) = logb 10 1.23 + 37 ∧
    ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
      Real.log (Real.sqrt z / (x * y)) = 1 / 2 * Real.log z - Real.log x - Real.log y := by
  refine ⟨?_, fun x y z hx hy hz => ?_⟩
  · rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    push_cast; ring
  · rw [Real.log_div (by positivity) (by positivity), Real.log_mul hx.ne' hy.ne',
      Real.log_sqrt hz.le]
    ring

/-- Stitz-Zeager Exercise 6.2.8: for `x > 0` and `y > 2`, `log_{1/3} (9x(y³-8)) =
-2 + log_{1/3} x + log_{1/3} (y-2) + log_{1/3} (y²+2y+4)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.8, p. 457"]
theorem exer_6_2_8 (x y : ℝ) (hx : 0 < x) (hy : 2 < y) :
    logb (1 / 3) (9 * x * (y ^ 3 - 8)) =
      -2 + logb (1 / 3) x + logb (1 / 3) (y - 2) + logb (1 / 3) (y ^ 2 + 2 * y + 4) := by
  have h := logb_zpow_aux2 (a := 3) (b := 1 / 3) (x := 9) (by norm_num) (-1) 2 (by norm_num)
    (by norm_num) (by norm_num)
  have h9 : logb (1 / 3) 9 = -2 := by rw [h]; norm_num
  have hy1 : 0 < y - 2 := by linarith
  have hy2 : 0 < y ^ 2 + 2 * y + 4 := by positivity
  rw [show y ^ 3 - 8 = (y - 2) * (y ^ 2 + 2 * y + 4) by ring,
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) hx.ne',
    Real.logb_mul hy1.ne' hy2.ne', h9]
  ring

/-- Stitz-Zeager Exercises 6.2.18, 6.2.20, 6.2.22: single-logarithm forms
`log₃ x - 2 log₃ y = log₃ (x/y²)`, `2 ln x - 3 ln y - 4 ln z = ln (x²/(y³z⁴))`,
`-⅓ ln x - ⅓ ln y + ⅓ ln z = ln ((z/(xy))^(1/3))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.18, p. 457"]
theorem exer_6_2_18_20_22 :
    (∀ x y : ℝ, 0 < x → 0 < y → logb 3 x - 2 * logb 3 y = logb 3 (x / y ^ 2)) ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
      2 * Real.log x - 3 * Real.log y - 4 * Real.log z = Real.log (x ^ 2 / (y ^ 3 * z ^ 4))) ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
      -(1 / 3) * Real.log x - 1 / 3 * Real.log y + 1 / 3 * Real.log z =
        Real.log ((z / (x * y)) ^ ((1 : ℝ) / 3))) := by
  refine ⟨fun x y hx hy => ?_, fun x y z hx hy hz => ?_, fun x y z hx hy hz => ?_⟩
  · rw [Real.logb_div hx.ne' (by positivity), Real.logb_pow]; push_cast; ring
  · rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  · rw [Real.log_rpow (by positivity), Real.log_div hz.ne' (by positivity), Real.log_mul hx.ne' hy.ne']
    ring

/-- Stitz-Zeager Exercises 6.2.6, 6.2.7, 6.2.9, 6.2.10: for `x > 5`, `log₅ (x²-25) = log₅ (x-5) + log₅ (x+5)`;
`log_{√2} (4x³) = 3 log_{√2} x + 4`; `log (1000 x³ y⁵) = 3 + 3 log x + 5 log y`;
`log₃ (x²/(81 y⁴)) = 2 log₃ x - 4 - 4 log₃ y` (positive variables). -/
@[kb "stitzzeager2013" "Exercise 6.2.6, p. 457"]
theorem exer_6_2_6_7_9_10 :
    (∀ x : ℝ, 5 < x → logb 5 (x ^ 2 - 25) = logb 5 (x - 5) + logb 5 (x + 5)) ∧
    (∀ x : ℝ, 0 < x → logb (Real.sqrt 2) (4 * x ^ 3) = 3 * logb (Real.sqrt 2) x + 4) ∧
    (∀ x y : ℝ, 0 < x → 0 < y →
      logb 10 (1000 * x ^ 3 * y ^ 5) = 3 + 3 * logb 10 x + 5 * logb 10 y) ∧
    (∀ x y : ℝ, 0 < x → 0 < y →
      logb 3 (x ^ 2 / (81 * y ^ 4)) = 2 * logb 3 x - 4 - 4 * logb 3 y) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · rw [show x ^ 2 - 25 = (x - 5) * (x + 5) by ring, Real.logb_mul (by linarith) (by linarith)]
  · have h2 : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
      rw [Real.log_sqrt (by norm_num)]
    have h2' : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [Real.logb, Real.logb, h2, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    field_simp
    ring
  · have h10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have h3 := logb_zpow_aux2 (a := 10) (b := 10) (x := 1000) (by norm_num) 1 3 one_ne_zero
      (by norm_num) (by norm_num)
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow, show logb 10 1000 = 3 by simpa using h3]
    push_cast; ring
  · have h3 := logb_zpow_aux2 (a := 3) (b := 3) (x := 81) (by norm_num) 1 4 one_ne_zero
      (by norm_num) (by norm_num)
    rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
      Real.logb_pow, Real.logb_pow, show logb 3 81 = 4 by simpa using h3]
    push_cast; ring

/-- Stitz-Zeager Exercises 6.2.16, 6.2.17, 6.2.19, 6.2.23, 6.2.24: single-logarithm forms
`4 ln x + 2 ln y = ln (x⁴y²)`, `log₂ x + log₂ y - log₂ z = log₂ (xy/z)`,
`½ log₃ x - 2 log₃ y - log₃ z = log₃ (√x/(y²z))`, `log₅ x - 3 = log₅ (x/125)`, `3 - log x = log (1000/x)`. -/
@[kb "stitzzeager2013" "Exercise 6.2.16, p. 457"]
theorem exer_6_2_16_17_19_23_24 :
    (∀ x y : ℝ, 0 < x → 0 < y → 4 * Real.log x + 2 * Real.log y = Real.log (x ^ 4 * y ^ 2)) ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
      logb 2 x + logb 2 y - logb 2 z = logb 2 (x * y / z)) ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z →
      1 / 2 * logb 3 x - 2 * logb 3 y - logb 3 z = logb 3 (Real.sqrt x / (y ^ 2 * z))) ∧
    (∀ x : ℝ, 0 < x → logb 5 x - 3 = logb 5 (x / 125)) ∧
    (∀ x : ℝ, 0 < x → 3 - logb 10 x = logb 10 (1000 / x)) := by
  refine ⟨fun x y hx hy => ?_, fun x y z hx hy hz => ?_, fun x y z hx hy hz => ?_,
    fun x hx => ?_, fun x hx => ?_⟩
  · rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  · rw [Real.logb_div (by positivity) hz.ne', Real.logb_mul hx.ne' hy.ne']
  · rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul (by positivity) hz.ne',
      Real.logb_pow, Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hx]
    push_cast; ring
  · have h := logb_zpow_aux2 (a := 5) (b := 5) (x := 125) (by norm_num) 1 3 one_ne_zero
      (by norm_num) (by norm_num)
    rw [Real.logb_div hx.ne' (by norm_num), show logb 5 125 = 3 by simpa using h]
  · have h := logb_zpow_aux2 (a := 10) (b := 10) (x := 1000) (by norm_num) 1 3 one_ne_zero
      (by norm_num) (by norm_num)
    rw [Real.logb_div (by norm_num) hx.ne', show logb 10 1000 = 3 by simpa using h]

/-- Stitz-Zeager Exercises 6.2.25, 6.2.26, 6.2.27: for `x > 3`, `log₇ x + log₇ (x-3) - 2 = log₇ (x(x-3)/49)`;
for `x > 0`, `ln x + 1/2 = ln (x √e)` and `log₂ x + log₄ x = log₂ (x^(3/2))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.25, p. 457"]
theorem exer_6_2_25_26_27 :
    (∀ x : ℝ, 3 < x → logb 7 x + logb 7 (x - 3) - 2 = logb 7 (x * (x - 3) / 49)) ∧
    (∀ x : ℝ, 0 < x → Real.log x + 1 / 2 = Real.log (x * Real.sqrt (exp 1))) ∧
    (∀ x : ℝ, 0 < x → logb 2 x + logb 4 x = logb 2 (x ^ ((3 : ℝ) / 2))) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h := logb_zpow_aux2 (a := 7) (b := 7) (x := 49) (by norm_num) 1 2 one_ne_zero
      (by norm_num) (by norm_num)
    rw [Real.logb_div (by nlinarith) (by norm_num), Real.logb_mul (by linarith) (by linarith),
      show logb 7 49 = 2 by simpa using h]
  · rw [Real.log_mul hx.ne' (by positivity), Real.log_sqrt (by positivity), Real.log_exp]
  · have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [Real.logb, Real.logb, Real.logb, Real.log_rpow hx, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    field_simp
    ring

/-- Stitz-Zeager Exercises 6.2.28, 6.2.29: for `x > 1`, `log₂ x + log₄ (x-1) = log₂ (x √(x-1))` and
`log₂ x + log_{1/2} (x-1) = log₂ (x/(x-1))`. -/
@[kb "stitzzeager2013" "Exercise 6.2.28, p. 457"]
theorem exer_6_2_28_29 (x : ℝ) (hx : 1 < x) :
    logb 2 x + logb 4 (x - 1) = logb 2 (x * Real.sqrt (x - 1)) ∧
    logb 2 x + logb (1 / 2) (x - 1) = logb 2 (x / (x - 1)) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hx1 : 0 < x - 1 := by linarith
  have hx0 : 0 < x := by linarith
  constructor
  · rw [Real.logb, Real.logb, Real.logb, Real.log_mul hx0.ne' (by positivity),
      Real.log_sqrt hx1.le, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    field_simp
  · rw [Real.logb, Real.logb, Real.logb, Real.log_div hx0.ne' hx1.ne', one_div, Real.log_inv]
    field_simp
    ring

/-- Stitz-Zeager Exercises 6.2.30, 6.2.31, 6.2.32, 6.2.33: change of base, `7^(x-1) = e^((x-1) ln 7)`,
`log₃ (x+2) = log (x+2) / log 3` (common logs), `(2/3)^x = e^(x ln (2/3))`,
`log (x²+1) = ln (x²+1) / ln 10`. -/
@[kb "stitzzeager2013" "Exercise 6.2.30, p. 458"]
theorem exer_6_2_30_to_33 :
    (∀ x : ℝ, (7 : ℝ) ^ (x - 1) = exp ((x - 1) * Real.log 7)) ∧
    (∀ x : ℝ, logb 3 (x + 2) = logb 10 (x + 2) / logb 10 3) ∧
    (∀ x : ℝ, ((2 : ℝ) / 3) ^ x = exp (x * Real.log (2 / 3))) ∧
    (∀ x : ℝ, logb 10 (x ^ 2 + 1) = Real.log (x ^ 2 + 1) / Real.log 10) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  · have h10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    rw [Real.logb, Real.logb, Real.logb]
    field_simp
  · rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  · rfl

/-- Stitz-Zeager Exercises 6.2.34, 6.2.35: `log₃ 12 ≈ 2.26186` lies between `2.26` and `2.27`, and
`log₅ 80 ≈ 2.72271` lies between `2.7` and `2.75`. -/
@[kb "stitzzeager2013" "Exercise 6.2.34, p. 458"]
theorem exer_6_2_34_35 :
    (2.26 < logb 3 12 ∧ logb 3 12 < 2.27) ∧ (2.7 < logb 5 80 ∧ logb 5 80 < 2.75) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := lt_logb_aux (b := 3) (x := 12) (by norm_num) (by norm_num) 113 50 (by norm_num)
      (by norm_num)
    convert this using 1; norm_num
  · have := logb_lt_aux (b := 3) (x := 12) (by norm_num) (by norm_num) 227 100 (by norm_num)
      (by norm_num)
    convert this using 1; norm_num
  · have := lt_logb_aux (b := 5) (x := 80) (by norm_num) (by norm_num) 27 10 (by norm_num)
      (by norm_num)
    convert this using 1; norm_num
  · have := logb_lt_aux (b := 5) (x := 80) (by norm_num) (by norm_num) 11 4 (by norm_num)
      (by norm_num)
    convert this using 1; norm_num

end UndergradKB.Precalculus.Course
