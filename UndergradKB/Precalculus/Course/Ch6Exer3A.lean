import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 6.2 -/

namespace UndergradKB.Precalculus.Course

private theorem x6w8a_lg {b c a : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (hc : 0 < c) (h : b ^ a = c) :
    Real.logb b c = a := (Real.logb_eq_iff_rpow_eq hb hb1 hc).2 h

/-- Stitz-Zeager Exercise 6.2.14: `log_{1/2}(4 ∛(x²) / (y √z)) = -2 + (2/3) log_{1/2} x - log_{1/2} y - (1/2) log_{1/2} z`
for positive `x, y, z`. -/
@[kb "stitzzeager2013" "Exercise 6.2.14, p. 457"]
theorem exer_6_2_14 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.logb (1 / 2) (4 * x ^ (2 / 3 : ℝ) / (y * Real.sqrt z)) =
      -2 + 2 / 3 * Real.logb (1 / 2) x - Real.logb (1 / 2) y - 1 / 2 * Real.logb (1 / 2) z := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h4 : Real.logb (1 / 2) 4 = -2 := by
    rw [Real.logb, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, one_div, Real.log_inv]
    push_cast; field_simp
  have hsz : Real.logb (1 / 2) (Real.sqrt z) = 1 / 2 * Real.logb (1 / 2) z := by
    rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hz]
  have hxp : Real.logb (1 / 2) (x ^ (2 / 3 : ℝ)) = 2 / 3 * Real.logb (1 / 2) x :=
    Real.logb_rpow_eq_mul_logb_of_pos hx
  have hsp : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hxq : 0 < x ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hx _
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul (by norm_num) hxq.ne',
    Real.logb_mul hy.ne' hsp.ne', h4, hxp, hsz]
  ring

/-- Stitz-Zeager Exercise 6.2.41: the quotient rule and the power rule for logarithms, for positive arguments. -/
@[kb "stitzzeager2013" "Exercise 6.2.41, p. 458"]
theorem exer_6_2_41 (b x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb b (x / y) = Real.logb b x - Real.logb b y ∧
      ∀ n : ℕ, Real.logb b (x ^ n) = n * Real.logb b x := by
  refine ⟨Real.logb_div hx.ne' hy.ne', fun n => ?_⟩
  rw [Real.logb_pow]

/-- Stitz-Zeager Exercise 6.2.42: numerical examples (base 2): `log(1+1) ≠ log 1 + log 1`,
`log(8-4) ≠ log 8 - log 4` and `log(8/4) ≠ log 8 / log 4`. -/
@[kb "stitzzeager2013" "Exercise 6.2.42, p. 458"]
theorem exer_6_2_42 :
    Real.logb 2 (1 + 1) ≠ Real.logb 2 1 + Real.logb 2 1 ∧
    Real.logb 2 (8 - 4) ≠ Real.logb 2 8 - Real.logb 2 4 ∧
    Real.logb 2 (8 / 4) ≠ Real.logb 2 8 / Real.logb 2 4 := by
  have h8 : Real.logb 2 8 = 3 := x6w8a_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 : Real.logb 2 4 = 2 := x6w8a_lg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (1 + 1 : ℝ) = 2 by norm_num, h2, Real.logb_one]; norm_num
  · rw [show (8 - 4 : ℝ) = 4 by norm_num, h8, h4]; norm_num
  · rw [show (8 / 4 : ℝ) = 2 by norm_num, h8, h4, h2]; norm_num

/-- Stitz-Zeager Exercise 6.2.43 (Henderson-Hasselbalch): with `Ka = [H⁺][A⁻]/[HA]`, `pH = -log[H⁺]` and
`pKa = -log Ka`, one gets `pH = pKa + log([A⁻]/[HA])`. -/
@[kb "stitzzeager2013" "Exercise 6.2.43, p. 458"]
theorem exer_6_2_43 (H A HA Ka : ℝ) (hH : 0 < H) (hA : 0 < A) (hHA : 0 < HA) (hKa : Ka = H * A / HA) :
    -Real.logb 10 H = -Real.logb 10 Ka + Real.logb 10 (A / HA) := by
  rw [hKa, Real.logb_div (by positivity) hHA.ne', Real.logb_mul hH.ne' hA.ne',
    Real.logb_div hA.ne' hHA.ne']
  ring

/-- Stitz-Zeager Exercise 6.2.40: `ln(x²) = 2 ln x` for `x > 0`; the left side is also defined for `x < 0`
(where `x² > 0`), where it equals `2 ln|x|`, while `2 ln x` is not defined there. -/
@[kb "stitzzeager2013" "Exercise 6.2.40, p. 458"]
theorem exer_6_2_40 :
    (∀ x : ℝ, 0 < x → Real.log (x ^ 2) = 2 * Real.log x) ∧
    (∀ x : ℝ, x ≠ 0 → Real.log (x ^ 2) = 2 * Real.log |x|) ∧ ∀ x : ℝ, x < 0 → 0 < x ^ 2 := by
  refine ⟨fun x _ => ?_, fun x _ => ?_, fun x hx => by nlinarith⟩
  · rw [Real.log_pow]; norm_num
  · rw [Real.log_pow, Real.log_abs]; norm_num

end UndergradKB.Precalculus.Course
