import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.Slope
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): constants, rates of change, absolute value, quadratic formula -/

namespace UndergradKB.Precalculus.Course

/-- Definition 2.2: the constant function with value `b` sends every real number to `b` (PC-038). -/
@[kb "stitzzeager2013" "Definition 2.2, p. 168"]
theorem def_2_2_constant_function (b x : ℝ) : (Function.const ℝ b) x = b :=
  rfl

/-- Definition 2.3: the average rate of change of `f` on `[a, b]` is the slope of the secant line,
`(f b - f a) / (b - a)` (PC-039). -/
@[kb "stitzzeager2013" "Definition 2.3, p. 172"]
theorem def_2_3_average_rate_of_change (f : ℝ → ℝ) (a b : ℝ) :
    slope f a b = (f b - f a) / (b - a) := by
  rw [slope_def_field]

/-- Definition 2.4: the absolute value of `x` is `-x` when `x < 0` and `x` when `x ≥ 0` (PC-040). -/
@[kb "stitzzeager2013" "Definition 2.4, p. 185"]
theorem def_2_4_abs_piecewise (x : ℝ) :
    (x < 0 → |x| = -x) ∧ (0 ≤ x → |x| = x) :=
  ⟨abs_of_neg, abs_of_nonneg⟩

/-- Theorem 2.1 (product, power and quotient rules): `|ab| = |a||b|`, `|aⁿ| = |a|ⁿ`, `|a/b| = |a|/|b|` (PC-041). -/
@[kb "stitzzeager2013" "Theorem 2.1, p. 185"]
theorem thm_2_1_abs_mul_pow_div (a b : ℝ) (n : ℕ) :
    |a * b| = |a| * |b| ∧ |a ^ n| = |a| ^ n ∧ |a / b| = |a| / |b| :=
  ⟨abs_mul a b, abs_pow a n, abs_div a b⟩

/-- Theorem 2.1 (equality properties): `|x| = 0` iff `x = 0`; for `c ≥ 0`, `|x| = c` iff `x = c` or `x = -c`;
for `c < 0` the equation `|x| = c` has no solution (PC-041). -/
@[kb "stitzzeager2013" "Theorem 2.1, p. 185"]
theorem thm_2_1_abs_equality (x c : ℝ) :
    (|x| = 0 ↔ x = 0) ∧ (0 ≤ c → (|x| = c ↔ x = c ∨ x = -c)) ∧ (c < 0 → |x| ≠ c) := by
  refine ⟨abs_eq_zero, fun hc => abs_eq hc, fun hc h => ?_⟩
  linarith [abs_nonneg x]

/-- Theorem 2.4: inequalities with an absolute value become double or split inequalities (PC-042). -/
@[kb "stitzzeager2013" "Theorem 2.4, p. 223"]
theorem thm_2_4_abs_inequalities (x c : ℝ) :
    (|x| < c ↔ -c < x ∧ x < c) ∧ (|x| ≤ c ↔ -c ≤ x ∧ x ≤ c) ∧
    (c < |x| ↔ x < -c ∨ c < x) ∧ (c ≤ |x| ↔ x ≤ -c ∨ c ≤ x) := by
  refine ⟨abs_lt, abs_le, ?_, ?_⟩
  · simp only [lt_abs, lt_neg]; tauto
  · simp only [le_abs', le_neg]

/-- Equation 2.5 (the quadratic formula): for `a ≠ 0` and `b² - 4ac ≥ 0`, the solutions of `ax² + bx + c = 0` are
exactly `(-b ± √(b² - 4ac)) / (2a)` (PC-047). -/
@[kb "stitzzeager2013" "Equation 2.5, p. 206"]
theorem eq_2_5_quadratic_formula (a b c x : ℝ) (ha : a ≠ 0) (h : 0 ≤ b ^ 2 - 4 * a * c) :
    a * x ^ 2 + b * x + c = 0 ↔
      x = (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) ∨
      x = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  have hs : discrim a b c = Real.sqrt (b ^ 2 - 4 * a * c) * Real.sqrt (b ^ 2 - 4 * a * c) := by
    rw [Real.mul_self_sqrt h]; unfold discrim; ring
  have := quadratic_eq_zero_iff ha hs x
  rw [← this]
  constructor <;> intro h <;> linear_combination h

/-- Definition 2.7: the discriminant of `ax² + bx + c` is `b² - 4ac` (PC-048). -/
@[kb "stitzzeager2013" "Definition 2.7, p. 207"]
theorem def_2_7_discriminant (a b c : ℝ) : discrim a b c = b ^ 2 - 4 * a * c := by
  unfold discrim; ring

end UndergradKB.Precalculus.Course
