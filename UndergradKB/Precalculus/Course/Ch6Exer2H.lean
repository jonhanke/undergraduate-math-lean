import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 6.4 (inverse), 6.5 -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology

/-- Two-sided numerical bounds for `exp x` on `[0, 1]` (twelve Taylor terms). -/
private theorem x6w7h_expb {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (∑ m ∈ Finset.range 12, x ^ m / (m.factorial : ℝ)) - 3e-9 ≤ Real.exp x ∧
    Real.exp x ≤ (∑ m ∈ Finset.range 12, x ^ m / (m.factorial : ℝ)) + 3e-9 := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound (x := x) hx1 (n := 12) (by norm_num)
  have hx : |x| ^ 12 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
  have hc : (((12 : ℕ).succ : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) ≤ 3e-9 := by
    norm_num [Nat.factorial]
  have h2 : |x| ^ 12 * (((12 : ℕ).succ : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) ≤ 3e-9 := by
    calc _ ≤ 1 * (((12 : ℕ).succ : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) :=
          mul_le_mul_of_nonneg_right hx (by positivity)
      _ ≤ 3e-9 := by linarith
  obtain ⟨a, b⟩ := abs_le.1 h
  constructor <;> linarith

private theorem x6w7h_exp_eq {y c : ℝ} (hc : 0 < c) : Real.exp y = c ↔ y = Real.log c := by
  constructor
  · intro h; rw [← h, Real.log_exp]
  · intro h; rw [h, Real.exp_log hc]

/-- Stitz-Zeager Exercise 6.5.4: `$1000` at `1.25%` compounded continuously, `A(t) = 1000 e^(0.0125t)`:
`A(5) ≈ 1064.49`, `A(10) ≈ 1133.15`, `A(30) ≈ 1454.99`, `A(35) ≈ 1548.83` (each within a cent), doubling time
`ln 2/0.0125 ≈ 55` years, and average rates of change `≈ 13.22` (years 4 to 5) and `≈ 19.24` (years 34 to 35). -/
@[kb "stitzzeager2013" "Exercise 6.5.4, p. 494"]
theorem exer_6_5_4 (A : ℝ → ℝ) (hA : A = fun t => 1000 * Real.exp (0.0125 * t)) :
    |A 5 - 1064.49| < 0.01 ∧ |A 10 - 1133.15| < 0.01 ∧ |A 30 - 1454.99| < 0.01 ∧
    |A 35 - 1548.83| < 0.01 ∧ (∀ t, A t = 2000 ↔ t = Real.log 2 / 0.0125) ∧
    54.5 < Real.log 2 / 0.0125 ∧ Real.log 2 / 0.0125 < 55.5 ∧
    |A 5 - A 4 - 13.22| < 0.02 ∧ |A 35 - A 34 - 19.24| < 0.02 := by
  subst hA
  have e1 := x6w7h_expb (x := 0.05) (by norm_num) (by norm_num)
  have e2 := x6w7h_expb (x := 0.0625) (by norm_num) (by norm_num)
  have e3 := x6w7h_expb (x := 0.125) (by norm_num) (by norm_num)
  have e4 := x6w7h_expb (x := 0.375) (by norm_num) (by norm_num)
  have e5 := x6w7h_expb (x := 0.425) (by norm_num) (by norm_num)
  have e6 := x6w7h_expb (x := 0.4375) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at e1 e2 e3 e4 e5 e6
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e2.1, e2.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e3.1, e3.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e4.1, e4.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e6.1, e6.2]
  · intro t
    have hp : 0 < Real.exp (0.0125 * t) := Real.exp_pos _
    simp only
    have key : 1000 * Real.exp (0.0125 * t) = 2000 ↔ Real.exp (0.0125 * t) = 2 := by
      constructor <;> intro h <;> linarith
    rw [key, x6w7h_exp_eq (by norm_num), eq_div_iff (by norm_num)]
    constructor <;> intro h <;> linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e5.1, e5.2, e6.1, e6.2]

end UndergradKB.Precalculus.Course
