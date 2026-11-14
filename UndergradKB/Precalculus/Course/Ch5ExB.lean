import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

/-- Stitz-Zeager Example 5.3.3(1): with `y = 50 - x` and `y² + 30² = z²`, the off-road length is
`z = √((50 - x)² + 900)` (the positive root), so the cost is `15 x + 20 z`. -/
@[kb "stitzzeager2013" "Example 5.3.3, p. 417"]
theorem ex_5_3_3_a (x y z : ℝ) (hz : 0 ≤ z) (hxy : x + y = 50) :
    y ^ 2 + 30 ^ 2 = z ^ 2 → 15 * x + 20 * z = 15 * x + 20 * Real.sqrt ((50 - x) ^ 2 + 900) := by
  intro h
  have : y = 50 - x := by linarith
  subst this
  congr 2
  rw [show (50 - x) ^ 2 + 900 = z ^ 2 by linarith]
  exact (Real.sqrt_sq hz).symm

/-- Stitz-Zeager Example 5.3.3(2): the cost `C x = 15 x + 20 √((50-x)² + 900)` on `[0, 50]` is
minimised at `x = 50 - 90 √7 / 7 ≈ 15.98`, where it equals `750 + 150 √7 ≈ 1146.86`. -/
@[kb "stitzzeager2013" "Example 5.3.3, p. 417"]
theorem ex_5_3_3_b :
    let C : ℝ → ℝ := fun x => 15 * x + 20 * Real.sqrt ((50 - x) ^ 2 + 900)
    let x₀ : ℝ := 50 - 90 * Real.sqrt 7 / 7
    x₀ ∈ Set.Icc (0 : ℝ) 50 ∧ C x₀ = 750 + 150 * Real.sqrt 7 ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 50, C x₀ ≤ C x) ∧
      (15.975 < x₀ ∧ x₀ < 15.985) ∧ (1146.86 < C x₀ ∧ C x₀ < 1146.87) := by
  intro C x₀
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hlo : (2.64575 : ℝ) < Real.sqrt 7 := by
    apply Real.lt_sqrt_of_sq_lt; norm_num
  have hhi : Real.sqrt 7 < (2.64576 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hz : Real.sqrt ((50 - x₀) ^ 2 + 900) = 120 * Real.sqrt 7 / 7 := by
    have : (50 - x₀) ^ 2 + 900 = (120 * Real.sqrt 7 / 7) ^ 2 := by
      simp only [x₀]; nlinarith
    rw [this]
    exact Real.sqrt_sq (by positivity)
  have hC : C x₀ = 750 + 150 * Real.sqrt 7 := by
    show 15 * x₀ + 20 * Real.sqrt ((50 - x₀) ^ 2 + 900) = _
    rw [hz]; simp only [x₀]; ring
  refine ⟨⟨by simp only [x₀]; linarith, by simp only [x₀]; linarith⟩, hC, ?_, ?_, ?_⟩
  · intro x hx
    rw [hC]
    show _ ≤ 15 * x + 20 * Real.sqrt ((50 - x) ^ 2 + 900)
    have hle : (15 * (50 - x) + 150 * Real.sqrt 7) / 20 ≤ Real.sqrt ((50 - x) ^ 2 + 900) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (Real.sqrt 7 * (50 - x) - 90)]
    linarith
  · simp only [x₀]; constructor <;> linarith
  · rw [hC]; constructor <;> linarith

end UndergradKB.Precalculus.Course
