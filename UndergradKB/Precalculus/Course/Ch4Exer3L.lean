import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 4 (Stitz-Zeager): Exercise 4.3.28 (wave 8)

The cereal box: volume 140 cubic inches, height 1.62 times the width of the base. The book asks for the dimensions
minimizing the surface area, rounded to two decimals, "with a calculator". Here the optimal width is the real root of
`w³ = K` (located by the intermediate value theorem), and minimality is the exact inequality
`a / w + b w² - (a / w₀ + b w₀²) = b (w - w₀)² (w + 2 w₀) / w ≥ 0` for `w₀³ = a / (2 b)`. -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Stitz-Zeager Exercise 4.3.28: among boxes with base width `w`, depth `d`, height `1.62 w` and volume 140, the
surface area `2 (w d + w h + d h)` is smallest for `w ≈ 4.12`, `h ≈ 6.67`, `d ≈ 5.09`, with area `≈ 164.91` (each
within half a unit of the last printed digit). -/
@[kb "stitzzeager2013" "Exercise 4.3.28, p. 366"]
theorem exer_4_3_28 :
    ∃ w₀ d₀ : ℝ, 0 < w₀ ∧ 0 < d₀ ∧ w₀ * d₀ * (1.62 * w₀) = 140 ∧
      w₀ ∈ Ioo 4.115 4.125 ∧ 1.62 * w₀ ∈ Ioo 6.665 6.675 ∧ d₀ ∈ Ioo 5.085 5.095 ∧
      2 * (w₀ * d₀ + w₀ * (1.62 * w₀) + d₀ * (1.62 * w₀)) ∈ Ioo 164.905 164.915 ∧
      ∀ w d : ℝ, 0 < w → 0 < d → w * d * (1.62 * w) = 140 →
        2 * (w₀ * d₀ + w₀ * (1.62 * w₀) + d₀ * (1.62 * w₀)) ≤
          2 * (w * d + w * (1.62 * w) + d * (1.62 * w)) := by
  have e : (1.62 : ℝ) = 81 / 50 := by norm_num
  simp only [e]
  -- `K = a / (2 b)` with `a = 2 · 2.62 · 140 / 1.62`, `b = 3.24`
  set K : ℝ := (2 * (131 / 50) * 140 / (81 / 50)) / (2 * (81 / 25)) with hK
  have hcont : Continuous fun w : ℝ => w ^ 3 := by fun_prop
  obtain ⟨w₀, hw, hw3⟩ : ∃ w ∈ Ioo (4.1189 : ℝ) 4.119, w ^ 3 = K :=
    intermediate_value_Ioo (by norm_num) hcont.continuousOn ⟨by norm_num [hK], by norm_num [hK]⟩
  obtain ⟨hw1, hw2⟩ := hw
  rw [hK] at hw3
  have hw0 : 0 < w₀ := by linarith
  set d₀ : ℝ := 140 / (81 / 50 * w₀ ^ 2) with hd₀
  have hd0 : 0 < d₀ := by positivity
  have hvol : w₀ * d₀ * (81 / 50 * w₀) = 140 := by
    rw [hd₀]; field_simp
  -- the area as a function of the width alone
  have area : ∀ w d : ℝ, 0 < w → w * d * (81 / 50 * w) = 140 →
      w * (2 * (w * d + w * (81 / 50 * w) + d * (81 / 50 * w))) =
        2 * (131 / 50) * 140 / (81 / 50) + 81 / 25 * w ^ 3 := by
    intro w d hw h
    have : w ^ 2 * d = 140 / (81 / 50) := by
      rw [eq_div_iff (by norm_num)]; linear_combination h
    linear_combination (2 * (131 / 50)) * this
  have hA0 : 2 * (w₀ * d₀ + w₀ * (81 / 50 * w₀) + d₀ * (81 / 50 * w₀)) = 3 * (81 / 25) * w₀ ^ 2 := by
    have h := area w₀ d₀ hw0 hvol
    have : w₀ * (2 * (w₀ * d₀ + w₀ * (81 / 50 * w₀) + d₀ * (81 / 50 * w₀))) =
        w₀ * (3 * (81 / 25) * w₀ ^ 2) := by
      rw [h]; linear_combination (-(2 * (81 / 25))) * hw3
    exact mul_left_cancel₀ hw0.ne' this
  have hd1 : d₀ ∈ Ioo 5.085 5.095 := by
    have hw2' : 0 < w₀ ^ 2 := by positivity
    rw [hd₀]
    constructor
    · rw [lt_div_iff₀ (by positivity)]; nlinarith
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
  refine ⟨w₀, d₀, hw0, hd0, hvol, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hd1, ?_, ?_⟩
  · rw [hA0]; constructor <;> nlinarith
  · intro w d hw hd h
    rw [hA0]
    have h1 := area w d hw h
    have key : w * (2 * (w * d + w * (81 / 50 * w) + d * (81 / 50 * w))) - w * (3 * (81 / 25) * w₀ ^ 2) =
        81 / 25 * ((w - w₀) ^ 2 * (w + 2 * w₀)) := by
      rw [h1]; linear_combination (-(2 * (81 / 25))) * hw3
    have hnn : 0 ≤ 81 / 25 * ((w - w₀) ^ 2 * (w + 2 * w₀)) := by positivity
    have : w * (3 * (81 / 25) * w₀ ^ 2) ≤ w * (2 * (w * d + w * (81 / 50 * w) + d * (81 / 50 * w))) := by
      linarith
    exact le_of_mul_le_mul_left this hw

end UndergradKB.Precalculus.Course
