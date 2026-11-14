import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 4.1 and 4.2 -/

namespace UndergradKB.Precalculus.Course

open Filter Topology

/-! ## Section 4.1 -/

/-- Stitz-Zeager Exercise 4.1.23: the typing-speed curve `Y = 216 (X + 19) / (X + 148)` has the horizontal
asymptote `Y = 216` (the practice limit) as `X → ∞`. (The book prints no answer; the claim is the one the exercise
asks to explain.) -/
@[kb "stitzzeager2013" "Exercise 4.1.23, p. 327"]
theorem exer_4_1_23 :
    Tendsto (fun X : ℝ => 216 * (X + 19) / (X + 148)) atTop (𝓝 216) := by
  have h1 : Tendsto (fun X : ℝ => X + 148) atTop atTop := tendsto_atTop_add_const_right _ 148 tendsto_id
  have h2 : Tendsto (fun X : ℝ => (27864 : ℝ) / (X + 148)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds h1
  have h3 : Tendsto (fun X : ℝ => 216 - (27864 : ℝ) / (X + 148)) atTop (𝓝 216) := by
    simpa using (tendsto_const_nhds (x := (216 : ℝ))).sub h2
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have : X + 148 ≠ 0 := by linarith
  field_simp
  ring

/-! ## Section 4.2 -/

/-- Stitz-Zeager Exercise 4.2.17: `f(x) = 1/(x - 2)` is the graph of `1/x` shifted right `2` units, and it tends
to `0` as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 4.2.17, p. 345"]
theorem exer_4_2_17 :
    (∀ x : ℝ, 1 / (x - 2) = (fun t : ℝ => 1 / t) (x - 2)) ∧
      Tendsto (fun x : ℝ => 1 / (x - 2)) atTop (𝓝 0) := by
  refine ⟨fun x => rfl, ?_⟩
  have h1 : Tendsto (fun x : ℝ => x - 2) atTop atTop := tendsto_atTop_add_const_right _ (-2) tendsto_id
  exact Tendsto.div_atTop tendsto_const_nhds h1

/-- Stitz-Zeager Exercise 4.2.18: `g(x) = 1 - 3/x` is `1/x` stretched vertically by `3`, reflected in the
`x`-axis, and shifted up `1` unit. -/
@[kb "stitzzeager2013" "Exercise 4.2.18, p. 345"]
theorem exer_4_2_18 (x : ℝ) : 1 - 3 / x = -(3 * (1 / x)) + 1 := by
  ring

end UndergradKB.Precalculus.Course
