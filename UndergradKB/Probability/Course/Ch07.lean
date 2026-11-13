import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.Sums

/-!
# Course layer, Chapter 7 (Grinstead–Snell, Sums of Random Variables)

Thin wrappers stating the book's results of Chapter 7 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Grinstead–Snell Example 7.5 (PR-091). The sum of two independent normal random variables is
normal, with the means added and the variances added. -/
@[kb "grinsteadsnell2006" "Example 7.5, p. 302"]
theorem gs_example_7_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gaussianReal m₁ v₁) P) (hY : HasLaw Y (gaussianReal m₂ v₂) P) :
    P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂) :=
  gaussianReal_add_gaussianReal_of_indepFun hXY hX hY

/-- Grinstead–Snell Definition 7.1 (PR-087). For independent integer-valued `X`, `Y` the distribution
of `X + Y` is the convolution `m(j) = ∑_k m₁(k) m₂(j - k)`. -/
@[kb "grinsteadsnell2006" "Definition 7.1, p. 294"]
theorem gs_definition_7_1 : type_of% @UndergradKB.Probability.measure_add_eq_tsum_int :=
  @UndergradKB.Probability.measure_add_eq_tsum_int

/-- Grinstead–Snell Theorem 7.1 (PR-088). For independent `X`, `Y` with densities `f`, `g` the sum has
density `(f * g)(z) = ∫ f(z - y) g(y) dy`. -/
@[kb "grinsteadsnell2006" "Theorem 7.1, p. 299"]
theorem gs_theorem_7_1 : type_of% @UndergradKB.Probability.map_add_eq_withDensity_convolution :=
  @UndergradKB.Probability.map_add_eq_withDensity_convolution

/-- Grinstead–Snell Example 7.1 (PR-151). The distribution of the sum of two rolls of a fair die. -/
@[kb "grinsteadsnell2006" "Example 7.1, p. 294"]
theorem gs_example_7_1 : type_of% @UndergradKB.Probability.two_dice_sum_distribution :=
  @UndergradKB.Probability.two_dice_sum_distribution

end UndergradKB.Probability.Course
