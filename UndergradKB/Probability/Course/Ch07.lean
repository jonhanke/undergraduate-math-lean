import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr

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

end UndergradKB.Probability.Course
