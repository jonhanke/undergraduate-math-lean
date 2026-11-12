import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 8 (Grinstead–Snell, Law of Large Numbers)

Thin wrappers stating the book's results of Chapter 8 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory

/-- Grinstead–Snell Theorem 8.1 (PR-094). Chebyshev inequality for a random variable with finite
variance: `P(|X - μ| ≥ ε) ≤ V(X) / ε²`. -/
@[kb "grinsteadsnell2006" "Theorem 8.1, p. 313"]
theorem gs_theorem_8_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |X ω - ∫ ω', X ω' ∂P|} ≤ ENNReal.ofReal (variance X P / ε ^ 2) :=
  meas_ge_le_variance_div_sq hX hε

/-- Grinstead–Snell Theorem 8.3 (PR-094). The Chebyshev inequality for a continuous random
variable; the same Mathlib statement covers discrete and continuous variables. -/
@[kb "grinsteadsnell2006" "Theorem 8.3, p. 324"]
theorem gs_theorem_8_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |X ω - ∫ ω', X ω' ∂P|} ≤ ENNReal.ofReal (variance X P / ε ^ 2) :=
  meas_ge_le_variance_div_sq hX hε

end UndergradKB.Probability.Course
