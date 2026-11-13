import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesLimits
import UndergradKB.Probability.LimitTheorems

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

/-- Grinstead–Snell Theorem 8.2 (PR-095). Law of large numbers (Chebyshev form): the probability that
the average deviates from `μ` by at least `ε` is at most `σ²/(n ε²)`. -/
@[kb "grinsteadsnell2006" "Theorem 8.2, p. 315"]
theorem gs_theorem_8_2 : type_of% @UndergradKB.Probability.weak_law_chebyshev_bound :=
  @UndergradKB.Probability.weak_law_chebyshev_bound

/-- Grinstead–Snell Theorem 8.4 (PR-095). Law of large numbers: `P(|S_n/n - μ| ≥ ε) → 0` for every
`ε > 0`. -/
@[kb "grinsteadsnell2006" "Theorem 8.4, p. 324"]
theorem gs_theorem_8_4 : type_of% @UndergradKB.Probability.weak_law_of_large_numbers :=
  @UndergradKB.Probability.weak_law_of_large_numbers

/-- Grinstead–Snell Example 8.2 (PR-157). The Chebyshev bound for the sum of independent die rolls. -/
@[kb "grinsteadsnell2006" "Example 8.2, p. 316"]
theorem gs_example_8_2 : type_of% @UndergradKB.Probability.die_chebyshev :=
  @UndergradKB.Probability.die_chebyshev

/-- Grinstead–Snell Example 8.3 (PR-157). The Chebyshev bound for Bernoulli trials. -/
@[kb "grinsteadsnell2006" "Example 8.3, p. 318"]
theorem gs_example_8_3 : type_of% @UndergradKB.Probability.bernoulli_chebyshev :=
  @UndergradKB.Probability.bernoulli_chebyshev

end UndergradKB.Probability.Course
