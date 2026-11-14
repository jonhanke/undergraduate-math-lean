import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesChebyshev
import UndergradKB.Probability.ExamplesLimits
import UndergradKB.Probability.LimitTheorems
import UndergradKB.Probability.CauchyAverage

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

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 8.1 (PR-175). For a real random variable `X` with finite variance `σ² > 0` and any `k > 0`, `P(|X - μ| ≥ kσ) ≤ 1/k²`. -/
@[kb "grinsteadsnell2006" "Example 8.1, p. 314"]
theorem gs_example_8_1 : type_of% @UndergradKB.Probability.chebyshev_standard_deviations :=
  @UndergradKB.Probability.chebyshev_standard_deviations

/-- Grinstead–Snell Example 8.4 (PR-175). The same bound for a continuous random variable (one with a density with respect to Lebesgue measure): `P(|X - μ| ≥ kσ) ≤ 1/k²`. -/
@[kb "grinsteadsnell2006" "Example 8.4, p. 324"]
theorem gs_example_8_4 : type_of% @UndergradKB.Probability.chebyshev_standard_deviations_continuous :=
  @UndergradKB.Probability.chebyshev_standard_deviations_continuous

/-- Grinstead–Snell Example 8.4 (PR-175). Sharpness. -/
@[kb "grinsteadsnell2006" "Example 8.4, p. 324"]
theorem gs_example_8_4_b : type_of% @UndergradKB.Probability.chebyshev_sharp :=
  @UndergradKB.Probability.chebyshev_sharp

/-- Grinstead–Snell Example 8.5 (PR-176). For `n ≥ 1` independent numbers `X i` chosen uniformly in `[0,1]`, the average `S_n/n` has mean `1/2` and variance `1/(12n)`, and for every `ε > 0`,... -/
@[kb "grinsteadsnell2006" "Example 8.5, p. 325"]
theorem gs_example_8_5 : type_of% @UndergradKB.Probability.uniform_samples_chebyshev :=
  @UndergradKB.Probability.uniform_samples_chebyshev

/-- Grinstead–Snell Example 8.6 (PR-176). For `n ≥ 1` independent standard normal samples `X i`, the average `S_n/n` has mean `0` and variance `1/n`, and for every `ε > 0`, `P(|S_n/n - 0| ≥ ε) ≤... -/
@[kb "grinsteadsnell2006" "Example 8.6, p. 326"]
theorem gs_example_8_6 : type_of% @UndergradKB.Probability.normal_samples_chebyshev :=
  @UndergradKB.Probability.normal_samples_chebyshev

/-- Grinstead–Snell Example 8.7 (PR-177). Let `g` be continuous on `[0,1]` with values in `[0,1]` and `X` uniform on `[0,1]`. -/
@[kb "grinsteadsnell2006" "Example 8.7, p. 327"]
theorem gs_example_8_7 : type_of% @UndergradKB.Probability.monte_carlo_mean_variance :=
  @UndergradKB.Probability.monte_carlo_mean_variance

/-- Grinstead–Snell Example 8.7 (PR-177). The Chebyshev estimate. -/
@[kb "grinsteadsnell2006" "Example 8.7, p. 327"]
theorem gs_example_8_7_b : type_of% @UndergradKB.Probability.monte_carlo_chebyshev :=
  @UndergradKB.Probability.monte_carlo_chebyshev


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell Example 8.8 (PR-092). The average of `n` independent standard Cauchy random variables is again standard Cauchy (so averaging does not improve the estimate, and the law of large numbers fails). -/
@[kb "grinsteadsnell2006" "Example 8.8, p. 328"]
theorem gs_example_8_8 : type_of% @UndergradKB.Probability.cauchy_average :=
  @UndergradKB.Probability.cauchy_average

end UndergradKB.Probability.Course
