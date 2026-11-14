import Mathlib.Probability.CentralLimitTheorem
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesChebyshev
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.LocalLimitBinomial
import UndergradKB.Probability.LocalLimit
import UndergradKB.Probability.LocalLimitLattice
import UndergradKB.Probability.CltBounded
import UndergradKB.Probability.ExamplesNormalApprox
import UndergradKB.Probability.ExamplesTests
import UndergradKB.Probability.NormalTable

/-!
# Course layer, Chapter 9 (Grinstead–Snell, Central Limit Theorem)

Thin wrappers stating the book's results of Chapter 9 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- Grinstead–Snell Theorem 9.4 (PR-100). Central limit theorem for an independent trials process
`X` with mean `μ` and variance `σ²`: `(S_n - n μ) / √n` converges in distribution to a normal
variable `Y` with mean `0` and variance `σ²` (equivalently `(S_n - n μ)/(σ √n)` tends to the
standard normal). -/
@[kb "grinsteadsnell2006" "Theorem 9.4, p. 351"]
theorem gs_theorem_9_4 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ) (hY : HasLaw Y (gaussianReal 0 (variance (X 0) P).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * ∫ ω', X 0 ω' ∂P))
      atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident

/-- Grinstead–Snell Theorem 9.6 (PR-100). Central limit theorem for centered, variance one
independent identically distributed summands: `S_n / √n` converges in distribution to the standard
normal. -/
@[kb "grinsteadsnell2006" "Theorem 9.6, p. 365"]
theorem gs_theorem_9_6 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ) (hY : HasLaw Y (gaussianReal 0 1) P')
    (h0 : ∫ ω, X 0 ω ∂P = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂P = 1) (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum hY h0 h1 hindep hident

/-- Grinstead–Snell Definition 9.1 (PR-096). The standardized sum `S_n* = (S_n - np)/√(npq)` has
mean `0`. -/
@[kb "grinsteadsnell2006" "Definition 9.1, p. 334"]
theorem gs_definition_9_1 : type_of% @UndergradKB.Probability.integral_standardize_sum :=
  @UndergradKB.Probability.integral_standardize_sum

/-- Grinstead–Snell Definition 9.1 (PR-096). The standardized sum has variance `1`. -/
@[kb "grinsteadsnell2006" "Definition 9.1, p. 334"]
theorem gs_definition_9_1_variance : type_of% @UndergradKB.Probability.variance_standardize_sum :=
  @UndergradKB.Probability.variance_standardize_sum

/-- Grinstead–Snell Theorem 9.1 (PR-097). Local limit theorem for the binomial: `√(npq) b(n,p,j)`
tends to the standard normal density. -/
@[kb "grinsteadsnell2006" "Theorem 9.1, p. 336"]
theorem gs_theorem_9_1 : type_of% @UndergradKB.Probability.local_limit_binomial :=
  @UndergradKB.Probability.local_limit_binomial

/-- Grinstead–Snell Theorem 9.1 (PR-097), nearest-integer form. -/
@[kb "grinsteadsnell2006" "Theorem 9.1, p. 336"]
theorem gs_theorem_9_1_nearest : type_of% @UndergradKB.Probability.local_limit_binomial_nearest :=
  @UndergradKB.Probability.local_limit_binomial_nearest

/-- Grinstead–Snell Theorem 9.2 (PR-098). Central limit theorem for Bernoulli trials,
`P(a ≤ S_n* ≤ b) → ∫_a^b φ`. -/
@[kb "grinsteadsnell2006" "Theorem 9.2, p. 338"]
theorem gs_theorem_9_2 : type_of% @UndergradKB.Probability.clt_bernoulli_interval :=
  @UndergradKB.Probability.clt_bernoulli_interval

/-- Grinstead–Snell Theorem 9.3 (PR-099). Local limit theorem for iid lattice variables. -/
@[kb "grinsteadsnell2006" "Theorem 9.3, p. 350"]
theorem gs_theorem_9_3 : type_of% @UndergradKB.Probability.local_limit_lattice :=
  @UndergradKB.Probability.local_limit_lattice

/-- Grinstead–Snell Theorem 9.3 (PR-099), ratio form. -/
@[kb "grinsteadsnell2006" "Theorem 9.3, p. 350"]
theorem gs_theorem_9_3_ratio : type_of% @UndergradKB.Probability.local_limit_lattice_ratio :=
  @UndergradKB.Probability.local_limit_lattice_ratio

/-- Grinstead–Snell Theorem 9.5 (PR-101). Central limit theorem for bounded, not identically
distributed variables (convergence in distribution). -/
@[kb "grinsteadsnell2006" "Theorem 9.5, p. 353"]
theorem gs_theorem_9_5 : type_of% @UndergradKB.Probability.clt_bounded :=
  @UndergradKB.Probability.clt_bounded

/-- Grinstead–Snell Theorem 9.5 (PR-101), interval form. -/
@[kb "grinsteadsnell2006" "Theorem 9.5, p. 353"]
theorem gs_theorem_9_5_interval : type_of% @UndergradKB.Probability.clt_bounded_interval :=
  @UndergradKB.Probability.clt_bounded_interval

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 9.9 (PR-178). The surveyor's independent measurements `X i` have mean `1` and standard deviation `.0002`. -/
@[kb "grinsteadsnell2006" "Example 9.9, p. 366"]
theorem gs_example_9_9 : type_of% @UndergradKB.Probability.surveyor_chebyshev :=
  @UndergradKB.Probability.surveyor_chebyshev


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell Example 9.7 (PR-205). For `n ≥ 1` independent numbers uniform in `[0, 1]` (`μ = 1/2`, `σ² = 1/12`), the sum has mean `n/2` and variance `n/12`, and the standardized sum `S_n* = (S_n - n/2) / (√n √(1/12))` has mean `0` and variance `1`. -/
@[kb "grinsteadsnell2006" "Example 9.7, p. 364"]
theorem gs_example_9_7 : type_of% @UndergradKB.Probability.uniform_standardized_sum :=
  @UndergradKB.Probability.uniform_standardized_sum

/-- Grinstead–Snell Example 9.8 (PR-205). For `n ≥ 1` independent exponential variables with rate `λ > 0` (`μ = σ = 1/λ`), the sum has mean `n/λ` and variance `n/λ²`, and the standardized sum `S_n* = (S_n - n/λ) / (√n /λ)` has mean `0` and variance `1`. -/
@[kb "grinsteadsnell2006" "Example 9.8, p. 364"]
theorem gs_example_9_8 : type_of% @UndergradKB.Probability.exponential_standardized_sum :=
  @UndergradKB.Probability.exponential_standardized_sum

/-- Grinstead–Snell Example 9.3 (PR-205). The acceptances of `1700` applicants, each accepting with probability `.6` independently (Bernoulli trials), have mean `1020` and variance `408` (so a standard deviation `√408`, about `20`: `20 < √408 < 20.2`). -/
@[kb "grinsteadsnell2006" "Example 9.3, p. 340"]
theorem gs_example_9_3 : type_of% @UndergradKB.Probability.dartmouth_acceptances_moments :=
  @UndergradKB.Probability.dartmouth_acceptances_moments

/-- Grinstead–Snell Example 9.5 (PR-205). A fair die (faces `1..6`, mass `1/6` each) has mean `7/2` and variance `35/12`; hence the sum of `420` independent rolls has mean `420 · 7/2 = 1470`, variance `420 · 35/12 = 1225` and standard deviation `√1225 = 35`. -/
@[kb "grinsteadsnell2006" "Example 9.5, p. 351"]
theorem gs_example_9_5 : type_of% @UndergradKB.Probability.die_sum_moments :=
  @UndergradKB.Probability.die_sum_moments

/-- Grinstead–Snell Example 9.6 (PR-205). The grading error law (`±1, …, ±5` with probabilities `|p/k|`, `p = 1/20`, and `0` with probability `463/600`) has total mass `1`, mean `0` and variance `3/2` (as the book says); the sum of the errors in `30` courses has mean `0` and variance `30 · 3/2 = 45`, and the book's threshold `1.5/√45` is `.2235 < 1.5/√45 < .2237` (about `.224`). -/
@[kb "grinsteadsnell2006" "Example 9.6, p. 351"]
theorem gs_example_9_6 : type_of% @UndergradKB.Probability.grading_error_moments :=
  @UndergradKB.Probability.grading_error_moments

/-- Grinstead–Snell Example 9.4 (PR-206). For `n ≥ 1` independent Bernoulli(`p`) answers, the sample proportion `p̄ = S_n / n` has mean `p` and variance `p q / n` with `q = 1 - p`, and its standard deviation is `√(p q / n) ≤ 1 / (2 √n)`. -/
@[kb "grinsteadsnell2006" "Example 9.4, p. 341"]
theorem gs_example_9_4 : type_of% @UndergradKB.Probability.poll_proportion_mean_variance :=
  @UndergradKB.Probability.poll_proportion_mean_variance

/-- Grinstead–Snell Example 9.4 (PR-206), the confidence interval. For every `p̄` and `n ≥ 1`, the 95 percent interval `p̄ ± 2 √(p̄ q̄ / n)` has length `4 √(p̄ q̄ / n) ≤ 2 / √n`. -/
@[kb "grinsteadsnell2006" "Example 9.4, p. 341"]
theorem gs_example_9_4_b : type_of% @UndergradKB.Probability.poll_interval_length :=
  @UndergradKB.Probability.poll_interval_length

/-- Grinstead–Snell Example 9.4 (PR-206), the sample size for a 95 percent interval of length `6` percent. For `n ≥ 1`, `1/√n ≤ .03` holds exactly when `n ≥ 1112` (the book writes `n ≥ 1111`, which is off by one: `1/√1111 > .03`), and then every interval `p̄ ± 2 √(p̄ q̄ / n)` has length at most `.06`. -/
@[kb "grinsteadsnell2006" "Example 9.4, p. 341"]
theorem gs_example_9_4_c : type_of% @UndergradKB.Probability.poll_sample_size :=
  @UndergradKB.Probability.poll_sample_size

/-- Grinstead–Snell Example 9.10 (PR-206). For the surveyor with `σ = .0002` and `n = 36`, with `S_n* = (S_n - 36 μ) / (√36 σ)`: the event `|S_n/36 - μ| < .0001` is the event `|S_n*| < 3` (the book's statement, which uses the tolerance `.0001` of Example 9.9; the book's text says `.0002`), while the event `|S_n/36 - μ| < .0002` is `|S_n*| < 6`. -/
@[kb "grinsteadsnell2006" "Example 9.10, p. 367"]
theorem gs_example_9_10 : type_of% @UndergradKB.Probability.surveyor_event_standardized :=
  @UndergradKB.Probability.surveyor_event_standardized

/-- Grinstead–Snell Example 9.1 (PR-204). Exact binomial values, to the printed precision: for a fair coin `b(100,1/2,55)` rounds to `.0485` (lies in `(.04845, .04855)`) and `b(100,1/2,50)` to `.0796` (`(.07955, .07965)`). The book's `b(36,1/6,8) = .1196` is a misprint: the true value rounds to `.1093` (lies in `(.10925, .10935)`), and the book's `.1196` is false (the value is below `.11955`). -/
@[kb "grinsteadsnell2006" "Example 9.1, p. 337"]
theorem gs_example_9_1 : type_of% @UndergradKB.Probability.clt_local_exact_values :=
  @UndergradKB.Probability.clt_local_exact_values

/-- Grinstead–Snell Example 9.2 (PR-204). For a fair coin tossed 100 times, `P(40 ≤ S₁₀₀ ≤ 60)` lies in `[.964795, .964805)` (`.96480` to five places) and `P(35 ≤ S₁₀₀ ≤ 65)` in `[.998205, .998215)` (`.99821`). -/
@[kb "grinsteadsnell2006" "Example 9.2, p. 340"]
theorem gs_example_9_2 : type_of% @UndergradKB.Probability.clt_global_exact_values :=
  @UndergradKB.Probability.clt_global_exact_values

/-- Grinstead–Snell Example 9.1 (PR-204), local approximation. For `n = 100`, `p = 1/2`, `j = 55` we have `x₅₅ = 1`, and the approximation `φ(1)/5 = e^{-1/2}/(5 √(2π))` lies in `(.04835, .04845)`, i.e. is `.0484` to four places. -/
@[kb "grinsteadsnell2006" "Example 9.1, p. 337"]
theorem gs_example_9_1_b : type_of% @UndergradKB.Probability.clt_local_approximation_value :=
  @UndergradKB.Probability.clt_local_approximation_value

/-! ## Wave 6 course layer (this library) -/

/-- Grinstead–Snell Example 9.2 (PR-204), the normal values. With the half-unit correction, the estimate of `P(40 ≤ S₁₀₀ ≤ 60)` for `100` fair tosses is `NA(-2.1, 2.1) = Φ(2.1) - Φ(-2.1)`, which lies in `(.9642, .9643)` (book: `.9642`), and the estimate of `P(35 ≤ S₁₀₀ ≤ 65)` is `NA(-3.1, 3.1) ∈ (.9980, .9981)` (book: `.9980`). -/
@[kb "grinsteadsnell2006" "Example 9.2, p. 340"]
theorem gs_example_9_2_b : type_of% @UndergradKB.Probability.coin_hundred_normal_values :=
  @UndergradKB.Probability.coin_hundred_normal_values

/-- Grinstead–Snell Example 9.3 (PR-205), the normal value. The estimate of the probability of too many acceptances is `P(S* ≥ 2.025) = 1 - Φ(2.025)`, which lies in `(.0214, .0215)`. The book's interpolated `.5 - .4784 = .0216` is slightly off (`NA(0, 2.025) = .47857`). -/
@[kb "grinsteadsnell2006" "Example 9.3, p. 340"]
theorem gs_example_9_3_b : type_of% @UndergradKB.Probability.dartmouth_normal_value :=
  @UndergradKB.Probability.dartmouth_normal_value

/-- Grinstead–Snell Example 9.5 (PR-205), the normal value. The estimate of `P(1400 ≤ S₄₂₀ ≤ 1550)` for `420` rolls of a die is `NA(-2.01, 2.30) = Φ(2.30) - Φ(-2.01)`, which lies in `(.9670, .9671)` (book: `.9670`). -/
@[kb "grinsteadsnell2006" "Example 9.5, p. 351"]
theorem gs_example_9_5_b : type_of% @UndergradKB.Probability.die_sum_normal_value :=
  @UndergradKB.Probability.die_sum_normal_value

/-- Grinstead–Snell Example 9.6 (PR-205), the normal value. The estimate for the grading errors is `NA(-.224, .224) = Φ(.224) - Φ(-.224)`, which lies in `(.1772, .1773)` (book: `.1772`). -/
@[kb "grinsteadsnell2006" "Example 9.6, p. 351"]
theorem gs_example_9_6_b : type_of% @UndergradKB.Probability.grading_error_normal_value :=
  @UndergradKB.Probability.grading_error_normal_value

/-- Grinstead–Snell Example 9.10 (PR-206), the normal value. The surveyor's estimate is `NA(-3, 3) = (2π)^{-1/2} ∫_{-3}^{3} e^{-x²/2} dx = Φ(3) - Φ(-3)`, which lies in `(.9972, .9974)` (book: `.997`). -/
@[kb "grinsteadsnell2006" "Example 9.10, p. 367"]
theorem gs_example_9_10_b : type_of% @UndergradKB.Probability.surveyor_normal_value :=
  @UndergradKB.Probability.surveyor_normal_value

end UndergradKB.Probability.Course
