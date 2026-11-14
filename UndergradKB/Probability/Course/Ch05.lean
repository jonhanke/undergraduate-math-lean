import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.Transforms
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.DiscreteDistributions
import UndergradKB.Probability.NormalFamilies
import UndergradKB.Probability.ExamplesNormalApprox
import UndergradKB.Probability.ExamplesQueueStock
import UndergradKB.Probability.ExamplesTests
import UndergradKB.Probability.NormalTable
import UndergradKB.Probability.PoissonClock

/-!
# Course layer, Chapter 5 (Grinstead–Snell, Important Distributions and Densities)

Thin wrappers stating the book's results of Chapter 5 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory Filter Topology
open scoped unitInterval NNReal

/-- Grinstead–Snell §5.1 geometric distribution (PR-050). The first success of Bernoulli trials
with success probability `p` occurs at trial `j` with probability `q^(j-1) p`; Mathlib counts the
failures before the first success, so trial `j` is the point `j - 1`. -/
@[kb "grinsteadsnell2006" "§5.1 geometric distribution, p. 193"]
theorem gs_section_5_1_geometric_distribution {p : I} (hp : p ≠ 0) {j : ℕ} (_hj : 1 ≤ j) :
    (geometricMeasure p).real {j - 1} = (1 - (p : ℝ)) ^ (j - 1) * p :=
  geometricMeasure_real_singleton hp (j - 1)

/-- Grinstead–Snell §5.1 Poisson distribution (PR-053). The Poisson law with mean `r` gives the
value `j` the probability `e^(-r) r^j / j!`, and these probabilities sum to one. -/
@[kb "grinsteadsnell2006" "§5.1 Poisson distribution, p. 197"]
theorem gs_section_5_1_poisson_distribution (r : ℝ≥0) :
    (∀ j : ℕ, (poissonMeasure r).real {j} = Real.exp (-r) * (r : ℝ) ^ j / j.factorial) ∧
      HasSum (fun j : ℕ => Real.exp (-r) * (r : ℝ) ^ j / j.factorial) 1 :=
  ⟨poissonMeasure_real_singleton r, hasSum_one_poissonMeasure r⟩

/-- Grinstead–Snell §5.1 Poisson approximation to the binomial (PR-054). If `n p_n` tends to
`r`, the binomial probabilities `C(n,k) p_n^k (1-p_n)^(n-k)` tend to `e^(-r) r^k / k!`. -/
@[kb "grinsteadsnell2006" "§5.1 Poisson approximation to the binomial, p. 197"]
theorem gs_section_5_1_poisson_approximation (p : ℕ → ℝ) (r : ℝ) (k : ℕ)
    (hr : Tendsto (fun n : ℕ => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) * p n ^ k * (1 - p n) ^ (n - k)) atTop
      (𝓝 (Real.exp (-r) * r ^ k / k.factorial)) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr

/-- Grinstead–Snell §5.2 gamma density (PR-056). The gamma law with shape `a` and rate `r` is a
probability measure with density `r^a x^(a-1) e^(-r x) / Γ(a)` on `x ≥ 0`, and shape `1` is the
exponential law. -/
@[kb "grinsteadsnell2006" "§5.2 gamma density, p. 213"]
theorem gs_section_5_2_gamma_density {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r) ∧
      (∀ x : ℝ, gammaPDFReal a r x =
        if 0 ≤ x then r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) else 0) ∧
      expMeasure r = gammaMeasure 1 r :=
  ⟨isProbabilityMeasure_gammaMeasure ha hr, fun _ => rfl, rfl⟩

/-- Grinstead–Snell §5.2 normal density (PR-057). The normal law with mean `μ` and standard
deviation `s > 0` has density `e^(-(x-μ)²/(2s²)) / (s √(2π))`. -/
@[kb "grinsteadsnell2006" "§5.2 normal density, p. 220"]
theorem gs_section_5_2_normal_density (μ : ℝ) {s : ℝ≥0} (_hs : s ≠ 0) (x : ℝ) :
    IsProbabilityMeasure (gaussianReal μ (s ^ 2)) ∧
      gaussianPDFReal μ (s ^ 2) x =
        Real.exp (-(x - μ) ^ 2 / (2 * (s : ℝ) ^ 2)) / ((s : ℝ) * Real.sqrt (2 * Real.pi)) := by
  refine ⟨inferInstance, ?_⟩
  have h : Real.sqrt (2 * Real.pi * ((s ^ 2 : ℝ≥0) : ℝ)) = s * Real.sqrt (2 * Real.pi) := by
    rw [NNReal.coe_pow, mul_comm (2 * Real.pi), Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (NNReal.coe_nonneg s)]
  rw [gaussianPDFReal_def, h, NNReal.coe_pow]
  ring

/-- Grinstead–Snell Theorem 5.1 (PR-062). For a strictly increasing `φ`, `Y = φ(X)` has cdf
`F_Y(y) = F_X(φ⁻¹(y))`. -/
@[kb "grinsteadsnell2006" "Theorem 5.1, p. 218"]
theorem gs_theorem_5_1 : type_of% @UndergradKB.Probability.cdf_map_strictMono :=
  @UndergradKB.Probability.cdf_map_strictMono

/-- Grinstead–Snell Theorem 5.1 (PR-062), probability form `P(φ(X) ≤ y) = P(X ≤ φ⁻¹(y))`. -/
@[kb "grinsteadsnell2006" "Theorem 5.1, p. 218"]
theorem gs_theorem_5_1_prob : type_of% @UndergradKB.Probability.measure_comp_le_strictMono :=
  @UndergradKB.Probability.measure_comp_le_strictMono

/-- Grinstead–Snell Corollary 5.1 (PR-062). The density of `φ(X)` is `f_X(φ⁻¹(y))` times the
derivative of `φ⁻¹`. -/
@[kb "grinsteadsnell2006" "Corollary 5.1, p. 218"]
theorem gs_corollary_5_1 : type_of% @UndergradKB.Probability.map_withDensity_strictMono :=
  @UndergradKB.Probability.map_withDensity_strictMono

/-- Grinstead–Snell Corollary 5.2 (PR-063). Inverse transform sampling: if `U` is uniform on `[0,1]`
and `F` a strictly increasing cdf then `F⁻¹(U)` has cdf `F`. -/
@[kb "grinsteadsnell2006" "Corollary 5.2, p. 220"]
theorem gs_corollary_5_2 : type_of% @UndergradKB.Probability.cdf_inverse_transform :=
  @UndergradKB.Probability.cdf_inverse_transform

/-- Grinstead–Snell Corollary 5.2 (PR-063), probability form `P(F⁻¹(U) ≤ y) = F(y)`. -/
@[kb "grinsteadsnell2006" "Corollary 5.2, p. 220"]
theorem gs_corollary_5_2_prob : type_of% @UndergradKB.Probability.measure_inverse_transform_le :=
  @UndergradKB.Probability.measure_inverse_transform_le

/-- Grinstead–Snell Example 5.1 (PR-150). The probability of no arrival in the first `k` time units. -/
@[kb "grinsteadsnell2006" "Example 5.1, p. 194"]
theorem gs_example_5_1 : type_of% @UndergradKB.Probability.queue_no_arrival :=
  @UndergradKB.Probability.queue_no_arrival

/-- Grinstead–Snell Example 5.1 (PR-150). The probability of no arrival, in random-variable form. -/
@[kb "grinsteadsnell2006" "Example 5.1, p. 194"]
theorem gs_example_5_1_b : type_of% @UndergradKB.Probability.queue_no_arrival_rv :=
  @UndergradKB.Probability.queue_no_arrival_rv

/-- Grinstead–Snell Example 5.1 (PR-150). The memoryless property of the geometric waiting time. -/
@[kb "grinsteadsnell2006" "Example 5.1, p. 194"]
theorem gs_example_5_1_c : type_of% @UndergradKB.Probability.queue_memoryless :=
  @UndergradKB.Probability.queue_memoryless

/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell §5.2 (PR-058). If `Z` is standard normal then `σ Z + μ` is normal with parameters `μ` and `σ²`. -/
@[kb "grinsteadsnell2006" "§5.2 standardized normal, p. 221"]
theorem gs_section_5_2_standardized_normal : type_of% @UndergradKB.Probability.hasLaw_gaussian_affine :=
  @UndergradKB.Probability.hasLaw_gaussian_affine

/-- Grinstead–Snell §5.2 (PR-058). If `X` is normal with parameters `μ` and `σ²` (`σ ≠ 0`) then the standardized version `(X - μ) / σ` is standard normal. -/
@[kb "grinsteadsnell2006" "§5.2 standardized version, p. 222"]
theorem gs_section_5_2_standardized_version : type_of% @UndergradKB.Probability.hasLaw_gaussian_standardize :=
  @UndergradKB.Probability.hasLaw_gaussian_standardize

/-- Grinstead–Snell §5.1, memoryless property (PR-051). For the number of trials `T` up to the first success, `P(T > r + s | T > r) = P(T > s)`. We assume `p ≠ 1` so that the conditioning event `T > r` has positive probability. -/
@[kb "grinsteadsnell2006" "§5.1 memoryless property, p. 194"]
theorem gs_section_5_1_memoryless_property : type_of% @UndergradKB.Probability.trialsLaw_memoryless :=
  @UndergradKB.Probability.trialsLaw_memoryless

/-- Grinstead–Snell §5.1 negative binomial distribution (PR-052): for `k ≥ 1` and `0 < p ≤ 1`, the masses `u(x, k, p)`, `x = k, k+1, ...` (written `x = j + k`) sum to `1`. -/
@[kb "grinsteadsnell2006" "§5.1 negative binomial distribution, p. 195"]
theorem gs_section_5_1_negative_binomial_distribution : type_of% @UndergradKB.Probability.hasSum_negBinomMass :=
  @UndergradKB.Probability.hasSum_negBinomMass

/-- Grinstead–Snell §5.1 (PR-052), indexed by the trial number `x`: the masses `u(x, k, p)` for `x ≥ k` (and `0` below `k`) sum to `1`. -/
@[kb "grinsteadsnell2006" "§5.1 negative binomial distribution, p. 195"]
theorem gs_section_5_1_negative_binomial_distribution_b : type_of% @UndergradKB.Probability.hasSum_negBinomMass_trial :=
  @UndergradKB.Probability.hasSum_negBinomMass_trial

/-- Grinstead–Snell §5.1 hypergeometric distribution (PR-055): the masses `h(a, b, n, k)`, `0 ≤ k ≤ n`, sum to `1` when `n ≤ a + b` (Vandermonde's identity). -/
@[kb "grinsteadsnell2006" "§5.1 hypergeometric distribution, p. 201"]
theorem gs_section_5_1_hypergeometric_distribution : type_of% @UndergradKB.Probability.sum_hyperMass :=
  @UndergradKB.Probability.sum_hyperMass

/-- Grinstead–Snell §5.1 hypergeometric distribution (PR-055): the mean number of special objects drawn is `n a / (a + b)`. -/
@[kb "grinsteadsnell2006" "§5.1 hypergeometric distribution, p. 201"]
theorem gs_section_5_1_hypergeometric_distribution_b : type_of% @UndergradKB.Probability.hyperMass_mean :=
  @UndergradKB.Probability.hyperMass_mean

/-- Grinstead–Snell §5.2 chi-squared density (PR-060). The law of the square of a standard normal variable is the gamma law with shape `1/2` and rate `1/2` (chi-squared, one degree of freedom). -/
@[kb "grinsteadsnell2006" "§5.2 chi-squared density, p. 225"]
theorem gs_section_5_2_chi_squared_density : type_of% @UndergradKB.Probability.map_sq_gaussianReal_eq_gammaMeasure :=
  @UndergradKB.Probability.map_sq_gaussianReal_eq_gammaMeasure

/-- Grinstead–Snell §5.2 chi-squared density (PR-060), random-variable form: if `Z` is standard normal then `Z²` has the gamma law with shape `1/2` and rate `1/2`. -/
@[kb "grinsteadsnell2006" "§5.2 chi-squared density, p. 225"]
theorem gs_section_5_2_chi_squared_density_b : type_of% @UndergradKB.Probability.hasLaw_sq_gammaMeasure :=
  @UndergradKB.Probability.hasLaw_sq_gammaMeasure

/-- Grinstead–Snell §5.2 Rayleigh density (PR-059), distribution function form. If `X` and `Y` are independent standard normal variables then the length `√(X² + Y²)` satisfies `P(√(X²+Y²) ≤ r) = 1 - e^{-r²/2}` for `r ≥ 0`, i.e. it has the Rayleigh density `r e^{-r²/2}`. -/
@[kb "grinsteadsnell2006" "§5.2 Rayleigh density, p. 223"]
theorem gs_section_5_2_rayleigh_density : type_of% @UndergradKB.Probability.measureReal_sqrt_sq_add_sq_le :=
  @UndergradKB.Probability.measureReal_sqrt_sq_add_sq_le

/-- Grinstead–Snell §5.2 Maxwell density (PR-059), distribution function form. If `V₀, V₁, V₂` are independent standard normal variables, the length `√(V₀² + V₁² + V₂²)` satisfies `P(length ≤ r) = ∫₀ʳ √(2/π) s² e^{-s²/2} ds` for `r ≥ 0`, i.e. it has the Maxwell density. -/
@[kb "grinsteadsnell2006" "§5.2 Maxwell density, p. 223"]
theorem gs_section_5_2_maxwell_density : type_of% @UndergradKB.Probability.measureReal_sqrt_sum_sq_le :=
  @UndergradKB.Probability.measureReal_sqrt_sum_sq_le

/-- Grinstead–Snell Example 5.11 (PR-061), cdf form: if `Θ` is uniform on `(-π/2, π/2)` then `P(tan Θ ≤ x) = 1/2 + arctan(x)/π`. -/
@[kb "grinsteadsnell2006" "Example 5.11, p. 226"]
theorem gs_example_5_11 : type_of% @UndergradKB.Probability.measureReal_tan_le_of_uniform :=
  @UndergradKB.Probability.measureReal_tan_le_of_uniform

/-- Grinstead–Snell Example 5.11 (PR-061). If `Θ` is uniform on `(-π/2, π/2)` then `tan Θ` has the standard Cauchy law (location `0`, scale `1`, density `1/(π(1+x²))`). -/
@[kb "grinsteadsnell2006" "Example 5.11, p. 226"]
theorem gs_example_5_11_b : type_of% @UndergradKB.Probability.map_tan_of_uniform :=
  @UndergradKB.Probability.map_tan_of_uniform

/-- Grinstead–Snell Example 5.8 (PR-200). If `X` is normal with mean `10` and variance `9` (standard deviation `3`), then `P(4 ≤ X ≤ 16) = Φ(2) - Φ(-2) = 2 Φ(2) - 1`, where `Φ` is the distribution function of the standard normal law. (The book's numerical value `.9544` is read from a table; see `normal_within_two_sd_value`.) -/
@[kb "grinsteadsnell2006" "Example 5.8, p. 222"]
theorem gs_example_5_8 : type_of% @UndergradKB.Probability.normal_within_two_sd :=
  @UndergradKB.Probability.normal_within_two_sd

/-- Grinstead–Snell Example 5.7 (PR-209), the time in the system in equilibrium. A customer who finds `j` customers ahead with probability `(1-ρ)ρ^j` (`ρ = λ/μ < 1`) and then spends `j+1` independent exponential(`μ`) service times in the system has total time of density `∑_j (1-ρ)ρ^j · gamma(j+1, μ)(t)` (the Erlang densities `μ^{j+1} t^j e^{-μt}/j!`), and this is the exponential density of rate `μ - λ... -/
@[kb "grinsteadsnell2006" "Example 5.7, p. 216"]
theorem gs_example_5_7 : type_of% @UndergradKB.Probability.queue_time_in_system_density :=
  @UndergradKB.Probability.queue_time_in_system_density

/-- Grinstead–Snell Example 5.6 (PR-199). Table 5.2 has marginals 28 women, 22 men, 32 Democrats, 18 Republicans (n = 50). Given the marginals, the number `a` of female Democrats has the hypergeometric law `C(32,a) C(18,28-a) / C(50,28)` (`a = 0..28`, zero for `a < 10`), whose masses sum to 1; its mean is `28 · 32/50 = 17.92`; and the tail probability of `a ≥ 24` (observed value 24, as extreme data 24... -/
@[kb "grinsteadsnell2006" "Example 5.6, p. 201"]
theorem gs_example_5_6 : type_of% @UndergradKB.Probability.fisher_exact_test_table_5_2 :=
  @UndergradKB.Probability.fisher_exact_test_table_5_2

/-- Grinstead–Snell Example 5.10 (PR-201). For Table 5.8 (319 students) the row totals are 93, 123, 90, 13, the column totals 152, 167, the grand total 319; the expected entries are (row total)(column total)/319 (for instance 44.3 for female A, to one place); the chi-squared statistic `∑ (O-E)²/E` lies in `[4.125, 4.135)`, i.e. -/
@[kb "grinsteadsnell2006" "Example 5.10, p. 224"]
theorem gs_example_5_10 : type_of% @UndergradKB.Probability.chi_squared_grades_gender :=
  @UndergradKB.Probability.chi_squared_grades_gender

/-! ## Wave 6 course layer (this library) -/

/-- Grinstead–Snell Example 5.8 (PR-200), the value. If `X` is normal with mean `10` and variance `9`, then `P(4 ≤ X ≤ 16) = Φ(2) - Φ(-2)` lies in `(.9544, .9546)` (the book: `.9772 - .0228 = .9544`; `Φ(2) = .97725` to five places, so the true value rounds to `.9545`). -/
@[kb "grinsteadsnell2006" "Example 5.8, p. 222"]
theorem gs_example_5_8_b : type_of% @UndergradKB.Probability.normal_within_two_sd_value :=
  @UndergradKB.Probability.normal_within_two_sd_value

/-! ## wave 8 course layer (this library) -/

/-- Grinstead–Snell §5.2 (PR-215), gamma density of `S_n` (proved in the book's Chapter 7). If `X_0, X_1, …` are independent exponential variables with rate `λ > 0`, then for `n ≥ 1` the sum `S_n = X_0 + ⋯ + X_{n-1}` has the gamma law with shape `n` and rate `λ` (density `λ (λx)^{n-1} e^{-λx}/(n-1)!` for `x > 0`). -/
@[kb "grinsteadsnell2006" "§5.2 gamma density, p. 213"]
theorem gs_section_5_2_gamma_density_b : type_of% @UndergradKB.Probability.hasLaw_sum_exponential_gamma :=
  @UndergradKB.Probability.hasLaw_sum_exponential_gamma

/-- Grinstead–Snell §5.2 (PR-215), distribution function of `S_n`. For the gamma law with integer shape `n ≥ 1` and rate `λ > 0`: `G_n(x) = 1 - e^{-λx}(1 + λx + ⋯ + (λx)^{n-1}/(n-1)!)` for `x ≥ 0`, and `G_n(x) = 0` for `x < 0`. -/
@[kb "grinsteadsnell2006" "§5.2 gamma density, p. 213"]
theorem gs_section_5_2_gamma_density_c : type_of% @UndergradKB.Probability.cdf_gammaMeasure_nat :=
  @UndergradKB.Probability.cdf_gammaMeasure_nat

/-- Grinstead–Snell §5.2 (PR-215), the exponential density and the Poisson distribution. Let `X_0, X_1, …` be independent exponential variables with parameter `λ > 0` (times between emissions), `S_n = X_0 + ⋯ + X_{n-1}`, and `t ≥ 0`. The probability that exactly `n` emissions occur by time `t`, `P(S_n ≤ t < S_{n+1})`, is the Poisson probability `e^{-λt}(λt)^n/n!`. -/
@[kb "grinsteadsnell2006" "§5.2 exponential and Poisson, p. 213"]
theorem gs_section_5_2_exponential_and_poisson : type_of% @UndergradKB.Probability.exponential_gaps_poisson_count :=
  @UndergradKB.Probability.exponential_gaps_poisson_count

end UndergradKB.Probability.Course
