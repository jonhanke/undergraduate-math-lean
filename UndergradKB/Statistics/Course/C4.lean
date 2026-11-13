import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Rules
import UndergradKB.Statistics.DistributionLimits

/-!
# Course layer, chapter 4 (OpenStax *Introductory Statistics 2e*): discrete distributions
-/

namespace UndergradKB.Statistics.Course.C4

open MeasureTheory ProbabilityTheory

/-- OpenStax Introductory Statistics 2e §4.2 (ST-002). Law of large numbers: the average of
independent identically distributed trials with finite mean converges (almost surely) to the
expected value. -/
@[kb "openstaxintrostats2e" "§4.2, p. 241"]
theorem law_of_large_numbers {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) P)
    (hind : Pairwise (Function.onFun (fun a b => a ⟂ᵢ[P] b) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds (∫ x, X 0 x ∂P)) :=
  strong_law_ae X hint hind hid

/-- OpenStax Introductory Statistics 2e §4.1 (ST-034). A discrete probability distribution has
each probability `P(x)` at most 1 and the probabilities add to 1. -/
@[kb "openstaxintrostats2e" "§4.1, p. 239"]
theorem discrete_distribution_sums_to_one {α : Type*} (p : PMF α) :
    (∀ a, p a ≤ 1) ∧ ∑' a, p a = 1 :=
  ⟨p.coe_le_one, p.tsum_coe⟩

/-- OpenStax Introductory Statistics 2e §4.2 (ST-035). The expected value of a discrete random
variable is `∑ x P(x)`. -/
@[kb "openstaxintrostats2e" "§4.2, p. 241"]
theorem expected_value_discrete (p : PMF ℝ) (h : Integrable (fun x : ℝ => x) p.toMeasure) :
    ∫ x : ℝ, x ∂p.toMeasure = ∑' x : ℝ, (p x).toReal * x :=
  by simpa using PMF.integral_eq_tsum p (fun x : ℝ => x) h

/-- OpenStax Introductory Statistics 2e §4.2 (ST-036). The variance is the expected squared
deviation from the mean, `σ² = E[(X - μ)²]`, so `σ` is its square root. -/
@[kb "openstaxintrostats2e" "§4.2, p. 241"]
theorem variance_is_expected_squared_deviation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ} (hX : AEMeasurable X P) :
    Var[X; P] = ∫ ω, (X ω - ∫ x, X x ∂P) ^ 2 ∂P :=
  variance_eq_integral hX

/-- OpenStax Introductory Statistics 2e §4.3 (ST-038). A Bernoulli trial has two outcomes:
success `x` with probability `p` and failure with probability `1 - p`. -/
@[kb "openstaxintrostats2e" "§4.3, p. 248"]
theorem bernoulli_success_probability {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {x y : X} (hxy : x ≠ y) (p : unitInterval) :
    bernoulliMeasure x y p {x} = (unitInterval.toNNReal p : ENNReal) := by
  classical
  rw [bernoulliMeasure_apply p (measurableSet_singleton x)]
  simp [hxy.symm]

/-- OpenStax Introductory Statistics 2e §4.3 (ST-039). Binomial distribution:
`P(X = k) = C(n, k) p^k q^(n-k)` with `q = 1 - p`. -/
@[kb "openstaxintrostats2e" "§4.3, p. 248"]
theorem binomial_probability (n k : ℕ) (p : unitInterval) :
    (binomial n p).real {k} = (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) :=
  binomial_real_singleton n k p

/-- OpenStax Introductory Statistics 2e §4.4, Example 4.20 (ST-041). Geometric distribution:
the probability that the first success occurs on trial `m + 1` is `q^m p` (Mathlib counts the
failures `m` before the first success). -/
@[kb "openstaxintrostats2e" "§4.4, p. 253"]
theorem geometric_probability {p : unitInterval} (hp : p ≠ 0) (m : ℕ) :
    geometricMeasure p {m} = ENNReal.ofReal ((1 - (p : ℝ)) ^ m * p) :=
  geometricMeasure_singleton hp m

/-- OpenStax Introductory Statistics 2e §4.4 (ST-041). The geometric probabilities sum to 1. -/
@[kb "openstaxintrostats2e" "§4.4, p. 253"]
theorem geometric_probabilities_sum_to_one {p : unitInterval} (hp : p ≠ 0) :
    HasSum (fun m : ℕ => (1 - (p : ℝ)) ^ m * p) 1 :=
  hasSum_one_geometricMeasure hp

/-- OpenStax Introductory Statistics 2e §4.6 (ST-046). Poisson approximation to the binomial:
if `n p_n → μ` then `C(n, k) p_n^k (1 - p_n)^(n-k) → e^(-μ) μ^k / k!`. -/
@[kb "openstaxintrostats2e" "§4.6, p. 261"]
theorem poisson_approximates_binomial {p : ℕ → ℝ} {μ : ℝ} (k : ℕ)
    (h : Filter.Tendsto (fun n : ℕ => (n : ℝ) * p n) Filter.atTop (nhds μ)) :
    Filter.Tendsto (fun n : ℕ => (n.choose k : ℝ) * p n ^ k * (1 - p n) ^ (n - k))
      Filter.atTop (nhds (Real.exp (-μ) * μ ^ k / k.factorial)) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop k h

/-- OpenStax Introductory Statistics 2e §4.6 (ST-047). The sum of independent Poisson random
variables with parameters `μ₁`, `μ₂` is Poisson with parameter `μ₁ + μ₂`. -/
@[kb "openstaxintrostats2e" "§4.6, p. 261"]
theorem poisson_sum {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {μ₁ μ₂ : NNReal}
    {X Y : Ω → ℕ} (hind : X ⟂ᵢ[P] Y) (hX : HasLaw X (poissonMeasure μ₁) P)
    (hY : HasLaw Y (poissonMeasure μ₂) P) :
    HasLaw (X + Y) (poissonMeasure (μ₁ + μ₂)) P :=
  IndepFun.hasLaw_add_poissonMeasure hind hX hY

/-- OpenStax Introductory Statistics 2e §4.3 (ST-040). The binomial distribution has mean `n p`. -/
@[kb "openstaxintrostats2e" "§4.3, p. 248"]
theorem binomial_mean {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ}
    {p : unitInterval} {X : Ω → ℝ}
    (hX : HasLaw X ((binomial n p).map (Nat.cast : ℕ → ℝ)) P) :
    ∫ ω, X ω ∂P = (n : ℝ) * p := by
  rw [integral_of_hasLaw_binomial hX]; ring

/-- OpenStax Introductory Statistics 2e §4.2 (ST-037). Expected value of a game: if the gains of
successive plays are independent, identically distributed and take values in a finite set `S`,
then almost surely the average gain over the first `n` plays converges to the expected value
`∑ x ∈ S, x · P(X 0 = x)`. -/
@[kb "openstaxintrostats2e" "§4.2, p. 241"]
theorem long_run_average_gain_eq_expected_value {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset ℝ) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hS : ∀ i ω, X i ω ∈ S)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω)
      Filter.atTop (nhds (∑ x ∈ S, x * P.real (X 0 ⁻¹' {x}))) :=
  UndergradKB.Statistics.long_run_average_gain P S X hmeas hS hindep hident

/-- OpenStax Introductory Statistics 2e §4.5 (ST-044). The binomial approximates the hypergeometric
for a large population: if the numbers of successes `A k` and failures `B k` both tend to infinity
with success fraction `A k / (A k + B k) → p`, then for a fixed sample size `n` and `x ≤ n` the
hypergeometric probability of `x` successes tends to the binomial probability
`C(n, x) p^x (1 - p)^(n - x)`. -/
@[kb "openstaxintrostats2e" "§4.5, p. 258"]
theorem hypergeometric_probability_tends_to_binomial {A B : ℕ → ℕ} {p : ℝ}
    (hA : Filter.Tendsto A Filter.atTop Filter.atTop)
    (hB : Filter.Tendsto B Filter.atTop Filter.atTop)
    (hp : Filter.Tendsto (fun k ↦ (A k : ℝ) / ((A k : ℝ) + B k)) Filter.atTop (nhds p))
    (n x : ℕ) (hx : x ≤ n) :
    Filter.Tendsto (fun k ↦ UndergradKB.Statistics.hypergeometricPMF (A k) (B k) n x)
      Filter.atTop (nhds ((n.choose x : ℝ) * p ^ x * (1 - p) ^ (n - x))) :=
  UndergradKB.Statistics.tendsto_hypergeometricPMF_binomial hA hB hp n x hx

end UndergradKB.Statistics.Course.C4
