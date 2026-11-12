import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr

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

end UndergradKB.Probability.Course
