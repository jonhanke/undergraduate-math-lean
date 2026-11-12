import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr

/-! # Probability: moments of sums, moment generating functions (Grinstead–Snell, Chapters 6, 10)

Mean and variance of sums and averages of independent trials, the fair heads-or-tails game,
moment generating functions of the standard laws. -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Mean and variance of sums and averages (PR-075) -/

/-- Grinstead–Snell Theorem 6.9 (PR-075). For independent square-integrable variables
`X 0, …, X (n-1)` with common mean `μ` and variance `σ²`, the sum `S_n` has mean `n μ` and
variance `n σ²`. -/
@[kb "grinsteadsnell2006" "Theorem 6.9, p. 268"]
theorem sum_mean_variance [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) {μ σ2 : ℝ} (hμ : ∀ i, P[X i] = μ)
    (hσ : ∀ i, Var[X i; P] = σ2) (n : ℕ) :
    P[∑ i ∈ range n, X i] = n * μ ∧ Var[∑ i ∈ range n, X i; P] = n * σ2 := by
  constructor
  · have : (∑ i ∈ range n, X i) = fun ω => ∑ i ∈ range n, X i ω := by
      funext ω; simp
    rw [this, integral_finsetSum _ (fun i _ => (hL2 i).integrable (by norm_num))]
    simp [hμ]
  · rw [IndepFun.variance_sum (fun i _ => hL2 i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp [hσ]

/-- Grinstead–Snell Corollary 6.1 (PR-075). Under the hypotheses of Theorem 6.9 with `n ≥ 1`, the
average `A_n = S_n / n` has mean `μ` and variance `σ² / n`. -/
@[kb "grinsteadsnell2006" "Corollary 6.1, p. 283"]
theorem average_mean_variance [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) {μ σ2 : ℝ} (hμ : ∀ i, P[X i] = μ)
    (hσ : ∀ i, Var[X i; P] = σ2) {n : ℕ} (hn : 1 ≤ n) :
    P[(n : ℝ)⁻¹ • ∑ i ∈ range n, X i] = μ ∧
      Var[(n : ℝ)⁻¹ • ∑ i ∈ range n, X i; P] = σ2 / n := by
  obtain ⟨h1, h2⟩ := sum_mean_variance hind hL2 hμ hσ n
  have hn' : (n : ℝ) ≠ 0 := by positivity
  constructor
  · have : ((n : ℝ)⁻¹ • ∑ i ∈ range n, X i) = fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω := by
      funext ω; simp
    rw [this, integral_const_mul, h1]
    field_simp
  · rw [variance_smul, h2]
    field_simp

/-! ## The fair heads-or-tails game (PR-086) -/

/-- The fair `±1` step law: `+1` and `-1` each with probability `1/2`. -/
noncomputable def fairStepLaw : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1) ⟨1 / 2, by constructor <;> norm_num⟩

instance : IsProbabilityMeasure fairStepLaw := by
  unfold fairStepLaw; infer_instance

theorem fairStepLaw_integral : ∫ x, x ∂fairStepLaw = 0 := by
  unfold fairStepLaw
  rw [integral_bernoulliMeasure]
  norm_num

theorem fairStepLaw_memLp : MemLp id 2 fairStepLaw := by
  refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 ?_
  unfold fairStepLaw
  exact integrable_bernoulliMeasure _ _ _ _

theorem fairStepLaw_variance : Var[id; fairStepLaw] = 1 := by
  rw [variance_eq_sub fairStepLaw_memLp]
  have : ∫ x, (id x) ^ 2 ∂fairStepLaw = 1 := by
    unfold fairStepLaw
    rw [integral_bernoulliMeasure]
    norm_num
  have h2 : ∫ x, id x ∂fairStepLaw = 0 := fairStepLaw_integral
  simp only [Pi.pow_apply] at *
  rw [this, h2]
  norm_num

/-- Grinstead–Snell Example 6.15 (PR-086). In the fair heads-or-tails game, the steps `X i` are
independent, each `+1` or `-1` with probability `1/2`; the fortune `S_n` has mean `0` and
variance `n`. -/
@[kb "grinsteadsnell2006" "Example 6.15, p. 249"]
theorem fair_game_mean_variance [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) fairStepLaw P) (n : ℕ) :
    P[∑ i ∈ range n, X i] = 0 ∧ Var[∑ i ∈ range n, X i; P] = n := by
  have h := sum_mean_variance hind (fun i => (hlaw i).memLp fairStepLaw_memLp) (μ := 0)
    (σ2 := 1) ?_ ?_ n
  · simpa using h
  · intro i; rw [(hlaw i).integral_eq]; exact fairStepLaw_integral
  · intro i; rw [(hlaw i).variance_eq]; exact fairStepLaw_variance

/-! ## Moment generating functions of standard laws (PR-105) -/

/-- Grinstead–Snell Example 10.2 (PR-105). The binomial law with `n` trials and success
probability `p` has moment generating function `(p e^t + q)^n`, where `q = 1 - p`. -/
@[kb "grinsteadsnell2006" "Example 10.2, p. 375"]
theorem mgf_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (binomial n p) t = ((p : ℝ) * Real.exp t + (1 - p)) ^ n := by
  unfold mgf
  rw [integral_binomial]
  have h : ∀ k ∈ Finset.Iic n, ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - p) ^ (n - k)) •
      Real.exp (t * k) = (n.choose k : ℝ) * ((p : ℝ) * Real.exp t) ^ k * (1 - p) ^ (n - k) := by
    intro k _
    rw [smul_eq_mul, mul_comm t, Real.exp_nat_mul, mul_pow]; ring
  rw [Finset.sum_congr rfl h, add_pow]
  have : Finset.Iic n = Finset.range (n + 1) := by ext k; simp [Nat.lt_succ_iff]
  rw [this]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Grinstead–Snell Example 10.3 (PR-105). For the geometric law with `P(X = j) = q^{j-1} p`
(`j ≥ 1`, `q = 1 - p`), realized as Mathlib's geometric law on `ℕ` shifted by one, the moment
generating function is `p e^t / (1 - q e^t)` whenever `q e^t < 1`. -/
@[kb "grinsteadsnell2006" "Example 10.3, p. 375"]
theorem mgf_geometric (p : unitInterval) (hp : p ≠ 0) (t : ℝ)
    (ht : (1 - (p : ℝ)) * Real.exp t < 1) :
    mgf (fun k : ℕ => (k : ℝ) + 1) (geometricMeasure p) t =
      (p : ℝ) * Real.exp t / (1 - (1 - (p : ℝ)) * Real.exp t) := by
  unfold mgf
  rw [integral_geometricMeasure hp]
  have h : ∀ k : ℕ, (((1 - (p : ℝ)) ^ k * p) • Real.exp (t * ((k : ℝ) + 1))) =
      ((p : ℝ) * Real.exp t) * ((1 - (p : ℝ)) * Real.exp t) ^ k := by
    intro k
    rw [smul_eq_mul, mul_add, mul_one, Real.exp_add, mul_pow, mul_comm t, Real.exp_nat_mul]; ring
  simp_rw [h]
  have hq : 0 ≤ (1 - (p : ℝ)) * Real.exp t :=
    mul_nonneg (sub_nonneg.2 p.2.2) (Real.exp_pos t).le
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq ht]
  ring

/-- Grinstead–Snell Example 10.4 (PR-105). The Poisson law with mean `λ` has moment generating
function `e^{λ(e^t - 1)}`. -/
@[kb "grinsteadsnell2006" "Example 10.4, p. 376"]
theorem mgf_poisson (r : NNReal) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (poissonMeasure r) t = Real.exp (r * (Real.exp t - 1)) := by
  unfold mgf
  rw [integral_poissonMeasure]
  have h : ∀ k : ℕ, ((Real.exp (-r) * (r : ℝ) ^ k / (k.factorial : ℝ)) • Real.exp (t * k)) =
      Real.exp (-r) * (((r : ℝ) * Real.exp t) ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [smul_eq_mul, mul_comm t, Real.exp_nat_mul, mul_pow]; ring
  simp_rw [h]
  rw [tsum_mul_left]
  have := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp t)).tsum_eq
  rw [this, ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  congr 1; ring

end UndergradKB.Probability
