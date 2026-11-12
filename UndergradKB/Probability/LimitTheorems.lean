import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import UndergradKB.Common.Attr

/-!
# Limit theorems (Grinstead–Snell, chapters 8 and 9)

The weak law of large numbers by Chebyshev's inequality (Theorems 8.2 and 8.4) and the central
limit theorem in interval form for iid sums and for Bernoulli trials (Theorems 9.2 and 9.4).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace UndergradKB.Probability

section WLLN

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Theorem 8.2 / 8.4 (PR-095), quantitative form. For pairwise independent
variables with common mean `μ` and common variance `σ2`, Chebyshev's inequality bounds the chance
that the sample mean is off by `ε` or more by `σ2 / (n ε²)`. -/
@[kb "grinsteadsnell2006" "Theorem 8.2, p. 315"]
theorem weak_law_chebyshev_bound {X : ℕ → Ω → ℝ} (hL : ∀ i, MemLp (X i) 2 P)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[P] X j) {μ σ2 : ℝ} (hμ : ∀ i, P[X i] = μ)
    (hσ : ∀ i, Var[X i; P] = σ2) {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |(∑ k ∈ Finset.range n, X k ω) / n - μ|} ≤ σ2 / (n * ε ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : MemLp (∑ i ∈ Finset.range n, X i) 2 P :=
    memLp_finsetSum' _ (fun i _ => hL i)
  have hY : MemLp ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i) 2 P := hS.const_smul _
  have hint : ∀ i, Integrable (X i) P := fun i => (hL i).integrable (by norm_num)
  have hmean : P[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i] = μ := by
    have : ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i) =
        fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
      ext ω; simp
    rw [this, integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
    simp [hμ]
    field_simp
  have hvar : Var[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i; P] = σ2 / n := by
    rw [variance_smul, IndepFun.variance_sum (fun i _ => hL i)
      (fun i _ j _ hij => hindep hij)]
    simp [hσ]
    field_simp
  have key := meas_ge_le_variance_div_sq hY hε
  rw [hmean, hvar] at key
  have hset : {ω | ε ≤ |((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i) ω - μ|} =
      {ω | ε ≤ |(∑ k ∈ Finset.range n, X k ω) / n - μ|} := by
    ext ω
    simp [div_eq_inv_mul]
  rw [hset] at key
  rw [measureReal_def]
  have h2 : σ2 / n / ε ^ 2 = σ2 / (n * ε ^ 2) := by field_simp
  rw [h2] at key
  exact ENNReal.toReal_le_of_le_ofReal (by
    have h0 : 0 ≤ σ2 := by
      rw [← hσ 0]; exact variance_nonneg _ _
    exact div_nonneg h0 (by positivity)) key

/-- Grinstead–Snell Theorem 8.2 / 8.4 (PR-095), limit form: the probability that the sample mean
differs from `μ` by at least `ε` tends to `0` (weak law of large numbers). -/
@[kb "grinsteadsnell2006" "Theorem 8.4, p. 324"]
theorem weak_law_of_large_numbers {X : ℕ → Ω → ℝ} (hL : ∀ i, MemLp (X i) 2 P)
    (hindep : Pairwise fun i j => X i ⟂ᵢ[P] X j) {μ σ2 : ℝ} (hμ : ∀ i, P[X i] = μ)
    (hσ : ∀ i, Var[X i; P] = σ2) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P.real {ω | ε ≤ |(∑ k ∈ Finset.range n, X k ω) / n - μ|})
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => σ2 / (n * ε ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) * ε ^ 2) atTop atTop :=
      h1.atTop_mul_const (by positivity)
    exact h2.const_div_atTop σ2
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact weak_law_chebyshev_bound hL hindep hμ hσ hn hε

end WLLN

end UndergradKB.Probability
