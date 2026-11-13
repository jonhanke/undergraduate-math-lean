import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Statistics.SampleMoments

/-!
# Course layer, chapter 7 (OpenStax *Introductory Statistics 2e*): the central limit theorem
-/

namespace UndergradKB.Statistics.Course.C7

open MeasureTheory ProbabilityTheory

section SampleMean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- OpenStax Introductory Statistics 2e §7.1 (ST-064). The sample mean of `n` independent
identically distributed observations with finite variance has expected value `μ`. -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem expected_sample_mean (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n) (hX : ∀ i, MemLp (X i) 2 P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hnr : (n : ℝ) ≠ 0 := by positivity
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hX i).integrable one_le_two)]
  rw [Finset.sum_congr rfl (fun i _ => (hid i).integral_eq)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- OpenStax Introductory Statistics 2e §7.1 (ST-064). The variance of the sample mean of `n`
independent identically distributed observations is `σ² / n`. -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem variance_sample_mean (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n) (hX : ∀ i, MemLp (X i) 2 P)
    (hind : Pairwise (Function.onFun (fun a b => a ⟂ᵢ[P] b) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    Var[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i; P] = Var[X 0; P] / n := by
  have hnr : (n : ℝ) ≠ 0 := by positivity
  rw [variance_smul, IndepFun.variance_sum (fun i _ => hX i) (hind.set_pairwise _)]
  rw [Finset.sum_congr rfl (fun i _ => (hid i).variance_eq)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- OpenStax Introductory Statistics 2e §7.1 (ST-064). The standard error of the sample mean is
`σ / √n`. -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem standard_error_sample_mean (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n)
    (hX : ∀ i, MemLp (X i) 2 P)
    (hind : Pairwise (Function.onFun (fun a b => a ⟂ᵢ[P] b) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    Real.sqrt Var[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i; P]
      = Real.sqrt Var[X 0; P] / Real.sqrt n := by
  rw [variance_sample_mean X n hn hX hind hid, Real.sqrt_div (variance_nonneg _ _)]

end SampleMean

section CLT

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

/-- OpenStax Introductory Statistics 2e §7.2 (ST-067). Central limit theorem for sums: for
independent identically distributed observations with finite variance, the standardized sum
`(S_n - n μ) / √n` converges in distribution to `N(0, σ²)`, i.e. `S_n` is approximately
`N(n μ, √n σ)`. -/
@[kb "openstaxintrostats2e" "§7.2, p. 381"]
theorem central_limit_theorem_sum (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * ∫ x, X 0 x ∂P))
      Filter.atTop Y (fun _ => P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hind hid

/-- OpenStax Introductory Statistics 2e §7.1 (ST-065). Central limit theorem for sample means:
`√n (X̄ₙ - μ)` converges in distribution to `N(0, σ²)`, i.e. `X̄ₙ` is approximately
`N(μ, σ/√n)`. -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem central_limit_theorem_mean (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hind : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω - ∫ x, X 0 x ∂P))
      Filter.atTop Y (fun _ => P) P' := by
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hind hid
  have e : (fun (n : ℕ) ω => √(n : ℝ) * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X k ω
      - ∫ x, X 0 x ∂P)) = fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - n * ∫ x, X 0 x ∂P) := by
    funext n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    obtain ⟨s, hs⟩ : ∃ s, s = √(n : ℝ) := ⟨_, rfl⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : s ^ 2 = n := by rw [hs]; exact Real.sq_sqrt hn'.le
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at h2
      norm_num at h2
      linarith
    rw [← hs, ← h2]
    field_simp
  rw [e]
  exact h

end CLT

/-- OpenStax Introductory Statistics 2e §7.1 (ST-068). Law of large numbers: the sample mean of
independent identically distributed observations with finite mean approaches the population
mean (almost surely). -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem sample_mean_tendsto_population_mean {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) P)
    (hind : Pairwise (Function.onFun (fun a b => a ⟂ᵢ[P] b) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds (∫ x, X 0 x ∂P)) :=
  strong_law_ae X hint hind hid

/-- OpenStax Introductory Statistics 2e §7.1 (ST-063). Sampling without replacement: for a simple
random sample of size `n` (`1 ≤ n ≤ N`, `N ≥ 2`) from a population `x` of `N` members, the sample
mean has variance `(σ²/n) · (N - n)/(N - 1)`, where `σ²` is the population variance (the finite
population correction factor). -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem variance_sample_mean_without_replacement {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N)
    (hN : 2 ≤ N) (x : Fin N → ℝ) :
    Var[fun S : Finset (Fin N) ↦ (∑ i ∈ S, x i) / n; UndergradKB.Statistics.srsLaw N n] =
      UndergradKB.Statistics.populationVariance x / n * (((N : ℝ) - n) / ((N : ℝ) - 1)) :=
  UndergradKB.Statistics.variance_srsLaw_sampleMean hn hnN hN x

end UndergradKB.Statistics.Course.C7
