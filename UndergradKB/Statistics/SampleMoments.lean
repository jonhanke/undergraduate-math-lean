import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Sampling

/-!
# Moments of sample means and sample variances

OpenStax *Introductory Statistics 2e*:
* §2.7: the sample variance (divisor `n - 1`) is an unbiased estimator of `σ²`, while the divisor-`n`
  version is not;
* §10.2: the difference of two independent sample means has mean `μ₁ - μ₂` and variance
  `σ₁²/n₁ + σ₂²/n₂`;
* §7.1: for simple random sampling without replacement from a finite population, the variance of the
  sample mean is `(σ²/n)(N - n)/(N - 1)`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Finset

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Variance of a weighted sum of pairwise independent square-integrable variables. -/
lemma variance_weighted_sum {ι : Type*} [Fintype ι] {W : ι → Ω → ℝ} (c : ι → ℝ)
    (hW : ∀ i, MemLp (W i) 2 P) (hind : Pairwise fun a b ↦ IndepFun (W a) (W b) P) :
    Var[fun ω ↦ ∑ a, c a * W a ω; P] = ∑ a, c a ^ 2 * Var[W a; P] := by
  have h := IndepFun.variance_sum (μ := P) (X := fun a ω ↦ c a * W a ω) (s := Finset.univ)
    (fun a _ ↦ (hW a).const_mul (c a))
    (fun a _ b _ hab ↦ (hind hab).comp (φ := fun x : ℝ ↦ c a * x) (ψ := fun x : ℝ ↦ c b * x)
      (by fun_prop) (by fun_prop))
  have e : (∑ a ∈ Finset.univ, fun ω ↦ c a * W a ω) = fun ω ↦ ∑ a, c a * W a ω := by
    funext ω
    simp [Finset.sum_apply]
  rw [e] at h
  rw [h]
  exact Finset.sum_congr rfl fun a _ ↦ variance_const_mul (c a) (W a) P

/-- Expectation of a weighted sum of square-integrable variables. -/
lemma integral_weighted_sum [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {W : ι → Ω → ℝ}
    (c : ι → ℝ) (hW : ∀ i, MemLp (W i) 2 P) :
    ∫ ω, ∑ a, c a * W a ω ∂P = ∑ a, c a * ∫ ω, W a ω ∂P := by
  rw [integral_finsetSum _ fun a _ ↦ ((hW a).integrable one_le_two).const_mul (c a)]
  exact Finset.sum_congr rfl fun a _ ↦ integral_const_mul _ _

variable {n : ℕ}

/-- `∑ (xᵢ - m)² = ∑ (xᵢ - x̄)² + n (x̄ - m)²`. -/
lemma sumSqDev_eq (x : Fin n → ℝ) (m : ℝ) :
    sumSqDev x = ∑ i, (x i - m) ^ 2 - n * (mean x - m) ^ 2 := by
  have h : ∀ i, (x i - m) ^ 2 =
      (x i - mean x) ^ 2 + 2 * (mean x - m) * (x i - mean x) + (mean x - m) ^ 2 := fun i ↦ by ring
  simp only [h, sum_add_distrib, ← mul_sum, sum_sub_mean, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  unfold sumSqDev
  ring

/-- The expected sum of squared deviations of an uncorrelated sample is `(n - 1) σ²`. -/
lemma integral_sumSqDev [IsProbabilityMeasure P] (hn : 1 ≤ n) {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hL : ∀ i, MemLp (X i) 2 P) (hμ : ∀ i, P[X i] = μ) (hσ : ∀ i, Var[X i; P] = σ ^ 2)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P) :
    ∫ ω, sumSqDev (fun i ↦ X i ω) ∂P = ((n : ℝ) - 1) * σ ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  set xb : Ω → ℝ := fun ω ↦ ∑ i, (1 / (n : ℝ)) * X i ω with hxb
  have hmean : ∀ ω, mean (fun i ↦ X i ω) = xb ω := by
    intro ω
    show (∑ i, X i ω) / n = ∑ i, 1 / (n : ℝ) * X i ω
    rw [← mul_sum]
    ring
  have hxbL : MemLp xb 2 P := memLp_finsetSum _ fun i _ ↦ (hL i).const_mul _
  have hExb : ∫ ω, xb ω ∂P = μ := by
    rw [hxb, integral_weighted_sum _ hL]
    simp only [hμ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hVxb : Var[xb; P] = σ ^ 2 / n := by
    rw [hxb, variance_weighted_sum _ hL hind]
    simp only [hσ, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hE1 : ∀ i, ∫ ω, (X i ω - μ) ^ 2 ∂P = σ ^ 2 := fun i ↦ by
    rw [← hσ i, variance_eq_integral (hL i).aemeasurable, hμ i]
  have hE2 : ∫ ω, (xb ω - μ) ^ 2 ∂P = σ ^ 2 / n := by
    rw [← hVxb, variance_eq_integral hxbL.aemeasurable, hExb]
  have hI1 : ∀ i, Integrable (fun ω ↦ (X i ω - μ) ^ 2) P := fun i ↦
    ((hL i).sub (memLp_const μ)).integrable_sq
  have hI2 : Integrable (fun ω ↦ (xb ω - μ) ^ 2) P := (hxbL.sub (memLp_const μ)).integrable_sq
  have hpt : (fun ω ↦ sumSqDev (fun i ↦ X i ω)) =
      fun ω ↦ ∑ i, (X i ω - μ) ^ 2 - n * (xb ω - μ) ^ 2 := by
    funext ω
    rw [sumSqDev_eq _ μ, hmean]
  rw [hpt, integral_sub (integrable_finsetSum _ fun i _ ↦ hI1 i) (hI2.const_mul _),
    integral_finsetSum _ fun i _ ↦ hI1 i, integral_const_mul, hE2]
  simp only [hE1, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Unbiasedness of the sample variance (ST-012).** For `n ≥ 2` pairwise independent square-integrable
random variables with common mean `μ` and common variance `σ²`, the expected value of the sample variance
`s² = ∑ (Xᵢ - X̄)² / (n - 1)` is `σ²`. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem integral_sampleVariance [IsProbabilityMeasure P] (hn : 2 ≤ n) {X : Fin n → Ω → ℝ}
    {μ σ : ℝ} (hL : ∀ i, MemLp (X i) 2 P) (hμ : ∀ i, P[X i] = μ) (hσ : ∀ i, Var[X i; P] = σ ^ 2)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P) :
    ∫ ω, sampleVariance (fun i ↦ X i ω) ∂P = σ ^ 2 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h := integral_sumSqDev (by omega) hL hμ hσ hind
  unfold sampleVariance
  rw [integral_div, h]
  have : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- **The divisor-`n` variance is biased (ST-012).** Under the same hypotheses, the expected value of the
variance of the data with divisor `n` is `(n - 1)/n · σ²`, which is smaller than `σ²` when `σ² > 0`. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem integral_populationVariance [IsProbabilityMeasure P] (hn : 2 ≤ n) {X : Fin n → Ω → ℝ}
    {μ σ : ℝ} (hL : ∀ i, MemLp (X i) 2 P) (hμ : ∀ i, P[X i] = μ) (hσ : ∀ i, Var[X i; P] = σ ^ 2)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P) :
    ∫ ω, populationVariance (fun i ↦ X i ω) ∂P = ((n : ℝ) - 1) / n * σ ^ 2 := by
  have h := integral_sumSqDev (by omega) hL hμ hσ hind
  unfold populationVariance
  rw [integral_div, h]
  ring

/-! ### Difference of two independent sample means -/

/-- **Difference of two sample means (ST-091).** Let `X₁, …, X_{n₁}` and `Y₁, …, Y_{n₂}` be pairwise
independent square-integrable random variables (all `n₁ + n₂` of them), the `Xᵢ` with mean `μ₁` and variance
`σ₁²`, the `Yⱼ` with mean `μ₂` and variance `σ₂²`. Then `x̄₁ - x̄₂` has mean `μ₁ - μ₂` and variance
`σ₁²/n₁ + σ₂²/n₂`. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem sampleMean_diff_moments [IsProbabilityMeasure P] {n₁ n₂ : ℕ} (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂)
    {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ} {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ j, MemLp (Y j) 2 P)
    (hμX : ∀ i, P[X i] = μ₁) (hμY : ∀ j, P[Y j] = μ₂)
    (hσX : ∀ i, Var[X i; P] = σ₁ ^ 2) (hσY : ∀ j, Var[Y j; P] = σ₂ ^ 2)
    (hind : Pairwise fun a b : Fin n₁ ⊕ Fin n₂ ↦ IndepFun (Sum.elim X Y a) (Sum.elim X Y b) P) :
    (∫ ω, (mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω)) ∂P = μ₁ - μ₂) ∧
      Var[fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω); P] = σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂ := by
  have hn₁ : (n₁ : ℝ) ≠ 0 := by positivity
  have hn₂ : (n₂ : ℝ) ≠ 0 := by positivity
  have hW : ∀ a, MemLp (Sum.elim X Y a) 2 P := by
    rintro (i | j)
    exacts [hX i, hY j]
  set c : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim (fun _ ↦ 1 / (n₁ : ℝ)) (fun _ ↦ -(1 / (n₂ : ℝ))) with hc
  have hfun : (fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω)) =
      fun ω ↦ ∑ a, c a * Sum.elim X Y a ω := by
    funext ω
    rw [Fintype.sum_sum_type]
    simp only [hc, Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum]
    unfold mean
    ring
  rw [hfun]
  constructor
  · rw [integral_weighted_sum c hW, Fintype.sum_sum_type]
    simp only [hc, Sum.elim_inl, Sum.elim_inr, hμX, hμY, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    ring
  · rw [variance_weighted_sum c hW hind, Fintype.sum_sum_type]
    simp only [hc, Sum.elim_inl, Sum.elim_inr, hσX, hσY, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp

/-- **Standard deviation of the difference of two sample means (ST-091).** Under the hypotheses of
`sampleMean_diff_moments`, the standard deviation of `x̄₁ - x̄₂` is `√(σ₁²/n₁ + σ₂²/n₂)`. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem sampleMean_diff_stdDev [IsProbabilityMeasure P] {n₁ n₂ : ℕ} (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂)
    {X : Fin n₁ → Ω → ℝ} {Y : Fin n₂ → Ω → ℝ} {μ₁ μ₂ σ₁ σ₂ : ℝ}
    (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ j, MemLp (Y j) 2 P)
    (hμX : ∀ i, P[X i] = μ₁) (hμY : ∀ j, P[Y j] = μ₂)
    (hσX : ∀ i, Var[X i; P] = σ₁ ^ 2) (hσY : ∀ j, Var[Y j; P] = σ₂ ^ 2)
    (hind : Pairwise fun a b : Fin n₁ ⊕ Fin n₂ ↦ IndepFun (Sum.elim X Y a) (Sum.elim X Y b) P) :
    Real.sqrt Var[fun ω ↦ mean (fun i ↦ X i ω) - mean (fun j ↦ Y j ω); P] =
      Real.sqrt (σ₁ ^ 2 / n₁ + σ₂ ^ 2 / n₂) := by
  rw [(sampleMean_diff_moments h₁ h₂ hX hY hμX hμY hσX hσY hind).2]

end Moments

/-! ### Simple random sampling without replacement: variance of the sample mean -/

section SRS

variable {N n : ℕ}

private lemma card_filter_mem_powersetCard {α : Type*} [DecidableEq α] (T : Finset α) {n : ℕ}
    (hn : 1 ≤ n) {i : α} (hi : i ∈ T) :
    ((T.powersetCard n).filter fun S ↦ i ∈ S).card = (T.card - 1).choose (n - 1) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := T.powersetCard n)
    (fun S : Finset α ↦ i ∈ S)
  have h2 : ((T.powersetCard n).filter fun S : Finset α ↦ i ∉ S) = (T.erase i).powersetCard n := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hs, hc⟩, hi'⟩
      exact ⟨fun a ha ↦ Finset.mem_erase.2 ⟨fun h ↦ hi' (h ▸ ha), hs ha⟩, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨fun a ha ↦ Finset.mem_of_mem_erase (hs ha), hc⟩, fun hi' ↦ by simpa using hs hi'⟩
  rw [h2, Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_erase_of_mem hi] at h1
  obtain ⟨t, ht⟩ : ∃ t, T.card = t + 1 :=
    ⟨T.card - 1, by have := Finset.card_pos.2 ⟨i, hi⟩; omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ht] at h1 ⊢
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have hp : (t + 1).choose (m + 1) = t.choose m + t.choose (m + 1) := Nat.choose_succ_succ' t m
  omega

/-- Number of `n`-subsets of `Fin N` containing `i` but not `j` (`i ≠ j`). -/
private lemma card_pair (hn : 1 ≤ n) {i j : Fin N} (hij : i ≠ j) :
    ((powersetCard n (univ : Finset (Fin N))).filter fun S ↦ i ∈ S ∧ j ∉ S).card =
      (N - 2).choose (n - 1) := by
  have e : ((powersetCard n (univ : Finset (Fin N))).filter fun S ↦ i ∈ S ∧ j ∉ S) =
      ((univ.erase j).powersetCard n).filter fun S ↦ i ∈ S := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨hc, hi, hj⟩
      exact ⟨⟨fun a ha ↦ mem_erase.2 ⟨fun h ↦ hj (h ▸ ha), mem_univ _⟩, hc⟩, hi⟩
    · rintro ⟨⟨hs, hc⟩, hi⟩
      exact ⟨hc, hi, fun hj ↦ by simpa using hs hj⟩
  rw [e, card_filter_mem_powersetCard _ hn (mem_erase.2 ⟨hij, mem_univ _⟩),
    card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have : N - 1 - 1 = N - 2 := by omega
  rw [this]

/-- Sum over `n`-subsets of the squared subset sums of a centred family. -/
private lemma sum_sq_subsets (hn : 1 ≤ n) (d : Fin N → ℝ) (hd : ∑ i, d i = 0) :
    ∑ S ∈ powersetCard n (univ : Finset (Fin N)), (∑ i ∈ S, d i) ^ 2 =
      ((N - 2).choose (n - 1) : ℝ) * ∑ i, d i ^ 2 := by
  classical
  set c : ℝ := ((N - 2).choose (n - 1) : ℝ) with hcdef
  have hA : ∀ S : Finset (Fin N), (∑ i ∈ S, d i) ^ 2 =
      -∑ i, ∑ j, (if i ∈ S ∧ j ∉ S then d i * d j else 0) := by
    intro S
    have h1 : ∑ i ∈ S, d i = ∑ i, if i ∈ S then d i else 0 := by
      rw [sum_ite_mem, univ_inter]
    have h2 : ∑ j, (if j ∉ S then d j else 0) = -∑ i ∈ S, d i := by
      have : ∑ j, (if j ∉ S then d j else 0) + ∑ j, (if j ∈ S then d j else 0) = ∑ j, d j := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun j _ ↦ by by_cases h : j ∈ S <;> simp [h]
      rw [h1]
      linarith
    have h3 : ∑ i, ∑ j, (if i ∈ S ∧ j ∉ S then d i * d j else 0) =
        (∑ i ∈ S, d i) * ∑ j, (if j ∉ S then d j else 0) := by
      rw [h1, sum_mul]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]
    rw [h3, h2]
    ring
  have hrow : ∀ i, ∑ j, (if i = j then (0 : ℝ) else c * (d i * d j)) = -(c * d i ^ 2) := by
    intro i
    have : ∀ j, (if i = j then (0 : ℝ) else c * (d i * d j)) =
        c * d i * d j - (if i = j then c * d i * d j else 0) := by
      intro j
      by_cases h : i = j
      · simp [h]
      · simp only [h, ↓reduceIte]
        ring
    simp_rw [this]
    rw [sum_sub_distrib, ← mul_sum, hd, sum_ite_eq]
    simp only [mem_univ, ↓reduceIte]
    ring
  have hcnt : ∀ i j : Fin N, ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
      (if i ∈ S ∧ j ∉ S then d i * d j else 0) = if i = j then 0 else c * (d i * d j) := by
    intro i j
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    by_cases h : i = j
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      rw [card_pair hn h]
  simp_rw [hA]
  rw [sum_neg_distrib]
  have hsw : ∑ S ∈ powersetCard n (univ : Finset (Fin N)), ∑ i, ∑ j,
      (if i ∈ S ∧ j ∉ S then d i * d j else 0) =
      ∑ i, ∑ j, ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
        (if i ∈ S ∧ j ∉ S then d i * d j else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [sum_comm]
  rw [hsw]
  simp_rw [hcnt, hrow]
  rw [sum_neg_distrib, ← mul_sum]
  ring

/-- The integral against the uniform law on `n`-subsets is the average over them. -/
private lemma integral_srsLaw_eq_sum (hnN : n ≤ N) (f : Finset (Fin N) → ℝ) :
    ∫ S, f S ∂srsLaw N n = ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
      ((powersetCard n (univ : Finset (Fin N))).card : ℝ)⁻¹ * f S := by
  rw [srsLaw, Measure.uniformOfFinset, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [integral_smul_measure, integral_dirac]
    simp
  · intro S _
    exact (integrable_dirac (by simp)).smul_measure
      (by simp [Finset.card_powersetCard, (Nat.choose_pos hnN).ne'])

/-- The counting identity `N (N - 1) C(N-2, n-1) = n (N - n) C(N, n)`. -/
private lemma choose_identity (hn : 1 ≤ n) (hnN : n ≤ N) (hN : 2 ≤ N) :
    (N : ℝ) * ((N : ℝ) - 1) * ((N - 2).choose (n - 1) : ℝ) =
      n * ((N : ℝ) - n) * (N.choose n : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hm : m ≤ M + 1 := by omega
  have e1 := congrArg (Nat.cast : ℕ → ℝ) (Nat.add_one_mul_choose_eq (M + 1) m)
  have e2 := congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_succ_eq M m)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hm] at e2
  push_cast at e1 e2 ⊢
  linear_combination ((M : ℝ) + 2) * e2 + ((M : ℝ) + 1 - m) * e1

/-- **Variance of the sample mean under sampling without replacement (ST-063).** For a simple random sample
of size `n` (`1 ≤ n ≤ N`, `N ≥ 2`) from a population `x` of `N` members, the sample mean has variance
`(σ²/n) · (N - n)/(N - 1)`, where `σ² = ∑ (xᵢ - μ)² / N` is the population variance. -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem variance_srsLaw_sampleMean (hn : 1 ≤ n) (hnN : n ≤ N) (hN : 2 ≤ N) (x : Fin N → ℝ) :
    Var[fun S : Finset (Fin N) ↦ (∑ i ∈ S, x i) / n; srsLaw N n] =
      populationVariance x / n * (((N : ℝ) - n) / ((N : ℝ) - 1)) := by
  classical
  have hmean := integral_srsLaw_sampleMean hn hnN x
  have hmeas : Measurable fun S : Finset (Fin N) ↦ (∑ i ∈ S, x i) / n := by
    have : (fun S : Finset (Fin N) ↦ (∑ i ∈ S, x i) / n) =
        fun S ↦ (∑ i, if i ∈ S then x i else 0) / n := by
      funext S
      rw [sum_ite_mem, univ_inter]
    rw [this]
    refine Measurable.div_const (Finset.measurable_sum _ fun i _ ↦ ?_) _
    exact Measurable.ite (measurableSet_mem_finset i) measurable_const
      measurable_const
  rw [variance_eq_integral hmeas.aemeasurable, hmean, integral_srsLaw_eq_sum hnN,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hC : (0 : ℝ) < (N.choose n : ℝ) := by exact_mod_cast Nat.choose_pos hnN
  set d : Fin N → ℝ := fun i ↦ x i - mean x with hd
  have hd0 : ∑ i, d i = 0 := sum_sub_mean x
  have hS : ∀ S ∈ powersetCard n (univ : Finset (Fin N)),
      ((∑ i ∈ S, x i) / n - mean x) ^ 2 = (∑ i ∈ S, d i) ^ 2 / (n : ℝ) ^ 2 := by
    intro S hS'
    have hc := (mem_powersetCard.1 hS').2
    simp only [hd, sum_sub_distrib, sum_const, hc, nsmul_eq_mul]
    field_simp
  rw [sum_congr rfl fun S hS' ↦ by rw [hS S hS']]
  have h2 : ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
      ((N.choose n : ℕ) : ℝ)⁻¹ * ((∑ i ∈ S, d i) ^ 2 / (n : ℝ) ^ 2) =
      ((N.choose n : ℕ) : ℝ)⁻¹ / (n : ℝ) ^ 2 *
        ∑ S ∈ powersetCard n (univ : Finset (Fin N)), (∑ i ∈ S, d i) ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun S _ ↦ by ring
  rw [h2, sum_sq_subsets hn d hd0]
  have hid := choose_identity hn hnN hN
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hc' : ((N - 2).choose (n - 1) : ℝ) =
      n * ((N : ℝ) - n) * (N.choose n : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) := by
    rw [eq_div_iff (by positivity)]
    linarith
  have hpv : populationVariance x = (∑ i, d i ^ 2) / N := rfl
  rw [hc', hpv]
  field_simp

end SRS

end UndergradKB.Statistics
