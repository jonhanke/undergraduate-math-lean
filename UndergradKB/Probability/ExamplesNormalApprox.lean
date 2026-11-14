import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.LocalLimit
import UndergradKB.Probability.Moments

/-! # Probability: worked examples on the normal approximation (Grinstead–Snell, Chapters 2, 5, 9)

Example 5.8 (a normal variable within two standard deviations), the moment computations behind the
central limit theorem applications (Examples 2.5, 9.3, 9.5, 9.6, 9.7, 9.8), and polls and the
surveyor (Examples 9.4 and 9.10). The book's decimals (`.9544`, `.9670`, `.1772`, `.997`) come from
tables of the normal distribution function; they are proved as certified brackets in
`NormalTable.lean`. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace UndergradKB.Probability

/-! ## Example 5.8 (PR-200) -/

section NormalWithinTwo

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

instance normalApprox_nullSingleton : NullSingletonClass (gaussianReal 0 1) :=
  ⟨fun x => gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)⟩

/-- The standard normal distribution function is symmetric: `Φ(-a) = 1 - Φ(a)`. -/
theorem normalApprox_cdf_neg (a : ℝ) :
    cdf (gaussianReal 0 1) (-a) = 1 - cdf (gaussianReal 0 1) a := by
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := 0) (v := 1)
  rw [cdf_eq_real, cdf_eq_real]
  have h1 : (gaussianReal 0 1).real (Iic (-a)) = (gaussianReal 0 1).real (Ici a) := by
    conv_lhs => rw [← hneg]
    rw [measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic, measureReal_def]
    congr 2
    ext x
    simp
  rw [h1, ← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio]
  rw [measureReal_congr Iio_ae_eq_Iic]

/-- Grinstead–Snell Example 5.8 (PR-200). If `X` is normal with mean `10` and variance `9` (standard
deviation `3`), then `P(4 ≤ X ≤ 16) = Φ(2) - Φ(-2) = 2 Φ(2) - 1`, where `Φ` is the distribution
function of the standard normal law. (The book's numerical value `.9544` is read from a table; it is
proved as a bracket in `normal_within_two_sd_value`.) -/
@[kb "grinsteadsnell2006" "Example 5.8, p. 222"]
theorem normal_within_two_sd (hX : HasLaw X (gaussianReal 10 9) P) :
    P.real {ω | 4 ≤ X ω ∧ X ω ≤ 16} =
        cdf (gaussianReal 0 1) 2 - cdf (gaussianReal 0 1) (-2) ∧
      cdf (gaussianReal 0 1) 2 - cdf (gaussianReal 0 1) (-2) =
        2 * cdf (gaussianReal 0 1) 2 - 1 := by
  have h9 : (9 : ℝ≥0) = (3 : ℝ≥0) ^ 2 := by norm_num
  rw [h9] at hX
  have hZ := hasLaw_gaussian_standardize (σ := 3) (by norm_num) hX
  have hset : {ω | 4 ≤ X ω ∧ X ω ≤ 16} =
      {ω | (fun x : ℝ => -2 ≤ x ∧ x ≤ 2) ((X ω - 10) / ((3 : ℝ≥0) : ℝ))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, NNReal.coe_ofNat]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [le_div_iff₀ (by norm_num)]; linarith,
        by rw [div_le_iff₀ (by norm_num)]; linarith⟩
    · rintro ⟨h1, h2⟩
      rw [le_div_iff₀ (by norm_num)] at h1
      rw [div_le_iff₀ (by norm_num)] at h2
      exact ⟨by linarith, by linarith⟩
  have hreal : P.real {ω | 4 ≤ X ω ∧ X ω ≤ 16} = (gaussianReal 0 1).real (Icc (-2) 2) := by
    rw [hset, hZ.measureReal_eq (p := fun x : ℝ => -2 ≤ x ∧ x ≤ 2) (measurableSet_Icc : MeasurableSet (Set.Icc (-2 : ℝ) 2))]
    rfl
  have hdiff : Iic (2 : ℝ) \ Iic (-2) = Ioc (-2) 2 := by
    ext x; simp
  have hIcc : (gaussianReal 0 1).real (Icc (-2) 2) =
      cdf (gaussianReal 0 1) 2 - cdf (gaussianReal 0 1) (-2) := by
    rw [cdf_eq_real, cdf_eq_real, ← measureReal_congr Ioc_ae_eq_Icc, ← hdiff,
      measureReal_sdiff (Iic_subset_Iic.2 (by norm_num)) measurableSet_Iic]
  refine ⟨hreal.trans hIcc, ?_⟩
  rw [normalApprox_cdf_neg]
  ring

end NormalWithinTwo

/-! ## Examples 2.5, 9.3, 9.5, 9.6, 9.7, 9.8 (PR-205) -/

section IidMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Examples 9.7 and 9.8 (PR-205), general form. For independent square-integrable
`X 0, …, X (n-1)` with common mean `μ` and variance `σ² > 0` (`n ≥ 1`), the sum `S_n` has mean `n μ`
and variance `n σ²`, and the standardized sum `S_n* = (S_n - n μ) / (√n σ)` has mean `0` and
variance `1`. -/
theorem iid_standardized_sum_mean_variance {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) {μ σ : ℝ} (hσ : 0 < σ) (hμ : ∀ i, P[X i] = μ)
    (hv : ∀ i, Var[X i; P] = σ ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    P[fun ω => ∑ i ∈ Finset.range n, X i ω] = n * μ ∧
    Var[fun ω => ∑ i ∈ Finset.range n, X i ω; P] = n * σ ^ 2 ∧
    P[fun ω => ((∑ i ∈ Finset.range n, X i ω) - n * μ) / (√n * σ)] = 0 ∧
    Var[fun ω => ((∑ i ∈ Finset.range n, X i ω) - n * μ) / (√n * σ); P] = 1 := by
  obtain ⟨h1, h2⟩ := sum_mean_variance hind hL2 hμ hv n
  have e : (∑ i ∈ Finset.range n, X i) = fun ω => ∑ i ∈ Finset.range n, X i ω := by
    funext ω; simp
  rw [e] at h1 h2
  have hS : MemLp (fun ω => ∑ i ∈ Finset.range n, X i ω) 2 P := by
    rw [← e]; exact memLp_finsetSum' _ (fun i _ => hL2 i)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < √(n : ℝ) * σ := by positivity
  refine ⟨h1, h2, integral_standardize hS h1, variance_standardize hS hpos ?_⟩
  rw [h2, mul_pow, Real.sq_sqrt hnR.le]

/-- A real variable with nonzero variance is square integrable (the variance of a non-`L²` variable
is `0` in Mathlib). -/
theorem memLp_of_variance_ne_zero {X : Ω → ℝ} (hm : AEStronglyMeasurable X P)
    (hv : Var[X; P] ≠ 0) : MemLp X 2 P := by
  by_contra h
  exact hv (variance_of_not_memLp hm h)

/-- Grinstead–Snell Example 2.5 (PR-205). The sum of `100` independent numbers chosen uniformly in
`[0, 1]` has mean `50` and variance `100/12`. -/
@[kb "grinsteadsnell2006" "Example 2.5, p. 55"]
theorem hundred_uniform_sum_moments {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hU : ∀ i, pdf.IsUniform (X i) (Icc (0 : ℝ) 1) P) :
    P[fun ω => ∑ i ∈ Finset.range 100, X i ω] = 50 ∧
      Var[fun ω => ∑ i ∈ Finset.range 100, X i ω; P] = 100 / 12 := by
  have hL2 : ∀ i, MemLp (X i) 2 P := fun i =>
    memLp_of_variance_ne_zero (hU i).aemeasurable.aestronglyMeasurable
      (by rw [variance_of_isUniform_Icc (hU i)]; norm_num)
  obtain ⟨h1, h2, -, -⟩ := iid_standardized_sum_mean_variance hind hL2
    (μ := 1 / 2) (σ := √(1 / 12)) (by positivity) (fun i => integral_of_isUniform_Icc (hU i))
    (fun i => by rw [variance_of_isUniform_Icc (hU i), Real.sq_sqrt (by norm_num)]) (n := 100)
    (by norm_num)
  rw [Real.sq_sqrt (by norm_num)] at h2
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num⟩

/-- Grinstead–Snell Example 9.7 (PR-205). For `n ≥ 1` independent numbers uniform in `[0, 1]`
(`μ = 1/2`, `σ² = 1/12`), the sum has mean `n/2` and variance `n/12`, and the standardized sum
`S_n* = (S_n - n/2) / (√n √(1/12))` has mean `0` and variance `1`. -/
@[kb "grinsteadsnell2006" "Example 9.7, p. 364"]
theorem uniform_standardized_sum {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hU : ∀ i, pdf.IsUniform (X i) (Icc (0 : ℝ) 1) P) {n : ℕ} (hn : 1 ≤ n) :
    P[fun ω => ∑ i ∈ Finset.range n, X i ω] = (n : ℝ) / 2 ∧
      Var[fun ω => ∑ i ∈ Finset.range n, X i ω; P] = (n : ℝ) / 12 ∧
      P[fun ω => ((∑ i ∈ Finset.range n, X i ω) - n * (1 / 2)) / (√n * √(1 / 12))] = 0 ∧
      Var[fun ω => ((∑ i ∈ Finset.range n, X i ω) - n * (1 / 2)) / (√n * √(1 / 12)); P] = 1 := by
  have hL2 : ∀ i, MemLp (X i) 2 P := fun i =>
    memLp_of_variance_ne_zero (hU i).aemeasurable.aestronglyMeasurable
      (by rw [variance_of_isUniform_Icc (hU i)]; norm_num)
  obtain ⟨h1, h2, h3, h4⟩ := iid_standardized_sum_mean_variance hind hL2
    (μ := 1 / 2) (σ := √(1 / 12)) (by positivity) (fun i => integral_of_isUniform_Icc (hU i))
    (fun i => by rw [variance_of_isUniform_Icc (hU i), Real.sq_sqrt (by norm_num)]) hn
  rw [Real.sq_sqrt (by norm_num)] at h2
  exact ⟨by rw [h1]; ring, by rw [h2]; ring, h3, h4⟩

/-- Grinstead–Snell Example 9.8 (PR-205). For `n ≥ 1` independent exponential variables with rate
`λ > 0` (`μ = σ = 1/λ`), the sum has mean `n/λ` and variance `n/λ²`, and the standardized sum
`S_n* = (S_n - n/λ) / (√n /λ)` has mean `0` and variance `1`. -/
@[kb "grinsteadsnell2006" "Example 9.8, p. 364"]
theorem exponential_standardized_sum {X : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r) (hind : iIndepFun X P)
    (hE : ∀ i, HasLaw (X i) (expMeasure r) P) {n : ℕ} (hn : 1 ≤ n) :
    P[fun ω => ∑ i ∈ Finset.range n, X i ω] = n * (1 / r) ∧
      Var[fun ω => ∑ i ∈ Finset.range n, X i ω; P] = n * (1 / r) ^ 2 ∧
      P[fun ω => ((∑ i ∈ Finset.range n, X i ω) - n * (1 / r)) / (√n * (1 / r))] = 0 ∧
      Var[fun ω => ((∑ i ∈ Finset.range n, X i ω) - n * (1 / r)) / (√n * (1 / r)); P] = 1 := by
  have hv : ∀ i, Var[X i; P] = (1 / r) ^ 2 := fun i => by
    rw [(hE i).variance_eq, variance_expMeasure hr, one_div_pow]
  have hL2 : ∀ i, MemLp (X i) 2 P := fun i =>
    memLp_of_variance_ne_zero (hE i).aemeasurable.aestronglyMeasurable
      (by rw [hv i]; positivity)
  exact iid_standardized_sum_mean_variance hind hL2 (μ := 1 / r) (σ := 1 / r) (by positivity)
    (fun i => by rw [(hE i).integral_eq, integral_expMeasure hr]) hv hn

/-- Grinstead–Snell Example 9.3 (PR-205). The acceptances of `1700` applicants, each accepting with
probability `.6` independently (Bernoulli trials), have mean `1020` and variance `408` (so a standard
deviation `√408`, about `20`: `20 < √408 < 20.2`). -/
@[kb "grinsteadsnell2006" "Example 9.3, p. 340"]
theorem dartmouth_acceptances_moments {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hB : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 ⟨3 / 5, by constructor <;> norm_num⟩) P) :
    P[fun ω => ∑ i ∈ Finset.range 1700, X i ω] = 1020 ∧
      Var[fun ω => ∑ i ∈ Finset.range 1700, X i ω; P] = 408 ∧ 20 < √408 ∧ √408 < 101 / 5 := by
  have hm := fun i => bernoulli_mean_variance (hB i)
  have e : (∑ i ∈ Finset.range 1700, X i) = fun ω => ∑ i ∈ Finset.range 1700, X i ω := by
    funext ω; simp
  obtain ⟨h1, h2⟩ := sum_mean_variance hind (fun i => bernoulli_memLp (hB i))
    (μ := 3 / 5) (σ2 := 3 / 5 * (1 - 3 / 5)) (fun i => (hm i).1) (fun i => (hm i).2) 1700
  rw [e] at h1 h2
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, ?_, ?_⟩
  · exact Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

end IidMoments

section FiniteLaws

/-- Mean `∑ v i · m i` of a finite law putting mass `m i` on the value `v i`, `i ∈ s`. -/
def finMean {ι : Type*} (s : Finset ι) (v m : ι → ℝ) : ℝ := ∑ i ∈ s, v i * m i

/-- Variance `∑ (v i - μ)² m i` of a finite law putting mass `m i` on the value `v i`, `i ∈ s`. -/
noncomputable def finVar {ι : Type*} (s : Finset ι) (v m : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (v i - finMean s v m) ^ 2 * m i

/-- Grinstead–Snell Example 9.5 (PR-205). A fair die (faces `1..6`, mass `1/6` each) has mean `7/2`
and variance `35/12`; hence the sum of `420` independent rolls has mean `420 · 7/2 = 1470`, variance
`420 · 35/12 = 1225` and standard deviation `√1225 = 35`. -/
@[kb "grinsteadsnell2006" "Example 9.5, p. 351"]
theorem die_sum_moments :
    finMean Finset.univ (fun i : Fin 6 => ((i : ℕ) : ℝ) + 1) (fun _ => 1 / 6) = 7 / 2 ∧
      finVar Finset.univ (fun i : Fin 6 => ((i : ℕ) : ℝ) + 1) (fun _ => 1 / 6) = 35 / 12 ∧
      (420 : ℝ) * (7 / 2) = 1470 ∧ (420 : ℝ) * (35 / 12) = 1225 ∧ √(1225 : ℝ) = 35 := by
  have hm : finMean Finset.univ (fun i : Fin 6 => ((i : ℕ) : ℝ) + 1) (fun _ => 1 / 6) = 7 / 2 := by
    simp [finMean, Fin.sum_univ_succ]; norm_num
  refine ⟨hm, ?_, by norm_num, by norm_num, ?_⟩
  · unfold finVar; rw [hm]; simp [Fin.sum_univ_succ]; norm_num
  · rw [show (1225 : ℝ) = 35 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

/-- The grading error `k ∈ {-5, …, 5}` of Example 9.6 (index `i` stands for `k = i - 5`). -/
noncomputable def gradingErrorValue (i : Fin 11) : ℝ := ((i : ℕ) : ℝ) - 5

/-- The grading error law of Example 9.6 with `p = 1/20`: error `k ≠ 0` has probability `|p/k|`, and
no error has probability `1 - (137/30) p = 463/600`. -/
noncomputable def gradingErrorMass (i : Fin 11) : ℝ :=
  if (i : ℕ) = 5 then 463 / 600 else (1 / 20) / |gradingErrorValue i|

/-- Grinstead–Snell Example 9.6 (PR-205). The grading error law (`±1, …, ±5` with probabilities
`|p/k|`, `p = 1/20`, and `0` with probability `463/600`) has total mass `1`, mean `0` and variance
`3/2` (as the book says); the sum of the errors in `30` courses has mean `0` and variance
`30 · 3/2 = 45`, and the book's threshold `1.5/√45` is `.2235 < 1.5/√45 < .2237` (about `.224`). -/
@[kb "grinsteadsnell2006" "Example 9.6, p. 351"]
theorem grading_error_moments :
    ∑ i, gradingErrorMass i = 1 ∧
      finMean Finset.univ gradingErrorValue gradingErrorMass = 0 ∧
      finVar Finset.univ gradingErrorValue gradingErrorMass = 3 / 2 ∧
      (30 : ℝ) * 0 = 0 ∧ (30 : ℝ) * (3 / 2) = 45 ∧
      0.2235 < (3 / 2) / √45 ∧ (3 / 2) / √45 < 0.2237 := by
  have hm : finMean Finset.univ gradingErrorValue gradingErrorMass = 0 := by
    simp [finMean, gradingErrorValue, gradingErrorMass, Fin.sum_univ_succ]
    norm_num
  refine ⟨?_, hm, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · simp [gradingErrorValue, gradingErrorMass, Fin.sum_univ_succ]
    norm_num
  · unfold finVar; rw [hm]
    simp [gradingErrorValue, gradingErrorMass, Fin.sum_univ_succ]
    norm_num
  · rw [lt_div_iff₀ (by positivity), ← lt_div_iff₀' (by norm_num)]
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  · rw [div_lt_iff₀ (by positivity), ← div_lt_iff₀' (by norm_num)]
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)

end FiniteLaws

/-! ## Examples 9.4 and 9.10 (PR-206) -/

section Polls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Example 9.4 (PR-206). For `n ≥ 1` independent Bernoulli(`p`) answers, the sample
proportion `p̄ = S_n / n` has mean `p` and variance `p q / n` with `q = 1 - p`, and its standard
deviation is `√(p q / n) ≤ 1 / (2 √n)`. -/
@[kb "grinsteadsnell2006" "Example 9.4, p. 341"]
theorem poll_proportion_mean_variance {X : ℕ → Ω → ℝ} {p : unitInterval} (hind : iIndepFun X P)
    (hB : ∀ i, HasLaw (X i) (bernoulliMeasure (1 : ℝ) 0 p) P) {n : ℕ} (hn : 1 ≤ n) :
    P[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i] = (p : ℝ) ∧
      Var[(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i; P] = (p : ℝ) * (1 - p) / n ∧
      √((p : ℝ) * (1 - p) / n) ≤ 1 / (2 * √n) := by
  have hm := fun i => bernoulli_mean_variance (hB i)
  obtain ⟨h1, h2⟩ := average_mean_variance hind (fun i => bernoulli_memLp (hB i))
    (fun i => (hm i).1) (fun i => (hm i).2) hn
  refine ⟨h1, h2, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpq : (p : ℝ) * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg ((p : ℝ) - 1 / 2)]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc (p : ℝ) * (1 - p) / n ≤ (1 / 4) / n := by gcongr
    _ = (1 / (2 * √n)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hnR.le]; field_simp; norm_num

/-- Grinstead–Snell Example 9.4 (PR-206), the confidence interval. For every `p̄` and `n ≥ 1`, the
95 percent interval `p̄ ± 2 √(p̄ q̄ / n)` has length `4 √(p̄ q̄ / n) ≤ 2 / √n`. -/
@[kb "grinsteadsnell2006" "Example 9.4, p. 341"]
theorem poll_interval_length (pbar : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    4 * √(pbar * (1 - pbar) / n) ≤ 2 / √n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpq : pbar * (1 - pbar) ≤ 1 / 4 := by nlinarith [sq_nonneg (pbar - 1 / 2)]
  have h : √(pbar * (1 - pbar) / n) ≤ 1 / (2 * √n) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc pbar * (1 - pbar) / n ≤ (1 / 4) / n := by gcongr
      _ = (1 / (2 * √n)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hnR.le]; field_simp; norm_num
  calc 4 * √(pbar * (1 - pbar) / n) ≤ 4 * (1 / (2 * √n)) := by gcongr
    _ = 2 / √n := by field_simp; norm_num

/-- Grinstead–Snell Example 9.4 (PR-206), the sample size for a 95 percent interval of length `6`
percent. For `n ≥ 1`, `1/√n ≤ .03` holds exactly when `n ≥ 1112` (the book writes `n ≥ 1111`, which is
off by one: `1/√1111 > .03`), and then every interval `p̄ ± 2 √(p̄ q̄ / n)` has length at most `.06`. -/
@[kb "grinsteadsnell2006" "Example 9.4, p. 341"]
theorem poll_sample_size {n : ℕ} (hn : 1 ≤ n) :
    (1 / √n ≤ 3 / 100 ↔ 1112 ≤ n) ∧
      (1112 ≤ n → ∀ pbar : ℝ, 4 * √(pbar * (1 - pbar) / n) ≤ 6 / 100) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hiff : 1 / √n ≤ 3 / 100 ↔ 1112 ≤ n := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hnR), ← div_le_iff₀' (by norm_num),
      Real.le_sqrt' (by norm_num)]
    constructor
    · intro h
      by_contra hlt
      have : (n : ℝ) ≤ 1111 := by exact_mod_cast (by omega : n ≤ 1111)
      norm_num at h
      linarith
    · intro h
      have : (1112 : ℝ) ≤ n := by exact_mod_cast h
      norm_num
      linarith
  refine ⟨hiff, fun h pbar => ?_⟩
  have h2 := poll_interval_length pbar hn
  have h3 : 1 / √n ≤ 3 / 100 := hiff.2 h
  have : 2 / √(n : ℝ) = 2 * (1 / √n) := by ring
  linarith

/-- Grinstead–Snell Example 9.10 (PR-206). For the surveyor with `σ = .0002` and `n = 36`, with
`S_n* = (S_n - 36 μ) / (√36 σ)`: the event `|S_n/36 - μ| < .0001` is the event `|S_n*| < 3` (the book's
statement, which uses the tolerance `.0001` of Example 9.9; the book's text says `.0002`), while the
event `|S_n/36 - μ| < .0002` is `|S_n*| < 6`. -/
@[kb "grinsteadsnell2006" "Example 9.10, p. 367"]
theorem surveyor_event_standardized {Ω' : Type*} (S : Ω' → ℝ) (μ : ℝ) :
    {ω | |S ω / 36 - μ| < 1 / 10000} =
        {ω | |(S ω - 36 * μ) / (√36 * (2 / 10000))| < 3} ∧
      {ω | |S ω / 36 - μ| < 2 / 10000} =
        {ω | |(S ω - 36 * μ) / (√36 * (2 / 10000))| < 6} := by
  have h6 : √(36 : ℝ) = 6 := by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have key : ∀ x : ℝ, (x - 36 * μ) / (6 * (2 / 10000)) = 30000 * (x / 36 - μ) := fun x => by
    field_simp; ring
  rw [h6]
  constructor <;> ext ω <;> simp only [Set.mem_ofPred_eq, key, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 30000)]
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

end Polls

end UndergradKB.Probability
