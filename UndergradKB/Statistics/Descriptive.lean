import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Probability.Independence.Basic
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data

/-!
# Descriptive statistics, sample-size algebra and elementary probability facts
(OpenStax *Introductory Statistics 2e*)
-/

namespace UndergradKB.Statistics

open Finset

variable {n : ℕ}

private lemma ssd_nonneg (x : Fin n → ℝ) : 0 ≤ sumSqDev x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### Frequencies and tabulated data -/

/-- (ST-005) Relative frequencies of the distinct values of a data list sum to one. -/
@[kb "openstaxintrostats2e" "§2.2, p. 86"]
theorem sum_relativeFrequency_eq_one (x : Fin n → ℝ) (hn : 0 < n) :
    ∑ v ∈ (univ : Finset (Fin n)).image x,
      ((univ.filter fun i => x i = v).card : ℝ) / n = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h := Finset.card_eq_sum_card_image x (univ : Finset (Fin n))
  rw [← Finset.sum_div, ← Nat.cast_sum, ← h]
  simp [hn']

/-- (ST-006) Tabulated data: the sum of a data list is the sum of each distinct value times its
frequency, so the mean is `∑ fⱼ vⱼ / ∑ fⱼ` with `∑ fⱼ = n`. -/
@[kb "openstaxintrostats2e" "§2.5, p. 109"]
theorem mean_eq_sum_value_mul_frequency (x : Fin n → ℝ) :
    mean x = (∑ v ∈ (univ : Finset (Fin n)).image x,
      ((univ.filter fun i => x i = v).card : ℝ) * v) / n := by
  unfold mean
  congr 1
  have := Finset.sum_comp (s := (univ : Finset (Fin n))) (fun v : ℝ => v) x
  simpa [nsmul_eq_mul] using this

/-! ### Variance and standard deviation -/

/-- (ST-012) The sample variance is nonnegative. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem sampleVariance_nonneg (x : Fin n → ℝ) (hn : 1 ≤ n) : 0 ≤ sampleVariance x := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (ssd_nonneg x) (by linarith)

/-- (ST-013) The sample standard deviation is zero exactly when all data values are equal. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem sampleStdDev_eq_zero_iff (x : Fin n → ℝ) (hn : 2 ≤ n) :
    sampleStdDev x = 0 ↔ ∀ i j, x i = x j := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : 0 < (n : ℝ) - 1 := by linarith
  have hn0 : 0 < n := by omega
  have key : sumSqDev x = 0 ↔ ∀ i j, x i = x j := by
    constructor
    · intro h i j
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - mean x))).1 h
      have hi := pow_eq_zero_iff (two_ne_zero) |>.1 (hz i (mem_univ i))
      have hj := pow_eq_zero_iff (two_ne_zero) |>.1 (hz j (mem_univ j))
      linarith
    · intro h
      have hm : ∀ i, mean x = x i := by
        intro i
        have hnr : (n : ℝ) ≠ 0 := by positivity
        unfold mean
        rw [sum_congr rfl (fun j _ => h j i)]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      exact sum_eq_zero fun i _ => by rw [hm i]; simp
  rw [← key]
  constructor
  · intro h
    rw [sampleStdDev, Real.sqrt_eq_zero'] at h
    by_contra hne
    have hp : 0 < sumSqDev x := lt_of_le_of_ne (ssd_nonneg x) (Ne.symm hne)
    have : 0 < sampleVariance x := div_pos hp hn'
    linarith
  · intro h
    simp [sampleStdDev, sampleVariance, h]

/-- (ST-012) Computational formula: `σ² = mean(x²) - (mean x)²`. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem populationVariance_eq (x : Fin n → ℝ) (hn : 0 < n) :
    populationVariance x = mean (fun i => x i ^ 2) - mean x ^ 2 := by
  have hnr : (n : ℝ) ≠ 0 := by positivity
  have hS : ∑ i, x i = n * mean x := by unfold mean; field_simp
  have hS2 : ∑ i, x i ^ 2 = n * mean (fun i => x i ^ 2) := by unfold mean; field_simp
  have h : ∀ i, (x i - mean x) ^ 2 = x i ^ 2 - (2 * mean x) * x i + mean x ^ 2 := by
    intro i; ring
  unfold populationVariance sumSqDev
  simp only [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, hS, hS2]
  field_simp
  ring

/-! ### z-scores -/

/-- (ST-014) The z-scores of a data list have mean zero. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem mean_zScore (x : Fin n → ℝ) : mean (fun i => zScore x (x i)) = 0 := by
  show (∑ i, (x i - mean x) / sampleStdDev x) / (n : ℝ) = 0
  rw [← Finset.sum_div, sum_sub_mean x]
  simp

/-- (ST-014) The z-scores of a data list (with positive spread) have sample variance one. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem sampleVariance_zScore (x : Fin n → ℝ) (hn : 2 ≤ n) (hs : 0 < sampleStdDev x) :
    sampleVariance (fun i => zScore x (x i)) = 1 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : 0 < (n : ℝ) - 1 := by linarith
  have hV : sampleStdDev x ^ 2 = sumSqDev x / ((n : ℝ) - 1) :=
    Real.sq_sqrt (div_nonneg (ssd_nonneg x) hn'.le)
  have hz := mean_zScore x
  have h1 : sumSqDev (fun i => zScore x (x i)) = sumSqDev x / sampleStdDev x ^ 2 := by
    unfold sumSqDev
    rw [hz]
    unfold zScore
    simp only [sub_zero, div_pow, ← Finset.sum_div]
  have hS : sumSqDev x ≠ 0 := by
    intro h
    have : 0 < sampleStdDev x ^ 2 := by positivity
    rw [hV, h] at this
    simp at this
  show sumSqDev _ / ((n : ℝ) - 1) = 1
  rw [h1, hV]
  field_simp

/-! ### Chebyshev's inequality for data -/

/-- (ST-015) At most `n / k²` of the data lie at least `k σ` away from the mean. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem chebyshev_data (x : Fin n → ℝ) (k : ℝ) (hk : 0 < k) (hσ : 0 < populationStdDev x) :
    ((univ.filter fun i => k * populationStdDev x ≤ |x i - mean x|).card : ℝ) ≤ n / k ^ 2 := by
  set σ := populationStdDev x with hσdef
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [hσdef, populationStdDev, populationVariance, sumSqDev] at hσ
    · exact h
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ2 : σ ^ 2 = sumSqDev x / n :=
    Real.sq_sqrt (div_nonneg (ssd_nonneg x) hnr.le)
  have hS : sumSqDev x = σ ^ 2 * n := by rw [hσ2]; field_simp
  have hc : (univ.filter fun i => k * σ ≤ |x i - mean x|).card • (k * σ) ^ 2
      ≤ ∑ i ∈ univ.filter (fun i => k * σ ≤ |x i - mean x|), (x i - mean x) ^ 2 := by
    apply Finset.card_nsmul_le_sum
    intro i hi
    have h := (mem_filter.1 hi).2
    have := pow_le_pow_left₀ (by positivity) h 2
    rwa [sq_abs] at this
  have hsub : ∑ i ∈ univ.filter (fun i => k * σ ≤ |x i - mean x|), (x i - mean x) ^ 2
      ≤ sumSqDev x :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  rw [nsmul_eq_mul] at hc
  rw [le_div_iff₀ (by positivity)]
  have hσp : 0 < σ ^ 2 := by positivity
  have : (↑(univ.filter fun i => k * σ ≤ |x i - mean x|).card * k ^ 2) * σ ^ 2 ≤ n * σ ^ 2 := by
    nlinarith
  exact le_of_mul_le_mul_right this hσp

/-- (ST-015) At least `n - n / k²` of the data lie strictly within `k σ` of the mean. -/
@[kb "openstaxintrostats2e" "§2.7, p. 118"]
theorem chebyshev_data_within (x : Fin n → ℝ) (k : ℝ) (hk : 0 < k)
    (hσ : 0 < populationStdDev x) :
    (n : ℝ) - n / k ^ 2
      ≤ ((univ.filter fun i => |x i - mean x| < k * populationStdDev x).card : ℝ) := by
  have h := chebyshev_data x k hk hσ
  have e : (univ.filter fun i => |x i - mean x| < k * populationStdDev x)
      = univ.filter fun i => ¬ (k * populationStdDev x ≤ |x i - mean x|) :=
    filter_congr fun i _ => by simp [not_le]
  have hc := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n))) (fun i => k * populationStdDev x ≤ |x i - mean x|)
  rw [e]
  have : ((univ.filter fun i => k * populationStdDev x ≤ |x i - mean x|).card : ℝ)
      + ((univ.filter fun i => ¬ (k * populationStdDev x ≤ |x i - mean x|)).card : ℝ) = n := by
    exact_mod_cast (by simpa using hc)
  linarith

/-! ### Linear change of data -/

/-- (ST-062) The mean of `a x + b` is `a x̄ + b`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem mean_affine (x : Fin n → ℝ) (a b : ℝ) (hn : 0 < n) :
    mean (fun i => a * x i + b) = a * mean x + b := by
  have : (n : ℝ) ≠ 0 := by positivity
  unfold mean
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma sumSqDev_affine (x : Fin n → ℝ) (a b : ℝ) :
    sumSqDev (fun i => a * x i + b) = a ^ 2 * sumSqDev x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sumSqDev]
  unfold sumSqDev
  rw [mean_affine x a b hn, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- (ST-062) The sample standard deviation of `a x + b` is `|a| s`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem sampleStdDev_affine (x : Fin n → ℝ) (a b : ℝ) :
    sampleStdDev (fun i => a * x i + b) = |a| * sampleStdDev x := by
  unfold sampleStdDev sampleVariance
  rw [sumSqDev_affine, mul_div_assoc, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-! ### Sample-size algebra -/

/-- (ST-073) If `n ≥ z²σ²/E²`, the margin of error `z σ / √n` is at most `E`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem margin_le_of_sampleSize (z σ E : ℝ) (n : ℕ) (hz : 0 < z) (hσ : 0 < σ) (hE : 0 < E)
    (hn : z ^ 2 * σ ^ 2 / E ^ 2 ≤ n) : z * σ / Real.sqrt n ≤ E := by
  have hpos : 0 < z ^ 2 * σ ^ 2 / E ^ 2 := by positivity
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hpos hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have h1 : z * σ / E ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, mul_pow]; exact hn
  rw [div_le_iff₀ hE] at h1
  rw [div_le_iff₀ hsq]
  linarith

/-- (ST-079) If `n ≥ z² p q / E²`, the margin `z √(p q / n)` is at most `E`. -/
@[kb "openstaxintrostats2e" "§8.3, p. 431"]
theorem proportion_margin_le_of_sampleSize (z p q E : ℝ) (n : ℕ) (hz : 0 < z) (hpq : 0 ≤ p * q)
    (hE : 0 < E) (hn : z ^ 2 * (p * q) / E ^ 2 ≤ n) : z * Real.sqrt (p * q / n) ≤ E := by
  have h1 : Real.sqrt (p * q / n) ≤ E / z := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp; positivity
    · have h0' : (0 : ℝ) < n := by exact_mod_cast h0
      rw [div_le_iff₀ (by positivity)] at hn
      rw [div_pow, div_le_div_iff₀ h0' (by positivity)]
      have : p * q * z ^ 2 ≤ E ^ 2 * n := by linarith
      exact this
  rw [le_div_iff₀ hz] at h1
  linarith

/-- (ST-079) `p (1 - p) ≤ 1/4`. -/
@[kb "openstaxintrostats2e" "§8.3, p. 431"]
theorem mul_one_sub_le_quarter (p : ℝ) : p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

/-- (ST-079) The conservative rule `p' = 0.5`: `n ≥ z² / (4E²)` suffices for every `p`. -/
@[kb "openstaxintrostats2e" "§8.3, p. 431"]
theorem proportion_margin_le_of_conservative (z p E : ℝ) (n : ℕ) (hz : 0 < z) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hE : 0 < E) (hn : z ^ 2 / (4 * E ^ 2) ≤ n) :
    z * Real.sqrt (p * (1 - p) / n) ≤ E := by
  apply proportion_margin_le_of_sampleSize z p (1 - p) E n hz
    (mul_nonneg hp0 (by linarith)) hE
  refine le_trans ?_ hn
  have h := mul_one_sub_le_quarter p
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ z ^ 2 * E ^ 2 := by positivity
  nlinarith

/-! ### Probability: independence -/

open MeasureTheory ProbabilityTheory

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {A B : Set Ω}

/-- (ST-027) Mutually exclusive events of positive probability are not independent. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem not_indepSet_of_disjoint (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B) (hpA : 0 < μ A) (hpB : 0 < μ B) : ¬ IndepSet A B μ := by
  rw [indepSet_iff_measure_inter_eq_mul hA hB μ, hd.inter_eq]
  simp only [measure_empty]
  exact fun h => (ENNReal.mul_pos hpA.ne' hpB.ne').ne h

/-- If `A` and `B` are independent, so are `A` and `Bᶜ`. -/
theorem IndepSet_compl_right' (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : IndepSet A B μ) : IndepSet A Bᶜ μ := by
  rw [indepSet_iff_measure_inter_eq_mul hA hB.compl μ]
  rw [indepSet_iff_measure_inter_eq_mul hA hB μ] at h
  have h1 : μ (A ∩ B) + μ (A \ B) = μ A := measure_inter_add_sdiff A hB
  have h2 : μ B + μ Bᶜ = 1 := by rw [measure_add_measure_compl hB]; exact measure_univ
  rw [← Set.sdiff_eq]
  have h3 : μ A * μ B + μ A * μ Bᶜ = μ A := by rw [← mul_add, h2, mul_one]
  rw [h] at h1
  have hfin : μ A * μ B ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)
  exact (ENNReal.add_right_inj hfin).1 (h1.trans h3.symm)

/-- (ST-028) If `A` and `B` are independent, so are `A` and `Bᶜ`. -/
@[kb "openstaxintrostats2e" "§3.3, p. 190"]
theorem indepSet_compl_right_of_indepSet (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : IndepSet A B μ) : IndepSet A Bᶜ μ :=
  IndepSet_compl_right' μ hA hB h

/-- (ST-028) If `A` and `B` are independent, so are `Aᶜ` and `Bᶜ`. -/
@[kb "openstaxintrostats2e" "§3.3, p. 190"]
theorem indepSet_compl_compl_of_indepSet (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : IndepSet A B μ) : IndepSet Aᶜ Bᶜ μ := by
  have h1 := IndepSet_compl_right' μ hA hB h
  have h2 := IndepSet_compl_right' μ hB.compl hA h1.symm
  exact h2.symm

end Prob

end UndergradKB.Statistics
