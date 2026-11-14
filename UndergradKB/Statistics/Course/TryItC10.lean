import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Welch
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.Course.ExamplesC10

/-!
# "Try It" exercises, chapter 10 (OpenStax *Introductory Statistics 2e*): hypothesis tests with two samples

Test statistics of the Try It exercises of chapter 10, computed from the given data with the
definitions of `ExamplesC10`: the Welch statistic `welchT` (also used, with true variances, as the
`z` statistic for known standard deviations), the pooled two-proportion statistic `pooledZ` and the
paired statistic `pairedT`; the Welch degrees of freedom `welchDF` are proved as two-sided bounds.
Normal `p`-values are proved as two-sided bounds (or bounded through the proved critical values
`1.645`, `1.96`, `2.576`). Student `t` critical values are values of a standard table (the book links to external tables) (quoted, not
proved) and are only used for the reject / do-not-reject decision.
-/

namespace UndergradKB.Statistics.Course.TryItC10

open UndergradKB.Statistics UndergradKB.Statistics.Course.ExamplesC10 MeasureTheory ProbabilityTheory
  Real Set

local notation "Φ" => cdf (gaussianReal 0 1)

/-! ### Helpers -/

private lemma pos_bounds {c x a b L U : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b) (h1 : a ^ 2 < x)
    (h2 : x < b ^ 2) (hL : L * b < c) (hU : c < U * a) : L < c / √x ∧ c / √x < U := by
  have s1 : a < √x := (Real.lt_sqrt ha.le).2 h1
  have s2 : √x < b := (Real.sqrt_lt' hb).2 h2
  have hp : 0 < √x := by linarith
  have hU0 : 0 ≤ U := by
    by_contra h
    have h' : U < 0 := not_le.mp h
    nlinarith
  constructor
  · rw [lt_div_iff₀ hp]
    rcases le_total 0 L with h | h
    · nlinarith [mul_le_mul_of_nonneg_left s2.le h]
    · nlinarith
  · rw [div_lt_iff₀ hp]
    nlinarith [mul_le_mul_of_nonneg_left s1.le hU0]

private lemma neg_bounds {c x a b L U : ℝ} (hc : c ≤ 0) (ha : 0 < a) (hb : 0 < b) (h1 : a ^ 2 < x)
    (h2 : x < b ^ 2) (hL : L * a < c) (hU : c < U * b) : L < c / √x ∧ c / √x < U := by
  have := pos_bounds (c := -c) (x := x) (a := a) (b := b) (L := -U) (U := -L) (by linarith) ha hb h1 h2
    (by linarith) (by linarith)
  rw [neg_div] at this
  constructor <;> linarith [this.1, this.2]

private lemma Phi_ge {z k c : ℝ} (hk : 0 ≤ k) (hkz : k ≤ z)
    (hc : c < (gaussianReal 0 1).real (Ioo (-k) k)) : 1 / 2 + c / 2 < Φ z := by
  have h1 := stdNormalCdf_eq_Ioo hk
  have h2 := monotone_cdf (gaussianReal 0 1) hkz
  linarith

private lemma Phi_le {z k c : ℝ} (hk : 0 ≤ k) (hzk : z ≤ k)
    (hc : (gaussianReal 0 1).real (Ioo (-k) k) < c) : Φ z < 1 / 2 + c / 2 := by
  have h1 := stdNormalCdf_eq_Ioo hk
  have h2 := monotone_cdf (gaussianReal 0 1) hzk
  linarith

/-- If `z ≥ 1.96` the right tail `1 - Φ z` is below `0.0251`. -/
private lemma tail_196 {z : ℝ} (h : 1.96 ≤ z) : 1 - Φ z < 0.0251 := by
  obtain ⟨_, ⟨h1, _⟩, _⟩ := critical_values_stdNormalCdf
  have := monotone_cdf (gaussianReal 0 1) h
  linarith

/-- If `z ≤ -2.576` the left tail `Φ z` is below `0.0051`. -/
private lemma tail_2576 {z : ℝ} (h : z ≤ -2.576) : Φ z < 0.0051 := by
  obtain ⟨_, _, ⟨h1, _⟩⟩ := critical_values_stdNormalCdf
  have := monotone_cdf (gaussianReal 0 1) (neg_le_neg h)
  have h3 := stdNormalCdf_neg z
  rw [neg_neg] at this
  have h4 := stdNormalCdf_neg (-z)
  rw [neg_neg] at h4
  linarith

/-! ### Section 10.1: two means, unknown standard deviations -/

/-- OpenStax Introductory Statistics 2e Try It 10.1. Population A (`n = 25`, mean `5`, standard
deviation `1`) against population B (`n = 16`, mean `4.7`, standard deviation `1.2`), two-sided at
`5%`. The Welch statistic lies strictly between `0.83205` and `0.83206`; the Welch degrees of freedom
strictly between `27.85` and `27.86`. The statistic is below a standard `t`-table critical value
`2.052` (`27` degrees of freedom, a table value, not proved): do not reject. -/
@[kb "openstaxintrostats2e" "Try It 10.1, p. 526"]
theorem tryit_10_1_two_populations :
    (0.83205 < welchT 5 4.7 (1 ^ 2) (1.2 ^ 2) 25 16 ∧ welchT 5 4.7 (1 ^ 2) (1.2 ^ 2) 25 16 < 0.83206) ∧
      (27.85 < welchDF (1 ^ 2) (1.2 ^ 2) 25 16 ∧ welchDF (1 ^ 2) (1.2 ^ 2) 25 16 < 27.86) ∧
      |welchT 5 4.7 (1 ^ 2) (1.2 ^ 2) 25 16| < 2.052 := by
  have e : welchT 5 4.7 (1 ^ 2) (1.2 ^ 2) 25 16 = (3 / 10) / √(13 / 100) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 3 / 10) (x := 13 / 100) (a := 0.3605551) (b := 0.3605552) (L := 0.83205)
    (U := 0.83206) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ⟨?_, ?_⟩, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num
  · rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]

/-- OpenStax Introductory Statistics 2e Try It 10.2. Company A (`n = 15`, mean `5`, standard deviation
`1.2`) against company B (`n = 20`, mean `4.5`, standard deviation `0.8`); the standard deviations are
sample values, so the Welch `t` test applies. The statistic lies strictly between `1.39754` and
`1.39755`, the degrees of freedom strictly between `23.00` and `23.01`. The statistic is below the
right-tail `5%` critical value `1.714` of a standard `t` table (`23` degrees of freedom, a table value):
do not reject. -/
@[kb "openstaxintrostats2e" "Try It 10.2, p. 528"]
theorem tryit_10_2_company_tenure :
    (1.39754 < welchT 5 4.5 (1.2 ^ 2) (0.8 ^ 2) 15 20 ∧
        welchT 5 4.5 (1.2 ^ 2) (0.8 ^ 2) 15 20 < 1.39755) ∧
      (23.00 < welchDF (1.2 ^ 2) (0.8 ^ 2) 15 20 ∧ welchDF (1.2 ^ 2) (0.8 ^ 2) 15 20 < 23.01) ∧
      welchT 5 4.5 (1.2 ^ 2) (0.8 ^ 2) 15 20 < 1.714 := by
  have e : welchT 5 4.5 (1.2 ^ 2) (0.8 ^ 2) 15 20 = (1 / 2) / √(16 / 125) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 1 / 2) (x := 16 / 125) (a := 0.3577708) (b := 0.3577709) (L := 1.39754)
    (U := 1.39755) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ⟨?_, ?_⟩, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num
  · linarith [hz.2]

/-- Final-exam scores of Professor A (Try It 10.3). -/
noncomputable def profA : Fin 10 → ℝ := ![97, 62, 73, 58, 84, 74, 66, 93, 73, 85]

/-- Final-exam scores of Professor B (Try It 10.3). -/
noncomputable def profB : Fin 10 → ℝ := ![85, 64, 74, 55, 76, 67, 72, 84, 71, 98]

private lemma profA_mean : mean profA = 153 / 2 := by
  simp [mean, profA, Fin.sum_univ_succ]; norm_num

private lemma profB_mean : mean profB = 373 / 5 := by
  simp [mean, profB, Fin.sum_univ_succ]; norm_num

private lemma profA_var : sampleVariance profA = 3029 / 18 := by
  rw [sampleVariance, sumSqDev, profA_mean]; simp [profA, Fin.sum_univ_succ]; norm_num

private lemma profB_var : sampleVariance profB = 6602 / 45 := by
  rw [sampleVariance, sumSqDev, profB_mean]; simp [profB, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 10.3. From the two lists of `10` scores the means are
exactly `76.5` (A) and `74.6` (B) and the sample variances `3029/18` and `6602/45`; the standard
deviations are unknown, so the Welch `t` test is used, right-tailed at `5%`. The statistic lies
strictly between `0.33853` and `0.33854` and the degrees of freedom strictly between `17.91` and
`17.92`. The statistic is below a standard `t`-table critical value `1.740` (`17` degrees of freedom,
a table value): do not reject, there is no evidence that A's mean is higher. -/
@[kb "openstaxintrostats2e" "Try It 10.3, p. 529"]
theorem tryit_10_3_two_professors :
    mean profA = 76.5 ∧ mean profB = 74.6 ∧ sampleVariance profA = 3029 / 18 ∧
      sampleVariance profB = 6602 / 45 ∧
      (0.33853 < welchT (mean profA) (mean profB) (sampleVariance profA) (sampleVariance profB) 10 10 ∧
        welchT (mean profA) (mean profB) (sampleVariance profA) (sampleVariance profB) 10 10 < 0.33854) ∧
      (17.91 < welchDF (sampleVariance profA) (sampleVariance profB) 10 10 ∧
        welchDF (sampleVariance profA) (sampleVariance profB) 10 10 < 17.92) ∧
      welchT (mean profA) (mean profB) (sampleVariance profA) (sampleVariance profB) 10 10 < 1.740 := by
  rw [profA_mean, profB_mean, profA_var, profB_var]
  have e : welchT (153 / 2) (373 / 5) (3029 / 18) (6602 / 45) 10 10 =
      (19 / 10) / √(3029 / 18 / 10 + 6602 / 45 / 10) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 19 / 10) (x := 3029 / 18 / 10 + 6602 / 45 / 10) (a := 5.612387)
    (b := 5.6123871) (L := 0.33853) (U := 0.33854) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  refine ⟨by norm_num, by norm_num, rfl, rfl, hz, ⟨?_, ?_⟩, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num
  · linarith [hz.2]

/-! ### Section 10.1: Cohen's d -/

/-- OpenStax Introductory Statistics 2e Try It 10.4. Cohen's `d` of Try It 10.2, the mean difference
`5 - 4.5` over the pooled standard deviation `√((14 · 1.2² + 19 · 0.8²)/33)`, lies strictly between
`0.50523` and `0.50524`: above `0.5` and below `0.8`, a medium effect. -/
@[kb "openstaxintrostats2e" "Try It 10.4, p. 531"]
theorem tryit_10_4_cohens_d_company_tenure :
    0.50523 < (5 - 4.5) / √(((15 - 1) * 1.2 ^ 2 + (20 - 1) * 0.8 ^ 2) / (15 + 20 - 2)) ∧
      (5 - 4.5) / √(((15 - 1) * 1.2 ^ 2 + (20 - 1) * 0.8 ^ 2) / (15 + 20 - 2)) < 0.50524 ∧
      (0.5 : ℝ) < 0.50523 ∧ (0.50524 : ℝ) < 0.8 := by
  have e : (5 - 4.5) / √(((15 - 1) * 1.2 ^ 2 + (20 - 1) * 0.8 ^ 2) / (15 + 20 - 2) : ℝ) =
      (1 / 2) / √(808 / 825) := by
    congr 1
    · norm_num
    · congr 1; norm_num
  rw [e]
  have hz := pos_bounds (c := 1 / 2) (x := 808 / 825) (a := 0.9896433) (b := 0.9896434) (L := 0.50523)
    (U := 0.50524) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨hz.1, hz.2, by norm_num, by norm_num⟩

/-- Northeast weighted alphas of Try It 10.5. -/
noncomputable def alphaNE : Fin 30 → ℝ :=
  ![94.2, 75.2, 69.6, 52.0, 48.0, 41.9, 36.4, 33.4, 31.5, 27.6, 77.3, 71.9, 67.5, 50.6, 46.2, 38.4, 35.2,
    33.0, 28.7, 26.5, 76.3, 71.7, 56.3, 48.7, 43.2, 37.6, 33.7, 31.8, 28.5, 26.0]

/-- West weighted alphas of Try It 10.5. -/
noncomputable def alphaW : Fin 30 → ℝ :=
  ![126.0, 70.6, 65.2, 51.4, 45.5, 37.0, 33.0, 29.6, 23.7, 22.6, 116.1, 70.6, 58.2, 51.2, 43.2, 36.0, 31.4,
    28.7, 23.5, 21.6, 78.2, 68.2, 55.6, 50.3, 39.0, 34.1, 31.0, 25.3, 23.4, 21.5]

private lemma NE_mean : mean alphaNE = 14389 / 300 := by
  simp [mean, alphaNE, Fin.sum_univ_succ]; norm_num

private lemma W_mean : mean alphaW = 14117 / 300 := by
  simp [mean, alphaW, Fin.sum_univ_succ]; norm_num

private lemma NE_var : sampleVariance alphaNE = 31380509 / 87000 := by
  rw [sampleVariance, sumSqDev, NE_mean]; simp [alphaNE, Fin.sum_univ_succ]; norm_num

private lemma W_var : sampleVariance alphaW = 59837741 / 87000 := by
  rw [sampleVariance, sumSqDev, W_mean]; simp [alphaW, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 10.5. From the two lists of `30` weighted alphas the
means are `14389/300 ≈ 47.96` (northeast) and `14117/300 ≈ 47.06` (west) and the sample variances
`31380509/87000` and `59837741/87000`. The Welch statistic (two-sided test, unknown standard
deviations) lies strictly between `0.15336` and `0.15337`, the degrees of freedom strictly between
`52.85` and `52.86`; the statistic is below the standard two-sided `5%` `t`-table critical value `2.009`
(a table value, about `50` degrees of freedom): do not reject. -/
@[kb "openstaxintrostats2e" "Try It 10.5, p. 531"]
theorem tryit_10_5_weighted_alpha :
    mean alphaNE = 14389 / 300 ∧ mean alphaW = 14117 / 300 ∧
      sampleVariance alphaNE = 31380509 / 87000 ∧ sampleVariance alphaW = 59837741 / 87000 ∧
      (0.15336 < welchT (mean alphaNE) (mean alphaW) (sampleVariance alphaNE) (sampleVariance alphaW) 30 30 ∧
        welchT (mean alphaNE) (mean alphaW) (sampleVariance alphaNE) (sampleVariance alphaW) 30 30 <
          0.15337) ∧
      (52.85 < welchDF (sampleVariance alphaNE) (sampleVariance alphaW) 30 30 ∧
        welchDF (sampleVariance alphaNE) (sampleVariance alphaW) 30 30 < 52.86) ∧
      |welchT (mean alphaNE) (mean alphaW) (sampleVariance alphaNE) (sampleVariance alphaW) 30 30| <
        2.009 := by
  rw [NE_mean, W_mean, NE_var, W_var]
  have e : welchT (14389 / 300) (14117 / 300) (31380509 / 87000) (59837741 / 87000) 30 30 =
      (68 / 75) / √(31380509 / 87000 / 30 + 59837741 / 87000 / 30) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 68 / 75) (x := 31380509 / 87000 / 30 + 59837741 / 87000 / 30)
    (a := 5.9118119) (b := 5.911812) (L := 0.15336) (U := 0.15337) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  refine ⟨rfl, rfl, rfl, rfl, hz, ⟨?_, ?_⟩, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num
  · rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]

/-- OpenStax Introductory Statistics 2e Try It 10.5(j). Cohen's `d` of the two weighted-alpha lists,
the mean difference over the pooled standard deviation `√((29 s₁² + 29 s₂²)/58)`, lies strictly between
`0.03959` and `0.0396`, below `0.2`: a negligible (smaller than small) effect. -/
@[kb "openstaxintrostats2e" "Try It 10.5, p. 531"]
theorem tryit_10_5_cohens_d_weighted_alpha :
    0.03959 < (mean alphaNE - mean alphaW) /
        √(((30 - 1) * sampleVariance alphaNE + (30 - 1) * sampleVariance alphaW) / (30 + 30 - 2)) ∧
      (mean alphaNE - mean alphaW) /
        √(((30 - 1) * sampleVariance alphaNE + (30 - 1) * sampleVariance alphaW) / (30 + 30 - 2))
          < 0.0396 ∧ (0.0396 : ℝ) < 0.2 := by
  rw [NE_mean, W_mean, NE_var, W_var]
  have e : ((14389 / 300 : ℝ) - 14117 / 300) /
      √(((30 - 1) * (31380509 / 87000) + (30 - 1) * (59837741 / 87000)) / (30 + 30 - 2)) =
      (68 / 75) / √(364873 / 696) := by
    congr 1
    · norm_num
    · congr 1; norm_num
  rw [e]
  have := pos_bounds (c := 68 / 75) (x := 364873 / 696) (a := 22.8963494) (b := 22.8963495)
    (L := 0.03959) (U := 0.0396) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨this.1, this.2, by norm_num⟩

/-! ### Section 10.2: two means, known standard deviations -/

/-- OpenStax Introductory Statistics 2e Try It 10.6. Engines `1` (mean `1500`, standard deviation `50`)
and `2` (mean `1600`, standard deviation `60`), `30` each, known standard deviations, right-tailed
(engine 2 higher). The `z` statistic for the difference `1600 - 1500` lies strictly between `7.01286`
and `7.01287`, and the right-tail `p`-value `1 - Φ(z)` is below `0.0251`, hence below `0.05`: reject. -/
@[kb "openstaxintrostats2e" "Try It 10.6, p. 533"]
theorem tryit_10_6_engines_rpm :
    (7.01286 < welchT 1600 1500 (60 ^ 2) (50 ^ 2) 30 30 ∧
        welchT 1600 1500 (60 ^ 2) (50 ^ 2) 30 30 < 7.01287) ∧
      1 - Φ (welchT 1600 1500 (60 ^ 2) (50 ^ 2) 30 30) < 0.0251 ∧
      1 - Φ (welchT 1600 1500 (60 ^ 2) (50 ^ 2) 30 30) < 0.05 := by
  have e : welchT 1600 1500 (60 ^ 2) (50 ^ 2) 30 30 = 100 / √(610 / 3) := by
    unfold welchT; norm_num
  have hz := pos_bounds (c := 100) (x := 610 / 3) (a := 14.2594997) (b := 14.2594998) (L := 7.01286)
    (U := 7.01287) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [e]
  have ht := tail_196 (z := 100 / √(610 / 3)) (by linarith [hz.1])
  exact ⟨hz, ht, by linarith⟩

/-- OpenStax Introductory Statistics 2e Try It 10.7. University A (mean age `46.672`, standard
deviation `8.53`) against B (mean `47.531`, standard deviation `7.83`), `10` professors each, right-tailed
at `5%`; the standard deviations are sample values, so the Welch `t` test applies. The statistic lies
strictly between `-0.2346` and `-0.23459` and the degrees of freedom strictly between `17.86` and
`17.87`. The statistic is negative, below the right-tail critical value `1.740` (`17` degrees of
freedom, a standard table value): do not reject. -/
@[kb "openstaxintrostats2e" "Try It 10.7, p. 535"]
theorem tryit_10_7_professors_ages :
    (-0.2346 < welchT 46.672 47.531 (8.53 ^ 2) (7.83 ^ 2) 10 10 ∧
        welchT 46.672 47.531 (8.53 ^ 2) (7.83 ^ 2) 10 10 < -0.23459) ∧
      (17.86 < welchDF (8.53 ^ 2) (7.83 ^ 2) 10 10 ∧ welchDF (8.53 ^ 2) (7.83 ^ 2) 10 10 < 17.87) ∧
      welchT 46.672 47.531 (8.53 ^ 2) (7.83 ^ 2) 10 10 < 1.740 := by
  have e : welchT 46.672 47.531 (8.53 ^ 2) (7.83 ^ 2) 10 10 =
      (-859 / 1000) / √(670349 / 50000) := by
    unfold welchT; norm_num
  have hz := neg_bounds (c := -859 / 1000) (x := 670349 / 50000) (a := 3.6615543) (b := 3.6615544)
    (L := -0.2346) (U := -0.23459) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [e]
  refine ⟨hz, ⟨?_, ?_⟩, ?_⟩
  · unfold welchDF; norm_num
  · unfold welchDF; norm_num
  · linarith [hz.2]

/-! ### Section 10.3: two proportions -/

/-- OpenStax Introductory Statistics 2e Try It 10.8. Valves: `15` of `100` (A) against `6` of `100` (B)
cracked; the pooled proportion is exactly `0.105`. The pooled `z` statistic lies strictly between
`2.07596` and `2.07598`, and the two-sided `p`-value `2(1 - Φ(z))` strictly between `0.0378` and
`0.038`, below `0.05`: reject. -/
@[kb "openstaxintrostats2e" "Try It 10.8, p. 536"]
theorem tryit_10_8_valves :
    (15 + 6) / (100 + 100 : ℝ) = 0.105 ∧
      (2.07596 < pooledZ 15 100 6 100 ∧ pooledZ 15 100 6 100 < 2.07598) ∧
      (0.0378 < 2 * (1 - Φ (pooledZ 15 100 6 100)) ∧ 2 * (1 - Φ (pooledZ 15 100 6 100)) < 0.038) ∧
      2 * (1 - Φ (pooledZ 15 100 6 100)) < 0.05 := by
  have e : pooledZ 15 100 6 100 = (9 / 100) / √((21 / 200) * (1 - 21 / 200) * (1 / 100 + 1 / 100)) := by
    unfold pooledZ; norm_num
  refine ⟨by norm_num, ?_⟩
  rw [e]
  have hz := pos_bounds (a := 0.0433532) (b := 0.0433533) (L := 2.07596) (U := 2.07598)
    (c := 9 / 100) (x := (21 / 200) * (1 - 21 / 200) * (1 / 100 + 1 / 100)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize (9 / 100 : ℝ) / √((21 / 200) * (1 - 21 / 200) * (1 / 100 + 1 / 100)) = z at hz ⊢
  have e1 := Ioo_enclosure (k := 2.07596) (a := 0.9620) (b := 0.9622) (by norm_num) 18 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have e2 := Ioo_enclosure (k := 2.07598) (a := 0.9620) (b := 0.9622) (by norm_num) 18 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have g1 := Phi_ge (by norm_num) hz.1.le e1.1
  have g2 := Phi_le (by norm_num) hz.2.le e2.2
  refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-- OpenStax Introductory Statistics 2e Try It 10.9. Tea: `16` of `230` men against `18` of `218`
women, right-tailed (men more) at `1%`. The pooled `z` statistic lies strictly between `-0.51947` and
`-0.51946`. It is negative, so the right-tail `p`-value `1 - Φ(z)` is at least `1/2`, hence above `0.01`: do not
reject. -/
@[kb "openstaxintrostats2e" "Try It 10.9, p. 538"]
theorem tryit_10_9_tea :
    (-0.51947 < pooledZ 16 230 18 218 ∧ pooledZ 16 230 18 218 < -0.51946) ∧
      1 / 2 ≤ 1 - Φ (pooledZ 16 230 18 218) ∧ 0.01 < 1 - Φ (pooledZ 16 230 18 218) := by
  have e : pooledZ 16 230 18 218 = (16 / 230 - 18 / 218) /
      √((34 / 448) * (1 - 34 / 448) * (1 / 230 + 1 / 218)) := by
    unfold pooledZ; norm_num
  rw [e]
  have hz := neg_bounds (a := 0.0250327) (b := 0.0250328) (L := -0.51947) (U := -0.51946)
    (c := 16 / 230 - 18 / 218) (x := (34 / 448) * (1 - 34 / 448) * (1 / 230 + 1 / 218))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize (16 / 230 - 18 / 218 : ℝ) / √((34 / 448) * (1 - 34 / 448) * (1 / 230 + 1 / 218)) = z
    at hz ⊢
  have h0 := stdNormalCdf_neg 0
  rw [neg_zero] at h0
  have hm := monotone_cdf (gaussianReal 0 1) (show z ≤ 0 by linarith [hz.2])
  refine ⟨hz, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Try It 10.10. Motorcyclists without helmets: `7622` of `113231`
(northeast) against `7439` of `104873` (southeast), two-sided at `5%`. The pooled `z` statistic lies
strictly between `-3.33122` and `-3.3309`, so it is below `-2.576`, and the two-sided `p`-value
`2 Φ(z)` is below `0.0102`, hence below `0.05`: reject. -/
@[kb "openstaxintrostats2e" "Try It 10.10, p. 539"]
theorem tryit_10_10_helmets :
    (-3.33122 < pooledZ 7622 113231 7439 104873 ∧ pooledZ 7622 113231 7439 104873 < -3.3309) ∧
      2 * Φ (pooledZ 7622 113231 7439 104873) < 0.0102 ∧
      2 * Φ (pooledZ 7622 113231 7439 104873) < 0.05 := by
  have e : pooledZ 7622 113231 7439 104873 = (7622 / 113231 - 7439 / 104873) /
      √((15061 / 218104) * (1 - 15061 / 218104) * (1 / 113231 + 1 / 104873)) := by
    unfold pooledZ; norm_num
  rw [e]
  have hz := neg_bounds (a := 0.0010866) (b := 0.0010867) (L := -3.33122) (U := -3.3309)
    (c := 7622 / 113231 - 7439 / 104873)
    (x := (15061 / 218104) * (1 - 15061 / 218104) * (1 / 113231 + 1 / 104873))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize (7622 / 113231 - 7439 / 104873 : ℝ) /
    √((15061 / 218104) * (1 - 15061 / 218104) * (1 / 113231 + 1 / 104873)) = z at hz ⊢
  have ht := tail_2576 (z := z) (by linarith [hz.2])
  refine ⟨hz, by linarith, by linarith⟩

/-! ### Section 10.4: matched pairs -/

/-- "After minus before" cholesterol differences of Try It 10.11. -/
noncomputable def dietDiff : Fin 9 → ℝ :=
  ![199, 207, 189, 209, 217, 202, 211, 223, 201] - ![209, 210, 205, 198, 216, 217, 238, 240, 222]

private lemma dietDiff_mean : mean dietDiff = -97 / 9 := by
  simp [mean, dietDiff, Fin.sum_univ_succ]; norm_num

private lemma dietDiff_var : sampleVariance dietDiff = 5065 / 36 := by
  rw [sampleVariance, sumSqDev, dietDiff_mean]; simp [dietDiff, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 10.11. The after-minus-before cholesterol differences
are `-10, -3, -16, 11, 1, -15, -27, -17, -21`, with mean exactly `-97/9` (about `-10.78`), sample
variance `5065/36`, and paired `t` statistic strictly between `-2.72592` and `-2.72591` on `8` degrees
of freedom. It is below the left-tail critical value `-1.860` of a standard `t` table (a table value,
not proved): reject, the mean cholesterol is lower after the diet. -/
@[kb "openstaxintrostats2e" "Try It 10.11, p. 542"]
theorem tryit_10_11_cholesterol_diet :
    dietDiff = ![-10, -3, -16, 11, 1, -15, -27, -17, -21] ∧ mean dietDiff = -97 / 9 ∧
      sampleVariance dietDiff = 5065 / 36 ∧
      (-2.72592 < pairedT dietDiff ∧ pairedT dietDiff < -2.72591) ∧ pairedT dietDiff < -1.860 := by
  have e : pairedT dietDiff = (-97 / 9) / √(5065 / 36 / 9) := by
    unfold pairedT; rw [dietDiff_mean, dietDiff_var]; norm_num
  have hz := neg_bounds (c := -97 / 9) (x := 5065 / 36 / 9) (a := 3.9538229) (b := 3.953823)
    (L := -2.72592) (U := -2.72591) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, dietDiff_mean, dietDiff_var, by rw [e]; exact hz, by rw [e]; linarith [hz.2]⟩
  funext i
  fin_cases i <;> simp [dietDiff] <;> norm_num

/-- "After minus before" score differences of the SAT course of Try It 10.12. -/
noncomputable def satDiff : Fin 4 → ℝ := ![1920, 2160, 2200, 2100] - ![1840, 1960, 1920, 2150]

private lemma satDiff_mean : mean satDiff = 255 / 2 := by
  simp [mean, satDiff, Fin.sum_univ_succ]; norm_num

private lemma satDiff_var : sampleVariance satDiff = 62275 / 3 := by
  rw [sampleVariance, sumSqDev, satDiff_mean]; simp [satDiff, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 10.12. The after-minus-before SAT differences are
`80, 200, 280, -50`, with mean exactly `255/2 = 127.5`, sample variance `62275/3`, and paired `t`
statistic strictly between `1.76988` and `1.76989` on `3` degrees of freedom. It is below the
right-tail `5%` critical value `2.353` of a standard `t` table (a table value): do not reject. -/
@[kb "openstaxintrostats2e" "Try It 10.12, p. 543"]
theorem tryit_10_12_sat_prep :
    satDiff = ![80, 200, 280, -50] ∧ mean satDiff = 255 / 2 ∧ sampleVariance satDiff = 62275 / 3 ∧
      (1.76988 < pairedT satDiff ∧ pairedT satDiff < 1.76989) ∧ pairedT satDiff < 2.353 := by
  have e : pairedT satDiff = (255 / 2) / √(62275 / 3 / 4) := by
    unfold pairedT; rw [satDiff_mean, satDiff_var]; norm_num
  have hz := pos_bounds (c := 255 / 2) (x := 62275 / 3 / 4) (a := 72.0387627) (b := 72.0387628)
    (L := 1.76988) (U := 1.76989) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, satDiff_mean, satDiff_var, by rw [e]; exact hz, by rw [e]; linarith [hz.2]⟩
  funext i
  fin_cases i <;> simp [satDiff] <;> norm_num

/-- "Dominant minus off-hand" distance differences of Try It 10.13. -/
noncomputable def ballDiff : Fin 5 → ℝ := ![120, 111, 135, 140, 125] - ![105, 109, 98, 111, 99]

private lemma ballDiff_mean : mean ballDiff = 109 / 5 := by
  simp [mean, ballDiff, Fin.sum_univ_succ]; norm_num

private lemma ballDiff_var : sampleVariance ballDiff = 1847 / 10 := by
  rw [sampleVariance, sumSqDev, ballDiff_mean]; simp [ballDiff, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 10.13. The dominant-minus-off-hand differences are
`15, 2, 37, 29, 26`, with mean exactly `109/5 = 21.8`, sample variance `1847/10`, and paired `t`
statistic strictly between `3.5868` and `3.58681` on `4` degrees of freedom. It exceeds the two-sided
`5%` critical value `2.776` of a standard `t` table (a table value): reject, the mean difference is
significant. -/
@[kb "openstaxintrostats2e" "Try It 10.13, p. 544"]
theorem tryit_10_13_throwing_hands :
    ballDiff = ![15, 2, 37, 29, 26] ∧ mean ballDiff = 109 / 5 ∧ sampleVariance ballDiff = 1847 / 10 ∧
      (3.5868 < pairedT ballDiff ∧ pairedT ballDiff < 3.58681) ∧ 2.776 < |pairedT ballDiff| := by
  have e : pairedT ballDiff = (109 / 5) / √(1847 / 10 / 5) := by
    unfold pairedT; rw [ballDiff_mean, ballDiff_var]; norm_num
  have hz := pos_bounds (c := 109 / 5) (x := 1847 / 10 / 5) (a := 6.0778285) (b := 6.0778286)
    (L := 3.5868) (U := 3.58681) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ballDiff_mean, ballDiff_var, by rw [e]; exact hz, ?_⟩
  · funext i
    fin_cases i <;> simp [ballDiff] <;> norm_num
  · rw [e, abs_of_pos (by linarith [hz.1])]
    linarith [hz.1]

end UndergradKB.Statistics.Course.TryItC10
