import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Welch
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.CriticalValues

/-!
# Worked examples, chapter 10 (OpenStax *Introductory Statistics 2e*): hypothesis tests with two samples

Test statistics of the book's two-sample examples are computed from the given data: the Welch statistic
(`welchT`, with `welchDF` from `Welch.lean`), the known-standard-deviation `z` statistic (the same formula
with true variances), the pooled two-proportion `z` statistic (`pooledZ`) and the paired `t` statistic
(`pairedT`, built on `mean` and `sampleVariance` of `Data.lean`). Where the book reports a normal `p`-value,
it is proved as a two-sided bound through enclosures of the standard normal distribution function `Φ`.
Student `t` `p`-values cannot be computed here: they are quoted from the book as table values and only used
for the reject / do-not-reject decision.
-/

namespace UndergradKB.Statistics.Course.ExamplesC10

open UndergradKB.Statistics MeasureTheory ProbabilityTheory Real Set

local notation "Φ" => cdf (gaussianReal 0 1)

/-- The two-sample mean statistic `(x̄₁ - x̄₂) / √(v₁/n₁ + v₂/n₂)`, where `v₁, v₂` are the sample variances
(Welch `t`) or the true variances (the `z` statistic for known standard deviations). -/
noncomputable def welchT (m₁ m₂ v₁ v₂ : ℝ) (n₁ n₂ : ℕ) : ℝ :=
  (m₁ - m₂) / √(v₁ / n₁ + v₂ / n₂)

/-- The pooled two-proportion `z` statistic for `x₁` successes out of `n₁` and `x₂` out of `n₂`:
`(p̂₁ - p̂₂) / √(p̂c (1 - p̂c) (1/n₁ + 1/n₂))`, with the pooled proportion `p̂c = (x₁ + x₂)/(n₁ + n₂)`. -/
noncomputable def pooledZ (x₁ n₁ x₂ n₂ : ℝ) : ℝ :=
  (x₁ / n₁ - x₂ / n₂) /
    √((x₁ + x₂) / (n₁ + n₂) * (1 - (x₁ + x₂) / (n₁ + n₂)) * (1 / n₁ + 1 / n₂))

/-- The paired `t` statistic of a list of differences, `d̄ / √(s²/n)` (equal to `d̄ / (s/√n)`). -/
noncomputable def pairedT {n : ℕ} (d : Fin n → ℝ) : ℝ := mean d / √(sampleVariance d / n)

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

/-! ### Section 10.1: two means, unknown standard deviations -/

/-- OpenStax Introductory Statistics 2e Example 10.1. Girls (`n = 9`, mean `2`) and boys (`n = 16`,
mean `3.2`, standard deviation `1`) playing sports. The girls' standard deviation is not legible in the
text; it is taken as `√0.75 ≈ 0.866`, which reproduces the book's `t = -3.14` and `df = 18.8462`. The
Welch statistic lies strictly between `-3.1424` and `-3.1422`, and the Welch degrees of freedom are exactly
`245/13`, strictly between `18.846` and `18.847`. The `p`-value `0.0054` is the book's table value and is
below the level `0.05`, so the null hypothesis is rejected. -/
@[kb "openstaxintrostats2e" "Example 10.1, p. 525"]
theorem example_10_1_girls_boys_sports :
    (-3.1424 < welchT 2 3.2 0.75 1 9 16 ∧ welchT 2 3.2 0.75 1 9 16 < -3.1422) ∧
      welchDF 0.75 1 9 16 = 245 / 13 ∧ 18.846 < welchDF 0.75 1 9 16 ∧ welchDF 0.75 1 9 16 < 18.847 ∧
      (0.0054 : ℝ) < 0.05 := by
  have e : welchT 2 3.2 0.75 1 9 16 = (-1.2) / √(7 / 48) := by
    unfold welchT; norm_num
  have h : welchDF 0.75 1 9 16 = 245 / 13 := by
    unfold welchDF; norm_num
  refine ⟨?_, h, ?_, ?_, by norm_num⟩
  · rw [e]
    exact neg_bounds (a := 0.38188) (b := 0.38189) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- OpenStax Introductory Statistics 2e Example 10.2. College A (`n = 11`, mean `4`, standard deviation
`1.5`) against college B (`n = 9`, mean `3.5`, standard deviation `1`), right-tailed at level `0.01`. The
Welch statistic lies strictly between `0.8899` and `0.89`, the Welch degrees of freedom strictly between
`17.39` and `17.40`; the book's `p`-value `0.1928` (a table value) exceeds `0.01`, so the null hypothesis is
not rejected. -/
@[kb "openstaxintrostats2e" "Example 10.2, p. 526"]
theorem example_10_2_math_classes :
    (0.8899 < welchT 4 3.5 (1.5 ^ 2) (1 ^ 2) 11 9 ∧ welchT 4 3.5 (1.5 ^ 2) (1 ^ 2) 11 9 < 0.89) ∧
      (17.39 < welchDF (1.5 ^ 2) (1 ^ 2) 11 9 ∧ welchDF (1.5 ^ 2) (1 ^ 2) 11 9 < 17.40) ∧
      (0.01 : ℝ) < 0.1928 := by
  have e : welchT 4 3.5 (1.5 ^ 2) (1 ^ 2) 11 9 = 0.5 / √(1.5 ^ 2 / 11 + 1 ^ 2 / 9) := by
    unfold welchT; norm_num
  refine ⟨?_, ?_, by norm_num⟩
  · rw [e]
    exact pos_bounds (a := 0.56183) (b := 0.56184) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · unfold welchDF; norm_num

/-- Final-exam scores of the online class of Example 10.3. -/
noncomputable def onlineScores : Fin 30 → ℝ :=
  ![67.6, 41.2, 85.3, 55.9, 82.4, 91.2, 73.5, 94.1, 64.7, 64.7, 70.6, 38.2, 61.8, 88.2, 70.6, 58.8, 91.2,
    73.5, 82.4, 35.5, 94.1, 88.2, 64.7, 55.9, 88.2, 97.1, 85.3, 61.8, 79.4, 79.4]

/-- Final-exam scores of the face-to-face class of Example 10.3. -/
noncomputable def f2fScores : Fin 30 → ℝ :=
  ![77.9, 95.3, 81.2, 74.1, 98.8, 88.2, 85.9, 92.9, 87.1, 88.2, 69.4, 57.6, 69.4, 67.1, 97.6, 85.9, 88.2,
    91.8, 78.8, 71.8, 98.8, 61.2, 92.9, 90.6, 97.6, 100, 95.3, 83.5, 92.9, 89.4]

private lemma online_mean : mean onlineScores = 1457 / 20 := by
  simp [mean, onlineScores, Fin.sum_univ_succ]; norm_num

private lemma f2f_mean : mean f2fScores = 4249 / 50 := by
  simp [mean, f2fScores, Fin.sum_univ_succ]; norm_num

private lemma online_var : sampleVariance onlineScores = 1660219 / 5800 := by
  rw [sampleVariance, sumSqDev, online_mean]; simp [onlineScores, Fin.sum_univ_succ]; norm_num

private lemma f2f_var : sampleVariance f2fScores = 994857 / 7250 := by
  rw [sampleVariance, sumSqDev, f2f_mean]; simp [f2fScores, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 10.3. From the two lists of `30` final-exam scores the
means are exactly `72.85` (online) and `84.98` (face to face) and the sample variances `1660219/5800` and
`994857/7250`. The Welch statistic lies strictly between `-3.2287` and `-3.2285` and the Welch degrees of
freedom strictly between `51.60` and `51.61`. The book's `p`-value `0.0011` is a table value below `0.05`
(reject: the online mean is lower). -/
@[kb "openstaxintrostats2e" "Example 10.3, p. 528"]
theorem example_10_3_online_vs_face_to_face :
    mean onlineScores = 72.85 ∧ mean f2fScores = 84.98 ∧
      sampleVariance onlineScores = 1660219 / 5800 ∧ sampleVariance f2fScores = 994857 / 7250 ∧
      (-3.2287 < welchT (mean onlineScores) (mean f2fScores) (sampleVariance onlineScores)
          (sampleVariance f2fScores) 30 30 ∧
        welchT (mean onlineScores) (mean f2fScores) (sampleVariance onlineScores)
          (sampleVariance f2fScores) 30 30 < -3.2285) ∧
      (51.60 < welchDF (sampleVariance onlineScores) (sampleVariance f2fScores) 30 30 ∧
        welchDF (sampleVariance onlineScores) (sampleVariance f2fScores) 30 30 < 51.61) ∧
      (0.0011 : ℝ) < 0.05 := by
  rw [online_mean, f2f_mean, online_var, f2f_var]
  have e : welchT (1457 / 20) (4249 / 50) (1660219 / 5800) (994857 / 7250) 30 30 =
      (-1213 / 100) / √(1660219 / 5800 / 30 + 994857 / 7250 / 30) := by
    unfold welchT; norm_num
  refine ⟨by norm_num, by norm_num, rfl, rfl, ?_, ?_, by norm_num⟩
  · rw [e]
    exact neg_bounds (a := 3.757) (b := 3.7571) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · unfold welchDF; norm_num

/-! ### Section 10.1: Cohen's d -/

/-- OpenStax Introductory Statistics 2e Example 10.5. Cohen's `d` of the two exam-score lists of Example
10.3, the mean difference (face to face minus online) over the pooled standard deviation
`√((29 s₁² + 29 s₂²)/58)`, lies strictly between `0.8335` and `0.8337` (the book's `0.834`), a large effect
(above `0.8`). -/
@[kb "openstaxintrostats2e" "Example 10.5, p. 531"]
theorem example_10_5_cohens_d_exam_scores :
    0.8335 < (mean f2fScores - mean onlineScores) /
        √(((30 - 1) * sampleVariance onlineScores + (30 - 1) * sampleVariance f2fScores) / (30 + 30 - 2)) ∧
      (mean f2fScores - mean onlineScores) /
        √(((30 - 1) * sampleVariance onlineScores + (30 - 1) * sampleVariance f2fScores) / (30 + 30 - 2))
          < 0.8337 ∧ 0.8 < (0.8335 : ℝ) := by
  rw [online_mean, f2f_mean, online_var, f2f_var]
  have e : ((4249 / 50 : ℝ) - 1457 / 20) /
      √(((30 - 1) * (1660219 / 5800) + (30 - 1) * (994857 / 7250)) / (30 + 30 - 2)) =
      (1213 / 100) / √((1660219 / 5800 + 994857 / 7250) / 2) := by
    congr 1
    · norm_num
    · congr 1; norm_num
  rw [e]
  have := pos_bounds (c := 1213 / 100) (x := (1660219 / 5800 + 994857 / 7250) / 2) (a := 14.551)
    (b := 14.552) (L := 0.8335) (U := 0.8337) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨this.1, this.2, by norm_num⟩

/-! ### Section 10.2: two means, known standard deviations -/

/-- OpenStax Introductory Statistics 2e Example 10.6. Floor waxes with means `3` and `2.9` months over
`20` floors each and known standard deviations `0.33` and `0.36`. The `z` statistic lies strictly
between `0.9156` and `0.9158` (the book's `0.9157`), and the right-tail `p`-value `1 - Φ(z)` lies strictly
between `0.1798` and `0.1801` (the book's `0.1799`), above the level `0.05`: do not reject. -/
@[kb "openstaxintrostats2e" "Example 10.6, p. 532"]
theorem example_10_6_floor_waxes :
    (0.9156 < welchT 3 2.9 (0.33 ^ 2) (0.36 ^ 2) 20 20 ∧
        welchT 3 2.9 (0.33 ^ 2) (0.36 ^ 2) 20 20 < 0.9158) ∧
      (0.1798 < 1 - Φ (welchT 3 2.9 (0.33 ^ 2) (0.36 ^ 2) 20 20) ∧
        1 - Φ (welchT 3 2.9 (0.33 ^ 2) (0.36 ^ 2) 20 20) < 0.1801) ∧
      0.05 < 1 - Φ (welchT 3 2.9 (0.33 ^ 2) (0.36 ^ 2) 20 20) := by
  have e : welchT 3 2.9 (0.33 ^ 2) (0.36 ^ 2) 20 20 = 0.1 / √(0.33 ^ 2 / 20 + 0.36 ^ 2 / 20) := by
    unfold welchT; norm_num
  rw [e]
  have hz := pos_bounds (a := 0.109201) (b := 0.109202) (L := 0.91573) (U := 0.91575)
    (c := 0.1) (x := 0.33 ^ 2 / 20 + 0.36 ^ 2 / 20) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize 0.1 / √(0.33 ^ 2 / 20 + 0.36 ^ 2 / 20) = z at hz ⊢
  have e1 := Ioo_enclosure (k := 0.91573) (a := 0.6400) (b := 0.6404) (by norm_num) 10 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have e2 := Ioo_enclosure (k := 0.91575) (a := 0.6400) (b := 0.6404) (by norm_num) 10 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have g1 := Phi_ge (by norm_num) hz.1.le e1.1
  have g2 := Phi_le (by norm_num) hz.2.le e2.2
  refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 10.7. Democratic (mean `61.704`, standard deviation
`9.55`) against Republican (mean `61.675`, standard deviation `10.17`) senators, `30` each, normal
approximation. The statistic lies strictly between `0.0113` and `0.0114`, and the right-tail `p`-value
`1 - Φ(z)` lies strictly between `0.4954` and `0.4956` (the book's `0.4955`), above `0.05`: do not
reject. -/
@[kb "openstaxintrostats2e" "Example 10.7, p. 534"]
theorem example_10_7_senators_ages :
    (0.0113 < welchT 61.704 61.675 (9.55 ^ 2) (10.17 ^ 2) 30 30 ∧
        welchT 61.704 61.675 (9.55 ^ 2) (10.17 ^ 2) 30 30 < 0.0114) ∧
      (0.4954 < 1 - Φ (welchT 61.704 61.675 (9.55 ^ 2) (10.17 ^ 2) 30 30) ∧
        1 - Φ (welchT 61.704 61.675 (9.55 ^ 2) (10.17 ^ 2) 30 30) < 0.4956) ∧
      0.05 < 1 - Φ (welchT 61.704 61.675 (9.55 ^ 2) (10.17 ^ 2) 30 30) := by
  have e : welchT 61.704 61.675 (9.55 ^ 2) (10.17 ^ 2) 30 30 =
      0.029 / √(9.55 ^ 2 / 30 + 10.17 ^ 2 / 30) := by
    unfold welchT; norm_num
  rw [e]
  have hz := pos_bounds (a := 2.547099) (b := 2.5471) (L := 0.01138) (U := 0.01139)
    (c := 0.029) (x := 9.55 ^ 2 / 30 + 10.17 ^ 2 / 30) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize 0.029 / √(9.55 ^ 2 / 30 + 10.17 ^ 2 / 30) = z at hz ⊢
  have e1 := Ioo_enclosure (k := 0.01138) (a := 0.0090) (b := 0.0092) (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have e2 := Ioo_enclosure (k := 0.01139) (a := 0.0090) (b := 0.0092) (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have g1 := Phi_ge (by norm_num) hz.1.le e1.1
  have g2 := Phi_le (by norm_num) hz.2.le e2.2
  refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-! ### Section 10.3: two proportions -/

/-- OpenStax Introductory Statistics 2e Example 10.8. Hives after `30` minutes: `20` of `200` (medication
A) against `12` of `200` (B); the pooled proportion is `0.08`. The pooled `z` statistic lies strictly
between `1.4743` and `1.475` (the book's `1.47`), and the two-sided `p`-value `2(1 - Φ(z))` strictly
between `0.1402` and `0.1406` (the book's `0.1404`), above `0.01`: do not reject. -/
@[kb "openstaxintrostats2e" "Example 10.8, p. 535"]
theorem example_10_8_hives_medications :
    (20 + 12) / (200 + 200 : ℝ) = 0.08 ∧
      (1.4743 < pooledZ 20 200 12 200 ∧ pooledZ 20 200 12 200 < 1.475) ∧
      (0.1402 < 2 * (1 - Φ (pooledZ 20 200 12 200)) ∧ 2 * (1 - Φ (pooledZ 20 200 12 200)) < 0.1406) ∧
      0.01 < 2 * (1 - Φ (pooledZ 20 200 12 200)) := by
  have e : pooledZ 20 200 12 200 =
      (1 / 25) / √((32 / 400) * (1 - 32 / 400) * (2 / 200)) := by
    unfold pooledZ; norm_num
  refine ⟨by norm_num, ?_⟩
  rw [e]
  have hz := pos_bounds (a := 0.0271293) (b := 0.0271294) (L := 1.47441) (U := 1.47443)
    (c := 1 / 25) (x := (32 / 400) * (1 - 32 / 400) * (2 / 200)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize (1 / 25 : ℝ) / √((32 / 400) * (1 - 32 / 400) * (2 / 200)) = z at hz ⊢
  have e1 := Ioo_enclosure (k := 1.47441) (a := 0.8594) (b := 0.8598) (by norm_num) 14 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have e2 := Ioo_enclosure (k := 1.47443) (a := 0.8594) (b := 0.8598) (by norm_num) 14 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have g1 := Phi_ge (by norm_num) hz.1.le e1.1
  have g2 := Phi_le (by norm_num) hz.2.le e2.2
  refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 10.9. Seat belts: `156` of `2169` women against `183` of
`2231` men do not wear one. The pooled `z` statistic lies strictly between `-1.2567` and `-1.2564` (the
book's `-1.256`), and the left-tail `p`-value `Φ(z)` strictly between `0.1044` and `0.1046` (the book's
`0.1045`), above `0.01`: do not reject. -/
@[kb "openstaxintrostats2e" "Example 10.9, p. 537"]
theorem example_10_9_seat_belts :
    (-1.2567 < pooledZ 156 2169 183 2231 ∧ pooledZ 156 2169 183 2231 < -1.2564) ∧
      (0.1044 < Φ (pooledZ 156 2169 183 2231) ∧ Φ (pooledZ 156 2169 183 2231) < 0.1046) ∧
      0.01 < Φ (pooledZ 156 2169 183 2231) := by
  have e : pooledZ 156 2169 183 2231 = (156 / 2169 - 183 / 2231) /
      √((339 / 4400) * (1 - 339 / 4400) * (1 / 2169 + 1 / 2231)) := by
    unfold pooledZ; norm_num
  rw [e]
  have hz := neg_bounds (a := 0.008041) (b := 0.0080411) (L := -1.2565) (U := -1.25647)
    (c := 156 / 2169 - 183 / 2231) (x := (339 / 4400) * (1 - 339 / 4400) * (1 / 2169 + 1 / 2231))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize (156 / 2169 - 183 / 2231 : ℝ) /
    √((339 / 4400) * (1 - 339 / 4400) * (1 / 2169 + 1 / 2231)) = z at hz ⊢
  have e1 := Ioo_enclosure (k := 1.25647) (a := 0.7908) (b := 0.7912) (by norm_num) 12 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have e2 := Ioo_enclosure (k := 1.2565) (a := 0.7908) (b := 0.7912) (by norm_num) 12 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have g1 := Phi_ge (z := -z) (by norm_num) (by linarith [hz.2]) e1.1
  have g2 := Phi_le (z := -z) (by norm_num) (by linarith [hz.1]) e2.2
  have hn := stdNormalCdf_neg z
  refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 10.10. Electric vehicles: `135` of `1343` younger adults
against `12` of `232` older adults (the calculator inputs, about the book's `10%` and `5%`). The pooled `z`
statistic lies strictly between `2.3584` and `2.3597` (the book's calculator shows `2.33`), and the
right-tail `p`-value `1 - Φ(z)` strictly between `0.0090` and `0.0093` (the book's calculator `0.0092`),
below `0.05`: reject. -/
@[kb "openstaxintrostats2e" "Example 10.10, p. 538"]
theorem example_10_10_electric_vehicles :
    (2.3584 < pooledZ 135 1343 12 232 ∧ pooledZ 135 1343 12 232 < 2.3597) ∧
      (0.0090 < 1 - Φ (pooledZ 135 1343 12 232) ∧ 1 - Φ (pooledZ 135 1343 12 232) < 0.0093) ∧
      1 - Φ (pooledZ 135 1343 12 232) < 0.05 := by
  have e : pooledZ 135 1343 12 232 = (135 / 1343 - 12 / 232) /
      √((147 / 1575) * (1 - 147 / 1575) * (1 / 1343 + 1 / 232)) := by
    unfold pooledZ; norm_num
  rw [e]
  have hz := pos_bounds (a := 0.0206823) (b := 0.0206824) (L := 2.35935) (U := 2.35937)
    (c := 135 / 1343 - 12 / 232) (x := (147 / 1575) * (1 - 147 / 1575) * (1 / 1343 + 1 / 232))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  generalize (135 / 1343 - 12 / 232 : ℝ) /
    √((147 / 1575) * (1 - 147 / 1575) * (1 / 1343 + 1 / 232)) = z at hz ⊢
  have e1 := Ioo_enclosure (k := 2.35935) (a := 0.9815) (b := 0.9819) (by norm_num) 18 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have e2 := Ioo_enclosure (k := 2.35937) (a := 0.9815) (b := 0.9819) (by norm_num) 18 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  have g1 := Phi_ge (by norm_num) hz.1.le e1.1
  have g2 := Phi_le (by norm_num) hz.2.le e2.2
  refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-! ### Section 10.4: matched pairs -/

/-- The "after minus before" differences of Example 10.11 (pain scores of eight subjects). -/
noncomputable def hypnosisDiff : Fin 8 → ℝ :=
  ![6.8, 2.4, 7.4, 8.5, 8.1, 6.1, 3.4, 2.0] - ![6.6, 6.5, 9.0, 10.3, 11.3, 8.1, 6.3, 11.6]

private lemma hypnosisDiff_mean : mean hypnosisDiff = -25 / 8 := by
  simp [mean, hypnosisDiff, Fin.sum_univ_succ]; norm_num

private lemma hypnosisDiff_var : sampleVariance hypnosisDiff = 11867 / 1400 := by
  rw [sampleVariance, sumSqDev, hypnosisDiff_mean]; simp [hypnosisDiff, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 10.11. The after-minus-before differences are
`0.2, -4.1, -1.6, -1.8, -3.2, -2, -2.9, -9.6`, with mean exactly `-25/8 = -3.125` (the book's `-3.13`),
sample variance `11867/1400`, standard deviation strictly between `2.91` and `2.92`, and paired `t`
statistic strictly between `-3.036` and `-3.0358` (the book's `-3.036`) on `7` degrees of freedom. The
book's `p`-value `0.0095` is a `t`-table value (not proved) and lies below `0.05`: reject. -/
@[kb "openstaxintrostats2e" "Example 10.11, p. 540"]
theorem example_10_11_hypnotism :
    hypnosisDiff = ![0.2, -4.1, -1.6, -1.8, -3.2, -2, -2.9, -9.6] ∧
      mean hypnosisDiff = -25 / 8 ∧ sampleVariance hypnosisDiff = 11867 / 1400 ∧
      (2.91 < sampleStdDev hypnosisDiff ∧ sampleStdDev hypnosisDiff < 2.92) ∧
      (-3.036 < pairedT hypnosisDiff ∧ pairedT hypnosisDiff < -3.0358) ∧ (0.0095 : ℝ) < 0.05 := by
  refine ⟨?_, hypnosisDiff_mean, hypnosisDiff_var, ?_, ?_, by norm_num⟩
  · funext i
    fin_cases i <;> simp [hypnosisDiff] <;> norm_num
  · rw [sampleStdDev, hypnosisDiff_var]
    exact ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩
  · have e : pairedT hypnosisDiff = (-25 / 8) / √(11867 / 1400 / 8) := by
      unfold pairedT; rw [hypnosisDiff_mean, hypnosisDiff_var]; norm_num
    rw [e]
    exact neg_bounds (a := 1.02934) (b := 1.02935) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The "after minus before" differences of Example 10.12 (maximum lifts of four players). -/
noncomputable def liftDiff : Fin 4 → ℝ := ![295, 252, 330, 360] - ![205, 241, 338, 368]

private lemma liftDiff_mean : mean liftDiff = 85 / 4 := by
  simp [mean, liftDiff, Fin.sum_univ_succ]; norm_num

private lemma liftDiff_var : sampleVariance liftDiff = 26171 / 12 := by
  rw [sampleVariance, sumSqDev, liftDiff_mean]; simp [liftDiff, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 10.12. The differences are `90, 11, -8, -8`, with mean
exactly `85/4 = 21.25` (the book's `21.3`), sample variance `26171/12`, and paired `t` statistic strictly
between `0.91` and `0.9101` on `3` degrees of freedom. The book's `p`-value `0.2150` is a `t`-table value
(not proved) and exceeds `0.05`: do not reject. -/
@[kb "openstaxintrostats2e" "Example 10.12, p. 542"]
theorem example_10_12_strength_class :
    liftDiff = ![90, 11, -8, -8] ∧ mean liftDiff = 85 / 4 ∧ sampleVariance liftDiff = 26171 / 12 ∧
      (0.91 < pairedT liftDiff ∧ pairedT liftDiff < 0.9101) ∧ (0.05 : ℝ) < 0.2150 := by
  refine ⟨?_, liftDiff_mean, liftDiff_var, ?_, by norm_num⟩
  · funext i
    fin_cases i <;> simp [liftDiff] <;> norm_num
  · have e : pairedT liftDiff = (85 / 4) / √(26171 / 12 / 4) := by
      unfold pairedT; rw [liftDiff_mean, liftDiff_var]; norm_num
    rw [e]
    exact pos_bounds (a := 23.35014) (b := 23.35015) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The "dominant minus weaker" differences of Example 10.13 (shot-put distances of seven students). -/
noncomputable def shotDiff : Fin 7 → ℝ := ![30, 26, 34, 17, 19, 26, 20] - ![28, 14, 27, 18, 17, 26, 16]

private lemma shotDiff_mean : mean shotDiff = 26 / 7 := by
  simp [mean, shotDiff, Fin.sum_univ_succ]; norm_num

private lemma shotDiff_var : sampleVariance shotDiff = 425 / 21 := by
  rw [sampleVariance, sumSqDev, shotDiff_mean]; simp [shotDiff, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 10.13. The differences are `2, 12, 7, -1, 2, 0, 4`, with
mean exactly `26/7` (the book's `3.71`), sample variance `425/21`, standard deviation strictly between
`4.49` and `4.50` (the book's `4.5`), and paired `t` statistic strictly between `2.1844` and `2.1845`
(the book's `2.18`) on `6` degrees of freedom. The book's `p`-value `0.0716` is a `t`-table value (not
proved) and exceeds `0.05`: do not reject. -/
@[kb "openstaxintrostats2e" "Example 10.13, p. 543"]
theorem example_10_13_shot_put :
    shotDiff = ![2, 12, 7, -1, 2, 0, 4] ∧ mean shotDiff = 26 / 7 ∧ sampleVariance shotDiff = 425 / 21 ∧
      (4.49 < sampleStdDev shotDiff ∧ sampleStdDev shotDiff < 4.50) ∧
      (2.1844 < pairedT shotDiff ∧ pairedT shotDiff < 2.1845) ∧ (0.05 : ℝ) < 0.0716 := by
  refine ⟨?_, shotDiff_mean, shotDiff_var, ?_, ?_, by norm_num⟩
  · funext i
    fin_cases i <;> simp [shotDiff] <;> norm_num
  · rw [sampleStdDev, shotDiff_var]
    exact ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩
  · have e : pairedT shotDiff = (26 / 7) / √(425 / 21 / 7) := by
      unfold pairedT; rw [shotDiff_mean, shotDiff_var]; norm_num
    rw [e]
    exact pos_bounds (a := 1.70034) (b := 1.70035) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end UndergradKB.Statistics.Course.ExamplesC10
