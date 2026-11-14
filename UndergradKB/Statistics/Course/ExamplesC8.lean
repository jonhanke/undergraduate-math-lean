import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.CriticalValues

/-!
# Course layer, chapter 8 (OpenStax *Introductory Statistics 2e*): worked examples

Confidence intervals. For the `z` intervals the critical value (`1.645`, `1.96`, `2.576`, and `2.326`
for Example 8.3) is shown to cut off the stated central mass of the standard normal law, and the
margin of error and endpoints follow by arithmetic. For the `t` intervals the table value of the
Student `t` quantile is taken from the book (it is not computed here) and the sample mean, sample
standard deviation, margin of error and endpoints are proved. Proportion intervals and sample-size
calculations are exact or two-sided bounds around the book's rounded values.
-/

namespace UndergradKB.Statistics.Course.ExamplesC8

open UndergradKB.Statistics MeasureTheory ProbabilityTheory Set

/-- The standard normal mass within `z` of zero. -/
noncomputable def centralMass (z : ℝ) : ℝ := (gaussianReal 0 1).real (Ioo (-z) z)

private lemma div_bounds {s a b r c d : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) (hc : 0 < c)
    (hcr : c < r) (hrd : r < d) : a / d < s / r ∧ s / r < b / c := by
  have hr : 0 < r := by linarith
  have hd : 0 < d := by linarith
  have hb : 0 < b := by linarith
  constructor
  · rw [div_lt_div_iff₀ hd hr]; nlinarith
  · rw [div_lt_div_iff₀ hr hc]; nlinarith

private lemma sqrt_between {x a b : ℝ} (ha : 0 ≤ a) (h1 : a ^ 2 < x) (h2 : x < b ^ 2) (hb : 0 ≤ b) :
    a < √x ∧ √x < b :=
  ⟨(Real.lt_sqrt ha).2 h1, (Real.sqrt_lt' (by nlinarith)).2 h2⟩

/-! ### Section 8.1: mean, known standard deviation -/

/-- OpenStax Introductory Statistics 2e Example 8.1. Sample mean `7` and error bound `2.5` give the
interval `(4.5, 9.5)`. -/
@[kb "openstaxintrostats2e" "Example 8.1, p. 419"]
theorem example_8_1_interval_from_error_bound :
    (7 : ℝ) - 2.5 = 4.5 ∧ (7 : ℝ) + 2.5 = 9.5 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 8.2. Exam scores with `σ = 3`, `n = 36`, mean `68`,
90% confidence. The critical value `1.645` leaves central standard normal mass in
`(0.8999, 0.9001)`; the margin of error `1.645 · 3/√36` is exactly `0.8225`, so the interval is
exactly `(67.1775, 68.8225)` (the book rounds to `(67.18, 68.82)`). -/
@[kb "openstaxintrostats2e" "Example 8.2, p. 421"]
theorem example_8_2_exam_scores_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let ebm : ℝ := 1.645 * (3 / √36)
    ebm = 0.8225 ∧ 68 - ebm = 67.1775 ∧ 68 + ebm = 68.8225 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro ebm
  have h6 : √(36 : ℝ) = 6 := by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have he : ebm = 0.8225 := by simp only [ebm, h6]; norm_num
  refine ⟨he, ?_, ?_⟩ <;> rw [he] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 8.3. The 30 SAR values of Table 8.1 have mean exactly
`3839/3750` (about `1.0237`; the book rounds to `1.024`). With `σ = 0.337` and the 98% critical
value `2.326`, which leaves central standard normal mass in `(0.9799, 0.9801)`, the margin of error is
in `(0.1430, 0.1432)` (book `0.1431`), and the interval has endpoints in `(0.8806, 0.8807)` and
`(1.1668, 1.1669)` (the book, using the rounded mean, gets `0.8809` and `1.1671`; its calculator
gives `(0.881, 1.167)`). -/
@[kb "openstaxintrostats2e" "Example 8.3, p. 423"]
theorem example_8_3_sar_98 :
    (0.9799 < centralMass 2.326 ∧ centralMass 2.326 < 0.9801) ∧
    let x : Fin 30 → ℝ := ![1.11, 1.36, 0.74, 1.48, 1.34, 0.5, 1.43, 1.18, 0.4, 1.3, 1.3, 0.867,
      1.09, 1.26, 0.68, 0.455, 1.29, 0.51, 1.41, 0.36, 1.13, 0.82, 0.52, 0.3, 0.78, 1.6, 1.48,
      1.25, 1.39, 1.38]
    let ebm : ℝ := 2.326 * (0.337 / √30)
    mean x = 3839 / 3750 ∧ 1.0237 < mean x ∧ mean x < 1.0238 ∧
      0.1430 < ebm ∧ ebm < 0.1432 ∧
      0.8806 < mean x - ebm ∧ mean x - ebm < 0.8807 ∧
      1.1668 < mean x + ebm ∧ mean x + ebm < 1.1669 := by
  refine ⟨?_, ?_⟩
  · have := Ioo_enclosure (k := 2.326) (a := 0.9799) (b := 0.9801) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    exact this
  intro x ebm
  have hm : mean x = 3839 / 3750 := by
    simp [mean, x, Fin.sum_univ_succ]; norm_num
  obtain ⟨h1, h2⟩ := sqrt_between (x := 30) (a := 5.477) (b := 5.478) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := 0.337) (a := 0.337) (b := 0.337) (by norm_num) le_rfl le_rfl
    (by norm_num) h1 h2
  have e1 : 0.1430 < ebm := by simp only [ebm]; norm_num at d1 ⊢; linarith
  have e2 : ebm < 0.1432 := by simp only [ebm]; norm_num at d2 ⊢; linarith
  have e3 : 0.14309 < ebm := by simp only [ebm]; norm_num at d1 ⊢; linarith
  have e4 : ebm < 0.14312 := by simp only [ebm]; norm_num at d2 ⊢; linarith
  rw [hm]
  refine ⟨rfl, by norm_num, by norm_num, e1, e2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### Section 8.1 continued: changing the level or the sample size -/

/-- OpenStax Introductory Statistics 2e Example 8.4. The 95% interval for the exam scores of
Example 8.2 (`σ = 3`, `n = 36`, mean `68`). The critical value `1.96` leaves central standard normal
mass in `(0.9499, 0.9501)`; the margin of error is exactly `0.98` and the interval exactly
`(67.02, 68.98)`, wider than the 90% interval. -/
@[kb "openstaxintrostats2e" "Example 8.4, p. 425"]
theorem example_8_4_exam_scores_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let ebm : ℝ := 1.96 * (3 / √36)
    ebm = 0.98 ∧ 68 - ebm = 67.02 ∧ 68 + ebm = 68.98 ∧ 0.8225 < ebm := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro ebm
  have h6 : √(36 : ℝ) = 6 := by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have he : ebm = 0.98 := by simp only [ebm, h6]; norm_num
  refine ⟨he, ?_, ?_, ?_⟩ <;> rw [he] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 8.5. With the 90% critical value `1.645`, `σ = 3`
and mean `68`, the margin of error is exactly `0.4935` for `n = 100` and exactly `0.987` for
`n = 25`; the larger sample gives the smaller margin of error. -/
@[kb "openstaxintrostats2e" "Example 8.5, p. 426"]
theorem example_8_5_sample_size_effect :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    1.645 * (3 / √100) = (0.4935 : ℝ) ∧ 1.645 * (3 / √25) = (0.987 : ℝ) ∧
      1.645 * (3 / √100) < (1.645 * (3 / √25) : ℝ) := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  have h10 : √(100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h5 : √(25 : ℝ) = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h10, h5]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Example 8.6. From the interval `(67.18, 68.82)` the error
bound is half the width, `0.82`, and the sample mean is the midpoint, `68`; also `68.82 - 68 = 0.82`
and `68.82 - 0.82 = 68`. -/
@[kb "openstaxintrostats2e" "Example 8.6, p. 427"]
theorem example_8_6_working_backwards :
    ((68.82 : ℝ) - 67.18) / 2 = 0.82 ∧ ((68.82 : ℝ) + 67.18) / 2 = 68 ∧
      (68.82 : ℝ) - 68 = 0.82 ∧ (68.82 : ℝ) - 0.82 = 68 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 8.7. With `σ = 15`, margin `2` and the 95% critical
value `1.96` (central standard normal mass in `(0.9499, 0.9501)`), the sample size must satisfy
`n ≥ (1.96 · 15/2)² = 216.09`; `217` is the least such natural number. -/
@[kb "openstaxintrostats2e" "Example 8.7, p. 428"]
theorem example_8_7_sample_size_ages :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    (1.96 * 15 / 2 : ℝ) ^ 2 = 216.09 ∧
      IsLeast {n : ℕ | (1.96 * 15 / 2 : ℝ) ^ 2 ≤ n} 217 := by
  refine ⟨critical_values_standard_normal.2.1, by norm_num, ?_, ?_⟩
  · show (1.96 * 15 / 2 : ℝ) ^ 2 ≤ ((217 : ℕ) : ℝ)
    norm_num
  · intro n hn
    by_contra h
    have : n ≤ 216 := by omega
    have h2 : (n : ℝ) ≤ 216 := by exact_mod_cast this
    have h3 : (1.96 * 15 / 2 : ℝ) ^ 2 ≤ n := hn
    norm_num at h3
    linarith

/-! ### Section 8.2: mean, unknown standard deviation (Student `t`) -/

/-- OpenStax Introductory Statistics 2e Example 8.8. Sensory rates of `15` subjects. The sample mean
is exactly `617/75` (book `8.2267`), the sample variance exactly `14681/5250`, and the standard
deviation lies in `(1.6722, 1.6723)` (book `1.6722`). Taking the table value `t = 2.145` for `14`
degrees of freedom from the book (not computed here), the 95% interval has lower endpoint in
`(7.30, 7.31)` and upper endpoint in `(9.15, 9.16)` (book `(7.30, 9.15)`; calculator
`(7.3006, 9.1527)`). -/
@[kb "openstaxintrostats2e" "Example 8.8, p. 430"]
theorem example_8_8_acupuncture_t95 :
    let x : Fin 15 → ℝ := ![8.6, 9.4, 7.9, 6.8, 8.3, 7.3, 9.2, 9.6, 8.7, 11.4, 10.3, 5.4, 8.1, 5.5,
      6.9]
    let tstar : ℝ := 2.145
    mean x = 617 / 75 ∧ sampleVariance x = 14681 / 5250 ∧
      1.6722 < sampleStdDev x ∧ sampleStdDev x < 1.6723 ∧
      7.30 < mean x - tstar * (sampleStdDev x / √15) ∧
      mean x - tstar * (sampleStdDev x / √15) < 7.31 ∧
      9.15 < mean x + tstar * (sampleStdDev x / √15) ∧
      mean x + tstar * (sampleStdDev x / √15) < 9.16 := by
  intro x tstar
  have hm : mean x = 617 / 75 := by
    simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 14681 / 5250 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  obtain ⟨s1, s2⟩ : 1.6722 < sampleStdDev x ∧ sampleStdDev x < 1.6723 := by
    rw [sampleStdDev, hv]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r1, r2⟩ := sqrt_between (x := 15) (a := 3.8729) (b := 3.873) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := sampleStdDev x) (a := 1.6722) (b := 1.6723) (by norm_num)
    s1.le s2.le (by norm_num) r1 r2
  refine ⟨hm, hv, s1, s2, ?_, ?_, ?_, ?_⟩ <;> simp only [tstar] <;> rw [hm] <;> norm_num at d1 d2 ⊢
    <;> linarith

/-- OpenStax Introductory Statistics 2e Example 8.9. Numbers of chemicals found in `20` cord-blood
samples. The sample mean is exactly `127.45`, the variance exactly `256179/380`, and the standard
deviation lies in `(25.964, 25.965)` (book `25.965`). Taking the book's table value `t = 1.729` for
`19` degrees of freedom (not computed here), the 90% interval has lower endpoint in
`(117.41, 117.42)` and upper endpoint in `(137.48, 137.49)` (book `(117.412, 137.488)`). -/
@[kb "openstaxintrostats2e" "Example 8.9, p. 431"]
theorem example_8_9_cord_blood_t90 :
    let x : Fin 20 → ℝ := ![79, 145, 147, 160, 116, 100, 159, 151, 156, 126, 137, 83, 156, 94, 121,
      144, 123, 114, 139, 99]
    let tstar : ℝ := 1.729
    mean x = 127.45 ∧ sampleVariance x = 256179 / 380 ∧
      25.964 < sampleStdDev x ∧ sampleStdDev x < 25.965 ∧
      117.41 < mean x - tstar * (sampleStdDev x / √20) ∧
      mean x - tstar * (sampleStdDev x / √20) < 117.42 ∧
      137.48 < mean x + tstar * (sampleStdDev x / √20) ∧
      mean x + tstar * (sampleStdDev x / √20) < 137.49 := by
  intro x tstar
  have hm : mean x = 127.45 := by
    simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 256179 / 380 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  obtain ⟨s1, s2⟩ : 25.964 < sampleStdDev x ∧ sampleStdDev x < 25.965 := by
    rw [sampleStdDev, hv]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r1, r2⟩ := sqrt_between (x := 20) (a := 4.4721) (b := 4.4722) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := sampleStdDev x) (a := 25.964) (b := 25.965) (by norm_num)
    s1.le s2.le (by norm_num) r1 r2
  refine ⟨hm, hv, s1, s2, ?_, ?_, ?_, ?_⟩ <;> simp only [tstar] <;> rw [hm] <;> norm_num at d1 d2 ⊢
    <;> linarith

/-! ### Section 8.3: proportions -/

/-- OpenStax Introductory Statistics 2e Example 8.10. `421` of `500` surveyed adults own a
smartphone: `p' = 421/500 = 0.842`. With the 95% critical value `1.96` (central standard normal mass
in `(0.9499, 0.9501)`), the error bound `1.96 √(p'q'/n)` lies in `(0.03196, 0.03199)` and the
interval has endpoints in `(0.8100, 0.8101)` and `(0.8739, 0.8740)` (calculator
`(0.81003, 0.87397)`). -/
@[kb "openstaxintrostats2e" "Example 8.10, p. 433"]
theorem example_8_10_smartphones_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let p : ℝ := 421 / 500
    let ebp : ℝ := 1.96 * √(p * (1 - p) / 500)
    p = 0.842 ∧ 0.03196 < ebp ∧ ebp < 0.03199 ∧
      0.8100 < p - ebp ∧ p - ebp < 0.8101 ∧ 0.8739 < p + ebp ∧ p + ebp < 0.8740 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro p ebp
  have hp : p = 0.842 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.01631 : ℝ) < √(p * (1 - p) / 500) ∧ √(p * (1 - p) / 500) < 0.01632 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;> linarith

/-- OpenStax Introductory Statistics 2e Example 8.11. `300` of `500` students are registered
voters, `p' = 0.6`. With the 90% critical value `1.645` (central standard normal mass in
`(0.8999, 0.9001)`), the error bound lies in `(0.03602, 0.03605)` and the interval has endpoints in
`(0.5639, 0.5640)` and `(0.6360, 0.6361)` (book `(0.564, 0.636)`). -/
@[kb "openstaxintrostats2e" "Example 8.11, p. 435"]
theorem example_8_11_registered_voters_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let p : ℝ := 300 / 500
    let ebp : ℝ := 1.645 * √(p * (1 - p) / 500)
    p = 0.6 ∧ 0.03602 < ebp ∧ ebp < 0.03605 ∧
      0.5639 < p - ebp ∧ p - ebp < 0.5640 ∧ 0.6360 < p + ebp ∧ p + ebp < 0.6361 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro p ebp
  have hp : p = 0.6 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.02190 : ℝ) < √(p * (1 - p) / 500) ∧ √(p * (1 - p) / 500) < 0.02191 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;> linarith

/-- OpenStax Introductory Statistics 2e Example 8.12. Plus-four interval for `6` smokers among `25`
students: the adjusted counts are `x = 8`, `n = 29`, so `p' = 8/29`. With the 95% critical value
`1.96` (central standard normal mass in `(0.9499, 0.9501)`), the error bound `1.96 √(p'q'/29)` lies in
`(0.1624, 0.1627)` (book `0.163`) and the interval has endpoints in `(0.113, 0.114)` and
`(0.438, 0.439)` (book `(0.113, 0.439)`). -/
@[kb "openstaxintrostats2e" "Example 8.12, p. 436"]
theorem example_8_12_plus_four_smokers_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let p : ℝ := (6 + 2) / (25 + 4)
    let ebp : ℝ := 1.96 * √(p * (1 - p) / (25 + 4))
    p = 8 / 29 ∧ 0.1624 < ebp ∧ ebp < 0.1627 ∧
      0.113 < p - ebp ∧ p - ebp < 0.114 ∧ 0.438 < p + ebp ∧ p + ebp < 0.439 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro p ebp
  have hp : p = 8 / 29 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.0829 : ℝ) < √(p * (1 - p) / (25 + 4)) ∧
      √(p * (1 - p) / (25 + 4)) < 0.083 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;> norm_num at r1 r2 ⊢
    <;> linarith

/-- OpenStax Introductory Statistics 2e Example 8.13. Plus-four interval for `13` of `50` adults
considering an electric vehicle: adjusted counts `x = 15`, `n = 54`, `p' = 15/54 = 5/18`. With the 90%
critical value `1.645` (central standard normal mass in `(0.8999, 0.9001)`), the error bound lies in
`(0.1002, 0.1003)` (book `0.100`) and the interval has endpoints in `(0.177, 0.178)` and
`(0.378, 0.379)` (book `(0.178, 0.378)`). -/
@[kb "openstaxintrostats2e" "Example 8.13, p. 437"]
theorem example_8_13_plus_four_electric_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let p : ℝ := (13 + 2) / (50 + 4)
    let ebp : ℝ := 1.645 * √(p * (1 - p) / (50 + 4))
    p = 5 / 18 ∧ 0.1002 < ebp ∧ ebp < 0.1003 ∧
      0.177 < p - ebp ∧ p - ebp < 0.178 ∧ 0.378 < p + ebp ∧ p + ebp < 0.379 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro p ebp
  have hp : p = 5 / 18 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.06095 : ℝ) < √(p * (1 - p) / (50 + 4)) ∧
      √(p * (1 - p) / (50 + 4)) < 0.06096 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;> norm_num at r1 r2 ⊢
    <;> linarith

/-- OpenStax Introductory Statistics 2e Example 8.14. To be within `0.03` of a proportion with 90%
confidence (critical value `1.645`, central standard normal mass in `(0.8999, 0.9001)`) and the
worst case `p' = q' = 0.5`, the sample size must satisfy `n ≥ 1.645² · 0.25 / 0.03²`, which is
`751.67…`; `752` is the least natural number that does (`751` fails). -/
@[kb "openstaxintrostats2e" "Example 8.14, p. 438"]
theorem example_8_14_sample_size_text_messaging :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    (751 : ℝ) < 1.645 ^ 2 * (0.5 * 0.5) / 0.03 ^ 2 ∧
      (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.03 ^ 2 < 752 ∧
      IsLeast {n : ℕ | (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.03 ^ 2 ≤ n} 752 := by
  refine ⟨critical_values_standard_normal.1, by norm_num, by norm_num, ?_, ?_⟩
  · show (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.03 ^ 2 ≤ ((752 : ℕ) : ℝ)
    norm_num
  · intro n hn
    by_contra h
    have : n ≤ 751 := by omega
    have h2 : (n : ℝ) ≤ 751 := by exact_mod_cast this
    have h3 : (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.03 ^ 2 ≤ n := hn
    norm_num at h3
    linarith

end UndergradKB.Statistics.Course.ExamplesC8
