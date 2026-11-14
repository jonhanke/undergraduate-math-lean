import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.CriticalValues

/-!
# Course layer, chapter 8 (OpenStax *Introductory Statistics 2e*): Try It exercises

Confidence intervals. For the `z` intervals the critical value (`1.645`, `1.96`, and for the
non-standard levels `1.812` and `2.054`) is shown to cut off the stated central mass of the standard
normal law (`1.645` and `1.96` through `critical_values_standard_normal`), and the margin of error and
endpoints follow by arithmetic. For the `t` intervals the Student `t` value is the book's table
constant (it is not computed here); the sample mean, standard deviation, margin of error and endpoints
are proved. Proportion intervals and sample-size calculations are exact or two-sided bounds around
rounded values.
-/

namespace UndergradKB.Statistics.Course.TryItC8

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

/-- OpenStax Introductory Statistics 2e Try It 8.1. Sample mean `15` and error bound `3.2` give the
interval `(11.8, 18.2)`. -/
@[kb "openstaxintrostats2e" "Try It 8.1, p. 419"]
theorem tryit_8_1_interval_from_error_bound :
    (15 : ℝ) - 3.2 = 11.8 ∧ (15 : ℝ) + 3.2 = 18.2 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 8.2. Pizza delivery times with `σ = 6`, `n = 28`, mean
`36`, 90% confidence. The critical value `1.645` leaves central standard normal mass in
`(0.8999, 0.9001)`; the margin of error `1.645 · 6/√28` lies in `(1.865, 1.866)` and the interval has
endpoints in `(34.134, 34.135)` and `(37.865, 37.866)` (about `(34.13, 37.87)`). -/
@[kb "openstaxintrostats2e" "Try It 8.2, p. 423"]
theorem tryit_8_2_pizza_delivery_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let ebm : ℝ := 1.645 * (6 / √28)
    1.865 < ebm ∧ ebm < 1.866 ∧
      34.134 < 36 - ebm ∧ 36 - ebm < 34.135 ∧ 37.865 < 36 + ebm ∧ 36 + ebm < 37.866 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro ebm
  obtain ⟨h1, h2⟩ := sqrt_between (x := 28) (a := 5.2915) (b := 5.2916) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := 6) (a := 6) (b := 6) (by norm_num) le_rfl le_rfl
    (by norm_num) h1 h2
  simp only [ebm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at d1 d2 ⊢ <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.3. Twenty SAR values (Table 8.2) with `σ = 0.337`
have mean exactly `0.94005`. The 93% critical value `1.812` leaves central standard normal mass in
`(0.9299, 0.9302)` (its table value is `1.8119`); the margin of error lies in `(0.1365, 0.1366)` and
the interval has endpoints in `(0.8035, 0.8036)` and `(1.0765, 1.0766)`. -/
@[kb "openstaxintrostats2e" "Try It 8.3, p. 424"]
theorem tryit_8_3_sar_93 :
    (0.9299 < centralMass 1.812 ∧ centralMass 1.812 < 0.9302) ∧
    let x : Fin 20 → ℝ := ![1.48, 1.53, 0.8, 0.68, 1.15, 1.4, 1.36, 1.24, 0.77, 0.57, 0.462, 0.2,
      1.36, 0.51, 1.39, 0.3, 1.3, 0.73, 0.7, 0.869]
    let ebm : ℝ := 1.812 * (0.337 / √20)
    mean x = 0.94005 ∧ 0.1365 < ebm ∧ ebm < 0.1366 ∧
      0.8035 < mean x - ebm ∧ mean x - ebm < 0.8036 ∧
      1.0765 < mean x + ebm ∧ mean x + ebm < 1.0766 := by
  refine ⟨?_, ?_⟩
  · exact Ioo_enclosure (k := 1.812) (a := 0.9299) (b := 0.9302) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  intro x ebm
  have hm : mean x = 0.94005 := by
    simp [mean, x, Fin.sum_univ_succ]; norm_num
  obtain ⟨h1, h2⟩ := sqrt_between (x := 20) (a := 4.4721) (b := 4.4722) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := 0.337) (a := 0.337) (b := 0.337) (by norm_num) le_rfl le_rfl
    (by norm_num) h1 h2
  rw [hm]
  simp only [ebm]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at d1 d2 ⊢ <;> linarith

/-! ### Section 8.1 continued: changing the level or the sample size -/

/-- OpenStax Introductory Statistics 2e Try It 8.4. The pizza delivery study again with `n = 20`,
mean `36`, `σ = 6` and 95% confidence (critical value `1.96`, central standard normal mass in
`(0.9499, 0.9501)`). The margin of error lies in `(2.629, 2.630)` and the interval has endpoints in
`(33.370, 33.371)` and `(38.629, 38.630)`. -/
@[kb "openstaxintrostats2e" "Try It 8.4, p. 426"]
theorem tryit_8_4_pizza_delivery_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let ebm : ℝ := 1.96 * (6 / √20)
    2.629 < ebm ∧ ebm < 2.630 ∧
      33.370 < 36 - ebm ∧ 36 - ebm < 33.371 ∧ 38.629 < 36 + ebm ∧ 36 + ebm < 38.630 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro ebm
  obtain ⟨h1, h2⟩ := sqrt_between (x := 20) (a := 4.4721) (b := 4.4722) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := 6) (a := 6) (b := 6) (by norm_num) le_rfl le_rfl
    (by norm_num) h1 h2
  simp only [ebm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at d1 d2 ⊢ <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.5. The pizza delivery study with `n = 50`, mean `36`,
`σ = 6` and 90% confidence (critical value `1.645`, central standard normal mass in
`(0.8999, 0.9001)`). The margin of error lies in `(1.395, 1.396)`, the interval has endpoints in
`(34.604, 34.605)` and `(37.395, 37.396)`, and the margin is smaller than the `n = 28` margin
`1.865` of Try It 8.2. -/
@[kb "openstaxintrostats2e" "Try It 8.5, p. 427"]
theorem tryit_8_5_pizza_delivery_n50 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let ebm : ℝ := 1.645 * (6 / √50)
    1.395 < ebm ∧ ebm < 1.396 ∧ ebm < 1.865 ∧
      34.604 < 36 - ebm ∧ 36 - ebm < 34.605 ∧ 37.395 < 36 + ebm ∧ 36 + ebm < 37.396 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro ebm
  obtain ⟨h1, h2⟩ := sqrt_between (x := 50) (a := 7.071) (b := 7.0711) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := 6) (a := 6) (b := 6) (by norm_num) le_rfl le_rfl
    (by norm_num) h1 h2
  simp only [ebm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at d1 d2 ⊢ <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.6. From the interval `(42.12, 47.88)` the error bound
is half the width, `2.88`, and the sample mean is the midpoint, `45`; also `47.88 - 45 = 2.88` and
`47.88 - 2.88 = 45`. -/
@[kb "openstaxintrostats2e" "Try It 8.6, p. 428"]
theorem tryit_8_6_working_backwards :
    ((47.88 : ℝ) - 42.12) / 2 = 2.88 ∧ ((47.88 : ℝ) + 42.12) / 2 = 45 ∧
      (47.88 : ℝ) - 45 = 2.88 ∧ (47.88 : ℝ) - 2.88 = 45 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 8.7. With `σ = 3`, margin `1` and the 95% critical
value `1.96` (central standard normal mass in `(0.9499, 0.9501)`), the sample size must satisfy
`n ≥ (1.96 · 3/1)² = 34.5744`; `35` is the least such natural number. -/
@[kb "openstaxintrostats2e" "Try It 8.7, p. 428"]
theorem tryit_8_7_sample_size_heights :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    (1.96 * 3 / 1 : ℝ) ^ 2 = 34.5744 ∧
      IsLeast {n : ℕ | (1.96 * 3 / 1 : ℝ) ^ 2 ≤ n} 35 := by
  refine ⟨critical_values_standard_normal.2.1, by norm_num, ?_, ?_⟩
  · show (1.96 * 3 / 1 : ℝ) ^ 2 ≤ ((35 : ℕ) : ℝ)
    norm_num
  · intro n hn
    by_contra h
    have : n ≤ 34 := by omega
    have h2 : (n : ℝ) ≤ 34 := by exact_mod_cast this
    have h3 : (1.96 * 3 / 1 : ℝ) ^ 2 ≤ n := hn
    norm_num at h3
    linarith

/-! ### Section 8.2: mean, unknown standard deviation (Student `t`) -/

/-- OpenStax Introductory Statistics 2e Try It 8.8. Hours of sleep of `12` subjects. The sample mean is
exactly `539/60` (about `8.9833`), the sample variance exactly `1099/660`, and the standard deviation
lies in `(1.2904, 1.2905)`. Taking the table value `t = 2.201` for `11` degrees of freedom from the
book (not computed here), the 95% interval has lower endpoint in `(8.163, 8.164)` and upper endpoint in
`(9.803, 9.804)`. -/
@[kb "openstaxintrostats2e" "Try It 8.8, p. 431"]
theorem tryit_8_8_hypnotherapy_t95 :
    let x : Fin 12 → ℝ := ![8.2, 9.1, 7.7, 8.6, 6.9, 11.2, 10.1, 9.9, 8.9, 9.2, 7.5, 10.5]
    let tstar : ℝ := 2.201
    mean x = 539 / 60 ∧ sampleVariance x = 1099 / 660 ∧
      1.2904 < sampleStdDev x ∧ sampleStdDev x < 1.2905 ∧
      8.163 < mean x - tstar * (sampleStdDev x / √12) ∧
      mean x - tstar * (sampleStdDev x / √12) < 8.164 ∧
      9.803 < mean x + tstar * (sampleStdDev x / √12) ∧
      mean x + tstar * (sampleStdDev x / √12) < 9.804 := by
  intro x tstar
  have hm : mean x = 539 / 60 := by
    simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 1099 / 660 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  obtain ⟨s1, s2⟩ : 1.2904 < sampleStdDev x ∧ sampleStdDev x < 1.2905 := by
    rw [sampleStdDev, hv]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r1, r2⟩ := sqrt_between (x := 12) (a := 3.4641) (b := 3.4642) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := sampleStdDev x) (a := 1.2904) (b := 1.2905) (by norm_num)
    s1.le s2.le (by norm_num) r1 r2
  refine ⟨hm, hv, s1, s2, ?_, ?_, ?_, ?_⟩ <;> simp only [tstar] <;> rw [hm] <;> norm_num at d1 d2 ⊢
    <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.9. Weekly television hours of `15` statistics
students (Table 8.4). The sample mean is exactly `92/15`, the sample variance exactly `3193/105`, and
the standard deviation lies in `(5.5144, 5.5145)`. Taking the table value `t = 2.624` for `14` degrees
of freedom from the book (not computed here), the 98% interval has lower endpoint in `(2.397, 2.398)`
and upper endpoint in `(9.869, 9.870)`. -/
@[kb "openstaxintrostats2e" "Try It 8.9, p. 432"]
theorem tryit_8_9_television_t98 :
    let x : Fin 15 → ℝ := ![0, 3, 1, 20, 9, 5, 10, 1, 10, 4, 14, 2, 4, 4, 5]
    let tstar : ℝ := 2.624
    mean x = 92 / 15 ∧ sampleVariance x = 3193 / 105 ∧
      5.5144 < sampleStdDev x ∧ sampleStdDev x < 5.5145 ∧
      2.397 < mean x - tstar * (sampleStdDev x / √15) ∧
      mean x - tstar * (sampleStdDev x / √15) < 2.398 ∧
      9.869 < mean x + tstar * (sampleStdDev x / √15) ∧
      mean x + tstar * (sampleStdDev x / √15) < 9.870 := by
  intro x tstar
  have hm : mean x = 92 / 15 := by
    simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 3193 / 105 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  obtain ⟨s1, s2⟩ : 5.5144 < sampleStdDev x ∧ sampleStdDev x < 5.5145 := by
    rw [sampleStdDev, hv]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r1, r2⟩ := sqrt_between (x := 15) (a := 3.8729) (b := 3.873) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨d1, d2⟩ := div_bounds (s := sampleStdDev x) (a := 5.5144) (b := 5.5145) (by norm_num)
    s1.le s2.le (by norm_num) r1 r2
  refine ⟨hm, hv, s1, s2, ?_, ?_, ?_, ?_⟩ <;> simp only [tstar] <;> rw [hm] <;> norm_num at d1 d2 ⊢
    <;> linarith

/-! ### Section 8.3: proportions -/

/-- OpenStax Introductory Statistics 2e Try It 8.10. `98` of `250` surveyed people own a tablet:
`p' = 98/250 = 0.392`. With the 95% critical value `1.96` (central standard normal mass in
`(0.9499, 0.9501)`), the error bound `1.96 √(p'q'/n)` lies in `(0.0605, 0.0606)` and the interval has
endpoints in `(0.3314, 0.3315)` and `(0.4525, 0.4526)`. -/
@[kb "openstaxintrostats2e" "Try It 8.10, p. 434"]
theorem tryit_8_10_tablets_95 :
    (0.9499 < centralMass 1.96 ∧ centralMass 1.96 < 0.9501) ∧
    let p : ℝ := 98 / 250
    let ebp : ℝ := 1.96 * √(p * (1 - p) / 250)
    p = 0.392 ∧ 0.0605 < ebp ∧ ebp < 0.0606 ∧
      0.3314 < p - ebp ∧ p - ebp < 0.3315 ∧ 0.4525 < p + ebp ∧ p + ebp < 0.4526 := by
  refine ⟨critical_values_standard_normal.2.1, ?_⟩
  intro p ebp
  have hp : p = 0.392 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.03087 : ℝ) < √(p * (1 - p) / 250) ∧ √(p * (1 - p) / 250) < 0.03088 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;> norm_num at r1 r2 ⊢
    <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.11. `480` of `600` students are against the new
legislation, `p' = 0.8`. With the 90% critical value `1.645` (central standard normal mass in
`(0.8999, 0.9001)`), the error bound lies in `(0.0268, 0.0269)` and the interval has endpoints in
`(0.7731, 0.7732)` and `(0.8268, 0.8269)`, about 77.3% to 82.7%. -/
@[kb "openstaxintrostats2e" "Try It 8.11, p. 436"]
theorem tryit_8_11_school_uniforms_90 :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let p : ℝ := 480 / 600
    let ebp : ℝ := 1.645 * √(p * (1 - p) / 600)
    p = 0.8 ∧ 0.0268 < ebp ∧ ebp < 0.0269 ∧
      0.7731 < p - ebp ∧ p - ebp < 0.7732 ∧ 0.8268 < p + ebp ∧ p + ebp < 0.8269 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro p ebp
  have hp : p = 0.8 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.01632 : ℝ) < √(p * (1 - p) / 600) ∧ √(p * (1 - p) / 600) < 0.01633 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;> norm_num at r1 r2 ⊢
    <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.12. Plus-four interval for `31` of `65` first-year
students with a declared major: adjusted counts `x = 33`, `n = 69`, `p' = 33/69 = 11/23`. The 96%
critical value `2.054` (its table value is `2.0537`) leaves central standard normal mass in
`(0.9599, 0.9602)`; the error bound lies in `(0.1235, 0.1236)` and the interval has endpoints in
`(0.3547, 0.3548)` and `(0.6017, 0.6018)`. -/
@[kb "openstaxintrostats2e" "Try It 8.12, p. 437"]
theorem tryit_8_12_plus_four_major_96 :
    (0.9599 < centralMass 2.054 ∧ centralMass 2.054 < 0.9602) ∧
    let p : ℝ := (31 + 2) / (65 + 4)
    let ebp : ℝ := 2.054 * √(p * (1 - p) / (65 + 4))
    p = 11 / 23 ∧ 0.1235 < ebp ∧ ebp < 0.1236 ∧
      0.3547 < p - ebp ∧ p - ebp < 0.3548 ∧ 0.6017 < p + ebp ∧ p + ebp < 0.6018 := by
  refine ⟨?_, ?_⟩
  · exact Ioo_enclosure (k := 2.054) (a := 0.9599) (b := 0.9602) (by norm_num) 14 (by norm_num)
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
      (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  intro p ebp
  have hp : p = 11 / 23 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.06013 : ℝ) < √(p * (1 - p) / (65 + 4)) ∧
      √(p * (1 - p) / (65 + 4)) < 0.06014 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;> norm_num at r1 r2 ⊢
    <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.13. Plus-four interval for `159` of `588` adults
considering an electric vehicle: adjusted counts `x = 161`, `n = 592`, `p' = 161/592`. With the 90%
critical value `1.645` (central standard normal mass in `(0.8999, 0.9001)`), the error bound lies in
`(0.0300, 0.0301)` and the interval has endpoints in `(0.2418, 0.2419)` and `(0.3020, 0.3021)`; it is
narrower (width below `0.0603`) than the interval of Example 8.13, whose width exceeds `0.2` (error
bound above `0.1002`). -/
@[kb "openstaxintrostats2e" "Try It 8.13, p. 438"]
theorem tryit_8_13_plus_four_electric_larger_sample :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    let p : ℝ := (159 + 2) / (588 + 4)
    let ebp : ℝ := 1.645 * √(p * (1 - p) / (588 + 4))
    p = 161 / 592 ∧ 0.0300 < ebp ∧ ebp < 0.0301 ∧
      0.2418 < p - ebp ∧ p - ebp < 0.2419 ∧ 0.3020 < p + ebp ∧ p + ebp < 0.3021 ∧
      (p + ebp) - (p - ebp) < 0.0603 ∧ 2 * ebp < 0.2 := by
  refine ⟨critical_values_standard_normal.1, ?_⟩
  intro p ebp
  have hp : p = 161 / 592 := by simp only [p]; norm_num
  obtain ⟨r1, r2⟩ : (0.01828 : ℝ) < √(p * (1 - p) / (588 + 4)) ∧
      √(p * (1 - p) / (588 + 4)) < 0.01829 := by
    rw [hp]
    exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ebp] <;> rw [hp] at * <;>
    norm_num at r1 r2 ⊢ <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 8.14. To be within `0.05` of a proportion with 90%
confidence (critical value `1.645`, central standard normal mass in `(0.8999, 0.9001)`) and the worst
case `p' = q' = 0.5`, the sample size must satisfy `n ≥ 1.645² · 0.25 / 0.05²`, which is `270.6025`;
`271` is the least natural number that does. -/
@[kb "openstaxintrostats2e" "Try It 8.14, p. 439"]
theorem tryit_8_14_sample_size_ads :
    (0.8999 < centralMass 1.645 ∧ centralMass 1.645 < 0.9001) ∧
    (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 = 270.6025 ∧
      IsLeast {n : ℕ | (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ n} 271 := by
  refine ⟨critical_values_standard_normal.1, by norm_num, ?_, ?_⟩
  · show (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ ((271 : ℕ) : ℝ)
    norm_num
  · intro n hn
    by_contra h
    have : n ≤ 270 := by omega
    have h2 : (n : ℝ) ≤ 270 := by exact_mod_cast this
    have h3 : (1.645 : ℝ) ^ 2 * (0.5 * 0.5) / 0.05 ^ 2 ≤ n := hn
    norm_num at h3
    linarith

end UndergradKB.Statistics.Course.TryItC8
