import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Anova

/-!
# "Try It" exercises, chapter 13 (OpenStax *Introductory Statistics 2e*): F distribution and ANOVA

The arithmetic of the one-way analysis of variance (sums of squares, mean squares, the `F` ratio) and of
the two-variance test (the ratio of sample variances). Quantiles of the `F` distribution and p-values are
not computable in this repository: where an exercise asks for a decision, the critical value is the
table value (named in the statement, not proved) and only the comparison is proved.
-/

namespace UndergradKB.Statistics.Course.TryItC13

open UndergradKB.Statistics

/-- OpenStax Introductory Statistics 2e Try It 13.1. Tomato yields (grams) under five soil covers with
three plants each. The ANOVA table: `SS(between) = 549728414/15` with `5 - 1 = 4` degrees of freedom and
mean square `274864207/30`; `SS(within) = 20446726` with `15 - 5 = 10` degrees of freedom and mean square
`10223363/5 = 2044672.6`; the `F` ratio is `274864207/61340178`, strictly between `4.480` and `4.482`. -/
@[kb "openstaxintrostats2e" "Try It 13.1, p. 695"]
theorem tryit_13_1_tomato_anova_table :
    let x : Fin 15 → ℝ := ![2625, 2997, 4915, 5348, 5682, 5482, 6583, 8560, 3830, 7285, 6897, 9230,
      6277, 7818, 8677]
    let g : Fin 15 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4]
    ssBetween x g = 549728414 / 15 ∧ msBetween x g = 274864207 / 30 ∧ ssWithin x g = 20446726 ∧
      msWithin x g = 2044672.6 ∧ fStatistic x g = 274864207 / 61340178 ∧
      4.480 < fStatistic x g ∧ fStatistic x g < 4.482 ∧ (5 : ℕ) - 1 = 4 ∧ (15 : ℕ) - 5 = 10 := by
  intro x g
  have hs : ∀ j, groupSize g j = (![3, 3, 3, 3, 3] : Fin 5 → ℕ) j := by
    intro j; fin_cases j <;> decide
  have hb : ssBetween x g = 549728414 / 15 := by
    simp only [ssBetween, groupMean, hs]
    simp [mean, x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hw : ssWithin x g = 20446726 := by
    simp only [ssWithin, groupMean, hs]
    simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hmb : msBetween x g = 274864207 / 30 := by
    rw [msBetween, hb]; norm_num
  have hmw : msWithin x g = 2044672.6 := by
    rw [msWithin, hw]; norm_num
  have hf : fStatistic x g = 274864207 / 61340178 := by
    rw [fStatistic, hmb, hmw]; norm_num
  rw [hf]
  exact ⟨hb, hmb, hw, hmw, rfl, by norm_num, by norm_num, rfl, rfl⟩

/-- OpenStax Introductory Statistics 2e Try It 13.2. Hospital stays (days) for five COVID-19 strains,
three patients each. The between-group sum of squares is `1757/125`, the within-group sum of squares
`2488/25`, the mean squares are `1757/500` and `1244/125`, and the `F` ratio is `1757/4976`, strictly
between `0.353` and `0.354`, with `4` and `10` degrees of freedom. The book's table critical value for the
5% level, `3.48` (not proved here), exceeds it, so the equality of mean stays is not rejected. -/
@[kb "openstaxintrostats2e" "Try It 13.2, p. 698"]
theorem tryit_13_2_covid_anova :
    let x : Fin 15 → ℝ := ![13.9, 14.9, 16.8, 11.7, 15.1, 9.9, 18.2, 14.6, 10.1, 16.9, 12.8, 11.2,
      9.3, 15.8, 16.4]
    let g : Fin 15 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4]
    ssBetween x g = 1757 / 125 ∧ ssWithin x g = 2488 / 25 ∧ msBetween x g = 1757 / 500 ∧
      msWithin x g = 1244 / 125 ∧ fStatistic x g = 1757 / 4976 ∧
      0.353 < fStatistic x g ∧ fStatistic x g < 0.354 ∧ (5 : ℕ) - 1 = 4 ∧ (15 : ℕ) - 5 = 10 ∧
      (let fCrit : ℝ := 3.48; fStatistic x g < fCrit) := by
  intro x g
  have hs : ∀ j, groupSize g j = (![3, 3, 3, 3, 3] : Fin 5 → ℕ) j := by
    intro j; fin_cases j <;> decide
  have hb : ssBetween x g = 1757 / 125 := by
    simp only [ssBetween, groupMean, hs]
    simp [mean, x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hw : ssWithin x g = 2488 / 25 := by
    simp only [ssWithin, groupMean, hs]
    simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hmb : msBetween x g = 1757 / 500 := by
    rw [msBetween, hb]; norm_num
  have hmw : msWithin x g = 1244 / 125 := by
    rw [msWithin, hw]; norm_num
  have hf : fStatistic x g = 1757 / 4976 := by
    rw [fStatistic, hmb, hmw]; norm_num
  rw [hf]
  exact ⟨hb, hw, hmb, hmw, rfl, by norm_num, by norm_num, rfl, rfl, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 13.3. GPAs of five players on each of four teams
(basketball, baseball, hockey, lacrosse). The group means are `161/50, 151/50, 3, 147/50`; the
between-group sum of squares is `443/2000`, the within-group sum of squares `1947/250`, the mean squares
`443/6000` and `1947/4000`, and the `F` ratio is `886/5841`, strictly between `0.151` and `0.152`, with `3`
and `16` degrees of freedom. The book's table critical value for the 5% level, `3.24` (not proved here),
exceeds it, so no difference among the teams is detected. -/
@[kb "openstaxintrostats2e" "Try It 13.3, p. 700"]
theorem tryit_13_3_gpa_anova :
    let x : Fin 20 → ℝ := ![3.6, 2.9, 2.5, 3.3, 3.8, 2.1, 2.6, 3.9, 3.1, 3.4, 4.0, 2.0, 2.6, 3.2, 3.2,
      2.0, 3.6, 3.9, 2.7, 2.5]
    let g : Fin 20 → Fin 4 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3]
    groupMean x g 0 = 161 / 50 ∧ groupMean x g 1 = 151 / 50 ∧ groupMean x g 2 = 3 ∧
      groupMean x g 3 = 147 / 50 ∧ ssBetween x g = 443 / 2000 ∧ ssWithin x g = 1947 / 250 ∧
      msBetween x g = 443 / 6000 ∧ msWithin x g = 1947 / 4000 ∧ fStatistic x g = 886 / 5841 ∧
      0.151 < fStatistic x g ∧ fStatistic x g < 0.152 ∧ (4 : ℕ) - 1 = 3 ∧ (20 : ℕ) - 4 = 16 ∧
      (let fCrit : ℝ := 3.24; fStatistic x g < fCrit) := by
  intro x g
  have hs : ∀ j, groupSize g j = (![5, 5, 5, 5] : Fin 4 → ℕ) j := by
    intro j; fin_cases j <;> decide
  have hm : groupMean x g 0 = 161 / 50 ∧ groupMean x g 1 = 151 / 50 ∧ groupMean x g 2 = 3 ∧
      groupMean x g 3 = 147 / 50 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [groupMean, hs]
      simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
      norm_num
  have hb : ssBetween x g = 443 / 2000 := by
    simp only [ssBetween, groupMean, hs]
    simp [mean, x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hw : ssWithin x g = 1947 / 250 := by
    simp only [ssWithin, groupMean, hs]
    simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hmb : msBetween x g = 443 / 6000 := by
    rw [msBetween, hb]; norm_num
  have hmw : msWithin x g = 1947 / 4000 := by
    rw [msWithin, hw]; norm_num
  have hf : fStatistic x g = 886 / 5841 := by
    rw [fStatistic, hmb, hmw]; norm_num
  rw [hf]
  exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, hb, hw, hmb, hmw, rfl, by norm_num, by norm_num, rfl, rfl,
    by norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 13.4. The three bean-plant groups of the worked example
(heights `24, 21, 23, 30, 23`; `25, 31, 23, 20, 28`; `23, 27, 22, 30, 20`) together with a fourth group
grown in a jelly-like mass (`24, 28, 25, 30, 32`). The group means are `121/5, 127/5, 122/5, 139/5`; the
between-group sum of squares is `819/20`, the within-group sum of squares `230`, the mean squares `273/20`
and `115/8`, and the `F` ratio is `546/575`, strictly between `0.949` and `0.950`, with `3` and `16`
degrees of freedom. The book's table critical value for the 5% level, `3.24` (not proved here), exceeds it,
so a difference in mean heights is not established. -/
@[kb "openstaxintrostats2e" "Try It 13.4, p. 702"]
theorem tryit_13_4_bean_four_groups :
    let x : Fin 20 → ℝ := ![24, 21, 23, 30, 23, 25, 31, 23, 20, 28, 23, 27, 22, 30, 20, 24, 28, 25,
      30, 32]
    let g : Fin 20 → Fin 4 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3]
    groupMean x g 0 = 121 / 5 ∧ groupMean x g 1 = 127 / 5 ∧ groupMean x g 2 = 122 / 5 ∧
      groupMean x g 3 = 139 / 5 ∧ ssBetween x g = 819 / 20 ∧ ssWithin x g = 230 ∧
      msBetween x g = 273 / 20 ∧ msWithin x g = 115 / 8 ∧ fStatistic x g = 546 / 575 ∧
      0.949 < fStatistic x g ∧ fStatistic x g < 0.950 ∧ (4 : ℕ) - 1 = 3 ∧ (20 : ℕ) - 4 = 16 ∧
      (let fCrit : ℝ := 3.24; fStatistic x g < fCrit) := by
  intro x g
  have hs : ∀ j, groupSize g j = (![5, 5, 5, 5] : Fin 4 → ℕ) j := by
    intro j; fin_cases j <;> decide
  have hm : groupMean x g 0 = 121 / 5 ∧ groupMean x g 1 = 127 / 5 ∧ groupMean x g 2 = 122 / 5 ∧
      groupMean x g 3 = 139 / 5 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [groupMean, hs]
      simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
      norm_num
  have hb : ssBetween x g = 819 / 20 := by
    simp only [ssBetween, groupMean, hs]
    simp [mean, x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hw : ssWithin x g = 230 := by
    simp only [ssWithin, groupMean, hs]
    simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hmb : msBetween x g = 273 / 20 := by
    rw [msBetween, hb]; norm_num
  have hmw : msWithin x g = 115 / 8 := by
    rw [msWithin, hw]; norm_num
  have hf : fStatistic x g = 546 / 575 := by
    rw [fStatistic, hmb, hmw]; norm_num
  rw [hf]
  exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, hb, hw, hmb, hmw, rfl, by norm_num, by norm_num, rfl, rfl,
    by norm_num⟩

/-- Heights of the 21 Tenor1 singers of Table 13.11. -/
private def tenorHeights : Fin 21 → ℝ :=
  ![69, 72, 71, 66, 76, 74, 71, 66, 68, 67, 70, 65, 72, 70, 68, 64, 73, 66, 68, 67, 64]

/-- Heights of the 26 Bass2 singers of Table 13.11. -/
private def bassHeights : Fin 26 → ℝ :=
  ![72, 75, 67, 75, 74, 72, 72, 74, 72, 72, 74, 70, 66, 68, 75, 68, 70, 72, 67, 70, 70, 69, 72, 71,
    74, 75]

/-- OpenStax Introductory Statistics 2e Try It 13.5. Heights of 21 Tenor1 and 26 Bass2 singers. The sample
variances are exactly `2329/210` (about `11.09`) and `484/65` (about `7.45`) (for the Tenor1 group
the sample mean is `1447/21`, for the Bass2 group `928/13`), so the ratio of the Tenor1 variance to the
Bass2 variance is `30277/20328`, strictly between `1.489` and `1.490`, with `20` and `25` degrees of
freedom. For the two-sided test at the 5% level the upper critical value is about `2.30` (a table value,
not proved here); the ratio is below it, so equal variances are not rejected. -/
@[kb "openstaxintrostats2e" "Try It 13.5, p. 704"]
theorem tryit_13_5_two_variances :
    mean tenorHeights = 1447 / 21 ∧ mean bassHeights = 928 / 13 ∧
      sampleVariance tenorHeights = 2329 / 210 ∧ sampleVariance bassHeights = 484 / 65 ∧
      sampleVariance tenorHeights / sampleVariance bassHeights = 30277 / 20328 ∧
      1.489 < sampleVariance tenorHeights / sampleVariance bassHeights ∧
      sampleVariance tenorHeights / sampleVariance bassHeights < 1.490 ∧
      (21 : ℕ) - 1 = 20 ∧ (26 : ℕ) - 1 = 25 ∧
      (let fCrit : ℝ := 2.30; sampleVariance tenorHeights / sampleVariance bassHeights < fCrit) := by
  have hm1 : mean tenorHeights = 1447 / 21 := by
    simp [mean, tenorHeights, Fin.sum_univ_succ]
    norm_num
  have hm2 : mean bassHeights = 928 / 13 := by
    simp [mean, bassHeights, Fin.sum_univ_succ]
    norm_num
  have hv1 : sampleVariance tenorHeights = 2329 / 210 := by
    simp only [sampleVariance, sumSqDev, hm1]
    simp [tenorHeights, Fin.sum_univ_succ]
    norm_num
  have hv2 : sampleVariance bassHeights = 484 / 65 := by
    simp only [sampleVariance, sumSqDev, hm2]
    simp [bassHeights, Fin.sum_univ_succ]
    norm_num
  have hr : sampleVariance tenorHeights / sampleVariance bassHeights = 30277 / 20328 := by
    rw [hv1, hv2]; norm_num
  rw [hr]
  exact ⟨hm1, hm2, hv1, hv2, rfl, by norm_num, by norm_num, rfl, rfl, by norm_num⟩

end UndergradKB.Statistics.Course.TryItC13
