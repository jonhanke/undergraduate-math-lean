import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Anova
import UndergradKB.Statistics.Pearson
import UndergradKB.Statistics.IndependenceTest

/-!
# Course layer, chapters 7 to 13 (OpenStax *Introductory Statistics 2e*): worked examples

Exact chi-square statistics computed from given observed tables (chapter 11), one-way analysis of
variance for small data sets (chapter 13, reusing `ssBetween`, `ssWithin`, `fStatistic` from
`Anova.lean`), and a few exact test-statistic computations from chapters 7, 9 and 10 (standard
errors, `z` and `t` statistics, Cohen's `d`). Where the book rounds, a two-sided bound is proved.
-/

namespace UndergradKB.Statistics.Course.ExamplesC11C13

open UndergradKB.Statistics

/-! ### Chi-square statistics of given tables -/

/-- The chi-square statistic `∑ (Oᵢ - Eᵢ)² / Eᵢ` of observed counts `O` and expected counts `E`. -/
noncomputable def chiSquareStat {ι : Type*} [Fintype ι] (O E : ι → ℝ) : ℝ :=
  ∑ i, (O i - E i) ^ 2 / E i

/-- The expected count `(row total)(column total)/(grand total)` of cell `(i, j)` of a table `O`. -/
noncomputable def tableExpected {r c : ℕ} (O : Fin r → Fin c → ℝ) (i : Fin r) (j : Fin c) : ℝ :=
  (∑ j', O i j') * (∑ i', O i' j) / ∑ i', ∑ j', O i' j'

/-- The chi-square statistic `∑ (O - E)² / E` of an observed table, with the expected counts of
independence (or homogeneity). -/
noncomputable def tableChiSquare {r c : ℕ} (O : Fin r → Fin c → ℝ) : ℝ :=
  ∑ i, ∑ j, (O i j - tableExpected O i j) ^ 2 / tableExpected O i j

/-- The goodness-of-fit statistic of `Pearson.lean` is the chi-square statistic of the observed counts
against the expected counts `n pᵢ`. -/
theorem pearsonStatistic_eq_chiSquareStat {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : ι → ℝ) (C : ℕ → Ω → ι)
    (n : ℕ) (ω : Ω) :
    pearsonStatistic p C n ω = chiSquareStat (fun i => observedCount C n i ω) (fun i => n * p i) :=
  rfl

/-- The independence statistic of `IndependenceTest.lean` is the chi-square statistic of the observed
table, when the table entries add up to the number `n` of observations. -/
theorem independenceStatistic_eq_tableChiSquare {Ω : Type*} [MeasurableSpace Ω] {r c : ℕ}
    (C : ℕ → Ω → Fin r × Fin c) (n : ℕ) (ω : Ω)
    (hn : ∑ i, ∑ j, observedCount C n (i, j) ω = n) :
    independenceStatistic C n ω = tableChiSquare (fun i j => observedCount C n (i, j) ω) := by
  unfold independenceStatistic expectedCount rowTotal colTotal tableChiSquare tableExpected
  rw [hn]

/-- OpenStax Introductory Statistics 2e Example 11.2. Sixty managers name the weekday with the most
absences: observed counts `15, 12, 9, 9, 15` against `12` expected on each of the five days. The
chi-square statistic is exactly `3`, with `5 - 1 = 4` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.2, p. 580"]
theorem example_11_2_goodness_of_fit_equal_days :
    chiSquareStat (![15, 12, 9, 9, 15] : Fin 5 → ℝ) (fun _ => 12) = 3 ∧ Fintype.card (Fin 5) - 1 = 4 := by
  refine ⟨?_, rfl⟩
  simp [chiSquareStat, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 11.3. A sample of 600 families gives streaming-service
counts `66, 119, 340, 60, 15`; the national percentages `10, 16, 55, 11, 8` give expected counts
`60, 96, 330, 66, 48`. The chi-square statistic is exactly `156533/5280`, strictly between `29.64`
and `29.65` (the book's `29.65`), with `5 - 1 = 4` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.3, p. 581"]
theorem example_11_3_goodness_of_fit_streaming :
    chiSquareStat (![66, 119, 340, 60, 15] : Fin 5 → ℝ) ![60, 96, 330, 66, 48] = 156533 / 5280 ∧
      29.64 < chiSquareStat (![66, 119, 340, 60, 15] : Fin 5 → ℝ) ![60, 96, 330, 66, 48] ∧
      chiSquareStat (![66, 119, 340, 60, 15] : Fin 5 → ℝ) ![60, 96, 330, 66, 48] < 29.65 ∧
      Fintype.card (Fin 5) - 1 = 4 := by
  have h : chiSquareStat (![66, 119, 340, 60, 15] : Fin 5 → ℝ) ![60, 96, 330, 66, 48] =
      156533 / 5280 := by
    simp [chiSquareStat, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨rfl, by norm_num, by norm_num, rfl⟩

/-- OpenStax Introductory Statistics 2e Example 11.3 (expected counts). The expected counts are the
national proportions times the sample size: `(0.10, 0.16, 0.55, 0.11, 0.08) · 600 = (60, 96, 330, 66, 48)`,
and they add up to the sample size 600. -/
@[kb "openstaxintrostats2e" "Example 11.3, p. 581"]
theorem example_11_3_expected_counts :
    (fun i : Fin 5 => 600 * (![0.10, 0.16, 0.55, 0.11, 0.08] : Fin 5 → ℝ) i) = ![60, 96, 330, 66, 48] ∧
      ∑ i : Fin 5, 600 * (![0.10, 0.16, 0.55, 0.11, 0.08] : Fin 5 → ℝ) i = 600 := by
  constructor
  · funext i
    fin_cases i <;> simp <;> norm_num
  · simp [Fin.sum_univ_succ]
    norm_num

/-- OpenStax Introductory Statistics 2e Example 11.4. A hundred flips of two coins give `20, 57, 23`
tosses with two, one, zero heads, against `25, 50, 25` expected for fair coins. The chi-square
statistic is exactly `107/50 = 2.14`, with `3 - 1 = 2` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.4, p. 585"]
theorem example_11_4_fair_coins :
    chiSquareStat (![20, 57, 23] : Fin 3 → ℝ) ![25, 50, 25] = 107 / 50 ∧
      chiSquareStat (![20, 57, 23] : Fin 3 → ℝ) ![25, 50, 25] = 2.14 ∧ Fintype.card (Fin 3) - 1 = 2 := by
  have h : chiSquareStat (![20, 57, 23] : Fin 3 → ℝ) ![25, 50, 25] = 107 / 50 := by
    simp [chiSquareStat, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨rfl, by norm_num, rfl⟩

/-- OpenStax Introductory Statistics 2e Example 11.5. Of 755 drivers, 70 had a speeding violation
and 305 used a cell phone; under independence the expected number with both is
`70 · 305 / 755 = 4270/151`, about `28.28` (the book's "about 28"). -/
@[kb "openstaxintrostats2e" "Example 11.5, p. 587"]
theorem example_11_5_expected_count_independence :
    (70 : ℝ) * 305 / 755 = 4270 / 151 ∧ 28.27 < (70 : ℝ) * 305 / 755 ∧ (70 : ℝ) * 305 / 755 < 28.28 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Observed hours-versus-volunteer-type table of Example 11.6 (rows: community college, four-year
college, nonstudents; columns: 1-3, 4-6, 7-9 hours). -/
noncomputable def volunteerTable : Fin 3 → Fin 3 → ℝ :=
  ![![111, 96, 48], ![96, 133, 61], ![91, 150, 53]]

/-- OpenStax Introductory Statistics 2e Example 11.6 (expected counts). The grand total of the
volunteer table is 839 and the top-left expected count is `255 · 298 / 839 = 75990/839`, strictly
between `90.57` and `90.58`. -/
@[kb "openstaxintrostats2e" "Example 11.6, p. 587"]
theorem example_11_6_expected_count :
    (∑ i, ∑ j, volunteerTable i j) = 839 ∧ tableExpected volunteerTable 0 0 = 75990 / 839 ∧
      90.57 < tableExpected volunteerTable 0 0 ∧ tableExpected volunteerTable 0 0 < 90.58 := by
  have h : tableExpected volunteerTable 0 0 = 75990 / 839 := by
    simp [tableExpected, volunteerTable, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨?_, rfl, by norm_num, by norm_num⟩
  simp [volunteerTable, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Example 11.6 (test statistic). For the volunteer table the
chi-square statistic of independence lies strictly between `12.99` and `13.00` (the book's `12.99`,
calculator output `12.9909`), with `(3 - 1)(3 - 1) = 4` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.6, p. 587"]
theorem example_11_6_independence_statistic :
    12.99 < tableChiSquare volunteerTable ∧ tableChiSquare volunteerTable < 13.00 ∧
      (Fintype.card (Fin 3) - 1) * (Fintype.card (Fin 3) - 1) = 4 := by
  have h : tableChiSquare volunteerTable = 17225609642245 / 1325973188484 := by
    simp [tableChiSquare, tableExpected, volunteerTable, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨by norm_num, by norm_num, rfl⟩

/-- Observed anxiety-versus-need table of Example 11.7 (rows: high, medium, low need; columns: high
to low anxiety). -/
noncomputable def anxietyTable : Fin 3 → Fin 5 → ℝ :=
  ![![35, 42, 53, 15, 10], ![18, 48, 63, 33, 31], ![4, 5, 11, 15, 17]]

/-- OpenStax Introductory Statistics 2e Example 11.7. For 400 students, the expected number with high
anxiety and high need is `155 · 57 / 400 = 22.0875` (about 22), and the expected number with
med-low anxiety and low need is `52 · 63 / 400 = 8.19` (about 8). -/
@[kb "openstaxintrostats2e" "Example 11.7, p. 590"]
theorem example_11_7_expected_counts :
    tableExpected anxietyTable 0 0 = 22.0875 ∧ tableExpected anxietyTable 2 3 = 8.19 := by
  constructor <;>
  · simp [tableExpected, anxietyTable, Fin.sum_univ_succ]
    norm_num

/-- Observed living-arrangement table of Example 11.8 (rows: men, women; columns: dormitory,
apartment, with parents, other). -/
noncomputable def livingTable : Fin 2 → Fin 4 → ℝ := ![![72, 84, 49, 45], ![91, 86, 88, 35]]

/-- OpenStax Introductory Statistics 2e Example 11.8. For the 250 men and 300 women, the
homogeneity chi-square statistic is strictly between `10.12` and `10.13` (the book's `10.1287`), with
`4 - 1 = 3` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.8, p. 591"]
theorem example_11_8_homogeneity_living :
    10.12 < tableChiSquare livingTable ∧ tableChiSquare livingTable < 10.13 ∧
      Fintype.card (Fin 4) - 1 = 3 := by
  have h : tableChiSquare livingTable = 9228304283 / 911104800 := by
    simp [tableChiSquare, tableExpected, livingTable, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨by norm_num, by norm_num, rfl⟩

/-- Observed voter-preference table of Example 11.9 (rows: before, after the earthquake; columns:
Perez, Chung, Stevens). -/
noncomputable def voterTable : Fin 2 → Fin 3 → ℝ := ![![167, 128, 135], ![214, 197, 225]]

/-- OpenStax Introductory Statistics 2e Example 11.9. For the before and after surveys the
homogeneity chi-square statistic is strictly between `3.26` and `3.27` (the book's `3.2603`), with
`3 - 1 = 2` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.9, p. 592"]
theorem example_11_9_homogeneity_voters :
    3.26 < tableChiSquare voterTable ∧ tableChiSquare voterTable < 3.27 ∧
      Fintype.card (Fin 3) - 1 = 2 := by
  have h : tableChiSquare voterTable = 16985237321 / 5209794000 := by
    simp [tableChiSquare, tableExpected, voterTable, Fin.sum_univ_succ]
    norm_num
  rw [h]
  refine ⟨by norm_num, by norm_num, rfl⟩

/-- OpenStax Introductory Statistics 2e Example 11.11. Single-variance test: 25 waiting times with
sample standard deviation `3.5` against a claimed `σ = 7.2` give the statistic
`(n - 1) s² / σ² = 24 · 3.5² / 7.2² = 1225/216`, strictly between `5.67` and `5.68`, with
`25 - 1 = 24` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 11.11, p. 595"]
theorem example_11_11_single_variance_statistic :
    ((25 : ℝ) - 1) * 3.5 ^ 2 / 7.2 ^ 2 = 1225 / 216 ∧ 5.67 < ((25 : ℝ) - 1) * 3.5 ^ 2 / 7.2 ^ 2 ∧
      ((25 : ℝ) - 1) * 3.5 ^ 2 / 7.2 ^ 2 < 5.68 ∧ 25 - 1 = 24 := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl⟩

/-! ### One-way analysis of variance -/

/-- OpenStax Introductory Statistics 2e Example 13.1. Three diet plans with weight losses
`5, 4.5, 4, 3`, `3.5, 7, 4.5` and `8, 4, 3.5`: the between-group sum of squares is exactly `539/240`
(`2.2458`), the within-group sum of squares `1001/48` (`20.8542`), the total `23.1`, and the `F` ratio
`MS(between)/MS(within)` is exactly `49/130` (the book's `0.3769`). -/
@[kb "openstaxintrostats2e" "Example 13.1, p. 694"]
theorem example_13_1_diet_anova :
    let x : Fin 10 → ℝ := ![5, 4.5, 4, 3, 3.5, 7, 4.5, 8, 4, 3.5]
    let g : Fin 10 → Fin 3 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 2]
    ssBetween x g = 539 / 240 ∧ ssWithin x g = 1001 / 48 ∧ sumSqDev x = 23.1 ∧
      msBetween x g = 539 / 480 ∧ msWithin x g = 1001 / 336 ∧ fStatistic x g = 49 / 130 := by
  intro x g
  have hs : ∀ j, groupSize g j = (![4, 3, 3] : Fin 3 → ℕ) j := by
    intro j; fin_cases j <;> decide
  have hb : ssBetween x g = 539 / 240 := by
    simp only [ssBetween, groupMean, hs]
    simp [mean, x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hw : ssWithin x g = 1001 / 48 := by
    simp only [ssWithin, groupMean, hs]
    simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have ht : sumSqDev x = 23.1 := by
    rw [sumSqDev_eq_ssBetween_add_ssWithin x g, hb, hw]; norm_num
  have hmb : msBetween x g = 539 / 480 := by
    rw [msBetween, hb]; norm_num
  have hmw : msWithin x g = 1001 / 336 := by
    rw [msWithin, hw]; norm_num
  refine ⟨hb, hw, ht, hmb, hmw, ?_⟩
  rw [fStatistic, hmb, hmw]; norm_num

/-- OpenStax Introductory Statistics 2e Example 13.2. Slicing-tomato yields (grams) for five
mulching conditions with three plants each. The between-group sum of squares is exactly
`549728414/15` (about `36648561`), the within-group sum of squares exactly `20446726`, and the `F`
ratio is `274864207/61340178`, strictly between `4.480` and `4.482` (the book's `4.4810`), with
`5 - 1 = 4` and `15 - 5 = 10` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 13.2, p. 697"]
theorem example_13_2_tomato_anova :
    let x : Fin 15 → ℝ := ![2625, 2997, 4915, 5348, 5682, 5482, 6583, 8560, 3830, 7285, 6897, 9230,
      6277, 7818, 8677]
    let g : Fin 15 → Fin 5 := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4]
    ssBetween x g = 549728414 / 15 ∧ ssWithin x g = 20446726 ∧
      fStatistic x g = 274864207 / 61340178 ∧ 4.480 < fStatistic x g ∧ fStatistic x g < 4.482 := by
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
  have hf : fStatistic x g = 274864207 / 61340178 := by
    rw [fStatistic, msBetween, msWithin, hb, hw]; norm_num
  rw [hf]
  refine ⟨hb, hw, rfl, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Example 13.3. Mean grades of four sororities with five
sisters each: the between-group sum of squares is exactly `72183/25000 = 2.88732`, the within-group
sum of squares `17261/2500 = 6.9044`, and the `F` ratio is `192488/86305`, strictly between `2.230`
and `2.231` (the book's `2.2303`), with `4 - 1 = 3` and `20 - 4 = 16` degrees of freedom. -/
@[kb "openstaxintrostats2e" "Example 13.3, p. 698"]
theorem example_13_3_sorority_anova :
    let x : Fin 20 → ℝ := ![2.17, 1.85, 2.83, 1.69, 3.33, 2.63, 1.77, 3.25, 1.86, 2.21, 2.63, 3.78,
      4.00, 2.55, 2.45, 3.79, 3.45, 3.08, 2.26, 3.18]
    let g : Fin 20 → Fin 4 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3]
    ssBetween x g = 2.88732 ∧ ssWithin x g = 6.9044 ∧ fStatistic x g = 192488 / 86305 ∧
      2.230 < fStatistic x g ∧ fStatistic x g < 2.231 := by
  intro x g
  have hs : ∀ j, groupSize g j = (![5, 5, 5, 5] : Fin 4 → ℕ) j := by
    intro j; fin_cases j <;> decide
  have hb : ssBetween x g = 2.88732 := by
    simp only [ssBetween, groupMean, hs]
    simp [mean, x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hw : ssWithin x g = 6.9044 := by
    simp only [ssWithin, groupMean, hs]
    simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hf : fStatistic x g = 192488 / 86305 := by
    rw [fStatistic, msBetween, msWithin, hb, hw]; norm_num
  rw [hf]
  refine ⟨hb, hw, rfl, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Example 13.4. Heights of bean plants in three soils (five
plants each): the group means are `24.2, 25.4, 24.4`, the between-group sum of squares is exactly
`62/15`, the within-group sum of squares `926/5`, and the `F` ratio is exactly `62/463`, strictly
between `0.133` and `0.134` (the book's `0.134`), with `3 - 1 = 2` and `15 - 3 = 12` degrees of
freedom. -/
@[kb "openstaxintrostats2e" "Example 13.4, p. 700"]
theorem example_13_4_bean_anova :
    let x : Fin 15 → ℝ := ![24, 21, 23, 30, 23, 25, 31, 23, 20, 28, 23, 27, 22, 30, 20]
    let g : Fin 15 → Fin 3 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]
    groupMean x g 0 = 24.2 ∧ groupMean x g 1 = 25.4 ∧ groupMean x g 2 = 24.4 ∧
      ssBetween x g = 62 / 15 ∧ ssWithin x g = 926 / 5 ∧ fStatistic x g = 62 / 463 ∧
      0.133 < fStatistic x g ∧ fStatistic x g < 0.134 := by
  intro x g
  have hs : ∀ j, groupSize g j = (![5, 5, 5] : Fin 3 → ℕ) j := by
    intro j; fin_cases j <;> decide
  have hm : groupMean x g 0 = 24.2 ∧ groupMean x g 1 = 25.4 ∧ groupMean x g 2 = 24.4 := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [groupMean, hs]
      simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
      norm_num
  have hb : ssBetween x g = 62 / 15 := by
    simp only [ssBetween, groupMean, hs]
    simp [mean, x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hw : ssWithin x g = 926 / 5 := by
    simp only [ssWithin, groupMean, hs]
    simp [x, g, Finset.sum_filter, Fin.sum_univ_succ]
    norm_num
  have hf : fStatistic x g = 62 / 463 := by
    rw [fStatistic, msBetween, msWithin, hb, hw]; norm_num
  rw [hf]
  refine ⟨hm.1, hm.2.1, hm.2.2, hb, hw, rfl, by norm_num, by norm_num⟩

/-! ### Standard errors and test statistics (chapters 7, 9, 10) -/

/-- OpenStax Introductory Statistics 2e Example 7.1. Samples of size 25 from a population with mean 90
and standard deviation 15 have standard error `15/√25 = 3`; the endpoints 85 and 92 have `z`-scores
`-5/3` and `2/3` for the sample mean. -/
@[kb "openstaxintrostats2e" "Example 7.1, p. 379"]
theorem example_7_1_standard_error_and_z :
    15 / Real.sqrt 25 = 3 ∧ (85 - 90) / (15 / Real.sqrt 25) = -5 / 3 ∧
      (92 - 90) / (15 / Real.sqrt 25) = 2 / 3 := by
  have h : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [h]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Example 7.7. For 70 app-engagement times with mean `8.2`
minutes and standard deviation `1`, the sum has mean `70 · 8.2 = 574` minutes and standard deviation
`√70 · 1`, strictly between `8.36` and `8.37` (the book's `8.37`). -/
@[kb "openstaxintrostats2e" "Example 7.7, p. 385"]
theorem example_7_7_mean_and_sd_of_sums :
    (70 : ℝ) * 8.2 = 574 ∧ 8.36 < Real.sqrt 70 * 1 ∧ Real.sqrt 70 * 1 < 8.37 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [mul_one]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  · rw [mul_one]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 9.9. For 10 loaves with sample mean `17` cm against
`μ₀ = 15` and known `σ = 0.5`, the standard error is `0.5/√10` and the test statistic
`z = (17 - 15)/(0.5/√10) = 4√10` lies strictly between `12.6` and `12.7`, so the sample mean is about
12.6 standard errors above `15` (an essentially zero p-value). -/
@[kb "openstaxintrostats2e" "Example 9.9, p. 479"]
theorem example_9_9_z_statistic :
    (17 - 15) / (0.5 / Real.sqrt 10) = 4 * Real.sqrt 10 ∧
      12.6 < (17 - 15) / (0.5 / Real.sqrt 10) ∧ (17 - 15) / (0.5 / Real.sqrt 10) < 12.7 := by
  have hs : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have h : (17 - 15) / (0.5 / Real.sqrt 10) = 4 * Real.sqrt 10 := by
    field_simp; norm_num
  rw [h]
  have h1 : 3.15 < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : Real.sqrt 10 < 3.175 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  refine ⟨rfl, by linarith, by linarith⟩

/-- OpenStax Introductory Statistics 2e Example 9.16. Ten test scores `65, 65, 70, 67, 66, 63, 63,
68, 72, 71` have sample mean exactly `67` and sample standard deviation `√(92/9)`, strictly between
`3.197` and `3.198` (the book's `3.1972`); the `t` statistic against `μ₀ = 65`,
`(x̄ - 65)/(s/√10)`, lies strictly between `1.97` and `1.98` (the book's `1.9781`). -/
@[kb "openstaxintrostats2e" "Example 9.16, p. 487"]
theorem example_9_16_t_statistic :
    let x : Fin 10 → ℝ := ![65, 65, 70, 67, 66, 63, 63, 68, 72, 71]
    mean x = 67 ∧ sampleVariance x = 92 / 9 ∧ 3.197 < sampleStdDev x ∧ sampleStdDev x < 3.198 ∧
      1.97 < (mean x - 65) / (sampleStdDev x / Real.sqrt 10) ∧
      (mean x - 65) / (sampleStdDev x / Real.sqrt 10) < 1.98 := by
  intro x
  have hm : mean x = 67 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 92 / 9 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  have hs1 : 3.197 < sampleStdDev x := by
    rw [sampleStdDev, hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : sampleStdDev x < 3.198 := by
    rw [sampleStdDev, hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h1 : 3.162 < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : Real.sqrt 10 < 3.163 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  refine ⟨hm, hv, hs1, hs2, ?_, ?_⟩
  · rw [hm, lt_div_iff₀ (by positivity), ← mul_div_assoc,
      div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    linarith
  · rw [hm, div_lt_iff₀ (by positivity), ← mul_div_assoc,
      lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    linarith

/-- OpenStax Introductory Statistics 2e Example 10.4. Cohen's `d` for two samples with means `4` and
`3.5`, standard deviations `1.5` and `1`, and sizes `11` and `9`: with the pooled standard deviation
`√((10 · 1.5² + 8 · 1²)/18)` it lies strictly between `0.384` and `0.385` (the book's `0.384`),
a small effect. -/
@[kb "openstaxintrostats2e" "Example 10.4, p. 531"]
theorem example_10_4_cohens_d :
    0.384 < (4 - 3.5) / Real.sqrt (((11 - 1) * 1.5 ^ 2 + (9 - 1) * 1 ^ 2) / (11 + 9 - 2)) ∧
      (4 - 3.5) / Real.sqrt (((11 - 1) * 1.5 ^ 2 + (9 - 1) * 1 ^ 2) / (11 + 9 - 2)) < 0.385 := by
  have hp : 0 < Real.sqrt (((11 - 1) * 1.5 ^ 2 + (9 - 1) * 1 ^ 2) / (11 + 9 - 2) : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have h1 : 1.30 < Real.sqrt (((11 - 1) * 1.5 ^ 2 + (9 - 1) * 1 ^ 2) / (11 + 9 - 2) : ℝ) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : Real.sqrt (((11 - 1) * 1.5 ^ 2 + (9 - 1) * 1 ^ 2) / (11 + 9 - 2) : ℝ) < 1.302 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

end UndergradKB.Statistics.Course.ExamplesC11C13
