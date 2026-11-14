import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Percentile
import UndergradKB.Statistics.Descriptive

/-!
# Practice exercises, chapter 2 (OpenStax *Introductory Statistics 2e*): descriptive statistics

Theorems with exact answers for the data of the chapter's Practice exercises. Data are concrete vectors
`![...] : Fin n → ℝ`; means, variances and z-scores use the repository's definitions
(`UndergradKB.Statistics.mean`, `sampleVariance`, `zScore`, ...), medians use `median`. Exercises that ask
only for a graph are stated through the numbers the graph is built from (class counts, class midpoints,
cumulative frequencies, five-number summaries, fences). Exercises about a figure that is given only as a
picture, and purely verbal ones, are not formalised.
-/

namespace UndergradKB.Statistics.Course.PracticeC2

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open UndergradKB.Statistics Finset

private lemma sortedData_eq_of_perm {n : ℕ} (x y : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hy : Monotone y) (h : ∀ i, y i = x (σ i)) : sortedData x = y := by
  have hm : Monotone (x ∘ σ) := by
    have : x ∘ σ = y := funext fun i => (h i).symm
    rw [this]; exact hy
  have := (Tuple.comp_sort_eq_comp_iff_monotone (f := x) (σ := σ)).2 hm
  have h2 : y = x ∘ σ := funext h
  rw [h2]; exact this.symm

private lemma sortedData_eq_self {n : ℕ} (y : Fin n → ℝ) (hy : Monotone y) : sortedData y = y :=
  sortedData_eq_of_perm y y (Equiv.refl _) hy fun _ => rfl

/-- The median of a nondecreasing list of odd length `2m + 1` is its middle entry. -/
private lemma median_odd {m : ℕ} (y : Fin (2 * m + 1) → ℝ) (hy : Monotone y) :
    median y = y ⟨m, by omega⟩ := by
  have hp : 0 < 2 * m + 1 := by omega
  simp only [median, hp, ↓reduceDIte, sortedData_eq_self y hy]
  have h1 : (2 * m + 1 - 1) / 2 = m := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp only [h1, h2]
  ring

/-- The median of a nondecreasing list of even length `2m + 2` is the mean of the two middle entries. -/
private lemma median_even {m : ℕ} (y : Fin (2 * m + 2) → ℝ) (hy : Monotone y) :
    median y = (y ⟨m, by omega⟩ + y ⟨m + 1, by omega⟩) / 2 := by
  have hp : 0 < 2 * m + 2 := by omega
  simp only [median, hp, ↓reduceDIte, sortedData_eq_self y hy]
  have h1 : (2 * m + 2 - 1) / 2 = m := by omega
  have h2 : (2 * m + 2) / 2 = m + 1 := by omega
  simp only [h1, h2]

private lemma mono_of_succ {n : ℕ} {y : Fin (n + 1) → ℝ}
    (h : ∀ i : Fin n, y i.castSucc ≤ y i.succ) : Monotone y :=
  Fin.monotone_iff_le_succ.2 h

/-- Monotonicity of a concrete vector of numerals. -/
local macro "mono_tac" : tactic =>
  `(tactic| (refine mono_of_succ fun i => ?_; fin_cases i <;> simp +zetaDelta <;> norm_num))

/-- The first `h` entries of a list (the lower half of ordered data). -/
private def lowerHalf {n : ℕ} (x : Fin n → ℝ) (h : ℕ) (hh : h ≤ n) : Fin h → ℝ :=
  fun i => x ⟨i, by omega⟩

/-- The last `h` entries of a list (the upper half of ordered data). -/
private def upperHalf {n : ℕ} (x : Fin n → ℝ) (h : ℕ) (hh : h ≤ n) : Fin h → ℝ :=
  fun i => x ⟨n - h + i, by omega⟩

private lemma lowerHalf_mono {n : ℕ} {x : Fin n → ℝ} (hx : Monotone x) (h : ℕ) (hh : h ≤ n) :
    Monotone (lowerHalf x h hh) := fun a b hab =>
  hx (Fin.mk_le_mk.2 (Fin.le_def.1 hab))

private lemma upperHalf_mono {n : ℕ} {x : Fin n → ℝ} (hx : Monotone x) (h : ℕ) (hh : h ≤ n) :
    Monotone (upperHalf x h hh) := fun a b hab =>
  hx (Fin.mk_le_mk.2 (by have := Fin.le_def.1 hab; show n - h + a.val ≤ n - h + b.val; omega))

private lemma sd_bounds {n : ℕ} (x : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h1 : a ^ 2 < sampleVariance x) (h2 : sampleVariance x < b ^ 2) :
    a < sampleStdDev x ∧ sampleStdDev x < b :=
  ⟨(Real.lt_sqrt ha).2 h1, (Real.sqrt_lt' hb).2 h2⟩

/-- The `j`-th (1-indexed) entry of a list, `0` out of range. -/
private noncomputable def entry {n : ℕ} (y : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j - 1 < n then y ⟨j - 1, h⟩ else 0

/-- The `k`-th percentile by the locating-index rule: with `i = k/100 · (n + 1)`, average the
entries in positions `⌊i⌋` and `⌈i⌉` of the ordered data (a single entry when `i` is an integer). -/
private noncomputable def percentileAt {n : ℕ} (y : Fin n → ℝ) (k : ℝ) : ℝ :=
  (entry y ⌊k / 100 * ((n : ℝ) + 1)⌋₊ + entry y ⌈k / 100 * ((n : ℝ) + 1)⌉₊) / 2

/-- Number of entries of the list in the half-open class `[lo, hi)`. -/
private noncomputable def stemCount {n : ℕ} (x : Fin n → ℝ) (lo hi : ℝ) : ℕ :=
  (univ.filter fun i => lo ≤ x i ∧ x i < hi).card

/-- Number of entries of the list lying outside the fences `q1 - 1.5 (q3 - q1)` and `q3 + 1.5 (q3 - q1)`. -/
private noncomputable def outlierCount {n : ℕ} (x : Fin n → ℝ) (q1 q3 : ℝ) : ℕ :=
  (univ.filter fun i => x i < q1 - 1.5 * (q3 - q1) ∨ q3 + 1.5 * (q3 - q1) < x i).card

/-- Evaluate a class count of a concrete list. -/
local macro "count_tac" : tactic =>
  `(tactic| (rw [Finset.card_filter]; simp +zetaDelta [Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num))

/-- OpenStax Introductory Statistics 2e Practice exercise 2.1 (stem plot). The 30 miles-per-gallon
ratings have 3, 10, 14 and 3 values with tens digit 1, 2, 3 and 4 (the leaves of the stem plot). -/
@[kb "openstaxintrostats2e" "Exercise 2.1, p. 134"]
theorem ex_2_1_stem_counts :
    let x : Fin 30 → ℝ := ![19, 19, 19, 20, 21, 21, 25, 25, 25, 26, 26, 28, 29, 31, 31, 32, 32, 33, 34,
      35, 36, 37, 37, 38, 38, 38, 38, 41, 43, 43]
    stemCount x 10 20 = 3 ∧ stemCount x 20 30 = 10 ∧ stemCount x 30 40 = 14 ∧
      stemCount x 40 50 = 3 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.1 (outliers). For the same 30 ratings the median
is 31.5, the quartiles (medians of the lower and upper 15 values) are 25 and 37, so the IQR is 12 and the
fences are 7 and 55; no rating lies outside them, so there are no outliers. -/
@[kb "openstaxintrostats2e" "Exercise 2.1, p. 134"]
theorem ex_2_1_no_outliers :
    let x : Fin 30 → ℝ := ![19, 19, 19, 20, 21, 21, 25, 25, 25, 26, 26, 28, 29, 31, 31, 32, 32, 33, 34,
      35, 36, 37, 37, 38, 38, 38, 38, 41, 43, 43]
    median x = 31.5 ∧ median (lowerHalf x 15 (by norm_num)) = 25 ∧
      median (upperHalf x 15 (by norm_num)) = 37 ∧ (37 : ℝ) - 25 = 12 ∧
      (25 : ℝ) - 1.5 * 12 = 7 ∧ (37 : ℝ) + 1.5 * 12 = 55 ∧ outlierCount x 25 37 = 0 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_⟩
  · rw [median_even (m := 14) x hx]; simp [x] <;> norm_num
  · rw [median_odd (m := 7) _ (lowerHalf_mono hx 15 (by norm_num))]; simp [lowerHalf, x]
  · rw [median_odd (m := 7) _ (upperHalf_mono hx 15 (by norm_num))]; simp [upperHalf, x]
  · unfold outlierCount; count_tac

/-- OpenStax Introductory Statistics 2e Practice exercise 2.2 (stem plot). The 25 tree heights (feet) have
2, 11, 6 and 6 values with tens digit 2, 3, 4 and 5. -/
@[kb "openstaxintrostats2e" "Exercise 2.2, p. 134"]
theorem ex_2_2_stem_counts :
    let x : Fin 25 → ℝ := ![25, 27, 33, 34, 34, 34, 35, 37, 37, 38, 39, 39, 39, 40, 41, 45, 46, 47, 49,
      50, 50, 53, 53, 54, 54]
    stemCount x 20 30 = 2 ∧ stemCount x 30 40 = 11 ∧ stemCount x 40 50 = 6 ∧
      stemCount x 50 60 = 6 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.2 (outliers). For the 25 heights the median is
39, the quartiles (medians of the lower and upper 12 values) are 34.5 and 49.5, the IQR is 15, the fences
are 12 and 72, and no height lies outside them: no outliers. -/
@[kb "openstaxintrostats2e" "Exercise 2.2, p. 134"]
theorem ex_2_2_no_outliers :
    let x : Fin 25 → ℝ := ![25, 27, 33, 34, 34, 34, 35, 37, 37, 38, 39, 39, 39, 40, 41, 45, 46, 47, 49,
      50, 50, 53, 53, 54, 54]
    median x = 39 ∧ median (lowerHalf x 12 (by norm_num)) = 34.5 ∧
      median (upperHalf x 12 (by norm_num)) = 49.5 ∧ (49.5 : ℝ) - 34.5 = 15 ∧
      (34.5 : ℝ) - 1.5 * 15 = 12 ∧ (49.5 : ℝ) + 1.5 * 15 = 72 ∧ outlierCount x 34.5 49.5 = 0 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_⟩
  · rw [median_odd (m := 12) x hx]; simp [x]
  · rw [median_even (m := 5) _ (lowerHalf_mono hx 12 (by norm_num))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 5) _ (upperHalf_mono hx 12 (by norm_num))]; simp [upperHalf, x] <;> norm_num
  · unfold outlierCount; count_tac

/-- OpenStax Introductory Statistics 2e Practice exercise 2.3 (stem plot). The 25 laptop prices rounded to the
nearest ten are 250, 250, 260, 270, 270, 280, 300, 300, 310, 320, 330, 330, 350, 350, 350, 370, 370, 390,
410, 460, 490, 560, 570, 570, 610; the stems 2, 3, 4, 5, 6 (hundreds) carry 6, 12, 3, 3 and 1 leaves. -/
@[kb "openstaxintrostats2e" "Exercise 2.3, p. 134"]
theorem ex_2_3_stem_counts :
    let x : Fin 25 → ℝ := ![250, 250, 260, 270, 270, 280, 300, 300, 310, 320, 330, 330, 350, 350, 350,
      370, 370, 390, 410, 460, 490, 560, 570, 570, 610]
    stemCount x 200 300 = 6 ∧ stemCount x 300 400 = 12 ∧ stemCount x 400 500 = 3 ∧
      stemCount x 500 600 = 3 ∧ stemCount x 600 700 = 1 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.3 (outliers). For the 25 original laptop prices
the median is 350, the quartiles (medians of the lower and upper 12 values) are 289.5 and 434, the IQR is
144.5, the fences are 72.75 and 650.75, and no price lies outside them: no outliers. -/
@[kb "openstaxintrostats2e" "Exercise 2.3, p. 134"]
theorem ex_2_3_no_outliers :
    let x : Fin 25 → ℝ := ![249, 249, 260, 265, 265, 280, 299, 299, 309, 319, 325, 326, 350, 350, 350,
      365, 369, 389, 409, 459, 489, 559, 569, 570, 610]
    median x = 350 ∧ median (lowerHalf x 12 (by norm_num)) = 289.5 ∧
      median (upperHalf x 12 (by norm_num)) = 434 ∧ (434 : ℝ) - 289.5 = 144.5 ∧
      (289.5 : ℝ) - 1.5 * 144.5 = 72.75 ∧ (434 : ℝ) + 1.5 * 144.5 = 650.75 ∧
      outlierCount x 289.5 434 = 0 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_⟩
  · rw [median_odd (m := 12) x hx]; simp [x]
  · rw [median_even (m := 5) _ (lowerHalf_mono hx 12 (by norm_num))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 5) _ (upperHalf_mono hx 12 (by norm_num))]; simp [upperHalf, x] <;> norm_num
  · unfold outlierCount; count_tac

/-- OpenStax Introductory Statistics 2e Practice exercise 2.4 (stem plot). The 30 daily high temperatures
have 10, 19 and 1 values with tens digit 6, 7 and 9 (and none with tens digit 8). -/
@[kb "openstaxintrostats2e" "Exercise 2.4, p. 134"]
theorem ex_2_4_stem_counts :
    let x : Fin 30 → ℝ := ![61, 61, 62, 64, 66, 67, 67, 67, 68, 69, 70, 70, 70, 71, 71, 72, 74, 74, 74,
      75, 75, 75, 76, 76, 77, 78, 78, 79, 79, 95]
    stemCount x 60 70 = 10 ∧ stemCount x 70 80 = 19 ∧ stemCount x 80 90 = 0 ∧
      stemCount x 90 100 = 1 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.4 (outlier). For the 30 temperatures the median
is 71.5, the quartiles are 67 and 76, the IQR is 9, the fences are 53.5 and 89.5, and exactly one
temperature (95) lies outside them: 95 is the outlier. -/
@[kb "openstaxintrostats2e" "Exercise 2.4, p. 134"]
theorem ex_2_4_outlier :
    let x : Fin 30 → ℝ := ![61, 61, 62, 64, 66, 67, 67, 67, 68, 69, 70, 70, 70, 71, 71, 72, 74, 74, 74,
      75, 75, 75, 76, 76, 77, 78, 78, 79, 79, 95]
    median x = 71.5 ∧ median (lowerHalf x 15 (by norm_num)) = 67 ∧
      median (upperHalf x 15 (by norm_num)) = 76 ∧ (76 : ℝ) - 67 = 9 ∧
      (67 : ℝ) - 1.5 * 9 = 53.5 ∧ (76 : ℝ) + 1.5 * 9 = 89.5 ∧ outlierCount x 67 76 = 1 ∧
      (89.5 : ℝ) < 95 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  · rw [median_even (m := 14) x hx]; simp [x] <;> norm_num
  · rw [median_odd (m := 7) _ (lowerHalf_mono hx 15 (by norm_num))]; simp [lowerHalf, x]
  · rw [median_odd (m := 7) _ (upperHalf_mono hx 15 (by norm_num))]; simp [upperHalf, x]
  · unfold outlierCount; count_tac

/-- OpenStax Introductory Statistics 2e Practice exercise 2.5. The frequencies 4, 10, 16, 6, 4 of the
numbers of store visits (1 to 5) add to the 40 people surveyed; the points of the line graph are these
frequencies against the number of visits. -/
@[kb "openstaxintrostats2e" "Exercise 2.5, p. 134"]
theorem ex_2_5_store_visits_total :
    (∑ i, (![4, 10, 16, 6, 4] : Fin 5 → ℕ) i) = 40 := by
  simp [Fin.sum_univ_succ]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.6. The frequencies 2, 8, 13, 22, 16, 9 of the
years since the last mattress purchase (0 to 5) add to 70 people. -/
@[kb "openstaxintrostats2e" "Exercise 2.6, p. 134"]
theorem ex_2_6_mattress_total :
    (∑ i, (![2, 8, 13, 22, 16, 9] : Fin 6 → ℕ) i) = 70 := by
  simp [Fin.sum_univ_succ]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.7. The frequencies 12, 18, 36, 7, 2 of the
numbers of daily TV shows (0 to 4) add to 75 children. -/
@[kb "openstaxintrostats2e" "Exercise 2.7, p. 135"]
theorem ex_2_7_tv_shows_total :
    (∑ i, (![12, 18, 36, 7, 2] : Fin 5 → ℕ) i) = 75 := by
  simp [Fin.sum_univ_succ]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.8. The birthday counts 8, 9, 11, 6 (spring,
summer, autumn, winter) of the class add to 34 students, which is the height of the bars of the bar graph. -/
@[kb "openstaxintrostats2e" "Exercise 2.8, p. 135"]
theorem ex_2_8_birthday_counts :
    (∑ i, (![8, 9, 11, 6] : Fin 4 → ℕ) i) = 34 := by
  simp [Fin.sum_univ_succ]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.9. The printed percentages 24, 26, 32, 18 of the
four seasons are the counts 8, 9, 11, 6 over 34 rounded to whole percents (each differs from the exact
percentage by less than 1/2), and the printed percentages add to 100. -/
@[kb "openstaxintrostats2e" "Exercise 2.9, p. 135"]
theorem ex_2_9_birthday_percentages :
    (∀ k : Fin 4, |(![8, 9, 11, 6] : Fin 4 → ℚ) k / 34 * 100 - (![24, 26, 32, 18] : Fin 4 → ℚ) k| < 1 / 2) ∧
      (24 + 26 + 32 + 18 = 100) := by
  refine ⟨?_, by norm_num⟩
  intro k
  fin_cases k <;> simp <;> norm_num [abs_lt]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.10. The percentages of the science-competition
population for the six high schools (28.9, 7.6, 12.1, 18.5, 24.2, 8.7) add to 100. -/
@[kb "openstaxintrostats2e" "Exercise 2.10, p. 135"]
theorem ex_2_10_competition_percentages :
    (28.9 + 7.6 + 12.1 + 18.5 + 24.2 + 8.7 : ℚ) = 100 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.11. The county-wide student percentages of the
six high schools (8.6, 23.2, 15.0, 14.3, 10.1, 28.8) add to 100, so they are the heights of the bars of a
complete bar graph. -/
@[kb "openstaxintrostats2e" "Exercise 2.11, p. 136"]
theorem ex_2_11_overall_percentages :
    (8.6 + 23.2 + 15.0 + 14.3 + 10.1 + 28.8 : ℚ) = 100 := by
  norm_num

/-- Frequencies of the car-salesperson table (3, 4, 5, 6, 7 cars per week). -/
private def salesFreq : Fin 5 → ℕ := ![14, 19, 12, 9, 11]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.12. In the table of the 65 car salespersons the
frequencies are 14, 19, 12, 9, 11 (total 65), the relative frequencies are 14/65, 19/65, 12/65, 9/65,
11/65 and the cumulative relative frequencies are 14/65, 33/65, 9/13, 54/65 and 1. -/
@[kb "openstaxintrostats2e" "Exercise 2.12, p. 136"]
theorem ex_2_12_sales_table :
    (∑ i, salesFreq i = 65) ∧
    ((fun k : Fin 5 => (salesFreq k : ℚ) / 65) = ![14 / 65, 19 / 65, 12 / 65, 9 / 65, 11 / 65]) ∧
    ((fun k : Fin 5 => ((∑ i : Fin 5, if i ≤ k then salesFreq i else 0 : ℕ) : ℚ) / 65) =
      ![14 / 65, 33 / 65, 9 / 13, 54 / 65, 1]) := by
  refine ⟨by simp [salesFreq, Fin.sum_univ_succ], ?_, ?_⟩
  · funext k
    fin_cases k <;> simp [salesFreq]
  · funext k
    fin_cases k <;> simp [salesFreq, Fin.sum_univ_succ, Fin.le_def] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.13. The frequency column of the car-salesperson
table adds to 65, the number of salespersons asked (every person is counted in exactly one row). -/
@[kb "openstaxintrostats2e" "Exercise 2.13, p. 136"]
theorem ex_2_13_frequency_sum :
    (∑ i, salesFreq i = 65) := by
  simp [salesFreq, Fin.sum_univ_succ]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.14. The relative frequency column of the
car-salesperson table adds to 1, since it is the frequency column divided by 65. -/
@[kb "openstaxintrostats2e" "Exercise 2.14, p. 136"]
theorem ex_2_14_relative_frequency_sum :
    (∑ i, (salesFreq i : ℚ) / 65) = 1 := by
  simp [salesFreq, Fin.sum_univ_succ]
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.15. For each value of the car-salesperson table
the frequency is 65 times the relative frequency, so the difference frequency minus relative frequency is
`64/65` of the frequency: 896/65, 1216/65, 768/65, 576/65, 704/65. -/
@[kb "openstaxintrostats2e" "Exercise 2.15, p. 136"]
theorem ex_2_15_frequency_minus_relative :
    (∀ k, (salesFreq k : ℚ) = 65 * ((salesFreq k : ℚ) / 65)) ∧
    ((fun k : Fin 5 => (salesFreq k : ℚ) - (salesFreq k : ℚ) / 65) =
      ![896 / 65, 1216 / 65, 768 / 65, 576 / 65, 704 / 65]) := by
  refine ⟨fun k => by ring, ?_⟩
  funext k
  fin_cases k <;> simp [salesFreq] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.16. In the car-salesperson table the cumulative
relative frequency minus the relative frequency of a row is the cumulative relative frequency of the row
before it: 0, 14/65, 33/65, 9/13, 54/65. -/
@[kb "openstaxintrostats2e" "Exercise 2.16, p. 136"]
theorem ex_2_16_cumulative_minus_relative :
    ((fun k : Fin 5 => ((∑ i : Fin 5, if i ≤ k then salesFreq i else 0 : ℕ) : ℚ) / 65 -
        (salesFreq k : ℚ) / 65) = ![0, 14 / 65, 33 / 65, 9 / 13, 54 / 65]) := by
  funext k
  fin_cases k <;> simp [salesFreq, Fin.sum_univ_succ, Fin.le_def] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.17. For the histogram of the car-salesperson
table the bars stand over the values 3 to 7 (class boundaries 2.5 to 7.5) and the tallest bar is the one
for 4 cars, of height 19; so the vertical axis must reach at least 19 and the horizontal axis must cover
2.5 to 7.5. -/
@[kb "openstaxintrostats2e" "Exercise 2.17, p. 136"]
theorem ex_2_17_histogram_scaling :
    (∀ k, salesFreq k ≤ 19) ∧ salesFreq 1 = 19 ∧ (7 : ℝ) + 0.5 - (3 - 0.5) = 5 := by
  refine ⟨?_, by simp [salesFreq], by norm_num⟩
  intro k
  fin_cases k <;> simp [salesFreq]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.18 (a). The pulse-rate classes 60-69, ..., 120-129
have midpoints 64.5, 74.5, ..., 124.5 (the x-coordinates of the frequency polygon, with class boundaries
59.5 to 129.5) and the frequencies 12, 14, 11, 1, 1, 0, 1 add to 40. -/
@[kb "openstaxintrostats2e" "Exercise 2.18, p. 137"]
theorem ex_2_18a_pulse_polygon :
    let lo : Fin 7 → ℝ := ![60, 70, 80, 90, 100, 110, 120]
    let hi : Fin 7 → ℝ := ![69, 79, 89, 99, 109, 119, 129]
    let m : Fin 7 → ℝ := ![64.5, 74.5, 84.5, 94.5, 104.5, 114.5, 124.5]
    (∀ i, (lo i + hi i) / 2 = m i) ∧ (∑ i, (![12, 14, 11, 1, 1, 0, 1] : Fin 7 → ℕ) i) = 40 := by
  intro lo hi m
  refine ⟨?_, by simp [Fin.sum_univ_succ]⟩
  intro i; fin_cases i <;> simp [lo, hi, m] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.18 (b). The speed classes 42-45, ..., 58-61 have
midpoints 43.5, 47.5, 51.5, 55.5, 59.5 and the frequencies 25, 14, 7, 3, 1 add to 50. -/
@[kb "openstaxintrostats2e" "Exercise 2.18, p. 137"]
theorem ex_2_18b_speed_polygon :
    let lo : Fin 5 → ℝ := ![42, 46, 50, 54, 58]
    let hi : Fin 5 → ℝ := ![45, 49, 53, 57, 61]
    let m : Fin 5 → ℝ := ![43.5, 47.5, 51.5, 55.5, 59.5]
    (∀ i, (lo i + hi i) / 2 = m i) ∧ (∑ i, (![25, 14, 7, 3, 1] : Fin 5 → ℕ) i) = 50 := by
  intro lo hi m
  refine ⟨?_, by simp [Fin.sum_univ_succ]⟩
  intro i; fin_cases i <;> simp [lo, hi, m] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.18 (c). The tar classes 10-13, ..., 26-29 have
midpoints 11.5, 15.5, 19.5, 23.5, 27.5 and the frequencies 1, 0, 15, 7, 2 add to 25. -/
@[kb "openstaxintrostats2e" "Exercise 2.18, p. 137"]
theorem ex_2_18c_tar_polygon :
    let lo : Fin 5 → ℝ := ![10, 14, 18, 22, 26]
    let hi : Fin 5 → ℝ := ![13, 17, 21, 25, 29]
    let m : Fin 5 → ℝ := ![11.5, 15.5, 19.5, 23.5, 27.5]
    (∀ i, (lo i + hi i) / 2 = m i) ∧ (∑ i, (![1, 0, 15, 7, 2] : Fin 5 → ℕ) i) = 25 := by
  intro lo hi m
  refine ⟨?_, by simp [Fin.sum_univ_succ]⟩
  intro i; fin_cases i <;> simp [lo, hi, m] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.19. The depth-of-hunger classes 230-259, ...,
410-439 have midpoints 244.5, 274.5, ..., 424.5. The frequencies 21, 13, 5, 7, 1, 1, 1 add to 49 (the text
speaks of 50 countries). -/
@[kb "openstaxintrostats2e" "Exercise 2.19, p. 138"]
theorem ex_2_19_hunger_polygon :
    let lo : Fin 7 → ℝ := ![230, 260, 290, 320, 350, 380, 410]
    let hi : Fin 7 → ℝ := ![259, 289, 319, 349, 379, 409, 439]
    let m : Fin 7 → ℝ := ![244.5, 274.5, 304.5, 334.5, 364.5, 394.5, 424.5]
    (∀ i, (lo i + hi i) / 2 = m i) ∧ (∑ i, (![21, 13, 5, 7, 1, 1, 1] : Fin 7 → ℕ) i) = 49 := by
  intro lo hi m
  refine ⟨?_, by simp [Fin.sum_univ_succ]⟩
  intro i; fin_cases i <;> simp [lo, hi, m] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.20. Life expectancy at birth in 20 countries,
grouped in classes with midpoints 52, 59, 66, 73, 80, 87: the female frequencies 3, 3, 1, 3, 8, 2 and the
male frequencies 3, 3, 1, 1, 7, 5 each add to 20; the grouped means are 358/5 = 71.6 years for females
and 1467/20 = 73.35 years for males. -/
@[kb "openstaxintrostats2e" "Exercise 2.20, p. 138"]
theorem ex_2_20_life_expectancy_grouped_means :
    let m : Fin 6 → ℝ := ![52, 59, 66, 73, 80, 87]
    let ff : Fin 6 → ℝ := ![3, 3, 1, 3, 8, 2]
    let fm : Fin 6 → ℝ := ![3, 3, 1, 1, 7, 5]
    (∑ i, ff i) = 20 ∧ (∑ i, fm i) = 20 ∧ (∑ i, ff i * m i) / (∑ i, ff i) = 358 / 5 ∧
      (∑ i, fm i * m i) / (∑ i, fm i) = 1467 / 20 := by
  intro m ff fm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [m, ff, fm, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.21. In each of the 21 years 1855 to 1875 the
female and male births listed add to the printed total, and in every year more boys than girls were born
(the numbers plotted in the three time series). -/
@[kb "openstaxintrostats2e" "Exercise 2.21, p. 139"]
theorem ex_2_21_births :
    let fb : Fin 21 → ℕ := ![45545, 49582, 50257, 50324, 51915, 51220, 52403, 51812, 53115, 54959,
      54850, 55307, 55527, 56292, 55033, 56431, 56099, 57472, 58233, 60109, 60146]
    let mb : Fin 21 → ℕ := ![47804, 52239, 53158, 53694, 54628, 54409, 54606, 55257, 56226, 57374,
      58220, 58360, 58517, 59222, 58321, 58959, 60029, 61293, 61467, 63602, 63432]
    let tb : Fin 21 → ℕ := ![93349, 101821, 103415, 104018, 106543, 105629, 107009, 107069, 109341,
      112333, 113070, 113667, 114044, 115514, 113354, 115390, 116128, 118765, 119700, 123711, 123578]
    (∀ i, fb i + mb i = tb i) ∧ (∀ i, fb i < mb i) := by
  intro fb mb tb
  exact ⟨by decide, by decide⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 2.22. Between 1961 and 1973 police per 100,000
citizens rose from 260.35 to 390.19, a ratio below 1.5, while homicides per 100,000 rose from 8.6 to 52.33,
a ratio above 6: homicides increased the fastest in relative terms. -/
@[kb "openstaxintrostats2e" "Exercise 2.22, p. 140"]
theorem ex_2_22_police_and_homicides :
    (390.19 : ℝ) / 260.35 < 1.5 ∧ (6 : ℝ) < 52.33 / 8.6 ∧ (390.19 : ℝ) / 260.35 < 52.33 / 8.6 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- A shared helper: the percentile locating rule with the floor and ceiling of the index supplied. -/
private lemma percentileAt_of {n : ℕ} (y : Fin n → ℝ) (k : ℝ) (a b : ℕ)
    (ha : ⌊k / 100 * ((n : ℝ) + 1)⌋₊ = a) (hb : ⌈k / 100 * ((n : ℝ) + 1)⌉₊ = b) :
    percentileAt y k = (entry y a + entry y b) / 2 := by
  simp only [percentileAt, ha, hb]

/-- Prove the floor and ceiling of a percentile index, then evaluate the entries. -/
local macro "pct_tac" a:term:max b:term:max : tactic =>
  `(tactic| rw [percentileAt_of _ _ $a $b (by rw [Nat.floor_eq_iff (by norm_num)]; norm_num) (by rw [Nat.ceil_eq_iff (by norm_num)]; norm_num)])

/-- The 29 ages of the best actors (Practice exercise 2.23). -/
private def ages29 : Fin 29 → ℝ := ![18, 21, 22, 25, 26, 27, 29, 30, 31, 33, 36, 37, 41, 42, 47, 52, 55,
  57, 58, 62, 64, 67, 69, 71, 72, 73, 74, 76, 77]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.23. For the 29 ages of Academy Award best actors,
the 40th percentile has index `0.40 · 30 = 12`, so it is the 12th value, 37; the 78th percentile has index
23.4, so it is the average of the 23rd and 24th values, 69 and 71: 70. -/
@[kb "openstaxintrostats2e" "Exercise 2.23, p. 140"]
theorem ex_2_23_percentiles_of_ages :
    percentileAt ages29 40 = 37 ∧ percentileAt ages29 78 = 70 := by
  constructor
  · pct_tac 12 12; simp [entry, ages29] <;> norm_num
  · pct_tac 23 24; simp [entry, ages29] <;> norm_num

/-- The 32 ages of the best actors (Practice exercise 2.24). -/
private def ages32 : Fin 32 → ℝ := ![18, 18, 21, 22, 25, 26, 27, 29, 30, 31, 31, 33, 36, 37, 37, 41, 42,
  47, 52, 55, 57, 58, 62, 64, 67, 69, 71, 72, 73, 74, 76, 77]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.24. In the 32 ages, 13 values are below 37 and two
equal it, so the percentile of 37 is `(13 + 2/2)/32 · 100 = 43.75`; 27 values are below 72 and one equals it,
so the percentile of 72 is `(27 + 1/2)/32 · 100 = 85.9375` (about 86). -/
@[kb "openstaxintrostats2e" "Exercise 2.24, p. 140"]
theorem ex_2_24_percentile_ranks :
    ((((univ.filter fun i => ages32 i < 37).card : ℝ) + ((univ.filter fun i => ages32 i = 37).card : ℝ) / 2)
        / 32 * 100 = 43.75) ∧
    ((((univ.filter fun i => ages32 i < 72).card : ℝ) + ((univ.filter fun i => ages32 i = 72).card : ℝ) / 2)
        / 32 * 100 = 85.9375) := by
  have a1 : (univ.filter fun i => ages32 i < 37).card = 13 := by
    rw [Finset.card_filter]; simp [ages32, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a2 : (univ.filter fun i => ages32 i = 37).card = 2 := by
    rw [Finset.card_filter]; simp [ages32, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a3 : (univ.filter fun i => ages32 i < 72).card = 27 := by
    rw [Finset.card_filter]; simp [ages32, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a4 : (univ.filter fun i => ages32 i = 72).card = 1 := by
    rw [Finset.card_filter]; simp [ages32, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  rw [a1, a2, a3, a4]
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.25. Jesse is 37th of 180, so 143 students rank
below him and one (himself) has his rank: his percentile is `(143 + 1/2)/180 · 100 = 79.72...` (strictly
between 79.72 and 79.73), which rounds to 80. -/
@[kb "openstaxintrostats2e" "Exercise 2.25, p. 140"]
theorem ex_2_25_jesse_percentile :
    (180 - 37 = 143) ∧ (79.72 < ((143 : ℝ) + 1 / 2) / 180 * 100 ∧ ((143 : ℝ) + 1 / 2) / 180 * 100 < 79.73) ∧
      round (((143 : ℝ) + 1 / 2) / 180 * 100) = 80 := by
  refine ⟨by norm_num, ⟨by norm_num, by norm_num⟩, ?_⟩
  rw [round_eq, Int.floor_eq_iff]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.32. The top 12% of students are those at or above
the 88th percentile (100 - 12 = 88), and the students at or above the 96th percentile of their school, the
"eligible in the local context", are the top 100 - 96 = 4% of each high school. -/
@[kb "openstaxintrostats2e" "Exercise 2.32, p. 141"]
theorem ex_2_32_admission_percentiles :
    (100 - 12 = 88) ∧ (100 - 96 = 4) := by
  decide

/-- OpenStax Introductory Statistics 2e Practice exercise 2.33. A budget at the 34th percentile of prices
affords the 34% of houses at or below it and not the other 66%: 34 + 66 = 100. -/
@[kb "openstaxintrostats2e" "Exercise 2.33, p. 141"]
theorem ex_2_33_affordable_houses :
    (34 + 66 = 100) ∧ ((34 : ℚ) / 100 = 0.34) := by
  refine ⟨by decide, by norm_num⟩

/-- The 65 numbers of cars sold per week (14 threes, 19 fours, 12 fives, 9 sixes, 11 sevens). -/
private def salesV : Fin 65 → ℝ := ![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7,
  7, 7, 7, 7, 7, 7, 7]

private lemma salesV_mono : Monotone salesV := by
  unfold salesV; mono_tac

/-- OpenStax Introductory Statistics 2e Practice exercise 2.34. For the 65 car salespersons the first
quartile is the 25th percentile: its index is `0.25 · 66 = 16.5`, the average of the 16th and 17th ordered
values, both 4, so it is 4. -/
@[kb "openstaxintrostats2e" "Exercise 2.34, p. 141"]
theorem ex_2_34_first_quartile :
    percentileAt salesV 25 = 4 := by
  (pct_tac 16 17; simp [entry, salesV] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.35. The median of the 65 numbers of cars sold is
the 33rd ordered value, 4 (equal to the 50th percentile with index 33). -/
@[kb "openstaxintrostats2e" "Exercise 2.35, p. 141"]
theorem ex_2_35_median :
    median salesV = 4 ∧ percentileAt salesV 50 = 4 := by
  refine ⟨?_, ?_⟩
  · rw [median_odd (m := 32) salesV salesV_mono]; simp [salesV]
  · (pct_tac 33 33; simp [entry, salesV] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.36. The third quartile of the 65 numbers of cars
sold is the 75th percentile, index `0.75 · 66 = 49.5`: the average of the 49th and 50th values, both 6. -/
@[kb "openstaxintrostats2e" "Exercise 2.36, p. 141"]
theorem ex_2_36_third_quartile :
    percentileAt salesV 75 = 6 := by
  (pct_tac 49 50; simp [entry, salesV] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.37. The interquartile range of the 65 numbers of
cars sold is `6 - 4 = 2`. -/
@[kb "openstaxintrostats2e" "Exercise 2.37, p. 141"]
theorem ex_2_37_iqr :
    percentileAt salesV 75 - percentileAt salesV 25 = 2 := by
  rw [ex_2_36_third_quartile, ex_2_34_first_quartile]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.38. The 10th percentile of the 65 numbers of cars
sold has index `0.10 · 66 = 6.6`: the average of the 6th and 7th values, both 3, so it is 3. -/
@[kb "openstaxintrostats2e" "Exercise 2.38, p. 141"]
theorem ex_2_38_tenth_percentile :
    percentileAt salesV 10 = 3 := by
  (pct_tac 6 7; simp [entry, salesV] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.39. The 70th percentile of the 65 numbers of cars
sold has index `0.70 · 66 = 46.2`: the average of the 46th and 47th values, both 6, so it is 6. -/
@[kb "openstaxintrostats2e" "Exercise 2.39, p. 141"]
theorem ex_2_39_seventieth_percentile :
    percentileAt salesV 70 = 6 := by
  (pct_tac 46 47; simp [entry, salesV] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 2.40. The five numbers of the box plot of the 65
numbers of cars sold: minimum 3 (first value), first quartile 4, median 4, third quartile 6, maximum 7
(last value). -/
@[kb "openstaxintrostats2e" "Exercise 2.40, p. 141"]
theorem ex_2_40_five_number_summary :
    salesV 0 = 3 ∧ percentileAt salesV 25 = 4 ∧ median salesV = 4 ∧ percentileAt salesV 75 = 6 ∧
      salesV 64 = 7 := by
  refine ⟨by simp [salesV], ex_2_34_first_quartile, ex_2_35_median.1, ex_2_36_third_quartile, by simp [salesV]⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 2.41. In the box plot of the 65 numbers of cars sold
the first quartile equals the median (both 4): the left edge of the box and the median line coincide, because
19 of the 65 values (more than a quarter) equal 4. The whiskers have the same length: 4 - 3 = 1 = 7 - 6. -/
@[kb "openstaxintrostats2e" "Exercise 2.41, p. 141"]
theorem ex_2_41_box_plot_concentration :
    percentileAt salesV 25 = median salesV ∧ (univ.filter fun i => salesV i = 4).card = 19 ∧
      65 < 4 * 19 ∧ (4 : ℝ) - 3 = 7 - 6 := by
  refine ⟨by rw [ex_2_34_first_quartile, ex_2_35_median.1], ?_, by norm_num, by norm_num⟩
  rw [Finset.card_filter]; simp [salesV, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.42 (a). In the grade table (classes
49.5-59.5, ..., 89.5-99.5 with midpoints 54.5, ..., 94.5 and frequencies 2, 3, 8, 12, 5) the frequencies add
to 30 and the grouped mean is 159/2 = 79.5. -/
@[kb "openstaxintrostats2e" "Exercise 2.42, p. 141"]
theorem ex_2_42a_grade_mean :
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    let f : Fin 5 → ℝ := ![2, 3, 8, 12, 5]
    (∑ i, f i) = 30 ∧ (∑ i, f i * m i) / (∑ i, f i) = 79.5 := by
  intro m f
  refine ⟨?_, ?_⟩ <;> simp [m, f, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.42 (b). In the daily-low-temperature table
(frequencies 53, 32, 15, 1, 0 over the same classes) the frequencies add to 101 and the grouped mean is
12309/202, between 60.93 and 60.94. -/
@[kb "openstaxintrostats2e" "Exercise 2.42, p. 141"]
theorem ex_2_42b_temperature_mean :
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    let f : Fin 5 → ℝ := ![53, 32, 15, 1, 0]
    (∑ i, f i) = 101 ∧ (∑ i, f i * m i) / (∑ i, f i) = 12309 / 202 ∧
      (60.93 < (12309 : ℝ) / 202 ∧ (12309 : ℝ) / 202 < 60.94) := by
  intro m f
  refine ⟨?_, ?_, by norm_num, by norm_num⟩ <;> simp [m, f, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.42 (c). In the points-per-game table
(frequencies 14, 32, 15, 23, 2) the frequencies add to 86 and the grouped mean is 6077/86, between 70.66
and 70.67. -/
@[kb "openstaxintrostats2e" "Exercise 2.42, p. 141"]
theorem ex_2_42c_points_mean :
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    let f : Fin 5 → ℝ := ![14, 32, 15, 23, 2]
    (∑ i, f i) = 86 ∧ (∑ i, f i * m i) / (∑ i, f i) = 6077 / 86 ∧
      (70.66 < (6077 : ℝ) / 86 ∧ (6077 : ℝ) / 86 < 70.67) := by
  intro m f
  refine ⟨?_, ?_, by norm_num, by norm_num⟩ <;> simp [m, f, Fin.sum_univ_succ] <;> norm_num

/-- The lengths of the 27 boats in the marina (Practice exercises 2.43 to 2.45). -/
private def boats : Fin 27 → ℝ := ![16, 17, 19, 20, 20, 21, 23, 24, 25, 25, 25, 26, 26, 27, 27, 27, 28,
  29, 30, 32, 33, 33, 34, 35, 37, 39, 40]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.43. The 27 boat lengths add to 738, so the mean
is 738/27 = 82/3, strictly between 27.33 and 27.34. -/
@[kb "openstaxintrostats2e" "Exercise 2.43, p. 142"]
theorem ex_2_43_boats_mean :
    (∑ i, boats i = 738) ∧ mean boats = 82 / 3 ∧ (27.33 < mean boats ∧ mean boats < 27.34) := by
  have h : ∑ i, boats i = 738 := by simp [boats, Fin.sum_univ_succ]; norm_num
  have hm : mean boats = 82 / 3 := by rw [mean, h]; norm_num
  refine ⟨h, hm, ?_, ?_⟩ <;> rw [hm] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.44. The median of the 27 ordered boat lengths is
the 14th, 27. -/
@[kb "openstaxintrostats2e" "Exercise 2.44, p. 142"]
theorem ex_2_44_boats_median :
    median boats = 27 := by
  have hx : Monotone boats := by unfold boats; mono_tac
  rw [median_odd (m := 13) boats hx]; simp [boats]

/-- OpenStax Introductory Statistics 2e Practice exercise 2.45. In the boat lengths the values 25 and 27 each
occur three times and every other length occurs at most twice, so the data are bimodal with modes 25 and
27. -/
@[kb "openstaxintrostats2e" "Exercise 2.45, p. 142"]
theorem ex_2_45_boats_modes :
    let l : List ℕ := [16, 17, 19, 20, 20, 21, 23, 24, 25, 25, 25, 26, 26, 27, 27, 27, 28, 29, 30, 32, 33,
      33, 34, 35, 37, 39, 40]
    (∀ v : ℕ, l.count v ≤ 3) ∧ (∀ v : ℕ, l.count v = 3 ↔ v = 25 ∨ v = 27) := by
  intro l
  have key : ∀ v < 41, l.count v ≤ 3 ∧ (l.count v = 3 ↔ v = 25 ∨ v = 27) := by decide
  have out : ∀ v : ℕ, 41 ≤ v → l.count v = 0 := fun v hv =>
    List.count_eq_zero.2 (by simp [l]; omega)
  refine ⟨fun v => ?_, fun v => ?_⟩
  · by_cases h : v < 41
    · exact (key v h).1
    · rw [out v (by omega)]; omega
  · by_cases h : v < 41
    · exact (key v h).2
    · rw [out v (by omega)]; omega

/-- OpenStax Introductory Statistics 2e Practice exercise 2.46. The sample mean of the 65 numbers of cars
sold is 309/65, between 4.75 and 4.76. -/
@[kb "openstaxintrostats2e" "Exercise 2.46, p. 143"]
theorem ex_2_46_sales_mean :
    (∑ i, salesV i = 309) ∧ mean salesV = 309 / 65 ∧ (4.75 < mean salesV ∧ mean salesV < 4.76) := by
  have h : ∑ i, salesV i = 309 := by simp [salesV, Fin.sum_univ_succ]; norm_num
  have hm : mean salesV = 309 / 65 := by rw [mean, h]; norm_num
  refine ⟨h, hm, ?_, ?_⟩ <;> rw [hm] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.47. The median number of cars sold, among the 65
salespersons, is 4 (the 33rd ordered value). -/
@[kb "openstaxintrostats2e" "Exercise 2.47, p. 143"]
theorem ex_2_47_sales_median :
    median salesV = 4 :=
  ex_2_35_median.1

/-- OpenStax Introductory Statistics 2e Practice exercise 2.48. The mode of the numbers of cars sold is 4: it
occurs 19 times and no other value occurs 19 times or more. -/
@[kb "openstaxintrostats2e" "Exercise 2.48, p. 143"]
theorem ex_2_48_sales_mode :
    let l : List ℕ := List.replicate 14 3 ++ List.replicate 19 4 ++ List.replicate 12 5 ++
      List.replicate 9 6 ++ List.replicate 11 7
    l.count 4 = 19 ∧ ∀ v : ℕ, v ≠ 4 → l.count v < 19 := by
  intro l
  have key : ∀ v < 8, v ≠ 4 → l.count v < 19 := by decide
  refine ⟨by decide, fun v hv => ?_⟩
  by_cases h : v < 8
  · exact key v h hv
  · have : l.count v = 0 := List.count_eq_zero.2 (by simp [l]; omega)
    rw [this]; omega

/-- OpenStax Introductory Statistics 2e Practice exercise 2.49. For the 20 values 1, 1, 1, 2, 2, 2, 2, 3, ...,
5, 5 the mean is 57/20 = 2.85 and the median is 3, only 0.15 apart (mean slightly below the median), and the
most frequent value, 3 (eight times), lies at the middle: the data are close to symmetric. -/
@[kb "openstaxintrostats2e" "Exercise 2.49, p. 143"]
theorem ex_2_49_symmetry :
    let x : Fin 20 → ℝ := ![1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 5, 5]
    mean x = 2.85 ∧ median x = 3 ∧ (3 : ℝ) - 2.85 = 0.15 ∧ (univ.filter fun i => x i = 3).card = 8 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, by norm_num, ?_⟩
  · simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  · rw [median_even (m := 9) x hx]; simp [x] <;> norm_num
  · rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.50. For the nine values 16, 17, 19, 22, 22, 22,
22, 22, 23 the mean is 185/9 (about 20.6), below the median 22 and the mode 22: the long tail is on the left,
so the data are skewed left. -/
@[kb "openstaxintrostats2e" "Exercise 2.50, p. 143"]
theorem ex_2_50_skewed_left :
    let x : Fin 9 → ℝ := ![16, 17, 19, 22, 22, 22, 22, 22, 23]
    mean x = 185 / 9 ∧ median x = 22 ∧ mean x < median x ∧ (univ.filter fun i => x i = 22).card = 5 := by
  intro x
  have hx : Monotone x := by mono_tac
  have hm : mean x = 185 / 9 := by simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  have hd : median x = 22 := by rw [median_odd (m := 4) x hx]; simp [x]
  refine ⟨hm, hd, by rw [hm, hd]; norm_num, ?_⟩
  rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.51. For the ten values 87 (five times), 88, 89, 89,
90, 91 the mean is 441/5 = 88.2, above the median 87.5 and the mode 87: the long tail is on the right, so the
data are skewed right. -/
@[kb "openstaxintrostats2e" "Exercise 2.51, p. 143"]
theorem ex_2_51_skewed_right :
    let x : Fin 10 → ℝ := ![87, 87, 87, 87, 87, 88, 89, 89, 90, 91]
    mean x = 88.2 ∧ median x = 87.5 ∧ median x < mean x ∧ (univ.filter fun i => x i = 87).card = 5 := by
  intro x
  have hx : Monotone x := by mono_tac
  have hm : mean x = 88.2 := by simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  have hd : median x = 87.5 := by rw [median_even (m := 4) x hx]; simp [x] <;> norm_num
  refine ⟨hm, hd, by rw [hm, hd]; norm_num, ?_⟩
  rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.64. For the 15 values 3, 4, 5, 5, 6, 6, 6, 6, 7
(seven times) the mean and the median are both 6, yet the data are not symmetric about 6: the value 7 occurs
seven times but its mirror image 5 only twice. -/
@[kb "openstaxintrostats2e" "Exercise 2.64, p. 146"]
theorem ex_2_64_not_symmetric :
    let x : Fin 15 → ℝ := ![3, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7]
    mean x = 6 ∧ median x = 6 ∧ (univ.filter fun i => x i = 7).card = 7 ∧
      (univ.filter fun i => x i = 5).card = 2 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  · rw [median_odd (m := 7) x hx]; simp [x]
  · rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  · rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.65. For the twelve values 11, 11, 12, 12, 12, 12,
13, 15, 17, 22, 22, 22 the mode is 12 (four times), the median is 12.5 and the mean is 181/12, about 15.1:
the mean is the greatest of the three. -/
@[kb "openstaxintrostats2e" "Exercise 2.65, p. 146"]
theorem ex_2_65_mean_is_greatest :
    let x : Fin 12 → ℝ := ![11, 11, 12, 12, 12, 12, 13, 15, 17, 22, 22, 22]
    mean x = 181 / 12 ∧ median x = 12.5 ∧ (univ.filter fun i => x i = 12).card = 4 ∧
      (12 : ℝ) < median x ∧ median x < mean x := by
  intro x
  have hx : Monotone x := by mono_tac
  have hm : mean x = 181 / 12 := by simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  have hd : median x = 12.5 := by rw [median_even (m := 5) x hx]; simp [x] <;> norm_num
  refine ⟨hm, hd, ?_, by rw [hd]; norm_num, by rw [hm, hd]; norm_num⟩
  rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.66. For the eleven values 56, 56, 56, 58, 59, 60,
62, 64, 64, 65, 67 the mode is 56 (three times), the median is 60 and the mean is 667/11, about 60.6: the mode
is the least of the three. -/
@[kb "openstaxintrostats2e" "Exercise 2.66, p. 146"]
theorem ex_2_66_mode_is_least :
    let x : Fin 11 → ℝ := ![56, 56, 56, 58, 59, 60, 62, 64, 64, 65, 67]
    mean x = 667 / 11 ∧ median x = 60 ∧ (univ.filter fun i => x i = 56).card = 3 ∧
      (56 : ℝ) < median x ∧ median x < mean x := by
  intro x
  have hx : Monotone x := by mono_tac
  have hm : mean x = 667 / 11 := by simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  have hd : median x = 60 := by rw [median_odd (m := 5) x hx]; simp [x]
  refine ⟨hm, hd, ?_, by rw [hd]; norm_num, by rw [hm, hd]; norm_num⟩
  rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- The 20 distances from retail stores to the distribution center (Practice exercises 2.69 and 2.70). -/
private def distances : Fin 20 → ℝ := ![29, 37, 38, 40, 58, 67, 68, 69, 76, 86, 87, 95, 96, 96, 99, 106,
  112, 127, 145, 150]

private lemma distances_mean : mean distances = 1681 / 20 := by
  simp [mean, distances, Fin.sum_univ_succ] <;> norm_num

private lemma distances_sd : 34.51 < sampleStdDev distances ∧ sampleStdDev distances < 34.52 := by
  refine sd_bounds distances (by norm_num) (by norm_num) ?_ ?_
  · simp only [sampleVariance, sumSqDev, distances_mean]
    simp [distances, Fin.sum_univ_succ] <;> norm_num
  · simp only [sampleVariance, sumSqDev, distances_mean]
    simp [distances, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.69. The sample standard deviation of the 20
distances (mean 1681/20 = 84.05 miles) lies between 34.51 and 34.52, i.e. 34.5 miles to the nearest tenth. -/
@[kb "openstaxintrostats2e" "Exercise 2.69, p. 146"]
theorem ex_2_69_distances_sd :
    mean distances = 84.05 ∧ (34.51 < sampleStdDev distances ∧ sampleStdDev distances < 34.52) := by
  refine ⟨by rw [distances_mean]; norm_num, distances_sd⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 2.70. The value one standard deviation below the mean
distance is `84.05 - s`, which lies between 49.53 and 49.54 (about 49.5 miles). -/
@[kb "openstaxintrostats2e" "Exercise 2.70, p. 146"]
theorem ex_2_70_one_sd_below_mean :
    49.53 < mean distances - sampleStdDev distances ∧ mean distances - sampleStdDev distances < 49.54 := by
  obtain ⟨h1, h2⟩ := distances_sd
  rw [distances_mean]
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 2.71. Fredo's batting average 0.158 against a team mean
0.166 and standard deviation 0.012 has z-score -2/3 (about -0.67); Karl's 0.177 against 0.189 and 0.015 has
z-score -4/5 = -0.8. Fredo's z-score is higher, so Fredo did better relative to his team. -/
@[kb "openstaxintrostats2e" "Exercise 2.71, p. 146"]
theorem ex_2_71_batting_z_scores :
    ((0.158 : ℝ) - 0.166) / 0.012 = -2 / 3 ∧ ((0.177 : ℝ) - 0.189) / 0.015 = -4 / 5 ∧
      ((0.177 : ℝ) - 0.189) / 0.015 < ((0.158 : ℝ) - 0.166) / 0.012 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 2.72. Three standard deviations from the team mean:
for Fredo's team (0.166, 0.012) the values are 0.202 and 0.130; for Karl's team (0.189, 0.015) they are 0.234
and 0.144. -/
@[kb "openstaxintrostats2e" "Exercise 2.72, p. 146"]
theorem ex_2_72_three_sd_from_mean :
    ((0.166 : ℝ) + 3 * 0.012 = 0.202 ∧ (0.166 : ℝ) - 3 * 0.012 = 0.130) ∧
      ((0.189 : ℝ) + 3 * 0.015 = 0.234 ∧ (0.189 : ℝ) - 3 * 0.015 = 0.144) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 2.73 (a). For the grade table (midpoints 54.5, ...,
94.5, frequencies 2, 3, 8, 12, 5, grouped mean 79.5) the standard deviation with divisor `n - 1 = 29` lies
between 11.06 and 11.07. -/
@[kb "openstaxintrostats2e" "Exercise 2.73, p. 146"]
theorem ex_2_73a_grade_sd :
    let f : Fin 5 → ℝ := ![2, 3, 8, 12, 5]
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    11.06 < Real.sqrt ((∑ i, f i * (m i - 79.5) ^ 2) / 29) ∧
      Real.sqrt ((∑ i, f i * (m i - 79.5) ^ 2) / 29) < 11.07 := by
  intro f m
  refine ⟨?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.73 (b). For the daily-low-temperature table
(frequencies 53, 32, 15, 1, 0; grouped mean 12309/202) the standard deviation with divisor `n - 1 = 100` lies
between 7.69 and 7.70. -/
@[kb "openstaxintrostats2e" "Exercise 2.73, p. 146"]
theorem ex_2_73b_temperature_sd :
    let f : Fin 5 → ℝ := ![53, 32, 15, 1, 0]
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    7.69 < Real.sqrt ((∑ i, f i * (m i - 12309 / 202) ^ 2) / 100) ∧
      Real.sqrt ((∑ i, f i * (m i - 12309 / 202) ^ 2) / 100) < 7.70 := by
  intro f m
  refine ⟨?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 2.73 (c). For the points-per-game table (frequencies
14, 32, 15, 23, 2; grouped mean 6077/86) the standard deviation with divisor `n - 1 = 85` lies between 11.18
and 11.19. -/
@[kb "openstaxintrostats2e" "Exercise 2.73, p. 146"]
theorem ex_2_73c_points_sd :
    let f : Fin 5 → ℝ := ![14, 32, 15, 23, 2]
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    11.18 < Real.sqrt ((∑ i, f i * (m i - 6077 / 86) ^ 2) / 85) ∧
      Real.sqrt ((∑ i, f i * (m i - 6077 / 86) ^ 2) / 85) < 11.19 := by
  intro f m
  refine ⟨?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num

end UndergradKB.Statistics.Course.PracticeC2
