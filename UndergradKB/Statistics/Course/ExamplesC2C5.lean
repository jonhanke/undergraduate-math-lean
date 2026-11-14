import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Probability.ConditionalProbability
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Percentile
import UndergradKB.Statistics.Descriptive

/-!
# Worked examples, chapter 2 (OpenStax *Introductory Statistics 2e*): remaining examples

Examples of chapter 2 that earlier files skipped because the book answers them with a graph:
stem plots, histograms and frequency polygons become exact counts of data in classes,
means, medians and fences; percentile interpretations become probability statements.
Data are concrete vectors `![...] : Fin n → ℝ`; statistics use the repository's `mean`, `median`.
-/

open MeasureTheory Finset

namespace UndergradKB.Statistics.Course.ExamplesC2C5

open UndergradKB.Statistics

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

/-- Counting the entries of a concrete vector that satisfy a numeric condition. -/
local macro "count_tac" : tactic =>
  `(tactic| (rw [Finset.card_filter]
             simp +zetaDelta [Fin.sum_univ_succ, -Finset.sum_boole]
             try norm_num))

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
  hx (Fin.mk_le_mk.2 (by have := Fin.le_def.1 hab; omega))

/-- Number of entries of a data vector equal to `v` (the frequency of `v`). -/
private noncomputable def freq {n : ℕ} (x : Fin n → ℝ) (v : ℝ) : ℕ := (univ.filter fun i => x i = v).card

/-- OpenStax Introductory Statistics 2e Example 2.2. The 21 distances (in km) to local supermarkets:
the stem counts of the stem plot are 2, 3, 5, 6, 2, 2 and 1 for the stems 1, 2, 3, 4, 5, 6 and 12
(leaves are tenths). -/
@[kb "openstaxintrostats2e" "Example 2.2, p. 79"]
theorem example_2_2_stem_counts :
    let x : Fin 21 → ℝ := ![1.1, 1.5, 2.3, 2.5, 2.7, 3.2, 3.3, 3.3, 3.5, 3.8, 4.0, 4.2, 4.5, 4.5,
      4.7, 4.8, 5.5, 5.6, 6.5, 6.7, 12.3]
    (univ.filter fun i => 1 ≤ x i ∧ x i < 2).card = 2 ∧
    (univ.filter fun i => 2 ≤ x i ∧ x i < 3).card = 3 ∧
    (univ.filter fun i => 3 ≤ x i ∧ x i < 4).card = 5 ∧
    (univ.filter fun i => 4 ≤ x i ∧ x i < 5).card = 6 ∧
    (univ.filter fun i => 5 ≤ x i ∧ x i < 6).card = 2 ∧
    (univ.filter fun i => 6 ≤ x i ∧ x i < 7).card = 2 ∧
    (univ.filter fun i => 12 ≤ x i ∧ x i < 13).card = 1 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> count_tac

/-- OpenStax Introductory Statistics 2e Example 2.2 (outlier). For the same 21 distances the median is
4.0, the quartiles (medians of the lower and upper ten values) are 2.95 and 5.15, the IQR is 2.2, and
the upper fence `Q3 + 1.5 IQR = 8.45` lies below 12.3, so 12.3 is a potential outlier, as the book
suspects; 6.7 is not. -/
@[kb "openstaxintrostats2e" "Example 2.2, p. 79"]
theorem example_2_2_outlier_by_iqr :
    let x : Fin 21 → ℝ := ![1.1, 1.5, 2.3, 2.5, 2.7, 3.2, 3.3, 3.3, 3.5, 3.8, 4.0, 4.2, 4.5, 4.5,
      4.7, 4.8, 5.5, 5.6, 6.5, 6.7, 12.3]
    median x = 4.0 ∧ median (lowerHalf x 10 (by omega)) = 2.95 ∧
      median (upperHalf x 10 (by omega)) = 5.15 ∧
      (5.15 : ℝ) - 2.95 = 2.2 ∧ (5.15 : ℝ) + 1.5 * 2.2 = 8.45 ∧ (6.7 : ℝ) < 8.45 ∧
      (8.45 : ℝ) < 12.3 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [median_odd (m := 10) x hx]; simp [x]
  · rw [median_even (m := 4) _ (lowerHalf_mono hx 10 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 4) _ (upperHalf_mono hx 10 (by omega))]; simp [upperHalf, x] <;> norm_num
  all_goals norm_num

/-- OpenStax Introductory Statistics 2e Example 2.3 (inauguration ages). The 44 ages of U.S.
presidents at inauguration (table 2.3): 9 are in the forties, 25 in the fifties and 10 in the
sixties (the stem counts of the stem plot), and the mean age is `2406/44`. -/
@[kb "openstaxintrostats2e" "Example 2.3, p. 80"]
theorem example_2_3_inauguration_ages :
    let x : Fin 44 → ℝ := ![57, 61, 57, 57, 58, 57, 61, 54, 68, 51, 49, 64, 50, 48, 65, 52, 56, 46,
      54, 49, 51, 47, 55, 55, 54, 42, 51, 56, 55, 51, 54, 51, 60, 62, 43, 55, 56, 61, 52, 69, 64, 47,
      54, 47]
    (univ.filter fun i => 40 ≤ x i ∧ x i < 50).card = 9 ∧
    (univ.filter fun i => 50 ≤ x i ∧ x i < 60).card = 25 ∧
    (univ.filter fun i => 60 ≤ x i ∧ x i < 70).card = 10 ∧
    mean x = 2406 / 44 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_⟩
  · count_tac
  · count_tac
  · count_tac
  · simp +zetaDelta [mean, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.3 (ages at death). The 39 ages at death of the
presidents (table 2.4) have stem counts 2, 5, 12, 11, 5, 4 for the forties through the nineties,
and the mean age at death is `2746/39`. -/
@[kb "openstaxintrostats2e" "Example 2.3, p. 80"]
theorem example_2_3_death_ages :
    let x : Fin 39 → ℝ := ![67, 90, 83, 85, 73, 80, 78, 79, 68, 71, 53, 65, 74, 64, 77, 56, 66, 63,
      70, 49, 56, 71, 67, 71, 58, 60, 72, 67, 57, 60, 90, 63, 88, 78, 46, 64, 81, 93, 93]
    (univ.filter fun i => 40 ≤ x i ∧ x i < 50).card = 2 ∧
    (univ.filter fun i => 50 ≤ x i ∧ x i < 60).card = 5 ∧
    (univ.filter fun i => 60 ≤ x i ∧ x i < 70).card = 12 ∧
    (univ.filter fun i => 70 ≤ x i ∧ x i < 80).card = 11 ∧
    (univ.filter fun i => 80 ≤ x i ∧ x i < 90).card = 5 ∧
    (univ.filter fun i => 90 ≤ x i ∧ x i < 100).card = 4 ∧
    mean x = 2746 / 39 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · simp +zetaDelta [mean, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.4. Forty parents report how often per week a
teenager must be reminded of chores (0 to 5 times, frequencies 2, 5, 8, 14, 7, 4): the frequencies
total 40, the value 3 has relative frequency `7/20` (the highest), the cumulative frequency up to
2 reminders is 15, and the mean number of reminders is `111/40`. -/
@[kb "openstaxintrostats2e" "Example 2.4, p. 83"]
theorem example_2_4_chore_reminders :
    let f : Fin 6 → ℝ := ![2, 5, 8, 14, 7, 4]
    let v : Fin 6 → ℝ := ![0, 1, 2, 3, 4, 5]
    (∑ i, f i) = 40 ∧ f 3 / 40 = 7 / 20 ∧ (∀ i, f i ≤ f 3) ∧ f 0 + f 1 + f 2 = 15 ∧
      (∑ i, f i * v i) / ∑ i, f i = 111 / 40 := by
  intro f v
  have h1 : (∑ i, f i) = 40 := by simp [f, Fin.sum_univ_succ]; norm_num
  have h2 : (∑ i, f i * v i) = 111 := by simp [f, v, Fin.sum_univ_succ]; norm_num
  refine ⟨h1, by simp [f]; norm_num, fun i => ?_, by simp [f]; norm_num, ?_⟩
  · fin_cases i <;> simp [f] <;> norm_num
  · rw [h1, h2]

/-- OpenStax Introductory Statistics 2e Example 2.5. The shares of U.S. TikTok users by age group
(10-19, 20-29, 30-39, 40-49, 50+) are 32.5, 29.5, 16.4, 13.9 and 7.1 per cent: the two youngest
groups together make 62 per cent, and the five listed shares total 99.4 per cent, slightly under
100 (the table in the book is not exactly complete). -/
@[kb "openstaxintrostats2e" "Example 2.5, p. 84"]
theorem example_2_5_tiktok_age_shares :
    let p : Fin 5 → ℝ := ![32.5, 29.5, 16.4, 13.9, 7.1]
    p 0 + p 1 = 62 ∧ (∑ i, p i) = 99.4 ∧ (∑ i, p i) < 100 ∧ (∀ i, p i ≤ p 0) := by
  intro p
  refine ⟨by simp [p]; norm_num, ?_, ?_, fun i => ?_⟩
  · simp [p, Fin.sum_univ_succ]; norm_num
  · simp [p, Fin.sum_univ_succ]; norm_num
  · fin_cases i <;> simp [p] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.6. Projected 2030 high school graduates by region
(Northeast, Midwest, South, West): 517 720, 695 170, 1 253 540 and 749 400 graduates, total
3 215 830, and each region's share of the total agrees with the book's percentage column
(16.1, 21.6, 39.0, 23.3, which total 100) to within half a tenth of a percentage point. -/
@[kb "openstaxintrostats2e" "Example 2.6, p. 85"]
theorem example_2_6_graduates_by_region :
    let n : Fin 4 → ℝ := ![517720, 695170, 1253540, 749400]
    let pct : Fin 4 → ℝ := ![16.1, 21.6, 39.0, 23.3]
    (∑ i, n i) = 3215830 ∧ (∑ i, pct i) = 100 ∧
      ∀ i, |100 * n i / 3215830 - pct i| < 0.05 := by
  intro n pct
  refine ⟨by simp [n, Fin.sum_univ_succ]; norm_num, by simp [pct, Fin.sum_univ_succ]; norm_num,
    fun i => ?_⟩
  fin_cases i <;> simp [n, pct] <;> rw [abs_lt] <;> constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.7. The 100 heights (inches) of semiprofessional
soccer players grouped with the book's boundaries 59.95, 61.95, ..., 75.95 (width 2): the eight
class counts are 5, 3, 15, 40, 17, 12, 7 and 1, which total 100. -/
@[kb "openstaxintrostats2e" "Example 2.7, p. 87"]
theorem example_2_7_soccer_heights_histogram :
    let x : Fin 100 → ℝ := ![60, 60.5, 61, 61, 61.5, 63.5, 63.5, 63.5, 64, 64, 64, 64, 64, 64, 64,
      64.5, 64.5, 64.5, 64.5, 64.5, 64.5, 64.5, 64.5, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66,
      66.5, 66.5, 66.5, 66.5, 66.5, 66.5, 66.5, 66.5, 66.5, 66.5, 66.5, 67, 67, 67, 67, 67, 67, 67,
      67, 67, 67, 67, 67, 67.5, 67.5, 67.5, 67.5, 67.5, 67.5, 67.5, 68, 68, 69, 69, 69, 69, 69, 69,
      69, 69, 69, 69, 69.5, 69.5, 69.5, 69.5, 69.5, 70, 70, 70, 70, 70, 70, 70.5, 70.5, 70.5, 71,
      71, 71, 72, 72, 72, 72.5, 72.5, 73, 73.5, 74]
    (univ.filter fun i => 59.95 ≤ x i ∧ x i < 61.95).card = 5 ∧
    (univ.filter fun i => 61.95 ≤ x i ∧ x i < 63.95).card = 3 ∧
    (univ.filter fun i => 63.95 ≤ x i ∧ x i < 65.95).card = 15 ∧
    (univ.filter fun i => 65.95 ≤ x i ∧ x i < 67.95).card = 40 ∧
    (univ.filter fun i => 67.95 ≤ x i ∧ x i < 69.95).card = 17 ∧
    (univ.filter fun i => 69.95 ≤ x i ∧ x i < 71.95).card = 12 ∧
    (univ.filter fun i => 71.95 ≤ x i ∧ x i < 73.95).card = 7 ∧
    (univ.filter fun i => 73.95 ≤ x i ∧ x i < 75.95).card = 1 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> count_tac

/-- OpenStax Introductory Statistics 2e Example 2.8. The numbers of books bought by 50 part-time
students: with the classes 0.5-1.5, 1.5-2.5, ..., 5.5-6.5 (each value in the middle of its class)
the class counts are 11, 10, 16, 6, 5 and 2, and the mean number of books is `14/5`. -/
@[kb "openstaxintrostats2e" "Example 2.8, p. 89"]
theorem example_2_8_books_histogram :
    let x : Fin 50 → ℝ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6]
    (univ.filter fun i => 0.5 ≤ x i ∧ x i < 1.5).card = 11 ∧
    (univ.filter fun i => 1.5 ≤ x i ∧ x i < 2.5).card = 10 ∧
    (univ.filter fun i => 2.5 ≤ x i ∧ x i < 3.5).card = 16 ∧
    (univ.filter fun i => 3.5 ≤ x i ∧ x i < 4.5).card = 6 ∧
    (univ.filter fun i => 4.5 ≤ x i ∧ x i < 5.5).card = 5 ∧
    (univ.filter fun i => 5.5 ≤ x i ∧ x i < 6.5).card = 2 ∧
    mean x = 14 / 5 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · simp +zetaDelta [mean, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.9. Twenty-five classmates' weekend video-game
hours. The book leaves the class layout open; with classes of width 5 starting at 0 (a value on a
left boundary belongs to the class, one on the right boundary does not) the counts are 2, 3, 4, 7
and 9 for 0-5, 5-10, 10-15, 15-20 and 20-25, and the mean is `15.552`. -/
@[kb "openstaxintrostats2e" "Example 2.9, p. 91"]
theorem example_2_9_video_game_histogram :
    let x : Fin 25 → ℝ := ![9.95, 10, 2.25, 16.75, 0, 19.5, 22.5, 7.5, 15, 12.75, 5.5, 11, 10,
      20.75, 17.5, 23, 21.9, 24, 23.75, 18, 20, 15, 22.9, 18.8, 20.5]
    (univ.filter fun i => 0 ≤ x i ∧ x i < 5).card = 2 ∧
    (univ.filter fun i => 5 ≤ x i ∧ x i < 10).card = 3 ∧
    (univ.filter fun i => 10 ≤ x i ∧ x i < 15).card = 4 ∧
    (univ.filter fun i => 15 ≤ x i ∧ x i < 20).card = 7 ∧
    (univ.filter fun i => 20 ≤ x i ∧ x i < 25).card = 9 ∧
    mean x = 15.552 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · count_tac
  · simp +zetaDelta [mean, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.10. The calculus final test scores table (class
frequencies 5, 10, 30, 40, 15): the frequencies total 100, the cumulative-frequency column
5, 15, 45, 85, 100 is the running sum of the frequencies, and the mean estimated from the class
midpoints 54.5, ..., 94.5 is 79.5. -/
@[kb "openstaxintrostats2e" "Example 2.10, p. 92"]
theorem example_2_10_test_score_frequencies :
    let f : Fin 5 → ℝ := ![5, 10, 30, 40, 15]
    let c : Fin 5 → ℝ := ![5, 15, 45, 85, 100]
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    (∑ i, f i) = 100 ∧ (∀ k : Fin 5, ∑ i ∈ univ.filter (· ≤ k), f i = c k) ∧
      (∑ i, f i * m i) / ∑ i, f i = 79.5 := by
  intro f c m
  refine ⟨by simp [f, Fin.sum_univ_succ]; norm_num, fun k => ?_, ?_⟩
  · fin_cases k <;> simp [Finset.sum_filter, Fin.sum_univ_succ, f, c, Fin.le_def] <;> norm_num
  · simp [f, m, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.11. Overlaying the calculus final test scores
(frequencies 5, 10, 30, 40, 15) and the final grades (frequencies 10, 10, 30, 45, 5): both tables
cover 100 students, the grades' cumulative column 10, 20, 50, 95, 100 is the running sum, and the
class-midpoint means are 79.5 for the scores and 77 for the grades, so the grades are centred
slightly lower. -/
@[kb "openstaxintrostats2e" "Example 2.11, p. 93"]
theorem example_2_11_scores_and_grades :
    let f : Fin 5 → ℝ := ![5, 10, 30, 40, 15]
    let g : Fin 5 → ℝ := ![10, 10, 30, 45, 5]
    let c : Fin 5 → ℝ := ![10, 20, 50, 95, 100]
    let m : Fin 5 → ℝ := ![54.5, 64.5, 74.5, 84.5, 94.5]
    (∑ i, f i) = 100 ∧ (∑ i, g i) = 100 ∧ (∀ k : Fin 5, ∑ i ∈ univ.filter (· ≤ k), g i = c k) ∧
      (∑ i, f i * m i) / 100 = 79.5 ∧ (∑ i, g i * m i) / 100 = 77 := by
  intro f g c m
  refine ⟨by simp [f, Fin.sum_univ_succ]; norm_num, by simp [g, Fin.sum_univ_succ]; norm_num,
    fun k => ?_, by simp [f, m, Fin.sum_univ_succ]; norm_num,
    by simp [g, m, Fin.sum_univ_succ]; norm_num⟩
  fin_cases k <;> simp [Finset.sum_filter, Fin.sum_univ_succ, g, c, Fin.le_def] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.12 (annual index). The annual consumer price
index of the ten years (184.0, 188.9, 195.3, 201.6, 207.342, 215.303, 214.537, 218.056, 224.939,
229.594) rises every year except the seventh, where it dips from 215.303 to 214.537, the shape the
time series graph shows. -/
@[kb "openstaxintrostats2e" "Example 2.12, p. 95"]
theorem example_2_12_annual_index_rises_except_year_seven :
    let a : Fin 10 → ℝ := ![184.0, 188.9, 195.3, 201.6, 207.342, 215.303, 214.537, 218.056,
      224.939, 229.594]
    (∀ i : Fin 9, i.val ≠ 5 → a i.castSucc < a i.succ) ∧ a 6 < a 5 := by
  intro a
  refine ⟨fun i hi => ?_, by simp [a]; norm_num⟩
  fin_cases i <;> simp [a] at hi ⊢ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.12 (annual value as a monthly mean). The twelve
monthly index values of year 1 average `183.958...`, which the book's annual column reports as 184.0
(within 0.05); for year 10 the monthly mean is within 0.0005 of the reported 229.594. -/
@[kb "openstaxintrostats2e" "Example 2.12, p. 95"]
theorem example_2_12_annual_is_monthly_mean :
    let y1 : Fin 12 → ℝ := ![181.7, 183.1, 184.2, 183.8, 183.5, 183.7, 183.9, 184.6, 185.2, 185.0,
      184.5, 184.3]
    let y10 : Fin 12 → ℝ := ![226.665, 227.663, 229.392, 230.085, 229.815, 229.478, 229.104,
      230.379, 231.407, 231.317, 230.221, 229.601]
    |mean y1 - 184.0| < 0.05 ∧ |mean y10 - 229.594| < 0.0005 := by
  intro y1 y10
  constructor
  · simp [mean, y1, Fin.sum_univ_succ]; rw [abs_lt]; constructor <;> norm_num
  · simp [mean, y10, Fin.sum_univ_succ]; rw [abs_lt]; constructor <;> norm_num

/-- The percentile condition: `q` is a `p`-th percentile of the law of `X` when the probability of
lying strictly below `q` is at most `p` and the probability of lying at or below `q` is at least `p`.
Then at least `p` of the mass is at or below `q` and at least `1 - p` is at or above `q`. -/
private lemma percentile_sides {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) {q p : ℝ}
    (h1 : P.real {ω | X ω < q} ≤ p) (h2 : p ≤ P.real {ω | X ω ≤ q}) :
    p ≤ P.real {ω | X ω ≤ q} ∧ 1 - p ≤ P.real {ω | q ≤ X ω} := by
  refine ⟨h2, ?_⟩
  have hm : MeasurableSet {ω | X ω < q} := measurableSet_lt hX measurable_const
  have e : {ω | q ≤ X ω} = {ω | X ω < q}ᶜ := by ext ω; simp
  rw [e, probReal_compl_eq_one_sub hm]
  linarith

/-- OpenStax Introductory Statistics 2e Example 2.19. If 35 minutes is the first quartile (25th
percentile) of the finishing times `T`, i.e. `P(T < 35) ≤ 1/4 ≤ P(T ≤ 35)`, then at least a quarter
of the students finished in 35 minutes or less and at least three quarters took 35 minutes or more. -/
@[kb "openstaxintrostats2e" "Example 2.19, p. 105"]
theorem example_2_19_first_quartile_interpretation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ} (hT : Measurable T)
    (h1 : P.real {ω | T ω < 35} ≤ 1 / 4) (h2 : 1 / 4 ≤ P.real {ω | T ω ≤ 35}) :
    1 / 4 ≤ P.real {ω | T ω ≤ 35} ∧ 3 / 4 ≤ P.real {ω | 35 ≤ T ω} := by
  have := percentile_sides hT h1 h2
  refine ⟨this.1, by linarith [this.2]⟩

/-- OpenStax Introductory Statistics 2e Example 2.20. If 16 correct answers is the 70th percentile
of the scores `S` on a 20-question test (`P(S < 16) ≤ 0.7 ≤ P(S ≤ 16)`), then at least 70% of the
students answered 16 or fewer questions correctly and at least 30% answered 16 or more correctly. -/
@[kb "openstaxintrostats2e" "Example 2.20, p. 105"]
theorem example_2_20_seventieth_percentile_interpretation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {S : Ω → ℝ} (hS : Measurable S)
    (h1 : P.real {ω | S ω < 16} ≤ 0.7) (h2 : 0.7 ≤ P.real {ω | S ω ≤ 16}) :
    0.7 ≤ P.real {ω | S ω ≤ 16} ∧ 0.3 ≤ P.real {ω | 16 ≤ S ω} := by
  have := percentile_sides hS h1 h2
  refine ⟨this.1, by linarith [this.2]⟩

/-- OpenStax Introductory Statistics 2e Example 2.21. If seven credit units is the 30th percentile
of the unit loads `U` of students (`P(U < 7) ≤ 0.3 ≤ P(U ≤ 7)`), then at least 30% of the students
take seven units or fewer and at least 70% take seven or more. -/
@[kb "openstaxintrostats2e" "Example 2.21, p. 105"]
theorem example_2_21_thirtieth_percentile_interpretation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    (h1 : P.real {ω | U ω < 7} ≤ 0.3) (h2 : 0.3 ≤ P.real {ω | U ω ≤ 7}) :
    0.3 ≤ P.real {ω | U ω ≤ 7} ∧ 0.7 ≤ P.real {ω | 7 ≤ U ω} := by
  have := percentile_sides hU h1 h2
  refine ⟨this.1, by linarith [this.2]⟩

/-- OpenStax Introductory Statistics 2e Example 2.24 (day class). For the 20 sorted scores of the
daytime class: minimum 32, maximum 99, median 74.5, quartiles 56 and 82.5, and the counts behind the
book's percentages: 6 scores are at most 56 (30%), 10 at most 74.5 (50%), 15 at most 82.5 (75%), and
16 scores are at least 56 (75%), 5 at least 82.5 (25%). -/
@[kb "openstaxintrostats2e" "Example 2.24, p. 109"]
theorem example_2_24_day_class_five_numbers :
    let x : Fin 20 → ℝ := ![32, 32, 45, 55.5, 56, 56, 59, 68, 70, 72, 77, 78, 79, 80, 81, 84, 84.5,
      90, 90, 99]
    (x 0 = 32 ∧ x 19 = 99 ∧ ∀ i, 32 ≤ x i ∧ x i ≤ 99) ∧
    median x = 74.5 ∧ median (lowerHalf x 10 (by omega)) = 56 ∧
      median (upperHalf x 10 (by omega)) = 82.5 ∧
    (univ.filter fun i => x i ≤ 56).card = 6 ∧ (univ.filter fun i => x i ≤ 74.5).card = 10 ∧
    (univ.filter fun i => x i ≤ 82.5).card = 15 ∧ (univ.filter fun i => 56 ≤ x i).card = 16 ∧
    (univ.filter fun i => 82.5 ≤ x i).card = 5 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨⟨by simp [x], by simp [x], fun i => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [x] <;> norm_num
  · rw [median_even (m := 9) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 4) _ (lowerHalf_mono hx 10 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 4) _ (upperHalf_mono hx 10 (by omega))]; simp [upperHalf, x] <;> norm_num
  all_goals count_tac

/-- OpenStax Introductory Statistics 2e Example 2.24 (evening class). For the 22 sorted scores of
the evening class: minimum 25.5, maximum 98, median 81, quartiles 78 and 89, the interquartile range
11 is narrower than the day class's 26.5, and the counts are 7 scores at most 78, 12 at most 81, 17 at
most 89, and 17 at least 78, 6 at least 89. -/
@[kb "openstaxintrostats2e" "Example 2.24, p. 109"]
theorem example_2_24_evening_class_five_numbers :
    let x : Fin 22 → ℝ := ![25.5, 45, 65, 68, 76, 78, 78, 79, 79, 80, 81, 81, 83, 84.5, 85, 88, 89,
      90, 90, 98, 98, 98]
    (x 0 = 25.5 ∧ x 21 = 98 ∧ ∀ i, 25.5 ≤ x i ∧ x i ≤ 98) ∧
    median x = 81 ∧ median (lowerHalf x 11 (by omega)) = 78 ∧
      median (upperHalf x 11 (by omega)) = 89 ∧ (89 : ℝ) - 78 < 82.5 - 56 ∧
    (univ.filter fun i => x i ≤ 78).card = 7 ∧ (univ.filter fun i => x i ≤ 81).card = 12 ∧
    (univ.filter fun i => x i ≤ 89).card = 17 ∧ (univ.filter fun i => 78 ≤ x i).card = 17 ∧
    (univ.filter fun i => 89 ≤ x i).card = 6 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨⟨by simp [x], by simp [x], fun i => ?_⟩, ?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [x] <;> norm_num
  · rw [median_even (m := 10) x hx]; simp [x] <;> norm_num
  · rw [median_odd (m := 5) _ (lowerHalf_mono hx 11 (by omega))]; simp [lowerHalf, x]
  · rw [median_odd (m := 5) _ (upperHalf_mono hx 11 (by omega))]; simp [upperHalf, x] <;> norm_num
  all_goals count_tac

/-- OpenStax Introductory Statistics 2e Example 2.28. Twenty exam scores: the mean is 73, the median
is 72, and the unique mode is 72, which occurs 5 times while every other score occurs fewer times. -/
@[kb "openstaxintrostats2e" "Example 2.28, p. 112"]
theorem example_2_28_mean_median_mode :
    let x : Fin 20 → ℝ := ![50, 53, 59, 59, 63, 63, 72, 72, 72, 72, 72, 76, 78, 81, 83, 84, 84, 84,
      90, 93]
    mean x = 73 ∧ median x = 72 ∧ freq x 72 = 5 ∧ ∀ i, x i ≠ 72 → freq x (x i) < 5 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · simp +zetaDelta [mean, Fin.sum_univ_succ]; norm_num
  · rw [median_even (m := 9) x hx]; simp [x]
  · unfold freq; count_tac
  · unfold freq
    rw [Finset.card_filter]
    fin_cases i <;> simp +zetaDelta [Fin.sum_univ_succ, -Finset.sum_boole] at hi ⊢ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.29. The five real-estate exam scores 430, 430, 480,
480, 495 have two modes: 430 and 480 each occur twice, 495 once, so no score occurs more than twice
and the data set is bimodal. -/
@[kb "openstaxintrostats2e" "Example 2.29, p. 113"]
theorem example_2_29_bimodal_scores :
    let x : Fin 5 → ℝ := ![430, 430, 480, 480, 495]
    freq x 430 = 2 ∧ freq x 480 = 2 ∧ freq x 495 = 1 ∧ ∀ i, freq x (x i) ≤ 2 := by
  intro x
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · unfold freq; count_tac
  · unfold freq; count_tac
  · unfold freq; count_tac
  · unfold freq
    rw [Finset.card_filter]
    fin_cases i <;> simp +zetaDelta [Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

end UndergradKB.Statistics.Course.ExamplesC2C5
