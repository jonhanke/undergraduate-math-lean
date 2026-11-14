import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Percentile
import UndergradKB.Statistics.Descriptive

/-!
# Worked examples, chapter 2 (OpenStax *Introductory Statistics 2e*): descriptive statistics

Small theorems with exact answers for data sets of the chapter's worked examples. Data are concrete
vectors `![...] : Fin n → ℝ`; means, variances and z-scores use the repository's definitions
(`UndergradKB.Statistics.mean`, `sampleVariance`, `zScore`, ...), medians use `median`.
-/

namespace UndergradKB.Statistics.Course.ExamplesC2

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

/-- A median of data given in arbitrary order equals the median of its sorted rearrangement. -/
private lemma median_eq_of_perm {n : ℕ} (x y : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hy : Monotone y) (h : ∀ i, y i = x (σ i)) : median x = median y := by
  unfold median
  rw [sortedData_eq_of_perm x y σ hy h, sortedData_eq_self y hy]

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
  hx (Fin.mk_le_mk.2 (by have := Fin.le_def.1 hab; omega))

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

/-- OpenStax Introductory Statistics 2e Example 2.1. Of the 31 first-exam scores of a pre-calculus
class, exactly 8 are at least 90, so the relative frequency of scores in the 90s or 100 is 8/31. -/
@[kb "openstaxintrostats2e" "Example 2.1, p. 78"]
theorem example_2_1_relative_frequency_of_As :
    let x : Fin 31 → ℝ := ![33, 42, 49, 49, 53, 55, 55, 61, 63, 67, 68, 68, 69, 69, 72, 73, 74, 78,
      80, 83, 88, 88, 88, 90, 92, 94, 94, 94, 94, 96, 100]
    ((univ.filter fun i => 90 ≤ x i).card : ℝ) / 31 = 8 / 31 := by
  intro x
  have : (univ.filter fun i => 90 ≤ x i).card = 8 := by
    rw [Finset.card_filter]
    simp [x, Fin.sum_univ_succ, -Finset.sum_boole]
    norm_num
  rw [this]; norm_num


/-- OpenStax Introductory Statistics 2e Example 2.13. Thirteen real-estate prices (in the order
listed, not sorted): the median is 488 800, the quartiles (medians of the lower and upper six
ordered prices) are 308 750 and 649 000, the IQR is 340 250, and with the fences `Q1 - 1.5 IQR` and
`Q3 + 1.5 IQR` the price 5 500 000 is a potential outlier while 1 095 000 is not. -/
@[kb "openstaxintrostats2e" "Example 2.13, p. 99"]
theorem example_2_13_iqr_outliers :
    let x : Fin 13 → ℝ := ![389950, 230500, 158000, 479000, 639000, 114950, 5500000, 387000, 659000,
      529000, 575000, 488800, 1095000]
    let lo : Fin 6 → ℝ := ![114950, 158000, 230500, 387000, 389950, 479000]
    let hi : Fin 6 → ℝ := ![529000, 575000, 639000, 659000, 1095000, 5500000]
    median x = 488800 ∧ median lo = 308750 ∧ median hi = 649000 ∧
      median hi - median lo = 340250 ∧
      (308750 : ℝ) - 1.5 * 340250 = -201625 ∧ (649000 : ℝ) + 1.5 * 340250 = 1159375 ∧
      (1095000 : ℝ) < 1159375 ∧ (1159375 : ℝ) < 5500000 := by
  intro x lo hi
  have hy : Monotone (![114950, 158000, 230500, 387000, 389950, 479000, 488800, 529000, 575000,
      639000, 659000, 1095000, 5500000] : Fin 13 → ℝ) := by
    refine mono_of_succ fun i => ?_
    fin_cases i <;> simp <;> norm_num
  have hlo : Monotone lo := by
    refine mono_of_succ fun i => ?_
    fin_cases i <;> simp [lo] <;> norm_num
  have hhi : Monotone hi := by
    refine mono_of_succ fun i => ?_
    fin_cases i <;> simp [hi] <;> norm_num
  let σ : Fin 13 ≃ Fin 13 := Equiv.ofBijective (![5, 2, 1, 7, 0, 3, 11, 9, 10, 4, 8, 12, 6] :
    Fin 13 → Fin 13) (by decide)
  have h1 : median x = 488800 := by
    rw [median_eq_of_perm x _ σ hy (by intro i; fin_cases i <;> simp [σ, x])]
    have := median_odd (m := 6) _ hy
    rw [this]; simp
  have h2 : median lo = 308750 := by
    rw [median_even (m := 2) lo hlo]; simp [lo]; norm_num
  have h3 : median hi = 649000 := by
    rw [median_even (m := 2) hi hhi]; simp [hi]; norm_num
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (rw [h2, h3]; norm_num) | norm_num

/-- OpenStax Introductory Statistics 2e Example 2.14 (day class). For the 20 scores of the daytime
statistics class (sorted), the median is 74.5, the quartiles are 56 and 82.5, the IQR is 26.5 and
the fences 16.25 and 122.25 enclose the minimum 32 and maximum 99, so there are no outliers. -/
@[kb "openstaxintrostats2e" "Example 2.14, p. 100"]
theorem example_2_14_day_class_iqr :
    let x : Fin 20 → ℝ := ![32, 32, 45, 55.5, 56, 56, 59, 68, 70, 72, 77, 78, 79, 80, 81, 84, 84.5,
      90, 90, 99]
    median x = 74.5 ∧ median (lowerHalf x 10 (by omega)) = 56 ∧
      median (upperHalf x 10 (by omega)) = 82.5 ∧
      (82.5 : ℝ) - 56 = 26.5 ∧ (56 : ℝ) - 1.5 * 26.5 = 16.25 ∧ (82.5 : ℝ) + 1.5 * 26.5 = 122.25 ∧
      (16.25 : ℝ) < 32 ∧ (99 : ℝ) < 122.25 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [median_even (m := 9) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 4) _ (lowerHalf_mono hx 10 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 4) _ (upperHalf_mono hx 10 (by omega))]; simp [upperHalf, x] <;> norm_num
  all_goals norm_num

/-- OpenStax Introductory Statistics 2e Example 2.14 (evening class). For the 22 scores of the
evening class (sorted), the median is 81, the quartiles are 78 and 89, the IQR is 11, and the
fences are 61.5 and 105.5: the scores 25.5 and 45 lie below the lower fence, 98 is below the upper
fence, and 65 is inside (so exactly two low outliers). -/
@[kb "openstaxintrostats2e" "Example 2.14, p. 100"]
theorem example_2_14_evening_class_iqr :
    let x : Fin 22 → ℝ := ![25.5, 45, 65, 68, 76, 78, 78, 79, 79, 80, 81, 81, 83, 84.5, 85, 88, 89,
      90, 90, 98, 98, 98]
    median x = 81 ∧ median (lowerHalf x 11 (by omega)) = 78 ∧
      median (upperHalf x 11 (by omega)) = 89 ∧
      (89 : ℝ) - 78 = 11 ∧ (78 : ℝ) - 1.5 * 11 = 61.5 ∧ (89 : ℝ) + 1.5 * 11 = 105.5 ∧
      (45 : ℝ) < 61.5 ∧ (61.5 : ℝ) < 65 ∧ (98 : ℝ) < 105.5 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [median_even (m := 10) x hx]; simp [x] <;> norm_num
  · rw [median_odd (m := 5) _ (lowerHalf_mono hx 11 (by omega))]; simp [lowerHalf, x]
  · rw [median_odd (m := 5) _ (upperHalf_mono hx 11 (by omega))]; simp [upperHalf, x] <;> norm_num
  all_goals norm_num

/-- OpenStax Introductory Statistics 2e Example 2.15. Fifty students report their nightly hours of
sleep (2 sleep 4 h, 5 sleep 5 h, 7 sleep 6 h, 12 sleep 7 h, 14 sleep 8 h, 7 sleep 9 h, 3 sleep
10 h). The median is 7, the 28th percentile (between the 14th and 15th ordered values) is 6.5 and the
third quartile (the 38th ordered value) is 8. -/
@[kb "openstaxintrostats2e" "Example 2.15, p. 101"]
theorem example_2_15_sleep_percentiles :
    let x : Fin 50 → ℝ := ![4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10]
    median x = 7 ∧ (entry x 14 + entry x 15) / 2 = 6.5 ∧ entry x 38 = 8 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_⟩
  · rw [median_even (m := 24) x hx]; simp [x] <;> norm_num
  · simp [entry, x] <;> norm_num
  · simp [entry, x]

/-- OpenStax Introductory Statistics 2e Example 2.16. For the 29 ages of best actors, the 70th
percentile (index `0.70 · 30 = 21`, an integer) is the 21st value, 64, and the 83rd percentile
(index 24.9) is the average of the 24th and 25th values, 71.5. -/
@[kb "openstaxintrostats2e" "Example 2.16, p. 102"]
theorem example_2_16_percentiles_of_ages :
    let x : Fin 29 → ℝ := ![18, 21, 22, 25, 26, 27, 29, 30, 31, 33, 36, 37, 41, 42, 47, 52, 55, 57,
      58, 62, 64, 67, 69, 71, 72, 73, 74, 76, 77]
    percentileAt x 70 = 64 ∧ percentileAt x 83 = 71.5 := by
  intro x
  have h1 : ⌊(70 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌋₊ = 21 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h2 : ⌈(70 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌉₊ = 21 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  have h3 : ⌊(83 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌋₊ = 24 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h4 : ⌈(83 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌉₊ = 25 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  constructor
  · simp only [percentileAt, h1, h2]; simp [entry, x] <;> norm_num
  · simp only [percentileAt, h3, h4]; simp [entry, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.17. Using the 50 sleep values of Example 2.15 (all
of them, sorted), the 80th percentile is 8.5 (index 40.8), the 90th percentile is 9 (index 45.9)
and the first quartile, the 25th percentile, is 6 (index 12.75). -/
@[kb "openstaxintrostats2e" "Example 2.17, p. 103"]
theorem example_2_17_percentiles_from_frequency_table :
    let x : Fin 50 → ℝ := ![4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10]
    percentileAt x 80 = 8.5 ∧ percentileAt x 90 = 9 ∧ percentileAt x 25 = 6 := by
  intro x
  have h1 : ⌊(80 : ℝ) / 100 * (((50 : ℕ) : ℝ) + 1)⌋₊ = 40 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h2 : ⌈(80 : ℝ) / 100 * (((50 : ℕ) : ℝ) + 1)⌉₊ = 41 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  have h3 : ⌊(90 : ℝ) / 100 * (((50 : ℕ) : ℝ) + 1)⌋₊ = 45 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h4 : ⌈(90 : ℝ) / 100 * (((50 : ℕ) : ℝ) + 1)⌉₊ = 46 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  have h5 : ⌊(25 : ℝ) / 100 * (((50 : ℕ) : ℝ) + 1)⌋₊ = 12 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h6 : ⌈(25 : ℝ) / 100 * (((50 : ℕ) : ℝ) + 1)⌉₊ = 13 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · simp only [percentileAt, h1, h2]; simp [entry, x] <;> norm_num
  · simp only [percentileAt, h3, h4]; simp [entry, x] <;> norm_num
  · simp only [percentileAt, h5, h6]; simp [entry, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.18. In the 29 ages of best actors, 18 values are
below 58 and one equals 58, so the percentile rank of 58 is `(18 + 1/2)/29 · 100 = 1850/29 ≈ 63.8`,
which rounds to 64; 3 values are below 25 and one equals 25, giving `350/29 ≈ 12.07`, rounding to 12. -/
@[kb "openstaxintrostats2e" "Example 2.18, p. 104"]
theorem example_2_18_percentile_rank_of_a_value :
    let x : Fin 29 → ℝ := ![18, 21, 22, 25, 26, 27, 29, 30, 31, 33, 36, 37, 41, 42, 47, 52, 55, 57,
      58, 62, 64, 67, 69, 71, 72, 73, 74, 76, 77]
    ((((univ.filter fun i => x i < 58).card : ℝ) + ((univ.filter fun i => x i = 58).card : ℝ) / 2)
        / 29 * 100 = 1850 / 29 ∧ round ((1850 : ℝ) / 29) = 64) ∧
    ((((univ.filter fun i => x i < 25).card : ℝ) + ((univ.filter fun i => x i = 25).card : ℝ) / 2)
        / 29 * 100 = 350 / 29 ∧ round ((350 : ℝ) / 29) = 12) := by
  intro x
  have a1 : (univ.filter fun i => x i < 58).card = 18 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a2 : (univ.filter fun i => x i = 58).card = 1 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a3 : (univ.filter fun i => x i < 25).card = 3 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a4 : (univ.filter fun i => x i = 25).card = 1 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  rw [a1, a2, a3, a4]
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · rw [round_eq, Int.floor_eq_iff]; norm_num
  · rw [round_eq, Int.floor_eq_iff]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.22. Fifteen students' daily exercise times in
minutes (sorted): minimum 0, first quartile 20, median 40, third quartile 60, maximum 300; the IQR
is 40, the upper fence is 120, and 300 exceeds it (a potential outlier). -/
@[kb "openstaxintrostats2e" "Example 2.22, p. 105"]
theorem example_2_22_exercise_five_number_summary :
    let x : Fin 15 → ℝ := ![0, 0, 10, 20, 30, 30, 30, 40, 45, 60, 60, 60, 90, 120, 300]
    x 0 = 0 ∧ median (lowerHalf x 7 (by omega)) = 20 ∧ median x = 40 ∧
      median (upperHalf x 7 (by omega)) = 60 ∧ x 14 = 300 ∧
      (60 : ℝ) - 20 = 40 ∧ (60 : ℝ) + 1.5 * 40 = 120 ∧ (120 : ℝ) < 300 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], ?_, ?_, ?_, by simp [x], ?_, ?_, ?_⟩
  · rw [median_odd (m := 3) _ (lowerHalf_mono hx 7 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_odd (m := 7) x hx]; simp [x] <;> norm_num
  · rw [median_odd (m := 3) _ (upperHalf_mono hx 7 (by omega))]; simp [upperHalf, x] <;> norm_num
  all_goals norm_num

/-- OpenStax Introductory Statistics 2e Example 2.23. The 40 student heights (sorted) have minimum 59,
maximum 77, median 66 and quartiles 64.5 and 70 (medians of the lower and upper 20 values); hence the
range is 18 and the IQR is 5.5. -/
@[kb "openstaxintrostats2e" "Example 2.23, p. 107"]
theorem example_2_23_heights_box_plot :
    let x : Fin 40 → ℝ := ![59, 60, 61, 62, 62, 63, 63, 64, 64, 64, 65, 65, 65, 65, 65, 65, 65, 65,
      65, 66, 66, 67, 67, 68, 68, 69, 70, 70, 70, 70, 70, 71, 71, 72, 72, 73, 74, 74, 75, 77]
    x 0 = 59 ∧ x 39 = 77 ∧ median (lowerHalf x 20 (by omega)) = 64.5 ∧ median x = 66 ∧
      median (upperHalf x 20 (by omega)) = 70 ∧ (77 : ℝ) - 59 = 18 ∧ (70 : ℝ) - 64.5 = 5.5 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], by simp [x], ?_, ?_, ?_, ?_, ?_⟩
  · rw [median_even (m := 9) _ (lowerHalf_mono hx 20 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 19) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 9) _ (upperHalf_mono hx 20 (by omega))]; simp [upperHalf, x] <;> norm_num
  all_goals norm_num

/-- OpenStax Introductory Statistics 2e Example 2.25. For the 15 values 10, 10, 10, 15, 35, 75, 90,
95, 100, 175, 420, 490, 515, 515, 790 the five numbers of the box-and-whisker plot are minimum 10,
first quartile 15, median 95, third quartile 490 and maximum 790. -/
@[kb "openstaxintrostats2e" "Example 2.25, p. 110"]
theorem example_2_25_five_number_summary :
    let x : Fin 15 → ℝ := ![10, 10, 10, 15, 35, 75, 90, 95, 100, 175, 420, 490, 515, 515, 790]
    x 0 = 10 ∧ median (lowerHalf x 7 (by omega)) = 15 ∧ median x = 95 ∧
      median (upperHalf x 7 (by omega)) = 490 ∧ x 14 = 790 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], ?_, ?_, ?_, by simp [x]⟩
  · rw [median_odd (m := 3) _ (lowerHalf_mono hx 7 (by omega))]; simp [lowerHalf, x]
  · rw [median_odd (m := 7) x hx]; simp [x]
  · rw [median_odd (m := 3) _ (upperHalf_mono hx 7 (by omega))]; simp [upperHalf, x]

/-- OpenStax Introductory Statistics 2e Example 2.26. Ages of 40 emergency-room patients (sorted):
the mean is 943/40 = 23.575 (about 23.6) and the median, the average of the 20th and 21st values
(both 24), is 24. -/
@[kb "openstaxintrostats2e" "Example 2.26, p. 111"]
theorem example_2_26_mean_and_median_of_ages :
    let x : Fin 40 → ℝ := ![3, 4, 8, 8, 10, 11, 12, 13, 14, 15, 15, 16, 16, 17, 17, 18, 21, 22, 22,
      24, 24, 25, 26, 26, 27, 27, 29, 29, 31, 32, 33, 33, 34, 34, 35, 37, 40, 44, 44, 47]
    mean x = 943 / 40 ∧ median x = 24 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_⟩
  · simp [mean, x, Fin.sum_univ_succ]; norm_num
  · rw [median_even (m := 19) x hx]; simp [x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.27. In a town of 50 people one earns 5 000 000 a
year and the other 49 earn 30 000 each: the mean income is 129 400 but the median is 30 000. -/
@[kb "openstaxintrostats2e" "Example 2.27, p. 112"]
theorem example_2_27_mean_versus_median :
    let x : Fin 50 → ℝ := fun i => if (i : ℕ) = 49 then 5000000 else 30000
    mean x = 129400 ∧ median x = 30000 := by
  intro x
  have hx : Monotone x := by
    intro a b hab
    have hab' := Fin.le_def.1 hab
    simp only [x]
    split_ifs with h1 h2 h2 <;> norm_num
    omega
  refine ⟨?_, ?_⟩
  · have hs : ∑ i : Fin 50, x i = 5000000 + 49 * 30000 := by
      rw [Fin.sum_univ_castSucc]
      have h0 : ∀ i : Fin 49, x i.castSucc = 30000 := fun i => by
        simp only [x, Fin.coe_castSucc]
        rw [if_neg (by omega)]
      simp [h0, x]
      norm_num
    simp only [mean, hs]; norm_num
  · rw [median_even (m := 24) x hx]; simp [x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.30. Grouped data: the class midpoints are 53.25,
59.5, 65.5, 71.5, 77.5, 83.5, 89.5, 95.5 with frequencies 1, 0, 4, 4, 2, 3, 4, 1 (19 students), so
the estimated mean is `∑ f m / ∑ f = 1460.25 / 19 = 5841/76`. -/
@[kb "openstaxintrostats2e" "Example 2.30, p. 114"]
theorem example_2_30_grouped_mean :
    let f : Fin 8 → ℝ := ![1, 0, 4, 4, 2, 3, 4, 1]
    let m : Fin 8 → ℝ := ![53.25, 59.5, 65.5, 71.5, 77.5, 83.5, 89.5, 95.5]
    (∑ i, f i) = 19 ∧ (∑ i, f i * m i) = 1460.25 ∧
      (∑ i, f i * m i) / ∑ i, f i = 5841 / 76 := by
  intro f m
  have h1 : (∑ i, f i) = 19 := by simp [f, Fin.sum_univ_succ]; norm_num
  have h2 : (∑ i, f i * m i) = 1460.25 := by simp [f, m, Fin.sum_univ_succ]; norm_num
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.31 (means). Letter counts in ten sampled texts of
three authors: Terry's mean is 3.7, Davis's is 2.7 and Maris's is 4.6. -/
@[kb "openstaxintrostats2e" "Example 2.31, p. 117"]
theorem example_2_31_author_means :
    mean (![7, 9, 3, 3, 3, 4, 1, 3, 2, 2] : Fin 10 → ℝ) = 3.7 ∧
      mean (![3, 3, 3, 4, 1, 4, 3, 2, 3, 1] : Fin 10 → ℝ) = 2.7 ∧
      mean (![2, 3, 4, 4, 4, 6, 6, 6, 8, 3] : Fin 10 → ℝ) = 4.6 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mean, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.31 (medians). The same three letter-count samples,
written in increasing order, have medians 3 (Terry), 3 (Davis) and 4 (Maris). -/
@[kb "openstaxintrostats2e" "Example 2.31, p. 117"]
theorem example_2_31_author_medians :
    median (![1, 2, 2, 3, 3, 3, 3, 4, 7, 9] : Fin 10 → ℝ) = 3 ∧
      median (![1, 1, 2, 3, 3, 3, 3, 3, 4, 4] : Fin 10 → ℝ) = 3 ∧
      median (![2, 3, 3, 4, 4, 4, 6, 6, 6, 8] : Fin 10 → ℝ) = 4 := by
  have h1 : Monotone (![1, 2, 2, 3, 3, 3, 3, 4, 7, 9] : Fin 10 → ℝ) := by mono_tac
  have h2 : Monotone (![1, 1, 2, 3, 3, 3, 3, 3, 4, 4] : Fin 10 → ℝ) := by mono_tac
  have h3 : Monotone (![2, 3, 3, 4, 4, 4, 6, 6, 6, 8] : Fin 10 → ℝ) := by mono_tac
  refine ⟨?_, ?_, ?_⟩
  · rw [median_even (m := 4) _ h1]; simp <;> norm_num
  · rw [median_even (m := 4) _ h2]; simp <;> norm_num
  · rw [median_even (m := 4) _ h3]; simp <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 2.32. Ages of 20 fifth graders (to the nearest half
year): the mean is 10.525, the sum of squared deviations is 9.7375, the sample variance is
9.7375/19, and the sample standard deviation lies between 0.715 and 0.716 (the book rounds it to
0.72). -/
@[kb "openstaxintrostats2e" "Example 2.32, p. 121"]
theorem example_2_32_fifth_graders_sample_sd :
    let x : Fin 20 → ℝ := ![9, 9.5, 9.5, 10, 10, 10, 10, 10.5, 10.5, 10.5, 10.5, 11, 11, 11, 11, 11,
      11, 11.5, 11.5, 11.5]
    mean x = 10.525 ∧ sumSqDev x = 9.7375 ∧ sampleVariance x = 9.7375 / 19 ∧
      0.715 < sampleStdDev x ∧ sampleStdDev x < 0.716 := by
  intro x
  have hm : mean x = 10.525 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hs : sumSqDev x = 9.7375 := by
    simp [sumSqDev, hm, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 9.7375 / 19 := by
    simp only [sampleVariance, hs]; norm_num
  refine ⟨hm, hs, hv, ?_⟩
  exact sd_bounds x (by norm_num) (by norm_num) (by rw [hv]; norm_num) (by rw [hv]; norm_num)

/-- OpenStax Introductory Statistics 2e Example 2.32 (population version). Treating the same 20
ages as an entire population, the population variance is `9.7375/20 = 0.486875`. -/
@[kb "openstaxintrostats2e" "Example 2.32, p. 121"]
theorem example_2_32_fifth_graders_population_variance :
    let x : Fin 20 → ℝ := ![9, 9.5, 9.5, 10, 10, 10, 10, 10.5, 10.5, 10.5, 10.5, 11, 11, 11, 11, 11,
      11, 11.5, 11.5, 11.5]
    populationVariance x = 0.486875 := by
  intro x
  have hm : mean x = 10.525 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  simp [populationVariance, sumSqDev, hm, x, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.33. The 31 first-exam scores of Example 2.1:
the mean is 2279/31 (about 73.5), the sample standard deviation lies in `(17.85, 17.95)` (about
17.9), the median is 73, the quartiles are 61 and 90 (medians of the 15 values below and above the
median) and the IQR is 29. -/
@[kb "openstaxintrostats2e" "Example 2.33, p. 123"]
theorem example_2_33_exam_scores_summary :
    let x : Fin 31 → ℝ := ![33, 42, 49, 49, 53, 55, 55, 61, 63, 67, 68, 68, 69, 69, 72, 73, 74, 78,
      80, 83, 88, 88, 88, 90, 92, 94, 94, 94, 94, 96, 100]
    mean x = 2279 / 31 ∧ (17.85 < sampleStdDev x ∧ sampleStdDev x < 17.95) ∧ median x = 73 ∧
      median (lowerHalf x 15 (by omega)) = 61 ∧ median (upperHalf x 15 (by omega)) = 90 ∧
      (90 : ℝ) - 61 = 29 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · simp [mean, x, Fin.sum_univ_succ]; norm_num
  · refine sd_bounds x (by norm_num) (by norm_num) ?_ ?_
    · simp [sampleVariance, sumSqDev, mean, x, Fin.sum_univ_succ]; norm_num
    · simp [sampleVariance, sumSqDev, mean, x, Fin.sum_univ_succ]; norm_num
  · rw [median_odd (m := 15) x hx]; simp [x]
  · rw [median_odd (m := 7) _ (lowerHalf_mono hx 15 (by omega))]; simp [lowerHalf, x]
  · rw [median_odd (m := 7) _ (upperHalf_mono hx 15 (by omega))]; simp [upperHalf, x]

/-- OpenStax Introductory Statistics 2e Example 2.34. Grouped data with class midpoints 1, 4, 7, 10,
13, 16 and frequencies 1, 6, 10, 7, 0, 2 (26 values): the grouped mean is `197/26` and the
standard deviation `√(∑ f (m - x̄)² / (n - 1))` lies between 3.5 and 3.51. -/
@[kb "openstaxintrostats2e" "Example 2.34, p. 126"]
theorem example_2_34_grouped_standard_deviation :
    let f : Fin 6 → ℝ := ![1, 6, 10, 7, 0, 2]
    let m : Fin 6 → ℝ := ![1, 4, 7, 10, 13, 16]
    (∑ i, f i) = 26 ∧ (∑ i, f i * m i) = 197 ∧
      (3.5 < Real.sqrt ((∑ i, f i * (m i - 197 / 26) ^ 2) / ((∑ i, f i) - 1)) ∧
        Real.sqrt ((∑ i, f i * (m i - 197 / 26) ^ 2) / ((∑ i, f i) - 1)) < 3.51) := by
  intro f m
  have h1 : (∑ i, f i) = 26 := by simp [f, Fin.sum_univ_succ]; norm_num
  have h2 : (∑ i, f i * m i) = 197 := by simp [f, m, Fin.sum_univ_succ]; norm_num
  have h3 : (∑ i, f i * (m i - 197 / 26) ^ 2) / ((∑ i, f i) - 1) =
      (∑ i, f i * (m i - 197 / 26) ^ 2) / 25 := by rw [h1]; norm_num
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h3, Real.lt_sqrt (by norm_num)]
    simp [f, m, Fin.sum_univ_succ]; norm_num
  · rw [h3, Real.sqrt_lt' (by norm_num)]
    simp [f, m, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Example 2.35. John's GPA 2.85 at a school whose GPAs have
mean 3.0 and standard deviation 0.7 has z-score `-3/14` (about -0.21); Ali's score 77 at a school
with mean 80 and standard deviation 10 has z-score `-0.3`. John's is higher. (The school data are
modelled by any three-point list with that mean and standard deviation, `μ - σ, μ, μ + σ`.) -/
@[kb "openstaxintrostats2e" "Example 2.35, p. 129"]
theorem example_2_35_z_score_comparison :
    let john : Fin 3 → ℝ := ![2.3, 3.0, 3.7]
    let ali : Fin 3 → ℝ := ![70, 80, 90]
    mean john = 3 ∧ sampleStdDev john = 0.7 ∧ zScore john 2.85 = -3 / 14 ∧
      mean ali = 80 ∧ sampleStdDev ali = 10 ∧ zScore ali 77 = -0.3 ∧
      zScore ali 77 < zScore john 2.85 := by
  intro john ali
  have hj : mean john = 3 := by simp [mean, john, Fin.sum_univ_succ]; norm_num
  have ha : mean ali = 80 := by simp [mean, ali, Fin.sum_univ_succ]; norm_num
  have sj : sampleStdDev john = 0.7 := by
    have : sampleVariance john = 0.7 ^ 2 := by
      simp [sampleVariance, sumSqDev, hj, john, Fin.sum_univ_succ]; norm_num
    rw [sampleStdDev, this, Real.sqrt_sq (by norm_num)]
  have sa : sampleStdDev ali = 10 := by
    have : sampleVariance ali = 10 ^ 2 := by
      simp [sampleVariance, sumSqDev, ha, ali, Fin.sum_univ_succ]; norm_num
    rw [sampleStdDev, this, Real.sqrt_sq (by norm_num)]
  have zj : zScore john 2.85 = -3 / 14 := by
    simp only [zScore, hj, sj]; norm_num
  have za : zScore ali 77 = -0.3 := by
    simp only [zScore, ha, sa]; norm_num
  refine ⟨hj, sj, zj, ha, sa, za, ?_⟩
  rw [zj, za]; norm_num

end UndergradKB.Statistics.Course.ExamplesC2
