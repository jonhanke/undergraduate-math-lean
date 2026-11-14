import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Percentile
import UndergradKB.Statistics.Descriptive

/-!
# Try It exercises, chapter 2 (OpenStax *Introductory Statistics 2e*): descriptive statistics

Small theorems with exact answers for the data of the chapter's Try It exercises. Data are concrete
vectors `![...] : Fin n → ℝ`; means, variances and z-scores use the repository's definitions
(`UndergradKB.Statistics.mean`, `sampleVariance`, `zScore`, ...), medians use `median`. Exercises that
ask only for a graph are stated through the numbers the graph is built from (class counts, class
widths, cumulative frequencies, five-number summaries).
-/

namespace UndergradKB.Statistics.Course.TryItC2

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

/-- Number of entries of the list in the half-open class `[lo, hi)`. -/
private noncomputable def stemCount {n : ℕ} (x : Fin n → ℝ) (lo hi : ℝ) : ℕ :=
  (univ.filter fun i => lo ≤ x i ∧ x i < hi).card

/-- Evaluate a class count of a concrete list. -/
local macro "count_tac" : tactic =>
  `(tactic| (rw [Finset.card_filter]; simp +zetaDelta [Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num))

/-- OpenStax Introductory Statistics 2e Try It 2.1. The 30 Park City basketball scores (sorted) fall
into the stems 3, 4, 5, 6 with 5, 12, 11 and 2 leaves respectively. -/
@[kb "openstaxintrostats2e" "Try It 2.1, p. 79"]
theorem tryit_2_1_stem_counts :
    let x : Fin 30 → ℝ := ![32, 32, 33, 34, 38, 40, 42, 42, 43, 44, 46, 47, 47, 48, 48, 48, 49, 50,
      50, 51, 52, 52, 52, 53, 54, 56, 57, 57, 60, 61]
    stemCount x 30 40 = 5 ∧ stemCount x 40 50 = 12 ∧ stemCount x 50 60 = 11 ∧
      stemCount x 60 70 = 2 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Try It 2.2 (stem counts). The 30 distances in miles have
2, 11, 7, 2, 3, 4 values with integer part 0 to 5 and one value (8.0) with integer part 8, none
with 6 or 7. -/
@[kb "openstaxintrostats2e" "Try It 2.2, p. 80"]
theorem tryit_2_2_stem_counts :
    let x : Fin 30 → ℝ := ![0.5, 0.7, 1.1, 1.2, 1.2, 1.3, 1.3, 1.5, 1.5, 1.7, 1.7, 1.8, 1.9, 2.0,
      2.2, 2.5, 2.6, 2.8, 2.8, 2.8, 3.5, 3.8, 4.4, 4.8, 4.9, 5.2, 5.5, 5.7, 5.8, 8.0]
    stemCount x 0 1 = 2 ∧ stemCount x 1 2 = 11 ∧ stemCount x 2 3 = 7 ∧ stemCount x 3 4 = 2 ∧
      stemCount x 4 5 = 3 ∧ stemCount x 5 6 = 4 ∧ stemCount x 6 8 = 0 ∧ stemCount x 8 9 = 1 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Try It 2.2 (outliers). For the same distances: median 2.35,
quartiles 1.5 and 4.4 (medians of the lower and upper 15 values), IQR 2.9. The upper fence
`4.4 + 1.5 · 2.9 = 8.75` is above the largest distance 8.0, and the lower fence `-2.85` is below the
smallest, 0.5, so by the 1.5 IQR rule the value 8.0 is the isolated large value but not a flagged
outlier. -/
@[kb "openstaxintrostats2e" "Try It 2.2, p. 80"]
theorem tryit_2_2_iqr_fences :
    let x : Fin 30 → ℝ := ![0.5, 0.7, 1.1, 1.2, 1.2, 1.3, 1.3, 1.5, 1.5, 1.7, 1.7, 1.8, 1.9, 2.0,
      2.2, 2.5, 2.6, 2.8, 2.8, 2.8, 3.5, 3.8, 4.4, 4.8, 4.9, 5.2, 5.5, 5.7, 5.8, 8.0]
    median x = 2.35 ∧ median (lowerHalf x 15 (by omega)) = 1.5 ∧
      median (upperHalf x 15 (by omega)) = 4.4 ∧ (4.4 : ℝ) - 1.5 = 2.9 ∧
      (1.5 : ℝ) - 1.5 * 2.9 = -2.85 ∧ (4.4 : ℝ) + 1.5 * 2.9 = 8.75 ∧
      (-2.85 : ℝ) < x 0 ∧ x 29 < 8.75 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · rw [median_even (m := 14) x hx]; simp [x] <;> norm_num
  · rw [median_odd (m := 7) _ (lowerHalf_mono hx 15 (by omega))]; simp [lowerHalf, x]
  · rw [median_odd (m := 7) _ (upperHalf_mono hx 15 (by omega))]; simp [upperHalf, x]
  · simp [x]; norm_num
  · simp [x]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.3 (losses). The 42 season losses of the Atlanta
Hawks, grouped by tens digit 1 to 6, have 1, 4, 14, 13, 9, 1 values. -/
@[kb "openstaxintrostats2e" "Try It 2.3, p. 82"]
theorem tryit_2_3_losses_stem_counts :
    let x : Fin 42 → ℝ := ![34, 34, 46, 46, 36, 47, 51, 53, 51, 41, 36, 32, 51, 40, 39, 42, 48, 32,
      25, 32, 30, 41, 39, 44, 39, 25, 40, 36, 26, 32, 19, 54, 57, 49, 47, 54, 69, 56, 52, 45, 35, 29]
    stemCount x 10 20 = 1 ∧ stemCount x 20 30 = 4 ∧ stemCount x 30 40 = 14 ∧
      stemCount x 40 50 = 13 ∧ stemCount x 50 60 = 9 ∧ stemCount x 60 70 = 1 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Try It 2.3 (wins). The 42 season win totals, grouped by tens
digit 1 to 6, have 1, 5, 13, 14, 9, 0 values. -/
@[kb "openstaxintrostats2e" "Try It 2.3, p. 82"]
theorem tryit_2_3_wins_stem_counts :
    let x : Fin 42 → ℝ := ![48, 48, 36, 36, 46, 35, 31, 29, 31, 41, 46, 50, 31, 42, 43, 40, 34, 50,
      57, 50, 52, 41, 43, 38, 43, 57, 42, 46, 56, 50, 31, 28, 25, 33, 35, 28, 13, 26, 30, 37, 47, 53]
    stemCount x 10 20 = 1 ∧ stemCount x 20 30 = 5 ∧ stemCount x 30 40 = 13 ∧
      stemCount x 40 50 = 14 ∧ stemCount x 50 60 = 9 ∧ stemCount x 60 70 = 0 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Try It 2.4. The frequencies 7, 10, 14, 9 of 0, 1, 2, 3
repair visits add up to the 40 people surveyed; the points of the line graph are the relative
frequencies `f/40`, and the mean number of visits is `65/40 = 13/8`. -/
@[kb "openstaxintrostats2e" "Try It 2.4, p. 84"]
theorem tryit_2_4_repair_frequencies :
    let f : Fin 4 → ℝ := ![7, 10, 14, 9]
    let k : Fin 4 → ℝ := ![0, 1, 2, 3]
    (∑ i, f i) = 40 ∧ (∑ i, f i * k i) = 65 ∧ (∑ i, f i * k i) / ∑ i, f i = 13 / 8 := by
  intro f k
  have h1 : (∑ i, f i) = 40 := by simp [f, Fin.sum_univ_succ]; norm_num
  have h2 : (∑ i, f i * k i) = 65 := by simp [f, k, Fin.sum_univ_succ]; norm_num
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.5. The three Park City age groups have 67 059,
152 198 and 131 662 people, 350 919 in all; their shares of the total round to 19, 43 and 38
percent, as printed, and these percentages add to 100. -/
@[kb "openstaxintrostats2e" "Try It 2.5, p. 85"]
theorem tryit_2_5_age_group_proportions :
    (67059 : ℝ) + 152198 + 131662 = 350919 ∧
      round ((67059 : ℝ) / 350919 * 100) = 19 ∧ round ((152198 : ℝ) / 350919 * 100) = 43 ∧
      round ((131662 : ℝ) / 350919 * 100) = 38 ∧ (19 : ℤ) + 43 + 38 = 100 := by
  refine ⟨by norm_num, ?_, ?_, ?_, by norm_num⟩ <;> (rw [round_eq, Int.floor_eq_iff]; norm_num)

/-- OpenStax Introductory Statistics 2e Try It 2.6. In each of the two columns of percentages of
the six voting districts (registered voters, and overall population) the six values add to 100;
district 5 has the largest share of registered voters (22.8%). -/
@[kb "openstaxintrostats2e" "Try It 2.6, p. 86"]
theorem tryit_2_6_district_percentages :
    let reg : Fin 6 → ℝ := ![15.5, 12.2, 9.8, 17.4, 22.8, 22.3]
    let pop : Fin 6 → ℝ := ![19.4, 15.6, 9.0, 18.5, 20.7, 16.8]
    (∑ i, reg i) = 100 ∧ (∑ i, pop i) = 100 ∧ (∀ i, reg i ≤ reg 4) := by
  intro reg pop
  refine ⟨by simp [reg, Fin.sum_univ_succ]; norm_num, by simp [pop, Fin.sum_univ_succ]; norm_num, ?_⟩
  intro i
  fin_cases i <;> simp [reg] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.7. For the 50 shoe sizes, the smallest is 9 and
the largest 14, so with the starting point `9 - 0.05 = 8.95` and ending value `14 + 0.05 = 14.05`
the six bars have raw width `(14.05 - 8.95)/6 = 0.85`; rounding up to width 1 gives the class
boundaries 8.95, 9.95, ..., 14.95 (none contains a data value), with counts 4, 14, 20, 11, 0, 1. -/
@[kb "openstaxintrostats2e" "Try It 2.7, p. 89"]
theorem tryit_2_7_shoe_size_histogram :
    let x : Fin 50 → ℝ := ![9, 9, 9.5, 9.5, 10, 10, 10, 10, 10, 10, 10.5, 10.5, 10.5, 10.5, 10.5,
      10.5, 10.5, 10.5, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11.5, 11.5, 11.5, 11.5,
      11.5, 11.5, 11.5, 12, 12, 12, 12, 12, 12, 12, 12.5, 12.5, 12.5, 12.5, 14]
    (14.05 - 8.95) / 6 = (0.85 : ℝ) ∧ stemCount x 8.95 9.95 = 4 ∧ stemCount x 9.95 10.95 = 14 ∧
      stemCount x 10.95 11.95 = 20 ∧ stemCount x 11.95 12.95 = 11 ∧
      stemCount x 12.95 13.95 = 0 ∧ stemCount x 13.95 14.95 = 1 := by
  intro x
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Try It 2.8. For the numbers of sports (frequencies 20, 22,
8 of the values 1, 2, 3, so 50 athletes) with starting point 0.5 and width 1, the class boundaries
are 0.5, 1.5, 2.5, 3.5: the blanks are `0.5 + 1 = 1.5`, then 1.5 to 2.5 and 2.5 to 3.5, and the
number of bars is `(3.5 - 0.5)/1 = 3`. -/
@[kb "openstaxintrostats2e" "Try It 2.8, p. 90"]
theorem tryit_2_8_sports_intervals :
    let f : Fin 3 → ℝ := ![20, 22, 8]
    (∑ i, f i) = 50 ∧ (0.5 : ℝ) + 1 = 1.5 ∧ (1.5 : ℝ) + 1 = 2.5 ∧ (2.5 : ℝ) + 1 = 3.5 ∧
      ((3.5 : ℝ) - 0.5) / 1 = 3 := by
  intro f
  refine ⟨by simp [f, Fin.sum_univ_succ]; norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 2.9. The 22 restaurant staff counts, in the classes
10-19, 20-29, 30-39, 40-49 (as `[10,20)`, ...), have 3, 11, 5, 3 values. -/
@[kb "openstaxintrostats2e" "Try It 2.9, p. 91"]
theorem tryit_2_9_employee_histogram :
    let x : Fin 22 → ℝ := ![22, 35, 15, 26, 40, 28, 18, 20, 25, 34, 39, 42, 24, 22, 19, 27, 22, 34,
      40, 20, 38, 28]
    stemCount x 10 20 = 3 ∧ stemCount x 20 30 = 11 ∧ stemCount x 30 40 = 5 ∧
      stemCount x 40 50 = 3 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold stemCount; count_tac)

/-- OpenStax Introductory Statistics 2e Try It 2.10. The class boundaries 41.5, 46.5, ..., 71.5 of
the presidents' inauguration ages have midpoints 44, 49, 54, 59, 64, 69 (the plotted points of the
polygon); the frequencies 4, 11, 14, 9, 4, 2 add to 44 presidents, and the grouped estimate of the
mean age is `2396/44 = 599/11`. -/
@[kb "openstaxintrostats2e" "Try It 2.10, p. 93"]
theorem tryit_2_10_presidents_frequency_polygon :
    let lo : Fin 6 → ℝ := ![41.5, 46.5, 51.5, 56.5, 61.5, 66.5]
    let hi : Fin 6 → ℝ := ![46.5, 51.5, 56.5, 61.5, 66.5, 71.5]
    let m : Fin 6 → ℝ := ![44, 49, 54, 59, 64, 69]
    let f : Fin 6 → ℝ := ![4, 11, 14, 9, 4, 2]
    (∀ i, (lo i + hi i) / 2 = m i) ∧ (∑ i, f i) = 44 ∧ (∑ i, f i * m i) = 2396 ∧
      (∑ i, f i * m i) / ∑ i, f i = 599 / 11 := by
  intro lo hi m f
  have h1 : (∑ i, f i) = 44 := by simp [f, Fin.sum_univ_succ]; norm_num
  have h2 : (∑ i, f i * m i) = 2396 := by simp [f, m, Fin.sum_univ_succ]; norm_num
  refine ⟨?_, h1, h2, ?_⟩
  · intro i; fin_cases i <;> simp [lo, hi, m] <;> norm_num
  · rw [h1, h2]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.11. For the 100 algebra final test scores with
class frequencies 10, 5, 40, 35, 10, the cumulative frequencies printed in the table are 10, 15, 55,
90, 100 (each is the sum of the frequencies of its class and the earlier ones), and the modal class
is 69.5-79.5. -/
@[kb "openstaxintrostats2e" "Try It 2.11, p. 94"]
theorem tryit_2_11_algebra_cumulative_frequencies :
    let f : Fin 5 → ℝ := ![10, 5, 40, 35, 10]
    let c : Fin 5 → ℝ := ![10, 15, 55, 90, 100]
    (∀ k, ∑ i ∈ univ.filter (· ≤ k), f i = c k) ∧ (∀ i, f i ≤ f 2) := by
  intro f c
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k <;> simp [f, c, Finset.sum_filter, Fin.sum_univ_succ] <;> norm_num
  · intro i; fin_cases i <;> simp [f] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.12. The seven yearly CO2 emission figures of the
United States: the largest is in year 5 and the smallest in year 7, and the drop from year 6 to
year 7 is 357 276. -/
@[kb "openstaxintrostats2e" "Try It 2.12, p. 97"]
theorem tryit_2_12_us_emissions_series :
    let x : Fin 7 → ℝ := ![5681664, 5790761, 5826394, 5737615, 5828697, 5656839, 5299563]
    (∀ i, x i ≤ x 4) ∧ (∀ i, x 6 ≤ x i) ∧ x 6 - x 5 = -357276 := by
  intro x
  refine ⟨?_, ?_, by simp [x]; norm_num⟩ <;> (intro i; fin_cases i <;> simp [x] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Try It 2.13. Eleven salaries (in the order listed): the
median is 54 000, the quartiles (medians of the lower and upper five ordered salaries) are 40 500 and
69 000, the IQR is 28 500, and with the fences `-2250` and `111 750` the salary 120 000 is a
potential outlier while 28 000 is not. -/
@[kb "openstaxintrostats2e" "Try It 2.13, p. 100"]
theorem tryit_2_13_salaries_iqr_outliers :
    let x : Fin 11 → ℝ := ![33000, 64500, 28000, 54000, 72000, 68500, 69000, 42000, 54000, 120000,
      40500]
    let lo : Fin 5 → ℝ := ![28000, 33000, 40500, 42000, 54000]
    let hi : Fin 5 → ℝ := ![64500, 68500, 69000, 72000, 120000]
    median x = 54000 ∧ median lo = 40500 ∧ median hi = 69000 ∧ median hi - median lo = 28500 ∧
      (40500 : ℝ) - 1.5 * 28500 = -2250 ∧ (69000 : ℝ) + 1.5 * 28500 = 111750 ∧
      (-2250 : ℝ) < 28000 ∧ (111750 : ℝ) < 120000 := by
  intro x lo hi
  have hy : Monotone (![28000, 33000, 40500, 42000, 54000, 54000, 64500, 68500, 69000, 72000,
      120000] : Fin 11 → ℝ) := by
    refine mono_of_succ fun i => ?_
    fin_cases i <;> simp <;> norm_num
  have hlo : Monotone lo := by
    refine mono_of_succ fun i => ?_
    fin_cases i <;> simp [lo] <;> norm_num
  have hhi : Monotone hi := by
    refine mono_of_succ fun i => ?_
    fin_cases i <;> simp [hi] <;> norm_num
  let σ : Fin 11 ≃ Fin 11 := Equiv.ofBijective (![2, 0, 10, 7, 3, 8, 1, 5, 6, 4, 9] :
    Fin 11 → Fin 11) (by decide)
  have h1 : median x = 54000 := by
    rw [median_eq_of_perm x _ σ hy (by intro i; fin_cases i <;> simp [σ, x])]
    have := median_odd (m := 5) _ hy
    rw [this]; simp
  have h2 : median lo = 40500 := by
    rw [median_odd (m := 2) lo hlo]; simp [lo]
  have h3 : median hi = 69000 := by
    rw [median_odd (m := 2) hi hhi]; simp [hi]
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_, ?_⟩ <;> first | (rw [h2, h3]; norm_num) | norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.14 (Class A). For the 20 scores of class A (sorted)
the median is 80.5, the quartiles are 72.5 and 90.5 and the IQR is 18. -/
@[kb "openstaxintrostats2e" "Try It 2.14, p. 100"]
theorem tryit_2_14_class_A_iqr :
    let x : Fin 20 → ℝ := ![65, 66, 67, 69, 69, 76, 77, 77, 79, 80, 81, 83, 85, 89, 90, 91, 94, 96,
      98, 99]
    median x = 80.5 ∧ median (lowerHalf x 10 (by omega)) = 72.5 ∧
      median (upperHalf x 10 (by omega)) = 90.5 ∧ (90.5 : ℝ) - 72.5 = 18 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · rw [median_even (m := 9) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 4) _ (lowerHalf_mono hx 10 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 4) _ (upperHalf_mono hx 10 (by omega))]; simp [upperHalf, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.14 (Class B). For the 20 scores of class B (sorted)
the median is 80, the quartiles are 72.5 and 93.5, the IQR is 21, which exceeds class A's IQR of 18,
so class B has the wider middle half. -/
@[kb "openstaxintrostats2e" "Try It 2.14, p. 100"]
theorem tryit_2_14_class_B_iqr :
    let x : Fin 20 → ℝ := ![68, 68, 70, 71, 72, 73, 75, 78, 79, 80, 80, 90, 90, 92, 92, 95, 95, 97,
      99, 100]
    median x = 80 ∧ median (lowerHalf x 10 (by omega)) = 72.5 ∧
      median (upperHalf x 10 (by omega)) = 93.5 ∧ (93.5 : ℝ) - 72.5 = 21 ∧
      (90.5 : ℝ) - 72.5 < 93.5 - 72.5 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩
  · rw [median_even (m := 9) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 4) _ (lowerHalf_mono hx 10 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 4) _ (upperHalf_mono hx 10 (by omega))]; simp [upperHalf, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.15. For the 40 bus drivers (12 spend 2 hours, 14
spend 3, 10 spend 4, 4 spend 5), the index of the 65th percentile is `0.65 · 41 = 26.65`, so it is
the average of the 26th and 27th ordered values, 3 and 4: the 65th percentile is 3.5. -/
@[kb "openstaxintrostats2e" "Try It 2.15, p. 101"]
theorem tryit_2_15_bus_route_percentile :
    let x : Fin 40 → ℝ := ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5]
    percentileAt x 65 = 3.5 := by
  intro x
  have h1 : ⌊(65 : ℝ) / 100 * (((40 : ℕ) : ℝ) + 1)⌋₊ = 26 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h2 : ⌈(65 : ℝ) / 100 * (((40 : ℕ) : ℝ) + 1)⌉₊ = 27 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  simp only [percentileAt, h1, h2]; simp [entry, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.16. For the 29 ages of best actors, the 20th
percentile has index `0.20 · 30 = 6` (an integer), so it is the 6th value, 27, and the 55th
percentile has index 16.5, so it is the average of the 16th and 17th values, 52 and 55: 53.5. -/
@[kb "openstaxintrostats2e" "Try It 2.16, p. 102"]
theorem tryit_2_16_percentiles_of_ages :
    let x : Fin 29 → ℝ := ![18, 21, 22, 25, 26, 27, 29, 30, 31, 33, 36, 37, 41, 42, 47, 52, 55, 57,
      58, 62, 64, 67, 69, 71, 72, 73, 74, 76, 77]
    percentileAt x 20 = 27 ∧ percentileAt x 55 = 53.5 := by
  intro x
  have h1 : ⌊(20 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌋₊ = 6 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h2 : ⌈(20 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌉₊ = 6 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  have h3 : ⌊(55 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌋₊ = 16 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h4 : ⌈(55 : ℝ) / 100 * (((29 : ℕ) : ℝ) + 1)⌉₊ = 17 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  constructor
  · simp only [percentileAt, h1, h2]; simp [entry, x] <;> norm_num
  · simp only [percentileAt, h3, h4]; simp [entry, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.17. For the 40 bus drivers of Try It 2.15, the third
quartile, which is another name for the 75th percentile, has index `0.75 · 41 = 30.75`, so it is the
average of the 30th and 31st ordered values, both 4: the third quartile is 4. -/
@[kb "openstaxintrostats2e" "Try It 2.17, p. 103"]
theorem tryit_2_17_bus_route_third_quartile :
    let x : Fin 40 → ℝ := ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5]
    percentileAt x 75 = 4 := by
  intro x
  have h1 : ⌊(75 : ℝ) / 100 * (((40 : ℕ) : ℝ) + 1)⌋₊ = 30 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have h2 : ⌈(75 : ℝ) / 100 * (((40 : ℕ) : ℝ) + 1)⌉₊ = 31 := by
    rw [Nat.ceil_eq_iff (by norm_num)]; norm_num
  simp only [percentileAt, h1, h2]; simp [entry, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.18. In the list of 30 ages of best actors, 15 values
are below 47 and one equals it, so the percentile rank of 47 is `(15 + 1/2)/30 · 100 = 155/3 ≈ 51.7`,
which rounds to 52; 8 values are below 31 and two equal it, giving `(8 + 1)/30 · 100 = 30`. -/
@[kb "openstaxintrostats2e" "Try It 2.18, p. 104"]
theorem tryit_2_18_percentile_ranks :
    let x : Fin 30 → ℝ := ![18, 21, 22, 25, 26, 27, 29, 30, 31, 31, 33, 36, 37, 41, 42, 47, 52, 55,
      57, 58, 62, 64, 67, 69, 71, 72, 73, 74, 76, 77]
    ((((univ.filter fun i => x i < 47).card : ℝ) + ((univ.filter fun i => x i = 47).card : ℝ) / 2)
        / 30 * 100 = 155 / 3 ∧ round ((155 : ℝ) / 3) = 52) ∧
    ((((univ.filter fun i => x i < 31).card : ℝ) + ((univ.filter fun i => x i = 31).card : ℝ) / 2)
        / 30 * 100 = 30) := by
  intro x
  have a1 : (univ.filter fun i => x i < 47).card = 15 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a2 : (univ.filter fun i => x i = 47).card = 1 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a3 : (univ.filter fun i => x i < 31).card = 8 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  have a4 : (univ.filter fun i => x i = 31).card = 2 := by
    rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num
  rw [a1, a2, a3, a4]
  refine ⟨⟨by norm_num, ?_⟩, by norm_num⟩
  rw [round_eq, Int.floor_eq_iff]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.22. For the 10 project times (sorted: 2, 2, 3, 3,
3, 3, 4, 4, 5, 11 hours): minimum 2, first quartile 3, median 3, third quartile 4, maximum 11; the
IQR is 1 and the upper fence is 5.5, so 11 is a potential outlier. The mean is 4. -/
@[kb "openstaxintrostats2e" "Try It 2.22, p. 106"]
theorem tryit_2_22_project_hours_five_numbers :
    let x : Fin 10 → ℝ := ![2, 2, 3, 3, 3, 3, 4, 4, 5, 11]
    x 0 = 2 ∧ median (lowerHalf x 5 (by omega)) = 3 ∧ median x = 3 ∧
      median (upperHalf x 5 (by omega)) = 4 ∧ x 9 = 11 ∧ (4 : ℝ) - 3 = 1 ∧
      (4 : ℝ) + 1.5 * 1 = 5.5 ∧ (5.5 : ℝ) < 11 ∧ mean x = 4 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], ?_, ?_, ?_, by simp [x], by norm_num, by norm_num, by norm_num, ?_⟩
  · rw [median_odd (m := 2) _ (lowerHalf_mono hx 5 (by omega))]; simp [lowerHalf, x]
  · rw [median_even (m := 4) x hx]; simp [x] <;> norm_num
  · rw [median_odd (m := 2) _ (upperHalf_mono hx 5 (by omega))]; simp [upperHalf, x]
  · simp [mean, x, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.23. The page counts of the 40 books (sorted): the
smallest is 136 and the largest 512, the median is 322, the quartiles are 237 and 395 (medians of the
lower and upper 20 values) and the interquartile range is 158. -/
@[kb "openstaxintrostats2e" "Try It 2.23, p. 108"]
theorem tryit_2_23_book_pages_box_plot :
    let x : Fin 40 → ℝ := ![136, 140, 178, 190, 205, 215, 217, 218, 232, 234, 240, 255, 270, 275, 290,
      301, 303, 315, 317, 318, 326, 333, 343, 349, 360, 369, 377, 388, 391, 392, 398, 400, 402, 405,
      408, 422, 429, 450, 475, 512]
    x 0 = 136 ∧ x 39 = 512 ∧ median (lowerHalf x 20 (by omega)) = 237 ∧ median x = 322 ∧
      median (upperHalf x 20 (by omega)) = 395 ∧ (395 : ℝ) - 237 = 158 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], by simp [x], ?_, ?_, ?_, by norm_num⟩
  · rw [median_even (m := 9) _ (lowerHalf_mono hx 20 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 19) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 9) _ (upperHalf_mono hx 20 (by omega))]; simp [upperHalf, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.24 (boys). Heights of the 20 boys (sorted): minimum
66, maximum 74, median 69, quartiles 68 and 72, IQR 4. -/
@[kb "openstaxintrostats2e" "Try It 2.24, p. 110"]
theorem tryit_2_24_boys_heights_box_plot :
    let x : Fin 20 → ℝ := ![66, 66, 67, 67, 68, 68, 68, 68, 68, 69, 69, 69, 70, 71, 72, 72, 72, 73,
      73, 74]
    x 0 = 66 ∧ median (lowerHalf x 10 (by omega)) = 68 ∧ median x = 69 ∧
      median (upperHalf x 10 (by omega)) = 72 ∧ x 19 = 74 ∧ (72 : ℝ) - 68 = 4 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], ?_, ?_, ?_, by simp [x], by norm_num⟩
  · rw [median_even (m := 4) _ (lowerHalf_mono hx 10 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 9) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 4) _ (upperHalf_mono hx 10 (by omega))]; simp [upperHalf, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.24 (girls). Heights of the 20 girls (sorted):
minimum 61, maximum 69, median 65.5, quartiles 63 and 68, IQR 5, which exceeds the boys' IQR of 4:
the girls' box is wider. -/
@[kb "openstaxintrostats2e" "Try It 2.24, p. 110"]
theorem tryit_2_24_girls_heights_box_plot :
    let x : Fin 20 → ℝ := ![61, 61, 62, 62, 63, 63, 63, 65, 65, 65, 66, 66, 66, 67, 68, 68, 68, 69,
      69, 69]
    x 0 = 61 ∧ median (lowerHalf x 10 (by omega)) = 63 ∧ median x = 65.5 ∧
      median (upperHalf x 10 (by omega)) = 68 ∧ x 19 = 69 ∧ (68 : ℝ) - 63 = 5 ∧
      (72 : ℝ) - 68 < 68 - 63 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], ?_, ?_, ?_, by simp [x], by norm_num, by norm_num⟩
  · rw [median_even (m := 4) _ (lowerHalf_mono hx 10 (by omega))]; simp [lowerHalf, x] <;> norm_num
  · rw [median_even (m := 9) x hx]; simp [x] <;> norm_num
  · rw [median_even (m := 4) _ (upperHalf_mono hx 10 (by omega))]; simp [upperHalf, x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.25. For the 15 values 0, 5, 5, 15, 30, 30, 45, 50,
50, 60, 75, 110, 140, 240, 330 the five numbers of the box-and-whisker plot are minimum 0, first
quartile 15, median 50, third quartile 110 and maximum 330. The IQR is 95, the upper fence is
252.5, and 330 exceeds it while 240 does not. -/
@[kb "openstaxintrostats2e" "Try It 2.25, p. 110"]
theorem tryit_2_25_five_number_summary :
    let x : Fin 15 → ℝ := ![0, 5, 5, 15, 30, 30, 45, 50, 50, 60, 75, 110, 140, 240, 330]
    x 0 = 0 ∧ median (lowerHalf x 7 (by omega)) = 15 ∧ median x = 50 ∧
      median (upperHalf x 7 (by omega)) = 110 ∧ x 14 = 330 ∧ (110 : ℝ) - 15 = 95 ∧
      (110 : ℝ) + 1.5 * 95 = 252.5 ∧ x 13 < 252.5 ∧ (252.5 : ℝ) < x 14 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨by simp [x], ?_, ?_, ?_, by simp [x], by norm_num, by norm_num, ?_, ?_⟩
  · rw [median_odd (m := 3) _ (lowerHalf_mono hx 7 (by omega))]; simp [lowerHalf, x]
  · rw [median_odd (m := 7) x hx]; simp [x]
  · rw [median_odd (m := 3) _ (upperHalf_mono hx 7 (by omega))]; simp [upperHalf, x]
  · simp [x] <;> norm_num
  · simp [x] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.26. Months on a transplant list for 39 patients
(sorted): the mean is `544/39` (about 13.9) and the median, the 20th value, is 13. -/
@[kb "openstaxintrostats2e" "Try It 2.26, p. 112"]
theorem tryit_2_26_transplant_wait_mean_median :
    let x : Fin 39 → ℝ := ![3, 4, 5, 7, 7, 7, 7, 8, 8, 9, 9, 10, 10, 10, 10, 10, 11, 12, 12, 13, 14,
      14, 15, 15, 17, 17, 18, 19, 19, 19, 21, 21, 22, 22, 23, 24, 24, 24, 24]
    mean x = 544 / 39 ∧ median x = 13 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_⟩
  · simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  · rw [median_odd (m := 19) x hx]; simp [x]

/-- OpenStax Introductory Statistics 2e Try It 2.27. Of 60 houses, one is worth 2 500 000, 29 are
worth 280 000 and 30 are worth 315 000. The mean is 334 500 and exceeds 59 of the 60 values, while the
median is 315 000, a typical value: the median is the better measure of the center. -/
@[kb "openstaxintrostats2e" "Try It 2.27, p. 112"]
theorem tryit_2_27_house_values_mean_vs_median :
    let x : Fin 60 → ℝ := ![280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000,
      280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000,
      280000, 280000, 280000, 280000, 280000, 280000, 280000, 280000, 315000, 315000, 315000, 315000,
      315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000,
      315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000, 315000,
      315000, 315000, 2500000]
    mean x = 334500 ∧ median x = 315000 ∧ (univ.filter fun i => x i < 334500).card = 59 := by
  intro x
  have hx : Monotone x := by mono_tac
  refine ⟨?_, ?_, ?_⟩
  · simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  · rw [median_even (m := 29) x hx]; simp [x] <;> norm_num
  · rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.28. In the 25 library-book counts the value 7
occurs four times and every other value occurs fewer than four times, so the mode is 7. -/
@[kb "openstaxintrostats2e" "Try It 2.28, p. 113"]
theorem tryit_2_28_library_books_mode :
    let x : Fin 25 → ℝ := ![0, 0, 0, 1, 2, 3, 3, 4, 4, 5, 5, 7, 7, 7, 7, 8, 8, 8, 9, 10, 10, 11, 11,
      12, 12]
    (univ.filter fun i => x i = 7).card = 4 ∧
      ∀ v : ℝ, v ≠ 7 → (univ.filter fun i => x i = v).card < 4 := by
  intro x
  refine ⟨by rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num, ?_⟩
  intro v hv
  by_cases h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨
      v = 11 ∨ v = 12
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hv
      | (rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num)
  · have : (univ.filter fun i => x i = v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      fin_cases i <;> simp [x] <;> intro hh <;> exact h (by subst hh; norm_num)
    rw [this]; simp

/-- OpenStax Introductory Statistics 2e Try It 2.29. In the credit scores 680, 680, 700, 720, 720
the values 680 and 720 each occur twice and 700 once, so the data are bimodal with modes 680 and 720.
(The second part, which measure of center suits the factory earnings, is a verbal judgement and is
not formalized.) -/
@[kb "openstaxintrostats2e" "Try It 2.29, p. 113"]
theorem tryit_2_29_credit_scores_bimodal :
    let x : Fin 5 → ℝ := ![680, 680, 700, 720, 720]
    (univ.filter fun i => x i = 680).card = 2 ∧ (univ.filter fun i => x i = 720).card = 2 ∧
      (univ.filter fun i => x i = 700).card = 1 := by
  intro x
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Try It 2.30. Hours of video games, classes with boundaries
0, 3.5, 7.5, 11.5, 15.5, 19.5 (midpoints 1.75, 5.5, 9.5, 13.5, 17.5) and frequencies 3, 7, 12, 7, 9
(38 teenagers): the best estimate of the mean is `∑ f m / ∑ f = 409.75/38 = 1639/152`, about 10.8. -/
@[kb "openstaxintrostats2e" "Try It 2.30, p. 115"]
theorem tryit_2_30_video_game_grouped_mean :
    let lo : Fin 5 → ℝ := ![0, 3.5, 7.5, 11.5, 15.5]
    let hi : Fin 5 → ℝ := ![3.5, 7.5, 11.5, 15.5, 19.5]
    let m : Fin 5 → ℝ := ![1.75, 5.5, 9.5, 13.5, 17.5]
    let f : Fin 5 → ℝ := ![3, 7, 12, 7, 9]
    (∀ i, (lo i + hi i) / 2 = m i) ∧ (∑ i, f i) = 38 ∧ (∑ i, f i * m i) = 409.75 ∧
      (∑ i, f i * m i) / ∑ i, f i = 1639 / 152 := by
  intro lo hi m f
  have h1 : (∑ i, f i) = 38 := by simp [f, Fin.sum_univ_succ] <;> norm_num
  have h2 : (∑ i, f i * m i) = 409.75 := by simp [f, m, Fin.sum_univ_succ] <;> norm_num
  refine ⟨?_, h1, h2, ?_⟩
  · intro i; fin_cases i <;> simp [lo, hi, m] <;> norm_num
  · rw [h1, h2]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.31 (part b). The 39 ages at death of the U.S.
presidents read off the stem-and-leaf table: the mean is `2733/39 = 911/13` (about 70.1) and the
median, the 20th value, is 68, so the mean is above the median (a right-skewed list); the ages 57 and
67 each occur three times. Parts a and c refer to figures that are not given as numbers and are not
formalized. -/
@[kb "openstaxintrostats2e" "Try It 2.31, p. 118"]
theorem tryit_2_31_presidents_age_at_death :
    let x : Fin 39 → ℝ := ![46, 49, 53, 56, 57, 57, 57, 58, 60, 60, 63, 63, 64, 64, 65, 66, 67, 67,
      67, 68, 70, 71, 71, 72, 73, 74, 77, 78, 78, 79, 80, 81, 83, 85, 88, 90, 90, 93, 93]
    mean x = 911 / 13 ∧ median x = 68 ∧ median x < mean x ∧
      (univ.filter fun i => x i = 57).card = 3 ∧ (univ.filter fun i => x i = 67).card = 3 := by
  intro x
  have hx : Monotone x := by mono_tac
  have hm : mean x = 911 / 13 := by simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  have hd : median x = 68 := by rw [median_odd (m := 19) x hx]; simp [x]
  refine ⟨hm, hd, by rw [hm, hd]; norm_num, ?_, ?_⟩ <;>
    (rw [Finset.card_filter]; simp [x, Fin.sum_univ_succ, -Finset.sum_boole] <;> norm_num)

/-- OpenStax Introductory Statistics 2e Try It 2.32. The 25 baseball player ages: the mean is
`767/25 = 30.68`, the sample standard deviation lies between 6.09 and 6.10 (about 6.1), and the
value two standard deviations above the mean lies between 42.86 and 42.88 (about 42.9). -/
@[kb "openstaxintrostats2e" "Try It 2.32, p. 123"]
theorem tryit_2_32_baseball_ages_mean_sd :
    let x : Fin 25 → ℝ := ![21, 21, 22, 23, 24, 24, 25, 25, 28, 29, 29, 31, 32, 33, 33, 34, 35, 36,
      36, 36, 36, 38, 38, 38, 40]
    mean x = 767 / 25 ∧ (6.09 < sampleStdDev x ∧ sampleStdDev x < 6.10) ∧
      (42.86 < mean x + 2 * sampleStdDev x ∧ mean x + 2 * sampleStdDev x < 42.88) := by
  intro x
  have hm : mean x = 767 / 25 := by simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  have hs : 6.09 < sampleStdDev x ∧ sampleStdDev x < 6.10 := by
    refine sd_bounds x (by norm_num) (by norm_num) ?_ ?_
    · simp [sampleVariance, sumSqDev, hm, x, Fin.sum_univ_succ] <;> norm_num
    · simp [sampleVariance, sumSqDev, hm, x, Fin.sum_univ_succ] <;> norm_num
  obtain ⟨h1, h2⟩ := hs
  refine ⟨hm, ⟨h1, h2⟩, ?_, ?_⟩ <;> rw [hm] <;> linarith

/-- OpenStax Introductory Statistics 2e Try It 2.33. The 29 pet-food counts: the sample mean is
`269/29`, which lies between 9.25 and 9.35 (9.3 to one decimal), and the sample standard deviation
lies between 2.15 and 2.16 (2.2 to one decimal). -/
@[kb "openstaxintrostats2e" "Try It 2.33, p. 125"]
theorem tryit_2_33_pet_food_mean_sd :
    let x : Fin 29 → ℝ := ![6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11,
      11, 11, 12, 12, 12, 12, 12, 12]
    mean x = 269 / 29 ∧ (9.25 < mean x ∧ mean x < 9.35) ∧
      (2.15 < sampleStdDev x ∧ sampleStdDev x < 2.16) := by
  intro x
  have hm : mean x = 269 / 29 := by simp [mean, x, Fin.sum_univ_succ] <;> norm_num
  refine ⟨hm, ⟨by rw [hm]; norm_num, by rw [hm]; norm_num⟩, ?_⟩
  refine sd_bounds x (by norm_num) (by norm_num) ?_ ?_
  · simp [sampleVariance, sumSqDev, hm, x, Fin.sum_univ_succ] <;> norm_num
  · simp [sampleVariance, sumSqDev, hm, x, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.34. The grouped data of Example 2.34 (midpoints 1,
4, 7, 10, 13, 16 with frequencies 1, 6, 10, 7, 0, 2; 26 values, grouped mean `197/26`): the sample
standard deviation (divisor `n - 1 = 25`) lies between 3.50 and 3.51, as a calculator's `Sx` shows,
and the population version (divisor 26) lies between 3.43 and 3.44. -/
@[kb "openstaxintrostats2e" "Try It 2.34, p. 126"]
theorem tryit_2_34_grouped_standard_deviations :
    let f : Fin 6 → ℝ := ![1, 6, 10, 7, 0, 2]
    let m : Fin 6 → ℝ := ![1, 4, 7, 10, 13, 16]
    (3.5 < Real.sqrt ((∑ i, f i * (m i - 197 / 26) ^ 2) / 25) ∧
        Real.sqrt ((∑ i, f i * (m i - 197 / 26) ^ 2) / 25) < 3.51) ∧
      (3.43 < Real.sqrt ((∑ i, f i * (m i - 197 / 26) ^ 2) / 26) ∧
        Real.sqrt ((∑ i, f i * (m i - 197 / 26) ^ 2) / 26) < 3.44) := by
  intro f m
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Real.lt_sqrt (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num
  · rw [Real.lt_sqrt (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; simp [f, m, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 2.35. Angie swam 26.2 s for a team with mean 27.2 and
standard deviation 0.8, Beth 27.3 s for a team with mean 30.1 and standard deviation 1.4: Angie's
z-score is `-1.25`, Beth's is `-2`, so Beth is further below her team's mean time, i.e. faster
relative to her team. (The team data are modelled by the three-point lists `μ - σ, μ, μ + σ`.) -/
@[kb "openstaxintrostats2e" "Try It 2.35, p. 129"]
theorem tryit_2_35_swimmers_z_scores :
    let angie : Fin 3 → ℝ := ![26.4, 27.2, 28.0]
    let beth : Fin 3 → ℝ := ![28.7, 30.1, 31.5]
    mean angie = 27.2 ∧ sampleStdDev angie = 0.8 ∧ zScore angie 26.2 = -1.25 ∧
      mean beth = 30.1 ∧ sampleStdDev beth = 1.4 ∧ zScore beth 27.3 = -2 ∧
      zScore beth 27.3 < zScore angie 26.2 := by
  intro angie beth
  have hj : mean angie = 27.2 := by simp [mean, angie, Fin.sum_univ_succ] <;> norm_num
  have ha : mean beth = 30.1 := by simp [mean, beth, Fin.sum_univ_succ] <;> norm_num
  have sj : sampleStdDev angie = 0.8 := by
    have : sampleVariance angie = 0.8 ^ 2 := by
      simp [sampleVariance, sumSqDev, hj, angie, Fin.sum_univ_succ] <;> norm_num
    rw [sampleStdDev, this, Real.sqrt_sq (by norm_num)]
  have sa : sampleStdDev beth = 1.4 := by
    have : sampleVariance beth = 1.4 ^ 2 := by
      simp [sampleVariance, sumSqDev, ha, beth, Fin.sum_univ_succ] <;> norm_num
    rw [sampleStdDev, this, Real.sqrt_sq (by norm_num)]
  have zj : zScore angie 26.2 = -1.25 := by
    simp only [zScore, hj, sj]; norm_num
  have za : zScore beth 27.3 = -2 := by
    simp only [zScore, ha, sa]; norm_num
  refine ⟨hj, sj, zj, ha, sa, za, ?_⟩
  rw [zj, za]; norm_num

end UndergradKB.Statistics.Course.TryItC2
