import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Discrete

/-!
# Practice exercises, chapter 4 (OpenStax *Introductory Statistics 2e*): discrete random variables

Probability tables, expected values and standard deviations, and the binomial, geometric,
hypergeometric and Poisson laws.  Exact rational answers where possible; two-sided bounds where the
book rounds or where `e^(-λ)` enters.  A table with one missing entry is stated as: whenever the
column adds to 1, the missing entry equals the value found.

Skipped (verbal or symbolic, no numbers to prove): 6, 10, 13, 14, 23, 24, 29, 37, 38, 39, 45, 46, 47,
51, 52, 53, 56, 57, 62, 63, 64, 65.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal unitInterval

set_option maxRecDepth 100000

namespace UndergradKB.Statistics.Course.PracticeC4

private lemma real_Iic (μ : Measure ℕ) [IsFiniteMeasure μ] (k : ℕ) :
    μ.real (Set.Iic k) = ∑ j ∈ range (k + 1), μ.real {j} := by
  have : (Set.Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext; simp
  rw [this, sum_measureReal_singleton]

private lemma real_Ioi (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    μ.real (Set.Ioi k) = 1 - ∑ j ∈ range (k + 1), μ.real {j} := by
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, real_Iic]

private lemma hp0 {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 1) :
    (⟨c, h0.le, h1⟩ : unitInterval) ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp at this
  linarith

private lemma choose_real (n k : ℕ) :
    (Nat.choose n k : ℝ) = (n.descFactorial k : ℝ) / (k.factorial : ℝ) := by
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div (Nat.factorial_dvd_descFactorial n k)
    (by positivity)]

/-- Bounds for `e^(-n)` from bounds for `e`. -/
private lemma exp_neg_nat_bounds (n : ℕ) (hn : n ≠ 0) :
    (1 / 2.7182818286 : ℝ) ^ n < Real.exp (-(n : ℝ)) ∧
      Real.exp (-(n : ℝ)) < (1 / 2.7182818283 : ℝ) ^ n := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have e : Real.exp (-(n : ℝ)) = (1 / Real.exp 1) ^ n := by
    rw [Real.exp_neg, one_div, inv_pow, ← Real.exp_nat_mul, mul_one]
  rw [e]
  constructor
  · apply pow_lt_pow_left₀ _ (by positivity) hn
    exact one_div_lt_one_div_of_lt (by positivity) h2
  · apply pow_lt_pow_left₀ _ (by positivity) hn
    exact one_div_lt_one_div_of_lt (by norm_num) h1

/-- Pure arithmetic: if `E` lies between two bounds and `S > 0`, the product `E * S` is bracketed. -/
private lemma bound_mul {E a b S lo hi : ℝ} (hS : 0 < S) (ha : a < E) (hb : E < b)
    (h1 : lo ≤ a * S) (h2 : b * S ≤ hi) : lo < E * S ∧ E * S < hi :=
  ⟨lt_of_le_of_lt h1 (mul_lt_mul_of_pos_right ha hS),
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hb hS) h2⟩

private lemma poisson_Iic (r : ℝ≥0) (k : ℕ) :
    (poissonMeasure r).real (Set.Iic k) =
      Real.exp (-(r : ℝ)) * ∑ j ∈ range (k + 1), (r : ℝ) ^ j / (j.factorial : ℝ) := by
  rw [real_Iic, Finset.mul_sum]
  exact sum_congr rfl fun j _ => by rw [poissonMeasure_real_singleton]; ring

/-! ### Section 4.1: probability distribution tables -/

/-- OpenStax Introductory Statistics 2e Practice exercise 4.1. Years a new hire stays (0 to 6) with
probabilities 0.12, 0.18, 0.30, 0.15, `P(4)`, 0.10, 0.05: the missing entry is 0.10, and then every
entry is in `[0, 1]` and the column adds to 1. -/
@[kb "openstaxintrostats2e" "Exercise 4.1, p. 276"]
theorem ex_4_1_attrition_table :
    (∀ p4 : ℝ, ∑ i, (![0.12, 0.18, 0.30, 0.15, p4, 0.10, 0.05] : Fin 7 → ℝ) i = 1 → p4 = 0.10) ∧
      (let p : Fin 7 → ℝ := ![0.12, 0.18, 0.30, 0.15, 0.10, 0.10, 0.05]
       (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∑ i, p i = 1) := by
  refine ⟨fun p4 h => ?_, ?_⟩
  · simp [Fin.sum_univ_succ] at h
    linarith
  · intro p
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp [p] <;> norm_num
    · simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.2. In the attrition table of 4.1 the
missing entry is `P(x = 4) = 0.10`. -/
@[kb "openstaxintrostats2e" "Exercise 4.2, p. 276"]
theorem ex_4_2_attrition_four_years :
    1 - (0.12 + 0.18 + 0.30 + 0.15 + 0.10 + 0.05 : ℝ) = 0.10 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.3. In the attrition table of 4.1,
`P(x ≥ 5) = 0.10 + 0.05 = 0.15`. -/
@[kb "openstaxintrostats2e" "Exercise 4.3, p. 276"]
theorem ex_4_3_attrition_at_least_five :
    let p : Fin 7 → ℝ := ![0.12, 0.18, 0.30, 0.15, 0.10, 0.10, 0.05]
    ∑ i : Fin 7, (if 5 ≤ (i : ℕ) then p i else 0) = 0.15 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.4. In the attrition table of 4.1 the
expected stay is `∑ x P(x) = 2.43` years. -/
@[kb "openstaxintrostats2e" "Exercise 4.4, p. 276"]
theorem ex_4_4_attrition_expected_years :
    let x : Fin 7 → ℝ := ![0, 1, 2, 3, 4, 5, 6]
    let p : Fin 7 → ℝ := ![0.12, 0.18, 0.30, 0.15, 0.10, 0.10, 0.05]
    ∑ i, x i * p i = 2.43 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.5. The column `P(x)` of the attrition
table adds to 1. -/
@[kb "openstaxintrostats2e" "Exercise 4.5, p. 276"]
theorem ex_4_5_attrition_sum_one :
    let p : Fin 7 → ℝ := ![0.12, 0.18, 0.30, 0.15, 0.10, 0.10, 0.05]
    ∑ i, p i = 1 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.7. Batches of muffins sold, 1 to 4, with
probabilities 0.15, 0.35, 0.40, 0.10 (a distribution: total 1): `P(x > 1) = 0.85`. -/
@[kb "openstaxintrostats2e" "Exercise 4.7, p. 277"]
theorem ex_4_7_muffins_more_than_one :
    let p : Fin 4 → ℝ := ![0.15, 0.35, 0.40, 0.10]
    ∑ i, p i = 1 ∧ ∑ i : Fin 4, (if 1 < (i : ℕ) + 1 then p i else 0) = 0.85 := by
  intro p
  constructor <;> simp [p, Fin.sum_univ_succ] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.8. In the muffin table of 4.7,
the probability of exactly one batch is `0.15` (the first entry; two batches would be `0.35`). -/
@[kb "openstaxintrostats2e" "Exercise 4.8, p. 277"]
theorem ex_4_8_muffins_exactly_one :
    let p : Fin 4 → ℝ := ![0.15, 0.35, 0.40, 0.10]
    p 0 = 0.15 ∧ p 1 = 0.35 := by
  intro p
  constructor <;> simp [p]

/-- OpenStax Introductory Statistics 2e Practice exercise 4.9. In the muffin table of 4.7 the
baker should plan on `∑ x P(x) = 2.45` batches on average. -/
@[kb "openstaxintrostats2e" "Exercise 4.9, p. 277"]
theorem ex_4_9_muffins_expected_batches :
    let x : Fin 4 → ℝ := ![1, 2, 3, 4]
    let p : Fin 4 → ℝ := ![0.15, 0.35, 0.40, 0.10]
    ∑ i, x i * p i = 2.45 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.11. Ellen practises 0, 1, 2, 3 days a
week with probabilities 0.03, 0.04, 0.08, 0.85: the table is a probability distribution (total 1). -/
@[kb "openstaxintrostats2e" "Exercise 4.11, p. 277"]
theorem ex_4_11_music_practice_table :
    let p : Fin 4 → ℝ := ![0.03, 0.04, 0.08, 0.85]
    ∑ i, p i = 1 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.12. The second characteristic of a
discrete probability distribution (besides total 1): each probability lies between 0 and 1.
Checked for Ellen's table of 4.11. -/
@[kb "openstaxintrostats2e" "Exercise 4.12, p. 277"]
theorem ex_4_12_music_practice_entries_in_unit_interval :
    let p : Fin 4 → ℝ := ![0.03, 0.04, 0.08, 0.85]
    ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
  intro p i
  fin_cases i <;> simp [p] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.15. Javier attends 0 to 5 events a
month with probabilities 0.05, 0.05, 0.10, 0.20, 0.25, 0.35: entries in `[0, 1]`, total 1. -/
@[kb "openstaxintrostats2e" "Exercise 4.15, p. 277"]
theorem ex_4_15_volunteer_table :
    let p : Fin 6 → ℝ := ![0.05, 0.05, 0.10, 0.20, 0.25, 0.35]
    (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ ∑ i, p i = 1 := by
  intro p
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [p] <;> norm_num
  · simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.16. In the volunteer table of 4.15,
`P(x < 3) = 0.05 + 0.05 + 0.10 = 0.20`. -/
@[kb "openstaxintrostats2e" "Exercise 4.16, p. 277"]
theorem ex_4_16_volunteer_less_than_three :
    let p : Fin 6 → ℝ := ![0.05, 0.05, 0.10, 0.20, 0.25, 0.35]
    ∑ i : Fin 6, (if (i : ℕ) < 3 then p i else 0) = 0.20 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.17. In the volunteer table of 4.15,
`P(x > 0) = 0.95`. -/
@[kb "openstaxintrostats2e" "Exercise 4.17, p. 277"]
theorem ex_4_17_volunteer_at_least_one :
    let p : Fin 6 → ℝ := ![0.05, 0.05, 0.10, 0.20, 0.25, 0.35]
    ∑ i : Fin 6, (if 0 < (i : ℕ) then p i else 0) = 0.95 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-! ### Section 4.2: expected value and standard deviation -/

/-- OpenStax Introductory Statistics 2e Practice exercise 4.18. The table `x = 0, 1, 2, 3` with
`P(x) = 0.2, 0.2, 0.4, 0.2` (total 1) has `x P(x)` column `0, 0.2, 0.8, 0.6` and expected value 1.6. -/
@[kb "openstaxintrostats2e" "Exercise 4.18, p. 277"]
theorem ex_4_18_expected_value_table :
    let x : Fin 4 → ℝ := ![0, 1, 2, 3]
    let p : Fin 4 → ℝ := ![0.2, 0.2, 0.4, 0.2]
    ∑ i, p i = 1 ∧ (fun i => x i * p i) = ![0, 0.2, 0.8, 0.6] ∧ ∑ i, x i * p i = 1.6 := by
  intro x p
  refine ⟨?_, ?_, ?_⟩
  · simp [p, Fin.sum_univ_succ]; norm_num
  · funext i; fin_cases i <;> simp [x, p] <;> norm_num
  · simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.19. For `x = 2, 4, 6, 8` with
`P(x) = 0.1, 0.3, 0.4, 0.2` the expected value is `0.2 + 1.2 + 2.4 + 1.6 = 5.4`. -/
@[kb "openstaxintrostats2e" "Exercise 4.19, p. 277"]
theorem ex_4_19_expected_value_two_four_six_eight :
    let x : Fin 4 → ℝ := ![2, 4, 6, 8]
    let p : Fin 4 → ℝ := ![0.1, 0.3, 0.4, 0.2]
    ∑ i, x i * p i = 5.4 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.20. For the table of 4.19 (mean 5.4) the
column `(x - μ)² P(x)` adds to the variance 3.24, so the standard deviation is exactly 1.8. -/
@[kb "openstaxintrostats2e" "Exercise 4.20, p. 278"]
theorem ex_4_20_standard_deviation_two_four_six_eight :
    let x : Fin 4 → ℝ := ![2, 4, 6, 8]
    let p : Fin 4 → ℝ := ![0.1, 0.3, 0.4, 0.2]
    ∑ i, (x i - 5.4) ^ 2 * p i = 3.24 ∧ Real.sqrt (∑ i, (x i - 5.4) ^ 2 * p i) = 1.8 := by
  intro x p
  have h : ∑ i, (x i - 5.4) ^ 2 * p i = 3.24 := by
    simp [x, p, Fin.sum_univ_succ]; norm_num
  refine ⟨h, ?_⟩
  rw [h, Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.21. The listed probabilities
`0.15, 0.25, 0.30, 0.20, 0.15` add to 1.05, not 1, so the table is not a probability distribution. -/
@[kb "openstaxintrostats2e" "Exercise 4.21, p. 278"]
theorem ex_4_21_probabilities_sum_too_large :
    let p : Fin 5 → ℝ := ![0.15, 0.25, 0.30, 0.20, 0.15]
    ∑ i, p i = 1.05 ∧ ∑ i, p i ≠ 1 := by
  intro p
  have h : ∑ i, p i = 1.05 := by simp [p, Fin.sum_univ_succ]; norm_num
  exact ⟨h, by rw [h]; norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 4.22. The probabilities
`0.15, 0.25, 0.25, 0.20, 0.15` for `x = 1, ..., 5` do add to 1, but the third column of the table
(`0.15, 0.40, 0.65, 0.85, 1`) is the running total of `P(x)`, not `x P(x)`, which is
`0.15, 0.50, 0.75, 0.80, 0.75`. -/
@[kb "openstaxintrostats2e" "Exercise 4.22, p. 278"]
theorem ex_4_22_running_total_instead_of_products :
    let x : Fin 5 → ℝ := ![1, 2, 3, 4, 5]
    let p : Fin 5 → ℝ := ![0.15, 0.25, 0.25, 0.20, 0.15]
    let shown : Fin 5 → ℝ := ![0.15, 0.40, 0.65, 0.85, 1]
    ∑ i, p i = 1 ∧ (fun i => ∑ j ∈ Finset.univ.filter (fun j : Fin 5 => j ≤ i), p j) = shown ∧
      (fun i => x i * p i) = ![0.15, 0.50, 0.75, 0.80, 0.75] ∧ (fun i => x i * p i) ≠ shown := by
  intro x p shown
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [p, Fin.sum_univ_succ]; norm_num
  · funext i; fin_cases i <;> simp [p, shown, Fin.sum_univ_succ, Finset.sum_filter] <;> norm_num
  · funext i; fin_cases i <;> simp [x, p] <;> norm_num
  · intro h
    have := congrFun h 1
    simp [x, p, shown] at this
    norm_num at this

/-- OpenStax Introductory Statistics 2e Practice exercise 4.25. Years of post-graduate research
`x = 1, ..., 6` with probabilities 0.35, 0.20, 0.15, `P(4)`, 0.10, 0.05: the missing entry is 0.15. -/
@[kb "openstaxintrostats2e" "Exercise 4.25, p. 279"]
theorem ex_4_25_physics_four_years :
    ∀ p4 : ℝ, ∑ i, (![0.35, 0.20, 0.15, p4, 0.10, 0.05] : Fin 6 → ℝ) i = 1 → p4 = 0.15 := by
  intro p4 h
  simp [Fin.sum_univ_succ] at h
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 4.26. In the physics table of 4.25,
`P(x ≤ 3) = 0.35 + 0.20 + 0.15 = 0.70`. -/
@[kb "openstaxintrostats2e" "Exercise 4.26, p. 279"]
theorem ex_4_26_physics_at_most_three :
    let p : Fin 6 → ℝ := ![0.35, 0.20, 0.15, 0.15, 0.10, 0.05]
    ∑ i : Fin 6, (if (i : ℕ) + 1 ≤ 3 then p i else 0) = 0.70 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.27. In the physics table of 4.25 the
expected number of years is `0.35 + 0.40 + 0.45 + 0.60 + 0.50 + 0.30 = 2.6`. -/
@[kb "openstaxintrostats2e" "Exercise 4.27, p. 279"]
theorem ex_4_27_physics_expected_years :
    let x : Fin 6 → ℝ := ![1, 2, 3, 4, 5, 6]
    let p : Fin 6 → ℝ := ![0.35, 0.20, 0.15, 0.15, 0.10, 0.05]
    ∑ i, x i * p i = 2.6 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.28. Years of ballet `x = 1, ..., 7` with
probabilities 0.10, 0.05, 0.10, `P(4)`, 0.30, 0.20, 0.10: the missing entry is 0.15, and the
completed `x P(x)` column is `0.1, 0.1, 0.3, 0.6, 1.5, 1.2, 0.7`. -/
@[kb "openstaxintrostats2e" "Exercise 4.28, p. 279"]
theorem ex_4_28_ballet_table :
    (∀ p4 : ℝ, ∑ i, (![0.10, 0.05, 0.10, p4, 0.30, 0.20, 0.10] : Fin 7 → ℝ) i = 1 → p4 = 0.15) ∧
      (let x : Fin 7 → ℝ := ![1, 2, 3, 4, 5, 6, 7]
       let p : Fin 7 → ℝ := ![0.10, 0.05, 0.10, 0.15, 0.30, 0.20, 0.10]
       (fun i => x i * p i) = ![0.1, 0.1, 0.3, 0.6, 1.5, 1.2, 0.7]) := by
  refine ⟨fun p4 h => ?_, ?_⟩
  · simp [Fin.sum_univ_succ] at h
    linarith
  · intro x p
    funext i; fin_cases i <;> simp [x, p] <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.30. In the ballet table of 4.28,
`P(x = 4) = 0.15`. -/
@[kb "openstaxintrostats2e" "Exercise 4.30, p. 280"]
theorem ex_4_30_ballet_four_years :
    1 - (0.10 + 0.05 + 0.10 + 0.30 + 0.20 + 0.10 : ℝ) = 0.15 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.31. In the ballet table of 4.28,
`P(x < 4) = 0.10 + 0.05 + 0.10 = 0.25`. -/
@[kb "openstaxintrostats2e" "Exercise 4.31, p. 280"]
theorem ex_4_31_ballet_less_than_four :
    let p : Fin 7 → ℝ := ![0.10, 0.05, 0.10, 0.15, 0.30, 0.20, 0.10]
    ∑ i : Fin 7, (if (i : ℕ) + 1 < 4 then p i else 0) = 0.25 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.32. In the ballet table of 4.28 the
expected number of years is 4.5. -/
@[kb "openstaxintrostats2e" "Exercise 4.32, p. 280"]
theorem ex_4_32_ballet_expected_years :
    let x : Fin 7 → ℝ := ![1, 2, 3, 4, 5, 6, 7]
    let p : Fin 7 → ℝ := ![0.10, 0.05, 0.10, 0.15, 0.30, 0.20, 0.10]
    ∑ i, x i * p i = 4.5 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.33. The column `P(x)` of the completed
ballet table adds to 1, as every probability distribution must. -/
@[kb "openstaxintrostats2e" "Exercise 4.33, p. 280"]
theorem ex_4_33_ballet_probabilities_sum :
    let p : Fin 7 → ℝ := ![0.10, 0.05, 0.10, 0.15, 0.30, 0.20, 0.10]
    ∑ i, p i = 1 := by
  intro p
  simp [p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.34. The column `x P(x)` of the ballet
table adds to the mean of the distribution, 4.5. -/
@[kb "openstaxintrostats2e" "Exercise 4.34, p. 280"]
theorem ex_4_34_ballet_products_sum :
    let x : Fin 7 → ℝ := ![1, 2, 3, 4, 5, 6, 7]
    let p : Fin 7 → ℝ := ![0.10, 0.05, 0.10, 0.15, 0.30, 0.20, 0.10]
    ∑ i, (fun j => x j * p j) i = 4.5 := by
  intro x p
  simp [x, p, Fin.sum_univ_succ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.35. Drawing a card with replacement,
a face card (12 of 52) wins 30 dollars and any other card (40 of 52) loses 2 dollars: the expected
value of playing is `30 (12/52) - 2 (40/52) = 70/13` dollars (about 5.38). -/
@[kb "openstaxintrostats2e" "Exercise 4.35, p. 280"]
theorem ex_4_35_face_card_game_expected_value :
    (30 : ℝ) * (12 / 52) + (-2) * (40 / 52) = 70 / 13 := by
  norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.36. The game of 4.35 has a positive
expected value (70/13 dollars per play, over 5.38), so on average the player gains by playing. -/
@[kb "openstaxintrostats2e" "Exercise 4.36, p. 280"]
theorem ex_4_36_face_card_game_should_play :
    0 < (30 : ℝ) * (12 / 52) + (-2) * (40 / 52) ∧
      (5.38 : ℝ) < (30 : ℝ) * (12 / 52) + (-2) * (40 / 52) := by
  constructor <;> norm_num

/-! ### Section 4.3: binomial, 8 students with probability 0.713 -/

/-- OpenStax Introductory Statistics 2e Practice exercise 4.40. For `X ~ B(8, 0.713)` (number of 8
first-year students answering yes) the probabilities of `x = 0, ..., 8` add to 1. -/
@[kb "openstaxintrostats2e" "Exercise 4.40, p. 280"]
theorem ex_4_40_binomial_pdf_sums_to_one :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    ∑ x ∈ range 9, Bin(8, p).real {x} = 1 := by
  intro p
  simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p]
  norm_num [Nat.choose]

/-- OpenStax Introductory Statistics 2e Practice exercise 4.41. For `X ~ B(8, 0.713)` the mean is
`np = 5.704` (about 5.7). -/
@[kb "openstaxintrostats2e" "Exercise 4.41, p. 281"]
theorem ex_4_41_binomial_mean :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    ∫ x, x ∂Bin(ℝ, 8, p) = 5.704 := by
  intro p
  have : ∫ x, x ∂Bin(ℝ, 8, p) = p * 8 :=
    integral_of_hasLaw_binomial (X := id) (P := Bin(ℝ, 8, p)) HasLaw.id
  rw [this]; simp [p]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.42. For `X ~ B(8, 0.713)` the variance
is `npq = 1.637048` and the standard deviation lies in `(1.2794, 1.2795)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.42, p. 281"]
theorem ex_4_42_binomial_standard_deviation :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    variance (id : ℝ → ℝ) Bin(ℝ, 8, p) = 1.637048 ∧
      (1.2794 < Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 8, p)) ∧
        Real.sqrt (variance (id : ℝ → ℝ) Bin(ℝ, 8, p)) < 1.2795) := by
  intro p
  have hv : variance (id : ℝ → ℝ) Bin(ℝ, 8, p) = 1.637048 := by
    rw [UndergradKB.Statistics.variance_binomial]; simp [p] <;> norm_num
  refine ⟨hv, ?_, ?_⟩
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.43. For `X ~ B(8, 0.713)`,
`P(X ≤ 5)` lies in `(0.4151, 0.4152)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.43, p. 281"]
theorem ex_4_43_binomial_at_most_five :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    0.4151 < Bin(8, p).real (Set.Iic 5) ∧ Bin(8, p).real (Set.Iic 5) < 0.4152 := by
  intro p
  rw [real_Iic]
  simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p]
  norm_num [Nat.choose]

/-- OpenStax Introductory Statistics 2e Practice exercise 4.44. For `X ~ B(8, 0.713)`,
`P(X ≥ 2) = P(X > 1)` lies in `(0.99903, 0.99904)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.44, p. 281"]
theorem ex_4_44_binomial_at_least_two :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    0.99903 < Bin(8, p).real (Set.Ioi 1) ∧ Bin(8, p).real (Set.Ioi 1) < 0.99904 := by
  intro p
  rw [real_Ioi]
  simp only [binomial_real_singleton, Finset.sum_range_succ, Finset.sum_range_zero, p]
  norm_num [Nat.choose]

/-! ### Section 4.4: geometric, success probability 0.713 -/

/-- OpenStax Introductory Statistics 2e Practice exercise 4.48. `X` is the number of students
asked until the first yes, success probability 0.713: `P(X = x) = 0.287^(x-1) 0.713`, and for
`x = 1, ..., 6` the values are within 10⁻⁶ of 0.713, 0.204631, 0.058729, 0.016855, 0.004837,
0.001388. -/
@[kb "openstaxintrostats2e" "Exercise 4.48, p. 281"]
theorem ex_4_48_geometric_pdf :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    (∀ k : ℕ, (geometricMeasure p).real {k} = 0.287 ^ k * 0.713) ∧
      |(geometricMeasure p).real {0} - 0.713| < 1e-6 ∧
      |(geometricMeasure p).real {1} - 0.204631| < 1e-6 ∧
      |(geometricMeasure p).real {2} - 0.058729| < 1e-6 ∧
      |(geometricMeasure p).real {3} - 0.016855| < 1e-6 ∧
      |(geometricMeasure p).real {4} - 0.004837| < 1e-6 ∧
      |(geometricMeasure p).real {5} - 0.001388| < 1e-6 := by
  intro p
  have hp := hp0 (c := 0.713) (by norm_num) (by norm_num)
  have h : ∀ k : ℕ, (geometricMeasure p).real {k} = 0.287 ^ k * 0.713 := by
    intro k
    rw [geometricMeasure_real_singleton hp]
    simp only [p]; norm_num
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h, abs_lt] <;> constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.49. With success probability 0.713 the
expected number of students asked until a yes is `1/p = 1/0.713`, which lies in `(1.4025, 1.4026)`
(about 1.4). -/
@[kb "openstaxintrostats2e" "Exercise 4.49, p. 281"]
theorem ex_4_49_geometric_mean_trials :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 1 / 0.713 ∧
      (1.4025 < (1 / 0.713 : ℝ) ∧ (1 / 0.713 : ℝ) < 1.4026) := by
  intro p
  have hp := hp0 (c := 0.713) (by norm_num) (by norm_num)
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [UndergradKB.Statistics.integral_geometricMeasure_trials hp]

/-- OpenStax Introductory Statistics 2e Practice exercise 4.50. With success probability 0.713,
needing fewer than three students asked means `X ≤ 2`, i.e. at most one failure first (in
Mathlib's count of failures, `k ≤ 1`): `0.713 + 0.287 · 0.713 = 0.917631`. -/
@[kb "openstaxintrostats2e" "Exercise 4.50, p. 281"]
theorem ex_4_50_geometric_fewer_than_three :
    let p : unitInterval := ⟨0.713, by norm_num⟩
    (geometricMeasure p).real (Set.Iic 1) = 0.917631 := by
  intro p
  have hp := hp0 (c := 0.713) (by norm_num) (by norm_num)
  rw [real_Iic]
  simp [Finset.sum_range_succ, geometricMeasure_real_singleton hp, p]
  norm_num

/-! ### Section 4.5: hypergeometric, 16 business and 7 non-business majors, sample of nine -/

/-- OpenStax Introductory Statistics 2e Practice exercise 4.54. For the number of business majors
`X ~ H(16, 7, 9)`: the mean is `144/23`, the variance `∑ (x - μ)² P(x) = 7056/5819`, and the
standard deviation lies in `(1.1011, 1.1012)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.54, p. 281"]
theorem ex_4_54_hypergeometric_standard_deviation :
    ∑ x ∈ range 10, ((x : ℝ) - 144 / 23) ^ 2 * UndergradKB.Statistics.hypergeometricPMF 16 7 9 x
        = 7056 / 5819 ∧
      (1.1011 < Real.sqrt (7056 / 5819) ∧ Real.sqrt (7056 / 5819) < 1.1012) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [UndergradKB.Statistics.hypergeometricPMF, choose_real, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num [Nat.descFactorial, Nat.factorial]
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 4.55. For `X ~ H(16, 7, 9)` the expected
number of business majors is `9 · 16/23 = 144/23`, which lies in `(6.26, 6.27)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.55, p. 281"]
theorem ex_4_55_hypergeometric_mean :
    ∑ x ∈ range 10, (x : ℝ) * UndergradKB.Statistics.hypergeometricPMF 16 7 9 x = 144 / 23 ∧
      (6.26 < (144 / 23 : ℝ) ∧ (144 / 23 : ℝ) < 6.27) := by
  have h := UndergradKB.Statistics.sum_mul_hypergeometricPMF 16 7 9 (by norm_num)
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [show (10 : ℕ) = 9 + 1 from rfl, h]
  norm_num

/-! ### Section 4.6: Poisson -/

/-- OpenStax Introductory Statistics 2e Practice exercise 4.58. A store with 120 customers a day on
average: with `X ~ P(120)`, `P(X = 150)` lies in `(0.0010114, 0.0010115)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.58, p. 282"]
theorem ex_4_58_customers_150_in_a_day :
    0.0010114 < (poissonMeasure 120).real {150} ∧ (poissonMeasure 120).real {150} < 0.0010115 := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 120 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  rw [poissonMeasure_real_singleton]
  simp only [NNReal.coe_ofNat]
  rw [mul_div_assoc]
  exact bound_mul (by positivity) h1 h2 (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Practice exercise 4.59. At 120 customers per 12-hour day
there are `120 · 4/12 = 40` customers in four hours; with `X ~ P(40)`, `P(X = 35)` lies in
`(0.04853, 0.04854)` (book: about 0.0485). -/
@[kb "openstaxintrostats2e" "Exercise 4.59, p. 282"]
theorem ex_4_59_customers_35_in_four_hours :
    (120 : ℝ) * 4 / 12 = 40 ∧
      (0.04853 < (poissonMeasure 40).real {35} ∧ (poissonMeasure 40).real {35} < 0.04854) := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 40 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  refine ⟨by norm_num, ?_⟩
  rw [poissonMeasure_real_singleton]
  simp only [NNReal.coe_ofNat]
  rw [mul_div_assoc]
  exact bound_mul (by positivity) h1 h2 (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Practice exercise 4.60. In one hour the mean is
`120/12 = 10`; with `X ~ P(10)`, `P(X > 12) = 1 - P(X ≤ 12)` lies in `(0.2084, 0.2085)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.60, p. 282"]
theorem ex_4_60_more_than_twelve_in_an_hour :
    (120 : ℝ) / 12 = 10 ∧
      (0.2084 < (poissonMeasure 10).real (Set.Ioi 12) ∧
        (poissonMeasure 10).real (Set.Ioi 12) < 0.2085) := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 10 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  refine ⟨by norm_num, ?_⟩
  have h := bound_mul (E := Real.exp (-10)) (S := ∑ j ∈ range 13, (10 : ℝ) ^ j / (j.factorial : ℝ))
    (lo := 0.7915) (hi := 0.7916) (by positivity) h1 h2
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, poisson_Iic]
  simp only [NNReal.coe_ofNat]
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 4.61. In two hours the mean is
`120 · 2/12 = 20`; with `X ~ P(20)`, `P(X < 12) = P(X ≤ 11)` lies in `(0.02138, 0.02139)`
(book: 0.0214). -/
@[kb "openstaxintrostats2e" "Exercise 4.61, p. 282"]
theorem ex_4_61_fewer_than_twelve_in_two_hours :
    (120 : ℝ) * 2 / 12 = 20 ∧
      (0.02138 < (poissonMeasure 20).real (Set.Iic 11) ∧
        (poissonMeasure 20).real (Set.Iic 11) < 0.02139) := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 20 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  refine ⟨by norm_num, ?_⟩
  rw [poisson_Iic]
  simp only [NNReal.coe_ofNat]
  exact bound_mul (by positivity) h1 h2
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Practice exercise 4.66. Teen motor-vehicle deaths per day
`X ~ P(8)`: `P(X = x) = e⁻⁸ 8^x / x!`, and for `x = 0, ..., 5` the values lie in
`(0.00033546, 0.00033547)`, `(0.0026837, 0.0026838)`, `(0.010734, 0.010735)`, `(0.028626, 0.028627)`,
`(0.057252, 0.057253)` and `(0.091603, 0.091604)`. -/
@[kb "openstaxintrostats2e" "Exercise 4.66, p. 282"]
theorem ex_4_66_poisson_eight_probabilities :
    (∀ k : ℕ, (poissonMeasure 8).real {k} = Real.exp (-8) * (8 ^ k / (k.factorial : ℝ))) ∧
      (0.00033546 < (poissonMeasure 8).real {0} ∧ (poissonMeasure 8).real {0} < 0.00033547) ∧
      (0.0026837 < (poissonMeasure 8).real {1} ∧ (poissonMeasure 8).real {1} < 0.0026838) ∧
      (0.010734 < (poissonMeasure 8).real {2} ∧ (poissonMeasure 8).real {2} < 0.010735) ∧
      (0.028626 < (poissonMeasure 8).real {3} ∧ (poissonMeasure 8).real {3} < 0.028627) ∧
      (0.057252 < (poissonMeasure 8).real {4} ∧ (poissonMeasure 8).real {4} < 0.057253) ∧
      (0.091603 < (poissonMeasure 8).real {5} ∧ (poissonMeasure 8).real {5} < 0.091604) := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 8 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  have h : ∀ k : ℕ, (poissonMeasure 8).real {k} = Real.exp (-8) * (8 ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [poissonMeasure_real_singleton, mul_div_assoc]
    simp only [NNReal.coe_ofNat]
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h] <;>
    exact bound_mul (by positivity) h1 h2 (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Practice exercise 4.67. A day with no teen deaths
(`X ~ P(8)`) has probability `e⁻⁸`, which lies in `(0.000335, 0.0003355)`: very unlikely. -/
@[kb "openstaxintrostats2e" "Exercise 4.67, p. 282"]
theorem ex_4_67_no_teen_deaths_unlikely :
    0.000335 < (poissonMeasure 8).real {0} ∧ (poissonMeasure 8).real {0} < 0.0003355 := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 8 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  rw [poissonMeasure_real_singleton]
  simp only [NNReal.coe_ofNat]
  rw [mul_div_assoc]
  exact bound_mul (by positivity) h1 h2 (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])

/-- OpenStax Introductory Statistics 2e Practice exercise 4.68. More than 20 teen deaths in a day
(`X ~ P(8)`) has probability `1 - P(X ≤ 20)` in `(0.0000939, 0.000094)`: very unlikely. -/
@[kb "openstaxintrostats2e" "Exercise 4.68, p. 282"]
theorem ex_4_68_more_than_twenty_teen_deaths_unlikely :
    0.0000939 < (poissonMeasure 8).real (Set.Ioi 20) ∧
      (poissonMeasure 8).real (Set.Ioi 20) < 0.000094 := by
  obtain ⟨h1, h2⟩ := exp_neg_nat_bounds 8 (by norm_num)
  simp only [Nat.cast_ofNat] at h1 h2
  have h := bound_mul (E := Real.exp (-8)) (S := ∑ j ∈ range 21, (8 : ℝ) ^ j / (j.factorial : ℝ))
    (lo := 0.999906) (hi := 0.9999061) (by positivity) h1 h2
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, poisson_Iic]
  simp only [NNReal.coe_ofNat]
  constructor <;> linarith [h.1, h.2]

end UndergradKB.Statistics.Course.PracticeC4
