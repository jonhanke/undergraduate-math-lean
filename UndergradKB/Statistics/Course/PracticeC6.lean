import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.Course.ExamplesC7

/-!
# Course layer, chapter 6 (OpenStax *Introductory Statistics 2e*): Practice exercises

Practice exercises 6.1-6.59 on the normal distribution: z-scores (exact arithmetic), the empirical rule,
normal probabilities and percentiles.  A normal variable `X ~ N(μ, σ²)` is
`HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P`; rounded calculator values of the book are replaced by
two-sided bounds, obtained by reducing to the standard normal distribution function `Φ` and enclosing `Φ`
by the alternating Taylor sums of `EmpiricalRule.lean` (`Phi_enc` of `ExamplesC7.lean`).  Percentile
exercises are stated for any `k` with `P(X ≤ k) = p`.  The book writes `N(mean, standard deviation)`.
Exercises that only ask for a verbal definition, a figure or a graph have no theorem.
-/

namespace UndergradKB.Statistics.Course.PracticeC6

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics
open UndergradKB.Statistics.Course.ExamplesC7

local notation "Φ" => cdf (gaussianReal 0 1)

/-! ### Values of `Φ` -/

private lemma phi_1 : (0.84132 : ℝ) < Φ 1 ∧ Φ 1 < 0.84136 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_2 : (0.97721 : ℝ) < Φ 2 ∧ Φ 2 < 0.97727 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_3 : (0.99862 : ℝ) < Φ 3 ∧ Φ 3 < 0.99867 :=
  Phi_enc (by norm_num) 9 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_1_4 : (0.59868 : ℝ) < Φ 0.25 ∧ Φ 0.25 < 0.59872 :=
  Phi_enc (by norm_num) 1 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_3_2 : (0.93316 : ℝ) < Φ 1.5 ∧ Φ 1.5 < 0.93321 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_7_4 : (0.95991 : ℝ) < Φ 1.75 ∧ Φ 1.75 < 0.95996 :=
  Phi_enc (by norm_num) 5 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_11_13 : (0.80124 : ℝ) < Φ (11 / 13) ∧ Φ (11 / 13) < 0.80128 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_19_13 : (0.92804 : ℝ) < Φ (19 / 13) ∧ Φ (19 / 13) < 0.92809 :=
  Phi_enc (by norm_num) 4 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_41_13 : (0.99916 : ℝ) < Φ (41 / 13) ∧ Φ (41 / 13) < 0.99922 :=
  Phi_enc (by norm_num) 10 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_841 : (0.7998 : ℝ) < Φ 0.841 ∧ Φ 0.841 < 0.79984 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_842 : (0.80008 : ℝ) < Φ 0.842 ∧ Φ 0.842 < 0.80012 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_253 : (0.59984 : ℝ) < Φ 0.253 ∧ Φ 0.253 < 0.59988 :=
  Phi_enc (by norm_num) 1 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_254 : (0.60022 : ℝ) < Φ 0.254 ∧ Φ 0.254 < 0.60027 :=
  Phi_enc (by norm_num) 1 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_524 : (0.69984 : ℝ) < Φ 0.524 ∧ Φ 0.524 < 0.69988 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_525 : (0.70019 : ℝ) < Φ 0.525 ∧ Φ 0.525 < 0.70023 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_674 : (0.74982 : ℝ) < Φ 0.674 ∧ Φ 0.674 < 0.74986 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma phi_0_675 : (0.75014 : ℝ) < Φ 0.675 ∧ Φ 0.675 < 0.75018 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-- A number `k` with `P(X ≤ k) = p` lies between the values given by `z`-scores `lo` and `hi`
whenever `Φ lo < p < Φ hi` (private helper). -/
private lemma pct {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {μ σ : ℝ}
    (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) {p lo hi : ℝ} (h0 : 0 < p)
    (h1 : p < 1) (hlo : Φ lo < p) (hhi : p < Φ hi) {k : ℝ} (hk : P.real {ω | X ω ≤ k} = p) :
    μ + σ * lo < k ∧ k < μ + σ * hi := by
  obtain ⟨k', hk', h1', h2'⟩ := percentile_bd hσ hX h0 h1 hlo hhi
  have e : k = k' := ((normal_percentile hσ hX h0 h1).2 k hk).trans
    ((normal_percentile hσ hX h0 h1).2 k' hk').symm
  rw [e]
  exact ⟨h1', h2'⟩

/-- Mean of a normal variable (private helper). -/
private lemma mean_gauss {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal μ v) P) : P[X] = μ := by
  rw [hX.integral_eq]
  exact integral_id_gaussianReal

/-- Standard deviation of a normal variable (private helper). -/
private lemma sd_gauss {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    Real.sqrt (variance X P) = σ := by
  rw [hX.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg σ)]
  exact Real.sqrt_sq hσ.le

section Scores

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-! ### Section 6.1: parameters, z-scores and the empirical rule -/

/-- OpenStax Introductory Statistics 2e Practice exercise 6.2. For `X ~ N(61, 15²)` the median equals
the mean: `P(X ≤ 61) = 1/2`, and the mean is `61`. -/
@[kb "openstaxintrostats2e" "Exercise 6.2, p. 363"]
theorem ex_6_2_normal_median (hX : HasLaw X (gaussianReal 61 ((15 : ℝ) ^ 2).toNNReal) P) :
    P[X] = 61 ∧ P.real {ω | X ω ≤ 61} = 1 / 2 := by
  refine ⟨mean_gauss hX, ?_⟩
  rw [prob_le_normal (by norm_num) hX, sub_self, zero_div, Phi_zero]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.3. For `X ~ N(1, 2²)` (mean 1, standard
deviation 2) the standard deviation `σ` is `2`. -/
@[kb "openstaxintrostats2e" "Exercise 6.3, p. 363"]
theorem ex_6_3_normal_sd (hX : HasLaw X (gaussianReal 1 ((2 : ℝ) ^ 2).toNNReal) P) :
    Real.sqrt (variance X P) = 2 :=
  sd_gauss (by norm_num) hX

/-- OpenStax Introductory Statistics 2e Practice exercise 6.5. For `X ~ N(-4, 1)` the median equals the
mean: `P(X ≤ -4) = 1/2`. -/
@[kb "openstaxintrostats2e" "Exercise 6.5, p. 363"]
theorem ex_6_5_normal_median (hX : HasLaw X (gaussianReal (-4) ((1 : ℝ) ^ 2).toNNReal) P) :
    P.real {ω | X ω ≤ -4} = 1 / 2 := by
  rw [prob_le_normal (by norm_num) hX, sub_self, zero_div, Phi_zero]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.6. For `X ~ N(3, 5²)` (mean 3, standard
deviation 5) the standard deviation `σ` is `5`. -/
@[kb "openstaxintrostats2e" "Exercise 6.6, p. 363"]
theorem ex_6_6_normal_sd (hX : HasLaw X (gaussianReal 3 ((5 : ℝ) ^ 2).toNNReal) P) :
    Real.sqrt (variance X P) = 5 :=
  sd_gauss (by norm_num) hX

/-- OpenStax Introductory Statistics 2e Practice exercise 6.7. For `X ~ N(-2, 1)` the mean `μ` is
`-2`. -/
@[kb "openstaxintrostats2e" "Exercise 6.7, p. 364"]
theorem ex_6_7_normal_mean (hX : HasLaw X (gaussianReal (-2) ((1 : ℝ) ^ 2).toNNReal) P) :
    P[X] = -2 :=
  mean_gauss hX

/-- OpenStax Introductory Statistics 2e Practice exercise 6.9. Standardizing a normal variable
`X ~ N(μ, σ²)` makes the mean zero: `(X - μ)/σ` is standard normal and has mean `0`. -/
@[kb "openstaxintrostats2e" "Exercise 6.9, p. 364"]
theorem ex_6_9_standardizing_mean {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    HasLaw (fun ω ↦ (X ω - μ) / σ) (gaussianReal 0 1) P ∧ P[fun ω ↦ (X ω - μ) / σ] = 0 := by
  have h := standardized_hasLaw hσ hX
  exact ⟨h, mean_gauss h⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 6.10. `X ~ N(0, 1)` is the standard normal
distribution: its mean is `0` and its variance (and standard deviation) is `1`. -/
@[kb "openstaxintrostats2e" "Exercise 6.10, p. 364"]
theorem ex_6_10_standard_normal (hX : HasLaw X (gaussianReal 0 1) P) :
    P[X] = 0 ∧ variance X P = 1 := by
  refine ⟨mean_gauss hX, ?_⟩
  rw [hX.variance_eq, variance_id_gaussianReal]
  simp

/-- OpenStax Introductory Statistics 2e Practice exercise 6.11. If `x = 12` lies two standard
deviations to the right of the mean `μ` (`σ > 0`), its z-score is `2`. -/
@[kb "openstaxintrostats2e" "Exercise 6.11, p. 364"]
theorem ex_6_11_z_score {μ σ : ℝ} (hσ : 0 < σ) (hx : (12 : ℝ) = μ + 2 * σ) :
    (12 - μ) / σ = 2 := by
  rw [div_eq_iff hσ.ne']; linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.12. If `x = 9` lies `1.5` standard
deviations to the left of the mean, its z-score is `-1.5`. -/
@[kb "openstaxintrostats2e" "Exercise 6.12, p. 364"]
theorem ex_6_12_z_score {μ σ : ℝ} (hσ : 0 < σ) (hx : (9 : ℝ) = μ - 1.5 * σ) :
    (9 - μ) / σ = -1.5 := by
  rw [div_eq_iff hσ.ne']; linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.13. If `x = -2` lies `2.78` standard
deviations to the right of the mean, its z-score is `2.78`. -/
@[kb "openstaxintrostats2e" "Exercise 6.13, p. 364"]
theorem ex_6_13_z_score {μ σ : ℝ} (hσ : 0 < σ) (hx : (-2 : ℝ) = μ + 2.78 * σ) :
    (-2 - μ) / σ = 2.78 := by
  rw [div_eq_iff hσ.ne']; linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.14. If `x = 7` lies `0.133` standard
deviations to the left of the mean, its z-score is `-0.133`. -/
@[kb "openstaxintrostats2e" "Exercise 6.14, p. 364"]
theorem ex_6_14_z_score {μ σ : ℝ} (hσ : 0 < σ) (hx : (7 : ℝ) = μ - 0.133 * σ) :
    (7 - μ) / σ = -0.133 := by
  rw [div_eq_iff hσ.ne']; linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.15. For `X ~ N(2, 6²)` the value with
z-score `3` is `x = 20`. -/
@[kb "openstaxintrostats2e" "Exercise 6.15, p. 364"]
theorem ex_6_15_value_from_z : ∀ x : ℝ, (x - 2) / 6 = 3 ↔ x = 20 := by
  intro x
  rw [div_eq_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.16. For `X ~ N(8, 1)` the value with
z-score `-2.25` is `x = 5.75`. -/
@[kb "openstaxintrostats2e" "Exercise 6.16, p. 364"]
theorem ex_6_16_value_from_z : ∀ x : ℝ, (x - 8) / 1 = -2.25 ↔ x = 5.75 := by
  intro x
  rw [div_eq_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.17. For `X ~ N(9, 5²)` the value with
z-score `-0.5` is `x = 6.5`. -/
@[kb "openstaxintrostats2e" "Exercise 6.17, p. 364"]
theorem ex_6_17_value_from_z : ∀ x : ℝ, (x - 9) / 5 = -0.5 ↔ x = 6.5 := by
  intro x
  rw [div_eq_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.18. For `X ~ N(2, 3²)` the value with
z-score `-0.67` is `x = -0.01`. -/
@[kb "openstaxintrostats2e" "Exercise 6.18, p. 364"]
theorem ex_6_18_value_from_z : ∀ x : ℝ, (x - 2) / 3 = -0.67 ↔ x = -0.01 := by
  intro x
  rw [div_eq_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.19. For `X ~ N(4, 2²)` the value `1.5`
standard deviations to the left of the mean is `x = 1`. -/
@[kb "openstaxintrostats2e" "Exercise 6.19, p. 364"]
theorem ex_6_19_value_left_of_mean : ∀ x : ℝ, (x - 4) / 2 = -1.5 ↔ x = 1 := by
  intro x
  rw [div_eq_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.20. For `X ~ N(4, 2²)` the value two
standard deviations to the right of the mean is `x = 8`. -/
@[kb "openstaxintrostats2e" "Exercise 6.20, p. 364"]
theorem ex_6_20_value_right_of_mean : ∀ x : ℝ, (x - 4) / 2 = 2 ↔ x = 8 := by
  intro x
  rw [div_eq_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.21. For `X ~ N(8, 9²)` the value `0.67`
standard deviations to the left of the mean is `x = 1.97`. -/
@[kb "openstaxintrostats2e" "Exercise 6.21, p. 364"]
theorem ex_6_21_value_left_of_mean : ∀ x : ℝ, (x - 8) / 9 = -0.67 ↔ x = 1.97 := by
  intro x
  rw [div_eq_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.22. For `X ~ N(-1, 2²)` the z-score of
`x = 2` is `3/2`. -/
@[kb "openstaxintrostats2e" "Exercise 6.22, p. 364"]
theorem ex_6_22_z_score : (2 - (-1)) / 2 = (3 / 2 : ℝ) := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 6.23. For `X ~ N(12, 6²)` the z-score of
`x = 2` is `-5/3`, strictly between `-1.67` and `-1.66`. -/
@[kb "openstaxintrostats2e" "Exercise 6.23, p. 364"]
theorem ex_6_23_z_score :
    (2 - 12) / 6 = (-5 / 3 : ℝ) ∧ -1.67 < (2 - 12) / (6 : ℝ) ∧ (2 - 12) / (6 : ℝ) < -1.66 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 6.24. For `X ~ N(9, 3²)` the z-score of the
mean `x = 9` is `0`. -/
@[kb "openstaxintrostats2e" "Exercise 6.24, p. 364"]
theorem ex_6_24_z_score : (9 - 9) / 3 = (0 : ℝ) := by norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 6.25. For mean `6` and standard deviation
`1.5` the z-score of `x = 5.5` is `-1/3`, strictly between `-0.34` and `-0.33`. -/
@[kb "openstaxintrostats2e" "Exercise 6.25, p. 364"]
theorem ex_6_25_z_score :
    (5.5 - 6) / 1.5 = (-1 / 3 : ℝ) ∧ -0.34 < (5.5 - 6) / (1.5 : ℝ) ∧ (5.5 - 6) / (1.5 : ℝ) < -0.33 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Practice exercise 6.26. If `x = 5` has z-score `-1.25`, then
`x` is `1.25` standard deviations to the left of the mean (`x < μ` and `μ - x = 1.25 σ`). -/
@[kb "openstaxintrostats2e" "Exercise 6.26, p. 364"]
theorem ex_6_26_position {μ σ : ℝ} (hσ : 0 < σ) (hz : (5 - μ) / σ = -1.25) :
    μ - 5 = 1.25 * σ ∧ 5 < μ := by
  rw [div_eq_iff hσ.ne'] at hz
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.27. If `x = 3` has z-score `0.67`, then
`x` is `0.67` standard deviations to the right of the mean (`μ < x` and `x - μ = 0.67 σ`). -/
@[kb "openstaxintrostats2e" "Exercise 6.27, p. 364"]
theorem ex_6_27_position {μ σ : ℝ} (hσ : 0 < σ) (hz : (3 - μ) / σ = 0.67) :
    3 - μ = 0.67 * σ ∧ μ < 3 := by
  rw [div_eq_iff hσ.ne'] at hz
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.28. If `x = -2` has z-score `6`, then `x`
is `6` standard deviations to the right of the mean (`μ < x` and `x - μ = 6 σ`). -/
@[kb "openstaxintrostats2e" "Exercise 6.28, p. 364"]
theorem ex_6_28_position {μ σ : ℝ} (hσ : 0 < σ) (hz : (-2 - μ) / σ = 6) :
    -2 - μ = 6 * σ ∧ μ < -2 := by
  rw [div_eq_iff hσ.ne'] at hz
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.29. If `x = -5` has z-score `-3.14`, then
`x` is `3.14` standard deviations to the left of the mean (`x < μ` and `μ - x = 3.14 σ`). -/
@[kb "openstaxintrostats2e" "Exercise 6.29, p. 364"]
theorem ex_6_29_position {μ σ : ℝ} (hσ : 0 < σ) (hz : (-5 - μ) / σ = -3.14) :
    μ - (-5) = 3.14 * σ ∧ -5 < μ := by
  rw [div_eq_iff hσ.ne'] at hz
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.30. If `x = 6` has z-score `-1.7`, then `x`
is `1.7` standard deviations to the left of the mean (`x < μ` and `μ - x = 1.7 σ`). -/
@[kb "openstaxintrostats2e" "Exercise 6.30, p. 364"]
theorem ex_6_30_position {μ σ : ℝ} (hσ : 0 < σ) (hz : (6 - μ) / σ = -1.7) :
    μ - 6 = 1.7 * σ ∧ 6 < μ := by
  rw [div_eq_iff hσ.ne'] at hz
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.31. For a normal variable the probability
of lying within one standard deviation of the mean lies strictly between `0.68` and `0.69` (about
68%). -/
@[kb "openstaxintrostats2e" "Exercise 6.31, p. 364"]
theorem ex_6_31_within_one_sd {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    (0.68 : ℝ) < P.real {ω | X ω ∈ Ioo (μ - σ) (μ + σ)} ∧
      P.real {ω | X ω ∈ Ioo (μ - σ) (μ + σ)} < 0.69 :=
  (empirical_rule_normal_population hσ hX).1

/-- OpenStax Introductory Statistics 2e Practice exercise 6.32. For a normal variable the probability
of lying within two standard deviations of the mean lies strictly between `0.95` and `0.96` (about
95%). -/
@[kb "openstaxintrostats2e" "Exercise 6.32, p. 364"]
theorem ex_6_32_within_two_sd {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    (0.95 : ℝ) < P.real {ω | X ω ∈ Ioo (μ - 2 * σ) (μ + 2 * σ)} ∧
      P.real {ω | X ω ∈ Ioo (μ - 2 * σ) (μ + 2 * σ)} < 0.96 :=
  (empirical_rule_normal_population hσ hX).2.1

/-- Standardization of an interval endpoint (private helper). -/
private lemma z_add {μ σ : ℝ} (hσ : 0 < σ) (k : ℝ) : (μ + k * σ - μ) / σ = k := by
  rw [div_eq_iff hσ.ne']; ring

/-- Probability of an interval with endpoints at multiples of `σ` from the mean (private helper). -/
private lemma prob_kk {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    {j k : ℝ} (hjk : j ≤ k) :
    P.real {ω | μ + j * σ < X ω ∧ X ω < μ + k * σ} = Φ k - Φ j := by
  rw [prob_Ioo hσ hX (by nlinarith), z_add hσ, z_add hσ]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.33. For a normal variable the probability
of lying between the second and third standard deviations from the mean, on both sides, lies strictly
between `0.042` and `0.044` (about 4%). -/
@[kb "openstaxintrostats2e" "Exercise 6.33, p. 364"]
theorem ex_6_33_between_second_third_sd {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    0.042 < P.real {ω | μ + (-3) * σ < X ω ∧ X ω < μ + (-2) * σ} +
        P.real {ω | μ + 2 * σ < X ω ∧ X ω < μ + 3 * σ} ∧
      P.real {ω | μ + (-3) * σ < X ω ∧ X ω < μ + (-2) * σ} +
        P.real {ω | μ + 2 * σ < X ω ∧ X ω < μ + 3 * σ} < 0.044 := by
  rw [prob_kk hσ hX (by norm_num), prob_kk hσ hX (by norm_num), stdNormalCdf_neg,
    stdNormalCdf_neg]
  constructor <;> linarith [phi_2.1, phi_2.2, phi_3.1, phi_3.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.34. For `X ~ N(15, 3²)` the interval
`(12, 18)`, centered at the mean with half-width one standard deviation, has probability strictly
between `0.6826` and `0.6828` (the 68.27% of the book). -/
@[kb "openstaxintrostats2e" "Exercise 6.34, p. 364"]
theorem ex_6_34_normal_68 (hX : HasLaw X (gaussianReal 15 ((3 : ℝ) ^ 2).toNNReal) P) :
    (15 - 3 = (12 : ℝ) ∧ 15 + 3 = (18 : ℝ)) ∧
      (0.6826 < P.real {ω | 12 < X ω ∧ X ω < 18} ∧ P.real {ω | 12 < X ω ∧ X ω < 18} < 0.6828) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  have h := prob_Ioo (by norm_num) hX (a := 12) (b := 18) (by norm_num)
  have e1 : ((18 : ℝ) - 15) / 3 = 1 := by norm_num
  have e2 : ((12 : ℝ) - 15) / 3 = -1 := by norm_num
  rw [h, e1, e2, stdNormalCdf_neg]
  constructor <;> linarith [phi_1.1, phi_1.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.35. For `X ~ N(-3, 1)` the interval
`(-5, -1)`, centered at the mean with half-width two standard deviations, has probability strictly
between `0.9544` and `0.9546` (the 95.45% of the book). -/
@[kb "openstaxintrostats2e" "Exercise 6.35, p. 364"]
theorem ex_6_35_normal_95 (hX : HasLaw X (gaussianReal (-3) ((1 : ℝ) ^ 2).toNNReal) P) :
    (-3 - 2 = (-5 : ℝ) ∧ -3 + 2 = (-1 : ℝ)) ∧
      (0.9544 < P.real {ω | -5 < X ω ∧ X ω < -1} ∧ P.real {ω | -5 < X ω ∧ X ω < -1} < 0.9546) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  have h := prob_Ioo (by norm_num) hX (a := -5) (b := -1) (by norm_num)
  have e1 : ((-1 : ℝ) - -3) / 1 = 2 := by norm_num
  have e2 : ((-5 : ℝ) - -3) / 1 = -2 := by norm_num
  rw [h, e1, e2, stdNormalCdf_neg]
  constructor <;> linarith [phi_2.1, phi_2.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.36. For `X ~ N(-3, 1)` the interval from
the mean `-3` to `-2` (one standard deviation above it) has probability strictly between `0.3412` and
`0.3415` (the 34.14% of the book). -/
@[kb "openstaxintrostats2e" "Exercise 6.36, p. 364"]
theorem ex_6_36_normal_34 (hX : HasLaw X (gaussianReal (-3) ((1 : ℝ) ^ 2).toNNReal) P) :
    0.3412 < P.real {ω | -3 < X ω ∧ X ω < -2} ∧ P.real {ω | -3 < X ω ∧ X ω < -2} < 0.3415 := by
  have h := prob_Ioo (by norm_num) hX (a := -3) (b := -2) (by norm_num)
  have e1 : ((-2 : ℝ) - -3) / 1 = 1 := by norm_num
  have e2 : ((-3 : ℝ) - -3) / 1 = 0 := by norm_num
  rw [h, e1, e2, Phi_zero]
  constructor <;> linarith [phi_1.1, phi_1.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.37. For a normal variable the probability
of lying between the mean and three standard deviations above it lies strictly between `0.4986` and
`0.4987` (about 50%). -/
@[kb "openstaxintrostats2e" "Exercise 6.37, p. 364"]
theorem ex_6_37_mean_to_three_sd {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    0.4986 < P.real {ω | μ + 0 * σ < X ω ∧ X ω < μ + 3 * σ} ∧
      P.real {ω | μ + 0 * σ < X ω ∧ X ω < μ + 3 * σ} < 0.4987 := by
  rw [prob_kk hσ hX (by norm_num), Phi_zero]
  constructor <;> linarith [phi_3.1, phi_3.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.38. For a normal variable the probability
of lying between the mean and one standard deviation above it lies strictly between `0.3413` and
`0.3414` (about 34%). -/
@[kb "openstaxintrostats2e" "Exercise 6.38, p. 364"]
theorem ex_6_38_mean_to_one_sd {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    0.3413 < P.real {ω | μ + 0 * σ < X ω ∧ X ω < μ + 1 * σ} ∧
      P.real {ω | μ + 0 * σ < X ω ∧ X ω < μ + 1 * σ} < 0.3414 := by
  rw [prob_kk hσ hX (by norm_num), Phi_zero]
  constructor <;> linarith [phi_1.1, phi_1.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.39. For a normal variable the probability
of lying between the first and second standard deviations from the mean, on both sides, lies strictly
between `0.271` and `0.273` (about 27%). -/
@[kb "openstaxintrostats2e" "Exercise 6.39, p. 365"]
theorem ex_6_39_between_first_second_sd {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    0.271 < P.real {ω | μ + (-2) * σ < X ω ∧ X ω < μ + (-1) * σ} +
        P.real {ω | μ + 1 * σ < X ω ∧ X ω < μ + 2 * σ} ∧
      P.real {ω | μ + (-2) * σ < X ω ∧ X ω < μ + (-1) * σ} +
        P.real {ω | μ + 1 * σ < X ω ∧ X ω < μ + 2 * σ} < 0.273 := by
  rw [prob_kk hσ hX (by norm_num), prob_kk hσ hX (by norm_num), stdNormalCdf_neg,
    stdNormalCdf_neg]
  constructor <;> linarith [phi_1.1, phi_1.2, phi_2.1, phi_2.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.40. For a normal variable the probability
of lying between the first and third standard deviations from the mean, on both sides, lies strictly
between `0.314` and `0.316` (about 31%). -/
@[kb "openstaxintrostats2e" "Exercise 6.40, p. 365"]
theorem ex_6_40_between_first_third_sd {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    0.314 < P.real {ω | μ + (-3) * σ < X ω ∧ X ω < μ + (-1) * σ} +
        P.real {ω | μ + 1 * σ < X ω ∧ X ω < μ + 3 * σ} ∧
      P.real {ω | μ + (-3) * σ < X ω ∧ X ω < μ + (-1) * σ} +
        P.real {ω | μ + 1 * σ < X ω ∧ X ω < μ + 3 * σ} < 0.316 := by
  rw [prob_kk hσ hX (by norm_num), prob_kk hσ hX (by norm_num), stdNormalCdf_neg,
    stdNormalCdf_neg]
  constructor <;> linarith [phi_1.1, phi_1.2, phi_3.1, phi_3.2]

/-! ### Section 6.2: using the normal distribution -/

/-- OpenStax Introductory Statistics 2e Practice exercise 6.45. For a normal (continuous) variable,
`P(X < 1) = P(X ≤ 1)`: a single value has probability zero. -/
@[kb "openstaxintrostats2e" "Exercise 6.45, p. 365"]
theorem ex_6_45_lt_eq_le {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    P.real {ω | X ω < 1} = P.real {ω | X ω ≤ 1} := by
  rw [prob_lt hσ hX, prob_le_normal hσ hX]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.48. If the area to the left of `x` under a
normal curve is `0.123` (`P(X < x) = 0.123`), the area to the right is `0.877`. -/
@[kb "openstaxintrostats2e" "Exercise 6.48, p. 366"]
theorem ex_6_48_area_to_right {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) {x : ℝ}
    (h : P.real {ω | X ω < x} = 0.123) : P.real {ω | x < X ω} = 0.877 := by
  rw [prob_lt hσ hX] at h
  rw [prob_gt hσ hX, h]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 6.49. If the area to the right of `x` under a
normal curve is `0.543` (`P(X > x) = 0.543`), the area to the left is `0.457`. -/
@[kb "openstaxintrostats2e" "Exercise 6.49, p. 366"]
theorem ex_6_49_area_to_left {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) {x : ℝ}
    (h : P.real {ω | x < X ω} = 0.543) : P.real {ω | X ω < x} = 0.457 := by
  rw [prob_gt hσ hX] at h
  rw [prob_lt hσ hX]; linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 6.50. For `X ~ N(54, 8²)`, `P(X > 56)`
(z-score `1/4`) lies strictly between `0.4012` and `0.4014`. -/
@[kb "openstaxintrostats2e" "Exercise 6.50, p. 366"]
theorem ex_6_50_above_56 (hX : HasLaw X (gaussianReal 54 ((8 : ℝ) ^ 2).toNNReal) P) :
    0.4012 < P.real {ω | 56 < X ω} ∧ P.real {ω | 56 < X ω} < 0.4014 := by
  rw [prob_gt (by norm_num) hX]
  have e : ((56 : ℝ) - 54) / 8 = 0.25 := by norm_num
  rw [e]
  constructor <;> linarith [phi_1_4.1, phi_1_4.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.51. For `X ~ N(54, 8²)`, `P(X < 30)`
(z-score `-3`) lies strictly between `0.0013` and `0.0014` (the book's `0.0013`). -/
@[kb "openstaxintrostats2e" "Exercise 6.51, p. 366"]
theorem ex_6_51_below_30 (hX : HasLaw X (gaussianReal 54 ((8 : ℝ) ^ 2).toNNReal) P) :
    0.0013 < P.real {ω | X ω < 30} ∧ P.real {ω | X ω < 30} < 0.0014 := by
  rw [prob_lt (by norm_num) hX]
  have e : ((30 : ℝ) - 54) / 8 = -3 := by norm_num
  rw [e, stdNormalCdf_neg]
  constructor <;> linarith [phi_3.1, phi_3.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.52. For `X ~ N(54, 8²)`, any `k` with
`P(X ≤ k) = 0.8` (the 80th percentile) lies in `(60.72, 60.74)`. -/
@[kb "openstaxintrostats2e" "Exercise 6.52, p. 366"]
theorem ex_6_52_percentile_80 (hX : HasLaw X (gaussianReal 54 ((8 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 4 / 5) : 60.72 < k ∧ k < 60.74 := by
  have l : Φ 0.841 < 4 / 5 := by linarith [phi_0_841.2]
  have g : 4 / 5 < Φ 0.842 := by linarith [phi_0_842.1]
  have := pct (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.53. For `X ~ N(54, 8²)`, any `k` with
`P(X ≤ k) = 0.6` (the 60th percentile) lies in `(56.02, 56.04)` (the book's `56.03`). -/
@[kb "openstaxintrostats2e" "Exercise 6.53, p. 366"]
theorem ex_6_53_percentile_60 (hX : HasLaw X (gaussianReal 54 ((8 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 3 / 5) : 56.02 < k ∧ k < 56.04 := by
  have l : Φ 0.253 < 3 / 5 := by linarith [phi_0_253.2]
  have g : 3 / 5 < Φ 0.254 := by linarith [phi_0_254.1]
  have := pct (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.54. For `X ~ N(6, 2²)`, `P(3 < X < 9)`
(z-scores `∓3/2`) lies strictly between `0.8663` and `0.8665`. -/
@[kb "openstaxintrostats2e" "Exercise 6.54, p. 366"]
theorem ex_6_54_between_3_and_9 (hX : HasLaw X (gaussianReal 6 ((2 : ℝ) ^ 2).toNNReal) P) :
    0.8663 < P.real {ω | 3 < X ω ∧ X ω < 9} ∧ P.real {ω | 3 < X ω ∧ X ω < 9} < 0.8665 := by
  rw [prob_Ioo (by norm_num) hX (a := 3) (b := 9) (by norm_num)]
  have e1 : ((9 : ℝ) - 6) / 2 = 1.5 := by norm_num
  have e2 : ((3 : ℝ) - 6) / 2 = -1.5 := by norm_num
  rw [e1, e2, stdNormalCdf_neg]
  constructor <;> linarith [phi_3_2.1, phi_3_2.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.55. For `X ~ N(-3, 4²)`, `P(1 < X < 4)`
(z-scores `1` and `7/4`) lies strictly between `0.1185` and `0.1187` (the book's `0.1186`). -/
@[kb "openstaxintrostats2e" "Exercise 6.55, p. 366"]
theorem ex_6_55_between_1_and_4 (hX : HasLaw X (gaussianReal (-3) ((4 : ℝ) ^ 2).toNNReal) P) :
    0.1185 < P.real {ω | 1 < X ω ∧ X ω < 4} ∧ P.real {ω | 1 < X ω ∧ X ω < 4} < 0.1187 := by
  rw [prob_Ioo (by norm_num) hX (a := 1) (b := 4) (by norm_num)]
  have e1 : ((4 : ℝ) - -3) / 4 = 1.75 := by norm_num
  have e2 : ((1 : ℝ) - -3) / 4 = 1 := by norm_num
  rw [e1, e2]
  constructor <;> linarith [phi_7_4.1, phi_7_4.2, phi_1.1, phi_1.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.56. For `X ~ N(4, 5²)`, the maximum of
the bottom quartile is the `k` with `P(X ≤ k) = 1/4`; it lies in `(0.625, 0.63)`. -/
@[kb "openstaxintrostats2e" "Exercise 6.56, p. 366"]
theorem ex_6_56_bottom_quartile (hX : HasLaw X (gaussianReal 4 ((5 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 1 / 4) : 0.625 < k ∧ k < 0.63 := by
  have l : Φ (-0.675) < 1 / 4 := by rw [stdNormalCdf_neg]; linarith [phi_0_675.1]
  have g : 1 / 4 < Φ (-0.674) := by rw [stdNormalCdf_neg]; linarith [phi_0_674.2]
  have := pct (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.57(b). Lifetimes of fitness devices are
`X ~ N(4.1, 1.3²)`. A device breaks within the three-year guarantee with probability `P(X < 3)`
(z-score `-11/13`) strictly between `0.1987` and `0.1988`. -/
@[kb "openstaxintrostats2e" "Exercise 6.57, p. 366"]
theorem ex_6_57_break_down_in_guarantee
    (hX : HasLaw X (gaussianReal 4.1 ((1.3 : ℝ) ^ 2).toNNReal) P) :
    0.1987 < P.real {ω | X ω < 3} ∧ P.real {ω | X ω < 3} < 0.1988 := by
  rw [prob_lt (by norm_num) hX]
  have e : ((3 : ℝ) - 4.1) / 1.3 = -(11 / 13) := by norm_num
  rw [e, stdNormalCdf_neg]
  constructor <;> linarith [phi_11_13.1, phi_11_13.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.57(b). With the minimum lifetime `0`
(as in the book's `P(0 < x < 3)`), the probability that a device with `X ~ N(4.1, 1.3²)` breaks down
during the guarantee, `P(0 < X < 3)`, lies strictly between `0.1978` and `0.1980` (the book's
`0.1979`). -/
@[kb "openstaxintrostats2e" "Exercise 6.57, p. 366"]
theorem ex_6_57_between_0_and_3
    (hX : HasLaw X (gaussianReal 4.1 ((1.3 : ℝ) ^ 2).toNNReal) P) :
    0.1978 < P.real {ω | 0 < X ω ∧ X ω < 3} ∧ P.real {ω | 0 < X ω ∧ X ω < 3} < 0.198 := by
  rw [prob_Ioo (by norm_num) hX (a := 0) (b := 3) (by norm_num)]
  have e1 : ((3 : ℝ) - 4.1) / 1.3 = -(11 / 13) := by norm_num
  have e2 : ((0 : ℝ) - 4.1) / 1.3 = -(41 / 13) := by norm_num
  rw [e1, e2, stdNormalCdf_neg, stdNormalCdf_neg]
  constructor <;> linarith [phi_11_13.1, phi_11_13.2, phi_41_13.1, phi_41_13.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.58. For `X ~ N(4.1, 1.3²)`, the
probability that a device lasts between `2.8` and `6` years (z-scores `-1` and `19/13`) lies strictly
between `0.7693` and `0.7695`. -/
@[kb "openstaxintrostats2e" "Exercise 6.58, p. 366"]
theorem ex_6_58_between_2_8_and_6
    (hX : HasLaw X (gaussianReal 4.1 ((1.3 : ℝ) ^ 2).toNNReal) P) :
    0.7693 < P.real {ω | 2.8 < X ω ∧ X ω < 6} ∧ P.real {ω | 2.8 < X ω ∧ X ω < 6} < 0.7695 := by
  rw [prob_Ioo (by norm_num) hX (a := 2.8) (b := 6) (by norm_num)]
  have e1 : ((6 : ℝ) - 4.1) / 1.3 = 19 / 13 := by norm_num
  have e2 : ((2.8 : ℝ) - 4.1) / 1.3 = -1 := by norm_num
  rw [e1, e2, stdNormalCdf_neg]
  constructor <;> linarith [phi_19_13.1, phi_19_13.2, phi_1.1, phi_1.2]

/-- OpenStax Introductory Statistics 2e Practice exercise 6.59. For `X ~ N(4.1, 1.3²)`, any `k` with
`P(X ≤ k) = 0.7` (the 70th percentile) lies in `(4.78, 4.79)` years (the book's `4.78`). -/
@[kb "openstaxintrostats2e" "Exercise 6.59, p. 367"]
theorem ex_6_59_percentile_70 (hX : HasLaw X (gaussianReal 4.1 ((1.3 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 7 / 10) : 4.78 < k ∧ k < 4.79 := by
  have l : Φ 0.524 < 7 / 10 := by linarith [phi_0_524.2]
  have g : 7 / 10 < Φ 0.525 := by linarith [phi_0_525.1]
  have := pct (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

end Scores

end UndergradKB.Statistics.Course.PracticeC6
