import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues

/-!
# Course layer, chapter 9 (OpenStax *Introductory Statistics 2e*): worked examples

One-sample hypothesis tests.  For the `z` tests (known standard deviation, or a proportion with the
null standard error) the sample statistic is modelled as a normal variable under the null
hypothesis; we prove two-sided bounds on the test statistic and on the p-value, using enclosures of
the standard normal distribution function `Φ`, and the resulting decision.  For the `t` test only the
statistic is proved; the book's p-value comes from a `t` table and is not proved here.

Examples 9.1 to 9.8, 9.10 to 9.13 only state hypotheses or errors in words and are not formalized.
-/

namespace UndergradKB.Statistics.Course.ExamplesC9

open MeasureTheory ProbabilityTheory Real Set UndergradKB.Statistics

local notation "Φ" => cdf (gaussianReal 0 1)

/-- Rational Taylor sums used in the `Φ` enclosures. -/
macro "emp_tac" : tactic =>
  `(tactic| (simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]))

private lemma Phi_gt {k z a : ℝ} (hk : 0 ≤ k) (m : ℕ) (ha : 0 < a) (hz : k ≤ z)
    (hl : a * 2.5067 < 2 * empR (2 * m) k) : 1 / 2 + a / 2 < Φ z := by
  have h : a < (gaussianReal 0 1).real (Ioo (-k) k) := by
    rw [gaussianReal_real_Ioo_eq hk]
    have hl' := le_integral_gauss m hk
    have s1 := sqrt_two_pi_gt
    have s2 := sqrt_two_pi_lt
    have hp : 0 < √(2 * π) := by linarith
    rw [lt_div_iff₀ hp]; nlinarith
  have h1 := stdNormalCdf_eq_Ioo hk
  have h2 : Φ k ≤ Φ z := (cdf (gaussianReal 0 1)).mono hz
  linarith

private lemma Phi_lt {k z b : ℝ} (hk : 0 ≤ k) (m : ℕ) (hb : 0 < b) (hz : z ≤ k)
    (hu : 2 * empR (2 * m + 1) k < b * 2.5066) : Φ z < 1 / 2 + b / 2 := by
  have h : (gaussianReal 0 1).real (Ioo (-k) k) < b := by
    rw [gaussianReal_real_Ioo_eq hk]
    have hu' := integral_gauss_le m hk
    have s1 := sqrt_two_pi_gt
    have s2 := sqrt_two_pi_lt
    have hp : 0 < √(2 * π) := by linarith
    rw [div_lt_iff₀ hp]; nlinarith
  have h1 := stdNormalCdf_eq_Ioo hk
  have h2 : Φ z ≤ Φ k := (cdf (gaussianReal 0 1)).mono hz
  linarith

private lemma Phi_neg_lt {k z a : ℝ} (hk : 0 ≤ k) (m : ℕ) (ha : 0 < a) (hz : z ≤ -k)
    (hl : a * 2.5067 < 2 * empR (2 * m) k) : Φ z < 1 / 2 - a / 2 := by
  have h := Phi_gt hk m ha (le_refl k) hl
  have h2 : Φ z ≤ Φ (-k) := (cdf (gaussianReal 0 1)).mono hz
  have h3 := stdNormalCdf_neg k
  linarith

private lemma Phi_neg_gt {k z b : ℝ} (hk : 0 ≤ k) (m : ℕ) (hb : 0 < b) (hz : -k ≤ z)
    (hu : 2 * empR (2 * m + 1) k < b * 2.5066) : 1 / 2 - b / 2 < Φ z := by
  have h := Phi_lt hk m hb (le_refl k) hu
  have h2 : Φ (-k) ≤ Φ z := (cdf (gaussianReal 0 1)).mono hz
  have h3 := stdNormalCdf_neg k
  linarith

/-- Right-tail probability of a normal variable: `P(X > x) = 1 - Φ((x - μ)/σ)`. -/
private lemma real_gt_normal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    P.real {ω | x < X ω} = 1 - Φ ((x - μ) / σ) := by
  have e : {ω | x < X ω} = {ω | X ω ≤ x}ᶜ := by
    ext ω; simp
  have hm : NullMeasurableSet {ω | X ω ≤ x} P :=
    hX.aemeasurable.nullMeasurable measurableSet_Iic
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure_iff.2 inferInstance
  rw [e, probReal_compl_eq_one_sub₀ hm, prob_le_normal hσ hX]

/-! ### Left-tailed test of a mean -/

/-- OpenStax Introductory Statistics 2e Example 9.14. Swim times with known `σ = 0.8`, `n = 15`,
null mean `16.43`, observed sample mean `16`. If the sample mean `X` is normal with mean `16.43`
and standard deviation `0.8/√15`, the `z` statistic lies in `(-2.083, -2.080)`, the left-tail
p-value `P(X ≤ 16)` lies in `(0.0185, 0.0189)` (the book's `0.0187`), and it is below `α = 0.05`,
so `H0` is rejected. -/
@[kb "openstaxintrostats2e" "Example 9.14, p. 483"]
theorem example_9_14_swim_z_test {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 16.43 (((0.8 : ℝ) / Real.sqrt 15) ^ 2).toNNReal) P) :
    (-2.083 < (16 - 16.43) / (0.8 / Real.sqrt 15) ∧
      (16 - 16.43) / (0.8 / Real.sqrt 15) < -2.080) ∧
    (0.0185 < P.real {ω | X ω ≤ 16} ∧ P.real {ω | X ω ≤ 16} < 0.0189) ∧
    P.real {ω | X ω ≤ 16} < 0.05 := by
  have hs1 : 3.87 < Real.sqrt 15 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt 15 < 3.875 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < (0.8 : ℝ) / Real.sqrt 15 := by positivity
  have hz : (16 - 16.43) / (0.8 / Real.sqrt 15) = -(0.5375 * Real.sqrt 15) := by
    have : Real.sqrt 15 ≠ 0 := by positivity
    field_simp; norm_num
  have hz1 : -2.0829 ≤ (16 - 16.43) / (0.8 / Real.sqrt 15) := by rw [hz]; linarith
  have hz2 : (16 - 16.43) / (0.8 / Real.sqrt 15) ≤ -2.0801 := by rw [hz]; linarith
  have hp := prob_le_normal hσ hX 16
  have u := Phi_neg_lt (k := 2.0801) (z := (16 - 16.43) / (0.8 / Real.sqrt 15)) (a := 0.9622)
    (by norm_num) 12 (by norm_num) hz2 (by emp_tac)
  have l := Phi_neg_gt (k := 2.0829) (z := (16 - 16.43) / (0.8 / Real.sqrt 15)) (b := 0.963)
    (by norm_num) 12 (by norm_num) hz1 (by emp_tac)
  refine ⟨⟨by rw [hz]; linarith, by rw [hz]; linarith⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [hp] <;> linarith

/-! ### Right-tailed test of a mean -/

/-- OpenStax Introductory Statistics 2e Example 9.15. Thirty bench-press values (frequencies
expanded) have mean exactly `1717/6 ≈ 286.17`. With known `σ = 55`, null mean `275`, the `z`
statistic lies in `(1.111, 1.113)`; if the sample mean is normal with mean `275` and standard
deviation `55/√30`, the right-tail p-value `P(X > x̄)` lies in `(0.1325, 0.1335)` (the book quotes
`0.1331`), which exceeds `α = 0.025`, so `H0` is not rejected. -/
@[kb "openstaxintrostats2e" "Example 9.15, p. 485"]
theorem example_9_15_bench_press_z_test {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 275 (((55 : ℝ) / Real.sqrt 30) ^ 2).toNNReal) P) :
    let x : Fin 30 → ℝ := ![205, 205, 205, 215, 215, 215, 225, 241, 241, 252, 252, 265, 265,
      275, 275, 313, 313, 316, 316, 316, 316, 316, 338, 338, 341, 345, 345, 368, 368, 385]
    mean x = 1717 / 6 ∧
    (1.111 < (mean x - 275) / (55 / Real.sqrt 30) ∧
      (mean x - 275) / (55 / Real.sqrt 30) < 1.113) ∧
    (0.1325 < P.real {ω | mean x < X ω} ∧ P.real {ω | mean x < X ω} < 0.1335) ∧
    0.025 < P.real {ω | mean x < X ω} := by
  intro x
  have hm : mean x = 1717 / 6 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hs1 : 5.477 < Real.sqrt 30 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt 30 < 5.478 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < (55 : ℝ) / Real.sqrt 30 := by positivity
  have hz : ((1717 / 6 : ℝ) - 275) / (55 / Real.sqrt 30) = 67 / 6 * Real.sqrt 30 / 55 := by
    rw [div_div_eq_mul_div]; ring
  have hz1 : 1.111 ≤ ((1717 / 6 : ℝ) - 275) / (55 / Real.sqrt 30) := by rw [hz]; linarith
  have hz2 : ((1717 / 6 : ℝ) - 275) / (55 / Real.sqrt 30) ≤ 1.113 := by rw [hz]; linarith
  have hp := real_gt_normal hσ hX (mean x)
  rw [hm] at hp ⊢
  have u := Phi_gt (k := 1.111) (z := ((1717 / 6 : ℝ) - 275) / (55 / Real.sqrt 30)) (a := 0.733)
    (by norm_num) 12 (by norm_num) hz1 (by emp_tac)
  have l := Phi_lt (k := 1.113) (z := ((1717 / 6 : ℝ) - 275) / (55 / Real.sqrt 30)) (b := 0.735)
    (by norm_num) 12 (by norm_num) hz2 (by emp_tac)
  refine ⟨rfl, ⟨by linarith, by linarith⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [hp] <;> linarith

/-! ### Tests of a proportion -/

/-- OpenStax Introductory Statistics 2e Example 9.17. Fifty-three of `100` brides: null `p = 0.5`,
standard error `√(0.5 · 0.5 / 100) = 0.05`, so `z = 0.6` exactly. If the sample proportion `X` is
normal with mean `0.5` and standard deviation `0.05`, the two-sided p-value
`P(X ≤ 0.47) + P(X > 0.53)` lies in `(0.5484, 0.5486)` (the book's `0.5485`), which exceeds
`α = 0.01`, so `H0` is not rejected. -/
@[kb "openstaxintrostats2e" "Example 9.17, p. 488"]
theorem example_9_17_brides_proportion_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.5 ((0.05 : ℝ) ^ 2).toNNReal) P) :
    Real.sqrt (0.5 * (1 - 0.5) / 100) = 0.05 ∧ (0.53 - 0.5) / 0.05 = (0.6 : ℝ) ∧
    (0.5484 < P.real {ω | X ω ≤ 0.47} + P.real {ω | 0.53 < X ω} ∧
      P.real {ω | X ω ≤ 0.47} + P.real {ω | 0.53 < X ω} < 0.5486) ∧
    0.01 < P.real {ω | X ω ≤ 0.47} + P.real {ω | 0.53 < X ω} := by
  have hσ : (0 : ℝ) < 0.05 := by norm_num
  have h1 := prob_le_normal hσ hX 0.47
  have h2 := real_gt_normal hσ hX 0.53
  have e1 : ((0.47 : ℝ) - 0.5) / 0.05 = -0.6 := by norm_num
  have e2 : ((0.53 : ℝ) - 0.5) / 0.05 = 0.6 := by norm_num
  rw [e1] at h1
  rw [e2] at h2
  have h3 := stdNormalCdf_neg 0.6
  have u := Phi_gt (k := 0.6) (z := 0.6) (a := 0.4514) (by norm_num) 12 (by norm_num) le_rfl
    (by emp_tac)
  have l := Phi_lt (k := 0.6) (z := 0.6) (b := 0.4516) (by norm_num) 12 (by norm_num) le_rfl
    (by emp_tac)
  refine ⟨?_, by norm_num, ⟨?_, ?_⟩, ?_⟩
  · rw [show (0.5 * (1 - 0.5) / 100 : ℝ) = 0.05 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  all_goals rw [h1, h2]; linarith

/-- OpenStax Introductory Statistics 2e Example 9.18. `43` of `150` households, null `p = 0.30`.
If the sample proportion `X` is normal with mean `0.3` and standard deviation
`√(0.3 · 0.7 / 150)`, the `z` statistic lies in `(-0.3565, -0.3555)`, the two-sided p-value
`P(X ≤ 43/150) + P(X > 47/150)` lies in `(0.721, 0.723)` (the book's `0.7216`), which exceeds the
default `α = 0.05`, so `H0` is not rejected. -/
@[kb "openstaxintrostats2e" "Example 9.18, p. 489"]
theorem example_9_18_cell_phones_proportion_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.3 ((Real.sqrt (0.3 * (1 - 0.3) / 150)) ^ 2).toNNReal) P) :
    (-0.3565 < (43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150) ∧
      (43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150) < -0.3555) ∧
    (0.721 < P.real {ω | X ω ≤ 43 / 150} + P.real {ω | 47 / 150 < X ω} ∧
      P.real {ω | X ω ≤ 43 / 150} + P.real {ω | 47 / 150 < X ω} < 0.723) ∧
    0.05 < P.real {ω | X ω ≤ 43 / 150} + P.real {ω | 47 / 150 < X ω} := by
  have hs1 : 0.03741 < Real.sqrt (0.3 * (1 - 0.3) / 150) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.3 * (1 - 0.3) / 150) < 0.03742 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.3 * (1 - 0.3) / 150) := by linarith
  have hz1 : -0.3565 < (43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150) < -0.3555 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h1 := prob_le_normal hσ hX (43 / 150)
  have h2 := real_gt_normal hσ hX (47 / 150)
  have e2 : ((47 : ℝ) / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150) =
      -((43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150)) := by
    rw [← neg_div]; congr 1; norm_num
  rw [e2] at h2
  have h3 := stdNormalCdf_neg ((43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150))
  have u := Phi_neg_lt (k := 0.3555) (z := (43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150))
    (a := 0.2777) (by norm_num) 8 (by norm_num) hz2.le (by emp_tac)
  have l := Phi_neg_gt (k := 0.3565) (z := (43 / 150 - 0.3) / Real.sqrt (0.3 * (1 - 0.3) / 150))
    (b := 0.2787) (by norm_num) 8 (by norm_num) hz1.le (by emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h1, h2] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 9.19. `17` of `42` fleas killed, null `p = 0.25`.
If the sample proportion `X` is normal with mean `0.25` and standard deviation
`√(0.25 · 0.75 / 42)`, the `z` statistic lies in `(2.31, 2.32)` (the book's `2.3163`), the
right-tail p-value `P(X > 17/42)` lies in `(0.0101, 0.0106)` (the book's `0.0103`), and it exceeds
`α = 0.01`. -/
@[kb "openstaxintrostats2e" "Example 9.19, p. 490"]
theorem example_9_19_fleas_proportion_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.25 ((Real.sqrt (0.25 * (1 - 0.25) / 42)) ^ 2).toNNReal) P) :
    (2.31 < (17 / 42 - 0.25) / Real.sqrt (0.25 * (1 - 0.25) / 42) ∧
      (17 / 42 - 0.25) / Real.sqrt (0.25 * (1 - 0.25) / 42) < 2.32) ∧
    (0.0101 < P.real {ω | 17 / 42 < X ω} ∧ P.real {ω | 17 / 42 < X ω} < 0.0106) ∧
    0.01 < P.real {ω | 17 / 42 < X ω} := by
  have hs1 : 0.0668 < Real.sqrt (0.25 * (1 - 0.25) / 42) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.25 * (1 - 0.25) / 42) < 0.0669 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.25 * (1 - 0.25) / 42) := by linarith
  have hz1 : 2.31 < (17 / 42 - 0.25) / Real.sqrt (0.25 * (1 - 0.25) / 42) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (17 / 42 - 0.25) / Real.sqrt (0.25 * (1 - 0.25) / 42) < 2.32 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h2 := real_gt_normal hσ hX (17 / 42)
  have u := Phi_gt (k := 2.31) (z := (17 / 42 - 0.25) / Real.sqrt (0.25 * (1 - 0.25) / 42))
    (a := 0.9789) (by norm_num) 12 (by norm_num) hz1.le (by emp_tac)
  have l := Phi_lt (k := 2.32) (z := (17 / 42 - 0.25) / Real.sqrt (0.25 * (1 - 0.25) / 42))
    (b := 0.9797) (by norm_num) 12 (by norm_num) hz2.le (by emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h2] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 9.21. `172` brain cancers among `420019` users,
null rate `0.00034`. If the sample proportion `X` is normal with mean `0.00034` and standard
deviation `√(0.00034 · 0.99966 / 420019)`, the `z` statistic lies in `(2.443, 2.444)`, the
right-tail p-value `P(X > 172/420019)` lies in `(0.0072, 0.0074)` (the book's `0.0073`), and it
exceeds `α = 0.005`, so `H0` is not rejected. -/
@[kb "openstaxintrostats2e" "Example 9.21, p. 493"]
theorem example_9_21_cell_phone_cancer_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.00034
      ((Real.sqrt (0.00034 * (1 - 0.00034) / 420019)) ^ 2).toNNReal) P) :
    (2.443 < (172 / 420019 - 0.00034) / Real.sqrt (0.00034 * (1 - 0.00034) / 420019) ∧
      (172 / 420019 - 0.00034) / Real.sqrt (0.00034 * (1 - 0.00034) / 420019) < 2.444) ∧
    (0.0072 < P.real {ω | 172 / 420019 < X ω} ∧ P.real {ω | 172 / 420019 < X ω} < 0.0074) ∧
    0.005 < P.real {ω | 172 / 420019 < X ω} := by
  have hs1 : 0.000028446 < Real.sqrt (0.00034 * (1 - 0.00034) / 420019) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.00034 * (1 - 0.00034) / 420019) < 0.000028447 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.00034 * (1 - 0.00034) / 420019) := by linarith
  have hz1 : 2.443 < (172 / 420019 - 0.00034) / Real.sqrt (0.00034 * (1 - 0.00034) / 420019) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (172 / 420019 - 0.00034) / Real.sqrt (0.00034 * (1 - 0.00034) / 420019) < 2.444 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h2 := real_gt_normal hσ hX (172 / 420019)
  have u := Phi_gt (k := 2.443)
    (z := (172 / 420019 - 0.00034) / Real.sqrt (0.00034 * (1 - 0.00034) / 420019))
    (a := 0.9854) (by norm_num) 12 (by norm_num) hz1.le (by emp_tac)
  have l := Phi_lt (k := 2.444)
    (z := (172 / 420019 - 0.00034) / Real.sqrt (0.00034 * (1 - 0.00034) / 420019))
    (b := 0.98549) (by norm_num) 12 (by norm_num) hz2.le (by emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h2] <;> linarith

/-- OpenStax Introductory Statistics 2e Example 9.22. `11` of `37937` residents, null rate
`0.00078`. If the sample proportion `X` is normal with mean `0.00078` and standard deviation
`√(0.00078 · 0.99922 / 37937)`, the `z` statistic lies in `(-3.4195, -3.4185)` (the book's
`-3.4189`), the two-sided p-value `P(X ≤ 11/37937) + P(X > 2 · 0.00078 - 11/37937)` lies in
`(0.0005, 0.0007)` (the book's `0.00063`), and it is below `α = 0.01`, so `H0` is rejected. -/
@[kb "openstaxintrostats2e" "Example 9.22, p. 495"]
theorem example_9_22_blood_type_test {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0.00078
      ((Real.sqrt (0.00078 * (1 - 0.00078) / 37937)) ^ 2).toNNReal) P) :
    (-3.4195 < (11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937) ∧
      (11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937) < -3.4185) ∧
    (0.0005 < P.real {ω | X ω ≤ 11 / 37937} + P.real {ω | 2 * 0.00078 - 11 / 37937 < X ω} ∧
      P.real {ω | X ω ≤ 11 / 37937} + P.real {ω | 2 * 0.00078 - 11 / 37937 < X ω} < 0.0007) ∧
    P.real {ω | X ω ≤ 11 / 37937} + P.real {ω | 2 * 0.00078 - 11 / 37937 < X ω} < 0.01 := by
  have hs1 : 0.00014333 < Real.sqrt (0.00078 * (1 - 0.00078) / 37937) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : Real.sqrt (0.00078 * (1 - 0.00078) / 37937) < 0.00014334 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hσ : 0 < Real.sqrt (0.00078 * (1 - 0.00078) / 37937) := by linarith
  have hz1 : -3.4195 < (11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937) := by
    rw [lt_div_iff₀ hσ]; linarith
  have hz2 : (11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937) < -3.4185 := by
    rw [div_lt_iff₀ hσ]; linarith
  have h1 := prob_le_normal hσ hX (11 / 37937)
  have h2 := real_gt_normal hσ hX (2 * 0.00078 - 11 / 37937)
  have e2 : (2 * (0.00078 : ℝ) - 11 / 37937 - 0.00078) /
      Real.sqrt (0.00078 * (1 - 0.00078) / 37937) =
      -((11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937)) := by
    rw [← neg_div]; congr 1; ring
  rw [e2] at h2
  have h3 := stdNormalCdf_neg ((11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937))
  have u := Phi_neg_lt (k := 3.4185)
    (z := (11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937))
    (a := 0.9993) (by norm_num) 14 (by norm_num) hz2.le (by emp_tac)
  have l := Phi_neg_gt (k := 3.4195)
    (z := (11 / 37937 - 0.00078) / Real.sqrt (0.00078 * (1 - 0.00078) / 37937))
    (b := 0.9995) (by norm_num) 14 (by norm_num) hz1.le (by emp_tac)
  refine ⟨⟨hz1, hz2⟩, ⟨?_, ?_⟩, ?_⟩ <;> rw [h1, h2] <;> linarith

/-! ### Test of a mean with unknown standard deviation -/

/-- OpenStax Introductory Statistics 2e Example 9.20. Eleven conductivity measurements have mean
exactly `1.04` and sample variance exactly `217/50000`, so the sample standard deviation lies in
`(0.06587, 0.06588)`; the `t` statistic against `μ₀ = 1` lies in `(2.013, 2.015)` (the book's
`2.014`). The book's right-tail p-value `0.036` (10 degrees of freedom) comes from a `t` table and
is not proved here. -/
@[kb "openstaxintrostats2e" "Example 9.20, p. 493"]
theorem example_9_20_conductivity_t_statistic :
    let x : Fin 11 → ℝ := ![1.11, 1.07, 1.11, 1.07, 1.12, 1.08, 0.98, 0.98, 1.02, 0.95, 0.95]
    mean x = 1.04 ∧ sampleVariance x = 217 / 50000 ∧
      (0.06587 < sampleStdDev x ∧ sampleStdDev x < 0.06588) ∧
      2.013 < (mean x - 1) / (sampleStdDev x / Real.sqrt 11) ∧
      (mean x - 1) / (sampleStdDev x / Real.sqrt 11) < 2.015 := by
  intro x
  have hm : mean x = 1.04 := by simp [mean, x, Fin.sum_univ_succ]; norm_num
  have hv : sampleVariance x = 217 / 50000 := by
    simp only [sampleVariance, sumSqDev, hm]
    simp [x, Fin.sum_univ_succ]
    norm_num
  have hs1 : 0.06587 < sampleStdDev x := by
    rw [sampleStdDev, hv]; exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs2 : sampleStdDev x < 0.06588 := by
    rw [sampleStdDev, hv]; exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h1 : 3.316 < Real.sqrt 11 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : Real.sqrt 11 < 3.317 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  refine ⟨hm, hv, ⟨hs1, hs2⟩, ?_, ?_⟩
  · rw [hm, lt_div_iff₀ (by positivity), ← mul_div_assoc,
      div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    linarith
  · rw [hm, div_lt_iff₀ (by positivity), ← mul_div_assoc,
      lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    linarith

end UndergradKB.Statistics.Course.ExamplesC9
