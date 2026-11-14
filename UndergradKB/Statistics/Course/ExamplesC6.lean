import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues

/-!
# Worked examples, chapter 6 (OpenStax *Introductory Statistics 2e*): the normal distribution

Z-scores (exact arithmetic), the empirical rule, and normal probabilities and percentiles for a
variable `X` with `HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P`.  Where the book quotes a rounded
calculator value, we prove a two-sided bound around it; these bounds are obtained by reducing to the
standard normal distribution function `Φ` and enclosing `Φ` with the alternating Taylor sums of
`EmpiricalRule.lean`.  Probabilities of `X < x` and `X ≤ x` agree for a continuous variable; we
state whichever form is directly available.
-/

namespace UndergradKB.Statistics.Course.ExamplesC6

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics

local notation "Φ" => cdf (gaussianReal 0 1)

section Helpers

macro "emp_num" : tactic =>
  `(tactic| (simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial]))

/-- Lower enclosure for `Φ`. -/
private lemma Phi_gt {z c : ℝ} (hz : 0 ≤ z) (m : ℕ) (h0 : 0 ≤ empR (2 * m) z)
    (h : c < 1 / 2 + empR (2 * m) z / 2.5067) : c < Φ z := by
  rw [stdNormalCdf_eq_Ioo hz, gaussianReal_real_Ioo_eq hz]
  have hl := le_integral_gauss m hz
  have s2 := sqrt_two_pi_lt
  have s1 := sqrt_two_pi_gt
  have hp : 0 < √(2 * Real.pi) := by linarith
  have h1 : empR (2 * m) z / 2.5067 ≤ empR (2 * m) z / √(2 * Real.pi) :=
    div_le_div_of_nonneg_left h0 hp s2.le
  have h2 : empR (2 * m) z / √(2 * Real.pi) ≤
      (∫ x in (0 : ℝ)..z, Real.exp (-(x ^ 2 / 2))) / √(2 * Real.pi) := by gcongr
  have h3 : 2 * (∫ x in (0 : ℝ)..z, Real.exp (-(x ^ 2 / 2))) / √(2 * Real.pi) / 2 =
      (∫ x in (0 : ℝ)..z, Real.exp (-(x ^ 2 / 2))) / √(2 * Real.pi) := by ring
  rw [h3]
  linarith

/-- Upper enclosure for `Φ`. -/
private lemma Phi_lt {z c : ℝ} (hz : 0 ≤ z) (m : ℕ) (h0 : 0 ≤ empR (2 * m + 1) z)
    (h : 1 / 2 + empR (2 * m + 1) z / 2.5066 < c) : Φ z < c := by
  rw [stdNormalCdf_eq_Ioo hz, gaussianReal_real_Ioo_eq hz]
  have hu := integral_gauss_le m hz
  have s1 := sqrt_two_pi_gt
  have s2 := sqrt_two_pi_lt
  have hp : 0 < √(2 * Real.pi) := by linarith
  have h1 : (∫ x in (0 : ℝ)..z, Real.exp (-(x ^ 2 / 2))) / √(2 * Real.pi) ≤
      empR (2 * m + 1) z / √(2 * Real.pi) := by gcongr
  have h2 : empR (2 * m + 1) z / √(2 * Real.pi) ≤ empR (2 * m + 1) z / 2.5066 :=
    div_le_div_of_nonneg_left h0 (by norm_num) s1.le
  have h3 : 2 * (∫ x in (0 : ℝ)..z, Real.exp (-(x ^ 2 / 2))) / √(2 * Real.pi) / 2 =
      (∫ x in (0 : ℝ)..z, Real.exp (-(x ^ 2 / 2))) / √(2 * Real.pi) := by ring
  rw [h3]
  linarith

private lemma q_bounds {p zl zh : ℝ} (h0 : 0 < p) (h1 : p < 1) (hl : Φ zl < p) (hh : p < Φ zh) :
    zl < normalQuantile p ∧ normalQuantile p < zh := by
  have e := (stdNormalCdf_normalQuantile h0 h1).1
  exact ⟨cdf_gaussianReal_strictMono.lt_iff_lt.1 (by rw [e]; exact hl),
    cdf_gaussianReal_strictMono.lt_iff_lt.1 (by rw [e]; exact hh)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma percentile_bounds {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) {p zl zh : ℝ} (h0 : 0 < p) (h1 : p < 1)
    (hl : Φ zl < p) (hh : p < Φ zh) {k : ℝ} (hk : P.real {ω | X ω ≤ k} = p) :
    μ + σ * zl < k ∧ k < μ + σ * zh := by
  have e := (normal_percentile hσ hX h0 h1).2 k hk
  have q := q_bounds h0 h1 hl hh
  have a := mul_lt_mul_of_pos_left q.1 hσ
  have b := mul_lt_mul_of_pos_left q.2 hσ
  rw [e]
  constructor <;> linarith

private lemma prob_gt_normal [IsProbabilityMeasure P] {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    P.real {ω | x < X ω} = 1 - Φ ((x - μ) / σ) := by
  have hZ := standardized_hasLaw hσ hX
  have e : {ω | x < X ω} = (fun ω ↦ (X ω - μ) / σ) ⁻¹' Ioi ((x - μ) / σ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
    rw [div_lt_div_iff_of_pos_right hσ]
    constructor <;> intro h <;> linarith
  rw [e, real_preimage_of_hasLaw hZ measurableSet_Ioi, ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]

end Helpers

/-! ### Section 6.1: z-scores and the empirical rule -/

/-- OpenStax Introductory Statistics 2e Example 6.1. For `X ~ N(5, 6²)`: `x = 17` has z-score `2`
(and `5 + 2 · 6 = 17`), `x = 1` has z-score `-2/3`, which the book rounds to `-0.67`; and the
standardized variable `(X - 5)/6` is standard normal. -/
@[kb "openstaxintrostats2e" "Example 6.1, p. 348"]
theorem example_6_1_z_scores {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 5 ((6 : ℝ) ^ 2).toNNReal) P) :
    ((17 - 5) / 6 = (2 : ℝ) ∧ 5 + 2 * 6 = (17 : ℝ)) ∧
    ((1 - 5) / 6 = -(2 / 3 : ℝ) ∧ -0.675 < (1 - 5) / (6 : ℝ) ∧ (1 - 5) / (6 : ℝ) < -0.665 ∧
      |5 + (-0.67) * 6 - (1 : ℝ)| < 0.05) ∧
    HasLaw (fun ω ↦ (X ω - 5) / 6) (gaussianReal 0 1) P := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num, ?_⟩,
    standardized_hasLaw (by norm_num) hX⟩
  rw [abs_lt]; constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 6.2. Z-scores for weight change `X ~ N(5, 2²)`:
`x = 10` gives `2.5`, `x = -3` gives `-4`, and for `Y ~ N(2, 1²)` the value `y = 4` has z-score `2`,
the same as `x = 17` for `N(5, 6²)`. -/
@[kb "openstaxintrostats2e" "Example 6.2, p. 349"]
theorem example_6_2_z_scores :
    (10 - 5) / 2 = (5 / 2 : ℝ) ∧ (-3 - 5) / 2 = (-4 : ℝ) ∧ (4 - 2) / 1 = (2 : ℝ) ∧
      (4 - 2) / 1 = ((17 - 5) / 6 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 6.3. Heights `X ~ N(170, 6.28²)` (cm): `x = 168` has
z-score `-2/6.28`, about `-0.32` as in the book, and a z-score of `1.27` corresponds to
`170 + 1.27 · 6.28 = 177.9756` cm, which the book rounds to `177.98`. -/
@[kb "openstaxintrostats2e" "Example 6.3, p. 350"]
theorem example_6_3_height_z_scores :
    (-0.325 < (168 - 170) / (6.28 : ℝ) ∧ (168 - 170) / (6.28 : ℝ) < -0.315) ∧
      (170 + 1.27 * 6.28 = (177.9756 : ℝ) ∧ 177.975 < 170 + 1.27 * (6.28 : ℝ) ∧
        170 + 1.27 * (6.28 : ℝ) < 177.985) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 6.4. The height `x = 160.58` under `N(170, 6.28²)` and
the height `y = 162.85` under `N(172.36, 6.34²)` both have z-score exactly `-1.5`, so they lie the
same number of standard deviations below their respective means. -/
@[kb "openstaxintrostats2e" "Example 6.4, p. 351"]
theorem example_6_4_equal_z_scores :
    (160.58 - 170) / (6.28 : ℝ) = -1.5 ∧ (162.85 - 172.36) / (6.34 : ℝ) = -1.5 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 6.5. For `X ~ N(50, 6²)`, the endpoints at one, two and
three standard deviations are `44, 56`, `38, 62` and `32, 68`, with z-scores `±1, ±2, ±3`; and the
probabilities of the three intervals lie in `(0.68, 0.69)`, `(0.95, 0.96)`, `(0.997, 0.998)`
(the book says "about 68%, 95%, 99.7%"). -/
@[kb "openstaxintrostats2e" "Example 6.5, p. 351"]
theorem example_6_5_empirical_rule {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 50 ((6 : ℝ) ^ 2).toNNReal) P) :
    ((50 - 6 = (44 : ℝ) ∧ 50 + 6 = (56 : ℝ)) ∧ (50 - 2 * 6 = (38 : ℝ) ∧ 50 + 2 * 6 = (62 : ℝ)) ∧
      (50 - 3 * 6 = (32 : ℝ) ∧ 50 + 3 * 6 = (68 : ℝ))) ∧
    ((44 - 50) / 6 = (-1 : ℝ) ∧ (56 - 50) / 6 = (1 : ℝ) ∧ (38 - 50) / 6 = (-2 : ℝ) ∧
      (62 - 50) / 6 = (2 : ℝ) ∧ (32 - 50) / 6 = (-3 : ℝ) ∧ (68 - 50) / 6 = (3 : ℝ)) ∧
    ((0.68 : ℝ) < P.real {ω | X ω ∈ Ioo (50 - 6) (50 + 6)} ∧
      P.real {ω | X ω ∈ Ioo (50 - 6) (50 + 6)} < 0.69) ∧
    ((0.95 : ℝ) < P.real {ω | X ω ∈ Ioo (50 - 2 * 6) (50 + 2 * 6)} ∧
      P.real {ω | X ω ∈ Ioo (50 - 2 * 6) (50 + 2 * 6)} < 0.96) ∧
    ((0.997 : ℝ) < P.real {ω | X ω ∈ Ioo (50 - 3 * 6) (50 + 3 * 6)} ∧
      P.real {ω | X ω ∈ Ioo (50 - 3 * 6) (50 + 3 * 6)} < 0.998) := by
  have emp := empirical_rule_normal_population (μ := 50) (σ := 6) (by norm_num) hX
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, emp⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 6.6. For heights `Y ~ N(172.36, 6.34²)`, the endpoints
at one, two, three standard deviations from the mean are `166.02, 178.7`, `159.68, 185.04` and
`153.34, 191.38`, with z-scores `±1, ±2, ±3`. -/
@[kb "openstaxintrostats2e" "Example 6.6, p. 352"]
theorem example_6_6_endpoints :
    ((172.36 - 6.34 = (166.02 : ℝ) ∧ 172.36 + 6.34 = (178.7 : ℝ)) ∧
      (172.36 - 2 * 6.34 = (159.68 : ℝ) ∧ 172.36 + 2 * 6.34 = (185.04 : ℝ)) ∧
      (172.36 - 3 * 6.34 = (153.34 : ℝ) ∧ 172.36 + 3 * 6.34 = (191.38 : ℝ))) ∧
    ((166.02 - 172.36) / (6.34 : ℝ) = -1 ∧ (178.7 - 172.36) / (6.34 : ℝ) = 1 ∧
      (159.68 - 172.36) / (6.34 : ℝ) = -2 ∧ (185.04 - 172.36) / (6.34 : ℝ) = 2 ∧
      (153.34 - 172.36) / (6.34 : ℝ) = -3 ∧ (191.38 - 172.36) / (6.34 : ℝ) = 3) := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- OpenStax Introductory Statistics 2e Example 6.6 (probabilities). For `Y ~ N(172.36, 6.34²)`, the
probabilities of lying within one, two, three standard deviations of the mean lie in
`(0.68, 0.69)`, `(0.95, 0.96)`, `(0.997, 0.998)`; the book says about 68%, 95%, 99.7%. -/
@[kb "openstaxintrostats2e" "Example 6.6, p. 352"]
theorem example_6_6_probabilities {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    (hY : HasLaw Y (gaussianReal 172.36 ((6.34 : ℝ) ^ 2).toNNReal) P) :
    ((0.68 : ℝ) < P.real {ω | Y ω ∈ Ioo (172.36 - 6.34) (172.36 + 6.34)} ∧
      P.real {ω | Y ω ∈ Ioo (172.36 - 6.34) (172.36 + 6.34)} < 0.69) ∧
    ((0.95 : ℝ) < P.real {ω | Y ω ∈ Ioo (172.36 - 2 * 6.34) (172.36 + 2 * 6.34)} ∧
      P.real {ω | Y ω ∈ Ioo (172.36 - 2 * 6.34) (172.36 + 2 * 6.34)} < 0.96) ∧
    ((0.997 : ℝ) < P.real {ω | Y ω ∈ Ioo (172.36 - 3 * 6.34) (172.36 + 3 * 6.34)} ∧
      P.real {ω | Y ω ∈ Ioo (172.36 - 3 * 6.34) (172.36 + 3 * 6.34)} < 0.998) :=
  empirical_rule_normal_population (μ := 172.36) (σ := 6.34) (by norm_num) hY

/-! ### Section 6.2: using the normal distribution -/

/-- OpenStax Introductory Statistics 2e Example 6.7. If the area to the left is `0.0228`, the area to
the right is `1 - 0.0228 = 0.9772`. In probability terms: for a normal `X` the right tail is
one minus the left tail, `P(X > x) = 1 - P(X ≤ x)`; and for the standard normal, `Φ(-2)` is within
`0.0001` of `0.0228` while `1 - Φ(-2) = Φ(2)` is within `0.0001` of `0.9772`. -/
@[kb "openstaxintrostats2e" "Example 6.7, p. 353"]
theorem example_6_7_complement {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    (1 - 0.0228 = (0.9772 : ℝ)) ∧ P.real {ω | x < X ω} = 1 - P.real {ω | X ω ≤ x} ∧
      ((0.0227 : ℝ) < Φ (-2) ∧ Φ (-2) < 0.0229) ∧
      ((0.9771 : ℝ) < 1 - Φ (-2) ∧ 1 - Φ (-2) < 0.9773) := by
  have g := Phi_gt (z := 2) (c := 0.9771) (by norm_num) 10 (by emp_num) (by emp_num)
  have l := Phi_lt (z := 2) (c := 0.9773) (by norm_num) 10 (by emp_num) (by emp_num)
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [prob_gt_normal hσ hX, prob_le_normal hσ hX]
  · rw [stdNormalCdf_neg]; constructor <;> linarith
  · rw [stdNormalCdf_neg]; constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Example 6.8, part a. Exam scores `X ~ N(63, 5²)`: the
probability of a score above `65` (z-score `0.4`) lies in `(0.3445, 0.3447)`; the book gives `0.3446`. -/
@[kb "openstaxintrostats2e" "Example 6.8, p. 353"]
theorem example_6_8a_more_than_65 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 63 ((5 : ℝ) ^ 2).toNNReal) P) :
    (0.3445 : ℝ) < P.real {ω | 65 < X ω} ∧ P.real {ω | 65 < X ω} < 0.3447 := by
  rw [prob_gt_normal (by norm_num) hX]
  have e : ((65 : ℝ) - 63) / 5 = 0.4 := by norm_num
  rw [e]
  have g := Phi_gt (z := 0.4) (c := 0.6553) (by norm_num) 10 (by emp_num) (by emp_num)
  have l := Phi_lt (z := 0.4) (c := 0.6555) (by norm_num) 10 (by emp_num) (by emp_num)
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Example 6.8, part b. The probability that a score is at most `85`
(z-score `4.4`) is at least `0.998` and below `1`; the book rounds it to `1`. -/
@[kb "openstaxintrostats2e" "Example 6.8, p. 353"]
theorem example_6_8b_less_than_85 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 63 ((5 : ℝ) ^ 2).toNNReal) P) :
    (0.998 : ℝ) < P.real {ω | X ω ≤ 85} ∧ P.real {ω | X ω ≤ 85} < 1 := by
  rw [prob_le_normal (by norm_num) hX]
  have g := Phi_gt (z := 3) (c := 0.998) (by norm_num) 16 (by emp_num) (by emp_num)
  have mono : Φ 3 ≤ Φ (((85 : ℝ) - 63) / 5) :=
    cdf_gaussianReal_strictMono.monotone (by norm_num)
  exact ⟨by linarith, (stdNormalCdf_properties.2.2.2.2 _).2⟩

/-- OpenStax Introductory Statistics 2e Example 6.8, part c. For `X ~ N(63, 5²)`, any `k` with
`P(X ≤ k) = 0.9` (the 90th percentile) lies in `(69.35, 69.45)`; the book gives `69.4`. -/
@[kb "openstaxintrostats2e" "Example 6.8, p. 353"]
theorem example_6_8c_percentile_90 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 63 ((5 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 9 / 10) : 69.35 < k ∧ k < 69.45 := by
  have l := Phi_lt (z := 1.27) (c := 9 / 10) (by norm_num) 10 (by emp_num) (by emp_num)
  have g := Phi_gt (z := 1.29) (c := 9 / 10) (by norm_num) 10 (by emp_num) (by emp_num)
  have := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Example 6.8, part d. For `X ~ N(63, 5²)`, any `k` with
`P(X ≤ k) = 0.7` (the 70th percentile) lies in `(65.55, 65.65)`; the book gives `65.6`. -/
@[kb "openstaxintrostats2e" "Example 6.8, p. 353"]
theorem example_6_8d_percentile_70 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 63 ((5 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 7 / 10) : 65.55 < k ∧ k < 65.65 := by
  have l := Phi_lt (z := 0.51) (c := 7 / 10) (by norm_num) 10 (by emp_num) (by emp_num)
  have g := Phi_gt (z := 0.53) (c := 7 / 10) (by norm_num) 10 (by emp_num) (by emp_num)
  have := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Example 6.9, part a. Daily entertainment time `X ~ N(2, 0.5²)`
hours: the probability of between `1.8` and `2.75` hours (the upper end included; the difference is
a null set) lies in `(0.5885, 0.5887)`; the book gives `0.5886`. -/
@[kb "openstaxintrostats2e" "Example 6.9, p. 355"]
theorem example_6_9a_between {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 2 ((0.5 : ℝ) ^ 2).toNNReal) P) :
    (0.5885 : ℝ) < P.real {ω | 1.8 < X ω ∧ X ω ≤ 2.75} ∧
      P.real {ω | 1.8 < X ω ∧ X ω ≤ 2.75} < 0.5887 := by
  rw [prob_Ioc_normal (by norm_num) hX _ _ (by norm_num)]
  have e1 : ((2.75 : ℝ) - 2) / 0.5 = 1.5 := by norm_num
  have e2 : ((1.8 : ℝ) - 2) / 0.5 = -0.4 := by norm_num
  rw [e1, e2, stdNormalCdf_neg]
  have g1 := Phi_gt (z := 1.5) (c := 0.93317) (by norm_num) 10 (by emp_num) (by emp_num)
  have l1 := Phi_lt (z := 1.5) (c := 0.93322) (by norm_num) 10 (by emp_num) (by emp_num)
  have g2 := Phi_gt (z := 0.4) (c := 0.6554) (by norm_num) 10 (by emp_num) (by emp_num)
  have l2 := Phi_lt (z := 0.4) (c := 0.65545) (by norm_num) 10 (by emp_num) (by emp_num)
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Example 6.9, part b. For `X ~ N(2, 0.5²)`, any `k` with
`P(X ≤ k) = 0.25` (the bottom quartile bound) lies in `(1.655, 1.665)`; the book gives `1.66`. -/
@[kb "openstaxintrostats2e" "Example 6.9, p. 355"]
theorem example_6_9b_bottom_quartile {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 2 ((0.5 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 1 / 4) : 1.655 < k ∧ k < 1.665 := by
  have g := Phi_gt (z := 0.69) (c := 3 / 4) (by norm_num) 10 (by emp_num) (by emp_num)
  have l := Phi_lt (z := 0.67) (c := 3 / 4) (by norm_num) 10 (by emp_num) (by emp_num)
  have l' : Φ (-0.69) < 1 / 4 := by rw [stdNormalCdf_neg]; linarith
  have g' : 1 / 4 < Φ (-0.67) := by rw [stdNormalCdf_neg]; linarith
  have := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l' g' hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Example 6.10, part a. Smartphone-user ages `X ~ N(36.9, 13.9²)`:
the probability of an age in `(23, 64.7]` (z-scores `-1` and `2`) lies in `(0.8185, 0.8187)`;
the book gives `0.8186`. -/
@[kb "openstaxintrostats2e" "Example 6.10, p. 356"]
theorem example_6_10a_between {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 36.9 ((13.9 : ℝ) ^ 2).toNNReal) P) :
    (0.8185 : ℝ) < P.real {ω | 23 < X ω ∧ X ω ≤ 64.7} ∧
      P.real {ω | 23 < X ω ∧ X ω ≤ 64.7} < 0.8187 := by
  rw [prob_Ioc_normal (by norm_num) hX _ _ (by norm_num)]
  have e1 : ((64.7 : ℝ) - 36.9) / 13.9 = 2 := by norm_num
  have e2 : ((23 : ℝ) - 36.9) / 13.9 = -1 := by norm_num
  rw [e1, e2, stdNormalCdf_neg]
  have g1 := Phi_gt (z := 2) (c := 0.97722) (by norm_num) 10 (by emp_num) (by emp_num)
  have l1 := Phi_lt (z := 2) (c := 0.97728) (by norm_num) 10 (by emp_num) (by emp_num)
  have g2 := Phi_gt (z := 1) (c := 0.84131) (by norm_num) 10 (by emp_num) (by emp_num)
  have l2 := Phi_lt (z := 1) (c := 0.84138) (by norm_num) 10 (by emp_num) (by emp_num)
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Example 6.10, part b. The probability that an age is at most
`50.8` (z-score `1`) lies in `(0.8412, 0.8414)`; the book gives `0.8413`. -/
@[kb "openstaxintrostats2e" "Example 6.10, p. 356"]
theorem example_6_10b_at_most {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 36.9 ((13.9 : ℝ) ^ 2).toNNReal) P) :
    (0.8412 : ℝ) < P.real {ω | X ω ≤ 50.8} ∧ P.real {ω | X ω ≤ 50.8} < 0.8414 := by
  rw [prob_le_normal (by norm_num) hX]
  have e : ((50.8 : ℝ) - 36.9) / 13.9 = 1 := by norm_num
  rw [e]
  have g := Phi_gt (z := 1) (c := 0.8412) (by norm_num) 10 (by emp_num) (by emp_num)
  have l := Phi_lt (z := 1) (c := 0.8414) (by norm_num) 10 (by emp_num) (by emp_num)
  exact ⟨g, l⟩

/-- OpenStax Introductory Statistics 2e Example 6.10, part c. For `X ~ N(36.9, 13.9²)`, any `k` with
`P(X ≤ k) = 0.8` (the 80th percentile) lies in `(48.55, 48.65)`; the book gives `48.6` years. -/
@[kb "openstaxintrostats2e" "Example 6.10, p. 356"]
theorem example_6_10c_percentile_80 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 36.9 ((13.9 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 4 / 5) : 48.55 < k ∧ k < 48.65 := by
  have l := Phi_lt (z := 0.839) (c := 4 / 5) (by norm_num) 10 (by emp_num) (by emp_num)
  have g := Phi_gt (z := 0.845) (c := 4 / 5) (by norm_num) 10 (by emp_num) (by emp_num)
  have := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Example 6.11, part a. For ages `X ~ N(36.9, 13.9²)`, the
quartiles `Q1` (with `P(X ≤ Q1) = 1/4`) and `Q3` (with `P(X ≤ Q3) = 3/4`) have interquartile range
in `(18.7, 18.9)`; the book gives `18.8`. -/
@[kb "openstaxintrostats2e" "Example 6.11, p. 357"]
theorem example_6_11a_iqr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 36.9 ((13.9 : ℝ) ^ 2).toNNReal) P) {Q1 Q3 : ℝ}
    (h1 : P.real {ω | X ω ≤ Q1} = 1 / 4) (h3 : P.real {ω | X ω ≤ Q3} = 3 / 4) :
    18.7 < Q3 - Q1 ∧ Q3 - Q1 < 18.9 := by
  have l := Phi_lt (z := 0.673) (c := 3 / 4) (by norm_num) 10 (by emp_num) (by emp_num)
  have g := Phi_gt (z := 0.679) (c := 3 / 4) (by norm_num) 10 (by emp_num) (by emp_num)
  have l' : Φ (-0.679) < 1 / 4 := by rw [stdNormalCdf_neg]; linarith
  have g' : 1 / 4 < Φ (-0.673) := by rw [stdNormalCdf_neg]; linarith
  have a := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l g h3
  have b := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l' g' h1
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- OpenStax Introductory Statistics 2e Example 6.11, part b. Forty percent of ages are at least `k`:
if `P(X ≥ k)`, equivalently `P(X > k)`, equals `0.4` for `X ~ N(36.9, 13.9²)` then `k` lies in
`(40.35, 40.45)`; the book gives `40.4`. -/
@[kb "openstaxintrostats2e" "Example 6.11, p. 357"]
theorem example_6_11b_at_least {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 36.9 ((13.9 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | k < X ω} = 2 / 5) : 40.35 < k ∧ k < 40.45 := by
  have hk' : P.real {ω | X ω ≤ k} = 3 / 5 := by
    have := prob_gt_normal (by norm_num) hX k
    rw [prob_le_normal (by norm_num) hX]
    linarith
  have l := Phi_lt (z := 0.2485) (c := 3 / 5) (by norm_num) 10 (by emp_num) (by emp_num)
  have g := Phi_gt (z := 0.2553) (c := 3 / 5) (by norm_num) 10 (by emp_num) (by emp_num)
  have := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l g hk'
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Example 6.12, part a. Orange diameters `X ~ N(5.85, 0.24²)` cm:
the probability of a diameter above `6.0` (z-score `0.625`) lies in `(0.2659, 0.2661)`; the book gives
`0.2660`. -/
@[kb "openstaxintrostats2e" "Example 6.12, p. 358"]
theorem example_6_12a_larger_than_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 5.85 ((0.24 : ℝ) ^ 2).toNNReal) P) :
    (0.2659 : ℝ) < P.real {ω | 6.0 < X ω} ∧ P.real {ω | 6.0 < X ω} < 0.2661 := by
  rw [prob_gt_normal (by norm_num) hX]
  have e : ((6.0 : ℝ) - 5.85) / 0.24 = 0.625 := by norm_num
  rw [e]
  have g := Phi_gt (z := 0.625) (c := 0.7339) (by norm_num) 10 (by emp_num) (by emp_num)
  have l := Phi_lt (z := 0.625) (c := 0.7341) (by norm_num) 10 (by emp_num) (by emp_num)
  constructor <;> linarith

/-- OpenStax Introductory Statistics 2e Example 6.12, part b. The middle 20% of diameters lie between
the 40th percentile `k1` (`P(X ≤ k1) = 0.4`) and the 60th percentile `k2` (`P(X ≤ k2) = 0.6`): `k1`
lies in `(5.785, 5.795)` and `k2` in `(5.905, 5.915)` (the book gives `5.79` and `5.91`), and
`P(k1 < X ≤ k2) = 1/5`. -/
@[kb "openstaxintrostats2e" "Example 6.12, p. 358"]
theorem example_6_12b_middle_20 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 5.85 ((0.24 : ℝ) ^ 2).toNNReal) P) {k1 k2 : ℝ}
    (h1 : P.real {ω | X ω ≤ k1} = 2 / 5) (h2 : P.real {ω | X ω ≤ k2} = 3 / 5) :
    (5.785 < k1 ∧ k1 < 5.795) ∧ (5.905 < k2 ∧ k2 < 5.915) ∧
      P.real {ω | k1 < X ω ∧ X ω ≤ k2} = 1 / 5 := by
  have l := Phi_lt (z := 0.2292) (c := 3 / 5) (by norm_num) 10 (by emp_num) (by emp_num)
  have g := Phi_gt (z := 0.2708) (c := 3 / 5) (by norm_num) 10 (by emp_num) (by emp_num)
  have l' : Φ (-0.2708) < 2 / 5 := by rw [stdNormalCdf_neg]; linarith
  have g' : 2 / 5 < Φ (-0.2292) := by rw [stdNormalCdf_neg]; linarith
  have a := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l g h2
  have b := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l' g' h1
  have hle : k1 ≤ k2 := by linarith [a.1, b.2]
  refine ⟨⟨by linarith [b.1], by linarith [b.2]⟩, ⟨by linarith [a.1], by linarith [a.2]⟩, ?_⟩
  rw [prob_Ioc_normal (by norm_num) hX _ _ hle]
  have e1 := prob_le_normal (by norm_num) hX k1
  have e2 := prob_le_normal (by norm_num) hX k2
  linarith

/-- OpenStax Introductory Statistics 2e Example 6.12, part c. For `X ~ N(5.85, 0.24²)`, any `k` with
`P(X ≤ k) = 0.9` (the 90th percentile) lies in `(6.155, 6.165)`; the book gives `6.16` cm. -/
@[kb "openstaxintrostats2e" "Example 6.12, p. 358"]
theorem example_6_12c_percentile_90 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 5.85 ((0.24 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 9 / 10) : 6.155 < k ∧ k < 6.165 := by
  have l := Phi_lt (z := 1.271) (c := 9 / 10) (by norm_num) 10 (by emp_num) (by emp_num)
  have g := Phi_gt (z := 1.312) (c := 9 / 10) (by norm_num) 10 (by emp_num) (by emp_num)
  have := percentile_bounds (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

end UndergradKB.Statistics.Course.ExamplesC6
