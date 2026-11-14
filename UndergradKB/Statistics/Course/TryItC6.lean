import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.Course.ExamplesC7

/-!
# "Try It" exercises, chapter 6 (OpenStax *Introductory Statistics 2e*): the normal distribution

Z-scores (exact arithmetic), the empirical rule, and normal probabilities and percentiles for a
variable `X` with `HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P`.  Rounded calculator values of the
book are replaced by two-sided bounds, obtained by reducing to the standard normal distribution
function `Φ` and enclosing `Φ` by the alternating Taylor sums of `EmpiricalRule.lean`
(`Phi_enc` of `ExamplesC7.lean`).  Percentile exercises are stated for any `k` with `P(X ≤ k) = p`.
-/

namespace UndergradKB.Statistics.Course.TryItC6

open MeasureTheory ProbabilityTheory Set UndergradKB.Statistics
open UndergradKB.Statistics.Course.ExamplesC7

local notation "Φ" => cdf (gaussianReal 0 1)

/-! ### Values of `Φ` -/

private lemma tphi_1 : (0.84133 : ℝ) < Φ 1 ∧ Φ 1 < 0.84135 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_2_3 : (0.74749 : ℝ) < Φ (2 / 3) ∧ Φ (2 / 3) < 0.74752 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_524 : (0.69985 : ℝ) < Φ 0.524 ∧ Φ 0.524 < 0.69987 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_525 : (0.7002 : ℝ) < Φ 0.525 ∧ Φ 0.525 < 0.70022 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_7122 : (0.76181 : ℝ) < Φ 0.7122 ∧ Φ 0.7122 < 0.76184 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_7123 : (0.76184 : ℝ) < Φ 0.7123 ∧ Φ 0.7123 < 0.76187 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_674 : (0.74983 : ℝ) < Φ 0.674 ∧ Φ 0.674 < 0.74985 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_675 : (0.75015 : ℝ) < Φ 0.675 ∧ Φ 0.675 < 0.75017 :=
  Phi_enc (by norm_num) 2 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_994 : (0.83987 : ℝ) < Φ 0.994 ∧ Φ 0.994 < 0.8399 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

private lemma tphi_0_995 : (0.84012 : ℝ) < Φ 0.995 ∧ Φ 0.995 < 0.84014 :=
  Phi_enc (by norm_num) 3 (by norm_num)
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])
    (by simp only [empR, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Nat.factorial])

/-- A number `k` with `P(X ≤ k) = p` lies between the values given by `z`-scores `lo` and `hi`
whenever `Φ lo < p < Φ hi`. -/
private lemma pct {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {μ σ : ℝ}
    (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) {p lo hi : ℝ} (h0 : 0 < p)
    (h1 : p < 1) (hlo : Φ lo < p) (hhi : p < Φ hi) {k : ℝ} (hk : P.real {ω | X ω ≤ k} = p) :
    μ + σ * lo < k ∧ k < μ + σ * hi := by
  obtain ⟨k', hk', h1', h2'⟩ := percentile_bd hσ hX h0 h1 hlo hhi
  have e : k = k' := ((normal_percentile hσ hX h0 h1).2 k hk).trans
    ((normal_percentile hσ hX h0 h1).2 k' hk').symm
  rw [e]
  exact ⟨h1', h2'⟩

/-! ### Section 6.1: z-scores and the empirical rule -/

/-- OpenStax Introductory Statistics 2e Try It 6.1. For `X ~ N(12, 3²)`, the value `x = 1` has
z-score `-11/3`, strictly between `-3.67` and `-3.66`; and `(X - 12)/3` is standard normal. -/
@[kb "openstaxintrostats2e" "Try It 6.1, p. 349"]
theorem tryit_6_1_z_score {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 12 ((3 : ℝ) ^ 2).toNNReal) P) :
    ((1 - 12) / 3 = -(11 / 3 : ℝ) ∧ -3.67 < (1 - 12) / (3 : ℝ) ∧ (1 - 12) / (3 : ℝ) < -3.66) ∧
      HasLaw (fun ω ↦ (X ω - 12) / 3) (gaussianReal 0 1) P := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, standardized_hasLaw (by norm_num) hX⟩

/-- OpenStax Introductory Statistics 2e Try It 6.2. Jerome scores `10` when his average is `16` with
standard deviation `4`: the z-score is `-3/2`, so the score lies `1.5` standard deviations to the left
of the mean `16`. -/
@[kb "openstaxintrostats2e" "Try It 6.2, p. 349"]
theorem tryit_6_2_z_score : (10 - 16) / 4 = (-3 / 2 : ℝ) ∧ (16 : ℝ) + (-3 / 2) * 4 = 10 := by
  constructor <;> norm_num

/-- OpenStax Introductory Statistics 2e Try It 6.3. For heights `X ~ N(170, 6.28²)`: `x = 176` has
z-score `6/6.28`, strictly between `0.955` and `0.956` (to the right of the mean `170`); and a
z-score of `-2` corresponds to the height `170 - 2 · 6.28 = 157.44`. -/
@[kb "openstaxintrostats2e" "Try It 6.3, p. 350"]
theorem tryit_6_3_height_z_scores :
    ((176 - 170) / (6.28 : ℝ) = 6 / 6.28 ∧ 0.955 < (176 - 170) / (6.28 : ℝ) ∧
      (176 - 170) / (6.28 : ℝ) < 0.956) ∧ (170 + (-2) * 6.28 = (157.44 : ℝ)) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 6.4. SAT verbal scores `X ~ N(496, 114²)`: `x₁ = 325`
has z-score exactly `-3/2` and `x₂ = 366.21` has z-score `-129.79/114`, strictly between `-1.14` and
`-1.138`; both scores lie below the mean `496`, `x₁` by more standard deviations. -/
@[kb "openstaxintrostats2e" "Try It 6.4, p. 351"]
theorem tryit_6_4_sat_z_scores :
    (325 - 496) / (114 : ℝ) = -3 / 2 ∧ (366.21 - 496) / (114 : ℝ) = -129.79 / 114 ∧
      -1.14 < (366.21 - 496) / (114 : ℝ) ∧ (366.21 - 496) / (114 : ℝ) < -1.138 ∧
      (325 - 496) / (114 : ℝ) < (366.21 - 496) / 114 ∧ (366.21 - 496) / (114 : ℝ) < 0 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- OpenStax Introductory Statistics 2e Try It 6.5. For `X ~ N(25, 5²)`, the interval within one
standard deviation of the mean is `(20, 30)`, and the probability of lying in it lies in
`(0.68, 0.69)`: about 68% of the values lie between 20 and 30. -/
@[kb "openstaxintrostats2e" "Try It 6.5, p. 351"]
theorem tryit_6_5_empirical_rule_68 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 25 ((5 : ℝ) ^ 2).toNNReal) P) :
    (25 - 5 = (20 : ℝ) ∧ 25 + 5 = (30 : ℝ)) ∧
      ((0.68 : ℝ) < P.real {ω | X ω ∈ Ioo (25 - 5) (25 + 5)} ∧
        P.real {ω | X ω ∈ Ioo (25 - 5) (25 + 5)} < 0.69) := by
  have emp := empirical_rule_normal_population (μ := 25) (σ := 5) (by norm_num) hX
  exact ⟨⟨by norm_num, by norm_num⟩, emp.1⟩

/-- OpenStax Introductory Statistics 2e Try It 6.6. For exam scores `Y ~ N(52, 11²)`, the endpoints at
one, two and three standard deviations are `41, 63`, `30, 74` and `19, 85`, with z-scores `±1, ±2, ±3`;
the probabilities of the three intervals lie in `(0.68, 0.69)`, `(0.95, 0.96)`, `(0.997, 0.998)`. -/
@[kb "openstaxintrostats2e" "Try It 6.6, p. 352"]
theorem tryit_6_6_empirical_rule {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    (hY : HasLaw Y (gaussianReal 52 ((11 : ℝ) ^ 2).toNNReal) P) :
    ((52 - 11 = (41 : ℝ) ∧ 52 + 11 = (63 : ℝ)) ∧ (52 - 2 * 11 = (30 : ℝ) ∧ 52 + 2 * 11 = (74 : ℝ)) ∧
      (52 - 3 * 11 = (19 : ℝ) ∧ 52 + 3 * 11 = (85 : ℝ))) ∧
    ((41 - 52) / 11 = (-1 : ℝ) ∧ (63 - 52) / 11 = (1 : ℝ) ∧ (30 - 52) / 11 = (-2 : ℝ) ∧
      (74 - 52) / 11 = (2 : ℝ) ∧ (19 - 52) / 11 = (-3 : ℝ) ∧ (85 - 52) / 11 = (3 : ℝ)) ∧
    ((0.68 : ℝ) < P.real {ω | Y ω ∈ Ioo (52 - 11) (52 + 11)} ∧
      P.real {ω | Y ω ∈ Ioo (52 - 11) (52 + 11)} < 0.69) ∧
    ((0.95 : ℝ) < P.real {ω | Y ω ∈ Ioo (52 - 2 * 11) (52 + 2 * 11)} ∧
      P.real {ω | Y ω ∈ Ioo (52 - 2 * 11) (52 + 2 * 11)} < 0.96) ∧
    ((0.997 : ℝ) < P.real {ω | Y ω ∈ Ioo (52 - 3 * 11) (52 + 3 * 11)} ∧
      P.real {ω | Y ω ∈ Ioo (52 - 3 * 11) (52 + 3 * 11)} < 0.998) := by
  have emp := empirical_rule_normal_population (μ := 52) (σ := 11) (by norm_num) hY
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, emp⟩ <;> norm_num

/-! ### Section 6.2: using the normal distribution -/

/-- OpenStax Introductory Statistics 2e Try It 6.7. If the area to the left of `x` is `0.012`, the
area to the right is `1 - 0.012 = 0.988`; in probability terms, for a normal `X`,
`P(X > x) = 1 - P(X ≤ x)`. -/
@[kb "openstaxintrostats2e" "Try It 6.7, p. 353"]
theorem tryit_6_7_complement {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    (1 - 0.012 = (0.988 : ℝ)) ∧ P.real {ω | x < X ω} = 1 - P.real {ω | X ω ≤ x} := by
  refine ⟨by norm_num, ?_⟩
  rw [prob_gt hσ hX, prob_le_normal hσ hX]

/-- OpenStax Introductory Statistics 2e Try It 6.8. Golf scores `X ~ N(68, 3²)`: the probability of a
score below 65 (z-score `-1`) lies in `(0.1586, 0.1588)`. -/
@[kb "openstaxintrostats2e" "Try It 6.8, p. 355"]
theorem tryit_6_8_golf_less_than_65 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 68 ((3 : ℝ) ^ 2).toNNReal) P) :
    (0.1586 : ℝ) < P.real {ω | X ω < 65} ∧ P.real {ω | X ω < 65} < 0.1588 := by
  rw [prob_lt (by norm_num) hX]
  have e : ((65 : ℝ) - 68) / 3 = -1 := by norm_num
  rw [e, stdNormalCdf_neg]
  constructor <;> linarith [tphi_1.1, tphi_1.2]

/-- OpenStax Introductory Statistics 2e Try It 6.9. Golf scores `X ~ N(68, 3²)`: the probability of a
score between 66 and 70 (z-scores `∓2/3`) lies in `(0.4949, 0.4951)`. -/
@[kb "openstaxintrostats2e" "Try It 6.9, p. 356"]
theorem tryit_6_9_golf_between {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 68 ((3 : ℝ) ^ 2).toNNReal) P) :
    (0.4949 : ℝ) < P.real {ω | 66 < X ω ∧ X ω < 70} ∧
      P.real {ω | 66 < X ω ∧ X ω < 70} < 0.4951 := by
  rw [prob_Ioo (by norm_num) hX (a := 66) (b := 70) (by norm_num)]
  have e1 : ((70 : ℝ) - 68) / 3 = 2 / 3 := by norm_num
  have e2 : ((66 : ℝ) - 68) / 3 = -(2 / 3) := by norm_num
  rw [e1, e2, stdNormalCdf_neg]
  constructor <;> linarith [tphi_2_3.1, tphi_2_3.2]

/-- OpenStax Introductory Statistics 2e Try It 6.10(a). For ages `X ~ N(36.9, 13.9²)`, any `k` with
`P(X ≤ k) = 0.3` (the 30th percentile) lies in `(29.6, 29.62)`; the book's value is about `29.6` years. -/
@[kb "openstaxintrostats2e" "Try It 6.10, p. 357"]
theorem tryit_6_10a_percentile_30 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 36.9 ((13.9 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 3 / 10) : 29.6 < k ∧ k < 29.62 := by
  have l : Φ (-0.525) < 3 / 10 := by rw [stdNormalCdf_neg]; linarith [tphi_0_525.1]
  have g : 3 / 10 < Φ (-0.524) := by rw [stdNormalCdf_neg]; linarith [tphi_0_524.2]
  have := pct (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

/-- OpenStax Introductory Statistics 2e Try It 6.10(b). For ages `X ~ N(36.9, 13.9²)`, the probability
of an age below 27 (z-score `-99/139`) lies in `(0.2381, 0.2382)`. -/
@[kb "openstaxintrostats2e" "Try It 6.10, p. 357"]
theorem tryit_6_10b_less_than_27 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 36.9 ((13.9 : ℝ) ^ 2).toNNReal) P) :
    (0.2381 : ℝ) < P.real {ω | X ω < 27} ∧ P.real {ω | X ω < 27} < 0.2382 := by
  rw [prob_lt (by norm_num) hX]
  have e : ((27 : ℝ) - 36.9) / 13.9 = -(99 / 139) := by norm_num
  rw [e, stdNormalCdf_neg]
  have h := Phi_between (z := 99 / 139) (lo := 0.7122) (hi := 0.7123) (by norm_num) (by norm_num)
    tphi_0_7122.1 tphi_0_7123.2
  constructor <;> linarith [h.1, h.2]

/-- OpenStax Introductory Statistics 2e Try It 6.11(a). For exam scores `X ~ N(81, 15²)`, any first
quartile `Q1` (with `P(X ≤ Q1) = 1/4`) lies in `(70.87, 70.89)` and any third quartile `Q3` in
`(91.11, 91.13)`; the book's values are about `70.9` and `91.1`. -/
@[kb "openstaxintrostats2e" "Try It 6.11, p. 358"]
theorem tryit_6_11a_quartiles {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 81 ((15 : ℝ) ^ 2).toNNReal) P) {Q1 Q3 : ℝ}
    (h1 : P.real {ω | X ω ≤ Q1} = 1 / 4) (h3 : P.real {ω | X ω ≤ Q3} = 3 / 4) :
    (70.87 < Q1 ∧ Q1 < 70.89) ∧ (91.11 < Q3 ∧ Q3 < 91.13) := by
  have l : Φ 0.674 < 3 / 4 := by linarith [tphi_0_674.2]
  have g : 3 / 4 < Φ 0.675 := by linarith [tphi_0_675.1]
  have l' : Φ (-0.675) < 1 / 4 := by rw [stdNormalCdf_neg]; linarith [tphi_0_675.1]
  have g' : 1 / 4 < Φ (-0.674) := by rw [stdNormalCdf_neg]; linarith [tphi_0_674.2]
  have a := pct (by norm_num) hX (by norm_num) (by norm_num) l g h3
  have b := pct (by norm_num) hX (by norm_num) (by norm_num) l' g' h1
  refine ⟨⟨by linarith [b.1], by linarith [b.2]⟩, ⟨by linarith [a.1], by linarith [a.2]⟩⟩

/-- OpenStax Introductory Statistics 2e Try It 6.11(b). The middle half of the scores lies between
the quartiles: for `X ~ N(81, 15²)` and `Q1`, `Q3` as above, `P(Q1 < X ≤ Q3) = 1/2`. -/
@[kb "openstaxintrostats2e" "Try It 6.11, p. 358"]
theorem tryit_6_11b_middle_half {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 81 ((15 : ℝ) ^ 2).toNNReal) P) {Q1 Q3 : ℝ}
    (h1 : P.real {ω | X ω ≤ Q1} = 1 / 4) (h3 : P.real {ω | X ω ≤ Q3} = 3 / 4) :
    P.real {ω | Q1 < X ω ∧ X ω ≤ Q3} = 1 / 2 := by
  have hle : Q1 ≤ Q3 := by
    have l : Φ 0.674 < 3 / 4 := by linarith [tphi_0_674.2]
    have g : 3 / 4 < Φ 0.675 := by linarith [tphi_0_675.1]
    have l' : Φ (-0.675) < 1 / 4 := by rw [stdNormalCdf_neg]; linarith [tphi_0_675.1]
    have g' : 1 / 4 < Φ (-0.674) := by rw [stdNormalCdf_neg]; linarith [tphi_0_674.2]
    have a := pct (by norm_num) hX (by norm_num) (by norm_num) l g h3
    have b := pct (by norm_num) hX (by norm_num) (by norm_num) l' g' h1
    linarith [a.1, b.2]
  rw [prob_Ioc_normal (by norm_num) hX _ _ hle]
  have e1 := prob_le_normal (by norm_num) hX Q1
  have e2 := prob_le_normal (by norm_num) hX Q3
  linarith

/-- OpenStax Introductory Statistics 2e Try It 6.12(a). For orange diameters `X ~ N(5.85, 0.24²)`,
the middle 40% lies between the 30th percentile `k₁` (`P(X ≤ k₁) = 0.3`), in `(5.72, 5.73)`, and the
70th percentile `k₂` (`P(X ≤ k₂) = 0.7`), in `(5.97, 5.98)`; and `P(k₁ < X ≤ k₂) = 2/5`. -/
@[kb "openstaxintrostats2e" "Try It 6.12, p. 358"]
theorem tryit_6_12a_middle_40 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 5.85 ((0.24 : ℝ) ^ 2).toNNReal) P) {k1 k2 : ℝ}
    (h1 : P.real {ω | X ω ≤ k1} = 3 / 10) (h2 : P.real {ω | X ω ≤ k2} = 7 / 10) :
    (5.72 < k1 ∧ k1 < 5.73) ∧ (5.97 < k2 ∧ k2 < 5.98) ∧
      P.real {ω | k1 < X ω ∧ X ω ≤ k2} = 2 / 5 := by
  have l : Φ 0.524 < 7 / 10 := by linarith [tphi_0_524.2]
  have g : 7 / 10 < Φ 0.525 := by linarith [tphi_0_525.1]
  have l' : Φ (-0.525) < 3 / 10 := by rw [stdNormalCdf_neg]; linarith [tphi_0_525.1]
  have g' : 3 / 10 < Φ (-0.524) := by rw [stdNormalCdf_neg]; linarith [tphi_0_524.2]
  have a := pct (by norm_num) hX (by norm_num) (by norm_num) l g h2
  have b := pct (by norm_num) hX (by norm_num) (by norm_num) l' g' h1
  have hle : k1 ≤ k2 := by linarith [a.1, b.2]
  refine ⟨⟨by linarith [b.1], by linarith [b.2]⟩, ⟨by linarith [a.1], by linarith [a.2]⟩, ?_⟩
  rw [prob_Ioc_normal (by norm_num) hX _ _ hle]
  have e1 := prob_le_normal (by norm_num) hX k1
  have e2 := prob_le_normal (by norm_num) hX k2
  linarith

/-- OpenStax Introductory Statistics 2e Try It 6.12(b). For orange diameters `X ~ N(5.85, 0.24²)`, any
`k` with `P(X ≤ k) = 0.16` (the 16th percentile) lies in `(5.61, 5.62)` cm. -/
@[kb "openstaxintrostats2e" "Try It 6.12, p. 358"]
theorem tryit_6_12b_percentile_16 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 5.85 ((0.24 : ℝ) ^ 2).toNNReal) P) {k : ℝ}
    (hk : P.real {ω | X ω ≤ k} = 4 / 25) : 5.61 < k ∧ k < 5.62 := by
  have l : Φ (-0.995) < 4 / 25 := by rw [stdNormalCdf_neg]; linarith [tphi_0_995.1]
  have g : 4 / 25 < Φ (-0.994) := by rw [stdNormalCdf_neg]; linarith [tphi_0_994.2]
  have := pct (by norm_num) hX (by norm_num) (by norm_num) l g hk
  constructor <;> linarith [this.1, this.2]

end UndergradKB.Statistics.Course.TryItC6
