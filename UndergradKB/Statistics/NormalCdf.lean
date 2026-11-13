import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import UndergradKB.Common.Attr
import UndergradKB.Statistics.PValue
import UndergradKB.Statistics.Percentile
import UndergradKB.Statistics.Course.C6

/-!
# The standard normal distribution function and its inverse (OpenStax *Introductory Statistics 2e*, §6.2)

`Φ = cdf (gaussianReal 0 1)` is the standard normal distribution function (the z-table).
We prove its basic properties, define its inverse `normalQuantile` (the z-score of a percentile),
and show how probabilities and percentiles of `N(μ, σ²)` reduce to `Φ` and `normalQuantile`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The standard normal distribution function. -/
local notation "Φ" => cdf (gaussianReal 0 1)

/-! ### Properties of `Φ` -/

/-- The standard normal law has no atoms. -/
lemma gaussianReal_zero_one_singleton (a : ℝ) : gaussianReal 0 1 {a} = 0 :=
  gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)

scoped instance : NullSingletonClass (gaussianReal 0 1) := ⟨gaussianReal_zero_one_singleton⟩

/-- `Φ` is continuous (the standard normal law has no atoms). -/
lemma continuous_stdNormalCdf : Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro a
  have hm : Monotone Φ := (cdf (gaussianReal 0 1)).mono
  rw [hm.continuousAt_iff_leftLim_eq_rightLim, (cdf (gaussianReal 0 1)).rightLim_eq a]
  have h := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, gaussianReal_zero_one_singleton] at h
  have h2 : Φ a - Function.leftLim Φ a ≤ 0 := by
    have := (ENNReal.ofReal_eq_zero).1 h.symm
    exact this
  have h3 : Function.leftLim Φ a ≤ Φ a := hm.leftLim_le le_rfl
  exact (by linarith : Function.leftLim Φ a = Φ a).symm ▸ rfl

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). The standard normal distribution function
`Φ` (the z-table) is continuous, strictly increasing, tends to `0` at `-∞` and to `1` at `+∞`,
and takes only values strictly between `0` and `1`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem stdNormalCdf_properties :
    Continuous Φ ∧ StrictMono Φ ∧ Tendsto Φ atBot (𝓝 0) ∧ Tendsto Φ atTop (𝓝 1) ∧
      ∀ z, 0 < Φ z ∧ Φ z < 1 := by
  refine ⟨continuous_stdNormalCdf, cdf_gaussianReal_strictMono, tendsto_cdf_atBot _,
    tendsto_cdf_atTop _, fun z ↦ ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_lt (cdf_nonneg _ _) (cdf_gaussianReal_strictMono (by linarith : z - 1 < z))
  · exact lt_of_lt_of_le (cdf_gaussianReal_strictMono (by linarith : z < z + 1)) (cdf_le_one _ _)

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Symmetry of the z-table:
`Φ(-z) = 1 - Φ(z)`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem stdNormalCdf_neg (z : ℝ) : Φ (-z) = 1 - Φ z := by
  rw [← gaussianReal_real_Ioi, ← gaussianReal_real_Iio_neg, cdf_eq_real]
  unfold Measure.real
  rw [measure_congr (Iio_ae_eq_Iic (μ := gaussianReal 0 1) (a := -z))]

/-! ### The inverse: z-scores of percentiles -/

lemma existsUnique_stdNormal {p : ℝ} (h : 0 < p ∧ p < 1) : ∃! q, Φ q = p := by
  have := existsUnique_percentile (gaussianReal 0 1) continuous_stdNormalCdf
    cdf_gaussianReal_strictMono h.1 h.2
  simpa [cdf_eq_real] using this

/-- The z-score of the `p`-quantile of the standard normal law: the inverse of `Φ` on `(0, 1)`
(and `0` outside, a junk value). -/
noncomputable def normalQuantile (p : ℝ) : ℝ :=
  if h : 0 < p ∧ p < 1 then (existsUnique_stdNormal h).exists.choose else 0

lemma stdNormalCdf_normalQuantile_aux {p : ℝ} (h : 0 < p ∧ p < 1) : Φ (normalQuantile p) = p := by
  unfold normalQuantile
  rw [dif_pos h]
  exact (existsUnique_stdNormal h).exists.choose_spec

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). `normalQuantile p` is a right inverse of
the z-table: `Φ (z_p) = p` for `0 < p < 1`, and it is the only such number. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem stdNormalCdf_normalQuantile {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    Φ (normalQuantile p) = p ∧ ∀ z, Φ z = p → z = normalQuantile p :=
  ⟨stdNormalCdf_normalQuantile_aux ⟨h0, h1⟩, fun z hz ↦
    cdf_gaussianReal_strictMono.injective (hz.trans (stdNormalCdf_normalQuantile_aux ⟨h0, h1⟩).symm)⟩

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Looking up `Φ z` and then inverting
returns the starting z-score: `normalQuantile (Φ z) = z`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem normalQuantile_stdNormalCdf (z : ℝ) : normalQuantile (Φ z) = z := by
  have h := (stdNormalCdf_properties.2.2.2.2 z)
  exact ((stdNormalCdf_normalQuantile h.1 h.2).2 z rfl).symm

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). The z-score of a percentile increases with
the percentile: `normalQuantile` is strictly monotone on `(0, 1)`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem normalQuantile_lt_normalQuantile {p q : ℝ} (hp : 0 < p) (hq : q < 1) (hpq : p < q) :
    normalQuantile p < normalQuantile q := by
  have e1 := stdNormalCdf_normalQuantile_aux (p := p) ⟨hp, by linarith⟩
  have e2 := stdNormalCdf_normalQuantile_aux (p := q) ⟨by linarith, hq⟩
  rw [← cdf_gaussianReal_strictMono.lt_iff_lt, e1, e2]
  exact hpq

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Symmetry of z-scores of percentiles:
`z_{1-p} = - z_p` for `0 < p < 1`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem normalQuantile_one_sub {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    normalQuantile (1 - p) = - normalQuantile p := by
  have e := (stdNormalCdf_normalQuantile (p := 1 - p) (by linarith) (by linarith)).2
    (-normalQuantile p) (by rw [stdNormalCdf_neg, (stdNormalCdf_normalQuantile h0 h1).1])
  exact e.symm

/-! ### Standardization -/

/-- Probability of a set for a standard normal random variable. -/
lemma real_preimage_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Z : Ω → ℝ} {m : Measure ℝ} (hZ : HasLaw Z m P) {S : Set ℝ} (hS : MeasurableSet S) :
    P.real (Z ⁻¹' S) = m.real S := by
  unfold Measure.real
  rw [← hZ.map_eq, Measure.map_apply_of_aemeasurable hZ.aemeasurable hS]

/-- Variance parameter of `N(μ, σ²)`. -/
private lemma sqrt_toNNReal_sq {σ : ℝ} : Real.sqrt ((σ ^ 2).toNNReal : ℝ) = |σ| := by
  rw [Real.coe_toNNReal _ (sq_nonneg σ)]
  exact Real.sqrt_sq_eq_abs σ

lemma standardized_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    HasLaw (fun ω ↦ (X ω - μ) / σ) (gaussianReal 0 1) P := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    have : 0 < σ ^ 2 := by positivity
    exact (Real.toNNReal_pos.2 this).ne'
  have h := Course.C6.standardization hX hv
  rwa [sqrt_toNNReal_sq, abs_of_pos hσ] at h

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Normal probabilities from the z-table: if
`X ~ N(μ, σ²)` with `σ > 0`, then `P(X ≤ x) = Φ((x - μ)/σ)`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem prob_le_normal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (x : ℝ) :
    P.real {ω | X ω ≤ x} = Φ ((x - μ) / σ) := by
  have hZ := standardized_hasLaw hσ hX
  have e : {ω | X ω ≤ x} = (fun ω ↦ (X ω - μ) / σ) ⁻¹' Iic ((x - μ) / σ) := by
    ext ω
    simp only [mem_setOf_eq, mem_preimage, mem_Iic]
    rw [div_le_div_iff_of_pos_right hσ]
    constructor <;> intro h <;> linarith
  rw [e, real_preimage_of_hasLaw hZ measurableSet_Iic, cdf_eq_real]

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Probability of an interval:
`P(a < X ≤ b) = Φ((b - μ)/σ) - Φ((a - μ)/σ)` for `X ~ N(μ, σ²)`, `σ > 0`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem prob_Ioc_normal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) (a b : ℝ)
    (hab : a ≤ b) :
    P.real {ω | a < X ω ∧ X ω ≤ b} = Φ ((b - μ) / σ) - Φ ((a - μ) / σ) := by
  have hZ := standardized_hasLaw hσ hX
  have e : {ω | a < X ω ∧ X ω ≤ b} =
      (fun ω ↦ (X ω - μ) / σ) ⁻¹' Ioc ((a - μ) / σ) ((b - μ) / σ) := by
    ext ω
    simp only [mem_setOf_eq, mem_preimage, mem_Ioc]
    rw [div_lt_div_iff_of_pos_right hσ, div_le_div_iff_of_pos_right hσ]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [e, real_preimage_of_hasLaw hZ measurableSet_Ioc]
  have hab' : (a - μ) / σ ≤ (b - μ) / σ := by gcongr
  have e2 : Ioc ((a - μ) / σ) ((b - μ) / σ) = Iic ((b - μ) / σ) \ Iic ((a - μ) / σ) := by
    ext x; simp [and_comm]
  rw [e2, measureReal_diff (Iic_subset_Iic.2 hab') measurableSet_Iic,
    ← cdf_eq_real, ← cdf_eq_real]

/-- OpenStax Introductory Statistics 2e §6.2 (ST-061). Percentiles of a normal law from the inverse
z-table: for `X ~ N(μ, σ²)`, `σ > 0`, and `0 < p < 1`, the number `x` with `P(X ≤ x) = p` exists, is
unique, and equals `μ + σ · normalQuantile p`. -/
@[kb "openstaxintrostats2e" "§6.2, p. 351"]
theorem normal_percentile {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    {μ σ : ℝ} (hσ : 0 < σ) (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P)
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    (P.real {ω | X ω ≤ μ + σ * normalQuantile p} = p) ∧
      ∀ x, P.real {ω | X ω ≤ x} = p → x = μ + σ * normalQuantile p := by
  have hq := stdNormalCdf_normalQuantile h0 h1
  refine ⟨?_, fun x hx ↦ ?_⟩
  · rw [prob_le_normal hσ hX]
    have : (μ + σ * normalQuantile p - μ) / σ = normalQuantile p := by
      field_simp; ring
    rw [this, hq.1]
  · rw [prob_le_normal hσ hX] at hx
    have := hq.2 _ hx
    field_simp at this
    linarith

end UndergradKB.Statistics
