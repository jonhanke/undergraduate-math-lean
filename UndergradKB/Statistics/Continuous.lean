import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ConditionalProbability
import UndergradKB.Common.Attr

/-!
# Continuous distributions: exponential and uniform

OpenStax *Introductory Statistics 2e*, chapter 5. The exponential law with decay rate `m` is Mathlib's
`ProbabilityTheory.expMeasure m` (mean `1/m`); the uniform law on `[a, b]` is
`MeasureTheory.pdf.IsUniform X (Set.Icc a b) P`, i.e. `HasLaw X (volume[|Icc a b]) P`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {μ : Measure ℝ}

private lemma hasLaw_preimage (hX : HasLaw X μ P) {u : Set ℝ} (hu : MeasurableSet u) :
    P (X ⁻¹' u) = μ u := by
  rw [← hX.map_eq, Measure.map_apply_of_aemeasurable hX.aemeasurable hu]

/-- Conditional probability of a nested pair of events for a variable with law `μ`:
`P(X ∈ t | X ∈ s) = μ(s)⁻¹ μ(t)` when `t ⊆ s`. -/
theorem hasLaw_cond_preimage (hX : HasLaw X μ P) {s t : Set ℝ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hts : t ⊆ s) :
    P[X ⁻¹' t | X ⁻¹' s] = (μ s)⁻¹ * μ t := by
  have hnm : NullMeasurableSet (X ⁻¹' s) P := hX.aemeasurable.nullMeasurable hs
  rw [ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply₀' hnm, smul_eq_mul,
    inter_eq_left.2 (preimage_mono hts), hasLaw_preimage hX hs, hasLaw_preimage hX ht]

end General

section Exponential

variable {m : ℝ}

/-- The exponential density, as a real number, is `m e^{-m x}` for `x ≥ 0` and `0` otherwise. -/
private lemma toReal_exponentialPDF (hm : 0 < m) (x : ℝ) :
    (exponentialPDF m x).toReal = if 0 ≤ x then m * exp (-(m * x)) else 0 := by
  rw [exponentialPDF_eq, ENNReal.toReal_ofReal]
  split_ifs
  · positivity
  · exact le_rfl

/-- The survival function of the exponential law: `P(X > x) = e^{-m x}` for `x ≥ 0`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem expMeasure_Ioi_real (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    (expMeasure m).real (Ioi x) = exp (-(m * x)) := by
  have := isProbabilityMeasure_expMeasure hm
  have h1 := cdf_eq_real (expMeasure m) x
  rw [cdf_expMeasure_eq hm, if_pos hx] at h1
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← h1]
  ring

theorem expMeasure_Ioi (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure m (Ioi x) = ENNReal.ofReal (exp (-(m * x))) := by
  have := isProbabilityMeasure_expMeasure hm
  rw [← expMeasure_Ioi_real hm hx, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Exponential survival (ST-054).** If `X` has the exponential law with decay rate `m`, then
`P(X > x) = e^{-m x}` for `x ≥ 0`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem expMeasure_survival_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (expMeasure m) P) (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x < X ω} = exp (-(m * x)) := by
  rw [hX.measureReal_eq (p := fun y => x < y) measurableSet_Ioi]
  exact expMeasure_Ioi_real hm hx

private lemma expMeasure_memoryless_aux (hm : 0 < m) {x k : ℝ} (hx : 0 ≤ x) (hk : 0 ≤ k) :
    (expMeasure m (Ioi x))⁻¹ * expMeasure m (Ioi (x + k)) = expMeasure m (Ioi k) := by
  rw [expMeasure_Ioi hm hx, expMeasure_Ioi hm (by linarith), expMeasure_Ioi hm hk,
    ← ENNReal.ofReal_inv_of_pos (exp_pos _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← exp_neg, ← exp_add]
  congr 1
  ring

/-- **Memorylessness of the exponential law (ST-055).** If `X` has the exponential distribution with
decay rate `m`, then for `x, k ≥ 0` knowing that `X > x` does not change the chance of waiting a
further `k`: `P(X > x + k | X > x) = P(X > k)`. Stated for the law itself. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem expMeasure_memoryless (hm : 0 < m) {x k : ℝ} (hx : 0 ≤ x) (hk : 0 ≤ k) :
    (expMeasure m)[Ioi (x + k) | Ioi x] = expMeasure m (Ioi k) := by
  rw [cond_apply measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi (by linarith))]
  exact expMeasure_memoryless_aux hm hx hk

/-- **Memorylessness (ST-055), random-variable form.** If `X` has law `expMeasure m` under `P`
(`m > 0`), then `P(X > x + k | X > x) = P(X > k)` for `x, k ≥ 0`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem expMeasure_memoryless_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (expMeasure m) P) (hm : 0 < m) {x k : ℝ} (hx : 0 ≤ x)
    (hk : 0 ≤ k) :
    P[X ⁻¹' Ioi (x + k) | X ⁻¹' Ioi x] = P (X ⁻¹' Ioi k) := by
  rw [hasLaw_cond_preimage hX measurableSet_Ioi measurableSet_Ioi
    (Ioi_subset_Ioi (by linarith)), hasLaw_preimage hX measurableSet_Ioi]
  exact expMeasure_memoryless_aux hm hx hk

/-- **Exponential percentile (ST-057).** The `p`-th quantile of the exponential law with decay rate
`m` is `-ln(1 - p) / m`: `P(X ≤ -ln(1-p)/m) = p` for `0 ≤ p < 1`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem expMeasure_percentile (hm : 0 < m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (expMeasure m).real (Iic (-Real.log (1 - p) / m)) = p := by
  have := isProbabilityMeasure_expMeasure hm
  have hx : 0 ≤ -Real.log (1 - p) / m := by
    have : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    exact div_nonneg (by linarith) hm.le
  rw [← cdf_eq_real, cdf_expMeasure_eq hm, if_pos hx]
  have : m * (-Real.log (1 - p) / m) = -Real.log (1 - p) := by field_simp
  rw [this, neg_neg, exp_log (by linarith)]
  ring

/-- Random-variable form of ST-057. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem expMeasure_percentile_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (expMeasure m) P) (hm : 0 < m) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p < 1) :
    P.real {ω | X ω ≤ -Real.log (1 - p) / m} = p := by
  rw [hX.measureReal_eq (p := fun y => y ≤ -Real.log (1 - p) / m) measurableSet_Iic]
  exact expMeasure_percentile hm hp0 hp1

/-- The exponential law as a measure with density. -/
private lemma expMeasure_eq_withDensity : expMeasure m = volume.withDensity (exponentialPDF m) :=
  rfl

private lemma integral_expMeasure (hm : 0 < m) (f : ℝ → ℝ) :
    ∫ x, f x ∂expMeasure m = ∫ x in Ioi 0, m * exp (-(m * x)) * f x := by
  rw [expMeasure_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (f := exponentialPDF m) ((measurable_exponentialPDFReal m).ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have : (fun x => (exponentialPDF m x).toReal • f x) =
      (Ici (0 : ℝ)).indicator (fun x => m * exp (-(m * x)) * f x) := by
    ext x
    rw [toReal_exponentialPDF hm]
    by_cases h : 0 ≤ x <;> simp [indicator, h]
  rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

private lemma integrable_pow_expMeasure (hm : 0 < m) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (expMeasure m) := by
  rw [expMeasure_eq_withDensity, integrable_withDensity_iff_integrable_smul'
    (f := exponentialPDF m) ((measurable_exponentialPDFReal m).ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have : (fun x => (exponentialPDF m x).toReal • x ^ k) =
      (Ici (0 : ℝ)).indicator (fun x => m * exp (-(m * x)) * x ^ k) := by
    ext x
    rw [toReal_exponentialPDF hm]
    by_cases h : 0 ≤ x <;> simp [indicator, h]
  rw [this, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := m)
    (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) one_pos hm
  have h2 : IntegrableOn (fun x : ℝ => m * (x ^ (k : ℝ) * exp (-m * x ^ (1 : ℝ)))) (Ioi 0) :=
    h.const_mul m
  refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [rpow_natCast, rpow_one]
  ring_nf

private lemma integral_pow_aux (hm : 0 < m) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), m * exp (-(m * x)) * x ^ k = k.factorial / m ^ k := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := m) (by positivity) hm
  have e : ∀ x ∈ Ioi (0 : ℝ), m * exp (-(m * x)) * x ^ k =
      m * (x ^ ((k : ℝ) + 1 - 1) * exp (-(m * x))) := by
    intro x _
    rw [add_sub_cancel_right, rpow_natCast]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, h, Real.Gamma_nat_eq_factorial]
  have : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [this, rpow_natCast, div_pow, one_pow]
  field_simp
  ring

/-- **Mean of the exponential law (ST-053).** With decay rate `m > 0` the mean is `1/m`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem integral_expMeasure_id (hm : 0 < m) : ∫ x, x ∂expMeasure m = 1 / m := by
  rw [integral_expMeasure hm (fun x => x)]
  have := integral_pow_aux hm 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at this
  exact this

/-- **Variance of the exponential law (ST-053).** With decay rate `m > 0` the variance is `1/m²`,
so the standard deviation equals the mean, `1/m`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem variance_expMeasure (hm : 0 < m) : variance id (expMeasure m) = 1 / m ^ 2 := by
  have := isProbabilityMeasure_expMeasure hm
  have hL : MemLp id 2 (expMeasure m) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_pow_expMeasure hm 2)
  rw [variance_eq_sub hL]
  have h2 : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂expMeasure m = 2 / m ^ 2 := by
    simp only [Pi.pow_apply, id]
    rw [integral_expMeasure hm (fun x => x ^ 2)]
    have := integral_pow_aux hm 2
    simpa [Nat.factorial] using this
  have h1 : ∫ x, (id : ℝ → ℝ) x ∂expMeasure m = 1 / m := integral_expMeasure_id hm
  rw [h2, h1]
  field_simp
  ring

/-- Standard deviation of the exponential law equals `1/m` (ST-053). -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem sqrt_variance_expMeasure (hm : 0 < m) : Real.sqrt (variance id (expMeasure m)) = 1 / m := by
  rw [variance_expMeasure hm, show 1 / m ^ 2 = (1 / m) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- ST-053 for a random variable with the exponential law: mean `1/m`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem expectation_of_hasLaw_exp {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (expMeasure m) P) (hm : 0 < m) : P[X] = 1 / m := by
  rw [hX.integral_eq, integral_expMeasure_id hm]

/-- ST-053 for a random variable with the exponential law: variance `1/m²`. -/
@[kb "openstaxintrostats2e" "§5.3, p. 313"]
theorem variance_of_hasLaw_exp {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (expMeasure m) P) (hm : 0 < m) : variance X P = 1 / m ^ 2 := by
  rw [hX.variance_eq, variance_expMeasure hm]

end Exponential

section Uniform

variable {a b : ℝ}

/-- The uniform law on `[a, b]` of an interval inside it. -/
private lemma unif_apply (hab : a < b) {t : Set ℝ} (ht : MeasurableSet t) :
    (volume : Measure ℝ)[t | Icc a b] = (ENNReal.ofReal (b - a))⁻¹ * volume (Icc a b ∩ t) := by
  rw [cond_apply measurableSet_Icc, Real.volume_Icc]

private lemma unif_Ioo (hab : a < b) {c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (volume : Measure ℝ)[Ioo c d | Icc a b] = ENNReal.ofReal ((d - c) / (b - a)) := by
  rw [unif_apply hab measurableSet_Ioo,
    inter_eq_right.2 (Ioo_subset_Icc_self.trans (Icc_subset_Icc hac hdb)), Real.volume_Ioo,
    ← ENNReal.ofReal_inv_of_pos (sub_pos.2 hab), ← ENNReal.ofReal_mul (by simp [hab.le])]
  congr 1
  rw [div_eq_inv_mul]

private lemma unif_Ioi (hab : a < b) {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    (volume : Measure ℝ)[Ioi c | Icc a b] = ENNReal.ofReal ((b - c) / (b - a)) := by
  have : Icc a b ∩ Ioi c = Ioc c b := by
    ext y
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [unif_apply hab measurableSet_Ioi, this, Real.volume_Ioc,
    ← ENNReal.ofReal_inv_of_pos (sub_pos.2 hab), ← ENNReal.ofReal_mul (by simp [hab.le])]
  congr 1
  rw [div_eq_inv_mul]

/-- **Uniform probability of an interval (ST-050).** If `X` is uniform on `[a, b]` and
`a ≤ c ≤ d ≤ b`, then `P(c < X < d) = (d - c)/(b - a)`. -/
@[kb "openstaxintrostats2e" "§5.2, p. 306"]
theorem uniform_prob_Ioo {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) :
    P {ω | c < X ω ∧ X ω < d} = ENNReal.ofReal ((d - c) / (b - a)) := by
  rw [HasLaw.measure_eq hX (p := fun y => c < y ∧ y < d) measurableSet_Ioo]
  exact unif_Ioo hab hac hcd hdb

/-- **Uniform conditional probability (ST-052).** If `X` is uniform on `[a, b]` and
`a ≤ c ≤ d ≤ b`, `c < b`, then `P(X > d | X > c) = (b - d)/(b - c)`. -/
@[kb "openstaxintrostats2e" "§5.2, p. 306"]
theorem uniform_cond_Ioi {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) {c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hcb : c < b) :
    P[X ⁻¹' Ioi d | X ⁻¹' Ioi c] = ENNReal.ofReal ((b - d) / (b - c)) := by
  rw [hasLaw_cond_preimage hX measurableSet_Ioi measurableSet_Ioi (Ioi_subset_Ioi hcd),
    unif_Ioi hab hac hcb.le, unif_Ioi hab (hac.trans hcd) hdb,
    ← ENNReal.ofReal_inv_of_pos (div_pos (sub_pos.2 hcb) (sub_pos.2 hab)),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (div_nonneg (sub_nonneg.2 hcb.le) (sub_nonneg.2 hab.le)))]
  congr 1
  have h1 : b - c ≠ 0 := (sub_pos.2 hcb).ne'
  have h2 : b - a ≠ 0 := (sub_pos.2 hab).ne'
  field_simp

private lemma isProb_unif (hab : a < b) : IsProbabilityMeasure ((volume : Measure ℝ)[|Icc a b]) :=
  cond_isProbabilityMeasure_of_finite (by simp [hab]) (by simp)

private lemma integral_unif (hab : a < b) (f : ℝ → ℝ) :
    ∫ x, f x ∂((volume : Measure ℝ)[|Icc a b]) = (b - a)⁻¹ * ∫ x in a..b, f x := by
  rw [ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.2 hab.le), smul_eq_mul,
    intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]

private lemma integrable_unif (hab : a < b) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f ((volume : Measure ℝ)[|Icc a b]) := by
  refine (hf.integrableOn_Icc (a := a) (b := b)).smul_measure ?_
  rw [Real.volume_Icc]
  exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'

private lemma unif_mean (hab : a < b) :
    ∫ x, x ∂((volume : Measure ℝ)[|Icc a b]) = (a + b) / 2 := by
  rw [integral_unif hab (fun x => x), integral_id]
  have : b - a ≠ 0 := (sub_pos.2 hab).ne'
  field_simp
  ring

/-- **Mean of the uniform law (ST-051).** The uniform law on `[a, b]` has mean `(a + b)/2`. -/
@[kb "openstaxintrostats2e" "§5.2, p. 306"]
theorem uniform_mean {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) : P[X] = (a + b) / 2 := by
  rw [HasLaw.integral_eq hX, unif_mean hab]

/-- **Variance of the uniform law (ST-051).** The uniform law on `[a, b]` has variance
`(b - a)² / 12`. -/
@[kb "openstaxintrostats2e" "§5.2, p. 306"]
theorem uniform_variance {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    (hX : pdf.IsUniform X (Icc a b) P) (hab : a < b) : variance X P = (b - a) ^ 2 / 12 := by
  have := isProb_unif hab
  rw [HasLaw.variance_eq hX]
  have hL : MemLp id 2 ((volume : Measure ℝ)[|Icc a b]) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_unif hab (continuous_id.pow 2))
  rw [variance_eq_sub hL]
  have h2 : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂((volume : Measure ℝ)[|Icc a b]) = (b ^ 3 - a ^ 3) / 3 /
      (b - a) := by
    simp only [Pi.pow_apply, id]
    rw [integral_unif hab (fun x => x ^ 2), integral_pow]
    push_cast
    norm_num
    ring
  have h1 : ∫ x, (id : ℝ → ℝ) x ∂((volume : Measure ℝ)[|Icc a b]) = (a + b) / 2 := unif_mean hab
  rw [h2, h1]
  have : b - a ≠ 0 := (sub_pos.2 hab).ne'
  field_simp
  ring

end Uniform

end UndergradKB.Statistics
