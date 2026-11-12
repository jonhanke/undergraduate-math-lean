import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import UndergradKB.Common.Attr

/-!
# Functions of random variables (Grinstead–Snell, chapters 2, 5, 6)

Cdf and density of an increasing transform `φ(X)`, inverse transform sampling, the tangent of a uniform
angle (Cauchy law), the distance of a uniform dart from the centre of the unit disk, the variance of a
random variable with density, and the square of a standard normal variable (chi-squared with one degree
of freedom).
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace UndergradKB.Probability

section Increasing

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
  {φ ψ : ℝ → ℝ}

lemma le_iff_inverse_of_strictMono (hφ : StrictMono φ) (hr : ∀ y, φ (ψ y) = y) (x y : ℝ) :
    φ x ≤ y ↔ x ≤ ψ y := by
  conv_lhs => rw [← hr y]
  exact hφ.le_iff_le

lemma monotone_of_strictMono_inverse (hφ : StrictMono φ) (hr : ∀ y, φ (ψ y) = y) : Monotone ψ := by
  intro a b hab
  by_contra h
  push Not at h
  have := hφ h
  rw [hr, hr] at this
  linarith

/-- Grinstead–Snell Theorem 5.1 (PR-062). If `φ` is strictly increasing with inverse `ψ` and `X` is a
random variable, then `Y = φ(X)` has distribution function `F_Y(y) = F_X(ψ(y))`. -/
@[kb "grinsteadsnell2006" "Theorem 5.1, p. 218"]
theorem cdf_map_strictMono (hX : AEMeasurable X P) (hφ : StrictMono φ)
    (hl : ∀ x, ψ (φ x) = x) (hr : ∀ y, φ (ψ y) = y) (y : ℝ) :
    cdf (P.map (fun ω => φ (X ω))) y = cdf (P.map X) (ψ y) := by
  have hφm : Measurable φ := hφ.monotone.measurable
  have hY : AEMeasurable (fun ω => φ (X ω)) P := hφm.comp_aemeasurable hX
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply_of_aemeasurable hY measurableSet_Iic,
    map_measureReal_apply_of_aemeasurable hX measurableSet_Iic]
  congr 1
  ext ω
  simp [le_iff_inverse_of_strictMono hφ hr]

omit [IsProbabilityMeasure P] in
/-- Grinstead–Snell Theorem 5.1 (PR-062), in probabilistic form: `P(φ(X) ≤ y) = P(X ≤ ψ(y))`. -/
@[kb "grinsteadsnell2006" "Theorem 5.1, p. 218"]
theorem measure_comp_le_strictMono (hφ : StrictMono φ) (hr : ∀ y, φ (ψ y) = y) (y : ℝ) :
    P {ω | φ (X ω) ≤ y} = P {ω | X ω ≤ ψ y} := by
  congr 1
  ext ω
  simp [le_iff_inverse_of_strictMono hφ hr]

/-- Grinstead–Snell Corollary 5.1 (PR-062). If `X` has density `f` and `φ` is strictly increasing with
differentiable inverse `ψ` (derivative `ψ'`), then `φ(X)` has density `y ↦ f(ψ y) ψ'(y)`. -/
@[kb "grinsteadsnell2006" "Corollary 5.1, p. 218"]
theorem map_withDensity_strictMono {f ψ' : ℝ → ℝ} (hX : AEMeasurable X P)
    (hlaw : P.map X = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hφ : StrictMono φ) (hl : ∀ x, ψ (φ x) = x) (hr : ∀ y, φ (ψ y) = y)
    (hψ : ∀ y, HasDerivAt ψ (ψ' y) y) :
    P.map (fun ω => φ (X ω)) =
      volume.withDensity (fun y => ENNReal.ofReal (f (ψ y) * ψ' y)) := by
  have hφm : Measurable φ := hφ.monotone.measurable
  have hψ0 : ∀ y, 0 ≤ ψ' y := fun y => by
    rw [← (hψ y).deriv]
    exact (monotone_of_strictMono_inverse hφ hr).deriv_nonneg
  have hinj : Function.Injective ψ := fun a b h => by
    rw [← hr a, ← hr b, h]
  ext s hs
  have hcomp : P.map (fun ω => φ (X ω)) = (P.map X).map φ :=
    (AEMeasurable.map_map_of_aemeasurable hφm.aemeasurable hX).symm
  rw [hcomp, hlaw,Measure.map_apply hφm hs,
    withDensity_apply _ (hφm hs), withDensity_apply _ hs]
  have himg : ψ '' s = φ ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hr] using hy
    · intro hx
      exact ⟨φ x, hx, hl x⟩
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun y _ => (hψ y).hasDerivWithinAt) hinj.injOn]
  refine lintegral_congr fun y => ?_
  rw [abs_of_nonneg (hψ0 y), mul_comm (f (ψ y)), ENNReal.ofReal_mul (hψ0 y)]

end Increasing

section InverseSampling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Corollary 5.2 (PR-063). If `U` is uniform on `[0,1]`, `F` is strictly increasing with
values in `(0,1)` and `ψ` inverts `F` on `(0,1)`, then `P(ψ(U) ≤ x) = F(x)`. -/
@[kb "grinsteadsnell2006" "Corollary 5.2, p. 220"]
theorem measure_inverse_transform_le {U : Ω → ℝ} (hU : HasLaw U (volume.restrict (Icc 0 1)) P)
    {F ψ : ℝ → ℝ} (hF : StrictMono F) (hFr : ∀ x, F x ∈ Ioo (0 : ℝ) 1)
    (hψ : ∀ y ∈ Ioo (0 : ℝ) 1, F (ψ y) = y) (x : ℝ) :
    P {ω | ψ (U ω) ≤ x} = ENNReal.ofReal (F x) := by
  have hmeas : P.map U = volume.restrict (Icc 0 1) := hU.map_eq
  have hae : ∀ᵐ ω ∂P, U ω ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_iff]
    have h := Measure.map_apply_of_aemeasurable hU.aemeasurable
      (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)).compl
    rw [hmeas, Measure.restrict_apply (measurableSet_Ioo.compl)] at h
    have h0 : volume ((Ioo (0 : ℝ) 1)ᶜ ∩ Icc 0 1) = 0 := by
      have : (Ioo (0 : ℝ) 1)ᶜ ∩ Icc 0 1 ⊆ {0, 1} := by
        intro y hy
        simp only [mem_inter_iff, mem_compl_iff, mem_Ioo, mem_Icc, not_and_or, not_lt] at hy
        simp only [mem_insert_iff, mem_singleton_iff]
        rcases hy with ⟨h1 | h1, h2, h3⟩
        · left; linarith
        · right; linarith
      exact measure_mono_null this ((Set.toFinite _).measure_zero _)
    rw [h0] at h
    exact h.symm
  have hset : P {ω | ψ (U ω) ≤ x} = P {ω | U ω ≤ F x} := by
    refine measure_congr ?_
    filter_upwards [hae] with ω hω
    show (ψ (U ω) ≤ x) = (U ω ≤ F x)
    apply propext
    rw [← hF.le_iff_le, hψ _ hω]
  rw [hset]
  have h := Measure.map_apply_of_aemeasurable hU.aemeasurable (measurableSet_Iic (a := F x))
  have hsub : {ω | U ω ≤ F x} = U ⁻¹' Iic (F x) := rfl
  rw [hsub, ← h, hmeas, Measure.restrict_apply measurableSet_Iic]
  have hx := hFr x
  have : Iic (F x) ∩ Icc 0 1 = Icc 0 (F x) := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hx.2]⟩
  rw [this, Real.volume_Icc, sub_zero]

/-- Grinstead–Snell Corollary 5.2 (PR-063), cdf form: the law of `ψ(U)` has distribution function `F`. -/
@[kb "grinsteadsnell2006" "Corollary 5.2, p. 220"]
theorem cdf_inverse_transform {U : Ω → ℝ} (hU : HasLaw U (volume.restrict (Icc 0 1)) P)
    {F ψ : ℝ → ℝ} (hF : StrictMono F) (hFr : ∀ x, F x ∈ Ioo (0 : ℝ) 1)
    (hψ : ∀ y ∈ Ioo (0 : ℝ) 1, F (ψ y) = y) (hψm : Measurable ψ) (x : ℝ) :
    cdf (P.map (fun ω => ψ (U ω))) x = F x := by
  have e0 : (fun ω => ψ (U ω)) = ψ ∘ U := rfl
  rw [e0, cdf_eq_real, map_measureReal_apply_of_aemeasurable (hψm.comp_aemeasurable hU.aemeasurable)
    measurableSet_Iic, measureReal_def]
  have := measure_inverse_transform_le hU hF hFr hψ x
  have e : ψ ∘ U ⁻¹' Iic x = {ω | ψ (U ω) ≤ x} := rfl
  rw [e, this, ENNReal.toReal_ofReal (hFr x).1.le]

end InverseSampling

section Cauchy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

private lemma measurable_tan' : Measurable Real.tan := by
  have : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
  rw [this]
  exact Real.measurable_sin.div Real.measurable_cos

private lemma prob_tan_slice {Θ : Ω → ℝ}
    (hΘ : pdf.IsUniform Θ (Ioo (-(π / 2)) (π / 2)) P) {s : Set ℝ} (hs : MeasurableSet s) :
    P ((fun ω => Real.tan (Θ ω)) ⁻¹' s) =
      (ENNReal.ofReal π)⁻¹ * volume (Ioo (-(π / 2)) (π / 2) ∩ Real.tan ⁻¹' s) := by
  have h := Measure.map_apply_of_aemeasurable hΘ.aemeasurable (measurable_tan' hs)
  have e : (fun ω => Real.tan (Θ ω)) ⁻¹' s = Θ ⁻¹' (Real.tan ⁻¹' s) := rfl
  have hm : P.map Θ = (volume : Measure ℝ)[|Ioo (-(π / 2)) (π / 2)] := hΘ.map_eq
  rw [e, ← h, hm, cond_apply measurableSet_Ioo, Real.volume_Ioo]
  congr 3
  ring

/-- Grinstead–Snell Example 5.11 (PR-061), cdf form: if `Θ` is uniform on `(-π/2, π/2)` then
`P(tan Θ ≤ x) = 1/2 + arctan(x)/π`. -/
@[kb "grinsteadsnell2006" "Example 5.11, p. 226"]
theorem measureReal_tan_le_of_uniform {Θ : Ω → ℝ}
    (hΘ : pdf.IsUniform Θ (Ioo (-(π / 2)) (π / 2)) P) (x : ℝ) :
    P.real {ω | Real.tan (Θ ω) ≤ x} = 1 / 2 + Real.arctan x / π := by
  have h := prob_tan_slice hΘ (measurableSet_Iic (a := x))
  have ha1 := Real.arctan_lt_pi_div_two x
  have hset : Ioo (-(π / 2)) (π / 2) ∩ Real.tan ⁻¹' Iic x = Ioc (-(π / 2)) (Real.arctan x) := by
    ext θ
    simp only [mem_inter_iff, mem_Ioo, mem_preimage, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      rw [← Real.arctan_tan h1 h2]
      exact Real.arctan_strictMono.monotone h3
    · rintro ⟨h1, h2⟩
      have h2' : θ < π / 2 := lt_of_le_of_lt h2 ha1
      refine ⟨⟨h1, h2'⟩, ?_⟩
      have := Real.strictMonoOn_tan.monotoneOn ⟨h1, h2'⟩ ⟨Real.neg_pi_div_two_lt_arctan x, ha1⟩ h2
      rwa [Real.tan_arctan] at this
  have hpi := Real.pi_pos
  rw [hset, Real.volume_Ioc] at h
  rw [measureReal_def]
  have e : {ω | Real.tan (Θ ω) ≤ x} = (fun ω => Real.tan (Θ ω)) ⁻¹' Iic x := rfl
  rw [e, h, ← ENNReal.ofReal_inv_of_pos hpi, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (by linarith [Real.neg_pi_div_two_lt_arctan x]))]
  field_simp
  ring

/-- Grinstead–Snell Example 5.11 (PR-061). If `Θ` is uniform on `(-π/2, π/2)` then `tan Θ` has the
standard Cauchy law (location `0`, scale `1`, density `1/(π(1+x²))`). -/
@[kb "grinsteadsnell2006" "Example 5.11, p. 226"]
theorem map_tan_of_uniform {Θ : Ω → ℝ} (hΘ : pdf.IsUniform Θ (Ioo (-(π / 2)) (π / 2)) P) :
    P.map (fun ω => Real.tan (Θ ω)) = cauchyMeasure 0 1 := by
  have hpi := Real.pi_pos
  have hT : AEMeasurable (fun ω => Real.tan (Θ ω)) P := measurable_tan'.comp_aemeasurable hΘ.aemeasurable
  ext s hs
  rw [Measure.map_apply_of_aemeasurable hT hs, prob_tan_slice hΘ hs,
    cauchyMeasure_of_scale_ne_zero 0 one_ne_zero, withDensity_apply _ hs]
  have himg : Ioo (-(π / 2)) (π / 2) ∩ Real.tan ⁻¹' s = Real.arctan '' s := by
    ext θ
    simp only [mem_inter_iff, mem_Ioo, mem_preimage, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨Real.tan θ, h3, Real.arctan_tan h1 h2⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨Real.neg_pi_div_two_lt_arctan z, Real.arctan_lt_pi_div_two z⟩, by
        rwa [Real.tan_arctan]⟩
  rw [himg]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul hs
    (f := Real.arctan) (f' := fun x => (1 + x ^ 2)⁻¹)
    (fun x _ => (Real.hasDerivAt_arctan' x).hasDerivWithinAt)
    Real.arctan_injective.injOn (fun _ => (ENNReal.ofReal π)⁻¹)
  rw [setLIntegral_const] at key
  rw [key]
  refine lintegral_congr fun x => ?_
  rw [cauchyPDF_def, cauchyPDFReal_def, abs_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hpi,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp
  ring

end Cauchy

section Disk

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Examples 2.8 and 2.11 (PR-015). A point `X` uniform on the unit disk lies within
distance `r` of the centre with probability `r²`, for `0 ≤ r ≤ 1`. -/
@[kb "grinsteadsnell2006" "Example 2.8, p. 64"]
theorem measureReal_norm_le_of_uniform_disk {X : Ω → EuclideanSpace ℝ (Fin 2)}
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    P.real {ω | ‖X ω‖ ≤ r} = r ^ 2 := by
  have hm : P.map X = (volume : Measure (EuclideanSpace ℝ (Fin 2)))[|Metric.ball 0 1] := hX.map_eq
  have e : {ω | ‖X ω‖ ≤ r} = X ⁻¹' Metric.closedBall 0 r := by
    ext ω; simp
  have hpi : ENNReal.ofReal π ≠ 0 := by simp [Real.pi_pos]
  have hpt : ENNReal.ofReal π ≠ ⊤ := ENNReal.ofReal_ne_top
  have hvol : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ Metric.closedBall 0 r) =
      ENNReal.ofReal r ^ 2 * ENNReal.ofReal π := by
    refine le_antisymm ?_ ?_
    · calc _ ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) :=
            measure_mono inter_subset_right
        _ = _ := by simp
    · calc _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r) := by simp
        _ ≤ _ := by
          refine measure_mono fun y hy => ⟨?_, Metric.ball_subset_closedBall hy⟩
          exact Metric.ball_subset_ball h1 hy
  rw [measureReal_def, e, ← Measure.map_apply_of_aemeasurable hX.aemeasurable
    Metric.isClosed_closedBall.measurableSet, hm, cond_apply Metric.isOpen_ball.measurableSet, hvol]
  have : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))⁻¹ *
      (ENNReal.ofReal r ^ 2 * ENNReal.ofReal π) = ENNReal.ofReal r ^ 2 := by
    rw [EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hpi hpt, mul_one]
  rw [this, ← ENNReal.ofReal_pow h0, ENNReal.toReal_ofReal (by positivity)]

/-- Grinstead–Snell Examples 2.8 and 2.11 (PR-015), density form: the distance `‖X‖` of a uniform point
of the unit disk from the centre has density `2x` on `[0,1]`, i.e. `P(‖X‖ ≤ r) = ∫₀ʳ 2x dx`. -/
@[kb "grinsteadsnell2006" "Example 2.11, p. 67"]
theorem measureReal_norm_le_eq_integral_of_uniform_disk {X : Ω → EuclideanSpace ℝ (Fin 2)}
    (hX : pdf.IsUniform X (Metric.ball 0 1) P) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    P.real {ω | ‖X ω‖ ≤ r} = ∫ x in (0 : ℝ)..r, 2 * x := by
  rw [measureReal_norm_le_of_uniform_disk hX h0 h1, intervalIntegral.integral_const_mul,
    integral_id]
  ring

end Disk

section DensityVariance

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Theorem 6.13 (PR-076). If `X` has density `f`, its variance is
`∫ (x - μ)² f(x) dx`, where `μ = ∫ x f(x) dx` is its mean. -/
@[kb "grinsteadsnell2006" "Theorem 6.13, p. 280"]
theorem variance_eq_integral_pdf {X : Ω → ℝ} [HasPDF X P volume] :
    Var[X; P] = ∫ x, (x - ∫ y, y * (pdf X P volume y).toReal) ^ 2 * (pdf X P volume x).toReal := by
  have hX : AEMeasurable X P := HasPDF.aemeasurable X P volume
  have hmean : ∫ ω, X ω ∂P = ∫ y, y * (pdf X P volume y).toReal := by
    have : ∫ y, (pdf X P volume y).toReal • y = ∫ ω, X ω ∂P :=
      pdf.integral_pdf_smul (f := fun y : ℝ => y) measurable_id.aestronglyMeasurable
    simp only [smul_eq_mul] at this
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  rw [variance_eq_integral hX, hmean]
  generalize (∫ y, y * (pdf X P volume y).toReal) = m
  have hm : Measurable (fun y : ℝ => (y - m) ^ 2) := by fun_prop
  have : ∫ y, (pdf X P volume y).toReal • (y - m) ^ 2 = ∫ ω, (X ω - m) ^ 2 ∂P :=
    pdf.integral_pdf_smul (f := fun y : ℝ => (y - m) ^ 2) hm.aestronglyMeasurable
  simp only [smul_eq_mul] at this
  rw [← this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)

end DensityVariance

end UndergradKB.Probability
