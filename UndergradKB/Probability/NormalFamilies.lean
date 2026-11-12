import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import UndergradKB.Common.Attr

/-!
# Families built from normal variables (Grinstead–Snell, chapters 5 and 7)

The square of a standard normal variable has the gamma law with shape `1/2` and rate `1/2`
(chi-squared with one degree of freedom).
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace UndergradKB.Probability

private lemma gamma_half_pdf_sq (x : ℝ) (hx : x ≠ 0) :
    ENNReal.ofReal |2 * x| * gammaPDF (1 / 2) (1 / 2) (x ^ 2) = 2 * gaussianPDF 0 1 x := by
  rw [gammaPDF_of_nonneg (sq_nonneg x), gaussianPDF_def, ← ENNReal.ofReal_mul (abs_nonneg _),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have hax : 0 < |x| := abs_pos.2 hx
  have h1 : (x ^ 2) ^ ((1 / 2 : ℝ) - 1) = |x|⁻¹ := by
    have : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
    rw [this, Real.rpow_neg (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  have h2 : ((1 / 2 : ℝ)) ^ ((1 / 2 : ℝ)) = (√2)⁻¹ := by
    rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv]
  have h3 : Real.Gamma (1 / 2) = √π := Real.Gamma_one_half_eq
  have h4 : Real.sqrt (2 * π * ((1 : ℝ≥0) : ℝ)) = √2 * √π := by
    simp [Real.sqrt_mul]
  have h5 : -(1 / 2 * x ^ 2) = -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) := by
    simp; ring
  have hs2 : 0 < √2 := by positivity
  have hsp : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [h1, h2, h3, gaussianPDFReal_def, h4]
  beta_reduce
  rw [← h5, abs_mul, abs_two]
  field_simp

private lemma split_zero (f : ℝ → ℝ≥0∞) {T : Set ℝ} (hT : MeasurableSet T) :
    ∫⁻ x in T, f x = (∫⁻ x in T ∩ Ioi 0, f x) + ∫⁻ x in T ∩ Iio 0, f x := by
  have h1 := lintegral_inter_add_sdiff (μ := volume) f T (measurableSet_Ioi (a := (0 : ℝ)))
  have h2 := lintegral_inter_add_sdiff (μ := volume) f (T \ Ioi 0)
    (measurableSet_Iio (a := (0 : ℝ)))
  have h0 : ∫⁻ x in (T \ Ioi 0) \ Iio 0, f x = 0 := by
    refine setLIntegral_measure_zero _ _ (measure_mono_null ?_ (measure_singleton (0 : ℝ)))
    intro x hx
    simp only [mem_diff, mem_Ioi, mem_Iio, not_lt] at hx
    simp only [mem_singleton_iff]
    exact le_antisymm hx.1.2 hx.2
  rw [h0, add_zero] at h2
  have e : (T \ Ioi 0) ∩ Iio 0 = T ∩ Iio 0 := by
    ext x; simp only [mem_inter_iff, mem_diff, mem_Ioi, mem_Iio, not_lt]
    constructor
    · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
    · rintro ⟨a, c⟩; exact ⟨⟨a, c.le⟩, c⟩
  rw [e] at h2
  rw [← h2] at h1
  exact h1.symm

/-- Grinstead–Snell §5.2 chi-squared density (PR-060). The law of the square of a standard normal
variable is the gamma law with shape `1/2` and rate `1/2` (chi-squared, one degree of freedom). -/
@[kb "grinsteadsnell2006" "§5.2 chi-squared density, p. 225"]
theorem map_sq_gaussianReal_eq_gammaMeasure :
    (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = gammaMeasure (1 / 2) (1 / 2) := by
  have hm : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  ext s hs
  rw [Measure.map_apply hm hs, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    withDensity_apply _ (hm hs), gammaMeasure, withDensity_apply _ hs]
  set T : Set ℝ := (fun x : ℝ => x ^ 2) ⁻¹' s with hT
  have hTm : MeasurableSet T := hm hs
  -- the two sides of zero
  have hside : ∀ {S : Set ℝ}, MeasurableSet S → (∀ x ∈ S, x ≠ 0) →
      Set.InjOn (fun x : ℝ => x ^ 2) S →
      (∀ x ∈ S, HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) S x) →
      ∫⁻ y in (fun x : ℝ => x ^ 2) '' S, gammaPDF (1 / 2) (1 / 2) y =
        2 * ∫⁻ x in S, gaussianPDF 0 1 x := by
    intro S hS hne hinj hder
    rw [lintegral_image_eq_lintegral_abs_deriv_mul hS hder hinj, ← lintegral_const_mul' _ _
      (by simp)]
    exact setLIntegral_congr_fun hS (fun x hx => gamma_half_pdf_sq x (hne x hx))
  have hpos := hside (S := T ∩ Ioi 0) (hTm.inter measurableSet_Ioi)
    (fun x hx => hx.2.ne') (fun a ha b hb h => by
      have := ha.2; have := hb.2; simp only [mem_Ioi] at *
      nlinarith [h])
    (fun x _ => (hasDerivAt_pow 2 x).hasDerivWithinAt.congr_deriv (by simp))
  have hneg := hside (S := T ∩ Iio 0) (hTm.inter measurableSet_Iio)
    (fun x hx => hx.2.ne) (fun a ha b hb h => by
      have := ha.2; have := hb.2; simp only [mem_Iio] at *
      nlinarith [h])
    (fun x _ => (hasDerivAt_pow 2 x).hasDerivWithinAt.congr_deriv (by simp))
  have e1 : (fun x : ℝ => x ^ 2) '' (T ∩ Ioi 0) = s ∩ Ioi 0 := by
    ext y
    simp only [hT, mem_image, mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
      exact ⟨hx, by positivity⟩
    · rintro ⟨hy, hy0⟩
      exact ⟨√y, ⟨by rwa [Real.sq_sqrt hy0.le], Real.sqrt_pos.2 hy0⟩, Real.sq_sqrt hy0.le⟩
  have e2 : (fun x : ℝ => x ^ 2) '' (T ∩ Iio 0) = s ∩ Ioi 0 := by
    ext y
    simp only [hT, mem_image, mem_inter_iff, mem_preimage, mem_Ioi, mem_Iio]
    constructor
    · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
      exact ⟨hx, by nlinarith⟩
    · rintro ⟨hy, hy0⟩
      refine ⟨-√y, ⟨?_, by simpa using Real.sqrt_pos.2 hy0⟩, ?_⟩
      · simpa [Real.sq_sqrt hy0.le] using hy
      · simp [Real.sq_sqrt hy0.le]
  rw [e1] at hpos
  rw [e2] at hneg
  have hI : ∫⁻ x in T ∩ Ioi 0, gaussianPDF 0 1 x = ∫⁻ x in T ∩ Iio 0, gaussianPDF 0 1 x := by
    have := hpos.symm.trans hneg
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 this
  have hG : ∫⁻ y in s, gammaPDF (1 / 2) (1 / 2) y =
      ∫⁻ y in s ∩ Ioi 0, gammaPDF (1 / 2) (1 / 2) y := by
    rw [split_zero _ hs]
    have : ∫⁻ y in s ∩ Iio 0, gammaPDF (1 / 2) (1 / 2) y = 0 := by
      rw [setLIntegral_congr_fun (hs.inter measurableSet_Iio) (g := fun _ => 0)
        (fun y (hy : y ∈ s ∩ Iio 0) => gammaPDF_of_neg (a := 1 / 2) (r := 1 / 2) hy.2),
        lintegral_zero]
    rw [this]
    simp
  rw [hG, hpos, two_mul]
  rw [split_zero _ hTm, ← hI]

section Chi

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Grinstead–Snell §5.2 chi-squared density (PR-060), random-variable form: if `Z` is standard normal
then `Z²` has the gamma law with shape `1/2` and rate `1/2`. -/
@[kb "grinsteadsnell2006" "§5.2 chi-squared density, p. 225"]
theorem hasLaw_sq_gammaMeasure {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) :
    HasLaw (fun ω => Z ω ^ 2) (gammaMeasure (1 / 2) (1 / 2)) P := by
  have hsq : HasLaw (fun x : ℝ => x ^ 2) (gammaMeasure (1 / 2) (1 / 2)) (gaussianReal 0 1) :=
    ⟨by fun_prop, map_sq_gaussianReal_eq_gammaMeasure⟩
  exact hsq.comp hZ

end Chi

section Rayleigh

private noncomputable def rayDens (ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ * ((2 * π)⁻¹ * rexp (-(ρ ^ 2 / 2))))

private lemma gauss_prod_polar (ρ θ : ℝ) :
    gaussianPDF 0 1 (ρ * cos θ) * gaussianPDF 0 1 (ρ * sin θ) =
      ENNReal.ofReal ((2 * π)⁻¹ * rexp (-(ρ ^ 2 / 2))) := by
  rw [gaussianPDF_def]
  beta_reduce
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  rw [gaussianPDFReal_def]
  beta_reduce
  have hpi := Real.pi_pos
  have h1 : (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    simp
  have h2 : rexp (-(ρ * cos θ - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) *
      rexp (-(ρ * sin θ - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) = rexp (-(ρ ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    have := sin_sq_add_cos_sq θ
    simp
    linear_combination (-(ρ ^ 2) / 2) * this
  calc _ = ((√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹ * (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹) *
        (rexp (-(ρ * cos θ - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) *
          rexp (-(ρ * sin θ - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))) := by ring
    _ = _ := by rw [h1, h2]

private lemma lintegral_rayDens {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ρ in Ioc 0 r, rayDens ρ = ENNReal.ofReal ((2 * π)⁻¹ * (1 - rexp (-(r ^ 2 / 2)))) := by
  have hpi := Real.pi_pos
  have hcont : Continuous (fun ρ : ℝ => ρ * ((2 * π)⁻¹ * rexp (-(ρ ^ 2 / 2)))) := by fun_prop
  have hderiv : ∀ ρ ∈ uIcc 0 r, HasDerivAt (fun ρ : ℝ => -((2 * π)⁻¹ * rexp (-(ρ ^ 2 / 2))))
      (ρ * ((2 * π)⁻¹ * rexp (-(ρ ^ 2 / 2)))) ρ := by
    intro ρ _
    have := ((((hasDerivAt_pow 2 ρ).div_const 2).neg).exp.const_mul (2 * π)⁻¹).neg
    refine this.congr_deriv ?_
    simp
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 r)
  have hnn : ∀ ρ ∈ Ioc 0 r, 0 ≤ ρ * ((2 * π)⁻¹ * rexp (-(ρ ^ 2 / 2))) := fun ρ hρ => by
    have := hρ.1; positivity
  have hint : IntegrableOn (fun ρ : ℝ => ρ * ((2 * π)⁻¹ * rexp (-(ρ ^ 2 / 2)))) (Ioc 0 r) :=
    (hcont.intervalIntegrable 0 r).1.mono_set (by simp [hr])
  have := ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hnn))
  unfold rayDens
  rw [← this, ← intervalIntegral.integral_of_le hr, hFTC]
  congr 1
  simp
  ring

/-- Grinstead–Snell §5.2 Rayleigh density (PR-059), distribution function form. If `X` and `Y` are
independent standard normal variables then the length `√(X² + Y²)` satisfies
`P(√(X²+Y²) ≤ r) = 1 - e^{-r²/2}` for `r ≥ 0`, i.e. it has the Rayleigh density `r e^{-r²/2}`. -/
@[kb "grinsteadsnell2006" "§5.2 Rayleigh density, p. 223"]
theorem measureReal_sqrt_sq_add_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P)
    (hY : HasLaw Y (gaussianReal 0 1) P) (hXY : IndepFun X Y P) {r : ℝ} (hr : 0 ≤ r) :
    P.real {ω | √(X ω ^ 2 + Y ω ^ 2) ≤ r} = 1 - rexp (-(r ^ 2 / 2)) := by
  have hpi := Real.pi_pos
  have hjoint : P.map (fun ω => (X ω, Y ω)) = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY,
      hX.map_eq, hY.map_eq]
  set S : Set (ℝ × ℝ) := {p | √(p.1 ^ 2 + p.2 ^ 2) ≤ r} with hSdef
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hXYm : AEMeasurable (fun ω => (X ω, Y ω)) P := hX.aemeasurable.prodMk hY.aemeasurable
  have hM : ((gaussianReal 0 1).prod (gaussianReal 0 1)) S =
      ENNReal.ofReal (1 - rexp (-(r ^ 2 / 2))) := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, prod_withDensity (measurable_gaussianPDF 0 1)
      (measurable_gaussianPDF 0 1), withDensity_apply _ hS, ← Measure.volume_eq_prod,
      ← lintegral_indicator hS, ← lintegral_comp_polarCoord_symm]
    set B : Set (ℝ × ℝ) := Iic r ×ˢ univ with hB
    have hBm : MeasurableSet B := measurableSet_Iic.prod MeasurableSet.univ
    have hpt : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
        S.indicator (fun p : ℝ × ℝ => gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2)
          (polarCoord.symm p) = B.indicator (fun p : ℝ × ℝ => rayDens p.1) p := by
      rintro ⟨ρ, θ⟩ ⟨hρ, _⟩
      have hρ : 0 < ρ := hρ
      have hsq : √((ρ * cos θ) ^ 2 + (ρ * sin θ) ^ 2) = ρ := by
        have : (ρ * cos θ) ^ 2 + (ρ * sin θ) ^ 2 = ρ ^ 2 := by
          have := sin_sq_add_cos_sq θ
          linear_combination ρ ^ 2 * this
        rw [this, Real.sqrt_sq hρ.le]
      simp only [polarCoord_symm_apply, smul_eq_mul]
      by_cases h : ρ ≤ r
      · have h1 : (ρ * cos θ, ρ * sin θ) ∈ S := by
          show √((ρ * cos θ) ^ 2 + (ρ * sin θ) ^ 2) ≤ r
          rwa [hsq]
        have h2 : (ρ, θ) ∈ B := ⟨h, trivial⟩
        rw [indicator_of_mem h1, indicator_of_mem h2, gauss_prod_polar, rayDens,
          ← ENNReal.ofReal_mul hρ.le]
      · have h1 : (ρ * cos θ, ρ * sin θ) ∉ S := by
          show ¬ √((ρ * cos θ) ^ 2 + (ρ * sin θ) ^ 2) ≤ r
          rwa [hsq]
        have h2 : (ρ, θ) ∉ B := fun hh => h hh.1
        rw [indicator_of_notMem h1, indicator_of_notMem h2, mul_zero]
    rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt, lintegral_indicator hBm,
      Measure.restrict_restrict hBm]
    have hset : B ∩ polarCoord.target = Ioc 0 r ×ˢ Ioo (-π) π := by
      ext ⟨ρ, θ⟩
      simp only [hB, polarCoord_target, mem_inter_iff, mem_prod, mem_Iic, mem_univ, and_true,
        mem_Ioi, mem_Ioc, mem_Ioo]
      tauto
    rw [hset, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have := lintegral_prod_mul (μ := volume.restrict (Ioc 0 r)) (ν := volume.restrict (Ioo (-π) π))
      (f := rayDens) (g := fun _ => 1) (by
        unfold rayDens; exact (by fun_prop : Measurable _).aemeasurable) aemeasurable_const
    simp only [mul_one] at this
    rw [this, lintegral_rayDens hr]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul,
      Real.volume_Ioo]
    have he : rexp (-(r ^ 2 / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (by linarith))]
    congr 1
    field_simp
    ring
  have hset : {ω | √(X ω ^ 2 + Y ω ^ 2) ≤ r} = (fun ω => (X ω, Y ω)) ⁻¹' S := rfl
  rw [measureReal_def, hset, ← Measure.map_apply_of_aemeasurable hXYm hS, hjoint, hM,
    ENNReal.toReal_ofReal]
  have : rexp (-(r ^ 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]
  linarith

end Rayleigh

section GammaConv

private lemma cpow_cast_eq (a b : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) =
      (x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1) := by
  have h1 := Complex.ofReal_cpow hx.1 (a - 1)
  have h2 := Complex.ofReal_cpow (sub_nonneg.2 hx.2) (b - 1)
  rw [Complex.ofReal_mul, h1, h2]
  push_cast
  rfl

private lemma beta_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 := by
  have h := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h ⊢
  refine h.re.congr_fun (fun x hx => ?_) measurableSet_Ioc
  have := cpow_cast_eq a b (x := x) ⟨hx.1.le, hx.2⟩
  simp only [RCLike.re_to_complex]
  rw [← this, Complex.ofReal_re]

private lemma beta_value {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hB : Complex.betaIntegral (a : ℂ) (b : ℂ) =
      ((∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr (fun x hx =>
      (cpow_cast_eq a b (by rwa [uIcc_of_le zero_le_one] at hx)).symm)
  rw [hB, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at h
  have h' : Real.Gamma a * Real.Gamma b = Real.Gamma (a + b) * ∫ x in (0 : ℝ)..1,
      x ^ (a - 1) * (1 - x) ^ (b - 1) := by exact_mod_cast h
  have hg : 0 < Real.Gamma (a + b) := Real.Gamma_pos_of_pos (add_pos ha hb)
  rw [h']
  field_simp

/-- Convolution of two gamma densities with the same rate, at a point `z > 0`. -/
private lemma gammaPDF_conv_pos {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) {z : ℝ}
    (hz : 0 < z) :
    ∫⁻ y, gammaPDF a r (z - y) * gammaPDF b r y = gammaPDF (a + b) r z := by
  have hGa := Real.Gamma_pos_of_pos ha
  have hGb := Real.Gamma_pos_of_pos hb
  set G : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (r ^ a / Real.Gamma a * (z - y) ^ (a - 1) *
    rexp (-(r * (z - y))) * (r ^ b / Real.Gamma b * y ^ (b - 1) * rexp (-(r * y)))) with hG
  have key : (fun y => gammaPDF a r (z - y) * gammaPDF b r y) = (Icc 0 z).indicator G := by
    funext y
    by_cases hy : y ∈ Icc 0 z
    · rw [indicator_of_mem hy, gammaPDF_of_nonneg (sub_nonneg.2 hy.2), gammaPDF_of_nonneg hy.1,
        hG, ← ENNReal.ofReal_mul (by
          have := hy.2; have : 0 ≤ z - y := by linarith
          positivity)]
    · rw [indicator_of_notMem hy]
      by_cases h0 : 0 ≤ y
      · have : z < y := by
          by_contra h
          exact hy ⟨h0, not_lt.1 h⟩
        rw [gammaPDF_of_neg (by linarith : z - y < 0), zero_mul]
      · rw [gammaPDF_of_neg (not_le.1 h0), mul_zero]
  have hI := beta_value hb ha
  have hint := beta_intervalIntegrable hb ha
  have hIl : ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (t ^ (b - 1) * (1 - t) ^ (a - 1)) =
      ENNReal.ofReal (Real.Gamma b * Real.Gamma a / Real.Gamma (b + a)) := by
    rw [← hI, intervalIntegral.integral_of_le zero_le_one,
      ofReal_integral_eq_lintegral_ofReal hint.1
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => by
          have := ht.1; have : 0 ≤ 1 - t := by linarith [ht.2]
          positivity)),
      setLIntegral_congr Ioc_ae_eq_Icc]
  rw [key, lintegral_indicator measurableSet_Icc]
  have himg : Icc (0 : ℝ) z = (fun t => z * t) '' Icc 0 1 := by
    ext y
    simp only [mem_Icc, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨y / z, ⟨by positivity, by rw [div_le_one hz]; exact h2⟩, by field_simp⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨by positivity, by nlinarith⟩
  rw [himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f' := fun _ => z)
    (fun t _ => by simpa using ((hasDerivAt_id' t).const_mul z).hasDerivWithinAt)
    (fun s _ t _ h => mul_left_cancel₀ hz.ne' h)]
  set K : ℝ := r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * z ^ (a + b - 1) * rexp (-(r * z))
    with hK
  have hKnn : 0 ≤ K := by positivity
  have hzab : z ^ (a + b - 1) = z * z ^ (a - 1) * z ^ (b - 1) := by
    rw [show a + b - 1 = 1 + (a - 1) + (b - 1) by ring, Real.rpow_add hz, Real.rpow_add hz,
      Real.rpow_one]
  have hrab : r ^ (a + b) = r ^ a * r ^ b := Real.rpow_add hr a b
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |z| * G (z * t) =
      ENNReal.ofReal K * ENNReal.ofReal (t ^ (b - 1) * (1 - t) ^ (a - 1)) := by
    intro t ht
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    have hexp : rexp (-(r * (z * (1 - t)))) * rexp (-(r * (z * t))) = rexp (-(r * z)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e1 : z - z * t = z * (1 - t) := by ring
    rw [hG]
    beta_reduce
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hKnn]
    congr 1
    rw [abs_of_pos hz, e1, Real.mul_rpow hz.le h1t, Real.mul_rpow hz.le ht.1, hK, hzab, hrab,
      ← hexp]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Icc hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    hIl, ← ENNReal.ofReal_mul hKnn, gammaPDF_of_nonneg hz.le]
  congr 1
  rw [hK, add_comm b a]
  field_simp

/-- Grinstead–Snell Example 7.7 (PR-060), gamma convolution. Two independent variables with gamma laws of
the same rate `r` and shapes `a`, `b` have a sum with the gamma law of shape `a + b` and rate `r`. -/
@[kb "grinsteadsnell2006" "Example 7.7, p. 303"]
theorem map_add_gammaMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (h : IndepFun X Y P) {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hXa : P.map X = gammaMeasure a r) (hYb : P.map Y = gammaMeasure b r) :
    P.map (X + Y) = gammaMeasure (a + b) r := by
  have hf : ∀ a, Measurable (gammaPDF a r) := fun a => (measurable_gammaPDFReal a r).ennreal_ofReal
  unfold gammaMeasure at hXa hYb ⊢
  rw [h.map_add_eq_map_conv_map hX hY, hXa, hYb, conv_withDensity_eq_lconvolution (hf a) (hf b)]
  refine withDensity_congr_ae ?_
  have hfun : (gammaPDF a r ⋆ₗ gammaPDF b r) =
      fun z => ∫⁻ y, gammaPDF a r (z - y) * gammaPDF b r y := by
    funext z
    rw [lconvolution_comm]
    refine lintegral_congr fun y => ?_
    rw [mul_comm]
    simp only [neg_add_eq_sub]
  rw [hfun]
  filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with z hz0
  rcases lt_or_gt_of_ne (by simpa using hz0 : z ≠ 0) with hneg | hpos
  · have : ∀ y, gammaPDF a r (z - y) * gammaPDF b r y = 0 := by
      intro y
      by_cases hy : y < 0
      · rw [gammaPDF_of_neg hy, mul_zero]
      · rw [gammaPDF_of_neg (by linarith [not_lt.1 hy] : z - y < 0), zero_mul]
    simp only [this, lintegral_zero]
    rw [gammaPDF_of_neg hneg]
  · exact gammaPDF_conv_pos ha hb hr hpos

end GammaConv

section ChiN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell §5.2 chi-squared density and Example 7.7 (PR-060), `n` degrees of freedom. The sum
of squares of `n ≥ 1` independent standard normal variables has the gamma law with shape `n/2` and
rate `1/2` (chi-squared with `n` degrees of freedom). -/
@[kb "grinsteadsnell2006" "Example 7.7, p. 303"]
theorem hasLaw_sum_sq_gammaMeasure {ι : Type*} {Z : ι → Ω → ℝ}
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) (hmeas : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (s : Finset ι) (hs : s.Nonempty) :
    HasLaw (fun ω => ∑ i ∈ s, Z i ω ^ 2) (gammaMeasure ((s.card : ℝ) / 2) (1 / 2)) P := by
  have hsq : ∀ i, HasLaw (fun ω => Z i ω ^ 2) (gammaMeasure (1 / 2) (1 / 2)) P :=
    fun i => hasLaw_sq_gammaMeasure (hZ i)
  have hind' : iIndepFun (fun i ω => Z i ω ^ 2) P :=
    hind.comp (fun _ x => x ^ 2) (fun _ => by fun_prop)
  have hmeas' : ∀ i, Measurable (fun ω => Z i ω ^ 2) := fun i => (hmeas i).pow_const 2
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hsq a
  | cons a s ha hs ih =>
    have hind2 : IndepFun (fun ω => Z a ω ^ 2) (∑ i ∈ s, fun ω => Z i ω ^ 2) P :=
      (hind'.indepFun_finsetSum_of_notMem hmeas' ha).symm
    have hmsum : Measurable (∑ i ∈ s, fun ω => Z i ω ^ 2) :=
      by
        rw [show (∑ i ∈ s, fun ω => Z i ω ^ 2) = fun ω => ∑ i ∈ s, Z i ω ^ 2 by
          funext ω; simp [Finset.sum_apply]]
        exact Finset.measurable_sum _ (fun i _ => hmeas' i)
    have ihm : P.map (∑ i ∈ s, fun ω => Z i ω ^ 2) = gammaMeasure ((s.card : ℝ) / 2) (1 / 2) := by
      have := ih.map_eq
      simpa [Finset.sum_fn] using this
    have hcard : (0 : ℝ) < (s.card : ℝ) / 2 := by
      have := hs.card_pos
      positivity
    have := map_add_gammaMeasure (hmeas' a) hmsum hind2 (by norm_num) hcard (by norm_num)
      (hsq a).map_eq ihm
    have hfun : (fun ω => ∑ i ∈ Finset.cons a s ha, Z i ω ^ 2) =
        (fun ω => Z a ω ^ 2) + ∑ i ∈ s, fun ω => Z i ω ^ 2 := by
      funext ω
      simp [Finset.sum_cons, Finset.sum_apply]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact (hmeas' a).add hmsum |>.aemeasurable
    · rw [hfun, this]
      congr 1
      rw [Finset.card_cons]
      push_cast
      ring

end ChiN

section Maxwell

private lemma gamma_three_halves_sq {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal |2 * s| * gammaPDF (3 / 2) (1 / 2) (s ^ 2) =
      ENNReal.ofReal (√(2 / π) * s ^ 2 * rexp (-(s ^ 2 / 2))) := by
  rw [gammaPDF_of_nonneg (sq_nonneg s), ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have h1 : (s ^ 2) ^ ((3 / 2 : ℝ) - 1) = s := by
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_sq hs]
  have h2 : ((1 / 2 : ℝ)) ^ ((3 / 2 : ℝ)) = (1 / 2) * (√2)⁻¹ := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv]
  have h3 : Real.Gamma (3 / 2) = √π / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hs2 : 0 < √2 := by positivity
  have hsp : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [h1, h2, h3, abs_of_nonneg (by positivity : 0 ≤ 2 * s), Real.sqrt_div (by norm_num)]
  have : -(1 / 2 * s ^ 2) = -(s ^ 2 / 2) := by ring
  rw [this]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Grinstead–Snell §5.2 Maxwell density (PR-059), distribution function form. If `V₀, V₁, V₂` are
independent standard normal variables, the length `√(V₀² + V₁² + V₂²)` satisfies
`P(length ≤ r) = ∫₀ʳ √(2/π) s² e^{-s²/2} ds` for `r ≥ 0`, i.e. it has the Maxwell density. -/
@[kb "grinsteadsnell2006" "§5.2 Maxwell density, p. 223"]
theorem measureReal_sqrt_sum_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Fin 3 → Ω → ℝ} (hV : ∀ i, HasLaw (V i) (gaussianReal 0 1) P)
    (hmeas : ∀ i, Measurable (V i)) (hind : iIndepFun V P) {r : ℝ} (hr : 0 ≤ r) :
    P.real {ω | √(∑ i, V i ω ^ 2) ≤ r} =
      ∫ s in (0 : ℝ)..r, √(2 / π) * s ^ 2 * rexp (-(s ^ 2 / 2)) := by
  have hW := hasLaw_sum_sq_gammaMeasure hV hmeas hind Finset.univ Finset.univ_nonempty
  have hcard : ((Finset.univ : Finset (Fin 3)).card : ℝ) / 2 = 3 / 2 := by simp
  rw [hcard] at hW
  have hset : {ω | √(∑ i, V i ω ^ 2) ≤ r} = (fun ω => ∑ i, V i ω ^ 2) ⁻¹' Iic (r ^ 2) := by
    ext ω
    simp only [mem_setOf_eq, mem_preimage, mem_Iic]
    exact Real.sqrt_le_left hr
  have hmap := Measure.map_apply_of_aemeasurable hW.aemeasurable (measurableSet_Iic (a := r ^ 2))
  rw [hW.map_eq, gammaMeasure, withDensity_apply _ measurableSet_Iic] at hmap
  have hL : ∫⁻ x in Iic (r ^ 2), gammaPDF (3 / 2) (1 / 2) x =
      ENNReal.ofReal (∫ s in (0 : ℝ)..r, √(2 / π) * s ^ 2 * rexp (-(s ^ 2 / 2))) := by
    rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ (sq_nonneg r),
      lintegral_gammaPDF_of_nonpos (le_refl 0), zero_add]
    have himg : Icc (0 : ℝ) (r ^ 2) = (fun s : ℝ => s ^ 2) '' Icc 0 r := by
      ext y
      simp only [mem_Icc, mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨√y, ⟨Real.sqrt_nonneg _, Real.sqrt_le_left hr |>.2 h2⟩, Real.sq_sqrt h1⟩
      · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
        exact ⟨by positivity, by nlinarith⟩
    rw [himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f' := fun s => 2 * s)
      (fun s _ => by simpa using (hasDerivAt_pow 2 s).hasDerivWithinAt)
      (fun a ha b hb h => by
        have := ha.1; have := hb.1
        have h' : a ^ 2 = b ^ 2 := h
        nlinarith)]
    rw [setLIntegral_congr_fun measurableSet_Icc (fun s hs => gamma_three_halves_sq hs.1)]
    have hcont : Continuous (fun s : ℝ => √(2 / π) * s ^ 2 * rexp (-(s ^ 2 / 2))) := by fun_prop
    rw [intervalIntegral.integral_of_le hr, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
        ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s _ => by positivity))]
  rw [hL] at hmap
  rw [measureReal_def, hset, ← hmap,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hr fun s _ => by positivity)]

end Maxwell

end UndergradKB.Probability
