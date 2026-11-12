import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.CharacteristicFunction
import UndergradKB.Common.Attr

/-!
# The average of independent standard Cauchy variables is standard Cauchy

Grinstead–Snell Examples 7.6 and 8.8. The key tool is the characteristic function of the standard
Cauchy law, `exp (-|t|)`, obtained from the Fourier transform of `exp (-|x|)` and Fourier
inversion.
-/

namespace UndergradKB.Probability

open MeasureTheory ProbabilityTheory Set Complex
open scoped FourierTransform

/-- The function `x ↦ exp (-|x|)` as a complex-valued function. -/
noncomputable def expNegAbs (x : ℝ) : ℂ := ((Real.exp (-|x|) : ℝ) : ℂ)

theorem integrable_expNegAbs_mul (a : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (((-a * x : ℝ) : ℂ) * I) * expNegAbs x) := by
  have h1 : IntegrableOn (fun x : ℝ => Complex.exp (((-1 - a * I) : ℂ) * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp) 0
  have h2 : IntegrableOn (fun x : ℝ => Complex.exp (((1 - a * I) : ℂ) * x)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simp) 0
  have e1 : EqOn (fun x : ℝ => Complex.exp (((-a * x : ℝ) : ℂ) * I) * expNegAbs x)
      (fun x : ℝ => Complex.exp (((-1 - a * I) : ℂ) * x)) (Ioi 0) := by
    intro x hx
    simp only [expNegAbs, abs_of_pos (mem_Ioi.1 hx)]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have e2 : EqOn (fun x : ℝ => Complex.exp (((-a * x : ℝ) : ℂ) * I) * expNegAbs x)
      (fun x : ℝ => Complex.exp (((1 - a * I) : ℂ) * x)) (Iic 0) := by
    intro x hx
    simp only [expNegAbs, abs_of_nonpos (mem_Iic.1 hx)]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have : IntegrableOn (fun x : ℝ => Complex.exp (((-a * x : ℝ) : ℂ) * I) * expNegAbs x) univ := by
    rw [← Iic_union_Ioi (a := (0 : ℝ))]
    exact (h2.congr_fun e2.symm measurableSet_Iic).union (h1.congr_fun e1.symm measurableSet_Ioi)
  simpa using this

theorem integral_expNegAbs_mul (a : ℝ) :
    ∫ x : ℝ, Complex.exp (((-a * x : ℝ) : ℂ) * I) * expNegAbs x = 2 / (1 + (a : ℂ) ^ 2) := by
  have h1 : IntegrableOn (fun x : ℝ => Complex.exp (((-1 - a * I) : ℂ) * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp) 0
  have h2 : IntegrableOn (fun x : ℝ => Complex.exp (((1 - a * I) : ℂ) * x)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simp) 0
  have e1 : EqOn (fun x : ℝ => Complex.exp (((-a * x : ℝ) : ℂ) * I) * expNegAbs x)
      (fun x : ℝ => Complex.exp (((-1 - a * I) : ℂ) * x)) (Ioi 0) := by
    intro x hx
    simp only [expNegAbs, abs_of_pos (mem_Ioi.1 hx)]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have e2 : EqOn (fun x : ℝ => Complex.exp (((-a * x : ℝ) : ℂ) * I) * expNegAbs x)
      (fun x : ℝ => Complex.exp (((1 - a * I) : ℂ) * x)) (Iic 0) := by
    intro x hx
    simp only [expNegAbs, abs_of_nonpos (mem_Iic.1 hx)]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      (h2.congr_fun e2.symm measurableSet_Iic) (h1.congr_fun e1.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Iic e2,
    setIntegral_congr_fun measurableSet_Ioi e1, integral_exp_mul_complex_Iic (by simp),
    integral_exp_mul_complex_Ioi (by simp)]
  have h3 : (1 - (a : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have h4 : (-1 - (a : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have h5 : (1 + (a : ℂ) ^ 2) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [sq] at this; nlinarith [sq_nonneg a]
  field_simp
  ring_nf
  simp [Complex.I_sq]; ring

theorem fourier_expNegAbs (w : ℝ) :
    𝓕 expNegAbs w = 2 / (1 + (((2 * Real.pi * w : ℝ)) : ℂ) ^ 2) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_expNegAbs_mul (2 * Real.pi * w)]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [smul_eq_mul]
  rw [show (-2 * Real.pi * v * w) = -(2 * Real.pi * w) * v by ring]

theorem continuous_expNegAbs : Continuous expNegAbs := by
  unfold expNegAbs; fun_prop

theorem integrable_expNegAbs : Integrable expNegAbs := by
  simpa using integrable_expNegAbs_mul 0

theorem integrable_fourier_expNegAbs : Integrable (𝓕 expNegAbs) := by
  have h : Integrable (fun x : ℝ => (2 * (1 + (2 * Real.pi * x) ^ 2)⁻¹ : ℝ)) := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    exact (integrable_inv_one_add_sq.const_mul 2).comp_mul_left' hpi
  have h2 := h.ofReal (𝕜 := ℂ)
  refine h2.congr (ae_of_all _ fun x => ?_)
  rw [fourier_expNegAbs]
  push_cast
  rw [div_eq_mul_inv]
  rfl

theorem inversion_expNegAbs (v : ℝ) :
    ∫ ξ : ℝ, Complex.exp (((2 * Real.pi * (ξ * v) : ℝ) : ℂ) * I) * (2 / (1 + (((2 * Real.pi * ξ : ℝ)) : ℂ) ^ 2))
      = expNegAbs v := by
  have h := continuous_expNegAbs.fourierInv_fourier_eq integrable_expNegAbs
    integrable_fourier_expNegAbs
  have := congrFun h v
  rw [Real.fourierInv_eq'] at this
  simp only [fourier_expNegAbs, smul_eq_mul] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp
  left; ring_nf

theorem charFun_cauchyMeasure_eq_integral (γ : NNReal) (hγ : γ ≠ 0) (t : ℝ) :
    charFun (cauchyMeasure 0 γ) t =
      ∫ x : ℝ, (cauchyPDF 0 γ x).toReal • Complex.exp (t * x * I) := by
  rw [charFun_apply_real, cauchyMeasure_of_scale_ne_zero 0 hγ,
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 γ)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]

/-- The characteristic function of the standard Cauchy law is `exp (-|t|)`. -/
theorem charFun_cauchyMeasure_one (t : ℝ) :
    charFun (cauchyMeasure 0 1) t = ((Real.exp (-|t|) : ℝ) : ℂ) := by
  rw [charFun_cauchyMeasure_eq_integral 1 one_ne_zero]
  set G : ℝ → ℂ := fun x => (cauchyPDF 0 1 x).toReal • Complex.exp (t * x * I) with hG
  have hscale := Measure.integral_comp_mul_left G (2 * Real.pi)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : ∀ ξ : ℝ, G (2 * Real.pi * ξ) =
      ((2 * Real.pi : ℝ)⁻¹ : ℂ) * (Complex.exp (((2 * Real.pi * (ξ * t) : ℝ) : ℂ) * I) *
        (2 / (1 + (((2 * Real.pi * ξ : ℝ)) : ℂ) ^ 2))) := by
    intro ξ
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hd : (1 + (2 * (Real.pi : ℂ) * ξ) ^ 2) ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp [sq] at this; nlinarith [sq_nonneg (2 * Real.pi * ξ)]
    simp only [hG, cauchyPDF, cauchyPDFReal_def]
    rw [Complex.real_smul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    have e : Complex.exp (↑t * ↑(2 * Real.pi * ξ) * I) =
        Complex.exp (((2 * Real.pi * (ξ * t) : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    rw [e]
    simp only [NNReal.coe_one, sub_zero]
    push_cast
    rw [show ((2 * (Real.pi : ℂ) * ξ) ^ 2 + 1 ^ 2) = 1 + (2 * (Real.pi : ℂ) * ξ) ^ 2 by ring]
    field_simp
  have h2 : ∫ x, G (2 * Real.pi * x) = ((2 * Real.pi : ℝ)⁻¹ : ℂ) * expNegAbs t := by
    simp_rw [h1]
    rw [integral_const_mul, inversion_expNegAbs]
  rw [h2, abs_of_pos (inv_pos.2 hpos), Complex.real_smul] at hscale
  have hne : ((2 * Real.pi : ℝ)⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hpi
  rw [Complex.ofReal_inv] at hscale
  exact (mul_left_cancel₀ hne hscale).symm

/-- The characteristic function of the Cauchy law with location `0` and scale `γ > 0`. -/
theorem charFun_cauchyMeasure (γ : NNReal) (hγ : γ ≠ 0) (t : ℝ) :
    charFun (cauchyMeasure 0 γ) t = ((Real.exp (-(γ * |t|)) : ℝ) : ℂ) := by
  have hγpos : (0 : ℝ) < γ := by positivity
  rw [charFun_cauchyMeasure_eq_integral γ hγ]
  set G : ℝ → ℂ := fun x => (cauchyPDF 0 γ x).toReal • Complex.exp (t * x * I) with hG
  have hscale := Measure.integral_comp_mul_left G (γ : ℝ)
  have h1 : ∀ y : ℝ, G ((γ : ℝ) * y) = ((γ : ℝ)⁻¹ : ℝ) •
      ((cauchyPDF 0 1 y).toReal • Complex.exp (((γ : ℝ) * t : ℝ) * y * I)) := by
    intro y
    have hr : (cauchyPDF 0 γ ((γ : ℝ) * y)).toReal = (γ : ℝ)⁻¹ * (cauchyPDF 0 1 y).toReal := by
      rw [cauchyPDF, cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos 0 hγ _).le,
        ENNReal.toReal_ofReal (cauchyPDF_pos 0 one_ne_zero _).le, cauchyPDFReal_def,
        cauchyPDFReal_def]
      simp only [NNReal.coe_one, sub_zero]
      field_simp
    simp only [hG]
    rw [hr, smul_smul, Complex.real_smul, Complex.real_smul]
    congr 2
    push_cast; ring
  have h2 : ∫ y, G ((γ : ℝ) * y) = ((γ : ℝ)⁻¹ : ℝ) • charFun (cauchyMeasure 0 1) ((γ : ℝ) * t) := by
    rw [charFun_cauchyMeasure_eq_integral 1 one_ne_zero]
    simp_rw [h1]
    rw [integral_smul]
  rw [h2, charFun_cauchyMeasure_one, abs_of_pos (inv_pos.2 hγpos), abs_mul,
    abs_of_pos hγpos] at hscale
  simp only [Complex.real_smul, Complex.ofReal_inv] at hscale
  have hne : ((γ : ℝ) : ℂ)⁻¹ ≠ 0 := by
    exact_mod_cast inv_ne_zero hγpos.ne'
  exact (mul_left_cancel₀ hne hscale).symm

/-- Grinstead–Snell Example 7.6 (PR-092). The sum of two independent standard Cauchy random
variables is Cauchy with scale parameter `2`. -/
@[kb "grinsteadsnell2006" "Example 7.6, p. 302"]
theorem cauchy_sum_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : HasLaw X (cauchyMeasure 0 1) P) (hY : HasLaw Y (cauchyMeasure 0 1) P)
    (hXY : IndepFun X Y P) :
    P.map (fun ω => X ω + Y ω) = cauchyMeasure 0 2 := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have h := congrFun (hXY.charFun_map_fun_add_eq_mul hX.aemeasurable hY.aemeasurable) t
  rw [h, Pi.mul_apply, hX.map_eq, hY.map_eq, charFun_cauchyMeasure_one,
    charFun_cauchyMeasure 2 two_ne_zero, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  push_cast; ring

/-- Grinstead–Snell Example 7.6 (PR-092). The average of two independent standard Cauchy random
variables is again standard Cauchy. -/
@[kb "grinsteadsnell2006" "Example 7.6, p. 302"]
theorem cauchy_average_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : HasLaw X (cauchyMeasure 0 1) P)
    (hY : HasLaw Y (cauchyMeasure 0 1) P) (hXY : IndepFun X Y P) :
    P.map (fun ω => 2⁻¹ * (X ω + Y ω)) = cauchyMeasure 0 1 := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hm : AEMeasurable (fun ω => X ω + Y ω) P := hX.aemeasurable.add hY.aemeasurable
  rw [charFun_map_mul_comp hm, cauchy_sum_two P X Y hX hY hXY, charFun_cauchyMeasure 2 two_ne_zero,
    charFun_cauchyMeasure_one]
  congr 2
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  push_cast; ring

/-- Grinstead–Snell Example 8.8 (PR-092). The average of `n` independent standard Cauchy random
variables is again standard Cauchy (so averaging does not improve the estimate, and the law of
large numbers fails). -/
@[kb "grinsteadsnell2006" "Example 8.8, p. 328"]
theorem cauchy_average {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) [NeZero n] (X : Fin n → Ω → ℝ) (hX : ∀ i, HasLaw (X i) (cauchyMeasure 0 1) P)
    (hind : iIndepFun X P) :
    P.map (fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω) = cauchyMeasure 0 1 := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hm : AEMeasurable (fun ω => ∑ i, X i ω) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => (hX i).aemeasurable
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hs := congrFun (hind.charFun_map_fun_sum_eq_prod (fun i => (hX i).aemeasurable)) ((n : ℝ)⁻¹ * t)
  simp only [Finset.prod_apply, fun i => (hX i).map_eq, charFun_cauchyMeasure_one] at hs
  rw [charFun_map_mul_comp hm, hs, charFun_cauchyMeasure_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  rw [abs_mul, abs_inv, Nat.abs_cast]
  field_simp

end UndergradKB.Probability
