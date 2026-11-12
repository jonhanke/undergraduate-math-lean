import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 3 (Examples of Functions): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`). -/

namespace UndergradKB.ComplexAnalysis.Course.Beck3
open Complex

/-- Beck Definition 3.4.1 (CX-046). exp(x + iy) = e^x (cos y + i sin y). -/
@[kb "beck2025" "Definition 3.4.1, p. 57"]
theorem exp_eq_polar (x y : ℝ) :
    exp (x + y * I) = Real.exp x * (Real.cos y + Real.sin y * I) := by
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Beck Proposition 3.4.2 (CX-047), parts (a)-(f). -/
@[kb "beck2025" "Proposition 3.4.2, p. 58"]
theorem exp_properties :
    (∀ z₁ z₂ : ℂ, exp z₁ * exp z₂ = exp (z₁ + z₂)) ∧
    (∀ z : ℂ, 1 / exp z = exp (-z)) ∧
    (∀ z : ℂ, exp (z + 2 * Real.pi * I) = exp z) ∧
    (∀ z : ℂ, ‖exp z‖ = Real.exp z.re) ∧
    (∀ z : ℂ, exp z ≠ 0) ∧
    (∀ z : ℂ, HasDerivAt exp (exp z) z) := by
  refine ⟨fun a b => (Complex.exp_add a b).symm, fun z => ?_, fun z => ?_, Complex.norm_exp,
    Complex.exp_ne_zero, Complex.hasDerivAt_exp⟩
  · rw [one_div, Complex.exp_neg]
  · rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Beck Definition 3.4.4 (CX-048). Sine, cosine and tangent through the exponential function. -/
@[kb "beck2025" "Definition 3.4.4, p. 59"]
theorem sin_cos_tan_via_exp (z : ℂ) :
    sin z = (exp (I * z) - exp (-(I * z))) / (2 * I) ∧
    cos z = (exp (I * z) + exp (-(I * z))) / 2 ∧
    tan z = -I * ((exp (2 * I * z) - 1) / (exp (2 * I * z) + 1)) := by
  have hs : sin z = (exp (I * z) - exp (-(I * z))) / (2 * I) := by
    rw [Complex.sin, show -z * I = -(I * z) by ring, show z * I = I * z by ring,
      eq_div_iff (by simp)]
    linear_combination (exp (-(I * z)) - exp (I * z)) * Complex.I_sq
  have hc : cos z = (exp (I * z) + exp (-(I * z))) / 2 := by
    rw [Complex.cos, show -z * I = -(I * z) by ring, show z * I = I * z by ring]
  refine ⟨hs, hc, ?_⟩
  set w := exp (I * z) with hw
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have h2 : exp (2 * I * z) = w ^ 2 := by
    rw [hw, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hinv : exp (-(I * z)) = w⁻¹ := by rw [hw, Complex.exp_neg]
  rw [Complex.tan_eq_sin_div_cos, hs, hc, h2, hinv, ← Complex.inv_I]
  by_cases hc2 : w ^ 2 + 1 = 0
  · have h3 : w + w⁻¹ = 0 := by
      have : w * (w + w⁻¹) = 0 := by field_simp; linear_combination hc2
      exact (mul_eq_zero.1 this).resolve_left hw0
    simp [hc2, h3]
  · have hI : I ≠ 0 := Complex.I_ne_zero
    field_simp

/-- Beck Proposition 3.4.5 (CX-049). Parity, periodicity, shifts by pi/2, addition formulas,
Pythagorean identity, double angle formula and derivatives of sine and cosine. -/
@[kb "beck2025" "Proposition 3.4.5, p. 59"]
theorem sin_cos_properties :
    (∀ z : ℂ, sin (-z) = -sin z) ∧ (∀ z : ℂ, cos (-z) = cos z) ∧
    (∀ z : ℂ, sin (z + 2 * Real.pi) = sin z) ∧ (∀ z : ℂ, cos (z + 2 * Real.pi) = cos z) ∧
    (∀ z : ℂ, tan (z + Real.pi) = tan z) ∧
    (∀ z : ℂ, sin (z + Real.pi / 2) = cos z) ∧ (∀ z : ℂ, cos (z + Real.pi / 2) = -sin z) ∧
    (∀ z₁ z₂ : ℂ, sin (z₁ + z₂) = sin z₁ * cos z₂ + cos z₁ * sin z₂) ∧
    (∀ z₁ z₂ : ℂ, cos (z₁ + z₂) = cos z₁ * cos z₂ - sin z₁ * sin z₂) ∧
    (∀ z : ℂ, cos z ^ 2 + sin z ^ 2 = 1) ∧
    (∀ z : ℂ, cos z ^ 2 - sin z ^ 2 = cos (2 * z)) ∧
    (∀ z : ℂ, HasDerivAt sin (cos z) z) ∧ (∀ z : ℂ, HasDerivAt cos (-sin z) z) := by
  refine ⟨Complex.sin_neg, Complex.cos_neg, fun z => ?_, fun z => ?_, fun z => ?_,
    fun z => ?_, fun z => ?_, Complex.sin_add, Complex.cos_add,
    fun z => by rw [add_comm]; exact Complex.sin_sq_add_cos_sq z,
    fun z => (Complex.cos_two_mul' z).symm, Complex.hasDerivAt_sin, Complex.hasDerivAt_cos⟩
  · simp [Complex.sin_add]
  · simp [Complex.cos_add]
  · rw [Complex.tan_eq_sin_div_cos, Complex.tan_eq_sin_div_cos]
    simp [Complex.sin_add, Complex.cos_add]
  · simp [Complex.sin_add]
  · simp [Complex.cos_add]

/-- Beck Definition 3.4.6 (CX-050). Hyperbolic sine and cosine via exp, their derivatives and the
relations to sine and cosine. -/
@[kb "beck2025" "Definition 3.4.6, p. 60"]
theorem sinh_cosh_properties :
    (∀ z : ℂ, sinh z = (exp z - exp (-z)) / 2) ∧ (∀ z : ℂ, cosh z = (exp z + exp (-z)) / 2) ∧
    (∀ z : ℂ, HasDerivAt sinh (cosh z) z) ∧ (∀ z : ℂ, HasDerivAt cosh (sinh z) z) ∧
    (∀ z : ℂ, sinh (I * z) = I * sin z) ∧ (∀ z : ℂ, cosh (I * z) = cos z) := by
  refine ⟨fun z => rfl, fun z => rfl, Complex.hasDerivAt_sinh, Complex.hasDerivAt_cosh,
    fun z => ?_, fun z => ?_⟩
  · rw [mul_comm, Complex.sinh_mul_I, mul_comm]
  · rw [mul_comm, Complex.cosh_mul_I]

/-- Beck Definition 3.5.2 (CX-052). The principal logarithm is `ln |z| + i Arg z`, where the
principal argument lies in `(-π, π]`. -/
@[kb "beck2025" "Definition 3.5.2, p. 61"]
theorem principal_log (z : ℂ) (hz : z ≠ 0) :
    Complex.arg z ∈ Set.Ioc (-Real.pi) Real.pi ∧
      log z = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * I := by
  have _ := hz
  exact ⟨⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩, rfl⟩

/-- Beck Example 3.5.3 (CX-052). Sample values of the principal logarithm. -/
@[kb "beck2025" "Example 3.5.3, p. 61"]
theorem principal_log_values :
    log 2 = (Real.log 2 : ℂ) ∧ log I = Real.pi / 2 * I ∧
    log (-3) = (Real.log 3 : ℂ) + Real.pi * I ∧
    log (1 - I) = (1 / 2 * Real.log 2 : ℝ) - (Real.pi / 4) * I := by
  refine ⟨?_, Complex.log_I, ?_, ?_⟩
  · simp
  · have harg : arg (-3 : ℂ) = Real.pi := by
      simpa using Complex.arg_ofReal_of_neg (x := -3) (by norm_num)
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, harg]
  · have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have harg : arg (1 - I) = -(Real.pi / 4) := by
      have := Complex.arg_mul_cos_add_sin_mul_I h2
        (θ := -(Real.pi / 4)) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at this
      rw [← this]
      congr 1
      rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
      apply Complex.ext
      · simp; nlinarith
      · simp; nlinarith
    have hn : ‖(1 - I : ℂ)‖ = Real.sqrt 2 := by
      rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num
    apply Complex.ext
    · simp [Complex.log_re, hn, Real.log_sqrt]
      ring
    · simp [Complex.log_im, harg]

/-- Beck Proposition 3.5.4 (CX-053). A branch of the logarithm on a region `G` (a continuous `L`
with `exp (L z) = z`) is differentiable with derivative `1 / z`. -/
@[kb "beck2025" "Proposition 3.5.4, p. 62"]
theorem branch_of_log_deriv (G : Set ℂ) (hG : IsOpen G) (L : ℂ → ℂ) (hL : ContinuousOn L G)
    (hexp : ∀ z ∈ G, exp (L z) = z) (z : ℂ) (hz : z ∈ G) : HasDerivAt L (1 / z) z := by
  have hz0 : z ≠ 0 := by rw [← hexp z hz]; exact Complex.exp_ne_zero _
  have h2 := HasDerivAt.of_local_left_inverse (f := exp) (g := L) (a := z)
    (hL.continuousAt (hG.mem_nhds hz)) (by simpa [hexp z hz] using Complex.hasDerivAt_exp (L z))
    hz0
    (by filter_upwards [hG.mem_nhds hz] with w hw using hexp w hw)
  simpa [hexp z hz] using h2

/-- Beck Definition 3.5.5 (CX-054). The principal value of `a^b` is `exp (b Log a)`. -/
@[kb "beck2025" "Definition 3.5.5, p. 62"]
theorem cpow_eq_exp_mul_log (a b : ℂ) (ha : a ≠ 0) : a ^ b = exp (b * log a) := by
  rw [Complex.cpow_def_of_ne_zero ha, mul_comm]

end UndergradKB.ComplexAnalysis.Course.Beck3
