import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 4 (Integration): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`).
Beck's Example 4.3.5 (an integral over a square) is not covered by this layer. -/

namespace UndergradKB.ComplexAnalysis.Course.Beck4
open Complex MeasureTheory Metric Set
open scoped Real

/-- Beck §4.1, formula (4.1) (CX-055). The integral of a continuous complex-valued function of a
real variable is the integral of its real part plus `i` times the integral of its imaginary part. -/
@[kb "beck2025" "Integral of a complex-valued function of a real variable §4.1, p. 70"]
theorem integral_eq_re_add_im_mul_I (g : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ∫ t in a..b, g t =
      ((∫ t in a..b, (g t).re : ℝ) : ℂ) + ((∫ t in a..b, (g t).im : ℝ) : ℂ) * I := by
  have hint : IntegrableOn g (Ioc a b) :=
    (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  simp only [intervalIntegral.integral_of_le hab]
  exact (integral_re_add_im hint).symm

/-- Beck Example 4.1.9 (CX-060). The integral of `1/(z - w)` over a circle about `w`, traversed
counterclockwise, is `2πi` (here for a circle `C[c, R]` with `w` inside, via `circleIntegral`). -/
@[kb "beck2025" "Example 4.1.9, p. 74"]
theorem integral_inv_sub_circle (c w : ℂ) (R : ℝ) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I :=
  circleIntegral.integral_sub_inv_of_mem_ball hw

/-- Beck Example 4.1.9 (CX-060). The same integral written with the parametrisation
`γ(t) = w + R e^{it}`, `γ'(t) = i R e^{it}`, `0 ≤ t ≤ 2π`. -/
@[kb "beck2025" "Example 4.1.9, p. 74"]
theorem integral_inv_sub_circle_param (w : ℂ) (R : ℝ) (hR : 0 < R) :
    ∫ t in (0 : ℝ)..2 * π, ((w + R * exp (t * I)) - w)⁻¹ * (I * R * exp (t * I)) =
      2 * π * I := by
  have h := integral_inv_sub_circle w w R (mem_ball_self hR)
  simp only [circleIntegral, deriv_circleMap, circleMap, smul_eq_mul] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- Beck Theorem 4.4.1 (CX-069). Cauchy's integral formula on a circle: if `f` is holomorphic in an
open set containing the closed disk `D[w, R]`, then `f w = (2πi)⁻¹ ∮_{C[w,R]} f z / (z - w) dz`. -/
@[kb "beck2025" "Theorem 4.4.1, p. 81"]
theorem cauchy_integral_formula_circle (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (w : ℂ) (R : ℝ)
    (hR : 0 < R) (hsub : closedBall w R ⊆ U) (hf : DifferentiableOn ℂ f U) :
    f w = (2 * π * I)⁻¹ * ∮ z in C(w, R), f z / (z - w) := by
  have _ := hU
  have hd : DiffContOnCl ℂ f (ball w R) :=
    ⟨(hf.mono (ball_subset_closedBall.trans hsub)),
      (hf.mono (by rw [closure_ball w hR.ne']; exact hsub)).continuousOn⟩
  have h := hd.circleIntegral_sub_inv_smul (mem_ball_self hR)
  have h2 : (∮ z in C(w, R), f z / (z - w)) = (2 * π * I) * f w := by
    rw [← smul_eq_mul, ← h]
    refine circleIntegral.integral_congr hR.le fun z _ => ?_
    simp [div_eq_inv_mul]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]

/-- Beck Corollary 4.4.2 (CX-069). Mean value property: for `f = u + iv` holomorphic in an open set
containing `D[w, R]`, the values `f w`, `u w`, `v w` are the averages over the circle. -/
@[kb "beck2025" "Corollary 4.4.2, p. 81"]
theorem mean_value_circle (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (w : ℂ) (R : ℝ)
    (hR : 0 < R) (hsub : closedBall w R ⊆ U) (hf : DifferentiableOn ℂ f U) :
    f w = (1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, f (w + R * exp (t * I)) ∧
    (f w).re = (1 / (2 * π)) * ∫ t in (0 : ℝ)..2 * π, (f (w + R * exp (t * I))).re ∧
    (f w).im = (1 / (2 * π)) * ∫ t in (0 : ℝ)..2 * π, (f (w + R * exp (t * I))).im := by
  have _ := hU
  have hd : DiffContOnCl ℂ f (ball w |R|) := by
    rw [abs_of_pos hR]
    exact ⟨(hf.mono (ball_subset_closedBall.trans hsub)),
      (hf.mono (by rw [closure_ball w hR.ne']; exact hsub)).continuousOn⟩
  have h := hd.circleAverage
  rw [Real.circleAverage_def] at h
  have hcont : Continuous fun t : ℝ => f (circleMap w R t) :=
    (hf.continuousOn.mono hsub).comp_continuous (continuous_circleMap w R)
      (fun t => by simpa [abs_of_pos hR] using (circleMap_mem_sphere w hR.le t).le)
  have hii : IntervalIntegrable (fun t : ℝ => f (circleMap w R t)) volume 0 (2 * π) :=
    hcont.intervalIntegrable _ _
  have e1 : f w = (1 / (2 * π) : ℝ) * ∫ t in (0 : ℝ)..2 * π, f (w + R * exp (t * I)) := by
    rw [← h]
    simp only [circleMap, Complex.real_smul]
    push_cast
    ring
  refine ⟨e1, ?_, ?_⟩
  · have := congrArg Complex.re e1
    rw [Complex.re_ofReal_mul] at this
    rw [this]
    congr 1
    exact (ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hii).symm
  · have := congrArg Complex.im e1
    rw [Complex.im_ofReal_mul] at this
    rw [this]
    congr 1
    exact (ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hii).symm

/-- Beck Example 4.4.3 (CX-069). `∮_{C[i,1]} dz / (z² + 1) = π`. -/
@[kb "beck2025" "Example 4.4.3, p. 83"]
theorem cauchy_formula_example : (∮ z in C(I, 1), ((z : ℂ) ^ 2 + 1)⁻¹) = (π : ℂ) := by
  have h1 : ∀ z : ℂ, (z ^ 2 + 1)⁻¹ = (z + I)⁻¹ / (z - I) := by
    intro z
    have : z ^ 2 + 1 = (z - I) * (z + I) := by linear_combination Complex.I_sq
    rw [this, mul_inv, div_eq_inv_mul, mul_comm]
  simp_rw [h1]
  have hsub : closedBall I 1 ⊆ {z : ℂ | z ≠ -I} := by
    intro z hz hzI
    have : dist z I ≤ 1 := hz
    rw [hzI, dist_eq_norm] at this
    have h2 : (-I - I : ℂ) = -(2 * I) := by ring
    rw [h2, norm_neg, norm_mul] at this
    simp at this

  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (z + I)⁻¹) {z : ℂ | z ≠ -I} := by
    intro z hz
    have : z + I ≠ 0 := fun h => hz (eq_neg_of_add_eq_zero_left h)
    exact ((differentiableAt_id.add_const I).inv this).differentiableWithinAt
  have key := cauchy_integral_formula_circle (fun z : ℂ => (z + I)⁻¹) {z : ℂ | z ≠ -I}
    isOpen_ne I 1 one_pos hsub hdiff
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have e : (∮ z in C(I, 1), (z + I)⁻¹ / (z - I)) = 2 * π * I * (I + I)⁻¹ := by
    rw [key]
    have : (2 * (π : ℂ) * I) ≠ 0 := by simp [hpi, hI]
    field_simp
  rw [e]
  have : (I + I : ℂ) = 2 * I := by ring
  rw [this]
  field_simp

end UndergradKB.ComplexAnalysis.Course.Beck4
