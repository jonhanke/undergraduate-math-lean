import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

/-!
# The integral formula for a harmonic conjugate on the plane (row CX-085)

Beck et al., Theorem 6.1.9: if `u` is harmonic on `ℂ`, then
`v(x, y) = ∫₀^y u_x(x, t) dt - ∫₀^x u_y(t, 0) dt` is a harmonic conjugate of `u`, i.e.
`u + i v` is entire. Also Example 6.1.8: for `u(x, y) = x y`, `v = -(x² - y²)/2`.

Instead of the Leibniz rule used in the book, we take an entire `F` with `Re F = u`
(Mathlib: `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`), observe that
`Re F' = u_x` and `Im F' = -u_y`, and apply the fundamental theorem of calculus along the vertical
and the horizontal segment to get `v z = Im F z - Im F 0`.
-/

open Set Complex InnerProductSpace

namespace UndergradKB.ComplexAnalysis

/-- The partial derivatives of `u = Re F` are `Re F'` and `-Im F'`. -/
lemma fderiv_re_partials {F : ℂ → ℂ} {u : ℂ → ℝ} (hF : Differentiable ℂ F)
    (hu : (fun z => (F z).re) = u) (w : ℂ) :
    fderiv ℝ u w 1 = (deriv F w).re ∧ fderiv ℝ u w I = -(deriv F w).im := by
  have h := ((hF w).hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  have h2 := Complex.reCLM.hasFDerivAt.comp w h
  have h3 : HasFDerivAt u (Complex.reCLM.comp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv F w)).restrictScalars ℝ)) w := by
    rw [← hu]; exact h2
  rw [h3.fderiv]
  simp

/-- The formula of Beck Theorem 6.1.9: `v(x, y) = Im F (x + i y) - Im F 0`. -/
lemma integral_formula_eq_im {F : ℂ → ℂ} {u : ℂ → ℝ} (hF : Differentiable ℂ F)
    (hu : (fun z => (F z).re) = u) (z : ℂ) :
    ((∫ t in (0:ℝ)..z.im, fderiv ℝ u ((z.re : ℂ) + (t : ℂ) * I) 1) -
      ∫ t in (0:ℝ)..z.re, fderiv ℝ u (t : ℂ) I) = (F z).im - (F 0).im := by
  have hc : Continuous (deriv F) := (hF.contDiff (n := 1)).continuous_deriv le_rfl
  have hp := fun w => fderiv_re_partials hF hu w
  simp_rw [(hp _).1, (hp _).2]
  have hv : ∀ t ∈ uIcc (0:ℝ) z.im, HasDerivAt (fun t : ℝ => (F ((z.re : ℂ) + (t : ℂ) * I)).im)
      (deriv F ((z.re : ℂ) + (t : ℂ) * I)).re t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℂ => (z.re : ℂ) + s * I) I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (z.re : ℂ)
    have h2 := (hF ((z.re : ℂ) + (t : ℂ) * I)).hasDerivAt.comp (t : ℂ) h1
    have h3 := h2.comp_ofReal
    have h4 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h3
    simp only [Function.comp_def, Complex.imCLM_apply] at h4
    simpa using h4
  have hh : ∀ t ∈ uIcc (0:ℝ) z.re, HasDerivAt (fun t : ℝ => (F (t : ℂ)).im)
      (deriv F (t : ℂ)).im t := by
    intro t _
    have h3 := (hF (t : ℂ)).hasDerivAt.comp_ofReal
    have h4 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h3
    simp only [Function.comp_def, Complex.imCLM_apply] at h4
    simpa using h4
  have I1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hv
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have I2 := intervalIntegral.integral_eq_sub_of_hasDerivAt hh
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_neg, I1, I2]
  have : (z.re : ℂ) + (z.im : ℂ) * I = z := by simp
  simp [this]

/-- Beck Theorem 6.1.9 (CX-085): if `u` is harmonic on `ℂ`, then
`v(x, y) = ∫₀^y u_x(x, t) dt - ∫₀^x u_y(t, 0) dt` is a harmonic conjugate of `u`:
`u + i v` is entire. -/
@[kb "beck2025" "Theorem 6.1.9, p. 105"]
theorem differentiable_add_I_mul_integralConjugate {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u univ) :
    Differentiable ℂ (fun z : ℂ => (u z : ℂ) +
      (((∫ t in (0:ℝ)..z.im, fderiv ℝ u ((z.re : ℂ) + (t : ℂ) * I) 1) -
        ∫ t in (0:ℝ)..z.re, fderiv ℝ u (t : ℂ) I : ℝ) : ℂ) * I) := by
  obtain ⟨F, hFa, hFu⟩ := hu.exists_analyticOnNhd_univ_re_eq
  have hF : Differentiable ℂ F := fun z => (hFa z (mem_univ z)).differentiableAt
  have key : (fun z : ℂ => (u z : ℂ) +
      (((∫ t in (0:ℝ)..z.im, fderiv ℝ u ((z.re : ℂ) + (t : ℂ) * I) 1) -
        ∫ t in (0:ℝ)..z.re, fderiv ℝ u (t : ℂ) I : ℝ) : ℂ) * I) =
      fun z => F z - (((F 0).im : ℝ) : ℂ) * I := by
    funext z
    rw [integral_formula_eq_im hF hFu z, ← congrFun hFu z]
    push_cast
    apply Complex.ext <;> simp
  rw [key]
  exact hF.sub_const _

/-- Beck Theorem 6.1.9 (CX-085), harmonicity of the conjugate. -/
@[kb "beck2025" "Theorem 6.1.9, p. 105"]
theorem harmonicOnNhd_integralConjugate {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u univ) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ =>
      (∫ t in (0:ℝ)..z.im, fderiv ℝ u ((z.re : ℂ) + (t : ℂ) * I) 1) -
        ∫ t in (0:ℝ)..z.re, fderiv ℝ u (t : ℂ) I) univ := by
  obtain ⟨F, hFa, hFu⟩ := hu.exists_analyticOnNhd_univ_re_eq
  have hF : Differentiable ℂ F := fun z => (hFa z (mem_univ z)).differentiableAt
  have hG : AnalyticOnNhd ℂ (fun z => F z - (((F 0).im : ℝ) : ℂ) * I) univ := by
    intro z hz
    exact (hFa z hz).sub analyticAt_const
  have : (fun z : ℂ =>
      (∫ t in (0:ℝ)..z.im, fderiv ℝ u ((z.re : ℂ) + (t : ℂ) * I) 1) -
        ∫ t in (0:ℝ)..z.re, fderiv ℝ u (t : ℂ) I) =
      fun z => (F z - (((F 0).im : ℝ) : ℂ) * I).im := by
    funext z
    rw [integral_formula_eq_im hF hFu z]
    simp
  rw [this]
  intro z hz
  exact (hG z hz).harmonicAt_im

/-- Beck Example 6.1.8: for `u(x, y) = x y`, `v(x, y) = -(x² - y²)/2` is a harmonic conjugate,
i.e. `u + i v = -(i/2) z²`. -/
@[kb "beck2025" "Example 6.1.8, p. 104"]
theorem example_6_1_8 (z : ℂ) :
    ((z.re * z.im : ℝ) : ℂ) + ((-(z.re ^ 2 - z.im ^ 2) / 2 : ℝ) : ℂ) * I
      = -(I / 2) * z ^ 2 := by
  apply Complex.ext <;> simp [pow_two] <;> ring

end UndergradKB.ComplexAnalysis
