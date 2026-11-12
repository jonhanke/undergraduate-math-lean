import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import UndergradKB.Common.Attr

/-!
# Cauchy-Riemann equations in partial-derivative form (row CX-032)

If `f = u + i v` is complex differentiable at `z₀ = x₀ + i y₀`, then the partial derivatives of
`u = Re f` and `v = Im f` (as functions of the real variables `x`, `y`) exist and satisfy
`u_x = v_y`, `u_y = -v_x`, and `f'(z₀) = u_x + i v_x`. The converse (continuous partials plus `f_x = -i f_y` give complex differentiability) is `hasDerivAt_of_continuous_partials`.
-/

open Complex Filter Topology

namespace UndergradKB.ComplexAnalysis

variable {f : ℂ → ℂ} {x₀ y₀ : ℝ}

/-- Derivative of `f` along the horizontal line through `x₀ + i y₀`. -/
lemma hasDerivAt_horizontal {f' : ℂ} (hf : HasDerivAt f f' ((x₀ : ℂ) + y₀ * I)) :
    HasDerivAt (fun x : ℝ => f ((x : ℂ) + y₀ * I)) f' x₀ := by
  have h : HasDerivAt (fun x : ℝ => (x : ℂ) + y₀ * I) 1 x₀ := by
    have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x₀ := ofRealCLM.hasDerivAt
    exact (hasDerivAt_add_const_iff ((y₀ : ℂ) * I)).2 h0
  have h2 := HasDerivAt.scomp (h := fun x : ℝ => (x : ℂ) + y₀ * I) x₀ hf h
  rw [one_smul] at h2
  exact h2

/-- Derivative of `f` along the vertical line through `x₀ + i y₀`. -/
lemma hasDerivAt_vertical {f' : ℂ} (hf : HasDerivAt f f' ((x₀ : ℂ) + y₀ * I)) :
    HasDerivAt (fun y : ℝ => f ((x₀ : ℂ) + y * I)) (I * f') y₀ := by
  have h : HasDerivAt (fun y : ℝ => (x₀ : ℂ) + y * I) I y₀ := by
    have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y₀ := ofRealCLM.hasDerivAt
    have h1 := (hasDerivAt_const_add_iff (x₀ : ℂ)).2 (HasDerivAt.mul_const h0 I)
    rw [one_mul] at h1
    exact h1
  have h2 := HasDerivAt.scomp (h := fun y : ℝ => (x₀ : ℂ) + y * I) y₀ hf h
  rw [smul_eq_mul] at h2
  exact h2

/-- Beck Theorem 2.3.1 (CX-032). If `f` is complex differentiable at `x₀ + i y₀`, the partial
derivatives of `u = Re f` and `v = Im f` exist, `u_x = v_y`, `u_y = -v_x`, and
`f' = u_x + i v_x`. -/
@[kb "beck2025" "Theorem 2.3.1, p. 39"]
theorem cauchy_riemann (hf : DifferentiableAt ℂ f ((x₀ : ℂ) + y₀ * I)) :
    DifferentiableAt ℝ (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).re) x₀ ∧
    DifferentiableAt ℝ (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).im) x₀ ∧
    DifferentiableAt ℝ (fun y : ℝ => (f ((x₀ : ℂ) + y * I)).re) y₀ ∧
    DifferentiableAt ℝ (fun y : ℝ => (f ((x₀ : ℂ) + y * I)).im) y₀ ∧
    deriv (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).re) x₀
      = deriv (fun y : ℝ => (f ((x₀ : ℂ) + y * I)).im) y₀ ∧
    deriv (fun y : ℝ => (f ((x₀ : ℂ) + y * I)).re) y₀
      = -deriv (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).im) x₀ ∧
    deriv f ((x₀ : ℂ) + y₀ * I)
      = deriv (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).re) x₀
        + deriv (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).im) x₀ * I := by
  have hH := hasDerivAt_horizontal hf.hasDerivAt
  have hV := hasDerivAt_vertical hf.hasDerivAt
  have hHr := reCLM.hasFDerivAt.comp_hasDerivAt x₀ hH
  have hHi := imCLM.hasFDerivAt.comp_hasDerivAt x₀ hH
  have hVr := reCLM.hasFDerivAt.comp_hasDerivAt y₀ hV
  have hVi := imCLM.hasFDerivAt.comp_hasDerivAt y₀ hV
  have e1 : HasDerivAt (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).re)
      (deriv f ((x₀ : ℂ) + y₀ * I)).re x₀ := hHr
  have e2 : HasDerivAt (fun x : ℝ => (f ((x : ℂ) + y₀ * I)).im)
      (deriv f ((x₀ : ℂ) + y₀ * I)).im x₀ := hHi
  have e3 : HasDerivAt (fun y : ℝ => (f ((x₀ : ℂ) + y * I)).re)
      (I * deriv f ((x₀ : ℂ) + y₀ * I)).re y₀ := hVr
  have e4 : HasDerivAt (fun y : ℝ => (f ((x₀ : ℂ) + y * I)).im)
      (I * deriv f ((x₀ : ℂ) + y₀ * I)).im y₀ := hVi
  refine ⟨e1.differentiableAt, e2.differentiableAt, e3.differentiableAt, e4.differentiableAt,
    ?_, ?_, ?_⟩
  · rw [e1.deriv, e4.deriv]; simp
  · rw [e3.deriv, e2.deriv]; simp
  · rw [e1.deriv, e2.deriv]; exact (Complex.re_add_im _).symm

/-- Beck Theorem 2.3.1, converse part (CX-032). If the partial derivatives of `f` in the `x` and `y`
directions exist near `z₀`, are continuous at `z₀`, and satisfy `f_x(z₀) = -i f_y(z₀)`, then `f` is
complex differentiable at `z₀` with derivative `f_x(z₀)`. -/
@[kb "beck2025" "Theorem 2.3.1, p. 39"]
theorem hasDerivAt_of_continuous_partials {f : ℂ → ℂ} {z₀ : ℂ}
    (hx : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ (fun x : ℝ => f ((x : ℂ) + z.im * I)) z.re)
    (hy : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ (fun y : ℝ => f ((z.re : ℂ) + y * I)) z.im)
    (cx : ContinuousAt (fun z : ℂ => deriv (fun x : ℝ => f ((x : ℂ) + z.im * I)) z.re) z₀)
    (cy : ContinuousAt (fun z : ℂ => deriv (fun y : ℝ => f ((z.re : ℂ) + y * I)) z.im) z₀)
    (hCR : deriv (fun x : ℝ => f ((x : ℂ) + z₀.im * I)) z₀.re
      = -I * deriv (fun y : ℝ => f ((z₀.re : ℂ) + y * I)) z₀.im) :
    HasDerivAt f (deriv (fun x : ℝ => f ((x : ℂ) + z₀.im * I)) z₀.re) z₀ := by
  set d1 : ℂ → ℂ := fun z => deriv (fun x : ℝ => f ((x : ℂ) + z.im * I)) z.re with hd1
  set d2 : ℂ → ℂ := fun z => deriv (fun y : ℝ => f ((z.re : ℂ) + y * I)) z.im with hd2
  set φ : ℝ × ℝ → ℂ := fun v => (v.1 : ℂ) + v.2 * I with hφdef
  have hφ : Continuous φ := by rw [hφdef]; fun_prop
  have hre : ∀ v, (φ v).re = v.1 := fun v => by simp [hφdef]
  have him : ∀ v, (φ v).im = v.2 := fun v => by simp [hφdef]
  set u : ℝ × ℝ := (z₀.re, z₀.im) with hu
  have hφu : φ u = z₀ := by
    simp only [hφdef, hu]
    exact Complex.re_add_im z₀
  set g : ℝ → ℝ → ℂ := fun x y => f ((x : ℂ) + y * I) with hg
  set f₁ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (d1 (φ (x, y))) with hf₁
  set f₂ : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (d2 (φ (x, y))) with hf₂
  have hx' : ∀ᶠ z in 𝓝 (φ u), DifferentiableAt ℝ (fun x : ℝ => f ((x : ℂ) + z.im * I)) z.re := by
    rwa [hφu]
  have hy' : ∀ᶠ z in 𝓝 (φ u), DifferentiableAt ℝ (fun y : ℝ => f ((z.re : ℂ) + y * I)) z.im := by
    rwa [hφu]
  have df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (g · v.2) (↿f₁ v) v.1 := by
    filter_upwards [(hφ.tendsto u).eventually hx'] with v hv
    rw [hre, him] at hv
    have := hasDerivAt_iff_hasFDerivAt.1 hv.hasDerivAt
    have e : d1 (φ v) = deriv (fun x : ℝ => f ((x : ℂ) + v.2 * I)) v.1 := by
      simp only [hd1]; rw [hre, him]
    show HasFDerivAt (fun x : ℝ => f ((x : ℂ) + v.2 * I))
      (ContinuousLinearMap.toSpanSingleton ℝ (d1 (φ v))) v.1
    rw [e]; exact this
  have df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (g v.1 ·) (↿f₂ v) v.2 := by
    filter_upwards [(hφ.tendsto u).eventually hy'] with v hv
    rw [hre, him] at hv
    have := hasDerivAt_iff_hasFDerivAt.1 hv.hasDerivAt
    have e : d2 (φ v) = deriv (fun y : ℝ => f ((v.1 : ℂ) + y * I)) v.2 := by
      simp only [hd2]; rw [hre, him]
    show HasFDerivAt (fun y : ℝ => f ((v.1 : ℂ) + y * I))
      (ContinuousLinearMap.toSpanSingleton ℝ (d2 (φ v))) v.2
    rw [e]; exact this
  have hspan : Continuous (fun c : ℂ => ContinuousLinearMap.toSpanSingleton ℝ c) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℂ)).continuous
  have cf₁ : ContinuousAt ↿f₁ u := by
    have : ContinuousAt (fun v : ℝ × ℝ => d1 (φ v)) u := by
      refine ContinuousAt.comp (g := d1) ?_ hφ.continuousAt
      rwa [hφu]
    exact hspan.continuousAt.comp this
  have cf₂ : ContinuousAt ↿f₂ u := by
    have : ContinuousAt (fun v : ℝ × ℝ => d2 (φ v)) u := by
      refine ContinuousAt.comp (g := d2) ?_ hφ.continuousAt
      rwa [hφu]
    exact hspan.continuousAt.comp this
  have hstrict := hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂
  let ψ : ℂ →L[ℝ] ℝ × ℝ := reCLM.prod imCLM
  have hψ : HasFDerivAt (fun z : ℂ => (z.re, z.im)) ψ z₀ := ψ.hasFDerivAt
  have hcomp := (hstrict.hasFDerivAt).comp z₀ hψ
  have hfun : (↿g ∘ fun z : ℂ => (z.re, z.im)) = f := by
    funext z
    show f ((z.re : ℂ) + z.im * I) = f z
    rw [Complex.re_add_im]
  rw [hfun] at hcomp
  have hf1u : ↿f₁ u = ContinuousLinearMap.toSpanSingleton ℝ (d1 z₀) := by
    show ContinuousLinearMap.toSpanSingleton ℝ (d1 (φ u)) = _
    rw [hφu]
  have hf2u : ↿f₂ u = ContinuousLinearMap.toSpanSingleton ℝ (d2 z₀) := by
    show ContinuousLinearMap.toSpanSingleton ℝ (d2 (φ u)) = _
    rw [hφu]
  have hD1 : (((↿f₁ u).coprod (↿f₂ u)).comp ψ) 1 = d1 z₀ := by
    simp [ψ, hf1u, hf2u]
  have hD2 : (((↿f₁ u).coprod (↿f₂ u)).comp ψ) I = d2 z₀ := by
    simp [ψ, hf1u, hf2u]
  have hCR2 : d2 z₀ = I * d1 z₀ := by
    have h : d1 z₀ = -I * d2 z₀ := hCR
    rw [h]
    linear_combination (d2 z₀) * Complex.I_mul_I
  have h₂ : (((↿f₁ u).coprod (↿f₂ u)).comp ψ) I
      = I • (((↿f₁ u).coprod (↿f₂ u)).comp ψ) 1 := by
    rw [hD1, hD2, hCR2, smul_eq_mul]
  have key := (HasFDerivAt.complexOfReal_hasFDerivAt hcomp h₂).hasDerivAt
  have e1 : (((↿f₁ u).coprod (↿f₂ u)).comp ψ).complexOfReal h₂ 1 = d1 z₀ := by
    rw [← hD1]; simp
  rw [e1] at key
  exact key

end UndergradKB.ComplexAnalysis
