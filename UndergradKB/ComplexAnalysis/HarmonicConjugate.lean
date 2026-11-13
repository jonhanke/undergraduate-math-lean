import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import UndergradKB.ComplexAnalysis.SimplyConnected
import UndergradKB.Common.Attr

/-!
# Harmonic conjugates on simply connected regions (row CX-084)

Beck et al., Theorem 6.1.7: if `u` is harmonic on a simply connected region `G`, then `u` has a
harmonic conjugate on `G`, i.e. `u` is the real part of a function holomorphic on `G`.

Following the book (and Mathlib's disc version
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), the function
`g = u_x - i u_y` is holomorphic on `G`; by Corollary 5.2.4
(`exists_antiderivative_of_simplyConnected`) it has an antiderivative `F` on `G`, normalised so that `Re F z₀ = u z₀`. Then `Re F` and `u` have
the same derivative, hence agree on the connected open set `G`.
-/

open Set Complex InnerProductSpace

namespace UndergradKB.ComplexAnalysis

/-- Beck Theorem 6.1.7 (CX-084): a harmonic function on a simply connected region is the real
part of a function analytic (holomorphic) on the region. -/
@[kb "beck2025" "Theorem 6.1.7, p. 103"]
theorem exists_holomorphic_re_eq_of_simplyConnected {u : ℂ → ℝ} {G : Set ℂ}
    (hG : IsSimplyConnectedRegion G) (hu : InnerProductSpace.HarmonicOnNhd u G) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F G ∧ G.EqOn (fun z => (F z).re) u := by
  have hGo : IsOpen G := hG.1
  have hGc : IsConnected G := hG.2.1
  obtain ⟨z₀, hz₀⟩ := hGc.nonempty
  let g : ℂ → ℂ := fun z => (fderiv ℝ u z 1 : ℂ) - I * (fderiv ℝ u z I : ℂ)
  have hg : DifferentiableOn ℂ g G :=
    fun x hx => (HarmonicAt.differentiableAt_complex_partial (hu x hx)).differentiableWithinAt
  obtain ⟨F₀, hF₀⟩ := exists_antiderivative_of_simplyConnected hG hg
  let F : ℂ → ℂ := fun z => F₀ z + ((u z₀ - (F₀ z₀).re : ℝ) : ℂ)
  have hF : ∀ z ∈ G, HasDerivAt F (g z) z := fun z hz => (hF₀ z hz).add_const _
  have h₁F : DifferentiableOn ℂ F G := fun x hx => (hF x hx).differentiableAt.differentiableWithinAt
  have h₂F : DifferentiableOn ℝ F G := h₁F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
  refine ⟨F, h₁F.analyticOnNhd hGo, ?_⟩
  have hre : (fun z => (F z).re) = Complex.reCLM ∘ F := by ext; simp
  rw [hre]
  refine hGo.eqOn_of_fderiv_eq (𝕜 := ℝ) hG.2.1.isPreconnected
    (Complex.reCLM.differentiable.comp_differentiableOn h₂F)
    (fun y hy => (ContDiffAt.differentiableAt (hu y hy).1 two_ne_zero).differentiableWithinAt)
    ?_ hz₀ ?_
  · intro y hy
    have h₄F := (hF y hy).differentiableAt
    have h₅F := h₄F.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
    rw [fderiv_comp y (by fun_prop) h₅F, ContinuousLinearMap.fderiv,
      h₄F.fderiv_restrictScalars (𝕜 := ℝ)]
    ext a
    nth_rw 2 [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ))]
    rw [map_add, map_smul, map_smul]
    simp [HasDerivAt.deriv (hF y hy), g]
  · simp [F]

/-- Beck Theorem 6.1.7 (CX-084), harmonic conjugate phrasing: if `u` is harmonic on a simply
connected region `G`, there is a harmonic `v` on `G` such that `u + i v` is holomorphic on `G`. -/
@[kb "beck2025" "Theorem 6.1.7, p. 103"]
theorem exists_harmonicConjugate_of_simplyConnected {u : ℂ → ℝ} {G : Set ℂ}
    (hG : IsSimplyConnectedRegion G) (hu : InnerProductSpace.HarmonicOnNhd u G) :
    ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v G ∧
      DifferentiableOn ℂ (fun z => (u z : ℂ) + (v z : ℂ) * Complex.I) G := by
  obtain ⟨F, hF, hFu⟩ := exists_holomorphic_re_eq_of_simplyConnected hG hu
  refine ⟨fun z => (F z).im, fun z hz => (hF z hz).harmonicAt_im, ?_⟩
  refine (hF.differentiableOn).congr (fun z hz => ?_)
  rw [← hFu hz]
  exact Complex.re_add_im (F z)

end UndergradKB.ComplexAnalysis
