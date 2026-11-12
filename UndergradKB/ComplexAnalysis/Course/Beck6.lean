import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 6 (Harmonic Functions): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`).
Beck's notion of "harmonic in a region `G`" is `IsHarmonicOn G u` below. -/

namespace UndergradKB.ComplexAnalysis.Course.Beck6
open Complex Metric InnerProductSpace
open scoped ContDiff

/-- Beck Definition 6.1.1 (CX-082). `u : G → ℝ` is harmonic in `G` if it has continuous second
partials and `u_xx + u_yy = 0`; the second partials in the directions `1` and `i` are
`iteratedFDeriv ℝ 2 u z ![1, 1]` and `iteratedFDeriv ℝ 2 u z ![I, I]`. -/
def IsHarmonicOn (G : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u G ∧
    ∀ z ∈ G, iteratedFDeriv ℝ 2 u z ![1, 1] + iteratedFDeriv ℝ 2 u z ![I, I] = 0

/-- Beck Definition 6.1.1 (CX-082). On an open set, the book's notion of harmonic coincides with
Mathlib's `HarmonicOnNhd` (defined through the Laplacian). -/
@[kb "beck2025" "Definition 6.1.1, p. 102"]
theorem isHarmonicOn_iff (G : Set ℂ) (hG : IsOpen G) (u : ℂ → ℝ) :
    IsHarmonicOn G u ↔ HarmonicOnNhd u G := by
  constructor
  · rintro ⟨hc, hl⟩ z hz
    refine ⟨(hc z hz).contDiffAt (hG.mem_nhds hz), ?_⟩
    filter_upwards [hG.mem_nhds hz] with y hy
    rw [laplacian_eq_iteratedFDeriv_complexPlane]
    exact hl y hy
  · intro h
    refine ⟨h.contDiffOn, fun z hz => ?_⟩
    have := (h z hz).2.self_of_nhds
    rw [laplacian_eq_iteratedFDeriv_complexPlane] at this
    exact this

/-- Beck Example 6.1.2 (CX-082). `u(x, y) = x y` is harmonic in `ℂ`. -/
@[kb "beck2025" "Example 6.1.2, p. 102"]
theorem harmonic_xy : IsHarmonicOn Set.univ (fun z : ℂ => z.re * z.im) := by
  rw [isHarmonicOn_iff _ isOpen_univ]
  intro z _
  have h : AnalyticAt ℂ (fun z : ℂ => z ^ 2 / 2) z := by fun_prop
  have := h.harmonicAt_im
  refine (harmonicAt_congr_nhds (Filter.Eventually.of_forall fun y => ?_)).1 this
  simp [pow_two]
  ring

/-- Beck Example 6.1.3 (CX-082). `u(x, y) = e^x cos y` is harmonic in `ℂ`. -/
@[kb "beck2025" "Example 6.1.3, p. 102"]
theorem harmonic_exp_mul_cos : IsHarmonicOn Set.univ (fun z : ℂ => Real.exp z.re * Real.cos z.im) := by
  rw [isHarmonicOn_iff _ isOpen_univ]
  intro z _
  have h : AnalyticAt ℂ Complex.exp z := Complex.differentiable_exp.analyticAt z
  have := h.harmonicAt_re
  refine (harmonicAt_congr_nhds (Filter.Eventually.of_forall fun y => ?_)).1 this
  simp [Complex.exp_re]

/-- Beck Proposition 6.1.4 (CX-083). The real and imaginary parts of a function holomorphic in a
region are harmonic there. -/
@[kb "beck2025" "Proposition 6.1.4, p. 102"]
theorem harmonic_of_holomorphic (G : Set ℂ) (hG : IsOpen G) (_hC : IsConnected G) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f G) :
    IsHarmonicOn G (fun z => (f z).re) ∧ IsHarmonicOn G (fun z => (f z).im) := by
  have ha : AnalyticOnNhd ℂ f G := hf.analyticOnNhd hG
  rw [isHarmonicOn_iff _ hG, isHarmonicOn_iff _ hG]
  exact ⟨fun z hz => (ha z hz).harmonicAt_re, fun z hz => (ha z hz).harmonicAt_im⟩

/-- Beck Example 6.1.5 (CX-083). `f(z) = z^2 / 2` is entire and `Im f(x + iy) = x y`. -/
@[kb "beck2025" "Example 6.1.5, p. 103"]
theorem im_half_sq : Differentiable ℂ (fun z : ℂ => z ^ 2 / 2) ∧
    ∀ z : ℂ, (z ^ 2 / 2).im = z.re * z.im := by
  refine ⟨by fun_prop, fun z => ?_⟩
  simp [pow_two]
  ring

/-- Beck Example 6.1.6 (CX-083). `exp` is entire and `Re exp(x + iy) = e^x cos y`. -/
@[kb "beck2025" "Example 6.1.6, p. 103"]
theorem re_exp : Differentiable ℂ Complex.exp ∧
    ∀ z : ℂ, (Complex.exp z).re = Real.exp z.re * Real.cos z.im :=
  ⟨Complex.differentiable_exp, fun z => Complex.exp_re z⟩

/-- Beck Corollary 6.1.10 (CX-085). A harmonic function is infinitely differentiable. -/
@[kb "beck2025" "Corollary 6.1.10, p. 105"]
theorem harmonic_contDiff (G : Set ℂ) (hG : IsOpen G) (_hC : IsConnected G) (u : ℂ → ℝ)
    (hu : IsHarmonicOn G u) : ContDiffOn ℝ ∞ u G := by
  intro z hz
  have h := ((isHarmonicOn_iff G hG u).1 hu) z hz
  exact ((HarmonicAt.analyticAt h).contDiffAt).contDiffWithinAt

/-- Beck Theorem 6.2.1 (CX-086). Mean value property: if `u` is harmonic in `G` and
`D[w, r] ⊂ G`, then `u w` is the average of `u` over the circle `C[w, r]`. -/
@[kb "beck2025" "Theorem 6.2.1, p. 106"]
theorem harmonic_mean_value (G : Set ℂ) (hG : IsOpen G) (_hC : IsConnected G) (u : ℂ → ℝ)
    (hu : IsHarmonicOn G u) (w : ℂ) (r : ℝ) (hr : 0 < r) (hsub : closedBall w r ⊆ G) :
    u w = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi, u (w + r * exp (t * I)) := by
  have h := ((isHarmonicOn_iff G hG u).1 hu).mono hsub
  have h2 := (InnerProductSpace.HarmonicOnNhd.circleAverage_eq (c := w) (R := r)
    (by rwa [abs_of_pos hr]))
  rw [Real.circleAverage_def] at h2
  rw [← h2]
  simp only [circleMap, smul_eq_mul]
  rw [one_div]

/-- Beck, Poisson integral formula, §6.3 (CX-160; stated in Exercise 6.3.13). If `u` is harmonic on
an open set containing the closed unit disk and `0 < r < 1`, then
`u (r e^{iφ}) = (2π)⁻¹ ∫_0^{2π} u (e^{it}) P_r(φ - t) dt` with the Poisson kernel
`P_r(x) = (1 - r²) / (1 - 2 r cos x + r²)`. -/
@[kb "beck2025" "Poisson integral formula §6.3, p. 108"]
theorem poisson_integral_formula (U : Set ℂ) (hU : IsOpen U) (u : ℂ → ℝ)
    (hu : IsHarmonicOn U u) (hsub : closedBall 0 1 ⊆ U) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (φ : ℝ) :
    u (r * exp (φ * I)) = (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..2 * Real.pi,
      u (exp (t * I)) * ((1 - r ^ 2) / (1 - 2 * r * Real.cos (φ - t) + r ^ 2)) := by
  have h := ((isHarmonicOn_iff U hU u).1 hu).mono hsub
  have hw : (r * exp (φ * I) : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp [abs_of_pos hr0, hr1]
  have h2 := HarmonicOnNhd.circleAverage_poissonKernel_smul (c := 0) (R := 1) h hw
  rw [Real.circleAverage_def] at h2
  rw [← h2]
  simp only [smul_eq_mul]
  rw [one_div]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hc : circleMap 0 1 t = exp (t * I) := by simp [circleMap]
  simp only [hc, Pi.mul_apply, poissonKernel_def, sub_zero]
  rw [mul_comm]
  congr 1
  have hn : ‖(exp (t * I) : ℂ)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hn2 : ‖(r : ℂ) * exp (φ * I)‖ = r := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [abs_of_pos hr0]
  rw [hn, hn2]
  have : ‖exp (t * I) - (r : ℂ) * exp (φ * I)‖ ^ 2 = 1 - 2 * r * Real.cos (φ - t) + r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq φ]
  rw [this]
  ring

end UndergradKB.ComplexAnalysis.Course.Beck6
