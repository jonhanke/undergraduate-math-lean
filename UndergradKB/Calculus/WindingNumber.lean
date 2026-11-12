import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.Common.Attr
import UndergradKB.Calculus.GreenGlued
import UndergradKB.Calculus.GreenHoles

/-! # Calculus: the circulation of the swirl field

OpenStax Calculus 3:Example 6.47 (CA-640). The circulation of the swirl field `(-y, x)/(x²+y²)` along a curve
avoiding the origin is the total change of the polar angle along it:
* `swirl_circulation_mem_zmultiples`: along every closed `C¹` curve avoiding the origin it is `2π` times an integer
  (the winding number of the curve about the origin). Proof: with `z = x + i y` and `Λ(t) = ∫_a^t z'/z`, the
  product `z e^{-Λ}` has derivative `0`, so `e^{Λ(b)} = z(b)/z(a) = 1`; the imaginary part of `z'/z` is the swirl
  integrand `(x y' - y x')/(x² + y²)`.
* `swirl_circulation_glued_annulus`: `2π` along a curve that, together with a small circle around the origin
  traversed clockwise, bounds a region glued from parametrized cells avoiding the origin (Green's theorem on that
  region, `green_glued`, the field being curl free there);
* `swirl_circulation_glued_zero`: `0` along the boundary of a region glued from parametrized cells avoiding the
  origin.

Still missing for the book's statement for every simple closed curve: the Jordan curve theorem (a simple closed
curve not enclosing the origin bounds a region avoiding it; one enclosing it has winding number `±1`). -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-- OpenStax Calculus 3:Example 6.47 (CA-640), integrality: the circulation of `(-y, x)/(x²+y²)` along a closed
`C¹` curve `γ` on `[a, b]` avoiding the origin is `2π` times an integer (its winding number about the origin). -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_mem_zmultiples (γ : ℝ → ℝ × ℝ) (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hcl : γ a = γ b) (h0 : ∀ t ∈ Icc a b, γ t ≠ 0) :
    ∃ k : ℤ, greenLineIntegral swirlP swirlQ (fun t => (γ t).1) (fun t => (γ t).2) a b = 2 * π * k := by
  classical
  set x : ℝ → ℝ := fun t => (γ t).1 with hxdef
  set y : ℝ → ℝ := fun t => (γ t).2 with hydef
  have hx : ContDiff ℝ 1 x := contDiff_fst.comp hγ
  have hy : ContDiff ℝ 1 y := contDiff_snd.comp hγ
  have hxd : Differentiable ℝ x := hx.differentiable (by norm_num)
  have hyd : Differentiable ℝ y := hy.differentiable (by norm_num)
  have hx' : Continuous (deriv x) := hx.continuous_deriv le_rfl
  have hy' : Continuous (deriv y) := hy.continuous_deriv le_rfl
  set z : ℝ → ℂ := fun t => (x t : ℂ) + (y t : ℂ) * Complex.I with hzdef
  have hzd : ∀ t, HasDerivAt z (((deriv x t : ℝ) : ℂ) + ((deriv y t : ℝ) : ℂ) * Complex.I) t := by
    intro t
    have h1 : HasDerivAt (fun s => (x s : ℂ)) ((deriv x t : ℝ) : ℂ) t := (hxd t).hasDerivAt.ofReal_comp
    have h2 : HasDerivAt (fun s => (y s : ℂ)) ((deriv y t : ℝ) : ℂ) t := (hyd t).hasDerivAt.ofReal_comp
    exact h1.add (h2.mul_const Complex.I)
  have hzc : Continuous z := by fun_prop
  have hz0 : ∀ t ∈ Icc a b, z t ≠ 0 := by
    intro t ht h
    apply h0 t ht
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hzdef] at h1 h2
    exact Prod.ext h1 h2
  set W : ℝ → ℂ := fun t => (((deriv x t : ℝ) : ℂ) + ((deriv y t : ℝ) : ℂ) * Complex.I) / z t with hWdef
  have hWc : ContinuousOn W (Icc a b) := by
    have hnum : Continuous
        (fun t => ((deriv x t : ℝ) : ℂ) + ((deriv y t : ℝ) : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp hx').add ((Complex.continuous_ofReal.comp hy').mul continuous_const)
    exact hnum.continuousOn.div hzc.continuousOn hz0
  set W' : ℝ → ℂ := fun t => W ((Set.projIcc a b hab t : Icc a b) : ℝ) with hW'def
  have hW'c : Continuous W' :=
    hWc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => (Set.projIcc a b hab t).2)
  have hW'eq : ∀ t ∈ Icc a b, W' t = W t := by
    intro t ht
    simp [hW'def, Set.projIcc_of_mem hab ht]
  set Λ : ℝ → ℂ := fun t => ∫ s in a..t, W' s with hΛdef
  have hΛd : ∀ t, HasDerivAt Λ (W' t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hW'c.intervalIntegrable _ _)
      (hW'c.stronglyMeasurableAtFilter _ _) hW'c.continuousAt
  set g : ℝ → ℂ := fun t => z t * Complex.exp (-Λ t) with hgdef
  have hgd : ∀ t ∈ Icc a b, HasDerivAt g 0 t := by
    intro t ht
    have h1 := (hzd t).mul ((hΛd t).neg.cexp)
    refine h1.congr_deriv ?_
    have hzt := hz0 t ht
    rw [hW'eq t ht]
    simp only [hWdef]
    field_simp
    ring
  have hgc : ContinuousOn g (Icc a b) := by
    intro t ht
    exact (hgd t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hgc
    (fun t ht => (hgd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) b (right_mem_Icc.2 hab)
  have hΛa : Λ a = 0 := by simp [hΛdef]
  have hza : z a ≠ 0 := hz0 a (left_mem_Icc.2 hab)
  have hzab : z b = z a := by
    simp only [hzdef, hxdef, hydef, hcl]
  have hexp : Complex.exp (Λ b) = 1 := by
    have h1 : z b * Complex.exp (-Λ b) = z a := by simpa [hgdef, hΛa] using hconst
    rw [hzab] at h1
    have h2 : Complex.exp (-Λ b) = 1 := by
      have := mul_left_cancel₀ hza (h1.trans (mul_one _).symm)
      exact this
    have h3 := congrArg (fun u => Complex.exp (Λ b) * u) h2
    simpa [← Complex.exp_add] using h3.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp
  refine ⟨n, ?_⟩
  have him := congrArg Complex.im hn
  have hint : IntervalIntegrable W' volume a b := hW'c.intervalIntegrable _ _
  have hIm : (Λ b).im = ∫ s in a..b, (W' s).im := by
    simp only [hΛdef]
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    have hI : Integrable W' (volume.restrict (Ioc a b)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hint
    have := Complex.imCLM.integral_comp_comm hI
    simpa using this.symm
  have hgl : greenLineIntegral swirlP swirlQ x y a b = ∫ s in a..b, (W' s).im := by
    unfold greenLineIntegral
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hab] at ht
    rw [hW'eq t ht]
    have hzt := hz0 t ht
    have hn0 : ((γ t).1) ^ 2 + (γ t).2 ^ 2 ≠ 0 := by
      intro h
      apply h0 t ht
      have h1 : (γ t).1 = 0 := by nlinarith [sq_nonneg (γ t).1, sq_nonneg (γ t).2]
      have h2 : (γ t).2 = 0 := by nlinarith [sq_nonneg (γ t).1, sq_nonneg (γ t).2]
      exact Prod.ext h1 h2
    simp only [hWdef, hzdef, swirlP, swirlQ, Complex.div_im]
    simp [Complex.normSq_apply, hxdef, hydef]
    field_simp
    ring
  rw [hgl, ← hIm, him]
  simp
  ring

/-- OpenStax Calculus 3:Example 6.47 (CA-640), curves enclosing the origin: let the closed curves `C` (a list of
oriented edges) and the circle of radius `r > 0` about the origin traversed clockwise together bound a region glued
from parametrized cells avoiding the origin (hypotheses as in `green_glued` with `U` the punctured plane, outer
edges `C` and the reversed circle). Then the circulation of `(-y, x)/(x²+y²)` along `C` is `2π`. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_glued_annulus {n : ℕ} (cells : Fin n → PlaneCell)
    (hC : ∀ i, (cells i).IsRegular {p | p ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (C : List (OrientedCurve (ℝ × ℝ))) {r : ℝ} (hr : 0 < r)
    (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      ((C ++ [(⟨fun t => (r * Real.cos t, r * Real.sin t), 0, 2 * π⟩ : OrientedCurve (ℝ × ℝ)).reverse]) ++
        pairs.flatMap fun e => [e.1, e.2])) :
    (C.map (planeCurveIntegral swirlP swirlQ)).sum = 2 * π := by
  have key := green_glued swirlP swirlQ isOpen_ne_zero_plane contDiffOn_swirlP contDiffOn_swirlQ cells hC hdisj
    _ pairs hpairs hperm
  have hz : ∫ p in ⋃ i, (cells i).region, curl2 swirlP swirlQ p = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun p hp => curl2_swirl ?_)
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    obtain ⟨z, hz, rfl⟩ := hi
    exact (hC i).mapsTo z ((hC i).sub hz)
  rw [hz, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
    planeCurveIntegral_reverse] at key
  have hcirc : planeCurveIntegral swirlP swirlQ ⟨fun t => (r * Real.cos t, r * Real.sin t), 0, 2 * π⟩ = 2 * π :=
    swirl_circulation_origin_circle r hr
  linarith

/-- OpenStax Calculus 3:Example 6.47 (CA-640), curves not enclosing the origin: the circulation of
`(-y, x)/(x²+y²)` along the boundary `C` of a region glued from parametrized cells avoiding the origin (hypotheses
as in `green_glued` with `U` the punctured plane) is `0`. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_glued_zero {n : ℕ} (cells : Fin n → PlaneCell)
    (hC : ∀ i, (cells i).IsRegular {p | p ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (C : List (OrientedCurve (ℝ × ℝ)))
    (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (C ++ pairs.flatMap fun e => [e.1, e.2])) :
    (C.map (planeCurveIntegral swirlP swirlQ)).sum = 0 := by
  rw [← green_glued swirlP swirlQ isOpen_ne_zero_plane contDiffOn_swirlP contDiffOn_swirlQ cells hC hdisj
    _ pairs hpairs hperm]
  refine setIntegral_eq_zero_of_forall_eq_zero (fun p hp => curl2_swirl ?_)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hp
  obtain ⟨z, hz, rfl⟩ := hi
  exact (hC i).mapsTo z ((hC i).sub hz)

end UndergradKB.Calculus
