import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import UndergradKB.Common.Attr

/-! # Calculus: parametric equations

Derivative of a parametric curve (via a local inverse of `x`), second derivative, area under a parametric
curve (the substitution rule), the cycloid arch area `3π`, arc length and surface area of revolution (bridging
definitions, since Mathlib has no integral formula for curve length), the area of a sphere, and the cycloid and
hypocycloid as the paths of a point of a rolling circle. -/

namespace UndergradKB.Calculus

open Real Filter Topology Set intervalIntegral MeasureTheory

/-! ## Derivatives of parametric curves -/

theorem parametric_deriv_aux {x y g : ℝ → ℝ} {x' y' u0 : ℝ} (hx : HasDerivAt x x' (g u0)) (hx' : x' ≠ 0)
    (hy : HasDerivAt y y' (g u0)) (hgc : ContinuousAt g u0) (hgr : ∀ᶠ u in 𝓝 u0, x (g u) = u) :
    HasDerivAt (y ∘ g) (y' / x') u0 := by
  have hg' : HasDerivAt g x'⁻¹ u0 := HasDerivAt.of_local_left_inverse hgc hx hx' hgr
  have := hy.comp u0 hg'
  simpa [div_eq_mul_inv] using this

/-- OpenStax Calculus 2:Theorem 7.1, 3:Theorem 1.1 (CA-392): if `x` and `y` are differentiable at `t0`,
`x'(t0) ≠ 0`, and `g` is a local inverse of `x` near `x t0` (continuous, with `x (g u) = u` for `u` near
`x t0`, and `g (x t0) = t0`), then `y` as a function of `x`, namely `y ∘ g`, has derivative `y'(t0)/x'(t0)`
at `x t0`: `dy/dx = (dy/dt)/(dx/dt)`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.1, p. 560"]
theorem parametric_deriv {x y g : ℝ → ℝ} {x' y' t0 : ℝ} (hx : HasDerivAt x x' t0) (hx' : x' ≠ 0)
    (hy : HasDerivAt y y' t0) (hgc : ContinuousAt g (x t0)) (hg0 : g (x t0) = t0)
    (hgr : ∀ᶠ u in 𝓝 (x t0), x (g u) = u) : HasDerivAt (y ∘ g) (y' / x') (x t0) := by
  refine parametric_deriv_aux ?_ hx' ?_ hgc hgr <;> rwa [hg0]

/-- OpenStax Calculus 2:Theorem 7.1 (CA-392), existence of the inverse: if `x` has a strict derivative
`x'(t0) ≠ 0` at `t0` (e.g. `x` is `C¹`), then `x` has a local inverse `g` near `x t0`, and `y ∘ g` has derivative
`y'(t0)/x'(t0)` at `x t0` for every `y` differentiable at `t0`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.1, p. 560"]
theorem parametric_deriv_exists_inverse {x y : ℝ → ℝ} {x' y' t0 : ℝ} (hx : HasStrictDerivAt x x' t0)
    (hx' : x' ≠ 0) (hy : HasDerivAt y y' t0) :
    ∃ g : ℝ → ℝ, (∀ᶠ t in 𝓝 t0, g (x t) = t) ∧ HasDerivAt (y ∘ g) (y' / x') (x t0) := by
  refine ⟨hx.localInverse x x' t0 hx', hx.eventually_left_inverse hx', ?_⟩
  have hl := hx.eventually_left_inverse hx'
  have hg0 : hx.localInverse x x' t0 hx' (x t0) = t0 := hl.self_of_nhds
  have hgs := hx.to_localInverse hx'
  have hgr := hx.eventually_right_inverse hx'
  exact parametric_deriv hx.hasDerivAt hx' hy hgs.hasDerivAt.continuousAt hg0 hgr

/-- OpenStax Calculus 2:§7.2 Equation (7.2), 3:Equation 1.2 (CA-393): the second derivative of a parametric
curve.  Suppose `x, y` have derivatives `x'(t), y'(t)` near `t0` with `x' ≠ 0`, `x'` and `y'` have derivatives
`a`, `b` at `t0`, and `g` is a local inverse of `x` near `x t0` (continuous near `x t0`, `g (x t0) = t0`,
`x (g u) = u` near `x t0`).  Then `u ↦ deriv (y ∘ g) u` (which is `dy/dx`) has derivative
`(d/dt (y'/x'))/x'` at `x t0`, i.e. `((b x' - y' a)/x'^2)/x'` evaluated at `t0`. -/
@[kb "openstaxcalculus2016" "2:§7.2 Equation (7.2), p. 564"]
theorem parametric_second_deriv {x y x' y' g : ℝ → ℝ} {t0 a b : ℝ}
    (hxd : ∀ᶠ t in 𝓝 t0, HasDerivAt x (x' t) t ∧ HasDerivAt y (y' t) t ∧ x' t ≠ 0)
    (hx'' : HasDerivAt x' a t0) (hy'' : HasDerivAt y' b t0)
    (hgc : ∀ᶠ u in 𝓝 (x t0), ContinuousAt g u) (hg0 : g (x t0) = t0)
    (hgr : ∀ᶠ u in 𝓝 (x t0), x (g u) = u) :
    HasDerivAt (deriv (y ∘ g)) (((b * x' t0 - y' t0 * a) / x' t0 ^ 2) / x' t0) (x t0) := by
  have hgc0 : ContinuousAt g (x t0) := hgc.self_of_nhds
  have hxd0 := hxd.self_of_nhds
  have hxd' : ∀ᶠ u in 𝓝 (x t0), HasDerivAt x (x' (g u)) (g u) ∧ HasDerivAt y (y' (g u)) (g u) ∧
      x' (g u) ≠ 0 := by
    have : ∀ᶠ t in 𝓝 (g (x t0)), HasDerivAt x (x' t) t ∧ HasDerivAt y (y' t) t ∧ x' t ≠ 0 := by
      rw [hg0]; exact hxd
    exact hgc0.tendsto.eventually this
  have hq : ∀ᶠ u in 𝓝 (x t0), deriv (y ∘ g) u = y' (g u) / x' (g u) := by
    filter_upwards [hxd', hgc, hgr.eventually_nhds] with u h1 h2 h3
    exact (parametric_deriv_aux h1.1 h1.2.2 h1.2.1 h2 h3).deriv
  have hg' : HasDerivAt g (x' t0)⁻¹ (x t0) :=
    HasDerivAt.of_local_left_inverse hgc0 (by rw [hg0]; exact hxd0.1) hxd0.2.2 hgr
  have hqd : HasDerivAt (fun t => y' t / x' t) ((b * x' t0 - y' t0 * a) / x' t0 ^ 2) (g (x t0)) := by
    rw [hg0]; exact hy''.div hx'' hxd0.2.2
  have hcomp := hqd.comp (x t0) hg'
  have h2 : HasDerivAt (fun u => y' (g u) / x' (g u))
      (((b * x' t0 - y' t0 * a) / x' t0 ^ 2) / x' t0) (x t0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using hcomp
  exact h2.congr_of_eventuallyEq hq

/-! ## Area under a parametric curve -/

/-- OpenStax Calculus 2:Theorem 7.2, 3:Theorem 1.2 (CA-394), substitution form: if `x` has continuous derivative
`x'` on `[t1, t2]` and `y = F ∘ x` there (`F` continuous), then `∫ y x' dt = ∫_{x t1}^{x t2} F`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.2, p. 565"]
theorem parametric_area_integral (x x' y F : ℝ → ℝ) (t1 t2 : ℝ)
    (hx : ∀ t ∈ uIcc t1 t2, HasDerivAt x (x' t) t) (hx' : ContinuousOn x' (uIcc t1 t2))
    (hF : ContinuousOn F (x '' uIcc t1 t2)) (hy : ∀ t ∈ uIcc t1 t2, y t = F (x t)) :
    ∫ t in t1..t2, y t * x' t = ∫ u in x t1..x t2, F u := by
  rw [← integral_comp_mul_deriv' hx hx' hF]
  refine integral_congr fun t ht => ?_
  simp [hy t ht]

/-- OpenStax Calculus 2:Theorem 7.2, 3:Theorem 1.2 (CA-394), area form: if `x` is increasing on `[t1, t2]` with
continuous derivative `x'` there, and `y = F ∘ x` with `F ≥ 0` continuous (the curve is the graph of `F`), the
region under the curve (between the `x`-axis and the graph of `F` over `(x t1, x t2]`) has area (Lebesgue
measure in `ℝ × ℝ`) `∫_{t1}^{t2} y(t) x'(t) dt`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.2, p. 565"]
theorem parametric_area (x x' y F : ℝ → ℝ) (t1 t2 : ℝ) (hle : t1 ≤ t2)
    (hx : ∀ t ∈ Icc t1 t2, HasDerivAt x (x' t) t) (hx' : ContinuousOn x' (Icc t1 t2))
    (hmono : MonotoneOn x (Icc t1 t2)) (hF : ContinuousOn F (Icc (x t1) (x t2)))
    (hF0 : ∀ u ∈ Icc (x t1) (x t2), 0 ≤ F u) (hy : ∀ t ∈ Icc t1 t2, y t = F (x t)) :
    volume (regionBetween (fun _ => (0 : ℝ)) F (Ioc (x t1) (x t2))) =
      ENNReal.ofReal (∫ t in t1..t2, y t * x' t) := by
  have hxle : x t1 ≤ x t2 := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
  have hu : uIcc t1 t2 = Icc t1 t2 := uIcc_of_le hle
  have hsub : ∀ t ∈ Icc t1 t2, x t ∈ Icc (x t1) (x t2) := fun t ht =>
    ⟨hmono ⟨le_rfl, hle⟩ ht ht.1, hmono ht ⟨hle, le_rfl⟩ ht.2⟩
  have hFi : IntegrableOn F (Ioc (x t1) (x t2)) :=
    (hF.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h1 := volume_regionBetween_eq_integral (μ := (volume : Measure ℝ)) (integrableOn_zero) hFi
    measurableSet_Ioc (fun u hu => hF0 u (Ioc_subset_Icc_self hu))
  have h2 : ∫ t in t1..t2, y t * x' t = ∫ u in x t1..x t2, F u := by
    refine parametric_area_integral x x' y F t1 t2 (by rwa [hu]) (by rwa [hu]) ?_ (by rwa [hu])
    rw [hu]
    refine hF.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hsub t ht
  rw [h2, integral_of_le hxle, Measure.volume_eq_prod]
  simpa using h1

/-- OpenStax Calculus 2:Example 7.7 (CA-395): `∫_0^{2π} (1 - cos t)(1 - cos t) dt = 3π`, the area under one arch
of the cycloid `x = t - sin t`, `y = 1 - cos t` (here `y x'` with `x' = 1 - cos t`). -/
@[kb "openstaxcalculus2016" "2:Example 7.7, p. 566"]
theorem cycloid_arch_integral : ∫ t in (0 : ℝ)..2 * π, (1 - cos t) * (1 - cos t) = 3 * π := by
  have h : ∀ t : ℝ, (1 - cos t) * (1 - cos t) = 1 - 2 * cos t + cos t ^ 2 := fun t => by ring
  simp_rw [h]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    integral_cos_sq, integral_cos]
  · simp
    ring
  · exact intervalIntegrable_const
  · exact (continuous_const.mul continuous_cos).intervalIntegrable _ _
  · exact (continuous_const.sub (continuous_const.mul continuous_cos)).intervalIntegrable _ _
  · exact (continuous_cos.pow 2).intervalIntegrable _ _

/-- OpenStax Calculus 2:Example 7.7 (CA-395): if a continuous `F ≥ 0` on `[0, 2π]` expresses the height of the
cycloid arch `x = t - sin t`, `y = 1 - cos t` (`0 ≤ t ≤ 2π`) as a function of `x` (`1 - cos t = F (t - sin t)`),
the region under the arch has area `3π`. -/
@[kb "openstaxcalculus2016" "2:Example 7.7, p. 566"]
theorem cycloid_arch_area (F : ℝ → ℝ) (hF : ContinuousOn F (Icc (0 - sin 0) (2 * π - sin (2 * π))))
    (hF0 : ∀ u ∈ Icc (0 - sin 0) (2 * π - sin (2 * π)), 0 ≤ F u)
    (hy : ∀ t ∈ Icc 0 (2 * π), 1 - cos t = F (t - sin t)) :
    volume (regionBetween (fun _ => (0 : ℝ)) F (Ioc (0 - sin 0) (2 * π - sin (2 * π)))) =
      ENNReal.ofReal (3 * π) := by
  have hpi := Real.pi_pos
  have hmono : Monotone (fun t : ℝ => t - sin t) :=
    monotone_of_deriv_nonneg (by fun_prop) (fun t => by simp; linarith [cos_le_one t])
  have := parametric_area (fun t => t - sin t) (fun t => 1 - cos t) (fun t => 1 - cos t) F 0 (2 * π)
    (by positivity) (fun t _ => (hasDerivAt_id' t).sub (hasDerivAt_sin t))
    (by fun_prop) (hmono.monotoneOn _) hF hF0 hy
  rw [this, cycloid_arch_integral]

/-! ## Arc length and surface area of revolution -/

/-- The arc length `∫_a^b √(x'(t)^2 + y'(t)^2) dt` of the parametric curve `(x(t), y(t))`, `a ≤ t ≤ b`
(OpenStax Calculus 2:Theorem 7.3, 3:Theorem 1.3).  Bridging definition: Mathlib has the variation of a function
(`eVariationOn`) but no integral formula for the length of a `C¹` curve. -/
noncomputable def parametricArcLength (x y : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, √(deriv x t ^ 2 + deriv y t ^ 2)

/-- OpenStax Calculus 2:Theorem 7.3, 3:Theorem 1.3 (CA-396): for the curve `x = t`, `y = f(t)` the parametric
arc length is `∫_a^b √(1 + f'(t)^2) dt`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.3, p. 567"]
theorem parametricArcLength_graph (f : ℝ → ℝ) (a b : ℝ) :
    parametricArcLength (fun t => t) f a b = ∫ t in a..b, √(1 + deriv f t ^ 2) := by
  unfold parametricArcLength
  simp

/-- OpenStax Calculus 2:§7.2 Equation (7.6), 3:Equation 1.6 (CA-397): the area of the surface obtained by
revolving the curve `(x(t), y(t))` (`y ≥ 0`) about the `x`-axis, `2π ∫ y(t) √(x'^2 + y'^2) dt`
(definition). -/
@[kb "openstaxcalculus2016" "2:§7.2 Equation (7.6), p. 571"]
noncomputable def surfaceAreaAboutXAxis (x y : ℝ → ℝ) (a b : ℝ) : ℝ :=
  2 * π * ∫ t in a..b, y t * √(deriv x t ^ 2 + deriv y t ^ 2)

/-- OpenStax Calculus 2:§7.2 Equation (7.6), 3:Equation 1.6 (CA-397): the area of the surface obtained by
revolving the curve `(x(t), y(t))` (`x ≥ 0`) about the `y`-axis, `2π ∫ x(t) √(x'^2 + y'^2) dt`
(definition). -/
@[kb "openstaxcalculus2016" "2:§7.2 Equation (7.6), p. 571"]
noncomputable def surfaceAreaAboutYAxis (x y : ℝ → ℝ) (a b : ℝ) : ℝ :=
  2 * π * ∫ t in a..b, x t * √(deriv x t ^ 2 + deriv y t ^ 2)

/-- OpenStax Calculus 3:Example 1.9 (CA-398): revolving the half circle `x = r cos t`, `y = r sin t`,
`0 ≤ t ≤ π`, about the `x`-axis gives the sphere, of area `4 π r^2`. -/
@[kb "openstaxcalculus2016" "3:Example 1.9, p. 43"]
theorem sphere_surface_area (r : ℝ) (hr : 0 ≤ r) :
    surfaceAreaAboutXAxis (fun t => r * cos t) (fun t => r * sin t) 0 π = 4 * π * r ^ 2 := by
  unfold surfaceAreaAboutXAxis
  have h : ∀ t : ℝ, (fun t => r * sin t) t * √(deriv (fun t => r * cos t) t ^ 2 +
      deriv (fun t => r * sin t) t ^ 2) = r ^ 2 * sin t := by
    intro t
    have e : √(deriv (fun t => r * cos t) t ^ 2 + deriv (fun t => r * sin t) t ^ 2) = r := by
      simp only [deriv_const_mul_field', Real.deriv_cos, Real.deriv_sin]
      rw [show (r * -sin t) ^ 2 + (r * cos t) ^ 2 = r ^ 2 * (sin t ^ 2 + cos t ^ 2) by ring,
        sin_sq_add_cos_sq, mul_one, Real.sqrt_sq hr]
    simp only [e]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_sin]
  simp
  ring

/-! ## Cycloid and hypocycloid -/

/-- OpenStax Calculus 2:§7.1 Cycloid equations, 3:§1.1 (CA-390): a wheel of radius `a` rolls along the
`x`-axis; when it has turned through the angle `t` its center is at `(a t, a)` (no slipping: the center moved
the arc length `a t`).  A point of the rim that started at the origin has then the direction
`ψ = -π/2 - t` from the center, and its position `center + a (cos ψ, sin ψ)` is `(a (t - sin t), a (1 - cos t))`.
The no-slip condition is `a · (-π/2 - ψ) = a t` (arc from the point to the contact point equals the distance
rolled). -/
@[kb "openstaxcalculus2016" "2:§7.1 Cycloid equations, p. 551"]
theorem cycloid_point (a t : ℝ) :
    a * (-(π / 2) - (-(π / 2) - t)) = a * t ∧
    a * t + a * cos (-(π / 2) - t) = a * (t - sin t) ∧
    a + a * sin (-(π / 2) - t) = a * (1 - cos t) := by
  refine ⟨by ring, ?_, ?_⟩
  · rw [cos_sub]; simp; ring
  · rw [sin_sub]; simp; ring

/-- OpenStax Calculus 2:§7.1 Cycloid equations (CA-390): the velocity of the cycloid point is
`(a (1 - cos t), a sin t)`, which vanishes when the point touches the line (`cos t = 1`): the cusps. -/
@[kb "openstaxcalculus2016" "2:§7.1 Cycloid equations, p. 551"]
theorem cycloid_velocity (a t : ℝ) :
    HasDerivAt (fun s => a * (s - sin s)) (a * (1 - cos t)) t ∧
    HasDerivAt (fun s => a * (1 - cos s)) (a * sin t) t ∧
    (cos t = 1 → a * (1 - cos t) = 0 ∧ a * sin t = 0) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  · exact ((hasDerivAt_id' t).sub (hasDerivAt_sin t)).const_mul a
  · simpa using ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_cos t)).const_mul a
  · have : sin t = 0 := by
      have := sin_sq_add_cos_sq t
      rw [h] at this
      nlinarith
    simp [h, this]

/-- OpenStax Calculus 2:§7.1 Hypocycloid equations, 3:§1.1 (CA-391): a circle of radius `b` rolls inside a circle
of radius `a` (`b ≠ 0`).  When the line of centers has turned through the angle `t`, the rolling center is
`(a - b)(cos t, sin t)`, and a rim point that started at `(a, 0)` has the direction `ψ = -((a - b)/b) t` from
it (the no-slip condition: the arc `b (t - ψ)` on the rolling circle from the point to the contact point equals
the arc `a t` of the fixed circle).  Its coordinates are the hypocycloid formulas. -/
@[kb "openstaxcalculus2016" "2:§7.1 Hypocycloid equations, p. 551"]
theorem hypocycloid_point (a b t : ℝ) (hb : b ≠ 0) :
    b * (t - (-((a - b) / b) * t)) = a * t ∧
    (a - b) * cos t + b * cos (-((a - b) / b) * t) = (a - b) * cos t + b * cos ((a - b) / b * t) ∧
    (a - b) * sin t + b * sin (-((a - b) / b) * t) = (a - b) * sin t - b * sin ((a - b) / b * t) := by
  refine ⟨by field_simp; ring, ?_, ?_⟩
  · rw [neg_mul, cos_neg]
  · rw [neg_mul, sin_neg]; ring

end UndergradKB.Calculus
