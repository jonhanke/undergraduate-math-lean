import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.CrossProduct
import UndergradKB.Common.Attr

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

/-- Partial derivative `r_u` of a parametrization `r : ℝ × ℝ → ℝ³` at `p = (u, v)`. -/
noncomputable def partialU (r : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  deriv (fun u => r (u, p.2)) p.1

/-- Partial derivative `r_v`. -/
noncomputable def partialV (r : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  deriv (fun v => r (p.1, v)) p.2

/-- The normal vector `r_u × r_v`. -/
noncomputable def surfNormal (r : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  crossProduct (partialU r p) (partialV r p)

/-- Euclidean length of a vector of `ℝ³` (as `Fin 3 → ℝ`). -/
noncomputable def surfVnorm (v : Fin 3 → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

theorem hasDerivAt_vec3 {f₁ f₂ f₃ : ℝ → ℝ} {a b c t : ℝ} (h₁ : HasDerivAt f₁ a t)
    (h₂ : HasDerivAt f₂ b t) (h₃ : HasDerivAt f₃ c t) :
    HasDerivAt (fun s => (![f₁ s, f₂ s, f₃ s] : Fin 3 → ℝ)) ![a, b, c] t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i <;> simpa

/-- Sphere parametrization (radius `R`, polar angle `φ`, azimuth `θ`). -/
noncomputable def sphereParam (R : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![R * Real.sin p.1 * Real.cos p.2, R * Real.sin p.1 * Real.sin p.2, R * Real.cos p.1]

theorem surfNormal_sphere (R : ℝ) (p : ℝ × ℝ) :
    surfNormal (sphereParam R) p =
      ![R ^ 2 * Real.sin p.1 * (Real.sin p.1 * Real.cos p.2),
        R ^ 2 * Real.sin p.1 * (Real.sin p.1 * Real.sin p.2), R ^ 2 * Real.sin p.1 * Real.cos p.1] := by
  have hu : partialU (sphereParam R) p =
      ![R * Real.cos p.1 * Real.cos p.2, R * Real.cos p.1 * Real.sin p.2, -(R * Real.sin p.1)] := by
    unfold partialU sphereParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using ((Real.hasDerivAt_sin p.1).const_mul R).mul_const (Real.cos p.2))
      (by simpa using ((Real.hasDerivAt_sin p.1).const_mul R).mul_const (Real.sin p.2))
      (by simpa using ((Real.hasDerivAt_cos p.1).const_mul R))
  have hv : partialV (sphereParam R) p =
      ![-(R * Real.sin p.1 * Real.sin p.2), R * Real.sin p.1 * Real.cos p.2, 0] := by
    unfold partialV sphereParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using ((Real.hasDerivAt_cos p.2).const_mul (R * Real.sin p.1)))
      (by simpa using ((Real.hasDerivAt_sin p.2).const_mul (R * Real.sin p.1))) (by simpa using hasDerivAt_const p.2 (R * Real.cos p.1))
  rw [surfNormal, hu, hv, cross_apply]
  ext i
  fin_cases i <;> simp <;>
    first | linear_combination (R ^ 2 * Real.cos p.1 * Real.sin p.1) * Real.sin_sq_add_cos_sq p.2 | ring

/-- A set integral over a rectangle of a continuous function is the iterated interval integral. -/
theorem setIntegral_rect {f : ℝ × ℝ → ℝ} (hf : Continuous f) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ p in Icc a b ×ˢ Icc c d, f p = ∫ x in a..b, ∫ y in c..d, f (x, y) := by
  have hi : IntegrableOn f (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi]
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hcd]

/-- Bridging definition (OpenStax Calculus 3:§6.6 Definition, regular parametrization, CA-650): a parametrization
`r(u,v)` of a surface in `ℝ³` over the parameter domain `D` is regular if `r_u × r_v ≠ 0` at every point of `D`. -/
def IsRegularParam (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ D, surfNormal r p ≠ 0

/-- Bridging definition (OpenStax Calculus 3:Equation 6.18, surface area, CA-651): the area of the surface
parametrized by `r` over `D` is `∬_D ‖r_u × r_v‖ dA`. -/
noncomputable def paramSurfaceArea (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, surfVnorm (surfNormal r p)

/-- Bridging definition (OpenStax Calculus 3:Equation 6.19, scalar surface integral, CA-654): the integral of a
scalar function `f` over the surface parametrized by `r` over `D` is `∬_D f(r(u,v)) ‖r_u × r_v‖ dA`. -/
noncomputable def scalarSurfaceIntegral (f : (Fin 3 → ℝ) → ℝ) (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, f (r p) * surfVnorm (surfNormal r p)

/-- Bridging definition (OpenStax Calculus 3:Equation 6.21, flux, CA-657): the flux of a vector field `F` across the
surface parametrized by `r` over `D` (orientation `r_u × r_v`) is `∬_D F(r(u,v)) · (r_u × r_v) dA`. -/
noncomputable def surfaceFlux (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in D, F (r p) ⬝ᵥ surfNormal r p

/-- OpenStax Calculus 3:Equation 6.19 (CA-654). Scalar surface integral of the constant function `1` is the surface
area (so `paramSurfaceArea` is the case `f = 1`). -/
@[kb "openstaxcalculus2016" "3:Equation 6.19, p. 695"]
theorem scalarSurfaceIntegral_one (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ)) :
    scalarSurfaceIntegral (fun _ => 1) r D = paramSurfaceArea r D := by
  simp [scalarSurfaceIntegral, paramSurfaceArea]

/-- The unit normal `N = r_u × r_v / ‖r_u × r_v‖` of a parametrization (CA-655). -/
noncomputable def unitNormal (r : ℝ × ℝ → Fin 3 → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  (surfVnorm (surfNormal r p))⁻¹ • surfNormal r p

/-- OpenStax Calculus 3:Equation 6.21 (CA-657, CA-656). The flux of `F` is the integral of `F · N` against the area
element, `N = r_u × r_v / ‖r_u × r_v‖`, when the parametrization is regular: Equation 6.20 (`∬ F·N dS`) agrees with
Equation 6.21 (`∬ F(r)·(r_u × r_v) dA`). -/
@[kb "openstaxcalculus2016" "3:Equation 6.21, p. 703"]
theorem surfaceFlux_eq_unitNormal (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (r : ℝ × ℝ → Fin 3 → ℝ) (D : Set (ℝ × ℝ))
    (hD : MeasurableSet D) (hr : IsRegularParam r D) :
    surfaceFlux F r D = ∫ p in D, (F (r p) ⬝ᵥ unitNormal r p) * surfVnorm (surfNormal r p) := by
  refine setIntegral_congr_fun hD (fun p hp => ?_)
  have hpos : 0 < surfVnorm (surfNormal r p) := by
    rw [surfVnorm, Real.sqrt_pos]
    exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
      (Ne.symm (fun h => hr p hp (dotProduct_self_eq_zero.1 h)))
  simp only [unitNormal, dotProduct_smul, smul_eq_mul]
  field_simp

/-! ### Sphere -/

theorem sphereParam_surfVnorm {R : ℝ} (hR : 0 < R) (p : ℝ × ℝ) : surfVnorm (sphereParam R p) = R := by
  have : sphereParam R p ⬝ᵥ sphereParam R p = R ^ 2 := by
    simp only [sphereParam, dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (R ^ 2 * Real.sin p.1 ^ 2) * Real.sin_sq_add_cos_sq p.2 +
      R ^ 2 * Real.sin_sq_add_cos_sq p.1
  rw [surfVnorm, this, Real.sqrt_sq hR.le]

theorem sphere_normal_surfVnorm (R : ℝ) {p : ℝ × ℝ} (hp : 0 ≤ Real.sin p.1) :
    surfVnorm (surfNormal (sphereParam R) p) = R ^ 2 * Real.sin p.1 := by
  have : surfNormal (sphereParam R) p ⬝ᵥ surfNormal (sphereParam R) p = (R ^ 2 * Real.sin p.1) ^ 2 := by
    rw [surfNormal_sphere]
    simp only [dotProduct, Fin.sum_univ_three]
    simp
    linear_combination (R ^ 4 * Real.sin p.1 ^ 4) * Real.sin_sq_add_cos_sq p.2 +
      (R ^ 4 * Real.sin p.1 ^ 2) * Real.sin_sq_add_cos_sq p.1
  rw [surfVnorm, this, Real.sqrt_sq (by positivity)]

/-- The parameter rectangle of the sphere. -/
noncomputable def sphereDomain : Set (ℝ × ℝ) := Icc 0 π ×ˢ Icc 0 (2 * π)

/-- OpenStax Calculus 3:Example 6.63 (CA-652). The area of the sphere of radius `R`, computed from the surface
area integral `∬ ‖r_φ × r_θ‖` of the spherical parametrization, is `4πR²`. -/
@[kb "openstaxcalculus2016" "3:Example 6.63, p. 692"]
theorem paramSurfaceArea_sphere (R : ℝ) : paramSurfaceArea (sphereParam R) sphereDomain = 4 * π * R ^ 2 := by
  have h : paramSurfaceArea (sphereParam R) sphereDomain = ∫ p in sphereDomain, R ^ 2 * Real.sin p.1 := by
    refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p hp => ?_)
    exact sphere_normal_surfVnorm R (Real.sin_nonneg_of_nonneg_of_le_pi hp.1.1 hp.1.2)
  rw [h, sphereDomain, setIntegral_rect (by fun_prop) Real.pi_pos.le (by positivity)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  simp only [intervalIntegral.integral_const_mul, integral_sin]
  simp
  ring

/-- The inverse-square field `x / ‖x‖³` (CA-663, CA-664). -/
noncomputable def invSquareField (x : Fin 3 → ℝ) : Fin 3 → ℝ := ((surfVnorm x) ^ 3)⁻¹ • x

theorem sphere_dot_normal (R : ℝ) (p : ℝ × ℝ) :
    sphereParam R p ⬝ᵥ surfNormal (sphereParam R) p = R ^ 3 * Real.sin p.1 := by
  rw [surfNormal_sphere]
  simp only [sphereParam, dotProduct, Fin.sum_univ_three]
  simp
  linear_combination (R ^ 3 * Real.sin p.1 ^ 3) * Real.sin_sq_add_cos_sq p.2 +
      (R ^ 3 * Real.sin p.1) * Real.sin_sq_add_cos_sq p.1

/-- OpenStax Calculus 3:Theorem 6.21 (CA-664), enclosing case for a sphere centered at the origin: the outward
flux of `r/‖r‖³` through the sphere of radius `R > 0` is `4π`, computed with the spherical parametrization. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.21, p. 738"]
theorem flux_invSquare_sphere {R : ℝ} (hR : 0 < R) :
    surfaceFlux invSquareField (sphereParam R) sphereDomain = 4 * π := by
  have h : surfaceFlux invSquareField (sphereParam R) sphereDomain = ∫ p in sphereDomain, Real.sin p.1 := by
    refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p _ => ?_)
    simp only [invSquareField, smul_dotProduct, smul_eq_mul, sphereParam_surfVnorm hR, sphere_dot_normal]
    field_simp
  rw [h, sphereDomain, setIntegral_rect (by fun_prop) Real.pi_pos.le (by positivity)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  simp only [intervalIntegral.integral_const_mul, integral_sin]
  simp
  ring

/-! ### Cone, cylinder, graph, surface of revolution (CA-649) -/

/-- OpenStax Calculus 3:Example 6.58 (CA-649): the cylinder `x² + y² = R²` by `(R cos u, R sin u, v)`. -/
noncomputable def cylinderParam (R : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![R * Real.cos p.1, R * Real.sin p.1, p.2]

/-- OpenStax Calculus 3:Example 6.60 (CA-649): the cone `z = k √(x²+y²)` by `(u cos v, u sin v, k u)`. -/
noncomputable def coneParam (k : ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![p.1 * Real.cos p.2, p.1 * Real.sin p.2, k * p.1]

/-- OpenStax Calculus 3:§6.6 Fact (CA-649): the graph `z = f(x,y)` by `(x, y, f(x,y))`. -/
def graphParam (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1, p.2, f p]

/-- OpenStax Calculus 3:Example 6.64 (CA-649): the surface of revolution of `y = f(x)` about the `x`-axis,
`(x, f(x) cos t, f(x) sin t)`, with parameters `(x, t)`. -/
noncomputable def revolutionParam (f : ℝ → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ :=
  ![p.1, f p.1 * Real.cos p.2, f p.1 * Real.sin p.2]

theorem surfNormal_cylinder (R : ℝ) (p : ℝ × ℝ) :
    surfNormal (cylinderParam R) p = ![R * Real.cos p.1, R * Real.sin p.1, 0] := by
  have hu : partialU (cylinderParam R) p = ![-(R * Real.sin p.1), R * Real.cos p.1, 0] := by
    unfold partialU cylinderParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using ((Real.hasDerivAt_cos p.1).const_mul R))
      (by simpa using ((Real.hasDerivAt_sin p.1).const_mul R)) (by simpa using hasDerivAt_const p.1 (p.2))
  have hv : partialV (cylinderParam R) p = ![0, 0, 1] := by
    unfold partialV cylinderParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using hasDerivAt_const p.2 (R * Real.cos p.1))
      (by simpa using hasDerivAt_const p.2 (R * Real.sin p.1)) (by simpa using hasDerivAt_id' p.2)
  rw [surfNormal, hu, hv, cross_apply]
  ext i
  fin_cases i <;> simp

theorem surfNormal_cone (k : ℝ) (p : ℝ × ℝ) :
    surfNormal (coneParam k) p = ![-(k * p.1 * Real.cos p.2), -(k * p.1 * Real.sin p.2), p.1] := by
  have hu : partialU (coneParam k) p = ![Real.cos p.2, Real.sin p.2, k] := by
    unfold partialU coneParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using (hasDerivAt_id' p.1).mul_const (Real.cos p.2))
      (by simpa using (hasDerivAt_id' p.1).mul_const (Real.sin p.2))
      (by simpa using (hasDerivAt_id' p.1).const_mul k)
  have hv : partialV (coneParam k) p = ![-(p.1 * Real.sin p.2), p.1 * Real.cos p.2, 0] := by
    unfold partialV coneParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using ((Real.hasDerivAt_cos p.2).const_mul p.1))
      (by simpa using ((Real.hasDerivAt_sin p.2).const_mul p.1))
      (by simpa using hasDerivAt_const p.2 (k * p.1))
  rw [surfNormal, hu, hv, cross_apply]
  ext i
  fin_cases i <;> simp <;>
    first | linear_combination (p.1) * Real.sin_sq_add_cos_sq p.2 | ring

theorem surfNormal_graph (f : ℝ × ℝ → ℝ) (fx fy : ℝ × ℝ → ℝ)
    (hx : ∀ p, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hy : ∀ p, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) (p : ℝ × ℝ) :
    surfNormal (graphParam f) p = ![-fx p, -fy p, 1] := by
  have hu : partialU (graphParam f) p = ![1, 0, fx p] := by
    unfold partialU graphParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using hasDerivAt_id' p.1) (by simpa using hasDerivAt_const p.1 p.2) (hx p)
  have hv : partialV (graphParam f) p = ![0, 1, fy p] := by
    unfold partialV graphParam
    refine HasDerivAt.deriv ?_
    exact hasDerivAt_vec3 (by simpa using hasDerivAt_const p.2 p.1) (by simpa using hasDerivAt_id' p.2) (hy p)
  rw [surfNormal, hu, hv, cross_apply]
  ext i
  fin_cases i <;> simp

/-- OpenStax Calculus 3:Example 6.61 (CA-650): the graph parametrization of a differentiable function is regular
(`r_x × r_y = (-f_x, -f_y, 1) ≠ 0`). -/
@[kb "openstaxcalculus2016" "3:§6.6 Definition (regular parametrization), p. 687"]
theorem graphParam_isRegular (f : ℝ × ℝ → ℝ) (fx fy : ℝ × ℝ → ℝ)
    (hx : ∀ p, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hy : ∀ p, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) (D : Set (ℝ × ℝ)) :
    IsRegularParam (graphParam f) D := by
  intro p _ h
  have := congrFun (surfNormal_graph f fx fy hx hy p ▸ h) 2
  simp at this

/-- OpenStax Calculus 3:Example 6.58 (CA-650): the cylinder parametrization is regular when `R ≠ 0`. -/
@[kb "openstaxcalculus2016" "3:Example 6.61, p. 687"]
theorem cylinderParam_isRegular {R : ℝ} (hR : R ≠ 0) (D : Set (ℝ × ℝ)) :
    IsRegularParam (cylinderParam R) D := by
  intro p _ h
  rw [surfNormal_cylinder] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  all_goals try first | exact hR h0 | exact hR h1
  nlinarith [Real.sin_sq_add_cos_sq p.1]

/-- OpenStax Calculus 3:Example 6.62 (CA-652): lateral area of a right circular cone of radius `ρ` and height `h`
(`ρ, h > 0`), computed from the area integral over `0 ≤ u ≤ ρ`, `0 ≤ v ≤ 2π` of `(u cos v, u sin v, (h/ρ) u)`, is
`π ρ √(ρ² + h²)`. -/
@[kb "openstaxcalculus2016" "3:Example 6.62, p. 690"]
theorem paramSurfaceArea_cone {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h) :
    paramSurfaceArea (coneParam (h / ρ)) (Icc 0 ρ ×ˢ Icc 0 (2 * π)) = π * ρ * Real.sqrt (ρ ^ 2 + h ^ 2) := by
  have hn : ∀ p ∈ Icc 0 ρ ×ˢ Icc 0 (2 * π), surfVnorm (surfNormal (coneParam (h / ρ)) p) =
      p.1 * (Real.sqrt (ρ ^ 2 + h ^ 2) / ρ) := by
    intro p hp
    have hu : 0 ≤ p.1 := hp.1.1
    have hs : Real.sqrt (ρ ^ 2 + h ^ 2) / ρ = Real.sqrt (1 + (h / ρ) ^ 2) := by
      rw [show 1 + (h / ρ) ^ 2 = (ρ ^ 2 + h ^ 2) / ρ ^ 2 by field_simp, Real.sqrt_div (by positivity),
        Real.sqrt_sq hρ.le]
    have hd : surfNormal (coneParam (h / ρ)) p ⬝ᵥ surfNormal (coneParam (h / ρ)) p =
        (p.1 * Real.sqrt (1 + (h / ρ) ^ 2)) ^ 2 := by
      rw [surfNormal_cone, mul_pow, Real.sq_sqrt (by positivity)]
      simp only [dotProduct, Fin.sum_univ_three]
      simp
      linear_combination ((h / ρ) ^ 2 * p.1 ^ 2) * Real.sin_sq_add_cos_sq p.2
    rw [surfVnorm, hd, hs, Real.sqrt_sq (by positivity)]
  rw [paramSurfaceArea, setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) hn,
    setIntegral_rect (by fun_prop) hρ.le (by positivity)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, integral_id]
  field_simp
  ring

/-- Surface area of the cylinder `x² + y² = R²`, `0 ≤ z ≤ H` (`R > 0`, `H ≥ 0`), from the area integral: `2π R H`. -/
theorem paramSurfaceArea_cylinder {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) :
    paramSurfaceArea (cylinderParam R) (Icc 0 (2 * π) ×ˢ Icc 0 H) = 2 * π * R * H := by
  have hn : ∀ p ∈ Icc 0 (2 * π) ×ˢ Icc 0 H, surfVnorm (surfNormal (cylinderParam R) p) = R := by
    intro p _
    have hd : surfNormal (cylinderParam R) p ⬝ᵥ surfNormal (cylinderParam R) p = R ^ 2 := by
      rw [surfNormal_cylinder]
      simp only [dotProduct, Fin.sum_univ_three]
      simp
      linear_combination (R ^ 2) * Real.sin_sq_add_cos_sq p.1
    rw [surfVnorm, hd, Real.sqrt_sq hR.le]
  rw [paramSurfaceArea, setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) hn,
    setIntegral_rect (by fun_prop) (by positivity) hH]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

/-- OpenStax Calculus 3:Equation 6.18 (CA-651) for a graph: the area of the graph of `f` over `D` is
`∬_D √(1 + f_x² + f_y²)`. -/
@[kb "openstaxcalculus2016" "3:Equation 6.18, p. 690"]
theorem paramSurfaceArea_graph (f : ℝ × ℝ → ℝ) (fx fy : ℝ × ℝ → ℝ)
    (hx : ∀ p, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hy : ∀ p, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) (D : Set (ℝ × ℝ)) :
    paramSurfaceArea (graphParam f) D = ∫ p in D, Real.sqrt (1 + fx p ^ 2 + fy p ^ 2) := by
  unfold paramSurfaceArea
  congr 1
  funext p
  rw [surfVnorm, surfNormal_graph f fx fy hx hy p]
  simp only [dotProduct, Fin.sum_univ_three]
  simp
  congr 1
  ring

end UndergradKB.Calculus
