import UndergradKB.Common.Attr
import UndergradKB.Calculus.GreenRegions
import UndergradKB.Calculus.Surfaces

/-! # Calculus: Stokes' theorem for parametrized surfaces

OpenStax Calculus 3 §6.7. For a vector field `F` of class `C¹` on an open set of `ℝ³` and a surface parametrized by
a `C²` map `r` of a rectangle `[a,b]×[c,d]` (oriented by `r_u × r_v`), the flux of `curl F` across the surface
(`surfaceFlux`, the book's `∬_D curl F(r(u,v)) · (r_u × r_v) dA`) equals the circulation of `F` around the boundary
curve, the image of the counterclockwise boundary of the rectangle, written as the line integrals
`∫ F(r(t)) · r'(t) dt` along the four image edges. Proof: `green_pullback_rect` for the work form `v ↦ F(x) · v`,
whose exterior derivative is `(a, b) ↦ curl F · (a × b)`.

Surfaces covered: every surface with a `C²` parametrization by a rectangle (graphs over rectangles, hemispheres and
spheres, cylinders, cones, surfaces of revolution: degenerate edges, where `r_u` or `r_v` vanishes, contribute `0`, and
edges traversed twice in opposite directions cancel). Missing for the book's statement in full generality: piecewise
smooth surfaces glued from several pieces along their edges, with the induced orientation (no theory of oriented
piecewise smooth surfaces with boundary in Mathlib). -/

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

/-- Bridging definition: the curl `(R_y - Q_z, P_z - R_x, Q_x - P_y)` of a field `F = (P, Q, R)` of `ℝ³` (as
`Fin 3 → ℝ`), partial derivatives taken as `fderiv` along the coordinate vectors. -/
noncomputable def curlVec (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![fderiv ℝ F x (Pi.single 1 1) 2 - fderiv ℝ F x (Pi.single 2 1) 1,
    fderiv ℝ F x (Pi.single 2 1) 0 - fderiv ℝ F x (Pi.single 0 1) 2,
    fderiv ℝ F x (Pi.single 0 1) 1 - fderiv ℝ F x (Pi.single 1 1) 0]

/-- The dot product as a continuous bilinear map. -/
noncomputable def dotCLM : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)

theorem dotCLM_apply (u v : Fin 3 → ℝ) : dotCLM u v = u ⬝ᵥ v := by
  simp [dotCLM, dotProduct, Fin.sum_univ_three]

theorem vec3_eq (a : Fin 3 → ℝ) :
    a = a 0 • Pi.single 0 1 + a 1 • Pi.single 1 1 + a 2 • Pi.single 2 1 := by
  ext i; fin_cases i <;> simp

/-- The exterior derivative of the work form: `(L a) · b - (L b) · a = curl · (a × b)`, where `L` is the
derivative of the field. -/
theorem dot_sub_dot_eq_curl (L : (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ) (a b : Fin 3 → ℝ) :
    L a ⬝ᵥ b - L b ⬝ᵥ a =
      ![L (Pi.single 1 1) 2 - L (Pi.single 2 1) 1, L (Pi.single 2 1) 0 - L (Pi.single 0 1) 2,
        L (Pi.single 0 1) 1 - L (Pi.single 1 1) 0] ⬝ᵥ crossProduct a b := by
  conv_lhs => rw [vec3_eq a, vec3_eq b]
  simp only [map_add, map_smul, dotProduct, Fin.sum_univ_three, cross_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.single_apply]
  simp
  ring

theorem partialU_eq_fderiv {r : ℝ × ℝ → Fin 3 → ℝ} (hr : Differentiable ℝ r) (p : ℝ × ℝ) :
    partialU r p = fderiv ℝ r p (1, 0) :=
  (hasDerivAt_horizontal (hr (p.1, p.2))).deriv

theorem partialV_eq_fderiv {r : ℝ × ℝ → Fin 3 → ℝ} (hr : Differentiable ℝ r) (p : ℝ × ℝ) :
    partialV r p = fderiv ℝ r p (0, 1) :=
  (hasDerivAt_vertical (hr (p.1, p.2))).deriv

/-- OpenStax Calculus 3:Theorem 6.19 (CA-658), Stokes' theorem for a surface parametrized by a rectangle: for `F`
of class `C¹` on an open set `U` and `r` of class `C²` mapping `[a,b]×[c,d]` into `U`, the flux of `curl F` across
the surface oriented by `r_u × r_v` equals the circulation `∮_C F · dr` along the boundary curve `C`, the image of
the counterclockwise boundary of the rectangle (edge curves `x ↦ r(x, c)`, `y ↦ r(b, y)` forward, `x ↦ r(x, d)`,
`y ↦ r(a, y)` backward; `partialU r (x, c)` is the velocity of the first, and so on). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.19, p. 714"]
theorem stokes_param (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (r : ℝ × ℝ → Fin 3 → ℝ) (hr : ContDiff ℝ 2 r) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hrU : ∀ z ∈ Icc a b ×ˢ Icc c d, r z ∈ U) :
    surfaceFlux (curlVec F) r (Icc a b ×ˢ Icc c d) =
      (∫ x in a..b, F (r (x, c)) ⬝ᵥ partialU r (x, c)) + (∫ y in c..d, F (r (b, y)) ⬝ᵥ partialV r (b, y)) -
        (∫ x in a..b, F (r (x, d)) ⬝ᵥ partialU r (x, d)) - (∫ y in c..d, F (r (a, y)) ⬝ᵥ partialV r (a, y)) := by
  have hd : Differentiable ℝ r := hr.differentiable (by norm_num)
  set ω : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ := fun x => dotCLM (F x) with hωdef
  have hω : ContDiffOn ℝ 1 ω U := dotCLM.contDiff.comp_contDiffOn hF
  have hωd : ∀ x ∈ U, ∀ u v, fderiv ℝ ω x u v = fderiv ℝ F x u ⬝ᵥ v := by
    intro x hx u v
    have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
      ((hF.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have h : HasFDerivAt ω (dotCLM.comp (fderiv ℝ F x)) x := dotCLM.hasFDerivAt.comp x hFx
    rw [h.fderiv]
    simp [dotCLM_apply]
  have hrU' : ∀ z ∈ uIcc a b ×ˢ uIcc c d, r z ∈ U := by rwa [uIcc_of_le hab, uIcc_of_le hcd]
  have key := green_pullback_rect ω r hU hω hr hrU'
  simp only [hωdef, dotCLM_apply] at key
  simp only [partialU_eq_fderiv hd, partialV_eq_fderiv hd]
  rw [← key, surfaceFlux]
  simp only [surfNormal, partialU_eq_fderiv hd, partialV_eq_fderiv hd]
  -- the integrand is the pulled-back exterior derivative
  have hG : ∀ z ∈ Icc a b ×ˢ Icc c d, curlVec F (r z) ⬝ᵥ crossProduct (fderiv ℝ r z (1, 0)) (fderiv ℝ r z (0, 1)) =
      fderiv ℝ ω (r z) (fderiv ℝ r z (1, 0)) (fderiv ℝ r z (0, 1)) -
        fderiv ℝ ω (r z) (fderiv ℝ r z (0, 1)) (fderiv ℝ r z (1, 0)) := by
    intro z hz
    rw [hωd _ (hrU z hz), hωd _ (hrU z hz), dot_sub_dot_eq_curl, curlVec]
  have hGc : ContinuousOn (fun z => fderiv ℝ ω (r z) (fderiv ℝ r z (1, 0)) (fderiv ℝ r z (0, 1)) -
      fderiv ℝ ω (r z) (fderiv ℝ r z (0, 1)) (fderiv ℝ r z (1, 0))) (Icc a b ×ˢ Icc c d) := by
    have c3 : ContinuousOn (fun z => fderiv ℝ ω (r z)) (Icc a b ×ˢ Icc c d) :=
      (hω.continuousOn_fderiv_of_isOpen hU le_rfl).comp hr.continuous.continuousOn (fun z hz => hrU z hz)
    have c4 : Continuous (fun z => fderiv ℝ r z) := hr.continuous_fderiv (by norm_num)
    have e1 : Continuous (fun z => fderiv ℝ r z (1, 0)) := c4.clm_apply continuous_const
    have e2 : Continuous (fun z => fderiv ℝ r z (0, 1)) := c4.clm_apply continuous_const
    exact ((c3.clm_apply e1.continuousOn).clm_apply e2.continuousOn).sub
      ((c3.clm_apply e2.continuousOn).clm_apply e1.continuousOn)
  rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) hG,
    setIntegral_Icc_prod hab hcd hGc]

/-- Two edge integrals agree when the edge curves agree on the closed interval (their velocities then agree in the
interior). -/
theorem edge_integral_congr (G : (Fin 3 → ℝ) → Fin 3 → ℝ) {f g : ℝ → Fin 3 → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, f x = g x) :
    ∫ x in a..b, G (f x) ⬝ᵥ deriv f x = ∫ x in a..b, G (g x) ⬝ᵥ deriv g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  have hev : f =ᶠ[nhds x] g :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun y hy => h y (Ioo_subset_Icc_self hy))
  rw [h x (Ioo_subset_Icc_self hx), hev.deriv_eq]

/-- OpenStax Calculus 3:Example 6.74 (CA-659), surface independence of the flux of a curl: two surfaces
parametrized (`C²`) by the same rectangle that have the same boundary curve (the parametrizations agree on the
boundary of the rectangle, so the boundaries carry the same orientation) have the same flux of `curl F`, for every
`C¹` field `F` on an open set containing both. -/
@[kb "openstaxcalculus2016" "3:Example 6.74, p. 718"]
theorem curl_flux_surface_independent (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (r₁ r₂ : ℝ × ℝ → Fin 3 → ℝ) (hr₁ : ContDiff ℝ 2 r₁) (hr₂ : ContDiff ℝ 2 r₂)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hrU₁ : ∀ z ∈ Icc a b ×ˢ Icc c d, r₁ z ∈ U)
    (hrU₂ : ∀ z ∈ Icc a b ×ˢ Icc c d, r₂ z ∈ U)
    (hx : ∀ x ∈ Icc a b, r₁ (x, c) = r₂ (x, c) ∧ r₁ (x, d) = r₂ (x, d))
    (hy : ∀ y ∈ Icc c d, r₁ (a, y) = r₂ (a, y) ∧ r₁ (b, y) = r₂ (b, y)) :
    surfaceFlux (curlVec F) r₁ (Icc a b ×ˢ Icc c d) = surfaceFlux (curlVec F) r₂ (Icc a b ×ˢ Icc c d) := by
  rw [stokes_param F hU hF r₁ hr₁ hab hcd hrU₁, stokes_param F hU hF r₂ hr₂ hab hcd hrU₂]
  simp only [partialU, partialV]
  rw [edge_integral_congr F hab (fun x hx' => (hx x hx').1), edge_integral_congr F hab (fun x hx' => (hx x hx').2),
    edge_integral_congr F hcd (fun y hy' => (hy y hy').1), edge_integral_congr F hcd (fun y hy' => (hy y hy').2)]

end UndergradKB.Calculus
