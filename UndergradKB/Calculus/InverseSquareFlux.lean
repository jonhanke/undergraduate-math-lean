import UndergradKB.Common.Attr
import UndergradKB.Calculus.Surfaces

/-! # Calculus: flux of the inverse-square field through star-shaped closed surfaces

OpenStax Calculus 3 §6.8 (Theorem 6.21, Gauss' law). A closed surface that is star shaped about the origin is a
radial graph `r(φ, θ) = ρ(φ, θ) u(φ, θ)` over the unit sphere `u = sphereParam 1`, `0 ≤ φ ≤ π`, `0 ≤ θ ≤ 2π`,
with `ρ > 0`. For such a surface the integrand of the flux of `r/‖r‖³` is `sin φ` whatever `ρ` is (the radial parts
of `r_φ` and `r_θ` do not contribute to the triple product with `r`), so the outward flux is `4π`; scaling gives
Gauss' law `q/ε₀` for a point charge inside. The case of a surface not enclosing the origin is in
`DivergenceParam.lean` (divergence theorem on a parametrized solid avoiding the origin). -/

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

/-- `u · ((α u + β v) × (γ u + δ w)) = β δ (u · (v × w))`. -/
theorem dot_cross_radial (u v w : Fin 3 → ℝ) (α β γ δ : ℝ) :
    u ⬝ᵥ crossProduct (α • u + β • v) (γ • u + δ • w) = β * δ * (u ⬝ᵥ crossProduct v w) := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, dotProduct_add, dotProduct_smul,
    cross_self, dot_self_cross, dot_cross_self, smul_eq_mul]
  simp only [dotProduct_zero, mul_zero, zero_add, add_zero]
  ring

theorem hasDerivAt_sphereParam_fst (φ θ : ℝ) :
    HasDerivAt (fun t => sphereParam 1 (t, θ))
      ![Real.cos φ * Real.cos θ, Real.cos φ * Real.sin θ, -Real.sin φ] φ := by
  unfold sphereParam
  exact hasDerivAt_vec3 (by simpa using (Real.hasDerivAt_sin φ).mul_const (Real.cos θ))
    (by simpa using (Real.hasDerivAt_sin φ).mul_const (Real.sin θ)) (by simpa using Real.hasDerivAt_cos φ)

theorem hasDerivAt_sphereParam_snd (φ θ : ℝ) :
    HasDerivAt (fun t => sphereParam 1 (φ, t))
      ![-(Real.sin φ * Real.sin θ), Real.sin φ * Real.cos θ, 0] θ := by
  unfold sphereParam
  exact hasDerivAt_vec3 (by simpa using (Real.hasDerivAt_cos θ).const_mul (Real.sin φ))
    (by simpa using (Real.hasDerivAt_sin θ).const_mul (Real.sin φ)) (by simpa using hasDerivAt_const θ (Real.cos φ))

theorem sphereParam_one_triple (φ θ : ℝ) :
    sphereParam 1 (φ, θ) ⬝ᵥ crossProduct ![Real.cos φ * Real.cos θ, Real.cos φ * Real.sin θ, -Real.sin φ]
      ![-(Real.sin φ * Real.sin θ), Real.sin φ * Real.cos θ, 0] = Real.sin φ := by
  simp only [sphereParam, cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  linear_combination (Real.sin φ * Real.cos φ ^ 2 + Real.sin φ ^ 3) * Real.sin_sq_add_cos_sq θ +
    Real.sin φ * Real.sin_sq_add_cos_sq φ

theorem surfVnorm_smul_sphereParam {ρ : ℝ} (hρ : 0 < ρ) (p : ℝ × ℝ) : surfVnorm (ρ • sphereParam 1 p) = ρ := by
  have h1 := sphereParam_surfVnorm one_pos p
  rw [surfVnorm] at h1 ⊢
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, Real.sqrt_mul (by positivity),
    h1, Real.sqrt_mul_self hρ.le, mul_one]

/-- Bridging definition: the radial graph `r(φ, θ) = ρ(φ, θ) u(φ, θ)` over the unit sphere (a closed surface star
shaped about the origin when `ρ > 0`). -/
noncomputable def radialGraph (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Fin 3 → ℝ := ρ p • sphereParam 1 p

/-- The flux integrand of `r/‖r‖³` on a radial graph is `sin φ`. -/
theorem invSquare_dot_normal_radialGraph (ρ : ℝ × ℝ → ℝ) (hρ : Differentiable ℝ ρ) {p : ℝ × ℝ}
    (hp : 0 < ρ p) : invSquareField (radialGraph ρ p) ⬝ᵥ surfNormal (radialGraph ρ) p = Real.sin p.1 := by
  obtain ⟨φ, θ⟩ := p
  have hφ : HasDerivAt (fun t => ρ (t, θ)) (deriv (fun t => ρ (t, θ)) φ) φ :=
    ((hρ.comp (differentiable_id.prodMk (differentiable_const θ))) φ).hasDerivAt
  have hθ : HasDerivAt (fun t => ρ (φ, t)) (deriv (fun t => ρ (φ, t)) θ) θ :=
    ((hρ.comp ((differentiable_const φ).prodMk differentiable_id)) θ).hasDerivAt
  have hu : partialU (radialGraph ρ) (φ, θ) =
      deriv (fun t => ρ (t, θ)) φ • sphereParam 1 (φ, θ) +
        ρ (φ, θ) • ![Real.cos φ * Real.cos θ, Real.cos φ * Real.sin θ, -Real.sin φ] := by
    unfold partialU radialGraph
    have h : HasDerivAt (fun t => ρ (t, θ) • sphereParam 1 (t, θ))
        (ρ (φ, θ) • ![Real.cos φ * Real.cos θ, Real.cos φ * Real.sin θ, -Real.sin φ] +
          deriv (fun t => ρ (t, θ)) φ • sphereParam 1 (φ, θ)) φ :=
      hφ.smul (hasDerivAt_sphereParam_fst φ θ)
    show deriv (fun t => ρ (t, θ) • sphereParam 1 (t, θ)) φ = _
    rw [h.deriv, add_comm]
  have hv : partialV (radialGraph ρ) (φ, θ) =
      deriv (fun t => ρ (φ, t)) θ • sphereParam 1 (φ, θ) +
        ρ (φ, θ) • ![-(Real.sin φ * Real.sin θ), Real.sin φ * Real.cos θ, 0] := by
    unfold partialV radialGraph
    have h : HasDerivAt (fun t => ρ (φ, t) • sphereParam 1 (φ, t))
        (ρ (φ, θ) • ![-(Real.sin φ * Real.sin θ), Real.sin φ * Real.cos θ, 0] +
          deriv (fun t => ρ (φ, t)) θ • sphereParam 1 (φ, θ)) θ :=
      hθ.smul (hasDerivAt_sphereParam_snd φ θ)
    show deriv (fun t => ρ (φ, t) • sphereParam 1 (φ, t)) θ = _
    rw [h.deriv, add_comm]
  rw [surfNormal, hu, hv, invSquareField, radialGraph, surfVnorm_smul_sphereParam hp, smul_dotProduct,
    smul_dotProduct, dot_cross_radial, sphereParam_one_triple, smul_eq_mul, smul_eq_mul]
  field_simp

/-- OpenStax Calculus 3:Theorem 6.21 (CA-664), enclosing case for every closed surface star shaped about the origin:
the outward flux of `r/‖r‖³` through the radial graph `r = ρ(φ, θ) u(φ, θ)` (`ρ` differentiable, positive on
`[0,π]×[0,2π]`, oriented by `r_φ × r_θ`, the outward normal) is `4π`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.21, p. 738"]
theorem flux_invSquare_radialGraph (ρ : ℝ × ℝ → ℝ) (hρ : Differentiable ℝ ρ)
    (hpos : ∀ p ∈ sphereDomain, 0 < ρ p) :
    surfaceFlux invSquareField (radialGraph ρ) sphereDomain = 4 * π := by
  have h : surfaceFlux invSquareField (radialGraph ρ) sphereDomain = ∫ p in sphereDomain, Real.sin p.1 :=
    setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      (fun p hp => invSquare_dot_normal_radialGraph ρ hρ (hpos p hp))
  rw [h, sphereDomain, setIntegral_rect (by fun_prop) Real.pi_pos.le (by positivity)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  simp only [intervalIntegral.integral_const_mul, integral_sin]
  simp
  ring

/-- OpenStax Calculus 3:§6.8 Gauss' law (CA-665), for every closed surface star shaped about the charge: the field
`E = (q/(4π ε₀)) r/‖r‖³` of a point charge `q` at the origin has outward flux `q/ε₀` through the radial graph
`r = ρ(φ, θ) u(φ, θ)` (`ρ` differentiable and positive). -/
@[kb "openstaxcalculus2016" "3:§6.8 Gauss' law, p. 739"]
theorem gauss_law_radialGraph {q ε₀ : ℝ} (hε : 0 < ε₀) (ρ : ℝ × ℝ → ℝ) (hρ : Differentiable ℝ ρ)
    (hpos : ∀ p ∈ sphereDomain, 0 < ρ p) :
    surfaceFlux (fun x => (q / (4 * π * ε₀)) • invSquareField x) (radialGraph ρ) sphereDomain = q / ε₀ := by
  have h : surfaceFlux (fun x => (q / (4 * π * ε₀)) • invSquareField x) (radialGraph ρ) sphereDomain =
      (q / (4 * π * ε₀)) * surfaceFlux invSquareField (radialGraph ρ) sphereDomain := by
    unfold surfaceFlux
    simp only [smul_dotProduct, smul_eq_mul]
    exact integral_const_mul _ _
  rw [h, flux_invSquare_radialGraph ρ hρ hpos]
  have := pi_pos
  field_simp

end UndergradKB.Calculus
