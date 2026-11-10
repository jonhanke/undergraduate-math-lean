import UndergradKB.Common.Attr
import UndergradKB.Calculus.Surfaces

/-! # Calculus: Gauss' law for a point charge and a sphere about it

The electrostatic field of a point charge `q` at the origin is `E = (q/(4π ε₀)) r/‖r‖³`. Its outward flux through
any sphere centred at the charge is `q/ε₀` (a corollary of `flux_invSquare_sphere`). The book states Gauss' law for
every closed piecewise smooth surface enclosing the charge; that general form needs the divergence theorem on solids
bounded by such surfaces (with the charge removed by a small sphere), which Mathlib does not have: its divergence
theorem (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`) is for boxes only, and there is no
surface measure on oriented piecewise smooth surfaces. -/

namespace UndergradKB.Calculus

open Real MeasureTheory

/-- OpenStax Calculus 3:§6.8 Gauss' law (CA-665), for a sphere centred at the charge. The field of a point charge
`q` at the origin, `E = (q/(4π ε₀)) r/‖r‖³`, has outward flux `q/ε₀` through the sphere of radius `R > 0` about the
origin (spherical parametrization, outward normal `r_φ × r_θ`). -/
@[kb "openstaxcalculus2016" "3:§6.8 Gauss' law, p. 739"]
theorem gauss_law_sphere {q ε₀ R : ℝ} (hε : 0 < ε₀) (hR : 0 < R) :
    surfaceFlux (fun x => (q / (4 * π * ε₀)) • invSquareField x) (sphereParam R) sphereDomain = q / ε₀ := by
  have h : surfaceFlux (fun x => (q / (4 * π * ε₀)) • invSquareField x) (sphereParam R) sphereDomain =
      (q / (4 * π * ε₀)) * surfaceFlux invSquareField (sphereParam R) sphereDomain := by
    unfold surfaceFlux
    simp only [smul_dotProduct, smul_eq_mul]
    exact integral_const_mul _ _
  rw [h, flux_invSquare_sphere hR]
  have := pi_pos
  field_simp

end UndergradKB.Calculus
