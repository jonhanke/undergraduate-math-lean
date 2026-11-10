import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Prod
import UndergradKB.Common.Attr

/-! # Calculus: reflective properties of the ellipse and the hyperbola

Completes `parabola_reflective` (`Conics.lean`). The law of reflection sends a ray with direction `d` arriving at a
point of a curve with tangent vector `T` to the ray with direction `R(d) = 2 ((d·T)/(T·T)) T - d`, the mirror image of
`d` in the tangent line (here up to the sign convention of the parabola file: `R(d)` is the reflection of `d` in the
tangent line). Both statements are exact vector identities: `R(d)` is a positive multiple of the vector from the
point to the other focus.

* Ellipse `x²/a² + y²/b² = 1` (`0 < b < a`), foci `(±c, 0)`, `c² = a² - b²`, point `(a cos t, b sin t)`: the ray from
  the focus `(-c, 0)` reflects through the focus `(c, 0)`.
* Hyperbola `x²/a² - y²/b² = 1`, foci `(±c, 0)`, `c² = a² + b²`, point `(a cosh u, b sinh u)` of the right branch: a
  ray aimed at the focus `(-c, 0)` reflects toward the focus `(c, 0)`. -/

namespace UndergradKB.Calculus

open Real

/-- OpenStax Calculus 2:§7.5 Reflective property of ellipse (CA-412). For the ellipse `x²/a² + y²/b² = 1`
(`0 < b < a`) with foci `(±c, 0)`, `c = √(a² - b²)`, at the point `P = (a cos t, b sin t)` with tangent vector
`T = (-a sin t, b cos t)`, the direction `d = P - (-c, 0)` of a ray leaving the focus `(-c, 0)` is reflected in the
tangent line to `2 ((d·T)/(T·T)) T - d = k ((c, 0) - P)` with `k = (a + c cos t)/(a - c cos t) > 0`: the reflected
ray passes through the other focus `(c, 0)`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Reflective property of ellipse, p. 607"]
theorem ellipse_reflective (a b c t : ℝ) (hb : 0 < b) (hab : b < a) (hc0 : 0 ≤ c)
    (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    HasDerivAt (fun u => (a * cos u, b * sin u)) (-(a * sin t), b * cos t) t ∧
    0 < (a + c * cos t) / (a - c * cos t) ∧
    2 * (((a * cos t + c) * -(a * sin t) + b * sin t * (b * cos t)) /
          (-(a * sin t) * -(a * sin t) + b * cos t * (b * cos t))) * -(a * sin t) - (a * cos t + c) =
        (a + c * cos t) / (a - c * cos t) * (c - a * cos t) ∧
    2 * (((a * cos t + c) * -(a * sin t) + b * sin t * (b * cos t)) /
          (-(a * sin t) * -(a * sin t) + b * cos t * (b * cos t))) * (b * cos t) - b * sin t =
        (a + c * cos t) / (a - c * cos t) * (0 - b * sin t) := by
  have hca : c < a := by nlinarith
  have hC1 := cos_le_one t
  have hC2 := neg_one_le_cos t
  have hsc := sin_sq_add_cos_sq t
  have hm : 0 < a - c * cos t := by nlinarith
  have hp : 0 < a + c * cos t := by nlinarith
  have hTT : -(a * sin t) * -(a * sin t) + b * cos t * (b * cos t) = (a - c * cos t) * (a + c * cos t) := by
    linear_combination a ^ 2 * hsc + cos t ^ 2 * hc
  have hdT : (a * cos t + c) * -(a * sin t) + b * sin t * (b * cos t) = -(c * sin t) * (a + c * cos t) := by
    linear_combination (sin t * cos t) * hc
  refine ⟨?_, div_pos hp hm, ?_, ?_⟩
  · have := ((hasDerivAt_cos t).const_mul a).prodMk ((hasDerivAt_sin t).const_mul b)
    convert this using 1
    rw [mul_neg]
  · rw [hTT, hdT]
    field_simp
    linear_combination (2 * a * c) * hsc
  · rw [hTT, hdT]
    field_simp
    ring

/-- OpenStax Calculus 2:§7.5 Reflective property of hyperbola (CA-412). For the hyperbola `x²/a² - y²/b² = 1`
(`a, b > 0`) with foci `(±c, 0)`, `c = √(a² + b²)`, at the point `P = (a cosh u, b sinh u)` of the right branch with
tangent vector `T = (a sinh u, b cosh u)`, a ray aimed at the focus `(-c, 0)` (direction `d = (-c, 0) - P`) is
reflected in the tangent line to `2 ((d·T)/(T·T)) T - d = k ((c, 0) - P)` with `k = (c cosh u + a)/(c cosh u - a) > 0`:
the reflected ray heads to the other focus `(c, 0)`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Reflective property of hyperbola, p. 611"]
theorem hyperbola_reflective (a b c u : ℝ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c)
    (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    HasDerivAt (fun v => (a * cosh v, b * sinh v)) (a * sinh u, b * cosh u) u ∧
    0 < (c * cosh u + a) / (c * cosh u - a) ∧
    2 * (((-c - a * cosh u) * (a * sinh u) + (0 - b * sinh u) * (b * cosh u)) /
          (a * sinh u * (a * sinh u) + b * cosh u * (b * cosh u))) * (a * sinh u) - (-c - a * cosh u) =
        (c * cosh u + a) / (c * cosh u - a) * (c - a * cosh u) ∧
    2 * (((-c - a * cosh u) * (a * sinh u) + (0 - b * sinh u) * (b * cosh u)) /
          (a * sinh u * (a * sinh u) + b * cosh u * (b * cosh u))) * (b * cosh u) - (0 - b * sinh u) =
        (c * cosh u + a) / (c * cosh u - a) * (0 - b * sinh u) := by
  have hac : a < c := by nlinarith
  have hH : 1 ≤ cosh u := one_le_cosh u
  have hhs : cosh u ^ 2 - sinh u ^ 2 = 1 := cosh_sq_sub_sinh_sq u
  have hm : 0 < c * cosh u - a := by nlinarith
  have hp : 0 < c * cosh u + a := by nlinarith
  have hTT : a * sinh u * (a * sinh u) + b * cosh u * (b * cosh u) = (c * cosh u - a) * (c * cosh u + a) := by
    linear_combination (-a ^ 2) * hhs - cosh u ^ 2 * hc
  have hdT : (-c - a * cosh u) * (a * sinh u) + (0 - b * sinh u) * (b * cosh u) =
      -(c * sinh u) * (a + c * cosh u) := by
    linear_combination (sinh u * cosh u) * hc
  refine ⟨?_, div_pos hp hm, ?_, ?_⟩
  · refine ((hasDerivAt_cosh u).const_mul a).prodMk ?_
    exact (hasDerivAt_sinh u).const_mul b
  · rw [hTT, hdT]
    field_simp
    linear_combination (2 * a ^ 2 * c + 2 * a * c ^ 2 * cosh u) * hhs
  · rw [hTT, hdT]
    field_simp
    ring

end UndergradKB.Calculus
