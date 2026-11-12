import UndergradKB.Calculus.Conics
import UndergradKB.Calculus.Parametric
import UndergradKB.Common.Attr

/-!
# OpenStax Calculus Volume 3, Chapter 1 (parametric equations and polar coordinates): course layer

Conic sections from their focus-directrix and focal definitions, proved in `UndergradKB.Calculus.Conics`.
-/

namespace UndergradKB.Calculus.Course.V3C1

open UndergradKB.Calculus

/-! ## Results proved in this library -/

/-- OpenStax Calculus 3:§1.5 Definition (parabola) (CA-411).
A point is equidistant from the focus `(h + p, k)` and the directrix `x = h - p` exactly when it
satisfies `(y - k)^2 = 4 p (x - h)`; the vertical case is symmetric. -/
@[kb "openstaxcalculus2016" "3:§1.5 Definition (parabola), p. 72"]
theorem parabola_standard_equation (h k p x y : ℝ) :
    (planeDist x y (h + p) k = |x - (h - p)| ↔ (y - k) ^ 2 = 4 * p * (x - h)) ∧
    (planeDist x y h (k + p) = |y - (k - p)| ↔ (x - h) ^ 2 = 4 * p * (y - k)) :=
  ⟨UndergradKB.Calculus.parabola_horizontal h k p x y,
    UndergradKB.Calculus.parabola_vertical h k p x y⟩

/-- OpenStax Calculus 3:§1.5 Definition (ellipse) (CA-414).
Points whose distances to the foci `(h ± c, k)` sum to `2a` are exactly those on
`(x-h)^2/a^2 + (y-k)^2/b^2 = 1`, where `c^2 = a^2 - b^2`. -/
@[kb "openstaxcalculus2016" "3:§1.5 Definition (ellipse), p. 76"]
theorem ellipse_standard_equation (a b c h k x y : ℝ) (hb : 0 < b) (hba : b ≤ a) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    planeDist x y (h - c) k + planeDist x y (h + c) k = 2 * a ↔
      (x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 = 1 :=
  UndergradKB.Calculus.ellipse_standard a b c h k x y hb hba hc hc2

/-- OpenStax Calculus 3:§1.5 Definition (hyperbola) (CA-416).
Points where the distances to the foci `(h ± c, k)` differ by `2a` in absolute value are exactly those
on `(x-h)^2/a^2 - (y-k)^2/b^2 = 1`, where `c^2 = a^2 + b^2`. -/
@[kb "openstaxcalculus2016" "3:§1.5 Definition (hyperbola), p. 80"]
theorem hyperbola_standard_equation (a b c h k x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) :
    |planeDist x y (h - c) k - planeDist x y (h + c) k| = 2 * a ↔
      (x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 = 1 :=
  UndergradKB.Calculus.hyperbola_standard a b c h k x y ha hb hc hc2

/-- OpenStax Calculus 3:§1.5 Definition (eccentricity) (CA-417).
Distance to the focus equal to `e` times the distance to the directrix is a quadratic curve
whose type (ellipse, parabola, hyperbola) is read off from `e`; for `e = 1` it is the parabola. -/
@[kb "openstaxcalculus2016" "3:§1.5 Definition (eccentricity), p. 83"]
theorem eccentricity_focus_directrix (e f d x y : ℝ) (he : 0 ≤ e) :
    (planeDist x y f 0 = e * |x - d| ↔
      (1 - e ^ 2) * x ^ 2 + y ^ 2 - 2 * (f - e ^ 2 * d) * x + (f ^ 2 - e ^ 2 * d ^ 2) = 0) ∧
    (e ^ 2 < 1 ↔ (0 : ℝ) ^ 2 - 4 * (1 - e ^ 2) * 1 < 0) ∧
    (e ^ 2 = 1 ↔ (0 : ℝ) ^ 2 - 4 * (1 - e ^ 2) * 1 = 0) ∧
    (1 < e ^ 2 ↔ 0 < (0 : ℝ) ^ 2 - 4 * (1 - e ^ 2) * 1) :=
  ⟨UndergradKB.Calculus.focus_directrix_quadratic e f d x y he,
    (UndergradKB.Calculus.eccentricity_discriminant e).2⟩

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 3:Example 1.9 (CA-398).
Revolving the semicircle `(r cos t, r sin t)`, `0 ≤ t ≤ π`, about the `x`-axis gives a sphere whose
surface area, by the parametric surface-of-revolution formula, is `4 π r²`. -/
@[kb "openstaxcalculus2016" "3:Example 1.9, p. 43"]
theorem sphere_surface_area_parametric (r : ℝ) (hr : 0 ≤ r) :
    surfaceAreaAboutXAxis (fun t => r * Real.cos t) (fun t => r * Real.sin t) 0 Real.pi
      = 4 * Real.pi * r ^ 2 :=
  UndergradKB.Calculus.sphere_surface_area r hr

end UndergradKB.Calculus.Course.V3C1
