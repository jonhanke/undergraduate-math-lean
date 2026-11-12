import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Parametric
import UndergradKB.Calculus.Polar
import UndergradKB.Calculus.Conics
import UndergradKB.Calculus.ConeSections
import UndergradKB.Calculus.ConicReflection
import UndergradKB.Calculus.RosePetals

/-!
# OpenStax Calculus Volume 2, Chapter 7 (parametric equations and polar coordinates): course layer

The polar angle of a point `(x, y)` of the plane is `Complex.arg ⟨x, y⟩`, a number in `(-π, π]`.
-/

namespace UndergradKB.Calculus.Course.V2C7

open Real

/-- OpenStax Calculus 2:§7.3 Definition (polar coordinate system) (CA-399).
The point with polar coordinates `(r, θ)` is `(r cos θ, r sin θ)`; Mathlib's `polarCoord` is the
inverse chart (an open partial homeomorphism using `r > 0`, `θ ∈ (-π, π)`). -/
@[kb "openstaxcalculus2016" "2:§7.3 Definition (polar coordinate system), p. 575"]
theorem polar_to_rectangular_point (r θ : ℝ) :
    polarCoord.symm (r, θ) = (r * cos θ, r * sin θ) :=
  polarCoord_symm_apply (r, θ)

/-- OpenStax Calculus 2:Theorem 7.4 (CA-400), `x = r cos θ`.
For a point `(x, y)` with `r = √(x² + y²)` and `θ` its polar angle, `x = r cos θ`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.4, p. 575"]
theorem rectangular_x_eq_r_cos (x y : ℝ) :
    x = √(x ^ 2 + y ^ 2) * cos (Complex.arg ⟨x, y⟩) := by
  have h := Complex.norm_mul_cos_arg (⟨x, y⟩ : ℂ)
  have hn : ‖(⟨x, y⟩ : ℂ)‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    congr 1
    ring
  rw [hn] at h
  exact h.symm

/-- OpenStax Calculus 2:Theorem 7.4 (CA-400), `y = r sin θ`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.4, p. 575"]
theorem rectangular_y_eq_r_sin (x y : ℝ) :
    y = √(x ^ 2 + y ^ 2) * sin (Complex.arg ⟨x, y⟩) := by
  have h := Complex.norm_mul_sin_arg (⟨x, y⟩ : ℂ)
  have hn : ‖(⟨x, y⟩ : ℂ)‖ = √(x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    congr 1
    ring
  rw [hn] at h
  exact h.symm

/-- OpenStax Calculus 2:Theorem 7.4 (CA-400), `r² = x² + y²`.
The radial coordinate `r = ‖x + iy‖` satisfies `r² = x² + y²`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.4, p. 575"]
theorem polar_radius_sq (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mk]
  ring

/-- OpenStax Calculus 2:Theorem 7.4 (CA-400), `tan θ = y / x` for `x ≠ 0`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.4, p. 575"]
theorem tan_polar_angle (x y : ℝ) : tan (Complex.arg ⟨x, y⟩) = y / x :=
  Complex.tan_arg ⟨x, y⟩

/-! ## Results proved in this library -/

open Filter Topology Set intervalIntegral MeasureTheory

/-- OpenStax Calculus 2:Theorem 7.1 (CA-392). For a parametric curve `(x(t), y(t))` with
`x'(t0) ≠ 0`, the slope is `dy/dx = y'(t0) / x'(t0)`: `y ∘ g` (with `g` a local inverse of `x`)
has this derivative at `x t0`, and such a local inverse exists when `x` is strictly
differentiable (for instance `C¹`). -/
@[kb "openstaxcalculus2016" "2:Theorem 7.1, p. 560"]
theorem parametric_slope :
    (∀ {x y g : ℝ → ℝ} {x' y' t0 : ℝ}, HasDerivAt x x' t0 → x' ≠ 0 → HasDerivAt y y' t0 →
      ContinuousAt g (x t0) → g (x t0) = t0 → (∀ᶠ u in 𝓝 (x t0), x (g u) = u) →
      HasDerivAt (y ∘ g) (y' / x') (x t0)) ∧
    (∀ {x y : ℝ → ℝ} {x' y' t0 : ℝ}, HasStrictDerivAt x x' t0 → x' ≠ 0 → HasDerivAt y y' t0 →
      ∃ g : ℝ → ℝ, (∀ᶠ t in 𝓝 t0, g (x t) = t) ∧ HasDerivAt (y ∘ g) (y' / x') (x t0)) :=
  ⟨fun hx hx' hy hgc hg0 hgr => UndergradKB.Calculus.parametric_deriv hx hx' hy hgc hg0 hgr,
    fun hx hx' hy => UndergradKB.Calculus.parametric_deriv_exists_inverse hx hx' hy⟩

/-- OpenStax Calculus 2:§7.2 Equation (7.2) (CA-393). The second derivative of a parametric
curve is `(d/dt (dy/dx)) / (dx/dt)`, here written out as
`((y'' x' - y' x'') / x'^2) / x'` at the parameter `t0`. -/
@[kb "openstaxcalculus2016" "2:§7.2 Equation (7.2), p. 564"]
theorem parametric_second_derivative {x y x' y' g : ℝ → ℝ} {t0 a b : ℝ}
    (hxd : ∀ᶠ t in 𝓝 t0, HasDerivAt x (x' t) t ∧ HasDerivAt y (y' t) t ∧ x' t ≠ 0)
    (hx'' : HasDerivAt x' a t0) (hy'' : HasDerivAt y' b t0)
    (hgc : ∀ᶠ u in 𝓝 (x t0), ContinuousAt g u) (hg0 : g (x t0) = t0)
    (hgr : ∀ᶠ u in 𝓝 (x t0), x (g u) = u) :
    HasDerivAt (deriv (y ∘ g)) (((b * x' t0 - y' t0 * a) / x' t0 ^ 2) / x' t0) (x t0) :=
  UndergradKB.Calculus.parametric_second_deriv hxd hx'' hy'' hgc hg0 hgr

/-- OpenStax Calculus 2:Theorem 7.2 (CA-394). Area under a parametric curve: for `y = F ∘ x`
with `x'` continuous, `∫ y(t) x'(t) dt = ∫_{x t1}^{x t2} F`; and when `x` is monotone and
`F ≥ 0` is continuous, the area of the region under the curve is
`∫_{t1}^{t2} y(t) x'(t) dt`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.2, p. 565"]
theorem parametric_area_under_curve :
    (∀ (x x' y F : ℝ → ℝ) (t1 t2 : ℝ), (∀ t ∈ uIcc t1 t2, HasDerivAt x (x' t) t) →
      ContinuousOn x' (uIcc t1 t2) → ContinuousOn F (x '' uIcc t1 t2) →
      (∀ t ∈ uIcc t1 t2, y t = F (x t)) →
      ∫ t in t1..t2, y t * x' t = ∫ u in x t1..x t2, F u) ∧
    (∀ (x x' y F : ℝ → ℝ) (t1 t2 : ℝ), t1 ≤ t2 → (∀ t ∈ Icc t1 t2, HasDerivAt x (x' t) t) →
      ContinuousOn x' (Icc t1 t2) → MonotoneOn x (Icc t1 t2) →
      ContinuousOn F (Icc (x t1) (x t2)) → (∀ u ∈ Icc (x t1) (x t2), 0 ≤ F u) →
      (∀ t ∈ Icc t1 t2, y t = F (x t)) →
      volume (regionBetween (fun _ => (0 : ℝ)) F (Ioc (x t1) (x t2))) =
        ENNReal.ofReal (∫ t in t1..t2, y t * x' t)) :=
  ⟨fun x x' y F t1 t2 hx hx' hF hy =>
      UndergradKB.Calculus.parametric_area_integral x x' y F t1 t2 hx hx' hF hy,
    fun x x' y F t1 t2 hle hx hx' hmono hF hF0 hy =>
      UndergradKB.Calculus.parametric_area x x' y F t1 t2 hle hx hx' hmono hF hF0 hy⟩

/-- OpenStax Calculus 2:Theorem 7.3 (CA-396). The arc length of the curve `(x(t), y(t))`,
`a ≤ t ≤ b`, is `∫ √(x'(t)² + y'(t)²) dt` (`UndergradKB.Calculus.parametricArcLength`); for the
graph `x = t`, `y = f(t)` it reduces to `∫ √(1 + f'(t)²) dt`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.3, p. 567"]
theorem parametric_arc_length :
    (∀ (x y : ℝ → ℝ) (a b : ℝ), UndergradKB.Calculus.parametricArcLength x y a b =
      ∫ t in a..b, √(deriv x t ^ 2 + deriv y t ^ 2)) ∧
    (∀ (f : ℝ → ℝ) (a b : ℝ), UndergradKB.Calculus.parametricArcLength (fun t => t) f a b =
      ∫ t in a..b, √(1 + deriv f t ^ 2)) :=
  ⟨fun _ _ _ _ => rfl, UndergradKB.Calculus.parametricArcLength_graph⟩

/-- OpenStax Calculus 2:§7.2 Equation (7.6) (CA-397). Surface area of revolution of the curve
`(x(t), y(t))`: about the `x`-axis it is `2π ∫ y(t) √(x'² + y'²) dt`, and about the `y`-axis
`2π ∫ x(t) √(x'² + y'²) dt` (`UndergradKB.Calculus.surfaceAreaAboutXAxis` and
`surfaceAreaAboutYAxis`). -/
@[kb "openstaxcalculus2016" "2:§7.2 Equation (7.6), p. 571"]
theorem parametric_surface_area_of_revolution :
    (∀ (x y : ℝ → ℝ) (a b : ℝ), UndergradKB.Calculus.surfaceAreaAboutXAxis x y a b =
      2 * π * ∫ t in a..b, y t * √(deriv x t ^ 2 + deriv y t ^ 2)) ∧
    (∀ (x y : ℝ → ℝ) (a b : ℝ), UndergradKB.Calculus.surfaceAreaAboutYAxis x y a b =
      2 * π * ∫ t in a..b, x t * √(deriv x t ^ 2 + deriv y t ^ 2)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- OpenStax Calculus 2:Theorem 7.5 (CA-406). Symmetry tests for a set `G` of polar coordinate
pairs `(r, θ)`: about the polar axis if `(r, -θ)` (or `(-r, π - θ)`) is again in `G`; about the
pole if `(-r, θ)` (or `(r, θ + π)`) is; about the vertical line `θ = π/2` if `(r, π - θ)` (or
`(-r, -θ)`) is. Also the tests for a graph `r = f θ`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_symmetry_tests :
    (∀ G : Set (ℝ × ℝ), (∀ p ∈ G, (p.1, -p.2) ∈ G) →
      ∀ q ∈ UndergradKB.Calculus.polarImage G, (q.1, -q.2) ∈ UndergradKB.Calculus.polarImage G) ∧
    (∀ G : Set (ℝ × ℝ), (∀ p ∈ G, (-p.1, π - p.2) ∈ G) →
      ∀ q ∈ UndergradKB.Calculus.polarImage G, (q.1, -q.2) ∈ UndergradKB.Calculus.polarImage G) ∧
    (∀ G : Set (ℝ × ℝ), (∀ p ∈ G, (-p.1, p.2) ∈ G) →
      ∀ q ∈ UndergradKB.Calculus.polarImage G,
        (-q.1, -q.2) ∈ UndergradKB.Calculus.polarImage G) ∧
    (∀ G : Set (ℝ × ℝ), (∀ p ∈ G, (p.1, p.2 + π) ∈ G) →
      ∀ q ∈ UndergradKB.Calculus.polarImage G,
        (-q.1, -q.2) ∈ UndergradKB.Calculus.polarImage G) ∧
    (∀ G : Set (ℝ × ℝ), (∀ p ∈ G, (p.1, π - p.2) ∈ G) →
      ∀ q ∈ UndergradKB.Calculus.polarImage G,
        (-q.1, q.2) ∈ UndergradKB.Calculus.polarImage G) ∧
    (∀ G : Set (ℝ × ℝ), (∀ p ∈ G, (-p.1, -p.2) ∈ G) →
      ∀ q ∈ UndergradKB.Calculus.polarImage G,
        (-q.1, q.2) ∈ UndergradKB.Calculus.polarImage G) ∧
    (∀ f : ℝ → ℝ,
      ((∀ θ, f (-θ) = f θ) →
        ∀ q ∈ UndergradKB.Calculus.polarImage {p | p.1 = f p.2},
          (q.1, -q.2) ∈ UndergradKB.Calculus.polarImage {p | p.1 = f p.2}) ∧
      ((∀ θ, f (π - θ) = f θ) →
        ∀ q ∈ UndergradKB.Calculus.polarImage {p | p.1 = f p.2},
          (-q.1, q.2) ∈ UndergradKB.Calculus.polarImage {p | p.1 = f p.2}) ∧
      ((∀ θ, f (θ + π) = f θ) →
        ∀ q ∈ UndergradKB.Calculus.polarImage {p | p.1 = f p.2},
          (-q.1, -q.2) ∈ UndergradKB.Calculus.polarImage {p | p.1 = f p.2})) :=
  ⟨fun G h => UndergradKB.Calculus.polar_symm_axis G h,
    fun G h => UndergradKB.Calculus.polar_symm_axis' G h,
    fun G h => UndergradKB.Calculus.polar_symm_pole G h,
    fun G h => UndergradKB.Calculus.polar_symm_pole' G h,
    fun G h => UndergradKB.Calculus.polar_symm_vertical G h,
    fun G h => UndergradKB.Calculus.polar_symm_vertical' G h,
    UndergradKB.Calculus.polar_curve_symmetry⟩

/-- OpenStax Calculus 2:Theorem 7.6 (CA-407). Area in polar coordinates: for `f` continuous and
nonnegative on `[α, β]` with `β - α ≤ 2π`, the region between the origin and the curve
`r = f θ` (`UndergradKB.Calculus.polarRegion`) has area `(1/2) ∫ f(θ)² dθ`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.6, p. 593"]
theorem polar_region_area_formula (f : ℝ → ℝ) (α β : ℝ) (hf : ContinuousOn f (Icc α β))
    (hf0 : ∀ θ ∈ Icc α β, 0 ≤ f θ) (hab : α < β) (h2π : β - α ≤ 2 * π) :
    volume (UndergradKB.Calculus.polarRegion f α β) =
      ENNReal.ofReal (1 / 2 * ∫ θ in α..β, f θ ^ 2) :=
  UndergradKB.Calculus.polar_region_area f α β hf hf0 hab h2π

/-- OpenStax Calculus 2:Theorem 7.7 (CA-408). Arc length of a polar curve `r = f θ`: the speed
of `θ ↦ (f θ cos θ, f θ sin θ)` is `√(f² + f'²)`, so the arc length over `[α, β]` is
`∫ √(f(θ)² + f'(θ)²) dθ`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.7, p. 596"]
theorem polar_arc_length_formula :
    (∀ (f f' : ℝ → ℝ) (θ : ℝ), HasDerivAt f (f' θ) θ →
      √(deriv (fun s => f s * cos s) θ ^ 2 + deriv (fun s => f s * sin s) θ ^ 2) =
        √(f θ ^ 2 + f' θ ^ 2)) ∧
    (∀ (f f' : ℝ → ℝ) (α β : ℝ), (∀ θ ∈ uIcc α β, HasDerivAt f (f' θ) θ) →
      ∫ θ in α..β,
          √(deriv (fun s => f s * cos s) θ ^ 2 + deriv (fun s => f s * sin s) θ ^ 2) =
        ∫ θ in α..β, √(f θ ^ 2 + f' θ ^ 2)) :=
  ⟨fun f f' θ hf => UndergradKB.Calculus.polar_arc_length_integrand f f' θ hf,
    fun f f' α β hf => UndergradKB.Calculus.polar_arc_length f f' α β hf⟩

/-- OpenStax Calculus 2:Theorem 7.11 (CA-419). Polar equation of a conic with a focus at the
pole, eccentricity `e` and focal parameter `p`: a point `(r, θ)` (`r ≥ 0`, on the focus side of
the directrix) is at distance `e` times its distance to the directrix exactly when
`r (1 ± e cos θ) = e p` (directrix `x = ±p`) or `r (1 ± e sin θ) = e p` (directrix `y = ±p`),
that is `r = e p / (1 ± e cos θ)` or `r = e p / (1 ± e sin θ)`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.11, p. 613"]
theorem polar_equation_of_conic :
    (∀ e p r θ : ℝ, 0 ≤ r → r * cos θ ≤ p →
      (UndergradKB.Calculus.planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * cos θ - p| ↔
        r * (1 + e * cos θ) = e * p) ∧
      (1 + e * cos θ ≠ 0 → (r * (1 + e * cos θ) = e * p ↔ r = e * p / (1 + e * cos θ)))) ∧
    (∀ e p r θ : ℝ, 0 ≤ r → -p ≤ r * cos θ →
      (UndergradKB.Calculus.planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * cos θ - -p| ↔
        r * (1 - e * cos θ) = e * p) ∧
      (1 - e * cos θ ≠ 0 → (r * (1 - e * cos θ) = e * p ↔ r = e * p / (1 - e * cos θ)))) ∧
    (∀ e p r θ : ℝ, 0 ≤ r → r * sin θ ≤ p →
      (UndergradKB.Calculus.planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * sin θ - p| ↔
        r * (1 + e * sin θ) = e * p) ∧
      (1 + e * sin θ ≠ 0 → (r * (1 + e * sin θ) = e * p ↔ r = e * p / (1 + e * sin θ)))) ∧
    (∀ e p r θ : ℝ, 0 ≤ r → -p ≤ r * sin θ →
      (UndergradKB.Calculus.planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * sin θ - -p| ↔
        r * (1 - e * sin θ) = e * p) ∧
      (1 - e * sin θ ≠ 0 → (r * (1 - e * sin θ) = e * p ↔ r = e * p / (1 - e * sin θ)))) :=
  ⟨fun e p r θ hr hs => UndergradKB.Calculus.polar_conic_cos_plus e p r θ hr hs,
    fun e p r θ hr hs => UndergradKB.Calculus.polar_conic_cos_minus e p r θ hr hs,
    fun e p r θ hr hs => UndergradKB.Calculus.polar_conic_sin_plus e p r θ hr hs,
    fun e p r θ hr hs => UndergradKB.Calculus.polar_conic_sin_minus e p r θ hr hs⟩

/-- OpenStax Calculus 2:§7.5 Rotation of axes for a conic (CA-421). Rotating the axes by `θ`
turns `A x² + B x y + C y² + D x + E y + F` into `A' x'² + B' x'y' + C' y'² + D' x' + E' y' + F`
with explicit new coefficients (`UndergradKB.Calculus.rotA` and the others); the cross-term
coefficient is `B cos 2θ + (C - A) sin 2θ`, it vanishes when `cot 2θ = (A - C)/B`, and such an
angle always exists. -/
@[kb "openstaxcalculus2016" "2:§7.5 Rotation of axes for a conic, p. 615"]
theorem conic_rotation_of_axes :
    (∀ A B C D E F θ x' y' : ℝ,
      A * (x' * cos θ - y' * sin θ) ^ 2 + B * (x' * cos θ - y' * sin θ) * (x' * sin θ + y' * cos θ) +
          C * (x' * sin θ + y' * cos θ) ^ 2 + D * (x' * cos θ - y' * sin θ) +
          E * (x' * sin θ + y' * cos θ) + F =
        UndergradKB.Calculus.rotA A B C θ * x' ^ 2 + UndergradKB.Calculus.rotB A B C θ * x' * y' +
          UndergradKB.Calculus.rotC A B C θ * y' ^ 2 + UndergradKB.Calculus.rotD D E θ * x' +
          UndergradKB.Calculus.rotE D E θ * y' + F) ∧
    (∀ A B C θ : ℝ, UndergradKB.Calculus.rotB A B C θ = B * cos (2 * θ) + (C - A) * sin (2 * θ)) ∧
    (∀ A B C θ : ℝ, B ≠ 0 → sin (2 * θ) ≠ 0 → cos (2 * θ) / sin (2 * θ) = (A - C) / B →
      UndergradKB.Calculus.rotB A B C θ = 0) ∧
    (∀ A B C : ℝ, ∃ θ : ℝ, UndergradKB.Calculus.rotB A B C θ = 0) :=
  ⟨UndergradKB.Calculus.rotation_equation, UndergradKB.Calculus.rotB_eq,
    fun A B C θ hB hs h => UndergradKB.Calculus.rotB_eq_zero_of_cot A B C θ hB hs h,
    UndergradKB.Calculus.exists_rotB_eq_zero⟩

/-! ## Wave 2: petals of roses and reflective properties of conics -/

/-- OpenStax Calculus 2:§7.3 Remark on petals of roses (CA-403). The rose `r = a cos(nθ)` (`a ≠ 0`, `n ≥ 1`) has
`n` petals for odd `n` and `2n` for even `n` (petals counted by their tips, the points at distance `|a|`); for real
`n > 0` the curve closes up exactly when `n` is rational. -/
@[kb "openstaxcalculus2016" "2:§7.3 Remark on petals of roses, p. 584"]
theorem rose_petals (a : ℝ) (ha : a ≠ 0) :
    (∀ n : ℕ, 1 ≤ n → (UndergradKB.Calculus.roseTips a n).ncard = if Odd n then n else 2 * n) ∧
    (∀ n : ℝ, 0 < n →
      ((∃ T > 0, ∀ θ, UndergradKB.Calculus.polarPoint (a * cos (n * (θ + T))) (θ + T) =
          UndergradKB.Calculus.polarPoint (a * cos (n * θ)) θ) ↔ ∃ q : ℚ, n = q)) :=
  ⟨fun n hn => UndergradKB.Calculus.rose_petal_count a ha n hn,
    fun n hn => UndergradKB.Calculus.rose_periodic_iff_rational a n ha hn⟩

/-- OpenStax Calculus 2:§7.5 Reflective property of ellipse (CA-412). A ray leaving one focus `(-c, 0)` of the ellipse
`x²/a² + y²/b² = 1` reflects in the tangent line at `(a cos t, b sin t)` toward the other focus `(c, 0)`: the
reflected direction is a positive multiple of the vector to `(c, 0)`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Reflective property of ellipse, p. 607"]
theorem reflective_property_ellipse (a b c t : ℝ) (hb : 0 < b) (hab : b < a) (hc0 : 0 ≤ c)
    (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    HasDerivAt (fun u => (a * cos u, b * sin u)) (-(a * sin t), b * cos t) t ∧
    0 < (a + c * cos t) / (a - c * cos t) ∧
    2 * (((a * cos t + c) * -(a * sin t) + b * sin t * (b * cos t)) /
          (-(a * sin t) * -(a * sin t) + b * cos t * (b * cos t))) * -(a * sin t) - (a * cos t + c) =
        (a + c * cos t) / (a - c * cos t) * (c - a * cos t) ∧
    2 * (((a * cos t + c) * -(a * sin t) + b * sin t * (b * cos t)) /
          (-(a * sin t) * -(a * sin t) + b * cos t * (b * cos t))) * (b * cos t) - b * sin t =
        (a + c * cos t) / (a - c * cos t) * (0 - b * sin t) :=
  UndergradKB.Calculus.ellipse_reflective a b c t hb hab hc0 hc

/-- OpenStax Calculus 2:§7.5 Reflective property of hyperbola (CA-412). A ray aimed at the focus `(-c, 0)` of the
hyperbola `x²/a² - y²/b² = 1` reflects in the tangent line at `(a cosh u, b sinh u)` toward the other focus `(c, 0)`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Reflective property of hyperbola, p. 611"]
theorem reflective_property_hyperbola (a b c u : ℝ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 ≤ c)
    (hc : c ^ 2 = a ^ 2 + b ^ 2) :
    HasDerivAt (fun v => (a * cosh v, b * sinh v)) (a * sinh u, b * cosh u) u ∧
    0 < (c * cosh u + a) / (c * cosh u - a) ∧
    2 * (((-c - a * cosh u) * (a * sinh u) + (0 - b * sinh u) * (b * cosh u)) /
          (a * sinh u * (a * sinh u) + b * cosh u * (b * cosh u))) * (a * sinh u) - (-c - a * cosh u) =
        (c * cosh u + a) / (c * cosh u - a) * (c - a * cosh u) ∧
    2 * (((-c - a * cosh u) * (a * sinh u) + (0 - b * sinh u) * (b * cosh u)) /
          (a * sinh u * (a * sinh u) + b * cosh u * (b * cosh u))) * (b * cosh u) - (0 - b * sinh u) =
        (c * cosh u + a) / (c * cosh u - a) * (0 - b * sinh u) :=
  UndergradKB.Calculus.hyperbola_reflective a b c u ha hb hc0 hc

/-- OpenStax Calculus 2:§7.5 Reflective properties of parabola, ellipse, hyperbola (CA-412), the parabola: a ray
parallel to the axis of `y = x²/(4p)` reflects through the focus `(0, p)`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Reflective properties of parabola, ellipse, hyperbola, p. 603"]
theorem reflective_property_parabola (p t : ℝ) (hp : 0 < p) :
    HasDerivAt (fun u : ℝ => u ^ 2 / (4 * p)) (t / (2 * p)) t ∧
    (2 * ((0 * 1 + (-1) * (t / (2 * p))) / (1 * 1 + (t / (2 * p)) * (t / (2 * p)))) * 1 - 0 =
        (1 / (p * (1 + (t / (2 * p)) ^ 2))) * (0 - t)) ∧
    (2 * ((0 * 1 + (-1) * (t / (2 * p))) / (1 * 1 + (t / (2 * p)) * (t / (2 * p)))) * (t / (2 * p)) - (-1) =
        (1 / (p * (1 + (t / (2 * p)) ^ 2))) * (p - t ^ 2 / (4 * p))) ∧
    0 < 1 / (p * (1 + (t / (2 * p)) ^ 2)) :=
  UndergradKB.Calculus.parabola_reflective p t hp

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 2:§7.1 Cycloid equations (CA-390). A point on a wheel of radius `a` rolling
along a line (rotating by `-(π/2) - t` about a centre that has moved `a t`) is at
`x = a (t - sin t)`, `y = a (1 - cos t)`; the velocity components are `a (1 - cos t)` and
`a sin t`, both zero when `cos t = 1`. -/
@[kb "openstaxcalculus2016" "2:§7.1 Cycloid equations, p. 551"]
theorem cycloid_equations :
    (∀ a t : ℝ, a * (-(π / 2) - (-(π / 2) - t)) = a * t ∧
      a * t + a * cos (-(π / 2) - t) = a * (t - sin t) ∧
      a + a * sin (-(π / 2) - t) = a * (1 - cos t)) ∧
    (∀ a t : ℝ, HasDerivAt (fun s => a * (s - sin s)) (a * (1 - cos t)) t ∧
      HasDerivAt (fun s => a * (1 - cos s)) (a * sin t) t ∧
      (cos t = 1 → a * (1 - cos t) = 0 ∧ a * sin t = 0)) :=
  ⟨fun a t => UndergradKB.Calculus.cycloid_point a t,
    fun a t => UndergradKB.Calculus.cycloid_velocity a t⟩

/-- OpenStax Calculus 2:§7.1 Hypocycloid equations (CA-391). A circle of radius `b` rolling inside
a circle of radius `a` traces `x = (a-b) cos t + b cos ((a-b)/b · t)`,
`y = (a-b) sin t - b sin ((a-b)/b · t)` (the rolling angle is `-((a-b)/b) t`). -/
@[kb "openstaxcalculus2016" "2:§7.1 Hypocycloid equations, p. 551"]
theorem hypocycloid_equations (a b t : ℝ) (hb : b ≠ 0) :
    b * (t - (-((a - b) / b) * t)) = a * t ∧
    (a - b) * cos t + b * cos (-((a - b) / b) * t) = (a - b) * cos t + b * cos ((a - b) / b * t) ∧
    (a - b) * sin t + b * sin (-((a - b) / b) * t) = (a - b) * sin t - b * sin ((a - b) / b * t) :=
  UndergradKB.Calculus.hypocycloid_point a b t hb

/-- OpenStax Calculus 2:Example 7.7 (CA-395). The area under one arch of the cycloid
`x = t - sin t`, `y = 1 - cos t`, `0 ≤ t ≤ 2π`, is `3π`: the integral `∫ y x' dt` is `3π`, and the
region under any nonnegative graph `F` matching the arch has measure `3π`. -/
@[kb "openstaxcalculus2016" "2:Example 7.7, p. 566"]
theorem cycloid_arch_area_example :
    (∫ t in (0 : ℝ)..2 * π, (1 - cos t) * (1 - cos t) = 3 * π) ∧
    (∀ F : ℝ → ℝ, ContinuousOn F (Icc (0 - sin 0) (2 * π - sin (2 * π))) →
      (∀ u ∈ Icc (0 - sin 0) (2 * π - sin (2 * π)), 0 ≤ F u) →
      (∀ t ∈ Icc 0 (2 * π), 1 - cos t = F (t - sin t)) →
      volume (regionBetween (fun _ => (0 : ℝ)) F (Ioc (0 - sin 0) (2 * π - sin (2 * π)))) =
        ENNReal.ofReal (3 * π)) :=
  ⟨UndergradKB.Calculus.cycloid_arch_integral,
    fun F hF hF0 hy => UndergradKB.Calculus.cycloid_arch_area F hF hF0 hy⟩

/-- OpenStax Calculus 2:§7.3 Non-uniqueness of polar coordinates (CA-401). The pairs `(r, θ)`,
`(r, θ + 2πn)` and `(-r, θ + π)` all give the same point, and two representations with positive
radius agree only if the radii are equal and the angles differ by a multiple of `2π`. -/
@[kb "openstaxcalculus2016" "2:§7.3 Non-uniqueness of polar coordinates, p. 577"]
theorem polar_coordinates_non_unique :
    (∀ (r θ : ℝ) (n : ℤ),
      UndergradKB.Calculus.polarPoint r (θ + n * (2 * π)) = UndergradKB.Calculus.polarPoint r θ) ∧
    (∀ r θ : ℝ,
      UndergradKB.Calculus.polarPoint (-r) (θ + π) = UndergradKB.Calculus.polarPoint r θ) ∧
    (∀ {r r' θ θ' : ℝ}, 0 < r → 0 < r' →
      (UndergradKB.Calculus.polarPoint r θ = UndergradKB.Calculus.polarPoint r' θ' ↔
        r = r' ∧ ∃ n : ℤ, θ' = θ + n * (2 * π))) :=
  ⟨fun r θ n => UndergradKB.Calculus.polarPoint_add_int_mul_two_pi r θ n,
    fun r θ => UndergradKB.Calculus.polarPoint_neg_add_pi r θ,
    fun hr hr' => UndergradKB.Calculus.polarPoint_eq_iff hr hr'⟩

/-- OpenStax Calculus 2:Example 7.13 (CA-402). In polar coordinates `θ = α` is the line through
the pole of slope `tan α` (the line `y cos α = x sin α`), and `r = k` with `k > 0` is the circle
`x² + y² = k²`. -/
@[kb "openstaxcalculus2016" "2:Example 7.13, p. 580"]
theorem polar_line_and_circle :
    (∀ α : ℝ,
      {q : ℝ × ℝ | ∃ r : ℝ, q = UndergradKB.Calculus.polarPoint r α} =
        {q : ℝ × ℝ | q.2 * cos α = q.1 * sin α} ∧
      (cos α ≠ 0 → {q : ℝ × ℝ | ∃ r : ℝ, q = UndergradKB.Calculus.polarPoint r α} =
        {q : ℝ × ℝ | q.2 = tan α * q.1})) ∧
    (∀ k : ℝ, 0 < k →
      {q : ℝ × ℝ | ∃ θ : ℝ, q = UndergradKB.Calculus.polarPoint k θ} =
        {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 = k ^ 2}) :=
  ⟨fun α => UndergradKB.Calculus.polar_theta_eq_line α,
    fun k hk => UndergradKB.Calculus.polar_r_eq_circle k hk⟩

/-- OpenStax Calculus 2:Example 7.14 (CA-404). An Archimedean spiral has `r = a + b θ` and a
logarithmic spiral has `r = a e^(b θ)`; one full turn adds the constant `2π b` to the radius of
the first and multiplies the radius of the second by `e^(2π b)`. -/
@[kb "openstaxcalculus2016" "2:Example 7.14, p. 584"]
theorem spirals_example (a b θ : ℝ) :
    UndergradKB.Calculus.archimedeanSpiral a b θ = a + b * θ ∧
    UndergradKB.Calculus.logSpiral a b θ = a * exp (b * θ) ∧
    (UndergradKB.Calculus.archimedeanSpiral a b (θ + 2 * π) =
        UndergradKB.Calculus.archimedeanSpiral a b θ + 2 * π * b ∧
      UndergradKB.Calculus.logSpiral a b (θ + 2 * π) =
        UndergradKB.Calculus.logSpiral a b θ * exp (2 * π * b)) :=
  ⟨rfl, rfl, UndergradKB.Calculus.spiral_per_turn a b θ⟩

/-- OpenStax Calculus 2:§7.3 Polar curve as parametric curve (CA-405). The polar curve `r = f(θ)`
is the range of the parametrisation `θ ↦ (f θ cos θ, f θ sin θ)`. -/
@[kb "openstaxcalculus2016" "2:§7.3 Polar curve as parametric curve, p. 586"]
theorem polar_curve_as_parametric (f : ℝ → ℝ) :
    {q : ℝ × ℝ | ∃ r θ : ℝ, r = f θ ∧ q = UndergradKB.Calculus.polarPoint r θ} =
        range (UndergradKB.Calculus.polarCurve f) ∧
    ∀ θ, UndergradKB.Calculus.polarCurve f θ = (f θ * cos θ, f θ * sin θ) :=
  UndergradKB.Calculus.polarCurve_range f

/-- OpenStax Calculus 2:§7.5 Conic sections as plane sections of a cone (CA-409). The plane
`z = m x + d` (`d ≠ 0`) cuts the cone `x² + y² = z²` in a curve projecting to an ellipse when
`|m| < 1`, a parabola when `|m| = 1` and a hyperbola when `|m| > 1`, and it meets both nappes
exactly in the hyperbola case. -/
@[kb "openstaxcalculus2016" "2:§7.5 Conic sections as plane sections of a cone, p. 600"]
theorem conic_sections_of_cone (m d : ℝ) (hd : d ≠ 0) :
    (∀ x y : ℝ, (∃ z, UndergradKB.Calculus.ConeSections.OnConeSection m d x y z) ↔
      (1 - m ^ 2) * x ^ 2 - 2 * m * d * x + y ^ 2 - d ^ 2 = 0) ∧
    (|m| < 1 → ∀ x y : ℝ, (∃ z, UndergradKB.Calculus.ConeSections.OnConeSection m d x y z) ↔
      (x - m * d / (1 - m ^ 2)) ^ 2 / (d / (1 - m ^ 2)) ^ 2 +
        y ^ 2 / (d ^ 2 / (1 - m ^ 2)) = 1) ∧
    (|m| = 1 → ∀ x y : ℝ, (∃ z, UndergradKB.Calculus.ConeSections.OnConeSection m d x y z) ↔
      x = (y ^ 2 - d ^ 2) / (2 * m * d)) ∧
    (1 < |m| → ∀ x y : ℝ, (∃ z, UndergradKB.Calculus.ConeSections.OnConeSection m d x y z) ↔
      (x - m * d / (1 - m ^ 2)) ^ 2 / (d / (1 - m ^ 2)) ^ 2 -
        y ^ 2 / (d ^ 2 / (m ^ 2 - 1)) = 1) ∧
    (((∃ x y z, UndergradKB.Calculus.ConeSections.OnConeSection m d x y z ∧ 0 < z) ∧
      (∃ x y z, UndergradKB.Calculus.ConeSections.OnConeSection m d x y z ∧ z < 0)) ↔ 1 < |m|) :=
  ⟨fun x y => UndergradKB.Calculus.ConeSections.cone_section_projection m d x y,
    fun hm x y => UndergradKB.Calculus.ConeSections.cone_section_ellipse m d hm hd x y,
    fun hm x y => UndergradKB.Calculus.ConeSections.cone_section_parabola m d hm hd x y,
    fun hm x y => UndergradKB.Calculus.ConeSections.cone_section_hyperbola m d hm hd x y,
    UndergradKB.Calculus.ConeSections.cone_section_both_nappes m d hd⟩

/-- OpenStax Calculus 2:§7.5 Definition (parabola) (CA-410). For the parabola with vertex
`(h, k)`, focus `(h + p, k)` and directrix `x = h - p`, the vertex is the midpoint between focus
and directrix: its distance to the focus is `|h - (h - p)|` and `h` is their average. -/
@[kb "openstaxcalculus2016" "2:§7.5 Definition (parabola), p. 600"]
theorem parabola_vertex_halfway (h k p : ℝ) :
    UndergradKB.Calculus.planeDist h k (h + p) k = |h - (h - p)| ∧
      h = ((h + p) + (h - p)) / 2 ∧ k = (k + k) / 2 :=
  UndergradKB.Calculus.parabola_vertex_midpoint h k p

/-- OpenStax Calculus 2:§7.5 Definition (ellipse) (CA-413). With `0 < b ≤ a` and `c² = a² - b²`,
the points whose distances to the foci `(h ± c, k)` (or `(h, k ± c)`) sum to `2a` are exactly
those satisfying the standard equation of the ellipse. -/
@[kb "openstaxcalculus2016" "2:§7.5 Definition (ellipse), p. 604"]
theorem ellipse_standard_equation (a b c h k x y : ℝ) (hb : 0 < b) (hba : b ≤ a) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    (UndergradKB.Calculus.planeDist x y (h - c) k + UndergradKB.Calculus.planeDist x y (h + c) k =
        2 * a ↔ (x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 = 1) ∧
    (UndergradKB.Calculus.planeDist x y h (k - c) + UndergradKB.Calculus.planeDist x y h (k + c) =
        2 * a ↔ (x - h) ^ 2 / b ^ 2 + (y - k) ^ 2 / a ^ 2 = 1) :=
  ⟨UndergradKB.Calculus.ellipse_standard a b c h k x y hb hba hc hc2,
    UndergradKB.Calculus.ellipse_standard_vertical a b c h k x y hb hba hc hc2⟩

/-- OpenStax Calculus 2:§7.5 Definition (hyperbola) (CA-415). With `a, b > 0` and `c² = a² + b²`,
the points whose distances to the foci `(h ± c, k)` differ by `2a` in absolute value are exactly
those satisfying the standard equation of the hyperbola. -/
@[kb "openstaxcalculus2016" "2:§7.5 Definition (hyperbola), p. 608"]
theorem hyperbola_standard_equation (a b c h k x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) :
    |UndergradKB.Calculus.planeDist x y (h - c) k - UndergradKB.Calculus.planeDist x y (h + c) k| =
        2 * a ↔ (x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 = 1 :=
  UndergradKB.Calculus.hyperbola_standard a b c h k x y ha hb hc hc2

/-- OpenStax Calculus 2:§7.5 Eccentricity of ellipse and hyperbola (CA-418). With eccentricity
`e = c / a`, the focus-directrix property holds for the ellipse (`c² = a² - b²`, and then `e < 1`)
and for the hyperbola (`c² = a² + b²`, and then `e > 1`): the distance to the focus `(h + c, k)`
is `e` times the distance to the line `x = h + a²/c` exactly on the curve. -/
@[kb "openstaxcalculus2016" "2:§7.5 Eccentricity of ellipse and hyperbola, p. 612"]
theorem conic_eccentricity (a b c h k x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (c ^ 2 = a ^ 2 - b ^ 2 →
      (UndergradKB.Calculus.planeDist x y (h + c) k = (c / a) * |x - (h + a ^ 2 / c)| ↔
        (x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 = 1) ∧ c / a < 1) ∧
    (c ^ 2 = a ^ 2 + b ^ 2 →
      (UndergradKB.Calculus.planeDist x y (h + c) k = (c / a) * |x - (h + a ^ 2 / c)| ↔
        (x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 = 1) ∧ 1 < c / a) :=
  ⟨fun hc2 => UndergradKB.Calculus.ellipse_directrix a b c h k x y ha hb hc hc2,
    fun hc2 => UndergradKB.Calculus.hyperbola_directrix a b c h k x y ha hb hc hc2⟩

/-- OpenStax Calculus 2:§7.5 General equations of degree two (discriminant) (CA-420). Rotating
the axes keeps `B² - 4AC` unchanged, and once the rotated cross term vanishes the sign of the
discriminant decides the type: negative (ellipse type), zero (parabola type), positive
(hyperbola type), according to the sign of the product `A'C'` of the new coefficients. -/
@[kb "openstaxcalculus2016" "2:§7.5 General equations of degree two (discriminant), p. 614"]
theorem general_quadratic_discriminant (A B C θ : ℝ) :
    UndergradKB.Calculus.rotB A B C θ ^ 2 -
        4 * UndergradKB.Calculus.rotA A B C θ * UndergradKB.Calculus.rotC A B C θ =
      B ^ 2 - 4 * A * C ∧
    (UndergradKB.Calculus.rotB A B C θ = 0 →
      B ^ 2 - 4 * A * C =
          -4 * (UndergradKB.Calculus.rotA A B C θ * UndergradKB.Calculus.rotC A B C θ) ∧
      (B ^ 2 - 4 * A * C < 0 ↔
        0 < UndergradKB.Calculus.rotA A B C θ * UndergradKB.Calculus.rotC A B C θ) ∧
      (B ^ 2 - 4 * A * C = 0 ↔
        UndergradKB.Calculus.rotA A B C θ * UndergradKB.Calculus.rotC A B C θ = 0) ∧
      (0 < B ^ 2 - 4 * A * C ↔
        UndergradKB.Calculus.rotA A B C θ * UndergradKB.Calculus.rotC A B C θ < 0)) :=
  ⟨UndergradKB.Calculus.rotation_discriminant A B C θ,
    fun h => UndergradKB.Calculus.discriminant_classification A B C θ h⟩

end UndergradKB.Calculus.Course.V2C7
