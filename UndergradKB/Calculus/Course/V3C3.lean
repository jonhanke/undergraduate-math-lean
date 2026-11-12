import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Calculus.Kepler
import UndergradKB.Calculus.KeplerThird
import UndergradKB.Calculus.SpaceCurves
import UndergradKB.Common.Attr

/-!
# OpenStax Calculus Volume 3, Chapter 3 (vector-valued functions): course layer

A vector-valued function `r : ℝ → Fin n → ℝ` has components `fun t => r t i`. The statements use the
product topology on `Fin n → ℝ` (the same as the Euclidean one). For the dot product rule the vectors
live in `EuclideanSpace ℝ (Fin n)`.
-/

namespace UndergradKB.Calculus.Course.V3C3

open Filter Topology MeasureTheory
open scoped InnerProductSpace

/-- OpenStax Calculus 3:Theorem 3.1 (CA-481).
The limit of a vector-valued function exists (equals `L`) exactly when each component has the
corresponding limit `L i`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.1, p. 249"]
theorem limit_vector_function_iff_components {n : ℕ} (r : ℝ → Fin n → ℝ) (L : Fin n → ℝ) (t : ℝ) :
    Tendsto r (𝓝[≠] t) (𝓝 L) ↔ ∀ i, Tendsto (fun s => r s i) (𝓝[≠] t) (𝓝 (L i)) :=
  tendsto_pi_nhds

/-- OpenStax Calculus 3:§3.1 Definition (continuity of vector-valued function) (CA-482).
A vector-valued function is continuous at `t` exactly when each component is. -/
@[kb "openstaxcalculus2016" "3:§3.1 Definition (continuity of vector-valued function), p. 249"]
theorem continuousAt_vector_function_iff_components {n : ℕ} (r : ℝ → Fin n → ℝ) (t : ℝ) :
    ContinuousAt r t ↔ ∀ i, ContinuousAt (fun s => r s i) t :=
  continuousAt_pi

/-- OpenStax Calculus 3:§3.2 Definition (derivative of a vector-valued function) (CA-483).
`r' (t) = v` iff `(r (t + h) - r t) / h → v` as `h → 0`, `h ≠ 0`. -/
@[kb "openstaxcalculus2016" "3:§3.2 Definition (derivative of a vector-valued function), p. 252"]
theorem derivative_vector_function_iff_limit {n : ℕ} (r : ℝ → Fin n → ℝ) (v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt r v t ↔ Tendsto (fun h : ℝ => h⁻¹ • (r (t + h) - r t)) (𝓝[≠] 0) (𝓝 v) :=
  hasDerivAt_iff_tendsto_slope_zero

/-- OpenStax Calculus 3:Theorem 3.2 (CA-484).
A vector-valued function is differentiable at `t` with derivative `v` exactly when each component
is differentiable with derivative `v i`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.2, p. 253"]
theorem derivative_vector_function_iff_components {n : ℕ} (r : ℝ → Fin n → ℝ) (v : Fin n → ℝ)
    (t : ℝ) : HasDerivAt r v t ↔ ∀ i, HasDerivAt (fun s => r s i) (v i) t :=
  hasDerivAt_pi

/-- OpenStax Calculus 3:Theorem 3.2 (CA-484).
If every component is differentiable at `t`, then `r' t` is the vector of component derivatives. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.2, p. 253"]
theorem deriv_vector_function_components {n : ℕ} (r : ℝ → Fin n → ℝ) (t : ℝ)
    (h : ∀ i, DifferentiableAt ℝ (fun s => r s i) t) :
    deriv r t = fun i => deriv (fun s => r s i) t :=
  deriv_pi h

/-- OpenStax Calculus 3:Theorem 3.3 (parts i-iv, vi) (CA-485), constant multiple rule. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (parts i-iv, vi), p. 254"]
theorem deriv_rule_const_mul {n : ℕ} {r : ℝ → EuclideanSpace ℝ (Fin n)}
    {r' : EuclideanSpace ℝ (Fin n)} {t : ℝ} (c : ℝ) (h : HasDerivAt r r' t) :
    HasDerivAt (fun s => c • r s) (c • r') t :=
  h.const_smul c

/-- OpenStax Calculus 3:Theorem 3.3 (parts i-iv, vi) (CA-485), sum rule. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (parts i-iv, vi), p. 254"]
theorem deriv_rule_add {n : ℕ} {r s : ℝ → EuclideanSpace ℝ (Fin n)}
    {r' s' : EuclideanSpace ℝ (Fin n)} {t : ℝ} (hr : HasDerivAt r r' t) (hs : HasDerivAt s s' t) :
    HasDerivAt (fun u => r u + s u) (r' + s') t :=
  hr.add hs

/-- OpenStax Calculus 3:Theorem 3.3 (parts i-iv, vi) (CA-485), difference rule. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (parts i-iv, vi), p. 254"]
theorem deriv_rule_sub {n : ℕ} {r s : ℝ → EuclideanSpace ℝ (Fin n)}
    {r' s' : EuclideanSpace ℝ (Fin n)} {t : ℝ} (hr : HasDerivAt r r' t) (hs : HasDerivAt s s' t) :
    HasDerivAt (fun u => r u - s u) (r' - s') t :=
  hr.sub hs

/-- OpenStax Calculus 3:Theorem 3.3 (parts i-iv, vi) (CA-485), scalar function times vector:
`(f r)' = f' r + f r'`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (parts i-iv, vi), p. 254"]
theorem deriv_rule_scalar_mul {n : ℕ} {f : ℝ → ℝ} {f' : ℝ} {r : ℝ → EuclideanSpace ℝ (Fin n)}
    {r' : EuclideanSpace ℝ (Fin n)} {t : ℝ} (hf : HasDerivAt f f' t) (hr : HasDerivAt r r' t) :
    HasDerivAt (fun s => f s • r s) (f' • r t + f t • r') t :=
  (hf.smul hr).congr_deriv (add_comm _ _)

/-- OpenStax Calculus 3:Theorem 3.3 (parts i-iv, vi) (CA-485), dot product rule:
`(r ⬝ s)' = r' ⬝ s + r ⬝ s'`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (parts i-iv, vi), p. 254"]
theorem deriv_rule_dot_product {n : ℕ} {r s : ℝ → EuclideanSpace ℝ (Fin n)}
    {r' s' : EuclideanSpace ℝ (Fin n)} {t : ℝ} (hr : HasDerivAt r r' t) (hs : HasDerivAt s s' t) :
    HasDerivAt (fun u => ⟪r u, s u⟫_ℝ) (⟪r t, s'⟫_ℝ + ⟪r', s t⟫_ℝ) t :=
  hr.inner ℝ hs

/-- OpenStax Calculus 3:Theorem 3.3 (parts i-iv, vi) (CA-485), chain rule:
`(r ∘ f)' = f' • r' (f t)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (parts i-iv, vi), p. 254"]
theorem deriv_rule_chain {n : ℕ} {r : ℝ → EuclideanSpace ℝ (Fin n)}
    {r' : EuclideanSpace ℝ (Fin n)} {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t)
    (hr : HasDerivAt r r' (f t)) : HasDerivAt (fun s => r (f s)) (f' • r') t :=
  HasDerivAt.scomp t hr hf

/-- OpenStax Calculus 3:§3.2 Definition (integral of vector-valued function) (CA-489).
The integral of a vector-valued function is computed componentwise. -/
@[kb "openstaxcalculus2016" "3:§3.2 Definition (integral of vector-valued function), p. 257"]
theorem integral_vector_function_components {n : ℕ} {r : ℝ → Fin n → ℝ} {a b : ℝ}
    (hr : IntervalIntegrable r volume a b) (i : Fin n) :
    (∫ t in a..b, r t) i = ∫ t in a..b, r t i :=
  by
  have := ContinuousLinearMap.intervalIntegral_comp_comm
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) hr
  simpa using this.symm

/-- OpenStax Calculus 3:§3.2 FTC remark (CA-490).
If `r` is differentiable on `[a, b]` with integrable derivative `r'`, then `∫_a^b r' = r b - r a`. -/
@[kb "openstaxcalculus2016" "3:§3.2 FTC remark, p. 257"]
theorem integral_vector_function_ftc {n : ℕ} {r r' : ℝ → Fin n → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt r (r' t) t) (hint : IntervalIntegrable r' volume a b) :
    ∫ t in a..b, r' t = r b - r a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint

/-! ## Results proved in this library -/

section ProvedInKB

open Matrix
open UndergradKB.Calculus (vnorm speed3 curve3 arcLength3 curvature3 unitTangent3 normalN3
  KeplerMotion keplerLRL keplerNorm)

/-- OpenStax Calculus 3:Theorem 3.3 (part v) (CA-486).
Product rule for the cross product: `(f × g)' = f' × g + f × g'`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (part v), p. 254"]
theorem deriv_rule_cross_product {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⨯₃ g s) (f' ⨯₃ g t + f t ⨯₃ g') t :=
  UndergradKB.Calculus.hasDerivAt_cross3 hf hg

/-- OpenStax Calculus 3:Theorem 3.3 (part vii) (CA-487).
If `‖r(s)‖` is constant near `t`, then `r(t)` is orthogonal to `r'(t)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (part vii), p. 254"]
theorem deriv_orthogonal_of_constant_norm {r : ℝ → Fin 3 → ℝ} {r' : Fin 3 → ℝ} {t c : ℝ}
    (hr : HasDerivAt r r' t) (hc : ∀ᶠ s in nhds t, vnorm (r s) = c) : r t ⬝ᵥ r' = 0 :=
  UndergradKB.Calculus.dot_deriv_eq_zero_of_norm_const hr hc

/-- OpenStax Calculus 3:Theorem 3.4 (CA-491).
The length of a space curve is `∫ ‖r'(t)‖ dt`; for a plane curve `(f, g)` the integrand is
`√(f'² + g'²)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.4, p. 266"]
theorem arc_length_space_curve {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a b : ℝ) :
    arcLength3 (curve3 f g (fun _ => 0)) a b = ∫ t in a..b, √(deriv f t ^ 2 + deriv g t ^ 2) :=
  UndergradKB.Calculus.arcLength3_plane hf hg a b

/-- OpenStax Calculus 3:Theorem 3.5 (CA-492).
The arc-length function `s(t) = ∫ₐᵗ ‖r'‖` has derivative `‖r'(t)‖`, and a unit-speed curve has
`s(t) = t - a`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.5, p. 268"]
theorem arc_length_function {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 1 r) (a t : ℝ) :
    HasDerivAt (fun u => arcLength3 r a u) (speed3 r t) t ∧
      ((∀ s, speed3 r s = 1) → arcLength3 r a t = t - a) :=
  ⟨UndergradKB.Calculus.hasDerivAt_arcLength3 hr a t,
    fun hu => UndergradKB.Calculus.arcLength3_unit_speed hu a t⟩

/-- OpenStax Calculus 3:Theorem 3.6 (CA-494).
Curvature is `‖r' × r''‖ / ‖r'‖³` and for a graph `y = f(x)` it is
`|f''| / (1 + f'²)^(3/2)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.6, p. 270"]
theorem curvature_formulas :
    (∀ {r : ℝ → Fin 3 → ℝ}, ContDiff ℝ 2 r → ∀ {t : ℝ}, deriv r t ≠ 0 →
      curvature3 r t = vnorm (deriv r t ⨯₃ deriv (deriv r) t) / speed3 r t ^ 3) ∧
    (∀ {f : ℝ → ℝ}, ContDiff ℝ 2 f → ∀ x : ℝ,
      curvature3 (curve3 id f (fun _ => 0)) x
        = |deriv (deriv f) x| / (1 + deriv f x ^ 2) ^ (3 / 2 : ℝ)) :=
  ⟨fun hr _ h => UndergradKB.Calculus.curvature3_eq_cross hr h,
    fun hf x => UndergradKB.Calculus.curvature_graph hf x⟩

/-- OpenStax Calculus 3:Theorem 3.7 (CA-498).
The acceleration is `(d speed/dt) T + κ (speed)² N`, so it lies in the plane of `T` and `N`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.7, p. 286"]
theorem acceleration_in_tangent_normal_plane {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) (hT' : deriv (unitTangent3 r) t ≠ 0) :
    deriv (deriv r) t = deriv (speed3 r) t • unitTangent3 r t
      + (curvature3 r t * speed3 r t ^ 2) • normalN3 r t :=
  UndergradKB.Calculus.acceleration_decomposition hr h hT'

/-- OpenStax Calculus 3:Theorem 3.8 (CA-499).
The tangential and normal components of acceleration are `r' ⬝ r'' / ‖r'‖` and
`‖r' × r''‖ / ‖r'‖`, and their squares add up to `‖r''‖²`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.8, p. 287"]
theorem tangential_and_normal_components {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) (hT' : deriv (unitTangent3 r) t ≠ 0) :
    deriv (deriv r) t ⬝ᵥ unitTangent3 r t
        = (deriv r t ⬝ᵥ deriv (deriv r) t) / speed3 r t ∧
    deriv (deriv r) t ⬝ᵥ normalN3 r t
        = vnorm (deriv r t ⨯₃ deriv (deriv r) t) / speed3 r t ∧
    (deriv (deriv r) t ⬝ᵥ unitTangent3 r t) ^ 2 + (deriv (deriv r) t ⬝ᵥ normalN3 r t) ^ 2
        = vnorm (deriv (deriv r) t) ^ 2 :=
  ⟨UndergradKB.Calculus.tangential_component, UndergradKB.Calculus.normal_component hr h hT',
    UndergradKB.Calculus.tangential_normal_sq hr h hT'⟩

/-- OpenStax Calculus 3:Theorem 3.9 (CA-502).
Kepler's laws: under inverse-square attraction the orbit satisfies a conic (polar) equation about
the centre; for a central force the motion is planar and sweeps equal areas in equal times. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem kepler_laws :
    (∀ {μ : ℝ} {r : ℝ → Fin 3 → ℝ}, KeplerMotion μ r → 0 < μ → keplerLRL μ r 0 ≠ 0 →
      ∀ t : ℝ, keplerNorm (r t) *
        (1 + (keplerNorm (keplerLRL μ r 0) / μ) *
          ((r t ⬝ᵥ keplerLRL μ r 0) / (keplerNorm (r t) * keplerNorm (keplerLRL μ r 0))))
        = keplerNorm (r 0 ⨯₃ deriv r 0) ^ 2 / μ) ∧
    (∀ {r : ℝ → Fin 3 → ℝ}, ContDiff ℝ 2 r → (∀ t, ∃ c : ℝ, deriv (deriv r) t = c • r t) →
      (∀ t : ℝ, r t ⬝ᵥ (r 0 ⨯₃ deriv r 0) = 0) ∧
      ∀ t₁ t₂ : ℝ, (∫ t in t₁..t₂, vnorm (r t ⨯₃ deriv r t) / 2)
        = vnorm (r 0 ⨯₃ deriv r 0) / 2 * (t₂ - t₁)) :=
  ⟨fun h hμ hA t => UndergradKB.Calculus.kepler_polar_equation h hμ hA t,
    fun hr hc => ⟨fun t => UndergradKB.Calculus.orbit_planar hr hc t,
      fun t₁ t₂ => UndergradKB.Calculus.keplerSecond_area hr hc t₁ t₂⟩⟩

end ProvedInKB

/-- OpenStax Calculus 3:§3.4 Equation 3.30 (CA-503), Kepler's third law in Newton's form: for a body of mass `m`
moving around a mass `M` on the focal ellipse `r = p/(1 + e cos θ)` with `r² θ' = h` and `p = h²/(G (M + m))`, the
period `P` (time for `θ` to go from `0` to `2π`) satisfies `P² = 4π² a³/(G (M + m))`, `a` the semimajor axis. -/
@[kb "openstaxcalculus2016" "3:§3.4 Equation 3.30, p. 295"]
theorem keplers_third_law {G M m h e p a P : ℝ} {θ θ' : ℝ → ℝ} (hGMm : 0 < G * (M + m)) (hh : 0 < h)
    (he0 : 0 ≤ e) (he1 : e < 1) (hp : p = h ^ 2 / (G * (M + m))) (ha : a = p / (1 - e ^ 2))
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hareal : ∀ t, (p / (1 + e * Real.cos (θ t))) ^ 2 * θ' t = h)
    (h0 : θ 0 = 0) (hP : θ P = 2 * Real.pi) :
    P ^ 2 = 4 * Real.pi ^ 2 * a ^ 3 / (G * (M + m)) :=
  UndergradKB.Calculus.kepler_third_law hGMm hh he0 he1 hp ha hθ hareal h0 hP

/-! ## Wave 3: further results -/

section Wave3

open Matrix
open UndergradKB.Calculus (vnorm speed3 curvature3 unitTangent3 normalN3 binormal3 helix3 graphCurve jvec)

/-- OpenStax Calculus 3:§3.1 helix example (CA-480).
The helix of radius `a` and pitch constant `b` is the space curve `(a cos t, a sin t, b t)`; for `a > 0`
its curvature is the constant `a/(a²+b²)`. -/
@[kb "openstaxcalculus2016" "3:§3.1 helix example, p. 247"]
theorem helix_space_curve (a b : ℝ) (ha : 0 < a) :
    helix3 a b = (fun t => ![a * Real.cos t, a * Real.sin t, b * t]) ∧
      ∀ t : ℝ, curvature3 (helix3 a b) t = a / (a ^ 2 + b ^ 2) :=
  ⟨rfl, fun t => UndergradKB.Calculus.curvature_helix3 ha t⟩

/-- OpenStax Calculus 3:§3.2 Definition (tangent and unit tangent vector) (CA-488).
If `r'(t) ≠ 0`, then `T(t) = r'(t)/‖r'(t)‖` has length one and `r'(t)` is its speed times `T(t)`. -/
@[kb "openstaxcalculus2016" "3:§3.2 Definition (tangent and unit tangent vector), p. 256"]
theorem unit_tangent_vector {r : ℝ → Fin 3 → ℝ} {t : ℝ} (h : deriv r t ≠ 0) :
    unitTangent3 r t = (vnorm (deriv r t))⁻¹ • deriv r t ∧ vnorm (unitTangent3 r t) = 1 ∧
      deriv r t = speed3 r t • unitTangent3 r t :=
  ⟨rfl, UndergradKB.Calculus.vnorm_unitTangent3 h,
    UndergradKB.Calculus.deriv_eq_speed_smul_unitTangent3 h⟩

/-- OpenStax Calculus 3:§3.3 Definition (curvature) (CA-493).
Curvature is the rate of turning of the unit tangent per unit of arc length, `‖T'‖/‖r'‖`; for a
unit-speed curve it is the length of the acceleration `r''`. -/
@[kb "openstaxcalculus2016" "3:§3.3 Definition (curvature), p. 270"]
theorem curvature_definition {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) :
    (∀ t : ℝ, curvature3 r t = vnorm (deriv (unitTangent3 r) t) / speed3 r t) ∧
      ((∀ s, speed3 r s = 1) → ∀ t : ℝ, curvature3 r t = vnorm (deriv (deriv r) t)) :=
  ⟨fun _ => rfl, fun hu t => UndergradKB.Calculus.curvature3_unit_speed hr hu t⟩

/-- OpenStax Calculus 3:§3.3 Definition (principal unit normal, binormal) (CA-495).
The principal unit normal is `N = T'/‖T'‖` and the binormal is `B = T × N`; `T`, `N`, `B` are unit
vectors that are pairwise orthogonal. -/
@[kb "openstaxcalculus2016" "3:§3.3 Definition (principal unit normal, binormal), p. 274"]
theorem principal_normal_and_binormal {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) (hT' : deriv (unitTangent3 r) t ≠ 0) :
    vnorm (unitTangent3 r t) = 1 ∧ vnorm (normalN3 r t) = 1 ∧ vnorm (binormal3 r t) = 1 ∧
    unitTangent3 r t ⬝ᵥ normalN3 r t = 0 ∧ unitTangent3 r t ⬝ᵥ binormal3 r t = 0 ∧
    normalN3 r t ⬝ᵥ binormal3 r t = 0 :=
  UndergradKB.Calculus.frame3_orthonormal hr h hT'

/-- OpenStax Calculus 3:§3.3 osculating circle (CA-496).
For a plane graph `y = f(x)` with `f''(x₀) ≠ 0`, the centre of the osculating circle is the point at
distance `1/κ` from the curve along the principal normal, and the circle of that radius about it
touches the graph to second order at `x₀`. -/
@[kb "openstaxcalculus2016" "3:§3.3 osculating circle, p. 278"]
theorem osculating_circle {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ)
    (hq : deriv (deriv f) x ≠ 0) :
    ((graphCurve f x + (1 / curvature3 (graphCurve f) x) • normalN3 (graphCurve f) x) 0
        = x - deriv f x * (1 + deriv f x ^ 2) / deriv (deriv f) x ∧
    (graphCurve f x + (1 / curvature3 (graphCurve f) x) • normalN3 (graphCurve f) x) 1
        = f x + (1 + deriv f x ^ 2) / deriv (deriv f) x ∧
    (graphCurve f x + (1 / curvature3 (graphCurve f) x) • normalN3 (graphCurve f) x) 2 = 0) ∧
    (let cx := x - deriv f x * (1 + deriv f x ^ 2) / deriv (deriv f) x
     let cy := f x + (1 + deriv f x ^ 2) / deriv (deriv f) x
     let φ := fun y => (y - cx) ^ 2 + (f y - cy) ^ 2 - (1 / curvature3 (graphCurve f) x) ^ 2
     φ x = 0 ∧ deriv φ x = 0 ∧ deriv (deriv φ) x = 0) :=
  ⟨UndergradKB.Calculus.osculating_center_graph hf x hq,
    UndergradKB.Calculus.osculating_circle_graph hf x hq⟩

/-- OpenStax Calculus 3:§3.4 projectile motion equations (CA-500).
If the only acceleration is gravity, `r'' = -g j`, with `r(0) = r₀` and `r'(0) = v₀`, then
`r(t) = -(1/2) g t² j + v₀ t + r₀`; launched from the origin at angle `θ` with speed `v` the path is
`(v cos θ · t, v sin θ · t - g t²/2)`. -/
@[kb "openstaxcalculus2016" "3:§3.4 projectile motion equations, p. 289"]
theorem projectile_motion_equations {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {g : ℝ}
    (hacc : ∀ t, deriv (deriv r) t = (-g) • jvec) :
    (∀ r0 v0 : Fin 3 → ℝ, r 0 = r0 → deriv r 0 = v0 → ∀ t : ℝ,
      r t = (-(g * t ^ 2 / 2)) • jvec + t • v0 + r0) ∧
    (∀ v θ : ℝ, r 0 = 0 → deriv r 0 = ![v * Real.cos θ, v * Real.sin θ, 0] → ∀ t : ℝ,
      r t = ![v * Real.cos θ * t, v * Real.sin θ * t - g * t ^ 2 / 2, 0]) :=
  ⟨fun _ _ h0 hv t => UndergradKB.Calculus.projectile_position hr hacc h0 hv t,
    fun _ _ h0 hv t => UndergradKB.Calculus.projectile_launch hr hacc h0 hv t⟩

/-- OpenStax Calculus 3:§3.4 range remark (CA-501).
The projectile returns to height zero after time `2 v sin θ / g` at horizontal distance
`v² sin 2θ / g`, and for `g > 0` this range is largest, among launch angles in `[0, π/2]`, exactly at
`θ = π/4`. -/
@[kb "openstaxcalculus2016" "3:§3.4 range remark, p. 293"]
theorem projectile_range_maximal {g v θ : ℝ} (hg : 0 < g) (hv : v ≠ 0)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (v * Real.sin θ * (2 * v * Real.sin θ / g) - g * (2 * v * Real.sin θ / g) ^ 2 / 2 = 0 ∧
      v * Real.cos θ * (2 * v * Real.sin θ / g) = v ^ 2 * Real.sin (2 * θ) / g) ∧
    (v ^ 2 * Real.sin (2 * θ) / g ≤ v ^ 2 * Real.sin (2 * (Real.pi / 4)) / g ∧
      (v ^ 2 * Real.sin (2 * θ) / g = v ^ 2 * Real.sin (2 * (Real.pi / 4)) / g →
        θ = Real.pi / 4)) :=
  ⟨UndergradKB.Calculus.projectile_range_formula hg.ne', UndergradKB.Calculus.range_max_at_pi_div_four hg hv hθ⟩

end Wave3

end UndergradKB.Calculus.Course.V3C3
