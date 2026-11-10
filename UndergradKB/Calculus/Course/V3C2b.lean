import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Calculus.LineRelations
import UndergradKB.Calculus.LinesPlanes
import UndergradKB.Calculus.QuadricsCoordinates
import UndergradKB.Calculus.Vectors
import UndergradKB.Common.Attr

/-!
# OpenStax Calculus Volume 3, Chapter 2 (vectors in space): course layer, wave 3

Further wrappers of results proved in the topic files `Vectors`, `LinesPlanes`, `LineRelations` and
`QuadricsCoordinates`. Vectors of space are `Fin 3 → ℝ`.
-/

namespace UndergradKB.Calculus.Course.V3C2

open Matrix

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 3:§2.1 Definition (parallel vectors) (CA-423).
Two nonzero vectors are parallel (one a scalar multiple of the other) exactly when the angle between
them is `0` or `π`. -/
@[kb "openstaxcalculus2016" "3:§2.1 Definition (parallel vectors), p. 98"]
theorem parallel_vectors_iff_angle {u v : Fin 3 → ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (∃ c : ℝ, u = c • v) ↔ (vangle u v = 0 ∨ vangle u v = Real.pi) :=
  UndergradKB.Calculus.parallel_iff_angle hu hv

/-- OpenStax Calculus 3:§2.1 text (components from magnitude and angle) (CA-429).
A plane vector with components `(x, y)` has components magnitude times cosine and sine of its direction
angle; and the magnitude of `(m cos θ, m sin θ)` is `|m|`. -/
@[kb "openstaxcalculus2016" "3:§2.1 text (components from magnitude and angle), p. 107"]
theorem plane_vector_components_from_angle (x y m θ : ℝ) :
    (x = Real.sqrt (x ^ 2 + y ^ 2) * Real.cos (Complex.arg ⟨x, y⟩) ∧
      y = Real.sqrt (x ^ 2 + y ^ 2) * Real.sin (Complex.arg ⟨x, y⟩)) ∧
    Real.sqrt ((m * Real.cos θ) ^ 2 + (m * Real.sin θ) ^ 2) = |m| :=
  ⟨UndergradKB.Calculus.plane_vector_components x y, UndergradKB.Calculus.sqrt_polar_components m θ⟩

/-- OpenStax Calculus 3:§2.3 Definition (direction angles and direction cosines) (CA-441).
For a nonzero vector the cosines of the angles with the three coordinate axes are its components over
its length, and the squares of the direction cosines sum to one. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (direction angles and direction cosines), p. 146"]
theorem direction_angles_cosines {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    Real.cos (vangle v ei) = v 0 / len v ∧ Real.cos (vangle v ej) = v 1 / len v ∧
    Real.cos (vangle v ek) = v 2 / len v ∧
    Real.cos (vangle v ei) ^ 2 + Real.cos (vangle v ej) ^ 2 + Real.cos (vangle v ek) ^ 2 = 1 :=
  UndergradKB.Calculus.direction_cosines hv

/-- OpenStax Calculus 3:§2.3 Definition (scalar projection, Eq 2.7) (CA-443).
The scalar projection of `v` onto `u` is `(u · v)/‖u‖`; it is the signed length of the vector projection
and equals `‖v‖ cos θ`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (scalar projection, Eq 2.7), p. 148"]
theorem scalar_projection_formula {u : Fin 3 → ℝ} (hu : u ≠ 0) (v : Fin 3 → ℝ) :
    vecProj u v = scalarProj u v • ((len u)⁻¹ • u) ∧ |scalarProj u v| = len (vecProj u v) ∧
    scalarProj u v = len v * Real.cos (vangle u v) ∧ (v - vecProj u v) ⬝ᵥ u = 0 :=
  UndergradKB.Calculus.scalarProj_spec hu v

/-- OpenStax Calculus 3:§2.3 Definition (work, Eq 2.8) (CA-445).
The work of a constant force `F` over the displacement `s` is the dot product `F · s`, equal to
`‖F‖ ‖s‖ cos θ`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (work, Eq 2.8), p. 151"]
theorem work_constant_force (F s : Fin 3 → ℝ) :
    F ⬝ᵥ s = len F * len s * Real.cos (vangle F s) :=
  UndergradKB.Calculus.work_eq F s

/-- OpenStax Calculus 3:§2.4 text (cross products of standard unit vectors) (CA-449).
The cross products among `i`, `j`, `k` follow the cyclic rule, reverse order flips the sign, and a unit
vector crossed with itself is zero. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (cross products of standard unit vectors), p. 160"]
theorem cross_products_of_standard_unit_vectors :
    ei ⨯₃ ej = ek ∧ ej ⨯₃ ek = ei ∧ ek ⨯₃ ei = ej ∧
    ej ⨯₃ ei = -ek ∧ ek ⨯₃ ej = -ei ∧ ei ⨯₃ ek = -ej ∧
    ei ⨯₃ ei = 0 ∧ ej ⨯₃ ej = 0 ∧ ek ⨯₃ ek = 0 :=
  UndergradKB.Calculus.cross_unit_vectors

/-- OpenStax Calculus 3:§2.4 text (identities for permuting a triple scalar product) (CA-456).
The triple scalar product is unchanged by cyclic permutations and changes sign under a swap of two
of the vectors. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (identities for permuting a triple scalar product), p. 168"]
theorem triple_scalar_product_permutations (u v w : Fin 3 → ℝ) :
    (u ⬝ᵥ v ⨯₃ w = v ⬝ᵥ w ⨯₃ u ∧ v ⬝ᵥ w ⨯₃ u = w ⬝ᵥ u ⨯₃ v) ∧
    (u ⬝ᵥ v ⨯₃ w = -(v ⬝ᵥ u ⨯₃ w) ∧ u ⬝ᵥ v ⨯₃ w = -(u ⬝ᵥ w ⨯₃ v) ∧
      u ⬝ᵥ v ⨯₃ w = -(w ⬝ᵥ v ⨯₃ u)) :=
  ⟨UndergradKB.Calculus.triple_cyclic u v w, UndergradKB.Calculus.triple_swap u v w⟩

/-- OpenStax Calculus 3:Example 2.42 (CA-458).
Three vectors in space are coplanar exactly when their triple scalar product vanishes. -/
@[kb "openstaxcalculus2016" "3:Example 2.42, p. 169"]
theorem coplanar_vectors_triple_product_zero (u v w : Fin 3 → ℝ) :
    Coplanar u v w ↔ u ⬝ᵥ v ⨯₃ w = 0 :=
  UndergradKB.Calculus.coplanar_iff_triple_eq_zero u v w

/-- OpenStax Calculus 3:§2.4 Definition (torque) (CA-459).
The torque `r × F` has magnitude `‖r‖ ‖F‖ sin θ`. -/
@[kb "openstaxcalculus2016" "3:§2.4 Definition (torque), p. 170"]
theorem torque_cross_product_magnitude (r F : Fin 3 → ℝ) :
    len (r ⨯₃ F) = len r * len F * Real.sin (vangle r F) :=
  UndergradKB.Calculus.torque_magnitude r F

/-- OpenStax Calculus 3:§2.5 text (skew lines and relationships between lines) (CA-463).
Two lines in space are equal, parallel and distinct, intersecting, or skew; these cases exclude each
other, and for a nonzero second direction skewness means that the scalar triple product is nonzero. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (skew lines and relationships between lines), p. 182"]
theorem lines_in_space_relationships (P Q a b : Fin 3 → ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (LinesEqual P a Q b ∨ LinesParallelDistinct P a Q b ∨ LinesIntersecting P a Q b ∨
      LinesSkew P a Q b) ∧
    (¬ (LinesEqual P a Q b ∧ LinesParallelDistinct P a Q b) ∧
    ¬ (LinesEqual P a Q b ∧ LinesIntersecting P a Q b) ∧
    ¬ (LinesEqual P a Q b ∧ LinesSkew P a Q b) ∧
    ¬ (LinesParallelDistinct P a Q b ∧ LinesIntersecting P a Q b) ∧
    ¬ (LinesParallelDistinct P a Q b ∧ LinesSkew P a Q b) ∧
    ¬ (LinesIntersecting P a Q b ∧ LinesSkew P a Q b)) ∧
    (LinesSkew P a Q b ↔ (a ⨯₃ b) ⬝ᵥ (Q - P) ≠ 0) :=
  ⟨UndergradKB.Calculus.lines_classification P Q a b ha hb,
    UndergradKB.Calculus.lines_classification_exclusive P Q a b,
    UndergradKB.Calculus.lines_skew_iff P Q a b hb⟩

/-- OpenStax Calculus 3:§2.5 Definition (vector and scalar equation of a plane, Eq 2.17, 2.18) (CA-464).
The plane through `P₀` with normal `n` is the solution set of `n · (x - P₀) = 0`, which in coordinates
is `a(x-x₀)+b(y-y₀)+c(z-z₀)=0` or the general form `ax+by+cz+d=0`; every general-form equation with
nonzero normal describes such a plane. -/
@[kb "openstaxcalculus2016" "3:§2.5 Definition (vector and scalar equation of a plane, Eq 2.17, 2.18), p. 186"]
theorem plane_equation_forms (n P₀ : Fin 3 → ℝ) :
    (plane n P₀ = {x | n 0 * (x 0 - P₀ 0) + n 1 * (x 1 - P₀ 1) + n 2 * (x 2 - P₀ 2) = 0} ∧
    plane n P₀ = planeGen n (-(n ⬝ᵥ P₀)) ∧
    planeGen n (-(n ⬝ᵥ P₀)) =
      {x | n 0 * x 0 + n 1 * x 1 + n 2 * x 2 + (-(n 0 * P₀ 0 + n 1 * P₀ 1 + n 2 * P₀ 2)) = 0}) ∧
    (n ≠ 0 → ∀ d : ℝ, ∃ Q₀, planeGen n d = plane n Q₀) :=
  ⟨UndergradKB.Calculus.plane_forms n P₀, fun hn d => UndergradKB.Calculus.planeGen_eq_plane hn d⟩

/-- OpenStax Calculus 3:§2.5 text (parallel and intersecting planes) (CA-466).
Two distinct planes with nonzero normals are either parallel (parallel normals, no common point) or meet
in a line with direction the cross product of the normals. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (parallel and intersecting planes), p. 189"]
theorem planes_parallel_or_meet_in_line (n₁ n₂ : Fin 3 → ℝ) (d₁ d₂ : ℝ) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0)
    (hne : planeGen n₁ d₁ ≠ planeGen n₂ d₂) :
    (Par n₁ n₂ ∧ Disjoint (planeGen n₁ d₁) (planeGen n₂ d₂)) ∨
    (¬ Par n₁ n₂ ∧ n₁ ⨯₃ n₂ ≠ 0 ∧
      ∃ P, planeGen n₁ d₁ ∩ planeGen n₂ d₂ = line P (n₁ ⨯₃ n₂)) :=
  UndergradKB.Calculus.planes_parallel_or_line n₁ n₂ d₁ d₂ h₁ h₂ hne

/-- OpenStax Calculus 3:§2.5 text (angle between two planes) (CA-467).
The angle between two planes has cosine `|n₁ · n₂|/(‖n₁‖‖n₂‖)` and lies in `[0, π/2]`; it is zero exactly
for parallel normals and `π/2` exactly for orthogonal normals. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (angle between two planes), p. 190"]
theorem angle_between_planes {n₁ n₂ : Fin 3 → ℝ} (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) :
    Real.cos (planeAngle n₁ n₂) = |n₁ ⬝ᵥ n₂| / (len n₁ * len n₂) ∧
    0 ≤ planeAngle n₁ n₂ ∧ planeAngle n₁ n₂ ≤ Real.pi / 2 ∧
    planeAngle n₁ n₂ = min (vangle n₁ n₂) (Real.pi - vangle n₁ n₂) ∧
    (planeAngle n₁ n₂ = 0 ↔ Par n₁ n₂) ∧
    (planeAngle n₁ n₂ = Real.pi / 2 ↔ n₁ ⬝ᵥ n₂ = 0) :=
  UndergradKB.Calculus.planeAngle_spec h₁ h₂

/-- OpenStax Calculus 3:§2.5 Student Project (distance between two skew lines) (CA-468).
The smallest distance between points of the lines through `P`, `Q` with directions `a`, `b` is
`|(a × b) · (Q - P)| / ‖a × b‖`. -/
@[kb "openstaxcalculus2016" "3:§2.5 Student Project (distance between two skew lines), p. 192"]
theorem distance_between_skew_lines (P Q a b : Fin 3 → ℝ) (hab : a ⨯₃ b ≠ 0) :
    IsLeast {r | ∃ s t : ℝ, r = len ((P + s • a) - (Q + t • b))}
      (|(a ⨯₃ b) ⬝ᵥ (Q - P)| / len (a ⨯₃ b)) :=
  UndergradKB.Calculus.distance_skew_lines P Q a b hab

/-- OpenStax Calculus 3:§2.6 text (ellipsoid and its traces) (CA-472).
The traces of the ellipsoid in horizontal planes and in the coordinate planes are ellipses, and it is a
sphere when the three semi-axes are equal. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (ellipsoid and its traces), p. 204"]
theorem ellipsoid_traces {a b c k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : |k| < c)
    (p : Fin 3 → ℝ) :
    ((p ∈ ellipsoid a b c ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * Real.sqrt (1 - k ^ 2 / c ^ 2))) ^ 2 +
        (p 1 / (b * Real.sqrt (1 - k ^ 2 / c ^ 2))) ^ 2 = 1)) ∧
    (((p ∈ ellipsoid a b c ∧ p 0 = 0) ↔ (p 0 = 0 ∧ p 1 ^ 2 / b ^ 2 + p 2 ^ 2 / c ^ 2 = 1)) ∧
    ((p ∈ ellipsoid a b c ∧ p 1 = 0) ↔ (p 1 = 0 ∧ p 0 ^ 2 / a ^ 2 + p 2 ^ 2 / c ^ 2 = 1))) ∧
    (∀ r : ℝ, 0 < r → (p ∈ ellipsoid r r r ↔ len p = r)) :=
  ⟨UndergradKB.Calculus.ellipsoid_trace_z ha hb hc hk p,
    UndergradKB.Calculus.ellipsoid_trace_coordinate a b c p,
    fun _ hr => UndergradKB.Calculus.ellipsoid_eq_sphere hr p⟩

/-- OpenStax Calculus 3:§2.6 text (elliptic paraboloid) (CA-473).
The elliptic paraboloid `z = x²/a² + y²/b²` has ellipses as traces in the planes `z = k` with `k > 0`
and parabolas as traces in the vertical coordinate planes. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (elliptic paraboloid), p. 205"]
theorem elliptic_paraboloid_traces {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (p : Fin 3 → ℝ) :
    ((p ∈ ellipticParaboloid a b ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * Real.sqrt k)) ^ 2 + (p 1 / (b * Real.sqrt k)) ^ 2 = 1)) ∧
    (((p ∈ ellipticParaboloid a b ∧ p 1 = k) ↔ (p 1 = k ∧ p 2 = p 0 ^ 2 / a ^ 2 + k ^ 2 / b ^ 2)) ∧
    ((p ∈ ellipticParaboloid a b ∧ p 0 = k) ↔ (p 0 = k ∧ p 2 = k ^ 2 / a ^ 2 + p 1 ^ 2 / b ^ 2))) :=
  ⟨UndergradKB.Calculus.paraboloid_trace_horizontal ha hb hk p,
    UndergradKB.Calculus.paraboloid_trace_vertical a b k p⟩

/-- OpenStax Calculus 3:§2.6 text (hyperboloid of one sheet) (CA-474).
Traces of the standard quadric surfaces in horizontal planes: ellipses for the hyperboloid of one sheet,
empty or ellipses for the hyperboloid of two sheets, ellipses for the elliptic cone away from the apex,
and the level curves `(x/a - y/b)(x/a + y/b) = k` of the hyperbolic paraboloid. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (hyperboloid of one sheet), p. 207"]
theorem quadric_surfaces_traces {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℝ)
    (p : Fin 3 → ℝ) :
    ((p ∈ hyperboloidOne a b c ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * Real.sqrt (1 + k ^ 2 / c ^ 2))) ^ 2 +
        (p 1 / (b * Real.sqrt (1 + k ^ 2 / c ^ 2))) ^ 2 = 1)) ∧
    ((|k| < c → ¬ (p ∈ hyperboloidTwo a b c ∧ p 2 = k)) ∧
      (c < |k| → ((p ∈ hyperboloidTwo a b c ∧ p 2 = k) ↔
        (p 2 = k ∧ (p 0 / (a * Real.sqrt (k ^ 2 / c ^ 2 - 1))) ^ 2 +
          (p 1 / (b * Real.sqrt (k ^ 2 / c ^ 2 - 1))) ^ 2 = 1)))) ∧
    (k ≠ 0 → ((p ∈ ellipticCone a b c ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * (|k| / c))) ^ 2 + (p 1 / (b * (|k| / c))) ^ 2 = 1))) ∧
    ((p ∈ hyperbolicParaboloid a b ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / a - p 1 / b) * (p 0 / a + p 1 / b) = k)) :=
  ⟨UndergradKB.Calculus.hyperboloidOne_trace ha hb hc k p,
    UndergradKB.Calculus.hyperboloidTwo_trace ha hb hc k p,
    fun hk => UndergradKB.Calculus.cone_trace ha hb hc k hk p,
    UndergradKB.Calculus.hyperbolicParaboloid_trace a b k p⟩

end UndergradKB.Calculus.Course.V3C2
