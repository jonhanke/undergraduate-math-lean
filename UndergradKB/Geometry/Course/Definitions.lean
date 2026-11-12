import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.Sphere.PolePolar
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Topology.MetricSpace.Isometry
import UndergradKB.Common.Attr

/-! # Course layer: definitions of Petrunin's book

The "in Mathlib" definition rows of the audit (`docs/coverage/geometry/checklist.md`) stated as
characterizations of the Mathlib notion, in the book's words (Petrunin, *Euclidean Plane and its
Relatives*, 3rd ed.): metric space, isometry, straight angle, degenerate triangle, sign of an angle,
circle, inside/outside, tangency, inversion, field automorphism of `ℝ`, polar, stereographic
projection, complex numbers, extended complex plane, holomorphic function, solid triangle,
bounded set. -/

namespace UndergradKB.Geometry.Course

open EuclideanGeometry Real Filter Asymptotics Topology
open scoped RealInnerProductSpace

/-! ## Chapter 1 -/

/-- Petrunin, Definition 1.1 (p. 10), GE-001: the four axioms of a metric. -/
@[kb "petrunin2025" "Definition 1.1, p. 10"]
theorem petrunin_def_metric_axioms (X : Type*) [MetricSpace X] :
    (∀ A B : X, 0 ≤ dist A B) ∧ (∀ A B : X, dist A B = 0 ↔ A = B) ∧
      (∀ A B : X, dist A B = dist B A) ∧ (∀ A B C : X, dist A C ≤ dist A B + dist B C) :=
  ⟨fun _ _ => dist_nonneg, fun _ _ => dist_eq_zero, dist_comm, dist_triangle⟩

/-- Petrunin, Section 1E (p. 12), GE-007: a map is distance-preserving iff it is an isometry of
Mathlib (preserves the extended distance). -/
@[kb "petrunin2025" "Section 1E, distance-preserving map, p. 12"]
theorem petrunin_def_distance_preserving {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Isometry f ↔ ∀ A B : X, dist (f A) (f B) = dist A B :=
  isometry_iff_dist_eq

/-- Petrunin, Section 1E (p. 12), GE-007: an isometry (an `IsometryEquiv`) is a bijective
distance-preserving map, and conversely. -/
@[kb "petrunin2025" "Section 1E, isometry, p. 12"]
theorem petrunin_def_isometry {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) :
    (∃ e : X ≃ᵢ Y, ⇑e = f) ↔ Function.Bijective f ∧ ∀ A B : X, dist (f A) (f B) = dist A B := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.bijective, fun A B => e.dist_eq A B⟩
  · rintro ⟨hb, hd⟩
    exact ⟨⟨Equiv.ofBijective f hb, isometry_iff_dist_eq.2 hd⟩, rfl⟩

/-- Petrunin, Section 1E (p. 12), GE-007: a motion of `X` is an isometry of `X` onto itself; the
motions form a group under composition. -/
@[kb "petrunin2025" "Section 1E, motion, p. 12"]
theorem petrunin_def_motion {X : Type*} [PseudoMetricSpace X] (f g : X ≃ᵢ X) (A B : X) :
    dist (f (g A)) (f (g B)) = dist A B ∧ (g.trans f) A = f (g A) :=
  ⟨by rw [f.dist_eq, g.dist_eq], rfl⟩

/-! ## Chapters 2 and 3 -/

/-- Petrunin, Section 2D (p. 20), GE-035: `O` lies between `A` and `B` iff `O ≠ A`, `O ≠ B` and
`O` lies on the segment `[AB]`. -/
@[kb "petrunin2025" "Definition, Section 2D, between, p. 20"]
theorem petrunin_def_between {V : Type*} [AddCommGroup V] [Module ℝ V] (A O B : V) :
    Sbtw ℝ A O B ↔ O ≠ A ∧ O ≠ B ∧ O ∈ segment ℝ A B := by
  rw [Sbtw, ← mem_segment_iff_wbtw]
  tauto

/-- Petrunin, Section 2D (p. 20), GE-035: the angle `AOB` is straight (equal to `π`) iff `O` lies
between `A` and `B`. -/
@[kb "petrunin2025" "Definition, Section 2D, straight angle, p. 20"]
theorem petrunin_def_straight_angle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (A O B : P) :
    ∠ A O B = π ↔ O ≠ A ∧ O ≠ B ∧ Wbtw ℝ A O B :=
  angle_eq_pi_iff_sbtw.trans (by rw [Sbtw]; tauto)

/-- Petrunin, Section 2D (p. 21), GE-037: a triangle is degenerate if its vertices lie on one line. -/
@[kb "petrunin2025" "Definition, Section 2D, degenerate triangle, p. 21"]
theorem petrunin_def_degenerate_triangle {V P : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (A B C : P) :
    (¬ AffineIndependent ℝ ![A, B, C]) ↔
      ∃ (L : P) (v : V), ∀ X ∈ ({A, B, C} : Set P), ∃ t : ℝ, X = t • v +ᵥ L := by
  rw [affineIndependent_iff_not_collinear_set, not_not]
  exact collinear_iff_exists_forall_eq_smul_vadd _

/-- Petrunin, Section 3A (p. 24), GE-044: an angle (a real number in `(-π, π]`, here
`Real.Angle.toReal`) is positive iff `0 < θ < π`; its sign is `1`. -/
@[kb "petrunin2025" "Definition, Section 3A, positive angle, p. 24"]
theorem petrunin_def_angle_positive (θ : Real.Angle) :
    θ.sign = 1 ↔ 0 < θ.toReal ∧ θ.toReal < π := by
  rw [← Real.Angle.toReal_mem_Ioo_iff_sign_pos]
  rfl

/-- Petrunin, Section 3A (p. 24), GE-044: an angle is negative iff `θ < 0`; its sign is `-1`. -/
@[kb "petrunin2025" "Definition, Section 3A, negative angle, p. 24"]
theorem petrunin_def_angle_negative (θ : Real.Angle) : θ.sign = -1 ↔ θ.toReal < 0 :=
  (Real.Angle.toReal_neg_iff_sign_neg).symm

/-- Petrunin, Section 3A (p. 24), GE-044: the zero and the straight angle are neither positive
nor negative (sign `0`), and only they. -/
@[kb "petrunin2025" "Definition, Section 3A, neither positive nor negative, p. 24"]
theorem petrunin_def_angle_neither (θ : Real.Angle) : θ.sign = 0 ↔ θ = 0 ∨ θ = π :=
  Real.Angle.sign_eq_zero_iff

/-! ## Chapter 5: circles -/

/-- Petrunin, circle (p. 30), GE-060: the circle of radius `r` around `O` is the set of points at
distance `r` from `O`. -/
@[kb "petrunin2025" "Definition, circle, p. 30"]
theorem petrunin_def_circle {P : Type*} [PseudoMetricSpace P] (O X : P) (r : ℝ) :
    X ∈ Metric.sphere O r ↔ dist X O = r :=
  Metric.mem_sphere

/-- Petrunin, circle (p. 30), GE-060: the same for the bundled `EuclideanGeometry.Sphere`. -/
@[kb "petrunin2025" "Definition, circle (bundled), p. 30"]
theorem petrunin_def_circle_sphere {P : Type*} [MetricSpace P] (s : EuclideanGeometry.Sphere P)
    (X : P) : X ∈ s ↔ dist X s.center = s.radius :=
  EuclideanGeometry.mem_sphere

/-- Petrunin, p. 42, GE-086: a point is inside the circle if its distance to the centre is below
the radius, outside if above. -/
@[kb "petrunin2025" "Definition, inside and outside a circle, p. 42"]
theorem petrunin_def_inside_outside {P : Type*} [PseudoMetricSpace P] (O X : P) (r : ℝ) :
    (X ∈ Metric.ball O r ↔ dist X O < r) ∧ (r < dist X O ↔ X ∈ (Metric.closedBall O r)ᶜ) :=
  ⟨Metric.mem_ball, by simp⟩

/-- Petrunin, p. 42, GE-086: `[AB]` is a diameter of the circle iff it is a chord (`A`, `B` on the
circle) whose midpoint is the centre; then the centre lies on `[AB]` and `AB = 2r`. -/
@[kb "petrunin2025" "Definition, chord and diameter, p. 42"]
theorem petrunin_def_diameter {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : EuclideanGeometry.Sphere V) (A B : V) (h : s.IsDiameter A B) :
    A ∈ s ∧ B ∈ s ∧ s.center ∈ segment ℝ A B ∧ dist A B = 2 * s.radius := by
  refine ⟨h.left_mem, h.right_mem, ?_, ?_⟩
  · rw [← h.midpoint_eq_center]
    exact midpoint_mem_segment A B
  · have h1 := h.left_mem
    rw [EuclideanGeometry.mem_sphere, ← h.midpoint_eq_center, dist_left_midpoint] at h1
    simp only [norm_ofNat] at h1
    linarith

/-- Petrunin, p. 43, GE-090: a line tangent to a circle at `P` has `P` as its only common point
with the circle. -/
@[kb "petrunin2025" "Definition, tangent line, p. 43"]
theorem petrunin_def_tangent_line {P V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (s : EuclideanGeometry.Sphere P) (p : P)
    (L : AffineSubspace ℝ P) (h : s.IsTangentAt p L) : ∀ q : P, (q ∈ s ∧ q ∈ L) ↔ q = p :=
  fun _ => h.mem_and_mem_iff_eq

/-- Petrunin, p. 43, GE-090: two circles are externally tangent at `P` iff `P` is on both circles
and between their centres; they are tangent iff the distance of centres is the sum of radii. -/
@[kb "petrunin2025" "Definition, tangent circles (external), p. 43"]
theorem petrunin_def_tangent_circles_ext {P V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (s₁ s₂ : EuclideanGeometry.Sphere P) :
    s₁.IsExtTangent s₂ ↔
      dist s₁.center s₂.center = s₁.radius + s₂.radius ∧ 0 ≤ s₁.radius ∧ 0 ≤ s₂.radius :=
  EuclideanGeometry.Sphere.isExtTangent_iff_dist_center

/-- Petrunin, p. 43, GE-090: internal tangency; the distance of the centres is the difference of
the radii. -/
@[kb "petrunin2025" "Definition, tangent circles (internal), p. 43"]
theorem petrunin_def_tangent_circles_int {P V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Nontrivial V] [MetricSpace P] [NormedAddTorsor V P]
    (s₁ s₂ : EuclideanGeometry.Sphere P) :
    s₁.IsIntTangent s₂ ↔
      dist s₁.center s₂.center = s₂.radius - s₁.radius ∧ 0 ≤ s₁.radius ∧ 0 ≤ s₂.radius :=
  EuclideanGeometry.Sphere.isIntTangent_iff_dist_center

/-! ## Inversion -/

/-- Petrunin, p. 73, GE-146: for `P ≠ O` the inversion of `P` in the circle `(O, r)` (`r ≠ 0`)
lies on the half-line `[OP)` and `OP · OP' = r²`. -/
@[kb "petrunin2025" "Definition, inversion, p. 73"]
theorem petrunin_def_inversion {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (O X : P) (r : ℝ) (hr : r ≠ 0) (hX : X ≠ O) :
    (∃ t : ℝ, 0 < t ∧ inversion O r X = AffineMap.lineMap O X t) ∧
      dist O X * dist O (inversion O r X) = r ^ 2 := by
  refine ⟨⟨(r / dist X O) ^ 2, ?_, inversion_eq_lineMap O r X⟩, ?_⟩
  · have : 0 < dist X O := dist_pos.2 hX
    positivity
  · rw [dist_center_inversion]
    have : dist O X ≠ 0 := dist_ne_zero.2 hX.symm
    field_simp

/-! ## Chapter 15 -/

/-- Petrunin, Section 14 (Lemma 15.17 on p. 130), GE-253 (D127, D128): for `P ≠ O`, the polar of
`P` with respect to the circle `(O, r)` is the line of points `X` with `⟨OX, OP⟩ = r²`. -/
@[kb "petrunin2025" "Definition, polar, p. 130"]
theorem petrunin_def_polar {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (s : EuclideanGeometry.Sphere P) (X Q : P)
    (hr : s.radius ≠ 0) (hQ : Q ≠ s.center) :
    X ∈ s.polar Q ↔ ⟪X -ᵥ s.center, Q -ᵥ s.center⟫ = s.radius ^ 2 := by
  rw [EuclideanGeometry.Sphere.mem_polar_iff_inner]
  simp [hr, hQ]

/-- Petrunin, p. 130, GE-253: the polar of `Q` is the line orthogonal to the radius through the
inverse of `Q`; and the pole of a line is the inverse of the foot of the perpendicular from the
centre. -/
@[kb "petrunin2025" "Definition, pole, p. 130"]
theorem petrunin_def_pole {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (s : EuclideanGeometry.Sphere P) (Q : P)
    (L : AffineSubspace ℝ P) [Nonempty L] [L.direction.HasOrthogonalProjection] :
    s.polar Q = s.orthRadius (inversion s.center s.radius Q) ∧
      s.pole L = inversion s.center s.radius (EuclideanGeometry.orthogonalProjection L s.center) :=
  ⟨rfl, rfl⟩

/-! ## Stereographic projection -/

/-- Petrunin, p. 134, GE-261: stereographic projection from the pole `v` of the unit sphere is
inverted by the explicit formula (scaled by the convention of Mathlib), and the two maps are mutually
inverse. -/
@[kb "petrunin2025" "Definition, stereographic projection, p. 134"]
theorem petrunin_def_stereographic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : ‖v‖ = 1) :
    (∀ x : Metric.sphere (0 : E) 1, (x : E) ≠ v → stereoInvFun hv (stereoToFun v x) = x) ∧
      (∀ w : (ℝ ∙ v)ᗮ, stereoToFun v (stereoInvFun hv w) = w) ∧
      (∀ w : (ℝ ∙ v)ᗮ, (stereoInvFun hv w : E) =
        (‖(w : E)‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • (w : E) + (‖(w : E)‖ ^ 2 - 4) • v)) :=
  ⟨fun _ hx => stereo_left_inv hv hx, stereo_right_inv hv, stereoInvFun_apply hv⟩

/-! ## Chapter 18 and the algebraic appendix -/

/-- Petrunin, Section 18A (p. 146), GE-281: a complex number is a pair of reals with componentwise
sum and the product `(a + bi)(c + di) = (ac - bd) + (ad + bc)i`. -/
@[kb "petrunin2025" "Section 18A, complex numbers, p. 146"]
theorem petrunin_def_complex (a b c d : ℝ) :
    (⟨a, b⟩ : ℂ) + ⟨c, d⟩ = ⟨a + c, b + d⟩ ∧
      (⟨a, b⟩ : ℂ) * ⟨c, d⟩ = ⟨a * c - b * d, a * d + b * c⟩ ∧
      (⟨a, b⟩ : ℂ).re = a ∧ (⟨a, b⟩ : ℂ).im = b :=
  ⟨Complex.ext (by simp) (by simp), Complex.ext (by simp) (by simp), rfl, rfl⟩

/-- Petrunin, Section 18G (p. 152), GE-299: the extended complex plane is `ℂ ∪ {∞}`: every point
is `∞` or a complex number, and `∞` is not a complex number. -/
@[kb "petrunin2025" "Section 18G, extended complex plane, p. 152"]
theorem petrunin_def_extended_plane :
    (∀ w : OnePoint ℂ, w = OnePoint.infty ∨ ∃ z : ℂ, (z : OnePoint ℂ) = w) ∧
      (∀ z : ℂ, (z : OnePoint ℂ) ≠ OnePoint.infty) ∧ Function.Injective ((↑) : ℂ → OnePoint ℂ) := by
  refine ⟨fun w => ?_, fun z => OnePoint.coe_ne_infty z, OnePoint.coe_injective⟩
  induction w using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe z => exact Or.inr ⟨z, rfl⟩

/-- Petrunin, Section 18J (p. 156), GE-307: `f` is holomorphic on the open set `D` iff at each
`z ∈ D` there is `s` (the derivative `f'(z)`) with `f(z + w) = f(z) + s w + o(|w|)`. -/
@[kb "petrunin2025" "Section 18J, holomorphic function, p. 156"]
theorem petrunin_def_holomorphic (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D) :
    DifferentiableOn ℂ f D ↔
      ∀ z ∈ D, ∃ s : ℂ, (fun w : ℂ => f (z + w) - f z - w * s) =o[𝓝 0] fun w => w := by
  constructor
  · intro h z hz
    have hs := (h.differentiableAt (hD.mem_nhds hz)).hasDerivAt
    exact ⟨deriv f z, by simpa [mul_comm] using hasDerivAt_iff_isLittleO_nhds_zero.1 hs⟩
  · intro h z hz
    obtain ⟨s, hs⟩ := h z hz
    exact (HasDerivAt.differentiableAt
      (hasDerivAt_iff_isLittleO_nhds_zero.2 (by simpa using hs))).differentiableWithinAt

/-- Petrunin, p. 118 (D118), GE-230: a field automorphism of `ℝ` sends `1` to `1`, is additive and
multiplicative; and it is the identity (so `ℝ` has only the trivial automorphism). -/
@[kb "petrunin2025" "Definition, field automorphism of the reals, p. 118"]
theorem petrunin_def_field_automorphism (f : ℝ ≃+* ℝ) :
    f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧ (∀ x y, f (x * y) = f x * f y) ∧
      ∀ x, f x = x := by
  refine ⟨map_one f, map_add f, map_mul f, fun x => ?_⟩
  exact congrArg (fun g : ℝ →+* ℝ => g x) (Subsingleton.elim (f : ℝ →+* ℝ) (RingHom.id ℝ))

/-- Petrunin, p. 118 (D118), GE-230: conversely, a bijective function with `f 1 = 1`, additive and
multiplicative is a ring automorphism of `ℝ`. -/
@[kb "petrunin2025" "Definition, field automorphism of the reals (converse), p. 118"]
theorem petrunin_def_field_automorphism_of_bijective (f : ℝ → ℝ) (hb : Function.Bijective f)
    (h1 : f 1 = 1) (ha : ∀ x y, f (x + y) = f x + f y) (hm : ∀ x y, f (x * y) = f x * f y) :
    ∃ e : ℝ ≃+* ℝ, ⇑e = f :=
  ⟨RingEquiv.ofBijective
    ({ toFun := f, map_one' := h1, map_mul' := hm,
       map_zero' := by simpa using ha 0 0, map_add' := ha } : ℝ →+* ℝ) hb, rfl⟩

/-! ## Chapters 20 -/

/-- Petrunin, Section 20A (p. 165), GE-329: the solid triangle `▲ABC` is the set of points with
barycentric weights in `[0,1]`; it is the convex hull of the vertices. -/
@[kb "petrunin2025" "Section 20A, solid triangle, p. 165"]
theorem petrunin_def_solid_triangle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (T : Affine.Triangle ℝ P) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.closedInterior ↔ ∀ i, w i ∈ Set.Icc (0 : ℝ) 1 :=
  Affine.Simplex.affineCombination_mem_closedInterior_iff hw

/-- Petrunin, Section 20A (p. 165), GE-329: the solid triangle is the convex hull of the vertices
(read for vector-space-valued triangles). -/
@[kb "petrunin2025" "Section 20A, solid triangle as convex hull, p. 165"]
theorem petrunin_def_solid_triangle_hull {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Affine.Triangle ℝ V) : T.closedInterior = convexHull ℝ (Set.range T.points) :=
  (Affine.Simplex.convexHull_eq_closedInterior T).symm

/-- Petrunin, p. 177, GE-352: a set is bounded iff it lies inside a circle (closed ball, or open
ball) about any given point. -/
@[kb "petrunin2025" "Parenthetical definition, bounded set, p. 177"]
theorem petrunin_def_bounded {X : Type*} [PseudoMetricSpace X] (S : Set X) (O : X) :
    (Bornology.IsBounded S ↔ ∃ r : ℝ, S ⊆ Metric.closedBall O r) ∧
      (Bornology.IsBounded S ↔ ∃ r : ℝ, S ⊆ Metric.ball O r) :=
  ⟨Metric.isBounded_iff_subset_closedBall O, Metric.isBounded_iff_subset_ball O⟩

end UndergradKB.Geometry.Course
