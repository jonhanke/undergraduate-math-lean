import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Angle.Bisector
import Mathlib.Geometry.Euclidean.Angle.Incenter
import Mathlib.Geometry.Euclidean.Congruence
import Mathlib.Geometry.Euclidean.Similarity
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.MongePoint
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Geometry.Euclidean.Incenter.Basic
import Mathlib.Geometry.Euclidean.Projection
import UndergradKB.Common.Attr

/-! # Course layer: Petrunin chapters 5 to 9

Thin, citable statements in the book's terms (Petrunin, *Euclidean Plane and its Relatives*, 3rd ed.),
each proved by the Mathlib lemma named in the audit (`docs/coverage/geometry/checklist.md`).

Chapter 5 (perpendiculars, circles, tangents), chapter 6 (similarity, Pythagorean theorem), chapter 7
(parallel lines, angles of a triangle), chapter 8 (circumcenter, orthocenter, centroid, bisectors,
incenter), chapter 9 (inscribed angles).  Triangles are `Affine.Triangle` (nondegenerate) or three
points with a non-collinearity hypothesis; signed angles need an oriented 2-dimensional space. -/

namespace UndergradKB.Geometry.Course

open EuclideanGeometry Real
open scoped RealInnerProductSpace Affine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Chapter 5 -/

section Ch5

/-- Petrunin, definition of the perpendicular bisector (p. 37): the perpendicular bisector of `[AB]`
passes through the midpoint of `A` and `B` and has direction orthogonal to `AB`. -/
@[kb "petrunin2025" "Perpendicular bisector, p. 37"]
theorem petrunin_ch5_perp_bisector (A B : P) :
    midpoint ℝ A B ∈ AffineSubspace.perpBisector A B ∧
      (AffineSubspace.perpBisector A B).direction = (ℝ ∙ (B -ᵥ A))ᗮ :=
  ⟨AffineSubspace.midpoint_mem_perpBisector A B, AffineSubspace.direction_perpBisector A B⟩

/-- Petrunin, Theorem 5.2 (p. 37): a point `X` is equidistant from `A` and `B` iff it lies on the
perpendicular bisector of `[AB]`. -/
@[kb "petrunin2025" "Theorem 5.2, p. 37"]
theorem petrunin_5_2 {A B : P} (X : P) :
    dist A X = dist B X ↔ X ∈ AffineSubspace.perpBisector A B :=
  AffineSubspace.mem_perpBisector_iff_dist_eq'.symm

/-- Petrunin, Theorem 5.6 (p. 38): through a point `X` there is exactly one line perpendicular to a
given line `ℓ` (a line `m` through `X` with direction `ℓ.directionᗮ`); it meets `ℓ` in exactly one
point, the footpoint of `X`, which is the orthogonal projection of `X` onto `ℓ`. -/
@[kb "petrunin2025" "Theorem 5.6, p. 38"]
theorem petrunin_5_6 [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)] (ℓ : AffineSubspace ℝ P) [Nonempty ℓ]
    (hℓ : Module.finrank ℝ ℓ.direction = 1) (X : P) :
    (∃! m : AffineSubspace ℝ P, X ∈ m ∧ m.direction = ℓ.directionᗮ) ∧
    ∀ m : AffineSubspace ℝ P, X ∈ m → m.direction = ℓ.directionᗮ →
      Module.finrank ℝ m.direction = 1 ∧
      ∀ Y : P, (Y ∈ ℓ ∧ Y ∈ m) ↔ Y = ↑(EuclideanGeometry.orthogonalProjection ℓ X) := by
  refine ⟨⟨AffineSubspace.mk' X ℓ.directionᗮ,
    ⟨AffineSubspace.self_mem_mk' _ _, AffineSubspace.direction_mk' _ _⟩, ?_⟩, ?_⟩
  · rintro m ⟨hXm, hdir⟩
    refine AffineSubspace.ext_of_direction_eq (by rw [hdir, AffineSubspace.direction_mk']) ?_
    exact ⟨X, hXm, AffineSubspace.self_mem_mk' _ _⟩
  · intro m hXm hdir
    refine ⟨?_, fun Y => ?_⟩
    · have := Submodule.finrank_add_finrank_orthogonal ℓ.direction
      rw [Fact.out (p := Module.finrank ℝ V = 2)] at this
      rw [hdir]
      omega
    · rw [eq_comm, EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
      constructor
      · rintro ⟨hYℓ, hYm⟩
        refine ⟨hYℓ, ?_⟩
        rw [← hdir]
        exact AffineSubspace.vsub_mem_direction hXm hYm
      · rintro ⟨hYℓ, hY⟩
        refine ⟨hYℓ, ?_⟩
        rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hXm, hdir]
        simpa using Submodule.neg_mem _ hY

/-- Petrunin, Lemma 5.20 (p. 42): a line and a circle have at most two common points (among any three
common points two coincide). -/
@[kb "petrunin2025" "Lemma 5.20, p. 42"]
theorem petrunin_5_20 {A B : P} (S : EuclideanGeometry.Sphere P) {X Y Z : P}
    (hX : X ∈ line[ℝ, A, B]) (hY : Y ∈ line[ℝ, A, B]) (hZ : Z ∈ line[ℝ, A, B])
    (hXS : X ∈ S) (hYS : Y ∈ S) (hZS : Z ∈ S) : X = Y ∨ Y = Z ∨ X = Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hXY, hYZ, hXZ⟩ := hcon
  have hcos : EuclideanGeometry.Cospherical (S : Set P) := ⟨S.center, S.radius, fun p hp => hp⟩
  have hinj : Function.Injective ![X, Y, Z] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hind := hcos.affineIndependent (p := ![X, Y, Z]) (by
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simpa) hinj
  rw [affineIndependent_iff_not_collinear_set] at hind
  exact hind (collinear_triple_of_mem_affineSpan_pair hX hY hZ)

/-- Petrunin, Exercise 5.21 (p. 43): two distinct circles have at most two common points (a third
common point equals one of two distinct common points). -/
@[kb "petrunin2025" "Exercise 5.21, p. 43"]
theorem petrunin_5_21 [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)] {S₁ S₂ : EuclideanGeometry.Sphere P}
    (hS : S₁ ≠ S₂) {X Y Z : P} (hXY : X ≠ Y) (hX₁ : X ∈ S₁) (hY₁ : Y ∈ S₁) (hZ₁ : Z ∈ S₁)
    (hX₂ : X ∈ S₂) (hY₂ : Y ∈ S₂) (hZ₂ : Z ∈ S₂) : Z = X ∨ Z = Y :=
  EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two Fact.out hS hXY hX₁ hY₁ hZ₁
    hX₂ hY₂ hZ₂

/-- Petrunin, Lemma 5.22 (p. 43): a line `ℓ` through a point `X` of a circle with center `O` is
tangent to the circle (it meets the circle only at `X`) iff it is perpendicular to `OX`. -/
@[kb "petrunin2025" "Lemma 5.22, p. 43"]
theorem petrunin_5_22 (S : EuclideanGeometry.Sphere P) {ℓ : AffineSubspace ℝ P} {X : P}
    (hXS : X ∈ S) (hXℓ : X ∈ ℓ) :
    (∀ Y, Y ∈ S → Y ∈ ℓ → Y = X) ↔ ∀ Y ∈ ℓ, ⟪Y -ᵥ X, X -ᵥ S.center⟫ = 0 := by
  constructor
  · intro h Y hY
    have h1 : S.secondInter X (Y -ᵥ X) ∈ ℓ :=
      affineSpan_pair_le_of_mem_of_mem hXℓ hY (S.secondInter_vsub_mem_affineSpan X Y)
    have h2 := h _ ((EuclideanGeometry.Sphere.secondInter_mem _).2 hXS) h1
    exact EuclideanGeometry.Sphere.secondInter_eq_self_iff.1 h2
  · intro h
    have ht : S.IsTangentAt X ℓ :=
      ⟨hXS, hXℓ, fun Y hY => EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left.2 (h Y hY)⟩
    exact fun Y hYS hYℓ => ht.eq_of_mem_of_mem hYS hYℓ

end Ch5

/-! ## Chapter 6: similar triangles and the Pythagorean theorem -/

section Ch6

/-- Petrunin, definition of similar triangles (p. 44): `A'B'C'` is similar to `ABC` iff all sides scale
by a common factor `k > 0` (angles then agree, and the relation is an equivalence relation; the case
`k = 1` is congruence). -/
@[kb "petrunin2025" "Definition, Section 6, p. 44"]
theorem petrunin_6_similar {A B C A' B' C' : P} :
    (Similar ![A, B, C] ![A', B', C'] ↔
      ∃ k : ℝ, 0 < k ∧ dist A B = k * dist A' B' ∧ dist B C = k * dist B' C' ∧
        dist C A = k * dist C' A') ∧
    (Similar ![A, B, C] ![A', B', C'] →
      ∠ A B C = ∠ A' B' C' ∧ ∠ B C A = ∠ B' C' A' ∧ ∠ C A B = ∠ C' A' B') ∧
    Equivalence (fun t t' : Fin 3 → P => Similar t t') ∧
    (Congruent ![A, B, C] ![A', B', C'] → Similar ![A, B, C] ![A', B', C']) := by
  refine ⟨?_, fun h => h.angle_eq_all, ⟨Similar.refl, Similar.symm, Similar.trans⟩,
    Congruent.similar⟩
  rw [similar_iff_exists_pos_dist_eq]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, by simpa using h 0 1, by simpa using h 1 2, by simpa using h 2 0⟩
  · rintro ⟨k, hk, h1, h2, h3⟩
    have h1' : dist B A = k * dist B' A' := by rw [dist_comm B A, dist_comm B' A']; exact h1
    have h2' : dist C B = k * dist C' B' := by rw [dist_comm C B, dist_comm C' B']; exact h2
    have h3' : dist A C = k * dist A' C' := by rw [dist_comm A C, dist_comm A' C']; exact h3
    refine ⟨k, hk, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h1', h2', h3']

/-- Petrunin, Theorem 6.2 (p. 45): triangles are similar under (SAS) one equal angle between
proportional sides, (AA) two equal angles in a nondegenerate triangle, and (SSS) proportional sides.
Angles are unsigned (`∠`). -/
@[kb "petrunin2025" "Theorem 6.2, p. 45"]
theorem petrunin_6_2 {A B C A' B' C' : P} :
    (¬Collinear ℝ ({A, B, C} : Set P) → ¬Collinear ℝ ({A', B', C'} : Set P) →
      ∠ A B C = ∠ A' B' C' → dist A B * dist B' C' = dist B C * dist A' B' →
        Similar ![A, B, C] ![A', B', C']) ∧
    (¬Collinear ℝ ({A, B, C} : Set P) → ∠ A B C = ∠ A' B' C' → ∠ B C A = ∠ B' C' A' →
        Similar ![A, B, C] ![A', B', C']) ∧
    (A ≠ B → A' ≠ B' → dist A B * dist B' C' = dist B C * dist A' B' →
      dist A B * dist C' A' = dist C A * dist A' B' → Similar ![A, B, C] ![A', B', C']) :=
  ⟨fun h h' hang hd => EuclideanGeometry.similar_of_side_angle_side h h' hang hd,
    fun h h₁ h₂ => EuclideanGeometry.similar_of_angle_angle h h₁ h₂,
    fun h h' h₁ h₂ => similar_of_dist_mul_eq_dist_mul_eq (dist_ne_zero.2 h) (dist_ne_zero.2 h')
      h₁ h₂⟩

/-- Petrunin, Pythagorean theorem 6.6 (p. 46): if the angle at `C` is right then
`AC² + BC² = AB²`. -/
@[kb "petrunin2025" "Theorem 6.6, p. 46"]
theorem petrunin_6_6 {A B C : P} (h : ∠ A C B = π / 2) :
    dist A C ^ 2 + dist B C ^ 2 = dist A B ^ 2 := by
  have := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A C B).2 h
  nlinarith [this]

/-- Petrunin, Exercise 6.8 (p. 47): converse of the Pythagorean theorem: `AC² + BC² = AB²` implies
that the angle at `C` is right. -/
@[kb "petrunin2025" "Exercise 6.8, p. 47"]
theorem petrunin_6_8 {A B C : P} (h : dist A C ^ 2 + dist B C ^ 2 = dist A B ^ 2) :
    ∠ A C B = π / 2 :=
  (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A C B).1 (by nlinarith [h])

end Ch6

/-! ## Chapter 7: parallel lines -/

section Ch7

/-- Petrunin, Corollary 7.3 (p. 50): parallelism of lines is transitive, hence an equivalence
relation (Mathlib's `AffineSubspace.Parallel`, in any dimension). -/
@[kb "petrunin2025" "Corollary 7.3, p. 50"]
theorem petrunin_7_3 : Equivalence (fun ℓ m : AffineSubspace ℝ P => ℓ ∥ m) :=
  AffineSubspace.Parallel.equivalence

/-- Petrunin, definition of reflection across a point (p. 51): `O` is the midpoint of `XX'` iff `X'`
is the reflection of `X` in `O`; `O` reflects to itself. -/
@[kb "petrunin2025" "Reflection across a point, p. 51"]
theorem petrunin_7a_point_reflection (X X' O : P) :
    midpoint ℝ X X' = O ↔ X' = AffineEquiv.pointReflection ℝ O X :=
  ⟨fun h => (midpoint_eq_iff.1 h).symm, fun h => midpoint_eq_iff.2 h.symm⟩

end Ch7

section Ch7Plane

variable [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]

/-- Petrunin, definition of parallel lines (p. 49): two lines of the plane are parallel iff they do not
meet or coincide.  (Mathlib's `AffineSubspace.Parallel` means that one is a translate of the other;
for lines of a plane the two notions agree.) -/
@[kb "petrunin2025" "Definition, Section 7, p. 49"]
theorem petrunin_7_parallel_def {ℓ m : AffineSubspace ℝ P} (hℓ : Module.finrank ℝ ℓ.direction = 1)
    (hm : Module.finrank ℝ m.direction = 1) :
    ℓ ∥ m ↔ (ℓ = m ∨ Disjoint (ℓ : Set P) (m : Set P)) := by
  constructor
  · intro h
    by_cases hne : ((ℓ : Set P) ∩ m).Nonempty
    · exact Or.inl (AffineSubspace.ext_of_direction_eq h.direction_eq hne)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne))
  · rintro (rfl | hd)
    · exact AffineSubspace.Parallel.refl _
    · have hℓbot : ℓ ≠ ⊥ := fun h => by rw [h, AffineSubspace.direction_bot] at hℓ; simp at hℓ
      have hmbot : m ≠ ⊥ := fun h => by rw [h, AffineSubspace.direction_bot] at hm; simp at hm
      by_contra hnp
      have hdir : ℓ.direction ≠ m.direction := fun hdeq =>
        hnp (AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot.2
          ⟨hdeq, ⟨fun h => absurd h hℓbot, fun h => absurd h hmbot⟩⟩)
      have hinf : Module.finrank ℝ ↥(ℓ.direction ⊓ m.direction) = 0 := by
        have hle : Module.finrank ℝ ↥(ℓ.direction ⊓ m.direction) ≤ 1 :=
          hℓ ▸ Submodule.finrank_mono inf_le_left
        by_contra hne
        have h1 : Module.finrank ℝ ↥(ℓ.direction ⊓ m.direction) = 1 := by omega
        have e1 : ℓ.direction ⊓ m.direction = ℓ.direction :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, hℓ])
        have e2 : ℓ.direction ⊓ m.direction = m.direction :=
          Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, hm])
        exact hdir (e1.symm.trans e2)
      have hsup : ℓ.direction ⊔ m.direction = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have := Submodule.finrank_sup_add_finrank_inf_eq ℓ.direction m.direction
        rw [Fact.out (p := Module.finrank ℝ V = 2)]
        omega
      obtain ⟨p, hp⟩ := (AffineSubspace.nonempty_iff_ne_bot ℓ).2 hℓbot
      obtain ⟨q, hq⟩ := (AffineSubspace.nonempty_iff_ne_bot m).2 hmbot
      have hv : q -ᵥ p ∈ ℓ.direction ⊔ m.direction := by rw [hsup]; trivial
      obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hv
      have h1 : u +ᵥ p ∈ ℓ := AffineSubspace.vadd_mem_of_mem_direction hu hp
      have h2 : u +ᵥ p ∈ m := by
        have : u +ᵥ p = (-w) +ᵥ q := by
          rw [← vsub_vadd q p, ← huw, vadd_vadd]
          congr 1
          abel
        rw [this]
        exact AffineSubspace.vadd_mem_of_mem_direction (neg_mem hw) hq
      exact Set.disjoint_left.1 hd h1 h2

end Ch7Plane

section Ch7Oriented

variable [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- Petrunin, Theorem 7.13 (p. 53): the signed angles of a triangle sum to `π` (mod `2π`). -/
@[kb "petrunin2025" "Theorem 7.13, p. 53"]
theorem petrunin_7_13 {A B C : P} (hBA : B ≠ A) (hCB : C ≠ B) (hAC : A ≠ C) :
    ∡ A B C + ∡ B C A + ∡ C A B = π :=
  EuclideanGeometry.oangle_add_oangle_add_oangle_eq_pi hBA hCB hAC

end Ch7Oriented

/-- Petrunin, Classroom exercise 7.14 (p. 54): the (unsigned) angles of a triangle sum to `π`. -/
@[kb "petrunin2025" "Classroom exercise 7.14, p. 54"]
theorem petrunin_7_14 {A B C : P} (hBA : B ≠ A) :
    ∠ A B C + ∠ B C A + ∠ C A B = π :=
  EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hBA

/-! ## Chapter 8: notable points of a triangle -/

section Ch8

variable [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)]

/-- In the plane the affine span of a (nondegenerate) triangle is everything. -/
theorem triangle_affineSpan_eq_top (T : Affine.Triangle ℝ P) :
    affineSpan ℝ (Set.range T.points) = ⊤ := by
  rw [T.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp [Fact.out (p := Module.finrank ℝ V = 2)]

/-- Petrunin, Theorem 8.1 (p. 58): the perpendicular bisectors of the sides of a nondegenerate
triangle meet in exactly one point, the circumcenter. -/
@[kb "petrunin2025" "Theorem 8.1, p. 58"]
theorem petrunin_8_1 (T : Affine.Triangle ℝ P) :
    (T.circumcenter ∈ AffineSubspace.perpBisector (T.points 0) (T.points 1) ∧
      T.circumcenter ∈ AffineSubspace.perpBisector (T.points 1) (T.points 2) ∧
      T.circumcenter ∈ AffineSubspace.perpBisector (T.points 2) (T.points 0)) ∧
    ∀ O : P, (O ∈ AffineSubspace.perpBisector (T.points 0) (T.points 1) ∧
      O ∈ AffineSubspace.perpBisector (T.points 1) (T.points 2) ∧
      O ∈ AffineSubspace.perpBisector (T.points 2) (T.points 0)) → O = T.circumcenter := by
  refine ⟨?_, ?_⟩
  · simp only [AffineSubspace.mem_perpBisector_iff_dist_eq', T.dist_circumcenter_eq_circumradius]
    simp
  · rintro O ⟨h1, h2, -⟩
    simp only [AffineSubspace.mem_perpBisector_iff_dist_eq'] at h1 h2
    refine T.eq_circumcenter_of_dist_eq (r := dist (T.points 0) O)
      (by rw [triangle_affineSpan_eq_top]; trivial) fun i => ?_
    fin_cases i
    · rfl
    · exact h1.symm
    · exact h2.symm.trans h1.symm

/-- Petrunin, Exercise 8.2 (p. 59): a nondegenerate triangle has a unique circle through its three
vertices (its circumcircle). -/
@[kb "petrunin2025" "Exercise 8.2, p. 59"]
theorem petrunin_8_2 (T : Affine.Triangle ℝ P) :
    ∃! S : EuclideanGeometry.Sphere P, ∀ i, T.points i ∈ S := by
  refine ⟨T.circumsphere, fun i => T.mem_circumsphere i, ?_⟩
  intro S hS
  have hc : S.center = T.circumcenter :=
    T.eq_circumcenter_of_dist_eq (r := S.radius) (by rw [triangle_affineSpan_eq_top]; trivial)
      fun i => EuclideanGeometry.mem_sphere.1 (hS i)
  have hr : S.radius = T.circumradius := by
    rw [← EuclideanGeometry.mem_sphere.1 (hS 0), hc, T.dist_circumcenter_eq_circumradius]
  exact EuclideanGeometry.Sphere.ext hc hr

omit [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)] in
/-- Petrunin, Theorem 8.3 (p. 59): the altitudes of a nondegenerate triangle meet in one point, the
orthocenter (a common point of two altitudes is the orthocenter). -/
@[kb "petrunin2025" "Theorem 8.3, p. 59"]
theorem petrunin_8_3 (T : Affine.Triangle ℝ P) :
    (∀ i, T.orthocenter ∈ T.altitude i) ∧
      ∀ (H : P) (i j : Fin 3), i ≠ j → H ∈ T.altitude i → H ∈ T.altitude j → H = T.orthocenter :=
  ⟨fun _ => T.orthocenter_mem_altitude, fun _ _ _ hij hi hj =>
    Affine.Triangle.eq_orthocenter_of_forall_mem_altitude hij hi hj⟩

omit [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)] in
/-- Petrunin, Theorem 8.6 (p. 60): the medians of a nondegenerate triangle (lines from a vertex to the
midpoint of the opposite side) meet at the centroid, which divides each median in the ratio `2 : 1`
(counted from the vertex). -/
@[kb "petrunin2025" "Theorem 8.6, p. 60"]
theorem petrunin_8_6 (T : Affine.Triangle ℝ P) :
    (T.faceOppositeCentroid 0 = midpoint ℝ (T.points 1) (T.points 2) ∧
      T.faceOppositeCentroid 1 = midpoint ℝ (T.points 0) (T.points 2) ∧
      T.faceOppositeCentroid 2 = midpoint ℝ (T.points 0) (T.points 1)) ∧
    (∀ i, T.centroid ∈ line[ℝ, T.points i, T.faceOppositeCentroid i]) ∧
    ∀ i, dist (T.points i) T.centroid = 2 * dist T.centroid (T.faceOppositeCentroid i) := by
  refine ⟨⟨?_, ?_, ?_⟩, fun i => T.centroid_mem_median i, fun i => ?_⟩
  · apply vsub_left_cancel (p := T.points 0)
    rw [T.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, midpoint_vsub]
    simp [Fin.sum_univ_three, smul_add]
  · apply vsub_left_cancel (p := T.points 1)
    rw [T.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, midpoint_vsub]
    simp [Fin.sum_univ_three, smul_add]
  · apply vsub_left_cancel (p := T.points 2)
    rw [T.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, midpoint_vsub]
    simp [Fin.sum_univ_three, smul_add]
  · rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, T.point_vsub_centroid_eq_smul_vsub, norm_smul]
    simp

omit [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 2)] in
/-- Petrunin, Theorem 8.16 (p. 63): the angle bisectors of a nondegenerate triangle meet at the
incenter, which is the center of the incircle: the incenter bisects every angle of the triangle, the
incircle touches the three sides, and the incenter is at the inradius from each side. -/
@[kb "petrunin2025" "Theorem 8.16, p. 63"]
theorem petrunin_8_16 (T : Affine.Triangle ℝ P) :
    (∀ {i j k : Fin 3}, i ≠ j → i ≠ k → j ≠ k →
      ∠ (T.points j) (T.points i) T.incenter = ∠ (T.points j) (T.points i) (T.points k) / 2) ∧
    (∀ i, T.insphere.IsTangentAt (T.touchpoint ∅ i)
      (affineSpan ℝ (Set.range (T.faceOpposite i).points))) ∧
    (∀ i, dist T.incenter (T.touchpoint ∅ i) = T.inradius) :=
  ⟨fun hij hik hjk => T.angle_incenter_eq_angle_div_two hij hik hjk,
    fun i => T.isTangentAt_insphere_touchpoint i, fun i => T.dist_incenter i⟩

end Ch8

section Ch8Oriented

variable [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- Petrunin, Proposition 8.15 (p. 62): for a nondegenerate triangle `ABC`, a point `X` is equidistant
from the lines `(BA)` and `(BC)` iff it lies on the bisector or the external bisector of the angle
`ABC`, i.e. `2·∡ABX ≡ 2·∡XBC`. -/
@[kb "petrunin2025" "Proposition 8.15, p. 62"]
theorem petrunin_8_15 {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) (X : P) :
    Metric.infDist X (line[ℝ, B, A] : Set P) = Metric.infDist X (line[ℝ, B, C] : Set P) ↔
      (2 : ℤ) • ∡ A B X = (2 : ℤ) • ∡ X B C := by
  have hind : AffineIndependent ℝ ![B, A, C] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hc; apply h
    have e : ({B, A, C} : Set P) = {A, B, C} := Set.insert_comm _ _ _
    rwa [e] at hc
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    ← EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  exact EuclideanGeometry.dist_orthogonalProjection_line_eq_iff_two_zsmul_oangle_eq hind

end Ch8Oriented

/-! ## Chapter 9: inscribed angles -/

section Ch9

variable [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- Petrunin, Theorem 9.2, "only if" part (p. 66): if `X`, `Y`, `Z` lie on a circle with center `O`
(`Z ≠ X`, `Z ≠ Y`) then `2·∡XZY ≡ ∡XOY`. -/
@[kb "petrunin2025" "Theorem 9.2, only if, p. 66"]
theorem petrunin_9_2 {S : EuclideanGeometry.Sphere P} {X Y Z : P} (hX : X ∈ S) (hZ : Z ∈ S)
    (hY : Y ∈ S) (hZX : Z ≠ X) (hZY : Z ≠ Y) :
    ∡ X S.center Y = (2 : ℤ) • ∡ X Z Y :=
  EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle hX hZ hY hZX hZY

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
/-- Petrunin, Corollary 9.8, Thales' theorem (p. 67): if `[AB]` is a diameter of a circle `Γ`, then the
angle `ACB` is right iff `C ∈ Γ`. -/
@[kb "petrunin2025" "Corollary 9.8, p. 67"]
theorem petrunin_9_8 {Γ : EuclideanGeometry.Sphere P} {A B : P} (hd : Γ.IsDiameter A B) (C : P) :
    ∠ A C B = π / 2 ↔ C ∈ Γ :=
  EuclideanGeometry.Sphere.angle_eq_pi_div_two_iff_mem_sphere_of_isDiameter hd

/-- Petrunin, Corollary 9.14 (p. 68): a nondegenerate quadrangle `ABCD` is inscribed in a circle iff
`2·∡ABC ≡ 2·∡ADC` (here nondegenerate means: `ABC` is a triangle and `D` differs from `A` and `C`;
the statement is the form in which this is used). -/
@[kb "petrunin2025" "Corollary 9.14, p. 68"]
theorem petrunin_9_14 {A B C D : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) (hDA : D ≠ A)
    (hDC : D ≠ C) :
    EuclideanGeometry.Cospherical ({A, B, C, D} : Set P) ↔
      (2 : ℤ) • ∡ A B C = (2 : ℤ) • ∡ A D C := by
  have hBA : B ≠ A := (ne₁₂_of_not_collinear h).symm
  have hBC : B ≠ C := ne₂₃_of_not_collinear h
  have e : ({A, B, C, D} : Set P) = {A, B, D, C} := by
    ext; simp; tauto
  rw [e]
  constructor
  · intro hc
    exact hc.two_zsmul_oangle_eq hBA hBC hDA hDC
  · intro h2
    exact EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear h2 h

end Ch9

/-- Petrunin, power of a point (p. 67, Exercise 9.3(c)): if `X, X'` lie on a circle `Γ` with center
`O` and radius `r`, and `Q` lies on the line `XX'`, then `QX·QX' = |OQ² - r²|`. -/
@[kb "petrunin2025" "Exercise 9.3(c), p. 67"]
theorem petrunin_9_3_c {Γ : EuclideanGeometry.Sphere P} {X X' Q : P} (hQ : Q ∈ line[ℝ, X, X'])
    (hX : X ∈ Γ) (hX' : X' ∈ Γ) :
    dist Q X * dist Q X' = |dist Q Γ.center ^ 2 - Γ.radius ^ 2| :=
  EuclideanGeometry.Sphere.mul_dist_eq_abs_power hQ hX hX'

end UndergradKB.Geometry.Course
