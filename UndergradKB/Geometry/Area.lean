import Mathlib.Geometry.Euclidean.Volume.Triangle
import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Segment
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import UndergradKB.Common.Attr

/-! # Area (Petrunin, chapter 20)

Model of the book's area function on the Euclidean plane `EuclideanSpace ℝ (Fin 2)`: the area of a
set is `(volume S).toReal` for the Lebesgue measure.  Bridging definitions: solid triangles,
elementary sets, polygonal sets, degenerate polygonal sets, congruent sets (Sections 20A, 20B,
Definition 20.2).  The area conditions of Section 20C (normalization, invariance, monotonicity,
inclusion-exclusion) are proved for polygonal sets (Claim 20.7), together with the vanishing of
degenerate sets (Proposition 20.8, Corollary 20.9), the area of a triangle (Theorem 20.14, Claim
20.22), the Pythagorean theorem and the area of the unit disc (Exercise 20.27). -/

namespace UndergradKB.Geometry

open MeasureTheory

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ### Bridging definitions -/

/-- The solid triangle on three points: the convex hull of the vertices (for a nondegenerate
triangle this is the triangle together with its interior). -/
def solidTriangle (A B C : E2) : Set E2 := convexHull ℝ {A, B, C}

/-- Elementary sets: a point, a segment, or a solid triangle. -/
def IsElementary (S : Set E2) : Prop :=
  (∃ A, S = {A}) ∨ (∃ A B, S = segment ℝ A B) ∨ ∃ A B C, S = solidTriangle A B C

/-- Degenerate elementary sets: points and segments. -/
def IsDegenerateElementary (S : Set E2) : Prop :=
  (∃ A, S = {A}) ∨ ∃ A B, S = segment ℝ A B

/-- Polygonal sets: finite unions of elementary sets (the empty union gives `∅`). -/
def IsPolygonal (S : Set E2) : Prop :=
  ∃ F : Set (Set E2), F.Finite ∧ (∀ T ∈ F, IsElementary T) ∧ S = ⋃₀ F

/-- Degenerate polygonal sets: finite unions of points and segments. -/
def IsDegeneratePolygonal (S : Set E2) : Prop :=
  ∃ F : Set (Set E2), F.Finite ∧ (∀ T ∈ F, IsDegenerateElementary T) ∧ S = ⋃₀ F

/-- The area of a set: the real number `(volume S).toReal` (Lebesgue measure). -/
noncomputable def area (S : Set E2) : ℝ := (volume S).toReal

/-- Congruent sets: one is the image of the other under a motion of the plane. -/
def SetCongruent (S T : Set E2) : Prop := ∃ f : E2 ≃ᵢ E2, f '' S = T

/-- The unit square `[0,1]²` in the plane. -/
def unitSquare : Set E2 := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

theorem IsDegenerateElementary.isElementary {S : Set E2} (h : IsDegenerateElementary S) :
    IsElementary S := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem IsDegeneratePolygonal.isPolygonal {S : Set E2} (h : IsDegeneratePolygonal S) :
    IsPolygonal S := by
  obtain ⟨F, hF, hT, rfl⟩ := h
  exact ⟨F, hF, fun T hT' => (hT T hT').isElementary, rfl⟩

theorem isPolygonal_empty : IsPolygonal (∅ : Set E2) :=
  ⟨∅, Set.finite_empty, by simp, by simp⟩

theorem IsElementary.isCompact {S : Set E2} (h : IsElementary S) : IsCompact S := by
  rcases h with ⟨A, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, C, rfl⟩
  · exact isCompact_singleton
  · rw [← convexHull_pair]; exact (Set.toFinite _).isCompact_convexHull ℝ
  · exact (Set.toFinite _).isCompact_convexHull ℝ

theorem IsPolygonal.isCompact {S : Set E2} (h : IsPolygonal S) : IsCompact S := by
  obtain ⟨F, hF, hT, rfl⟩ := h
  exact hF.isCompact_sUnion fun T hT' => (hT T hT').isCompact

theorem IsPolygonal.measurableSet {S : Set E2} (h : IsPolygonal S) : MeasurableSet S :=
  h.isCompact.isClosed.measurableSet

theorem IsPolygonal.isBounded {S : Set E2} (h : IsPolygonal S) : Bornology.IsBounded S :=
  h.isCompact.isBounded

theorem IsPolygonal.measure_lt_top {S : Set E2} (h : IsPolygonal S) : volume S < ⊤ :=
  h.isCompact.measure_lt_top

/-- Claim 20.6, union part: the union of two polygonal sets is polygonal. -/
theorem IsPolygonal.union {S T : Set E2} (hS : IsPolygonal S) (hT : IsPolygonal T) :
    IsPolygonal (S ∪ T) := by
  obtain ⟨F, hF, hFe, rfl⟩ := hS
  obtain ⟨G, hG, hGe, rfl⟩ := hT
  refine ⟨F ∪ G, hF.union hG, ?_, by rw [Set.sUnion_union]⟩
  rintro T (hT | hT)
  exacts [hFe T hT, hGe T hT]

/-- Finite unions of polygonal sets are polygonal. -/
theorem IsPolygonal.sUnion {𝓕 : Set (Set E2)} (h𝓕 : 𝓕.Finite) (h : ∀ S ∈ 𝓕, IsPolygonal S) :
    IsPolygonal (⋃₀ 𝓕) := by
  classical
  induction 𝓕, h𝓕 using Set.Finite.induction_on with
  | empty => simpa using isPolygonal_empty
  | insert hn hf ih =>
    rw [Set.sUnion_insert]
    exact (h _ (Set.mem_insert _ _)).union (ih fun S hS => h S (Set.mem_insert_of_mem _ hS))

/-! ### Null sets: points, segments, degenerate polygonal sets -/

theorem measure_segment_eq_zero (A B : E2) : volume (segment ℝ A B) = 0 := by
  have hne : (line[ℝ, A, B] : Set E2) ≠ Set.univ := by
    intro h
    have h1 : line[ℝ, A, B] = ⊤ := by rw [← AffineSubspace.coe_eq_univ_iff]; exact h
    have h2 := congrArg (fun s : AffineSubspace ℝ E2 => Module.finrank ℝ s.direction) h1
    rw [AffineSubspace.direction_top, direction_affineSpan, finrank_top,
      finrank_euclideanSpace_fin] at h2
    have h3 := finrank_vectorSpan_range_le ℝ ![A, B] (n := 1) (by simp)
    have h4 : Set.range ![A, B] = {A, B} := by ext x; simp [or_comm, eq_comm]
    rw [h4] at h3
    omega
  refine measure_mono_null ?_ (Measure.addHaar_affineSubspace volume line[ℝ, A, B] ?_)
  · intro x hx
    rw [← convexHull_pair] at hx
    exact convexHull_subset_affineSpan _ hx
  · intro h; exact hne (by rw [h]; rfl)

/-- Proposition 20.8: points and segments have zero area. -/
theorem IsDegenerateElementary.area_eq_zero {S : Set E2} (h : IsDegenerateElementary S) :
    area S = 0 := by
  unfold area
  rcases h with ⟨A, rfl⟩ | ⟨A, B, rfl⟩
  · simp
  · simp [measure_segment_eq_zero]

/-- Corollary 20.9: a degenerate polygonal set has zero area. -/
theorem IsDegeneratePolygonal.area_eq_zero {S : Set E2} (h : IsDegeneratePolygonal S) :
    area S = 0 := by
  obtain ⟨F, hF, hT, rfl⟩ := h
  unfold area
  have : volume (⋃₀ F) = 0 := by
    rw [measure_sUnion_null_iff hF.countable]
    intro T hT'
    have := (hT T hT').area_eq_zero
    unfold area at this
    rcases hT T hT' with ⟨A, rfl⟩ | ⟨A, B, rfl⟩
    · simp
    · exact measure_segment_eq_zero A B
  simp [this]

/-! ### Claim 20.7: the area function satisfies the book's conditions -/

theorem measure_unitSquare : volume unitSquare = 1 := by
  have : unitSquare = (WithLp.ofLp ⁻¹' Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp [unitSquare, Pi.le_def, Fin.forall_fin_two]
    tauto
  rw [this, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet]
  simp [Real.volume_Icc_pi]

/-- Claim 20.7 (a): normalization, the unit square has area `1`. -/
@[kb "petrunin2025" "Claim 20.7, p. 168"]
theorem area_unitSquare : area unitSquare = 1 := by
  simp [area, measure_unitSquare]

/-- Claim 20.7: invariance of area under motions of the plane (for every set). -/
@[kb "petrunin2025" "Claim 20.7, p. 168"]
theorem area_image_isometryEquiv (f : E2 ≃ᵢ E2) (S : Set E2) : area (f '' S) = area S := by
  unfold area
  have h := Isometry.euclideanHausdorffMeasure_image (d := 2) f.isometry S
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
  rw [h]

/-- Claim 20.7: monotonicity of area on polygonal sets. -/
@[kb "petrunin2025" "Claim 20.7, p. 168"]
theorem area_mono {S T : Set E2} (hT : IsPolygonal T) (hST : S ⊆ T) : area S ≤ area T :=
  ENNReal.toReal_mono hT.measure_lt_top.ne (measure_mono hST)

/-- Claim 20.7: inclusion-exclusion, `area (S ∪ T) + area (S ∩ T) = area S + area T`, for
polygonal sets. -/
@[kb "petrunin2025" "Claim 20.7, p. 168"]
theorem area_union_add_area_inter {S T : Set E2} (hS : IsPolygonal S) (hT : IsPolygonal T) :
    area (S ∪ T) + area (S ∩ T) = area S + area T := by
  unfold area
  have h := measure_union_add_inter (μ := volume) S hT.measurableSet
  have h1 : volume (S ∪ T) ≠ ⊤ := (hS.union hT).measure_lt_top.ne
  have h2 : volume (S ∩ T) ≠ ⊤ := ((measure_mono Set.inter_subset_left).trans_lt
    hS.measure_lt_top).ne
  rw [← ENNReal.toReal_add h1 h2, h, ENNReal.toReal_add hS.measure_lt_top.ne hT.measure_lt_top.ne]

/-- Claim 20.7 (existence of an area function): `area` is a function on polygonal sets that is
normalized on the unit square, invariant under motions, monotone, and satisfies inclusion-exclusion;
it also vanishes on degenerate polygonal sets. -/
@[kb "petrunin2025" "Claim 20.7, p. 168"]
theorem exists_area_function :
    ∃ a : Set E2 → ℝ, a unitSquare = 1 ∧ (∀ (f : E2 ≃ᵢ E2) S, a (f '' S) = a S) ∧
      (∀ S T, IsPolygonal T → S ⊆ T → a S ≤ a T) ∧
      (∀ S T, IsPolygonal S → IsPolygonal T → a (S ∪ T) + a (S ∩ T) = a S + a T) ∧
      (∀ S, IsDegeneratePolygonal S → a S = 0) :=
  ⟨area, area_unitSquare, area_image_isometryEquiv, fun _ _ hT h => area_mono hT h,
    fun _ _ hS hT => area_union_add_area_inter hS hT, fun _ h => h.area_eq_zero⟩

/-! ### Congruent sets -/

theorem SetCongruent.refl (S : Set E2) : SetCongruent S S := ⟨IsometryEquiv.refl _, Set.image_id S⟩

theorem SetCongruent.symm {S T : Set E2} (h : SetCongruent S T) : SetCongruent T S := by
  obtain ⟨f, rfl⟩ := h
  exact ⟨f.symm, by ext x; simp⟩

theorem SetCongruent.trans {S T U : Set E2} (h : SetCongruent S T) (h' : SetCongruent T U) :
    SetCongruent S U := by
  obtain ⟨f, rfl⟩ := h
  obtain ⟨g, rfl⟩ := h'
  exact ⟨f.trans g, by ext x; simp⟩

/-- Definition 20.2 and Claim 20.7: congruent sets have equal area. -/
@[kb "petrunin2025" "Definition 20.2, p. 166"]
theorem SetCongruent.area_eq {S T : Set E2} (h : SetCongruent S T) : area S = area T := by
  obtain ⟨f, rfl⟩ := h
  exact (area_image_isometryEquiv f S).symm

/-! ### Exercise 20.27: the area of the disc -/

/-- The closed disc of radius `r` has area `π r²`. -/
theorem area_closedBall (x : E2) {r : ℝ} (hr : 0 ≤ r) :
    area (Metric.closedBall x r) = Real.pi * r ^ 2 := by
  unfold area
  rw [EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin]
  have : Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1) = 1 := by
    have h : (((2 : ℕ) : ℝ) / 2 + 1) = ((1 : ℕ) : ℝ) + 1 := by norm_num
    rw [h, Real.Gamma_nat_eq_factorial]; simp
  rw [this]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity)]
  simp [Real.sq_sqrt Real.pi_pos.le]
  ring

/-- Exercise 20.27: the closed unit disc has area `π`. (In Mathlib `π` is defined analytically;
the book's quadrability of the disc is replaced by Lebesgue measurability.) -/
@[kb "petrunin2025" "Exercise 20.27, p. 177"]
theorem area_closedBall_one (x : E2) : area (Metric.closedBall x 1) = Real.pi := by
  simpa using area_closedBall x zero_le_one

/-! ### Theorem 20.14 and Claim 20.22: area of a triangle -/

open EuclideanGeometry in
theorem convexHull_range_points_eq (t : Affine.Triangle ℝ E2) :
    convexHull ℝ (Set.range t.points) = solidTriangle (t.points 0) (t.points 1) (t.points 2) := by
  unfold solidTriangle
  congr 1
  ext x
  simp [Fin.exists_fin_succ, eq_comm]

/-- The area of the solid triangle of a nondegenerate triangle equals Mathlib's
`Affine.Simplex.volume`. -/
theorem area_solidTriangle_eq_volume (t : Affine.Triangle ℝ E2) :
    area (solidTriangle (t.points 0) (t.points 1) (t.points 2)) = t.volume := by
  rw [← convexHull_range_points_eq, Affine.Simplex.convexHull_eq_closedInterior,
    t.volume_eq_volume_real_closedInterior (by simp)]
  rfl

/-- Theorem 20.14: the area of a solid triangle is half of a side times the corresponding height
(the distance from the opposite vertex to the foot of its altitude, Mathlib's `height`). -/
@[kb "petrunin2025" "Theorem 20.14, p. 172"]
theorem area_solidTriangle (t : Affine.Triangle ℝ E2) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    area (solidTriangle (t.points 0) (t.points 1) (t.points 2)) =
      2⁻¹ * t.height i₁ * dist (t.points i₂) (t.points i₃) := by
  rw [area_solidTriangle_eq_volume, t.volume_eq_height_mul h₁₂ h₁₃ h₂₃]

/-- Area of a solid triangle as `½ a b sin C`. -/
theorem area_solidTriangle_eq_mul_sin (t : Affine.Triangle ℝ E2) :
    area (solidTriangle (t.points 0) (t.points 1) (t.points 2)) =
      2⁻¹ * dist (t.points 0) (t.points 1) * dist (t.points 1) (t.points 2) *
        Real.sin (EuclideanGeometry.angle (t.points 0) (t.points 1) (t.points 2)) := by
  rw [area_solidTriangle_eq_volume, t.volume_eq_mul_sin (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)]

/-- Claim 20.22: two triangles with equal altitudes (from the vertices `0`) have areas in the ratio
of the opposite sides. -/
@[kb "petrunin2025" "Claim 20.22, p. 174"]
theorem area_ratio_of_height_eq (t t' : Affine.Triangle ℝ E2) (h : t.height 0 = t'.height 0) :
    area (solidTriangle (t.points 0) (t.points 1) (t.points 2)) /
        area (solidTriangle (t'.points 0) (t'.points 1) (t'.points 2)) =
      dist (t.points 1) (t.points 2) / dist (t'.points 1) (t'.points 2) := by
  rw [area_solidTriangle t (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide),
    area_solidTriangle t' (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide), h]
  have hh : 0 < t'.height 0 := t'.height_pos 0
  have hd : 0 < dist (t'.points 1) (t'.points 2) :=
    dist_pos.mpr fun e => by simpa using t'.independent.injective e
  field_simp

/-! ### Pythagorean theorem -/

/-- Pythagorean theorem (Section 20H): for a right angle at `B`, `AB² + BC² = AC²`.  The book proves
it by dissecting a square of side `a + b` into a square and four triangles; here this is the
Mathlib theorem (proved from inner products), and the dissection is not formalized. -/
@[kb "petrunin2025" "Section 20H, Pythagorean theorem, p. 173"]
theorem pythagoras_of_angle_eq_pi_div_two {A B C : E2}
    (h : EuclideanGeometry.angle A B C = Real.pi / 2) :
    dist A B ^ 2 + dist C B ^ 2 = dist A C ^ 2 :=
  by rw [sq, sq, sq]; exact ((EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A B C).mpr h).symm

/-- A right triangle with right angle at `B` has area `½ · AB · BC` (the area-method ingredient
of the book's proof). -/
theorem area_solidTriangle_of_angle_eq_pi_div_two (t : Affine.Triangle ℝ E2)
    (h : EuclideanGeometry.angle (t.points 0) (t.points 1) (t.points 2) = Real.pi / 2) :
    area (solidTriangle (t.points 0) (t.points 1) (t.points 2)) =
      2⁻¹ * dist (t.points 0) (t.points 1) * dist (t.points 1) (t.points 2) := by
  rw [area_solidTriangle_eq_mul_sin, h]; simp

end UndergradKB.Geometry
