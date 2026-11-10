import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.Congruence
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import UndergradKB.Common.Attr

/-! # Motions: direct and indirect (Petrunin, chapters 1J, 5, 7)

Motions of an oriented Euclidean plane (`P ≃ᵢ P`), direct and indirect motions (Section 5E),
reflections in lines (5D), the point reflection (7A), and congruence of triangles by motions (1J).
By Mazur-Ulam a motion is affine; its linear part has nonzero determinant, whose sign decides
whether signed angles are preserved or negated. -/

namespace UndergradKB.Geometry

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
  [Module.Oriented ℝ V (Fin 2)] [MetricSpace P] [NormedAddTorsor V P]

instance finiteDimensional_of_finrank_two : FiniteDimensional ℝ V :=
  Module.finite_of_finrank_eq_succ (n := 1) (Fact.out : Module.finrank ℝ V = 2)

/-- The linear part of a motion. -/
noncomputable def motionLinear (f : P ≃ᵢ P) : V ≃ₗᵢ[ℝ] V :=
  f.toRealAffineIsometryEquiv.linearIsometryEquiv

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
lemma motionLinear_vsub (f : P ≃ᵢ P) (p q : P) :
    motionLinear (V := V) f (p -ᵥ q) = f p -ᵥ f q :=
  f.toRealAffineIsometryEquiv.map_vsub p q

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
lemma motionLinear_toIsometryEquiv (e : P ≃ᵃⁱ[ℝ] P) :
    motionLinear (V := V) e.toIsometryEquiv = e.linearIsometryEquiv := by
  ext v
  obtain ⟨q⟩ := (inferInstance : Nonempty P)
  have h1 := motionLinear_vsub (V := V) e.toIsometryEquiv (v +ᵥ q) q
  have h2 := e.map_vsub (v +ᵥ q) q
  simp only [vadd_vsub] at h1 h2
  exact h1.trans h2.symm

lemma motion_oangle_of_det_pos (f : P ≃ᵢ P)
    (h : 0 < LinearMap.det (motionLinear (V := V) f).toLinearEquiv.toLinearMap) (A O B : P) :
    ∡ (f A) (f O) (f B) = ∡ A O B := by
  have hm := (positiveOrientation (R := ℝ) (M := V) (ι := Fin 2)).map_eq_iff_det_pos
    (motionLinear (V := V) f).toLinearEquiv (by simp [Fact.out (p := Module.finrank ℝ V = 2)])
  have := hm.2 h
  unfold EuclideanGeometry.oangle
  rw [← motionLinear_vsub, ← motionLinear_vsub]
  have h2 := Orientation.oangle_map (positiveOrientation (R := ℝ) (M := V) (ι := Fin 2))
    (motionLinear (V := V) f (A -ᵥ O)) (motionLinear (V := V) f (B -ᵥ O)) (motionLinear (V := V) f)
  rw [this] at h2
  simpa using h2

lemma motion_oangle_of_det_neg (f : P ≃ᵢ P)
    (h : LinearMap.det (motionLinear (V := V) f).toLinearEquiv.toLinearMap < 0) (A O B : P) :
    ∡ (f A) (f O) (f B) = -∡ A O B := by
  have hm := (positiveOrientation (R := ℝ) (M := V) (ι := Fin 2)).map_eq_neg_iff_det_neg
    (motionLinear (V := V) f).toLinearEquiv (by simp [Fact.out (p := Module.finrank ℝ V = 2)])
  have := hm.2 h
  unfold EuclideanGeometry.oangle
  rw [← motionLinear_vsub, ← motionLinear_vsub]
  have h2 := Orientation.oangle_map (positiveOrientation (R := ℝ) (M := V) (ι := Fin 2))
    (motionLinear (V := V) f (A -ᵥ O)) (motionLinear (V := V) f (B -ᵥ O)) (motionLinear (V := V) f)
  rw [this] at h2
  simp at h2
  rw [Orientation.oangle_neg_orientation_eq_neg] at h2
  rw [← h2, neg_neg]

/-- Every motion preserves all signed angles or reverses all of them. -/
lemma motion_oangle_dichotomy (f : P ≃ᵢ P) :
    (∀ A O B : P, ∡ (f A) (f O) (f B) = ∡ A O B) ∨
      (∀ A O B : P, ∡ (f A) (f O) (f B) = -∡ A O B) := by
  have hne : LinearMap.det (motionLinear (V := V) f).toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr (motion_oangle_of_det_neg f h)
  · exact Or.inl (motion_oangle_of_det_pos f h)

/-- A motion is *direct* if it preserves the signed angle of every triangle (book definition D045). -/
def IsDirectMotion (f : P ≃ᵢ P) : Prop :=
  ∀ A B C : P, ¬Collinear ℝ ({A, B, C} : Set P) → ∡ (f A) (f B) (f C) = ∡ A B C

/-- A motion is *indirect* if it negates the signed angle of every triangle (book definition D046). -/
def IsIndirectMotion (f : P ≃ᵢ P) : Prop :=
  ∀ A B C : P, ¬Collinear ℝ ({A, B, C} : Set P) → ∡ (f A) (f B) (f C) = -∡ A B C

/-- **Every motion is direct or indirect** (Petrunin, Proposition 5.12). -/
@[kb "petrunin2025" "Proposition 5.12, p. 41"]
theorem motion_isDirect_or_isIndirect (f : P ≃ᵢ P) : IsDirectMotion f ∨ IsIndirectMotion f := by
  rcases motion_oangle_dichotomy f with h | h
  · exact Or.inl fun A B C _ => h A B C
  · exact Or.inr fun A B C _ => h A B C

/-! ### Reflections in a line -/

section Reflection

variable {A B : P}

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
lemma reflection_linearIsometryEquiv (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (reflection s).linearIsometryEquiv = s.direction.reflection := by
  ext v
  have h := (reflection s).map_vsub (v +ᵥ (Classical.arbitrary s : P)) (Classical.arbitrary s)
  simp only [vadd_vsub] at h
  rw [h]
  simp only [reflection_apply, vadd_vsub_vadd_cancel_right, vadd_vsub, vsub_self, map_zero,
    sub_zero]

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
lemma finrank_direction_line (h : A ≠ B) :
    Module.finrank ℝ (line[ℝ, A, B]).direction = 1 := by
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.2 h)

omit [Module.Oriented ℝ V (Fin 2)] in
lemma det_reflection_line (h : A ≠ B) :
    LinearMap.det (motionLinear (V := V) (reflection line[ℝ, A, B]).toIsometryEquiv).toLinearEquiv.toLinearMap
      = -1 := by
  have h1 := finrank_direction_line (V := V) h
  have h2 := Submodule.finrank_add_finrank_orthogonal (line[ℝ, A, B]).direction
  rw [Fact.out (p := Module.finrank ℝ V = 2), h1] at h2
  have h3 : Module.finrank ℝ (line[ℝ, A, B]).directionᗮ = 1 := by omega
  rw [motionLinear_toIsometryEquiv, reflection_linearIsometryEquiv]
  have := Submodule.det_reflection (line[ℝ, A, B]).direction
  rw [h3] at this
  simpa using this

/-- The reflection in a line is a motion, and every signed angle changes sign
(Petrunin, Corollary 5.10). -/
lemma oangle_reflection (h : A ≠ B) (X Y Z : P) :
    ∡ (reflection line[ℝ, A, B] X) (reflection line[ℝ, A, B] Y) (reflection line[ℝ, A, B] Z)
      = -∡ X Y Z :=
  motion_oangle_of_det_neg (reflection line[ℝ, A, B]).toIsometryEquiv
    (by rw [det_reflection_line h]; norm_num) X Y Z

/-- **Reflections in lines are indirect motions** (Petrunin, Corollary 5.10). -/
@[kb "petrunin2025" "Corollary 5.10, p. 40"]
theorem reflection_isIndirectMotion (h : A ≠ B) :
    IsIndirectMotion (reflection line[ℝ, A, B]).toIsometryEquiv :=
  fun X Y Z _ => oangle_reflection h X Y Z

/-- **Reflection of a point in a line** (Petrunin, Proposition 5.8): the reflection `P'` of `P` in
`(AB)` satisfies `AP' = AP` and `∡BAP' = -∡BAP`. -/
@[kb "petrunin2025" "Proposition 5.8, p. 39"]
theorem reflection_dist_oangle (h : A ≠ B) (X : P) :
    dist A (reflection line[ℝ, A, B] X) = dist A X ∧
      ∡ B A (reflection line[ℝ, A, B] X) = -∡ B A X := by
  refine ⟨dist_reflection_eq_of_mem _ (left_mem_affineSpan_pair ℝ A B) X, ?_⟩
  have hA : reflection line[ℝ, A, B] A = A :=
    (reflection_eq_self_iff A).2 (left_mem_affineSpan_pair ℝ A B)
  have hB : reflection line[ℝ, A, B] B = B :=
    (reflection_eq_self_iff B).2 (right_mem_affineSpan_pair ℝ A B)
  have := oangle_reflection h B A X
  rwa [hA, hB] at this

end Reflection

/-! ### Point reflection -/

/-- **The reflection in a point is a direct motion** (Petrunin, Proposition 7.6). -/
@[kb "petrunin2025" "Proposition 7.6, p. 51"]
theorem pointReflection_isDirectMotion (c : P) :
    IsDirectMotion (AffineIsometryEquiv.pointReflection ℝ c).toIsometryEquiv := by
  intro A B C _
  have key : ∀ p q : P, (AffineIsometryEquiv.pointReflection ℝ c) p -ᵥ
      (AffineIsometryEquiv.pointReflection ℝ c) q = -(p -ᵥ q) := by
    intro p q
    simp only [AffineIsometryEquiv.pointReflection_apply, vadd_vsub_vadd_cancel_right,
      vsub_sub_vsub_cancel_left, neg_vsub_eq_vsub_rev]
  unfold EuclideanGeometry.oangle
  change (positiveOrientation (R := ℝ) (M := V) (ι := Fin 2)).oangle
    ((AffineIsometryEquiv.pointReflection ℝ c) A -ᵥ (AffineIsometryEquiv.pointReflection ℝ c) B)
    ((AffineIsometryEquiv.pointReflection ℝ c) C -ᵥ (AffineIsometryEquiv.pointReflection ℝ c) B) = _
  rw [key, key, Orientation.oangle_neg_neg]

/-! ### Motions as products of at most three line reflections; congruence by motions -/

section Products

open AffineSubspace

set_option linter.unusedSectionVars false

/-- `r` is the reflection across a line of the plane; every line is the perpendicular bisector
`perpBisector a b` of two distinct points `a ≠ b`. -/
def IsLineReflection (r : P ≃ᵃⁱ[ℝ] P) : Prop :=
  ∃ a b : P, a ≠ b ∧ r = reflection (perpBisector a b)

/-- The perpendicular bisector of two distinct points of the plane is a line. -/
lemma finrank_direction_perpBisector {a b : P} (h : a ≠ b) :
    Module.finrank ℝ (perpBisector a b).direction = 1 := by
  have : Fact (Module.finrank ℝ V = 1 + 1) := ⟨Fact.out⟩
  rw [direction_perpBisector]
  exact Submodule.finrank_orthogonal_span_singleton (n := 1) (vsub_ne_zero.2 h.symm)

lemma exists_reflection_step (X Y : P) (S : Set P) (hS : ∀ Z ∈ S, dist Z X = dist Z Y) :
    ∃ L : List (P ≃ᵃⁱ[ℝ] P), L.length ≤ 1 ∧ (∀ r ∈ L, IsLineReflection r) ∧ L.prod X = Y ∧
      ∀ Z ∈ S, L.prod Z = Z := by
  by_cases h : X = Y
  · exact ⟨[], by simp, by simp, by simp [h], by simp⟩
  · refine ⟨[reflection (perpBisector X Y)], by simp, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      exact ⟨X, Y, h, hr⟩
    · simp
    · intro Z hZ
      simp only [List.prod_cons, List.prod_nil, mul_one]
      exact (reflection_eq_self_iff Z).2 (mem_perpBisector_iff_dist_eq.2 (hS Z hZ))

lemma prod_append_apply (L₁ L₂ L₃ : List (P ≃ᵃⁱ[ℝ] P)) (x : P) :
    (L₃ ++ L₂ ++ L₁).prod x = L₃.prod (L₂.prod (L₁.prod x)) := by
  simp [List.prod_append, AffineIsometryEquiv.coe_mul]

lemma exists_three_reflections (A B C A' B' C' : P) (hAB : dist A B = dist A' B')
    (hAC : dist A C = dist A' C') (hBC : dist B C = dist B' C') :
    ∃ L : List (P ≃ᵃⁱ[ℝ] P), L.length ≤ 3 ∧ (∀ r ∈ L, IsLineReflection r) ∧
      L.prod A = A' ∧ L.prod B = B' ∧ L.prod C = C' := by
  obtain ⟨L₁, l₁, r₁, a₁, -⟩ := exists_reflection_step A A' ∅ (by simp)
  obtain ⟨L₂, l₂, r₂, b₂, f₂⟩ := exists_reflection_step (L₁.prod B) B' {A'} (by
    intro Z hZ
    rw [Set.mem_singleton_iff] at hZ
    subst hZ
    calc dist Z (L₁.prod B) = dist (L₁.prod A) (L₁.prod B) := by rw [a₁]
      _ = dist A B := AffineIsometryEquiv.dist_map _ _ _
      _ = dist Z B' := hAB)
  have hA2 : L₂.prod (L₁.prod A) = A' := by rw [a₁]; exact f₂ A' rfl
  obtain ⟨L₃, l₃, r₃, c₃, f₃⟩ := exists_reflection_step (L₂.prod (L₁.prod C)) C' {A', B'} (by
    intro Z hZ
    rcases hZ with rfl | hZ
    · calc dist Z (L₂.prod (L₁.prod C)) = dist (L₂.prod (L₁.prod A)) (L₂.prod (L₁.prod C)) := by
            rw [hA2]
        _ = dist A C := by simp [AffineIsometryEquiv.dist_map]
        _ = dist Z C' := hAC
    · rw [Set.mem_singleton_iff] at hZ
      subst hZ
      calc dist Z (L₂.prod (L₁.prod C)) = dist (L₂.prod (L₁.prod B)) (L₂.prod (L₁.prod C)) := by
            rw [b₂]
        _ = dist B C := by simp [AffineIsometryEquiv.dist_map]
        _ = dist Z C' := hBC)
  refine ⟨L₃ ++ L₂ ++ L₁, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append]; omega
  · intro r hr
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    exacts [r₃ r hr, r₂ r hr, r₁ r hr]
  · rw [prod_append_apply, hA2]; exact f₃ A' (by simp)
  · rw [prod_append_apply, b₂]; exact f₃ B' (by simp)
  · rw [prod_append_apply, c₃]

include V in
/-- **Congruence by motions** (Petrunin, Section 1J): triangles `ABC` and `A'B'C'` have equal
corresponding sides iff some motion of the plane maps `A, B, C` to `A', B', C'`. -/
@[kb "petrunin2025" "Definition of congruent triangles, Section 1J, p. 16"]
theorem sides_eq_iff_exists_motion (A B C A' B' C' : P) :
    (dist A B = dist A' B' ∧ dist B C = dist B' C' ∧ dist C A = dist C' A') ↔
      ∃ f : P ≃ᵢ P, f A = A' ∧ f B = B' ∧ f C = C' := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨L, -, -, hA, hB, hC⟩ :=
      exists_three_reflections (V := V) A B C A' B' C' h1 (by rw [dist_comm A C, dist_comm A' C']; exact h3) h2
    exact ⟨L.prod.toIsometryEquiv, hA, hB, hC⟩
  · rintro ⟨f, rfl, rfl, rfl⟩
    exact ⟨(f.dist_eq _ _).symm, (f.dist_eq _ _).symm, (f.dist_eq _ _).symm⟩

include V in
/-- The motion-based congruence of triangles agrees with Mathlib's distance-based `Congruent`
(Petrunin, Section 1J). -/
@[kb "petrunin2025" "Definition of congruent triangles, Section 1J, p. 16"]
theorem congruent_iff_exists_motion (A B C A' B' C' : P) :
    Congruent ![A, B, C] ![A', B', C'] ↔ ∃ f : P ≃ᵢ P, f A = A' ∧ f B = B' ∧ f C = C' := by
  rw [← sides_eq_iff_exists_motion (V := V), triangle_congruent_iff_dist_eq]
  constructor
  · intro h
    exact ⟨by simpa using h 0 1, by simpa using h 1 2, by simpa using h 2 0⟩
  · rintro ⟨h1, h2, h3⟩ i j
    fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

/-- **Every motion of the plane is a composition of at most three reflections across lines**
(Petrunin, Exercise 5.11). A line is given as the perpendicular bisector of two distinct points. -/
@[kb "petrunin2025" "Exercise 5.11, p. 41"]
theorem motion_eq_prod_reflections (f : P ≃ᵢ P) :
    ∃ L : List (P ≃ᵃⁱ[ℝ] P), L.length ≤ 3 ∧ (∀ r ∈ L, IsLineReflection r) ∧ ∀ x, f x = L.prod x := by
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional (k := ℝ) (V := V) (P := P)
    (ι := Fin 3) (by simp [Fact.out (p := Module.finrank ℝ V = 2)])
  obtain ⟨L, hl, hr, hA, hB, hC⟩ := exists_three_reflections (b 0) (b 1) (b 2)
    (f (b 0)) (f (b 1)) (f (b 2)) (f.dist_eq _ _).symm (f.dist_eq _ _).symm (f.dist_eq _ _).symm
  refine ⟨L, hl, hr, ?_⟩
  have key : f.toRealAffineIsometryEquiv.toAffineEquiv = L.prod.toAffineEquiv := by
    refine AffineEquiv.ext_on b.tot _ _ ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hA.symm
    · exact hB.symm
    · exact hC.symm
  intro x
  exact congrArg (fun T => T x) key

end Products

end UndergradKB.Geometry
