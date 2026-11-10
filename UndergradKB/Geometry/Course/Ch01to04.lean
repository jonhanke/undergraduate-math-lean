import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Congruence
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Order.IntermediateValue
import UndergradKB.Common.Attr

/-! # Course layer: Petrunin chapters 1 to 4

Thin, citable statements in the book's terms (Petrunin, *Euclidean Plane and its Relatives*, 3rd ed.),
each proved by the Mathlib lemma named in the audit (`docs/coverage/geometry/checklist.md`).
The plane is an oriented 2-dimensional real inner product affine space (signed angles `∡`), or a general
inner product space when the book's statement holds there.

Chapter 1 (metric spaces, isometries, continuity), chapter 2 (axioms, zero and straight angles, vertical
angles, point reflection), chapter 3 (signs of angles, intermediate value theorem), chapter 4 (congruence
conditions, isosceles triangles).  Definitions (metric space, isometry, motion, triangle, circle, sign of
an angle) are not restated: they are Mathlib's `MetricSpace`, `Isometry`, `IsometryEquiv`, `Sbtw`,
`Real.Angle.sign`, `EuclideanGeometry.Sphere`. -/

namespace UndergradKB.Geometry.Course

open EuclideanGeometry Real

/-! ## Chapter 1: metric spaces -/

section Ch1

/-- Petrunin, example "Real line" (p. 11): the metric on `ℝ` is `|A - B|`. -/
@[kb "petrunin2025" "Example, Real line, p. 11"]
theorem petrunin_ch1_real_line_metric (A B : ℝ) : dist A B = |A - B| :=
  Real.dist_eq A B

/-- Petrunin, Exercise 1.3 (p. 11): the three standard metrics on `ℝ²`, as explicit formulas
(Manhattan `d₁`, Euclidean `d₂`, maximum `d_∞`); each is a metric (an instance in Mathlib). -/
@[kb "petrunin2025" "Exercise 1.3, p. 11"]
theorem petrunin_1_3 (x y : Fin 2 → ℝ) :
    dist (WithLp.toLp 1 x) (WithLp.toLp 1 y) = |x 0 - y 0| + |x 1 - y 1| ∧
    dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) ∧
    dist x y = max |x 0 - y 0| |x 1 - y 1| := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PiLp.dist_eq_of_L1]
    simp [Fin.sum_univ_two, Real.dist_eq]
  · rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  · rw [dist_pi_def]
    simp [Fin.univ_succ, Real.dist_eq]

/-- Petrunin, Exercise 1.5 (p. 12): a distance-preserving map is injective. -/
@[kb "petrunin2025" "Exercise 1.5, p. 12"]
theorem petrunin_1_5 {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}
    (hf : ∀ A B, dist (f A) (f B) = dist A B) : Function.Injective f :=
  Isometry.injective (Isometry.of_dist_eq hf)

/-- Petrunin, Remark in section 1E (p. 12): a subset of a metric space is a metric space with the
restricted distance. -/
@[kb "petrunin2025" "Remark, Section 1E, p. 12"]
theorem petrunin_ch1_subset_metric {X : Type*} [MetricSpace X] (S : Set X) (A B : S) :
    dist A B = dist (A : X) (B : X) :=
  Subtype.dist_eq A B

/-- Petrunin, Section 1H (p. 14): `α ≡ β (mod 2π)` iff they differ by an integer multiple of `2π`
(congruence of reals is equality in `Real.Angle`). -/
@[kb "petrunin2025" "Section 1H, p. 14"]
theorem petrunin_ch1_mod_two_pi (α β : ℝ) :
    (α : Real.Angle) = (β : Real.Angle) ↔ ∃ k : ℤ, α - β = 2 * π * k :=
  Real.Angle.angle_eq_iff_two_pi_dvd_sub

/-- Petrunin, Exercise 1.13 (p. 15): `2·α ≡ 0` iff `α ≡ 0` or `α ≡ π`. -/
@[kb "petrunin2025" "Exercise 1.13, p. 15"]
theorem petrunin_1_13 (α : ℝ) :
    ((2 * α : ℝ) : Real.Angle) = 0 ↔ (α : Real.Angle) = 0 ∨ (α : Real.Angle) = (π : ℝ) := by
  rw [← Real.Angle.two_zsmul_eq_zero_iff, two_zsmul, two_mul, Real.Angle.coe_add]

/-- Petrunin, Section 1I (p. 15): epsilon-delta continuity of a map of metric spaces. -/
@[kb "petrunin2025" "Section 1I, p. 15"]
theorem petrunin_ch1_continuity {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ a : X, ∀ ε > 0, ∃ δ > 0, ∀ x : X, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuous_iff

/-- Petrunin, Exercise 1.15 (p. 16): `B ↦ d(A, B)` and `(A, B) ↦ d(A, B)` are continuous. -/
@[kb "petrunin2025" "Exercise 1.15, p. 16"]
theorem petrunin_1_15 {X : Type*} [MetricSpace X] (A : X) :
    Continuous (fun B : X => dist A B) ∧ Continuous (fun p : X × X => dist p.1 p.2) :=
  ⟨continuous_const.dist continuous_id, continuous_dist⟩

/-- Petrunin, Exercise 1.16 (p. 16): a composition of continuous maps is continuous. -/
@[kb "petrunin2025" "Exercise 1.16, p. 16"]
theorem petrunin_1_16 {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf

end Ch1

/-! ## Chapter 2: axioms and first consequences -/

section Ch2

/-- Petrunin, Axiom I (p. 19): the Euclidean plane `ℝ²` (with its Euclidean metric) is a metric space
with at least two points. -/
@[kb "petrunin2025" "Axiom I, p. 19"]
theorem petrunin_axiom_I : ∃ A B : EuclideanSpace ℝ (Fin 2), A ≠ B := by
  obtain ⟨A, B, h⟩ := exists_pair_ne (EuclideanSpace ℝ (Fin 2))
  exact ⟨A, B, h⟩

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- Petrunin, Axiom III (p. 19): the measure of an angle `AOB` is a real number in `(-π, π]`
(the representative of the signed angle `∡AOB` modulo `2π`). -/
@[kb "petrunin2025" "Axiom III, p. 19"]
theorem petrunin_axiom_III (A O B : P) : -π < (∡ A O B).toReal ∧ (∡ A O B).toReal ≤ π :=
  ⟨Real.Angle.neg_pi_lt_toReal _, Real.Angle.toReal_le_pi _⟩

/-- Petrunin, Axiom III(b) (p. 19): `∡AOB + ∡BOC ≡ ∡AOC` for points `A, B, C` distinct from `O`. -/
@[kb "petrunin2025" "Axiom III(b), p. 19"]
theorem petrunin_axiom_III_b {A B C O : P} (hA : A ≠ O) (hB : B ≠ O) (hC : C ≠ O) :
    ∡ A O B + ∡ B O C = ∡ A O C :=
  EuclideanGeometry.oangle_add hA hB hC

/-- Petrunin, Axiom III(c) (p. 19): the angle function is continuous at every triple `(A, O, B)` with
`O ≠ A`, `O ≠ B` (as a function with values in the circle `Real.Angle`; the real-valued form of the
book is its composite with the representative in `(-π, π]`, continuous away from `π`). -/
@[kb "petrunin2025" "Axiom III(c), p. 19"]
theorem petrunin_axiom_III_c {A O B : P} (hA : A ≠ O) (hB : B ≠ O) :
    ContinuousAt (fun x : P × P × P => ∡ x.1 x.2.1 x.2.2) (A, O, B) :=
  EuclideanGeometry.continuousAt_oangle hA hB

/-- Unsigned angles agree iff the signed angles agree up to sign (for points distinct from the vertex). -/
theorem angle_eq_iff_oangle_eq_or_eq_neg {A B C A' B' C' : P} (hB : B ≠ A) (hC : C ≠ A)
    (hB' : B' ≠ A') (hC' : C' ≠ A') :
    ∠ C' A' B' = ∠ C A B ↔ (∡ C' A' B' = ∡ C A B ∨ ∡ C' A' B' = -∡ C A B) := by
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal hC' hB',
    EuclideanGeometry.angle_eq_abs_oangle_toReal hC hB]
  constructor
  · intro h
    rcases abs_eq_abs.1 h with h | h
    · exact Or.inl (Real.Angle.toReal_injective h)
    · by_cases hpi : ∡ C A B = π
      · have h1 := Real.Angle.neg_pi_lt_toReal (∡ C' A' B')
        rw [h, hpi, Real.Angle.toReal_pi] at h1
        linarith
      · refine Or.inr (Real.Angle.toReal_injective ?_)
        rw [h, Real.Angle.toReal_neg_eq_neg_toReal_iff.2 hpi]
  · rintro (h | h)
    · rw [h]
    · rw [h, Real.Angle.abs_toReal_neg]

/-- Petrunin, Axiom IV (p. 19), SAS: triangles `ABC` and `A'B'C'` with `A'B' = AB`, `A'C' = AC` and
`∡C'A'B' = ±∡CAB` are congruent (equal pairwise distances, Mathlib's `Congruent`); conversely
congruent triangles satisfy these equalities.  Stated for triangles with `A ≠ B`, `A ≠ C`. -/
@[kb "petrunin2025" "Axiom IV, p. 19"]
theorem petrunin_axiom_IV {A B C A' B' C' : P} (hAB : A ≠ B) (hAC : A ≠ C) :
    Congruent ![A, B, C] ![A', B', C'] ↔
      dist A' B' = dist A B ∧ dist A' C' = dist A C ∧
        (∡ C' A' B' = ∡ C A B ∨ ∡ C' A' B' = -∡ C A B) := by
  constructor
  · intro h
    have h1 : dist A' B' = dist A B := by simpa using (h.dist_eq 0 1).symm
    have h2 : dist A' C' = dist A C := by simpa using (h.dist_eq 0 2).symm
    have hB' : B' ≠ A' := by
      intro e; rw [e, dist_self] at h1; exact hAB (dist_eq_zero.1 h1.symm)
    have hC' : C' ≠ A' := by
      intro e; rw [e, dist_self] at h2; exact hAC (dist_eq_zero.1 h2.symm)
    refine ⟨h1, h2, ?_⟩
    rw [← angle_eq_iff_oangle_eq_or_eq_neg hAB.symm hAC.symm hB' hC']
    simpa using (EuclideanGeometry.angle_eq_of_congruent h 2 0 1).symm
  · rintro ⟨h1, h2, h3⟩
    have hB' : B' ≠ A' := by
      intro e; rw [e, dist_self] at h1; exact hAB (dist_eq_zero.1 h1.symm)
    have hC' : C' ≠ A' := by
      intro e; rw [e, dist_self] at h2; exact hAC (dist_eq_zero.1 h2.symm)
    have hang := (angle_eq_iff_oangle_eq_or_eq_neg hAB.symm hAC.symm hB' hC').2 h3
    have key : Congruent ![B, A, C] ![B', A', C'] :=
      EuclideanGeometry.side_angle_side
        (by rw [EuclideanGeometry.angle_comm B A C, EuclideanGeometry.angle_comm B' A' C']
            exact hang.symm)
        (by rw [dist_comm, dist_comm B' A']; exact h1.symm)
        h2.symm
    have hBC : dist B C = dist B' C' := by simpa using key.dist_eq 0 2
    exact EuclideanGeometry.side_side_side h1.symm hBC (by rw [dist_comm C A, dist_comm C' A']; exact h2.symm)

/-- Petrunin, Proposition 2.4 (zero angle): `∡AOA = 0` (the book assumes `A ≠ O`; Mathlib needs no
hypothesis). -/
@[kb "petrunin2025" "Proposition 2.4, p. 20"]
theorem petrunin_2_4 {A O : P} : ∡ A O A = 0 :=
  EuclideanGeometry.oangle_self_left_right A O

/-- Petrunin, Exercise 2.5 (p. 20): if `∡AOB = 0` then the half-lines `[OA)` and `[OB)` coincide
(one of `A`, `B` lies on the segment from `O` to the other; equivalently `OA` and `OB` are on one ray). -/
@[kb "petrunin2025" "Exercise 2.5, p. 20"]
theorem petrunin_2_5 {A O B : P} (h : ∡ A O B = 0) :
    SameRay ℝ (A -ᵥ O) (B -ᵥ O) ∧ (Wbtw ℝ O A B ∨ Wbtw ℝ O B A) :=
  ⟨(Module.Oriented.positiveOrientation (R := ℝ) (M := V) (ι := Fin 2)).oangle_eq_zero_iff_sameRay.1 h,
    EuclideanGeometry.oangle_eq_zero_iff_wbtw.1 h⟩

/-- Petrunin, Proposition 2.6 (p. 20): `∡AOB ≡ -∡BOA`. -/
@[kb "petrunin2025" "Proposition 2.6, p. 20"]
theorem petrunin_2_6 {A O B : P} : ∡ A O B = -∡ B O A :=
  EuclideanGeometry.oangle_rev B O A

/-- Petrunin, Theorem 2.7 (p. 20): the angle `AOB` is straight (`∡AOB = π`) iff `O` lies between `A`
and `B`. -/
@[kb "petrunin2025" "Theorem 2.7, p. 20"]
theorem petrunin_2_7 {A O B : P} : ∡ A O B = π ↔ Sbtw ℝ A O B :=
  EuclideanGeometry.oangle_eq_pi_iff_sbtw

/-- Petrunin, Corollary 2.8 (p. 21): a triangle `ABC` is degenerate iff one of its angles is `0` or
`π`; and then the angle measures are `0`, `0`, `π` (in some order). -/
@[kb "petrunin2025" "Corollary 2.8, p. 21"]
theorem petrunin_2_8 {A B C : P} (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    (Collinear ℝ ({A, B, C} : Set P) ↔
      ((∡ A B C = 0 ∨ ∡ A B C = π) ∨ (∡ B C A = 0 ∨ ∡ B C A = π) ∨
        (∡ C A B = 0 ∨ ∡ C A B = π))) ∧
    (Collinear ℝ ({A, B, C} : Set P) →
      (∡ A B C = π ∧ ∡ B C A = 0 ∧ ∡ C A B = 0) ∨ (∡ A B C = 0 ∧ ∡ B C A = π ∧ ∡ C A B = 0) ∨
        (∡ A B C = 0 ∧ ∡ B C A = 0 ∧ ∡ C A B = π)) := by
  have e1 : ({B, C, A} : Set P) = {A, B, C} := by ext; simp; tauto
  have e2 : ({C, A, B} : Set P) = {A, B, C} := by ext; simp; tauto
  refine ⟨?_, ?_⟩
  · rw [← EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | h | h)
      · exact h
      · have := EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear.1 h
        rw [e1] at this
        exact EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear.2 this
      · have := EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear.1 h
        rw [e2] at this
        exact EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear.2 this
  · intro h
    rcases h.wbtw_or_wbtw_or_wbtw with h1 | h1 | h1
    · have hs : Sbtw ℝ A B C := ⟨h1, hAB.symm, hBC⟩
      exact Or.inl ⟨hs.oangle₁₂₃_eq_pi, hs.oangle₂₃₁_eq_zero, hs.oangle₃₁₂_eq_zero⟩
    · have hs : Sbtw ℝ B C A := ⟨h1, hBC.symm, hCA⟩
      exact Or.inr (Or.inl ⟨hs.oangle₃₁₂_eq_zero, hs.oangle₁₂₃_eq_pi, hs.oangle₂₃₁_eq_zero⟩)
    · have hs : Sbtw ℝ C A B := ⟨h1, hCA.symm, hAB⟩
      exact Or.inr (Or.inr ⟨hs.oangle₂₃₁_eq_zero, hs.oangle₃₁₂_eq_zero, hs.oangle₁₂₃_eq_pi⟩)

/-- Petrunin, Proposition 2.12 (p. 22): vertical angles are equal: if `O` lies between `A` and `A'`
and between `B` and `B'`, then `∡AOB = ∡A'OB'`. -/
@[kb "petrunin2025" "Proposition 2.12, p. 22"]
theorem petrunin_2_12 {A A' B B' O : P} (hA : Sbtw ℝ A O A') (hB : Sbtw ℝ B O B') :
    ∡ A O B = ∡ A' O B' :=
  hA.oangle_eq_left_right hB

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
/-- Petrunin, Lemma 2.13 (p. 22): for `X ≠ O` there is a unique `X'` such that `O` is the midpoint of
`[XX']`, and it is the reflection of `X` across `O`. -/
@[kb "petrunin2025" "Lemma 2.13, p. 22"]
theorem petrunin_2_13 {X O : P} (_h : X ≠ O) :
    (∃! X' : P, midpoint ℝ X X' = O) ∧ midpoint ℝ X (AffineEquiv.pointReflection ℝ O X) = O := by
  refine ⟨⟨AffineEquiv.pointReflection ℝ O X, midpoint_eq_iff.2 rfl, ?_⟩, midpoint_eq_iff.2 rfl⟩
  intro y hy
  exact (midpoint_eq_iff.1 hy).symm

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
/-- Petrunin, Proposition 2.14 (p. 23): reflection across a point is a motion of the plane (an
isometry of the plane onto itself) fixing `O` and swapping each point with its mirror image. -/
@[kb "petrunin2025" "Proposition 2.14, p. 23"]
theorem petrunin_2_14 (O : P) :
    ∃ f : P ≃ᵢ P, f O = O ∧ ∀ X, midpoint ℝ X (f X) = O :=
  ⟨(AffineIsometryEquiv.pointReflection ℝ O).toIsometryEquiv, by simp,
    fun X => midpoint_eq_iff.2 rfl⟩

end Ch2

/-! ## Chapter 3: half-planes -/

section Ch3

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- Petrunin, Lemma 3.2 (p. 24): if the angle `AOB` is straight, then for `X ≠ O` the angle `AOX` is
positive iff `BOX` is negative. -/
@[kb "petrunin2025" "Lemma 3.2, p. 24"]
theorem petrunin_3_2 {A B O X : P} (h : ∡ A O B = π) (hX : X ≠ O) :
    (∡ A O X).sign = 1 ↔ (∡ B O X).sign = -1 := by
  have hs : Sbtw ℝ A O B := EuclideanGeometry.oangle_eq_pi_iff_sbtw.1 h
  rw [hs.oangle_eq_add_pi_left hX, Real.Angle.sign_add_pi, neg_eq_iff_eq_neg]

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
/-- Petrunin, Theorem 3.4 (p. 25), intermediate value theorem: a continuous `f : [a, b] → ℝ` whose
values at the ends have opposite signs vanishes at some `t₀ ∈ [a, b]` (indeed in `(a, b)`). -/
@[kb "petrunin2025" "Theorem 3.4, p. 25"]
theorem petrunin_3_4 {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (h : f a < 0 ∧ 0 < f b ∨ f b < 0 ∧ 0 < f a) : ∃ t ∈ Set.Ioo a b, f t = 0 := by
  have hmem : (0 : ℝ) ∈ f '' Set.Icc a b := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact intermediate_value_Icc hab hf ⟨h1.le, h2.le⟩
    · exact intermediate_value_Icc' hab hf ⟨h1.le, h2.le⟩
  obtain ⟨t, ht, ht0⟩ := hmem
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, ht0⟩
  · rintro rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · rintro rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- Petrunin, Lemma 3.6 (p. 25): if `Q'` lies on the half-line `[PQ)`, `Q' ≠ P` (and `P ≠ Q`), then
for every `X` the angles `PQX` and `PQ'X` have the same sign (in the book `X ∉ (PQ)`; the proof in
Mathlib shows more, namely `∡XPQ = ∡XPQ'`, so no hypothesis on `X` is needed). -/
@[kb "petrunin2025" "Lemma 3.6, p. 25"]
theorem petrunin_3_6 {P₀ Q Q' X : P} (hPQ : Q ≠ P₀) (hQ' : Q' ≠ P₀)
    (hray : SameRay ℝ (Q -ᵥ P₀) (Q' -ᵥ P₀)) :
    (∡ P₀ Q X).sign = (∡ P₀ Q' X).sign := by
  rw [EuclideanGeometry.oangle_rotate_sign X P₀ Q, EuclideanGeometry.oangle_rotate_sign X P₀ Q']
  rcases wbtw_total_of_sameRay_vsub_left hray with h | h
  · rw [h.oangle_eq_right hPQ]
  · rw [h.oangle_eq_right hQ']

/-- Petrunin, Signs of angles of a triangle 3.7 (p. 26): in a nondegenerate triangle `ABC` the
angles `ABC`, `BCA`, `CAB` are nonzero and have the same sign. -/
@[kb "petrunin2025" "Signs of angles of a triangle 3.7, p. 26"]
theorem petrunin_3_7 {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) :
    (∡ A B C).sign ≠ 0 ∧ (∡ B C A).sign = (∡ A B C).sign ∧ (∡ C A B).sign = (∡ A B C).sign := by
  refine ⟨?_, EuclideanGeometry.oangle_rotate_sign A B C, ?_⟩
  · intro h0
    exact h (EuclideanGeometry.oangle_sign_eq_zero_iff_collinear.1 h0)
  · rw [EuclideanGeometry.oangle_rotate_sign B C A, EuclideanGeometry.oangle_rotate_sign A B C]

/-- Petrunin, Lemma 3.9 (p. 26): if the segment `[XY]` does not meet the line `(PQ)` then the angles
`PQX` and `PQY` have the same sign. -/
@[kb "petrunin2025" "Lemma 3.9, p. 26"]
theorem petrunin_3_9 {P₀ Q X Y : P} (hPQ : P₀ ≠ Q)
    (h : ∀ Z, Wbtw ℝ X Z Y → Z ∉ line[ℝ, P₀, Q]) :
    (∡ P₀ Q X).sign = (∡ P₀ Q Y).sign := by
  let s : Set P := affineSegment ℝ X Y
  have hQ : Q ∈ line[ℝ, P₀, Q] := right_mem_affineSpan_pair ℝ P₀ Q
  have hs : IsConnected s :=
    (isConnected_Icc zero_le_one).image _ (AffineMap.lineMap_continuous.continuousOn)
  have hne : ∀ z ∈ s, z ≠ Q := fun z hz hzQ => h z hz (hzQ ▸ hQ)
  have hf : ContinuousOn (fun z : P => ∡ P₀ Q z) s := by
    intro z hz
    have hc := EuclideanGeometry.continuousAt_oangle (x := (P₀, Q, z)) hPQ (hne z hz)
    exact (hc.comp (f := fun z : P => (P₀, Q, z)) (x := z) (by fun_prop)).continuousWithinAt
  have hsp : ∀ z ∈ s, ∡ P₀ Q z ≠ 0 ∧ ∡ P₀ Q z ≠ π := by
    intro z hz
    rw [EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent,
      affineIndependent_iff_not_collinear_set]
    intro hcol
    exact h z hz (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hPQ)
  exact (Real.Angle.sign_eq_of_continuousOn hs hf hsp (wbtw_self_left ℝ X Y)
    (wbtw_self_right ℝ X Y)).symm

end Ch3

/-! ## Chapter 4: congruent triangles -/

section Ch4

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Petrunin, section 4A (p. 31), SAS: two sides and the included angle equal imply congruence
(unsigned angles; the signed `±` form is `petrunin_axiom_IV`). -/
@[kb "petrunin2025" "Section 4A, p. 31"]
theorem petrunin_4a_sas {A B C A' B' C' : P} (h : ∠ A B C = ∠ A' B' C')
    (h₁ : dist A B = dist A' B') (h₂ : dist B C = dist B' C') :
    Congruent ![A, B, C] ![A', B', C'] :=
  EuclideanGeometry.side_angle_side h h₁ h₂

/-- Petrunin, SSS condition 4.4 (p. 33): triangles with equal corresponding sides are congruent (also
when degenerate). -/
@[kb "petrunin2025" "SSS condition 4.4, p. 33"]
theorem petrunin_4_4 {A B C A' B' C' : P} (h₁ : dist A B = dist A' B')
    (h₂ : dist B C = dist B' C') (h₃ : dist C A = dist C' A') :
    Congruent ![A, B, C] ![A', B', C'] :=
  EuclideanGeometry.side_side_side h₁ h₂ h₃

/-- Petrunin, Corollary 4.5 (p. 33): if `AB + BC = AC` then `B` lies on the segment `[AC]`
(proved in any real inner product space, in particular for the Euclidean plane). -/
@[kb "petrunin2025" "Corollary 4.5, p. 33"]
theorem petrunin_4_5 {A B C : P} (h : dist A B + dist B C = dist A C) :
    Wbtw ℝ A B C :=
  (dist_add_dist_eq_iff).1 h

/-- Petrunin, SAA remark, section 4E (p. 34): a side and two angles (one of them opposite the side)
determine the triangle: if `ABC` is nondegenerate, `∠ABC = ∠A'B'C'`, `∠BCA = ∠B'C'A'` and
`CA = C'A'` then `ABC ≅ A'B'C'` (unsigned angles). -/
@[kb "petrunin2025" "SAA remark, Section 4E, p. 34"]
theorem petrunin_4e_saa {A B C A' B' C' : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (h₁ : ∠ A B C = ∠ A' B' C') (h₂ : ∠ B C A = ∠ B' C' A') (h₃ : dist C A = dist C' A') :
    Congruent ![A, B, C] ![A', B', C'] :=
  EuclideanGeometry.angle_angle_side h h₁ h₂ h₃

end Ch4

section Ch4Oriented

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- A nondegenerate triangle cannot have two vertices equal after matching signed angles up to sign. -/
theorem ne_of_oangle_eq_or_eq_neg {A B C A' B' C' : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hang : ∡ A' B' C' = ∡ A B C ∨ ∡ A' B' C' = -∡ A B C) : A' ≠ B' ∧ C' ≠ B' := by
  have h0 : ∡ A B C ≠ 0 ∧ ∡ A B C ≠ π := by
    rw [EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affineIndependent,
      affineIndependent_iff_not_collinear_set]
    exact h
  constructor
  · rintro rfl
    rw [EuclideanGeometry.oangle_self_left] at hang
    rcases hang with h1 | h1
    · exact h0.1 h1.symm
    · exact h0.1 (neg_eq_zero.1 h1.symm)
  · rintro rfl
    rw [EuclideanGeometry.oangle_self_right] at hang
    rcases hang with h1 | h1
    · exact h0.1 h1.symm
    · exact h0.1 (neg_eq_zero.1 h1.symm)

/-- Petrunin, ASA condition 4.1 (p. 31): if `AB = A'B'`, `∡ABC = ±∡A'B'C'`, `∡CAB = ±∡C'A'B'`
and `ABC` is nondegenerate, then `ABC ≅ A'B'C'`. -/
@[kb "petrunin2025" "ASA condition 4.1, p. 31"]
theorem petrunin_4_1 {A B C A' B' C' : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hAB : dist A B = dist A' B')
    (hB : ∡ A' B' C' = ∡ A B C ∨ ∡ A' B' C' = -∡ A B C)
    (hA : ∡ C' A' B' = ∡ C A B ∨ ∡ C' A' B' = -∡ C A B) :
    Congruent ![A, B, C] ![A', B', C'] := by
  have hABne : A ≠ B := ne₁₂_of_not_collinear h
  have hCBne : C ≠ B := (ne₂₃_of_not_collinear h).symm
  have hCAne : C ≠ A := (ne₁₃_of_not_collinear h).symm
  have h' : ¬Collinear ℝ ({C, A, B} : Set P) := by
    intro hc
    apply h
    have e : ({C, A, B} : Set P) = {A, B, C} := by ext; simp; tauto
    rwa [e] at hc
  obtain ⟨hA'B', hC'B'⟩ := ne_of_oangle_eq_or_eq_neg h hB
  obtain ⟨hC'A', hB'A'⟩ := ne_of_oangle_eq_or_eq_neg h' hA
  have e1 : ∠ A' B' C' = ∠ A B C :=
    (angle_eq_iff_oangle_eq_or_eq_neg (A := B) (B := C) (C := A) (A' := B') (B' := C') (C' := A')
      hCBne hABne hC'B' hA'B').2 hB
  have e2 : ∠ C' A' B' = ∠ C A B :=
    (angle_eq_iff_oangle_eq_or_eq_neg (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C')
      hABne.symm hCAne hB'A' hC'A').2 hA
  have key : Congruent ![C, B, A] ![C', B', A'] :=
    EuclideanGeometry.angle_side_angle (by
        intro hc; apply h
        have e : ({C, B, A} : Set P) = {A, B, C} := by ext; simp; tauto
        rwa [e] at hc)
      (by rw [EuclideanGeometry.angle_comm C B A, EuclideanGeometry.angle_comm C' B' A']
          exact e1.symm)
      (by rw [dist_comm B A, dist_comm B' A']; exact hAB)
      (by rw [EuclideanGeometry.angle_comm B A C, EuclideanGeometry.angle_comm B' A' C']
          exact e2.symm)
  have hBC : dist B C = dist B' C' := by simpa [dist_comm] using key.dist_eq 0 1
  have hCA : dist C A = dist C' A' := by simpa using key.dist_eq 0 2
  exact EuclideanGeometry.side_side_side hAB hBC hCA

/-- Petrunin, Theorem 4.2, Pappus (p. 32): in a triangle `ABC` with `CA = CB` (isosceles with base
`[AB]`) the base angles satisfy `∡ABC ≡ -∡BAC`; conversely, for a nondegenerate triangle
`∡ABC ≡ -∡BAC` forces `CA = CB`. -/
@[kb "petrunin2025" "Theorem 4.2, p. 32"]
theorem petrunin_4_2 {A B C : P} :
    (dist C A = dist C B → ∡ A B C = -∡ B A C) ∧
    (¬Collinear ℝ ({A, B, C} : Set P) → ∡ A B C = -∡ B A C → dist C A = dist C B) := by
  refine ⟨fun h => ?_, fun hnc h => ?_⟩
  · rw [EuclideanGeometry.oangle_rev C A B, neg_neg]
    exact (EuclideanGeometry.oangle_eq_oangle_of_dist_eq h).symm
  · have hAB : A ≠ B := ne₁₂_of_not_collinear hnc
    have hCB : C ≠ B := (ne₂₃_of_not_collinear hnc).symm
    have hCA : C ≠ A := (ne₁₃_of_not_collinear hnc).symm
    have h1 : ∡ C A B = ∡ A B C := by
      rw [h, EuclideanGeometry.oangle_rev C A B, neg_neg]
    have h2 : ∠ C A B = ∠ C B A := by
      rw [EuclideanGeometry.angle_eq_abs_oangle_toReal hCA hAB.symm,
        EuclideanGeometry.angle_eq_abs_oangle_toReal hCB hAB, h1,
        EuclideanGeometry.oangle_rev A B C, Real.Angle.abs_toReal_neg]
    have hnc' : ¬Collinear ℝ ({A, C, B} : Set P) := by
      intro hc; apply hnc
      have e : ({A, C, B} : Set P) = {A, B, C} := by ext; simp; tauto
      rwa [e] at hc
    exact EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi h2
      (EuclideanGeometry.angle_lt_pi_of_not_collinear hnc').ne

end Ch4Oriented

end UndergradKB.Geometry.Course
