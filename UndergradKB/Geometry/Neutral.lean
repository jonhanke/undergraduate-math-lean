import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import UndergradKB.Geometry.Axioms
import UndergradKB.Geometry.Motions
import UndergradKB.Common.Attr

/-! # The neutral plane (Petrunin, Section 2A and Chapter 11)

Petrunin's axiomatic plane (Section 2A, p. 19) is a metric space with an angle measure satisfying
Axioms I-V. Removing Axiom V gives the *neutral* (absolute) plane (Chapter 11, p. 83). We record the
axioms as a structure `NeutralPlane` on a metric space, with the angle measure valued in
`Real.Angle` (the book's measure in `(-π, π]` is `Real.Angle.toReal`, and the book's `≡` is equality
in `Real.Angle`). Axiom V and the hyperbolic axiom h-V (p. 88) are predicates on a neutral plane.

The Euclidean plane (an oriented two-dimensional real inner product space with the oriented angle
`∡`) is a neutral plane satisfying Axiom V (`euclideanNeutralPlane`, `euclideanNeutralPlane_axiomV`).
-/

namespace UndergradKB.Geometry

open EuclideanGeometry

section Defs

variable (P : Type*) [MetricSpace P]

/-- The book's half-line `[OA)` in a metric space (p. 13): the points `f t`, `t ≥ 0`, for an isometry
`f : ℝ → P` with `f 0 = O` and `A = f q` for some `q > 0`. (Wave 1's `HalfLine` is the same set,
stated for normed torsors; see `metricHalfLine_eq_halfLine`.) -/
def metricHalfLine {P : Type*} [MetricSpace P] (O A : P) : Set P :=
  {X | ∃ f : ℝ → P, Isometry f ∧ f 0 = O ∧ (∃ q : ℝ, 0 < q ∧ f q = A) ∧ ∃ t : ℝ, 0 ≤ t ∧ f t = X}

/-- A *triangle* `ABC` (Section 1J, p. 16) is an ordered triple of distinct points of a metric space; it may be
degenerate (Mathlib's `Affine.Triangle` excludes this, so the book's notion is recorded here). -/
@[kb "petrunin2025" "Definition of a triangle, Section 1J, p. 16"]
def IsTriangle {P : Type*} [MetricSpace P] (A B C : P) : Prop := A ≠ B ∧ B ≠ C ∧ C ≠ A

/-- A triangle is *degenerate* (p. 21) if its vertices lie on one line (a subset isometric to `ℝ`). -/
@[kb "petrunin2025" "Degenerate triangle, p. 21"]
def IsTriangle.Degenerate {P : Type*} [MetricSpace P] (A B C : P) : Prop :=
  ∃ L : Set P, IsLine L ∧ A ∈ L ∧ B ∈ L ∧ C ∈ L

/-- Triangles `ABC` and `A'B'C'` are congruent (Section 1J, p. 16) if some motion of the plane
(a distance-preserving bijection) maps `A, B, C` to `A', B', C'`. -/
def TriangleCongruent {P : Type*} [MetricSpace P] (A B C A' B' C' : P) : Prop :=
  ∃ f : P ≃ᵢ P, f A = A' ∧ f B = B' ∧ f C = C'

/-- **Neutral plane (Chapter 11, p. 83).** Petrunin's Axioms I-IV (Section 2A, p. 19) on a metric
space `P`, with angle measure `angle A O B` (the book's `∡AOB`, here in `Real.Angle`):
I. at least two points; II. a unique line (a subset isometric to `ℝ`) through two distinct points;
IIIa. a unique half-line at a given angle from a given half-line (the measure is that of the angle, i.e. it
depends only on the half-lines: field `axiomIII_halfLine`); IIIb. angles add;
IIIc. continuity of the angle measure away from straight angles; IV. side-angle-side congruence
(triangles have distinct vertices; congruence is by a motion of the plane). -/
@[kb "petrunin2025" "Definition of the neutral plane, p. 83; Axioms I-IV, p. 19"]
structure NeutralPlane where
  /-- The angle measure `∡AOB`. -/
  angle : P → P → P → Real.Angle
  axiomI : ∃ A B : P, A ≠ B
  axiomII : ∀ A B : P, A ≠ B → ∃! L : Set P, IsLine L ∧ A ∈ L ∧ B ∈ L
  axiomIIIa : ∀ O A : P, A ≠ O → ∀ α : Real.Angle,
    ∃ B : P, B ≠ O ∧ angle A O B = α ∧ ∀ B' : P, B' ≠ O → angle A O B' = α → B' ∈ metricHalfLine O B
  /-- Axiom III speaks of the measure `∡AOB` of the *angle* `∠AOB`, the pair of half-lines `[OA)`, `[OB)`
  (Section 1G): the measure does not change when `A` is replaced by another point `A' ≠ O` of `[OA)`. -/
  axiomIII_halfLine : ∀ O A A' B : P, A ≠ O → A' ∈ metricHalfLine O A → A' ≠ O → B ≠ O →
    angle A' O B = angle A O B
  axiomIIIb : ∀ O A B C : P, A ≠ O → B ≠ O → C ≠ O → angle A O B + angle B O C = angle A O C
  axiomIIIc : ∀ A O B : P, A ≠ O → B ≠ O → angle A O B ≠ (Real.pi : Real.Angle) →
    ContinuousAt (fun x : P × P × P => angle x.1 x.2.1 x.2.2) (A, O, B)
  axiomIV : ∀ A B C A' B' C' : P, A ≠ B → B ≠ C → C ≠ A → A' ≠ B' → B' ≠ C' → C' ≠ A' →
    (TriangleCongruent A B C A' B' C' ↔
      dist A' B' = dist A B ∧ dist A' C' = dist A C ∧
        (angle C' A' B' = angle C A B ∨ angle C' A' B' = -angle C A B))

variable {P}

/-- **Axiom V (p. 19)** for a neutral plane: scaling the two sides of a triangle at a vertex by
`k > 0` scales the third side by `k` and keeps the other two angles. -/
@[kb "petrunin2025" "Axiom V, p. 19"]
def NeutralPlane.AxiomV (N : NeutralPlane P) : Prop :=
  ∀ A B C B' C' : P, ∀ k : ℝ, 0 < k → A ≠ B → A ≠ C → B ≠ C →
    B' ∈ metricHalfLine A B → C' ∈ metricHalfLine A C → dist A B' = k * dist A B →
      dist A C' = k * dist A C →
        dist B' C' = k * dist B C ∧ N.angle A B C = N.angle A B' C' ∧ N.angle A C B = N.angle A C' B'

/-- Two lines are *parallel* (p. 53) if they are equal or disjoint; here, for a point off a line,
a line through it is parallel iff it misses the line. -/
def IsLine.ParallelThrough {P : Type*} [MetricSpace P] (ℓ m : Set P) (Q : P) : Prop :=
  IsLine m ∧ Q ∈ m ∧ Disjoint ℓ m

/-- **Axiom h-V (p. 88)**: for every line `ℓ` and point `Q ∉ ℓ` there are at least two lines through
`Q` parallel to `ℓ`. A neutral plane satisfying it is a *hyperbolic plane*. -/
@[kb "petrunin2025" "Axiom h-V, p. 88"]
def NeutralPlane.AxiomHV (_N : NeutralPlane P) : Prop :=
  ∀ ℓ : Set P, IsLine ℓ → ∀ Q : P, Q ∉ ℓ →
    ∃ m m' : Set P, m ≠ m' ∧ IsLine.ParallelThrough ℓ m Q ∧ IsLine.ParallelThrough ℓ m' Q

end Defs

section Basic

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

/-- **Proposition 2.4 (p. 20)**, neutral: `∡AOA = 0`. -/
@[kb "petrunin2025" "Proposition 2.4, p. 20"]
theorem NeutralPlane.angle_self {A O : P} (hA : A ≠ O) : N.angle A O A = 0 := by
  have h := N.axiomIIIb O A A A hA hA hA
  simpa using h

/-- **Proposition 2.6 (p. 20)**, neutral: `∡AOB ≡ -∡BOA`. -/
@[kb "petrunin2025" "Proposition 2.6, p. 20"]
theorem NeutralPlane.angle_rev {A B O : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.angle A O B = -N.angle B O A := by
  have h := N.axiomIIIb O A B A hA hB hA
  rw [N.angle_self hA] at h
  exact eq_neg_of_add_eq_zero_left h

end Basic

section Euclidean

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The metric half-line agrees with wave 1's `HalfLine` in a normed torsor. -/
theorem metricHalfLine_eq_halfLine (O A : P) : metricHalfLine O A = HalfLine O A := rfl

/-- In a Euclidean space, a triangle (distinct vertices) is degenerate in the book's sense iff its
vertices are collinear. -/
@[kb "petrunin2025" "Degenerate triangle, p. 21"]
theorem IsTriangle.degenerate_iff_collinear {A B C : P} (h : IsTriangle A B C) :
    IsTriangle.Degenerate A B C ↔ Collinear ℝ {A, B, C} := by
  constructor
  · rintro ⟨L, hL, hA, hB, hC⟩
    obtain ⟨X, Y, hXY, rfl⟩ := (isLine_iff_exists_affineSpan (V := V)).1 hL
    exact collinear_triple_of_mem_affineSpan_pair hA hB hC
  · intro hcol
    refine ⟨line[ℝ, A, B], (isLine_iff_exists_affineSpan (V := V)).2 ⟨A, B, h.1, rfl⟩,
      left_mem_affineSpan_pair ℝ A B, right_mem_affineSpan_pair ℝ A B, ?_⟩
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h.1

variable [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
/-- In a triangle the unsigned angle at a vertex is determined by the three sides (law of cosines). -/
private lemma angle_eq_of_dist_eq {A B C A' B' C' : P} (hB : B ≠ A) (hC : C ≠ A)
    (h1 : dist B' A' = dist B A) (h2 : dist C' A' = dist C A) (h3 : dist B' C' = dist B C) :
    ∠ B' A' C' = ∠ B A C := by
  have l1 := law_cos B A C
  have l2 := law_cos B' A' C'
  rw [h1, h2, h3] at l2
  have hpos : 0 < dist B A * dist C A := mul_pos (dist_pos.2 hB) (dist_pos.2 hC)
  have key : (dist B A * dist C A) * (Real.cos (∠ B' A' C') - Real.cos (∠ B A C)) = 0 := by
    linarith
  have hcos : Real.cos (∠ B' A' C') = Real.cos (∠ B A C) := by
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h hpos.ne'
    · linarith
  exact Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ hcos

/-- **The Euclidean plane is a neutral plane** (Chapter 11, p. 83: "the Euclidean plane is an example
of a neutral plane"): an oriented two-dimensional Euclidean affine plane with the oriented angle `∡`
satisfies Axioms I-IV. -/
@[kb "petrunin2025" "Chapter 11, p. 83"]
noncomputable def euclideanNeutralPlane : NeutralPlane P where
  angle A O B := ∡ A O B
  axiomI := by
    have : Module.finrank ℝ V = 2 := Fact.out
    have hV : Nontrivial V := Module.nontrivial_of_finrank_eq_succ this
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨p⟩ := (inferInstance : Nonempty P)
    refine ⟨p, v +ᵥ p, fun h => hv ?_⟩
    have := congrArg (· -ᵥ p) h
    simpa using this.symm
  axiomII A B h := existsUnique_isLine (V := V) h
  axiomIIIa O A hA α := by
    obtain ⟨B, hB, hang, huniq⟩ := exists_unique_halfLine_oangle (V := V) hA α
    refine ⟨B, hB, hang, fun B' hB' h' => ?_⟩
    rw [metricHalfLine_eq_halfLine, halfLine_eq hB.symm]
    have hsr := huniq B' hB' h'
    obtain ⟨r, hr, hrv⟩ := hsr.symm.exists_nonneg_left (vsub_ne_zero.2 hB)
    exact ⟨r, hr, by rw [AffineMap.lineMap_apply, hrv, vsub_vadd]⟩
  axiomIII_halfLine O A A' B hA hA' hA'O _ := by
    rw [metricHalfLine_eq_halfLine, halfLine_eq hA.symm] at hA'
    obtain ⟨t, ht, rfl⟩ := hA'
    have ht0 : 0 < t := by
      rcases ht.lt_or_eq with h | h
      · exact h
      · subst h; simp at hA'O
    simp only [EuclideanGeometry.oangle, AffineMap.lineMap_vsub_left]
    exact (o).oangle_smul_left_of_pos _ _ ht0
  axiomIIIb O A B C hA hB hC := oangle_add hA hB hC
  axiomIIIc A O B hA hB _ := continuousAt_oangle (x := (A, O, B)) hA hB
  axiomIV A B C A' B' C' hAB hBC hCA hAB' hBC' hCA' := by
    unfold TriangleCongruent
    rw [← sides_eq_iff_exists_motion (V := V)]
    have e : ∀ X Y X' Y' : P, dist X Y = dist X' Y' → dist Y X = dist Y' X' := fun X Y X' Y' h => by
      rw [dist_comm, h, dist_comm]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1.symm, (e _ _ _ _ h3).symm, ?_⟩
      have hang : ∠ C' A' B' = ∠ C A B :=
        angle_eq_of_dist_eq (V := V) hCA hAB.symm h3.symm (e _ _ _ _ h1).symm (e _ _ _ _ h2).symm
      exact oangle_eq_or_eq_neg_of_angle_eq hang hCA'.symm hAB' hCA.symm hAB
    · rintro ⟨h1, h2, h3⟩
      have hang : ∠ C' A' B' = ∠ C A B := by
        rw [angle_eq_abs_oangle_toReal hCA' hAB'.symm, angle_eq_abs_oangle_toReal hCA hAB.symm]
        rcases h3 with h3 | h3 <;> rw [h3]
        exact Real.Angle.abs_toReal_neg _
      refine ⟨h1.symm, ?_, (e _ _ _ _ h2).symm⟩
      have l1 := law_cos C A B
      have l2 := law_cos C' A' B'
      rw [e _ _ _ _ h2, e _ _ _ _ h1, hang] at l2
      have hsq : dist C' B' * dist C' B' = dist C B * dist C B := by rw [l2, l1]
      have := (mul_self_inj dist_nonneg dist_nonneg).1 hsq
      exact (e _ _ _ _ this).symm

/-- The angle measure of `euclideanNeutralPlane` is the oriented angle. -/
theorem euclideanNeutralPlane_angle (A O B : P) :
    (euclideanNeutralPlane (V := V)).angle A O B = ∡ A O B := rfl

/-- **The Euclidean plane satisfies Axiom V (p. 19)**, so it is a Euclidean (not only neutral) plane. -/
@[kb "petrunin2025" "Axiom V, p. 19"]
theorem euclideanNeutralPlane_axiomV : (euclideanNeutralPlane (V := V) (P := P)).AxiomV := by
  intro A B C B' C' k hk hAB hAC _ hB' hC' hdB hdC
  rw [metricHalfLine_eq_halfLine, halfLine_eq hAB] at hB'
  rw [metricHalfLine_eq_halfLine, halfLine_eq hAC] at hC'
  obtain ⟨h1, h2, h3, -⟩ := axiomV hk hAB hAC hB' hC' hdB hdC
  refine ⟨h1, h2, ?_⟩
  simp only [euclideanNeutralPlane_angle] at *
  rw [oangle_rev B C A, oangle_rev B' C' A, h3]

end Euclidean

end UndergradKB.Geometry
