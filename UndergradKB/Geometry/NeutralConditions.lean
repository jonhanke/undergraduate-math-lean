import UndergradKB.Geometry.Neutral
import UndergradKB.Common.Attr

/-! # The conditions of Theorem 11.16 (Petrunin, Chapter 11, pp. 87-88)

The unsigned angle `|∡AOB|`, the defect of a triangle, and the six conditions (a)-(f) of Theorem 11.16, for an
arbitrary neutral plane. They are verified on the two models in `NeutralEquivalents` and proved equivalent to
Axiom V for every neutral plane in `NeutralTheorem1116`. -/

namespace UndergradKB.Geometry

section Conditions

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

/-- The unsigned angle `|∡AOB|` at the vertex `O`. -/
noncomputable def NeutralPlane.uangle (A O B : P) : ℝ := |(N.angle A O B).toReal|

/-- The **defect** of a triangle (p. 87): `π − |∡ABC| − |∡BCA| − |∡CAB|`. -/
@[kb "petrunin2025" "Definition of defect, p. 87"]
noncomputable def NeutralPlane.defect (A B C : P) : ℝ :=
  Real.pi - N.uangle A B C - N.uangle B C A - N.uangle C A B

/-- Condition (a) of Theorem 11.16: some line `ℓ` and some point `Q ∉ ℓ` such that exactly one line passes
through `Q` and is parallel to `ℓ` (does not meet it). -/
@[kb "petrunin2025" "Theorem 11.16 (a), p. 88"]
def NeutralPlane.OnlyOneParallel (_N : NeutralPlane P) : Prop :=
  ∃ ℓ : Set P, IsLine ℓ ∧ ∃ Q : P, Q ∉ ℓ ∧ ∃! m : Set P, IsLine.ParallelThrough ℓ m Q

/-- Condition (b): every nondegenerate triangle can be circumscribed, i.e. its three vertices lie on a
circle `{X | dist O X = r}`. -/
@[kb "petrunin2025" "Theorem 11.16 (b), p. 88"]
def NeutralPlane.AllTrianglesCircumscribable (_N : NeutralPlane P) : Prop :=
  ∀ A B C : P, IsTriangle A B C → ¬ IsTriangle.Degenerate A B C →
    ∃ (O : P) (r : ℝ), dist O A = r ∧ dist O B = r ∧ dist O C = r

/-- Condition (c): two distinct lines at bounded distance from each other: every point of `ℓ` is within
`C` of a point of `m`. -/
@[kb "petrunin2025" "Theorem 11.16 (c), p. 88"]
def NeutralPlane.BoundedDistantLines (_N : NeutralPlane P) : Prop :=
  ∃ ℓ m : Set P, IsLine ℓ ∧ IsLine m ∧ ℓ ≠ m ∧ ∃ C : ℝ, ∀ X ∈ ℓ, ∃ Y ∈ m, dist X Y ≤ C

/-- `I` lies strictly inside the triangle `ABC`: the three oriented angles `∡AIB`, `∡BIC`, `∡CIA` have the
same nonzero sign (they then add up to `2π`; this is the angle sum used in the book's proof of Theorem 13.6). -/
def NeutralPlane.InteriorPoint (A B C I : P) : Prop :=
  (N.angle A I B).sign = (N.angle B I C).sign ∧ (N.angle B I C).sign = (N.angle C I A).sign ∧
    (N.angle A I B).sign ≠ 0

/-- The triangle `ABC` has inradius at least `r`: some interior point `I` is at distance `≥ r` from all
points of the three side lines, so the disc of radius `r` about `I` lies in the triangle. -/
def NeutralPlane.InradiusGE (A B C : P) (r : ℝ) : Prop :=
  ∃ I : P, N.InteriorPoint A B C I ∧ ∀ L : Set P, IsLine L →
    ((A ∈ L ∧ B ∈ L) ∨ (B ∈ L ∧ C ∈ L) ∨ (C ∈ L ∧ A ∈ L)) → ∀ X ∈ L, r ≤ dist I X

/-- Condition (d): triangles of arbitrarily large inradius. -/
@[kb "petrunin2025" "Theorem 11.16 (d), p. 88"]
def NeutralPlane.ArbitrarilyLargeInradius : Prop :=
  ∀ r : ℝ, ∃ A B C : P, IsTriangle A B C ∧ ¬ IsTriangle.Degenerate A B C ∧ N.InradiusGE A B C r

/-- Condition (e): a nondegenerate triangle with zero defect. -/
@[kb "petrunin2025" "Theorem 11.16 (e), p. 88"]
def NeutralPlane.ZeroDefectTriangle : Prop :=
  ∃ A B C : P, IsTriangle A B C ∧ ¬ IsTriangle.Degenerate A B C ∧ N.defect A B C = 0

/-- A rectangle: a quadrangle (four distinct points) with right angles at `B`, `C`, `D`, `A`. -/
def NeutralPlane.IsRectangle (A B C D : P) : Prop :=
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    N.uangle A B C = Real.pi / 2 ∧ N.uangle B C D = Real.pi / 2 ∧
    N.uangle C D A = Real.pi / 2 ∧ N.uangle D A B = Real.pi / 2

/-- Condition (f): there is a rectangle. -/
@[kb "petrunin2025" "Theorem 11.16 (f), p. 88"]
def NeutralPlane.HasRectangle : Prop := ∃ A B C D : P, N.IsRectangle A B C D

end Conditions

end UndergradKB.Geometry
