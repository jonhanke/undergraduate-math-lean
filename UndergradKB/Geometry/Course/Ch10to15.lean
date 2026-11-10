import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Affine.Ceva
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import UndergradKB.Common.Attr

/-! # Course layer: Petrunin chapters 10 to 15

Thin theorems in the book's terms, each proved by the Mathlib lemma named in the checklist.

* Chapter 11 (neutral plane): the two-angle bound (Proposition 11.5) and the angle sum bound of
  Legendre (Theorem 11.10). In the Euclidean plane the angle sum is exactly `π`, which implies both.
* Chapter 12 (hyperbolic plane): the double-argument identities for `ch` and `sh` and the identities
  of Exercise 12.22.
* Chapter 14 (affine geometry): motions are affine (Observation 14.2), the only field automorphism
  of `ℝ` is the identity (Lemma 14.17), Ceva's theorem (Exercise 14.20a, unsigned form).

Items that are only definitions (inversion, polar and pole, stereographic projection, field
automorphisms, the line of Claim 15.17) have no wrapper here. -/

namespace UndergradKB.Geometry.Course

open EuclideanGeometry Real

section Neutral

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Petrunin, Proposition 11.5: in a nondegenerate triangle, two of the angles sum to less than `π`.
Stated for unsigned angles (the book's `|∡CAB| + |∡ABC| < π`) in any real inner product space,
in particular in the Euclidean plane (where it is a consequence of the angle sum). -/
@[kb "petrunin2025" "Proposition 11.5, p. 84"]
theorem petrunin_11_5 {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) :
    ∠ C A B + ∠ A B C < π := by
  have hAB : B ≠ A := (ne₁₂_of_not_collinear h).symm
  have hsum := angle_add_angle_add_angle_eq_pi C hAB
  have h' : ¬Collinear ℝ ({B, C, A} : Set P) := by
    have : ({B, C, A} : Set P) = {A, B, C} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [this]
  have hpos : 0 < ∠ B C A := angle_pos_of_not_collinear h'
  linarith [angle_comm C A B, angle_comm A B C]

/-- Petrunin, Theorem 11.10 (Legendre): the angles of a triangle sum to at most `π`. In the
Euclidean plane the sum is exactly `π` (Mathlib's `angle_add_angle_add_angle_eq_pi`), which is
stronger; here the book's inequality is recorded for unsigned angles. -/
@[kb "petrunin2025" "Theorem 11.10, p. 86"]
theorem petrunin_11_10 {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) :
    ∠ A B C + ∠ B C A + ∠ C A B ≤ π :=
  (angle_add_angle_add_angle_eq_pi C (ne₁₂_of_not_collinear h).symm).le

end Neutral

/-- Petrunin, Exercise 12.22 and the identities used in 12.24: derivatives of `ch` and `sh` and
`(ch x)^2 - (sh x)^2 = 1`. -/
theorem petrunin_12_22 (x : ℝ) :
    HasDerivAt Real.cosh (Real.sinh x) x ∧ HasDerivAt Real.sinh (Real.cosh x) x ∧
      Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 :=
  ⟨Real.hasDerivAt_cosh x, Real.hasDerivAt_sinh x, Real.cosh_sq_sub_sinh_sq x⟩

/-- Petrunin, Statement 12.24: double-argument identities for the hyperbolic functions. -/
@[kb "petrunin2025" "Statement 12.24, p. 102"]
theorem petrunin_12_24 (x : ℝ) :
    Real.cosh (2 * x) = Real.cosh x ^ 2 + Real.sinh x ^ 2 ∧
      Real.sinh (2 * x) = 2 * Real.sinh x * Real.cosh x :=
  ⟨Real.cosh_two_mul x, Real.sinh_two_mul x⟩

section Affine

/-- Petrunin, Observation 14.2: every motion of the Euclidean plane is an affine transformation.
Both readings are given: the motion is an affine map (indeed an affine isometry equivalence), and it
maps each line `(PQ)` onto the line through the image points. -/
@[kb "petrunin2025" "Observation 14.2, p. 114"]
theorem petrunin_14_2 (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) :
    (∃ g : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2), ⇑g = f) ∧
      ∀ P Q : EuclideanSpace ℝ (Fin 2), f '' (line[ℝ, P, Q] : Set _) = line[ℝ, f P, f Q] := by
  refine ⟨⟨f.toRealAffineIsometryEquiv, rfl⟩, fun P Q => ?_⟩
  have h := AffineSubspace.map_span (f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap)
    ({P, Q} : Set (EuclideanSpace ℝ (Fin 2)))
  have e : ⇑f.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap = f := rfl
  simp only [e, Set.image_pair] at h
  rw [← h]
  rfl

/-- Petrunin, Lemma 14.17: a function `f : ℝ → ℝ` with `f 1 = 1`, additive and multiplicative
(no continuity assumed) is the identity. -/
@[kb "petrunin2025" "Lemma 14.17, p. 117"]
theorem petrunin_14_17 (f : ℝ → ℝ) (h1 : f 1 = 1) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmul : ∀ x y, f (x * y) = f x * f y) (x : ℝ) : f x = x := by
  let φ : ℝ →+* ℝ :=
    { toFun := f, map_one' := h1, map_mul' := hmul,
      map_zero' := by simpa using hadd 0 0, map_add' := hadd }
  have : φ = RingHom.id ℝ := Subsingleton.elim _ _
  exact congrArg (fun g : ℝ →+* ℝ => g x) this

/-- Petrunin, Exercise 14.20a (Ceva's theorem), unsigned form. In a nondegenerate triangle `ABC`,
let `A'`, `B'`, `C'` lie on the lines `(BC)`, `(CA)`, `(AB)` (and differ from `C`, `A`, `B`
respectively, so the ratios exist) and let `(AA')`, `(BB')`, `(CC')` pass through a common point `X`.
Then `AC'/BC' * BA'/CA' * CB'/AB' = 1`. -/
@[kb "petrunin2025" "Exercise 14.20a, p. 120"]
theorem petrunin_14_20a {A B C A' B' C' X : EuclideanSpace ℝ (Fin 2)}
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hA' : A' ∈ line[ℝ, B, C]) (hB' : B' ∈ line[ℝ, C, A]) (hC' : C' ∈ line[ℝ, A, B])
    (hA'C : A' ≠ C) (hB'A : B' ≠ A) (hC'B : C' ≠ B)
    (hXA : X ∈ line[ℝ, A, A']) (hXB : X ∈ line[ℝ, B, B']) (hXC : X ∈ line[ℝ, C, C']) :
    dist A C' / dist B C' * (dist B A' / dist C A') * (dist C B' / dist A B') = 1 := by
  let t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A, B, C], hABC⟩
  have key := Affine.Triangle.prod_dist_div_dist_eq_one_of_mem_line_of_mem_line (t := t)
    (p := ![A', B', C']) (p' := X)
    (by intro i; fin_cases i <;> simp [t, hA'C, hB'A, hC'B])
    (by intro i; fin_cases i
        · exact hA'
        · exact hB'
        · exact hC')
    (by intro i; fin_cases i
        · exact hXA
        · exact hXB
        · exact hXC)
  rw [Fin.prod_univ_three] at key
  simp [t] at key
  rw [dist_comm B C', dist_comm C A', dist_comm A B']
  rw [← key]
  ring

end Affine

end UndergradKB.Geometry.Course
