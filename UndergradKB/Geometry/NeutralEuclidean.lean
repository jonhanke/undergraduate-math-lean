import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Congruence
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import UndergradKB.Common.Attr

/-! # Neutral-plane results of chapter 11, in the Euclidean plane (Petrunin, chapter 11)

The book proves these statements in a *neutral* plane (without the parallel axiom). Here they are proved
for the Euclidean case, i.e. in any real inner product space (resp. oriented 2-dimensional one for signed
angles); each docstring repeats this. Covered: the hinge proposition 11.9, hypotenuse-leg (Theorem 11.1),
Exercise 11.6 and the defect of a triangle (11.12, p. 87). -/

namespace UndergradKB.Geometry

open EuclideanGeometry Real
open scoped Affine

section Unoriented

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Hinge proposition** (Petrunin, Proposition 11.9; the book proves it in the neutral plane, this is
the Euclidean case via the law of cosines): if `AC = A'C'` and `BC = B'C'` (the triangles being
nondegenerate at `C`, i.e. these lengths are nonzero), then `AB < A'B'` iff `∠ACB < ∠A'C'B'`.
The unoriented angle is the book's `|∡ACB|`. -/
@[kb "petrunin2025" "Proposition 11.9, p. 85"]
theorem hinge_dist_lt_iff_angle_lt {A B C A' B' C' : P} (hAC : A ≠ C) (hBC : B ≠ C)
    (h₁ : dist A C = dist A' C') (h₂ : dist B C = dist B' C') :
    dist A B < dist A' B' ↔ ∠ A C B < ∠ A' C' B' := by
  have hA : 0 < dist A C := dist_pos.mpr hAC
  have hB : 0 < dist B C := dist_pos.mpr hBC
  have l1 := law_cos A C B
  have l2 := law_cos A' C' B'
  rw [← h₁, ← h₂] at l2
  have hk : 0 < 2 * dist A C * dist B C := by positivity
  have key : dist A B < dist A' B' ↔ dist A B ^ 2 < dist A' B' ^ 2 :=
    (pow_lt_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).symm
  rw [key, pow_two, pow_two, l1, l2]
  have hcos : Real.cos (∠ A' C' B') < Real.cos (∠ A C B) ↔ ∠ A C B < ∠ A' C' B' :=
    Real.strictAntiOn_cos.lt_iff_gt ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
      ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
  rw [← hcos]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Hypotenuse-leg congruence** (Petrunin, Theorem 11.1; the book proves it in the neutral plane, this
is the Euclidean case via Pythagoras): two triangles with a right angle at `C`, `C'`, equal
hypotenuses `AB = A'B'` and one equal leg `AC = A'C'` are congruent. -/
@[kb "petrunin2025" "Theorem 11.1, p. 83"]
theorem hypotenuse_leg {A B C A' B' C' : P} (h : ∠ A C B = π / 2) (h' : ∠ A' C' B' = π / 2)
    (hyp : dist A B = dist A' B') (leg : dist A C = dist A' C') :
    Congruent ![A, B, C] ![A', B', C'] := by
  have p1 := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A C B).mpr h
  have p2 := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two A' C' B').mpr h'
  have hBC : dist B C = dist B' C' := by
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg]
    rw [hyp, leg] at p1
    nlinarith
  exact side_side_side hyp hBC (by rw [dist_comm C A, dist_comm C' A', leg])

/-- The **defect** of a triangle `ABC` (Petrunin, p. 87): `π` minus the sum of its three (unoriented)
angles. In the neutral plane it is a nonnegative number; in the Euclidean plane it is zero
(`defect_eq_zero`). -/
noncomputable def defect (A B C : P) : ℝ := π - (∠ A B C + ∠ B C A + ∠ C A B)

/-- In the Euclidean plane every triangle has zero defect (angle sum `π`). -/
@[kb "petrunin2025" "Definition of defect, p. 87"]
theorem defect_eq_zero {A B C : P} (h : B ≠ A) : defect A B C = 0 := by
  unfold defect
  rw [angle_add_angle_add_angle_eq_pi C h]
  ring

/-- **Additivity of the defect** (Petrunin, Classroom exercise 11.12, p. 87; the book proves it in the
neutral plane, this is the Euclidean case, where both sides are zero anyway, but the direct angle
computation is used and does not invoke the angle sum): if `D` lies strictly between `B` and `C` and `A`
differs from `B` and `C`, then `defect ABC = defect ABD + defect ADC`. -/
@[kb "petrunin2025" "Classroom exercise 11.12, p. 87"]
theorem defect_add_of_sbtw {A B C D : P} (hAB : A ≠ B) (hAC : A ≠ C) (hD : Sbtw ℝ B D C) :
    defect A B C = defect A B D + defect A D C := by
  unfold defect
  have e1 : ∠ A B D = ∠ A B C := hD.angle_eq_right A
  have e2 : ∠ A C D = ∠ A C B := hD.symm.angle_eq_right A
  have e3 : ∠ A D B + ∠ A D C = π := angle_add_angle_eq_pi_of_angle_eq_pi A hD.angle₁₂₃_eq_pi
  have e4 : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_ne_of_ne hAB hAC hD.wbtw
  have c1 := angle_comm B D A
  have c2 := angle_comm D A B
  have c3 := angle_comm C A D
  have c4 := angle_comm D C A
  have c5 := angle_comm C A B
  have c6 := angle_comm B C A
  linarith

end Unoriented

section Oriented

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Exercise 11.6** (Petrunin, p. 85; the book works in the neutral plane, this is the Euclidean plane):
if `2·∡ABC + 2·∡BCD = 0` (with `A ≠ B`, `B ≠ C`, `C ≠ D`, so that the lines are defined), then the lines
`(AB)` and `(CD)` are parallel. -/
@[kb "petrunin2025" "Exercise 11.6, p. 85"]
theorem parallel_of_two_zsmul_oangle_add {A B C D : P} (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D)
    (h : (2 : ℤ) • ∡ A B C + (2 : ℤ) • ∡ B C D = 0) :
    line[ℝ, A, B] ∥ line[ℝ, C, D] := by
  apply parallel_of_two_zsmul_oangle hAB hBC hCD
  rw [oangle_rev B C D]
  have : (2 : ℤ) • ∡ A B C = -((2 : ℤ) • ∡ B C D) := eq_neg_of_add_eq_zero_left h
  rw [this, smul_neg]

end Oriented

end UndergradKB.Geometry
