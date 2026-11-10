import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import UndergradKB.Common.Attr

/-! # Angle bisectors (Petrunin, chapter 8D)

The angle bisector theorem (Lemma 8.11) and its consequence that a bisector which bisects the opposite
side forces an isosceles triangle (Exercise 8.13). The book works in the Euclidean plane with signed angles;
"the bisector of the angle at `A` meets `[BC]` at `D`" means `D` lies on the segment `[BC]` and the
unsigned angles `∠BAD` and `∠DAC` are equal (for a point of the segment the two signed angles have the same
sign, so this is the book's condition `∡BAD ≡ -∡CAD`). The statements hold in every real inner product
space, in particular in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`. -/

namespace UndergradKB.Geometry

open EuclideanGeometry Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- If `D` on `[BC]` makes equal angles with `AB` and `AC`, then `D` lies strictly between `B` and `C`
and the half-angle at `A` has positive sine. -/
theorem bisector_foot_aux {A B C D : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hD : Wbtw ℝ B D C) (hbis : ∠ B A D = ∠ D A C) :
    Sbtw ℝ B D C ∧ 0 < Real.sin (∠ B A D) ∧ ∠ B A D + ∠ D A C = ∠ B A C := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear h
  have hAC : A ≠ C := ne₁₃_of_not_collinear h
  have hsum : ∠ B A D + ∠ D A C = ∠ B A C := angle_add_of_ne_of_ne hAB hAC hD
  have h' : ¬Collinear ℝ ({B, A, C} : Set P) := by rwa [Set.insert_comm]
  have hpos : 0 < ∠ B A C := angle_pos_of_not_collinear h'
  have hlt : ∠ B A C < π := angle_lt_pi_of_not_collinear h'
  refine ⟨⟨hD, ?_, ?_⟩, ?_, hsum⟩
  · rintro rfl
    rw [angle_self_of_ne hAB.symm] at hbis
    linarith
  · rintro rfl
    rw [angle_self_of_ne hAC.symm] at hbis
    linarith
  · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith

/-- **Angle bisector theorem** (Petrunin, Lemma 8.11): in a nondegenerate triangle `ABC`, if the bisector
at `A` meets `[BC]` at `D`, then `AB / AC = DB / DC`. -/
@[kb "petrunin2025" "Lemma 8.11, p. 61"]
theorem angle_bisector_theorem {A B C D : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hD : Wbtw ℝ B D C) (hbis : ∠ B A D = ∠ D A C) :
    dist A B / dist A C = dist D B / dist D C := by
  obtain ⟨hs, hsin, -⟩ := bisector_foot_aux h hD hbis
  have hAC : A ≠ C := ne₁₃_of_not_collinear h
  have hDC : D ≠ C := hs.ne_right
  have hpi : ∠ B D C = π := hs.angle₁₂₃_eq_pi
  have hsupp := angle_add_angle_eq_pi_of_angle_eq_pi A hpi
  have hsinD : Real.sin (∠ A D B) = Real.sin (∠ A D C) := by
    rw [show ∠ A D B = π - ∠ A D C by linarith, Real.sin_pi_sub]
  have h1 := law_sin D A B
  have h2 := law_sin D A C
  rw [angle_comm D A B, angle_comm B D A, hsinD] at h1
  rw [← hbis, angle_comm C D A] at h2
  have hACpos : dist A C ≠ 0 := dist_ne_zero.mpr hAC
  have hDCpos : dist D C ≠ 0 := dist_ne_zero.mpr hDC
  rw [div_eq_div_iff hACpos hDCpos]
  apply mul_left_cancel₀ hsin.ne'
  rw [dist_comm B D, dist_comm C D] at *
  linear_combination (dist D C) * h1 - (dist D B) * h2

/-- Petrunin, Exercise 8.13: if the bisector at `A` of a nondegenerate triangle `ABC` meets `[BC]` at its
midpoint, then the triangle is isosceles, `AB = AC`. -/
@[kb "petrunin2025" "Exercise 8.13, p. 62"]
theorem isosceles_of_bisector_bisects {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hbis : ∠ B A (midpoint ℝ B C) = ∠ (midpoint ℝ B C) A C) :
    dist A B = dist A C := by
  have hD : Wbtw ℝ B (midpoint ℝ B C) C := wbtw_midpoint ℝ B C
  have key := angle_bisector_theorem h hD hbis
  have hAC : A ≠ C := ne₁₃_of_not_collinear h
  have hBC : B ≠ C := ne₂₃_of_not_collinear h
  have hm : dist (midpoint ℝ B C) B = dist (midpoint ℝ B C) C := by
    rw [dist_comm, dist_left_midpoint, dist_midpoint_right]
  have hne : dist (midpoint ℝ B C) C ≠ 0 := by
    refine dist_ne_zero.mpr fun h => hBC ?_
    rwa [midpoint_eq_right_iff] at h
  rw [hm, div_self hne, div_eq_one_iff_eq (dist_ne_zero.mpr hAC)] at key
  exact key

end UndergradKB.Geometry
