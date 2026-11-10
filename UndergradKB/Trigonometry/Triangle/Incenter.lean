import Mathlib.Geometry.Euclidean.Incenter.Basic
import Mathlib.Geometry.Euclidean.Triangle
import UndergradKB.Common.Attr

/-! # The incenter lies on the angle bisectors (Corral §2.5)

Mathlib defines the incenter of a simplex (`Affine.Simplex.incenter`, through barycentric weights) and its
touchpoints with the faces. Corral §2.5 introduces the incenter as the common point of the three interior
angle bisectors. We prove that Mathlib's incenter lies on each of them: the line from a vertex to the incenter
makes equal angles with the two sides at that vertex.

Proof: the two touchpoints on the sides through the vertex `A` are at the same distance from `A` (equal
tangent lengths, `EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem`) and at the same distance `r`
from the incenter `I`; by the law of cosines the angles at `A` of the two triangles `A T I` are equal, and
each touchpoint lies strictly inside its side, so these are the angles between the sides and `AI`.
-/

namespace UndergradKB.Trigonometry

open EuclideanGeometry
open scoped EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **The incenter is on the bisector of each angle**: for a triangle and its vertex `i₁`, the line from the
vertex to the incenter makes equal angles with the two sides through the vertex. Hence the incenter is the
common point of the three angle bisectors. (TR-096) -/
@[kb "corraltrig" "Box §2.5 (incenter on the angle bisectors), p. 70"]
theorem angle_points_incenter_eq (t : Affine.Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ∠ (t.points i₂) (t.points i₁) t.incenter = ∠ t.incenter (t.points i₁) (t.points i₃) := by
  set A := t.points i₁
  set I := t.incenter
  -- the touchpoints on the sides `A i₃` (opposite `i₂`) and `A i₂` (opposite `i₃`)
  set T₂ := t.touchpoint ∅ i₂
  set T₃ := t.touchpoint ∅ i₃
  have hs₂ : Sbtw ℝ A T₂ (t.points i₃) := t.sbtw_touchpoint_empty h₁₂ h₁₃ h₂₃
  have hs₃ : Sbtw ℝ A T₃ (t.points i₂) := t.sbtw_touchpoint_empty h₁₃ h₁₂ h₂₃.symm
  have hA₂ : A ∈ affineSpan ℝ (Set.range (t.faceOpposite i₂).points) := by
    rw [Affine.Simplex.range_faceOpposite_points]
    exact subset_affineSpan ℝ _ ⟨i₁, h₁₂, rfl⟩
  have hA₃ : A ∈ affineSpan ℝ (Set.range (t.faceOpposite i₃).points) := by
    rw [Affine.Simplex.range_faceOpposite_points]
    exact subset_affineSpan ℝ _ ⟨i₁, h₁₃, rfl⟩
  have htan : dist A T₂ = dist A T₃ :=
    (t.isTangentAt_insphere_touchpoint i₂).dist_eq_of_mem_of_mem
      (t.isTangentAt_insphere_touchpoint i₃) hA₂ hA₃
  have hr : dist I T₂ = dist I T₃ := by
    rw [t.dist_incenter i₂, t.dist_incenter i₃]
  have hAT₂ : A ≠ T₂ := hs₂.left_ne
  have hAI : I ≠ A := t.incenter_ne_point i₁
  -- law of cosines in the triangles `T₂ A I` and `T₃ A I`
  have hc₂ := law_cos T₂ A I
  have hc₃ := law_cos T₃ A I
  rw [dist_comm T₂ A, dist_comm T₃ A, ← htan, dist_comm T₂ I, dist_comm T₃ I, ← hr] at *
  have hpos : 0 < dist A T₂ * dist I A := mul_pos (dist_pos.2 hAT₂) (dist_pos.2 hAI)
  have hcos : Real.cos (∠ T₂ A I) = Real.cos (∠ T₃ A I) := by
    have : 2 * (dist A T₂ * dist I A) * (Real.cos (∠ T₂ A I) - Real.cos (∠ T₃ A I)) = 0 := by
      linear_combination hc₂ - hc₃
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · linarith
  have hang : ∠ T₂ A I = ∠ T₃ A I :=
    Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
      hcos
  rw [← hs₃.angle_eq_left I, ← hang, hs₂.angle_eq_left I, angle_comm]

end UndergradKB.Trigonometry
