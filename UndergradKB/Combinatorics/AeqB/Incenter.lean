import Mathlib.Geometry.Euclidean.Angle.Incenter
import UndergradKB.Common.Attr

/-!
# The angle bisectors of a triangle are concurrent (A = B, Theorem 1.4.2 setting)

Mathlib defines the incenter of a simplex and proves it bisects the angle at each vertex.  We
package this as concurrency of the three internal angle bisectors.
-/

namespace UndergradKB.Combinatorics.AeqB

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- CO-348. The three internal angle bisectors of a triangle meet in one point, the incenter `I`,
which lies in the interior of the triangle: for every vertex `A_{i₁}` with the other vertices
`A_{i₂}, A_{i₃}`, the angle `∠ A_{i₂} A_{i₁} I` equals `∠ I A_{i₁} A_{i₃}` and both are half of the
angle of the triangle at `A_{i₁}`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 1.4.2, p. 20"]
theorem angle_bisectors_concurrent (t : Affine.Triangle ℝ P) :
    ∃ I : P, I ∈ t.interior ∧ ∀ i₁ i₂ i₃ : Fin 3, i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ →
      ∠ (t.points i₂) (t.points i₁) I = ∠ (t.points i₂) (t.points i₁) (t.points i₃) / 2 ∧
      ∠ (t.points i₂) (t.points i₁) I = ∠ I (t.points i₁) (t.points i₃) :=
  ⟨t.incenter, t.incenter_mem_interior, fun _ _ _ h₁₂ h₁₃ h₂₃ =>
    ⟨t.angle_incenter_eq_angle_div_two h₁₂ h₁₃ h₂₃, t.angle_incenter h₁₂ h₁₃ h₂₃⟩⟩

end UndergradKB.Combinatorics.AeqB
