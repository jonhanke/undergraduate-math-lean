import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import UndergradKB.Common.Attr

/-! # Hefferon chapter One (Hefferon-only rows) -/

namespace UndergradKB.LinearAlgebra.Course

open Matrix

/-- A square coefficient matrix is nonsingular iff the system has exactly one solution for every
right-hand side; so a singular matrix never gives exactly one solution. -/
@[kb "hefferon2020" "One.I.3.Remark, p. 41"]
theorem hefferon_One_I_3_Remark {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : (∀ b : n → K, ∃! x : n → K, A *ᵥ x = b) ↔ IsUnit A := by
  rw [← Function.bijective_iff_existsUnique, Function.Bijective,
    Matrix.mulVec_injective_iff_isUnit, Matrix.mulVec_surjective_iff_isUnit, and_self]

/-- Linear Combination Lemma: a linear combination of linear combinations of `v 0, ..., v (n-1)` is
a linear combination of them. -/
@[kb "hefferon2020" "One.III.2.3, p. 67"]
theorem hefferon_One_III_2_3 {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n k : ℕ}
    (v : Fin n → V) (u : Fin k → V) (hu : ∀ i, ∃ a : Fin n → K, u i = ∑ j, a j • v j)
    (c : Fin k → K) : ∃ d : Fin n → K, ∑ i, c i • u i = ∑ j, d j • v j := by
  choose a ha using hu
  refine ⟨fun j => ∑ i, c i * a i j, ?_⟩
  simp only [ha, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/-- A nonzero vector divided by its length has length one. -/
@[kb "hefferon2020" "One.II.2.Normalize, p. 53"]
theorem hefferon_One_II_2_Normalize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} (hv : v ≠ 0) : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 :=
  norm_smul_inv_norm hv

/-- The angle between `u` and `v` is the arccosine of `u ⬝ v / (‖u‖ ‖v‖)`. -/
@[kb "hefferon2020" "One.II.2.7, p. 56"]
theorem hefferon_One_II_2_7 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v : E) :
    InnerProductGeometry.angle u v = Real.arccos (inner ℝ u v / (‖u‖ * ‖v‖)) := rfl

/-- The angle with a zero vector is a right angle. -/
@[kb "hefferon2020" "One.II.2.7, p. 56"]
theorem hefferon_One_II_2_7_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : InnerProductGeometry.angle 0 v = Real.pi / 2 :=
  InnerProductGeometry.angle_zero_left v

/-- The quotient in the angle formula has absolute value at most one (Cauchy-Schwarz), so the
arccosine is defined. -/
@[kb "hefferon2020" "One.II.2.7, p. 56"]
theorem hefferon_One_II_2_7_wd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : |inner ℝ u v / (‖u‖ * ‖v‖)| ≤ 1 :=
  abs_real_inner_div_norm_mul_norm_le_one u v

/-- Vectors are orthogonal iff the dot product is zero (angle a right angle). -/
@[kb "hefferon2020" "One.II.2.8, p. 56"]
theorem hefferon_One_II_2_8_orth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : inner ℝ u v = 0 ↔ InnerProductGeometry.angle u v = Real.pi / 2 :=
  InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two u v

/-- Nonzero vectors point in the same direction iff the dot product is the product of lengths. -/
@[kb "hefferon2020" "One.II.2.8, p. 56"]
theorem hefferon_One_II_2_8_par {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    inner ℝ u v = ‖u‖ * ‖v‖ ↔ InnerProductGeometry.angle u v = 0 :=
  InnerProductGeometry.inner_eq_mul_norm_iff_angle_eq_zero hu hv

end UndergradKB.LinearAlgebra.Course
