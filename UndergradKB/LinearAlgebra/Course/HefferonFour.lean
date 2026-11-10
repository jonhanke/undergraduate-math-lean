import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import UndergradKB.Common.Attr

/-! # Hefferon chapter Four (Hefferon-only rows) -/

namespace UndergradKB.LinearAlgebra.Course

open Matrix

section Det

variable {R : Type*} [CommRing R]

/-- The permutation matrix of `φ` has rows the unit row vectors `ι_{φ(1)}, ..., ι_{φ(n)}`. -/
@[kb "hefferon2020" "Four.I.3.7, p. 351"]
theorem hefferon_Four_I_3_7 {n : Type*} [DecidableEq n] (φ : Equiv.Perm n) (i : n) :
    φ.permMatrix R i = Pi.single (φ i) 1 :=
  PEquiv.toMatrix_toPEquiv_apply φ i

/-- Determinants of sizes one, two and three are `a`, `ad - bc`, and the six-term sum. -/
@[kb "hefferon2020" "Four.I.3.13, p. 352", kb "hefferon2020" "Four.I.0.1, p. 336"]
theorem hefferon_Four_I_3_13 (a b c d e f g h i : R) :
    (Matrix.of ![![a]] : Matrix (Fin 1) (Fin 1) R).det = a ∧
    !![a, b; c, d].det = a * d - b * c ∧
    !![a, b, c; d, e, f; g, h, i].det =
      a * e * i + b * f * g + c * d * h - h * f * a - i * d * b - g * e * c := by
  refine ⟨by simp, Matrix.det_fin_two_of a b c d, ?_⟩
  rw [Matrix.det_fin_three]
  simp
  ring

/-- Existence of determinant functions: `det` swaps sign on row swaps, scales on row scaling,
is unchanged by adding a multiple of one row to another, and is `1` on the identity. -/
@[kb "hefferon2020" "Four.I.3.14, p. 353", kb "hefferon2020" "Four.I.4.9, p. 359"]
theorem hefferon_Four_I_3_14 {n : Type*} [Fintype n] [DecidableEq n] :
    (∀ (A : Matrix n n R) (i j : n), i ≠ j → (A.submatrix (Equiv.swap i j) id).det = - A.det) ∧
    (∀ (A : Matrix n n R) (i : n) (k : R), (A.updateRow i (k • A i)).det = k * A.det) ∧
    (∀ (A : Matrix n n R) (i j : n), i ≠ j → ∀ k : R,
      (A.updateRow i (A i + k • A j)).det = A.det) ∧
    (1 : Matrix n n R).det = 1 := by
  refine ⟨fun A i j hij => ?_, fun A i k => ?_, fun A i j hij k => ?_, Matrix.det_one⟩
  · rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]; simp
  · rw [Matrix.det_updateRow_smul]; simp
  · exact Matrix.det_updateRow_add_smul_self A hij k

/-- The adjugate is the transpose of the cofactor matrix. -/
@[kb "hefferon2020" "Four.III.1.8, p. 376"]
theorem hefferon_Four_III_1_8 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) :
    A.adjugate i j = (-1) ^ (j + i : ℕ) * (A.submatrix j.succAbove i.succAbove).det :=
  Matrix.adjugate_fin_succ_eq_det_submatrix A i j

end Det

section Inverse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `T adj(T) = adj(T) T = det(T) I`; hence a matrix with nonzero determinant has inverse
`adj(T) / det(T)`. -/
@[kb "hefferon2020" "Four.III.1.9, p. 376"]
theorem hefferon_Four_III_1_9 {K : Type*} [Field K] (T : Matrix n n K) :
    T * T.adjugate = T.det • (1 : Matrix n n K) ∧ T.adjugate * T = T.det • (1 : Matrix n n K) ∧
      (T.det ≠ 0 → T⁻¹ = (T.det)⁻¹ • T.adjugate) := by
  refine ⟨Matrix.mul_adjugate T, Matrix.adjugate_mul T, fun h => ?_⟩
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

/-- Cramer's Rule: if `det A ≠ 0`, the system `A x = b` has the unique solution
`x_i = det(B_i) / det(A)` where `B_i` is `A` with column `i` replaced by `b`. -/
@[kb "hefferon2020" "Topic-Cramer.1, p. 380"]
theorem hefferon_Topic_Cramer_1 {K : Type*} [Field K] (A : Matrix n n K) (hA : A.det ≠ 0)
    (b : n → K) :
    ∃! x : n → K, A *ᵥ x = b ∧ ∀ i, x i = (A.updateCol i b).det / A.det := by
  have hx : A *ᵥ (fun i => (A.updateCol i b).det / A.det) = b := by
    have h := Matrix.mulVec_cramer A b
    have : (fun i => (A.updateCol i b).det / A.det) = (A.det)⁻¹ • Matrix.cramer A b := by
      ext i; simp [Matrix.cramer_apply, div_eq_inv_mul]
    rw [this, Matrix.mulVec_smul, h, smul_smul, inv_mul_cancel₀ hA, one_smul]
  refine ⟨fun i => (A.updateCol i b).det / A.det, ⟨hx, fun i => rfl⟩, ?_⟩
  rintro y ⟨-, hy⟩
  funext i
  exact hy i

end Inverse

section Volume

open MeasureTheory

/-- The box formed by `v_1, ..., v_n` is the set of combinations with all coefficients in `[0,1]`. -/
@[kb "hefferon2020" "Four.II.1.1, p. 365"]
theorem hefferon_Four_II_1_1 {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (v : ι → E) (x : E) :
    x ∈ parallelepiped v ↔ ∃ t : ι → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ x = ∑ i, t i • v i := by
  rw [mem_parallelepiped_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, fun i => ⟨ht.1 i, ht.2 i⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ⟨fun i => (ht i).1, fun i => (ht i).2⟩, rfl⟩

/-- The volume of the box formed by the columns `v_j` is the absolute value of the determinant. -/
@[kb "hefferon2020" "Four.II.1.3, p. 367", kb "hefferon2020" "Four.II.1.0, p. 355"]
theorem hefferon_Four_II_1_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → EuclideanSpace ℝ ι) :
    volume (parallelepiped v) =
      ENNReal.ofReal |(Matrix.of fun i j => v j i).det| := by
  rw [← (EuclideanSpace.basisFun ι ℝ).addHaar_eq_volume]
  rw [MeasureTheory.Measure.addHaar_parallelepiped]
  congr 2

end Volume

end UndergradKB.LinearAlgebra.Course
