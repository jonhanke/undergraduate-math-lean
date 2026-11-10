import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.ColumnRowPartitioned
import UndergradKB.Common.Attr

/-! # Linear systems and square matrices (Hefferon One, Axler 3B/3D)

Systems of equations encoded as `A *ᵥ x = b`; augmented matrices; counting unknowns against equations;
the equivalent conditions for a square matrix; the `2 × 2` inverse formula. -/

open Matrix

namespace UndergradKB.LinearAlgebra

section System

variable {K : Type*} {m n : Type*} [Fintype n]

/-- Each of the `m` linear equations `a_{i1} x_1 + ... + a_{in} x_n = d_i` holds iff the single matrix
equation `A x = d` holds. -/
@[kb "hefferon2020" "One.I.1.1, p. 12"]
theorem hefferon_One_I_1_1 [CommSemiring K] (A : Matrix m n K) (d : m → K) (x : n → K) :
    (∀ i, ∑ j, A i j * x j = d i) ↔ A *ᵥ x = d := by
  simp only [funext_iff, Matrix.mulVec, dotProduct]

/-- The solution set of `A x = b`, once one solution `x₀` is known, is the translate of the null space
of `A` by `x₀`. -/
@[kb "hefferon2020" "One.I.2.9, p. 27"]
theorem hefferon_One_I_2_9 [CommRing K] (A : Matrix m n K) (x₀ : n → K) (b' : m → K)
    (h : A *ᵥ x₀ = b') :
    {x | A *ᵥ x = b'} = (fun y => x₀ + y) '' (LinearMap.ker A.mulVecLin : Set (n → K)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker,
    Matrix.mulVecLin_apply]
  constructor
  · intro hx
    refine ⟨x - x₀, ?_, by abel⟩
    rw [Matrix.mulVec_sub, hx, h, sub_self]
  · rintro ⟨y, hy, rfl⟩
    rw [Matrix.mulVec_add, h, hy, add_zero]

/-- The augmented matrix `[A | b]` of the system `A x = b`: the coefficient columns followed by the
constant column. -/
def augmented [CommSemiring K] (A : Matrix m n K) (b : m → K) : Matrix m (n ⊕ Unit) K :=
  Matrix.fromCols A (Matrix.of fun i _ => b i)

/-- `x` solves `A x = b` iff the augmented matrix sends the column `(x, -1)` to zero. -/
theorem augmented_mulVec [CommRing K] (A : Matrix m n K) (b : m → K) (x : n → K) :
    augmented A b *ᵥ Sum.elim x (fun _ => -1) = A *ᵥ x - b := by
  ext i
  simp [augmented, Matrix.mulVec, dotProduct, sub_eq_add_neg]

omit [Fintype n] in
/-- A row operation, given by left multiplication by a matrix `P`, acts on the augmented matrix by
acting on the coefficients and on the constants separately. -/
@[kb "hefferon2020" "One.I.2.7, p. 26"]
theorem hefferon_One_I_2_7 [CommSemiring K] {l : Type*} [Fintype m] (P : Matrix l m K)
    (A : Matrix m n K) (b : m → K) :
    P * augmented A b = augmented (P * A) (P *ᵥ b) := by
  ext i (j | j)
  · simp [augmented, Matrix.mul_apply]
  · simp [augmented, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Row operations (invertible `P`) do not change the solution set of the system. -/
theorem solutionSet_rowOp [CommRing K] [Fintype m] [DecidableEq m] (P : Matrix m m K) (hP : IsUnit P)
    (A : Matrix m n K) (b : m → K) :
    {x | (P * A) *ᵥ x = P *ᵥ b} = {x | A *ᵥ x = b} := by
  obtain ⟨u, rfl⟩ := hP
  ext x
  simp only [Set.mem_ofPred_eq, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun v => (↑u⁻¹ : Matrix m m K) *ᵥ v) h
    simpa [Matrix.mulVec_mulVec] using this
  · intro h; rw [h]

end System

section Counting

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

/-- A homogeneous system with more unknowns than equations has a nonzero solution. -/
@[kb "axler2024" "3.26, p. 83"]
theorem axler_3_26 (A : Matrix m n K) (h : Fintype.card m < Fintype.card n) :
    ∃ x : n → K, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have hne : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using h
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨x, hx0, by simpa using hx⟩

/-- A system with more equations than unknowns has a right-hand side for which it has no solution. -/
@[kb "axler2024" "3.28, p. 83"]
theorem axler_3_28 (A : Matrix m n K) (h : Fintype.card n < Fintype.card m) :
    ∃ b : m → K, ∀ x : n → K, A *ᵥ x ≠ b := by
  by_contra hcon
  push Not at hcon
  have hs : A.mulVec.Surjective := fun b => by
    obtain ⟨x, hx⟩ := hcon b
    exact ⟨x, hx⟩
  have := Matrix.mulVec_surjective_iff_rank_eq_card.mp hs
  have h2 := A.rank_le_card_width
  omega

end Counting

section Square

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a square matrix `A` over a field, these are equivalent: rank equals the size; `A` is invertible
(nonsingular); the rows are independent; the columns are independent; every system with matrix `A` has
exactly one solution. -/
@[kb "hefferon2020" "Two.III.3.14, p. 151"]
theorem hefferon_Two_III_3_14 (A : Matrix n n K) :
    List.TFAE [A.rank = Fintype.card n, IsUnit A, LinearIndependent K A.row,
      LinearIndependent K A.col, ∀ b : n → K, ∃! x : n → K, A *ᵥ x = b] := by
  tfae_have 1 ↔ 2 := by
    rw [← Matrix.mulVec_surjective_iff_rank_eq_card, Matrix.mulVec_surjective_iff_isUnit]
  tfae_have 3 ↔ 2 := Matrix.linearIndependent_row_iff_isUnit
  tfae_have 4 ↔ 2 := Matrix.linearIndependent_col_iff_isUnit
  tfae_have 5 ↔ 2 := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    constructor
    · intro h x y hxy
      obtain ⟨z, _, hz⟩ := h (A *ᵥ y)
      exact (hz x hxy).trans (hz y rfl).symm
    · intro hinj b
      have hs : A.mulVec.Surjective := by
        rw [Matrix.mulVec_surjective_iff_isUnit, ← Matrix.mulVec_injective_iff_isUnit]; exact hinj
      obtain ⟨x, hx⟩ := hs b
      exact ⟨x, hx, fun y hy => hinj (hy.trans hx.symm)⟩
  tfae_finish

end Square

section TwoByTwo

variable {K : Type*} [Field K]

/-- The `2 × 2` matrix `[[a, b], [c, d]]` is invertible iff `a d - b c ≠ 0`, and then its inverse is
`(a d - b c)⁻¹ • [[d, -b], [-c, a]]`. -/
@[kb "hefferon2020" "Three.IV.4.11, p. 269"]
theorem hefferon_Three_IV_4_11 (a b c d : K) :
    (IsUnit !![a, b; c, d] ↔ a * d - b * c ≠ 0) ∧
      (a * d - b * c ≠ 0 →
        (!![a, b; c, d])⁻¹ = (a * d - b * c)⁻¹ • !![d, -b; -c, a]) := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of, isUnit_iff_ne_zero]
  · rw [Matrix.inv_def, Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of, Ring.inverse_eq_inv']

end TwoByTwo

end UndergradKB.LinearAlgebra
