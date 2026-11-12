import UndergradKB.Common.Attr
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-! # Algebraic integers as eigenvalues of integer matrices (Etingof et al., Definition 4.10, Proposition 4.11)

A complex number is an algebraic integer when it is integral over `ℤ` (Mathlib's `IsIntegral ℤ z`).  We show
that this holds exactly when `z` is an eigenvalue of a square integer matrix, and that `z` is algebraic over
`ℚ` exactly when it is an eigenvalue of a square rational matrix.  One direction uses that the characteristic
polynomial of a matrix is monic; the other uses the matrix of multiplication by `z` on the power basis of
`R[z]`, whose characteristic polynomial is the minimal polynomial of `z`.
-/

namespace UndergradKB.RepresentationTheory

open Polynomial

section general

variable {R : Type*} [CommRing R] [Algebra R ℂ]

/-- An eigenvalue (root of the characteristic polynomial) of a matrix over `R`, viewed over `ℂ`, is integral
over `R`. -/
lemma isIntegral_of_isRoot_charpoly_map {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : ℂ)
    (hz : (A.map (algebraMap R ℂ)).charpoly.IsRoot z) : IsIntegral R z := by
  refine ⟨A.charpoly, Matrix.charpoly_monic A, ?_⟩
  rw [Matrix.charpoly_map] at hz
  simpa [IsRoot, eval_map] using hz

/-- An integral element of `ℂ` over an integrally closed domain `R` is a root of the characteristic
polynomial of a square matrix over `R`. -/
lemma exists_matrix_isRoot_charpoly_map_of_isIntegral [IsDomain R] [IsIntegrallyClosed R]
    [Module.IsTorsionFree R ℂ] {z : ℂ} (hz : IsIntegral R z) :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), (A.map (algebraMap R ℂ)).charpoly.IsRoot z := by
  let pb := Algebra.adjoin.powerBasis' hz
  refine ⟨pb.dim, Algebra.leftMulMatrix pb.basis pb.gen, ?_⟩
  rw [Matrix.charpoly_map, charpoly_leftMulMatrix, Algebra.adjoin.powerBasis'_gen]
  have h : minpoly R (⟨z, Algebra.self_mem_adjoin_singleton R z⟩ : Algebra.adjoin R ({z} : Set ℂ))
      = minpoly R z :=
    minpoly.algebraMap_eq (A := R) (B := Algebra.adjoin R ({z} : Set ℂ)) 
      Subtype.val_injective _ |>.symm
  rw [h, IsRoot, eval_map_algebraMap]
  exact minpoly.aeval R z

end general

/-- **Etingof, Proposition 4.11 (integer case).**  A complex number is an algebraic integer iff it is a root of
the characteristic polynomial of some square integer matrix, i.e. an eigenvalue of it. -/
@[kb "etingof2011" "Proposition 4.11, p. 49"]
theorem isIntegral_int_iff_exists_matrix_isRoot_charpoly (z : ℂ) :
    IsIntegral ℤ z ↔ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
      (A.map (Int.castRingHom ℂ)).charpoly.IsRoot z := by
  constructor
  · intro h
    exact exists_matrix_isRoot_charpoly_map_of_isIntegral h
  · rintro ⟨n, A, h⟩
    exact isIntegral_of_isRoot_charpoly_map A z h

/-- **Etingof, Proposition 4.11 (integer case, eigenvalue form).**  A complex number is an algebraic integer
iff it is an eigenvalue of the linear map `ℂⁿ → ℂⁿ` of some square integer matrix. -/
@[kb "etingof2011" "Proposition 4.11, p. 49"]
theorem isIntegral_int_iff_exists_matrix_hasEigenvalue (z : ℂ) :
    IsIntegral ℤ z ↔ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
      Module.End.HasEigenvalue (Matrix.toLin' (A.map (Int.castRingHom ℂ))) z := by
  rw [isIntegral_int_iff_exists_matrix_isRoot_charpoly]
  refine exists_congr fun n => exists_congr fun A => ?_
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']

/-- **Etingof, Proposition 4.11 (rational case).**  A complex number is algebraic over `ℚ` iff it is a root
of the characteristic polynomial of some square rational matrix. -/
@[kb "etingof2011" "Proposition 4.11, p. 49"]
theorem isAlgebraic_rat_iff_exists_matrix_isRoot_charpoly (z : ℂ) :
    IsAlgebraic ℚ z ↔ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
      (A.map (algebraMap ℚ ℂ)).charpoly.IsRoot z := by
  rw [isAlgebraic_iff_isIntegral]
  constructor
  · intro h
    exact exists_matrix_isRoot_charpoly_map_of_isIntegral h
  · rintro ⟨n, A, h⟩
    exact isIntegral_of_isRoot_charpoly_map A z h

/-- **Etingof, Proposition 4.11 (rational case, eigenvalue form).** -/
@[kb "etingof2011" "Proposition 4.11, p. 49"]
theorem isAlgebraic_rat_iff_exists_matrix_hasEigenvalue (z : ℂ) :
    IsAlgebraic ℚ z ↔ ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
      Module.End.HasEigenvalue (Matrix.toLin' (A.map (algebraMap ℚ ℂ))) z := by
  rw [isAlgebraic_rat_iff_exists_matrix_isRoot_charpoly]
  refine exists_congr fun n => exists_congr fun A => ?_
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']

end UndergradKB.RepresentationTheory
