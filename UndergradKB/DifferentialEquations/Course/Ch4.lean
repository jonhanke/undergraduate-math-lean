import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapter 4 (Fourier series and PDEs): course layer

Thin wrappers around Mathlib stating the preliminary facts of the chapter in the book's terms.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch4

open scoped RealInnerProductSpace

/-- Lebl §4.1 symmetric matrix (DE-116). A matrix equal to its transpose has
`A i j = A j i` for all entries. -/
@[kb "lebldiffyqs2026" "§4.1 symmetric matrix, p. 193"]
theorem lebl_symmetric_matrix_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsSymm ↔ ∀ i j, A i j = A j i := by
  constructor
  · intro h i j
    exact (congrFun (congrFun h.eq i) j).symm
  · intro h
    ext i j
    exact (h j i)

/-- Lebl §4.2 periodic function (DE-119). `f` is `P`-periodic iff `f (t + P) = f t` for all `t`. -/
@[kb "lebldiffyqs2026" "§4.2 periodic function, p. 198"]
theorem lebl_periodic_iff (f : ℝ → ℝ) (P : ℝ) :
    Function.Periodic f P ↔ ∀ t, f (t + P) = f t :=
  Iff.rfl

/-- Lebl §4.2 decomposition in orthogonal vectors (DE-121). A vector decomposes along an
orthonormal basis `w` with coefficients `⟨w i, v⟩` (the orthonormal case, where
`⟨w i, w i⟩ = 1`). -/
@[kb "lebldiffyqs2026" "§4.2 decomposition in orthogonal vectors, p. 199"]
theorem lebl_orthonormal_decomposition {n : ℕ} (w : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ⟪w i, v⟫ • w i = v :=
  w.sum_repr' v

end UndergradKB.DifferentialEquations.Course.Ch4
