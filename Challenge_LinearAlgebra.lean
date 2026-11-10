/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.LinearAlgebra.Jordan
import UndergradKB.LinearAlgebra.JordanUnique
import UndergradKB.LinearAlgebra.Schur

/-!
# Headline statements of undergraduate-math-lean 0.1.0: linear algebra (Axler; Hefferon)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: the Jordan normal form of an operator over an algebraically closed field, the uniqueness of the Jordan
form of a matrix up to the order of the blocks, and Schur's triangularization of a complex operator in an
orthonormal basis. To check what is claimed, read this file. `Solution_LinearAlgebra.lean` proves the same
statements from the library, and `lake comparator` (configured by `comparator/LinearAlgebra.json`) checks that each
proved statement is exactly the one here and uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `UndergradKB.LinearAlgebra.IsJordanBasis` (Axler Definition 8.44): a basis, indexed by the concatenation of
  `p` blocks of sizes `n 0, ..., n (p-1)`, in which the operator has a block diagonal matrix whose blocks are
  Jordan blocks.
* `UndergradKB.LinearAlgebra.jordanBlock` (Axler 8.44): the square matrix of size `n` with `a` on the diagonal,
  `1` directly above it and zeros elsewhere.
-/

universe u

namespace UndergradKB.Headlines.LinearAlgebra

/-- **Jordan normal form** (Axler 8.46): over an algebraically closed field (in particular `ℂ`), every operator on
a finite-dimensional vector space has a Jordan basis. Related: Mathlib has only the Jordan-Chevalley
decomposition (`Mathlib/LinearAlgebra/JordanChevalley.lean`), and Tau Ceti has Jordan-chain bases of nilpotent
maps (`exists_jordanChainBasis`), not the form for every operator. -/
theorem jordan_normal_form {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [IsAlgClosed K]
    [FiniteDimensional K V] (T : Module.End K V) :
    ∃ (p : ℕ) (n : Fin p → ℕ) (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V),
      UndergradKB.LinearAlgebra.IsJordanBasis T b := by
  sorry

/-- **Uniqueness of the Jordan form** (Hefferon Remark Five.IV.2.9, matrix form): two similar matrices that are
both Jordan matrices (block diagonal with Jordan blocks of positive sizes, after relabelling the rows and columns
by `ι`) have the same blocks up to order. Related: Tau Ceti has the Jordan partition as a conjugacy invariant for
nilpotent maps only (`TauCeti/LinearAlgebra/End/JordanChain/Partition.lean`); Mathlib has nothing. -/
theorem jordan_form_unique {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    {n : Fin p → ℕ} {p' : ℕ} {n' : Fin p' → ℕ} (lam : Fin p → K)
    (lam' : Fin p' → K) (hn : ∀ i, 0 < n i) (hn' : ∀ i, 0 < n' i)
    (e : (Σ i : Fin p, Fin (n i)) ≃ ι) (e' : (Σ i : Fin p', Fin (n' i)) ≃ ι)
    (P : (Matrix ι ι K)ˣ)
    (h : Matrix.reindex e e (Matrix.blockDiagonal'
        fun i => UndergradKB.LinearAlgebra.jordanBlock (lam i) (n i)) =
      (P : Matrix ι ι K) *
        Matrix.reindex e' e' (Matrix.blockDiagonal'
          fun i => UndergradKB.LinearAlgebra.jordanBlock (lam' i) (n' i)) *
        ((P⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K)) :
    Multiset.map (fun i => (lam i, n i)) Finset.univ.val =
      Multiset.map (fun i => (lam' i, n' i)) Finset.univ.val := by
  sorry

/-- **Schur's triangularization** (Axler 6.38): every operator on a finite-dimensional complex inner product space
has an upper-triangular matrix in some orthonormal basis. Related: neither Mathlib nor Tau Ceti has this (the
Schur results of Mathlib are about the Schur complement and the Schur-Horn theorem). -/
theorem schur_triangularization {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    ∃ u : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      (LinearMap.toMatrix u.toBasis u.toBasis T).IsUpperTriangular := by
  sorry

end UndergradKB.Headlines.LinearAlgebra
