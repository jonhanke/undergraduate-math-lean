/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.LinearAlgebra.Jordan
import UndergradKB.LinearAlgebra.JordanUnique
import UndergradKB.LinearAlgebra.Schur

/-!
# Proofs of the linear algebra headline statements

Proves the statements of `Challenge_LinearAlgebra.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_LinearAlgebra.lean`.
-/

universe u

namespace UndergradKB.Headlines.LinearAlgebra

theorem jordan_normal_form {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [IsAlgClosed K]
    [FiniteDimensional K V] (T : Module.End K V) :
    ∃ (p : ℕ) (n : Fin p → ℕ) (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V),
      UndergradKB.LinearAlgebra.IsJordanBasis T b :=
  UndergradKB.LinearAlgebra.axler_8_46 T

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
      Multiset.map (fun i => (lam' i, n' i)) Finset.univ.val :=
  UndergradKB.LinearAlgebra.hefferon_Five_IV_2_9_matrix lam lam' hn hn' e e' P h

theorem schur_triangularization {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    ∃ u : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      (LinearMap.toMatrix u.toBasis u.toBasis T).IsUpperTriangular :=
  UndergradKB.LinearAlgebra.axler_6_38 T

end UndergradKB.Headlines.LinearAlgebra
