/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.RepresentationTheory.GroupDeterminant
import UndergradKB.RepresentationTheory.AlgebrasChapter2b
import UndergradKB.RepresentationTheory.PeterWeyl
import UndergradKB.RepresentationTheory.PolynomialRepsSum
import UndergradKB.RepresentationTheory.McKayClassification

/-!
# Proofs of the representation theory headline statements

Proves the statements of `Challenge_RepresentationTheory.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_RepresentationTheory.lean`.
-/

namespace UndergradKB.Headlines.RepresentationTheory

open Module Representation MvPolynomial UndergradKB.RepresentationTheory UndergradKB.RepresentationTheory.Roots
open scoped TensorProduct DirectSum

theorem groupDeterminant_factorization {G : Type*} [Group G] [Fintype G] [DecidableEq G] {ι : Type*} [Fintype ι]
    (X : ι → IrrRep ℂ G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    groupDeterminant G ℂ = C (((Equiv.Perm.sign (Equiv.inv G) : ℤˣ) : ℤ) : ℂ) *
        ∏ i, groupPoly (X i).ρ ^ finrank ℂ (X i).V ∧
      (∀ i, Irreducible (groupPoly (X i).ρ)) ∧
      (∀ i j (c : ℂ), groupPoly (X i).ρ = C c * groupPoly (X j).ρ → i = j) :=
  UndergradKB.RepresentationTheory.groupDeterminant_factorization X hinj hsurj

theorem dixmier_lemma {A : Type*} {V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] [IsSimpleModule A V]
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (φ : Module.End A V) :
    ∃ c : ℂ, φ = algebraMap ℂ (Module.End A V) c :=
  UndergradKB.RepresentationTheory.exists_eq_algebraMap_of_rank_le_aleph0 hV φ

theorem peter_weyl_gl {N : ℕ} :
    ∃ e : (⨁ lam : HighestWeights N, Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) ≃ₗ[ℂ]
        (ratFunctions N ℂ).toSubmodule,
      ∀ (lam : HighestWeights N) (f : Module.Dual ℂ (LCarrier lam)) (v : LCarrier lam) (x : GL (Fin N) ℂ),
        (e (DirectSum.lof ℂ _ (fun lam => Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) lam (f ⊗ₜ v)) :
          GL (Fin N) ℂ → ℂ) x = f (Lrep lam x v) :=
  ⟨UndergradKB.RepresentationTheory.peterWeyl, UndergradKB.RepresentationTheory.peterWeyl_apply_tmul⟩

theorem rational_irrep_is_glIrrep {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) (hirr : IsIrredRep ρ) :
    ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
      Nonempty (Representation.Equiv ρ (glIrrep (N := N) ν a)) :=
  UndergradKB.RepresentationTheory.IsRationalRep.exists_equiv_glIrrep hρ hirr

theorem glIrrep_iso_iff {N n m : ℕ} (ν : DiagramsOfSize n) (μ : DiagramsOfSize m)
    (hν : ν.1.colLen 0 ≤ N) (hμ : μ.1.colLen 0 ≤ N) (a b : ℤ) :
    Nonempty (Representation.Equiv (glIrrep (N := N) ν a) (glIrrep (N := N) μ b)) ↔
      highestWeight N ν a = highestWeight N μ b :=
  UndergradKB.RepresentationTheory.glIrrep_equiv_iff ν μ hν hμ a b

theorem rational_rep_decomposition {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) :
    ∃ (s : Finset (Submodule ℂ W)) (h : ∀ U ∈ s, ∀ g, ∀ w ∈ U, ρ g w ∈ U),
      DirectSum.IsInternal (fun U : s => (U : Submodule ℂ W)) ∧
      ∀ U (hU : U ∈ s), ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
        Nonempty (Representation.Equiv (⟨U, fun g _ hw => h U hU g _ hw⟩ : Subrepresentation ρ).toRepresentation
          (glIrrep (N := N) ν a)) :=
  UndergradKB.RepresentationTheory.IsRationalRep.exists_isInternal_glIrrep hρ

open scoped Classical in
theorem mckay_affine_classification (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hG : G ≠ ⊥) :
    (∃ i j : irrChars ℂ G, i ≠ j ∧ mckay (natRep G) i j = 2 ∧ ∀ k, k = i ∨ k = j) ∨
    ∃ (N : ℕ) (e : irrChars ℂ G ≃ Fin N) (M : SimpleGraph (Fin N)),
      (∀ i j, mckay (natRep G) i j = 0 ∨ mckay (natRep G) i j = 1) ∧
      (∀ i j, M.Adj (e i) (e j) ↔ mckay (natRep G) i j = 1) ∧
      ((∃ k, Nonempty (affineCycle k ≃g M)) ∨ (∃ k, Nonempty (affineD k ≃g M)) ∨
        Nonempty (affineE6 ≃g M) ∨ Nonempty (affineE7 ≃g M) ∨
        Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g M)) :=
  UndergradKB.RepresentationTheory.mckay_affine_classification G hG

end UndergradKB.Headlines.RepresentationTheory
