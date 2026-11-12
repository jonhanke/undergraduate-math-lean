/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.RepresentationTheory.GroupDeterminant
import UndergradKB.RepresentationTheory.AlgebrasChapter2b

/-!
# Proofs of the representation theory headline statements

Proves the statements of `Challenge_RepresentationTheory.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_RepresentationTheory.lean`.
-/

namespace UndergradKB.Headlines.RepresentationTheory

open Module Representation MvPolynomial UndergradKB.RepresentationTheory

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

end UndergradKB.Headlines.RepresentationTheory
