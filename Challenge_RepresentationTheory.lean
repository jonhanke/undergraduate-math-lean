/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.RepresentationTheory.GroupDeterminant
import UndergradKB.RepresentationTheory.AlgebrasChapter2b

/-!
# Headline statements of undergraduate-math-lean 0.2.0: representation theory (Etingof et al.)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: Frobenius's factorization of the group determinant, and Dixmier's lemma (Schur's lemma for irreducible
representations of countable dimension). Most named theorems of the book (Burnside's `pᵃqᵇ` theorem, Frobenius
reciprocity and divisibility, Gabriel's theorem, Schur–Weyl duality, the hook length formula, the Frobenius character
formula) are proved here too but are not headlines: Tau Ceti has them. To check what is claimed, read this file.
`Solution_RepresentationTheory.lean` proves the same statements from the library, and `lake comparator` (configured
by `comparator/RepresentationTheory.json`) checks that each proved statement is exactly the one here and uses only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library (namespace `UndergradKB.RepresentationTheory`);
a reader checking a statement should check these too:

* `IrrRep ℂ G`: a finite-dimensional irreducible complex representation of `G`, bundled with its space `V` and its
  action `ρ` (Mathlib's `Representation` and `IsIrreducible`).
* `groupMatrix G R`: the matrix indexed by `G × G` whose `(g, h)` entry is the variable `x_{gh}` of the polynomial
  ring `MvPolynomial G R`; `groupDeterminant G R` is its determinant (Etingof et al., Definition 4.6).
* `groupPoly ρ`: the polynomial `det (∑_g x_g ρ(g))` in the variables `x_g`, computed in a basis of `V`.
-/

namespace UndergradKB.Headlines.RepresentationTheory

open Module Representation MvPolynomial UndergradKB.RepresentationTheory

/-- **Frobenius's factorization of the group determinant** (Etingof et al. Theorem 4.7): for a finite group `G` and
a list `X` of its irreducible complex representations, one of each isomorphism class, the group determinant is
`ε ∏ᵢ Pᵢ ^ dim Vᵢ` with `Pᵢ = det (∑_g x_g ρᵢ(g))`, the `Pᵢ` are irreducible polynomials, and two of them are
proportional only if they are equal. Here `ε` is the sign of the permutation `g ↦ g⁻¹` of `G`: the matrix `(x_{gh})`
is the matrix of the regular representation only after reordering its columns by `h ↦ h⁻¹`, a sign the book omits.
Related: neither Mathlib nor Tau Ceti has the group determinant. -/
theorem groupDeterminant_factorization {G : Type*} [Group G] [Fintype G] [DecidableEq G] {ι : Type*} [Fintype ι]
    (X : ι → IrrRep ℂ G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    groupDeterminant G ℂ = C (((Equiv.Perm.sign (Equiv.inv G) : ℤˣ) : ℤ) : ℂ) *
        ∏ i, groupPoly (X i).ρ ^ finrank ℂ (X i).V ∧
      (∀ i, Irreducible (groupPoly (X i).ρ)) ∧
      (∀ i j (c : ℂ), groupPoly (X i).ρ = C c * groupPoly (X j).ρ → i = j) := by
  sorry

/-- **Dixmier's lemma** (Etingof et al. Problem 1.23): every endomorphism of an irreducible representation of a
complex algebra on a space of countable dimension is a scalar. Related: Mathlib and Tau Ceti have Schur's lemma for
finite-dimensional (or compact) settings only. -/
theorem dixmier_lemma {A : Type*} {V : Type*} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] [IsSimpleModule A V]
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (φ : Module.End A V) :
    ∃ c : ℂ, φ = algebraMap ℂ (Module.End A V) c := by
  sorry

end UndergradKB.Headlines.RepresentationTheory
