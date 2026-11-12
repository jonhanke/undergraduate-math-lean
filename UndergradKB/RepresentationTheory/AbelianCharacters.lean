import UndergradKB.Common.Attr
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The character group of a finite abelian group (Etingof et al., §3.3)

For a finite abelian group `G`, the one-dimensional complex characters `G →* ℂˣ` form a group `G^∨` under
pointwise multiplication (Mathlib: `G →* ℂˣ` is a `CommGroup`).  This group has the same order as `G`, is
non-canonically isomorphic to `G`, and `G` is canonically isomorphic to its double dual via evaluation.
All of this is a specialisation of Mathlib's duality theory over a commutative monoid with enough roots of
unity (`ℂ` being algebraically closed).
-/

namespace UndergradKB.RepresentationTheory

variable (G : Type*) [CommGroup G] [Finite G]

/-- The group of one-dimensional characters `G →* ℂˣ` of a finite abelian group has the same order as `G`. -/
@[kb "etingof2011" "§3.3, p. 35"]
theorem nat_card_monoidHom_units_complex : Nat.card (G →* ℂˣ) = Nat.card G :=
  CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ

/-- A finite abelian group is (non-canonically) isomorphic to its character group `G →* ℂˣ`. -/
@[kb "etingof2011" "§3.3, p. 35"]
theorem nonempty_mulEquiv_monoidHom_units_complex : Nonempty (G ≃* (G →* ℂˣ)) :=
  ⟨(CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.symm⟩

/-- A finite abelian group is canonically isomorphic to its double dual: there is an isomorphism
`e : G ≃* ((G →* ℂˣ) →* ℂˣ)` given by evaluation, `e g χ = χ g`. -/
@[kb "etingof2011" "§3.3, p. 35"]
theorem exists_mulEquiv_doubleDual_units_complex :
    ∃ e : G ≃* ((G →* ℂˣ) →* ℂˣ), ∀ (g : G) (χ : G →* ℂˣ), e g χ = χ g :=
  ⟨(CommGroup.monoidHomMonoidHomEquiv G ℂ).symm, fun g χ =>
    CommGroup.monoidHomMonoidHomEquiv_symm_apply_apply G ℂ g χ⟩

end UndergradKB.RepresentationTheory
