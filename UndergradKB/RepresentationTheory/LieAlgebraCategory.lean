import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.CategoryTheory.Adjunction.Basic
import UndergradKB.Common.Attr

/-! # The enveloping algebra as a left adjoint (Etingof et al., Example 6.13(3))

Mathlib has no category of Lie algebras, so this file adds a small bridging one: objects are Lie algebras over a
commutative ring `R`, morphisms are Lie algebra homomorphisms. Every associative `R`-algebra is a Lie algebra under
the commutator, which gives a functor from `AlgCat R` to Lie algebras; the universal enveloping algebra is a functor
the other way, and it is left adjoint to the commutator functor (this is the universal property of `U(L)`).
-/

universe u

namespace UndergradKB.RepresentationTheory

open CategoryTheory

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]

/-- The category of Lie algebras over `R` (bridging definition: not in Mathlib). -/
structure LieAlgCat where
  /-- The underlying type. -/
  carrier : Type u
  [lieRing : LieRing carrier]
  [lieAlgebra : LieAlgebra R carrier]

attribute [instance] LieAlgCat.lieRing LieAlgCat.lieAlgebra

namespace LieAlgCat

instance : CoeSort (LieAlgCat R) (Type u) := ⟨LieAlgCat.carrier⟩

/-- The object of `LieAlgCat R` attached to a Lie algebra. -/
abbrev of (L : Type u) [LieRing L] [LieAlgebra R L] : LieAlgCat R := ⟨L⟩

instance : Category (LieAlgCat R) where
  Hom L M := L →ₗ⁅R⁆ M
  id L := LieHom.id
  comp f g := g.comp f

end LieAlgCat

/-- Every associative algebra is a Lie algebra under the commutator `[a, b] = ab - ba`; algebra maps are Lie
algebra maps. -/
@[kb "etingof2011" "Example 6.13(3), p. 103"]
def algToLie : AlgCat.{u} R ⥤ LieAlgCat R where
  obj A := LieAlgCat.of R A
  map f := (f.hom.toLieHom : _ →ₗ⁅R⁆ _)

/-- The universal enveloping algebra as a functor from Lie algebras to associative algebras. -/
@[kb "etingof2011" "Example 6.13(3), p. 103"]
noncomputable def envelopingFunctor : LieAlgCat R ⥤ AlgCat.{u} R where
  obj L := AlgCat.of R (UniversalEnvelopingAlgebra R L)
  map {L M} f := AlgCat.ofHom (UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (f : L →ₗ⁅R⁆ M)))
  map_id L := by
    apply AlgCat.hom_ext
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    simp
    rfl
  map_comp {L M N} f g := by
    apply AlgCat.hom_ext
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    simp
    rfl

/-- The universal enveloping algebra functor is left adjoint to the functor from associative algebras to Lie
algebras: algebra maps `U(L) → A` correspond naturally to Lie algebra maps `L → A`. -/
@[kb "etingof2011" "Example 6.13(3), p. 103"]
noncomputable def envelopingAdjunction : envelopingFunctor R ⊣ algToLie R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun L A =>
        { toFun := fun f => ((UniversalEnvelopingAlgebra.lift R).symm f.hom : L →ₗ⁅R⁆ A)
          invFun := fun g => AlgCat.ofHom (UniversalEnvelopingAlgebra.lift R (g : L →ₗ⁅R⁆ A))
          left_inv := fun f => by
            apply AlgCat.hom_ext
            exact (UniversalEnvelopingAlgebra.lift R).apply_symm_apply _
          right_inv := fun g => (UniversalEnvelopingAlgebra.lift R (L := L) (A := A)).symm_apply_apply g }
      homEquiv_naturality_left_symm := by
        intro L L' A f g
        apply AlgCat.hom_ext
        apply UniversalEnvelopingAlgebra.hom_ext
        apply LieHom.ext
        intro x
        simp [envelopingFunctor]
        rfl

      homEquiv_naturality_right := by
        intro L A A' f g
        rfl }

/-- The adjunction recovers the universal property: a Lie algebra map `L → A` into an associative algebra
extends uniquely to an algebra map `U(L) → A`. -/
@[kb "etingof2011" "Example 6.13(3), p. 103"]
theorem enveloping_isLeftAdjoint : (envelopingFunctor R).IsLeftAdjoint :=
  (envelopingAdjunction R).isLeftAdjoint

end UndergradKB.RepresentationTheory
