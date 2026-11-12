import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.RepresentationTheory.FiniteIndex
import UndergradKB.RepresentationTheory.Categories

/-! # More on abelian categories and exact functors (Etingof et al., chapter 6)

* The book's description of an abelian category as (up to equivalence) a full subcategory of a module category
  closed under finite sums, kernels and cokernels: this is the Freyd-Mitchell embedding theorem, which Mathlib
  proves as a full, faithful, exact functor into modules over a ring (Definition 6.14).
* Induction from a subgroup of finite index is an exact functor (Example 6.23): it is both left and right adjoint
  to restriction.
-/

universe u

namespace UndergradKB.RepresentationTheory

open CategoryTheory CategoryTheory.Limits

/-- Freyd-Mitchell: every abelian category admits a full, faithful functor into the category of modules over
some ring, preserving finite limits and finite colimits (so kernels, cokernels and finite sums); hence it is
equivalent to a full subcategory of a module category closed under these operations. -/
@[kb "etingof2011" "Definition 6.14, p. 103"]
theorem abelian_embedding_modules (C : Type u) [Category.{u} C] [Abelian C] :
    ∃ (R : Type u) (_ : Ring R) (F : C ⥤ ModuleCat.{u} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  Abelian.freyd_mitchell C

/-- The Freyd-Mitchell functor is exact in the book's sense (Definition 6.20): it sends short exact sequences
to short exact sequences. -/
@[kb "etingof2011" "Definition 6.14, p. 103"]
theorem abelian_embedding_modules_exact (C : Type u) [Category.{u} C] [Abelian C] :
    ∃ (R : Type u) (_ : Ring R) (F : C ⥤ ModuleCat.{u} R) (_ : F.Additive),
      F.Full ∧ F.Faithful ∧ IsExactFunctor F := by
  obtain ⟨R, _, F, h1, h2, h3, h4⟩ := Abelian.freyd_mitchell C
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  exact ⟨R, inferInstance, F, inferInstance, h1, h2, (isExactFunctor_iff F).2 ⟨h3, h4⟩⟩

section Induction

variable (k : Type u) {G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]
  [DecidableRel (QuotientGroup.rightRel S)]

instance indFunctor_additive : (Rep.indFunctor.{u} k S.subtype).Additive := by
  have := (Rep.resIndAdjunction.{u, u, u} k S).rightAdjoint_preservesLimits.{0, 0}
  have : PreservesFiniteLimits (Rep.indFunctor.{u} k S.subtype) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact Functor.additive_of_preserves_binary_products _

/-- Induction from a subgroup of finite index (in particular from any subgroup of a finite group) is an exact
functor: it has restriction as a left adjoint (so it is left exact) and as a right adjoint (so it is right
exact). -/
@[kb "etingof2011" "Example 6.23, p. 105"]
theorem isExactFunctor_indFunctor : IsExactFunctor (Rep.indFunctor.{u} k S.subtype) := by
  rw [isExactFunctor_iff]
  refine ⟨?_, ?_⟩
  · have := (Rep.resIndAdjunction.{u, u, u} k S).rightAdjoint_preservesLimits.{0, 0}
    exact PreservesLimitsOfSize.preservesFiniteLimits _
  · have := (Rep.indResAdjunction.{u, u, u} k S.subtype).leftAdjoint_preservesColimits.{0, 0}
    exact PreservesColimitsOfSize.preservesFiniteColimits _

end Induction

end UndergradKB.RepresentationTheory
