import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 2 (general results)

Thin theorems in the book's terms for the items of Chapter 2 that Mathlib already contains,
each tagged with the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open scoped TensorProduct

/-- Etingof et al., Definition 2.1: a module is semisimple (completely reducible) when it is a
direct sum of simple submodules. -/
@[kb "etingof2011" "Definition 2.1, p. 23"]
theorem etingof_2_1 (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    IsSemisimpleModule R M ↔
      ∃ (s : Set (Submodule R M)) (_ : M ≃ₗ[R] Π₀ m : s, m.1), ∀ m : s, IsSimpleModule R m.1 :=
  isSemisimpleModule_iff_exists_linearEquiv_dfinsupp

/-- Etingof et al., Lemma 2.8: a module of finite length (Noetherian and Artinian, in particular
a finite-dimensional representation) has a chain of submodules from `0` to the whole module in
which each step has a simple quotient. -/
@[kb "etingof2011" "Lemma 2.8, p. 25"]
theorem etingof_2_8 (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [IsNoetherian R M]
    [IsArtinian R M] :
    ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ :=
  exists_compositionSeries_of_isNoetherian_isArtinian R M

/-- Etingof et al., Definition 2.15: for an Artinian ring (such as a finite-dimensional algebra),
semisimplicity is equivalent to the vanishing of the Jacobson radical. -/
@[kb "etingof2011" "Definition 2.15, p. 27"]
theorem etingof_2_15 (R : Type*) [Ring R] [IsArtinianRing R] :
    IsSemisimpleRing R ↔ Ring.jacobson R = ⊥ :=
  IsArtinianRing.isSemisimpleRing_iff_jacobson

/-- Etingof et al., Section 2.7: the length of a module equals the length of any composition
series running from `0` to the whole module. -/
@[kb "etingof2011" "§2.7, p. 29"]
theorem etingof_sec_2_7_a (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) :
    s.length = Module.length R M :=
  Module.length_compositionSeries s h₁ h₂

/-- Etingof et al., Section 2.7: equivalent (Jordan-Hölder) series, i.e. series whose successive
quotients agree up to permutation, have the same length. -/
@[kb "etingof2011" "§2.7, p. 29"]
theorem etingof_sec_2_7_b {X : Type*} [Lattice X] [JordanHolderLattice X]
    {s₁ s₂ : CompositionSeries X} (h : s₁.Equivalent s₂) : s₁.length = s₂.length :=
  CompositionSeries.Equivalent.length_eq h

/-- Etingof et al., Section 2.10: the tensor product of two algebras is an algebra with
componentwise multiplication on pure tensors. -/
@[kb "etingof2011" "§2.10, p. 31"]
theorem etingof_sec_2_10 {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] (a₁ a₂ : A) (b₁ b₂ : B) :
    (a₁ ⊗ₜ[R] b₁) * (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  Algebra.TensorProduct.tmul_mul_tmul a₁ a₂ b₁ b₂

end UndergradKB.RepresentationTheory.Course
