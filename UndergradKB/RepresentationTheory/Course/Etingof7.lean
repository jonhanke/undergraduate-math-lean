import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Idempotents
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 7 (structure of finite-dimensional algebras)

Thin theorems in the book's terms for the items of Chapter 7 that Mathlib already contains,
each tagged with the source key `etingof2011` and the locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

/-- Etingof et al., Definition 7.2: a module is projective when the surjection from the free
module on its elements has a linear section. -/
@[kb "etingof2011" "Definition 7.2, p. 106"]
theorem etingof_7_2 (R P : Type*) [Semiring R] [AddCommMonoid P] [Module R P] :
    Module.Projective R P ↔
      ∃ s : P →ₗ[R] P →₀ R, Finsupp.linearCombination R id ∘ₗ s = LinearMap.id :=
  Module.projective_def'

/-- Etingof et al., Definition 7.4: a complete system of orthogonal idempotents consists of
idempotents with pairwise zero products that add up to `1`. -/
@[kb "etingof2011" "Definition 7.4, p. 107"]
theorem etingof_7_4 {R I : Type*} [Semiring R] [Fintype I] {e : I → R}
    (he : CompleteOrthogonalIdempotents e) :
    (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∑ i, e i = 1 :=
  ⟨fun i => he.idem i, fun _ _ h => he.ortho h, he.complete⟩

/-- Etingof et al., Corollary 7.5: complete systems of orthogonal idempotents lift along a ring
homomorphism whose kernel consists of nilpotent elements, provided the idempotents lie in the
image. -/
@[kb "etingof2011" "Corollary 7.5, p. 107"]
theorem etingof_7_5 {R S I : Type*} [Ring R] [Ring S] [Fintype I] (f : R →+* S)
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x) {e : I → S} (he : CompleteOrthogonalIdempotents e)
    (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : I → R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e :=
  CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker f h he he'

end UndergradKB.RepresentationTheory.Course
