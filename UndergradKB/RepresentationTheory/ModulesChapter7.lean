import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.NoncommRing
import UndergradKB.Common.Attr

/-! # Projective modules and lifting idempotents (Etingof et al., Chapter 7)

* Theorem 7.1: five equivalent descriptions of a projective module `P` over a ring `A`
  (Mathlib's definition, the lifting property, splitting of surjections onto `P`, being a direct summand
  of a free module, and exactness of `Hom_A(P, -)` on surjections).
* Proposition 7.3: idempotents lift along a ring map with nil kernel (a nilpotent ideal being the
  motivating case), and two liftings of the same idempotent are conjugate by a unit congruent to `1`.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Module

/-! ### Theorem 7.1 -/

section Projective

variable (A : Type u) (P : Type v) [Ring A] [AddCommGroup P] [Module A P]

/-- Four characterisations of projectivity, together with Mathlib's definition (item 0).  The test
modules `M`, `N` live in the universe of `P` (`Small.{v} A` is needed so that the free module on the
elements of `P` is not larger than the test modules).  The items say that the module `P` is projective;
every map out of `P` lifts along surjections; every surjection onto `P` splits; `P` is a retract of a
free module; and composition with a surjection induces a surjection on `Hom_A(P, -)`. -/
@[kb "etingof2011" "Theorem 7.1, p. 106"]
theorem projective_tfae [Small.{v} A] :
    List.TFAE
      [ Module.Projective A P,
        ∀ (M N : Type v) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
          (f : M →ₗ[A] N) (g : P →ₗ[A] N), Function.Surjective f → ∃ h : P →ₗ[A] M, f ∘ₗ h = g,
        ∀ (M : Type v) [AddCommGroup M] [Module A M] (s : M →ₗ[A] P), Function.Surjective s →
          ∃ i : P →ₗ[A] M, s ∘ₗ i = LinearMap.id,
        ∃ (ι : Type v) (i : P →ₗ[A] (ι →₀ A)) (s : (ι →₀ A) →ₗ[A] P), s ∘ₗ i = LinearMap.id,
        ∀ (M N : Type v) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
          (f : M →ₗ[A] N), Function.Surjective f →
            Function.Surjective (fun h : P →ₗ[A] M => f ∘ₗ h) ] := by
  tfae_have 1 → 2 := by
    intro hP M N _ _ _ _ f g hf
    exact Module.projective_lifting_property f g hf
  tfae_have 2 → 3 := by
    intro h M _ _ s hs
    exact h M P s LinearMap.id hs
  tfae_have 3 → 1 := by
    intro h
    refine Module.Projective.of_lifting_property'' fun p hp => ?_
    let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv A A)
    obtain ⟨g, hg⟩ := h (P →₀ Shrink.{v} A) (p ∘ₗ e.toLinearMap) (hp.comp e.surjective)
    exact ⟨e.toLinearMap ∘ₗ g, by rw [← LinearMap.comp_assoc]; exact hg⟩
  tfae_have 1 → 4 := by
    intro hP
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hP
    exact ⟨P, s, Finsupp.linearCombination A id, hs⟩
  tfae_have 4 → 1 := by
    rintro ⟨ι, i, s, hs⟩
    exact Module.Projective.of_split i s hs
  tfae_have 2 → 5 := by
    intro h M N _ _ _ _ f hf g
    obtain ⟨k, hk⟩ := h M N f g hf
    exact ⟨k, hk⟩
  tfae_have 5 → 2 := by
    intro h M N _ _ _ _ f g hf
    exact h M N f hf g
  tfae_finish

end Projective

/-! ### Proposition 7.3 -/

section Idempotents

variable {A B : Type*} [Ring A] [Ring B] (f : A →+* B)

/-- Two idempotents of `A` with the same image under `f` are conjugate by a unit that maps to `1`,
provided every element of the kernel of `f` is nilpotent. -/
theorem exists_unit_conj_of_map_eq_idempotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e e' : A} (he : IsIdempotentElem e) (he' : IsIdempotentElem e') (hee' : f e = f e') :
    ∃ u : Aˣ, f u = 1 ∧ (u : A) * e' = e * u := by
  set w : A := e * e' + (1 - e) * (1 - e') with hw
  have hfw : f w = 1 := by
    have h1 : IsIdempotentElem (f e) := he.map f
    have h2 : (1 - f e) * (1 - f e) = 1 - f e := h1.one_sub.eq
    simp only [hw, map_add, map_mul, map_sub, map_one, ← hee', h2, h1.eq]
    exact add_sub_cancel _ _
  have hker : w - 1 ∈ RingHom.ker f := by simp [RingHom.mem_ker, hfw]
  have hnil : IsNilpotent (-(w - 1)) := (h _ hker).neg
  have hunit : IsUnit w := by
    have := hnil.isUnit_one_sub
    simpa using this
  refine ⟨hunit.unit, by simpa using hfw, ?_⟩
  simp only [IsUnit.unit_spec, hw]
  have e1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have e2 : (1 - e') * e' = 0 := by rw [sub_mul, one_mul, he'.eq, sub_self]
  calc (e * e' + (1 - e) * (1 - e')) * e'
      = e * (e' * e') + (1 - e) * ((1 - e') * e') := by noncomm_ring
    _ = e * e' := by rw [e2, mul_zero, add_zero, he'.eq]
    _ = e * (e * e') + (e * (1 - e)) * (1 - e') := by rw [e1, zero_mul, add_zero, ← mul_assoc, he.eq]
    _ = e * (e * e' + (1 - e) * (1 - e')) := by noncomm_ring

/-- Idempotents lift along a ring homomorphism whose kernel consists of nilpotent elements (for
instance a surjection `A → A / I` with `I` a nilpotent ideal): every idempotent in the range of `f`
has an idempotent preimage, and any two idempotent preimages are conjugate by a unit congruent to `1`
modulo the kernel. -/
@[kb "etingof2011" "Proposition 7.3, p. 106"]
theorem idempotent_lift_and_conjugate (h : ∀ x ∈ RingHom.ker f, IsNilpotent x) {b : B}
    (hb : b ∈ f.range) (hb' : IsIdempotentElem b) :
    (∃ e : A, IsIdempotentElem e ∧ f e = b) ∧
      ∀ e e' : A, IsIdempotentElem e → IsIdempotentElem e' → f e = b → f e' = b →
        ∃ u : Aˣ, f u = 1 ∧ (u : A) * e' = e * u := by
  refine ⟨exists_isIdempotentElem_eq_of_ker_isNilpotent f h b hb hb', ?_⟩
  intro e e' he he' h1 h2
  exact exists_unit_conj_of_map_eq_idempotent f h he he' (h1.trans h2.symm)

end Idempotents

end UndergradKB.RepresentationTheory
