import UndergradKB.RepresentationTheory.ModulesChapter7
import UndergradKB.RepresentationTheory.ProjectiveCovers
import UndergradKB.RepresentationTheory.ProjectiveCoversMore
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 7 (structure of finite-dimensional algebras), repository proofs

Thin theorems in the book's terms for the items of Chapter 7 that are proved in this repository
(characterisations of projective modules, lifting of idempotents, and the indecomposable projective
modules of a finite-dimensional algebra), each tagged with the source key `etingof2011` and the
locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open Module UndergradKB.RepresentationTheory

universe u v

/-- Etingof et al., Theorem 7.1: for a module `P` the following are equivalent: `P` is projective, maps out
of `P` lift along surjections, every surjection onto `P` splits, `P` is a direct summand of a free module,
and `Hom_A(P, -)` preserves surjections. -/
@[kb "etingof2011" "Theorem 7.1, p. 106"]
theorem etingof_7_1 (A : Type u) (P : Type v) [Ring A] [AddCommGroup P] [Module A P] [Small.{v} A] :
    List.TFAE
      [ Module.Projective A P,
        ∀ (M N : Type v) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
          (f : M →ₗ[A] N) (g : P →ₗ[A] N), Function.Surjective f → ∃ h : P →ₗ[A] M, f ∘ₗ h = g,
        ∀ (M : Type v) [AddCommGroup M] [Module A M] (s : M →ₗ[A] P), Function.Surjective s →
          ∃ i : P →ₗ[A] M, s ∘ₗ i = LinearMap.id,
        ∃ (ι : Type v) (i : P →ₗ[A] (ι →₀ A)) (s : (ι →₀ A) →ₗ[A] P), s ∘ₗ i = LinearMap.id,
        ∀ (M N : Type v) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
          (f : M →ₗ[A] N), Function.Surjective f →
            Function.Surjective (fun h : P →ₗ[A] M => f ∘ₗ h) ] :=
  projective_tfae A P

/-- Etingof et al., Proposition 7.3: along a ring map whose kernel consists of nilpotent elements, every
idempotent in the image lifts to an idempotent, and any two idempotent lifts are conjugate by a unit
congruent to one modulo the kernel. -/
@[kb "etingof2011" "Proposition 7.3, p. 106"]
theorem etingof_7_3 {A B : Type*} [Ring A] [Ring B] (f : A →+* B)
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x) {b : B}
    (hb : b ∈ f.range) (hb' : IsIdempotentElem b) :
    (∃ e : A, IsIdempotentElem e ∧ f e = b) ∧
      ∀ e e' : A, IsIdempotentElem e → IsIdempotentElem e' → f e = b → f e' = b →
        ∃ u : Aˣ, f u = 1 ∧ (u : A) * e' = e * u :=
  idempotent_lift_and_conjugate f h hb hb'

section Theorem76

variable {k : Type u} {A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)]
  [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
  [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]

/-- Etingof et al., Theorem 7.6: for each simple module in a complete list there is an idempotent `e` such
that the left ideal `A e` is projective with `dim Hom_A(A e, V_j)` equal to one for the chosen simple and
zero for the others. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem etingof_7_6_a
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (hcomp : ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] V i))
    (i : ι) :
    ∃ e : A, IsIdempotentElem e ∧ Module.Projective A (Ideal.span {e}) ∧
      ∀ j, finrank k (Ideal.span {e} →ₗ[A] V j) = if j = i then 1 else 0 :=
  exists_projective_finrank_hom_eq_ite hV hcomp i

/-- Etingof et al., Theorem 7.6: the indecomposable projectives `P_i = A e_i` exist, `A` is a direct sum of
`dim V_i` copies of `P_i`, and every finite-dimensional indecomposable projective module is isomorphic to
some `P_i`. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem etingof_7_6_b
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) (hcomp : SimpleComplete A V) :
    ∃ e : ι → A,
      (∀ i, IsIdempotentElem (e i) ∧ Module.Projective A (Ideal.span {e i}) ∧
        IsTopModule k A V i (Ideal.span {e i}) ∧ IsIndecomposableModule A (Ideal.span {e i})) ∧
      (∃ (T : Type) (c : T → ι), Finite T ∧ Nonempty (A ≃ₗ[A] ∀ t, Ideal.span {e (c t)}) ∧
        ∀ j, Nat.card {t // c t = j} = finrank k (V j)) ∧
      (∀ (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
        [FiniteDimensional k P] [Module.Projective A P], IsIndecomposableModule A P →
        ∃ i, Nonempty (P ≃ₗ[A] Ideal.span {e i})) :=
  exists_indecomposable_projectives hV hcomp

end Theorem76

section Theorem76Core

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {ι : Type*} [DecidableEq ι]
  {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module k (V i)]
  [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]
  {P : Type u} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
  [FiniteDimensional k P] {i : ι}

/-- Etingof et al., Theorem 7.6: a module with `dim Hom_A(P, V_j)` equal to the Kronecker delta of the
chosen simple has a unique maximal submodule, hence is indecomposable. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem etingof_7_6_c (hcomp : SimpleComplete A V) (hP : IsTopModule k A V i P) :
    IsIndecomposableModule A P :=
  IsTopModule.isIndecomposable hcomp hP

/-- Etingof et al., Theorem 7.6: two projective modules with the same Hom-dimensions into the simples are
isomorphic. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem etingof_7_6_d {Q : Type u} [AddCommGroup Q] [Module A Q] [Module k Q]
    [IsScalarTower k A Q] [FiniteDimensional k Q]
    (hcomp : SimpleComplete A V) (hP : IsTopModule k A V i P)
    (hQ : IsTopModule k A V i Q) [Module.Projective A P] [Module.Projective A Q] :
    Nonempty (P ≃ₗ[A] Q) :=
  IsTopModule.nonempty_equiv hcomp hP hQ

/-- Etingof et al., Theorem 7.6: if `F j` are projective modules realising each Kronecker delta, every
indecomposable finite-dimensional projective module is isomorphic to one of them. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem etingof_7_6_e (hcomp : SimpleComplete A V)
    (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)] [∀ i, Module k (F i)]
    [∀ i, IsScalarTower k A (F i)] [∀ i, FiniteDimensional k (F i)]
    [∀ i, Module.Projective A (F i)]
    (hF : ∀ i, IsTopModule k A V i (F i))
    (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [FiniteDimensional k P] [Module.Projective A P] (hP : IsIndecomposableModule A P) :
    ∃ j, Nonempty (P ≃ₗ[A] F j) :=
  exists_equiv_of_indecomposable F hcomp hF P hP

end Theorem76Core

end UndergradKB.RepresentationTheory.Course
