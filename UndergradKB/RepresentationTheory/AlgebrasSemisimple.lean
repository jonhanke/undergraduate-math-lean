import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Algebra.Pi
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.AlgebrasChapter2

/-! # Radical, finiteness of simple modules and semisimplicity criteria (Etingof et al., §2.5-2.6)

Over an algebraically closed field `k`, a finite-dimensional algebra `A` has only finitely many simple modules up
to isomorphism, `A / Rad(A)` is the product of the endomorphism algebras of the simple modules, and the
following are equivalent: `Rad(A) = 0`, `∑ (dim Vᵢ)² = dim A`, `A` is a product of matrix algebras, `A` is
semisimple, and every module is semisimple.
-/

namespace UndergradKB.RepresentationTheory

open Module

universe u

section Family

variable {k : Type u} {A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] {ι : Type*} [Fintype ι]
  {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module k (V i)]
  [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]

variable (k A V) in
/-- The action of `A` on a family of modules, as an algebra map `A → ∏ End_k Vᵢ`. -/
noncomputable def actionPi : A →ₐ[k] ∀ i, Module.End k (V i) :=
  AlgHom.pi fun i => (Algebra.lsmul k k (V i) : A →ₐ[k] Module.End k (V i))

theorem actionPi_apply (a : A) (i : ι) : actionPi k A V a i = Algebra.lsmul k k (V i) a := rfl

/-- If the family `Vᵢ` contains every simple module up to isomorphism, then an element acts by zero on all `Vᵢ`
exactly when it lies in the radical. -/
theorem actionPi_eq_zero_iff
    (hcomp : ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] V i))
    (a : A) : actionPi k A V a = 0 ↔ a ∈ algebraRadical A := by
  rw [mem_algebraRadical_iff]
  constructor
  · intro h S _ _ _ v
    obtain ⟨i, ⟨e⟩⟩ := hcomp S
    apply e.injective
    have := congrArg (fun φ => φ i (e v)) h
    simp only [actionPi_apply, Pi.zero_apply, LinearMap.zero_apply] at this
    simpa using this
  · intro h
    funext i
    ext v
    exact h (V i) v

variable (k) in
/-- **Etingof et al., Theorem 2.12 (second part)**: if `V₁, …, Vₙ` are the simple modules of the finite-dimensional
algebra `A` up to isomorphism, then `A / Rad(A) ≅ ∏ End Vᵢ`. -/
@[kb "etingof2011" "Theorem 2.12, p. 26"]
noncomputable def quotientRadicalEquivPi
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (hcomp : ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] V i)) :

    (A ⧸ algebraRadical A) ≃ₐ[k] ∀ i, Module.End k (V i) := by
  classical
  have hker : RingHom.ker (actionPi k A V) = algebraRadical A := by
    ext a
    rw [RingHom.mem_ker]
    exact actionPi_eq_zero_iff hcomp a
  have hsurj : Function.Surjective (actionPi k A V) := density_pi_surjective hV
  exact (Ideal.quotientEquivAlgOfEq k hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)

/-- **Etingof et al., Proposition 2.16, (i) ⇔ (ii)**: for a finite-dimensional algebra with a complete list
`V₁, …, Vₙ` of simple modules, `∑ (dim Vᵢ)² = dim A` exactly when the radical vanishes. -/
@[kb "etingof2011" "Proposition 2.16, p. 27"]
theorem sum_finrank_sq_eq_finrank_iff [FiniteDimensional k A]
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (hcomp : ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] V i)) :
    ∑ i, finrank k (V i) ^ 2 = finrank k A ↔ algebraRadical A = ⊥ := by
  classical
  have hsurj : Function.Surjective (actionPi k A V) := density_pi_surjective hV
  have hrn := LinearMap.finrank_range_add_finrank_ker (actionPi k A V).toLinearMap
  have hrange : LinearMap.range (actionPi k A V).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  rw [hrange, finrank_top, Module.finrank_pi_fintype] at hrn
  have hsum : ∑ i, finrank k (Module.End k (V i)) = ∑ i, finrank k (V i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.finrank_linearMap, sq]
  rw [hsum] at hrn
  have hker : LinearMap.ker (actionPi k A V).toLinearMap = ⊥ ↔ algebraRadical A = ⊥ := by
    have key : ∀ a, a ∈ LinearMap.ker (actionPi k A V).toLinearMap ↔ a ∈ algebraRadical A := by
      intro a
      rw [LinearMap.mem_ker, ← actionPi_eq_zero_iff (k := k) hcomp]
      rfl
    simp only [Submodule.eq_bot_iff, key]
  rw [← hker, ← Submodule.finrank_eq_zero (R := k)]
  omega

end Family

section Criteria

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

variable (k) in
include k in
/-- **Etingof et al., Proposition 2.16, (i) ⇔ (v)**: a finite-dimensional algebra is semisimple, i.e. completely
reducible as a module over itself, exactly when its radical is zero. -/
@[kb "etingof2011" "Proposition 2.16, p. 27"]
theorem isSemisimpleRing_iff_algebraRadical_eq_bot : IsSemisimpleRing A ↔ algebraRadical A = ⊥ := by
  have := IsArtinianRing.of_finite k A
  rw [algebraRadical_eq_jacobson]
  exact IsArtinianRing.isSemisimpleRing_iff_jacobson

/-- **Etingof et al., Proposition 2.16, (i) ⇔ (iii)**: over an algebraically closed field, a finite-dimensional
algebra is semisimple exactly when it is isomorphic to a product of matrix algebras. -/
@[kb "etingof2011" "Proposition 2.16, p. 27"]
theorem isSemisimpleRing_iff_exists_algEquiv_pi_matrix [IsAlgClosed k] :
    IsSemisimpleRing A ↔ ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k) := by
  constructor
  · intro h
    exact IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k A
  · rintro ⟨n, d, -, ⟨e⟩⟩
    exact isSemisimpleRing_iff_pi_matrix_divisionRing.2 ⟨n, fun _ => k, d, fun _ => inferInstance,
      ⟨e.toRingEquiv⟩⟩

omit [Field k] [Algebra k A] [FiniteDimensional k A] in
/-- **Etingof et al., Proposition 2.16 (every module of a semisimple algebra is completely reducible)**:
semisimplicity of `A` is equivalent to complete reducibility of every `A`-module. -/
@[kb "etingof2011" "Proposition 2.16, p. 27"]
theorem isSemisimpleRing_iff_forall_isSemisimpleModule :
    IsSemisimpleRing A ↔ ∀ (M : Type u) [AddCommGroup M] [Module A M], IsSemisimpleModule A M :=
  ⟨fun _ _ _ _ => inferInstance, fun h => h A⟩

end Criteria

section Tfae

variable {k : Type u} {A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {ι : Type*} [Fintype ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)]
  [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)]
  [∀ i, FiniteDimensional k (V i)]

/-- **Etingof et al., Proposition 2.16**: for a finite-dimensional algebra `A` over an algebraically closed field
with `V₁, …, Vₙ` its simple modules up to isomorphism, the following are equivalent: (1) `Rad(A) = 0`;
(2) `∑ (dim Vᵢ)² = dim A`; (3) `A` is a product of matrix algebras; (4) every `A`-module is completely
reducible; (5) `A` is completely reducible as a module over itself. -/
@[kb "etingof2011" "Proposition 2.16, p. 27"]
theorem semisimple_tfae (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j))
    (hcomp : ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S],
      ∃ i, Nonempty (S ≃ₗ[A] V i)) :
    List.TFAE
      [ algebraRadical A = ⊥,
        ∑ i, finrank k (V i) ^ 2 = finrank k A,
        ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
          Nonempty (A ≃ₐ[k] ∀ i, Matrix (Fin (d i)) (Fin (d i)) k),
        ∀ (M : Type u) [AddCommGroup M] [Module A M], IsSemisimpleModule A M,
        IsSemisimpleModule A A ] := by
  tfae_have 2 ↔ 1 := sum_finrank_sq_eq_finrank_iff hV hcomp
  tfae_have 1 ↔ 5 := (isSemisimpleRing_iff_algebraRadical_eq_bot k).symm
  tfae_have 3 ↔ 5 := (isSemisimpleRing_iff_exists_algEquiv_pi_matrix (k := k) (A := A)).symm
  tfae_have 4 ↔ 5 := (isSemisimpleRing_iff_forall_isSemisimpleModule (A := A)).symm
  tfae_finish

end Tfae

section Finiteness

variable {k : Type u} {A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {ι : Type*} {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module k (V i)]
  [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]

/-- **Etingof et al., Theorem 2.12 (first part)**: a finite-dimensional algebra has only finitely many
simple modules up to isomorphism: any family of pairwise non-isomorphic finite-dimensional simple modules is finite,
with at most `dim A` members. -/
@[kb "etingof2011" "Theorem 2.12, p. 26"]
theorem finite_of_pairwise_nonIso (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Finite ι ∧ Nat.card ι ≤ finrank k A := by
  classical
  have hle : ∀ s : Finset ι, s.card ≤ finrank k A := by
    intro s
    have h := sum_finrank_sq_le_finrank (k := k) (A := A) (V := fun x : s => V x)
      (fun i j hij => hV i j (fun h => hij (Subtype.ext h)))
    have : s.card ≤ ∑ i : s, finrank k (V i) ^ 2 := by
      calc s.card = ∑ _i : s, 1 := by simp
        _ ≤ ∑ i : s, finrank k (V i) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : Nontrivial (V i) := IsSimpleModule.nontrivial A (V i)
          have := Module.finrank_pos (R := k) (M := V i)
          nlinarith
    omega
  have hfin : Finite ι := by
    by_contra h
    have : Infinite ι := not_finite_iff_infinite.1 h
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι (finrank k A + 1)
    have := hle s
    omega
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  exact hle Finset.univ

end Finiteness

end UndergradKB.RepresentationTheory
