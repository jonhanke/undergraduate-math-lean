import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Semisimple
import UndergradKB.Common.Attr

/-! # A representation is determined by its character (Etingof et al., Corollary 3.7)

In characteristic zero, two finite-dimensional representations of a finite group with the same
character are isomorphic.

The proof is by strong induction on the dimension.  Equality of characters gives, via the formula
`dim Hom_G(τ, ρ) = |G|⁻¹ ∑ χ_ρ(g) χ_τ(g⁻¹)`, equality of `dim Hom_G(τ, ρ)` and `dim Hom_G(τ, σ)`
for every `τ`.  Taking `τ` to be a minimal nonzero subrepresentation `S` of `ρ`, there is a nonzero
(hence injective) intertwining map `S → σ`.  By Maschke's theorem both `ρ` and `σ` split off a copy
of `S`, the complements have equal characters, and induction applies to them.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Representation Module

section helpers

variable {k G : Type*} [Field k] [Group G]

/-- The character of a product representation is the sum of the characters. -/
lemma char_prod {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g := by
  show LinearMap.trace k _ (LinearMap.prodMap (ρ g) (σ g)) = LinearMap.trace k _ (ρ g) + LinearMap.trace k _ (σ g)
  exact LinearMap.trace_prodMap' _ _

/-- A complement of subrepresentations is a complement of the underlying submodules. -/
lemma isCompl_toSubmodule {V : Type*} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
    {S T : Subrepresentation ρ} (h : IsCompl S T) : IsCompl S.toSubmodule T.toSubmodule := by
  refine IsCompl.of_eq ?_ ?_
  · exact congrArg Subrepresentation.toSubmodule h.inf_eq_bot
  · exact congrArg Subrepresentation.toSubmodule h.sup_eq_top

/-- If `S` and `T` are complementary subrepresentations of `ρ`, then `ρ ≅ S × T`. -/
noncomputable def prodEquivOfIsCompl {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k G V} (S T : Subrepresentation ρ) (h : IsCompl S T) :
    Representation.Equiv (S.toRepresentation.prod T.toRepresentation) ρ :=
  Representation.Equiv.mk
    (Submodule.prodEquivOfIsCompl S.toSubmodule T.toSubmodule (isCompl_toSubmodule h))
    (fun g => LinearMap.ext fun x => by
      show ((S.toRepresentation g x.1 : V) + (T.toRepresentation g x.2 : V)) =
        ρ g ((x.1 : V) + (x.2 : V))
      rw [map_add]
      rfl)

/-- Product of equivalences of representations. -/
noncomputable def equivProd {V₁ V₂ W₁ W₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup W₁] [Module k W₁] [AddCommGroup W₂]
    [Module k W₂] {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {τ₁ : Representation k G W₁} {τ₂ : Representation k G W₂}
    (φ : Representation.Equiv ρ₁ τ₁) (ψ : Representation.Equiv ρ₂ τ₂) :
    Representation.Equiv (ρ₁.prod ρ₂) (τ₁.prod τ₂) :=
  Representation.Equiv.mk (φ.toLinearEquiv.prodCongr ψ.toLinearEquiv)
    (fun g => LinearMap.ext fun x => Prod.ext (by exact IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g x.1)
      (by exact IntertwiningMap.isIntertwining _ _ ψ.toIntertwiningMap g x.2))

/-- In characteristic zero, equal characters give equal dimensions of the spaces of
intertwining maps out of any representation. -/
lemma finrank_intertwiningMap_eq [CharZero k] [Fintype G] {X V W : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (τ : Representation k G X) (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) :
    finrank k (IntertwiningMap τ ρ) = finrank k (IntertwiningMap τ σ) := by
  have : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank τ ρ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank τ σ
  rw [h] at h1
  exact Nat.cast_injective (R := k) (h1.symm.trans h2)

/-- A nonzero finite-dimensional representation has a minimal nonzero subrepresentation. -/
lemma exists_minimal_subrepresentation {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V) :
    ∃ S : Subrepresentation ρ, S ≠ ⊥ ∧ ∀ T : Subrepresentation ρ, T ≤ S → T = ⊥ ∨ T = S := by
  obtain ⟨S, hS, hmin⟩ := (measure fun S : Subrepresentation ρ => finrank k S.toSubmodule).wf.has_min
    {S | S ≠ ⊥} ⟨⊤, fun e => top_ne_bot (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨S, hS, fun T hT => ?_⟩
  by_contra hne
  push Not at hne
  refine hmin T hne.1 ?_
  have hlt : T.toSubmodule < S.toSubmodule :=
    lt_of_le_of_ne (fun x hx => hT hx)
      (fun e => hne.2 (Subrepresentation.toSubmodule_injective e))
  exact Submodule.finrank_lt_finrank_of_lt hlt

/-- A nonzero intertwining map out of a minimal subrepresentation is injective. -/
lemma injective_of_minimal {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] {ρ : Representation k G V} {σ : Representation k G W} (S : Subrepresentation ρ)
    (hmin : ∀ T : Subrepresentation ρ, T ≤ S → T = ⊥ ∨ T = S)
    (f : IntertwiningMap S.toRepresentation σ) (hf : f ≠ 0) : Function.Injective f := by
  let K : Subrepresentation ρ :=
    { toSubmodule := (f.ker).toSubmodule.map S.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨x, hx, rfl⟩
        exact ⟨S.toRepresentation g x, f.ker.apply_mem_toSubmodule g hx, rfl⟩ }
  have hKS : K ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rcases hmin K hKS with h | h
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hxK : (x : V) ∈ K := ⟨x, hx, rfl⟩
    rw [h] at hxK
    exact Subtype.ext hxK
  · exfalso
    apply hf
    refine IntertwiningMap.ext (LinearMap.ext fun x => ?_)
    have hxK : (x : V) ∈ K := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hxK
    have : y = x := Subtype.ext hyx
    subst this
    exact hy

end helpers

section main

variable {k G : Type*} [Field k] [CharZero k] [Group G] [Fintype G]

private theorem character_determines_aux : ∀ (n : ℕ) (V : Type u) (W : Type v)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    finrank k V = n → ρ.character = σ.character → Nonempty (Representation.Equiv ρ σ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ ρ σ hn h
  have : NeZero (Nat.card G : k) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hW : finrank k W = 0 := by
      have h1 := congrFun h 1
      simp only [char_one] at h1
      rw [hn] at h1
      exact_mod_cast h1.symm
    have : Subsingleton V := Module.finrank_zero_iff.mp hn
    have : Subsingleton W := Module.finrank_zero_iff.mp hW
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton V W)
      (fun g => LinearMap.ext fun x => Subsingleton.elim _ _)⟩
  · have : Nontrivial V := Module.finrank_pos_iff.mp (show 0 < finrank k V by omega)
    obtain ⟨S, hS, hmin⟩ := exists_minimal_subrepresentation (k := k) ρ
    have hSne : S.toSubmodule ≠ ⊥ := fun e => hS (Subrepresentation.ext e)
    -- inclusion of `S` into `ρ`
    let incl : IntertwiningMap S.toRepresentation ρ :=
      ⟨S.toSubmodule.subtype, fun g => LinearMap.ext fun x => rfl⟩
    have hincl : incl ≠ 0 := by
      intro e
      apply hSne
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have := DFunLike.congr_fun e ⟨x, hx⟩
      simpa [incl] using this
    have hpos1 : 0 < finrank k (IntertwiningMap S.toRepresentation ρ) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨incl, hincl⟩
    rw [finrank_intertwiningMap_eq S.toRepresentation ρ σ h] at hpos1
    obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos1
    have hinj : Function.Injective f.toLinearMap := injective_of_minimal S hmin f hf
    let S' : Subrepresentation σ := f.range
    let eS : Representation.Equiv S.toRepresentation S'.toRepresentation :=
      Representation.Equiv.mk (LinearEquiv.ofInjective f.toLinearMap hinj)
        (fun g => LinearMap.ext fun x => Subtype.ext (IntertwiningMap.isIntertwining _ _ f g x))
    obtain ⟨T, hT⟩ := ComplementedLattice.exists_isCompl S
    obtain ⟨U, hU⟩ := ComplementedLattice.exists_isCompl S'
    let eρ := prodEquivOfIsCompl S T hT
    let eσ := prodEquivOfIsCompl S' U hU
    have hdim : finrank k V = finrank k S.toSubmodule + finrank k T.toSubmodule := by
      rw [← LinearEquiv.finrank_eq eρ.toLinearEquiv, Module.finrank_prod]
    have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hSne
    have hSpos : 0 < finrank k S.toSubmodule := Module.finrank_pos
    have hchar : T.toRepresentation.character = U.toRepresentation.character := by
      funext g
      have h1 := char_iso eρ.symm
      have h2 := char_iso eσ.symm
      have h3 := char_iso eS
      have a := congrFun h1 g
      have b := congrFun h2 g
      have c := congrFun h3 g
      have d := congrFun h g
      rw [← char_iso eρ, char_prod] at d
      rw [← char_iso eσ, char_prod] at d
      linear_combination d - c
    obtain ⟨eTU⟩ := ih (finrank k T.toSubmodule) (by omega) T.toSubmodule U.toSubmodule
      T.toRepresentation U.toRepresentation rfl hchar
    exact ⟨eρ.symm.trans ((equivProd eS eTU).trans eσ)⟩

end main

variable {k G V W : Type*} [Field k] [CharZero k] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]

/-- **Etingof et al., Corollary 3.7**: over a field of characteristic zero, a finite-dimensional
representation of a finite group is determined up to isomorphism by its character: two such
representations with the same character are isomorphic. -/
@[kb "etingof2011" "Corollary 3.7, p. 35"]
theorem nonempty_equiv_of_character_eq
    (ρ : Representation k G V) (σ : Representation k G W) (h : ρ.character = σ.character) :
    Nonempty (Representation.Equiv ρ σ) :=
  character_determines_aux _ V W ρ σ rfl h

/-- Isomorphic representations have equal characters, and conversely in characteristic zero. -/
theorem nonempty_equiv_iff_character_eq_of_charZero
    (ρ : Representation k G V) (σ : Representation k G W) :
    Nonempty (Representation.Equiv ρ σ) ↔ ρ.character = σ.character :=
  ⟨fun ⟨φ⟩ => Representation.char_iso φ, nonempty_equiv_of_character_eq ρ σ⟩

end UndergradKB.RepresentationTheory
