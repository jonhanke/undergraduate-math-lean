import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.CharactersMore
import UndergradKB.RepresentationTheory.ComplexCharacters
import UndergradKB.RepresentationTheory.Induced

/-! # Representations of semidirect products with an abelian factor: the little group method
(Etingof et al., Section 4.26)
-/

set_option linter.unusedSectionVars false

universe u v w

namespace UndergradKB.RepresentationTheory

open Representation Module

section LittleGroup

variable {A : Type u} {G : Type v} [CommGroup A] [Group G] (φ : G →* MulAut A) (x : A →* ℂˣ)

/-- The stabilizer `G_x` of a character `x` of `A` under the action of `G` on the dual of `A`
(`g` fixes `x` iff `x (g a) = x a` for all `a`). -/
def stabChar : Subgroup G where
  carrier := {g | ∀ a, x (φ g a) = x a}
  mul_mem' := by
    intro g h hg hh a
    show x (φ (g * h) a) = x a
    rw [map_mul, MulAut.mul_apply, hg, hh]
  one_mem' := by intro a; simp
  inv_mem' := by
    intro g hg a
    show x (φ g⁻¹ a) = x a
    have := hg (φ g⁻¹ a)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
    exact this.symm

lemma mem_stabChar {g : G} : g ∈ stabChar φ x ↔ ∀ a, x (φ g a) = x a := Iff.rfl

/-- The subgroup `A ⋊ G_x` of `A ⋊ G`. -/
def littleSub : Subgroup (A ⋊[φ] G) := (stabChar φ x).comap SemidirectProduct.rightHom

lemma mem_littleSub {s : A ⋊[φ] G} : s ∈ littleSub φ x ↔ s.right ∈ stabChar φ x := Iff.rfl

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (U : Representation ℂ (stabChar φ x) W)

/-- The representation of `A ⋊ G_x` on `W`, with `(a, h)` acting by `x(a) · U(h)` (the book's `U` with `A` acting by
the character `x`). -/
noncomputable def littleRep : Representation ℂ (littleSub φ x) W where
  toFun s := ((x s.1.left : ℂˣ) : ℂ) • U ⟨s.1.right, s.2⟩
  map_one' := by
    ext w
    have e : ∀ h, (⟨1, h⟩ : stabChar φ x) = 1 := fun _ => rfl
    simp [e]
  map_mul' s t := by
    ext w
    have h1 : x (φ s.1.right t.1.left) = x t.1.left := s.2 t.1.left
    have h3 := congrArg (fun f => f w) (map_mul U ⟨s.1.right, s.2⟩ ⟨t.1.right, t.2⟩)
    simp only [mul_apply_eq_comp] at h3
    simp only [Subgroup.coe_mul, SemidirectProduct.mul_left, map_mul, Units.val_mul, h1]
    simp only [mul_apply_eq_comp, LinearMap.smul_apply, map_smul, smul_smul]
    rw [mul_comm]
    congr 1

section Character

variable [Fintype A] [Fintype G]

/-- `A ⋊ G` is finite when `A` and `G` are. -/
noncomputable instance : Fintype (A ⋊[φ] G) := Fintype.ofEquiv (A × G) SemidirectProduct.equivProd.symm

theorem sum_semidirect {M : Type*} [AddCommMonoid M] (f : A ⋊[φ] G → M) :
    ∑ s : A ⋊[φ] G, f s = ∑ l : A, ∑ g : G, f ⟨l, g⟩ := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv SemidirectProduct.equivProd _ _ (fun s => rfl)

variable [FiniteDimensional ℂ W]

theorem character_littleRep (s : littleSub φ x) :
    (littleRep φ x U).character s = (x s.1.left : ℂ) * U.character ⟨s.1.right, s.2⟩ := by
  simp [Representation.character, littleRep, map_smul]

theorem charExt_little (s : A ⋊[φ] G) :
    charExt (littleSub φ x) (littleRep φ x U) s = (x s.left : ℂ) * charExt (stabChar φ x) U s.right := by
  classical
  by_cases hs : s.right ∈ stabChar φ x
  · rw [charExt_of_mem _ _ (show s ∈ littleSub φ x from hs), charExt_of_mem _ _ hs, character_littleRep]
  · rw [charExt_of_not_mem _ _ (show s ∉ littleSub φ x from hs), charExt_of_not_mem _ _ hs, mul_zero]

theorem conj_semidirect (b l : A) (k g : G) :
    ((⟨b, k⟩ : A ⋊[φ] G) * ⟨l, g⟩ * ⟨b, k⟩⁻¹).left = b * φ k l * φ (k * g * k⁻¹) b⁻¹ ∧
    ((⟨b, k⟩ : A ⋊[φ] G) * ⟨l, g⟩ * ⟨b, k⟩⁻¹).right = k * g * k⁻¹ := by
  refine ⟨?_, ?_⟩
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      map_mul, MulAut.mul_apply, map_inv]
  · simp

theorem charExt_little_conj (b l : A) (k g : G) :
    charExt (littleSub φ x) (littleRep φ x U) ((⟨b, k⟩ : A ⋊[φ] G) * ⟨l, g⟩ * ⟨b, k⟩⁻¹) =
      (x (φ k l) : ℂ) * charExt (stabChar φ x) U (k * g * k⁻¹) := by
  rw [charExt_little, (conj_semidirect φ b l k g).1, (conj_semidirect φ b l k g).2]
  by_cases hc : k * g * k⁻¹ ∈ stabChar φ x
  · congr 1
    have h : x (φ (k * g * k⁻¹) b⁻¹) = x b⁻¹ := hc b⁻¹
    rw [map_mul, map_mul, h]
    simp
  · rw [charExt_of_not_mem _ _ hc, mul_zero, mul_zero]

theorem card_littleSub : Nat.card (littleSub φ x) = Nat.card A * Nat.card (stabChar φ x) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun s => (s.1.left, ⟨s.1.right, s.2⟩)
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := fun s => rfl
      right_inv := fun p => rfl }

theorem character_littleInd (l : A) (g : G) :
    (Ind (littleSub φ x) (littleRep φ x U)).character ⟨l, g⟩ =
      (Nat.card (stabChar φ x) : ℂ)⁻¹ * ∑ k : G, (x (φ k l) : ℂ) * charExt (stabChar φ x) U (k * g * k⁻¹) := by
  have hA : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hS : (Nat.card (stabChar φ x) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card (littleSub φ x) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Fintype (RCosets (littleSub φ x)) := Fintype.ofFinite _
  rw [character_Ind_averaged, sum_semidirect]
  simp only [charExt_little_conj]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, invOf_eq_inv,
    card_littleSub, Nat.cast_mul]
  field_simp

end Character

section Norm

open scoped ComplexConjugate

variable [Fintype A] [Fintype G]

theorem conj_char (a : A) : (starRingEnd ℂ) ((x a : ℂˣ) : ℂ) = (((x a)⁻¹ : ℂˣ) : ℂ) := by
  have h1 : ((x a : ℂˣ) : ℂ) ^ Fintype.card A = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  have h2 : ‖((x a : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
  have h3 : (starRingEnd ℂ) ((x a : ℂˣ) : ℂ) * ((x a : ℂˣ) : ℂ) = 1 := by
    rw [Complex.conj_mul', h2]; simp
  rw [Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_left h3

theorem sum_char_eq_zero (l : A →* ℂˣ) (h : l ≠ 1) : ∑ a : A, ((l a : ℂˣ) : ℂ) = 0 := by
  obtain ⟨b, hb⟩ : ∃ b, l b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h (MonoidHom.ext fun a => by simpa using hcon a)
  have h1 : ∑ a : A, ((l a : ℂˣ) : ℂ) = ((l b : ℂˣ) : ℂ) * ∑ a : A, ((l a : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum]
    exact (Fintype.sum_equiv (Equiv.mulLeft b) _ _ (fun a => by simp)).symm
  have hb' : ((l b : ℂˣ) : ℂ) ≠ 1 := fun e => hb (Units.ext e)
  have : (1 - ((l b : ℂˣ) : ℂ)) * ∑ a : A, ((l a : ℂˣ) : ℂ) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hb'))

open scoped Classical in
theorem alpha_sum (k k' : G) :
    ∑ l : A, (x (φ k l) : ℂ) * (starRingEnd ℂ) (x (φ k' l) : ℂ) =
      if k * k'⁻¹ ∈ stabChar φ x then (Nat.card A : ℂ) else 0 := by
  classical
  set c := k * k'⁻¹ with hc
  let lam : A →* ℂˣ := (x.comp (φ c).toMonoidHom) / x
  have hlam : ∀ m, ((lam m : ℂˣ) : ℂ) = (x (φ c m) : ℂ) * (((x m)⁻¹ : ℂˣ) : ℂ) := by
    intro m
    simp [lam, div_eq_mul_inv]
  have e1 : ∑ l : A, (x (φ k l) : ℂ) * (starRingEnd ℂ) (x (φ k' l) : ℂ) = ∑ m : A, ((lam m : ℂˣ) : ℂ) := by
    refine Fintype.sum_equiv (φ k').toEquiv _ _ (fun l => ?_)
    rw [conj_char, hlam]
    have : φ c (φ k' l) = φ k l := by
      rw [← MulAut.mul_apply, ← map_mul, hc, inv_mul_cancel_right]
    rw [MulEquiv.toEquiv_eq_coe]
    simp only [MulEquiv.coe_toEquiv]
    rw [this]
  rw [e1]
  by_cases hmem : c ∈ stabChar φ x
  · rw [if_pos hmem]
    have : lam = 1 := by
      ext m
      simp [lam, div_eq_mul_inv, hmem m]
    simp [this, Nat.card_eq_fintype_card]
  · rw [if_neg hmem]
    apply sum_char_eq_zero
    intro hl
    apply hmem
    intro m
    have := congrArg (fun f : A →* ℂˣ => f m) hl
    simp only [lam, MonoidHom.div_apply, MonoidHom.comp_apply, MonoidHom.one_apply] at this
    exact (div_eq_one.mp this)

end Norm

end LittleGroup

end UndergradKB.RepresentationTheory
