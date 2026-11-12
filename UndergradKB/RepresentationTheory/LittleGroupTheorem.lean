import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.LittleGroup
import UndergradKB.RepresentationTheory.CharacterDetermines
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Semisimple

/-! # Irreducibility in the little group method (Etingof et al., Theorem 4.75)

* `isIrreducible_of_hermitianPairing_self_eq_one`: a finite-dimensional complex representation of a finite group
  whose character has Hermitian norm `1` is irreducible (the norm of a sum of two nonzero subrepresentations is at
  least `2`, by Maschke and Theorem 3.8).
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open Representation Module

section NormOne

variable {G : Type*} [Group G] [Fintype G]

lemma hermitianPairing_add_left (f₁ f₂ f : G → ℂ) :
    hermitianPairing (f₁ + f₂) f = hermitianPairing f₁ f + hermitianPairing f₂ f := by
  simp only [hermitianPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma hermitianPairing_add_right (f₁ f₂ f : G → ℂ) :
    hermitianPairing f (f₁ + f₂) = hermitianPairing f f₁ + hermitianPairing f f₂ := by
  simp only [hermitianPairing, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The identity is a nonzero self-intertwiner of a nonzero representation. -/
lemma one_le_finrank_intertwiningMap_self (ρ : Representation ℂ G V) [Nontrivial V] :
    1 ≤ finrank ℂ (IntertwiningMap ρ ρ) := by
  refine Nat.one_le_iff_ne_zero.2 (Module.finrank_pos_iff_exists_ne_zero.2 ⟨IntertwiningMap.id ρ, ?_⟩).ne'
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (by simpa using congrArg (fun f : IntertwiningMap ρ ρ => f v) h)

/-- **Etingof et al., Theorem 3.8 (consequence)**: a finite-dimensional complex representation of a finite group
whose character has Hermitian norm `1` is irreducible. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem isIrreducible_of_hermitianPairing_self_eq_one (ρ : Representation ℂ G V)
    (h : hermitianPairing ρ.character ρ.character = 1) : IsIrreducible ρ := by
  have : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have h0 : ρ.character = 0 := by
      funext g
      show LinearMap.trace ℂ V (ρ g) = 0
      rw [Subsingleton.elim (ρ g) 0, map_zero]
    rw [h0] at h
    simp [hermitianPairing] at h
  have hnt : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⊥, ⊤, fun e => ?_⟩
    have := congrArg Subrepresentation.toSubmodule e
    exact bot_ne_top (α := Submodule ℂ V) this
  refine ⟨fun S => ?_⟩
  by_contra hS
  push Not at hS
  obtain ⟨T, hT⟩ := ComplementedLattice.exists_isCompl S
  have hSne : S.toSubmodule ≠ ⊥ := fun e => hS.1 (by
    apply le_antisymm _ bot_le
    intro x hx
    have : x ∈ S.toSubmodule := hx
    rw [e] at this
    exact this)
  have hTne : T.toSubmodule ≠ ⊥ := fun e => hS.2 (by
    have hsup := hT.sup_eq_top
    have : T = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have : x ∈ T.toSubmodule := hx
      rw [e] at this
      exact this
    rw [this, sup_bot_eq] at hsup
    exact hsup)
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hSne
  have : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hTne
  have hchar : ρ.character = S.toRepresentation.character + T.toRepresentation.character := by
    funext g
    rw [← char_iso (prodEquivOfIsCompl S T hT), Pi.add_apply, char_prod]
  rw [hchar, hermitianPairing_add_left, hermitianPairing_add_right, hermitianPairing_add_right,
    hermitianPairing_character_eq_finrank, hermitianPairing_character_eq_finrank,
    hermitianPairing_character_eq_finrank, hermitianPairing_character_eq_finrank] at h
  have h1 := one_le_finrank_intertwiningMap_self S.toRepresentation
  have h2 := one_le_finrank_intertwiningMap_self T.toRepresentation
  have h' : ((finrank ℂ (IntertwiningMap S.toRepresentation S.toRepresentation) +
      finrank ℂ (IntertwiningMap T.toRepresentation S.toRepresentation) +
      (finrank ℂ (IntertwiningMap S.toRepresentation T.toRepresentation) +
      finrank ℂ (IntertwiningMap T.toRepresentation T.toRepresentation)) : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
    push_cast
    exact h
  have := Nat.cast_injective h'
  omega

end NormOne

section LittleNorm

open scoped ComplexConjugate

variable {A : Type*} {G : Type*} [CommGroup A] [Group G] (φ : G →* MulAut A) (x : A →* ℂˣ) [Fintype A]
  [Fintype G] {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (U : Representation ℂ (stabChar φ x) W)

lemma card_semidirectProduct : Nat.card (A ⋊[φ] G) = Nat.card A * Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr SemidirectProduct.equivProd

open scoped Classical in
/-- The number of `k` with `k k'⁻¹` in a subgroup `H` is `|H|`. -/
lemma card_filter_mul_inv_mem (H : Subgroup G) (k' : G) :
    ((Finset.univ.filter fun k : G => k * k'⁻¹ ∈ H).card : ℂ) = Nat.card H := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact congrArg _ (Nat.card_congr ((Equiv.mulRight k'⁻¹).subtypeEquiv fun k => Iff.rfl))

/-- A function supported on a subgroup: its sum over `G` is the sum over the subgroup. -/
lemma sum_charExt_mul_conj (H : Subgroup G) [Fintype H] (σ : Representation ℂ H W) {W' : Type*}
    [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W'] (σ' : Representation ℂ H W') :
    ∑ g : G, charExt H σ g * conj (charExt H σ' g) = ∑ h : H, σ.character h * conj (σ'.character h) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ H)]
  have h0 : ∑ g : {g : G // g ∉ H}, charExt H σ g * conj (charExt H σ' g) = 0 :=
    Finset.sum_eq_zero fun g _ => by rw [charExt_of_not_mem H σ g.2, zero_mul]
  rw [h0, add_zero]
  exact Finset.sum_congr (by ext; simp) fun h _ => by rw [charExt_of_mem H σ h.2, charExt_of_mem H σ' h.2]

/-- The Hermitian inner product of the characters of the little-group representations `V_(O,U)` and `V_(O,U')`
equals that of `U` and `U'` (the computation in the proof of Theorem 4.75, using `alpha_sum`). -/
theorem hermitianPairing_littleInd [Fintype (stabChar φ x)] {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W'] (U' : Representation ℂ (stabChar φ x) W') :
    hermitianPairing (Ind (littleSub φ x) (littleRep φ x U)).character
        (Ind (littleSub φ x) (littleRep φ x U')).character =
      hermitianPairing U.character U'.character := by
  classical
  set E : G → ℂ := charExt (stabChar φ x) U with hE
  set E' : G → ℂ := charExt (stabChar φ x) U' with hE'
  set χ := (Ind (littleSub φ x) (littleRep φ x U)).character with hχdef
  set χ' := (Ind (littleSub φ x) (littleRep φ x U')).character with hχdef'
  have hHc : (Nat.card (stabChar φ x) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hAc : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hGc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hχ : ∀ l g, χ ⟨l, g⟩ =
      (Nat.card (stabChar φ x) : ℂ)⁻¹ * ∑ k : G, ((x (φ k l) : ℂˣ) : ℂ) * E (k * g * k⁻¹) :=
    fun l g => character_littleInd φ x U l g
  have hχ' : ∀ l g, χ' ⟨l, g⟩ =
      (Nat.card (stabChar φ x) : ℂ)⁻¹ * ∑ k : G, ((x (φ k l) : ℂˣ) : ℂ) * E' (k * g * k⁻¹) :=
    fun l g => character_littleInd φ x U' l g
  have hconj : conj ((Nat.card (stabChar φ x) : ℂ)⁻¹) = (Nat.card (stabChar φ x) : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_natCast]
  -- the sum over `l` for fixed `g, k, k'`
  have key : ∀ g k k' : G, ∑ l : A, (((x (φ k l) : ℂˣ) : ℂ) * E (k * g * k⁻¹)) *
      conj (((x (φ k' l) : ℂˣ) : ℂ) * E' (k' * g * k'⁻¹)) =
      (if k * k'⁻¹ ∈ (stabChar φ x) then (Nat.card A : ℂ) else 0) * (E (k * g * k⁻¹) * conj (E' (k' * g * k'⁻¹))) := by
    intro g k k'
    rw [← alpha_sum φ x k k', Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  -- the sum over `k` for fixed `g, k'`
  have key2 : ∀ g k' : G, ∑ k : G, (if k * k'⁻¹ ∈ (stabChar φ x) then (Nat.card A : ℂ) else 0) *
      (E (k * g * k⁻¹) * conj (E' (k' * g * k'⁻¹))) =
      (Nat.card A : ℂ) * Nat.card (stabChar φ x) * (E (k' * g * k'⁻¹) * conj (E' (k' * g * k'⁻¹))) := by
    intro g k'
    have h1 : ∀ k : G, (if k * k'⁻¹ ∈ (stabChar φ x) then (Nat.card A : ℂ) else 0) *
        (E (k * g * k⁻¹) * conj (E' (k' * g * k'⁻¹))) =
        if k * k'⁻¹ ∈ (stabChar φ x) then (Nat.card A : ℂ) * (E (k' * g * k'⁻¹) * conj (E' (k' * g * k'⁻¹))) else 0 := by
      intro k
      split_ifs with hk
      · have := charExt_conj (stabChar φ x) U ⟨k * k'⁻¹, hk⟩ (k' * g * k'⁻¹)
        have e : (k * k'⁻¹) * (k' * g * k'⁻¹) * (k * k'⁻¹)⁻¹ = k * g * k⁻¹ := by group
        simp only [e] at this
        rw [hE, this]
      · rw [zero_mul]
    rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_filter_mul_inv_mem]
    ring
  -- the sum over `g` for fixed `k'`
  have key3 : ∀ k' : G, ∑ g : G, E (k' * g * k'⁻¹) * conj (E' (k' * g * k'⁻¹)) =
      ∑ g : G, E g * conj (E' g) :=
    fun k' => Fintype.sum_equiv (MulAut.conj k').toEquiv _ _ (fun g => by simp [MulAut.conj_apply])
  have total : ∑ s : A ⋊[φ] G, χ s * conj (χ' s) =
      (Nat.card A : ℂ) * Nat.card G * (Nat.card (stabChar φ x) : ℂ)⁻¹ * ∑ g : G, E g * conj (E' g) := by
    rw [sum_semidirect]
    simp only [hχ, hχ', map_mul, hconj, map_sum]
    calc ∑ l : A, ∑ g : G, (Nat.card (stabChar φ x) : ℂ)⁻¹ * (∑ k : G, ((x (φ k l) : ℂˣ) : ℂ) * E (k * g * k⁻¹)) *
          ((Nat.card (stabChar φ x) : ℂ)⁻¹ * ∑ k' : G, conj ((x (φ k' l) : ℂˣ) : ℂ) * conj (E' (k' * g * k'⁻¹)))
        = ∑ g : G, ∑ k' : G, ∑ k : G, (Nat.card (stabChar φ x) : ℂ)⁻¹ * (Nat.card (stabChar φ x) : ℂ)⁻¹ *
            ∑ l : A, (((x (φ k l) : ℂˣ) : ℂ) * E (k * g * k⁻¹)) *
              conj (((x (φ k' l) : ℂˣ) : ℂ) * E' (k' * g * k'⁻¹)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          simp only [Finset.mul_sum, Finset.sum_mul, map_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = ∑ g : G, ∑ k' : G, (Nat.card (stabChar φ x) : ℂ)⁻¹ * (Nat.card (stabChar φ x) : ℂ)⁻¹ *
            ((Nat.card A : ℂ) * Nat.card (stabChar φ x) * (E (k' * g * k'⁻¹) * conj (E' (k' * g * k'⁻¹)))) := by
          refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun k' _ => ?_
          rw [← key2, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [key]
      _ = (Nat.card A : ℂ) * (Nat.card (stabChar φ x) : ℂ)⁻¹ *
            ∑ k' : G, ∑ g : G, E (k' * g * k'⁻¹) * conj (E' (k' * g * k'⁻¹)) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          field_simp
      _ = (Nat.card A : ℂ) * Nat.card G * (Nat.card (stabChar φ x) : ℂ)⁻¹ * ∑ g : G, E g * conj (E' g) := by
          simp only [key3, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
          ring
  rw [hermitianPairing, total, card_semidirectProduct, hermitianPairing, hE, hE', sum_charExt_mul_conj]
  push_cast
  field_simp

/-- **Etingof et al., Theorem 4.75 (irreducibility)**: for an irreducible representation `U` of the stabilizer
`G_x` of a character `x` of the abelian group `A`, the little-group representation `V_(O,U)`, induced from
`A ⋊ G_x` acting by `x ⊗ U`, is an irreducible representation of `A ⋊ G`. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem isIrreducible_littleInd [IsIrreducible U] :
    IsIrreducible (Ind (littleSub φ x) (littleRep φ x U)) := by
  classical
  have := Fintype.ofFinite (stabChar φ x)
  apply isIrreducible_of_hermitianPairing_self_eq_one
  rw [hermitianPairing_littleInd φ x U U, hermitianPairing_irreducible U U, ite_eq_left_of_eq_true _ _ (eq_true ⟨Representation.Equiv.refl U⟩)]

/-- **Etingof et al., Theorem 4.75 (distinct `U`)**: for non-isomorphic irreducible representations `U`, `U'` of
`G_x`, the little-group representations `V_(O,U)` and `V_(O,U')` are not isomorphic. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem isEmpty_equiv_littleInd [IsIrreducible U] {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W'] (U' : Representation ℂ (stabChar φ x) W') [IsIrreducible U']
    (h : IsEmpty (Representation.Equiv U U')) :
    IsEmpty (Representation.Equiv (Ind (littleSub φ x) (littleRep φ x U)) (Ind (littleSub φ x) (littleRep φ x U'))) := by
  classical
  have := Fintype.ofFinite (stabChar φ x)
  refine ⟨fun e => ?_⟩
  have h1 := hermitianPairing_littleInd φ x U U'
  have hUU : hermitianPairing U.character U.character = 1 := by
    rw [hermitianPairing_irreducible U U]
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨Representation.Equiv.refl U⟩)
  have hUU' : hermitianPairing U.character U'.character = 0 := by
    rw [hermitianPairing_irreducible U U']
    exact ite_eq_right_of_eq_false _ _ (eq_false fun ⟨f⟩ => h.false f.symm)
  rw [← char_iso e, hermitianPairing_littleInd φ x U U, hUU, hUU'] at h1
  exact one_ne_zero h1

/-- For a character `x'` of `A` outside the `G`-orbit of `x`, the sum over `A` of `x(k l) conj x'(k' l)` vanishes. -/
lemma sum_char_mul_conj_eq_zero (x' : A →* ℂˣ) (h : ∀ g : G, ∃ a, x' a ≠ x (φ g a)) (k k' : G) :
    ∑ l : A, ((x (φ k l) : ℂˣ) : ℂ) * conj ((x' (φ k' l) : ℂˣ) : ℂ) = 0 := by
  let lam : A →* ℂˣ := x.comp (φ k).toMonoidHom / x'.comp (φ k').toMonoidHom
  have hlam : ∀ l, ((lam l : ℂˣ) : ℂ) = ((x (φ k l) : ℂˣ) : ℂ) * conj ((x' (φ k' l) : ℂˣ) : ℂ) := by
    intro l
    rw [conj_char x']
    simp [lam, div_eq_mul_inv]
  rw [← Finset.sum_congr rfl fun l _ => hlam l]
  apply sum_char_eq_zero
  intro hl
  obtain ⟨a, ha⟩ := h (k * k'⁻¹)
  apply ha
  have := congrArg (fun f : A →* ℂˣ => f (φ k'⁻¹ a)) hl
  simp only [lam, MonoidHom.div_apply, MonoidHom.comp_apply, MonoidHom.one_apply, div_eq_one] at this
  have e1 : φ k' (φ k'⁻¹ a) = a := by rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have e2 : φ k (φ k'⁻¹ a) = φ (k * k'⁻¹) a := by rw [map_mul, MulAut.mul_apply]
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, e1, e2] at this
  exact this.symm

/-- **Etingof et al., Theorem 4.75 (distinct orbits)**: if `x'` is not in the `G`-orbit of `x`, the characters of
`V_(O,U)` and `V_(O',U')` are orthogonal. -/
theorem hermitianPairing_littleInd_eq_zero (x' : A →* ℂˣ) [Fintype (stabChar φ x)] [Fintype (stabChar φ x')]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W'] (U' : Representation ℂ (stabChar φ x') W')
    (h : ∀ g : G, ∃ a, x' a ≠ x (φ g a)) :
    hermitianPairing (Ind (littleSub φ x) (littleRep φ x U)).character
        (Ind (littleSub φ x') (littleRep φ x' U')).character = 0 := by
  classical
  have hconj : ∀ n : ℕ, conj ((n : ℂ)⁻¹) = (n : ℂ)⁻¹ := fun n => by rw [map_inv₀, Complex.conj_natCast]
  rw [hermitianPairing, sum_semidirect, Finset.sum_comm, mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun g _ => ?_
  simp only [character_littleInd, map_mul, hconj, map_sum, Finset.mul_sum, Finset.sum_mul]
  have : ∀ k k' : G, ∑ l : A, (Nat.card (stabChar φ x) : ℂ)⁻¹ * (((x (φ k l) : ℂˣ) : ℂ) *
      charExt (stabChar φ x) U (k * g * k⁻¹)) * ((Nat.card (stabChar φ x') : ℂ)⁻¹ *
      (conj ((x' (φ k' l) : ℂˣ) : ℂ) * conj (charExt (stabChar φ x') U' (k' * g * k'⁻¹)))) = 0 := by
    intro k k'
    rw [← mul_zero ((Nat.card (stabChar φ x) : ℂ)⁻¹ * charExt (stabChar φ x) U (k * g * k⁻¹) *
      ((Nat.card (stabChar φ x') : ℂ)⁻¹ * conj (charExt (stabChar φ x') U' (k' * g * k'⁻¹)))),
      ← sum_char_mul_conj_eq_zero φ x x' h k k', Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun k' _ => this k' k

/-- **Etingof et al., Theorem 4.75 (distinct orbits)**: if `x'` is not in the `G`-orbit of `x`, then for irreducible
`U`, `U'` the little-group representations `V_(O,U)` and `V_(O',U')` are not isomorphic. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem isEmpty_equiv_littleInd_of_not_mem_orbit [IsIrreducible U] (x' : A →* ℂˣ) {W' : Type*} [AddCommGroup W']
    [Module ℂ W'] [FiniteDimensional ℂ W'] (U' : Representation ℂ (stabChar φ x') W')
    (h : ∀ g : G, ∃ a, x' a ≠ x (φ g a)) :
    IsEmpty (Representation.Equiv (Ind (littleSub φ x) (littleRep φ x U)) (Ind (littleSub φ x') (littleRep φ x' U'))) := by
  classical
  have := Fintype.ofFinite (stabChar φ x)
  have := Fintype.ofFinite (stabChar φ x')
  refine ⟨fun e => ?_⟩
  have h1 := hermitianPairing_littleInd_eq_zero φ x U x' U' h
  rw [← char_iso e, hermitianPairing_littleInd φ x U U, hermitianPairing_irreducible U U,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨Representation.Equiv.refl U⟩)] at h1
  exact one_ne_zero h1

end LittleNorm

end UndergradKB.RepresentationTheory
