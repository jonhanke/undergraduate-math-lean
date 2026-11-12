import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Character
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import UndergradKB.Common.Attr

/-! # Induced representations (Etingof et al., §4.8)

For a subgroup `H ≤ G` and a representation `ρ` of `H` on `V`, the book's induced representation
`Ind_H^G V` (Definition 4.28) is the space of functions `f : G → V` with `f (h x) = ρ h (f x)` for `h ∈ H`,
with `G` acting by right translation, `(g f)(x) = f (x g)`.  In Mathlib this is exactly the coinduced
representation `Representation.coind H.subtype ρ`, on the submodule `Representation.coindV H.subtype ρ`.
We use it as the definition of `Ind`.

We prove the dimension formula (Remark 4.30) and the induced character formula (Theorem 4.32).
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Representation Module

section Setup

variable {k : Type u} {G : Type v} {V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (H : Subgroup G) (ρ : Representation k H V)

/-- **Etingof et al., Definition 4.28**: the induced representation `Ind_H^G V` of `G`, the space of functions
`f : G → V` with `f (h x) = ρ h (f x)`, with `G` acting by right translation.  This is Mathlib's
coinduced representation along the inclusion `H ↪ G`. -/
@[kb "etingof2011" "Definition 4.28, p. 54"]
noncomputable abbrev Ind : Representation k G (coindV H.subtype ρ) := coind H.subtype ρ

/-- The set of right cosets `H x` of `H` in `G`. -/
abbrev RCosets : Type v := Quotient (QuotientGroup.rightRel H)

/-- A chosen representative of a right coset. -/
noncomputable def rep (c : RCosets H) : G := Quotient.out c

/-- The right coset of an element. -/
def rcoset (x : G) : RCosets H := Quotient.mk (QuotientGroup.rightRel H) x

lemma rcoset_eq_iff {x y : G} : rcoset H x = rcoset H y ↔ y * x⁻¹ ∈ H :=
  Quotient.eq (r := QuotientGroup.rightRel H) |>.trans QuotientGroup.rightRel_apply

lemma rcoset_rep (c : RCosets H) : rcoset H (rep H c) = c := Quotient.out_eq c

lemma rcoset_mul_left (h : H) (x : G) : rcoset H ((h : G) * x) = rcoset H x := by
  rw [rcoset_eq_iff]
  simp

lemma mul_rep_inv_mem (x : G) : x * (rep H (rcoset H x))⁻¹ ∈ H := by
  have := (rcoset_eq_iff H (x := rep H (rcoset H x)) (y := x)).1 (rcoset_rep H (rcoset H x))
  exact this

/-- The element of `H` carrying the chosen representative of the coset of `x` to `x`. -/
noncomputable def cosetElt (x : G) : H := ⟨x * (rep H (rcoset H x))⁻¹, mul_rep_inv_mem H x⟩

lemma cosetElt_mul (h : H) (x : G) : cosetElt H ((h : G) * x) = h * cosetElt H x := by
  ext
  simp [cosetElt, rcoset_mul_left, mul_assoc]

lemma cosetElt_mul_rep (x : G) : (cosetElt H x : G) * rep H (rcoset H x) = x := by
  simp [cosetElt]

/-- The linear isomorphism `Ind_H^G V ≃ (H\G → V)`, `f ↦ (f (r_c))_c`, over chosen coset representatives. -/
noncomputable def indEquivPi : coindV H.subtype ρ ≃ₗ[k] (RCosets H → V) where
  toFun f := fun c ↦ f.1 (rep H c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun F := ⟨fun x ↦ ρ (cosetElt H x) (F (rcoset H x)), by
    intro h x
    simp [cosetElt_mul, rcoset_mul_left]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    have := f.2 (cosetElt H x) (rep H (rcoset H x))
    simp only [Subgroup.subtype_apply, cosetElt_mul_rep] at this
    simpa using this.symm
  right_inv F := by
    funext c
    have h1 : cosetElt H (rep H c) = 1 := by
      ext
      simp [cosetElt, rcoset_rep]
    simp [h1, rcoset_rep]

end Setup

section Dimension

variable {k : Type u} {G : Type v} {V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (H : Subgroup G) (ρ : Representation k H V)

/-- **Etingof et al., Remark 4.30**: for a finite group `G`, a subgroup `H` and a finite-dimensional
representation `V` of `H`, the induced representation has dimension `dim V * [G : H]`. -/
@[kb "etingof2011" "Remark 4.30, p. 55"]
theorem finrank_Ind [Finite G] [Module.Finite k V] :
    finrank k (coindV H.subtype ρ) = finrank k V * H.index := by
  classical
  have := Fintype.ofFinite G
  rw [LinearEquiv.finrank_eq (indEquivPi H ρ), Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [← Nat.card_eq_fintype_card, Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)]

end Dimension

section Character

variable {k : Type u} {G : Type v} {V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (H : Subgroup G) (ρ : Representation k H V)

open scoped Classical in
/-- The character of `V` (a representation of `H`) extended by zero to `G`: `χ̃ x = χ_V x` if `x ∈ H`, else `0`. -/
noncomputable def charExt (x : G) : k := if h : x ∈ H then ρ.character ⟨x, h⟩ else 0

lemma charExt_of_mem {x : G} (hx : x ∈ H) : charExt H ρ x = ρ.character ⟨x, hx⟩ := by
  simp [charExt, hx]

lemma charExt_of_not_mem {x : G} (hx : x ∉ H) : charExt H ρ x = 0 := by
  simp [charExt, hx]

lemma charExt_conj [Module.Finite k V] (h : H) (y : G) :
    charExt H ρ ((h : G) * y * (h : G)⁻¹) = charExt H ρ y := by
  by_cases hy : y ∈ H
  · have hy' : (h : G) * y * (h : G)⁻¹ ∈ H := H.mul_mem (H.mul_mem h.2 hy) (H.inv_mem h.2)
    rw [charExt_of_mem H ρ hy, charExt_of_mem H ρ hy']
    exact ρ.char_conj ⟨y, hy⟩ h
  · have hy' : (h : G) * y * (h : G)⁻¹ ∉ H := by
      intro hh
      apply hy
      have := H.mul_mem (H.mul_mem (H.inv_mem h.2) hh) h.2
      simpa [mul_assoc] using this
    rw [charExt_of_not_mem H ρ hy, charExt_of_not_mem H ρ hy']

lemma rcoset_rep_mul_eq_iff (c : RCosets H) (g : G) :
    rcoset H (rep H c * g) = c ↔ rep H c * g * (rep H c)⁻¹ ∈ H := by
  have : rcoset H (rep H c * g) = c ↔ rcoset H (rep H c * g) = rcoset H (rep H c) := by
    rw [rcoset_rep]
  rw [this, rcoset_eq_iff, ← H.inv_mem_iff]
  simp [mul_assoc]

variable [Fintype (RCosets H)]

/-- The block form of the action of `g` on `Ind` in the coordinates given by `indEquivPi`. -/
noncomputable def indBlock (g : G) : (RCosets H → V) →ₗ[k] (RCosets H → V) :=
  open scoped Classical in
  ∑ c : RCosets H, (LinearMap.single k (fun _ : RCosets H ↦ V) c) ∘ₗ
    (ρ (cosetElt H (rep H c * g))) ∘ₗ (LinearMap.proj (rcoset H (rep H c * g)))

lemma indEquivPi_conj (g : G) :
    (indEquivPi H ρ).conj (Ind H ρ g) = indBlock H ρ g := by
  classical
  refine LinearMap.ext fun F ↦ funext fun d ↦ ?_
  rw [LinearEquiv.conj_apply_apply]
  have h1 : (indEquivPi H ρ ((Ind H ρ g) ((indEquivPi H ρ).symm F))) d =
      ρ (cosetElt H (rep H d * g)) (F (rcoset H (rep H d * g))) := rfl
  rw [h1]
  simp [indBlock, Finset.sum_apply, Pi.single_apply]

/-- **Etingof et al., Theorem 4.32** (the induced character): let `R` be a set of representatives of the
right cosets `H x` of `H` in `G`, here `rep c` for `c` a coset.  Then the character of `Ind_H^G V`
(with `G` acting by right translation, `(g f)(x) = f (x g)`) is
`χ_{Ind V}(g) = ∑_{x ∈ R} χ̃_V (x g x⁻¹)`, where `χ̃_V` is `χ_V` on `H` and `0` outside `H`;
only the terms with `x g x⁻¹ ∈ H` contribute. -/
@[kb "etingof2011" "Theorem 4.32, p. 55"]
theorem character_Ind [Module.Finite k V] (g : G) :
    (Ind H ρ).character g = ∑ c : RCosets H, charExt H ρ (rep H c * g * (rep H c)⁻¹) := by
  classical
  unfold Representation.character
  rw [← LinearMap.trace_conj' (Ind H ρ g) (indEquivPi H ρ), indEquivPi_conj, indBlock,
    map_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [LinearMap.trace_comp_comm' (R := k) (M := RCosets H → V) (N := V)]
  by_cases hc : rcoset H (rep H c * g) = c
  · have hmem := (rcoset_rep_mul_eq_iff H c g).1 hc
    rw [charExt_of_mem H ρ hmem]
    have e1 : (LinearMap.proj (R := k) (φ := fun _ : RCosets H ↦ V) (rcoset H (rep H c * g))) ∘ₗ
        (LinearMap.single k (fun _ : RCosets H ↦ V) c) = LinearMap.id := by
      rw [hc]; ext; simp
    have e2 : cosetElt H (rep H c * g) = ⟨rep H c * g * (rep H c)⁻¹, hmem⟩ := by
      ext
      simp [cosetElt, hc]
    rw [LinearMap.comp_assoc, e1, e2]
    rfl
  · have hmem : ¬ rep H c * g * (rep H c)⁻¹ ∈ H := fun h ↦ hc ((rcoset_rep_mul_eq_iff H c g).2 h)
    rw [charExt_of_not_mem H ρ hmem]
    have e1 : (LinearMap.proj (R := k) (φ := fun _ : RCosets H ↦ V) (rcoset H (rep H c * g))) ∘ₗ
        (LinearMap.single k (fun _ : RCosets H ↦ V) c) = 0 := by
      ext x
      simp [hc]
    rw [LinearMap.comp_assoc, e1]
    simp

omit [Fintype (RCosets H)] in
lemma charExt_conj_cosetElt [Module.Finite k V] (g x : G) :
    charExt H ρ (x * g * x⁻¹) = charExt H ρ (rep H (rcoset H x) * g * (rep H (rcoset H x))⁻¹) := by
  have hx := cosetElt_mul_rep H x
  set o := rep H (rcoset H x)
  rw [← charExt_conj H ρ (cosetElt H x) (o * g * o⁻¹)]
  congr 1
  conv_lhs => rw [← hx]
  simp [mul_assoc]

omit [Fintype (RCosets H)] in
/-- The fibre of `rcoset` over a coset has `|H|` elements. -/
lemma card_filter_rcoset [Fintype G] [DecidableEq (RCosets H)] [Fintype H] (c : RCosets H) :
    (Finset.univ.filter fun x : G ↦ rcoset H x = c).card = Fintype.card H := by
  rw [← Finset.card_univ (α := H)]
  refine Finset.card_bij (fun x _ ↦ cosetElt H x) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rw [← cosetElt_mul_rep H x, ← cosetElt_mul_rep H y, hx, hy, hxy]
  · intro h _
    refine ⟨(h : G) * rep H c, ?_, ?_⟩
    · simp [rcoset_mul_left, rcoset_rep]
    · have := cosetElt_mul H h (rep H c)
      rw [this]
      have h1 : cosetElt H (rep H c) = 1 := by
        ext
        simp [cosetElt, rcoset_rep]
      simp [h1]

/-- **Etingof et al., Theorem 4.32** (averaged form): if `|H|` is invertible in `k`, then
`χ_{Ind V}(g) = |H|⁻¹ ∑_{x ∈ G, x g x⁻¹ ∈ H} χ_V (x g x⁻¹)`, the sum running over all of `G`
(`charExt` vanishes when `x g x⁻¹ ∉ H`). -/
@[kb "etingof2011" "Theorem 4.32, p. 55"]
theorem character_Ind_averaged [Module.Finite k V] [Fintype G] [Invertible (Nat.card H : k)] (g : G) :
    (Ind H ρ).character g = ⅟(Nat.card H : k) * ∑ x : G, charExt H ρ (x * g * x⁻¹) := by
  classical
  rw [character_Ind, Finset.sum_congr rfl fun x _ ↦ charExt_conj_cosetElt H ρ g x]
  rw [← Finset.sum_fiberwise Finset.univ (rcoset H)
    (fun x : G ↦ charExt H ρ (rep H (rcoset H x) * g * (rep H (rcoset H x))⁻¹))]
  have : ∀ c : RCosets H, (∑ x ∈ Finset.univ.filter fun x : G ↦ rcoset H x = c,
      charExt H ρ (rep H (rcoset H x) * g * (rep H (rcoset H x))⁻¹)) =
      (Nat.card H : k) * charExt H ρ (rep H c * g * (rep H c)⁻¹) := by
    intro c
    rw [Finset.sum_congr rfl (g := fun _ ↦ charExt H ρ (rep H c * g * (rep H c)⁻¹))]
    · rw [Finset.sum_const, card_filter_rcoset, nsmul_eq_mul, Nat.card_eq_fintype_card]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hx]
  simp_rw [this]
  rw [← Finset.mul_sum, invOf_mul_cancel_left]

end Character

end UndergradKB.RepresentationTheory
