import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Rat
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.Induced
import UndergradKB.Common.Attr

/-! # Artin's induction theorem (Etingof et al., §4.25)

Throughout, `G` is a finite group and `k` an algebraically closed field of characteristic zero.

* For a subgroup `H` and a function `ψ : H → k`, `indClassFun H ψ` is the induced class function
  `g ↦ |H|⁻¹ ∑_{x ∈ G} ψ°(x g x⁻¹)` (`ψ°` is `ψ` extended by zero); for the character of a representation of `H` it is
  the character of the induced representation (`character_Ind_eq_indClassFun`).
* Frobenius reciprocity for the pairing of class functions (`pairing_indClassFun`).
* **Theorem 4.73** (`artin_induction`): for a family `X` of subgroups, the following are equivalent:
  every element of `G` is conjugate into some member of `X`; the characters induced from irreducible characters of
  members of `X` span the class functions over `k`; every irreducible character of `G` is a rational linear
  combination of such induced characters.
* **Corollary 4.74** (`artin_cyclic`): the family of cyclic subgroups satisfies these conditions.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Representation Module

/-- In characteristic zero the order of a finite group is invertible in the field. -/
noncomputable instance invertibleNatCard {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] [Finite G] :
    Invertible (Nat.card G : k) :=
  invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')

/-! ### Induced class functions and Frobenius reciprocity -/

section Ind

variable {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)

open scoped Classical in
/-- A function on `H` extended by zero to `G`. -/
noncomputable def extZero (ψ : H → k) (x : G) : k := if h : x ∈ H then ψ ⟨x, h⟩ else 0

lemma extZero_of_mem {ψ : H → k} {x : G} (hx : x ∈ H) : extZero H ψ x = ψ ⟨x, hx⟩ := by
  simp [extZero, hx]

lemma extZero_of_not_mem {ψ : H → k} {x : G} (hx : x ∉ H) : extZero H ψ x = 0 := by
  simp [extZero, hx]

variable [Fintype G]

/-- The class function on `G` induced from a function `ψ` on the subgroup `H`:
`g ↦ |H|⁻¹ ∑_{x ∈ G} ψ°(x g x⁻¹)`. -/
noncomputable def indClassFun (ψ : H → k) (g : G) : k :=
  (Nat.card H : k)⁻¹ * ∑ x : G, extZero H ψ (x * g * x⁻¹)

lemma indClassFun_mem (ψ : H → k) : indClassFun H ψ ∈ classFunctions k G := by
  intro g h
  unfold indClassFun
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun x ↦ ?_)
  simp only [Equiv.coe_mulRight, mul_inv_rev, mul_assoc]

lemma indClassFun_eq_zero (ψ : H → k) {g : G} (h : ∀ x : G, x * g * x⁻¹ ∉ H) : indClassFun H ψ g = 0 := by
  unfold indClassFun
  rw [Finset.sum_eq_zero (fun x _ ↦ extZero_of_not_mem H (h x)), mul_zero]

/-- The character of the induced representation is the induced class function of the character
(Etingof et al., Theorem 4.32 in averaged form). -/
theorem character_Ind_eq_indClassFun {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Invertible (Nat.card H : k)] (ρ : Representation k H V) :
    (Ind H ρ).character = indClassFun H ρ.character := by
  funext g
  have := Fintype.ofFinite (RCosets H)
  rw [character_Ind_averaged, invOf_eq_inv]
  rfl

lemma sum_extZero_mul [Fintype H] (ψ : H → k) (φ : G → k) :
    ∑ y : G, extZero H ψ y * φ y⁻¹ = ∑ h : H, ψ h * φ (h : G)⁻¹ := by
  classical
  calc ∑ y : G, extZero H ψ y * φ y⁻¹
      = ∑ y ∈ Finset.univ.filter (· ∈ H), extZero H ψ y * φ y⁻¹ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        by_cases hy : y ∈ H
        · simp [hy]
        · simp [hy, extZero_of_not_mem H hy]
    _ = ∑ h : H, extZero H ψ h * φ (h : G)⁻¹ :=
        Finset.sum_subtype _ (fun x ↦ by simp) (fun y ↦ extZero H ψ y * φ y⁻¹)
    _ = _ := Finset.sum_congr rfl fun h _ ↦ by rw [extZero_of_mem H h.2]

theorem pairing_comm (f₁ f₂ : G → k) : pairing f₁ f₂ = pairing f₂ f₁ := by
  rw [pairing_apply, pairing_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ (fun g ↦ ?_)
  simp [mul_comm]

/-- **Frobenius reciprocity** for class functions: the pairing of an induced function with a class function `φ` of `G`
is the pairing on `H` of the original function with the restriction of `φ`. -/
theorem pairing_indClassFun [CharZero k] [Fintype H] (ψ : H → k) {φ : G → k} (hφ : φ ∈ classFunctions k G) :
    pairing (indClassFun H ψ) φ = pairing ψ (fun h : H ↦ φ h) := by
  have hG : (Nat.card G : k) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hS : ∀ x : G, ∑ g : G, extZero H ψ (x * g * x⁻¹) * φ g⁻¹ = ∑ h : H, ψ h * φ (h : G)⁻¹ := by
    intro x
    rw [← sum_extZero_mul H ψ φ]
    refine Fintype.sum_equiv (MulAut.conj x).toEquiv _ _ (fun g ↦ ?_)
    have := hφ g⁻¹ x
    simp only [MulAut.conj_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, mul_inv_rev, inv_inv]
    rw [← this]
    simp [mul_assoc]
  rw [pairing_apply, pairing_apply]
  have h1 : ∑ g : G, indClassFun H ψ g * φ g⁻¹ =
      (Nat.card H : k)⁻¹ * ((Nat.card G : k) * ∑ h : H, ψ h * φ (h : G)⁻¹) := by
    have h2 : ∑ g : G, indClassFun H ψ g * φ g⁻¹ =
        (Nat.card H : k)⁻¹ * ∑ x : G, ∑ g : G, extZero H ψ (x * g * x⁻¹) * φ g⁻¹ := by
      unfold indClassFun
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    rw [h2, Finset.sum_congr rfl (fun x _ ↦ hS x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
  rw [h1]
  field_simp
  simp

end Ind

/-! ### Artin's induction theorem -/

section Artin

variable {k : Type u} {G : Type v} [Field k] [CharZero k] [IsAlgClosed k] [Group G] [Fintype G]

variable (k) in
open scoped Classical in
/-- The characters induced from irreducible characters of members of a family `X` of subgroups. -/
def indChars (X : Set (Subgroup G)) : Set (G → k) :=
  {f | ∃ H ∈ X, ∃ ψ ∈ irrChars k H, f = indClassFun H ψ}

omit [CharZero k] [IsAlgClosed k] in
lemma indChars_subset(X : Set (Subgroup G)) : indChars k X ⊆ classFunctions k G := by
  rintro _ ⟨H, -, ψ, -, rfl⟩
  exact indClassFun_mem H ψ

/-- Representing a linear functional on functions on `G` by a class function. -/
theorem exists_pairing_eq_of_linear (lam : (G → k) →ₗ[k] k) :
    ∃ φ ∈ classFunctions k G, ∀ f ∈ classFunctions k G, lam f = pairing f φ := by
  refine ⟨∑ b : irrChars k G, lam (b : G → k) • (b : G → k), ?_, fun f hf ↦ ?_⟩
  · exact Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (mem_classFunctions_of_mem_irrChars b)
  · have h := congrArg lam (eq_sum_pairing_smul hf)
    simp only [map_sum, map_smul, smul_eq_mul] at h ⊢
    rw [h]
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _

/-- A class function orthogonal to all the induced characters from a family `X` covering `G` up to conjugacy vanishes
(Frobenius reciprocity and Theorem 3.5 on each member of `X`). -/
theorem eq_zero_of_pairing_indChars {X : Set (Subgroup G)} (hX : ∀ g : G, ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H)
    {φ : G → k} (hφ : φ ∈ classFunctions k G) (h : ∀ f ∈ indChars k X, pairing f φ = 0) : φ = 0 := by
  classical
  funext g
  obtain ⟨H, hHX, x, hx⟩ := hX g
  have hres : (fun h : H ↦ φ h) = 0 := by
    refine eq_zero_of_pairing_eq_zero (G := H) ?_ (fun Y ↦ ?_)
    · intro a b
      have := hφ a b
      simpa using this
    · rw [pairing_comm, ← pairing_indClassFun H _ hφ]
      exact h _ ⟨H, hHX, _, ⟨Y, rfl⟩, rfl⟩
  have := congrFun hres ⟨x * g * x⁻¹, hx⟩
  simpa [hφ g x] using this

theorem classFunctions_le_span_indChars {X : Set (Subgroup G)}
    (hX : ∀ g : G, ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H) :
    classFunctions k G ≤ Submodule.span k (indChars k X) := by
  intro f hf
  by_contra hnot
  obtain ⟨lam, hlam, hS⟩ := Submodule.exists_le_ker_of_notMem hnot
  obtain ⟨φ, hφ, hrep⟩ := exists_pairing_eq_of_linear lam
  have h0 : φ = 0 := by
    refine eq_zero_of_pairing_indChars hX hφ fun g hg ↦ ?_
    rw [← hrep g (indChars_subset X hg)]
    exact LinearMap.mem_ker.1 (hS (Submodule.subset_span hg))
  apply hlam
  rw [hrep f hf, h0]
  simp

omit [IsAlgClosed k] in
theorem exists_conj_mem_of_le_span{X : Set (Subgroup G)}
    (h : classFunctions k G ≤ Submodule.span k (indChars k X)) (g : G) :
    ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H := by
  by_contra hne
  push Not at hne
  have hone : (fun _ : G ↦ (1 : k)) ∈ classFunctions k G := fun _ _ ↦ rfl
  have hle : Submodule.span k (indChars k X) ≤ LinearMap.ker (LinearMap.proj g : (G → k) →ₗ[k] k) := by
    rw [Submodule.span_le]
    rintro _ ⟨H, hH, ψ, -, rfl⟩
    exact LinearMap.mem_ker.2 (by simpa using indClassFun_eq_zero H ψ (hne H hH))
  have := LinearMap.mem_ker.1 (hle (h hone))
  simp at this

omit [IsAlgClosed k] in
/-- The multiplicity of an irreducible character of `G` in an induced irreducible character is a natural number. -/
theorem exists_nat_pairing_indClassFun (H : Subgroup G) [Fintype H] {ψ : H → k} (hψ : ψ ∈ irrChars k H)
    (j : irrChars k G) : ∃ m : ℕ, pairing (indClassFun H ψ) (j : G → k) = m := by
  obtain ⟨Y, rfl⟩ := hψ
  obtain ⟨X, hX⟩ := j.2
  have := Fintype.ofFinite (RCosets H)
  have : Module.Finite k (coindV H.subtype Y.ρ) := Module.Finite.equiv (indEquivPi H Y.ρ).symm
  refine ⟨finrank k (IntertwiningMap X.ρ (Ind H Y.ρ)), ?_⟩
  rw [← hX, ← character_Ind_eq_indClassFun H Y.ρ, pairing_apply]
  exact card_inv_mul_sum_char_mul_char_eq_finrank X.ρ (Ind H Y.ρ)

/-- The rationality step: if the induced characters span the class functions over `k`, every irreducible character
of `G` is a rational linear combination of them.  The induced characters have natural-number coordinates in the basis
of irreducible characters, so a rational linear functional vanishing on them and not on the given irreducible character
would give a `k`-linear functional with the same property, contradicting the spanning hypothesis. -/
theorem mem_span_rat_of_le_span (X : Set (Subgroup G))
    (h : classFunctions k G ≤ Submodule.span k (indChars k X)) (j₀ : irrChars k G) :
    (j₀ : G → k) ∈ Submodule.span ℚ (indChars k X) := by
  classical
  have hsm : ∀ (q : ℚ) (f : G → k), q • f = (q : k) • f := by
    intro q f
    ext x
    simp [Rat.smul_def]
  let E : (irrChars k G → ℚ) →ₗ[ℚ] (G → k) :=
    ∑ j : irrChars k G, (LinearMap.proj j : (irrChars k G → ℚ) →ₗ[ℚ] ℚ).smulRight (j : G → k)
  have hE : ∀ v, E v = ∑ j : irrChars k G, v j • (j : G → k) := by
    intro v
    simp [E]
  let r : (G → k) → (irrChars k G → ℚ) := fun f j ↦
    if hm : ∃ m : ℕ, pairing f (j : G → k) = m then (hm.choose : ℚ) else 0
  have hr : ∀ f ∈ indChars k X, ∀ j : irrChars k G, pairing f (j : G → k) = ((r f j : ℚ) : k) := by
    rintro _ ⟨H, -, ψ, hψ, rfl⟩ j
    have hm := exists_nat_pairing_indClassFun H hψ j
    simp only [r, dif_pos hm]
    simpa using hm.choose_spec
  have hEr : ∀ f ∈ indChars k X, E (r f) = f := by
    intro f hf
    rw [hE]
    conv_rhs => rw [eq_sum_pairing_smul (indChars_subset X hf)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hr f hf j, hsm]
  by_contra hnot
  let e : irrChars k G → ℚ := fun i ↦ if j₀ = i then 1 else 0
  have hEe : E e = (j₀ : G → k) := by
    rw [hE]
    simp [e, ite_smul]
  have he : e ∈ Submodule.span ℚ (r '' indChars k X) := by
    by_contra hne
    obtain ⟨lam, hlam, hRle⟩ := Submodule.exists_le_ker_of_notMem hne
    let c : irrChars k G → ℚ := fun j ↦ lam (fun i ↦ if j = i then 1 else 0)
    have hlamv : ∀ v, lam v = ∑ j, v j * c j := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ lam v]
      simp [c, smul_eq_mul]
    let Λ : (G → k) →ₗ[k] k :=
      ∑ j : irrChars k G, ((c j : ℚ) : k) • (pairing (k := k) (G := G)).flip (j : G → k)
    have hΛ : ∀ f, Λ f = ∑ j : irrChars k G, ((c j : ℚ) : k) * pairing f (j : G → k) := by
      intro f
      simp [Λ]
    have hΛind : ∀ f ∈ indChars k X, Λ f = 0 := by
      intro f hf
      have hker : lam (r f) = 0 := hRle (Submodule.subset_span ⟨f, hf, rfl⟩)
      rw [hlamv] at hker
      rw [hΛ]
      have : ∑ j : irrChars k G, ((c j : ℚ) : k) * pairing f (j : G → k) =
          ((∑ j, r f j * c j : ℚ) : k) := by
        push_cast
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hr f hf j]
        ring
      rw [this, hker]
      simp
    have hΛspan : ∀ f ∈ Submodule.span k (indChars k X), Λ f = 0 := by
      intro f hf
      have : Submodule.span k (indChars k X) ≤ LinearMap.ker Λ :=
        Submodule.span_le.2 fun g hg ↦ LinearMap.mem_ker.2 (hΛind g hg)
      exact LinearMap.mem_ker.1 (this hf)
    have h0 := hΛspan _ (h (mem_classFunctions_of_mem_irrChars j₀))
    rw [hΛ, Finset.sum_eq_single j₀] at h0
    · rw [pairing_irrChars j₀.2 j₀.2, if_pos rfl, mul_one] at h0
      exact hlam (Rat.cast_eq_zero.1 h0)
    · intro j _ hj
      rw [pairing_irrChars j₀.2 j.2, if_neg (fun hh ↦ hj (Subtype.ext hh.symm)), mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  apply hnot
  rw [← hEe]
  have hmap : Submodule.map E (Submodule.span ℚ (r '' indChars k X)) ≤ Submodule.span ℚ (indChars k X) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [hEr f hf]
    exact Submodule.subset_span hf
  exact hmap (Submodule.mem_map_of_mem he)

theorem span_indChars_eq {X : Set (Subgroup G)} (hX : ∀ g : G, ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H) :
    Submodule.span k (indChars k X) = classFunctions k G :=
  le_antisymm (Submodule.span_le.2 (indChars_subset X)) (classFunctions_le_span_indChars hX)

theorem mem_span_rat_of_cover {X : Set (Subgroup G)} (hX : ∀ g : G, ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H) :
    ∀ χ ∈ irrChars k G, χ ∈ Submodule.span ℚ (indChars k X) :=
  fun χ hχ ↦ mem_span_rat_of_le_span X (classFunctions_le_span_indChars hX) ⟨χ, hχ⟩

/-- **Etingof et al., Theorem 4.73** (Artin's induction theorem): for a family `X` of subgroups of a finite group `G`
(over an algebraically closed field `k` of characteristic zero), the following are equivalent:
1. every element of `G` is conjugate to an element of some member of `X`;
2. the characters induced from irreducible characters of members of `X` span the class functions of `G` over `k`;
3. every irreducible character of `G` is a *rational* linear combination of characters induced from irreducible
   characters of members of `X`. -/
@[kb "etingof2011" "Theorem 4.73, p. 75"]
theorem artin_induction (X : Set (Subgroup G)) :
    List.TFAE [∀ g : G, ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H,
      Submodule.span k (indChars k X) = classFunctions k G,
      ∀ χ ∈ irrChars k G, χ ∈ Submodule.span ℚ (indChars k X)] := by
  tfae_have 1 → 2 := span_indChars_eq
  tfae_have 2 → 3 := fun h χ hχ ↦ mem_span_rat_of_le_span X h.ge ⟨χ, hχ⟩
  tfae_have 3 → 1 := fun h ↦ by
    refine exists_conj_mem_of_le_span (k := k) (X := X) ?_
    rw [← span_irrChars (k := k) (G := G), Submodule.span_le]
    intro χ hχ
    exact Submodule.span_subset_span ℚ k _ (h χ hχ)
  tfae_finish

/-- The character of any finite-dimensional representation of `G` has natural-number multiplicities of irreducible
characters, hence is a rational combination of induced characters when the equivalent conditions of
`artin_induction` hold. -/
theorem character_mem_span_rat {X : Set (Subgroup G)} (hX : ∀ g : G, ∃ H ∈ X, ∃ x : G, x * g * x⁻¹ ∈ H)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] (ρ : Representation k G V) :
    ρ.character ∈ Submodule.span ℚ (indChars k X) := by
  have h3 := mem_span_rat_of_cover (k := k) hX
  rw [eq_sum_pairing_smul (character_mem_classFunctions ρ)]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  obtain ⟨Y, hY⟩ := j.2
  have hm : pairing ρ.character (j : G → k) = finrank k (IntertwiningMap Y.ρ ρ) := by
    rw [← hY, pairing_apply]
    exact card_inv_mul_sum_char_mul_char_eq_finrank Y.ρ ρ
  rw [hm, Nat.cast_smul_eq_nsmul]
  exact Submodule.smul_of_tower_mem _ _ (h3 _ j.2)

/-- The family of cyclic subgroups of `G`. -/
def cyclicSubgroups (G : Type*) [Group G] : Set (Subgroup G) := Set.range Subgroup.zpowers

/-- **Etingof et al., Corollary 4.74**: every character of a finite group `G` (over an algebraically closed field of
characteristic zero) is a rational linear combination of characters induced from irreducible characters of cyclic
subgroups; equivalently (for irreducible characters, and then over `k` for all class functions) the induced characters
from cyclic subgroups span. -/
@[kb "etingof2011" "Corollary 4.74, p. 76"]
theorem artin_cyclic :
    Submodule.span k (indChars k (cyclicSubgroups G)) = classFunctions k G ∧
    (∀ χ ∈ irrChars k G, χ ∈ Submodule.span ℚ (indChars k (cyclicSubgroups G))) ∧
    ∀ {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] (ρ : Representation k G V),
      ρ.character ∈ Submodule.span ℚ (indChars k (cyclicSubgroups G)) := by
  have hX : ∀ g : G, ∃ H ∈ cyclicSubgroups G, ∃ x : G, x * g * x⁻¹ ∈ H :=
    fun g ↦ ⟨Subgroup.zpowers g, ⟨g, rfl⟩, 1, by simp⟩
  exact ⟨span_indChars_eq hX, mem_span_rat_of_cover hX, fun ρ ↦ character_mem_span_rat hX ρ⟩

end Artin

end UndergradKB.RepresentationTheory
