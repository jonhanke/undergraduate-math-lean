import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.AbstractAlgebra.Galois
import UndergradKB.AbstractAlgebra.RadicalTowers
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 23: Galois theory (course layer)

Thin wrappers around Mathlib for automorphism groups of fields, the Galois correspondence and
the solvability results. -/

namespace UndergradKB.AbstractAlgebra.Course

open Polynomial

/-- AA-421. The automorphisms of a field form a group under composition. -/
@[kb "judson2026" "Proposition 23.1.1, p. 318"]
theorem judson_23_1_1 (F : Type*) [Field F] (f g h : RingAut F) :
    f * g * h = f * (g * h) ∧ 1 * f = f ∧ f * 1 = f ∧ f⁻¹ * f = 1 ∧ f * f⁻¹ = 1 :=
  ⟨mul_assoc f g h, one_mul f, mul_one f, inv_mul_cancel f, mul_inv_cancel f⟩

/-- AA-422. The automorphisms of `E` fixing `F` form a group under composition. -/
@[kb "judson2026" "Proposition 23.1.2, p. 318"]
theorem judson_23_1_2 (F E : Type*) [Field F] [Field E] [Algebra F E] (σ τ ρ : E ≃ₐ[F] E) :
    σ * τ * ρ = σ * (τ * ρ) ∧ 1 * σ = σ ∧ σ * 1 = σ ∧ σ⁻¹ * σ = 1 ∧ σ * σ⁻¹ = 1 ∧
    ∀ a : F, σ (algebraMap F E a) = algebraMap F E a :=
  ⟨mul_assoc σ τ ρ, one_mul σ, mul_one σ, inv_mul_cancel σ, mul_inv_cancel σ, fun a => σ.commutes a⟩

/-- AA-426. For the splitting field `E` of a separable polynomial over `F`,
`|G(E/F)| = [E : F]`. -/
@[kb "judson2026" "Theorem 23.1.7, p. 320"]
theorem judson_23_1_7 {F E : Type*} [Field F] [Field E] [Algebra F E] (f : F[X])
    [f.IsSplittingField F E] (hf : f.Separable) :
    Nat.card (E ≃ₐ[F] E) = Module.finrank F E := by
  haveI : IsGalois F E := IsGalois.of_separable_splitting_field hf
  haveI : FiniteDimensional F E := Polynomial.IsSplittingField.finiteDimensional E f
  exact IsGalois.card_aut_eq_finrank F E

/-- AA-427. For a finite extension `E / F` of finite fields of degree `k`, the group `G(E/F)` is
cyclic of order `k`. -/
@[kb "judson2026" "Corollary 23.1.9, p. 320"]
theorem judson_23_1_9 (F E : Type*) [Field F] [Field E] [Finite E] [Algebra F E] :
    IsCyclic (E ≃ₐ[F] E) ∧ Nat.card (E ≃ₐ[F] E) = Module.finrank F E := by
  haveI : Finite F := Finite.of_injective (algebraMap F E) (algebraMap F E).injective
  haveI : FiniteDimensional F E := Module.Finite.of_finite
  exact ⟨inferInstance, IsGalois.card_aut_eq_finrank F E⟩

/-- AA-430. Primitive element theorem: a finite separable extension is simple. -/
@[kb "judson2026" "Theorem 23.1.13, p. 322"]
theorem judson_23_1_13 (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] : ∃ α : E, IntermediateField.adjoin F {α} = ⊤ :=
  Field.exists_primitive_element F E

/-- AA-431. The set of elements fixed by a group of automorphisms is a subfield (the fixed
field). -/
@[kb "judson2026" "Corollary 23.2.2, p. 323"]
theorem judson_23_2_2 (G E : Type*) [Group G] [Field E] [MulSemiringAction G E] :
    ∃ K : Subfield E, ∀ x : E, x ∈ K ↔ ∀ g : G, g • x = x :=
  ⟨FixedPoints.subfield G E, fun x => MulAction.mem_fixedPoints.trans Iff.rfl⟩

/-- AA-433. If `E` is the splitting field of a separable polynomial over `F`, the fixed field of
`G(E/F)` is `F`. -/
@[kb "judson2026" "Proposition 23.2.4, p. 323"]
theorem judson_23_2_4 {F E : Type*} [Field F] [Field E] [Algebra F E] (f : F[X])
    [f.IsSplittingField F E] (hf : f.Separable) (x : E) :
    (∀ σ : E ≃ₐ[F] E, σ x = x) ↔ ∃ a : F, algebraMap F E a = x := by
  haveI : IsGalois F E := IsGalois.of_separable_splitting_field hf
  haveI : FiniteDimensional F E := Polynomial.IsSplittingField.finiteDimensional E f
  rw [← IsGalois.mem_bot_iff_fixed, IntermediateField.mem_bot]
  exact Set.mem_range

/-- AA-434. For a finite group `G` of automorphisms of `E` with fixed field `F`,
`[E : F] ≤ |G|`. -/
@[kb "judson2026" "Lemma 23.2.5, p. 323"]
theorem judson_23_2_5 (G E : Type*) [Group G] [Field E] [MulSemiringAction G E] [Fintype G] :
    Module.finrank (FixedPoints.subfield G E) E ≤ Fintype.card G :=
  FixedPoints.finrank_le_card G E

/-- AA-436. If `F` is the fixed field of a finite group `G` of automorphisms of `K` (acting
faithfully), then `G = G(K/F)`. -/
@[kb "judson2026" "Corollary 23.2.7, p. 325"]
theorem judson_23_2_7 (G K : Type*) [Group G] [Field K] [MulSemiringAction G K] [Finite G]
    [FaithfulSMul G K] : Nonempty (G ≃* (K ≃ₐ[FixedPoints.subfield G K] K)) :=
  ⟨FixedPoints.toAlgAutMulEquiv G K⟩

/-- AA-437. Fundamental Theorem of Galois Theory, bijection and degrees: for a finite Galois
extension `E / F`, intermediate fields correspond bijectively and inclusion-reversingly to
subgroups of `G(E/F)` via `K ↦ G(E/K)` with inverse `H ↦ E_H`, with `[E : E_H] = |H|` and
`[K : F] = [G : G(E/K)]`. -/
@[kb "judson2026" "Theorem 23.2.10, p. 325"]
theorem judson_23_2_10 (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] :
    (∃ e : IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ,
      ∀ K, e K = OrderDual.toDual K.fixingSubgroup) ∧
    (∀ K : IntermediateField F E, IntermediateField.fixedField K.fixingSubgroup = K) ∧
    (∀ H : Subgroup (E ≃ₐ[F] E), (IntermediateField.fixedField H).fixingSubgroup = H) ∧
    (∀ H : Subgroup (E ≃ₐ[F] E),
      Module.finrank (IntermediateField.fixedField H) E = Nat.card H) ∧
    (∀ K : IntermediateField F E, Module.finrank F K = K.fixingSubgroup.index) := by
  refine ⟨⟨IsGalois.intermediateFieldEquivSubgroup, fun K => rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact fun K => IsGalois.fixedField_fixingSubgroup K
  · exact fun H => IntermediateField.fixingSubgroup_fixedField H
  · exact fun H => IntermediateField.finrank_fixedField_eq_card H
  · exact fun K => IntermediateField.finrank_eq_fixingSubgroup_index E K

/-- AA-437. Fundamental Theorem of Galois Theory, normality: an intermediate field `K` is
normal over `F` iff its group `G(E/K)` is a normal subgroup, and then `G(K/F) ≅ G(E/F) / G(E/K)`. -/
theorem judson_23_2_10_normal (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    (∀ K : IntermediateField F E, IsGalois F K → K.fixingSubgroup.Normal) ∧
    (∀ (H : Subgroup (E ≃ₐ[F] E)) [H.Normal], IsGalois F (IntermediateField.fixedField H)) ∧
    (∀ (H : Subgroup (E ≃ₐ[F] E)) [H.Normal],
      Nonempty ((E ≃ₐ[F] E) ⧸ H ≃* (IntermediateField.fixedField H ≃ₐ[F]
        IntermediateField.fixedField H))) := by
  refine ⟨fun K hK => ?_, fun H _ => ?_, fun H _ => ?_⟩
  · exact IsGalois.fixingSubgroup_normal_of_isGalois K
  · exact IsGalois.of_fixedField_normal_subgroup H
  · exact ⟨IsGalois.normalAutEquivQuotient H⟩

/-- AA-440. The splitting field of `x ^ n - a` has solvable Galois group. -/
@[kb "judson2026" "Lemma 23.3.2, p. 329"]
theorem judson_23_3_2 {F : Type*} [Field F] (n : ℕ) (a : F) :
    Group.IsSolvable (X ^ n - C a).Gal :=
  gal_X_pow_sub_C_isSolvable n a

/-- AA-443. For `p` prime, a subgroup of `S_p` containing a transposition and a `p`-cycle is all
of `S_p`. -/
@[kb "judson2026" "Lemma 23.3.5, p. 330"]
theorem judson_23_3_5 (p : ℕ) (hp : p.Prime) (G : Subgroup (Equiv.Perm (Fin p)))
    (σ τ : Equiv.Perm (Fin p)) (hσ : σ ∈ G) (hσc : σ.IsCycle) (hσs : σ.support = Finset.univ)
    (hτ : τ ∈ G) (hτs : τ.IsSwap) : G = ⊤ := by
  have h := Equiv.Perm.closure_prime_cycle_swap (by simpa using hp) hσc hσs hτs
  rw [eq_top_iff, ← h]
  exact (Subgroup.closure_le G).mpr (by
    rintro x (rfl | rfl)
    · exact hσ
    · exact hτ)

/-- AA-445. Fundamental Theorem of Algebra: `ℂ` is algebraically closed. -/
@[kb "judson2026" "Theorem 23.3.8, p. 332"]
theorem judson_23_3_8 : IsAlgClosed ℂ :=
  Complex.isAlgClosed

/-- AA-424. An automorphism in `G(E/F)` permutes the roots in `E` of any `f ∈ F[x]`. -/
@[kb "judson2026" "Proposition 23.1.5, p. 319"]
theorem judson_23_1_5 {F E : Type*} [Field F] [Field E] [Algebra F E] (σ : E ≃ₐ[F] E)
    (f : F[X]) : ∃ e : f.rootSet E ≃ f.rootSet E, ∀ x, (e x : E) = σ x :=
  UndergradKB.AbstractAlgebra.autEquiv_rootSet σ f

/-- AA-425. If `α, β` are conjugate over `F` (same minimal polynomial), there is an
`F`-isomorphism `F(α) → F(β)` sending `α` to `β`. -/
@[kb "judson2026" "Proposition 23.1.6, p. 320"]
theorem judson_23_1_6 {F E : Type*} [Field F] [Field E] [Algebra F E] {α β : E}
    (hα : IsIntegral F α) (hβ : IsIntegral F β) (h : minpoly F α = minpoly F β) :
    ∃ φ : IntermediateField.adjoin F {α} ≃ₐ[F] IntermediateField.adjoin F {β},
      φ (IntermediateField.AdjoinSimple.gen F α) = IntermediateField.AdjoinSimple.gen F β :=
  UndergradKB.AbstractAlgebra.exists_algEquiv_adjoin_of_minpoly_eq hα hβ h

/-- AA-429. An irreducible polynomial over a field of characteristic 0 is separable. -/
@[kb "judson2026" "Proposition 23.1.12, p. 322"]
theorem judson_23_1_12 {F : Type*} [Field F] [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable :=
  UndergradKB.AbstractAlgebra.irreducible_separable_charZero hf

/-- AA-429. In characteristic `p`, an irreducible polynomial is separable iff it is not a
polynomial in `x ^ p`. -/
@[kb "judson2026" "Proposition 23.1.12 (characteristic p), p. 322"]
theorem judson_23_1_12_charP {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {f : F[X]}
    (hf : Irreducible f) : f.Separable ↔ ¬ ∃ g : F[X], f = expand F p g :=
  UndergradKB.AbstractAlgebra.irreducible_separable_iff_not_expand p hf

/-- AA-435. For a finite extension `E / F` the following are equivalent: `E / F` is normal and
separable; `E` is the splitting field of a separable polynomial over `F`; `F` is the fixed field
of a finite group of automorphisms of `E`. -/
@[kb "judson2026" "Theorem 23.2.6, p. 324"]
theorem judson_23_2_6 {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    List.TFAE [
      Normal F E ∧ Algebra.IsSeparable F E,
      ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E,
      ∃ G : Subgroup (E ≃+* E), Finite G ∧
        ∀ x : E, x ∈ Set.range (algebraMap F E) ↔ ∀ g ∈ G, g x = x] :=
  UndergradKB.AbstractAlgebra.galois_tfae

/-- AA-441. A finite radical extension `E` of `F` inside a normal extension `L` is contained in a
normal radical extension (its normal closure in `L`). -/
@[kb "judson2026" "Lemma 23.3.3, p. 329"]
theorem judson_23_3_3 {F L : Type*} [Field F] [Field L] [Algebra F L] [Normal F L]
    (E : IntermediateField F L) [FiniteDimensional F E]
    (h : UndergradKB.AbstractAlgebra.IsRadical F E) :
    UndergradKB.AbstractAlgebra.IsRadical F (IntermediateField.normalClosure F E L) ∧
      Normal F (IntermediateField.normalClosure F E L) ∧
      E ≤ IntermediateField.normalClosure F E L :=
  UndergradKB.AbstractAlgebra.isRadical_normalClosure E h

/-- AA-442. If `f` is solvable by radicals over a field `F` (here of any characteristic), its
Galois group is solvable. -/
@[kb "judson2026" "Theorem 23.3.4, p. 330"]
theorem judson_23_3_4 {F : Type*} [Field F] {f : F[X]}
    (hf : UndergradKB.AbstractAlgebra.SolvableByRadicals F f) : Group.IsSolvable f.Gal :=
  UndergradKB.AbstractAlgebra.isSolvable_gal_of_solvableByRadicals hf

/-- AA-444. The quintic `x ^ 5 - 6 x ^ 3 - 27 x - 3` over `ℚ` has Galois group `S₅` (the action on
its complex roots is a bijection onto their permutations), which is not solvable; hence the
quintic is not solvable by radicals. -/
@[kb "judson2026" "Example 23.3.7, p. 331"]
theorem judson_23_3_7 :
    Function.Bijective (Polynomial.Gal.galActionHom UndergradKB.AbstractAlgebra.Quintic.quintic ℂ) ∧
    ¬ Group.IsSolvable UndergradKB.AbstractAlgebra.Quintic.quintic.Gal ∧
    ¬ UndergradKB.AbstractAlgebra.SolvableByRadicals ℚ UndergradKB.AbstractAlgebra.Quintic.quintic :=
  ⟨UndergradKB.AbstractAlgebra.Quintic.quintic_galActionHom_bijective,
    UndergradKB.AbstractAlgebra.Quintic.quintic_gal_not_isSolvable,
    UndergradKB.AbstractAlgebra.Quintic.quintic_not_solvableByRadicals⟩

end UndergradKB.AbstractAlgebra.Course
