import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Nat.Prime.Int
import Mathlib.GroupTheory.Solvable
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapters 22 and 23: separability, Galois extensions, solvability by radicals

Separable polynomials, the action of automorphisms on roots, conjugate elements, the equivalent
descriptions of finite Galois extensions, and the solvability criterion. -/

open Polynomial

namespace UndergradKB.AbstractAlgebra

section Separable

variable {F : Type*} [Field F]

/-- AA-404. A nonzero polynomial is separable (coprime to its derivative) iff it has no repeated
root in a splitting field. -/
@[kb "judson2026" "Definition (separable polynomial), p. 304"]
theorem separable_iff_nodup_roots_splittingField {f : F[X]} (hf : f ≠ 0) :
    f.Separable ↔ (f.aroots f.SplittingField).Nodup :=
  (nodup_aroots_iff_of_splits hf (SplittingField.splits f)).symm

/-- AA-429 (characteristic 0). An irreducible polynomial over a field of characteristic 0 is
separable. -/
@[kb "judson2026" "Proposition 23.1.12, p. 322"]
theorem irreducible_separable_charZero [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable :=
  hf.separable

/-- AA-429 (characteristic `p`). An irreducible polynomial over a field of characteristic `p` is
separable iff it is not a polynomial in `x ^ p`. -/
theorem irreducible_separable_iff_not_expand (p : ℕ) [Fact p.Prime] [CharP F p] {f : F[X]}
    (hf : Irreducible f) : f.Separable ↔ ¬ ∃ g : F[X], f = expand F p g := by
  rw [separable_iff_derivative_ne_zero hf]
  constructor
  · rintro h ⟨g, rfl⟩
    apply h
    simp [derivative_expand]
  · intro h hd
    exact h ⟨_, (expand_contract p hd (Fact.out : p.Prime).ne_zero).symm⟩

end Separable

section Roots

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- AA-424. An automorphism of `E` over `F` permutes the roots in `E` of a polynomial over `F`:
there is a bijection of the root set that is `σ` on elements. -/
@[kb "judson2026" "Proposition 23.1.5, p. 319"]
theorem autEquiv_rootSet (σ : E ≃ₐ[F] E) (f : F[X]) :
    ∃ e : f.rootSet E ≃ f.rootSet E, ∀ x, (e x : E) = σ x := by
  have key : ∀ (τ : E ≃ₐ[F] E) (x : E), x ∈ f.rootSet E → τ x ∈ f.rootSet E := by
    intro τ x hx
    rw [mem_rootSet] at hx ⊢
    exact ⟨hx.1, by rw [aeval_algHom_apply]; simp [hx.2]⟩
  exact ⟨⟨fun x => ⟨σ x, key σ x x.2⟩, fun x => ⟨σ.symm x, key σ.symm x x.2⟩,
    fun x => Subtype.ext (by simp), fun x => Subtype.ext (by simp)⟩, fun x => rfl⟩

end Roots

section Conjugate

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- AA-425. Two elements with the same minimal polynomial over `F` give an `F`-isomorphism
`F(α) ≅ F(β)` sending `α` to `β`. -/
@[kb "judson2026" "Proposition 23.1.6, p. 320"]
theorem exists_algEquiv_adjoin_of_minpoly_eq {α β : E} (hα : IsIntegral F α) (hβ : IsIntegral F β)
    (h : minpoly F α = minpoly F β) :
    ∃ φ : F⟮α⟯ ≃ₐ[F] F⟮β⟯, φ (AdjoinSimple.gen F α) = AdjoinSimple.gen F β := by
  have hroot : AdjoinSimple.gen F β ∈ (minpoly F α).aroots F⟮β⟯ := by
    rw [mem_aroots]
    refine ⟨minpoly.ne_zero hα, ?_⟩
    rw [h]
    exact aeval_gen_minpoly F β
  let f : F⟮α⟯ →ₐ[F] F⟮β⟯ := (algHomAdjoinIntegralEquiv F hα).symm ⟨_, hroot⟩
  have hf : f (AdjoinSimple.gen F α) = AdjoinSimple.gen F β :=
    algHomAdjoinIntegralEquiv_symm_apply_gen F hα ⟨_, hroot⟩
  have hrank : Module.finrank F F⟮α⟯ = Module.finrank F F⟮β⟯ := by
    rw [adjoin.finrank hα, adjoin.finrank hβ, h]
  have : FiniteDimensional F F⟮α⟯ := adjoin.finiteDimensional hα
  have : FiniteDimensional F F⟮β⟯ := adjoin.finiteDimensional hβ
  have hinj : Function.Injective f := f.toRingHom.injective
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := f.toLinearMap)).1 hinj
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end Conjugate

section GaloisTFAE

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- AA-435. For a finite extension `E/F` the following are equivalent: (1) `E/F` is normal and
separable; (2) `E` is a splitting field over `F` of a separable polynomial; (3) there is a finite
group `G` of automorphisms of `E` whose fixed field is exactly `F`. -/
@[kb "judson2026" "Theorem 23.2.6, p. 324"]
theorem galois_tfae [FiniteDimensional F E] : List.TFAE [
    Normal F E ∧ Algebra.IsSeparable F E,
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E,
    ∃ G : Subgroup (E ≃+* E), Finite G ∧
      ∀ x : E, x ∈ Set.range (algebraMap F E) ↔ ∀ g ∈ G, g x = x] := by
  tfae_have 1 → 2 := fun h ↦ by
    have : IsGalois F E := isGalois_iff.2 ⟨h.2, h.1⟩
    exact IsGalois.is_separable_splitting_field F E
  tfae_have 2 → 1 := fun h ↦ by
    obtain ⟨p, hp, hs⟩ := h
    have := IsGalois.of_separable_splitting_field (F := F) (E := E) hp
    exact ⟨this.to_normal, this.to_isSeparable⟩
  tfae_have 1 → 3 := fun h ↦ by
    have : IsGalois F E := isGalois_iff.2 ⟨h.2, h.1⟩
    let f : (E ≃ₐ[F] E) →* (E ≃+* E) :=
      { toFun := AlgEquiv.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
    refine ⟨f.range, (Set.finite_range f).to_subtype, fun x => ?_⟩
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    constructor
    · intro hx g hg
      obtain ⟨σ, rfl⟩ := hg
      exact hx σ
    · intro hx σ
      exact hx (f σ) ⟨σ, rfl⟩
  tfae_have 3 → 1 := fun ⟨G, _, hG⟩ ↦ by
    have hfix : ∀ g ∈ G, ∀ a : F, g (algebraMap F E a) = algebraMap F E a :=
      fun g hg a => (hG _).1 ⟨a, rfl⟩ g hg
    have h2 : IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥ := by
      refine eq_bot_iff.2 fun x hx => ?_
      rw [IntermediateField.mem_fixedField_iff] at hx
      rw [IntermediateField.mem_bot]
      refine (hG x).2 fun g hg => ?_
      let σ : E ≃ₐ[F] E := { g with commutes' := hfix g hg }
      exact hx σ trivial
    have := IsGalois.of_fixedField_eq_bot F E h2
    exact ⟨this.to_normal, this.to_isSeparable⟩
  tfae_finish

end GaloisTFAE

section Radicals

variable (F : Type*) [Field F]

/-- AA-439. A polynomial `f` over `F` is solvable by radicals if all its roots in a splitting field
lie in `solvableByRad F`, the smallest subfield closed under taking `n`-th roots. This is the
book's tower-of-radical-extensions definition, phrased through Mathlib's closure: a root lies in
such a tower iff it is built from `F` by field operations and radicals. -/
@[kb "judson2026" "Definition (solvable by radicals), p. 328"]
def SolvableByRadicals (f : F[X]) : Prop :=
  ∀ x ∈ f.rootSet f.SplittingField, x ∈ solvableByRad F f.SplittingField

variable {F}

/-- AA-442. If a polynomial is solvable by radicals, its Galois group is solvable (stated without
the characteristic-0 hypothesis, which Mathlib does not need). -/
@[kb "judson2026" "Theorem 23.3.4, p. 330"]
theorem isSolvable_gal_of_solvableByRadicals {f : F[X]} (hf : SolvableByRadicals F f) :
    Group.IsSolvable f.Gal := by
  by_cases h0 : f = 0
  · subst h0
    exact gal_zero_isSolvable
  classical
  let E := f.SplittingField
  let s : Multiset F[X] := (f.aroots E).map (minpoly F)
  have hrad : ∀ x ∈ f.aroots E, x ∈ solvableByRad F E := fun x hx =>
    hf x (by
      rw [mem_rootSet]
      exact ⟨h0, (mem_aroots.1 hx).2⟩)
  have hs : ∀ q ∈ s, Group.IsSolvable q.Gal := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hq
    exact isSolvable_gal_minpoly (hrad x hx)
  have hne : s.prod ≠ 0 := by
    rw [Ne, Multiset.prod_eq_zero_iff]
    intro hq
    obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.1 hq
    exact minpoly.ne_zero (isIntegral_of_mem_solvableByRad (hrad x hx)) hx0
  have hdvd : f ∣ s.prod := by
    rw [← map_dvd_map' (algebraMap F E)]
    have hsp := (SplittingField.splits f).eq_prod_roots
    have hlc : (f.map (algebraMap F E)).leadingCoeff ≠ 0 := by
      rw [Ne, leadingCoeff_eq_zero]
      exact map_ne_zero h0
    have hu : IsUnit (C (f.map (algebraMap F E)).leadingCoeff) := isUnit_C.2 hlc.isUnit
    refine (dvd_of_eq hsp).trans ((hu.mul_left_dvd).2 ?_)
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    exact Multiset.prod_dvd_prod_of_dvd _ _ fun x hx => by
      rw [Function.comp_apply, dvd_iff_isRoot, IsRoot, eval_map_algebraMap]
      exact minpoly.aeval F x ▸ rfl
  have := gal_prod_isSolvable hs
  exact Group.isSolvable_of_surjective (Gal.restrictDvd_surjective hdvd hne)

end Radicals

namespace Quintic

/-- The integer polynomial `x^5 - 6x^3 - 27x - 3`. -/
noncomputable def quinticZ : ℤ[X] := X ^ 5 - C 6 * X ^ 3 - C 27 * X - C 3

/-- The rational polynomial `x^5 - 6x^3 - 27x - 3` of the book's example. -/
noncomputable def quintic : ℚ[X] := X ^ 5 - C 6 * X ^ 3 - C 27 * X - C 3

theorem quinticZ_natDegree : quinticZ.natDegree = 5 := by
  unfold quinticZ
  compute_degree!

theorem quinticZ_monic : quinticZ.Monic := by
  unfold quinticZ
  monicity!

theorem quinticZ_coeff (n : ℕ) : quinticZ.coeff n =
    if n = 5 then 1 else if n = 3 then -6 else if n = 1 then -27 else if n = 0 then -3 else 0 := by
  unfold quinticZ
  simp only [coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  split_ifs <;> omega

theorem quintic_map : quinticZ.map (Int.castRingHom ℚ) = quintic := by
  simp only [quinticZ, quintic, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C]
  norm_num

/-- Eisenstein at the prime 3 (then Gauss's lemma). -/
theorem quintic_irreducible : Irreducible quintic := by
  rw [← quintic_map,
    ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast quinticZ_monic.isPrimitive]
  have hP : (Ideal.span {(3 : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact_mod_cast Nat.prime_iff_prime_int.1 Nat.prime_three
  refine irreducible_of_eisenstein_criterion hP ?_ ?_ ?_ ?_ quinticZ_monic.isPrimitive
  · rw [quinticZ_monic.leadingCoeff, Ideal.mem_span_singleton]
    norm_num
  · intro n hn
    rw [degree_eq_natDegree quinticZ_monic.ne_zero, quinticZ_natDegree] at hn
    have : n < 5 := by exact_mod_cast hn
    rw [quinticZ_coeff, Ideal.mem_span_singleton]
    split_ifs <;> omega
  · rw [degree_eq_natDegree quinticZ_monic.ne_zero, quinticZ_natDegree]
    norm_num
  · rw [quinticZ_coeff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num

theorem quintic_natDegree : quintic.natDegree = 5 := by
  unfold quintic
  compute_degree!

theorem mem_rootSet_real (x : ℝ) :
    x ∈ quintic.rootSet ℝ ↔ x ^ 5 - 6 * x ^ 3 - 27 * x - 3 = 0 := by
  rw [mem_rootSet]
  have : quintic ≠ 0 := quintic_irreducible.ne_zero
  constructor
  · rintro ⟨_, h⟩
    simpa [quintic] using h
  · intro h
    exact ⟨this, by simpa [quintic] using h⟩

theorem mem_rootSet_deriv_real (x : ℝ) :
    x ∈ (derivative quintic).rootSet ℝ ↔ 5 * x ^ 4 - 18 * x ^ 2 - 27 = 0 := by
  have hd : derivative quintic = C 5 * X ^ 4 - C 18 * X ^ 2 - C 27 := by
    simp only [quintic, derivative_sub, derivative_mul, derivative_X_pow, derivative_C,
      derivative_X]
    simp
    rw [← mul_assoc, ← C_mul]
    norm_num
  have hne : derivative quintic ≠ 0 := by
    rw [Ne, derivative_eq_zero, quintic_natDegree]
    norm_num
  rw [mem_rootSet]
  constructor
  · rintro ⟨_, h⟩
    rw [hd] at h
    simpa using h
  · intro h
    refine ⟨hne, ?_⟩
    rw [hd]
    simpa using h

/-- The derivative has at most two real roots. -/
theorem card_rootSet_deriv_real_le : Fintype.card ((derivative quintic).rootSet ℝ) ≤ 2 := by
  classical
  have hsq : ∀ x y : ℝ, 5 * x ^ 4 - 18 * x ^ 2 - 27 = 0 → 5 * y ^ 4 - 18 * y ^ 2 - 27 = 0 →
      x ^ 2 = y ^ 2 := by
    intro x y hx hy
    have h1 : (x ^ 2 - y ^ 2) * (5 * (x ^ 2 + y ^ 2) - 18) = 0 := by
      linear_combination hx - hy
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · exfalso
      have h2 : y ^ 2 = 18 / 5 - x ^ 2 := by linarith
      have h3 : 5 * (x ^ 2 * y ^ 2) = -27 := by
        rw [h2]
        linear_combination (-1 : ℝ) * hx
      nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  rw [← Set.toFinset_card]
  by_cases hex : ∃ x, x ∈ (derivative quintic).rootSet ℝ
  · obtain ⟨x0, hx0⟩ := hex
    rw [mem_rootSet_deriv_real] at hx0
    refine (Finset.card_le_card (t := {x0, -x0}) ?_).trans Finset.card_le_two
    intro y hy
    rw [Set.mem_toFinset, mem_rootSet_deriv_real] at hy
    have : y ^ 2 = x0 ^ 2 := hsq y x0 hy hx0
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h | h <;> simp [h]
  · rw [Set.toFinset_card]
    have : IsEmpty ((derivative quintic).rootSet ℝ) := ⟨fun ⟨x, hx⟩ => hex ⟨x, hx⟩⟩
    simp

/-- At most three real roots (Rolle). -/
theorem card_rootSet_real_le : Fintype.card (quintic.rootSet ℝ) ≤ 3 :=
  (card_rootSet_le_derivative quintic).trans (by have := card_rootSet_deriv_real_le; omega)

/-- At least three real roots (intermediate value theorem on `[-3,-2]`, `[-2,0]`, `[0,4]`). -/
theorem card_rootSet_real_ge : 3 ≤ Fintype.card (quintic.rootSet ℝ) := by
  classical
  let f : ℝ → ℝ := fun x => x ^ 5 - 6 * x ^ 3 - 27 * x - 3
  have hf : Continuous f := by fun_prop
  obtain ⟨r1, hr1, h1⟩ : ∃ r ∈ Set.Ioo (-3 : ℝ) (-2), f r = 0 :=
    intermediate_value_Ioo (by norm_num) hf.continuousOn (by norm_num [f])
  obtain ⟨r2, hr2, h2⟩ : ∃ r ∈ Set.Ioo (-2 : ℝ) 0, f r = 0 :=
    intermediate_value_Ioo' (by norm_num) hf.continuousOn (by norm_num [f])
  obtain ⟨r3, hr3, h3⟩ : ∃ r ∈ Set.Ioo (0 : ℝ) 4, f r = 0 :=
    intermediate_value_Ioo (by norm_num) hf.continuousOn (by norm_num [f])
  rw [← Set.toFinset_card]
  have hcard : ({r1, r2, r3} : Finset ℝ).card = 3 := by
    apply Finset.card_eq_three.2
    refine ⟨r1, r2, r3, ?_, ?_, ?_, rfl⟩ <;> intro h <;> simp only [Set.mem_Ioo] at hr1 hr2 hr3 <;>
      linarith [hr1.1, hr1.2, hr2.1, hr2.2, hr3.1, hr3.2]
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  rw [Set.mem_toFinset, mem_rootSet_real]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

theorem card_rootSet_complex : Fintype.card (quintic.rootSet ℂ) = 5 := by
  have hsep : quintic.Separable := quintic_irreducible.separable
  have := card_rootSet_eq_natDegree (K := ℂ) hsep (IsAlgClosed.splits _)
  rw [this, quintic_natDegree]

instance : Fact ((quintic.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩

/-- AA-444. The Galois group of `x^5 - 6x^3 - 27x - 3` over `ℚ` acts on its five complex roots
as the full symmetric group (the action homomorphism is bijective). -/
@[kb "judson2026" "Example 23.3.7, p. 331"]
theorem quintic_galActionHom_bijective :
    Function.Bijective (Polynomial.Gal.galActionHom quintic ℂ) := by
  refine Polynomial.Gal.galActionHom_bijective_of_prime_degree quintic_irreducible
    (by rw [quintic_natDegree]; exact Nat.prime_five) ?_
  rw [card_rootSet_complex]
  have := card_rootSet_real_le
  have := card_rootSet_real_ge
  omega

/-- AA-444. The Galois group of `x^5 - 6x^3 - 27x - 3` over `ℚ` is not solvable (it is `S₅`). -/
theorem quintic_gal_not_isSolvable : ¬ Group.IsSolvable quintic.Gal := by
  intro h
  have : Group.IsSolvable (Equiv.Perm (quintic.rootSet ℂ)) :=
    Group.isSolvable_of_surjective quintic_galActionHom_bijective.2
  refine Equiv.Perm.not_isSolvable (quintic.rootSet ℂ) ?_ this
  rw [Cardinal.mk_fintype, card_rootSet_complex]
  norm_num

/-- AA-444. The quintic `x^5 - 6x^3 - 27x - 3` is not solvable by radicals over `ℚ`. -/
theorem quintic_not_solvableByRadicals : ¬ SolvableByRadicals ℚ quintic := fun h =>
  quintic_gal_not_isSolvable (isSolvable_gal_of_solvableByRadicals h)

end Quintic

end UndergradKB.AbstractAlgebra
