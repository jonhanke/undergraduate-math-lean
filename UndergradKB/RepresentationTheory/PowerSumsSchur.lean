import Mathlib.Data.Fin.Tuple.Sort
import UndergradKB.RepresentationTheory.FrobeniusTheorem
import UndergradKB.Common.Attr

/-! # Power sums in terms of Schur polynomials (Etingof et al., Proposition 4.61)

* `alternating_eq_sum_alternant`: an alternating polynomial `F` (one with `F(x_{π 1}, …) = sign π · F`) in
  `N` variables is the sum, over its strictly decreasing exponents `a`, of `F_a · det (x_i ^ a_j)`.
* `cyclePoly_eq_sum_frobChar_schurPoly` (Proposition 4.61, with Theorem 4.47 identifying `θ_λ` with the
  character of `V_λ`): `∏_m (x_1^m + ⋯ + x_N^m)^{i_m} = ∑_λ θ_λ(g) S_λ(x)`, the sum over nonincreasing `λ` with
  at most `N` parts and sum `n`.
-/

namespace UndergradKB.RepresentationTheory

open Finset MvPolynomial

variable {N : ℕ}

/-- A polynomial is alternating if permuting the variables by `π` multiplies it by `sign π`. -/
def IsAlternating (F : MvPolynomial (Fin N) ℂ) : Prop :=
  ∀ π : Equiv.Perm (Fin N), rename π F = ((Equiv.Perm.sign π : ℤ) : ℂ) • F

lemma mapDomain_perm_apply (d : Fin N →₀ ℕ) (π : Equiv.Perm (Fin N)) (k : Fin N) :
    d.mapDomain π k = d (π.symm k) := by
  conv_lhs => rw [← π.apply_symm_apply k]
  exact Finsupp.mapDomain_apply_of_injective π.injective d _

lemma IsAlternating.coeff_mapDomain {F : MvPolynomial (Fin N) ℂ} (hF : IsAlternating F)
    (d : Fin N →₀ ℕ) (π : Equiv.Perm (Fin N)) :
    F.coeff (d.mapDomain π) = ((Equiv.Perm.sign π : ℤ) : ℂ) * F.coeff d := by
  have h := coeff_rename_mapDomain π π.injective F d
  rw [hF π, coeff_smul, smul_eq_mul] at h
  have hs : ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign π : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [← h, ← mul_assoc, hs, one_mul]

lemma IsAlternating.coeff_eq_zero {F : MvPolynomial (Fin N) ℂ} (hF : IsAlternating F)
    {d : Fin N →₀ ℕ} {i j : Fin N} (hij : i ≠ j) (hd : d i = d j) : F.coeff d = 0 := by
  have hsw : d.mapDomain (Equiv.swap i j) = d := by
    ext k
    rw [mapDomain_perm_apply, Equiv.symm_swap]
    rcases eq_or_ne k i with rfl | hki
    · simp [hd]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hd]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := hF.coeff_mapDomain d (Equiv.swap i j)
  rw [hsw, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  have : (2 : ℂ) * F.coeff d = 0 := by linear_combination h
  simpa using this

/-- The alternant `det (x_i ^ a_j)` as a signed sum of monomials. -/
lemma alternant_eq_sum (a : Fin N → ℕ) :
    (alternant a : MvPolynomial (Fin N) ℂ) = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      monomial ((Finsupp.equivFunOnFinite.symm a).mapDomain σ) (1 : ℂ) := by
  unfold alternant
  rw [Matrix.det_apply]
  refine sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
  congr 1
  simp only [Matrix.of_apply]
  rw [FrobeniusDet.prod_X_pow_eq_monomial (fun j => σ j) a]
  have hE : (∑ j, Finsupp.single (σ j) (a j)) = (Finsupp.equivFunOnFinite.symm a).mapDomain σ := by
    ext k
    rw [mapDomain_perm_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single (σ.symm k)]
    · simp
    · intro j _ hj
      refine Finsupp.single_eq_of_ne' fun h => hj ?_
      rw [← h, Equiv.symm_apply_apply]
    · simp
  rw [hE]

lemma coeff_alternant (a : Fin N → ℕ) (b : Fin N →₀ ℕ) :
    (alternant a : MvPolynomial (Fin N) ℂ).coeff b = ∑ σ : Equiv.Perm (Fin N),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if (Finsupp.equivFunOnFinite.symm a).mapDomain σ = b then 1 else 0) := by
  classical
  rw [alternant_eq_sum, coeff_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [coeff_smul, coeff_monomial, smul_eq_mul]

lemma eq_comp_of_mapDomain_eq {a : Fin N → ℕ} {b : Fin N →₀ ℕ} {σ : Equiv.Perm (Fin N)}
    (h : (Finsupp.equivFunOnFinite.symm a).mapDomain σ = b) : a = ⇑b ∘ σ := by
  funext i
  rw [Function.comp_apply, ← h, mapDomain_perm_apply, Equiv.symm_apply_apply]
  rfl

/-- **Alternating polynomials are combinations of alternants.** -/
theorem alternating_eq_sum_alternant {F : MvPolynomial (Fin N) ℂ} (hF : IsAlternating F) :
    F = ∑ d ∈ F.support.filter (fun d : Fin N →₀ ℕ => StrictAnti ⇑d), F.coeff d • (alternant ⇑d : MvPolynomial (Fin N) ℂ) := by
  classical
  ext b
  rw [coeff_sum]
  simp_rw [coeff_smul, coeff_alternant, smul_eq_mul]
  by_cases hinj : Function.Injective ⇑b
  · set π := Tuple.sortDesc ⇑b
    have hanti : StrictAnti (⇑b ∘ π) :=
      (Tuple.antitone_sortDesc ⇑b).strictAnti_of_injective (hinj.comp π.injective)
    set d0 : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (⇑b ∘ π)
    have hd0 : d0.mapDomain π = b := by
      ext k
      rw [mapDomain_perm_apply]
      simp [d0]
    have hb : F.coeff b = ((Equiv.Perm.sign π : ℤ) : ℂ) * F.coeff d0 := by
      rw [← hF.coeff_mapDomain, hd0]
    have hinner : ∀ d ∈ F.support.filter (fun d : Fin N →₀ ℕ => StrictAnti ⇑d),
        F.coeff d * ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (if (Finsupp.equivFunOnFinite.symm ⇑d).mapDomain σ = b then 1 else 0) =
        if d = d0 then F.coeff d0 * ((Equiv.Perm.sign π : ℤ) : ℂ) else 0 := by
      intro d hd
      have hds : StrictAnti ⇑d := (mem_filter.1 hd).2
      rw [sum_eq_single π]
      · by_cases hdd : d = d0
        · subst hdd
          have : Finsupp.equivFunOnFinite.symm ⇑d0 = d0 := by ext; rfl
          rw [if_pos rfl, this, if_pos hd0, mul_one, mul_comm]
        · rw [if_neg hdd]
          rw [if_neg, mul_zero, mul_zero]
          intro h
          apply hdd
          have := eq_comp_of_mapDomain_eq h
          ext i
          exact congrFun this i
      · intro σ _ hσ
        rw [if_neg, mul_zero]
        intro h
        apply hσ
        have h1 := eq_comp_of_mapDomain_eq h
        have h2 : StrictAnti ((⇑b ∘ π) ∘ (π.symm * σ)) := by
          have : (⇑b ∘ π) ∘ ⇑(π.symm * σ) = ⇑b ∘ σ := by
            funext i; simp
          rw [this, ← h1]; exact hds
        have := FrobeniusDet.perm_eq_one_of_strictAnti hanti h2
        calc σ = π * (π.symm * σ) := by ext; simp
          _ = π := by rw [this, mul_one]
      · simp
    rw [sum_congr rfl hinner, sum_ite_eq']
    split_ifs with hmem
    · rw [hb, mul_comm]
    · rw [hb]
      have : F.coeff d0 = 0 := by
        by_contra hne
        exact hmem (mem_filter.2 ⟨mem_support_iff.2 hne, hanti⟩)
      rw [this, mul_zero]
  · obtain ⟨i, j, hbij, hij⟩ : ∃ i j, b i = b j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, h1, h2⟩ := hinj
      exact ⟨i, j, h1, h2⟩
    rw [hF.coeff_eq_zero hij hbij]
    refine (sum_eq_zero fun d hd => ?_).symm
    have hds : StrictAnti ⇑d := (mem_filter.1 hd).2
    rw [sum_eq_zero, mul_zero]
    intro σ _
    rw [if_neg, mul_zero]
    intro h
    have h1 := eq_comp_of_mapDomain_eq h
    apply hij
    have : (⇑b ∘ σ) (σ.symm i) = (⇑b ∘ σ) (σ.symm j) := by simp [hbij]
    rw [← h1] at this
    simpa using hds.injective this

/-! ### Proposition 4.61 -/

lemma isAlternating_vandermondeDelta : IsAlternating (vandermondeDelta ℂ N) := by
  intro π
  rw [← det_projVandermonde_one]
  set M := Matrix.projVandermonde (1 : Fin N → MvPolynomial (Fin N) ℂ) X
  have h : rename π (Matrix.det M) = Matrix.det (M.submatrix π id) := by
    rw [show (rename π) (Matrix.det M) =
      ((rename π : MvPolynomial (Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N) ℂ) :
        MvPolynomial (Fin N) ℂ →+* MvPolynomial (Fin N) ℂ) (Matrix.det M) from rfl, RingHom.map_det]
    congr 1
    ext i j
    simp [M, Matrix.projVandermonde_apply]
  rw [h, Matrix.det_permute, Algebra.smul_def, map_intCast]

lemma rename_cyclePoly (n : ℕ) (g : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin N)) :
    rename π (cyclePoly n N g) = cyclePoly n N g := by
  unfold cyclePoly
  simp only [map_prod, map_pow]
  refine prod_congr rfl fun m _ => ?_
  rw [psum_isSymmetric (Fin N) ℂ m π]

lemma isAlternating_delta_mul_cyclePoly (n : ℕ) (g : Equiv.Perm (Fin n)) :
    IsAlternating (vandermondeDelta ℂ N * cyclePoly n N g) := by
  intro π
  have h1 : rename π (vandermondeDelta ℂ N) = ((Equiv.Perm.sign π : ℤ) : ℂ) • vandermondeDelta ℂ N :=
    isAlternating_vandermondeDelta π
  rw [map_mul, h1, rename_cyclePoly, smul_mul_assoc]

lemma strictAnti_add_le {d : Fin N → ℕ} (hd : StrictAnti d) :
    ∀ k : ℕ, ∀ i j : Fin N, (j : ℕ) = i + k → d j + k ≤ d i := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have : j = i := Fin.ext (by simpa using h)
    subst this
    simp
  | succ k ih =>
    intro i j h
    have hj : (i : ℕ) + k < N := by have := j.isLt; omega
    have h1 := ih i ⟨i + k, hj⟩ rfl
    have h2 : d j < d ⟨i + k, hj⟩ := hd (Fin.lt_def.2 (by simp; omega))
    omega

lemma rhoExp_le_of_strictAnti {d : Fin N → ℕ} (hd : StrictAnti d) (i : Fin N) : rhoExp N i ≤ d i := by
  have := strictAnti_add_le hd (N - 1 - i) i ⟨N - 1, by have := i.isLt; omega⟩ (by simp; have := i.isLt; omega)
  simp only [rhoExp, Fin.val_rev]
  omega

lemma antitone_sub_rhoExp {d : Fin N → ℕ} (hd : StrictAnti d) : Antitone fun i => d i - rhoExp N i := by
  intro i j hij
  have := strictAnti_add_le hd (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega)
  have h1 := rhoExp_le_of_strictAnti hd i
  have h2 := rhoExp_le_of_strictAnti hd j
  simp only [rhoExp, Fin.val_rev] at h1 h2 ⊢
  have : (i : ℕ) ≤ j := hij
  omega

lemma coeffChar_eq_zero_of_sum_ne {n : ℕ} (α : Fin N → ℕ) (h : ∑ i, α i ≠ n) (g : Equiv.Perm (Fin n)) :
    coeffChar n N α g = 0 := by
  classical
  rw [coeffChar, coeff_cyclePoly_eq_card, Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
  rintro f - ⟨-, hf⟩
  apply h
  rw [← Finset.sum_congr rfl fun j _ => hf j]
  have := (Finset.card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_fin] at this
  exact this.symm

lemma frobChar_eq_zero_of_sum_ne {n : ℕ} {lam : Fin N → ℕ} (h : ∑ i, lam i ≠ n) (g : Equiv.Perm (Fin n)) :
    frobChar n N lam g = 0 := by
  rw [frobChar_eq_sum']
  refine sum_eq_zero fun σ _ => ?_
  split_ifs with hP
  · rw [coeffChar_eq_zero_of_sum_ne _ (by rw [sum_termExp hP]; exact h), mul_zero]
  · rw [mul_zero]

/-- The nonincreasing vectors `λ_1 ≥ ⋯ ≥ λ_N` of naturals with sum `n` (partitions of `n` with at most `N` parts). -/
noncomputable def partitionVecs (n N : ℕ) : Finset (Fin N → ℕ) :=
  (Fintype.piFinset fun _ : Fin N => range (n + 1)).filter fun lam => Antitone lam ∧ ∑ i, lam i = n

lemma mem_partitionVecs {n : ℕ} {lam : Fin N → ℕ} : lam ∈ partitionVecs n N ↔ Antitone lam ∧ ∑ i, lam i = n := by
  unfold partitionVecs
  simp only [mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  rintro ⟨-, hs⟩ i
  have : lam i ≤ ∑ i, lam i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  omega

/-- **Proposition 4.61.**  `∏_m (x_1^m + ⋯ + x_N^m)^{i_m} = ∑_λ θ_λ(g) S_λ(x)`, the sum over the partitions `λ` of
`n` with at most `N` parts; by Theorem 4.47 (`frobenius_character_formula`) `θ_λ` is the character of `V_λ`. -/
@[kb "etingof2011" "Proposition 4.61, p. 66"]
theorem cyclePoly_eq_sum_frobChar_schurPoly (n : ℕ) (g : Equiv.Perm (Fin n)) :
    cyclePoly n N g = ∑ lam ∈ partitionVecs n N, frobChar n N lam g • (schurPoly lam : MvPolynomial (Fin N) ℂ) := by
  classical
  have hF := alternating_eq_sum_alternant (isAlternating_delta_mul_cyclePoly (N := N) n g)
  set S := (vandermondeDelta ℂ N * cyclePoly n N g).support.filter (fun d : Fin N →₀ ℕ => StrictAnti ⇑d)
  have hlamS : ∀ d ∈ S, (vandermondeDelta ℂ N * cyclePoly n N g).coeff d = frobChar n N (fun i => d i - rhoExp N i) g ∧
      (alternant ⇑d : MvPolynomial (Fin N) ℂ) = vandermondeDelta ℂ N * schurPoly (fun i => d i - rhoExp N i) := by
    intro d hd
    have hds : StrictAnti ⇑d := (mem_filter.1 hd).2
    have hsh : shiftExp (fun i => d i - rhoExp N i) = d := by
      ext i
      show d i - rhoExp N i + rhoExp N i = d i
      have := rhoExp_le_of_strictAnti hds i
      omega
    refine ⟨by rw [frobChar, hsh], ?_⟩
    rw [← schurAlternant_eq_vandermondeDelta_mul_schurPoly]
    unfold schurAlternant
    congr 1
    funext j
    have := rhoExp_le_of_strictAnti hds j
    simp only [schurExp, rhoExp] at this ⊢
    omega
  have hsum : vandermondeDelta ℂ N * cyclePoly n N g = vandermondeDelta ℂ N * ∑ d ∈ S, frobChar n N (fun i => d i - rhoExp N i) g •
      (schurPoly (fun i => d i - rhoExp N i) : MvPolynomial (Fin N) ℂ) := by
    conv_lhs => rw [hF]
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    rw [(hlamS d hd).1, (hlamS d hd).2, mul_smul_comm]
  have hne : vandermondeDelta ℂ N ≠ 0 := by
    unfold vandermondeDelta
    refine prod_ne_zero_iff.2 (fun i _ => prod_ne_zero_iff.2 (fun j hj => ?_))
    rw [sub_ne_zero]
    intro hij
    exact (ne_of_gt (mem_Ioi.1 hj)) (MvPolynomial.X_injective hij).symm
  have h1 : cyclePoly n N g = ∑ d ∈ S, frobChar n N (fun i => d i - rhoExp N i) g •
      (schurPoly (fun i => d i - rhoExp N i) : MvPolynomial (Fin N) ℂ) :=
    mul_left_cancel₀ hne hsum
  rw [h1]
  have hinj : Set.InjOn (fun d : Fin N →₀ ℕ => fun i => d i - rhoExp N i) S := by
    intro d hd d' hd' h
    ext i
    have := congrFun h i
    have h1 := rhoExp_le_of_strictAnti (mem_filter.1 hd).2 i
    have h2 := rhoExp_le_of_strictAnti (mem_filter.1 hd').2 i
    simp only at this
    omega
  rw [← sum_image (f := fun lam => frobChar n N lam g • (schurPoly lam : MvPolynomial (Fin N) ℂ)) hinj]
  refine sum_subset ?_ ?_
  · intro lam hlam
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hlam
    rw [mem_partitionVecs]
    refine ⟨antitone_sub_rhoExp (mem_filter.1 hd).2, ?_⟩
    by_contra hs
    have h0 := frobChar_eq_zero_of_sum_ne hs g
    rw [← (hlamS d hd).1] at h0
    exact (mem_support_iff.1 (mem_filter.1 hd).1) h0
  · intro lam hlam hnot
    have hl := (mem_partitionVecs.1 hlam).1
    suffices frobChar n N lam g = 0 by rw [this, zero_smul]
    by_contra h0
    apply hnot
    refine mem_image.2 ⟨shiftExp lam, mem_filter.2 ⟨mem_support_iff.2 h0, ?_⟩, ?_⟩
    · exact strictAnti_add_rho hl
    · funext i
      simp [shiftExp]

/-- **Proposition 4.61, the coefficients are characters.**  For each partition `λ` of `n` with at most `N` parts,
`θ_λ` is the character of the Specht module of the Young diagram with row lengths `λ` (Theorem 4.47). -/
@[kb "etingof2011" "Proposition 4.61, p. 66"]
theorem exists_spechtChar_eq_frobChar {n : ℕ} {lam : Fin N → ℕ} (hlam : lam ∈ partitionVecs n N) :
    ∃ la : DiagramsOfSize n, la.1.colLen 0 ≤ N ∧ (∀ j : Fin N, la.1.rowLen j = lam j) ∧
      ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) = frobChar n N lam := by
  obtain ⟨hl, hs⟩ := mem_partitionVecs.1 hlam
  obtain ⟨la, hN, hrow⟩ := exists_diagram_of_antitone lam hl hs
  refine ⟨la, hN, hrow, ?_⟩
  rw [frobenius_character_formula la hN]
  congr 1
  funext j
  exact hrow j

end UndergradKB.RepresentationTheory
