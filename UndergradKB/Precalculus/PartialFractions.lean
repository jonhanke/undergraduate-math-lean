import UndergradKB.Precalculus.Matrices
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Partial fractions in the book's form (Stitz-Zeager, Precalculus, Theorem 8.10)

Wave 1 proved the decomposition for monic pairwise coprime factors in the field of rational functions
(`partial_fractions_proper`). Here the statement is the book's: the denominator is factored completely into a
nonzero constant, powers `(a x + b)^m` of linear factors with distinct zeros, and powers `(p x² + q x + r)^n` of
irreducible quadratics (`q² - 4 p r < 0`), no two of them constant multiples of each other. Then for every `x`
where the denominator is nonzero, `N(x)/D(x)` is the sum of terms `A / (a x + b)^j` (`1 ≤ j ≤ m`) and
`(B x + C) / (p x² + q x + r)^j` (`1 ≤ j ≤ n`), as an identity of real numbers.

Proof: normalise each factor to a monic one, use the polynomial identity of wave 1, evaluate, and read off the
numerators from their degrees.
-/

namespace UndergradKB.Precalculus

open Polynomial

/-- Evaluated partial fraction identity for monic pairwise coprime factors. -/
theorem pf_eval_monic {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → ℝ[X]}
    (hg : ∀ i ∈ s, (g i).Monic) (hgg : Set.Pairwise (↑s) fun i j => IsCoprime (g i) (g j))
    (e : ι → ℕ) (N : ℝ[X]) (hN : N.degree < (∏ k ∈ s, g k ^ e k).degree) :
    ∃ r : (i : ι) → Fin (e i) → ℝ[X], (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      ∀ x : ℝ, (∀ i ∈ s, (g i).eval x ≠ 0) →
        N.eval x / (∏ k ∈ s, g k ^ e k).eval x =
          ∑ i ∈ s, ∑ j : Fin (e i), (r i j).eval x / (g i).eval x ^ (j.1 + 1) := by
  obtain ⟨r, hr, hNeq⟩ := pf_poly_identity hg hgg e N hN
  refine ⟨fun i j => r i j.rev, fun i hi j => hr i hi _, fun x hx => ?_⟩
  rw [hNeq, eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [eval_finsetSum, Finset.sum_div, ← Equiv.sum_comp Fin.revPerm]
  refine Fintype.sum_congr _ _ fun j => ?_
  obtain ⟨t, ht⟩ : ∃ t, e i = j.1 + 1 + t := ⟨e i - (j.1 + 1), by have := j.2; omega⟩
  have hrev : (j.rev : ℕ) = t := by
    rw [Fin.val_rev]
    omega
  have hD : (∏ k ∈ s, g k ^ e k).eval x =
      (g i).eval x ^ (j.1 + 1 + t) * (∏ k ∈ s.erase i, g k ^ e k).eval x := by
    rw [← Finset.mul_prod_erase s (fun k => g k ^ e k) hi, eval_mul, eval_pow]
    exact congrArg (fun n : ℕ => (g i).eval x ^ n * (∏ k ∈ s.erase i, g k ^ e k).eval x) ht
  have hP : (∏ k ∈ s.erase i, g k ^ e k).eval x ≠ 0 := by
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun k hk => by
      rw [eval_pow]; exact pow_ne_zero _ (hx k (Finset.mem_of_mem_erase hk))
  simp only [Fin.revPerm_apply]
  rw [hD, eval_mul, eval_mul, eval_pow, hrev]
  have h1 := hx i hi
  field_simp
  ring

/-- Evaluated partial fraction identity for nonzero pairwise coprime factors (not necessarily monic). -/
theorem pf_eval {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → ℝ[X]}
    (hg : ∀ i ∈ s, g i ≠ 0) (hgg : Set.Pairwise (↑s) fun i j => IsCoprime (g i) (g j))
    (e : ι → ℕ) (N : ℝ[X]) (hN : N.degree < (∏ k ∈ s, g k ^ e k).degree) :
    ∃ r : (i : ι) → Fin (e i) → ℝ[X], (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      ∀ x : ℝ, (∀ i ∈ s, (g i).eval x ≠ 0) →
        N.eval x / (∏ k ∈ s, g k ^ e k).eval x =
          ∑ i ∈ s, ∑ j : Fin (e i), (r i j).eval x / (g i).eval x ^ (j.1 + 1) := by
  set u : ι → ℝ := fun i => (g i).leadingCoeff with hu
  have hu0 : ∀ i ∈ s, u i ≠ 0 := fun i hi => leadingCoeff_ne_zero.2 (hg i hi)
  set g' : ι → ℝ[X] := fun i => g i * C (u i)⁻¹ with hg'
  have hg'm : ∀ i ∈ s, (g' i).Monic := fun i hi => monic_mul_leadingCoeff_inv (hg i hi)
  have hunit : ∀ i ∈ s, IsUnit (C (u i)⁻¹) := fun i hi =>
    isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (hu0 i hi)))
  have hgg' : Set.Pairwise (↑s) fun i j => IsCoprime (g' i) (g' j) := fun i hi j hj hij =>
    (isCoprime_mul_units_right (hunit i hi) (hunit j hj) _ _).2 (hgg hi hj hij)
  set c : ℝ := ∏ k ∈ s, ((u k)⁻¹) ^ e k with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk => pow_ne_zero _ (inv_ne_zero (hu0 k hk))
  have hD' : ∏ k ∈ s, g' k ^ e k = (∏ k ∈ s, g k ^ e k) * C c := by
    simp only [hg', mul_pow, Finset.prod_mul_distrib, hc, map_prod, C_pow]
  have hN' : N.degree < (∏ k ∈ s, g' k ^ e k).degree := by
    rw [hD', degree_mul_C hc0]; exact hN
  obtain ⟨r', hr', h⟩ := pf_eval_monic hg'm hgg' e N hN'
  refine ⟨fun i j => C (c * u i ^ (j.1 + 1)) * r' i j, fun i hi j => ?_, fun x hx => ?_⟩
  · have hne : c * u i ^ (j.1 + 1) ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ (hu0 i hi))
    rw [degree_C_mul hne]
    have := hr' i hi j
    rwa [hg', degree_mul_C (inv_ne_zero (hu0 i hi))] at this
  · have hx' : ∀ i ∈ s, (g' i).eval x ≠ 0 := fun i hi => by
      simp only [hg', eval_mul, eval_C]
      exact mul_ne_zero (hx i hi) (inv_ne_zero (hu0 i hi))
    have hDx : (∏ k ∈ s, g k ^ e k).eval x ≠ 0 := by
      rw [eval_prod]
      exact Finset.prod_ne_zero_iff.2 fun k hk => by rw [eval_pow]; exact pow_ne_zero _ (hx k hk)
    have h1 : N.eval x / (∏ k ∈ s, g k ^ e k).eval x =
        c * (N.eval x / (∏ k ∈ s, g' k ^ e k).eval x) := by
      rw [hD', eval_mul, eval_C]
      field_simp
    rw [h1, h x hx', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun j => ?_
    have h2 := hx i hi
    have h3 := hu0 i hi
    simp only [hg', eval_mul, eval_C]
    field_simp
    rw [div_pow]
    field_simp

/-! ### The factors of Theorem 8.10 -/

/-- A quadratic `p x² + q x + r` with `q² - 4 p r < 0` has no real zeros. -/
theorem quadratic_eval_ne_zero {p q r : ℝ} (hd : q ^ 2 - 4 * p * r < 0) (x : ℝ) :
    (C p * X ^ 2 + C q * X + C r).eval x ≠ 0 := by
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  intro h
  have hp : p ≠ 0 := by rintro rfl; nlinarith [sq_nonneg q]
  have : q ^ 2 - 4 * p * r = (2 * p * x + q) ^ 2 := by linear_combination (-4 * p) * h
  nlinarith [sq_nonneg (2 * p * x + q)]

theorem quadratic_leading_ne_zero {p q r : ℝ} (hd : q ^ 2 - 4 * p * r < 0) : p ≠ 0 := by
  rintro rfl; nlinarith [sq_nonneg q]

theorem quadratic_irreducible {p q r : ℝ} (hd : q ^ 2 - 4 * p * r < 0) :
    Irreducible (C p * X ^ 2 + C q * X + C r) := by
  have hdeg := natDegree_quadratic (b := q) (c := r) (quadratic_leading_ne_zero hd)
  rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  exact quadratic_eval_ne_zero hd x (mem_roots'.1 hx).2

theorem linear_irreducible {a b : ℝ} (ha : a ≠ 0) : Irreducible (C a * X + C b) :=
  irreducible_of_degree_eq_one (degree_linear ha)

theorem linear_eval_eq_zero {a b : ℝ} (ha : a ≠ 0) : (C a * X + C b).eval (-b / a) = 0 := by
  simp only [eval_add, eval_mul, eval_C, eval_X]
  field_simp
  ring

/-- Linear factors with different zeros are coprime. -/
theorem linear_isCoprime {a b a' b' : ℝ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hz : -b / a ≠ -b' / a') :
    IsCoprime (C a * X + C b) (C a' * X + C b') := by
  have hdet : a' * b - a * b' ≠ 0 := by
    intro h; apply hz
    field_simp
    linarith
  refine ⟨C (a' / (a' * b - a * b')), C (-a / (a' * b - a * b')), ?_⟩
  have e1 : C (a' / (a' * b - a * b')) * (C a * X + C b) + C (-a / (a' * b - a * b')) * (C a' * X + C b') =
      C (a' / (a' * b - a * b') * a + -a / (a' * b - a * b') * a') * X +
        C (a' / (a' * b - a * b') * b + -a / (a' * b - a * b') * b') := by
    simp only [C_add, C_mul]; ring
  have e2 : a' / (a' * b - a * b') * a + -a / (a' * b - a * b') * a' = 0 := by ring
  have e3 : a' / (a' * b - a * b') * b + -a / (a' * b - a * b') * b' = 1 := by
    field_simp
    ring
  rw [e1, e2, e3]
  simp

/-- A linear factor and an irreducible quadratic are coprime. -/
theorem linear_quadratic_isCoprime {a b p q r : ℝ} (ha : a ≠ 0) (hd : q ^ 2 - 4 * p * r < 0) :
    IsCoprime (C a * X + C b) (C p * X ^ 2 + C q * X + C r) := by
  rw [(linear_irreducible (b := b) ha).coprime_iff_not_dvd]
  rintro ⟨h, hh⟩
  apply quadratic_eval_ne_zero hd (-b / a)
  rw [hh, eval_mul, linear_eval_eq_zero ha, zero_mul]

/-- Two irreducible quadratics that are not constant multiples of each other are coprime. -/
theorem quadratic_isCoprime {p q r p' q' r' : ℝ} (hd : q ^ 2 - 4 * p * r < 0)
    (hd' : q' ^ 2 - 4 * p' * r' < 0) (hne : ¬∃ k : ℝ, p' = k * p ∧ q' = k * q ∧ r' = k * r) :
    IsCoprime (C p * X ^ 2 + C q * X + C r) (C p' * X ^ 2 + C q' * X + C r') := by
  rw [(quadratic_irreducible hd).coprime_iff_not_dvd]
  rintro ⟨h, hh⟩
  have hp := quadratic_leading_ne_zero hd
  have hp' := quadratic_leading_ne_zero hd'
  have h0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact quadratic_eval_ne_zero hd' 0 (by rw [hh]; simp)
  have hdeg := congrArg natDegree hh
  rw [natDegree_quadratic hp', natDegree_mul (quadratic_irreducible hd).ne_zero h0,
    natDegree_quadratic hp] at hdeg
  obtain ⟨k, hk⟩ : ∃ k : ℝ, h = C k := ⟨h.coeff 0, eq_C_of_natDegree_eq_zero (by omega)⟩
  rw [hk, mul_comm] at hh
  apply hne
  have c2 := congrArg (fun P => P.coeff 2) hh
  have c1 := congrArg (fun P => P.coeff 1) hh
  have c0 := congrArg (fun P => P.coeff 0) hh
  simp only [coeff_C_mul, coeff_add, coeff_X, coeff_C] at c2 c1 c0
  norm_num at c2 c1 c0
  exact ⟨k, by rw [c2, mul_comm], by rw [c1, mul_comm], by rw [c0, mul_comm]⟩

/-! ### Theorem 8.10 -/

/-- Theorem 8.10 (partial fraction decomposition), in the book's form. Let `N/D` be proper (`deg N < deg D`),
where `D = K · ∏ᵢ (aᵢ x + bᵢ)^{mᵢ} · ∏ₖ (pₖ x² + qₖ x + rₖ)^{nₖ}` is factored completely: `K ≠ 0`, the linear
factors have `aᵢ ≠ 0` and distinct zeros `-bᵢ/aᵢ`, the quadratic factors are irreducible (`qₖ² - 4pₖrₖ < 0`) and no
two are constant multiples of each other. Then there are numbers `A i j`, `B k j`, `C k j` such that for every real
`x` with `D(x) ≠ 0`,
`N(x)/D(x) = ∑ᵢ ∑_{j<mᵢ} A i j / (aᵢ x + bᵢ)^{j+1} + ∑ₖ ∑_{j<nₖ} (B k j x + C k j) / (pₖ x² + qₖ x + rₖ)^{j+1}`
(PC-164). -/
@[kb "stitzzeager2013" "Theorem 8.10, p. 642"]
theorem partial_fractions_book {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (a b : ι → ℝ) (m : ι → ℕ) (ha : ∀ i ∈ s, a i ≠ 0) (hm : ∀ i ∈ s, 0 < m i)
    (hlin : Set.Pairwise (↑s) fun i i' => -b i / a i ≠ -b i' / a i')
    (p q r : κ → ℝ) (n : κ → ℕ) (hquad : ∀ k ∈ t, q k ^ 2 - 4 * p k * r k < 0)
    (hdist : Set.Pairwise (↑t) fun k k' =>
      ¬∃ c : ℝ, p k' = c * p k ∧ q k' = c * q k ∧ r k' = c * r k)
    (K : ℝ) (hK : K ≠ 0) (N D : ℝ[X])
    (hD : D = C K * (∏ i ∈ s, (C (a i) * X + C (b i)) ^ m i) *
      ∏ k ∈ t, (C (p k) * X ^ 2 + C (q k) * X + C (r k)) ^ n k)
    (hN : N.degree < D.degree) :
    ∃ (A : (i : ι) → Fin (m i) → ℝ) (B C' : (k : κ) → Fin (n k) → ℝ),
      ∀ x : ℝ, D.eval x ≠ 0 →
        N.eval x / D.eval x =
          ∑ i ∈ s, ∑ j : Fin (m i), A i j / (a i * x + b i) ^ (j.1 + 1) +
          ∑ k ∈ t, ∑ j : Fin (n k), (B k j * x + C' k j) / (p k * x ^ 2 + q k * x + r k) ^ (j.1 + 1) := by
  -- the factors, indexed by `ι ⊕ κ`
  let g : ι ⊕ κ → ℝ[X] := Sum.elim (fun i => C (a i) * X + C (b i))
    (fun k => C (p k) * X ^ 2 + C (q k) * X + C (r k))
  let e : ι ⊕ κ → ℕ := Sum.elim m n
  have hg0 : ∀ σ ∈ s.disjSum t, g σ ≠ 0 := by
    rintro (i | k) hσ
    · rw [Finset.inl_mem_disjSum] at hσ
      exact (linear_irreducible (b := b i) (ha i hσ)).ne_zero
    · rw [Finset.inr_mem_disjSum] at hσ
      exact (quadratic_irreducible (hquad k hσ)).ne_zero
  have hgg : Set.Pairwise (↑(s.disjSum t)) fun σ τ => IsCoprime (g σ) (g τ) := by
    rintro (i | k) hσ (i' | k') hτ hne
    · have hi : i ∈ s := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 hσ)
      have hi' : i' ∈ s := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 hτ)
      exact linear_isCoprime (ha i hi) (ha i' hi') (hlin hi hi' fun h => hne (by rw [h]))
    · have hi : i ∈ s := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 hσ)
      have hk' : k' ∈ t := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 hτ)
      exact linear_quadratic_isCoprime (ha i hi) (hquad k' hk')
    · have hk : k ∈ t := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 hσ)
      have hi' : i' ∈ s := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 hτ)
      exact (linear_quadratic_isCoprime (ha i' hi') (hquad k hk)).symm
    · have hk : k ∈ t := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 hσ)
      have hk' : k' ∈ t := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 hτ)
      exact quadratic_isCoprime (hquad k hk) (hquad k' hk') (hdist hk hk' fun h => hne (by rw [h]))
  have hprod : ∏ σ ∈ s.disjSum t, g σ ^ e σ = (∏ i ∈ s, (C (a i) * X + C (b i)) ^ m i) *
      ∏ k ∈ t, (C (p k) * X ^ 2 + C (q k) * X + C (r k)) ^ n k := by
    rw [Finset.prod_disjSum]; rfl
  have hDK : D = C K * ∏ σ ∈ s.disjSum t, g σ ^ e σ := by rw [hprod, hD, mul_assoc]
  have hN' : (C K⁻¹ * N).degree < (∏ σ ∈ s.disjSum t, g σ ^ e σ).degree := by
    rw [degree_C_mul (inv_ne_zero hK)]
    rw [hDK, degree_C_mul hK] at hN
    exact hN
  obtain ⟨R, hR, hid⟩ := pf_eval hg0 hgg e (C K⁻¹ * N) hN'
  refine ⟨fun i j => (R (Sum.inl i) j).coeff 0, fun k j => (R (Sum.inr k) j).coeff 1,
    fun k j => (R (Sum.inr k) j).coeff 0, fun x hx => ?_⟩
  have hx' : ∀ σ ∈ s.disjSum t, (g σ).eval x ≠ 0 := by
    rintro (i | k) hσ h0
    · rw [Finset.inl_mem_disjSum] at hσ
      apply hx
      rw [hDK, eval_mul, eval_prod]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.inl_mem_disjSum.2 hσ) ?_)
      rw [eval_pow, h0]
      exact zero_pow (Nat.pos_iff_ne_zero.1 (hm i hσ))
    · rw [Finset.inr_mem_disjSum] at hσ
      exact quadratic_eval_ne_zero (hquad k hσ) x h0
  have h1 : N.eval x / D.eval x =
      (C K⁻¹ * N).eval x / (∏ σ ∈ s.disjSum t, g σ ^ e σ).eval x := by
    rw [hDK, eval_mul, eval_C, eval_mul, eval_C]
    field_simp
  rw [h1, hid x hx', Finset.sum_disjSum]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => Fintype.sum_congr _ _ fun j => ?_
    have hi' : Sum.inl i ∈ s.disjSum t := Finset.inl_mem_disjSum.2 hi
    have hdeg : (g (Sum.inl i)).natDegree = 1 := natDegree_linear (ha i hi)
    obtain ⟨A, hA⟩ := (partial_fraction_numerator_shape _ _ (hR _ hi' j)).1 hdeg
    show (R (Sum.inl i) j).eval x / ((C (a i) * X + C (b i)).eval x) ^ (j.1 + 1) =
      (R (Sum.inl i) j).coeff 0 / (a i * x + b i) ^ (j.1 + 1)
    rw [hA]
    simp
  · refine Finset.sum_congr rfl fun k hk => Fintype.sum_congr _ _ fun j => ?_
    have hk' : Sum.inr k ∈ s.disjSum t := Finset.inr_mem_disjSum.2 hk
    have hdeg : (g (Sum.inr k)).natDegree = 2 := natDegree_quadratic (quadratic_leading_ne_zero (hquad k hk))
    obtain ⟨B, C₀, hBC⟩ := (partial_fraction_numerator_shape _ _ (hR _ hk' j)).2 hdeg
    show (R (Sum.inr k) j).eval x / ((C (p k) * X ^ 2 + C (q k) * X + C (r k)).eval x) ^ (j.1 + 1) =
      ((R (Sum.inr k) j).coeff 1 * x + (R (Sum.inr k) j).coeff 0) /
        (p k * x ^ 2 + q k * x + r k) ^ (j.1 + 1)
    rw [hBC]
    simp [coeff_X]

end UndergradKB.Precalculus
