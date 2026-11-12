import UndergradKB.Combinatorics.AeqB.OperatorsMore

/-!
# The adjoint of a recurrence operator (Petkovsek–Wilf–Zeilberger, "A = B", §8.10, p. 173)

CO-511.  For `L = ∑_{k ≤ d} p_k(n) N^k` of order at most `d`, the adjoint is
`L* = ∑_{k ≤ d} p_{d-k}(n+k) N^k` (`RecOp.adjoint`, CO-510).  The book writes its rules with the
two-sided shift `N^{-d}`; conjugation `A ↦ N^d A N^{-d}` is the shift of the coefficients
`p(n) ↦ p(n+d)` (`RecOp.shiftBy`), a ring automorphism of the operator ring, so the rules are
stated without `N^{-1}`:

* `N^d A = (shiftBy d A) N^d` (`N_pow_mul_eq_shiftBy`): `shiftBy d` is the conjugation by `N^d`;
* `L** = N^d L N^{-d}`, i.e. `L** = shiftBy d L` (`adjoint_adjoint`);
* `(LM)* = (N^d M* N^{-d}) L*`, i.e. `(LM)* = shiftBy d (M*) · L*` (`adjoint_mul`), adjoints taken with
  respect to the orders `d + e`, `e`, `d`;
* hence left factors of `L` of order one correspond to right factors of `L*` of order one
  (`adjoint_right_factor_of_left_factor`, `left_factor_of_adjoint_right_factor`).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

namespace RecOp

/-- Every operator is the sum of its terms `p_k(n) N^k`. -/
theorem coeff_finset_sum {ι : Type*} (t : Finset ι) (f : ι → RecOp K) (m : ℕ) :
    (∑ i ∈ t, f i).coeff m = ∑ i ∈ t, (f i).coeff m := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SkewPolynomial.coeff_add, ih]

theorem eq_sum_terms (L : RecOp K) : L = ∑ k ∈ L.support, term k (L.coeff k) :=
  (SkewPolynomial.sum_monomial L).symm.trans (SkewPolynomial.sum_def L _)

/-- The shift of the coefficients by `s`: `∑ p_k(n) N^k ↦ ∑ p_k(n+s) N^k`.  For `s = d` a natural
number this is the conjugation `A ↦ N^d A N^{-d}` of the book (`N_pow_mul_eq_shiftBy`). -/
def shiftBy (s : K) (L : RecOp K) : RecOp K := L.sum fun k p => term k (p.comp (X + C s))

theorem shiftBy_term (s : K) (k : ℕ) (p : K[X]) :
    shiftBy s (term k p) = term k (p.comp (X + C s)) := by
  unfold shiftBy term
  rw [SkewPolynomial.sum_monomial_index (by simp)]

theorem shiftBy_add (s : K) (L M : RecOp K) : shiftBy s (L + M) = shiftBy s L + shiftBy s M := by
  simp only [shiftBy, SkewPolynomial.sum_def']
  rw [SkewMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (by simp) (fun a b₁ b₂ => by
    simp only [add_comp]; exact map_add (SkewPolynomial.monomial _) _ _)

theorem shiftBy_zero (s : K) : shiftBy s (0 : RecOp K) = 0 := by
  simp [shiftBy, SkewPolynomial.sum_def']

theorem shiftBy_sum {ι : Type*} (s : K) (t : Finset ι) (f : ι → RecOp K) :
    shiftBy s (∑ i ∈ t, f i) = ∑ i ∈ t, shiftBy s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [shiftBy_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, shiftBy_add, ih]

theorem shiftBy_term_mul_term (s : K) (r q : ℕ) (a b : K[X]) :
    shiftBy s (term r a * term q b) = shiftBy s (term r a) * shiftBy s (term q b) := by
  rw [term_mul_term, shiftBy_term, shiftBy_term, shiftBy_term, term_mul_term, mul_comp,
    comp_shift_comp_shift, comp_shift_comp_shift, add_comm (r : K) s]

/-- The coefficient shift is multiplicative. -/
theorem shiftBy_mul (s : K) (L M : RecOp K) : shiftBy s (L * M) = shiftBy s L * shiftBy s M := by
  conv_lhs => rw [eq_sum_terms L, eq_sum_terms M]
  conv_rhs => rw [eq_sum_terms L, eq_sum_terms M]
  simp only [Finset.sum_mul_sum, shiftBy_sum, shiftBy_term_mul_term]

theorem shiftBy_one (s : K) : shiftBy s (1 : RecOp K) = 1 := by
  have : (1 : RecOp K) = term 0 1 := rfl
  rw [this, shiftBy_term, one_comp]

theorem shiftBy_shiftBy (s t : K) (L : RecOp K) : shiftBy t (shiftBy s L) = shiftBy (s + t) L := by
  conv_lhs => rw [eq_sum_terms L]
  conv_rhs => rw [eq_sum_terms L]
  rw [shiftBy_sum, shiftBy_sum, shiftBy_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shiftBy_term, shiftBy_term, shiftBy_term, comp_shift_comp_shift]

theorem shiftBy_zero_shift (L : RecOp K) : shiftBy 0 L = L := by
  conv_rhs => rw [eq_sum_terms L]
  conv_lhs => rw [eq_sum_terms L]
  rw [shiftBy_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shiftBy_term, C_0, add_zero, comp_X]

/-- CO-511. Conjugation by `N^d` shifts the coefficients: `N^d A = (shiftBy d A) N^d`, i.e.
`shiftBy d A = N^d A N^{-d}`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 173"]
theorem N_pow_mul_eq_shiftBy (d : ℕ) (A : RecOp K) : N ^ d * A = shiftBy (d : K) A * N ^ d := by
  rw [SkewPolynomial.X_pow_mul]
  congr 1
  unfold shiftBy
  congr 1
  funext k p
  rw [SkewPolynomial.φ_iterate_apply]
  rfl

/-- Right multiplication by `N^d` is injective. -/
theorem mul_N_pow_injective (d : ℕ) {P Q : RecOp K} (h : P * N ^ d = Q * N ^ d) : P = Q := by
  have key : ∀ R : RecOp K, ∀ n, (R * N ^ d).coeff (n + d) = R.coeff n := by
    intro R n
    rw [eq_sum_terms R, Finset.sum_mul]
    have e : ∀ k ∈ R.support, term k (R.coeff k) * N ^ d = term (k + d) (R.coeff k) := by
      intro k _
      exact SkewPolynomial.monomial_mul_X_pow k _ d
    rw [Finset.sum_congr rfl e]
    rw [coeff_finset_sum, coeff_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [term, SkewPolynomial.coeff_monomial]
    by_cases hk : k = n
    · simp [hk]
    · have : k + d ≠ n + d := by omega
      simp [hk]
  rw [SkewPolynomial.ext_iff]
  intro n
  rw [← key P n, ← key Q n, h]

/-! ### The adjoint -/

theorem adjoint_add (d : ℕ) (L M : RecOp K) : adjoint d (L + M) = adjoint d L + adjoint d M := by
  unfold adjoint
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [SkewPolynomial.coeff_add, add_comp]
  exact map_add (SkewPolynomial.monomial _) _ _

theorem adjoint_zero (d : ℕ) : adjoint d (0 : RecOp K) = 0 := by
  unfold adjoint
  refine Finset.sum_eq_zero fun k _ => ?_
  have : (0 : RecOp K).coeff (d - k) = 0 := by
    rw [← SkewPolynomial.notMem_support_iff]; simp
  rw [this, zero_comp]
  exact map_zero (SkewPolynomial.monomial _)

theorem adjoint_sum {ι : Type*} (d : ℕ) (t : Finset ι) (f : ι → RecOp K) :
    adjoint d (∑ i ∈ t, f i) = ∑ i ∈ t, adjoint d (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [adjoint_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adjoint_add, ih]

theorem adjoint_term (D m : ℕ) (c : K[X]) (hm : m ≤ D) :
    adjoint D (term m c) = term (D - m) (c.comp (X + C ((D - m : ℕ) : K))) := by
  unfold adjoint
  rw [Finset.sum_eq_single (D - m)]
  · rw [Nat.sub_sub_self hm]
    simp [term, SkewPolynomial.coeff_monomial]
  · intro k hk hne
    have hk' : k ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have : m ≠ D - k := by omega
    simp [term, SkewPolynomial.coeff_monomial, this]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- The adjoint of an operator of order at most `d` has order at most `d`. -/
theorem support_adjoint_le (d : ℕ) (L : RecOp K) : ∀ k ∈ (adjoint d L).support, k ≤ d := by
  intro k hk
  rw [adjoint_eq_ofCoeffs, SkewPolynomial.mem_support_iff, coeff_ofCoeffs] at hk
  by_contra h
  simp [h] at hk

theorem support_mul_le (d e : ℕ) (L M : RecOp K) (hL : ∀ k ∈ L.support, k ≤ d)
    (hM : ∀ k ∈ M.support, k ≤ e) : ∀ k ∈ (L * M).support, k ≤ d + e := by
  intro k hk
  by_contra hlt
  apply SkewPolynomial.mem_support_iff.1 hk
  rw [eq_sum_terms L, eq_sum_terms M, Finset.sum_mul_sum]
  rw [coeff_finset_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [coeff_finset_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [term_mul_term]
  have : i + j ≠ k := by have := hL i hi; have := hM j hj; omega
  simp [term, SkewPolynomial.coeff_monomial, this]

/-- CO-511. The adjoint reverses products: `(LM)* = (N^d M* N^{-d}) L*`, here
`(LM)* = shiftBy d (M*) · L*`, for `L` of order at most `d` and `M` of order at most `e` (adjoints
with respect to `d + e`, `e` and `d`). -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 173"]
theorem adjoint_mul (d e : ℕ) (L M : RecOp K) (hL : ∀ k ∈ L.support, k ≤ d)
    (hM : ∀ k ∈ M.support, k ≤ e) :
    adjoint (d + e) (L * M) = shiftBy (d : K) (adjoint e M) * adjoint d L := by
  rw [eq_ofCoeffs_of_support d L hL, eq_ofCoeffs_of_support e M hM]
  unfold ofCoeffs
  simp only [Finset.sum_mul_sum, adjoint_sum, shiftBy_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [term_mul_term, adjoint_term _ _ _ (by omega), adjoint_term _ _ _ hj', adjoint_term _ _ _ hi',
    shiftBy_term, term_mul_term]
  obtain ⟨i', rfl⟩ : ∃ i', d = i + i' := ⟨d - i, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', e = j + j' := ⟨e - j, by omega⟩
  have e1 : i + i' + (j + j') - (i + j) = j' + i' := by omega
  have e2 : j + j' - j = j' := by omega
  have e3 : i + i' - i = i' := by omega
  rw [e1, e2, e3, mul_comp, mul_comm, comp_shift_comp_shift, comp_shift_comp_shift,
    comp_shift_comp_shift]
  congr 3 <;> push_cast <;> ring_nf

/-- CO-511. `L** = N^d L N^{-d}`: the second adjoint is the coefficient shift by `d`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 173"]
theorem adjoint_adjoint (d : ℕ) (L : RecOp K) (hL : ∀ k ∈ L.support, k ≤ d) :
    adjoint d (adjoint d L) = shiftBy (d : K) L := by
  apply mul_N_pow_injective d
  rw [adjoint_adjoint_mul d L hL, N_pow_mul_eq_shiftBy]

/-- CO-511. A left factor of order one of `L` gives a right factor of order one of `L*`:
if `L = F M` with `F` of order at most `1` and `M` of order at most `d`, then
`L* = shiftBy 1 (M*) · F*` (adjoint of `L` with respect to `1 + d`), and `F*` has order at most `1`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 173-174"]
theorem adjoint_right_factor_of_left_factor (d : ℕ) (F M : RecOp K)
    (hF : ∀ k ∈ F.support, k ≤ 1) (hM : ∀ k ∈ M.support, k ≤ d) :
    adjoint (1 + d) (F * M) = shiftBy 1 (adjoint d M) * adjoint 1 F ∧
      ∀ k ∈ (adjoint 1 F).support, k ≤ 1 := by
  refine ⟨?_, support_adjoint_le 1 F⟩
  have := adjoint_mul 1 d F M hF hM
  simpa using this

/-- CO-511. Conversely, a right factor of order one of `L*` gives a left factor of order one of
`L`: if `L` has order at most `1 + d` and `L* = A G` with `A` of order at most `d` and `G` of order
at most `1`, then `L = G' A'` with `G' = shiftBy (-1) (G*)` of order at most `1` and
`A' = shiftBy (-(1+d)) (A*)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 173-174"]
theorem left_factor_of_adjoint_right_factor (d : ℕ) (L A G : RecOp K)
    (hL : ∀ k ∈ L.support, k ≤ 1 + d) (hA : ∀ k ∈ A.support, k ≤ d)
    (hG : ∀ k ∈ G.support, k ≤ 1) (h : adjoint (1 + d) L = A * G) :
    L = shiftBy (-1) (adjoint 1 G) * shiftBy (-((1 + d : ℕ) : K)) (adjoint d A) ∧
      ∀ k ∈ (shiftBy (-1) (adjoint 1 G)).support, k ≤ 1 := by
  have h2 : adjoint (1 + d) (A * G) = shiftBy ((d : ℕ) : K) (adjoint 1 G) * adjoint d A := by
    have := adjoint_mul d 1 A G hA hG
    rwa [add_comm d 1] at this
  have h3 := adjoint_adjoint (1 + d) L hL
  rw [h, h2] at h3
  refine ⟨?_, ?_⟩
  · have h4 := congrArg (shiftBy (-((1 + d : ℕ) : K))) h3
    rw [shiftBy_shiftBy, add_neg_cancel, shiftBy_zero_shift, shiftBy_mul, shiftBy_shiftBy] at h4
    rw [← h4]
    congr 2
    push_cast; ring
  · intro k hk
    rw [SkewPolynomial.mem_support_iff] at hk
    by_contra hk1
    apply hk
    rw [eq_sum_terms (adjoint 1 G), shiftBy_sum]
    rw [coeff_finset_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have := support_adjoint_le 1 G j hj
    have hne : j ≠ k := by omega
    simp [shiftBy_term, term, SkewPolynomial.coeff_monomial, hne]

end RecOp

end UndergradKB.Combinatorics.AeqB

end
