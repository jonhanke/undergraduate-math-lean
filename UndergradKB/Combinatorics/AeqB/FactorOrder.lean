import UndergradKB.Combinatorics.AeqB.Adjoint

/-!
# Factoring recurrence operators of order two and three (Petkovsek–Wilf–Zeilberger, "A = B", §8.10)

The order of a recurrence operator is the largest power of the shift appearing in it.  We prove
that the order is additive under multiplication (the product of the leading coefficients is
nonzero, since polynomials form a domain), and use this to show:

* an operator of order two is a product of two operators of positive order exactly when it has a
  right factor of order one;
* an operator of order three (whose lowest coefficient is nonzero, so that its adjoint again has
  order three) is a product of two operators of positive order exactly when it, or its adjoint,
  has a right factor of order one.

A right factor of order one `q(n) N - p(n)` of an operator yields a hypergeometric solution (when
one exists with ratio `p/q`).  So factoring operators of order two and three reduces to finding
hypergeometric solutions of the operator and of its adjoint.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

namespace RecOp

/-! ### Orders and leading coefficients -/

/-- The order of a recurrence operator: the largest power of the shift occurring in it (`0` for
the zero operator). -/
def recOrder (L : RecOp K) : ℕ := L.support.sup id

theorem coeff_le_recOrder (L : RecOp K) {k : ℕ} (hk : L.coeff k ≠ 0) : k ≤ recOrder L :=
  Finset.le_sup (f := id) (SkewPolynomial.mem_support_iff.2 hk)

theorem recOrder_le_of_support {L : RecOp K} {d : ℕ} (h : ∀ k ∈ L.support, k ≤ d) :
    recOrder L ≤ d :=
  Finset.sup_le h

theorem recOrder_eq_of {L : RecOp K} {d : ℕ} (h : ∀ k ∈ L.support, k ≤ d) (hd : L.coeff d ≠ 0) :
    recOrder L = d :=
  le_antisymm (recOrder_le_of_support h) (coeff_le_recOrder L hd)

theorem recOrder_zero : recOrder (0 : RecOp K) = 0 := by simp [recOrder]

theorem ne_zero_of_one_le_recOrder {L : RecOp K} (h : 1 ≤ recOrder L) : L ≠ 0 := by
  rintro rfl
  rw [recOrder_zero] at h
  omega

theorem support_le_recOrder (L : RecOp K) : ∀ k ∈ L.support, k ≤ recOrder L :=
  fun _ hk => Finset.le_sup (f := id) hk

theorem coeff_recOrder_ne_zero {L : RecOp K} (hL : L ≠ 0) : L.coeff (recOrder L) ≠ 0 := by
  have hne : L.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hL (SkewPolynomial.support_eq_empty.1 he)
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup L.support hne id
  have : recOrder L = j := hjeq
  rw [this]
  exact SkewPolynomial.mem_support_iff.1 hj

theorem coeff_zero_op : (0 : RecOp K).coeff 0 = 0 := by
  rw [← SkewPolynomial.notMem_support_iff]; simp

theorem coeff_ofCoeffs_mul_top (d e : ℕ) (c c' : ℕ → K[X]) :
    (ofCoeffs d c * ofCoeffs e c').coeff (d + e) = c d * (c' e).comp (X + C (d : K)) := by
  unfold ofCoeffs
  rw [Finset.sum_mul_sum, coeff_finset_sum, Finset.sum_eq_single d]
  · rw [coeff_finset_sum, Finset.sum_eq_single e]
    · rw [term_mul_term]; simp [term, SkewPolynomial.coeff_monomial]
    · intro j hj hne
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [term_mul_term]
      have : d + j ≠ d + e := by omega
      simp only [term, SkewPolynomial.coeff_monomial]
      rw [if_neg this]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · intro i hi hne
    have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [coeff_finset_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [term_mul_term]
    have : i + j ≠ d + e := by omega
    simp only [term, SkewPolynomial.coeff_monomial]
    rw [if_neg this]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- The coefficient of the top power in a product of operators of orders at most `d` and `e`. -/
theorem coeff_mul_top (d e : ℕ) (L M : RecOp K) (hL : ∀ k ∈ L.support, k ≤ d)
    (hM : ∀ k ∈ M.support, k ≤ e) :
    (L * M).coeff (d + e) = L.coeff d * (M.coeff e).comp (X + C (d : K)) := by
  have := coeff_ofCoeffs_mul_top d e L.coeff M.coeff
  rwa [← eq_ofCoeffs_of_support d L hL, ← eq_ofCoeffs_of_support e M hM] at this

theorem coeff_ofCoeffs_mul_zero (d e : ℕ) (c c' : ℕ → K[X]) :
    (ofCoeffs d c * ofCoeffs e c').coeff 0 = c 0 * c' 0 := by
  unfold ofCoeffs
  rw [Finset.sum_mul_sum, coeff_finset_sum, Finset.sum_eq_single 0]
  · rw [coeff_finset_sum, Finset.sum_eq_single 0]
    · rw [term_mul_term]; simp [term, SkewPolynomial.coeff_monomial]
    · intro j hj hne
      rw [term_mul_term]
      have : 0 + j ≠ 0 := by omega
      simp only [term, SkewPolynomial.coeff_monomial]
      rw [if_neg this]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · intro i hi hne
    rw [coeff_finset_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [term_mul_term]
    have : i + j ≠ 0 := by omega
    simp only [term, SkewPolynomial.coeff_monomial]
    rw [if_neg this]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- The lowest coefficient of a product is the product of the lowest coefficients. -/
theorem coeff_mul_zero (L M : RecOp K) : (L * M).coeff 0 = L.coeff 0 * M.coeff 0 := by
  have := coeff_ofCoeffs_mul_zero (recOrder L) (recOrder M) L.coeff M.coeff
  rwa [← eq_ofCoeffs_of_support _ L (support_le_recOrder L),
    ← eq_ofCoeffs_of_support _ M (support_le_recOrder M)] at this

/-- The leading coefficient of a product (orders add, nothing cancels in a domain). -/
theorem recOrder_mul {L M : RecOp K} (hL : L ≠ 0) (hM : M ≠ 0) :
    recOrder (L * M) = recOrder L + recOrder M ∧ L * M ≠ 0 := by
  have hc : (L * M).coeff (recOrder L + recOrder M) ≠ 0 := by
    rw [coeff_mul_top _ _ L M (support_le_recOrder L) (support_le_recOrder M)]
    exact mul_ne_zero (coeff_recOrder_ne_zero hL)
      (comp_X_add_C_ne_zero_iff.2 (coeff_recOrder_ne_zero hM))
  refine ⟨recOrder_eq_of (support_mul_le _ _ L M (support_le_recOrder L)
    (support_le_recOrder M)) hc, ?_⟩
  intro h0
  apply hc
  rw [h0]
  rw [← SkewPolynomial.notMem_support_iff]; simp

theorem shiftBy_coeff (s : K) (L : RecOp K) (k : ℕ) :
    (shiftBy s L).coeff k = (L.coeff k).comp (X + C s) := by
  conv_lhs => rw [eq_sum_terms L]
  rw [shiftBy_sum, coeff_finset_sum, Finset.sum_eq_single k]
  · rw [shiftBy_term]; simp [term, SkewPolynomial.coeff_monomial]
  · intro j hj hne
    rw [shiftBy_term]; simp [term, SkewPolynomial.coeff_monomial, hne]
  · intro hk
    rw [SkewPolynomial.notMem_support_iff.1 hk, shiftBy_term]
    simp [term, SkewPolynomial.coeff_monomial]

theorem adjoint_one_coeff_one (G : RecOp K) :
    (adjoint 1 G).coeff 1 = (G.coeff 0).comp (X + C ((1 : ℕ) : K)) := by
  rw [adjoint_eq_ofCoeffs, coeff_ofCoeffs]; simp

theorem adjoint_coeff_zero (d : ℕ) (L : RecOp K) :
    (adjoint d L).coeff 0 = (L.coeff d).comp X := by
  rw [adjoint_eq_ofCoeffs, coeff_ofCoeffs]; simp

/-- An operator of order exactly one is `q(n) N + r(n)` with `q ≠ 0`. -/
theorem order_one_form {G : RecOp K} (hG : recOrder G = 1) :
    G = firstOrder (G.coeff 1) (G.coeff 0) ∧ G.coeff 1 ≠ 0 := by
  have hs : ∀ k ∈ G.support, k ≤ 1 := fun k hk => hG ▸ support_le_recOrder G k hk
  refine ⟨?_, ?_⟩
  · rw [firstOrder, add_comm]
    conv_lhs => rw [eq_ofCoeffs_of_support 1 G hs]
    simp [ofCoeffs, Finset.sum_range_succ]
  · have := coeff_recOrder_ne_zero (ne_zero_of_one_le_recOrder (show 1 ≤ recOrder G by omega))
    rwa [hG] at this

/-- `L` is a product of two operators of positive order. -/
def IsReducible (L : RecOp K) : Prop :=
  ∃ A B : RecOp K, L = A * B ∧ 1 ≤ recOrder A ∧ 1 ≤ recOrder B

/-- `L` has a right factor of order exactly one. -/
def HasRightFactorOne (L : RecOp K) : Prop :=
  ∃ A G : RecOp K, recOrder G = 1 ∧ L = A * G

/-- A right factor `q(n) N - p(n)` of `L`, with `q ≠ 0`, such that every hypergeometric term with
ratio `p/q` is a solution of `L`. -/
def HyperRightFactor (L : RecOp K) : Prop :=
  ∃ (A : RecOp K) (p q : K[X]), q ≠ 0 ∧ L = A * firstOrder q (-p) ∧
    ∀ y : ℕ → K, IsHypergeometric y →
      (∀ᶠ n : ℕ in atTop, y (n + 1) / y n = p.eval (n : K) / q.eval (n : K)) →
      IsHypergeometric y ∧ ∀ᶠ n : ℕ in atTop, act L y n = 0

theorem HasRightFactorOne.hyper {L : RecOp K} (h : HasRightFactorOne L) : HyperRightFactor L := by
  obtain ⟨A, G, hG, hL⟩ := h
  obtain ⟨hform, hq⟩ := order_one_form hG
  have hL' : L = A * firstOrder (G.coeff 1) (-(-G.coeff 0)) := by
    rw [neg_neg, ← hform]; exact hL
  exact ⟨A, -G.coeff 0, G.coeff 1, hq, hL', fun y hy hr =>
    hyper_solution_of_right_factor L A _ _ hL' y hy hr hq⟩

/-! ### Operators of order two -/

/-- CO-511. An operator of order two is a product of two operators of positive order exactly when
it has a right factor of order one (for a product `A B` of positive orders `a + b = 2`, so
`b = 1`). -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 174"]
theorem reducible_iff_order_two (L : RecOp K) (hL : recOrder L = 2) :
    IsReducible L ↔ HasRightFactorOne L := by
  constructor
  · rintro ⟨A, B, h, hA, hB⟩
    have hA0 := ne_zero_of_one_le_recOrder hA
    have hB0 := ne_zero_of_one_le_recOrder hB
    have := (recOrder_mul hA0 hB0).1
    rw [← h] at this
    exact ⟨A, B, by omega, h⟩
  · rintro ⟨A, G, hG, h⟩
    have hL0 : L ≠ 0 := ne_zero_of_one_le_recOrder (by omega)
    have hA0 : A ≠ 0 := fun h0 => hL0 (by rw [h, h0, zero_mul])
    have hG0 : G ≠ 0 := ne_zero_of_one_le_recOrder (by omega)
    have := (recOrder_mul hA0 hG0).1
    rw [← h] at this
    exact ⟨A, G, h, by omega, by omega⟩

/-! ### Operators of order three -/

theorem hasRightFactorOne_adjoint_of_left (L A B : RecOp K) (h : L = A * B)
    (hA : recOrder A = 1) (hB : recOrder B = 2) (h0 : L.coeff 0 ≠ 0) :
    HasRightFactorOne (adjoint 3 L) := by
  subst h
  have hA0 : A.coeff 0 ≠ 0 := by
    rw [coeff_mul_zero] at h0
    exact left_ne_zero_of_mul h0
  have hAs : ∀ k ∈ A.support, k ≤ 1 := fun k hk => hA ▸ support_le_recOrder A k hk
  have hBs : ∀ k ∈ B.support, k ≤ 2 := fun k hk => hB ▸ support_le_recOrder B k hk
  obtain ⟨h1, h2⟩ := adjoint_right_factor_of_left_factor 2 A B hAs hBs
  have hG : recOrder (adjoint 1 A) = 1 := by
    refine recOrder_eq_of h2 ?_
    rw [adjoint_one_coeff_one]
    exact comp_X_add_C_ne_zero_iff.2 hA0
  exact ⟨_, adjoint 1 A, hG, h1⟩

theorem isReducible_of_adjoint (L : RecOp K) (hL : recOrder L = 3) (h : HasRightFactorOne (adjoint 3 L)) :
    IsReducible L := by
  obtain ⟨A, G, hG, h⟩ := h
  have hL0 : L ≠ 0 := ne_zero_of_one_le_recOrder (by omega)
  have hL3 : L.coeff 3 ≠ 0 := by
    have := coeff_recOrder_ne_zero hL0
    rwa [hL] at this
  have hadj0 : (adjoint 3 L).coeff 0 ≠ 0 := by
    rw [adjoint_coeff_zero]
    simpa using hL3
  rw [h, coeff_mul_zero] at hadj0
  have hA0' : A.coeff 0 ≠ 0 := left_ne_zero_of_mul hadj0
  have hG0' : G.coeff 0 ≠ 0 := right_ne_zero_of_mul hadj0
  have hA0 : A ≠ 0 := fun h0 => hA0' (by rw [h0]; exact coeff_zero_op)
  have hG1 : 1 ≤ recOrder G := by omega
  have hG0 : G ≠ 0 := ne_zero_of_one_le_recOrder hG1
  have hord := (recOrder_mul hA0 hG0).1
  rw [← h] at hord
  have hle : recOrder (adjoint 3 L) ≤ 3 := recOrder_le_of_support (support_adjoint_le 3 L)
  have hAs : ∀ k ∈ A.support, k ≤ 2 := fun k hk =>
    le_trans (support_le_recOrder A k hk) (by omega)
  have hGs : ∀ k ∈ G.support, k ≤ 1 := fun k hk => hG ▸ support_le_recOrder G k hk
  have hLs : ∀ k ∈ L.support, k ≤ 1 + 2 := fun k hk => by
    have := support_le_recOrder L k hk
    omega
  obtain ⟨hfac, hsupp⟩ := left_factor_of_adjoint_right_factor 2 L A G hLs hAs hGs h
  set G' := shiftBy (-1) (adjoint 1 G) with hG'
  set A' := shiftBy (-((1 + 2 : ℕ) : K)) (adjoint 2 A) with hA'
  have hG'1 : recOrder G' = 1 := by
    refine recOrder_eq_of hsupp ?_
    rw [hG', shiftBy_coeff, adjoint_one_coeff_one]
    exact comp_X_add_C_ne_zero_iff.2 (comp_X_add_C_ne_zero_iff.2 hG0')
  have hG'0 : G' ≠ 0 := ne_zero_of_one_le_recOrder (by omega)
  have hA'0 : A' ≠ 0 := fun h0 => hL0 (by rw [hfac, h0, mul_zero])
  have hord2 := (recOrder_mul hG'0 hA'0).1
  rw [← hfac] at hord2
  exact ⟨G', A', hfac, by omega, by omega⟩

/-- CO-511. An operator `L` of order three whose lowest coefficient is nonzero (so the adjoint
`L*`, taken with respect to order three, again has order three) is a product of two operators of
positive order exactly when `L` or `L*` has a right factor of order one.  The factorization
`L = A B` has orders `(2,1)` or `(1,2)`; in the first case `B` is a right factor of order one, in
the second the adjoint of the left factor `A` is one for `L*`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 174"]
theorem reducible_iff_order_three (L : RecOp K) (hL : recOrder L = 3) (h0 : L.coeff 0 ≠ 0) :
    IsReducible L ↔ HasRightFactorOne L ∨ HasRightFactorOne (adjoint 3 L) := by
  constructor
  · rintro ⟨A, B, h, hA, hB⟩
    have hA0 := ne_zero_of_one_le_recOrder hA
    have hB0 := ne_zero_of_one_le_recOrder hB
    have := (recOrder_mul hA0 hB0).1
    rw [← h] at this
    by_cases hB1 : recOrder B = 1
    · exact Or.inl ⟨A, B, hB1, h⟩
    · exact Or.inr (hasRightFactorOne_adjoint_of_left L A B h (by omega) (by omega) h0)
  · rintro (⟨A, G, hG, h⟩ | h)
    · have hL0 : L ≠ 0 := ne_zero_of_one_le_recOrder (by omega)
      have hA0 : A ≠ 0 := fun h0 => hL0 (by rw [h, h0, zero_mul])
      have hG0 : G ≠ 0 := ne_zero_of_one_le_recOrder (by omega)
      have := (recOrder_mul hA0 hG0).1
      rw [← h] at this
      exact ⟨A, G, h, by omega, by omega⟩
    · exact isReducible_of_adjoint L hL h

/-- CO-511. Factoring operators of order two and three reduces to hypergeometric solutions:
for a reducible operator of order two, `L` has a right factor `q N - p` (`q ≠ 0`) and every
hypergeometric term of ratio `p/q` solves `L`; for a reducible operator of order three with
nonzero lowest coefficient, this holds for `L` or for its adjoint `L*`.  Conversely
(`reducible_iff_order_two`, `reducible_iff_order_three`) such a right factor of order one gives
the factorization, so one only needs to search for hypergeometric solutions of `L` and of `L*`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 174"]
theorem hyper_right_factor_of_reducible (L : RecOp K) :
    (recOrder L = 2 → IsReducible L → HyperRightFactor L) ∧
    (recOrder L = 3 → L.coeff 0 ≠ 0 → IsReducible L →
      HyperRightFactor L ∨ HyperRightFactor (adjoint 3 L)) := by
  refine ⟨fun h2 hr => ((reducible_iff_order_two L h2).1 hr).hyper, fun h3 h0 hr => ?_⟩
  rcases (reducible_iff_order_three L h3 h0).1 hr with h | h
  · exact Or.inl h.hyper
  · exact Or.inr h.hyper

end RecOp

end UndergradKB.Combinatorics.AeqB

end
