import UndergradKB.Combinatorics.AeqB.HypergeometricSeries
import UndergradKB.Common.Attr

/-!
# The hypergeometric series lookup algorithm (Petkovsek-Wilf-Zeilberger, Section 3.3)

CO-355. A sequence with `t 0 = 1` whose term ratio is a quotient of products of linear factors
is the term sequence of the corresponding `pFq`.  We prove the correctness of steps 1, 3 and 4 of
the algorithm (shift/normalize, factor and read off the parameters).
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Finset Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- CO-355 (step 4). If `t 0 = 1` and the term ratio is
`t (k+1) / t k = x (k+a₁)⋯(k+a_p) / ((k+b₁)⋯(k+b_q)(k+1))` (stated multiplicatively), with no
lower parameter a nonpositive integer, then `t` is the term sequence of `pFq[a; b; x]`. -/
@[kb "petkovsekwilfzeilberger1996" "text lookup algorithm, p. 47"]
theorem eq_pFqTerm_of_term_ratio {p q : ℕ} (a : Fin p → K) {b : Fin q → K} (hb : LowerOK b)
    (x : K) (t : ℕ → K) (h0 : t 0 = 1)
    (h : ∀ k : ℕ, t (k + 1) * ((∏ j, ((k : K) + b j)) * ((k : K) + 1)) =
      t k * ((∏ i, ((k : K) + a i)) * x)) :
    ∀ k, t k = pFqTerm a b x k := by
  intro k
  induction k with
  | zero => rw [h0, pFqTerm_zero]
  | succ k ih =>
    have hD : (∏ j, ((k : K) + b j)) * ((k : K) + 1) ≠ 0 :=
      mul_ne_zero (hb.prod_add_ne_zero k) (by exact_mod_cast k.succ_ne_zero)
    apply mul_right_cancel₀ hD
    rw [h k, pFqTerm_succ_mul a hb x k, ih]

/-- CO-355 (steps 2-4, polynomial form). If `t 0 = 1` and `Q(k) t(k+1) = P(k) t(k)` with
`P = c_P ∏ (X + a_i)` and `Q = c_Q ∏ (X + b_j) · (X + 1)` (`c_Q ≠ 0`, `Q` nonvanishing on `ℕ`
for lower parameters not nonpositive integers), then `t` is the term sequence of
`pFq[a; b; c_P / c_Q]`: the numerical factors are absorbed into `x`. -/
@[kb "petkovsekwilfzeilberger1996" "text lookup algorithm, p. 47"]
theorem eq_pFqTerm_of_factored_ratio {p q : ℕ} (a : Fin p → K) {b : Fin q → K} (hb : LowerOK b)
    (cP cQ : K) (hcQ : cQ ≠ 0) (t : ℕ → K) (h0 : t 0 = 1)
    (h : ∀ k : ℕ,
      (C cQ * (∏ j, (X + C (b j))) * (X + 1)).eval (k : K) * t (k + 1) =
        (C cP * ∏ i, (X + C (a i))).eval (k : K) * t k) :
    ∀ k, t k = pFqTerm a b (cP / cQ) k := by
  refine eq_pFqTerm_of_term_ratio a hb (cP / cQ) t h0 fun k => ?_
  have := h k
  simp only [eval_mul, eval_prod, eval_add, eval_X, eval_C, eval_one] at this
  field_simp
  linear_combination this

/-- CO-355 (step 3, inserting the factor `k+1`). If `Q` has no factor `k + 1`, the ratio
`P(k)/Q(k)` is rewritten as `P(k)(k+1) / (Q(k)(k+1))`, i.e. the upper parameter list is
extended by the parameter `1`. -/
@[kb "petkovsekwilfzeilberger1996" "text lookup algorithm, p. 47"]
theorem eq_pFqTerm_of_factored_ratio_insert {p q : ℕ} (a : Fin p → K) {b : Fin q → K}
    (hb : LowerOK b) (cP cQ : K) (hcQ : cQ ≠ 0) (t : ℕ → K) (h0 : t 0 = 1)
    (h : ∀ k : ℕ,
      (C cQ * (∏ j, (X + C (b j)))).eval (k : K) * t (k + 1) =
        (C cP * ∏ i, (X + C (a i))).eval (k : K) * t k) :
    ∀ k, t k = pFqTerm (Fin.cons (1 : K) a : Fin (p + 1) → K) b (cP / cQ) k := by
  refine eq_pFqTerm_of_term_ratio _ hb (cP / cQ) t h0 fun k => ?_
  have := h k
  simp only [eval_mul, eval_prod, eval_add, eval_X, eval_C] at this
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  field_simp
  linear_combination this

/-- CO-355 (step 1, shift and normalize). If the ratio relation `q k * t (k+1) = p k * t k`
holds for `k ≥ m` and `t m ≠ 0`, then `s k = t (m+k) / t m` starts with `1` and satisfies the
shifted ratio relation. -/
@[kb "petkovsekwilfzeilberger1996" "text lookup algorithm, p. 47"]
theorem lookup_shift_normalize (t : ℕ → K) (m : ℕ) (hm : t m ≠ 0) (P Q : ℕ → K)
    (h : ∀ k, m ≤ k → Q k * t (k + 1) = P k * t k) :
    (fun k => t (m + k) / t m) 0 = 1 ∧
      ∀ k, Q (m + k) * (t (m + (k + 1)) / t m) = P (m + k) * (t (m + k) / t m) := by
  refine ⟨by simp [div_self hm], fun k => ?_⟩
  have := h (m + k) (Nat.le_add_right _ _)
  rw [← add_assoc]
  field_simp
  exact this

end UndergradKB.Combinatorics.AeqB
