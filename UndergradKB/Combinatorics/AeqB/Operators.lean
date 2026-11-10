import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar

/-!
# Recurrence operators with polynomial coefficients (Petkovsek–Wilf–Zeilberger, "A = B", §8.7, 8.10, 9.2)

A linear recurrence operator `∑ p_k(n) N^k` with polynomial coefficients is an element of the
skew polynomial ring `K[n][N; σ]` of Mathlib (`SkewPolynomial`), where `σ` is the shift
`p(n) ↦ p(n+1)` of `K[n]`; multiplication is determined by `N p(n) = p(n+1) N`.  It acts on
sequences `ℕ → K` by `(p(n) N^k) y = p(n) y(n+k)`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K]

/-! ### The shift action on polynomials -/

/-- The additive monoid `ℕ` acts on `K[n]` by shifts: `k • p = p(n + k)`.  This is the structure
needed to form the skew polynomial ring of Mathlib so that `N p(n) = p(n+1) N`. -/
scoped instance shiftAction : MulSemiringAction (Multiplicative ℕ) K[X] where
  smul k p := p.comp (X + C ((Multiplicative.toAdd k : ℕ) : K))
  one_smul p := by simp [HSMul.hSMul, SMul.smul]
  mul_smul a b p := by
    show p.comp (X + C ((Multiplicative.toAdd (a * b) : ℕ) : K))
      = (p.comp (X + C ((Multiplicative.toAdd b : ℕ) : K))).comp (X + C ((Multiplicative.toAdd a : ℕ) : K))
    rw [comp_assoc]
    congr 1
    simp [add_comm, add_left_comm, add_assoc]
  smul_zero a := zero_comp
  smul_add a p q := add_comp
  smul_one a := one_comp
  smul_mul a p q := mul_comp _ _ _

theorem shiftAction_smul (k : ℕ) (p : K[X]) :
    (Multiplicative.ofAdd k : Multiplicative ℕ) • p = p.comp (X + C (k : K)) := rfl

/-- Recurrence operators with polynomial coefficients: `∑ p_k(n) N^k`, as skew polynomials over
`K[n]` for the shift `p(n) ↦ p(n+1)`. -/
abbrev RecOp (K : Type*) [Field K] := SkewPolynomial K[X]

namespace RecOp

/-- The shift operator `N`. -/
abbrev N : RecOp K := SkewPolynomial.X

/-- The operator `p(n) N^k`. -/
abbrev term (k : ℕ) (p : K[X]) : RecOp K := SkewPolynomial.monomial k p

/-- CO-505. The multiplication rule of recurrence operators:
`(a(n) N^r)(b(n) N^s) = a(n) b(n+r) N^{r+s}`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem term_mul_term (r s : ℕ) (a b : K[X]) :
    term r a * term s b = term (r + s) (a * b.comp (X + C (r : K))) := by
  unfold term
  rw [SkewPolynomial.monomial_mul_monomial, SkewPolynomial.φ_iterate_apply]
  rfl

/-- CO-505. The commutation rule `N p(n) = p(n+1) N` in the ring of recurrence operators. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem N_mul_C (p : K[X]) :
    N * SkewPolynomial.C p = SkewPolynomial.C (p.comp (X + 1)) * N := by
  have h1 : (N : RecOp K) = term 1 1 := rfl
  have h2 : (SkewPolynomial.C p : RecOp K) = term 0 p := rfl
  have h3 : (SkewPolynomial.C (p.comp (X + 1)) : RecOp K) = term 0 (p.comp (X + 1)) := rfl
  rw [h1, h2, h3, term_mul_term, term_mul_term]
  simp

/-! ### Action on sequences -/

/-- The action of a recurrence operator on a sequence: `(∑ p_k(n) N^k) y = (n ↦ ∑ p_k(n) y(n+k))`. -/
def act (L : RecOp K) (y : ℕ → K) : ℕ → K :=
  fun n => L.sum fun k p => p.eval (n : K) * y (n + k)

theorem act_def (L : RecOp K) (y : ℕ → K) (n : ℕ) :
    act L y n = ∑ k ∈ L.support, (L.coeff k).eval (n : K) * y (n + k) :=
  SkewPolynomial.sum_def _ _

theorem act_zero (y : ℕ → K) : act (0 : RecOp K) y = 0 := by
  funext n
  simp [act, SkewPolynomial.sum_def']

theorem act_term (k : ℕ) (p : K[X]) (y : ℕ → K) (n : ℕ) :
    act (term k p) y n = p.eval (n : K) * y (n + k) := by
  unfold act term
  rw [SkewPolynomial.sum_monomial_index (by simp)]

theorem act_add (L M : RecOp K) (y : ℕ → K) : act (L + M) y = act L y + act M y := by
  funext n
  simp only [act, SkewPolynomial.sum_def', Pi.add_apply]
  rw [show SkewMonoidAlgebra.coeff (L + M) = SkewMonoidAlgebra.coeff L + SkewMonoidAlgebra.coeff M
    from SkewMonoidAlgebra.coeff_add L M]
  exact Finsupp.sum_add_index' (by simp) (fun a b₁ b₂ => by simp [mul_add, add_mul])

theorem act_add_seq (L : RecOp K) (y z : ℕ → K) : act L (y + z) = act L y + act L z := by
  funext n
  simp [act_def, mul_add, Finset.sum_add_distrib]

theorem act_sum_seq {ι : Type*} (L : RecOp K) (s : Finset ι) (y : ι → ℕ → K) (n : ℕ) :
    act L (fun m => ∑ i ∈ s, y i m) n = ∑ i ∈ s, act L (y i) n := by
  simp only [act_def, Finset.mul_sum]
  exact Finset.sum_comm

theorem act_term_term (r s : ℕ) (a b : K[X]) (y : ℕ → K) :
    act (term r a * term s b) y = act (term r a) (act (term s b) y) := by
  funext n
  rw [term_mul_term, act_term, act_term, act_term]
  simp only [eval_mul, eval_comp, eval_add, eval_X, eval_C]
  rw [show n + (r + s) = n + r + s by ring]
  push_cast
  ring_nf

theorem act_term_mul (n : ℕ) (r : K[X]) (M : RecOp K) (y : ℕ → K) :
    act (term n r * M) y = act (term n r) (act M y) := by
  induction M using SkewPolynomial.induction with
  | h0 => funext x; simp [act_zero, act_term]
  | ha m s q' _ _ ih =>
    rw [mul_add, act_add, ih, act_term_term, act_add]
    funext x
    simp only [act_term, Pi.add_apply]
    ring

/-- CO-505. Operators act on sequences compatibly with the (noncommutative) ring structure:
`(L M) y = L (M y)`.  Together with `term_mul_term` this says that recurrence operators with
polynomial coefficients form a ring with `N p(n) = p(n+1) N` acting on sequences. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem act_mul (L M : RecOp K) (y : ℕ → K) : act (L * M) y = act L (act M y) := by
  induction L using SkewPolynomial.induction with
  | h0 => simp [act_zero]
  | ha n r q _ _ ih =>
    rw [add_mul, act_add, act_add, act_term_mul, ih]

/-- CO-505. In particular `N (p(n) y(n)) = p(n+1) (N y)(n)`: `N p(n) = p(n+1) N` on sequences. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem act_N_act_C (p : K[X]) (y : ℕ → K) (n : ℕ) :
    act N (act (SkewPolynomial.C p) y) n = act (SkewPolynomial.C (p.comp (X + 1))) (act N y) n := by
  have h1 : (N : RecOp K) = term 1 1 := rfl
  have h2 : (SkewPolynomial.C p : RecOp K) = term 0 p := rfl
  have h3 : (SkewPolynomial.C (p.comp (X + 1)) : RecOp K) = term 0 (p.comp (X + 1)) := rfl
  rw [h1, h2, h3]
  simp only [act_term, eval_one, one_mul, eval_comp, eval_add, eval_X, eval_C]
  push_cast
  ring_nf

/-! ### The adjoint (CO-510) -/

/-- CO-510. The adjoint of a recurrence operator `L = ∑_{k ≤ d} p_k(n) N^k` of order at most `d`
is `L* = ∑_{k ≤ d} p_{d-k}(n+k) N^k`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 173"]
def adjoint (d : ℕ) (L : RecOp K) : RecOp K :=
  ∑ k ∈ Finset.range (d + 1), term k ((L.coeff (d - k)).comp (X + C (k : K)))

end RecOp

/-! ### CO-513: P-recursive sequences -/

/-- CO-513. A sequence is P-recursive (holonomic) if it is annihilated by a nonzero linear
recurrence operator with polynomial coefficients: `∑ p_i(n) x(n+i) = 0` for all `n ≥ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 9.2.1, p. 184"]
def IsPRecursive (x : ℕ → K) : Prop := ∃ L : RecOp K, L ≠ 0 ∧ ∀ n : ℕ, RecOp.act L x n = 0

variable [CharZero K]

/-- CO-513 (closure fact). Every hypergeometric term is P-recursive (the recurrence, valid for
large `n`, is multiplied by `∏_{i<N} (n - i)` to make it valid for all `n`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition 9.2.1, p. 184"]
theorem IsHypergeometric.isPRecursive {t : ℕ → K} (ht : IsHypergeometric t) : IsPRecursive t := by
  obtain ⟨-, p, q, hp, hq, h⟩ := ht
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  set m : K[X] := ∏ i ∈ Finset.range N, (X - C (i : K)) with hm
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact Finset.prod_ne_zero_iff.2 fun i _ => X_sub_C_ne_zero _
  have hmN : ∀ n : ℕ, n < N → m.eval (n : K) = 0 := fun n hn => by
    rw [hm, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.2 hn) (by simp)
  refine ⟨RecOp.term 1 (m * p) + RecOp.term 0 (m * q), ?_, fun n => ?_⟩
  · intro h0
    have h1 : SkewPolynomial.monomial 1 (m * p) = SkewPolynomial.monomial 0 (-(m * q)) := by
      rw [map_neg]; exact eq_neg_of_add_eq_zero_left h0
    rcases SkewPolynomial.monomial_eq_monomial_iff.1 h1 with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact one_ne_zero h2
    · exact mul_ne_zero hm0 hp h2
  · rw [RecOp.act_add, Pi.add_apply, RecOp.act_term, RecOp.act_term]
    by_cases hn : n < N
    · simp [eval_mul, hmN n hn]
    · push Not at hn
      have := hN n hn
      simp only [eval_mul, add_zero]
      linear_combination m.eval (n : K) * this

namespace RecOp

/-! ### CO-498, CO-499 -/

/-- Rational multiples: `s = (p/q) t` for polynomials `p, q`, `q ≠ 0` (here `p` may vanish). -/
def IsRatMul (s t : ℕ → K) : Prop :=
  ∃ p q : K[X], q ≠ 0 ∧ ∀ᶠ n : ℕ in atTop, q.eval (n : K) * s n = p.eval (n : K) * t n

theorem IsRatMul.zero (t : ℕ → K) : IsRatMul (fun _ => 0) t :=
  ⟨0, 1, one_ne_zero, Eventually.of_forall fun n => by simp⟩

theorem IsRatMul.add {s₁ s₂ t : ℕ → K} (h₁ : IsRatMul s₁ t) (h₂ : IsRatMul s₂ t) :
    IsRatMul (fun n => s₁ n + s₂ n) t := by
  obtain ⟨p₁, q₁, hq₁, e₁⟩ := h₁
  obtain ⟨p₂, q₂, hq₂, e₂⟩ := h₂
  refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, mul_ne_zero hq₁ hq₂, ?_⟩
  filter_upwards [e₁, e₂] with n a b
  simp only [eval_mul, eval_add]
  linear_combination q₂.eval (n : K) * a + q₁.eval (n : K) * b

theorem IsRatMul.smul_poly {s t : ℕ → K} (c : K[X]) (h : IsRatMul s t) :
    IsRatMul (fun n => c.eval (n : K) * s n) t := by
  obtain ⟨p, q, hq, e⟩ := h
  refine ⟨c * p, q, hq, e.mono fun n a => ?_⟩
  simp only [eval_mul]
  linear_combination c.eval (n : K) * a

/-- A shift of a hypergeometric term is a rational multiple of it. -/
theorem isRatMul_shift {h : ℕ → K} (hh : IsHypergeometric h) (k : ℕ) :
    IsRatMul (fun n => h (n + k)) h := by
  obtain ⟨-, P, Q, hP, hQ, hPQ⟩ := isHypergeometric_iff.1 hh
  induction k with
  | zero => exact ⟨1, 1, one_ne_zero, Eventually.of_forall fun n => by simp⟩
  | succ k ih =>
    obtain ⟨p, q, hq, e⟩ := ih
    have hQk : Q.comp (X + C (k : K)) ≠ 0 := comp_X_add_C_ne_zero_iff.2 hQ
    refine ⟨P.comp (X + C (k : K)) * p, Q.comp (X + C (k : K)) * q, mul_ne_zero hQk hq, ?_⟩
    have e2 : ∀ᶠ n : ℕ in atTop, Q.eval ((n + k : ℕ) : K) * h (n + k + 1)
        = P.eval ((n + k : ℕ) : K) * h (n + k) := (tendsto_add_atTop_nat k).eventually hPQ
    filter_upwards [e, e2] with n a b
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_C]
    push_cast at b ⊢
    rw [show n + (k + 1) = n + k + 1 by ring]
    linear_combination q.eval (n : K) * b + P.eval ((n : K) + k) * a

theorem isRatMul_finset_sum {h : ℕ → K} (hh : IsHypergeometric h) (s : Finset ℕ) (c : ℕ → K[X]) :
    IsRatMul (fun n => ∑ k ∈ s, (c k).eval (n : K) * h (n + k)) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsRatMul.zero h
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (isRatMul_shift hh a).smul_poly (c a) |>.add ih

/-- `L h` is a rational multiple of the hypergeometric term `h`. -/
theorem isRatMul_act (L : RecOp K) {h : ℕ → K} (hh : IsHypergeometric h) :
    IsRatMul (act L h) h := by
  have : act L h = fun n : ℕ => ∑ k ∈ L.support, (L.coeff k).eval (n : K) * h (n + k) :=
    funext (act_def L h)
  rw [this]
  exact isRatMul_finset_sum hh _ _

/-- CO-498. Proposition 8.7.1: if `h` is a hypergeometric term and `L h ≠ 0`, then `L h` is a
hypergeometric term similar to `h` (a rational multiple of `h`). -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.7.1, p. 168"]
theorem isHypergeometric_act (L : RecOp K) {h : ℕ → K} (hh : IsHypergeometric h)
    (hL : ¬ ∀ᶠ n : ℕ in atTop, act L h n = 0) :
    IsHypergeometric (act L h) ∧ IsSimilar (act L h) h := by
  obtain ⟨p, q, hq, e⟩ := isRatMul_act L hh
  have hp : p ≠ 0 := by
    rintro rfl
    apply hL
    filter_upwards [e, eventually_eval_ne_zero hq] with n a b
    simp only [eval_zero, zero_mul] at a
    exact (mul_eq_zero.1 a).resolve_left b
  have hs : IsSimilar (act L h) h := ⟨p, q, hp, hq, e⟩
  exact ⟨hs.isHypergeometric hh, hs⟩

/-- CO-499. Theorem 8.7.1: if a linear recurrence operator `L` with polynomial coefficients
kills (almost everywhere) a sum `h = ∑ h_i` of pairwise dissimilar hypergeometric terms, then
`L` kills each `h_i`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.7.1, p. 169"]
theorem act_eq_zero_of_sum_dissimilar {ι : Type*} [DecidableEq ι] (L : RecOp K) (s : Finset ι)
    (h : ι → ℕ → K) (hh : ∀ i ∈ s, IsHypergeometric (h i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ IsSimilar (h i) (h j))
    (hL : ∀ᶠ n : ℕ in atTop, act L (fun m => ∑ i ∈ s, h i m) n = 0) :
    ∀ i ∈ s, ∀ᶠ n : ℕ in atTop, act L (h i) n = 0 := by
  classical
  by_contra hcon
  obtain ⟨i₀, hc⟩ := not_forall.1 hcon
  obtain ⟨hi₀, hne⟩ := not_forall.1 hc
  set s' : Finset ι := s.filter fun i => ¬ ∀ᶠ n : ℕ in atTop, act L (h i) n = 0 with hs'
  have hmem : ∀ i, i ∈ s' ↔ i ∈ s ∧ ¬ ∀ᶠ n : ℕ in atTop, act L (h i) n = 0 := fun i => by
    rw [hs', Finset.mem_filter]
  have hsne : s'.Nonempty := ⟨i₀, (hmem i₀).2 ⟨hi₀, hne⟩⟩
  have hhyp : ∀ i ∈ s', IsHypergeometric (act L (h i)) := fun i hi =>
    (isHypergeometric_act L (hh i ((hmem i).1 hi).1) ((hmem i).1 hi).2).1
  have hrest : ∀ᶠ n : ℕ in atTop, ∀ i ∈ s, i ∉ s' → act L (h i) n = 0 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    by_cases hi' : i ∈ s'
    · exact Eventually.of_forall fun n h' => absurd hi' h'
    · have : ∀ᶠ n : ℕ in atTop, act L (h i) n = 0 := by
        by_contra hc
        exact hi' ((hmem i).2 ⟨hi, hc⟩)
      exact this.mono fun n hn _ => hn
  have hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s', act L (h i) n = 0 := by
    filter_upwards [hL, hrest] with n a b
    rw [act_sum_seq] at a
    rw [← a]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hi' => b i hi hi'
  obtain ⟨i, hi, j, hj, hij, hsim⟩ := exists_similar_of_sum_eq_zero s' hsne
    (fun i => act L (h i)) hhyp hsum
  have hi1 := (hmem i).1 hi
  have hj1 := (hmem j).1 hj
  have si := (isHypergeometric_act L (hh i hi1.1) hi1.2).2
  have sj := (isHypergeometric_act L (hh j hj1.1) hj1.2).2
  exact hd i hi1.1 j hj1.1 hij ((si.symm.trans hsim).trans sj)

end RecOp

end UndergradKB.Combinatorics.AeqB

end
