import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import UndergradKB.Combinatorics.AeqB.WZ
import UndergradKB.Common.Attr

/-!
# Zeilberger's algorithm (creative telescoping) (Petkovsek–Wilf–Zeilberger, "A = B", Chapter 6)

* CO-420: a *telescoped recurrence* `∑_{j ≤ J} a_j(n) F(n+j,k) = G(n,k+1) - G(n,k)` (6.1.3).
* CO-424 (the rewriting step of Theorem 6.2.1): every two-variable recurrence
  `∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n+j, k+i) = 0` (as given by the Fundamental Theorem) can be rewritten
  in telescoped form `P(N, n, 1) F = (K - 1) G` with `G = Q(N, n, K) F` an explicit combination of
  shifts of `F` (so `G/F` is rational when `F` is hypergeometric).
* CO-425, CO-426: the steps of the algorithm (6.3.1)–(6.3.12) for a fixed order `J`: the ratio of
  `t_k = ∑ a_j F(n+j,k)` is `p_0(k+1) r(k) / (p_0(k) s(k))` with `p_0` linear in the `a_j` and `r, s`
  free of them; after Gosper's canonical form, a solution `b` of
  `p_2(k) b(k+1) - p_3(k-1) b(k) = p(k)` (6.3.11) gives the recurrence, with
  `G(n,k) = p_3(k-1) b(k) t_k / p(k)` (6.3.12).
* CO-427: the unknowns `a_j` and the coefficients of `b` solve a *linear* system.
* CO-471: a WZ pair is the order-one case `Ω = N - 1` of creative telescoping.

The parameter `n` is a free integer; values are in a field `K`.  Rational functions of `n, k` are
represented by their values (`ℤ → ℤ → K`) and every ratio is stated without division.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Finset Polynomial

namespace Zeilberger

variable {K : Type*} [Field K]

/-! ### CO-420: telescoped recurrences -/

/-- CO-420. `F` satisfies the telescoped recurrence (6.1.3) of order `J` with coefficients
`a_j(n)` and right-hand side `G`: `∑_{j=0}^{J} a_j(n) F(n+j, k) = G(n, k+1) - G(n, k)` for all
integers `n, k`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.1.3), p. 112"]
def IsTelescopedRecurrence (J : ℕ) (a : ℕ → ℤ → K) (F G : ℤ → ℤ → K) : Prop :=
  ∀ n k : ℤ, ∑ j ∈ range (J + 1), a j n * F (n + j) k = G n (k + 1) - G n k

/-- CO-471. A WZ pair is exactly the order-one case of a telescoped recurrence, with operator
`Ω = N - 1` (coefficients `a_0 = -1`, `a_1 = 1`). -/
@[kb "petkovsekwilfzeilberger1996" "Equation (7.5.2), p. 150"]
theorem wzEq_iff_isTelescopedRecurrence (F G : ℤ → ℤ → K) :
    WZEq F G ↔ IsTelescopedRecurrence 1 (fun j _ => if j = 0 then -1 else 1) F G := by
  unfold WZEq IsTelescopedRecurrence
  refine forall_congr' fun n => forall_congr' fun k => ?_
  simp [sum_range_succ]
  constructor <;> intro h <;> linear_combination h

/-! ### CO-424: from a two-variable recurrence to telescoped form -/

/-- `F(k+i) - F(k) = ∑_{t<i} F(k+1+t) - ∑_{t<i} F(k+t)`. -/
theorem sub_eq_telescope (f : ℤ → K) (k : ℤ) (i : ℕ) :
    f (k + i) - f k = ∑ t ∈ range i, f (k + 1 + t) - ∑ t ∈ range i, f (k + t) := by
  rw [← sum_sub_distrib]
  have := Finset.sum_range_sub (fun t : ℕ => f (k + t)) i
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ] at this
  rw [← this]
  refine sum_congr rfl fun t _ => ?_
  rw [show k + 1 + (t : ℤ) = k + (t + 1) by ring]

/-- CO-424 (Theorem 6.2.1, the rewriting step (6.2.2)). If `F` satisfies a two-variable recurrence
`∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n+j, k+i) = 0` for all `n, k`, then it satisfies the telescoped
recurrence with coefficients `∑_i a_{ij}(n)` (the operator `P(N, n, 1)`) and right-hand side
`G(n,k) = -∑_{i,j} a_{ij}(n) ∑_{t < i} F(n+j, k+t)` (the operator `-Q(N, n, K)` applied to `F`,
from `P(N,n,K) = P(N,n,1) + (K - 1) Q`); `G` is a combination of shifts of `F`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 6.2.1 (proof), p. 115"]
theorem isTelescopedRecurrence_of_two_variable (I J : ℕ) (a : ℕ → ℕ → ℤ → K)
    (F : ℤ → ℤ → K)
    (h : ∀ n k : ℤ, ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1), a i j n * F (n + j) (k + i) = 0) :
    IsTelescopedRecurrence J (fun j n => ∑ i ∈ range (I + 1), a i j n) F
      (fun n k => -∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1),
        a i j n * ∑ t ∈ range i, F (n + j) (k + t)) := by
  intro n k
  simp only
  calc ∑ j ∈ range (J + 1), (∑ i ∈ range (I + 1), a i j n) * F (n + j) k
      = ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1), a i j n * F (n + j) k := by
        simp_rw [sum_mul]; exact sum_comm
    _ = ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1), (a i j n * F (n + j) (k + i) -
          a i j n * (∑ t ∈ range i, F (n + j) (k + 1 + t) - ∑ t ∈ range i, F (n + j) (k + t))) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [← sub_eq_telescope (F (n + j)) k i]; ring
    _ = ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1), a i j n * F (n + j) (k + i) -
          (∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1), a i j n * ∑ t ∈ range i, F (n + j) (k + 1 + t) -
            ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1), a i j n * ∑ t ∈ range i, F (n + j) (k + t)) := by
        simp only [mul_sub, sum_sub_distrib]
    _ = _ := by rw [h n k]; ring

/-- A function on `ℤ` with finite support and `g(k+1) = g(k)` for all `k` vanishes. -/
theorem eq_zero_of_succ_eq_of_finite {g : ℤ → K} (hg : (Function.support g).Finite)
    (h : ∀ k, g (k + 1) = g k) : g = 0 := by
  obtain ⟨k0, hk0⟩ := hg.infinite_compl.nonempty
  have hk0' : g k0 = 0 := by simpa using hk0
  funext k
  rw [Pi.zero_apply, int_eq_of_succ_eq h k k0, hk0']

/-- Summation by parts: `∑_{i ≤ m} c_i X_i = S_m X_m + ∑_{i < m} S_i (X_i - X_{i+1})` with
`S_i = ∑_{t ≤ i} c_t`. -/
theorem sum_by_parts (c X : ℕ → K) (m : ℕ) :
    ∑ i ∈ range (m + 1), c i * X i = (∑ t ∈ range (m + 1), c t) * X m +
      ∑ i ∈ range m, (∑ t ∈ range (i + 1), c t) * (X i - X (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ (fun i => c i * X i), ih, sum_range_succ (fun t => c t) (m + 1),
      sum_range_succ (fun i => (∑ t ∈ range (i + 1), c t) * (X i - X (i + 1))) m]
    ring

/-- The rewriting step with a nonzero operator `P(N, n, 1)`. -/
theorem telescoped_of_sum_ne_zero (F : ℤ → ℤ → K) (I J : ℕ) (a : ℕ → ℕ → Polynomial K)
    (hsum : ∃ j ≤ J, ∑ i ∈ range (I + 1), a i j ≠ 0)
    (hrec : ∀ n k : ℤ, ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1),
      (a i j).eval (n : K) * F (n + j) (k + i) = 0) :
    ∃ c : ℕ → Polynomial K, (∃ j ≤ J, c j ≠ 0) ∧
      ∃ G : ℤ → ℤ → K, IsTelescopedRecurrence J (fun j n => (c j).eval (n : K)) F G := by
  obtain ⟨j, hj, hj0⟩ := hsum
  refine ⟨fun j => ∑ i ∈ range (I + 1), a i j, ⟨j, hj, hj0⟩,
    fun n k => -∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1),
      (a i j).eval (n : K) * ∑ t ∈ range i, F (n + j) (k + t), ?_⟩
  have := isTelescopedRecurrence_of_two_variable I J (fun i j n => (a i j).eval (n : K)) F hrec
  intro n k
  simpa [Polynomial.eval_finsetSum] using this n k

/-- CO-424 (nontriviality). Let `F(n, ·)` have finite support for every `n` and let `F` satisfy a
nontrivial two-variable recurrence `∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n+j, k+i) = 0` (polynomial
coefficients, not all zero) at all integer points. Then `F` satisfies a telescoped recurrence
`∑_{j ≤ J} c_j(n) F(n+j, k) = G(n,k+1) - G(n,k)` whose operator `∑_j c_j(n) N^j` is nonzero.
(If `P(N, n, 1) = 0` then `P = (K - 1) Q`, and `G = Q F` is constant in `k` with finite support, hence
zero: `Q` is a nontrivial recurrence of smaller span in `k`. This descent replaces the book's
minimal-degree argument of Graham, Knuth and Patashnik.) -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 6.2.1, p. 115"]
theorem exists_nontrivial_telescoped (F : ℤ → ℤ → K) (hF : ∀ n, (Function.support (F n)).Finite)
    (J : ℕ) : ∀ (I : ℕ) (a : ℕ → ℕ → Polynomial K),
    (∃ i ≤ I, ∃ j ≤ J, a i j ≠ 0) →
    (∀ n k : ℤ, ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1),
      (a i j).eval (n : K) * F (n + j) (k + i) = 0) →
    ∃ c : ℕ → Polynomial K, (∃ j ≤ J, c j ≠ 0) ∧
      ∃ G : ℤ → ℤ → K, IsTelescopedRecurrence J (fun j n => (c j).eval (n : K)) F G := by
  intro I
  induction I with
  | zero =>
    intro a hne hrec
    obtain ⟨i, hi, j, hj, hij⟩ := hne
    obtain rfl : i = 0 := by omega
    exact telescoped_of_sum_ne_zero F 0 J a ⟨j, hj, by simpa using hij⟩ hrec
  | succ I ih =>
    intro a hne hrec
    by_cases hsum : ∃ j ≤ J, ∑ i ∈ range (I + 1 + 1), a i j ≠ 0
    · exact telescoped_of_sum_ne_zero F (I + 1) J a hsum hrec
    · push Not at hsum
      -- `P = (K - 1) Q` with `b_i = -∑_{t ≤ i} a_t`
      set b : ℕ → ℕ → Polynomial K := fun i j => -∑ t ∈ range (i + 1), a t j with hb
      have hQ : ∀ n k : ℤ, ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1),
          (b i j).eval (n : K) * F (n + j) (k + i) = 0 := by
        intro n
        set g : ℤ → K := fun k => ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1),
          (b i j).eval (n : K) * F (n + j) (k + i) with hg
        have hgfin : (Function.support g).Finite := by
          let T : Finset ℤ := (range (I + 1)).biUnion fun i => (range (J + 1)).biUnion fun j =>
            ((hF (n + j)).preimage (f := fun k : ℤ => k + i)
              (fun x _ y _ h => add_right_cancel h)).toFinset
          refine T.finite_toSet.subset fun k hk => ?_
          obtain ⟨i, hi, hk'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
          obtain ⟨j, hj, hk''⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk'
          simp only [T, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
            Set.Finite.mem_toFinset, Set.mem_preimage, Function.mem_support]
          exact ⟨i, hi, j, hj, right_ne_zero_of_mul hk''⟩
        have hstep : ∀ k, g (k + 1) = g k := by
          intro k
          rw [← sub_eq_zero, ← hrec n k]
          have L : g (k + 1) - g k = ∑ j ∈ range (J + 1), ∑ i ∈ range (I + 1),
              (b i j).eval (n : K) * (F (n + j) (k + 1 + i) - F (n + j) (k + i)) := by
            simp only [hg]
            rw [← sum_sub_distrib]
            simp_rw [← sum_sub_distrib, ← mul_sub]
            exact sum_comm
          rw [L, Finset.sum_comm (s := range (I + 1 + 1))]
          refine sum_congr rfl fun j hj => ?_
          have hz : ∑ t ∈ range (I + 1 + 1), (a t j).eval (n : K) = 0 := by
            rw [← Polynomial.eval_finsetSum, hsum j (Nat.lt_succ_iff.1 (mem_range.1 hj)),
              Polynomial.eval_zero]
          rw [sum_by_parts (fun i => (a i j).eval (n : K)) (fun i : ℕ => F (n + j) (k + i)) (I + 1),
            hz, zero_mul, zero_add]
          refine sum_congr rfl fun i _ => ?_
          simp only [hb, Polynomial.eval_neg, Polynomial.eval_finsetSum]
          rw [show k + 1 + (i : ℤ) = k + ((i + 1 : ℕ) : ℤ) by push_cast; ring]
          ring
        have := eq_zero_of_succ_eq_of_finite hgfin hstep
        intro k
        exact congrFun this k
      have hne' : ∃ i ≤ I, ∃ j ≤ J, b i j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨i, hi, j, hj, hij⟩ := hne
        have hS : ∀ i ≤ I + 1, ∑ t ∈ range (i + 1), a t j = 0 := by
          intro i hi
          rcases Nat.lt_or_ge i (I + 1) with h | h
          · have := hcon i (by omega) j hj
            simpa [hb] using this
          · obtain rfl : i = I + 1 := by omega
            exact hsum j hj
        apply hij
        rcases i with _ | i
        · simpa using hS 0 (by omega)
        · have e := sum_range_succ (fun t => a t j) (i + 1)
          rw [hS (i + 1) hi, hS i (by omega)] at e
          linear_combination -e
      exact ih b hne' hQ

/-! ### CO-425, CO-426: the steps of the algorithm for a fixed order `J` -/

/-- `t_k = ∑_{j=0}^{J} a_j F(n+j, k)` (6.3.1). -/
def tSeq (J : ℕ) (a : ℕ → ℤ → K) (F : ℤ → ℤ → K) (n k : ℤ) : K :=
  ∑ j ∈ range (J + 1), a j n * F (n + j) k

/-- `∏_{r=1}^{J} s_2(n+r, k)`. -/
def s2Prod (J : ℕ) (s2 : ℤ → ℤ → K) (n k : ℤ) : K := ∏ r ∈ range J, s2 (n + (r + 1 : ℕ)) k

/-- `p_0(n,k) = ∑_j a_j(n) ∏_{i<j} s_1(n+j-i, k) ∏_{r=j+1}^{J} s_2(n+r, k)` (6.3.6). -/
def p0 (J : ℕ) (a : ℕ → ℤ → K) (s1 s2 : ℤ → ℤ → K) (n k : ℤ) : K :=
  ∑ j ∈ range (J + 1), a j n * (∏ i ∈ range j, s1 (n + j - i) k) *
    ∏ r ∈ range (J - j), s2 (n + (j + r + 1 : ℕ)) k

/-- (6.3.3): if `s_2(n,k) F(n,k) = s_1(n,k) F(n-1,k)` (the ratio `F(n,k)/F(n-1,k) = s_1/s_2`), then
`F(n+j, k) ∏_{r=1}^{j} s_2(n+r, k) = F(n,k) ∏_{i<j} s_1(n+j-i, k)`. -/
theorem shift_mul_prod (s1 s2 F : ℤ → ℤ → K) (hs : ∀ n k, s2 n k * F n k = s1 n k * F (n - 1) k)
    (n k : ℤ) (j : ℕ) :
    F (n + j) k * ∏ r ∈ range j, s2 (n + (r + 1 : ℕ)) k =
      F n k * ∏ i ∈ range j, s1 (n + j - i) k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_range_succ, prod_range_succ']
    have h1 := hs (n + (j + 1 : ℕ)) k
    rw [show n + ((j + 1 : ℕ) : ℤ) - 1 = n + j by push_cast; ring] at h1
    have e : ∀ i ∈ range j, s1 (n + ((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) k =
        s1 (n + j - i) k := fun i _ => by congr 1; push_cast; ring
    rw [prod_congr rfl e]
    simp only [Nat.cast_zero, sub_zero]
    linear_combination (∏ r ∈ range j, s2 (n + (r + 1 : ℕ)) k) * h1 +
      s1 (n + ((j + 1 : ℕ) : ℤ)) k * ih

/-- (6.3.4)–(6.3.6): `t_k ∏_{r=1}^{J} s_2(n+r, k) = p_0(n,k) F(n,k)`. -/
theorem tSeq_mul_s2Prod (J : ℕ) (a : ℕ → ℤ → K) (s1 s2 F : ℤ → ℤ → K)
    (hs : ∀ n k, s2 n k * F n k = s1 n k * F (n - 1) k) (n k : ℤ) :
    tSeq J a F n k * s2Prod J s2 n k = p0 J a s1 s2 n k * F n k := by
  unfold tSeq p0 s2Prod
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun j hj => ?_
  have hjJ : j ≤ J := Nat.lt_succ_iff.1 (mem_range.1 hj)
  have hsplit : ∏ r ∈ range J, s2 (n + (r + 1 : ℕ)) k =
      (∏ r ∈ range j, s2 (n + (r + 1 : ℕ)) k) * ∏ r ∈ range (J - j), s2 (n + (j + r + 1 : ℕ)) k := by
    conv_lhs => rw [show J = j + (J - j) by omega]
    rw [prod_range_add]
  rw [hsplit]
  have := shift_mul_prod s1 s2 F hs n k j
  linear_combination a j n * (∏ r ∈ range (J - j), s2 (n + (j + r + 1 : ℕ)) k) * this

/-- CO-425 (6.3.5)–(6.3.8). If moreover `r_2(n,k) F(n,k+1) = r_1(n,k) F(n,k)`, then
`t_{k+1} p_0(k) s(k) = t_k p_0(k+1) r(k)` with `r(k) = r_1(n,k) ∏_{r=1}^{J} s_2(n+r,k)` and
`s(k) = r_2(n,k) ∏_{r=1}^{J} s_2(n+r,k+1)`: the unknowns `a_j` enter only through `p_0`. -/
@[kb "petkovsekwilfzeilberger1996" "Equations (6.3.5)-(6.3.8), p. 117"]
theorem tSeq_ratio (J : ℕ) (a : ℕ → ℤ → K) (s1 s2 r1 r2 F : ℤ → ℤ → K)
    (hs : ∀ n k, s2 n k * F n k = s1 n k * F (n - 1) k)
    (hr : ∀ n k, r2 n k * F n (k + 1) = r1 n k * F n k) (n k : ℤ) :
    tSeq J a F n (k + 1) * p0 J a s1 s2 n k * (r2 n k * s2Prod J s2 n (k + 1)) =
      tSeq J a F n k * p0 J a s1 s2 n (k + 1) * (r1 n k * s2Prod J s2 n k) := by
  have h1 := tSeq_mul_s2Prod J a s1 s2 F hs n (k + 1)
  have h2 := tSeq_mul_s2Prod J a s1 s2 F hs n k
  have h3 := hr n k
  linear_combination p0 J a s1 s2 n k * r2 n k * h1 - p0 J a s1 s2 n (k + 1) * r1 n k * h2 +
    p0 J a s1 s2 n k * p0 J a s1 s2 n (k + 1) * h3

/-- (6.3.9)–(6.3.10). With Gosper's canonical form `r(k) p_1(k) p_3(k) = s(k) p_1(k+1) p_2(k)` and
`p = p_0 p_1`, the ratio of `t_k` is `p(k+1) p_2(k) / (p(k) p_3(k))`, at points where `s(k) ≠ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.3.10), p. 118"]
theorem tSeq_ratio_canonical {t p0' r s p1 p2 p3 : ℤ → K} (k : ℤ)
    (h5 : t (k + 1) * p0' k * s k = t k * p0' (k + 1) * r k)
    (h9 : r k * p1 k * p3 k = s k * p1 (k + 1) * p2 k) (hs : s k ≠ 0) :
    t (k + 1) * (p0' k * p1 k) * p3 k = t k * (p0' (k + 1) * p1 (k + 1)) * p2 k := by
  refine mul_right_cancel₀ hs ?_
  linear_combination p1 k * p3 k * h5 + t k * p0' (k + 1) * h9

/-- CO-426 (6.3.11)–(6.3.12), Gosper's step. If `t_{k+1} p(k) p_3(k) = t_k p(k+1) p_2(k)` and `b`
solves `p_2(k) b(k+1) - p_3(k-1) b(k) = p(k)`, then `G(k) = p_3(k-1) b(k) t_k / p(k)` satisfies
`G(k+1) - G(k) = t_k` at every `k` with `p(k), p(k+1) ≠ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Equations (6.3.11)-(6.3.12), p. 118-119"]
theorem gosper_step {t p p2 p3 b : ℤ → K} (k : ℤ)
    (h10 : t (k + 1) * p k * p3 k = t k * p (k + 1) * p2 k)
    (h11 : p2 k * b (k + 1) - p3 (k - 1) * b k = p k) (hp : p k ≠ 0) (hp1 : p (k + 1) ≠ 0) :
    p3 (k + 1 - 1) * b (k + 1) * t (k + 1) / p (k + 1) - p3 (k - 1) * b k * t k / p k = t k := by
  rw [show k + 1 - 1 = k by ring, div_sub_div _ _ hp1 hp, div_eq_iff (mul_ne_zero hp1 hp)]
  linear_combination b (k + 1) * h10 + t k * p (k + 1) * h11

/-- CO-425 / CO-426. **Correctness of Zeilberger's algorithm** for a fixed order `J`. Let the ratios
of `F` be `F(n,k)/F(n-1,k) = s_1/s_2` and `F(n,k+1)/F(n,k) = r_1/r_2` (stated without division), let
`p_1, p_2, p_3` give the canonical form (6.3.9) of `r/s`, `p = p_0 p_1`, and let `b` solve (6.3.11).
Then the telescoped recurrence `∑_j a_j(n) F(n+j,k) = G(n,k+1) - G(n,k)` holds with
`G(n,k) = p_3(k-1) b(k) t_k / p(k)` at every point where `s(k), p(k), p(k+1)` do not vanish. -/
@[kb "petkovsekwilfzeilberger1996" "text (6.3.1)-(6.3.12), p. 116-119"]
theorem zeilberger_sound (J : ℕ) (a : ℕ → ℤ → K) (s1 s2 r1 r2 F : ℤ → ℤ → K)
    (hs : ∀ n k, s2 n k * F n k = s1 n k * F (n - 1) k)
    (hr : ∀ n k, r2 n k * F n (k + 1) = r1 n k * F n k)
    (p1 p2 p3 b : ℤ → ℤ → K) (n k : ℤ)
    (h9 : (r1 n k * s2Prod J s2 n k) * p1 n k * p3 n k =
      (r2 n k * s2Prod J s2 n (k + 1)) * p1 n (k + 1) * p2 n k)
    (h11 : p2 n k * b n (k + 1) - p3 n (k - 1) * b n k = p0 J a s1 s2 n k * p1 n k)
    (hs0 : r2 n k * s2Prod J s2 n (k + 1) ≠ 0)
    (hp : p0 J a s1 s2 n k * p1 n k ≠ 0) (hp1 : p0 J a s1 s2 n (k + 1) * p1 n (k + 1) ≠ 0) :
    ∑ j ∈ range (J + 1), a j n * F (n + j) k =
      p3 n (k + 1 - 1) * b n (k + 1) * tSeq J a F n (k + 1) /
          (p0 J a s1 s2 n (k + 1) * p1 n (k + 1)) -
        p3 n (k - 1) * b n k * tSeq J a F n k / (p0 J a s1 s2 n k * p1 n k) := by
  have h10 := tSeq_ratio_canonical (t := tSeq J a F n) (p0' := p0 J a s1 s2 n)
    (s := fun k => r2 n k * s2Prod J s2 n (k + 1)) (r := fun k => r1 n k * s2Prod J s2 n k)
    (p1 := p1 n) (p2 := p2 n) (p3 := p3 n) k (tSeq_ratio J a s1 s2 r1 r2 F hs hr n k) h9 hs0
  exact (gosper_step (t := tSeq J a F n) (p := fun k => p0 J a s1 s2 n k * p1 n k)
    (p2 := p2 n) (p3 := p3 n) (b := b n) k h10 h11 hp hp1).symm

/-! ### CO-427: the system for the `a_j` and `b` is linear -/

/-- CO-427. For fixed polynomials `p_2, p_3, p_1` (independent of the unknowns) and fixed
`w_j` (so that `p_0 = ∑_j a_j w_j`, linear in the `a_j`), the map
`(a, b) ↦ p_2(k) b(k+1) - p_3(k-1) b(k) - p_1(k) ∑_j a_j w_j(k)` is linear over the ring of
coefficients `R` (e.g. `R = K[n]`), so the solutions of (6.3.11) in the unknowns
`a_0, …, a_J, β_0, …, β_Δ` (with `b = ∑ β_l k^l` of degree `≤ Δ`) form a submodule: its kernel. -/
@[kb "petkovsekwilfzeilberger1996" "text after (6.3.11), p. 118"]
def zeilbergerSystem {R : Type*} [CommRing R] (J : ℕ) (w : ℕ → R[X]) (p1 p2 p3 : R[X]) :
    (Fin (J + 1) → R) × R[X] →ₗ[R] R[X] where
  toFun x := p2 * x.2.comp (X + 1) - p3.comp (X - 1) * x.2 - p1 * ∑ j : Fin (J + 1), C (x.1 j) * w j
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, C_add, add_mul, sum_add_distrib,
      add_comp]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, C_mul, RingHom.id_apply,
      smul_eq_C_mul, mul_comp, C_comp, mul_assoc, ← mul_sum]
    ring

/-- CO-427. `(a, b)` is a solution of (6.3.11) iff it lies in the kernel of the linear system; in
particular every `R`-linear combination of solutions is a solution. -/
@[kb "petkovsekwilfzeilberger1996" "text after (6.3.11), p. 118"]
theorem zeilbergerSystem_eq_zero_iff {R : Type*} [CommRing R] (J : ℕ) (w : ℕ → R[X])
    (p1 p2 p3 : R[X]) (a : Fin (J + 1) → R) (b : R[X]) :
    zeilbergerSystem J w p1 p2 p3 (a, b) = 0 ↔
      p2 * b.comp (X + 1) - p3.comp (X - 1) * b = p1 * ∑ j : Fin (J + 1), C (a j) * w j := by
  simp only [zeilbergerSystem, LinearMap.coe_mk, AddHom.coe_mk]
  exact sub_eq_zero

end Zeilberger

end UndergradKB.Combinatorics.AeqB
