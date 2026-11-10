import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharZero.Infinite
import UndergradKB.Common.Attr

/-!
# Proving identities by a recurrence and finitely many checks (A=B, Sections 2.2 and 4.4)

If two sequences satisfy the same linear recurrence whose leading coefficient never vanishes
(from some point on) and agree on as many consecutive starting values as the order, then they
agree from that point on.  This is the logical core of the Zeilberger principle (find a
recurrence for the sum, check the answer satisfies it, check initial values), and of the
finite-check bound `n0 = order + (largest natural root of the leading coefficient)`.
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset Polynomial

section Forward

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Uniqueness for a linear recurrence of order `J` with a leading coefficient `a J n` that is
nonzero for `n ≥ n0`: a solution is determined by its values at `n0, …, n0 + J - 1`. -/
theorem eq_of_recurrence_forward (J n0 : ℕ) (a : ℕ → ℕ → R) (hlead : ∀ n, n0 ≤ n → a J n ≠ 0)
    (f g : ℕ → R)
    (hf : ∀ n, n0 ≤ n → ∑ j ∈ range (J + 1), a j n * f (n + j) = 0)
    (hg : ∀ n, n0 ≤ n → ∑ j ∈ range (J + 1), a j n * g (n + j) = 0)
    (hinit : ∀ i, i < J → f (n0 + i) = g (n0 + i)) : ∀ n, n0 ≤ n → f n = g n := by
  have hd : ∀ n, n0 ≤ n → ∑ j ∈ range (J + 1), a j n * (f - g) (n + j) = 0 := by
    intro n hn
    have := sub_eq_zero.2 ((hf n hn).trans (hg n hn).symm)
    rw [← this, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_sub]
  suffices h : ∀ n, n0 ≤ n → (f - g) n = 0 by
    intro n hn; exact sub_eq_zero.1 (h n hn)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < n0 + J
    · have := hinit (n - n0) (by omega)
      rw [show n0 + (n - n0) = n by omega] at this
      simp [this]
    · have hm : n0 ≤ n - J := by omega
      have h := hd (n - J) hm
      rw [sum_range_succ, Finset.sum_eq_zero] at h
      · rw [zero_add, show n - J + J = n by omega] at h
        exact (mul_eq_zero.1 h).resolve_left (hlead _ hm)
      · intro j hj
        rw [mem_range] at hj
        rw [ih (n - J + j) (by omega) (by omega)]
        simp

/-- CO-386. The Zeilberger principle for sums (the logical skeleton): to prove
`∑_k summand(n,k) = answer(n)` for `n ≥ n0`, find a recurrence of order `J` with nowhere-vanishing
leading coefficient satisfied by the sum, check that `answer` satisfies it, and check the `J`
initial values. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 34"]
theorem zeilberger_principle {ι : Type*} (J n0 : ℕ) (a : ℕ → ℕ → R)
    (hlead : ∀ n, n0 ≤ n → a J n ≠ 0) (s : ℕ → Finset ι) (F : ℕ → ι → R) (answer : ℕ → R)
    (hsum : ∀ n, n0 ≤ n →
      ∑ j ∈ range (J + 1), a j n * ∑ k ∈ s (n + j), F (n + j) k = 0)
    (hans : ∀ n, n0 ≤ n → ∑ j ∈ range (J + 1), a j n * answer (n + j) = 0)
    (hinit : ∀ i, i < J → ∑ k ∈ s (n0 + i), F (n0 + i) k = answer (n0 + i)) :
    ∀ n, n0 ≤ n → ∑ k ∈ s n, F n k = answer n :=
  eq_of_recurrence_forward J n0 a hlead (fun n => ∑ k ∈ s n, F n k) answer hsum hans hinit

end Forward

section Poly

variable {K : Type*} [Field K]

/-- CO-391 (polynomial coefficients). A recurrence `∑_{j ≤ J} a_j(n) f(n + j) = 0` with polynomial
coefficients whose leading polynomial has no natural-number root `≥ m`: two solutions agreeing at
`m, …, m + J - 1` agree for all `n ≥ m`. -/
@[kb "petkovsekwilfzeilberger1996" "text, pp. 79-80"]
theorem eq_of_polynomial_recurrence (J m : ℕ) (a : ℕ → K[X])
    (hroot : ∀ k : ℕ, m ≤ k → ¬ (a J).IsRoot (k : K)) (f g : ℕ → K)
    (hf : ∀ n, m ≤ n → ∑ j ∈ range (J + 1), (a j).eval (n : K) * f (n + j) = 0)
    (hg : ∀ n, m ≤ n → ∑ j ∈ range (J + 1), (a j).eval (n : K) * g (n + j) = 0)
    (hinit : ∀ i, i < J → f (m + i) = g (m + i)) : ∀ n, m ≤ n → f n = g n :=
  eq_of_recurrence_forward J m (fun j n => (a j).eval (n : K)) (fun n hn => hroot n hn) f g hf hg
    hinit

/-- A nonzero polynomial over a field of characteristic zero has only finitely many natural
roots, so there is a bound `N` beyond which it has none. -/
theorem exists_bound_natural_roots [CharZero K] (P : K[X]) (hP : P ≠ 0) :
    ∃ N : ℕ, ∀ k : ℕ, N < k → ¬ P.IsRoot (k : K) := by
  classical
  have hfin : {k : ℕ | P.IsRoot (k : K)}.Finite := by
    refine Set.Finite.of_finite_image (f := fun k : ℕ => (k : K)) ?_ Nat.cast_injective.injOn
    refine (P.roots.toFinset.finite_toSet).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    simpa [hP] using hk
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N, fun k hk hroot => ?_⟩
  have := hN hroot
  omega

/-- CO-391 (the book's form). For a recurrence `∑_{i ≤ J} b_i(n) f(n - i) = 0` (valid for `n ≥ J`)
with polynomial coefficients and nonzero leading coefficient polynomial `b 0`, there is a bound
`N` (any bound on its natural roots) such that two solutions agreeing for all `n ≤ J + N`
(i.e. up to the order plus the largest nonnegative root) agree everywhere. -/
@[kb "petkovsekwilfzeilberger1996" "text, pp. 79-80"]
theorem eq_of_backward_recurrence (J N : ℕ) (b : ℕ → K[X])
    (hroot : ∀ k : ℕ, N < k → ¬ (b 0).IsRoot (k : K)) (f g : ℕ → K)
    (hf : ∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * f (n - i) = 0)
    (hg : ∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * g (n - i) = 0)
    (hinit : ∀ n, n ≤ J + N → f n = g n) : ∀ n, f n = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hle : n ≤ J + N
    · exact hinit n hle
    · have hJ : J ≤ n := by omega
      have h := sub_eq_zero.2 ((hf n hJ).trans (hg n hJ).symm)
      rw [← Finset.sum_sub_distrib, sum_range_succ'] at h
      rw [Finset.sum_eq_zero] at h
      · simp only [zero_add, Nat.sub_zero] at h
        have h2 : (b 0).eval (n : K) * (f n - g n) = 0 := by
          rw [← h]; ring
        exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (hroot n (by omega)))
      · intro i hi
        rw [mem_range] at hi
        rw [ih (n - (i + 1)) (by omega)]
        simp

/-- CO-391. Combination of the previous theorem with `exists_bound_natural_roots`: for a
nonzero leading polynomial there is some finite check bound `N` that suffices. -/
@[kb "petkovsekwilfzeilberger1996" "text, pp. 79-80"]
theorem exists_finite_check_bound [CharZero K] (J : ℕ) (b : ℕ → K[X]) (hb : b 0 ≠ 0) :
    ∃ N : ℕ, ∀ f g : ℕ → K,
      (∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * f (n - i) = 0) →
      (∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * g (n - i) = 0) →
      (∀ n, n ≤ J + N → f n = g n) → ∀ n, f n = g n := by
  obtain ⟨N, hN⟩ := exists_bound_natural_roots (b 0) hb
  exact ⟨N, fun f g hf hg hi => eq_of_backward_recurrence J N b hN f g hf hg hi⟩

end Poly

end UndergradKB.Combinatorics.AeqB
