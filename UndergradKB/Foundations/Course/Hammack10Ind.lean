import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Data.Nat.Factorization.Basic
import UndergradKB.Common

/-! # Course layer: Hammack, Chapter 10 (induction and sequences)
Thin theorems in the book's terms for the rows of the checklist section "Induction and sequences" that are
`in Mathlib` (and stated by Hammack, possibly also by Levin). Levin-only rows are in `Levin04Ind.lean`. -/

namespace UndergradKB.Foundations.Course

open Finset

/-- FO-171. Induction: a base case at 1 and the step `P k → P (k+1)` give `P n` for all `n ≥ 1`. -/
@[kb "hammack2018" "Outline §10.1, p. 194", kb "levin2025" "Induction Proof Structure §4.5.3, p. 385"]
theorem hammack_s10_1_induction (P : ℕ → Prop) (base : P 1) (step : ∀ k ≥ 1, P k → P (k + 1)) :
    ∀ n ≥ 1, P n := fun n hn =>
  Nat.le_induction base (fun k hk ih => step k hk ih) n hn

/-- FO-173. Induction may start at any base `m`: `P m` and `P k → P (k+1)` for `k ≥ m` give `P n` for `n ≥ m`. -/
@[kb "hammack2018" "Prop §10.1, p. 195", kb "levin2025" "Induction Proof Structure §4.5.3, p. 386"]
theorem hammack_s10_1_induction_any_base (P : ℕ → Prop) (m : ℕ) (base : P m)
    (step : ∀ k ≥ m, P k → P (k + 1)) : ∀ n ≥ m, P n := fun n hn =>
  Nat.le_induction base (fun k hk ih => step k hk ih) n hn

/-- FO-174. A statement about all integers follows from the case `0`, a step up and a step down. -/
@[kb "hammack2018" "Prop §10.1, p. 195"]
theorem hammack_s10_1_int_induction (P : ℤ → Prop) (h0 : P 0) (up : ∀ k : ℤ, P k → P (k + 1))
    (down : ∀ k : ℤ, P k → P (k - 1)) : ∀ n : ℤ, P n := fun n =>
  Int.induction_on n h0 (fun _ ih => up _ ih) (fun _ ih => down _ ih)

/-- FO-175. Strong induction: base case `P 1` and "`P 1, ..., P k` all hold implies `P (k+1)`"
give `P n` for all `n ≥ 1`. -/
@[kb "hammack2018" "Outline §10.2, p. 199", kb "levin2025" "Strong Induction Proof Structure §4.6.2, p. 399"]
theorem hammack_s10_2_strong_induction (P : ℕ → Prop) (base : P 1)
    (step : ∀ k ≥ 1, (∀ j, 1 ≤ j → j ≤ k → P j) → P (k + 1)) : ∀ n ≥ 1, P n := by
  have key : ∀ n, ∀ j, 1 ≤ j → j ≤ n → P j := by
    intro n
    induction n with
    | zero => intro j h1 h2; omega
    | succ n ih =>
      intro j h1 h2
      rcases Nat.lt_or_ge n j with h | h
      · have hj : j = n + 1 := by omega
        subst hj
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; exact base
        · exact step n hpos (fun i hi1 hi2 => ih i hi1 hi2)
      · exact ih j h1 h
  exact fun n hn => key n n hn le_rfl

/-- FO-177. Smallest counterexample: if some `S n` fails, there is a least failing index `k`,
and `S m` holds for every `m < k`. -/
@[kb "hammack2018" "Outline §10.3, p. 203"]
theorem hammack_s10_3_smallest_counterexample (S : ℕ → Prop) [DecidablePred S] (h : ∃ n, ¬ S n) :
    ∃ k, ¬ S k ∧ ∀ m < k, S m :=
  ⟨Nat.find h, Nat.find_spec h, fun m hm => by simpa using Nat.find_min h hm⟩

/-- FO-179. The sum `1 + 2 + ... + n` times two is `n (n+1)`; equivalently the sum is `n (n+1) / 2`. -/
@[kb "hammack2018" "Exercise 1 §10, p. 207", kb "levin2025" "Example 4.5.2, p. 386"]
theorem hammack_s10_triangular (n : ℕ) :
    ∑ i ∈ range n, (i + 1) = n * (n + 1) / 2 := by
  have h1 := Finset.sum_range_id (n + 1)
  have h2 := Finset.sum_range_succ' (fun i => i) n
  simp only [Nat.add_sub_cancel, add_zero] at h1 h2
  rw [← h2, h1]
  simp [Nat.mul_comm]

/-- FO-181. Bernoulli's inequality: `(1 + x)^n ≥ 1 + n x` for real `x > -1`. -/
@[kb "hammack2018" "Prop §10.1, p. 198"]
theorem hammack_s10_1_bernoulli (x : ℝ) (hx : -1 < x) (n : ℕ) :
    1 + n * x ≤ (1 + x) ^ n :=
  one_add_mul_le_pow (by linarith) n

/-- FO-182. If a prime divides a product of natural numbers, it divides one of the factors. -/
@[kb "hammack2018" "Prop 10.1, p. 198"]
theorem hammack_s10_1_prime_dvd_prod {p n : ℕ} (hp : p.Prime) (a : Fin n → ℕ)
    (h : p ∣ ∏ i, a i) : ∃ i, p ∣ a i := by
  obtain ⟨i, _, hi⟩ := hp.prime.exists_mem_finset_dvd h
  exact ⟨i, hi⟩

/-- FO-184. For integers `x`, `x - 1` divides `x^n - 1`. -/
@[kb "hammack2018" "Prop §10.3, p. 203", kb "levin2025" "Example 4.5.3, p. 387"]
theorem hammack_s10_3_sub_one_dvd_pow (x : ℤ) (n : ℕ) : x - 1 ∣ x ^ n - 1 :=
  _root_.sub_one_dvd_pow_sub_one x n

/-- FO-184 (instance). 4 divides `5^n - 1`. -/
@[kb "hammack2018" "Prop §10.3, p. 203", kb "levin2025" "Example 4.5.3, p. 387"]
theorem hammack_s10_3_four_dvd_five_pow (n : ℕ) : (4 : ℤ) ∣ 5 ^ n - 1 := by
  simpa using _root_.sub_one_dvd_pow_sub_one (5 : ℤ) n

/-- FO-186. A tree is a connected graph with no cycles. -/
@[kb "hammack2018" "Def §10.2, p. 201"]
theorem hammack_s10_2_tree_iff {V : Type*} (G : SimpleGraph V) :
    G.IsTree ↔ G.Connected ∧ ∀ (v : V) (c : G.Walk v v), ¬ c.IsCycle :=
  SimpleGraph.isTree_iff G

/-- FO-187. A finite tree with `n` vertices has `n - 1` edges. -/
@[kb "hammack2018" "Prop §10.2, p. 202"]
theorem hammack_s10_2_tree_edges {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (h : G.IsTree) : G.edgeFinset.card = Fintype.card V - 1 := by
  have := h.card_edgeFinset
  omega

/-- FO-188. Fundamental theorem of arithmetic, existence: every `n > 1` is a product of primes. -/
@[kb "hammack2018" "Thm 10.1, p. 204", kb "levin2025" "Example 4.6.4, p. 400"]
theorem hammack_thm_10_1_exists_prime_factorization (n : ℕ) (hn : 1 < n) :
    ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n :=
  ⟨n.primeFactorsList, fun _ hp => Nat.prime_of_mem_primeFactorsList hp,
    Nat.prod_primeFactorsList (by omega)⟩

/-- FO-189. Fundamental theorem of arithmetic, uniqueness: two prime factorizations of the same
number agree up to order. -/
@[kb "hammack2018" "Thm 10.1, p. 204"]
theorem hammack_thm_10_1_unique_prime_factorization (l₁ l₂ : List ℕ) (h₁ : ∀ p ∈ l₁, p.Prime)
    (h₂ : ∀ p ∈ l₂, p.Prime) (h : l₁.prod = l₂.prod) : l₁.Perm l₂ :=
  (Nat.primeFactorsList_unique rfl h₁).trans
    (Nat.primeFactorsList_unique h.symm h₂).symm

/-- FO-190. Fibonacci numbers: `F 1 = F 2 = 1` and `F (n+2) = F (n+1) + F n` for `n ≥ 1`. -/
@[kb "hammack2018" "Def §10.5, p. 205", kb "levin2025" "Section 4.4.1, p. 373"]
theorem hammack_s10_5_fibonacci :
    Nat.fib 1 = 1 ∧ Nat.fib 2 = 1 ∧ ∀ n ≥ 1, Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n :=
  ⟨by simp, by simp, fun n _ => by rw [Nat.fib_add_two, add_comm]⟩

/-- FO-192. The ratio `F (n+1) / F n` tends to the golden ratio. -/
@[kb "hammack2018" "Eq (10.1) §10.5, p. 206"]
theorem hammack_eq_10_1_fib_ratio_limit :
    Filter.Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib n) Filter.atTop
      (nhds ((1 + Real.sqrt 5) / 2)) :=
  tendsto_fib_succ_div_fib_atTop

/-- FO-193. The golden ratio is `(1 + √5) / 2`. -/
@[kb "hammack2018" "Def §10.5, p. 207", kb "levin2025" "Text §4.4.3, p. 378"]
theorem hammack_s10_5_golden_ratio : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl

/-- FO-194. Binet's formula: `F n = (φ^n - ψ^n) / √5` with `φ = (1+√5)/2`, `ψ = (1-√5)/2`. -/
@[kb "hammack2018" "Exercise 30 §10, p. 209", kb "levin2025" "Example 4.1.6, p. 335"]
theorem hammack_ex_s10_30_binet (n : ℕ) :
    (Nat.fib n : ℝ) =
      (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) / Real.sqrt 5 := by
  have := Real.coe_fib_eq n
  simpa [Real.goldenRatio, Real.goldenConj] using this

end UndergradKB.Foundations.Course
