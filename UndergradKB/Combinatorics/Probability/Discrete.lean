import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

/-!
# Finite discrete probability (Keller–Trotter, Chapters 10 and 11)

The book's probability spaces are finite: a finite set `Ω` with a mass function `p`.
We model them by `FinProbSpace`, with events as `Finset Ω`, and prove linearity of expectation,
expectation and variance of the number of successes in `n` Bernoulli trials, the first moment
method, and the win probability of Example 10.28.
-/

open Finset

namespace UndergradKB.Combinatorics.Probability

/-- A finite probability space: a probability mass function on a finite type. -/
structure FinProbSpace (Ω : Type*) [Fintype Ω] where
  /-- the mass of each outcome -/
  p : Ω → ℝ
  p_nonneg : ∀ ω, 0 ≤ p ω
  sum_p : ∑ ω, p ω = 1

namespace FinProbSpace

variable {Ω : Type*} [Fintype Ω] (μ : FinProbSpace Ω)

/-- The probability of an event (a finite set of outcomes). -/
def prob (s : Finset Ω) : ℝ := ∑ ω ∈ s, μ.p ω

/-- The expectation of a random variable `X : Ω → ℝ`. -/
def expect (X : Ω → ℝ) : ℝ := ∑ ω, μ.p ω * X ω

/-- The variance of a random variable: the expectation of `(X - E X)^2`. -/
def variance (X : Ω → ℝ) : ℝ := μ.expect fun ω => (X ω - μ.expect X) ^ 2

lemma prob_nonneg (s : Finset Ω) : 0 ≤ μ.prob s :=
  sum_nonneg fun ω _ => μ.p_nonneg ω

lemma prob_le_one (s : Finset Ω) : μ.prob s ≤ 1 := by
  rw [← μ.sum_p]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ s) fun ω _ _ => μ.p_nonneg ω

lemma prob_univ : μ.prob univ = 1 := μ.sum_p

lemma prob_mono {s t : Finset Ω} (h : s ⊆ t) : μ.prob s ≤ μ.prob t :=
  sum_le_sum_of_subset_of_nonneg h fun ω _ _ => μ.p_nonneg ω

lemma prob_union_of_disjoint [DecidableEq Ω] {s t : Finset Ω} (h : Disjoint s t) :
    μ.prob (s ∪ t) = μ.prob s + μ.prob t :=
  sum_union h

lemma expect_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X :=
  sum_nonneg fun ω _ => mul_nonneg (μ.p_nonneg ω) (h ω)

/-- CO-240. Linearity of expectation (Proposition 10.17): the expectation of a sum of finitely
many random variables is the sum of their expectations. -/
@[kb "kellertrotter2017" "Proposition 10.17, p. 244"]
theorem expect_finset_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.expect (X i) := by
  unfold expect
  simp_rw [mul_sum]
  exact sum_comm

lemma expect_add (X Y : Ω → ℝ) : μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  unfold expect
  simp_rw [mul_add, sum_add_distrib]

lemma expect_const_mul (c : ℝ) (X : Ω → ℝ) : μ.expect (fun ω => c * X ω) = c * μ.expect X := by
  unfold expect
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by ring

lemma expect_const (c : ℝ) : μ.expect (fun _ => c) = c := by
  unfold expect
  rw [← sum_mul, μ.sum_p, one_mul]

/-- The usual formula `Var X = E(X^2) - E(X)^2`. -/
lemma variance_eq (X : Ω → ℝ) : μ.variance X = μ.expect (fun ω => X ω ^ 2) - μ.expect X ^ 2 := by
  have h : ∀ ω, (X ω - μ.expect X) ^ 2
      = X ω ^ 2 + (-2 * μ.expect X) * X ω + μ.expect X ^ 2 := fun ω => by ring
  unfold variance
  simp_rw [h]
  rw [expect_add, expect_add, expect_const_mul, expect_const]
  ring

/-- CO-249. First moment method (text p. 257): if `X` counts bad structures and `E(X) < 1`,
then some outcome of positive probability has no bad structure. -/
@[kb "kellertrotter2017" "text, p. 257"]
theorem first_moment (X : Ω → ℕ) (h : μ.expect (fun ω => (X ω : ℝ)) < 1) :
    ∃ ω, 0 < μ.p ω ∧ X ω = 0 := by
  by_contra hne
  push Not at hne
  apply absurd h
  rw [not_lt, ← μ.sum_p]
  refine sum_le_sum fun ω _ => ?_
  rcases (μ.p_nonneg ω).eq_or_lt with h0 | h0
  · simp [← h0]
  · have : (1 : ℝ) ≤ X ω := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hne ω h0)
    nlinarith

/-- First moment method, plain form: some outcome has no bad structure. -/
@[kb "kellertrotter2017" "text, p. 257"]
theorem exists_eq_zero_of_expect_lt_one (X : Ω → ℕ) (h : μ.expect (fun ω => (X ω : ℝ)) < 1) :
    ∃ ω, X ω = 0 :=
  let ⟨ω, _, h⟩ := μ.first_moment X h
  ⟨ω, h⟩

/-- CO-248. Example 10.28, as a geometric series: with `a = P(A)` (win) and `b = P(B)` (loss),
the probability of winning at round `k+1` is `(1-a-b)^k * a`, and these sum to `a/(a+b)`. -/
@[kb "kellertrotter2017" "Example 10.28, p. 249"]
theorem hasSum_win (a b : ℝ) (hab : a + b ≤ 1) (hpos : 0 < a + b) :
    HasSum (fun k : ℕ => (1 - a - b) ^ k * a) (a / (a + b)) := by
  have h := (hasSum_geometric_of_lt_one (r := 1 - a - b) (by linarith) (by linarith)).mul_right a
  convert h using 1
  have : 1 - (1 - a - b) = a + b := by ring
  rw [this, inv_mul_eq_div]

/-- Example 10.28 in the book's shape: `P(A) + P(A) * Σ_{n ≥ 1} (1 - P(A) - P(B))^n = P(A)/(P(A)+P(B))`
for disjoint events `A`, `B` with `P(A) + P(B) > 0`. -/
@[kb "kellertrotter2017" "Example 10.28, p. 249"]
theorem win_probability [DecidableEq Ω] {A B : Finset Ω} (hAB : Disjoint A B) (hpos : 0 < μ.prob A + μ.prob B) :
    μ.prob A + μ.prob A * ∑' n : ℕ, (1 - μ.prob A - μ.prob B) ^ (n + 1)
      = μ.prob A / (μ.prob A + μ.prob B) := by
  have hle : μ.prob A + μ.prob B ≤ 1 := by
    rw [← μ.prob_union_of_disjoint hAB]; exact μ.prob_le_one _
  have h := hasSum_win (μ.prob A) (μ.prob B) hle hpos
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one, pow_zero, one_mul] at h2
  have h3 := h2.tsum_eq
  rw [tsum_mul_right] at h3
  linarith

end FinProbSpace

/-! ### Bernoulli trials -/

section Bernoulli

variable (n : ℕ) (q : ℝ)

/-- The weight of an outcome of `n` Bernoulli trials with success probability `q`
(`true` = success): `q^k (1-q)^(n-k)` where `k` is the number of successes. -/
def bernoulliWeight (ω : Fin n → Bool) : ℝ := ∏ i, if ω i then q else 1 - q

/-- The weight is `q^k (1-q)^(n-k)` with `k` the number of successes. -/
lemma bernoulliWeight_eq (ω : Fin n → Bool) :
    bernoulliWeight n q ω
      = q ^ (univ.filter fun i => ω i = true).card * (1 - q) ^ (univ.filter fun i => ω i = false).card := by
  unfold bernoulliWeight
  rw [Finset.prod_ite]
  simp only [prod_const, Bool.not_eq_true]

lemma sum_bernoulliWeight_mul_prod (f : Fin n → Bool → ℝ) :
    ∑ ω : Fin n → Bool, bernoulliWeight n q ω * ∏ j, f j (ω j)
      = ∏ j, (q * f j true + (1 - q) * f j false) := by
  have h1 : ∀ ω : Fin n → Bool, bernoulliWeight n q ω * ∏ j, f j (ω j)
      = ∏ j, ((if ω j then q else 1 - q) * f j (ω j)) := fun ω => by
    rw [bernoulliWeight, ← prod_mul_distrib]
  simp_rw [h1]
  have h := Finset.sum_prod_piFinset (univ : Finset Bool) (fun j b => (if b then q else 1 - q) * f j b)
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine prod_congr rfl fun j _ => ?_
  simp

variable {q}

/-- `n` Bernoulli trials with success probability `q ∈ [0,1]` as a finite probability space on
`Fin n → Bool`. -/
def bernoulliSpace (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinProbSpace (Fin n → Bool) where
  p := bernoulliWeight n q
  p_nonneg ω := prod_nonneg fun i _ => by
    split_ifs
    · exact h0
    · linarith
  sum_p := by
    have := sum_bernoulliWeight_mul_prod n q (fun _ _ => 1)
    simpa using this

variable (h0 : 0 ≤ q) (h1 : q ≤ 1)
include h0 h1

/-- The indicator of success at trial `i`. -/
private noncomputable def succ {n : ℕ} (i : Fin n) (ω : Fin n → Bool) : ℝ := if ω i = true then 1 else 0

omit h0 h1 in
/-- The number of successes is the sum of the trial indicators. -/
private lemma card_eq_sum (ω : Fin n → Bool) :
    (((univ.filter fun i => ω i = true).card : ℕ) : ℝ) = ∑ i, succ i ω := by
  simp only [succ, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private lemma expect_prod_succ (T : Finset (Fin n)) :
    (bernoulliSpace n h0 h1).expect (fun ω => ∏ j ∈ T, succ j ω) = q ^ T.card := by
  have h := sum_bernoulliWeight_mul_prod n q
    (fun j b => if j ∈ T then (if b = true then (1 : ℝ) else 0) else 1)
  have e1 : ∀ ω : Fin n → Bool, ∏ j ∈ T, succ j ω
      = ∏ j, (if j ∈ T then (if ω j = true then (1 : ℝ) else 0) else 1) := fun ω => by
    rw [Finset.prod_ite_mem]
    simp [succ]
  have e2 : ∀ j : Fin n, (q * (if j ∈ T then (if true = true then (1 : ℝ) else 0) else 1)
      + (1 - q) * (if j ∈ T then (if false = true then (1 : ℝ) else 0) else 1))
        = if j ∈ T then q else 1 := fun j => by
    by_cases hj : j ∈ T <;> simp [hj]
  rw [prod_congr rfl (fun j _ => e2 j), Finset.prod_ite_mem] at h
  simp only [prod_const, univ_inter] at h
  simp_rw [e1]
  exact h

/-- CO-241. Example 10.18: the expected number of successes in `n` Bernoulli trials with success
probability `q` is `n q`. -/
@[kb "kellertrotter2017" "Example 10.18, p. 244"]
theorem expect_successes :
    (bernoulliSpace n h0 h1).expect
      (fun ω => (((univ.filter fun i => ω i = true).card : ℕ) : ℝ)) = n * q := by
  simp_rw [card_eq_sum]
  rw [FinProbSpace.expect_finset_sum]
  have : ∀ i : Fin n, (bernoulliSpace n h0 h1).expect (succ i) = q := fun i => by
    have := expect_prod_succ n h0 h1 {i}
    simpa using this
  simp [this]

private lemma expect_succ_mul (i k : Fin n) :
    (bernoulliSpace n h0 h1).expect (fun ω => succ i ω * succ k ω)
      = if i = k then q else q ^ 2 := by
  by_cases hik : i = k
  · subst hik
    have := expect_prod_succ n h0 h1 {i}
    simp only [prod_singleton, card_singleton, pow_one] at this
    have e : ∀ ω : Fin n → Bool, succ i ω * succ i ω = succ i ω := fun ω => by
      unfold succ; split_ifs <;> simp
    simp_rw [e]
    simpa using this
  · have := expect_prod_succ n h0 h1 {i, k}
    rw [card_pair hik] at this
    simpa [prod_pair hik, hik] using this

/-- CO-245. Example 10.22: the variance of the number of successes in `n` Bernoulli trials with
success probability `q` is `n q (1 - q)`. -/
@[kb "kellertrotter2017" "Example 10.22, p. 246"]
theorem variance_successes :
    (bernoulliSpace n h0 h1).variance
      (fun ω => (((univ.filter fun i => ω i = true).card : ℕ) : ℝ)) = n * q * (1 - q) := by
  rw [FinProbSpace.variance_eq, expect_successes n h0 h1]
  simp_rw [card_eq_sum]
  have e : ∀ ω : Fin n → Bool, (∑ i, succ i ω) ^ 2 = ∑ i, ∑ k, succ i ω * succ k ω := fun ω => by
    rw [sq, sum_mul_sum]
  simp_rw [e]
  rw [FinProbSpace.expect_finset_sum]
  simp_rw [FinProbSpace.expect_finset_sum, expect_succ_mul n h0 h1]
  have : ∀ i : Fin n, ∑ k : Fin n, (if i = k then q else q ^ 2) = q + (n - 1) * q ^ 2 := fun i => by
    have : ∀ k : Fin n, (if i = k then q else q ^ 2) = q ^ 2 + (if i = k then q - q ^ 2 else 0) :=
      fun k => by split_ifs <;> ring
    simp_rw [this, sum_add_distrib]
    simp
    ring
  simp_rw [this]
  simp
  ring

end Bernoulli

end UndergradKB.Combinatorics.Probability
