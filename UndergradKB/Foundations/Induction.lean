import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Induction and sequences (gap rows)

Closed forms by induction, strong induction, recurrences determining sequences,
arithmetic and geometric sequences, differences, and a chocolate-bar break count.
-/

namespace UndergradKB.Foundations

open Finset
open scoped Nat

/-- FO-178. The sum of the first `n` odd numbers is `n ^ 2`. -/
@[kb "hammack2018" "Prop §10.1, p. 194"]
theorem hammack_s10_1_sum_odds (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

/-- FO-180. `0·0! + 1·1! + ... + n·n! = (n+1)! - 1`. -/
@[kb "hammack2018" "Prop §10.1, p. 196"]
theorem hammack_s10_1_sum_mul_factorial (n : ℕ) :
    ∑ i ∈ range (n + 1), i * i ! = (n + 1)! - 1 := by
  have h : ∀ n : ℕ, ∑ i ∈ range (n + 1), i * i ! + 1 = (n + 1)! := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, Nat.factorial_succ (n + 1)]
      nlinarith [ih]
  have := h n
  omega

/-- FO-185. Every postage of 8 cents or more can be made with 3-cent and 5-cent stamps
(strong induction). -/
@[kb "hammack2018" "Prop §10.2, p. 199"]
theorem hammack_s10_2_stamps (n : ℕ) (hn : 8 ≤ n) : ∃ a b : ℕ, n = 3 * a + 5 * b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h8 : n = 8
    · exact ⟨1, 1, by omega⟩
    by_cases h9 : n = 9
    · exact ⟨3, 0, by omega⟩
    by_cases h10 : n = 10
    · exact ⟨0, 2, by omega⟩
    obtain ⟨a, b, hab⟩ := ih (n - 3) (by omega) (by omega)
    exact ⟨a + 1, b, by omega⟩

/-- FO-191. `F(n+1)^2 - F(n+1) F(n) - F(n)^2 = (-1)^n` for Fibonacci numbers. -/
@[kb "hammack2018" "Prop §10.5, p. 206"]
theorem hammack_s10_5_fib_identity (n : ℕ) :
    ((Nat.fib (n + 1) : ℤ)) ^ 2 - Nat.fib (n + 1) * Nat.fib n - (Nat.fib n : ℤ) ^ 2 =
      (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    rw [h, pow_succ (-1 : ℤ) n, ← ih]
    push_cast
    ring

/-- FO-196. A recurrence of order `k` together with the first `k` terms determines the
sequence: two sequences with the same initial terms and the same recurrence agree. -/
@[kb "levin2025" "Def 4.1.5, p. 334", kb "levin2025" "Example 4.1.8, p. 336"]
theorem levin_def_4_1_5_recurrence_determines {α : Type*} (k : ℕ)
    (G : ℕ → (Fin k → α) → α) (a b : ℕ → α)
    (hinit : ∀ i < k, a i = b i)
    (ha : ∀ n, a (n + k) = G n (fun i => a (n + i)))
    (hb : ∀ n, b (n + k) = G n (fun i => b (n + i))) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < k
    · exact hinit n hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
      rw [ha, hb]
      congr 1
      funext i
      exact ih (m + i) (by have := i.2; omega)

/-- FO-196 (two-term case). A two-term recurrence with initial terms `a 0`, `a 1` determines
the sequence. -/
@[kb "levin2025" "Def 4.1.5, p. 334", kb "levin2025" "Example 4.1.8, p. 336"]
theorem levin_def_4_1_5_two_term_determines {α : Type*} (g : ℕ → α → α → α) (a b : ℕ → α)
    (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (ha : ∀ n, a (n + 2) = g n (a n) (a (n + 1)))
    (hb : ∀ n, b (n + 2) = g n (b n) (b (n + 1))) : a = b := by
  refine levin_def_4_1_5_recurrence_determines 2 (fun n v => g n (v 0) (v 1)) a b ?_ ?_ ?_
  · intro i hi
    interval_cases i
    · exact h0
    · exact h1
  · intro n; exact ha n
  · intro n; exact hb n

/-- FO-197. A sequence is its first term plus the partial sums of its differences:
`a n = a 0 + ∑_{i<n} (a (i+1) - a i)`, and conversely partial sums of `d` satisfy
`s (n+1) = s n + d n`. -/
@[kb "levin2025" "Example 4.1.10, p. 340", kb "levin2025" "Differences §4.1.3, p. 341"]
theorem levin_s4_1_3_differences_partial_sums (a : ℕ → ℤ) (d : ℕ → ℤ) (n : ℕ) :
    a n = a 0 + ∑ i ∈ range n, (a (i + 1) - a i) ∧
      (∑ i ∈ range (n + 1), d i) = (∑ i ∈ range n, d i) + d n := by
  refine ⟨?_, sum_range_succ d n⟩
  rw [sum_range_sub (fun i => a i) n]
  ring

/-- FO-199. Arithmetic sequence: a constant difference `d` gives `a n = a 0 + n d`
(and `b n = b 1 + (n - 1) d` when indexed from 1). -/
@[kb "levin2025" "Arithmetic Sequences, p. 349", kb "levin2025" "Example 4.2.2, p. 350",
  kb "levin2025" "Remark 4.2.4, p. 352"]
theorem levin_s4_2_arithmetic_closed_form {R : Type*} [Ring R] (a : ℕ → R) (d : R)
    (h : ∀ n, a (n + 1) = a n + d) :
    (∀ n, a n = a 0 + n * d) ∧ (∀ n, a (n + 1) = a 1 + n * d) := by
  have h0 : ∀ n, a n = a 0 + n * d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [h, ih]; push_cast; noncomm_ring
  refine ⟨h0, fun n => ?_⟩
  rw [h0 (n + 1), h0 1]
  push_cast
  noncomm_ring

/-- FO-200. Geometric sequence: a constant ratio `r` gives `a n = a 0 * r ^ n`. -/
@[kb "levin2025" "Geometric Sequences, p. 351", kb "levin2025" "Example 4.2.3, p. 351"]
theorem levin_s4_2_geometric_closed_form {R : Type*} [CommSemiring R] (a : ℕ → R) (r : R)
    (h : ∀ n, a (n + 1) = r * a n) : ∀ n, a n = a 0 * r ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [h, ih]; ring

/-- FO-201. Sum of a finite arithmetic sequence (reverse and add):
twice the sum of the `N + 1` terms is `(N + 1)` times (first + last). -/
@[kb "levin2025" "Reverse and Add §4.3.2, p. 360", kb "levin2025" "Example 4.3.2, p. 360"]
theorem levin_s4_3_2_arithmetic_sum {R : Type*} [CommRing R] (a : ℕ → R) (d : R)
    (h : ∀ n, a (n + 1) = a n + d) (N : ℕ) :
    2 * ∑ i ∈ range (N + 1), a i = (N + 1) * (a 0 + a N) := by
  have h0 := (levin_s4_2_arithmetic_closed_form a d h).1
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, h0 N, h0 (N + 1)]
    push_cast
    ring

/-- FO-202. A sequence is `Δ^k`-constant when its `k`-th differences are constant. -/
def IsDeltaConstant {G : Type*} [AddCommGroup G] (k : ℕ) (a : ℕ → G) : Prop :=
  ∃ c : G, ∀ n, ((fwdDiff (1 : ℕ))^[k] a) n = c

/-- FO-202. `Δ^0`-constant means constant, and `Δ^(k+1)`-constant means the first differences
are `Δ^k`-constant; a `Δ^k`-constant sequence is `Δ^(k+1)`-constant; the squares are
`Δ^2`-constant. -/
@[kb "levin2025" "Def §4.3.3, p. 363", kb "levin2025" "Example 4.3.5, p. 363"]
theorem levin_s4_3_3_delta_constant (a : ℕ → ℤ) :
    (IsDeltaConstant 0 a ↔ ∃ c, ∀ n, a n = c) ∧
    (∀ k, IsDeltaConstant (k + 1) a ↔ IsDeltaConstant k (fwdDiff (1 : ℕ) a)) ∧
    (∀ k, IsDeltaConstant k a → IsDeltaConstant (k + 1) a) ∧
    IsDeltaConstant 2 (fun n => (n : ℤ) ^ 2) := by
  refine ⟨Iff.rfl, fun k => ?_, fun k ⟨c, hc⟩ => ⟨0, fun n => ?_⟩, ⟨2, fun n => ?_⟩⟩
  · unfold IsDeltaConstant
    rw [Function.iterate_succ]
    rfl
  · rw [Function.iterate_succ_apply']
    simp [fwdDiff, hc]
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, fwdDiff]
    push_cast
    ring

/-- FO-205. `1² + 2² + ... + n² = n (n + 1) (2n + 1) / 6`. -/
@[kb "hammack2018" "Exercise 2 §10, p. 207", kb "levin2025" "Example 4.3.8, p. 365"]
theorem hammack_ex_s10_sum_squares (n : ℕ) :
    6 * ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) ∧
      ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  have h : ∀ n : ℕ, 6 * ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, mul_add, ih]; ring
  refine ⟨h n, ?_⟩
  rw [← h n]
  omega

/-- A way of breaking a rectangular chocolate bar of `a × b` squares into single squares:
either it is a single square, or it is broken once along a column line into an `a × b` and an
`a' × b` bar, or along a row line into `a × b` and `a × b'` bars, each of which is then broken
further independently. -/
inductive BreakPlan : ℕ → ℕ → Type
  | single : BreakPlan 1 1
  | cutCols {a a' b : ℕ} : BreakPlan a b → BreakPlan a' b → BreakPlan (a + a') b
  | cutRows {a b b' : ℕ} : BreakPlan a b → BreakPlan a b' → BreakPlan a (b + b')

/-- The number of breaks used by a plan. -/
def BreakPlan.breaks : {a b : ℕ} → BreakPlan a b → ℕ
  | _, _, .single => 0
  | _, _, .cutCols p q => p.breaks + q.breaks + 1
  | _, _, .cutRows p q => p.breaks + q.breaks + 1

/-- FO-211. Any plan that reduces an `a × b` bar to single squares uses exactly `a b - 1`
breaks, and such a plan exists for every nonempty bar. -/
@[kb "levin2025" "Proposition 4.6.3, p. 400"]
theorem levin_prop_4_6_3_chocolate :
    (∀ {a b : ℕ} (p : BreakPlan a b), p.breaks + 1 = a * b) ∧
      ∀ a b : ℕ, 0 < a → 0 < b → Nonempty (BreakPlan a b) := by
  constructor
  · intro a b p
    induction p with
    | single => rfl
    | cutCols p q ihp ihq => simp only [BreakPlan.breaks]; nlinarith [ihp, ihq]
    | cutRows p q ihp ihq => simp only [BreakPlan.breaks]; nlinarith [ihp, ihq]
  · have row : ∀ b : ℕ, Nonempty (BreakPlan 1 (b + 1)) := by
      intro b
      induction b with
      | zero => exact ⟨.single⟩
      | succ b ih => obtain ⟨p⟩ := ih; exact ⟨.cutRows p .single⟩
    intro a b ha hb
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    induction a with
    | zero => exact row b
    | succ a ih =>
      obtain ⟨p⟩ := ih (by omega)
      obtain ⟨q⟩ := row b
      exact ⟨.cutCols p q⟩

/-- FO-212. `n ^ 2 < 2 ^ n` for all `n ≥ 5`. -/
@[kb "levin2025" "Example 4.5.4, p. 388"]
theorem levin_ex_4_5_4_sq_lt_two_pow (n : ℕ) (hn : 5 ≤ n) : n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ (2 : ℕ) n]; nlinarith [ih, hn]

end UndergradKB.Foundations
