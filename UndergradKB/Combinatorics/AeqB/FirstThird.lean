import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-!
# The sum of the first third of the binomial coefficients: an exact difference equation

Let `S(n) = ∑_{k ≤ n} C(3n, k)` and `T(n) = C(3n, n)`.  Repeated use of Pascal's rule gives
`S(n+1) = 8 S(n) + C(3n, n+1) - 4 C(3n, n) - C(3n, n-1)`, and the ratios of neighbouring binomial
coefficients turn this into the identity
`(n+1)(2n+1) (S(n+1) - 8 S(n)) = - (5n² + 11n + 4) T(n)`,
where `T(n+1)` is a rational multiple of `T(n)`.  Eliminating `T` yields a recurrence of order two for
`S`.  All identities are stated in `ℕ` (with the negative terms moved across) so that they transfer
to any field of characteristic zero.
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset

/-- `ftR N m = ∑_{k < m} C(N, k)`, a partial row sum of Pascal's triangle. -/
def ftR (N m : ℕ) : ℕ := ∑ k ∈ range m, N.choose k

/-- The sum of the first third of the binomial coefficients `∑_{k ≤ n} C(3n, k)`. -/
def ftS (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (3 * n).choose k

lemma ftS_eq (n : ℕ) : ftS n = ftR (3 * n) (n + 1) := rfl

lemma ftR_succ_right (N m : ℕ) : ftR N (m + 1) = ftR N m + N.choose m := by
  simp [ftR, Finset.sum_range_succ]

lemma ftR_succ (N m : ℕ) : ftR (N + 1) (m + 1) = ftR N (m + 1) + ftR N m := by
  induction m with
  | zero => simp [ftR]
  | succ m ih =>
    have hp := Nat.choose_succ_succ' N m
    rw [ftR_succ_right (N + 1) (m + 1), ih, ftR_succ_right N (m + 1), ftR_succ_right N m]
    omega

/-- Pascal's rule thrice: the passage from `n` to `n + 1` (written for `n = k + 1`). -/
lemma ftS_step (k : ℕ) :
    ftS (k + 2) + 4 * (3 * (k + 1)).choose (k + 1) + (3 * (k + 1)).choose k
      = 8 * ftS (k + 1) + (3 * (k + 1)).choose (k + 2) := by
  have e3 : 3 * (k + 2) = 3 * (k + 1) + 3 := by ring
  rw [ftS_eq, ftS_eq, e3]
  generalize hN : 3 * (k + 1) = N
  show ftR (N + 3) (k + 3) + 4 * N.choose (k + 1) + N.choose k
    = 8 * ftR N (k + 2) + N.choose (k + 2)
  have a1 : ftR (N + 3) (k + 3) = ftR (N + 2) (k + 3) + ftR (N + 2) (k + 2) :=
    ftR_succ (N + 2) (k + 2)
  have a2 : ftR (N + 2) (k + 3) = ftR (N + 1) (k + 3) + ftR (N + 1) (k + 2) :=
    ftR_succ (N + 1) (k + 2)
  have a3 : ftR (N + 2) (k + 2) = ftR (N + 1) (k + 2) + ftR (N + 1) (k + 1) :=
    ftR_succ (N + 1) (k + 1)
  have a4 : ftR (N + 1) (k + 3) = ftR N (k + 3) + ftR N (k + 2) := ftR_succ N (k + 2)
  have a5 : ftR (N + 1) (k + 2) = ftR N (k + 2) + ftR N (k + 1) := ftR_succ N (k + 1)
  have a6 : ftR (N + 1) (k + 1) = ftR N (k + 1) + ftR N k := ftR_succ N k
  have b1 : ftR N (k + 3) = ftR N (k + 2) + N.choose (k + 2) := ftR_succ_right N (k + 2)
  have b2 : ftR N (k + 2) = ftR N (k + 1) + N.choose (k + 1) := ftR_succ_right N (k + 1)
  have b3 : ftR N (k + 1) = ftR N k + N.choose k := ftR_succ_right N k
  omega

lemma ftT_ratio1 (n : ℕ) :
    (n + 1) * (3 * n).choose (n + 1) = 2 * n * (3 * n).choose n := by
  have h := Nat.choose_succ_right_eq (3 * n) n
  have e : 3 * n - n = 2 * n := by omega
  rw [e] at h
  linarith

lemma ftT_ratio2 (k : ℕ) :
    (3 * (k + 1)).choose k * (2 * (k + 1) + 1)
      = (3 * (k + 1)).choose (k + 1) * (k + 1) := by
  have h := Nat.choose_succ_right_eq (3 * (k + 1)) k
  have e : 3 * (k + 1) - k = 2 * (k + 1) + 1 := by omega
  rw [e] at h
  linarith

/-- The exact difference equation, in `ℕ`:
`(n+1)(2n+1) S(n+1) + (5n²+11n+4) C(3n,n) = 8 (n+1)(2n+1) S(n)`. -/
lemma ftS_diff (n : ℕ) :
    (n + 1) * (2 * n + 1) * ftS (n + 1) + (5 * n ^ 2 + 11 * n + 4) * (3 * n).choose n
      = 8 * ((n + 1) * (2 * n + 1)) * ftS n := by
  rcases n with _ | k
  · decide
  · have h := ftS_step k
    have r1 := ftT_ratio1 (k + 1)
    have r2 := ftT_ratio2 k
    set S1 := ftS (k + 2)
    set S0 := ftS (k + 1)
    set T := (3 * (k + 1)).choose (k + 1)
    set c1 := (3 * (k + 1)).choose (k + 2)
    set cm := (3 * (k + 1)).choose k
    -- multiply the step relation by `(n+1)(2n+1)` and eliminate `c1`, `cm`
    have : ((k + 1 + 1) * (2 * (k + 1) + 1)) * (S1 + 4 * T + cm)
        = ((k + 1 + 1) * (2 * (k + 1) + 1)) * (8 * S0 + c1) := by rw [h]
    have e1 : (k + 1 + 1) * (2 * (k + 1) + 1) * c1 = 2 * (k + 1) * (2 * (k + 1) + 1) * T := by
      calc (k + 1 + 1) * (2 * (k + 1) + 1) * c1
          = ((k + 1 + 1) * c1) * (2 * (k + 1) + 1) := by ring
        _ = (2 * (k + 1) * T) * (2 * (k + 1) + 1) := by rw [r1]
        _ = _ := by ring
    have e2 : (k + 1 + 1) * (2 * (k + 1) + 1) * cm = (k + 1 + 1) * (k + 1) * T := by
      calc (k + 1 + 1) * (2 * (k + 1) + 1) * cm
          = (k + 1 + 1) * (cm * (2 * (k + 1) + 1)) := by ring
        _ = (k + 1 + 1) * (T * (k + 1)) := by rw [r2]
        _ = _ := by ring
    nlinarith [this, e1, e2]

lemma ftT_ratio3 (n : ℕ) :
    (3 * (n + 1)).choose (n + 1) * (2 * ((n + 1) * (2 * n + 1)))
      = 3 * ((3 * n + 1) * (3 * n + 2)) * (3 * n).choose n := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 3 * (n + 1) by omega)
  have e1 : 3 * n - n = 2 * n := by omega
  have e2 : 3 * (n + 1) - (n + 1) = 2 * n + 2 := by omega
  rw [e1] at h1
  rw [e2] at h2
  have f1 : (3 * (n + 1)).factorial = (3 * n + 3) * ((3 * n + 2) * ((3 * n + 1) * (3 * n).factorial)) := by
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
  have f2 : (2 * n + 2).factorial = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  rw [f1, Nat.factorial_succ n, f2, ← h1] at h2
  have hpos : 0 < n.factorial * (2 * n).factorial * (n + 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.succ_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  nlinarith [h2]

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The exact difference equation, over a field of characteristic zero. -/
lemma ftS_diff_K (n : ℕ) :
    ((n : K) + 1) * (2 * n + 1) * (ftS (n + 1) : K) + (5 * (n : K) ^ 2 + 11 * n + 4)
      * ((3 * n).choose n : K) = 8 * (((n : K) + 1) * (2 * n + 1)) * (ftS n : K) := by
  exact_mod_cast ftS_diff n

lemma ftT_ratio3_K (n : ℕ) :
    ((3 * (n + 1)).choose (n + 1) : K) * (2 * (((n : K) + 1) * (2 * n + 1)))
      = 3 * ((3 * (n : K) + 1) * (3 * n + 2)) * ((3 * n).choose n : K) := by
  exact_mod_cast ftT_ratio3 n

/-- The order-two recurrence for `S(n) = ∑_{k ≤ n} C(3n, k)`:
`24 (3n+1)(3n+2)(5n²+21n+20) S(n) - (8 A(n) + 3(3n+1)(3n+2)(5n²+21n+20)) S(n+1) + A(n) S(n+2) = 0`
with `A(n) = 2 (n+2)(2n+3)(5n²+11n+4)`. -/
lemma ftS_rec_K (n : ℕ) :
    24 * ((3 * (n : K) + 1) * (3 * n + 2) * (5 * n ^ 2 + 21 * n + 20)) * (ftS n : K)
      - (8 * (2 * ((n : K) + 2) * (2 * n + 3) * (5 * n ^ 2 + 11 * n + 4))
        + 3 * ((3 * (n : K) + 1) * (3 * n + 2) * (5 * n ^ 2 + 21 * n + 20))) * (ftS (n + 1) : K)
      + (2 * ((n : K) + 2) * (2 * n + 3) * (5 * n ^ 2 + 11 * n + 4)) * (ftS (n + 2) : K) = 0 := by
  have hD0 := ftS_diff_K (K := K) n
  have hD1 := ftS_diff_K (K := K) (n + 1)
  have hT := ftT_ratio3_K (K := K) n
  push_cast at hD1
  have hu : (((n : K) + 1) * (2 * n + 1)) ≠ 0 := by
    have : ((((n + 1) * (2 * n + 1) : ℕ)) : K) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
    push_cast at this
    exact this
  refine mul_left_cancel₀ hu ?_
  rw [mul_zero]
  have hD1' : ((n : K) + 1 + 1) * (2 * ((n : K) + 1) + 1) * (ftS (n + 2) : K)
      + (5 * ((n : K) + 1) ^ 2 + 11 * ((n : K) + 1) + 4) * ((3 * (n + 1)).choose (n + 1) : K)
      = 8 * (((n : K) + 1 + 1) * (2 * ((n : K) + 1) + 1)) * (ftS (n + 1) : K) := hD1
  linear_combination (2 * (((n : K) + 1) * (2 * n + 1)) * (5 * (n : K) ^ 2 + 11 * n + 4)) * hD1'
    - (3 * ((3 * (n : K) + 1) * (3 * n + 2)) * (5 * (n : K) ^ 2 + 21 * n + 20)) * hD0
    - ((5 * (n : K) ^ 2 + 11 * n + 4) * (5 * (n : K) ^ 2 + 21 * n + 20)) * hT

end Field

end UndergradKB.Combinatorics.AeqB
