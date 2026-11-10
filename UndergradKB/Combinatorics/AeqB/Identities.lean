import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB
open Finset Polynomial

/-- CO-047. `∑_k k * C(n,k) = n * 2^(n-1)` (here for all `n : ℕ`, natural subtraction). -/
@[kb "petkovsekwilfzeilberger1996" "Example 4.1.1, p. 65"]
theorem sum_mul_choose (n : ℕ) : ∑ k ∈ range (n + 1), k * n.choose k = n * 2 ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [sum_range_succ']
    simp only [zero_mul, add_zero]
    have : ∀ j ∈ range (m + 1), (j + 1) * (m + 1).choose (j + 1) = (m + 1) * m.choose j :=
      fun j _ => by rw [mul_comm, ← Nat.add_one_mul_choose_eq]
    rw [sum_congr rfl this, ← mul_sum, Nat.sum_range_choose]
    simp

theorem neg_one_pow_sub_even (n i : ℕ) (hi : i ≤ 2 * n) :
    (-1 : ℤ) ^ (2 * n - i) = (-1) ^ i := by
  have h : (-1 : ℤ) ^ (2 * n - i) * (-1) ^ i = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hi, pow_mul]; simp
  have h2 : ((-1 : ℤ) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow]; simp
  calc (-1 : ℤ) ^ (2 * n - i) = (-1) ^ (2 * n - i) * ((-1) ^ i * (-1) ^ i) := by rw [h2, mul_one]
    _ = ((-1) ^ (2 * n - i) * (-1) ^ i) * (-1) ^ i := by ring
    _ = (-1) ^ i := by rw [h, one_mul]

/-- CO-045. `∑_k (-1)^k C(2n,k)^2 = (-1)^n C(2n,n)`. Proof: the coefficient of `X^(2n)` in
`(X-1)^(2n) (X+1)^(2n) = (X^2-1)^(2n)`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 3.6.1, p. 55"]
theorem alt_sum_choose_sq (n : ℕ) :
    ∑ k ∈ range (2 * n + 1), (-1 : ℤ) ^ k * ((2 * n).choose k : ℤ) ^ 2
      = (-1) ^ n * ((2 * n).choose n : ℤ) := by
  have hP : ((X + C (-1 : ℤ)) ^ (2 * n) * (X + 1) ^ (2 * n)).coeff (2 * n)
      = ∑ k ∈ range (2 * n + 1), (-1 : ℤ) ^ k * ((2 * n).choose k : ℤ) ^ 2 := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 2 * n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [coeff_X_add_C_pow, coeff_X_add_one_pow, Nat.choose_symm hk', neg_one_pow_sub_even n k hk']
    push_cast; ring
  have h2 : (X + C (-1 : ℤ)) ^ (2 * n) * (X + 1) ^ (2 * n)
      = expand ℤ 2 ((X + C (-1 : ℤ)) ^ (2 * n)) := by
    rw [← mul_pow, map_pow]
    congr 1
    simp only [map_add, expand_X, map_neg, map_one]
    ring
  rw [← hP, h2, coeff_expand (by norm_num)]
  simp only [dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [coeff_X_add_C_pow]
  have : 2 * n - n = n := by omega
  rw [this]

/-- CO-048. Reed–Dawson identity: `∑_k C(n,k) C(2k,k) (-2)^(n-k)` is `0` for odd `n` and
`C(n, n/2)` for even `n`. Proof: the coefficient of `X^n` in `((1+X)^2 - 2X)^n = (1+X^2)^n`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 4.3.3, p. 73"]
theorem reed_dawson (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * ((2 * k).choose k : ℤ) * (-2) ^ (n - k)
      = if 2 ∣ n then (n.choose (n / 2) : ℤ) else 0 := by
  have h1 : (((1 + X : ℤ[X]) ^ 2 + C (-2) * X) ^ n).coeff n
      = ∑ k ∈ range (n + 1), (n.choose k : ℤ) * ((2 * k).choose k : ℤ) * (-2) ^ (n - k) := by
    rw [add_pow, finsetSum_coeff]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have : ((1 + X : ℤ[X]) ^ 2) ^ k * (C (-2) * X) ^ (n - k) * (n.choose k : ℤ[X])
        = C ((-2) ^ (n - k) * (n.choose k : ℤ)) * (X ^ (n - k) * ((1 + X) ^ 2) ^ k) := by
      rw [show (n.choose k : ℤ[X]) = C (n.choose k : ℤ) by simp, C_mul, C_pow]
      ring
    rw [this, coeff_C_mul, coeff_X_pow_mul', if_pos (Nat.sub_le n k), Nat.sub_sub_self hk',
      ← pow_mul, coeff_one_add_X_pow]
    ring
  have h2 : ((1 + X : ℤ[X]) ^ 2 + C (-2) * X) = expand ℤ 2 (1 + X) := by
    simp only [map_add, map_one, expand_X]
    have : (C (-2 : ℤ) : ℤ[X]) = -2 := by simp
    rw [this]; ring
  rw [← h1, h2, ← map_pow, coeff_expand (by norm_num), coeff_one_add_X_pow]

/-- Integer form of CO-379: `∑_k C(n,2k) C(2k,k) 2^(n-2k) = C(2n,n)`. -/
theorem sum_choose_two_mul_centralBinom (n : ℕ) :
    ∑ m ∈ range (n + 1), n.choose (2 * m) * (2 * m).choose m * 2 ^ (n - 2 * m)
      = (2 * n).choose n := by
  have h1 : (((X * (X + C 2) + 1 : ℕ[X])) ^ n).coeff n
      = ∑ k ∈ range (n + 1), n.choose k * (2 ^ (k - (n - k)) * k.choose (n - k)) := by
    rw [add_pow, finsetSum_coeff]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have : (X * (X + C 2)) ^ k * 1 ^ (n - k) * (n.choose k : ℕ[X])
        = C (n.choose k) * (X ^ k * (X + C 2) ^ k) := by
      rw [one_pow, mul_pow, show (n.choose k : ℕ[X]) = C (n.choose k) by simp]
      ring
    rw [this, coeff_C_mul, coeff_X_pow_mul', if_pos hk', coeff_X_add_C_pow, Nat.cast_id]
  have h2 : (X * (X + C 2) + 1 : ℕ[X]) = (1 + X) ^ 2 := by
    have : (C 2 : ℕ[X]) = 2 := by simp
    rw [this]; ring
  have h3 : (2 * n).choose n
      = ∑ k ∈ range (n + 1), n.choose k * (2 ^ (k - (n - k)) * k.choose (n - k)) := by
    rw [← h1, h2, ← pow_mul, coeff_one_add_X_pow, Nat.cast_id]
  rw [h3]
  have h4 := sum_range_reflect (fun k => n.choose k * (2 ^ (k - (n - k)) * k.choose (n - k))) (n + 1)
  simp only [Nat.add_sub_cancel] at h4
  rw [← h4]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hm)
  have e := Nat.choose_mul (n := n) (k := 2 * m) (s := m) (by omega)
  have e2 : 2 * m - m = m := by omega
  rw [e2] at e
  simp only [Nat.sub_sub_self hm', Nat.choose_symm hm']
  have e3 : n - m - m = n - 2 * m := by omega
  rw [e3]
  calc n.choose (2 * m) * (2 * m).choose m * 2 ^ (n - 2 * m)
      = n.choose m * (n - m).choose m * 2 ^ (n - 2 * m) := by rw [e]
    _ = _ := by ring

/-- CO-379. `∑_k C(n,2k) C(2k,k) 4^(-k) = 2^(-(n-1)) C(2n-1,n-1)` for `n ≥ 1`, written with
`n = m + 1`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 123"]
theorem sum_choose_two_mul_centralBinom_div (m : ℕ) :
    ∑ k ∈ range (m + 2), ((m + 1).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) / 4 ^ k
      = ((2 * m + 1).choose m : ℚ) / 2 ^ m := by
  have h := sum_choose_two_mul_centralBinom (m + 1)
  have hq : ∑ k ∈ range (m + 2), ((m + 1).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ)
      * 2 ^ (m + 1 - 2 * k) = ((2 * (m + 1)).choose (m + 1) : ℚ) := by exact_mod_cast h
  have h5 : ∀ k ∈ range (m + 2), ((m + 1).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) / 4 ^ k
      = ((m + 1).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) * 2 ^ (m + 1 - 2 * k)
        / 2 ^ (m + 1) := by
    intro k _
    by_cases hk : 2 * k ≤ m + 1
    · have : (2 : ℚ) ^ (m + 1) = 2 ^ (m + 1 - 2 * k) * 4 ^ k := by
        rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
        congr 1; omega
      rw [this]; field_simp
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [sum_congr rfl h5]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hq, ← div_eq_mul_inv]
  have h6 : (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1).choose m := by
    have := Nat.choose_succ_succ' (2 * m + 1) m
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, this,
      show (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m by
        rw [← Nat.choose_symm (show m ≤ 2 * m + 1 by omega)]; congr 1; omega]
    ring
  rw [h6]; push_cast
  rw [pow_succ]; field_simp

/-- The finite-sum (natural-number indexed) form of the WZ argument: if `F(n+1,k) - F(n,k) =
G(n,k+1) - G(n,k)`, `F n k = 0` for `k > n`, `G n 0 = 0` and `G n (n+2) = 0`, then
`∑_{k ≤ n} F n k = F 0 0`. -/
theorem sum_range_eq_of_wz {E : Type*} [AddCommGroup E] {F G : ℕ → ℕ → E}
    (h : ∀ n k, F (n + 1) k - F n k = G n (k + 1) - G n k)
    (hF : ∀ n k, n < k → F n k = 0) (hG0 : ∀ n, G n 0 = 0) (hG1 : ∀ n, G n (n + 2) = 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), F n k = F 0 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ k ∈ range (n + 2), F (n + 1) k = ∑ k ∈ range (n + 2), F n k := by
      have : ∑ k ∈ range (n + 2), (F (n + 1) k - F n k) = 0 := by
        simp_rw [h n]
        rw [sum_range_sub (G n) (n + 2), hG1, hG0, sub_self]
      rw [sum_sub_distrib, sub_eq_zero] at this; exact this
    rw [h1, sum_range_succ, hF n (n + 1) (by omega), add_zero]; exact ih

/-- Summand of the dual identity CO-460 (the book's `F'` up to the factor `2`). -/
def dualF (n k : ℕ) : ℤ := (3 * (k : ℤ) - 2 * n) * (n.choose k : ℤ) ^ 2 * ((2 * k).choose k : ℤ)

/-- WZ mate of `dualF` (the book's `G'` up to the factor `-2`). -/
def dualG (n k : ℕ) : ℤ := -((k : ℤ) * (n.choose (k - 1) : ℤ) ^ 2 * ((2 * k).choose k : ℤ))

/-- `(j+1) C(n,j+1) = (n-j) C(n,j)` in any commutative ring, with `n - j` computed in the ring. -/
theorem choose_succ_right_cast (R : Type*) [CommRing R] (n j : ℕ) :
    ((j : R) + 1) * (n.choose (j + 1) : R) = ((n : R) - j) * (n.choose j : R) := by
  by_cases hj : j ≤ n
  · have := Nat.choose_succ_right_eq n j
    have h2 : ((n.choose (j + 1) * (j + 1) : ℕ) : R) = ((n.choose j * (n - j) : ℕ) : R) := by
      rw [this]
    push_cast [Nat.cast_sub hj] at h2
    linear_combination h2
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem dual_wz (n k : ℕ) : dualF (n + 1) k - dualF n k = dualG n (k + 1) - dualG n k := by
  cases k with
  | zero => simp [dualF, dualG]; ring
  | succ j =>
    have hrel := choose_succ_right_cast ℤ n j
    have hM := Nat.succ_mul_centralBinom_succ (j + 1)
    simp only [Nat.centralBinom_eq_two_mul_choose] at hM
    have hM' : ((j : ℤ) + 1 + 1) * ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℤ)
        = 2 * (2 * ((j : ℤ) + 1) + 1) * ((2 * (j + 1)).choose (j + 1) : ℤ) := by
      exact_mod_cast hM
    simp only [dualF, dualG, Nat.add_sub_cancel, Nat.choose_succ_succ' n j]
    push_cast
    linear_combination (((n.choose (j + 1) : ℤ)) ^ 2) * hM' +
      (((2 * (j + 1)).choose (j + 1) : ℤ) * (4 * (n.choose (j + 1) : ℤ) + 2 * (n.choose j : ℤ))) * hrel

/-- CO-460. The dual of the sum-of-squares identity: `∑_k (3k - 2n) C(n,k)^2 C(2k,k) = 0`.
(The book's displayed formula has `C(n,k)^2`; the audit row omits the square, and without the
square the identity is false, e.g. `n = 2` gives `4`.)  Proved from the WZ pair `dualF, dualG`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.3.5, p. 142"]
theorem sum_dual_squares (n : ℕ) :
    ∑ k ∈ range (n + 1), (3 * (k : ℤ) - 2 * n) * (n.choose k : ℤ) ^ 2 * ((2 * k).choose k : ℤ)
      = 0 := by
  have h := sum_range_eq_of_wz (F := dualF) (G := dualG) dual_wz
    (fun n k hnk => by simp [dualF, Nat.choose_eq_zero_of_lt hnk])
    (fun n => by simp [dualG])
    (fun n => by simp [dualG]) n
  simpa [dualF] using h

/-! ### CO-380: `∑_k C(n+k,2k) C(2k,k) (-1)^k/(k+1)` -/

/-- Algebraic core of the verification of the telescoped recurrence for CO-380. -/
theorem cat_alg (n k P Q R K c a b : ℚ) (hk : 0 < k)
    (r1 : 2 * k * Q = (n - k + 1) * P) (r2 : (2 * k + 1) * R = (n - k) * Q)
    (r3 : (k + 1) * c = K) (r4 : K = 2 * a) (r5 : (k + 1) * b = (2 * k + 1) * K) :
    (n + 1) * (n * (Q * c) - (n + 2) * ((Q + P) * c))
      = -2 * (k + 1) * (Q + R) * b - 2 * k * P * a := by
  have hk0 : k ≠ 0 := hk.ne'
  have hk1 : k + 1 ≠ 0 := by positivity
  have hk2 : 2 * k + 1 ≠ 0 := by positivity
  have hQ : Q = (n - k + 1) * P / (2 * k) := by field_simp; linarith
  have hR : R = (n - k) * Q / (2 * k + 1) := by field_simp; linarith
  have hc : c = K / (k + 1) := by field_simp; linarith
  have ha : a = K / 2 := by linarith
  have hb : b = (2 * k + 1) * K / (k + 1) := by field_simp; linarith
  subst hc ha hb
  rw [hR, hQ]
  field_simp
  ring

theorem cat_alg_int (n k P Q R K c a b : ℤ) (hk : 0 < k)
    (r1 : 2 * k * Q = (n - k + 1) * P) (r2 : (2 * k + 1) * R = (n - k) * Q)
    (r3 : (k + 1) * c = K) (r4 : K = 2 * a) (r5 : (k + 1) * b = (2 * k + 1) * K) :
    (n + 1) * (n * (Q * c) - (n + 2) * ((Q + P) * c))
      = -2 * (k + 1) * (Q + R) * b - 2 * k * P * a := by
  have := cat_alg (n : ℚ) (k : ℚ) P Q R K c a b (by exact_mod_cast hk) (by exact_mod_cast r1)
    (by exact_mod_cast r2) (by exact_mod_cast r3) (by exact_mod_cast r4) (by exact_mod_cast r5)
  exact_mod_cast this

/-- Summand of CO-380 with the Catalan number `C(2k,k)/(k+1)`. -/
def catF (n k : ℕ) : ℤ := (-1) ^ k * ((n + k).choose (2 * k) : ℤ) * (catalan k : ℤ)

/-- WZ-style certificate for `catF`. -/
def catG (n k : ℕ) : ℤ :=
  2 * (-1) ^ k * (k : ℤ) * ((n + k).choose (2 * k - 1) : ℤ) * ((2 * k - 1).choose k : ℤ)

theorem cat_wz (n k : ℕ) :
    ((n : ℤ) + 1) * (n * catF n k - (n + 2) * catF (n + 1) k) = catG n (k + 1) - catG n k := by
  cases k with
  | zero => simp [catF, catG]; ring
  | succ j =>
    have eF1 : (n + (j + 1)).choose (2 * (j + 1)) = (n + (j + 1)).choose (2 * j + 1 + 1) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    have eF2 : (n + 1 + (j + 1)).choose (2 * (j + 1))
        = (n + (j + 1)).choose (2 * j + 1) + (n + (j + 1)).choose (2 * j + 1 + 1) := by
      rw [show n + 1 + (j + 1) = (n + (j + 1)) + 1 by ring,
        show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.choose_succ_succ']
    have eG1 : (n + (j + 1 + 1)).choose (2 * (j + 1 + 1) - 1)
        = (n + (j + 1)).choose (2 * j + 1 + 1) + (n + (j + 1)).choose (2 * j + 1 + 1 + 1) := by
      rw [show n + (j + 1 + 1) = (n + (j + 1)) + 1 by ring,
        show 2 * (j + 1 + 1) - 1 = (2 * j + 1 + 1) + 1 by omega, Nat.choose_succ_succ']
    have eG2 : (2 * (j + 1 + 1) - 1).choose (j + 1 + 1) = (2 * (j + 1) + 1).choose (j + 1 + 1) := by
      rw [show 2 * (j + 1 + 1) - 1 = 2 * (j + 1) + 1 by omega]
    have eG3 : (n + (j + 1)).choose (2 * (j + 1) - 1) = (n + (j + 1)).choose (2 * j + 1) := by
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    simp only [catF, catG, eF1, eF2, eG1, eG2, eG3]
    have r1 := choose_succ_right_cast ℤ (n + (j + 1)) (2 * j + 1)
    have r2 := choose_succ_right_cast ℤ (n + (j + 1)) (2 * j + 1 + 1)
    have r3 := succ_mul_catalan_eq_centralBinom (j + 1)
    rw [Nat.centralBinom_eq_two_mul_choose] at r3
    have r5 := Nat.add_one_mul_choose_eq (2 * (j + 1)) (j + 1)
    have r4 : (2 * (j + 1)).choose (j + 1) = 2 * (2 * (j + 1) - 1).choose (j + 1) := by
      have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
      have e' : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [e', e, Nat.choose_succ_succ',
        show (2 * j + 1).choose j = (2 * j + 1).choose (j + 1) by
          rw [← Nat.choose_symm (show j ≤ 2 * j + 1 by omega)]; congr 1; omega]
      ring
    have key := cat_alg_int (n : ℤ) ((j : ℤ) + 1)
      ((n + (j + 1)).choose (2 * j + 1) : ℕ) ((n + (j + 1)).choose (2 * j + 1 + 1) : ℕ)
      ((n + (j + 1)).choose (2 * j + 1 + 1 + 1) : ℕ) ((2 * (j + 1)).choose (j + 1) : ℕ)
      (catalan (j + 1) : ℕ) ((2 * (j + 1) - 1).choose (j + 1) : ℕ)
      ((2 * (j + 1) + 1).choose (j + 1 + 1) : ℕ) (by positivity)
      (by push_cast at r1; linear_combination r1)
      (by push_cast at r2; linear_combination r2)
      (by exact_mod_cast r3)
      (by exact_mod_cast r4)
      (by
        have h' : (2 * ((j : ℤ) + 1) + 1) * ((2 * (j + 1)).choose (j + 1) : ℤ)
            = ((2 * (j + 1) + 1).choose (j + 1 + 1) : ℤ) * ((j : ℤ) + 1 + 1) := by
          exact_mod_cast r5
        linear_combination -h')
    push_cast
    linear_combination ((-1 : ℤ) ^ (j + 1)) * key

theorem cat_wz_zero_sum (n : ℕ) : ((n : ℤ) + 1) * (n * ∑ k ∈ range (n + 2), catF n k
    - (n + 2) * ∑ k ∈ range (n + 2), catF (n + 1) k) = 0 := by
  have h := sum_range_sub (catG n) (n + 2)
  have e : ∀ k ∈ range (n + 2), ((n : ℤ) + 1) * (n * catF n k - (n + 2) * catF (n + 1) k)
      = catG n (k + 1) - catG n k := fun k _ => cat_wz n k
  have hG : catG n (n + 2) = 0 := by
    simp only [catG]
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have hG0 : catG n 0 = 0 := by simp [catG]
  have h2 : ((n : ℤ) + 1) * (n * ∑ k ∈ range (n + 2), catF n k
      - (n + 2) * ∑ k ∈ range (n + 2), catF (n + 1) k)
      = ∑ k ∈ range (n + 2), ((n : ℤ) + 1) * (n * catF n k - (n + 2) * catF (n + 1) k) := by
    rw [← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum]
  rw [h2, sum_congr rfl e, h, hG, hG0, sub_self]

theorem catF_eq_zero_of_lt {n k : ℕ} (h : n < k) : catF n k = 0 := by
  simp [catF, Nat.choose_eq_zero_of_lt (show n + k < 2 * k by omega)]

/-- The sum of CO-380 in integer form. -/
def catSum (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), catF n k

theorem catSum_rec (n : ℕ) : (n : ℤ) * catSum n = (n + 2) * catSum (n + 1) := by
  have h := cat_wz_zero_sum n
  rw [sum_range_succ, catF_eq_zero_of_lt (by omega), add_zero] at h
  have h' : ((n : ℤ) + 1) * ((n : ℤ) * catSum n - (n + 2) * catSum (n + 1)) = 0 := h
  have := (mul_eq_zero.1 h').resolve_left (by positivity)
  linarith

theorem catSum_succ (n : ℕ) : catSum (n + 1) = 0 := by
  induction n with
  | zero =>
    have h := catSum_rec 0
    simp at h
    linarith
  | succ n ih =>
    have h := catSum_rec (n + 1)
    rw [ih] at h
    push_cast at h
    have : ((n : ℤ) + 1 + 2) * catSum (n + 1 + 1) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by positivity)

/-- CO-380. `∑_k C(n+k,2k) C(2k,k) (-1)^k/(k+1)` is `1` for `n = 0` and `0` for `n ≥ 1`
(proved via the first-order recurrence `n f(n) = (n+2) f(n+1)`, i.e. the telescoped
recurrence `catF`, `catG`). -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.5.2, p. 125"]
theorem sum_choose_centralBinom_alt_div (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n + k).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) * (-1) ^ k / (k + 1)
      = if n = 0 then 1 else 0 := by
  have hcat : ∀ k : ℕ, (catF n k : ℚ)
      = ((n + k).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) * (-1) ^ k / (k + 1) := by
    intro k
    have h := succ_mul_catalan_eq_centralBinom k
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have h' : ((k : ℚ) + 1) * (catalan k : ℚ) = ((2 * k).choose k : ℚ) := by exact_mod_cast h
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    rw [eq_div_iff hk]
    simp only [catF]
    push_cast
    linear_combination (((n + k).choose (2 * k) : ℚ) * (-1) ^ k) * h'
  have hsum : ((catSum n : ℤ) : ℚ)
      = ∑ k ∈ range (n + 1), ((n + k).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) * (-1) ^ k / (k + 1) := by
    rw [catSum, Int.cast_sum]
    exact sum_congr rfl fun k _ => hcat k
  rw [← hsum]
  cases n with
  | zero => simp [catSum, catF]
  | succ m => rw [catSum_succ]; simp

/-! ### CO-378: `∑_k (-1)^k C(n+1,k) C(2n-2k+1,n) = 1` -/

/-- CO-378. `∑_k (-1)^k C(n+1,k) C(2n-2k+1,n) = 1` for `n ≥ 0`.  (The terms with `k > n` vanish
in the book's convention, so the sum is taken over `0 ≤ k ≤ n`.)  Proof: with
`H = ∑_{k ≤ n} (-1)^k C(n+1,k) (1+X)^(2n+1-2k)` one has `(1+X) H = (X (X+2))^(n+1) + (-1)^n`,
so the coefficients of `H` up to `X^n` are `(-1)^(n+j)`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.4.3, p. 121"]
theorem alt_sum_choose_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose k : ℤ) * ((2 * n + 1 - 2 * k).choose n : ℤ)
      = 1 := by
  set H : ℤ[X] := ∑ k ∈ range (n + 1),
    C ((-1 : ℤ) ^ k * ((n + 1).choose k : ℤ)) * (1 + X) ^ (2 * n + 1 - 2 * k) with hH
  have hcoef : H.coeff n = ∑ k ∈ range (n + 1),
      (-1 : ℤ) ^ k * ((n + 1).choose k : ℤ) * ((2 * n + 1 - 2 * k).choose n : ℤ) := by
    rw [hH, finsetSum_coeff]
    refine sum_congr rfl fun k _ => ?_
    rw [coeff_C_mul, coeff_one_add_X_pow]
  have hterm : ∀ k : ℕ, (C ((-1 : ℤ) ^ k * ((n + 1).choose k : ℤ)) : ℤ[X]) * ((1 + X) ^ 2) ^ (n + 1 - k)
      = (-1 : ℤ[X]) ^ k * ((1 + X) ^ 2) ^ (n + 1 - k) * ((n + 1).choose k : ℤ[X]) := by
    intro k
    rw [C_mul, C_pow, show (C (-1 : ℤ) : ℤ[X]) = -1 by simp,
      show (C ((n + 1).choose k : ℤ) : ℤ[X]) = ((n + 1).choose k : ℤ[X]) by simp]
    ring
  have hmul : (1 + X) * H = (X * (X + 2)) ^ (n + 1) + C ((-1 : ℤ) ^ n) := by
    have h1 : (1 + X) * H = ∑ k ∈ range (n + 1),
        C ((-1 : ℤ) ^ k * ((n + 1).choose k : ℤ)) * ((1 + X) ^ 2) ^ (n + 1 - k) := by
      rw [hH, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
      rw [← pow_mul, show 2 * (n + 1 - k) = (2 * n + 1 - 2 * k) + 1 by omega, pow_succ]
      ring
    have h2 := add_pow (-1 : ℤ[X]) ((1 + X) ^ 2) (n + 1)
    have h3 : (-1 + (1 + X) ^ 2 : ℤ[X]) = X * (X + 2) := by ring
    rw [h3, sum_range_succ] at h2
    have h4 : ∑ k ∈ range (n + 1), (-1 : ℤ[X]) ^ k * ((1 + X) ^ 2) ^ (n + 1 - k)
          * ((n + 1).choose k : ℤ[X])
        = ∑ k ∈ range (n + 1),
          C ((-1 : ℤ) ^ k * ((n + 1).choose k : ℤ)) * ((1 + X) ^ 2) ^ (n + 1 - k) :=
      sum_congr rfl fun k _ => (hterm k).symm
    rw [h4] at h2
    rw [h1]
    have h5 : (-1 : ℤ[X]) ^ (n + 1) * ((1 + X) ^ 2) ^ (n + 1 - (n + 1)) *
        ((n + 1).choose (n + 1) : ℤ[X]) = - C ((-1 : ℤ) ^ n) := by
      rw [Nat.sub_self, Nat.choose_self, C_pow, show (C (-1 : ℤ) : ℤ[X]) = -1 by simp]
      push_cast; ring
    rw [h5] at h2
    linear_combination -h2
  have hT : ∀ j, j ≤ n → ((X * (X + 2) : ℤ[X]) ^ (n + 1)).coeff j = 0 := by
    intro j hj
    rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]
  have hcj : ∀ j, j ≤ n → H.coeff j = (-1) ^ n * (-1) ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      have := congrArg (fun p => p.coeff 0) hmul
      simp only [add_mul, one_mul, coeff_add, coeff_X_mul_zero, add_zero, coeff_C_zero] at this
      rw [hT 0 (Nat.zero_le n), zero_add] at this
      simpa using this
    | succ j ih =>
      intro hj
      have := congrArg (fun p => p.coeff (j + 1)) hmul
      simp only [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_C] at this
      rw [hT (j + 1) hj] at this
      simp only [Nat.succ_ne_zero, if_false, add_zero] at this
      rw [ih (by omega)] at this
      rw [pow_succ]
      linear_combination this
  rw [← hcoef, hcj n le_rfl, ← mul_pow]
  simp

/-! ### CO-377: `∑_k (-1)^k C(n,k)/C(x+k,k) = x/(x+n)` -/

/-- The WZ-type telescoped recurrence of CO-377, for an abstract sequence `A k = C(x+k,k)`. -/
theorem kummer_wz (x : ℚ) (A : ℕ → ℚ) (hA0 : A 0 = 1)
    (hA : ∀ k : ℕ, ((k : ℚ) + 1) * A (k + 1) = (x + k + 1) * A k)
    (hAne : ∀ k, A k ≠ 0) (hx : ∀ k : ℕ, x + k ≠ 0) (n k : ℕ) :
    ((n : ℚ) + x) * ((-1) ^ k * (n.choose k : ℚ) / A k)
      - ((n : ℚ) + 1 + x) * ((-1) ^ k * ((n + 1).choose k : ℚ) / A k)
      = (-1) ^ (k + 1) * ((k : ℚ) + 1) * (x + (k + 1 : ℕ)) * ((n + 1).choose (k + 1) : ℚ)
          / (((n : ℚ) + 1) * A (k + 1))
        - (-1) ^ k * (k : ℚ) * (x + k) * ((n + 1).choose k : ℚ) / (((n : ℚ) + 1) * A k) := by
  cases k with
  | zero =>
    have h1 := hA 0
    rw [hA0] at h1
    have hx1 : x + 1 ≠ 0 := by simpa using hx 1
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have hc : ((n + 1).choose (0 + 1) : ℚ) = n + 1 := by simp
    simp only [Nat.choose_zero_right, hA0, hc]
    push_cast
    have hA1 : A 1 = x + 1 := by simpa using h1
    rw [hA1]
    field_simp
    ring
  | succ j =>
    have e1 := Nat.add_one_mul_choose_eq n (j + 1)
    have e3 := Nat.choose_succ_succ' n j
    have hrel := choose_succ_right_cast ℚ n j
    have e3' : ((n + 1).choose (j + 1) : ℚ) = (n.choose j : ℚ) + (n.choose (j + 1) : ℚ) := by
      exact_mod_cast e3
    have hAj := hA (j + 1)
    have hAne1 := hAne (j + 1)
    have hAne2 := hAne (j + 1 + 1)
    have hxj : x + ((j + 1 + 1 : ℕ) : ℚ) ≠ 0 := hx (j + 1 + 1)
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have hj2 : (j : ℚ) + 1 + 1 ≠ 0 := by positivity
    push_cast at hxj hAj ⊢
    rw [e3']
    have hA2 : A (j + 1 + 1) = (x + (j + 1) + 1) * A (j + 1) / ((j : ℚ) + 1 + 1) := by
      field_simp; linarith
    rw [hA2]
    have hC' : ((n + 1).choose (j + 1 + 1) : ℚ)
        = ((n : ℚ) + 1) * (n.choose (j + 1) : ℚ) / ((j : ℚ) + 1 + 1) := by
      have e1' : ((n + 1).choose (j + 1 + 1) : ℚ) * ((j : ℚ) + 1 + 1)
          = ((n : ℚ) + 1) * (n.choose (j + 1) : ℚ) := by exact_mod_cast e1.symm
      field_simp; linarith
    have hX1 : x + ((j : ℚ) + 1) + 1 ≠ 0 := by intro h; apply hxj; linarith
    rw [hC']
    field_simp
    linear_combination ((-1 : ℚ) ^ (j + 1) * (x + ((j : ℚ) + 1) + 1) * (x + n + j + 2)) * hrel

/-- `(k+1) * C(r,k+1) = (r-k) * C(r,k)` for `Ring.choose` over `ℚ`. -/
theorem ring_choose_succ_right (r : ℚ) (k : ℕ) :
    ((k : ℚ) + 1) * Ring.choose r (k + 1) = (r - k) * Ring.choose r k := by
  have h := Ring.choose_smul_choose r (show k ≤ k + 1 by omega)
  rw [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
    nsmul_eq_mul] at h
  push_cast at h
  rw [h]; ring

theorem ring_choose_shift (x : ℚ) (k : ℕ) :
    ((k : ℚ) + 1) * Ring.choose (x + ((k + 1 : ℕ) : ℚ)) (k + 1)
      = (x + k + 1) * Ring.choose (x + (k : ℚ)) k := by
  have e : x + ((k + 1 : ℕ) : ℚ) = (x + k) + 1 := by push_cast; ring
  rw [e, Ring.choose_succ_succ, mul_add, ring_choose_succ_right]
  ring

/-- CO-377. For `x` not a non-positive integer,
`∑_k (-1)^k C(n,k) / C(x+k,k) = x/(x+n)`, with `C(x+k,k) = Ring.choose (x + k) k` the general
binomial coefficient over `ℚ`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.4.2, p. 120"]
theorem kummer_sum (x : ℚ) (hx : ∀ n : ℕ, x + n ≠ 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℚ) / Ring.choose (x + (k : ℚ)) k
      = x / (x + n) := by
  set A : ℕ → ℚ := fun k => Ring.choose (x + (k : ℚ)) k with hAdef
  have hA0 : A 0 = 1 := by simp [hAdef]
  have hA : ∀ k : ℕ, ((k : ℚ) + 1) * A (k + 1) = (x + k + 1) * A k :=
    fun k => ring_choose_shift x k
  have hAne : ∀ k, A k ≠ 0 := by
    intro k
    induction k with
    | zero => rw [hA0]; exact one_ne_zero
    | succ k ih =>
      intro h
      have h2 := hA k
      rw [h, mul_zero] at h2
      have hxk : x + k + 1 ≠ 0 := by
        have := hx (k + 1)
        push_cast at this
        intro h'; apply this; linarith
      exact (mul_ne_zero hxk ih) h2.symm
  have hs : ∀ n : ℕ, ((n : ℚ) + x) * ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℚ) / A k
      = ((n : ℚ) + 1 + x) * ∑ k ∈ range (n + 1 + 1), (-1) ^ k * ((n + 1).choose k : ℚ) / A k := by
    intro n
    set Gf : ℕ → ℚ := fun k =>
      (-1) ^ k * (k : ℚ) * (x + k) * ((n + 1).choose k : ℚ) / (((n : ℚ) + 1) * A k) with hGf
    have h1 : ∑ k ∈ range (n + 2), (((n : ℚ) + x) * ((-1) ^ k * (n.choose k : ℚ) / A k)
        - ((n : ℚ) + 1 + x) * ((-1) ^ k * ((n + 1).choose k : ℚ) / A k)) = Gf (n + 2) - Gf 0 := by
      rw [← sum_range_sub Gf (n + 2)]
      refine sum_congr rfl fun k _ => ?_
      have := kummer_wz x A hA0 hA hAne hx n k
      simp only [hGf]
      push_cast at this ⊢
      linear_combination this
    have hG2 : Gf (n + 2) = 0 := by
      simp only [hGf]
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have hG0 : Gf 0 = 0 := by simp [hGf]
    rw [hG2, hG0, sub_zero, sum_sub_distrib, ← mul_sum, ← mul_sum] at h1
    rw [sum_range_succ (fun k => (-1) ^ k * (n.choose k : ℚ) / A k) (n + 1),
      Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)] at h1
    simp only [Nat.cast_zero, mul_zero, zero_div, add_zero] at h1
    linarith
  induction n with
  | zero =>
    simp [hAdef]
    have := hx 0
    simp at this
    field_simp
  | succ n ih =>
    have h := hs n
    have hxn1 : (n : ℚ) + 1 + x ≠ 0 := by
      have := hx (n + 1); push_cast at this; intro h'; apply this; linarith
    have ih' : ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℚ) / A k = x / (x + n) := ih
    rw [ih'] at h
    show ∑ k ∈ range (n + 1 + 1), (-1) ^ k * ((n + 1).choose k : ℚ) / A k
      = x / (x + ((n + 1 : ℕ) : ℚ))
    push_cast
    have hxn' : x + n ≠ 0 := hx n
    have hxn2 : x + (n + 1) ≠ 0 := by intro h'; apply hxn1; linarith
    rw [eq_div_iff hxn2]
    have : ∑ k ∈ range (n + 1 + 1), (-1) ^ k * ((n + 1).choose k : ℚ) / A k
        = ((n : ℚ) + x) * (x / (x + n)) / ((n : ℚ) + 1 + x) := by
      rw [eq_div_iff hxn1]; linear_combination -h
    rw [this]
    field_simp
    ring

end UndergradKB.Combinatorics.AeqB
