import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Combinatorics.AeqB.QAnalogue
import UndergradKB.Common.Attr

/-!
# Paule's symmetrized finite Rogers–Ramanujan certificates (A = B, §6.5)

CO-382: the summands of the two sides of (6.5.6) are annihilated, up to a telescoping difference,
by the order-2 operator `A(N)` with the printed certificates `R_L`, `R_R`.
-/

noncomputable section

namespace UndergradKB.Combinatorics.AeqB

open Finset QAnalogue

namespace RogersRamanujan

variable {K : Type*} [Field K]

/-- The q-Pochhammer symbol `(q;q)_m = ∏_{t=1}^m (1 - q^t)`. -/
def poch (q : K) (m : ℕ) : K := qFac q 1 m

theorem poch_succ (q : K) (m : ℕ) : poch q (m + 1) = poch q m * (1 - q ^ (m + 1)) := by
  simp [poch, qFac_succ]

/-- The exponent `(5k² - k)/2` of (6.5.6). -/
def expo (k : ℕ) : ℕ := (5 * k ^ 2 - k) / 2

theorem expo_succ (j : ℕ) : expo (j + 1) = expo j + (5 * j + 2) := by
  have h1 : j ≤ j ^ 2 := by nlinarith
  have h2 : 5 * (j + 1) ^ 2 = 5 * j ^ 2 + 10 * j + 5 := by ring
  have h3 : 5 * (j + 1) ^ 2 - (j + 1) = (5 * j ^ 2 - j) + 2 * (5 * j + 2) := by omega
  unfold expo
  rw [h3]
  omega

/-- Left summand of (6.5.6): `2 q^{k²} / ((q;q)_k (q;q)_{n-k})`. -/
def FL (q : K) (n k : ℕ) : K := 2 * q ^ (k ^ 2) / (poch q k * poch q (n - k))

/-- Right summand of (6.5.6): `(-1)^k (1+q^k) q^{(5k²-k)/2} / ((q;q)_{n-k} (q;q)_{n+k})`. -/
def FR (q : K) (n k : ℕ) : K :=
  (-1) ^ k * (1 + q ^ k) * q ^ expo k / (poch q (n - k) * poch q (n + k))

/-- Paule's certificate `R_L(n,k) = -q^{2n-1} (1 - q^{n-k})`. -/
def RL (q : K) (n k : ℕ) : K := -q ^ (2 * n - 1) * (1 - q ^ (n - k))

/-- Paule's certificate `R_R(n,k) = q^{2n+3k} (1 - q^{n-k}) / (1+q^k)`. -/
def RR (q : K) (n k : ℕ) : K := q ^ (2 * n + 3 * k) / (1 + q ^ k) * (1 - q ^ (n - k))

/-- The coefficient `1 + q - q^n + q^{2n-1}` of `A(N)`. -/
def Acoef (q : K) (n : ℕ) : K := 1 + q - q ^ n + q ^ (2 * n - 1)

/-- `A(N) F` evaluated at `(n,k)`, for a summand `F` (`N^{-1}` is the shift `n ↦ n-1`). -/
def applyA (q : K) (F : ℕ → ℕ → K) (n k : ℕ) : K :=
  (1 - q ^ n) * F n k - Acoef q n * F (n - 1) k + q * F (n - 2) k

theorem poch_ne_zero (q : K) (hP : ∀ t, 0 < t → 1 - q ^ t ≠ 0) (m : ℕ) : poch q m ≠ 0 := by
  induction m with
  | zero => simp [poch, qFac]
  | succ m ih => rw [poch_succ]; exact mul_ne_zero ih (hP _ (Nat.succ_pos m))

theorem left_aux (q : K) (a j : ℕ) (hP : ∀ t, 0 < t → 1 - q ^ t ≠ 0) :
    applyA q (FL q) (a + j + 3) (j + 1) =
      RL q (a + j + 3) (j + 1) * FL q (a + j + 3) (j + 1)
        - RL q (a + j + 3) j * FL q (a + j + 3) j := by
  have e1 : a + j + 3 - (j + 1) = a + 2 := by omega
  have e2 : a + j + 2 - (j + 1) = a + 1 := by omega
  have e3 : a + j + 1 - (j + 1) = a := by omega
  have e4 : a + j + 3 - j = a + 3 := by omega
  have e5 : 2 * (a + j + 3) - 1 = 2 * a + 2 * j + 5 := by omega
  have e6 : a + j + 3 - 1 = a + j + 2 := by omega
  have e7 : a + j + 3 - 2 = a + j + 1 := by omega
  have h1 := hP (a + 1) (by omega)
  have h2 := hP (a + 2) (by omega)
  have h3 := hP (a + 3) (by omega)
  have h4 := hP (j + 1) (by omega)
  have hA := poch_ne_zero q hP a
  have hJ := poch_ne_zero q hP j
  simp only [applyA, Acoef, FL, RL, e1, e2, e3, e4, e5, e6, e7, poch_succ]
  field_simp
  ring

theorem right_aux (q : K) (a j : ℕ) (hP : ∀ t, 0 < t → 1 - q ^ t ≠ 0)
    (hQ : ∀ t, 1 + q ^ t ≠ 0) :
    applyA q (FR q) (a + j + 3) (j + 1) =
      RR q (a + j + 3) (j + 1) * FR q (a + j + 3) (j + 1)
        - RR q (a + j + 3) j * FR q (a + j + 3) j := by
  have e1 : a + j + 3 - (j + 1) = a + 2 := by omega
  have e2 : a + j + 2 - (j + 1) = a + 1 := by omega
  have e3 : a + j + 1 - (j + 1) = a := by omega
  have e4 : a + j + 3 - j = a + 3 := by omega
  have e5 : 2 * (a + j + 3) - 1 = 2 * a + 2 * j + 5 := by omega
  have e6 : a + j + 3 - 1 = a + j + 2 := by omega
  have e7 : a + j + 3 - 2 = a + j + 1 := by omega
  have f1 : a + j + 3 + (j + 1) = (a + 2 * j) + 4 := by omega
  have f2 : a + j + 2 + (j + 1) = (a + 2 * j) + 3 := by omega
  have f3 : a + j + 1 + (j + 1) = (a + 2 * j) + 2 := by omega
  have f4 : a + j + 3 + j = (a + 2 * j) + 3 := by omega
  have g1 := hP (a + 1) (by omega)
  have g2 := hP (a + 2) (by omega)
  have g3 := hP (a + 3) (by omega)
  have g4 := hP (a + 2 * j + 1) (by omega)
  have g5 := hP (a + 2 * j + 2) (by omega)
  have g6 := hP (a + 2 * j + 3) (by omega)
  have g7 := hP (a + 2 * j + 4) (by omega)
  have hA := poch_ne_zero q hP a
  have hM := poch_ne_zero q hP (a + 2 * j)
  have i1 := hQ j
  have i2 := hQ (j + 1)
  simp only [applyA, Acoef, FR, RR, expo_succ, e1, e2, e3, e4, e5, e6, e7,
    f1, f2, f3, f4, poch_succ]
  field_simp
  ring

/-- CO-382. Paule's certificate `R_L` for the left side of (6.5.6): `A(N) F_L = G_L(n,k) - G_L(n,k-1)`
with `G_L = R_L F_L`, at integers `1 ≤ k ≤ n-2` (so all Pochhammer arguments are nonnegative);
`q` is assumed not to be a root of unity, which makes all denominators nonzero. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.5.7), p. 127"]
theorem paule_left (q : K) (hP : ∀ t, 0 < t → 1 - q ^ t ≠ 0) (n k : ℕ) (hk : 1 ≤ k)
    (hn : k + 2 ≤ n) :
    applyA q (FL q) n k = RL q n k * FL q n k - RL q n (k - 1) * FL q n (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, n = a + j + 3 := ⟨n - j - 3, by omega⟩
  simpa using left_aux q a j hP

/-- CO-382. Paule's certificate `R_R` for the right side of (6.5.6): `A(N) F_R = G_R(n,k) - G_R(n,k-1)`
with `G_R = R_R F_R`, at integers `1 ≤ k ≤ n-2`; `q` not a root of unity and `1 + q^t ≠ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.5.7), p. 127"]
theorem paule_right (q : K) (hP : ∀ t, 0 < t → 1 - q ^ t ≠ 0) (hQ : ∀ t, 1 + q ^ t ≠ 0)
    (n k : ℕ) (hk : 1 ≤ k) (hn : k + 2 ≤ n) :
    applyA q (FR q) n k = RR q n k * FR q n k - RR q n (k - 1) * FR q n (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, n = a + j + 3 := ⟨n - j - 3, by omega⟩
  simpa using right_aux q a j hP hQ

end RogersRamanujan

namespace MonthlySum

def aSeq (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), 2 ^ k * (n - k).choose (2 * k)
def cSeq (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), 2 ^ k * (n - k).choose (2 * k + 1)

theorem cSeq_succ (n : ℕ) : cSeq (n + 1) = cSeq n + aSeq n := by
  unfold cSeq aSeq
  rw [sum_range_succ, add_comm (∑ k ∈ range (n + 1), _), ← sum_add_distrib]
  have h0 : (n + 1 - (n + 1)).choose (2 * (n + 1) + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h0, mul_zero, zero_add]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simp at hk; omega
  have e : n + 1 - k = (n - k) + 1 := by omega
  rw [e, Nat.choose_succ_succ' (n - k) (2 * k), mul_add]
  ring

theorem aSeq_succ2 (n : ℕ) : aSeq (n + 2) = aSeq (n + 1) + 2 * cSeq n := by
  have h1 : aSeq (n + 2) = 1 + ∑ k ∈ range (n + 1),
      2 ^ (k + 1) * ((n - k).choose (2 * k + 1) + (n - k).choose (2 * k + 2)) := by
    unfold aSeq
    rw [sum_range_succ', sum_range_succ]
    have h0 : (n + 2 - (n + 1 + 1)).choose (2 * (n + 1 + 1)) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [h0, mul_zero, add_zero, add_comm]
    simp only [pow_zero]
    congr 1
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by simp at hk; omega
    have e : n + 2 - (k + 1) = (n - k) + 1 := by omega
    rw [e, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ' (n - k) (2 * k + 1)]
  have h2 : aSeq (n + 1) = 1 + ∑ k ∈ range (n + 1),
      2 ^ (k + 1) * (n - k).choose (2 * k + 2) := by
    unfold aSeq
    rw [sum_range_succ', add_comm]
    simp only [pow_zero]
    congr 1
    apply sum_congr rfl
    intro k hk
    have e : n + 1 - (k + 1) = n - k := by omega
    rw [e, show 2 * (k + 1) = 2 * k + 2 by ring]
  have h3 : 2 * cSeq n = ∑ k ∈ range (n + 1), 2 ^ (k + 1) * (n - k).choose (2 * k + 1) := by
    unfold cSeq
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    ring
  rw [h1, h2, h3, add_assoc, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  ring

/-- The integer sequence `1, 0, -1, 0, ...` (that is `cos (n π / 2)`). -/
def wSeq : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | n + 2 => - wSeq n

theorem aSeq_cSeq_closed (n : ℕ) :
    ((5 * aSeq n : ℕ) : ℤ) = 2 ^ (n + 1) + 3 * wSeq n - wSeq (n + 1) ∧
    ((5 * cSeq n : ℕ) : ℤ) = 2 ^ (n + 1) - 2 * wSeq n - wSeq (n + 1) := by
  have key : ∀ n, (((5 * aSeq n : ℕ) : ℤ) = 2 ^ (n + 1) + 3 * wSeq n - wSeq (n + 1) ∧
      ((5 * cSeq n : ℕ) : ℤ) = 2 ^ (n + 1) - 2 * wSeq n - wSeq (n + 1)) ∧
      (((5 * aSeq (n + 1) : ℕ) : ℤ) = 2 ^ (n + 2) + 3 * wSeq (n + 1) - wSeq (n + 2) ∧
      ((5 * cSeq (n + 1) : ℕ) : ℤ) = 2 ^ (n + 2) - 2 * wSeq (n + 1) - wSeq (n + 2)) := by
    intro n
    induction n with
    | zero => simp [aSeq, cSeq, wSeq, sum_range_succ]
    | succ n ih =>
      obtain ⟨⟨ha, hc⟩, ha1, hc1⟩ := ih
      refine ⟨⟨ha1, hc1⟩, ?_, ?_⟩
      · have e := aSeq_succ2 n
        have w2 : wSeq (n + 2) = - wSeq n := rfl
        have w3 : wSeq (n + 1 + 2) = - wSeq (n + 1) := rfl
        rw [e]
        push_cast at ha hc ha1 hc1 ⊢
        rw [w3]
        linear_combination ha1 + 2 * hc - 4 * w2
      · have e := cSeq_succ (n + 1)
        have w3 : wSeq (n + 1 + 2) = - wSeq (n + 1) := rfl
        rw [e]
        push_cast at ha hc ha1 hc1 ⊢
        rw [w3]
        linear_combination hc1 + ha1
  exact (key n).1

/-- Pointwise Pascal-type identity. -/
theorem term_eq (p j : ℕ) :
    (2 : ℚ) ^ (j + 1) * (((p + j + 2 : ℕ) : ℚ) / (p + 1)) * ((p + 1).choose (2 * j + 2) : ℚ)
      = 2 ^ (j + 1) * ((p + 1).choose (2 * j + 2) : ℚ) + 2 ^ j * (p.choose (2 * j + 1) : ℚ) := by
  have h := Nat.add_one_mul_choose_eq p (2 * j + 1)
  have h' : ((p + 1).choose (2 * j + 2) : ℚ) = (p + 1) * (p.choose (2 * j + 1) : ℚ) / (2 * j + 2) := by
    have h2 : (((p + 1) * p.choose (2 * j + 1) : ℕ) : ℚ)
        = (((p + 1).choose (2 * j + 1 + 1) * (2 * j + 1 + 1) : ℕ) : ℚ) := by rw [h]
    push_cast at h2
    field_simp
    linarith
  rw [h']
  push_cast
  field_simp
  ring

/-- CO-423. Summand `2^k · n/(n-k) · C(n-k, 2k)` of Monthly problem 10424. -/
def Fsum (n k : ℕ) : ℚ := 2 ^ k * ((n : ℚ) / ((n : ℚ) - k)) * ((n - k).choose (2 * k) : ℚ)

/-- CO-423. `f(n) = ∑_{0 ≤ k ≤ n/3} 2^k n/(n-k) C(n-k,2k)` (Example 6.1.1). -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.1.1, p. 114"]
def fSum (n : ℕ) : ℚ := ∑ k ∈ range (n / 3 + 1), Fsum n k

theorem fSum_eq_range (n : ℕ) : fSum n = ∑ k ∈ range (n + 1), Fsum n k := by
  unfold fSum
  apply sum_subset
  · intro k hk
    simp only [mem_range] at hk ⊢
    have := Nat.div_le_self n 3
    omega
  · intro k hk hk'
    simp only [mem_range] at hk hk'
    have h : n - k < 2 * k := by omega
    simp [Fsum, Nat.choose_eq_zero_of_lt h]

theorem aSeq_form (m : ℕ) : aSeq (m + 2) = 1 + ∑ j ∈ range (m + 1),
    2 ^ (j + 1) * ((m - j) + 1).choose (2 * j + 2) := by
  unfold aSeq
  rw [sum_range_succ', sum_range_succ]
  have h0 : (m + 2 - (m + 1 + 1)).choose (2 * (m + 1 + 1)) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  rw [h0, mul_zero, add_zero, add_comm]
  simp only [pow_zero]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ m := by simp at hk; omega
  have e : m + 2 - (k + 1) = (m - k) + 1 := by omega
  rw [e, show 2 * (k + 1) = 2 * k + 2 by ring]

theorem fSum_eq (m : ℕ) : fSum (m + 2) = (aSeq (m + 2) : ℚ) + cSeq m := by
  rw [fSum_eq_range, sum_range_succ', sum_range_succ]
  have h0 : Fsum (m + 2) (m + 1 + 1) = 0 := by
    have : (m + 2 - (m + 1 + 1)).choose (2 * (m + 1 + 1)) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    unfold Fsum
    rw [this]
    simp
  have h1 : Fsum (m + 2) 0 = 1 := by
    have : ((m : ℚ) + 2) ≠ 0 := by positivity
    simp [Fsum, this]
  rw [h0, add_zero, h1, aSeq_form]
  unfold cSeq
  have hc : ∑ j ∈ range (m + 1), 2 ^ j * ((m - j).choose (2 * j + 1) : ℚ)
      = ∑ j ∈ range (m + 1), (2 ^ j * (m - j).choose (2 * j + 1) : ℕ) := by
    push_cast; rfl
  push_cast
  rw [add_comm, add_assoc]
  congr 1
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ m := by simp at hj; omega
  obtain ⟨p, rfl⟩ : ∃ p, m = p + j := ⟨m - j, by omega⟩
  have e : p + j - j = p := by omega
  have e2 : p + j + 2 - (j + 1) = p + 1 := by omega
  have e3 : p + j + 2 - (j + 1) - 1 = p := by omega
  simp only [Fsum, e, e2, show 2 * (j + 1) = 2 * j + 2 from by ring]
  have := term_eq p j
  have e4 : ((p + j + 2 : ℕ) : ℚ) - ((j + 1 : ℕ) : ℚ) = (p : ℚ) + 1 := by push_cast; ring
  rw [e4]
  push_cast at this ⊢
  linarith

theorem fSum_closed (m : ℕ) : fSum (m + 2) = 2 ^ (m + 1) + (wSeq (m + 2) : ℚ) := by
  have ha := (aSeq_cSeq_closed (m + 2)).1
  have hc := (aSeq_cSeq_closed m).2
  push_cast at ha hc
  have ha' : (5 : ℚ) * aSeq (m + 2) = 2 ^ (m + 2 + 1) + 3 * (wSeq (m + 2) : ℚ) - wSeq (m + 2 + 1) := by
    exact_mod_cast ha
  have hc' : (5 : ℚ) * cSeq m = 2 ^ (m + 1) - 2 * (wSeq m : ℚ) - wSeq (m + 1) := by
    exact_mod_cast hc
  have w2 : (wSeq (m + 2) : ℚ) = - wSeq m := by simp [wSeq]
  have w3 : (wSeq (m + 2 + 1) : ℚ) = - wSeq (m + 1) := by simp [wSeq]
  have : (5 : ℚ) * fSum (m + 2) = 5 * (2 ^ (m + 1) + (wSeq (m + 2) : ℚ)) := by
    rw [fSum_eq]
    linear_combination ha' + hc' - 2 * w2 - w3
  linarith

theorem wSeq_cos : ∀ n : ℕ, (wSeq n : ℝ) = Real.cos (n * Real.pi / 2)
  | 0 => by simp [wSeq]
  | 1 => by simp [wSeq]
  | n + 2 => by
    have e : ((n + 2 : ℕ) : ℝ) * Real.pi / 2 = n * Real.pi / 2 + Real.pi := by push_cast; ring
    rw [e, Real.cos_add_pi, ← wSeq_cos n]
    simp [wSeq]

/-- CO-423. For `n ≥ 2`, `f(n) = 2^{n-1} + cos(nπ/2)`, with `cos(nπ/2)` the integer sequence
`1, 0, -1, 0, ...` (`wSeq`). -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.1.1, p. 114"]
theorem fSum_formula (n : ℕ) (hn : 2 ≤ n) : fSum n = 2 ^ (n - 1) + (wSeq n : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simpa using fSum_closed m

/-- CO-423. The book's form: `f(n) = 2^{n-1} + Real.cos (n π / 2)` for `n ≥ 2`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.1.1, p. 114"]
theorem fSum_formula_cos (n : ℕ) (hn : 2 ≤ n) :
    (fSum n : ℝ) = 2 ^ (n - 1) + Real.cos (n * Real.pi / 2) := by
  rw [fSum_formula n hn, ← wSeq_cos]
  push_cast
  ring

end MonthlySum

end UndergradKB.Combinatorics.AeqB
