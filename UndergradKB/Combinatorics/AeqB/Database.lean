import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Int.Interval
import UndergradKB.Common.Attr

/-!
# The hypergeometric database and recurrences by creative telescoping (A = B, Chapters 2, 3, 6, 7)

Terminating hypergeometric identities (Dixon, the alternating cube sum, Franel's recurrence, ...),
proved by telescoping certificates found by hand or by Zeilberger's algorithm.  Reciprocal
factorials `rf m = 1/m!` (zero at negative `m`) are used to write summands in a form where the
telescoping identity holds at every integer `k`, boundary terms included.
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset
open scoped Nat

/-- Reciprocal factorial of an integer, `0` at negative integers. -/
def rf (m : ℤ) : ℚ := if 0 ≤ m then (((m.toNat)! : ℕ) : ℚ)⁻¹ else 0

/-- Factorial of an integer (as a rational number; junk value `0! = 1` at negatives). -/
def fct (m : ℤ) : ℚ := (((m.toNat)! : ℕ) : ℚ)

theorem rf_rec (m m' : ℤ) (h : m' = m + 1) : rf m = ((m : ℚ) + 1) * rf m' := by
  subst h
  by_cases hm : 0 ≤ m
  · have e : (m + 1).toNat = m.toNat + 1 := by omega
    have e2 : ((m.toNat : ℕ) : ℚ) = (m : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hm
    simp only [rf, hm, ite_true, e, Nat.factorial_succ, show 0 ≤ m + 1 from by omega, ite_true]
    push_cast
    rw [← e2]
    have : ((m.toNat)! : ℚ) ≠ 0 := by positivity
    field_simp
  · by_cases hm1 : m = -1
    · subst hm1; simp [rf]
    · have : ¬ 0 ≤ m + 1 := by omega
      simp [rf, hm, this]

theorem fct_rec (m m' : ℤ) (h : m' = m + 1) (hm : 0 ≤ m) : fct m' = ((m : ℚ) + 1) * fct m := by
  subst h
  have e : (m + 1).toNat = m.toNat + 1 := by omega
  have e2 : ((m.toNat : ℕ) : ℚ) = (m : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hm
  simp only [fct, e, Nat.factorial_succ]
  push_cast
  rw [e2]

theorem rf_zero_of_neg {m : ℤ} (h : m < 0) : rf m = 0 := by simp [rf, not_le.2 h]

theorem fct_natCast (m : ℕ) : fct (m : ℤ) = (m ! : ℚ) := by simp [fct]

theorem rf_natCast (m : ℕ) : rf (m : ℤ) = ((m ! : ℕ) : ℚ)⁻¹ := by simp [rf]

/-- Dixon summand, normalised without division (factorial form). -/
def dixT (b c n k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * fct (n + b) * fct (n + c) * fct (b + c) *
    (rf (n + k) * rf (b - k) * rf (c + k) * rf (n - k) * rf (b + k) * rf (c - k))

def dixH (b c n k : ℤ) : ℚ :=
  -((k + b : ℚ) * (k + c) / 2) * (-1 : ℚ) ^ k * fct (n + b) * fct (n + c) * fct (b + c) *
    (rf (n + k) * rf (b - k) * rf (c + k) * rf (n + 1 - k) * rf (b + k) * rf (c - k))

theorem dix_step (b c n k : ℤ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hn : 0 ≤ n) :
    ((n : ℚ) + 1) * dixT b c (n + 1) k - ((n : ℚ) + b + c + 1) * dixT b c n k
      = dixH b c n (k + 1) - dixH b c n k := by
  unfold dixT dixH
  have s : (-1 : ℚ) ^ (k + 1) = -(-1 : ℚ) ^ k := by rw [zpow_add_one₀ (a := (-1 : ℚ)) (by norm_num) k]; ring
  rw [s]
  have f1 := fct_rec (n + b) (n + 1 + b) (by ring) (by omega)
  have f2 := fct_rec (n + c) (n + 1 + c) (by ring) (by omega)
  have r1 := rf_rec (n + k) (n + 1 + k) (by ring)
  have r1' : n + (k + 1) = n + 1 + k := by ring
  have r2 := rf_rec (b - (k + 1)) (b - k) (by ring)
  have r3 := rf_rec (c + k) (c + (k + 1)) (by ring)
  have r4 := rf_rec (n - k) (n + 1 - k) (by ring)
  have r4' : n + 1 - (k + 1) = n - k := by ring
  have r5 := rf_rec (b + k) (b + (k + 1)) (by ring)
  have r6 := rf_rec (c - (k + 1)) (c - k) (by ring)
  simp only [r1', r4', f1, f2]
  rw [r1, r4, r3, r5, r2, r6]
  push_cast
  ring

theorem sum_Icc_telescope (g : ℤ → ℚ) (a b : ℤ) (hab : a ≤ b + 1) :
    ∑ k ∈ Finset.Icc a b, (g (k + 1) - g k) = g (b + 1) - g a := by
  have e : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e]
  generalize b + 1 = c at hab ⊢
  induction c, hab using Int.leInduction with
  | base => simp
  | succ c hc ih =>
    have : Finset.Ico a (c + 1) = insert c (Finset.Ico a c) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [this, Finset.sum_insert (by simp), ih]; ring

theorem dixT_eq_zero {b c n k : ℤ} (h : k ∉ Finset.Icc (-b) c) : dixT b c n k = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at h
  unfold dixT
  rcases h with h | h
  · rw [rf_zero_of_neg (m := b + k) (by omega)]; ring
  · rw [rf_zero_of_neg (m := c - k) (by omega)]; ring

/-- The Dixon sum with an auxiliary parameter `n`, summed over the support `[-b, c]`. -/
def dixSum (b c n : ℕ) : ℚ := ∑ k ∈ Finset.Icc (-(b : ℤ)) c, dixT b c n k

theorem dixSum_succ (b c n : ℕ) :
    ((n : ℚ) + 1) * dixSum b c (n + 1) = ((n : ℚ) + b + c + 1) * dixSum b c n := by
  have h : ((n : ℚ) + 1) * dixSum b c (n + 1) - ((n : ℚ) + b + c + 1) * dixSum b c n
      = ∑ k ∈ Finset.Icc (-(b : ℤ)) c, (dixH b c n (k + 1) - dixH b c n k) := by
    unfold dixSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := dix_step (b : ℤ) (c : ℤ) (n : ℤ) k (by positivity) (by positivity) (by positivity)
    push_cast at this ⊢
    exact this
  rw [sum_Icc_telescope (dixH b c n) _ _ (by omega)] at h
  have h1 : dixH b c n ((c : ℤ) + 1) = 0 := by
    unfold dixH
    rw [show (c : ℤ) - ((c : ℤ) + 1) = -1 by ring]
    simp [rf]
  have h2 : dixH b c n (-(b : ℤ)) = 0 := by
    unfold dixH; simp
  rw [h1, h2] at h
  linarith

theorem dixSum_zero (b c : ℕ) : dixSum b c 0 = ((b + c) ! : ℚ) / (b ! * c !) := by
  unfold dixSum
  rw [Finset.sum_eq_single (0 : ℤ)]
  · unfold dixT
    simp only [Nat.cast_zero, zero_add, add_zero, sub_zero, zpow_zero, one_mul]
    have e1 : fct (b : ℤ) = (b ! : ℚ) := fct_natCast b
    have e2 : fct (c : ℤ) = (c ! : ℚ) := fct_natCast c
    have e3 : fct ((b : ℤ) + c) = ((b + c) ! : ℚ) := by
      rw [← Nat.cast_add, fct_natCast]
    rw [e1, e2, e3, rf_natCast, rf_natCast]
    have : rf 0 = 1 := by simp [rf]
    rw [this]
    have h1 : (b ! : ℚ) ≠ 0 := by positivity
    have h2 : (c ! : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  · intro k _ hk
    unfold dixT
    rcases lt_or_gt_of_ne hk with h | h
    · simp only [Nat.cast_zero, zero_add]
      rw [rf_zero_of_neg h]; ring
    · simp only [Nat.cast_zero, zero_sub]
      rw [rf_zero_of_neg (by omega : -k < 0)]; ring
  · intro h; exfalso; apply h; simp

theorem dixSum_eq (b c n : ℕ) :
    dixSum b c n = ((n + b + c) ! : ℚ) / (n ! * b ! * c !) := by
  induction n with
  | zero =>
    rw [dixSum_zero]
    simp only [Nat.zero_add, Nat.factorial_zero, Nat.cast_one]
    field_simp
  | succ n ih =>
    have := dixSum_succ b c n
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    have h1 : (n ! : ℚ) ≠ 0 := by positivity
    have h2 : (b ! : ℚ) ≠ 0 := by positivity
    have h3 : (c ! : ℚ) ≠ 0 := by positivity
    have e : dixSum b c (n + 1) = ((n : ℚ) + b + c + 1) / ((n : ℚ) + 1) * dixSum b c n := by
      field_simp; linarith
    rw [e, ih, show n + 1 + b + c = (n + b + c) + 1 by ring, Nat.factorial_succ (n + b + c),
      Nat.factorial_succ n]
    push_cast
    field_simp

/-- Binomial coefficient `C(m, j)` with an integer lower index, equal to `0` for `j < 0`. -/
def zchoose (m : ℕ) (j : ℤ) : ℕ := if 0 ≤ j then m.choose j.toNat else 0

theorem zchoose_cast (m : ℕ) (j : ℤ) :
    (zchoose m j : ℚ) = (m ! : ℚ) * rf j * rf ((m : ℤ) - j) := by
  by_cases h0 : 0 ≤ j
  · obtain ⟨j', rfl⟩ := Int.eq_ofNat_of_zero_le h0
    by_cases h1 : j' ≤ m
    · have e : (m : ℤ) - (j' : ℤ) = ((m - j' : ℕ) : ℤ) := by push_cast [Nat.cast_sub h1]; ring
      rw [e, rf_natCast, rf_natCast, zchoose, if_pos h0, Int.toNat_natCast, Nat.cast_choose ℚ h1]
      have : ((j' !: ℕ) : ℚ) ≠ 0 := by positivity
      have : (((m - j') ! : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
    · have : (m : ℤ) - (j' : ℤ) < 0 := by omega
      rw [rf_zero_of_neg this, zchoose, if_pos h0, Int.toNat_natCast,
        Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · rw [zchoose, if_neg h0, rf_zero_of_neg (by omega)]
    simp

theorem dixT_eq (a b c : ℕ) (k : ℤ) :
    dixT b c a k = (-1 : ℚ) ^ k * (zchoose (a + b) (a + k) : ℚ) * (zchoose (a + c) (c + k) : ℚ)
      * (zchoose (b + c) (b + k) : ℚ) := by
  rw [zchoose_cast, zchoose_cast, zchoose_cast]
  have e1 : ((a + b : ℕ) : ℤ) - ((a : ℤ) + k) = (b : ℤ) - k := by push_cast; ring
  have e2 : ((a + c : ℕ) : ℤ) - ((c : ℤ) + k) = (a : ℤ) - k := by push_cast; ring
  have e3 : ((b + c : ℕ) : ℤ) - ((b : ℤ) + k) = (c : ℤ) - k := by push_cast; ring
  rw [e1, e2, e3]
  unfold dixT
  have f1 : fct ((a : ℤ) + b) = ((a + b) ! : ℚ) := by rw [← Nat.cast_add, fct_natCast]
  have f2 : fct ((a : ℤ) + c) = ((a + c) ! : ℚ) := by rw [← Nat.cast_add, fct_natCast]
  have f3 : fct ((b : ℤ) + c) = ((b + c) ! : ℚ) := by rw [← Nat.cast_add, fct_natCast]
  rw [f1, f2, f3]
  ring

/-- CO-364 (and CO-452, summand form). Dixon's identity, over `ℚ`: for naturals `a b c`,
`∑_k (-1)^k C(a+b, a+k) C(a+c, c+k) C(b+c, b+k) = (a+b+c)! / (a! b! c!)`, where `k` ranges over
all integers (binomials with negative lower index vanish; the sum is finite). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 54 (IV)"]
theorem dixon (a b c : ℕ) :
    ∑ᶠ k : ℤ, (-1 : ℚ) ^ k * (zchoose (a + b) (a + k) : ℚ) * (zchoose (a + c) (c + k) : ℚ)
      * (zchoose (b + c) (b + k) : ℚ) = ((a + b + c) ! : ℚ) / (a ! * b ! * c !) := by
  have hsupp : Function.support (fun k : ℤ => (-1 : ℚ) ^ k * (zchoose (a + b) (a + k) : ℚ)
      * (zchoose (a + c) (c + k) : ℚ) * (zchoose (b + c) (b + k) : ℚ))
      ⊆ ↑(Finset.Icc (-(b : ℤ)) c) := by
    intro k hk
    by_contra hk'
    apply hk
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk'
    have := dixT_eq_zero (b := b) (c := c) (n := a) (k := k) (by simpa using hk')
    rw [dixT_eq] at this
    exact this
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have := dixSum_eq b c a
  unfold dixSum at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => (dixT_eq a b c k).symm

/-- CO-044. The alternating sum of cubes `∑_s (-1)^s C(2m, s)^3 = (-1)^m (3m)!/(m!)^3`
(the case `a = b = c = m` of Dixon's identity). -/
@[kb "petkovsekwilfzeilberger1996" "Eq 2.2.4, p. 33"]
theorem alternating_choose_cube (m : ℕ) :
    ∑ s ∈ Finset.range (2 * m + 1), (-1 : ℚ) ^ s * ((2 * m).choose s : ℚ) ^ 3
      = (-1 : ℚ) ^ m * ((3 * m) ! : ℚ) / ((m !) ^ 3 : ℚ) := by
  have h := dixSum_eq m m m
  unfold dixSum at h
  have h2 : ∑ k ∈ Finset.Icc (-(m : ℤ)) m, dixT m m m k
      = ∑ s ∈ Finset.range (2 * m + 1), dixT m m m ((s : ℤ) - m) := by
    symm
    apply Finset.sum_nbij' (fun s : ℕ => (s : ℤ) - m) (fun k : ℤ => (k + m).toNat)
    · intro s hs; simp only [Finset.mem_range] at hs; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · intro s hs; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · intro s hs; rfl
  rw [h2] at h
  have hm : ((m ! : ℕ) : ℚ) ≠ 0 := by positivity
  have h3 : ∀ s ∈ Finset.range (2 * m + 1), dixT m m m ((s : ℤ) - m)
      = (-1 : ℚ) ^ m * ((-1 : ℚ) ^ s * ((2 * m).choose s : ℚ) ^ 3) := by
    intro s hs
    rw [dixT_eq]
    have e : (m : ℤ) + ((s : ℤ) - m) = (s : ℤ) := by ring
    rw [e]
    have e2 : (zchoose (m + m) (s : ℤ) : ℚ) = ((2 * m).choose s : ℚ) := by
      simp [zchoose, two_mul]
    rw [e2]
    have e3 : (-1 : ℚ) ^ ((s : ℤ) - m) = (-1 : ℚ) ^ s * (-1 : ℚ) ^ m := by
      rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast,
        div_eq_iff (pow_ne_zero _ (by norm_num)), mul_assoc, ← mul_pow]
      simp
    rw [e3]; ring
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum] at h
  have hs : ((-1 : ℚ) ^ m) * (-1 : ℚ) ^ m = 1 := by rw [← mul_pow]; simp
  have e4 : m + m + m = 3 * m := by ring
  rw [e4] at h
  generalize (∑ s ∈ Finset.range (2 * m + 1), (-1 : ℚ) ^ s * ((2 * m).choose s : ℚ) ^ 3) = S at h ⊢
  have hM : ((m ! : ℕ) : ℚ) ^ 3 ≠ 0 := by positivity
  field_simp at h
  rw [eq_div_iff hM]
  linear_combination ((-1 : ℚ) ^ m) * h - (S * ((m ! : ℕ) : ℚ) ^ 3) * hs


/-- Contiguity relations for binomial coefficients, as rational numbers, valid for `k ≤ n + 2`. -/
theorem choose_contig (n k : ℕ) (hk : k ≤ n + 2) :
    ((n + 1).choose k : ℚ) = ((n + 2).choose k : ℚ) * ((n + 2 - k : ℚ) / (n + 2)) ∧
    (n.choose k : ℚ) = ((n + 1).choose k : ℚ) * ((n + 1 - k : ℚ) / (n + 1)) ∧
    ((n + 2).choose (k + 1) : ℚ) = ((n + 2).choose k : ℚ) * ((n + 2 - k : ℚ) / (k + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · have := Nat.choose_mul_succ_eq (n + 1) k
    have h2 : ((n + 1 + 1 - k : ℕ) : ℚ) = (n + 2 - k : ℚ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : (((n + 1).choose k : ℕ) : ℚ) * (n + 2) = ((n + 2).choose k : ℚ) * (n + 2 - k : ℚ) := by
      rw [← h2]; exact_mod_cast this
    field_simp
    linear_combination h3
  · by_cases hk' : k ≤ n + 1
    · have := Nat.choose_mul_succ_eq n k
      have h2 : ((n + 1 - k : ℕ) : ℚ) = (n + 1 - k : ℚ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have h3 : ((n.choose k : ℕ) : ℚ) * (n + 1) = ((n + 1).choose k : ℚ) * (n + 1 - k : ℚ) := by
        rw [← h2]; exact_mod_cast this
      field_simp
      linear_combination h3
    · have hk2 : k = n + 2 := by omega
      subst hk2
      simp [Nat.choose_eq_zero_of_lt]
  · have := Nat.choose_succ_right_eq (n + 2) k
    have h2 : ((n + 2 - k : ℕ) : ℚ) = (n + 2 - k : ℚ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : (((n + 2).choose (k + 1) : ℕ) : ℚ) * (k + 1) = ((n + 2).choose k : ℚ) * (n + 2 - k : ℚ) := by
      rw [← h2]; exact_mod_cast this
    field_simp
    linear_combination h3

/-- Franel numbers `f(n) = ∑_k C(n,k)^3`. -/
def franel (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), (n.choose k : ℚ) ^ 3

/-- The polynomial in the Zeilberger certificate for Franel numbers. -/
def franelP (n k : ℚ) : ℚ :=
  (72 - 78 * k + 30 * k ^ 2 - 4 * k ^ 3) + n * (272 - 249 * k + 78 * k ^ 2 - 8 * k ^ 3)
  + n ^ 2 * (402 - 291 * k + 66 * k ^ 2 - 4 * k ^ 3) + n ^ 3 * (290 - 147 * k + 18 * k ^ 2)
  + n ^ 4 * (102 - 27 * k) + 14 * n ^ 5

/-- The certificate term `G`. -/
def franelG (n k : ℕ) : ℚ :=
  (k : ℚ) ^ 3 * franelP n k * ((n + 2).choose k : ℚ) ^ 3 / (((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 3

theorem franel_step (n k : ℕ) (hk : k ≤ n + 2) :
    8 * ((n : ℚ) + 1) ^ 2 * (n.choose k : ℚ) ^ 3
      + (7 * (n : ℚ) ^ 2 + 21 * n + 16) * ((n + 1).choose k : ℚ) ^ 3
      - ((n : ℚ) + 2) ^ 2 * ((n + 2).choose k : ℚ) ^ 3
      = franelG n (k + 1) - franelG n k := by
  obtain ⟨h1, h2, h3⟩ := choose_contig n k hk
  rw [h2, h1]
  unfold franelG
  rw [Nat.cast_succ, h3]
  unfold franelP
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem sum_range_choose_cube_ext (m M : ℕ) (h : m + 1 ≤ M) :
    ∑ k ∈ range M, (m.choose k : ℚ) ^ 3 = franel m := by
  unfold franel
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro k hk hk'
  simp only [Finset.mem_range] at hk hk'
  rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- CO-233. The Franel numbers satisfy `8(n+1)^2 f(n) + (7n^2+21n+16) f(n+1) - (n+2)^2 f(n+2) = 0`,
proved by the telescoping certificate `franelG` (found by solving a linear system for the
numerator of the rational certificate, as Zeilberger's algorithm would). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 31"]
theorem franel_recurrence (n : ℕ) :
    8 * ((n : ℚ) + 1) ^ 2 * franel n + (7 * (n : ℚ) ^ 2 + 21 * n + 16) * franel (n + 1)
      - ((n : ℚ) + 2) ^ 2 * franel (n + 2) = 0 := by
  rw [← sum_range_choose_cube_ext n (n + 3) (by omega),
    ← sum_range_choose_cube_ext (n + 1) (n + 3) (by omega),
    ← sum_range_choose_cube_ext (n + 2) (n + 3) (by omega),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  have : ∀ k ∈ range (n + 3),
      8 * ((n : ℚ) + 1) ^ 2 * (n.choose k : ℚ) ^ 3
      + (7 * (n : ℚ) ^ 2 + 21 * n + 16) * ((n + 1).choose k : ℚ) ^ 3
      - ((n : ℚ) + 2) ^ 2 * ((n + 2).choose k : ℚ) ^ 3
      = franelG n (k + 1) - franelG n k := fun k hk =>
    franel_step n k (by simp at hk; omega)
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (franelG n) (n + 3)]
  simp [franelG]


/-- CO-054. Euler's identity `∑_k (-1)^k C(n,k) (x-k)^n = n!`, in any commutative ring.  (From the
statement that the `n`-th forward difference of `r ↦ r^n` is the constant `n!`.) -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 201 (9.11.3)"]
theorem euler_identity {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    ∑ k ∈ range (n + 1), (-1 : R) ^ k * (n.choose k : R) * (x - k) ^ n = (n ! : R) := by
  have h := congrFun (fwdDiff_iter_eq_factorial (R := R) (n := n)) (x - n)
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [Pi.natCast_apply] at h
  rw [← h, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; omega
  rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm hk']
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one]
  push_cast
  rw [Nat.cast_sub hk']
  ring_nf


/-! ### Laguerre polynomials -/

/-- The Laguerre polynomial `L_n(x) = ∑_k (-1)^k C(n,k) x^k / k!`, evaluated at `x : ℚ`. -/
def laguerre (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * x ^ k / (k ! : ℚ)

/-- Summand of the Laguerre polynomial. -/
def lagT (x : ℚ) (n k : ℕ) : ℚ := (-1 : ℚ) ^ k * (n.choose k : ℚ) * x ^ k / (k ! : ℚ)

/-- The certificate term for the Laguerre recurrence: `G(n,k) = -k^2/(n+2) * T(n+2,k)`. -/
def lagG (x : ℚ) (n k : ℕ) : ℚ := -((k : ℚ) ^ 2 / ((n : ℚ) + 2)) * lagT x (n + 2) k

theorem lag_step (x : ℚ) (n k : ℕ) (hk : k ≤ n + 2) :
    ((n : ℚ) + 2) * lagT x (n + 2) k + (x - 2 * n - 3) * lagT x (n + 1) k
      + ((n : ℚ) + 1) * lagT x n k = lagG x n (k + 1) - lagG x n k := by
  obtain ⟨h1, h2, h3⟩ := choose_contig n k hk
  unfold lagG lagT
  rw [h2, h1, Nat.cast_succ, h3, Nat.factorial_succ]
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hf : (k ! : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem laguerre_eq_sum (n M : ℕ) (x : ℚ) (h : n + 1 ≤ M) :
    ∑ k ∈ range M, lagT x n k = laguerre n x := by
  unfold laguerre lagT
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro k hk hk'
  simp only [Finset.mem_range] at hk hk'
  rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- CO-234. Three-term recurrence of the Laguerre polynomials, `(n+2) L_{n+2}(x) +
(x - 2n - 3) L_{n+1}(x) + (n+1) L_n(x) = 0` (the book's `n L_n + (x+1-2n) L_{n-1} +
(n-1) L_{n-2} = 0` with `n` replaced by `n + 2`), proved by telescoping. -/
@[kb "petkovsekwilfzeilberger1996" "Ex 4.3.2, p. 71"]
theorem laguerre_recurrence (n : ℕ) (x : ℚ) :
    ((n : ℚ) + 2) * laguerre (n + 2) x + (x - 2 * n - 3) * laguerre (n + 1) x
      + ((n : ℚ) + 1) * laguerre n x = 0 := by
  rw [← laguerre_eq_sum n (n + 3) x (by omega), ← laguerre_eq_sum (n + 1) (n + 3) x (by omega),
    ← laguerre_eq_sum (n + 2) (n + 3) x (by omega),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have : ∀ k ∈ range (n + 3),
      ((n : ℚ) + 2) * lagT x (n + 2) k + (x - 2 * n - 3) * lagT x (n + 1) k
        + ((n : ℚ) + 1) * lagT x n k = lagG x n (k + 1) - lagG x n k := fun k hk =>
    lag_step x n k (by simp at hk; omega)
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (lagG x n) (n + 3)]
  simp [lagG, lagT]

/-- CO-234 (book indexing). For `n ≥ 2`: `n L_n + (x + 1 - 2n) L_{n-1} + (n-1) L_{n-2} = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Ex 4.3.2, p. 71"]
theorem laguerre_recurrence' (n : ℕ) (hn : 2 ≤ n) (x : ℚ) :
    (n : ℚ) * laguerre n x + (x + 1 - 2 * n) * laguerre (n - 1) x
      + ((n : ℚ) - 1) * laguerre (n - 2) x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have := laguerre_recurrence m x
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  push_cast
  linear_combination this



/-! ### Vandermonde's identity (CO-050) -/

/-- CO-050 (the identity). Vandermonde's convolution in the form `∑_k C(a,k) C(n,k) = C(n+a,a)`
(Mathlib has it in antidiagonal form, `Nat.add_choose_eq`). -/
@[kb "petkovsekwilfzeilberger1996" "Ex 7.3.4, p. 140"]
theorem vandermonde_sum (a n : ℕ) :
    ∑ k ∈ range (n + 1), (a.choose k) * (n.choose k) = (n + a).choose a := by
  rw [show (n + a).choose a = (a + n).choose n by rw [add_comm, Nat.choose_symm_add],
    Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun k hk => ?_
  have : k ≤ n := by simp at hk; omega
  simp only [Nat.choose_symm this]

/-! ### Iterated partial sums of central binomial coefficients (CO-049) -/

/-- The `s`-fold iterated partial sums of `C(2m,m)/4^m`: `iterCentral 0 n = C(2n,n)/4^n` and
`iterCentral (s+1) n = ∑_{m ≤ n} iterCentral s m`. -/
def iterCentral : ℕ → ℕ → ℚ
  | 0, n => ((2 * n).choose n : ℚ) / 4 ^ n
  | s + 1, n => ∑ m ∈ range (n + 1), iterCentral s m

/-- The closed form, in factorials. -/
def centralClosed (s n : ℕ) : ℚ :=
  ((2 * n + 2 * s) ! : ℚ) * (s ! : ℚ) / (((2 * s) ! : ℚ) * (n ! : ℚ) * ((n + s) ! : ℚ) * 4 ^ n)

theorem centralClosed_binom (s n : ℕ) :
    centralClosed s n = ((2 * n + 2 * s).choose (2 * s) : ℚ) * ((2 * n).choose n : ℚ)
      / (((n + s).choose s : ℚ) * 4 ^ n) := by
  unfold centralClosed
  have h1 : (2 * s) ≤ 2 * n + 2 * s := by omega
  have h2 : n ≤ 2 * n := by omega
  have h3 : s ≤ n + s := by omega
  rw [Nat.cast_choose ℚ h1, Nat.cast_choose ℚ h2, Nat.cast_choose ℚ h3]
  have e1 : 2 * n + 2 * s - 2 * s = 2 * n := by omega
  have e2 : 2 * n - n = n := by omega
  have e3 : n + s - s = n := by omega
  rw [e1, e2, e3]
  have : ((2 * s) ! : ℚ) ≠ 0 := by positivity
  have : ((2 * n) ! : ℚ) ≠ 0 := by positivity
  have : (n ! : ℚ) ≠ 0 := by positivity
  have : (s ! : ℚ) ≠ 0 := by positivity
  have : ((n + s) ! : ℚ) ≠ 0 := by positivity
  field_simp

theorem centralClosed_step (s n : ℕ) :
    centralClosed (s + 1) (n + 1) = centralClosed (s + 1) n + centralClosed s (n + 1) := by
  unfold centralClosed
  have f1 : (2 * (n + 1) + 2 * (s + 1)) ! = (2 * n + 2 * s + 4) * (2 * n + 2 * s + 3)
      * (2 * n + 2 * s + 2) * (2 * n + 2 * s + 1) * (2 * n + 2 * s) ! := by
    rw [show 2 * (n + 1) + 2 * (s + 1) = (2 * n + 2 * s) + 1 + 1 + 1 + 1 by ring]
    simp only [Nat.factorial_succ] <;> ring
  have f2 : (2 * n + 2 * (s + 1)) ! = (2 * n + 2 * s + 2) * (2 * n + 2 * s + 1)
      * (2 * n + 2 * s) ! := by
    rw [show 2 * n + 2 * (s + 1) = (2 * n + 2 * s) + 1 + 1 by ring]
    simp only [Nat.factorial_succ] <;> ring
  have f3 : (2 * (n + 1) + 2 * s) ! = (2 * n + 2 * s + 2) * (2 * n + 2 * s + 1)
      * (2 * n + 2 * s) ! := by
    rw [show 2 * (n + 1) + 2 * s = (2 * n + 2 * s) + 1 + 1 by ring]
    simp only [Nat.factorial_succ] <;> ring
  have f4 : (2 * (s + 1)) ! = (2 * s + 2) * (2 * s + 1) * (2 * s) ! := by
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring]
    simp only [Nat.factorial_succ] <;> ring
  have f5 : (n + 1 + (s + 1)) ! = (n + s + 2) * (n + s + 1) * (n + s) ! := by
    rw [show n + 1 + (s + 1) = (n + s) + 1 + 1 by ring]
    simp only [Nat.factorial_succ] <;> ring
  have f6 : (n + (s + 1)) ! = (n + s + 1) * (n + s) ! := by
    rw [show n + (s + 1) = (n + s) + 1 by ring]
    simp only [Nat.factorial_succ] <;> ring
  have f7 : (n + 1 + s) ! = (n + s + 1) * (n + s) ! := by
    rw [show n + 1 + s = (n + s) + 1 by ring]
    simp only [Nat.factorial_succ] <;> ring
  rw [f1, f2, f3, f4, f5, f6, f7, Nat.factorial_succ s, Nat.factorial_succ n]
  have : ((2 * s) ! : ℚ) ≠ 0 := by positivity
  have : ((2 * n + 2 * s) ! : ℚ) ≠ 0 := by positivity
  have : (n ! : ℚ) ≠ 0 := by positivity
  have : (s ! : ℚ) ≠ 0 := by positivity
  have : ((n + s) ! : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- CO-049. The `s`-fold iterated partial sums of `C(2m,m)/4^m` are
`C(2n+2s, 2s) C(2n,n) / (C(n+s,s) 4^n)` (equation 5.5.2, proved by induction on `s` using the
telescoping relation `f(n,s) - f(n-1,s) = f(n,s-1)` found by Gosper's algorithm). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 99 (5.5.2)"]
theorem iterCentral_eq (s n : ℕ) :
    iterCentral s n = ((2 * n + 2 * s).choose (2 * s) : ℚ) * ((2 * n).choose n : ℚ)
      / (((n + s).choose s : ℚ) * 4 ^ n) := by
  rw [← centralClosed_binom]
  induction s generalizing n with
  | zero =>
    rw [centralClosed_binom]
    simp [iterCentral]
  | succ s ih =>
    induction n with
    | zero =>
      simp only [iterCentral, ih]
      simp [centralClosed]
      have : ((2 * s) ! : ℚ) ≠ 0 := by positivity
      field_simp
    | succ n ihn =>
      rw [iterCentral, Finset.sum_range_succ, ← iterCentral, ihn, ih, centralClosed_step]



/-! ### Partial sums of binomial coefficients (CO-463) -/

/-- `∑_{k ≤ r} C(m+1,k) + C(m,r) = 2 ∑_{k ≤ r} C(m,k)`. -/
theorem partial_choose_succ (m r : ℕ) :
    ∑ k ∈ range (r + 1), (m + 1).choose k + m.choose r = 2 * ∑ k ∈ range (r + 1), m.choose k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => m.choose k) (r + 1),
      Nat.choose_succ_succ']
    omega

/-- The step relation for `T n = ∑_{k ≤ n} C(3n,k)`. -/
theorem partial_choose_three_step (n : ℕ) :
    (∑ k ∈ range (n + 2), (3 * n + 3).choose k : ℚ) = 8 * ∑ k ∈ range (n + 1), (3 * n).choose k
      + 4 * (3 * n).choose (n + 1) - 2 * (3 * n + 1).choose (n + 1)
      - (3 * n + 2).choose (n + 1) := by
  have h1 := partial_choose_succ (3 * n + 2) (n + 1)
  have h2 := partial_choose_succ (3 * n + 1) (n + 1)
  have h3 := partial_choose_succ (3 * n) (n + 1)
  have h4 : ∑ k ∈ range (n + 2), (3 * n).choose k
      = ∑ k ∈ range (n + 1), (3 * n).choose k + (3 * n).choose (n + 1) :=
    Finset.sum_range_succ _ _
  have e1 : 3 * n + 2 + 1 = 3 * n + 3 := by ring
  have e2 : 3 * n + 1 + 1 = 3 * n + 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have := congrArg (fun x : ℕ => (x : ℚ)) h1
  have := congrArg (fun x : ℕ => (x : ℚ)) h2
  have := congrArg (fun x : ℕ => (x : ℚ)) h3
  have := congrArg (fun x : ℕ => (x : ℚ)) h4
  push_cast at *
  linarith

/-- The binomial identity behind the step: for `n = m + 1 ≥ 1`,
`4 C(3n,n+1) - 2 C(3n+1,n+1) - C(3n+2,n+1) = ρ C(3n+3,n+1)` with
`ρ = (2/3) (2 - j - 5 j^2) / ((3j-1)(3j-2))`, `j = n + 1`. -/
theorem choose_three_aux (m : ℕ) :
    4 * ((3 * (m + 1)).choose (m + 1 + 1) : ℚ) - 2 * (3 * (m + 1) + 1).choose (m + 1 + 1)
      - (3 * (m + 1) + 2).choose (m + 1 + 1)
    = (2 / 3) * (2 - ((m : ℚ) + 1 + 1) - 5 * ((m : ℚ) + 1 + 1) ^ 2)
      / ((3 * ((m : ℚ) + 1 + 1) - 1) * (3 * ((m : ℚ) + 1 + 1) - 2))
      * ((3 * (m + 1) + 3).choose (m + 1 + 1) : ℚ) := by
  have h1 : m + 1 + 1 ≤ 3 * (m + 1) := by omega
  have h2 : m + 1 + 1 ≤ 3 * (m + 1) + 1 := by omega
  have h3 : m + 1 + 1 ≤ 3 * (m + 1) + 2 := by omega
  have h4 : m + 1 + 1 ≤ 3 * (m + 1) + 3 := by omega
  rw [Nat.cast_choose ℚ h1, Nat.cast_choose ℚ h2, Nat.cast_choose ℚ h3, Nat.cast_choose ℚ h4]
  have a1 : 3 * (m + 1) - (m + 1 + 1) = 2 * m + 1 := by omega
  have a2 : 3 * (m + 1) + 1 - (m + 1 + 1) = 2 * m + 2 := by omega
  have a3 : 3 * (m + 1) + 2 - (m + 1 + 1) = 2 * m + 3 := by omega
  have a4 : 3 * (m + 1) + 3 - (m + 1 + 1) = 2 * m + 4 := by omega
  rw [a1, a2, a3, a4]
  have f1 : (3 * (m + 1) + 1) ! = (3 * m + 4) * (3 * (m + 1)) ! := by
    simp only [Nat.factorial_succ] <;> ring
  have f2 : (3 * (m + 1) + 2) ! = (3 * m + 5) * (3 * m + 4) * (3 * (m + 1)) ! := by
    simp only [Nat.factorial_succ] <;> ring
  have f3 : (3 * (m + 1) + 3) ! = (3 * m + 6) * (3 * m + 5) * (3 * m + 4) * (3 * (m + 1)) ! := by
    simp only [Nat.factorial_succ] <;> ring
  have g1 : (2 * m + 2) ! = (2 * m + 2) * (2 * m + 1) ! := by
    simp only [Nat.factorial_succ] <;> ring
  have g2 : (2 * m + 3) ! = (2 * m + 3) * (2 * m + 2) * (2 * m + 1) ! := by
    simp only [Nat.factorial_succ] <;> ring
  have g3 : (2 * m + 4) ! = (2 * m + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1) ! := by
    simp only [Nat.factorial_succ] <;> ring
  have k1 : (m + 1 + 1) ! = (m + 2) * (m + 1) * m ! := by
    simp only [Nat.factorial_succ] <;> ring
  rw [f1, f2, f3, g1, g2, g3, k1]
  have : ((3 * (m + 1)) ! : ℚ) ≠ 0 := by positivity
  have : ((2 * m + 1) ! : ℚ) ≠ 0 := by positivity
  have : (m ! : ℚ) ≠ 0 := by positivity
  push_cast
  have hm : (0 : ℚ) ≤ m := by positivity
  have hx1 : (3 * ((m : ℚ) + 1 + 1) - 1) ≠ 0 := ne_of_gt (by linarith)
  have hx2 : (3 * ((m : ℚ) + 1 + 1) - 2) ≠ 0 := ne_of_gt (by linarith)
  have hy1 : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  have hy2 : (2 * (m : ℚ) + 2) ≠ 0 := by positivity
  have hy3 : (2 * (m : ℚ) + 3) ≠ 0 := by positivity
  have hy4 : (2 * (m : ℚ) + 4) ≠ 0 := by positivity
  have hy5 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hy6 : ((m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- CO-463. For `n ≥ 0`, `8^{-n} ∑_{k ≤ n} C(3n,k) = 1 + (2/3) ∑_{j=1}^n (2 - j - 5j^2) /
((3j-1)(3j-2)) 8^{-j} C(3j,j)`. -/
@[kb "petkovsekwilfzeilberger1996" "Ex 7.3.6, p. 144 (7.3.9)"]
theorem partial_choose_three (n : ℕ) :
    (∑ k ∈ range (n + 1), (3 * n).choose k : ℚ) / 8 ^ n
      = 1 + (2 / 3) * ∑ j ∈ range n,
        (2 - ((j : ℚ) + 1) - 5 * ((j : ℚ) + 1) ^ 2)
          / ((3 * ((j : ℚ) + 1) - 1) * (3 * ((j : ℚ) + 1) - 2))
          * ((3 * (j + 1)).choose (j + 1) : ℚ) / 8 ^ (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_rhs => rw [Finset.sum_range_succ, mul_add, ← add_assoc, ← ih]
    rcases n with _ | m
    · norm_num [Finset.sum_range_succ, Nat.choose]
    · have hs := partial_choose_three_step (m + 1)
      have hc := choose_three_aux m
      push_cast at hs
      have h8 : (8 : ℚ) ^ (m + 1 + 1) = 8 * 8 ^ (m + 1) := by ring
      have e : 3 * (m + 1 + 1) = 3 * (m + 1) + 3 := by ring
      rw [e, show m + 1 + 2 = m + 1 + 1 + 1 from rfl, hs, h8]
      have hX : (8 * ∑ k ∈ range (m + 1 + 1), ((3 * (m + 1)).choose k : ℚ)
          + 4 * ((3 * (m + 1)).choose (m + 1 + 1) : ℚ)
          - 2 * ((3 * (m + 1) + 1).choose (m + 1 + 1) : ℚ)
          - ((3 * (m + 1) + 2).choose (m + 1 + 1) : ℚ))
          = 8 * ∑ k ∈ range (m + 1 + 1), ((3 * (m + 1)).choose k : ℚ)
          + (2 / 3) * (2 - ((m : ℚ) + 1 + 1) - 5 * ((m : ℚ) + 1 + 1) ^ 2)
            / ((3 * ((m : ℚ) + 1 + 1) - 1) * (3 * ((m : ℚ) + 1 + 1) - 2))
            * ((3 * (m + 1) + 3).choose (m + 1 + 1) : ℚ) := by linarith
      rw [hX]
      have h8' : (8 : ℚ) ^ (m + 1) ≠ 0 := by positivity
      push_cast
      field_simp


end UndergradKB.Combinatorics.AeqB
