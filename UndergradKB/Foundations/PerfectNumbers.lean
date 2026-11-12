import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.Prime
import UndergradKB.Common

/-! # Even perfect numbers: Euclid and Euler

Hammack, *Book of Proof*, Section 8.4: Theorem 8.1 (Euclid: if `2^n - 1` is prime then `2^(n-1) (2^n - 1)` is perfect)
and Theorem 8.2 (Euler: every even perfect number has that form). A number `p` is perfect when the sum of its positive
divisors other than `p` is `p` (Mathlib's `Nat.Perfect`).

The argument follows the proof of Theorem 70 of the "100 theorems" in the Mathlib Archive
(`Archive/Wiedijk100Theorems/PerfectNumbers.lean`, Aaron Anderson, Apache 2.0), which is not importable as a library;
it is restated here and specialized to the book's form with exponent `n ≥ 1`.
-/

namespace UndergradKB.Foundations

open ArithmeticFunction Finset

open scoped sigma

/-- The sum of the divisors of `2^k` is `2^(k+1) - 1`. -/
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Euclid, with exponent `k + 1`. -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

/-- Every positive integer is a power of two times an odd number. -/
theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- Euler, with exponent `k + 1`. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

/-- FO-159 (Hammack Theorem 8.1, Euclid). If `2^n - 1` is prime, then `2^(n-1) (2^n - 1)` is perfect. -/
@[kb "hammack2018" "Theorem 8.1, p. 179"]
theorem euclid_perfect (n : ℕ) (hp : (2 ^ n - 1).Prime) : Nat.Perfect (2 ^ (n - 1) * (2 ^ n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    rcases n with _ | k
    · exact absurd hp (by norm_num)
    · exact ⟨k, rfl⟩
  exact perfect_two_pow_mul_mersenne_of_prime k hp

/-- FO-160 (Hammack Theorem 8.2, Euler). Every even perfect number `p` is `2^(n-1) (2^n - 1)` for some `n` with
`2^n - 1` prime. -/
@[kb "hammack2018" "Theorem 8.2, p. 181"]
theorem euler_even_perfect (p : ℕ) (hev : Even p) (hperf : Nat.Perfect p) :
    ∃ n : ℕ, (2 ^ n - 1).Prime ∧ p = 2 ^ (n - 1) * (2 ^ n - 1) := by
  obtain ⟨k, hk, rfl⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect hev hperf
  exact ⟨k + 1, hk, rfl⟩

end UndergradKB.Foundations
