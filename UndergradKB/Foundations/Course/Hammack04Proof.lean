import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 4 (proof techniques and elementary number theory)

Parity, divisibility, lcm, the division algorithm and unique factorization, as used in the
direct-proof chapter.
-/

namespace UndergradKB.Foundations.Course

/-- FO-100. An integer is even iff it is `2a` for some integer `a`, odd iff it is `2a + 1`. -/
@[kb "hammack2018" "Definition 4.1, p. 127", kb "hammack2018" "Definition 4.2, p. 127",
  kb "levin2025" "Ex 1.4.8, p. 88", kb "levin2025" "Ex 1.4.11, p. 90"]
theorem hammack_def_4_1_even_odd (n : ℤ) :
    (Even n ↔ ∃ a : ℤ, n = 2 * a) ∧ (Odd n ↔ ∃ a : ℤ, n = 2 * a + 1) :=
  ⟨⟨fun ⟨r, hr⟩ => ⟨r, by omega⟩, fun ⟨a, ha⟩ => ⟨a, by omega⟩⟩, Iff.rfl⟩

/-- FO-102. Two integers of opposite parity have an odd sum. -/
@[kb "hammack2018" "Prop §4.5, p. 137"]
theorem hammack_s4_5_opposite_parity_odd_sum (m n : ℤ)
    (h : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) : Odd (m + n) := by
  rcases h with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · exact hm.add_odd hn
  · exact hm.add_even hn

/-- FO-104. An integer is even iff its square is even, and odd iff its square is odd. -/
@[kb "hammack2018" "Prop §4.3, p. 131", kb "hammack2018" "Prop §6.2, p. 153",
  kb "hammack2018" "Prop §7.1, p. 160", kb "levin2025" "Ex 1.4.8, p. 88",
  kb "levin2025" "Ex 1.4.11, p. 90"]
theorem hammack_s4_3_even_iff_sq_even (n : ℤ) :
    (Even n ↔ Even (n ^ 2)) ∧ (Odd n ↔ Odd (n ^ 2)) := by
  refine ⟨(Int.even_pow' two_ne_zero).symm, ?_⟩
  rw [← Int.not_even_iff_odd, ← Int.not_even_iff_odd, Int.even_pow' two_ne_zero]

/-- FO-105. `a ∣ b` means `b = a c` for some integer `c`; also `x ∣ 0`, `x ∣ x`, `1 ∣ n`. -/
@[kb "hammack2018" "Definition 4.4, p. 128", kb "levin2025" "Box §6.2.1, p. 453",
  kb "levin2025" "Ex 6.2.1, p. 453"]
theorem hammack_def_4_4_dvd (a b : ℤ) :
    (a ∣ b ↔ ∃ c : ℤ, b = a * c) ∧ a ∣ 0 ∧ a ∣ a ∧ 1 ∣ b :=
  ⟨Iff.rfl, dvd_zero a, dvd_refl a, one_dvd b⟩

/-- FO-106. Divisibility is transitive. -/
@[kb "hammack2018" "Prop §4.3, p. 133", kb "levin2025" "Ex 1.4.9, p. 88"]
theorem hammack_s4_3_dvd_trans (a b c : ℤ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c :=
  dvd_trans hab hbc

/-- FO-107. The sum, difference and product of two integers are integers. -/
@[kb "hammack2018" "Fact 4.1, p. 129"]
theorem hammack_fact_4_1_int_closed (a b : ℤ) :
    ∃ s d p : ℤ, s = a + b ∧ d = a - b ∧ p = a * b :=
  ⟨a + b, a - b, a * b, rfl, rfl, rfl⟩

/-- FO-111. For natural numbers, `lcm (c a) (c b) = c * lcm a b`. -/
@[kb "hammack2018" "Prop §4.3, p. 134"]
theorem hammack_s4_3_lcm_mul_left (a b c : ℕ) :
    Nat.lcm (c * a) (c * b) = c * Nat.lcm a b :=
  Nat.lcm_mul_left c a b

/-- FO-112. Division algorithm: for `b > 0` there is exactly one pair `(q, r)` with
`a = q b + r` and `0 ≤ r < b`. -/
@[kb "hammack2018" "Prop §4.2, p. 129", kb "levin2025" "Box §6.2.1, p. 455"]
theorem hammack_s4_2_division_algorithm (a b : ℤ) (hb : 0 < b) :
    ∃! qr : ℤ × ℤ, a = qr.1 * b + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < b := by
  refine ⟨(a / b, a % b), ⟨?_, Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩, ?_⟩
  · simp only
    have := ((Int.ediv_emod_unique (a := a) hb).mp ⟨rfl, rfl⟩).1
    linarith [mul_comm b (a / b)]
  · rintro ⟨q, r⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    have : a / b = q ∧ a % b = r :=
      (Int.ediv_emod_unique hb).mpr ⟨by linarith [mul_comm q b], h2, h3⟩
    ext <;> simp [this.1, this.2]

/-- FO-113. Fundamental theorem of arithmetic: every `n > 1` is a product of primes, and the
multiset of prime factors is unique. -/
@[kb "hammack2018" "Prop §4.2, p. 129"]
theorem hammack_s4_2_fta (n : ℕ) (hn : 1 < n) :
    (∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n) ∧
      ∀ l l' : List ℕ, (∀ p ∈ l, p.Prime) → l.prod = n → (∀ p ∈ l', p.Prime) → l'.prod = n →
        l.Perm l' := by
  refine ⟨⟨n.primeFactorsList, fun p hp => Nat.prime_of_mem_primeFactorsList hp,
    Nat.prod_primeFactorsList (by omega)⟩, ?_⟩
  intro l l' h1 h2 h3 h4
  exact (Nat.primeFactorsList_unique h2 h1).trans (Nat.primeFactorsList_unique h4 h3).symm

/-- FO-116. For positive `x ≤ y`, `√x ≤ √y`. -/
@[kb "hammack2018" "Prop §4.3, p. 134"]
theorem hammack_s4_3_sqrt_mono (x y : ℝ) (_hx : 0 < x) (h : x ≤ y) :
    Real.sqrt x ≤ Real.sqrt y :=
  Real.sqrt_le_sqrt h

end UndergradKB.Foundations.Course
