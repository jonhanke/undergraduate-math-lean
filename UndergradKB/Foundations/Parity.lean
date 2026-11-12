import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Order.Setoid.Partition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import UndergradKB.Common

/-!
# Foundations gap rows: parity, primes, gcd/lcm and small number-theory facts

Rows FO-101, 108, 110, 117, 125, 132, 134, 135, 137, 183 of the Foundations checklist.
-/

namespace UndergradKB.Foundations

/-! ## FO-101: parity -/

/-- FO-101. Two integers have the same parity when both are even or both are odd. -/
def SameParity (m n : ℤ) : Prop := (Even m ∧ Even n) ∨ (Odd m ∧ Odd n)

/-- FO-101. Two integers have opposite parity when one is even and the other odd. -/
def OppositeParity (m n : ℤ) : Prop := (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)

/-- FO-101. Integers have the same parity iff their difference is even. -/
@[kb "hammack2018" "Definition 4.3, p. 127"]
theorem sameParity_iff_even_sub (m n : ℤ) : SameParity m n ↔ Even (m - n) := by
  rw [Int.even_sub]
  unfold SameParity
  simp only [← Int.not_even_iff_odd]
  tauto

/-- FO-101. Integers have opposite parity iff their difference is odd. -/
@[kb "hammack2018" "Definition 4.3, p. 127"]
theorem oppositeParity_iff_odd_sub (m n : ℤ) : OppositeParity m n ↔ Odd (m - n) := by
  rw [← Int.not_even_iff_odd, Int.even_sub]
  unfold OppositeParity
  simp only [← Int.not_even_iff_odd]
  tauto

/-! ## FO-108: primes and composites -/

/-- FO-108. A natural number is composite when it exceeds 1 and is not prime. -/
def Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- FO-108. A number is prime iff it has exactly two positive divisors. -/
@[kb "hammack2018" "Definition 4.5, p. 128"]
theorem prime_iff_card_divisors_eq_two (n : ℕ) : n.Prime ↔ n.divisors.card = 2 := by
  constructor
  · intro h
    rw [Nat.Prime.divisors h, Finset.card_pair h.one_lt.ne]
  · intro h
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at h
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp at h
    have hn : 1 < n := by omega
    rw [Nat.prime_def]
    refine ⟨hn, fun m hm => ?_⟩
    have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hn0]
    have heq : ({1, n} : Finset ℕ) = n.divisors :=
      Finset.eq_of_subset_of_card_le hsub (by rw [h, Finset.card_pair hn.ne])
    have : m ∈ n.divisors := Nat.mem_divisors.2 ⟨hm, hn0⟩
    rw [← heq] at this
    simpa using this

/-- FO-108. A number above 1 is composite iff it has more than two positive divisors. -/
@[kb "hammack2018" "Definition 4.5, p. 128"]
theorem composite_iff_two_lt_card_divisors (n : ℕ) : Composite n ↔ 2 < n.divisors.card := by
  unfold Composite
  rw [prime_iff_card_divisors_eq_two]
  constructor
  · rintro ⟨hn, hp⟩
    have hn0 : n ≠ 0 := by omega
    have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hn0]
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (by omega)] at this
    omega
  · intro h
    refine ⟨?_, by omega⟩
    by_contra hn
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp at h

/-- FO-108. The number 1 is neither prime nor composite. -/
@[kb "hammack2018" "Definition 4.5, p. 128"]
theorem one_neither_prime_nor_composite : ¬ Nat.Prime 1 ∧ ¬ Composite 1 :=
  ⟨Nat.not_prime_one, fun h => absurd h.1 (lt_irrefl 1)⟩

/-! ## FO-110: gcd and lcm as largest common divisor and smallest common multiple -/

/-- FO-110. For integers not both zero, `gcd` is the largest of their common divisors. -/
@[kb "hammack2018" "Definition 4.6, p. 128", kb "levin2025" "Box §6.2.4, p. 460"]
theorem gcd_isGreatest_common_divisor (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    IsGreatest {d : ℤ | d ∣ a ∧ d ∣ b} (Int.gcd a b : ℤ) := by
  refine ⟨⟨Int.gcd_dvd_left a b, Int.gcd_dvd_right a b⟩, fun d ⟨hda, hdb⟩ => ?_⟩
  have hpos : 0 < Int.gcd a b := Int.gcd_pos_iff.2 h
  exact Int.le_of_dvd (by exact_mod_cast hpos) (Int.dvd_coe_gcd hda hdb)

/-- FO-110. For nonzero integers, `lcm` is the smallest positive common multiple. -/
@[kb "hammack2018" "Definition 4.6, p. 128"]
theorem lcm_isLeast_positive_common_multiple (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsLeast {m : ℤ | 0 < m ∧ a ∣ m ∧ b ∣ m} (Int.lcm a b : ℤ) := by
  refine ⟨⟨?_, Int.dvd_lcm_left a b, Int.dvd_lcm_right a b⟩, fun m ⟨hm, ham, hbm⟩ => ?_⟩
  · exact_mod_cast Nat.pos_of_ne_zero (Int.lcm_ne_zero ha hb)
  · exact Int.le_of_dvd hm (by rw [Int.coe_lcm]; exact _root_.lcm_dvd ham hbm)

/-! ## FO-117: AM-GM for two numbers -/

/-- FO-117. For positive reals, `2 √(xy) ≤ x + y`. -/
@[kb "hammack2018" "Prop §4.3, p. 135"]
theorem two_mul_sqrt_mul_le_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  have h : Real.sqrt (x * y) ≤ (x + y) / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [sq_nonneg (x - y)]⟩
  linarith

/-! ## FO-125: remainder classes -/

/-- FO-125. Every integer has exactly one remainder `r` with `0 ≤ r < b` on division by `b > 0`. -/
@[kb "levin2025" "Box §6.2.2, p. 455"]
theorem exists_unique_remainder (b : ℤ) (hb : 0 < b) (a : ℤ) :
    ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  refine ⟨a % b, ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb, (Int.mod_modEq a b).symm⟩, ?_⟩
  rintro r ⟨h0, h1, h2⟩
  have : a % b = r % b := h2
  rw [this, Int.emod_eq_of_lt h0 h1]

/-- FO-125. The remainder class of `r` modulo `b`: the integers leaving remainder `r`. -/
def remainderClass (b r : ℤ) : Set ℤ := {a | a % b = r}

/-- FO-125. The `b` remainder classes modulo `b > 0` partition the integers into exactly `b` blocks. -/
@[kb "levin2025" "Box §6.2.2, p. 455"]
theorem remainderClasses_partition (b : ℕ) (hb : 0 < b) :
    Setoid.IsPartition ((remainderClass b) '' Set.Ico (0 : ℤ) b) ∧
      ((remainderClass b) '' Set.Ico (0 : ℤ) b).ncard = b := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hmem : ∀ r ∈ Set.Ico (0 : ℤ) b, r ∈ remainderClass b r := by
    intro r hr
    exact Int.emod_eq_of_lt hr.1 hr.2
  constructor
  · refine ⟨?_, fun a => ?_⟩
    · rintro ⟨r, hr, h⟩
      have := hmem r hr
      rw [h] at this
      exact this
    · refine ⟨remainderClass b (a % b), ⟨⟨a % b, ⟨Int.emod_nonneg _ hb'.ne',
        Int.emod_lt_of_pos _ hb'⟩, rfl⟩, ?_⟩, ?_⟩
      · rfl
      · rintro C ⟨⟨r, hr, rfl⟩, ha⟩
        have : a % b = r := ha
        rw [this]
  · rw [Set.InjOn.ncard_image]
    · rw [← Finset.coe_Ico, Set.ncard_coe_finset]
      simp
    · intro r hr s hs h
      have := hmem r hr
      rw [h] at this
      have h2 : r % b = s := this
      rw [Int.emod_eq_of_lt hr.1 hr.2] at h2
      exact h2

/-! ## FO-132: no integer solution of a^2 - 4b = 2 -/

/-- FO-132. There are no integers `a`, `b` with `a^2 - 4b = 2`. -/
@[kb "hammack2018" "Prop §6, p. 149", kb "levin2025" "Ex 1.4.17, p. 93"]
theorem no_int_sq_sub_four_mul_eq_two : ¬ ∃ a b : ℤ, a ^ 2 - 4 * b = 2 := by
  rintro ⟨a, b, h⟩
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' a
  · have : (2 * k) ^ 2 = 4 * (k * k) := by ring
    omega
  · have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    omega

/-! ## FO-134: nonzero rationals are products of two irrationals -/

/-- FO-134. Every nonzero rational is the product of two irrational numbers. -/
@[kb "hammack2018" "Prop §6.3, p. 154"]
theorem rat_eq_mul_irrationals (q : ℚ) (hq : q ≠ 0) :
    ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ a * b = q := by
  refine ⟨Real.sqrt 2, q / Real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two.ratCast_div hq, ?_⟩
  have : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-! ## FO-135: consecutive integers are coprime -/

/-- FO-135. No integer `a ≥ 2` divides both `b` and `b + 1`. -/
@[kb "hammack2018" "Prop §6.2, p. 154"]
theorem not_dvd_both_consecutive (a b : ℤ) (ha : 2 ≤ a) : ¬ (a ∣ b ∧ a ∣ b + 1) := by
  rintro ⟨h1, h2⟩
  have h3 : a ∣ 1 := by
    have := dvd_sub h2 h1
    simpa using this
  have := Int.le_of_dvd one_pos h3
  omega

/-! ## FO-137: no real x with x^4 < x < x^2 -/

/-- FO-137. There is no real number `x` with `x^4 < x < x^2`. -/
@[kb "hammack2018" "Example 9.3, p. 188", kb "hammack2018" "Example 9.5, p. 190"]
theorem no_real_x4_lt_x_lt_x2 : ¬ ∃ x : ℝ, x ^ 4 < x ∧ x < x ^ 2 := by
  rintro ⟨x, h1, h2⟩
  rcases lt_or_ge x 0 with hx | hx
  · nlinarith [pow_two_nonneg (x ^ 2)]
  · have hx0 : 0 < x := by
      rcases hx.eq_or_lt with h | h
      · rw [← h] at h2; norm_num at h2
      · exact h
    have hx1 : 1 < x := by nlinarith
    nlinarith [mul_pos hx0 hx0, mul_pos (mul_pos hx0 hx0) hx0]

/-! ## FO-183: 5 divides n^5 - n -/

/-- FO-183. For every natural number `n`, `5` divides `n^5 - n`; proved by induction on `n`. -/
@[kb "hammack2018" "Prop §10.1, p. 195"]
theorem five_dvd_pow_five_sub (n : ℕ) : (5 : ℤ) ∣ (n : ℤ) ^ 5 - n := by
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (k : ℤ) ^ 4 + 2 * k ^ 3 + 2 * k ^ 2 + k, ?_⟩
    push_cast
    linear_combination hc

end UndergradKB.Foundations
