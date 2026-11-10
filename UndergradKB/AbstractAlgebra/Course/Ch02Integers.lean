import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Integers

/-! # Judson–Beezer, chapter 2: the integers (course layer)

Thin wrappers around Mathlib for induction, the division algorithm, gcd, and the fundamental theorem
of arithmetic. -/

namespace UndergradKB.AbstractAlgebra.Course

/-- AA-011. First principle of induction, starting at `n₀`: a base case and the step
`P k → P (k+1)` for `k ≥ n₀` give `P n` for all `n ≥ n₀`. -/
@[kb "judson2026" "Principle 2.1.1, p. 31"]
theorem judson_2_1_1 {P : ℕ → Prop} (n₀ : ℕ) (base : P n₀) (step : ∀ k, n₀ ≤ k → P k → P (k + 1)) :
    ∀ n, n₀ ≤ n → P n :=
  fun n hn => Nat.le_induction base (fun k hk ih => step k hk ih) n hn

/-- AA-015. Binomial theorem: `(a+b)^n = ∑ₖ C(n,k) a^k b^(n-k)` (in any commutative semiring). -/
@[kb "judson2026" "Example 2.1.4, p. 31"]
theorem judson_2_1_4 {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * a ^ k * b ^ (n - k) := by
  rw [add_pow]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- AA-012. Second principle of induction: if `P n` follows from `P m` for all `m < n`, then `P`
holds for every natural number. -/
@[kb "judson2026" "Principle 2.1.5, p. 32"]
theorem judson_2_1_5 {P : ℕ → Prop} (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n :=
  fun n => Nat.strong_induction_on n h

/-- AA-013. Well-ordering: every nonempty set of positive integers has a least element. -/
@[kb "judson2026" "Principle 2.1.6, p. 32"]
theorem judson_2_1_6 (S : Set ℕ) (_hpos : ∀ n ∈ S, 0 < n) (hne : S.Nonempty) :
    ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  obtain ⟨m, hm, hmin⟩ := wellFounded_lt.has_min S hne
  exact ⟨m, hm, fun n hn => not_lt.mp (hmin n hn)⟩

/-- AA-016. Division algorithm: for `b > 0` there are unique integers `q, r` with `a = b q + r`
and `0 ≤ r < b`. -/
@[kb "judson2026" "Theorem 2.2.1, p. 33"]
theorem judson_2_2_1 (a b : ℤ) (hb : 0 < b) :
    ∃! qr : ℤ × ℤ, a = b * qr.1 + qr.2 ∧ 0 ≤ qr.2 ∧ qr.2 < b := by
  refine ⟨(a / b, a % b), ⟨?_, Int.emod_nonneg a hb.ne', Int.emod_lt_of_pos a hb⟩, ?_⟩
  · exact (Int.mul_ediv_add_emod a b).symm
  · rintro ⟨q, r⟩ ⟨h1, h2, h3⟩
    have := (Int.ediv_emod_unique (a := a) (q := q) (r := r) hb).mpr ⟨by simp at h1; linarith, h2, h3⟩
    simp [this.1, this.2]

/-- AA-018. The gcd of two integers is a common divisor divisible by every common divisor, and is
an integer combination `a r + b s`. -/
@[kb "judson2026" "Theorem 2.2.2, p. 33"]
theorem judson_2_2_2 (a b : ℤ) :
    ((Int.gcd a b : ℤ) ∣ a) ∧ ((Int.gcd a b : ℤ) ∣ b) ∧
    (∀ d : ℤ, d ∣ a → d ∣ b → d ∣ (Int.gcd a b : ℤ)) ∧
    ∃ r s : ℤ, (Int.gcd a b : ℤ) = a * r + b * s :=
  ⟨Int.gcd_dvd_left a b, Int.gcd_dvd_right a b, fun _ h1 h2 => Int.dvd_coe_gcd h1 h2,
    ⟨Int.gcdA a b, Int.gcdB a b, Int.gcd_eq_gcd_ab a b⟩⟩

/-- AA-018. Integers `a, b` are relatively prime iff `a r + b s = 1` for some integers `r, s`. -/
@[kb "judson2026" "Corollary 2.2.3, p. 34"]
theorem judson_2_2_3 (a b : ℤ) : Int.gcd a b = 1 ↔ ∃ r s : ℤ, a * r + b * s = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  constructor
  · rintro ⟨r, s, h⟩
    exact ⟨r, s, by linarith⟩
  · rintro ⟨r, s, h⟩
    exact ⟨r, s, by linarith⟩

/-- AA-021. Euclid's lemma: a prime dividing a product divides one of the factors. -/
@[kb "judson2026" "Lemma 2.2.5, p. 35"]
theorem judson_2_2_5 {p : ℕ} (hp : p.Prime) (a b : ℕ) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  (Nat.Prime.dvd_mul hp).mp h

/-- AA-022. There are infinitely many primes. -/
@[kb "judson2026" "Theorem 2.2.6, p. 35"]
theorem judson_2_2_6 : Set.Infinite {p : ℕ | p.Prime} :=
  Nat.infinite_setOfPred_prime

/-- AA-023. Fundamental theorem of arithmetic: every integer `n > 1` is a product of primes, and
any two such factorizations agree up to order. -/
@[kb "judson2026" "Theorem 2.2.7, p. 35"]
theorem judson_2_2_7 (n : ℕ) (hn : 1 < n) :
    ∃ l : List ℕ, (∀ p ∈ l, p.Prime) ∧ l.prod = n ∧
      ∀ l' : List ℕ, (∀ p ∈ l', p.Prime) → l'.prod = n → l'.Perm l :=
  ⟨n.primeFactorsList, fun _ hp => Nat.prime_of_mem_primeFactorsList hp,
    Nat.prod_primeFactorsList (by omega), fun _ h1 h2 => Nat.primeFactorsList_unique h2 h1⟩

/-- AA-014. Lemma 2.1.7: the principle of induction implies that 1 is the least positive integer. -/
@[kb "judson2026" "Lemma 2.1.7, p. 32"]
theorem judson_2_1_7 (h : UndergradKB.AbstractAlgebra.PrincipleOfInduction) (n : ℕ) (hn : 0 < n) :
    1 ≤ n :=
  UndergradKB.AbstractAlgebra.one_le_of_induction h n hn

/-- AA-014. Theorem 2.1.8: the principles of induction, strong induction and well-ordering
are equivalent. -/
@[kb "judson2026" "Theorem 2.1.8, p. 32"]
theorem judson_2_1_8 :
    List.TFAE [UndergradKB.AbstractAlgebra.PrincipleOfInduction,
      UndergradKB.AbstractAlgebra.PrincipleOfStrongInduction,
      UndergradKB.AbstractAlgebra.PrincipleOfWellOrdering] :=
  UndergradKB.AbstractAlgebra.induction_strongInduction_wellOrdering_tfae

end UndergradKB.AbstractAlgebra.Course
