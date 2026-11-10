import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 2: the integers (and the polar form and repeated squares of chapter 4)

Results of chapter 2 that Mathlib does not state in the book's form. Here the natural numbers
`ℕ` of the book are the integers `n ≥ 1`. -/

namespace UndergradKB.AbstractAlgebra

section Induction

/-- The Principle of Mathematical Induction, for sets of positive integers. -/
def PrincipleOfInduction : Prop :=
  ∀ S : Set ℕ, 1 ∈ S → (∀ n, 1 ≤ n → n ∈ S → n + 1 ∈ S) → ∀ n, 1 ≤ n → n ∈ S

/-- The Principle of Strong Induction, for sets of positive integers. -/
def PrincipleOfStrongInduction : Prop :=
  ∀ S : Set ℕ, (∀ n, 1 ≤ n → (∀ k, 1 ≤ k → k < n → k ∈ S) → n ∈ S) → ∀ n, 1 ≤ n → n ∈ S

/-- The Principle of Well-Ordering: a set containing a positive integer has a least positive
element. -/
def PrincipleOfWellOrdering : Prop :=
  ∀ S : Set ℕ, (∃ n, 1 ≤ n ∧ n ∈ S) → ∃ m, 1 ≤ m ∧ m ∈ S ∧ ∀ k, 1 ≤ k → k ∈ S → m ≤ k

/-- AA-014. Lemma 2.1.7: induction implies that 1 is the least positive integer. -/
@[kb "judson2026" "Lemma 2.1.7, p. 32"]
theorem one_le_of_induction (h : PrincipleOfInduction) (n : ℕ) (hn : 0 < n) : 1 ≤ n :=
  h {n | 1 ≤ n} (show 1 ≤ 1 from le_rfl)
    (fun m hm _ => show 1 ≤ m + 1 by omega) n hn

/-- AA-014. Theorem 2.1.8: induction implies well-ordering (as in the book, by induction on a bound
for an element of `S`). -/
@[kb "judson2026" "Theorem 2.1.8, p. 32"]
theorem wellOrdering_of_induction (h : PrincipleOfInduction) : PrincipleOfWellOrdering := by
  intro S ⟨m, hm1, hmS⟩
  let P : ℕ → Prop := fun n => (∃ k, 1 ≤ k ∧ k ∈ S ∧ k ≤ n) →
      ∃ m, 1 ≤ m ∧ m ∈ S ∧ ∀ k, 1 ≤ k → k ∈ S → m ≤ k
  have base : P 1 := by
    rintro ⟨k, hk1, hkS, hk⟩
    have : k = 1 := by omega
    subst this
    exact ⟨1, le_rfl, hkS, fun j hj _ => hj⟩
  have step : ∀ n, 1 ≤ n → P n → P (n + 1) := by
    intro n hn ih ⟨k, hk1, hkS, hk⟩
    by_cases hex : ∃ k', 1 ≤ k' ∧ k' ∈ S ∧ k' ≤ n
    · exact ih hex
    · have hex' : ∀ k', 1 ≤ k' → k' ∈ S → n < k' := fun k' h1 h2 => by
        by_contra hc
        exact hex ⟨k', h1, h2, by omega⟩
      have hkn : k = n + 1 := by have := hex' k hk1 hkS; omega
      subst hkn
      exact ⟨n + 1, hk1, hkS, fun j hj hjS => by have := hex' j hj hjS; omega⟩
  have key : ∀ n, 1 ≤ n → P n := h {n | P n} base (fun n hn hP => step n hn hP)
  exact key m hm1 ⟨m, hm1, hmS, le_rfl⟩

/-- AA-014. Well-ordering implies strong induction. -/
theorem strongInduction_of_wellOrdering (h : PrincipleOfWellOrdering) :
    PrincipleOfStrongInduction := by
  intro S hS n hn
  by_contra hnS
  obtain ⟨m, hm1, hmS, hmin⟩ := h {n | n ∉ S} ⟨n, hn, hnS⟩
  refine hmS (hS m hm1 fun k hk1 hkm => ?_)
  by_contra hkS
  exact absurd (hmin k hk1 hkS) (by omega)

/-- AA-014. Strong induction implies ordinary induction. -/
theorem induction_of_strongInduction (h : PrincipleOfStrongInduction) :
    PrincipleOfInduction := by
  intro S h1 hstep
  refine h S (fun n hn ih => ?_)
  rcases Nat.eq_or_lt_of_le hn with rfl | hlt
  · exact h1
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    exact hstep p (by omega) (ih p (by omega) (by omega))

/-- AA-014. The principles of induction, strong induction and well-ordering are equivalent. -/
@[kb "judson2026" "Theorem 2.1.8, p. 32"]
theorem induction_strongInduction_wellOrdering_tfae :
    List.TFAE [PrincipleOfInduction, PrincipleOfStrongInduction, PrincipleOfWellOrdering] := by
  tfae_have 1 → 3 := wellOrdering_of_induction
  tfae_have 3 → 2 := strongInduction_of_wellOrdering
  tfae_have 2 → 1 := induction_of_strongInduction
  tfae_finish

end Induction

section GCD

/-- AA-017. A common divisor of `a` and `b`, nonnegative and divisible by every common divisor,
is `gcd a b`; and `Int.gcd a b` has these properties. -/
@[kb "judson2026" "Definition (greatest common divisor), p. 33"]
theorem gcd_universal_property (a b d : ℤ) :
    (0 ≤ d ∧ d ∣ a ∧ d ∣ b ∧ ∀ c : ℤ, c ∣ a → c ∣ b → c ∣ d) ↔ d = (Int.gcd a b : ℤ) := by
  constructor
  · rintro ⟨h0, hda, hdb, hmax⟩
    exact Int.dvd_antisymm h0 (by positivity) (Int.dvd_coe_gcd hda hdb)
      (hmax _ (Int.gcd_dvd_left a b) (Int.gcd_dvd_right a b))
  · rintro rfl
    exact ⟨by positivity, Int.gcd_dvd_left a b, Int.gcd_dvd_right a b,
      fun c h1 h2 => Int.dvd_coe_gcd h1 h2⟩

end GCD

section Polar

open Complex

/-- AA-057. Polar form multiplication via the exponential: moduli multiply, arguments add. -/
@[kb "judson2026" "Proposition 4.2.5, p. 64"]
theorem polar_mul_exp (r s θ φ : ℝ) :
    ((r : ℂ) * exp (θ * I)) * ((s : ℂ) * exp (φ * I)) = ((r * s : ℝ) : ℂ) * exp ((θ + φ : ℝ) * I) := by
  push_cast
  rw [add_mul, exp_add]
  ring

/-- AA-057. The same in cosine/sine form (`cis θ = cos θ + i sin θ`). -/
theorem polar_mul_cos_sin (r s θ φ : ℝ) :
    ((r : ℂ) * (Real.cos θ + Real.sin θ * I)) * ((s : ℂ) * (Real.cos φ + Real.sin φ * I)) =
      ((r * s : ℝ) : ℂ) * (Real.cos (θ + φ) + Real.sin (θ + φ) * I) := by
  rw [Real.cos_add, Real.sin_add]
  push_cast
  ring_nf
  rw [I_sq]
  ring

end Polar

section RepeatedSquares

/-- The binary method: `go n sq m acc` multiplies `acc` by `sq^(2^i)` for each binary digit `1` of
`m` (position `i`), reducing modulo `n` at each step. -/
def powModGo (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | sq, m, acc =>
    if h : m = 0 then acc
    else powModGo n (sq * sq % n) (m / 2) (if m % 2 = 1 then acc * sq % n else acc)
termination_by _ m _ => m
decreasing_by omega

/-- AA-062. Computing `a ^ m mod n` by repeated squares of `a` along the binary digits of `m`. -/
def powModBinary (a m n : ℕ) : ℕ := powModGo n (a % n) m (1 % n) % n

theorem powModGo_spec (n : ℕ) (m : ℕ) : ∀ sq acc : ℕ,
    powModGo n sq m acc % n = acc * sq ^ m % n := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro sq acc
    rw [powModGo]
    by_cases h : m = 0
    · simp [h]
    · simp only [h, dite_false]
      have hlt : m / 2 < m := by omega
      rw [ih _ hlt]
      have hm : sq ^ m = (sq * sq) ^ (m / 2) * sq ^ (m % 2) := by
        rw [← pow_two, ← pow_mul, ← pow_add]
        congr 1
        omega
      rw [hm]
      have h1 : (sq * sq % n) ^ (m / 2) ≡ (sq * sq) ^ (m / 2) [MOD n] :=
        (Nat.mod_modEq _ _).pow _
      split_ifs with hodd
      · rw [hodd, pow_one]
        refine ((Nat.mod_modEq (acc * sq) n).mul h1).trans ?_
        rw [show acc * sq * (sq * sq) ^ (m / 2) = acc * ((sq * sq) ^ (m / 2) * sq) by ring]
      · have : m % 2 = 0 := by omega
        rw [this, pow_zero, mul_one]
        refine (Nat.ModEq.refl acc).mul h1 |>.trans ?_
        rw [mul_comm acc]

/-- AA-062. The binary method computes `a ^ m mod n`. -/
@[kb "judson2026" "Section 4.3, p. 66-67"]
theorem powModBinary_eq (a m n : ℕ) : powModBinary a m n = a ^ m % n := by
  unfold powModBinary
  rw [powModGo_spec]
  have := (Nat.mod_modEq 1 n).mul ((Nat.mod_modEq a n).pow m)
  rw [one_mul] at this
  exact this

end RepeatedSquares

end UndergradKB.AbstractAlgebra
