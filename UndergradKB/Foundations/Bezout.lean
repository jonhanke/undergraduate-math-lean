import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-! # Combinations `ax + by`, linear congruences and linear Diophantine equations

* Hammack, *Book of Proof*, Section 7.3: for `a, b ∈ ℕ` there is a unique `d ∈ ℕ` whose multiples are exactly the integers
  `ax + by` (it is `gcd(a, b)`), FO-115.
* Levin, *Discrete Mathematics*, Section 6.2.4: if `gcd(a, n) ∤ b` then `ax ≡ b (mod n)` has no solution; we prove the
  full criterion (solvable iff `gcd(a, n) ∣ b`), FO-127.
* Levin, Section 6.2.5: the linear Diophantine equation `ax + by = c` is solvable iff `gcd(a, b) ∣ c`, and from one
  solution `(x₀, y₀)` all solutions are `x = x₀ + (b/d) k`, `y = y₀ - (a/d) k` with `d = gcd(a, b)`, FO-128.
-/

namespace UndergradKB.Foundations

/-! ## The multiples of the greatest common divisor (FO-115) -/

/-- FO-115 (Hammack, §7.3). For `a, b ∈ ℕ` there is a unique positive `d ∈ ℕ` such that an integer `m` is a multiple
of `d` iff `m = ax + by` for some integers `x, y`; the book's proof, with `d = gcd(a, b)`. -/
@[kb "hammack2018" "Prop §7.3, p. 165"]
theorem existsUnique_multiples_eq_combinations (a b : ℕ) (ha : 0 < a) :
    ∃! d : ℕ, 0 < d ∧ ∀ m : ℤ, (d : ℤ) ∣ m ↔ ∃ x y : ℤ, m = a * x + b * y := by
  set g := Nat.gcd a b with hg
  have hgA : (g : ℤ) ∣ a := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b)
  have hgB : (g : ℤ) ∣ b := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b)
  have hcomb : ∀ m : ℤ, (g : ℤ) ∣ m ↔ ∃ x y : ℤ, m = a * x + b * y := by
    intro m
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨Nat.gcdA a b * t, Nat.gcdB a b * t, ?_⟩
      rw [hg, Nat.gcd_eq_gcd_ab]
      ring
    · rintro ⟨x, y, rfl⟩
      exact dvd_add (dvd_mul_of_dvd_left hgA x) (dvd_mul_of_dvd_left hgB y)
  refine ⟨g, ⟨Nat.gcd_pos_of_pos_left b ha, hcomb⟩, ?_⟩
  rintro d' ⟨_, hd'⟩
  have h1 : (d' : ℤ) ∣ a := (hd' a).mpr ⟨1, 0, by ring⟩
  have h2 : (d' : ℤ) ∣ b := (hd' b).mpr ⟨0, 1, by ring⟩
  have hdg : d' ∣ g := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp h1) (Int.natCast_dvd_natCast.mp h2)
  have hgd : g ∣ d' := Int.natCast_dvd_natCast.mp ((hcomb d').mpr ((hd' d').mp dvd_rfl))
  exact Nat.dvd_antisymm hdg hgd

/-! ## Linear congruences (FO-127) -/

/-- FO-127 (Levin, §6.2.4). The linear congruence `ax ≡ b (mod n)` has an integer solution iff `gcd(a, n) ∣ b`; in
particular, if `gcd(a, n) ∤ b` there is no solution (the book's statement). -/
@[kb "levin2025" "Box §6.2.4, p. 463", kb "levin2025" "Ex 6.2.6, p. 461"]
theorem exists_linear_congruence_iff (a b n : ℤ) :
    (∃ x : ℤ, a * x ≡ b [ZMOD n]) ↔ (Int.gcd a n : ℤ) ∣ b := by
  constructor
  · rintro ⟨x, hx⟩
    have h := (Int.modEq_iff_dvd.mp hx)
    have h1 : (Int.gcd a n : ℤ) ∣ b - a * x := (Int.gcd_dvd_right a n).trans h
    have h2 : (Int.gcd a n : ℤ) ∣ a * x := dvd_mul_of_dvd_left (Int.gcd_dvd_left a n) x
    simpa using dvd_add h1 h2
  · rintro ⟨t, rfl⟩
    refine ⟨Int.gcdA a n * t, Int.modEq_iff_dvd.mpr ⟨Int.gcdB a n * t, ?_⟩⟩
    rw [Int.gcd_eq_gcd_ab]
    ring

/-- FO-127. The book's form: if `gcd(a, n) ∤ b` then `ax ≡ b (mod n)` has no solution. -/
@[kb "levin2025" "Box §6.2.4, p. 463"]
theorem no_solution_linear_congruence (a b n : ℤ) (h : ¬ (Int.gcd a n : ℤ) ∣ b) :
    ¬ ∃ x : ℤ, a * x ≡ b [ZMOD n] :=
  fun hx => h ((exists_linear_congruence_iff a b n).mp hx)

/-! ## Linear Diophantine equations (FO-128) -/

/-- FO-128 (Levin, §6.2.5). The linear Diophantine equation `ax + by = c` has an integer solution iff
`gcd(a, b) ∣ c`. -/
@[kb "levin2025" "Box §6.2.5, p. 463"]
theorem exists_linear_diophantine_iff (a b c : ℤ) :
    (∃ x y : ℤ, a * x + b * y = c) ↔ (Int.gcd a b : ℤ) ∣ c := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) x)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) y)
  · rintro ⟨t, rfl⟩
    refine ⟨Int.gcdA a b * t, Int.gcdB a b * t, ?_⟩
    rw [Int.gcd_eq_gcd_ab]
    ring

/-- FO-128 (Levin, §6.2.5 and Example 6.2.7). For nonzero `a, b` with `d = gcd(a, b)` and one solution `(x₀, y₀)` of
`ax + by = c`, the integer solutions are exactly `x = x₀ + (b/d) k`, `y = y₀ - (a/d) k` for `k ∈ ℤ`. -/
@[kb "levin2025" "Ex 6.2.7, p. 465"]
theorem linear_diophantine_solutions {a b c x₀ y₀ : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : a * x₀ + b * y₀ = c) (x y : ℤ) :
    a * x + b * y = c ↔
      ∃ k : ℤ, x = x₀ + b / (Int.gcd a b : ℤ) * k ∧ y = y₀ - a / (Int.gcd a b : ℤ) * k := by
  set d : ℤ := (Int.gcd a b : ℤ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast Int.gcd_ne_zero_left ha
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  rw [← hd] at ha' hb'
  have hadiv : a / d = a' := by rw [ha']; exact Int.mul_ediv_cancel_left a' hd0
  have hbdiv : b / d = b' := by rw [hb']; exact Int.mul_ediv_cancel_left b' hd0
  rw [hadiv, hbdiv]
  constructor
  · intro h
    have hcop : IsCoprime a' b' := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := Int.gcd_div_gcd_div_gcd (Int.gcd_pos_of_ne_zero_left b ha)
      rwa [← hd, hadiv, hbdiv] at this
    have key : a' * (x - x₀) = b' * (y₀ - y) := by
      apply mul_left_cancel₀ hd0
      have e := h.trans h₀.symm
      rw [ha', hb'] at e
      linear_combination e
    have hb'dvd : b' ∣ x - x₀ := hcop.symm.dvd_of_dvd_mul_left ⟨y₀ - y, key⟩
    obtain ⟨k, hk⟩ := hb'dvd
    have hb'0 : b' ≠ 0 := by rintro rfl; simp at hb'; exact hb hb'
    refine ⟨k, by linarith, ?_⟩
    have : b' * (a' * k) = b' * (y₀ - y) := by rw [← key, hk]; ring
    have := mul_left_cancel₀ hb'0 this
    linarith
  · rintro ⟨k, rfl, rfl⟩
    rw [← h₀, ha', hb']
    ring

end UndergradKB.Foundations
