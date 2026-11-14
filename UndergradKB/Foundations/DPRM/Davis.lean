import Mathlib.NumberTheory.Dioph
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Factorial.BigOperators
import UndergradKB.Foundations.DPRM.PolyBound
import UndergradKB.Foundations.DPRM.Arith

/-!
# Foundations, DPRM: Davis's bounded universal quantifier theorem

Diophantine sets are closed under bounded universal quantification (Davis 1953; we follow
M. Davis, *Hilbert's tenth problem is unsolvable*, Amer. Math. Monthly 80 (1973), Theorem 5.1):
if `S ⊆ ℕ^(1 + α)` is Diophantine and `y` is a Diophantine function, then
`{v | ∀ k < y v, (k, v) ∈ S}` is Diophantine (`dioph_forall_lt`).

The proof codes the `y v` witnesses by the Chinese remainder theorem with the pairwise coprime moduli
`1 + (k + 1) t`, `k < y`, where `t = Q!` for a bound `Q` on the values of the polynomial: the
condition becomes `1 + (e + 1) t = ∏_{k < y} (1 + (k + 1) t)`, `1 + (e + 1) t ∣ p (e, v, a)` and, for each
unknown, `1 + (e + 1) t ∣ a (a - 1) ⋯ (a - u)`, which says that modulo every prime factor of a modulus
the unknown is congruent to a number at most `u`.
-/

namespace UndergradKB.Foundations.DPRM

open Dioph Nat Finset

local infixr:67 " ::ₒ " => Option.elim'
local infixr:65 " ⊗ " => Sum.elim


/-! ### Number theory of the moduli `1 + c t` -/

/-- A prime factor of `1 + c t` does not divide `t`, so it exceeds `Q` when `Q! ∣ t`. -/
theorem lt_of_prime_dvd_one_add {Q t c p : ℕ} (hQ : Q ! ∣ t) (hp : p.Prime)
    (hd : p ∣ 1 + c * t) : Q < p := by
  by_contra h
  push Not at h
  have hpt : p ∣ t := (Nat.dvd_factorial hp.pos h).trans hQ
  have h1 : p ∣ 1 + c * t - c * t := Nat.dvd_sub hd (dvd_mul_of_dvd_right hpt c)
  rw [Nat.add_sub_cancel] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem coprime_one_add_mul_self (c t : ℕ) : Nat.Coprime (1 + c * t) t :=
  (Nat.coprime_add_mul_right_left 1 t c).2 (Nat.coprime_one_left t)

/-- The moduli `1 + (i + 1) t` are pairwise coprime when `Q! ∣ t` and the indices differ by at
most `Q`. -/
theorem coprime_one_add_mul {Q t i j : ℕ} (hQ : Q ! ∣ t) (hij : i < j) (hjQ : j - i ≤ Q) :
    Nat.Coprime (1 + (i + 1) * t) (1 + (j + 1) * t) := by
  apply Nat.coprime_of_dvd
  intro p hp h1 h2
  have hpQ := lt_of_prime_dvd_one_add hQ hp h1
  have h3 : p ∣ (j + 1) * (1 + (i + 1) * t) - (i + 1) * (1 + (j + 1) * t) :=
    Nat.dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  have e : (j + 1) * (1 + (i + 1) * t) = (j - i) + (i + 1) * (1 + (j + 1) * t) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    rw [show i + d + 1 - i = d + 1 by omega]
    ring
  rw [e, Nat.add_sub_cancel] at h3
  have := Nat.le_of_dvd (by omega) h3
  omega

/-- If `m` is coprime to `t` and divides both `1 + (e + 1) t` and `1 + (k + 1) t`, then
`e ≡ k (mod m)`. -/
theorem intModEq_of_dvd_one_add {m t e k : ℕ} (hmt : Nat.Coprime m t)
    (he : m ∣ 1 + (e + 1) * t) (hk : m ∣ 1 + (k + 1) * t) : (e : ℤ) ≡ k [ZMOD m] := by
  have h1 : (m : ℤ) ∣ ((1 + (e + 1) * t : ℕ) : ℤ) - ((1 + (k + 1) * t : ℕ) : ℤ) :=
    dvd_sub (Int.natCast_dvd_natCast.2 he) (Int.natCast_dvd_natCast.2 hk)
  have h2 : ((1 + (e + 1) * t : ℕ) : ℤ) - ((1 + (k + 1) * t : ℕ) : ℤ) = ((e : ℤ) - k) * t := by
    push_cast; ring
  rw [h2] at h1
  have h3 : (m : ℤ) ∣ (e : ℤ) - k := (Nat.isCoprime_iff_coprime.2 hmt).dvd_of_dvd_mul_right h1
  exact (Int.modEq_iff_dvd.2 h3).symm

/-- A prime dividing the falling factorial `a (a - 1) ⋯ (a - n + 1)` divides one of its factors. -/
theorem exists_of_prime_dvd_descFactorial {p a : ℕ} (hp : p.Prime) :
    ∀ n, n ≤ a → p ∣ a.descFactorial n → ∃ j < n, j ≤ a ∧ p ∣ a - j
  | 0, _, h => by
    rw [Nat.descFactorial_zero, Nat.dvd_one] at h
    exact absurd h hp.ne_one
  | n + 1, hn, h => by
    rw [Nat.descFactorial_succ] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ⟨n, Nat.lt_succ_self n, by omega, h⟩
    · obtain ⟨j, hj, hja, hd⟩ := exists_of_prime_dvd_descFactorial hp n (by omega) h
      exact ⟨j, by omega, hja, hd⟩

theorem sub_dvd_descFactorial (a : ℕ) {x : ℕ} : ∀ {n}, x < n → (a - x) ∣ a.descFactorial n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [Nat.descFactorial_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact dvd_mul_of_dvd_right (sub_dvd_descFactorial a h) _
    · exact dvd_mul_right _ _

theorem prod_one_add_eq (t : ℕ) :
    ∀ y, ∃ c, y ≤ c ∧ ∏ k ∈ range y, (1 + (k + 1) * t) = 1 + c * t
  | 0 => ⟨0, le_rfl, by simp⟩
  | y + 1 => by
    obtain ⟨c, hc, h⟩ := prod_one_add_eq t y
    refine ⟨c + (y + 1) + c * (y + 1) * t, ?_, ?_⟩
    · exact (by omega : y + 1 ≤ c + (y + 1)).trans (Nat.le_add_right _ _)
    · rw [prod_range_succ, h]
      ring

/-- Pairwise coprime integers dividing a number: their product divides it. -/
theorem prod_dvd_of_coprime_nat {s : Finset ℕ} {m : ℕ → ℕ} {n : ℤ}
    (hco : (s : Set ℕ).Pairwise (Function.onFun Nat.Coprime m)) (h : ∀ k ∈ s, (m k : ℤ) ∣ n) :
    ((∏ k ∈ s, m k : ℕ) : ℤ) ∣ n := by
  push_cast
  refine Finset.prod_dvd_of_coprime (fun i hi j hj hij => ?_) h
  exact Nat.isCoprime_iff_coprime.2 (hco hi hj hij)

end UndergradKB.Foundations.DPRM
