import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.NumberTheory.FermatPsp
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Cryptography

/-! # Judson–Beezer, chapter 7: cryptography (course layer)

Wrappers for the shift, affine and matrix ciphers, RSA and its correctness, and pseudoprimes;
the proofs are in `UndergradKB.AbstractAlgebra.Cryptography`. -/

namespace UndergradKB.AbstractAlgebra.Course

open UndergradKB.AbstractAlgebra

/-- AA-095. The shift cipher `p ↦ p + b` on `ℤ_n` (book: `n = 26`) is a bijection with inverse
`p ↦ p - b`. -/
@[kb "judson2026" "Example 7.1.1, p. 97"]
theorem judson_7_1_1 (n : ℕ) (b : ZMod n) :
    Function.Bijective (fun p : ZMod n => p + b) ∧ (∀ p : ZMod n, (p + b) - b = p) ∧
      ∀ c : ZMod n, (c - b) + b = c :=
  ⟨(shiftCipher_bijective n b).1, fun p => by simp, fun c => by simp⟩

/-- AA-096. The affine cipher `p ↦ a p + b` on `ℤ_n` can be decrypted exactly when
`gcd(a, n) = 1`, and then the inverse is `c ↦ a⁻¹ (c - b)`. -/
@[kb "judson2026" "Example 7.1.3, p. 98"]
theorem judson_7_1_3 (n a : ℕ) (b : ZMod n) :
    (Function.Bijective (fun p : ZMod n => (a : ZMod n) * p + b) ↔ Nat.Coprime a n) ∧
      ∀ (u : (ZMod n)ˣ) (p : ZMod n), (↑u⁻¹ : ZMod n) * (((u : ZMod n) * p + b) - b) = p :=
  ⟨affineCipher_bijective_iff n a b, fun u p => (affineCipher n u b).decrypt_encrypt p⟩

/-- AA-097. A matrix cipher `p ↦ A p + b` on blocks over `ℤ_26`: `A` is invertible iff `det A` is
a unit, and then the cipher is bijective with inverse `c ↦ A⁻¹ (c - b)`. -/
@[kb "judson2026" "Example 7.1.4, p. 98"]
theorem judson_7_1_4 {k : ℕ} (A : Matrix (Fin k) (Fin k) (ZMod 26)) (b : Fin k → ZMod 26) :
    (IsUnit A ↔ IsUnit A.det) ∧
      (IsUnit A.det → Function.Bijective (fun p : Fin k → ZMod 26 => A.mulVec p + b) ∧
        ∀ p : Fin k → ZMod 26, A⁻¹.mulVec ((A.mulVec p + b) - b) = p) :=
  ⟨matrix_invertible_iff_det_unit A, fun hA =>
    ⟨matrixCipher_bijective A hA b, (matrixCipher A hA b).decrypt_encrypt⟩⟩

/-- `φ(pq) = (p-1)(q-1)` for distinct primes. -/
private lemma totient_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.totient (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq), Nat.totient_prime hp,
    Nat.totient_prime hq]

/-- AA-098. RSA: for distinct primes `p, q`, `n = pq`, `m = φ(n)`, `E` coprime to `m` and
`D E ≡ 1 (mod m)`, decrypting `y ↦ y^D` undoes encrypting `x ↦ x^E` in `ℤ_n` (and conversely). -/
@[kb "judson2026" "Example 7.2.1, p. 99"]
theorem judson_7_2_1 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (E D : ℕ)
    (_hE : Nat.Coprime E (Nat.totient (p * q))) (hD : D * E ≡ 1 [MOD Nat.totient (p * q)]) :
    (∀ x : ZMod (p * q), (x ^ E) ^ D = x) ∧ ∀ y : ZMod (p * q), (y ^ D) ^ E = y := by
  rw [totient_mul_primes hp hq hpq] at hD
  refine ⟨fun x => rsa_correct hp hq hpq E D (by rw [Nat.mul_comm E D]; exact hD) x,
    fun y => rsa_correct hp hq hpq D E hD y⟩

/-- AA-099. RSA correctness: with `n = pq` for distinct primes and `D E ≡ 1 (mod φ(n))`,
`(x^E)^D ≡ x (mod n)` for every `x < n` (whether or not `x` is coprime to `n`). -/
@[kb "judson2026" "Discussion after Example 7.2.1, p. 100"]
theorem judson_7_2_rsa_correct {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (E D : ℕ)
    (hED : E * D ≡ 1 [MOD Nat.totient (p * q)]) (x : ℕ) (_hx : x < p * q) :
    (x ^ E) ^ D ≡ x [MOD p * q] := by
  rw [totient_mul_primes hp hq hpq] at hED
  have h := rsa_correct hp hq hpq E D hED (x : ZMod (p * q))
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact h

/-- AA-101. A pseudoprime to base `b` (odd composite `n` with `b^(n-1) ≡ 1 mod n`) is, for
`b ≠ 0`, an odd Fermat pseudoprime in Mathlib's sense. -/
@[kb "judson2026" "Definition (pseudoprime), p. 104"]
theorem judson_7_2_pseudoprime {n b : ℕ} (hb : b ≠ 0) :
    (Odd n ∧ 1 < n ∧ ¬ n.Prime ∧ b ^ (n - 1) ≡ 1 [MOD n]) ↔ Odd n ∧ Nat.FermatPsp n b :=
  isPseudoprime_iff_fermatPsp hb

/-- AA-101. The smallest Carmichael number, 561, is an odd composite that is a pseudoprime to
every base coprime to it. -/
@[kb "judson2026" "Definition (Carmichael number), p. 104"]
theorem judson_7_2_carmichael_561 :
    Nat.IsCarmichael 561 ∧ Odd 561 ∧
      ∀ b : ℕ, b.Coprime 561 → (Odd 561 ∧ 1 < 561 ∧ ¬ Nat.Prime 561 ∧ b ^ 560 ≡ 1 [MOD 561]) :=
  carmichael_561

end UndergradKB.AbstractAlgebra.Course
