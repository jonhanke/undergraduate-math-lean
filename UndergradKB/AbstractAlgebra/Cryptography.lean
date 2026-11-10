import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.NumberTheory.FermatPsp
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 7: cryptography

Classical ciphers on `ZMod n` (shift, affine, matrix), RSA and its correctness theorem,
message verification, and pseudoprimes. -/

namespace UndergradKB.AbstractAlgebra

open Matrix

/-- AA-094. A cryptosystem: encryption and decryption maps, decryption undoing encryption. -/
@[kb "judson2026" "Definition (cryptosystem), p. 96"]
structure Cryptosystem (M C : Type*) where
  /-- Encryption map. -/
  encrypt : M → C
  /-- Decryption map. -/
  decrypt : C → M
  /-- Decrypting an encrypted message recovers it. -/
  decrypt_encrypt : ∀ m, decrypt (encrypt m) = m

/-- AA-095. The shift cipher `p ↦ p + b` on `ZMod n` (the book uses `n = 26`). -/
@[kb "judson2026" "Example 7.1.1, p. 97"]
def shiftCipher (n : ℕ) (b : ZMod n) : Cryptosystem (ZMod n) (ZMod n) where
  encrypt p := p + b
  decrypt c := c - b
  decrypt_encrypt p := by simp

/-- AA-095. The shift cipher is a bijection with inverse `p ↦ p - b`. -/
@[kb "judson2026" "Example 7.1.1, p. 97"]
theorem shiftCipher_bijective (n : ℕ) (b : ZMod n) :
    Function.Bijective (shiftCipher n b).encrypt ∧
      (∀ c, (shiftCipher n b).encrypt (c - b) = c) := by
  refine ⟨(Equiv.addRight b).bijective, fun c => ?_⟩
  simp [shiftCipher]

/-- AA-096. The affine cipher `p ↦ a p + b` on `ZMod n` is a bijection iff `gcd(a, n) = 1`. -/
@[kb "judson2026" "Example 7.1.3, p. 98"]
theorem affineCipher_bijective_iff (n a : ℕ) (b : ZMod n) :
    Function.Bijective (fun p : ZMod n => (a : ZMod n) * p + b) ↔ Nat.Coprime a n := by
  rw [← ZMod.isUnit_iff_coprime]
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h.2 (1 + b)
    have : (a : ZMod n) * p = 1 := by simpa using hp
    exact ⟨⟨_, p, this, by rw [mul_comm]; exact this⟩, rfl⟩
  · intro ⟨u, hu⟩
    refine Function.bijective_iff_has_inverse.2 ⟨fun c => ↑u⁻¹ * (c - b), ?_, ?_⟩
    · intro p
      simp only [add_sub_cancel_right, ← mul_assoc, ← hu]
      simp
    · intro c
      simp only [← hu]
      simp [← mul_assoc]

/-- AA-096. The affine cipher with `gcd(a, n) = 1` as a cryptosystem, decrypting by `a⁻¹ (c - b)`. -/
@[kb "judson2026" "Example 7.1.3, p. 98"]
noncomputable def affineCipher (n : ℕ) (a : (ZMod n)ˣ) (b : ZMod n) :
    Cryptosystem (ZMod n) (ZMod n) where
  encrypt p := (a : ZMod n) * p + b
  decrypt c := (↑a⁻¹ : ZMod n) * (c - b)
  decrypt_encrypt p := by
    simp [← mul_assoc]

/-- AA-097. The matrix cipher `p ↦ A p + b` on blocks; invertible when `det A` is a unit,
with inverse `A⁻¹ (p - b)`. Works over any commutative ring (the book uses `ZMod 26`). -/
@[kb "judson2026" "Example 7.1.4, p. 98"]
noncomputable def matrixCipher {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R)
    (hA : IsUnit A.det) (b : Fin k → R) : Cryptosystem (Fin k → R) (Fin k → R) where
  encrypt p := A *ᵥ p + b
  decrypt c := A⁻¹ *ᵥ (c - b)
  decrypt_encrypt p := by
    have h : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
    simp [Matrix.mulVec_mulVec, h]

/-- AA-097. The matrix cipher is also a right inverse, hence bijective. -/
@[kb "judson2026" "Example 7.1.4, p. 98"]
theorem matrixCipher_bijective {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R)
    (hA : IsUnit A.det) (b : Fin k → R) : Function.Bijective (matrixCipher A hA b).encrypt := by
  have h : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  refine Function.bijective_iff_has_inverse.2 ⟨(matrixCipher A hA b).decrypt,
    (matrixCipher A hA b).decrypt_encrypt, fun c => ?_⟩
  simp [matrixCipher, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h]

/-- AA-097. A matrix over `ZMod 26` is invertible iff its determinant is a unit. -/
@[kb "judson2026" "Example 7.1.4, p. 98"]
theorem matrix_invertible_iff_det_unit {k : ℕ} (A : Matrix (Fin k) (Fin k) (ZMod 26)) :
    IsUnit A ↔ IsUnit A.det := Matrix.isUnit_iff_isUnit_det A

/-! ### RSA -/

/-- Fermat in the form `x ^ (1 + t (p - 1)) = x` in `ZMod p`. -/
lemma zmod_pow_one_add_mul (p : ℕ) [Fact p.Prime] (x : ZMod p) (t : ℕ) :
    x ^ (1 + t * (p - 1)) = x := by
  by_cases hx : x = 0
  · subst hx; simp
  · rw [pow_add, pow_mul', ZMod.pow_card_sub_one_eq_one hx]; simp

/-- AA-099. RSA correctness: `x ^ (E D) = x` in `ZMod (p q)` for every `x`
(including `x` not coprime to `p q`). -/
@[kb "judson2026" "Discussion after Example 7.2.1, p. 100"]
theorem rsa_correct {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (E D : ℕ)
    (hED : E * D ≡ 1 [MOD (p - 1) * (q - 1)]) (x : ZMod (p * q)) :
    (x ^ E) ^ D = x := by
  have := Fact.mk hp
  have := Fact.mk hq
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hm : 2 ≤ (p - 1) * (q - 1) := by
    rcases Nat.lt_or_gt_of_ne hpq with h | h
    · have : 1 ≤ p - 1 := by omega
      have : 2 ≤ q - 1 := by omega
      nlinarith
    · have : 2 ≤ p - 1 := by omega
      have : 1 ≤ q - 1 := by omega
      nlinarith
  obtain ⟨t, ht⟩ : ∃ t, E * D = 1 + t * ((p - 1) * (q - 1)) := by
    have h1 : 1 % ((p - 1) * (q - 1)) = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 := hED
    unfold Nat.ModEq at h2
    rw [h1] at h2
    refine ⟨E * D / ((p - 1) * (q - 1)), ?_⟩
    have := Nat.div_add_mod (E * D) ((p - 1) * (q - 1))
    rw [h2] at this
    linarith
  rw [← pow_mul]
  apply (ZMod.chineseRemainder hcop).injective
  rw [map_pow]
  ext
  · rw [Prod.pow_fst, ht, show 1 + t * ((p - 1) * (q - 1)) = 1 + (t * (q - 1)) * (p - 1) by ring]
    exact zmod_pow_one_add_mul p _ _
  · rw [Prod.pow_snd, ht, show 1 + t * ((p - 1) * (q - 1)) = 1 + (t * (p - 1)) * (q - 1) by ring]
    exact zmod_pow_one_add_mul q _ _

/-- AA-098. RSA encryption `x ↦ x ^ E` on `ZMod n`. -/
@[kb "judson2026" "Definition (RSA), p. 99"]
def rsaEncrypt (n E : ℕ) (x : ZMod n) : ZMod n := x ^ E

/-- AA-098. RSA decryption `y ↦ y ^ D` on `ZMod n`. -/
@[kb "judson2026" "Definition (RSA), p. 99"]
def rsaDecrypt (n D : ℕ) (y : ZMod n) : ZMod n := y ^ D

/-- AA-098. RSA as a cryptosystem; decryption inverts encryption by `rsa_correct`. -/
@[kb "judson2026" "Definition (RSA), p. 99"]
def rsaCryptosystem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (E D : ℕ)
    (hED : E * D ≡ 1 [MOD (p - 1) * (q - 1)]) : Cryptosystem (ZMod (p * q)) (ZMod (p * q)) where
  encrypt := rsaEncrypt (p * q) E
  decrypt := rsaDecrypt (p * q) D
  decrypt_encrypt x := rsa_correct hp hq hpq E D hED x

/-- AA-098. Decryption inverts encryption. -/
@[kb "judson2026" "Definition (RSA), p. 99"]
theorem rsaDecrypt_rsaEncrypt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (E D : ℕ)
    (hED : E * D ≡ 1 [MOD (p - 1) * (q - 1)]) (x : ZMod (p * q)) :
    rsaDecrypt (p * q) D (rsaEncrypt (p * q) E x) = x := rsa_correct hp hq hpq E D hED x

/-- AA-098. Encryption inverts decryption too. -/
theorem rsaEncrypt_rsaDecrypt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (E D : ℕ)
    (hED : E * D ≡ 1 [MOD (p - 1) * (q - 1)]) (x : ZMod (p * q)) :
    rsaEncrypt (p * q) E (rsaDecrypt (p * q) D x) = x := by
  have := rsa_correct hp hq hpq D E (by rw [Nat.mul_comm D E]; exact hED) x
  simpa [rsaEncrypt, rsaDecrypt] using this

/-- AA-100. Message verification: the sender (modulus `p q`, keys `EA, DA`) signs `x` with the
secret key `DA` and encrypts with the receiver's public key (modulus `p' q' ≥ p q`); the receiver
decrypts with `DB` and applies the sender's public key `EA`, recovering `x`. -/
@[kb "judson2026" "Discussion (message verification), p. 100"]
theorem message_verification {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp' : p'.Prime) (hq' : q'.Prime) (hpq' : p' ≠ q') (EA DA EB DB : ℕ)
    (hA : EA * DA ≡ 1 [MOD (p - 1) * (q - 1)]) (hB : EB * DB ≡ 1 [MOD (p' - 1) * (q' - 1)])
    (hle : p * q ≤ p' * q') (x : ZMod (p * q)) :
    let signed : ZMod (p * q) := rsaDecrypt (p * q) DA x
    let sent : ZMod (p' * q') := rsaEncrypt (p' * q') EB ((signed.val : ℕ) : ZMod (p' * q'))
    let received : ZMod (p' * q') := rsaDecrypt (p' * q') DB sent
    rsaEncrypt (p * q) EA ((received.val : ℕ) : ZMod (p * q)) = x := by
  intro signed sent received
  have h1 : received = ((signed.val : ℕ) : ZMod (p' * q')) :=
    rsaDecrypt_rsaEncrypt hp' hq' hpq' EB DB hB _
  have hpos : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have h2 : received.val = signed.val := by
    rw [h1]
    exact ZMod.val_natCast_of_lt (lt_of_lt_of_le (ZMod.val_lt signed) hle)
  rw [h2, ZMod.natCast_zmod_val]
  exact rsaEncrypt_rsaDecrypt hp hq hpq EA DA hA x

/-! ### Pseudoprimes -/

/-- AA-101. The book's pseudoprime to base `b`: an odd composite `n` with `b ^ (n-1) ≡ 1 (mod n)`. -/
@[kb "judson2026" "Definition (pseudoprime), p. 104"]
def IsPseudoprime (n b : ℕ) : Prop := Odd n ∧ 1 < n ∧ ¬ n.Prime ∧ b ^ (n - 1) ≡ 1 [MOD n]

/-- AA-101. For `b ≠ 0`, the book's pseudoprimes are Mathlib's `Nat.FermatPsp` that are odd. -/
@[kb "judson2026" "Definition (pseudoprime), p. 104"]
theorem isPseudoprime_iff_fermatPsp {n b : ℕ} (hb : b ≠ 0) :
    IsPseudoprime n b ↔ Odd n ∧ Nat.FermatPsp n b := by
  have key : b ^ (n - 1) ≡ 1 [MOD n] ↔ n.ProbablePrime b := by
    rw [Nat.probablePrime_iff_zmod_one n hb, ← ZMod.natCast_eq_natCast_iff]
    simp
  unfold IsPseudoprime Nat.FermatPsp
  rw [key]
  tauto

/-- AA-101. 561 is a Carmichael number (Mathlib), is odd, and is an odd pseudoprime to every
coprime base in the book's sense. -/
@[kb "judson2026" "Definition (Carmichael number), p. 104"]
theorem carmichael_561 : Nat.IsCarmichael 561 ∧ Odd 561 ∧
    ∀ b, b.Coprime 561 → IsPseudoprime 561 b := by
  refine ⟨Nat.isCarmichael_561, by decide, fun b hb => ?_⟩
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [isPseudoprime_iff_fermatPsp hb0]
  obtain ⟨_, hnp, hpp⟩ := Nat.isCarmichael_561
  exact ⟨by decide, hpp b hb, hnp, by decide⟩

end UndergradKB.AbstractAlgebra
