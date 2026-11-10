import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 8: algebraic coding theory

Binary words are `Fin n → ZMod 2`. Block codes, minimum distance, group codes, null-space
(linear) codes, canonical parity-check and standard generator matrices, syndromes and coset
decoding. -/

namespace UndergradKB.AbstractAlgebra

open Matrix

/-- Binary words of length `n`. -/
abbrev Word (n : ℕ) := Fin n → ZMod 2

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

lemma zmod2_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

lemma zmod2_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by revert a; decide

lemma word_add_self {n : ℕ} (x : Word n) : x + x = 0 := by
  ext i; simp [zmod2_add_self]

lemma word_neg {n : ℕ} (x : Word n) : -x = x := by
  ext i; simp only [Pi.neg_apply]
  have := zmod2_add_self (x i)
  exact neg_eq_of_add_eq_zero_right this

lemma hammingDist_eq_norm_sub {n : ℕ} (x y : Word n) : hammingDist x y = hammingNorm (x - y) := by
  rw [hammingDist_eq_hammingNorm, word_neg, sub_eq_add_neg, word_neg]

/-! ### Block codes, parity -/

/-- AA-102. An `(n, m)`-block code: an injective encoder `Z₂^m → Z₂^n` and a decoder. -/
@[kb "judson2026" "Definition (block code), p. 111"]
structure BlockCode (n m : ℕ) where
  /-- Encoding map. -/
  encode : Word m → Word n
  /-- Decoding map. -/
  decode : Word n → Word m
  /-- The encoder is injective. -/
  encode_injective : Function.Injective encode

/-- AA-102. The codewords of a block code: the image of the encoder. -/
@[kb "judson2026" "Definition (block code), p. 111"]
def BlockCode.codewords {n m : ℕ} (C : BlockCode n m) : Set (Word n) := Set.range C.encode

/-- The even-parity words of length `n`. -/
def evenParity (n : ℕ) : Set (Word n) := {x | ∑ i, x i = 0}

/-- AA-103. Even parity detects single-bit errors: flipping one bit of an even-parity word
leaves the set of even-parity words. -/
@[kb "judson2026" "Example 8.1.3, p. 108"]
theorem evenParity_detects_single_error {n : ℕ} {c : Word n} (hc : c ∈ evenParity n) (i : Fin n) :
    c + Pi.single i 1 ∉ evenParity n := by
  intro h
  simp only [evenParity, Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib,
    Finset.sum_pi_single'] at h hc
  rw [hc] at h
  simp at h

/-- AA-103. The parity-check block code `(n+1, n)`: append the parity bit. -/
@[kb "judson2026" "Example 8.1.3, p. 108"]
def parityBlockCode (n : ℕ) : BlockCode (n + 1) n where
  encode x := Fin.snoc (α := fun _ => ZMod 2) x (∑ i, x i)
  decode y i := y i.castSucc
  encode_injective := by
    intro x y h
    ext i
    have := congrFun h i.castSucc
    simpa using this

/-- AA-103. Every codeword of the parity block code has even parity. -/
@[kb "judson2026" "Example 8.1.3, p. 108"]
theorem parityBlockCode_codewords_even (n : ℕ) :
    (parityBlockCode n).codewords ⊆ evenParity (n + 1) := by
  rintro _ ⟨x, rfl⟩
  simp only [evenParity, parityBlockCode, Set.mem_ofPred_eq, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  exact zmod2_add_self _

/-! ### Minimum distance -/

/-- AA-106. Minimum distance of a code (a finite set of words): the least Hamming distance
between two distinct codewords. -/
@[kb "judson2026" "Definition (minimum distance), p. 111"]
noncomputable def minDist {n : ℕ} (C : Finset (Word n)) : ℕ :=
  sInf {d | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = d}

/-- AA-106. The minimum distance is at most the distance of any two distinct codewords. -/
@[kb "judson2026" "Definition (minimum distance), p. 111"]
theorem minDist_le {n : ℕ} {C : Finset (Word n)} {x y : Word n} (hx : x ∈ C) (hy : y ∈ C)
    (hne : x ≠ y) : minDist C ≤ hammingDist x y :=
  Nat.sInf_le ⟨x, hx, y, hy, hne, rfl⟩

/-- AA-106. The weight of a word is its Hamming norm, and `w(x) = d(x, 0)`. -/
@[kb "judson2026" "Definition (weight), p. 111"]
theorem weight_eq_dist_zero {n : ℕ} (x : Word n) : hammingNorm x = hammingDist x 0 :=
  (hammingDist_zero_right x).symm

/-- AA-108 (correction). If the minimum distance is at least `2k+1`, a received word within
distance `k` of a codeword `c` has no other codeword within distance `k`, and `c` is a nearest
codeword. -/
@[kb "judson2026" "Theorem 8.1.13, p. 112"]
theorem correct_up_to {n k : ℕ} {C : Finset (Word n)} (h : 2 * k + 1 ≤ minDist C) {c : Word n}
    (hc : c ∈ C) {r : Word n} (hr : hammingDist r c ≤ k) :
    (∀ c' ∈ C, c' ≠ c → k < hammingDist r c') ∧ (∀ c' ∈ C, hammingDist r c ≤ hammingDist r c') := by
  have key : ∀ c' ∈ C, c' ≠ c → k < hammingDist r c' := by
    intro c' hc' hne
    have h1 := minDist_le hc hc' hne.symm
    have h2 := hammingDist_triangle c r c'
    rw [hammingDist_comm c r] at h2
    omega
  refine ⟨key, fun c' hc' => ?_⟩
  by_cases hne : c' = c
  · subst hne; exact le_rfl
  · have := key c' hc' hne; omega

/-- AA-108 (detection). If the minimum distance is at least `2k+1`, a word that differs from a
codeword in between 1 and `2k` places is not a codeword. -/
@[kb "judson2026" "Theorem 8.1.13, p. 112"]
theorem detect_up_to {n k : ℕ} {C : Finset (Word n)} (h : 2 * k + 1 ≤ minDist C) {c : Word n}
    (hc : c ∈ C) {r : Word n} (hr : hammingDist r c ≤ 2 * k) (hne : r ≠ c) : r ∉ C := by
  intro hrC
  have := minDist_le hc hrC hne.symm
  rw [hammingDist_comm] at this
  omega

/-! ### Group codes -/

/-- AA-109. A group code: an additive subgroup of `Z₂^n`. -/
@[kb "judson2026" "Definition (group code), p. 113"]
abbrev GroupCode (n : ℕ) := AddSubgroup (Word n)

/-- AA-109. A nonempty set of binary words closed under addition is a group code. -/
@[kb "judson2026" "Definition (group code), p. 113"]
def groupCodeOfAddClosed {n : ℕ} (S : Set (Word n)) (h0 : S.Nonempty)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) : GroupCode n where
  carrier := S
  add_mem' := fun {a b} ha hb => hadd a ha b hb
  zero_mem' := by
    obtain ⟨x, hx⟩ := h0
    simpa [word_add_self] using hadd x hx x hx
  neg_mem' := fun {a} ha => by rwa [word_neg]

/-- The words of a group code, as a finset. -/
noncomputable def GroupCode.toFinset {n : ℕ} (C : GroupCode n) : Finset (Word n) := by
  classical exact Finset.univ.filter (· ∈ C)

lemma GroupCode.mem_toFinset {n : ℕ} (C : GroupCode n) (x : Word n) : x ∈ C.toFinset ↔ x ∈ C := by
  classical simp [GroupCode.toFinset]

/-- AA-111. For a group code, the minimum distance is the least weight of a nonzero codeword. -/
@[kb "judson2026" "Theorem 8.2.3, p. 114"]
theorem minDist_groupCode {n : ℕ} (C : GroupCode n) :
    minDist C.toFinset = sInf {w | ∃ x ∈ C, x ≠ 0 ∧ hammingNorm x = w} := by
  unfold minDist
  congr 1
  ext d
  simp only [Set.mem_ofPred_eq, GroupCode.mem_toFinset]
  constructor
  · rintro ⟨x, hx, y, hy, hne, rfl⟩
    exact ⟨x - y, C.sub_mem hx hy, sub_ne_zero.2 hne, (hammingDist_eq_norm_sub x y).symm⟩
  · rintro ⟨x, hx, hne, rfl⟩
    exact ⟨x, hx, 0, C.zero_mem, hne, hammingDist_zero_right x⟩

/-! ### Null-space codes -/

/-- AA-112. The null space `{x | H x = 0}` of a binary matrix is a group code. -/
@[kb "judson2026" "Theorem 8.2.6, p. 115"]
def nullCode {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) : GroupCode n where
  carrier := {x | H *ᵥ x = 0}
  add_mem' := by
    intro a b ha hb
    simp_all [Matrix.mulVec_add]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp_all [Matrix.mulVec_neg]

lemma mem_nullCode {m n : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {x : Word n} :
    x ∈ nullCode H ↔ H *ᵥ x = 0 := Iff.rfl

/-- AA-113. A linear code: the null space of some binary matrix. -/
@[kb "judson2026" "Definition (linear code), p. 115"]
def IsLinearCode {n : ℕ} (C : GroupCode n) : Prop :=
  ∃ (m : ℕ) (H : Matrix (Fin m) (Fin n) (ZMod 2)), C = nullCode H

/-- AA-113. Null spaces are linear codes. -/
@[kb "judson2026" "Definition (linear code), p. 115"]
theorem isLinearCode_nullCode {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) :
    IsLinearCode (nullCode H) := ⟨m, H, rfl⟩

/-! ### Canonical parity-check and standard generator matrices -/

section Canonical

variable {k m : ℕ}

/-- AA-114. The canonical parity-check matrix `H = (A | I_m)`. -/
@[kb "judson2026" "Definition (canonical parity-check matrix), p. 116"]
def canonH (A : Matrix (Fin m) (Fin k) (ZMod 2)) : Matrix (Fin m) (Fin (k + m)) (ZMod 2) :=
  Matrix.of fun i j => Fin.addCases (fun a => A i a) (fun b => if i = b then 1 else 0) j

/-- AA-114. The standard generator matrix `G = (I_k over A)`. -/
@[kb "judson2026" "Definition (canonical parity-check matrix), p. 116"]
def stdG (A : Matrix (Fin m) (Fin k) (ZMod 2)) : Matrix (Fin (k + m)) (Fin k) (ZMod 2) :=
  Matrix.of fun i j => Fin.addCases (fun a => if a = j then 1 else 0) (fun b => A b j) i

lemma canonH_mulVec (A : Matrix (Fin m) (Fin k) (ZMod 2)) (x : Word (k + m)) :
    canonH A *ᵥ x = A *ᵥ (fun a => x (Fin.castAdd m a)) + fun b => x (Fin.natAdd k b) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, canonH]

lemma stdG_mulVec (A : Matrix (Fin m) (Fin k) (ZMod 2)) (u : Word k) :
    stdG A *ᵥ u = Fin.append u (A *ᵥ u) := by
  ext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp [Matrix.mulVec, dotProduct, stdG]
  · simp [Matrix.mulVec, dotProduct, stdG]

/-- AA-117. `H G = 0`. -/
@[kb "judson2026" "Lemma 8.3.5, p. 118"]
theorem canonH_mul_stdG (A : Matrix (Fin m) (Fin k) (ZMod 2)) : canonH A * stdG A = 0 := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_add, canonH, stdG, zmod2_add_self]

/-- AA-116. The standard generator matrix as an encoder `Z₂^k → Z₂^(k+m)` (injective), with
the decoder reading the first `k` bits. -/
@[kb "judson2026" "Theorem 8.3.4, p. 118"]
def stdBlockCode (A : Matrix (Fin m) (Fin k) (ZMod 2)) : BlockCode (k + m) k where
  encode u := stdG A *ᵥ u
  decode y a := y (Fin.castAdd m a)
  encode_injective := by
    intro u v h
    have h : stdG A *ᵥ u = stdG A *ᵥ v := h
    rw [stdG_mulVec, stdG_mulVec] at h
    ext a
    have := congrFun h (Fin.castAdd m a)
    simpa using this

/-- AA-116. The encoder is additive. -/
@[kb "judson2026" "Theorem 8.3.4, p. 118"]
theorem stdBlockCode_encode_add (A : Matrix (Fin m) (Fin k) (ZMod 2)) (u v : Word k) :
    (stdBlockCode A).encode (u + v) = (stdBlockCode A).encode u + (stdBlockCode A).encode v :=
  by simp only [stdBlockCode]; exact Matrix.mulVec_add _ _ _

/-- AA-116. The image of the standard generator matrix, a group code. -/
@[kb "judson2026" "Theorem 8.3.4, p. 118"]
def stdCode (A : Matrix (Fin m) (Fin k) (ZMod 2)) : GroupCode (k + m) :=
  (Matrix.mulVecLin (stdG A)).range.toAddSubgroup

/-- AA-116. The codewords of the block code are the elements of the group code. -/
@[kb "judson2026" "Theorem 8.3.4, p. 118"]
theorem stdBlockCode_codewords (A : Matrix (Fin m) (Fin k) (ZMod 2)) :
    (stdBlockCode A).codewords = (stdCode A : Set (Word (k + m))) := by
  ext y
  simp [BlockCode.codewords, stdBlockCode, stdCode]

/-- AA-115. For `H = (A | I)`, `x` is a codeword iff its last `m` bits (check bits) are determined
by the first `k` (information) bits as `A` times them. -/
@[kb "judson2026" "Theorem 8.3.3, p. 118"]
theorem mem_nullCode_canonH_iff (A : Matrix (Fin m) (Fin k) (ZMod 2)) (x : Word (k + m)) :
    x ∈ nullCode (canonH A) ↔
      (fun b => x (Fin.natAdd k b)) = A *ᵥ (fun a => x (Fin.castAdd m a)) := by
  rw [mem_nullCode, canonH_mulVec]
  constructor
  · intro h
    ext b
    have := congrFun h b
    simp only [Pi.add_apply, Pi.zero_apply] at this
    exact (zmod2_add_eq_zero this).symm
  · intro h
    rw [h]
    ext b
    simp [zmod2_add_self]

/-- AA-118. The code generated by `G` is the null space of `H`. -/
@[kb "judson2026" "Theorem 8.3.6, p. 119"]
theorem stdCode_eq_nullCode (A : Matrix (Fin m) (Fin k) (ZMod 2)) :
    stdCode A = nullCode (canonH A) := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    show canonH A *ᵥ (stdG A *ᵥ u) = 0
    rw [Matrix.mulVec_mulVec, canonH_mul_stdG, Matrix.zero_mulVec]
  · intro hy
    refine ⟨fun a => y (Fin.castAdd m a), ?_⟩
    have h := (mem_nullCode_canonH_iff A y).1 hy
    show stdG A *ᵥ _ = y
    rw [stdG_mulVec, ← h]
    ext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

end Canonical

end UndergradKB.AbstractAlgebra
