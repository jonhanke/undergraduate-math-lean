import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Codes

/-! # Judson–Beezer, chapter 8 (continued): syndromes, Hamming codes, the channel

Single-error detection and correction for null-space codes, syndromes and coset decoding,
Hamming codes, and the binary symmetric channel. -/

namespace UndergradKB.AbstractAlgebra

open Matrix

/-! ### Single errors -/

/-- A code detects single errors: flipping any one bit of a codeword leaves the code. -/
def DetectsSingleErrors {n : ℕ} (C : GroupCode n) : Prop :=
  ∀ c ∈ C, ∀ i, c + Pi.single i 1 ∉ C

/-- A code corrects single errors: a received word is within distance 1 of at most one codeword. -/
def CorrectsSingleErrors {n : ℕ} (C : GroupCode n) : Prop :=
  ∀ r : Word n, ∀ c ∈ C, ∀ c' ∈ C, hammingDist r c ≤ 1 → hammingDist r c' ≤ 1 → c = c'

lemma hammingNorm_single {n : ℕ} (i : Fin n) :
    hammingNorm (Pi.single i (1 : ZMod 2) : Word n) = 1 := by
  unfold hammingNorm
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma hammingNorm_single_add_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    hammingNorm (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Word n) = 2 := by
  have hc2 : (Finset.univ.filter (fun l => (Pi.single i 1 + Pi.single j 1 : Word n) l ≠ 0)) =
      {i, j} := by
    ext l
    by_cases hl1 : l = i
    · subst hl1; simp [Pi.single_apply, hij]
    · by_cases hl2 : l = j
      · subst hl2; simp [Pi.single_apply, Ne.symm hij]
      · simp [Pi.single_apply, hl1, hl2]
  unfold hammingNorm
  rw [hc2, Finset.card_pair hij]

/-- A word of weight at most 2 is zero, a unit vector, or a sum of two distinct unit vectors. -/
lemma word_weight_le_two {n : ℕ} {x : Word n} (h : hammingNorm x ≤ 2) :
    x = 0 ∨ (∃ i, x = Pi.single i 1) ∨ ∃ i j, i ≠ j ∧ x = Pi.single i 1 + Pi.single j 1 := by
  have hs : ∀ j, x j ≠ 0 → x j = 1 := fun j hj => zmod2_ne_zero hj
  have hcard : (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ 2 := h
  have hcases : (Finset.univ.filter (fun i => x i ≠ 0)).card = 0 ∨
      (Finset.univ.filter (fun i => x i ≠ 0)).card = 1 ∨
      (Finset.univ.filter (fun i => x i ≠ 0)).card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · left
    ext j
    by_contra hj
    have : j ∈ Finset.univ.filter (fun i => x i ≠ 0) := by simpa using hj
    rw [Finset.card_eq_zero] at h0
    simp [h0] at this
  · right; left
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
    refine ⟨i, ?_⟩
    ext j
    by_cases hji : j = i
    · subst hji
      have : j ∈ Finset.univ.filter (fun i => x i ≠ 0) := by rw [hi]; simp
      simpa using hs j (by simpa using this)
    · have : j ∉ Finset.univ.filter (fun i => x i ≠ 0) := by rw [hi]; simpa using hji
      simp at this
      simp [this, hji]
  · right; right
    obtain ⟨i, j, hij, hi⟩ := Finset.card_eq_two.1 h2
    refine ⟨i, j, hij, ?_⟩
    ext l
    have hl : x l ≠ 0 ↔ l = i ∨ l = j := by
      have : l ∈ Finset.univ.filter (fun i => x i ≠ 0) ↔ l ∈ ({i, j} : Finset (Fin n)) := by
        rw [hi]
      simpa using this
    by_cases h1 : l = i
    · subst h1
      have := hs l (hl.2 (Or.inl rfl))
      simp [this, Pi.single_apply, hij]
    · by_cases h2 : l = j
      · subst h2
        have := hs l (hl.2 (Or.inr rfl))
        simp [this, Pi.single_apply, Ne.symm hij]
      · have : x l = 0 := by
          by_contra hne
          rcases hl.1 hne with h | h
          · exact h1 h
          · exact h2 h
        simp [this, Pi.single_apply, h1, h2]

/-- AA-120. The null space of `H` detects single errors iff `H` has no zero column. -/
@[kb "judson2026" "Theorem 8.3.9, p. 120"]
theorem nullCode_detects_iff {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) :
    DetectsSingleErrors (nullCode H) ↔ ∀ i, H.col i ≠ 0 := by
  have key : ∀ (c : Word n) (i : Fin n), c ∈ nullCode H →
      (c + Pi.single i 1 ∈ nullCode H ↔ H.col i = 0) := by
    intro c i hc
    rw [mem_nullCode] at hc
    rw [mem_nullCode, Matrix.mulVec_add, hc, zero_add, Matrix.mulVec_single_one]
  constructor
  · intro h i hi
    exact h 0 (zero_mem _) i ((key 0 i (zero_mem _)).2 hi)
  · intro h c hc i hmem
    exact h i ((key c i hc).1 hmem)

/-- AA-121. The null space of `H` corrects single errors iff `H` has no zero column and no two
equal columns. -/
@[kb "judson2026" "Theorem 8.3.12, p. 120"]
theorem nullCode_corrects_iff {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) :
    CorrectsSingleErrors (nullCode H) ↔
      (∀ i, H.col i ≠ 0) ∧ ∀ i j, i ≠ j → H.col i ≠ H.col j := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i j hij hcol => ?_⟩
    · have hmem : (Pi.single i 1 : Word n) ∈ nullCode H := by
        rw [mem_nullCode, Matrix.mulVec_single_one]; exact hi
      have := h 0 0 (zero_mem _) _ hmem (by simp) (by
        rw [hammingDist_zero_left, hammingNorm_single])
      have h2 := congrFun this i
      simp at h2
    · have hmem : (Pi.single i 1 + Pi.single j 1 : Word n) ∈ nullCode H := by
        rw [mem_nullCode, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
          hcol]
        ext l; simp [zmod2_add_self]
      have := h (Pi.single i 1) 0 (zero_mem _) _ hmem
        (by rw [hammingDist_zero_right, hammingNorm_single])
        (by
          rw [hammingDist_eq_norm_sub, show (Pi.single i 1 : Word n) -
            (Pi.single i 1 + Pi.single j 1) = Pi.single j 1 by
              rw [sub_eq_add_neg, word_neg]
              ext l
              simp only [Pi.add_apply]
              rw [← add_assoc, zmod2_add_self, zero_add]]
          rw [hammingNorm_single])
      have h2 := congrFun this i
      simp [Pi.single_apply, hij] at h2
  · rintro ⟨h0, h1⟩ r c hc c' hc' hr hr'
    have hd : hammingDist c c' ≤ 2 := by
      have := hammingDist_triangle c r c'
      rw [hammingDist_comm c r] at this
      omega
    have hd' : hammingNorm (c - c') ≤ 2 := by rwa [← hammingDist_eq_norm_sub]
    have hmem : c - c' ∈ nullCode H := (nullCode H).sub_mem hc hc'
    rw [mem_nullCode] at hmem
    rcases word_weight_le_two hd' with h | ⟨i, hi⟩ | ⟨i, j, hij, hij'⟩
    · exact sub_eq_zero.1 h
    · rw [hi, Matrix.mulVec_single_one] at hmem
      exact absurd hmem (h0 i)
    · rw [hij', Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hmem
      exact absurd (by
        ext l; exact zmod2_add_eq_zero (by simpa using congrFun hmem l)) (h1 i j hij)

/-! ### Syndromes and cosets -/

/-- AA-122. The syndrome of a word `x` with respect to `H` is `H x`. -/
@[kb "judson2026" "Definition (syndrome), p. 121"]
def syndrome {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (x : Word n) : Fin m → ZMod 2 :=
  H *ᵥ x

/-- AA-123. The syndrome of `c + e` for a codeword `c` is the syndrome of `e`. -/
@[kb "judson2026" "Proposition 8.4.2, p. 121"]
theorem syndrome_add_codeword {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) {c : Word n}
    (hc : c ∈ nullCode H) (e : Word n) : syndrome H (c + e) = syndrome H e := by
  rw [mem_nullCode] at hc
  simp [syndrome, Matrix.mulVec_add, hc]

/-- AA-124. For a code correcting single errors, if a received word `r` is within distance 1 of a
codeword `c`, then either `r = c` (syndrome 0), or `r = c + e_i` for a position `i`, the syndrome
is the `i`-th column of `H`, and `i` is the only position with that column. -/
@[kb "judson2026" "Theorem 8.4.3, p. 122"]
theorem syndrome_single_error {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (hcorr : CorrectsSingleErrors (nullCode H)) {c r : Word n} (hc : c ∈ nullCode H)
    (hr : hammingDist r c ≤ 1) :
    (r = c ∧ syndrome H r = 0) ∨
      ∃ i, r = c + Pi.single i 1 ∧ syndrome H r = H.col i ∧
        ∀ j, H.col j = syndrome H r → j = i := by
  obtain ⟨h0, h1⟩ := (nullCode_corrects_iff H).1 hcorr
  have hn : hammingNorm (r - c) ≤ 1 := by rwa [← hammingDist_eq_norm_sub]
  have hrc : r = c + (r - c) := by abel
  rcases word_weight_le_two (by omega : hammingNorm (r - c) ≤ 2) with
    h | ⟨i, hi⟩ | ⟨i, j, hij, hij'⟩
  · left
    have : r = c := sub_eq_zero.1 h
    refine ⟨this, ?_⟩
    rw [this]; exact hc
  · right
    refine ⟨i, by rw [← hi]; exact hrc, ?_⟩
    have hs : syndrome H r = H.col i := by
      rw [hrc, syndrome_add_codeword H hc, hi, syndrome, Matrix.mulVec_single_one]
    refine ⟨hs, fun j hj => ?_⟩
    by_contra hne
    exact h1 j i hne (hj.trans hs)
  · exfalso
    rw [hij', hammingNorm_single_add_single hij] at hn
    omega

/-- AA-126. Two words lie in the same coset of `Null(H)` iff they have the same syndrome. -/
@[kb "judson2026" "Proposition 8.4.9, p. 123"]
theorem sameCoset_iff_syndrome {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (r s : Word n) :
    r - s ∈ nullCode H ↔ syndrome H r = syndrome H s := by
  rw [mem_nullCode, Matrix.mulVec_sub, sub_eq_zero]; rfl

/-- AA-126. In terms of quotient cosets. -/
@[kb "judson2026" "Proposition 8.4.9, p. 123"]
theorem quotient_eq_iff_syndrome {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (r s : Word n) :
    (r : Word n ⧸ nullCode H) = s ↔ syndrome H r = syndrome H s := by
  rw [QuotientAddGroup.eq, neg_add_eq_sub, sameCoset_iff_syndrome, eq_comm]

/-- AA-125. `e` is a coset leader for `r` w.r.t. a code `C`: `r - e` is a codeword and `e` has
least weight among words with that property. -/
@[kb "judson2026" "Definition (coset leader), p. 122"]
def IsCosetLeader {n : ℕ} (C : GroupCode n) (r e : Word n) : Prop :=
  r - e ∈ C ∧ ∀ e', r - e' ∈ C → hammingNorm e ≤ hammingNorm e'

/-- AA-125. Every word has a coset leader. -/
@[kb "judson2026" "Definition (coset leader), p. 122"]
theorem exists_cosetLeader {n : ℕ} (C : GroupCode n) (r : Word n) : ∃ e, IsCosetLeader C r e := by
  classical
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun e => r - e ∈ C))
    hammingNorm ⟨r, by simp⟩
  exact ⟨e, by simpa using he, fun e' h' => hmin e' (by simpa using h')⟩

/-- AA-125. Being a coset leader depends only on the syndrome of the received word. -/
@[kb "judson2026" "Definition (coset leader), p. 122"]
theorem isCosetLeader_nullCode_iff {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (r e : Word n) :
    IsCosetLeader (nullCode H) r e ↔
      syndrome H r = syndrome H e ∧
        ∀ e', syndrome H r = syndrome H e' → hammingNorm e ≤ hammingNorm e' := by
  unfold IsCosetLeader
  simp only [sameCoset_iff_syndrome]

/-- AA-126. Coset decoding: decode `r` to `r - L r`, where `L` picks a coset leader. -/
@[kb "judson2026" "Definition (coset decoding), p. 122"]
def cosetDecode {n : ℕ} (L : Word n → Word n) (r : Word n) : Word n := r - L r

/-- AA-126. The decoded word is a codeword, and a nearest codeword to `r`. -/
@[kb "judson2026" "Definition (coset decoding), p. 122"]
theorem cosetDecode_spec {n : ℕ} (C : GroupCode n) (L : Word n → Word n)
    (hL : ∀ r, IsCosetLeader C r (L r)) (r : Word n) :
    cosetDecode L r ∈ C ∧ ∀ c ∈ C, hammingDist r (cosetDecode L r) ≤ hammingDist r c := by
  refine ⟨(hL r).1, fun c hc => ?_⟩
  have h1 : hammingDist r (cosetDecode L r) = hammingNorm (L r) := by
    rw [hammingDist_eq_norm_sub, cosetDecode, sub_sub_cancel]
  have h2 : hammingDist r c = hammingNorm (r - c) := hammingDist_eq_norm_sub r c
  rw [h1, h2]
  exact (hL r).2 _ (by simpa using hc)

/-! ### Hamming codes -/

/-- AA-127. The Hamming matrix: its `j`-th column (`j = 0, ..., 2^r - 2`) is `j + 1` in binary. -/
@[kb "judson2026" "Definition (Hamming code), p. 129"]
def hammingMatrix (r : ℕ) : Matrix (Fin r) (Fin (2 ^ r - 1)) (ZMod 2) :=
  Matrix.of fun i j => if (j.val + 1).testBit i.val then 1 else 0

lemma hamming_bit_false {r : ℕ} (j : Fin (2 ^ r - 1)) (b : ℕ) (hb : r ≤ b) :
    (j.val + 1).testBit b = false := by
  apply Nat.testBit_lt_two_pow
  have := j.isLt
  have h2 : 2 ^ r ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have : 0 < 2 ^ r := by positivity
  omega

/-- AA-127. The Hamming matrix has no zero column and no two equal columns. -/
@[kb "judson2026" "Definition (Hamming code), p. 129"]
theorem hammingMatrix_cols (r : ℕ) :
    (∀ j, (hammingMatrix r).col j ≠ 0) ∧
      ∀ i j, i ≠ j → (hammingMatrix r).col i ≠ (hammingMatrix r).col j := by
  constructor
  · intro j hj
    have h0 : ∀ b, (j.val + 1).testBit b = false := by
      intro b
      by_cases hb : b < r
      · have := congrFun hj ⟨b, hb⟩
        simp [hammingMatrix] at this
        simpa using this
      · exact hamming_bit_false j b (by omega)
    have : j.val + 1 = 0 := Nat.eq_of_testBit_eq (fun b => by simp [h0 b])
    omega
  · intro i j hij hcol
    apply hij
    apply Fin.ext
    have : i.val + 1 = j.val + 1 := by
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b < r
      · have := congrFun hcol ⟨b, hb⟩
        simp only [hammingMatrix, Matrix.col_apply, Matrix.of_apply] at this
        by_cases h1 : (i.val + 1).testBit b = true <;>
          by_cases h2 : (j.val + 1).testBit b = true <;> simp_all
      · rw [hamming_bit_false i b (by omega), hamming_bit_false j b (by omega)]
    omega

/-- AA-127. The Hamming code (null space of `hammingMatrix r`) corrects single errors. -/
@[kb "judson2026" "Definition (Hamming code), p. 129"]
theorem hammingCode_corrects (r : ℕ) : CorrectsSingleErrors (nullCode (hammingMatrix r)) :=
  (nullCode_corrects_iff _).2 (hammingMatrix_cols r)

/-! ### The binary symmetric channel -/

/-- AA-104. Probability, on a binary symmetric channel with bit-error probability `q` (and
`p = 1 - q`), that the error pattern is exactly `e`: each bit is flipped independently. -/
@[kb "judson2026" "Definition (binary symmetric channel), p. 109"]
noncomputable def errProb {n : ℕ} (p q : ℝ) (e : Word n) : ℝ :=
  ∏ i, if e i = 0 then p else q

lemma errProb_eq {n : ℕ} (p q : ℝ) (e : Word n) :
    errProb p q e = q ^ hammingNorm e * p ^ (n - hammingNorm e) := by
  unfold errProb
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, mul_comm]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => e i = 0)
  have h2 : (Finset.univ.filter (fun i => ¬ e i = 0)).card = hammingNorm e := rfl
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have : (Finset.univ.filter (fun i => e i = 0)).card = n - hammingNorm e := by omega
  rw [this, h2]

lemma card_weight_eq {n : ℕ} (k : ℕ) :
    (Finset.univ.filter (fun e : Word n => hammingNorm e = k)).card = n.choose k := by
  classical
  have : (Finset.univ.powersetCard k : Finset (Finset (Fin n))).card = n.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← this]
  refine Finset.card_nbij' (fun e => Finset.univ.filter (fun i => e i ≠ 0))
    (fun s => fun i => if i ∈ s then 1 else 0) ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, he.2⟩
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : (Finset.univ.filter (fun i => ((if i ∈ s then 1 else 0 : ZMod 2)) ≠ 0)) = s := by
      ext i; by_cases h : i ∈ s <;> simp [h]
    unfold hammingNorm
    rw [this, hs.2]
  · intro e he
    ext i
    by_cases h : e i = 0
    · simp [h]
    · simp [h, zmod2_ne_zero h]
  · intro s hs
    ext i
    by_cases h : i ∈ s <;> simp [h]

/-- AA-105. The probability that exactly `k` of the `n` bits are in error is
`C(n,k) q^k p^(n-k)`: the sum of `errProb` over all error patterns of weight `k`. -/
@[kb "judson2026" "Theorem 8.1.7, p. 110"]
theorem prob_exactly_k_errors {n : ℕ} (p q : ℝ) (k : ℕ) :
    ∑ e ∈ Finset.univ.filter (fun e : Word n => hammingNorm e = k), errProb p q e =
      (n.choose k : ℝ) * q ^ k * p ^ (n - k) := by
  rw [Finset.sum_congr rfl (fun e he => by rw [errProb_eq, (Finset.mem_filter.1 he).2]),
    Finset.sum_const, card_weight_eq, nsmul_eq_mul]
  ring

end UndergradKB.AbstractAlgebra
