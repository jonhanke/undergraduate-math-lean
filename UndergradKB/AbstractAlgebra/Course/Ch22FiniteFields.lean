import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain
import Mathlib.LinearAlgebra.Vandermonde
import UndergradKB.AbstractAlgebra.FiniteFields
import UndergradKB.AbstractAlgebra.CyclicCodes
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 22: finite fields (course layer)

Thin wrappers around Mathlib for the structure of finite fields and the Vandermonde determinant. -/

namespace UndergradKB.AbstractAlgebra.Course

open Polynomial

/-- AA-401. A finite field has prime characteristic. -/
@[kb "judson2026" "Proposition 22.1.1, p. 303"]
theorem judson_22_1_1 (F : Type*) [Field F] [Finite F] : ∃ p : ℕ, p.Prime ∧ CharP F p := by
  obtain ⟨p, hp⟩ := CharP.exists F
  exact ⟨p, (CharP.char_is_prime_or_zero F p).resolve_right (CharP.char_ne_zero_of_finite F p), hp⟩

/-- AA-402. A finite field of characteristic `p` has `p ^ n` elements for some `n ≥ 1`. -/
@[kb "judson2026" "Proposition 22.1.2, p. 303"]
theorem judson_22_1_2 (F : Type*) [Field F] [Fintype F] (p : ℕ) [CharP F p] :
    ∃ n : ℕ, 1 ≤ n ∧ Fintype.card F = p ^ n := by
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  exact ⟨n, n.pos, hn⟩

/-- AA-403. Freshman's dream: in characteristic `p`, `(a + b) ^ (p ^ n) = a ^ (p ^ n) + b ^ (p ^ n)`. -/
@[kb "judson2026" "Lemma 22.1.3, p. 303"]
theorem judson_22_1_3 {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ)
    (a b : R) : (a + b) ^ p ^ n = a ^ p ^ n + b ^ p ^ n :=
  add_pow_char_pow a b p n

/-- AA-405. A nonzero polynomial `f` over `F` is separable (has distinct roots in a splitting
field `E`) iff `f` and `f'` are relatively prime. -/
@[kb "judson2026" "Lemma 22.1.5, p. 304"]
theorem judson_22_1_5 {F E : Type*} [Field F] [Field E] [Algebra F E] (f : F[X]) (hf : f ≠ 0)
    [f.IsSplittingField F E] :
    (f.map (algebraMap F E)).roots.Nodup ↔ IsCoprime f (derivative f) := by
  rw [← Polynomial.separable_def, ← Polynomial.separable_map (algebraMap F E)]
  exact Polynomial.nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf)
    (Polynomial.IsSplittingField.splits E f)

/-- AA-406. For every prime `p` and `n ≥ 1` there is a field with `p ^ n` elements (the splitting
field of `x ^ (p ^ n) - x` over `ℤ_p`), and any two finite fields with the same number of elements
are isomorphic. -/
@[kb "judson2026" "Theorem 22.1.6, p. 305"]
theorem judson_22_1_6 (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    (Finite (GaloisField p n) ∧ Nat.card (GaloisField p n) = p ^ n ∧
      (X ^ p ^ n - X : (ZMod p)[X]).IsSplittingField (ZMod p) (GaloisField p n)) ∧
    ∀ (K L : Type) [Field K] [Field L] [Fintype K] [Fintype L],
      Fintype.card K = p ^ n → Fintype.card L = p ^ n → Nonempty (K ≃+* L) := by
  refine ⟨⟨inferInstance, GaloisField.card p n hn,
    inferInstanceAs (IsSplittingField (ZMod p) (SplittingField (X ^ p ^ n - X : (ZMod p)[X])) _)⟩,
    ?_⟩
  intro K L _ _ _ _ hK hL
  exact ⟨FiniteField.ringEquivOfCardEq (hK.trans hL.symm)⟩

/-- AA-409. A finite subgroup of the unit group of a field is cyclic. -/
@[kb "judson2026" "Theorem 22.1.10, p. 306"]
theorem judson_22_1_10 {F : Type*} [Field F] (G : Subgroup Fˣ) [Finite G] : IsCyclic G :=
  inferInstance

/-- AA-409. The multiplicative group of a finite field is cyclic. -/
@[kb "judson2026" "Corollary 22.1.11, p. 306"]
theorem judson_22_1_11 (F : Type*) [Field F] [Finite F] : IsCyclic Fˣ :=
  inferInstance

/-- AA-410. Every finite extension of a finite field is simple. -/
@[kb "judson2026" "Corollary 22.1.12, p. 306"]
theorem judson_22_1_12 (F E : Type*) [Field F] [Field E] [Algebra F E] [Finite F]
    [FiniteDimensional F E] : ∃ α : E, IntermediateField.adjoin F {α} = ⊤ :=
  Field.exists_primitive_element_of_finite_bot F E

/-- AA-417. The Vandermonde determinant is the product of the pairwise differences. -/
@[kb "judson2026" "Lemma 22.2.7, p. 311"]
theorem judson_22_2_7 {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    (Matrix.vandermonde v).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) :=
  Matrix.det_vandermonde v

/-- AA-408. If `E` is a field with `p ^ n` elements, every subfield has `p ^ m` elements with
`m ∣ n`, and for each `m ∣ n` there is exactly one subfield with `p ^ m` elements. -/
@[kb "judson2026" "Theorem 22.1.7, p. 305"]
theorem judson_22_1_7 (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [Finite E]
    [Algebra (ZMod p) E] {n : ℕ} (hn : Nat.card E = p ^ n) :
    (∀ K : IntermediateField (ZMod p) E, ∃ m : ℕ, Nat.card K = p ^ m ∧ m ∣ n) ∧
    (∀ m : ℕ, m ∣ n → ∃! K : IntermediateField (ZMod p) E, Nat.card K = p ^ m) :=
  ⟨fun K => UndergradKB.AbstractAlgebra.finiteField_subfield_card_dvd p hn K,
    fun _ hm => UndergradKB.AbstractAlgebra.finiteField_exists_unique_subfield p hn hm⟩

/-- AA-413. A linear code in `F ^ n` is cyclic iff it corresponds to an ideal of
`R_n = F[x] / ⟨x ^ n - 1⟩`. -/
@[kb "judson2026" "Theorem 22.2.3, p. 309"]
theorem judson_22_2_3 {F : Type*} [Field F] {n : ℕ} [NeZero n] (C : Submodule F (Fin n → F)) :
    UndergradKB.AbstractAlgebra.CyclicCodes.IsCyclicCode C ↔
      ∃ I : Ideal (UndergradKB.AbstractAlgebra.CyclicCodes.Rn F n),
        (I : Set (UndergradKB.AbstractAlgebra.CyclicCodes.Rn F n)) =
          UndergradKB.AbstractAlgebra.CyclicCodes.toR '' (C : Set (Fin n → F)) :=
  UndergradKB.AbstractAlgebra.CyclicCodes.isCyclicCode_iff_exists_ideal C

/-- AA-415. If `x ^ n - 1 = g h`, a word lies in the cyclic code `⟨g⟩` iff its class in `R_n`
times `h` is zero (the parity-check condition `H G = 0`). -/
@[kb "judson2026" "Proposition 22.2.5, p. 310"]
theorem judson_22_2_5 {F : Type*} [Field F] {n : ℕ} [NeZero n] {g h : F[X]}
    (hgh : g * h = X ^ n - 1) (w : Fin n → F) :
    w ∈ UndergradKB.AbstractAlgebra.CyclicCodes.cyclicCodeOf n g ↔
      UndergradKB.AbstractAlgebra.CyclicCodes.toR w * AdjoinRoot.mk (X ^ n - 1 : F[X]) h = 0 :=
  UndergradKB.AbstractAlgebra.CyclicCodes.mem_cyclicCodeOf_iff_mul_eq_zero hgh w

/-- AA-418. BCH bound: if `g` vanishes at `s` consecutive powers of a primitive `n`th root `ω`,
every nonzero word of `⟨g⟩` has at least `s + 1` nonzero entries (so the minimum distance is at
least `s + 1`). -/
@[kb "judson2026" "Theorem 22.2.8, p. 311"]
theorem judson_22_2_8 {F E : Type*} [Field F] [DecidableEq F] [Field E] [Algebra F E] {n : ℕ}
    [NeZero n] {ω : E} (hω : IsPrimitiveRoot ω n) (a s : ℕ) {g : F[X]}
    (hg : ∀ k < s, aeval (ω ^ (a + k)) g = 0) {w : Fin n → F}
    (hw : w ∈ UndergradKB.AbstractAlgebra.CyclicCodes.cyclicCodeOf n g) (hw0 : w ≠ 0) :
    s + 1 ≤ hammingNorm w :=
  UndergradKB.AbstractAlgebra.CyclicCodes.bch_bound hω a s hg hw hw0

/-- AA-420. A word lies in the BCH code with designed distance `2r + 1` iff its polynomial
vanishes at `ω ^ i` for `i = 1, …, 2r`; distinct codewords are at distance at least `2r + 1`. -/
@[kb "judson2026" "Theorem 22.2.9, p. 312"]
theorem judson_22_2_9 {F E : Type*} [Field F] [DecidableEq F] [Field E] [Algebra F E] {n : ℕ}
    [NeZero n] {ω : E} (hω : IsPrimitiveRoot ω n) (r : ℕ) :
    (∀ w : Fin n → F, w ∈ UndergradKB.AbstractAlgebra.CyclicCodes.bchCode n ω r ↔
      ∀ i ∈ Finset.Icc 1 (2 * r),
        aeval (ω ^ i) (UndergradKB.AbstractAlgebra.CyclicCodes.toPoly w) = 0) ∧
    (∀ u v : Fin n → F, u ∈ UndergradKB.AbstractAlgebra.CyclicCodes.bchCode n ω r →
      v ∈ UndergradKB.AbstractAlgebra.CyclicCodes.bchCode n ω r → u ≠ v →
      2 * r + 1 ≤ hammingDist u v) :=
  ⟨fun w => UndergradKB.AbstractAlgebra.CyclicCodes.mem_bchCode_iff hω r w,
    fun _ _ hu hv huv => UndergradKB.AbstractAlgebra.CyclicCodes.bchCode_minDist hω r hu hv huv⟩

end UndergradKB.AbstractAlgebra.Course
