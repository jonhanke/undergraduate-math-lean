import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers, Section 3.4 -/

namespace UndergradKB.Precalculus.Course

open Complex ComplexConjugate

/-- `(z - a)² + b² = 0` iff `z = a ± b i`. -/
private lemma aux_cq (z a b : ℂ) : (z - a) ^ 2 + b ^ 2 = 0 ↔ z = a + b * I ∨ z = a - b * I := by
  constructor
  · intro h
    have : (z - (a + b * I)) * (z - (a - b * I)) = 0 := by linear_combination h - b ^ 2 * I_sq
    rcases mul_eq_zero.1 this with h | h
    · left; exact sub_eq_zero.1 h
    · right; exact sub_eq_zero.1 h
  · rintro (h | h) <;> rw [h] <;> linear_combination b ^ 2 * I_sq

/-- `z² + b² = 0` iff `z = ± b i`. -/
private lemma aux_sq_add (z b : ℂ) : z ^ 2 + b ^ 2 = 0 ↔ z = b * I ∨ z = -(b * I) := by
  have := aux_cq z 0 b
  simpa [sub_zero, zero_add, zero_sub] using this

/-- `(√c : ℂ)² = n` for real `c ≥ 0` with `(c : ℂ) = n`. -/
private lemma aux_sqrt_sq (c : ℝ) (n : ℂ) (hc : 0 ≤ c) (hn : (c : ℂ) = n) :
    ((√c : ℝ) : ℂ) ^ 2 = n := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hc, hn]

/-! ## Section 3.4 -/

/-- Stitz-Zeager Exercise 3.4.1: for `z = 2 + 3i`, `w = 4i`: `z + w = 2 + 7i`, `zw = -12 + 8i`,
`z² = -5 + 12i`, `1/z = 2/13 - 3i/13`, `z/w = 3/4 - i/2`, `w/z = 12/13 + 8i/13`, `z̄ = 2 - 3i`,
`z z̄ = 13`, `(z̄)² = -5 - 12i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.1, p. 307"]
theorem exer_3_4_1 :
    let z : ℂ := 2 + 3 * I
    let w : ℂ := 4 * I
    z + w = 2 + 7 * I ∧ z * w = -12 + 8 * I ∧ z ^ 2 = -5 + 12 * I ∧
    1 / z = 2 / 13 - 3 / 13 * I ∧ z / w = 3 / 4 - 1 / 2 * I ∧ w / z = 12 / 13 + 8 / 13 * I ∧
    conj z = 2 - 3 * I ∧ z * conj z = 13 ∧ conj z ^ 2 = -5 - 12 * I := by
  intro z w
  simp only [z, w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, pow_two] <;> norm_num

/-- Stitz-Zeager Exercise 3.4.3: for `z = i`, `w = -1 + 2i`: `z + w = -1 + 3i`, `zw = -2 - i`,
`z² = -1`, `1/z = -i`, `z/w = 2/5 - i/5`, `w/z = 2 + i`, `z̄ = -i`, `z z̄ = 1`, `(z̄)² = -1`. -/
@[kb "stitzzeager2013" "Exercise 3.4.3, p. 307"]
theorem exer_3_4_3 :
    let z : ℂ := I
    let w : ℂ := -1 + 2 * I
    z + w = -1 + 3 * I ∧ z * w = -2 - I ∧ z ^ 2 = -1 ∧ 1 / z = -I ∧
    z / w = 2 / 5 - 1 / 5 * I ∧ w / z = 2 + I ∧ conj z = -I ∧ z * conj z = 1 ∧
    conj z ^ 2 = -1 := by
  intro z w
  simp only [z, w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, pow_two] <;> norm_num

/-- Stitz-Zeager Exercise 3.4.5: for `z = 3 - 5i`, `w = 2 + 7i`: `z + w = 5 + 2i`, `zw = 41 + 11i`,
`z² = -16 - 30i`, `1/z = 3/34 + 5i/34`, `z/w = -29/53 - 31i/53`, `w/z = -29/34 + 31i/34`,
`z̄ = 3 + 5i`, `z z̄ = 34`, `(z̄)² = -16 + 30i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.5, p. 307"]
theorem exer_3_4_5 :
    let z : ℂ := 3 - 5 * I
    let w : ℂ := 2 + 7 * I
    z + w = 5 + 2 * I ∧ z * w = 41 + 11 * I ∧ z ^ 2 = -16 - 30 * I ∧
    1 / z = 3 / 34 + 5 / 34 * I ∧ z / w = -29 / 53 - 31 / 53 * I ∧
    w / z = -29 / 34 + 31 / 34 * I ∧ conj z = 3 + 5 * I ∧ z * conj z = 34 ∧
    conj z ^ 2 = -16 + 30 * I := by
  intro z w
  simp only [z, w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, pow_two] <;> norm_num

/-- Stitz-Zeager Exercise 3.4.13-14: with `√(-c) = i√c`, `√(-25) · √(-4) = -10`, whereas
`√((-25)(-4)) = √100 = 10`. -/
@[kb "stitzzeager2013" "Exercise 3.4.13, p. 307"]
theorem exer_3_4_13 :
    (((√25 : ℝ) : ℂ) * I) * (((√4 : ℝ) : ℂ) * I) = -10 ∧ √100 = (10 : ℝ) := by
  have h25 : √25 = (5 : ℝ) := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h4 : √4 = (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h100 : √100 = (10 : ℝ) := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, h100⟩
  rw [h25, h4]
  push_cast
  linear_combination (10 : ℂ) * I_sq

/-- Stitz-Zeager Exercise 3.4.23-26: `i¹⁵ = -i`, `i²⁶ = -1`, `i¹¹⁷ = i`, `i³⁰⁴ = 1`. -/
@[kb "stitzzeager2013" "Exercise 3.4.23, p. 307"]
theorem exer_3_4_23 : I ^ 15 = -I ∧ I ^ 26 = -1 ∧ I ^ 117 = I ∧ I ^ 304 = 1 := by
  have h4 : I ^ 4 = 1 := I_pow_four
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 15 = 4 * 3 + 3 by norm_num, pow_add, pow_mul, h4]; simp [pow_succ]
  · rw [show 26 = 4 * 6 + 2 by norm_num, pow_add, pow_mul, h4]; simp
  · rw [show 117 = 4 * 29 + 1 by norm_num, pow_add, pow_mul, h4]; simp
  · rw [show 304 = 4 * 76 by norm_num, pow_mul, h4]; simp

/-- Stitz-Zeager Exercise 3.4.27: `x² - 4x + 13 = (x - (2 + 3i))(x - (2 - 3i))`, with complex zeros
`2 ± 3i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.27, p. 307"]
theorem exer_3_4_27 (z : ℂ) :
    z ^ 2 - 4 * z + 13 = (z - (2 + 3 * I)) * (z - (2 - 3 * I)) ∧
      (z ^ 2 - 4 * z + 13 = 0 ↔ z = 2 + 3 * I ∨ z = 2 - 3 * I) := by
  refine ⟨by linear_combination 9 * I_sq, ?_⟩
  have := aux_cq z 2 3
  rw [← this]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 3.4.28: `x² - 2x + 5 = (x - (1 + 2i))(x - (1 - 2i))`, with complex zeros
`1 ± 2i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.28, p. 307"]
theorem exer_3_4_28 (z : ℂ) :
    z ^ 2 - 2 * z + 5 = (z - (1 + 2 * I)) * (z - (1 - 2 * I)) ∧
      (z ^ 2 - 2 * z + 5 = 0 ↔ z = 1 + 2 * I ∨ z = 1 - 2 * I) := by
  refine ⟨by linear_combination 4 * I_sq, ?_⟩
  have := aux_cq z 1 2
  rw [← this]
  constructor <;> intro h <;> linear_combination h

/-- Stitz-Zeager Exercise 3.4.29: the zeros of `3x² + 2x + 10` are `-1/3 ± (√29/3) i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.29, p. 307"]
theorem exer_3_4_29 (z : ℂ) :
    3 * z ^ 2 + 2 * z + 10 = 0 ↔
      z = -1 / 3 + ((√29 : ℝ) : ℂ) / 3 * I ∨ z = -1 / 3 - ((√29 : ℝ) : ℂ) / 3 * I := by
  have hs := aux_sqrt_sq 29 29 (by norm_num) (by norm_num)
  have := aux_cq z (-1 / 3) (((√29 : ℝ) : ℂ) / 3)
  rw [← this]
  constructor
  · intro h; linear_combination (1 / 3 : ℂ) * h + (1 / 9 : ℂ) * hs
  · intro h; linear_combination (3 : ℂ) * h - (1 / 3 : ℂ) * hs

/-- Stitz-Zeager Exercise 3.4.30: `x³ - 2x² + 9x - 18 = (x - 2)(x - 3i)(x + 3i)`, with complex zeros
`2`, `±3i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.30, p. 307"]
theorem exer_3_4_30 (z : ℂ) :
    z ^ 3 - 2 * z ^ 2 + 9 * z - 18 = (z - 2) * (z - 3 * I) * (z + 3 * I) ∧
      (z ^ 3 - 2 * z ^ 2 + 9 * z - 18 = 0 ↔ z = 2 ∨ z = 3 * I ∨ z = -(3 * I)) := by
  refine ⟨by linear_combination (9 * (z - 2)) * I_sq, ?_⟩
  have e : z ^ 3 - 2 * z ^ 2 + 9 * z - 18 = (z - 2) * (z ^ 2 + 3 ^ 2) := by ring
  rw [e, mul_eq_zero, sub_eq_zero, aux_sq_add]

/-- Stitz-Zeager Exercise 3.4.31: `x³ + 6x² + 6x + 5 = (x + 5)(x² + x + 1)`, with complex zeros
`-5` and `-1/2 ± (√3/2) i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.31, p. 307"]
theorem exer_3_4_31 (z : ℂ) :
    z ^ 3 + 6 * z ^ 2 + 6 * z + 5 = 0 ↔
      z = -5 ∨ z = -1 / 2 + ((√3 : ℝ) : ℂ) / 2 * I ∨ z = -1 / 2 - ((√3 : ℝ) : ℂ) / 2 * I := by
  have hs := aux_sqrt_sq 3 3 (by norm_num) (by norm_num)
  have e : z ^ 3 + 6 * z ^ 2 + 6 * z + 5 = (z + 5) * (z ^ 2 + z + 1) := by ring
  have q : z ^ 2 + z + 1 = 0 ↔ (z - (-1 / 2)) ^ 2 + (((√3 : ℝ) : ℂ) / 2) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h + (1 / 4 : ℂ) * hs
    · intro h; linear_combination h - (1 / 4 : ℂ) * hs
  rw [e, mul_eq_zero, q, aux_cq, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.4.33: `x³ + 3x² + 4x + 12 = (x + 3)(x + 2i)(x - 2i)`, with complex zeros
`-3`, `±2i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.33, p. 308"]
theorem exer_3_4_33 (z : ℂ) :
    z ^ 3 + 3 * z ^ 2 + 4 * z + 12 = (z + 3) * (z + 2 * I) * (z - 2 * I) ∧
      (z ^ 3 + 3 * z ^ 2 + 4 * z + 12 = 0 ↔ z = -3 ∨ z = 2 * I ∨ z = -(2 * I)) := by
  refine ⟨by linear_combination (4 * (z + 3)) * I_sq, ?_⟩
  have e : z ^ 3 + 3 * z ^ 2 + 4 * z + 12 = (z + 3) * (z ^ 2 + 2 ^ 2) := by ring
  rw [e, mul_eq_zero, add_eq_zero_iff_eq_neg, aux_sq_add]

/-- Stitz-Zeager Exercise 3.4.37: `4x⁴ - 4x³ + 13x² - 12x + 3 = 4(x - 1/2)²(x + i√3)(x - i√3)`;
the complex zeros are `1/2` and `±i√3`. -/
@[kb "stitzzeager2013" "Exercise 3.4.37, p. 308"]
theorem exer_3_4_37 (z : ℂ) :
    4 * z ^ 4 - 4 * z ^ 3 + 13 * z ^ 2 - 12 * z + 3 = 0 ↔
      z = 1 / 2 ∨ z = ((√3 : ℝ) : ℂ) * I ∨ z = -(((√3 : ℝ) : ℂ) * I) := by
  have hs := aux_sqrt_sq 3 3 (by norm_num) (by norm_num)
  have e : 4 * z ^ 4 - 4 * z ^ 3 + 13 * z ^ 2 - 12 * z + 3 =
      4 * (z - 1 / 2) ^ 2 * (z ^ 2 + 3) := by ring
  have q : z ^ 2 + 3 = 0 ↔ z ^ 2 + ((√3 : ℝ) : ℂ) ^ 2 = 0 := by
    rw [hs]
  rw [e, mul_eq_zero, mul_eq_zero, q, aux_sq_add]
  constructor
  · rintro ((h | h) | h)
    · norm_num at h
    · left; exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
    · right; exact h
  · rintro (h | h)
    · left; right; rw [h]; norm_num
    · right; exact h

/-- Stitz-Zeager Exercise 3.4.43: `x⁴ + 9x² + 20 = (x² + 4)(x² + 5)`, with complex zeros `±2i`,
`±i√5`. -/
@[kb "stitzzeager2013" "Exercise 3.4.43, p. 308"]
theorem exer_3_4_43 (z : ℂ) :
    z ^ 4 + 9 * z ^ 2 + 20 = 0 ↔
      z = 2 * I ∨ z = -(2 * I) ∨ z = ((√5 : ℝ) : ℂ) * I ∨ z = -(((√5 : ℝ) : ℂ) * I) := by
  have hs := aux_sqrt_sq 5 5 (by norm_num) (by norm_num)
  have e : z ^ 4 + 9 * z ^ 2 + 20 = (z ^ 2 + 2 ^ 2) * (z ^ 2 + ((√5 : ℝ) : ℂ) ^ 2) := by
    linear_combination (-(z ^ 2 + 4)) * hs
  rw [e, mul_eq_zero, aux_sq_add, aux_sq_add]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.4.47: `x⁴ - 2x³ + 27x² - 2x + 26 = (x² + 1)(x² - 2x + 26)`, with complex
zeros `±i` and `1 ± 5i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.47, p. 308"]
theorem exer_3_4_47 (z : ℂ) :
    z ^ 4 - 2 * z ^ 3 + 27 * z ^ 2 - 2 * z + 26 = 0 ↔
      z = 1 * I ∨ z = -(1 * I) ∨ z = 1 + 5 * I ∨ z = 1 - 5 * I := by
  have e : z ^ 4 - 2 * z ^ 3 + 27 * z ^ 2 - 2 * z + 26 =
      (z ^ 2 + 1 ^ 2) * ((z - 1) ^ 2 + 5 ^ 2) := by ring
  rw [e, mul_eq_zero, aux_sq_add, aux_cq]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.4.48: `2x⁴ + 5x³ + 13x² + 7x + 5 = (x² + 2x + 5)(2x² + x + 1)`, with
complex zeros `-1 ± 2i` and `-1/4 ± (√7/4) i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.48, p. 308"]
theorem exer_3_4_48 (z : ℂ) :
    2 * z ^ 4 + 5 * z ^ 3 + 13 * z ^ 2 + 7 * z + 5 = 0 ↔
      z = -1 + 2 * I ∨ z = -1 - 2 * I ∨
        z = -1 / 4 + ((√7 : ℝ) : ℂ) / 4 * I ∨ z = -1 / 4 - ((√7 : ℝ) : ℂ) / 4 * I := by
  have hs := aux_sqrt_sq 7 7 (by norm_num) (by norm_num)
  have e : 2 * z ^ 4 + 5 * z ^ 3 + 13 * z ^ 2 + 7 * z + 5 =
      ((z - (-1)) ^ 2 + 2 ^ 2) * (2 * z ^ 2 + z + 1) := by ring
  have q : 2 * z ^ 2 + z + 1 = 0 ↔ (z - (-1 / 4)) ^ 2 + (((√7 : ℝ) : ℂ) / 4) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination (1 / 2 : ℂ) * h + (1 / 16 : ℂ) * hs
    · intro h; linear_combination (2 : ℂ) * h - (1 / 8 : ℂ) * hs
  rw [e, mul_eq_zero, q, aux_cq, aux_cq]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.4.54: complex conjugation is multiplicative and an involution. -/
@[kb "stitzzeager2013" "Exercise 3.4.54, p. 308"]
theorem exer_3_4_54 (z w : ℂ) : conj (z * w) = conj z * conj w ∧ conj (conj z) = z :=
  ⟨map_mul _ z w, Complex.conj_conj z⟩

end UndergradKB.Precalculus.Course
