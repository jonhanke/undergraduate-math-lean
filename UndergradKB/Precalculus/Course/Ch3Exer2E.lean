import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.ComputeDegree
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Polynomials

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 3.4,
complex zeros and polynomials -/

namespace UndergradKB.Precalculus.Course

open Complex

private lemma w7e_cq (z a b : ℂ) : (z - a) ^ 2 + b ^ 2 = 0 ↔ z = a + b * I ∨ z = a - b * I := by
  constructor
  · intro h
    have : (z - (a + b * I)) * (z - (a - b * I)) = 0 := by linear_combination h - b ^ 2 * I_sq
    rcases mul_eq_zero.1 this with h | h
    · left; exact sub_eq_zero.1 h
    · right; exact sub_eq_zero.1 h
  · rintro (h | h) <;> rw [h] <;> linear_combination b ^ 2 * I_sq

private lemma w7e_sq_add (z b : ℂ) : z ^ 2 + b ^ 2 = 0 ↔ z = b * I ∨ z = -(b * I) := by
  have := w7e_cq z 0 b
  simpa [sub_zero, zero_add, zero_sub] using this

private lemma w7e_rq (z a b : ℂ) : (z - a) ^ 2 - b ^ 2 = 0 ↔ z = a + b ∨ z = a - b := by
  constructor
  · intro h
    have : (z - (a + b)) * (z - (a - b)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · left; exact sub_eq_zero.1 h
    · right; exact sub_eq_zero.1 h
  · rintro (h | h) <;> rw [h] <;> ring

private lemma w7e_sqrt_sq (c : ℝ) (n : ℂ) (hc : 0 ≤ c) (hn : (c : ℂ) = n) :
    ((Real.sqrt c : ℝ) : ℂ) ^ 2 = n := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hc, hn]

/-! ## Section 3.4 -/

/-- Stitz-Zeager Exercise 3.4.32: `3x³ - 13x² + 43x - 13 = (3x - 1)(x - (2 + 3i))(x - (2 - 3i))`; the
zeros are `1/3` and `2 ± 3i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.32, p. 307"]
theorem exer_3_4_32 (z : ℂ) :
    3 * z ^ 3 - 13 * z ^ 2 + 43 * z - 13 = (3 * z - 1) * (z - (2 + 3 * I)) * (z - (2 - 3 * I)) ∧
      (3 * z ^ 3 - 13 * z ^ 2 + 43 * z - 13 = 0 ↔ z = 1 / 3 ∨ z = 2 + 3 * I ∨ z = 2 - 3 * I) := by
  refine ⟨by linear_combination (9 * (3 * z - 1)) * I_sq, ?_⟩
  have e : 3 * z ^ 3 - 13 * z ^ 2 + 43 * z - 13 = (3 * z - 1) * ((z - 2) ^ 2 + 3 ^ 2) := by ring
  have a1 : 3 * z - 1 = 0 ↔ z = 1 / 3 :=
    ⟨fun h => by linear_combination h / 3, fun h => by linear_combination 3 * h⟩
  rw [e, mul_eq_zero, a1, w7e_cq]

/-- Stitz-Zeager Exercise 3.4.34: `4x³ - 6x² - 8x + 15 = 4(x + 3/2)(x - (3/2 + i/2))(x - (3/2 - i/2))`;
the zeros are `-3/2` and `3/2 ± i/2`. -/
@[kb "stitzzeager2013" "Exercise 3.4.34, p. 307"]
theorem exer_3_4_34 (z : ℂ) :
    4 * z ^ 3 - 6 * z ^ 2 - 8 * z + 15 =
        4 * (z + 3 / 2) * (z - (3 / 2 + 1 / 2 * I)) * (z - (3 / 2 - 1 / 2 * I)) ∧
      (4 * z ^ 3 - 6 * z ^ 2 - 8 * z + 15 = 0 ↔
        z = -3 / 2 ∨ z = 3 / 2 + 1 / 2 * I ∨ z = 3 / 2 - 1 / 2 * I) := by
  refine ⟨by linear_combination (z + 3 / 2) * I_sq, ?_⟩
  have e : 4 * z ^ 3 - 6 * z ^ 2 - 8 * z + 15 =
      4 * ((z + 3 / 2) * ((z - 3 / 2) ^ 2 + (1 / 2) ^ 2)) := by ring
  have a1 : z + 3 / 2 = 0 ↔ z = -3 / 2 := by constructor <;> intro h <;> linear_combination h
  rw [e, mul_eq_zero, mul_eq_zero, a1, w7e_cq]
  constructor
  · rintro (h | h | h)
    · norm_num at h
    · left; exact h
    · right; exact h
  · rintro (h | h)
    · right; left; exact h
    · right; right; exact h

/-- Stitz-Zeager Exercise 3.4.35: `x³ + 7x² + 9x - 2 = (x + 2)(x² + 5x - 1)`; the zeros are `-2` and
`(-5 ± √29)/2`. -/
@[kb "stitzzeager2013" "Exercise 3.4.35, p. 307"]
theorem exer_3_4_35 (z : ℂ) :
    z ^ 3 + 7 * z ^ 2 + 9 * z - 2 = 0 ↔
      z = -2 ∨ z = -5 / 2 + ((Real.sqrt 29 : ℝ) : ℂ) / 2 ∨ z = -5 / 2 - ((Real.sqrt 29 : ℝ) : ℂ) / 2 := by
  have hs := w7e_sqrt_sq 29 29 (by norm_num) (by norm_num)
  have e : z ^ 3 + 7 * z ^ 2 + 9 * z - 2 = (z + 2) * (z ^ 2 + 5 * z - 1) := by ring
  have q : z ^ 2 + 5 * z - 1 = 0 ↔ (z - (-5 / 2)) ^ 2 - (((Real.sqrt 29 : ℝ) : ℂ) / 2) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h - (1 / 4 : ℂ) * hs
    · intro h; linear_combination h + (1 / 4 : ℂ) * hs
  have a1 : z + 2 = 0 ↔ z = -2 := by constructor <;> intro h <;> linear_combination h
  rw [e, mul_eq_zero, a1, q, w7e_rq]

/-- Stitz-Zeager Exercise 3.4.36: `9x³ + 2x + 1 = (x + 1/3)(9x² - 3x + 3)`; the zeros are `-1/3` and
`1/6 ± (√11/6) i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.36, p. 307"]
theorem exer_3_4_36 (z : ℂ) :
    9 * z ^ 3 + 2 * z + 1 = 0 ↔
      z = -1 / 3 ∨ z = 1 / 6 + ((Real.sqrt 11 : ℝ) : ℂ) / 6 * I ∨
        z = 1 / 6 - ((Real.sqrt 11 : ℝ) : ℂ) / 6 * I := by
  have hs := w7e_sqrt_sq 11 11 (by norm_num) (by norm_num)
  have e : 9 * z ^ 3 + 2 * z + 1 = (z + 1 / 3) * (9 * z ^ 2 - 3 * z + 3) := by ring
  have q : 9 * z ^ 2 - 3 * z + 3 = 0 ↔
      (z - 1 / 6) ^ 2 + (((Real.sqrt 11 : ℝ) : ℂ) / 6) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination (1 / 9 : ℂ) * h + (1 / 36 : ℂ) * hs
    · intro h; linear_combination (9 : ℂ) * h - (1 / 4 : ℂ) * hs
  have a1 : z + 1 / 3 = 0 ↔ z = -1 / 3 := by constructor <;> intro h <;> linear_combination h
  rw [e, mul_eq_zero, a1, q, w7e_cq]

/-- Stitz-Zeager Exercise 3.4.38: `2x⁴ - 7x³ + 14x² - 15x + 6 = (x - 1)²(2x² - 3x + 6)`; the zeros are
`1` (double) and `3/4 ± (√39/4) i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.38, p. 308"]
theorem exer_3_4_38 (z : ℂ) :
    2 * z ^ 4 - 7 * z ^ 3 + 14 * z ^ 2 - 15 * z + 6 = 0 ↔
      z = 1 ∨ z = 3 / 4 + ((Real.sqrt 39 : ℝ) : ℂ) / 4 * I ∨
        z = 3 / 4 - ((Real.sqrt 39 : ℝ) : ℂ) / 4 * I := by
  have hs := w7e_sqrt_sq 39 39 (by norm_num) (by norm_num)
  have e : 2 * z ^ 4 - 7 * z ^ 3 + 14 * z ^ 2 - 15 * z + 6 =
      (z - 1) ^ 2 * (2 * z ^ 2 - 3 * z + 6) := by ring
  have q : 2 * z ^ 2 - 3 * z + 6 = 0 ↔
      (z - 3 / 4) ^ 2 + (((Real.sqrt 39 : ℝ) : ℂ) / 4) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination (1 / 2 : ℂ) * h + (1 / 16 : ℂ) * hs
    · intro h; linear_combination (2 : ℂ) * h - (1 / 8 : ℂ) * hs
  rw [e, mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero, q, w7e_cq]

/-- Stitz-Zeager Exercise 3.4.39: `x⁴ + x³ + 7x² + 9x - 18 = (x + 2)(x - 1)(x² + 9)`; the zeros are
`-2`, `1`, `±3i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.39, p. 308"]
theorem exer_3_4_39 (z : ℂ) :
    z ^ 4 + z ^ 3 + 7 * z ^ 2 + 9 * z - 18 = (z + 2) * (z - 1) * (z - 3 * I) * (z + 3 * I) ∧
      (z ^ 4 + z ^ 3 + 7 * z ^ 2 + 9 * z - 18 = 0 ↔ z = -2 ∨ z = 1 ∨ z = 3 * I ∨ z = -(3 * I)) := by
  refine ⟨by linear_combination (9 * (z + 2) * (z - 1)) * I_sq, ?_⟩
  have e : z ^ 4 + z ^ 3 + 7 * z ^ 2 + 9 * z - 18 = (z + 2) * (z - 1) * (z ^ 2 + 3 ^ 2) := by ring
  rw [e, mul_eq_zero, mul_eq_zero, w7e_sq_add, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

/-- Stitz-Zeager Exercise 3.4.40: `6x⁴ + 17x³ - 55x² + 16x + 12 = (3x + 1)(2x - 3)(x² + 4x - 4)`; the
zeros are `-1/3`, `3/2`, `-2 ± 2√2`. -/
@[kb "stitzzeager2013" "Exercise 3.4.40, p. 308"]
theorem exer_3_4_40 (z : ℂ) :
    6 * z ^ 4 + 17 * z ^ 3 - 55 * z ^ 2 + 16 * z + 12 = 0 ↔
      z = -1 / 3 ∨ z = 3 / 2 ∨ z = -2 + 2 * ((Real.sqrt 2 : ℝ) : ℂ) ∨
        z = -2 - 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hs := w7e_sqrt_sq 2 2 (by norm_num) (by norm_num)
  have e : 6 * z ^ 4 + 17 * z ^ 3 - 55 * z ^ 2 + 16 * z + 12 =
      (3 * z + 1) * (2 * z - 3) * (z ^ 2 + 4 * z - 4) := by ring
  have q : z ^ 2 + 4 * z - 4 = 0 ↔ (z - (-2)) ^ 2 - (2 * ((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h - 4 * hs
    · intro h; linear_combination h + 4 * hs
  have a1 : 3 * z + 1 = 0 ↔ z = -1 / 3 :=
    ⟨fun h => by linear_combination h / 3, fun h => by linear_combination 3 * h⟩
  have a2 : 2 * z - 3 = 0 ↔ z = 3 / 2 :=
    ⟨fun h => by linear_combination h / 2, fun h => by linear_combination 2 * h⟩
  rw [e, mul_eq_zero, mul_eq_zero, a1, a2, q, w7e_rq]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.4.41: `-3x⁴ - 8x³ - 12x² - 12x - 5 = (x + 1)²(-3x² - 2x - 5)`; the zeros
are `-1` (double) and `-1/3 ± (√14/3) i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.41, p. 308"]
theorem exer_3_4_41 (z : ℂ) :
    -3 * z ^ 4 - 8 * z ^ 3 - 12 * z ^ 2 - 12 * z - 5 = 0 ↔
      z = -1 ∨ z = -1 / 3 + ((Real.sqrt 14 : ℝ) : ℂ) / 3 * I ∨
        z = -1 / 3 - ((Real.sqrt 14 : ℝ) : ℂ) / 3 * I := by
  have hs := w7e_sqrt_sq 14 14 (by norm_num) (by norm_num)
  have e : -3 * z ^ 4 - 8 * z ^ 3 - 12 * z ^ 2 - 12 * z - 5 =
      (z + 1) ^ 2 * (-3 * z ^ 2 - 2 * z - 5) := by ring
  have q : -3 * z ^ 2 - 2 * z - 5 = 0 ↔
      (z - (-1 / 3)) ^ 2 + (((Real.sqrt 14 : ℝ) : ℂ) / 3) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination (-1 / 3 : ℂ) * h + (1 / 9 : ℂ) * hs
    · intro h; linear_combination (-3 : ℂ) * h + (1 / 3 : ℂ) * hs
  rw [e, mul_eq_zero, pow_eq_zero_iff two_ne_zero, q, w7e_cq, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.4.42: `8x⁴ + 50x³ + 43x² + 2x - 4 = (2x + 1)(4x - 1)(x² + 6x + 4)`; the
zeros are `-1/2`, `1/4`, `-3 ± √5`. -/
@[kb "stitzzeager2013" "Exercise 3.4.42, p. 308"]
theorem exer_3_4_42 (z : ℂ) :
    8 * z ^ 4 + 50 * z ^ 3 + 43 * z ^ 2 + 2 * z - 4 = 0 ↔
      z = -1 / 2 ∨ z = 1 / 4 ∨ z = -3 + ((Real.sqrt 5 : ℝ) : ℂ) ∨ z = -3 - ((Real.sqrt 5 : ℝ) : ℂ) := by
  have hs := w7e_sqrt_sq 5 5 (by norm_num) (by norm_num)
  have e : 8 * z ^ 4 + 50 * z ^ 3 + 43 * z ^ 2 + 2 * z - 4 =
      (2 * z + 1) * (4 * z - 1) * (z ^ 2 + 6 * z + 4) := by ring
  have q : z ^ 2 + 6 * z + 4 = 0 ↔ (z - (-3)) ^ 2 - ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h - hs
    · intro h; linear_combination h + hs
  have a1 : 2 * z + 1 = 0 ↔ z = -1 / 2 :=
    ⟨fun h => by linear_combination h / 2, fun h => by linear_combination 2 * h⟩
  have a2 : 4 * z - 1 = 0 ↔ z = 1 / 4 :=
    ⟨fun h => by linear_combination h / 4, fun h => by linear_combination 4 * h⟩
  rw [e, mul_eq_zero, mul_eq_zero, a1, a2, q, w7e_rq]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.4.44: `x⁴ + 5x² - 24 = (x² - 3)(x² + 8)`; the zeros are `±√3` and
`±2√2 i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.44, p. 308"]
theorem exer_3_4_44 (z : ℂ) :
    z ^ 4 + 5 * z ^ 2 - 24 = 0 ↔
      z = ((Real.sqrt 3 : ℝ) : ℂ) ∨ z = -((Real.sqrt 3 : ℝ) : ℂ) ∨
        z = 2 * ((Real.sqrt 2 : ℝ) : ℂ) * I ∨ z = -(2 * ((Real.sqrt 2 : ℝ) : ℂ) * I) := by
  have h3 := w7e_sqrt_sq 3 3 (by norm_num) (by norm_num)
  have h2 := w7e_sqrt_sq 2 2 (by norm_num) (by norm_num)
  have e : z ^ 4 + 5 * z ^ 2 - 24 = (z ^ 2 - 3) * (z ^ 2 + 8) := by ring
  have q1 : z ^ 2 - 3 = 0 ↔ (z - 0) ^ 2 - ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h - h3
    · intro h; linear_combination h + h3
  have q2 : z ^ 2 + 8 = 0 ↔ z ^ 2 + (2 * ((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h + 4 * h2
    · intro h; linear_combination h - 4 * h2
  rw [e, mul_eq_zero, q1, q2, w7e_rq, w7e_sq_add]
  simp only [zero_add, zero_sub, or_assoc]

/-- Stitz-Zeager Exercise 3.4.45: `x⁵ - x⁴ + 7x³ - 7x² + 12x - 12 = (x - 1)(x² + 3)(x² + 4)`; the
zeros are `1`, `±i√3`, `±2i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.45, p. 308"]
theorem exer_3_4_45 (z : ℂ) :
    z ^ 5 - z ^ 4 + 7 * z ^ 3 - 7 * z ^ 2 + 12 * z - 12 = 0 ↔
      z = 1 ∨ z = ((Real.sqrt 3 : ℝ) : ℂ) * I ∨ z = -(((Real.sqrt 3 : ℝ) : ℂ) * I) ∨
        z = 2 * I ∨ z = -(2 * I) := by
  have h3 := w7e_sqrt_sq 3 3 (by norm_num) (by norm_num)
  have e : z ^ 5 - z ^ 4 + 7 * z ^ 3 - 7 * z ^ 2 + 12 * z - 12 =
      (z - 1) * ((z ^ 2 + 3) * (z ^ 2 + 4)) := by ring
  have q1 : z ^ 2 + 3 = 0 ↔ z ^ 2 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 0 := by rw [h3]
  have q2 : z ^ 2 + 4 = 0 ↔ z ^ 2 + 2 ^ 2 = 0 := by norm_num
  rw [e, mul_eq_zero, mul_eq_zero, q1, q2, w7e_sq_add, w7e_sq_add, sub_eq_zero]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.4.46: `x⁶ - 64 = (x - 2)(x + 2)(x² + 2x + 4)(x² - 2x + 4)`; the zeros are
`±2`, `-1 ± i√3`, `1 ± i√3`. -/
@[kb "stitzzeager2013" "Exercise 3.4.46, p. 308"]
theorem exer_3_4_46 (z : ℂ) :
    z ^ 6 - 64 = 0 ↔
      z = 2 ∨ z = -2 ∨ z = -1 + ((Real.sqrt 3 : ℝ) : ℂ) * I ∨ z = -1 - ((Real.sqrt 3 : ℝ) : ℂ) * I ∨
        z = 1 + ((Real.sqrt 3 : ℝ) : ℂ) * I ∨ z = 1 - ((Real.sqrt 3 : ℝ) : ℂ) * I := by
  have h3 := w7e_sqrt_sq 3 3 (by norm_num) (by norm_num)
  have e : z ^ 6 - 64 = (z - 2) * (z + 2) * ((z ^ 2 + 2 * z + 4) * (z ^ 2 - 2 * z + 4)) := by ring
  have q1 : z ^ 2 + 2 * z + 4 = 0 ↔ (z - (-1)) ^ 2 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h + h3
    · intro h; linear_combination h - h3
  have q2 : z ^ 2 - 2 * z + 4 = 0 ↔ (z - 1) ^ 2 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 0 := by
    constructor
    · intro h; linear_combination h + h3
    · intro h; linear_combination h - h3
  have a1 : z - 2 = 0 ↔ z = 2 := ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have a2 : z + 2 = 0 ↔ z = -2 := ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  rw [e, mul_eq_zero, mul_eq_zero, mul_eq_zero, a1, a2, q1, q2, w7e_cq, w7e_cq]
  simp only [or_assoc]

open Polynomial Filter in
/-- Stitz-Zeager Exercise 3.4.49: `f(x) = 42(x - 1)(x + 1)(x² + 1)` has real coefficients, degree `4`,
leading term `42x⁴`, real zeros `±1` and complex zeros `±i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.49, p. 308"]
theorem exer_3_4_49 (f : ℝ[X]) (hf : f = 42 * (X - 1) * (X + 1) * (X ^ 2 + 1)) :
    f.natDegree = 4 ∧ f.leadingCoeff = 42 ∧
      (∀ x : ℝ, f.eval x = 0 ↔ x = 1 ∨ x = -1) ∧
      (∀ z : ℂ, aeval z f = 0 ↔ z = 1 ∨ z = -1 ∨ z = I ∨ z = -I) := by
  have e : f = 42 * X ^ 4 - 42 := by rw [hf]; ring
  have hd : f.natDegree = 4 := by rw [e]; compute_degree!
  refine ⟨hd, by rw [leadingCoeff, hd, e]; compute_degree!, fun x => ?_, fun z => ?_⟩
  · simp only [hf, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_one, eval_ofNat,
      mul_eq_zero]
    constructor
    · rintro (((h | h) | h) | h)
      · norm_num at h
      · left; linarith
      · right; linarith
      · nlinarith [sq_nonneg x]
    · rintro (h | h)
      · left; left; right; linarith
      · left; right; linarith
  · have h42 : aeval z (42 : ℝ[X]) = 42 := map_ofNat (aeval z) 42
    have h1 : aeval z f = 42 * ((z - 1) * (z + 1) * (z ^ 2 + 1)) := by
      simp [hf, h42]; ring
    have h2 : z ^ 2 + 1 = 0 ↔ z = I ∨ z = -I := by
      have := w7e_sq_add z 1
      simpa using this
    rw [h1, mul_eq_zero, mul_eq_zero, mul_eq_zero, h2, sub_eq_zero]
    constructor
    · rintro (h | (h | h) | h | h)
      · norm_num at h
      · left; exact h
      · right; left; linear_combination h
      · right; right; left; exact h
      · right; right; right; exact h
    · rintro (h | h | h | h)
      · right; left; left; exact h
      · right; left; right; linear_combination h
      · right; right; left; exact h
      · right; right; right; exact h

open Polynomial Filter

private lemma w7e_aeval_ofNat (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (aeval z) (OfNat.ofNat n : ℝ[X]) = OfNat.ofNat n := map_ofNat (aeval z) n

/-- Stitz-Zeager Exercise 3.4.50: `f(x) = 117(x + 1)²(x² + 4)` has leading term `117x⁴`, the zero `2i`,
and `(-1, 0)` is a (global, hence local) minimum of its graph. -/
@[kb "stitzzeager2013" "Exercise 3.4.50, p. 308"]
theorem exer_3_4_50 (f : ℝ[X]) (hf : f = 117 * (X + 1) ^ 2 * (X ^ 2 + 4)) :
    f.natDegree = 4 ∧ f.leadingCoeff = 117 ∧ aeval (2 * I : ℂ) f = 0 ∧
      (∀ x : ℝ, f.eval (-1) ≤ f.eval x) := by
  have e : f = 117 * X ^ 4 + 234 * X ^ 3 + 585 * X ^ 2 + 936 * X + 468 := by rw [hf]; ring
  have hd : f.natDegree = 4 := by rw [e]; compute_degree!
  refine ⟨hd, by rw [leadingCoeff, hd, e]; compute_degree!, ?_, fun x => ?_⟩
  · have h117 : aeval (2 * I : ℂ) (117 : ℝ[X]) = 117 := map_ofNat _ 117
    have h4 : aeval (2 * I : ℂ) (4 : ℝ[X]) = 4 := map_ofNat _ 4
    simp only [hf, map_mul, map_add, map_sub, map_pow, aeval_X, map_one, h117, h4]
    linear_combination (117 * (2 * I + 1) ^ 2 * 4) * I_sq
  · simp [hf]
    positivity

/-- Stitz-Zeager Exercise 3.4.51: `f(x) = -3(x - 2)²(x + 2)(x² + 49)` has leading term `-3x⁵`, real zeros
`±2`, the complex zero `7i`, and `(2, 0)` is a local maximum of its graph. -/
@[kb "stitzzeager2013" "Exercise 3.4.51, p. 308"]
theorem exer_3_4_51 (f : ℝ[X]) (hf : f = -3 * (X - 2) ^ 2 * (X + 2) * (X ^ 2 + 49)) :
    f.natDegree = 5 ∧ f.leadingCoeff = -3 ∧ aeval (7 * I : ℂ) f = 0 ∧
      (∀ x : ℝ, f.eval x = 0 ↔ x = 2 ∨ x = -2) ∧
      (∀ x : ℝ, |x - 2| < 1 → f.eval x ≤ f.eval 2) := by
  have e : f = -3 * X ^ 5 + 6 * X ^ 4 - 135 * X ^ 3 + 270 * X ^ 2 + 588 * X - 1176 := by
    rw [hf]; ring
  have hd : f.natDegree = 5 := by rw [e]; compute_degree!
  have hev : ∀ x : ℝ, f.eval x = -3 * ((x - 2) ^ 2 * ((x + 2) * (x ^ 2 + 49))) := by
    intro x; simp [hf]; ring
  refine ⟨hd, by rw [leadingCoeff, hd, e]; compute_degree!, ?_, fun x => ?_, fun x hx => ?_⟩
  · have h3 : aeval (7 * I : ℂ) (3 : ℝ[X]) = 3 := map_ofNat _ 3
    have h2 : aeval (7 * I : ℂ) (2 : ℝ[X]) = 2 := map_ofNat _ 2
    have h49 : aeval (7 * I : ℂ) (49 : ℝ[X]) = 49 := map_ofNat _ 49
    simp only [hf, map_mul, map_add, map_sub, map_pow, map_neg, aeval_X, h3, h2, h49]
    linear_combination (-3 * (7 * I - 2) ^ 2 * (7 * I + 2) * 49) * I_sq
  · rw [hev, mul_eq_zero, mul_eq_zero, mul_eq_zero, pow_eq_zero_iff two_ne_zero]
    constructor
    · rintro (h | h | h | h)
      · norm_num at h
      · left; linarith
      · right; linarith
      · nlinarith [sq_nonneg x]
    · rintro (h | h)
      · right; left; linarith
      · right; right; left; linarith
  · rw [hev, hev]
    rw [abs_lt] at hx
    have h1 : 0 ≤ (x - 2) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (x + 2) * (x ^ 2 + 49) := mul_nonneg (by linarith) (by positivity)
    norm_num
    nlinarith [mul_nonneg h1 h2]

/-- Stitz-Zeager Exercise 3.4.52: for `a < 0`, `f(x) = a(x - 6)(x² + 1)(x² - 2x + 10)` has degree `5`,
the zeros `6`, `i`, `1 ± 3i`, and tends to `+∞` as `x → -∞`. -/
@[kb "stitzzeager2013" "Exercise 3.4.52, p. 308"]
theorem exer_3_4_52 (a : ℝ) (ha : a < 0) (f : ℝ[X])
    (hf : f = C a * (X - 6) * (X ^ 2 + 1) * (X ^ 2 - 2 * X + 10)) :
    f.natDegree = 5 ∧ f.eval 6 = 0 ∧ aeval (I : ℂ) f = 0 ∧ aeval (1 - 3 * I : ℂ) f = 0 ∧
      aeval (1 + 3 * I : ℂ) f = 0 ∧ Tendsto (fun x : ℝ => f.eval x) atBot atTop := by
  have ha0 : a ≠ 0 := ha.ne
  have e : f = C a * (X ^ 5 - 8 * X ^ 4 + 23 * X ^ 3 - 68 * X ^ 2 + 22 * X - 60) := by
    rw [hf]; ring
  have hd : f.natDegree = 5 := by rw [e]; compute_degree!
  have hl : f.leadingCoeff = a := by rw [leadingCoeff, hd, e]; compute_degree!
  have hA : ∀ z : ℂ, aeval z f = (a : ℂ) * (z - 6) * (z ^ 2 + 1) * (z ^ 2 - 2 * z + 10) := by
    intro z
    have h6 : aeval z (6 : ℝ[X]) = 6 := map_ofNat _ 6
    have h2 : aeval z (2 : ℝ[X]) = 2 := map_ofNat _ 2
    have h10 : aeval z (10 : ℝ[X]) = 10 := map_ofNat _ 10
    simp only [hf, map_mul, map_add, map_sub, map_pow, aeval_X, aeval_C, map_one, h6, h2, h10]
    rfl
  refine ⟨hd, by simp [hf], ?_, ?_, ?_, ?_⟩
  · rw [hA]; linear_combination ((a : ℂ) * (I - 6) * (I ^ 2 - 2 * I + 10)) * I_sq
  · rw [hA]; linear_combination ((a : ℂ) * (1 - 3 * I - 6) * ((1 - 3 * I) ^ 2 + 1) * 9) * I_sq
  · rw [hA]; linear_combination ((a : ℂ) * (1 + 3 * I - 6) * ((1 + 3 * I) ^ 2 + 1) * 9) * I_sq
  · have hp : 0 < f.degree := by
      rw [degree_eq_natDegree (by intro h; rw [h] at hd; simp at hd), hd]; norm_num
    exact ((poly_tendsto_atBot_cases f hp).2 (by rw [hd]; decide)).2 (by rw [hl]; exact ha)

/-- Stitz-Zeager Exercise 3.4.53: `f(x) = -2(x² + 4)(x + 2)` has leading term `-2x³`, the zero `2i`, and
`f(0) = -16`. -/
@[kb "stitzzeager2013" "Exercise 3.4.53, p. 308"]
theorem exer_3_4_53 (f : ℝ[X]) (hf : f = -2 * (X ^ 2 + 4) * (X + 2)) :
    f.natDegree = 3 ∧ f.leadingCoeff = -2 ∧ aeval (2 * I : ℂ) f = 0 ∧ f.eval 0 = -16 := by
  have e : f = -2 * X ^ 3 - 4 * X ^ 2 - 8 * X - 16 := by rw [hf]; ring
  have hd : f.natDegree = 3 := by rw [e]; compute_degree!
  refine ⟨hd, by rw [leadingCoeff, hd, e]; compute_degree!, ?_, by simp [hf]; norm_num⟩
  have h2 : aeval (2 * I : ℂ) (2 : ℝ[X]) = 2 := map_ofNat _ 2
  have h4 : aeval (2 * I : ℂ) (4 : ℝ[X]) = 4 := map_ofNat _ 4
  simp only [hf, map_mul, map_add, map_pow, map_neg, aeval_X, h2, h4]
  linear_combination (-2 * (2 * I + 2) * 4) * I_sq

end UndergradKB.Precalculus.Course
