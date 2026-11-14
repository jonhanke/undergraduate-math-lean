import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers, Section 3.3 -/

namespace UndergradKB.Precalculus.Course

open Polynomial

private lemma aux_rm (q : ℝ[X]) (a : ℝ) (n : ℕ) (h : q.eval a ≠ 0) :
    (q * (X - C a) ^ n).rootMultiplicity a = n := by
  have hq : q ≠ 0 := fun h0 => h (by simp [h0])
  rw [rootMultiplicity_mul_X_sub_C_pow hq, rootMultiplicity_eq_zero (by simpa [IsRoot] using h)]
  simp

private lemma aux_rm' (p q : ℝ[X]) (a : ℝ) (n : ℕ) (hp : p = q * (X - C a) ^ n)
    (h : q.eval a ≠ 0) : p.rootMultiplicity a = n := by
  rw [hp]; exact aux_rm q a n h

private lemma aux_sq_eq_sqrt (y c : ℝ) (hc : 0 ≤ c) : y ^ 2 = c ↔ y = √c ∨ y = -√c := by
  have h := Real.sq_sqrt hc
  constructor
  · intro hy
    have : (y - √c) * (y + √c) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (h1 | h1) <;> rw [h1] <;> nlinarith

/-- `x² - c = 0` iff `x = ±√c`, with the roots in the order used below. -/
private lemma aux_sq_sub (x c : ℝ) (hc : 0 ≤ c) : x ^ 2 - c = 0 ↔ x = -√c ∨ x = √c := by
  rw [sub_eq_zero, aux_sq_eq_sqrt x c hc, or_comm]

private lemma aux_pos (r s x : ℝ) (h : r ≤ s) : 0 < (x - r) * (x - s) ↔ x < r ∨ s < x := by
  constructor
  · intro h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sub_nonneg.2 hc.1) (sub_nonneg.2 hc.2)]
  · rintro (a | a)
    · nlinarith [mul_pos (sub_pos.2 a) (sub_pos.2 (lt_of_lt_of_le a h))]
    · nlinarith [mul_pos (sub_pos.2 (lt_of_le_of_lt h a)) (sub_pos.2 a)]

private lemma aux_nonneg (r s x : ℝ) (h : r ≤ s) : 0 ≤ (x - r) * (x - s) ↔ x ≤ r ∨ s ≤ x := by
  constructor
  · intro h1
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hc.1) (sub_pos.2 hc.2)]
  · rintro (a | a)
    · nlinarith [mul_nonneg (sub_nonneg.2 a) (sub_nonneg.2 (le_trans a h))]
    · nlinarith [mul_nonneg (sub_nonneg.2 (le_trans h a)) (sub_nonneg.2 a)]

private lemma aux_nonpos (r s x : ℝ) (h : r ≤ s) : (x - r) * (x - s) ≤ 0 ↔ r ≤ x ∧ x ≤ s := by
  rw [← not_lt, aux_pos r s x h]; push Not; exact Iff.rfl

/-- Sign of a cubic with three real roots `r₁ ≤ r₂ ≤ r₃`. -/
private lemma aux3_neg (r1 r2 r3 x : ℝ) (h1 : r1 ≤ r2) (h2 : r2 ≤ r3) :
    (x - r1) * (x - r2) * (x - r3) < 0 ↔ x < r1 ∨ (r2 < x ∧ x < r3) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨a, b⟩ := hc
    rcases lt_or_ge x r2 with c | c
    · have p1 : 0 ≤ (x - r2) * (x - r3) :=
        (mul_pos_of_neg_of_neg (by linarith) (by linarith)).le
      nlinarith [mul_nonneg (sub_nonneg.2 a) p1]
    · rcases eq_or_lt_of_le c with c | c
      · have : x - r2 = 0 := by linarith
        rw [this, mul_zero, zero_mul] at h
        exact lt_irrefl _ h
      · have b' := b c
        have p1 : 0 ≤ (x - r1) * (x - r2) := mul_nonneg (by linarith) (by linarith)
        nlinarith [mul_nonneg p1 (sub_nonneg.2 b')]
  · rintro (a | ⟨a, b⟩)
    · have p1 : 0 < (x - r1) * (x - r2) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      exact mul_neg_of_pos_of_neg p1 (by linarith)
    · have p1 : 0 < (x - r1) * (x - r2) := mul_pos (by linarith) (by linarith)
      exact mul_neg_of_pos_of_neg p1 (by linarith)

/-! ## Section 3.3 -/

/-- Stitz-Zeager Exercise 3.3.11: `f(x) = x³ - 2x² - 5x + 6` has the three simple zeros `-2, 1, 3`. -/
@[kb "stitzzeager2013" "Exercise 3.3.11, p. 292"]
theorem exer_3_3_11 (f : ℝ[X]) (hf : f = X ^ 3 - 2 * X ^ 2 - 5 * X + 6) :
    f.rootMultiplicity (-2) = 1 ∧ f.rootMultiplicity 1 = 1 ∧ f.rootMultiplicity 3 = 1 ∧
      ∀ x : ℝ, f.eval x = 0 ↔ x = -2 ∨ x = 1 ∨ x = 3 := by
  have e : f = (X + 2) * (X - 1) * (X - 3) := by rw [hf]; ring
  refine ⟨aux_rm' _ ((X - 1) * (X - 3)) (-2) 1 ?_ (by simp; norm_num),
    aux_rm' _ ((X + 2) * (X - 3)) 1 1 ?_ (by simp; norm_num),
    aux_rm' _ ((X + 2) * (X - 1)) 3 1 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [e]; simp only [map_neg, map_ofNat]; ring
  · rw [e]; simp only [map_one]; ring
  · rw [e]; simp only [map_ofNat]; ring
  · rw [e]; simp [sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

/-- Stitz-Zeager Exercise 3.3.12: `f(x) = x⁴ + 2x³ - 12x² - 40x - 32` has the zeros `-2`
(multiplicity `3`) and `4` (multiplicity `1`). -/
@[kb "stitzzeager2013" "Exercise 3.3.12, p. 292"]
theorem exer_3_3_12 (f : ℝ[X]) (hf : f = X ^ 4 + 2 * X ^ 3 - 12 * X ^ 2 - 40 * X - 32) :
    f.rootMultiplicity (-2) = 3 ∧ f.rootMultiplicity 4 = 1 ∧
      ∀ x : ℝ, f.eval x = 0 ↔ x = -2 ∨ x = 4 := by
  have e : f = (X - 4) * (X + 2) ^ 3 := by rw [hf]; ring
  refine ⟨aux_rm' _ (X - 4) (-2) 3 ?_ (by simp; norm_num),
    aux_rm' _ ((X + 2) ^ 3) 4 1 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [e]; simp only [map_neg, map_ofNat]; ring
  · rw [e]; simp only [map_ofNat]; ring
  · rw [e]; simp [sub_eq_zero, add_eq_zero_iff_eq_neg, or_comm]

/-- Stitz-Zeager Exercise 3.3.13: `f(x) = x⁴ - 9x² - 4x + 12` has the zeros `-2` (multiplicity
`2`), `1` and `3` (multiplicity `1` each). -/
@[kb "stitzzeager2013" "Exercise 3.3.13, p. 292"]
theorem exer_3_3_13 (f : ℝ[X]) (hf : f = X ^ 4 - 9 * X ^ 2 - 4 * X + 12) :
    f.rootMultiplicity (-2) = 2 ∧ f.rootMultiplicity 1 = 1 ∧ f.rootMultiplicity 3 = 1 ∧
      ∀ x : ℝ, f.eval x = 0 ↔ x = -2 ∨ x = 1 ∨ x = 3 := by
  have e : f = (X + 2) ^ 2 * (X - 1) * (X - 3) := by rw [hf]; ring
  refine ⟨aux_rm' _ ((X - 1) * (X - 3)) (-2) 2 ?_ (by simp; norm_num),
    aux_rm' _ ((X + 2) ^ 2 * (X - 3)) 1 1 ?_ (by simp; norm_num),
    aux_rm' _ ((X + 2) ^ 2 * (X - 1)) 3 1 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [e]; simp only [map_neg, map_ofNat]; ring
  · rw [e]; simp only [map_one]; ring
  · rw [e]; simp only [map_ofNat]; ring
  · rw [e]; simp [sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

/-- Stitz-Zeager Exercise 3.3.14: `f(x) = x³ + 4x² - 11x + 6` has the zeros `-6` (multiplicity `1`)
and `1` (multiplicity `2`). -/
@[kb "stitzzeager2013" "Exercise 3.3.14, p. 292"]
theorem exer_3_3_14 (f : ℝ[X]) (hf : f = X ^ 3 + 4 * X ^ 2 - 11 * X + 6) :
    f.rootMultiplicity (-6) = 1 ∧ f.rootMultiplicity 1 = 2 ∧
      ∀ x : ℝ, f.eval x = 0 ↔ x = -6 ∨ x = 1 := by
  have e : f = (X + 6) * (X - 1) ^ 2 := by rw [hf]; ring
  refine ⟨aux_rm' _ ((X - 1) ^ 2) (-6) 1 ?_ (by simp; norm_num),
    aux_rm' _ (X + 6) 1 2 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [e]; simp only [map_neg, map_ofNat]; ring
  · rw [e]; simp only [map_one]
  · rw [e]; simp [sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.3.15: `f(x) = x³ - 7x² + x - 7` has the single real zero `7`, of
multiplicity `1`. -/
@[kb "stitzzeager2013" "Exercise 3.3.15, p. 292"]
theorem exer_3_3_15 (f : ℝ[X]) (hf : f = X ^ 3 - 7 * X ^ 2 + X - 7) :
    f.rootMultiplicity 7 = 1 ∧ ∀ x : ℝ, f.eval x = 0 ↔ x = 7 := by
  have e : f = (X ^ 2 + 1) * (X - 7) := by rw [hf]; ring
  refine ⟨aux_rm' _ (X ^ 2 + 1) 7 1 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [e]; simp only [map_ofNat]; ring
  · rw [e]
    simp only [eval_mul, eval_add, eval_pow, eval_X, eval_one, eval_sub, eval_ofNat, mul_eq_zero,
      sub_eq_zero]
    constructor
    · rintro (h | h)
      · nlinarith [sq_nonneg x]
      · exact h
    · intro h; right; exact h

/-- Stitz-Zeager Exercise 3.3.16: `-2x³ + 19x² - 49x + 20 = (1 - 2x)(x - 4)(x - 5)`, with simple
zeros `1/2`, `4`, `5`. -/
@[kb "stitzzeager2013" "Exercise 3.3.16, p. 292"]
theorem exer_3_3_16 (x : ℝ) :
    -2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20 = (1 - 2 * x) * (x - 4) * (x - 5) ∧
      (-2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20 = 0 ↔ x = 1 / 2 ∨ x = 4 ∨ x = 5) := by
  have e : -2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20 = (1 - 2 * x) * (x - 4) * (x - 5) := by ring
  have a1 : 1 - 2 * x = 0 ↔ x = 1 / 2 := by constructor <;> intro h <;> linarith
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, mul_eq_zero, a1, sub_eq_zero, sub_eq_zero]
  tauto

/-- Stitz-Zeager Exercise 3.3.17: `-17x³ + 5x² + 34x - 10 = (5 - 17x)(x² - 2)`, with simple zeros
`5/17` and `±√2`. -/
@[kb "stitzzeager2013" "Exercise 3.3.17, p. 292"]
theorem exer_3_3_17 (x : ℝ) :
    -17 * x ^ 3 + 5 * x ^ 2 + 34 * x - 10 = (5 - 17 * x) * (x ^ 2 - 2) ∧
      (-17 * x ^ 3 + 5 * x ^ 2 + 34 * x - 10 = 0 ↔ x = 5 / 17 ∨ x = -√2 ∨ x = √2) := by
  have e : -17 * x ^ 3 + 5 * x ^ 2 + 34 * x - 10 = (5 - 17 * x) * (x ^ 2 - 2) := by ring
  have a1 : 5 - 17 * x = 0 ↔ x = 5 / 17 := by constructor <;> intro h <;> linarith
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, a1, aux_sq_sub x 2 (by norm_num)]

/-- Stitz-Zeager Exercise 3.3.18: `36x⁴ - 12x³ - 11x² + 2x + 1 = (2x - 1)²(3x + 1)²`, with zeros
`1/2` and `-1/3`, each of multiplicity `2`. -/
@[kb "stitzzeager2013" "Exercise 3.3.18, p. 292"]
theorem exer_3_3_18 (x : ℝ) :
    36 * x ^ 4 - 12 * x ^ 3 - 11 * x ^ 2 + 2 * x + 1 = (2 * x - 1) ^ 2 * (3 * x + 1) ^ 2 ∧
      (36 * x ^ 4 - 12 * x ^ 3 - 11 * x ^ 2 + 2 * x + 1 = 0 ↔ x = 1 / 2 ∨ x = -1 / 3) := by
  have e : 36 * x ^ 4 - 12 * x ^ 3 - 11 * x ^ 2 + 2 * x + 1 =
      (2 * x - 1) ^ 2 * (3 * x + 1) ^ 2 := by ring
  have a1 : 2 * x - 1 = 0 ↔ x = 1 / 2 := by constructor <;> intro h <;> linarith
  have a2 : 3 * x + 1 = 0 ↔ x = -1 / 3 := by constructor <;> intro h <;> linarith
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff two_ne_zero, a1, a2]

/-- Stitz-Zeager Exercise 3.3.19: `3x³ + 3x² - 11x - 10 = (x + 2)(3x² - 3x - 5)`, with simple zeros
`-2` and `(3 ± √69)/6`. -/
@[kb "stitzzeager2013" "Exercise 3.3.19, p. 292"]
theorem exer_3_3_19 (x : ℝ) :
    3 * x ^ 3 + 3 * x ^ 2 - 11 * x - 10 = (x + 2) * (3 * x ^ 2 - 3 * x - 5) ∧
      (3 * x ^ 3 + 3 * x ^ 2 - 11 * x - 10 = 0 ↔
        x = -2 ∨ x = (3 - √69) / 6 ∨ x = (3 + √69) / 6) := by
  have e : 3 * x ^ 3 + 3 * x ^ 2 - 11 * x - 10 = (x + 2) * (3 * x ^ 2 - 3 * x - 5) := by ring
  have a1 : x + 2 = 0 ↔ x = -2 := by constructor <;> intro h <;> linarith
  have a2 : 3 * x ^ 2 - 3 * x - 5 = 0 ↔ x = (3 - √69) / 6 ∨ x = (3 + √69) / 6 := by
    have key : 3 * x ^ 2 - 3 * x - 5 = 0 ↔ (6 * x - 3) ^ 2 = 69 := by
      constructor <;> intro h <;> nlinarith
    rw [key, aux_sq_eq_sqrt _ _ (by norm_num)]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, a1, a2]

/-- Stitz-Zeager Exercise 3.3.20: `2x⁴ + x³ - 7x² - 3x + 3 = (x + 1)(2x - 1)(x² - 3)`, with simple
zeros `-1`, `1/2`, `±√3`. -/
@[kb "stitzzeager2013" "Exercise 3.3.20, p. 292"]
theorem exer_3_3_20 (x : ℝ) :
    2 * x ^ 4 + x ^ 3 - 7 * x ^ 2 - 3 * x + 3 = (x + 1) * (2 * x - 1) * (x ^ 2 - 3) ∧
      (2 * x ^ 4 + x ^ 3 - 7 * x ^ 2 - 3 * x + 3 = 0 ↔
        x = -1 ∨ x = 1 / 2 ∨ x = -√3 ∨ x = √3) := by
  have e : 2 * x ^ 4 + x ^ 3 - 7 * x ^ 2 - 3 * x + 3 = (x + 1) * (2 * x - 1) * (x ^ 2 - 3) := by
    ring
  have a1 : x + 1 = 0 ↔ x = -1 := by constructor <;> intro h <;> linarith
  have a2 : 2 * x - 1 = 0 ↔ x = 1 / 2 := by constructor <;> intro h <;> linarith
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, mul_eq_zero, a1, a2, aux_sq_sub x 3 (by norm_num)]
  tauto

/-- Stitz-Zeager Exercise 3.3.21: `9x³ - 5x² - x = x(9x² - 5x - 1)`, with simple zeros `0` and
`(5 ± √61)/18`. -/
@[kb "stitzzeager2013" "Exercise 3.3.21, p. 292"]
theorem exer_3_3_21 (x : ℝ) :
    9 * x ^ 3 - 5 * x ^ 2 - x = 0 ↔ x = 0 ∨ x = (5 - √61) / 18 ∨ x = (5 + √61) / 18 := by
  have e : 9 * x ^ 3 - 5 * x ^ 2 - x = x * (9 * x ^ 2 - 5 * x - 1) := by ring
  have a2 : 9 * x ^ 2 - 5 * x - 1 = 0 ↔ x = (5 - √61) / 18 ∨ x = (5 + √61) / 18 := by
    have key : 9 * x ^ 2 - 5 * x - 1 = 0 ↔ (18 * x - 5) ^ 2 = 61 := by
      constructor <;> intro h <;> nlinarith
    rw [key, aux_sq_eq_sqrt _ _ (by norm_num)]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  rw [e, mul_eq_zero, a2]

/-- Stitz-Zeager Exercise 3.3.22: `6x⁴ - 5x³ - 9x² = x²(6x² - 5x - 9)`, with zero `0` (multiplicity
`2`) and simple zeros `(5 ± √241)/12`. -/
@[kb "stitzzeager2013" "Exercise 3.3.22, p. 292"]
theorem exer_3_3_22 (x : ℝ) :
    6 * x ^ 4 - 5 * x ^ 3 - 9 * x ^ 2 = x ^ 2 * (6 * x ^ 2 - 5 * x - 9) ∧
      (6 * x ^ 4 - 5 * x ^ 3 - 9 * x ^ 2 = 0 ↔
        x = 0 ∨ x = (5 - √241) / 12 ∨ x = (5 + √241) / 12) := by
  have e : 6 * x ^ 4 - 5 * x ^ 3 - 9 * x ^ 2 = x ^ 2 * (6 * x ^ 2 - 5 * x - 9) := by ring
  have a2 : 6 * x ^ 2 - 5 * x - 9 = 0 ↔ x = (5 - √241) / 12 ∨ x = (5 + √241) / 12 := by
    have key : 6 * x ^ 2 - 5 * x - 9 = 0 ↔ (12 * x - 5) ^ 2 = 241 := by
      constructor <;> intro h <;> nlinarith
    rw [key, aux_sq_eq_sqrt _ _ (by norm_num)]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, pow_eq_zero_iff two_ne_zero, a2]

/-- Stitz-Zeager Exercise 3.3.23-26: the real zeros of `x⁴ + 2x² - 15` are `±√3`; of `x⁴ - 9x² + 14`
are `±√2`, `±√7`; of `3x⁴ - 14x² - 5` are `±√5`; of `2x⁴ - 7x² + 6` are `±√2`, `±√6/2`. -/
@[kb "stitzzeager2013" "Exercise 3.3.23, p. 292"]
theorem exer_3_3_23 (x : ℝ) :
    (x ^ 4 + 2 * x ^ 2 - 15 = 0 ↔ x = -√3 ∨ x = √3) ∧
    (x ^ 4 - 9 * x ^ 2 + 14 = 0 ↔ x = -√2 ∨ x = √2 ∨ x = -√7 ∨ x = √7) ∧
    (3 * x ^ 4 - 14 * x ^ 2 - 5 = 0 ↔ x = -√5 ∨ x = √5) ∧
    (2 * x ^ 4 - 7 * x ^ 2 + 6 = 0 ↔ x = -√2 ∨ x = √2 ∨ x = -(√6 / 2) ∨ x = √6 / 2) := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have h6 := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have h6' := Real.sqrt_nonneg 6
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : x ^ 4 + 2 * x ^ 2 - 15 = (x ^ 2 + 5) * (x ^ 2 - 3) := by ring
    rw [e, mul_eq_zero, aux_sq_sub x 3 (by norm_num)]
    constructor
    · rintro (h | h)
      · exfalso; linarith
      · exact h
    · intro h; right; exact h
  · have e : x ^ 4 - 9 * x ^ 2 + 14 = (x ^ 2 - 2) * (x ^ 2 - 7) := by ring
    rw [e, mul_eq_zero, aux_sq_sub x 2 (by norm_num), aux_sq_sub x 7 (by norm_num)]
    simp only [or_assoc]
  · have e : 3 * x ^ 4 - 14 * x ^ 2 - 5 = (3 * x ^ 2 + 1) * (x ^ 2 - 5) := by ring
    rw [e, mul_eq_zero, aux_sq_sub x 5 (by norm_num)]
    constructor
    · rintro (h | h)
      · exfalso; linarith
      · exact h
    · intro h; right; exact h
  · have e : 2 * x ^ 4 - 7 * x ^ 2 + 6 = (2 * x ^ 2 - 3) * (x ^ 2 - 2) := by ring
    have a1 : 2 * x ^ 2 - 3 = 0 ↔ x = -(√6 / 2) ∨ x = √6 / 2 := by
      have key : 2 * x ^ 2 - 3 = 0 ↔ (2 * x) ^ 2 = 6 := by
        constructor <;> intro h <;> nlinarith
      rw [key, aux_sq_eq_sqrt _ _ (by norm_num)]
      constructor
      · rintro (h | h)
        · right; linarith
        · left; linarith
      · rintro (h | h)
        · right; linarith
        · left; linarith
    rw [e, mul_eq_zero, a1, aux_sq_sub x 2 (by norm_num)]
    tauto

/-- Stitz-Zeager Exercise 3.3.29-30: `x⁵ - 2x⁴ - 4x + 8 = (x - 2)(x² - 2)(x² + 2)` has real zeros
`2`, `±√2`; `2x⁵ + 3x⁴ - 18x - 27 = (2x + 3)(x² - 3)(x² + 3)` has real zeros `-3/2`, `±√3`. -/
@[kb "stitzzeager2013" "Exercise 3.3.29, p. 292"]
theorem exer_3_3_29 (x : ℝ) :
    (x ^ 5 - 2 * x ^ 4 - 4 * x + 8 = 0 ↔ x = 2 ∨ x = -√2 ∨ x = √2) ∧
    (2 * x ^ 5 + 3 * x ^ 4 - 18 * x - 27 = 0 ↔ x = -3 / 2 ∨ x = -√3 ∨ x = √3) := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  constructor
  · have e : x ^ 5 - 2 * x ^ 4 - 4 * x + 8 = (x - 2) * (x ^ 2 - 2) * (x ^ 2 + 2) := by ring
    rw [e, mul_eq_zero, mul_eq_zero, sub_eq_zero, aux_sq_sub x 2 (by norm_num)]
    constructor
    · rintro ((h | h) | h)
      · left; exact h
      · right; exact h
      · exfalso; linarith
    · rintro (h | h)
      · left; left; exact h
      · left; right; exact h
  · have e : 2 * x ^ 5 + 3 * x ^ 4 - 18 * x - 27 = (2 * x + 3) * (x ^ 2 - 3) * (x ^ 2 + 3) := by
      ring
    have a1 : 2 * x + 3 = 0 ↔ x = -3 / 2 := by constructor <;> intro h <;> linarith
    rw [e, mul_eq_zero, mul_eq_zero, a1, aux_sq_sub x 3 (by norm_num)]
    constructor
    · rintro ((h | h) | h)
      · left; exact h
      · right; exact h
      · exfalso; linarith
    · rintro (h | h)
      · left; left; exact h
      · left; right; exact h

/-- Stitz-Zeager Exercise 3.3.31: `x⁵ - 60x³ - 80x² + 960x + 2304 = (x + 4)³(x - 6)²`, so `-4` has
multiplicity `3` and `6` has multiplicity `2`. -/
@[kb "stitzzeager2013" "Exercise 3.3.31, p. 293"]
theorem exer_3_3_31 (f : ℝ[X]) (hf : f = X ^ 5 - 60 * X ^ 3 - 80 * X ^ 2 + 960 * X + 2304) :
    f.rootMultiplicity (-4) = 3 ∧ f.rootMultiplicity 6 = 2 ∧
      ∀ x : ℝ, f.eval x = 0 ↔ x = -4 ∨ x = 6 := by
  have e : f = (X + 4) ^ 3 * (X - 6) ^ 2 := by rw [hf]; ring
  refine ⟨aux_rm' _ ((X - 6) ^ 2) (-4) 3 ?_ (by simp; norm_num),
    aux_rm' _ ((X + 4) ^ 3) 6 2 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [e]; simp only [map_neg, map_ofNat]; ring
  · rw [e]; simp only [map_ofNat]
  · rw [e]; simp [sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.3.32: `25x⁵ - 105x⁴ + 174x³ - 142x² + 57x - 9 = (5x - 3)²(x - 1)³`,
with zeros `3/5` (multiplicity `2`) and `1` (multiplicity `3`). -/
@[kb "stitzzeager2013" "Exercise 3.3.32, p. 293"]
theorem exer_3_3_32 (x : ℝ) :
    25 * x ^ 5 - 105 * x ^ 4 + 174 * x ^ 3 - 142 * x ^ 2 + 57 * x - 9 =
        (5 * x - 3) ^ 2 * (x - 1) ^ 3 ∧
      (25 * x ^ 5 - 105 * x ^ 4 + 174 * x ^ 3 - 142 * x ^ 2 + 57 * x - 9 = 0 ↔
        x = 3 / 5 ∨ x = 1) := by
  have e : 25 * x ^ 5 - 105 * x ^ 4 + 174 * x ^ 3 - 142 * x ^ 2 + 57 * x - 9 =
      (5 * x - 3) ^ 2 * (x - 1) ^ 3 := by ring
  have a1 : 5 * x - 3 = 0 ↔ x = 3 / 5 := by constructor <;> intro h <;> linarith
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff three_ne_zero, a1, sub_eq_zero]

/-- Stitz-Zeager Exercise 3.3.33: `90x⁴ - 399x³ + 622x² - 399x + 90 = (2x - 3)(3x - 2)(3x - 5)(5x - 3)`,
with simple zeros `2/3`, `3/2`, `3/5`, `5/3`. -/
@[kb "stitzzeager2013" "Exercise 3.3.33, p. 293"]
theorem exer_3_3_33 (x : ℝ) :
    90 * x ^ 4 - 399 * x ^ 3 + 622 * x ^ 2 - 399 * x + 90 =
        (2 * x - 3) * (3 * x - 2) * (3 * x - 5) * (5 * x - 3) ∧
      (90 * x ^ 4 - 399 * x ^ 3 + 622 * x ^ 2 - 399 * x + 90 = 0 ↔
        x = 3 / 2 ∨ x = 2 / 3 ∨ x = 5 / 3 ∨ x = 3 / 5) := by
  have e : 90 * x ^ 4 - 399 * x ^ 3 + 622 * x ^ 2 - 399 * x + 90 =
      (2 * x - 3) * (3 * x - 2) * (3 * x - 5) * (5 * x - 3) := by ring
  have a1 : 2 * x - 3 = 0 ↔ x = 3 / 2 := by constructor <;> intro h <;> linarith
  have a2 : 3 * x - 2 = 0 ↔ x = 2 / 3 := by constructor <;> intro h <;> linarith
  have a3 : 3 * x - 5 = 0 ↔ x = 5 / 3 := by constructor <;> intro h <;> linarith
  have a4 : 5 * x - 3 = 0 ↔ x = 3 / 5 := by constructor <;> intro h <;> linarith
  refine ⟨e, ?_⟩
  rw [e, mul_eq_zero, mul_eq_zero, mul_eq_zero, a1, a2, a3, a4]
  simp only [or_assoc]

/-- Stitz-Zeager Exercise 3.3.34: `72 f(x) = 72x³ - 6x² - 7x + 1` for `f(x) = x³ - x²/12 - 7x/72 + 1/72`,
and both have exactly the zeros `-1/3`, `1/6`, `1/4`. -/
@[kb "stitzzeager2013" "Exercise 3.3.34, p. 293"]
theorem exer_3_3_34 (x : ℝ) :
    72 * (x ^ 3 - 1 / 12 * x ^ 2 - 7 / 72 * x + 1 / 72) = 72 * x ^ 3 - 6 * x ^ 2 - 7 * x + 1 ∧
      (x ^ 3 - 1 / 12 * x ^ 2 - 7 / 72 * x + 1 / 72 = 0 ↔ x = -1 / 3 ∨ x = 1 / 6 ∨ x = 1 / 4) ∧
      (72 * x ^ 3 - 6 * x ^ 2 - 7 * x + 1 = 0 ↔ x = -1 / 3 ∨ x = 1 / 6 ∨ x = 1 / 4) := by
  have e : 72 * x ^ 3 - 6 * x ^ 2 - 7 * x + 1 = (3 * x + 1) * (6 * x - 1) * (4 * x - 1) := by ring
  have a1 : 3 * x + 1 = 0 ↔ x = -1 / 3 := by constructor <;> intro h <;> linarith
  have a2 : 6 * x - 1 = 0 ↔ x = 1 / 6 := by constructor <;> intro h <;> linarith
  have a3 : 4 * x - 1 = 0 ↔ x = 1 / 4 := by constructor <;> intro h <;> linarith
  have hq : 72 * x ^ 3 - 6 * x ^ 2 - 7 * x + 1 = 0 ↔ x = -1 / 3 ∨ x = 1 / 6 ∨ x = 1 / 4 := by
    rw [e, mul_eq_zero, mul_eq_zero, a1, a2, a3]; simp only [or_assoc]
  refine ⟨by ring, ?_, hq⟩
  rw [← hq]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 3.3.45: `-2x³ + 19x² - 49x + 20 > 0` has solution set
`(-∞, 1/2) ∪ (4, 5)`. -/
@[kb "stitzzeager2013" "Exercise 3.3.45, p. 293"]
theorem exer_3_3_45 :
    {x : ℝ | 0 < -2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20} = Set.Iio (1 / 2) ∪ Set.Ioo 4 5 := by
  ext x
  have e : 0 < -2 * x ^ 3 + 19 * x ^ 2 - 49 * x + 20 ↔ (x - 1 / 2) * (x - 4) * (x - 5) < 0 := by
    constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioo, e]
  exact aux3_neg _ _ _ _ (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 3.3.46: `x⁴ - 9x² ≤ 4x - 12` has solution set `{-2} ∪ [1, 3]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.46, p. 293"]
theorem exer_3_3_46 : {x : ℝ | x ^ 4 - 9 * x ^ 2 ≤ 4 * x - 12} = {-2} ∪ Set.Icc 1 3 := by
  ext x
  have q := aux_nonpos 1 3 x (by norm_num)
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · intro h
    by_cases hx : x = -2
    · left; exact hx
    · right
      have hp : 0 < (x + 2) ^ 2 := by
        have : x + 2 ≠ 0 := fun h0 => hx (by linarith)
        positivity
      apply q.1
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hp hc]
  · rintro (h | h)
    · rw [h]; norm_num
    · have := q.2 h
      nlinarith [mul_nonneg (sq_nonneg (x + 2)) (neg_nonneg.2 this)]

/-- Stitz-Zeager Exercise 3.3.47: `(x - 1)² ≥ 4` has solution set `(-∞, -1] ∪ [3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 3.3.47, p. 293"]
theorem exer_3_3_47 : {x : ℝ | 4 ≤ (x - 1) ^ 2} = Set.Iic (-1) ∪ Set.Ici 3 := by
  ext x
  have e : 4 ≤ (x - 1) ^ 2 ↔ 0 ≤ (x - (-1)) * (x - 3) := by
    constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, e]
  exact aux_nonneg _ _ _ (by norm_num)

/-- Stitz-Zeager Exercise 3.3.49: `x⁴ ≤ 16 + 4x - x³` has solution set `[-2, 2]`. -/
@[kb "stitzzeager2013" "Exercise 3.3.49, p. 293"]
theorem exer_3_3_49 : {x : ℝ | x ^ 4 ≤ 16 + 4 * x - x ^ 3} = Set.Icc (-2) 2 := by
  ext x
  have q : 0 < x ^ 2 + x + 4 := by nlinarith [sq_nonneg (x + 1 / 2)]
  have e : x ^ 4 ≤ 16 + 4 * x - x ^ 3 ↔ (x - (-2)) * (x - 2) ≤ 0 := by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hc q]
    · intro h
      nlinarith [mul_nonneg (neg_nonneg.2 h) q.le]
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, e]
  exact aux_nonpos _ _ _ (by norm_num)

/-- Stitz-Zeager Exercise 3.3.51: `(x³ + 2x²)/2 < x + 2` has solution set
`(-∞, -2) ∪ (-√2, √2)`. -/
@[kb "stitzzeager2013" "Exercise 3.3.51, p. 293"]
theorem exer_3_3_51 :
    {x : ℝ | (x ^ 3 + 2 * x ^ 2) / 2 < x + 2} = Set.Iio (-2) ∪ Set.Ioo (-√2) (√2) := by
  ext x
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have hle : √2 ≤ 2 := by nlinarith
  have key : (x - (-2)) * (x - (-√2)) * (x - √2) = x ^ 3 + 2 * x ^ 2 - 2 * x - 4 := by
    linear_combination (-(x + 2)) * h2
  have e : (x ^ 3 + 2 * x ^ 2) / 2 < x + 2 ↔ (x - (-2)) * (x - (-√2)) * (x - √2) < 0 := by
    rw [key]; constructor <;> intro h <;> linarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioo, e]
  exact aux3_neg _ _ _ _ (by linarith) (by linarith)

/-- Stitz-Zeager Exercise 3.3.52: `(x³ + 20x)/8 ≥ x² + 2` has solution set `{2} ∪ [4, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 3.3.52, p. 293"]
theorem exer_3_3_52 : {x : ℝ | x ^ 2 + 2 ≤ (x ^ 3 + 20 * x) / 8} = {2} ∪ Set.Ici 4 := by
  ext x
  have e : x ^ 2 + 2 ≤ (x ^ 3 + 20 * x) / 8 ↔ ¬ ((x - 2) * (x - 2) * (x - 4) < 0) := by
    rw [not_lt]; constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici, e,
    aux3_neg 2 2 4 x le_rfl (by norm_num)]
  constructor
  · intro h
    push Not at h
    obtain ⟨a, b⟩ := h
    by_cases c : x = 2
    · left; exact c
    · right; exact b (lt_of_le_of_ne a (Ne.symm c))
  · rintro (h | h) hh
    · rw [h] at hh; norm_num at hh
    · rcases hh with hh | ⟨_, hh⟩ <;> linarith

/-- Stitz-Zeager Exercise 3.3.53: `2x⁴ > 5x² + 3` has solution set `(-∞, -√3) ∪ (√3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 3.3.53, p. 293"]
theorem exer_3_3_53 :
    {x : ℝ | 5 * x ^ 2 + 3 < 2 * x ^ 4} = Set.Iio (-√3) ∪ Set.Ioi (√3) := by
  ext x
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 3
  have e : 5 * x ^ 2 + 3 < 2 * x ^ 4 ↔ 0 < (x - (-√3)) * (x - √3) := by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [mul_nonneg (neg_nonneg.2 hc) (sq_nonneg x)]
    · intro h
      nlinarith [mul_pos h (show 0 < 2 * x ^ 2 + 1 by positivity)]
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, e]
  exact aux_pos _ _ _ (by linarith)

/-- Stitz-Zeager Exercise 3.3.55: for `0 < x < 5`, the box volume `V(x) = 4x³ - 44x² + 120x` is at
least `80` exactly when `1 ≤ x ≤ 5 - √5` (about `2.76`). -/
@[kb "stitzzeager2013" "Exercise 3.3.55, p. 293"]
theorem exer_3_3_55 (x : ℝ) (_ : 0 < x) (hx5 : x < 5) :
    80 ≤ 4 * x ^ 3 - 44 * x ^ 2 + 120 * x ↔ 1 ≤ x ∧ x ≤ 5 - √5 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 := Real.sqrt_nonneg 5
  have hs : x - (5 + √5) < 0 := by linarith
  have hV : 4 * x ^ 3 - 44 * x ^ 2 + 120 * x - 80 =
      4 * ((x - 1) * (x - (5 - √5)) * (x - (5 + √5))) := by
    linear_combination (4 * (x - 1)) * h5
  have q := aux_nonpos 1 (5 - √5) x (by nlinarith)
  rw [← q]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hc (neg_pos.2 hs)]
  · intro h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h hs.le]

/-- Stitz-Zeager Exercise 3.3.54 (ERRATUM: the book prints open intervals; the inequality is
non-strict, so the endpoints belong to the solution set): `x⁶ + x³ ≥ 6` iff
`x ≤ -∛3` or `x ≥ ∛2`. -/
@[kb "stitzzeager2013" "Exercise 3.3.54, p. 293"]
theorem exer_3_3_54 :
    {x : ℝ | 6 ≤ x ^ 6 + x ^ 3} = Set.Iic (-((3 : ℝ) ^ (1 / 3 : ℝ))) ∪ Set.Ici ((2 : ℝ) ^ (1 / 3 : ℝ)) := by
  ext x
  have ha : ((3 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hb : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have mono : ∀ u v : ℝ, u ≤ v ↔ u ^ 3 ≤ v ^ 3 := fun u v =>
    ((Odd.strictMono_pow (by decide : Odd 3)).le_iff_le).symm
  have e : 6 ≤ x ^ 6 + x ^ 3 ↔ 0 ≤ (x ^ 3 - (-3)) * (x ^ 3 - 2) := by
    constructor <;> intro h <;> nlinarith
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, e]
  rw [aux_nonneg _ _ _ (by norm_num), mono x, mono _ x, neg_pow, ha, hb]
  norm_num

end UndergradKB.Precalculus.Course
