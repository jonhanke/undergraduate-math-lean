import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers, Section 3.2 -/

namespace UndergradKB.Precalculus.Course

open Polynomial

private lemma aux_div (f g q r : ℝ[X]) (d : ℕ) (hg : g.Monic) (hgd : g.natDegree = d + 1)
    (hr : r.natDegree ≤ d) (h : f = g * q + r) : f /ₘ g = q ∧ f %ₘ g = r :=
  div_modByMonic_unique q r hg ⟨by rw [h]; ring, degree_lt_degree (by omega)⟩

private lemma aux_sq_eq_sqrt (y c : ℝ) (hc : 0 ≤ c) : y ^ 2 = c ↔ y = √c ∨ y = -√c := by
  have h := Real.sq_sqrt hc
  constructor
  · intro hy
    have : (y - √c) * (y + √c) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (h1 | h1) <;> rw [h1] <;> nlinarith

/-! ## Section 3.2 -/

/-- Stitz-Zeager Exercise 3.2.1: dividing `4x² + 3x - 1` by `x - 3` gives quotient `4x + 15` and
remainder `44`. -/
@[kb "stitzzeager2013" "Exercise 3.2.1, p. 277"]
theorem exer_3_2_1 :
    ((4 * X ^ 2 + 3 * X - 1 : ℝ[X]) /ₘ (X - 3) = 4 * X + 15) ∧
    ((4 * X ^ 2 + 3 * X - 1 : ℝ[X]) %ₘ (X - 3) = 44) :=
  aux_div _ _ _ _ 0 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.2: dividing `2x³ - x + 1` by `x² + x + 1` gives quotient `2x - 2`
and remainder `-x + 3`. -/
@[kb "stitzzeager2013" "Exercise 3.2.2, p. 277"]
theorem exer_3_2_2 :
    ((2 * X ^ 3 - X + 1 : ℝ[X]) /ₘ (X ^ 2 + X + 1) = 2 * X - 2) ∧
    ((2 * X ^ 3 - X + 1 : ℝ[X]) %ₘ (X ^ 2 + X + 1) = -X + 3) :=
  aux_div _ _ _ _ 1 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.3: dividing `5x⁴ - 3x³ + 2x² - 1` by `x² + 4` gives quotient
`5x² - 3x - 18` and remainder `12x + 71`. -/
@[kb "stitzzeager2013" "Exercise 3.2.3, p. 277"]
theorem exer_3_2_3 :
    ((5 * X ^ 4 - 3 * X ^ 3 + 2 * X ^ 2 - 1 : ℝ[X]) /ₘ (X ^ 2 + 4) = 5 * X ^ 2 - 3 * X - 18) ∧
    ((5 * X ^ 4 - 3 * X ^ 3 + 2 * X ^ 2 - 1 : ℝ[X]) %ₘ (X ^ 2 + 4) = 12 * X + 71) :=
  aux_div _ _ _ _ 1 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.4: dividing `-x⁵ + 7x³ - x` by `x³ - x² + 1` gives quotient
`-x² - x + 6` and remainder `7x² - 6`. -/
@[kb "stitzzeager2013" "Exercise 3.2.4, p. 277"]
theorem exer_3_2_4 :
    ((-X ^ 5 + 7 * X ^ 3 - X : ℝ[X]) /ₘ (X ^ 3 - X ^ 2 + 1) = -X ^ 2 - X + 6) ∧
    ((-X ^ 5 + 7 * X ^ 3 - X : ℝ[X]) %ₘ (X ^ 3 - X ^ 2 + 1) = 7 * X ^ 2 - 6) :=
  aux_div _ _ _ _ 2 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.6: dividing `4x² - x - 23` by `x² - 1` gives quotient `4` and
remainder `-x - 19`. -/
@[kb "stitzzeager2013" "Exercise 3.2.6, p. 277"]
theorem exer_3_2_6 :
    ((4 * X ^ 2 - X - 23 : ℝ[X]) /ₘ (X ^ 2 - 1) = 4) ∧
    ((4 * X ^ 2 - X - 23 : ℝ[X]) %ₘ (X ^ 2 - 1) = -X - 19) :=
  aux_div _ _ _ _ 1 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.7: dividing `3x² - 2x + 1` by `x - 1` gives quotient `3x + 1` and
remainder `2`. -/
@[kb "stitzzeager2013" "Exercise 3.2.7, p. 277"]
theorem exer_3_2_7 :
    ((3 * X ^ 2 - 2 * X + 1 : ℝ[X]) /ₘ (X - 1) = 3 * X + 1) ∧
    ((3 * X ^ 2 - 2 * X + 1 : ℝ[X]) %ₘ (X - 1) = 2) :=
  aux_div _ _ _ _ 0 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.9: dividing `3 - 4x - 2x²` by `x + 1` gives quotient `-2x - 2` and
remainder `5`. -/
@[kb "stitzzeager2013" "Exercise 3.2.9, p. 277"]
theorem exer_3_2_9 :
    ((3 - 4 * X - 2 * X ^ 2 : ℝ[X]) /ₘ (X + 1) = -2 * X - 2) ∧
    ((3 - 4 * X - 2 * X ^ 2 : ℝ[X]) %ₘ (X + 1) = 5) :=
  aux_div _ _ _ _ 0 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.10: dividing `4x² - 5x + 3` by `x + 3` gives quotient `4x - 17` and
remainder `54`. -/
@[kb "stitzzeager2013" "Exercise 3.2.10, p. 277"]
theorem exer_3_2_10 :
    ((4 * X ^ 2 - 5 * X + 3 : ℝ[X]) /ₘ (X + 3) = 4 * X - 17) ∧
    ((4 * X ^ 2 - 5 * X + 3 : ℝ[X]) %ₘ (X + 3) = 54) :=
  aux_div _ _ _ _ 0 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.11: `x³ + 8` is divisible by `x + 2` with quotient `x² - 2x + 4`. -/
@[kb "stitzzeager2013" "Exercise 3.2.11, p. 277"]
theorem exer_3_2_11 :
    ((X ^ 3 + 8 : ℝ[X]) /ₘ (X + 2) = X ^ 2 - 2 * X + 4) ∧ ((X ^ 3 + 8 : ℝ[X]) %ₘ (X + 2) = 0) :=
  aux_div _ _ _ _ 0 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.12: dividing `4x³ + 2x - 3` by `x - 3` gives quotient
`4x² + 12x + 38` and remainder `111`. -/
@[kb "stitzzeager2013" "Exercise 3.2.12, p. 277"]
theorem exer_3_2_12 :
    ((4 * X ^ 3 + 2 * X - 3 : ℝ[X]) /ₘ (X - 3) = 4 * X ^ 2 + 12 * X + 38) ∧
    ((4 * X ^ 3 + 2 * X - 3 : ℝ[X]) %ₘ (X - 3) = 111) :=
  aux_div _ _ _ _ 0 (by monicity!) (by compute_degree!) (by compute_degree!) (by ring)

/-- Stitz-Zeager Exercise 3.2.13-18: divisions by `x - c` with rational `c`:
`18x² - 15x - 25 = (x - 5/3)(18x + 15)`, `4x² - 1 = (x - 1/2)(4x + 2)`,
`2x³ + x² + 2x + 1 = (x + 1/2)(2x² + 2)`, `3x³ - x + 4 = (x - 2/3)(3x² + 2x + 1/3) + 38/9`,
`2x³ - 3x + 1 = (x - 1/2)(2x² + x - 5/2) - 1/4`,
`4x⁴ - 12x³ + 13x² - 12x + 9 = (x - 3/2)(4x³ - 6x² + 4x - 6)`. -/
@[kb "stitzzeager2013" "Exercise 3.2.13, p. 277"]
theorem exer_3_2_13 (x : ℝ) :
    18 * x ^ 2 - 15 * x - 25 = (x - 5 / 3) * (18 * x + 15) + 0 ∧
    4 * x ^ 2 - 1 = (x - 1 / 2) * (4 * x + 2) + 0 ∧
    2 * x ^ 3 + x ^ 2 + 2 * x + 1 = (x + 1 / 2) * (2 * x ^ 2 + 2) + 0 ∧
    3 * x ^ 3 - x + 4 = (x - 2 / 3) * (3 * x ^ 2 + 2 * x + 1 / 3) + 38 / 9 ∧
    2 * x ^ 3 - 3 * x + 1 = (x - 1 / 2) * (2 * x ^ 2 + x - 5 / 2) - 1 / 4 ∧
    4 * x ^ 4 - 12 * x ^ 3 + 13 * x ^ 2 - 12 * x + 9 =
      (x - 3 / 2) * (4 * x ^ 3 - 6 * x ^ 2 + 4 * x - 6) + 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- Stitz-Zeager Exercise 3.2.19-20: with `r = √3`,
`x⁴ - 6x² + 9 = (x - √3)(x³ + √3x² - 3x - 3√3)`, and with `s = √2`,
`x⁶ - 6x⁴ + 12x² - 8 = (x + √2)(x⁵ - √2x⁴ - 4x³ + 4√2x² + 4x - 4√2)`. -/
@[kb "stitzzeager2013" "Exercise 3.2.19, p. 277"]
theorem exer_3_2_19 (x : ℝ) :
    x ^ 4 - 6 * x ^ 2 + 9 = (x - √3) * (x ^ 3 + √3 * x ^ 2 - 3 * x - 3 * √3) + 0 ∧
    x ^ 6 - 6 * x ^ 4 + 12 * x ^ 2 - 8 =
      (x + √2) * (x ^ 5 - √2 * x ^ 4 - 4 * x ^ 3 + 4 * √2 * x ^ 2 + 4 * x - 4 * √2) + 0 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · linear_combination (x ^ 2 - 3 : ℝ) * h3
  · linear_combination (x ^ 2 - 2) ^ 2 * h2

/-- Stitz-Zeager Exercise 3.2.21-26: remainders `p(4) = 29` for `2x² - x + 1`, `p(-3) = -45` for
`2x³ - x + 6`, `p(-1) = 2` for `x³ + 2x² + 3x + 4`; and the factorizations
`4x² - 33x - 180 = (x - 12)(4x + 15)`, `3x³ - 6x² + 4x - 8 = (x - 2)(3x² + 4)`,
`8x³ + 12x² + 6x + 1 = (x + 1/2)(8x² + 8x + 2)` with `p(12) = p(2) = p(-1/2) = 0`. -/
@[kb "stitzzeager2013" "Exercise 3.2.21, p. 277"]
theorem exer_3_2_21 :
    (2 * 4 ^ 2 - 4 + 1 : ℝ) = 29 ∧ (2 * (-3) ^ 3 - (-3) + 6 : ℝ) = -45 ∧
    ((-1) ^ 3 + 2 * (-1) ^ 2 + 3 * (-1) + 4 : ℝ) = 2 ∧
    (4 * 12 ^ 2 - 33 * 12 - 180 : ℝ) = 0 ∧ (3 * 2 ^ 3 - 6 * 2 ^ 2 + 4 * 2 - 8 : ℝ) = 0 ∧
    (8 * (-1 / 2) ^ 3 + 12 * (-1 / 2) ^ 2 + 6 * (-1 / 2) + 1 : ℝ) = 0 ∧
    (∀ x : ℝ, 4 * x ^ 2 - 33 * x - 180 = (x - 12) * (4 * x + 15)) ∧
    (∀ x : ℝ, 3 * x ^ 3 - 6 * x ^ 2 + 4 * x - 8 = (x - 2) * (3 * x ^ 2 + 4)) ∧
    (∀ x : ℝ, 8 * x ^ 3 + 12 * x ^ 2 + 6 * x + 1 = (x + 1 / 2) * (8 * x ^ 2 + 8 * x + 2)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    fun x => by ring, fun x => by ring, fun x => by ring⟩

/-- Stitz-Zeager Exercise 3.2.30: `x = 2 - √3` is a zero of `x² - 4x + 1`, which factors as
`(x - (2 - √3))(x - (2 + √3))`. -/
@[kb "stitzzeager2013" "Exercise 3.2.30, p. 277"]
theorem exer_3_2_30 (x : ℝ) :
    (2 - √3) ^ 2 - 4 * (2 - √3) + 1 = 0 ∧
      x ^ 2 - 4 * x + 1 = (x - (2 - √3)) * (x - (2 + √3)) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · linear_combination h3
  · linear_combination h3

/-- Stitz-Zeager Exercise 3.2.31: `x³ - 6x² + 11x - 6 = (x-1)(x-2)(x-3)`, with real zeros `1, 2, 3`. -/
@[kb "stitzzeager2013" "Exercise 3.2.31, p. 278"]
theorem exer_3_2_31 (x : ℝ) :
    x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = (x - 1) * (x - 2) * (x - 3) ∧
      (x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3) := by
  have e : x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = (x - 1) * (x - 2) * (x - 3) := by ring
  refine ⟨e, ?_⟩
  rw [e]; simp [sub_eq_zero, or_assoc]

/-- Stitz-Zeager Exercise 3.2.32: `x³ - 24x² + 192x - 512 = (x - 8)³`, with the single zero `8`. -/
@[kb "stitzzeager2013" "Exercise 3.2.32, p. 278"]
theorem exer_3_2_32 (x : ℝ) :
    x ^ 3 - 24 * x ^ 2 + 192 * x - 512 = (x - 8) ^ 3 ∧
      (x ^ 3 - 24 * x ^ 2 + 192 * x - 512 = 0 ↔ x = 8) := by
  have e : x ^ 3 - 24 * x ^ 2 + 192 * x - 512 = (x - 8) ^ 3 := by ring
  refine ⟨e, ?_⟩
  rw [e]; simp [sub_eq_zero]

/-- Stitz-Zeager Exercise 3.2.33: `3x³ + 4x² - x - 2 = 3(x - 2/3)(x + 1)²`, with zeros `2/3`, `-1`. -/
@[kb "stitzzeager2013" "Exercise 3.2.33, p. 278"]
theorem exer_3_2_33 (x : ℝ) :
    3 * x ^ 3 + 4 * x ^ 2 - x - 2 = 3 * (x - 2 / 3) * (x + 1) ^ 2 ∧
      (3 * x ^ 3 + 4 * x ^ 2 - x - 2 = 0 ↔ x = 2 / 3 ∨ x = -1) := by
  have e : 3 * x ^ 3 + 4 * x ^ 2 - x - 2 = 3 * (x - 2 / 3) * (x + 1) ^ 2 := by ring
  refine ⟨e, ?_⟩
  rw [e]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · norm_num at h
      · left; linarith
    · right; have := pow_eq_zero_iff (two_ne_zero) |>.1 h; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 3.2.34: `2x³ - 3x² - 11x + 6 = 2(x - 1/2)(x + 2)(x - 3)`, with zeros
`1/2`, `-2`, `3`. -/
@[kb "stitzzeager2013" "Exercise 3.2.34, p. 278"]
theorem exer_3_2_34 (x : ℝ) :
    2 * x ^ 3 - 3 * x ^ 2 - 11 * x + 6 = 2 * (x - 1 / 2) * (x + 2) * (x - 3) ∧
      (2 * x ^ 3 - 3 * x ^ 2 - 11 * x + 6 = 0 ↔ x = 1 / 2 ∨ x = -2 ∨ x = 3) := by
  have e : 2 * x ^ 3 - 3 * x ^ 2 - 11 * x + 6 = 2 * (x - 1 / 2) * (x + 2) * (x - 3) := by ring
  refine ⟨e, ?_⟩
  rw [e]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · norm_num at h
        · left; linarith
      · right; left; linarith
    · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 3.2.35: `x³ + 2x² - 3x - 6 = (x + 2)(x + √3)(x - √3)`, with real zeros
`-2`, `±√3`. -/
@[kb "stitzzeager2013" "Exercise 3.2.35, p. 278"]
theorem exer_3_2_35 (x : ℝ) :
    x ^ 3 + 2 * x ^ 2 - 3 * x - 6 = (x + 2) * (x + √3) * (x - √3) ∧
      (x ^ 3 + 2 * x ^ 2 - 3 * x - 6 = 0 ↔ x = -2 ∨ x = -√3 ∨ x = √3) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : x ^ 3 + 2 * x ^ 2 - 3 * x - 6 = (x + 2) * (x + √3) * (x - √3) := by
    linear_combination (x + 2) * h3
  refine ⟨e, ?_⟩
  rw [e]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · left; linarith
      · right; left; linarith
    · right; right; linarith
  · rintro (rfl | rfl | rfl)
    · norm_num
    · ring
    · ring

/-- Stitz-Zeager Exercise 3.2.36: `2x³ - x² - 10x + 5 = 2(x - 1/2)(x + √5)(x - √5)`, with real
zeros `1/2`, `±√5`. -/
@[kb "stitzzeager2013" "Exercise 3.2.36, p. 278"]
theorem exer_3_2_36 (x : ℝ) :
    2 * x ^ 3 - x ^ 2 - 10 * x + 5 = 2 * (x - 1 / 2) * (x + √5) * (x - √5) ∧
      (2 * x ^ 3 - x ^ 2 - 10 * x + 5 = 0 ↔ x = 1 / 2 ∨ x = -√5 ∨ x = √5) := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have e : 2 * x ^ 3 - x ^ 2 - 10 * x + 5 = 2 * (x - 1 / 2) * (x + √5) * (x - √5) := by
    linear_combination (2 * x - 1) * h5
  refine ⟨e, ?_⟩
  rw [e]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · norm_num at h
        · left; linarith
      · right; left; linarith
    · right; right; linarith
  · rintro (rfl | rfl | rfl)
    · norm_num
    · ring
    · ring

/-- Stitz-Zeager Exercise 3.2.37: `4x⁴ - 4x³ + 13x² - 12x + 3 = 4(x - 1/2)²(x² + 3)`, so `1/2` is
the only real zero. -/
@[kb "stitzzeager2013" "Exercise 3.2.37, p. 278"]
theorem exer_3_2_37 (x : ℝ) :
    4 * x ^ 4 - 4 * x ^ 3 + 13 * x ^ 2 - 12 * x + 3 = 4 * (x - 1 / 2) ^ 2 * (x ^ 2 + 3) ∧
      (4 * x ^ 4 - 4 * x ^ 3 + 13 * x ^ 2 - 12 * x + 3 = 0 ↔ x = 1 / 2) := by
  have e : 4 * x ^ 4 - 4 * x ^ 3 + 13 * x ^ 2 - 12 * x + 3 = 4 * (x - 1 / 2) ^ 2 * (x ^ 2 + 3) := by
    ring
  refine ⟨e, ?_⟩
  rw [e]
  constructor
  · intro h
    have h3 : 0 < x ^ 2 + 3 := by positivity
    rcases mul_eq_zero.1 h with h | h
    · have : (x - 1 / 2) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this; linarith
    · linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 3.2.38: `x⁵ + 2x⁴ - 12x³ - 38x² - 37x - 12 = (x+1)³(x+3)(x-4)`. -/
@[kb "stitzzeager2013" "Exercise 3.2.38, p. 278"]
theorem exer_3_2_38 (x : ℝ) :
    x ^ 5 + 2 * x ^ 4 - 12 * x ^ 3 - 38 * x ^ 2 - 37 * x - 12 = (x + 1) ^ 3 * (x + 3) * (x - 4) ∧
      (x ^ 5 + 2 * x ^ 4 - 12 * x ^ 3 - 38 * x ^ 2 - 37 * x - 12 = 0 ↔ x = -1 ∨ x = -3 ∨ x = 4) := by
  have e : x ^ 5 + 2 * x ^ 4 - 12 * x ^ 3 - 38 * x ^ 2 - 37 * x - 12 =
      (x + 1) ^ 3 * (x + 3) * (x - 4) := by ring
  refine ⟨e, ?_⟩
  rw [e]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · left; have := pow_eq_zero_iff (three_ne_zero) |>.1 h; linarith
      · right; left; linarith
    · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 3.2.40: `x² - 2x - 2 = (x - (1 - √3))(x - (1 + √3))`. -/
@[kb "stitzzeager2013" "Exercise 3.2.40, p. 278"]
theorem exer_3_2_40 (x : ℝ) :
    x ^ 2 - 2 * x - 2 = (x - (1 - √3)) * (x - (1 + √3)) ∧
      (x ^ 2 - 2 * x - 2 = 0 ↔ x = 1 - √3 ∨ x = 1 + √3) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : x ^ 2 - 2 * x - 2 = (x - (1 - √3)) * (x - (1 + √3)) := by linear_combination h3
  refine ⟨e, ?_⟩
  rw [e]
  simp [sub_eq_zero]

/-- Stitz-Zeager Exercise 3.2.41: `p(x) = 117(x+2)(x-2)(x+1)(x-1) = 117x⁴ - 585x² + 468` has zeros
`±2`, `±1` and leading term `117x⁴`. -/
@[kb "stitzzeager2013" "Exercise 3.2.41, p. 278"]
theorem exer_3_2_41 (x : ℝ) :
    117 * (x + 2) * (x - 2) * (x + 1) * (x - 1) = 117 * x ^ 4 - 585 * x ^ 2 + 468 ∧
      (117 * (x + 2) * (x - 2) * (x + 1) * (x - 1) = 0 ↔ x = -2 ∨ x = 2 ∨ x = -1 ∨ x = 1) := by
  refine ⟨by ring, ?_⟩
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · norm_num at h
          · left; linarith
        · right; left; linarith
      · right; right; left; linarith
    · right; right; right; linarith
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 3.2.46: `5x² - 6x - 4` has real zeros `(3 ± √29)/5`. -/
@[kb "stitzzeager2013" "Exercise 3.2.46, p. 278"]
theorem exer_3_2_46 (x : ℝ) :
    5 * x ^ 2 - 6 * x - 4 = 0 ↔ x = (3 - √29) / 5 ∨ x = (3 + √29) / 5 := by
  have key : 5 * x ^ 2 - 6 * x - 4 = 0 ↔ (5 * x - 3) ^ 2 = 29 := by
    constructor <;> intro h <;> nlinarith
  rw [key, aux_sq_eq_sqrt _ _ (by norm_num)]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

end UndergradKB.Precalculus.Course
