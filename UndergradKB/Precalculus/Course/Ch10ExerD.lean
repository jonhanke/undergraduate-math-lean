import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.4 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 10.4 -/

private lemma eq_of_pos_sq'' {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (h : c ^ 2 = a ^ 2) : c = a :=
  (pow_left_inj₀ hc.le ha two_ne_zero).mp h

private lemma eq_of_neg_sq'' {c a : ℝ} (hc : c < 0) (ha : a ≤ 0) (h : c ^ 2 = a ^ 2) : c = a := by
  have := eq_of_pos_sq'' (c := -c) (a := -a) (by linarith) (by linarith) (by simpa using h)
  linarith

private lemma cos_pi12 : cos (π / 12) = (√6 + √2) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h, cos_sub, cos_pi_div_three, cos_pi_div_four, sin_pi_div_three, sin_pi_div_four, h6]; ring

private lemma sin_pi12 : sin (π / 12) = (√6 - √2) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h, sin_sub, cos_pi_div_three, cos_pi_div_four, sin_pi_div_three, sin_pi_div_four, h6]; ring

private lemma sqrt_half_sq (u : ℝ) (hu : 0 ≤ u) : (√u / 2) ^ 2 = u / 4 := by
  rw [div_pow, Real.sq_sqrt hu]; norm_num

/-- Stitz-Zeager Exercise 10.4.1: `sin(3π - 2θ) = -sin(2θ - 3π)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.1, p. 794"]
theorem exer_10_4_1 (θ : ℝ) : sin (3 * π - 2 * θ) = -sin (2 * θ - 3 * π) := by
  rw [← sin_neg]; congr 1; ring

/-- Stitz-Zeager Exercise 10.4.2: `cos(-π/4 - 5t) = cos(5t + π/4)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.2, p. 794"]
theorem exer_10_4_2 (t : ℝ) : cos (-(π / 4) - 5 * t) = cos (5 * t + π / 4) := by
  rw [← cos_neg]; congr 1; ring

/-- Stitz-Zeager Exercise 10.4.3: `tan(-t² + 1) = -tan(t² - 1)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.3, p. 794"]
theorem exer_10_4_3 (t : ℝ) : tan (-t ^ 2 + 1) = -tan (t ^ 2 - 1) := by
  rw [← tan_neg]; congr 1; ring

/-- Stitz-Zeager Exercise 10.4.4: `csc(-θ - 5) = -csc(θ + 5)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.4, p. 794"]
theorem exer_10_4_4 (θ : ℝ) : (sin (-θ - 5))⁻¹ = -(sin (θ + 5))⁻¹ := by
  rw [show -θ - 5 = -(θ + 5) by ring, sin_neg, inv_neg]

/-- Stitz-Zeager Exercise 10.4.5: `sec(-6t) = sec(6t)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.5, p. 794"]
theorem exer_10_4_5 (t : ℝ) : (cos (-(6 * t)))⁻¹ = (cos (6 * t))⁻¹ := by rw [cos_neg]

/-- Stitz-Zeager Exercise 10.4.6: `cot(9 - 7θ) = -cot(7θ - 9)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.6, p. 794"]
theorem exer_10_4_6 (θ : ℝ) :
    cos (9 - 7 * θ) / sin (9 - 7 * θ) = -(cos (7 * θ - 9) / sin (7 * θ - 9)) := by
  rw [show 9 - 7 * θ = -(7 * θ - 9) by ring, cos_neg, sin_neg, div_neg]

/-- Stitz-Zeager Exercise 10.4.7: `cos 75° = (√6 - √2)/4`. -/
@[kb "stitzzeager2013" "Exercise 10.4.7, p. 794"]
theorem exer_10_4_7 : cos (75 * π / 180) = (√6 - √2) / 4 := by
  rw [show 75 * π / 180 = π / 2 - π / 12 by ring, cos_pi_div_two_sub, sin_pi12]

/-- Stitz-Zeager Exercise 10.4.9: `sin 105° = (√6 + √2)/4`. -/
@[kb "stitzzeager2013" "Exercise 10.4.9, p. 794"]
theorem exer_10_4_9 : sin (105 * π / 180) = (√6 + √2) / 4 := by
  rw [show 105 * π / 180 = π / 2 + π / 12 by ring, sin_add, sin_pi_div_two, cos_pi_div_two,
    cos_pi12]; ring

/-- Stitz-Zeager Exercise 10.4.12: `tan 375° = 2 - √3`. -/
@[kb "stitzzeager2013" "Exercise 10.4.12, p. 794"]
theorem exer_10_4_12 : tan (375 * π / 180) = 2 - √3 := by
  have h': 375 * π / 180 = π / 12 + ((2 : ℤ) : ℝ) * π := by push_cast; ring
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hb : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpa : 0 < √2 := by positivity
  have hpb : 0 < √3 := by positivity
  have hne : (√6 + √2) / 4 ≠ 0 := by rw [h6]; positivity
  rw [h', tan_add_int_mul_pi, tan_eq_sin_div_cos, sin_pi12, cos_pi12, div_eq_iff hne, h6]
  linear_combination (√2 / 4) * hb

/-- Stitz-Zeager Exercise 10.4.13: `cos(13π/12) = -(√6 + √2)/4`. -/
@[kb "stitzzeager2013" "Exercise 10.4.13, p. 794"]
theorem exer_10_4_13 : cos (13 * π / 12) = -((√6 + √2) / 4) := by
  rw [show 13 * π / 12 = π / 12 + π by ring, cos_add_pi, cos_pi12]

/-- Stitz-Zeager Exercise 10.4.14: `sin(11π/12) = (√6 - √2)/4`. -/
@[kb "stitzzeager2013" "Exercise 10.4.14, p. 794"]
theorem exer_10_4_14 : sin (11 * π / 12) = (√6 - √2) / 4 := by
  rw [show 11 * π / 12 = π - π / 12 by ring, sin_pi_sub, sin_pi12]

/-- Stitz-Zeager Exercise 10.4.15: `tan(13π/12) = 2 - √3`. -/
@[kb "stitzzeager2013" "Exercise 10.4.15, p. 794"]
theorem exer_10_4_15 : tan (13 * π / 12) = 2 - √3 := by
  have h' : 13 * π / 12 = π / 12 + ((1 : ℤ) : ℝ) * π := by push_cast; ring
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hb : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpa : 0 < √2 := by positivity
  have hpb : 0 < √3 := by positivity
  have hne : (√6 + √2) / 4 ≠ 0 := by rw [h6]; positivity
  rw [h', tan_add_int_mul_pi, tan_eq_sin_div_cos, sin_pi12, cos_pi12, div_eq_iff hne, h6]
  linear_combination (√2 / 4) * hb

/-- Stitz-Zeager Exercise 10.4.16: `cos(7π/12) = (√2 - √6)/4`. -/
@[kb "stitzzeager2013" "Exercise 10.4.16, p. 794"]
theorem exer_10_4_16 : cos (7 * π / 12) = (√2 - √6) / 4 := by
  rw [show 7 * π / 12 = π / 2 + π / 12 by ring, cos_add, cos_pi_div_two, sin_pi_div_two, sin_pi12]
  ring

/-- Stitz-Zeager Exercise 10.4.17: `tan(17π/12) = 2 + √3`. -/
@[kb "stitzzeager2013" "Exercise 10.4.17, p. 794"]
theorem exer_10_4_17 : tan (17 * π / 12) = 2 + √3 := by
  have h' : 17 * π / 12 = (π / 2 - π / 12) + ((1 : ℤ) : ℝ) * π := by push_cast; ring
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hb : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpa : 0 < √2 := by positivity
  have hpb : 0 < √3 := by positivity
  have hne : (√6 - √2) / 4 ≠ 0 := by
    rw [h6]
    have : 1 < √3 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have : 0 < √3 * √2 - √2 := by nlinarith
    exact (div_pos this (by norm_num)).ne'
  rw [h', tan_add_int_mul_pi, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub, sin_pi12,
    cos_pi12, div_eq_iff hne, h6]
  linear_combination (-(√2) / 4) * hb

/-- Stitz-Zeager Exercise 10.4.18: `sin(π/12) = (√6 - √2)/4`. -/
@[kb "stitzzeager2013" "Exercise 10.4.18, p. 794"]
theorem exer_10_4_18 : sin (π / 12) = (√6 - √2) / 4 := sin_pi12

/-- Stitz-Zeager Exercise 10.4.20: `csc(5π/12) = √6 - √2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.20, p. 794"]
theorem exer_10_4_20 : (sin (5 * π / 12))⁻¹ = √6 - √2 := by
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hb : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpa : 0 < √2 := by positivity
  have hpb : 0 < √3 := by positivity
  have ha : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply inv_eq_of_mul_eq_one_right
  rw [show 5 * π / 12 = π / 2 - π / 12 by ring, sin_pi_div_two_sub, cos_pi12, h6]
  linear_combination (√2 ^ 2 / 4) * hb + (1 / 2) * ha

/-- Stitz-Zeager Exercise 10.4.21: `sec(-π/12) = √6 - √2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.21, p. 794"]
theorem exer_10_4_21 : (cos (-(π / 12)))⁻¹ = √6 - √2 := by
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hb : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply inv_eq_of_mul_eq_one_right
  rw [cos_neg, cos_pi12, h6]
  linear_combination (√2 ^ 2 / 4) * hb + (1 / 2) * ha

end UndergradKB.Precalculus.Course
