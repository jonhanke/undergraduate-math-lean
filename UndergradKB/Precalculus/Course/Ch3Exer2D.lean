import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Polynomials

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 3.4,
complex arithmetic -/

namespace UndergradKB.Precalculus.Course

open Complex ComplexConjugate

private lemma w7d_sqrt_neg (c : ℝ) (hc : 0 ≤ c) :
    (-(c : ℂ)) ^ (1 / 2 : ℂ) = I * (Real.sqrt c : ℝ) :=
  (imaginary_unit_sq_and_sqrt_neg c hc).2

private lemma w7d_sqrt_sq (a b : ℝ) (ha : 0 ≤ a) (hb : a = b ^ 2) (hb0 : 0 ≤ b) :
    Real.sqrt a = b := by
  rw [hb]; exact Real.sqrt_sq hb0

set_option hygiene false in
/-- Close a goal of complex arithmetic in `s` and `I` once `hs : s ^ 2 = _` and `hs4 : s ^ 4 = _`
are in the context. -/
local macro "w7alg" : tactic =>
  `(tactic| (ring_nf; try simp only [hs, hs4, I_sq, I_pow_four]; ring_nf))

set_option linter.unusedSimpArgs false

/-! ## Section 3.4 -/

/-- Stitz-Zeager Exercise 3.4.2: for `z = 1 + i`, `w = -i`: `z + w = 1`, `zw = 1 - i`, `z² = 2i`,
`1/z = 1/2 - i/2`, `z/w = -1 + i`, `w/z = -1/2 - i/2`, `z̄ = 1 - i`, `z z̄ = 2`, `(z̄)² = -2i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.2, p. 307"]
theorem exer_3_4_2 :
    let z : ℂ := 1 + I
    let w : ℂ := -I
    z + w = 1 ∧ z * w = 1 - I ∧ z ^ 2 = 2 * I ∧ 1 / z = 1 / 2 - 1 / 2 * I ∧
    z / w = -1 + I ∧ w / z = -1 / 2 - 1 / 2 * I ∧ conj z = 1 - I ∧ z * conj z = 2 ∧
    conj z ^ 2 = -2 * I := by
  intro z w
  simp only [z, w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, pow_two] <;> norm_num

/-- Stitz-Zeager Exercise 3.4.4: for `z = 4i`, `w = 2 - 2i`: `z + w = 2 + 2i`, `zw = 8 + 8i`,
`z² = -16`, `1/z = -i/4`, `z/w = -1 + i`, `w/z = -1/2 - i/2`, `z̄ = -4i`, `z z̄ = 16`, `(z̄)² = -16`. -/
@[kb "stitzzeager2013" "Exercise 3.4.4, p. 307"]
theorem exer_3_4_4 :
    let z : ℂ := 4 * I
    let w : ℂ := 2 - 2 * I
    z + w = 2 + 2 * I ∧ z * w = 8 + 8 * I ∧ z ^ 2 = -16 ∧ 1 / z = -(1 / 4) * I ∧
    z / w = -1 + I ∧ w / z = -1 / 2 - 1 / 2 * I ∧ conj z = -4 * I ∧ z * conj z = 16 ∧
    conj z ^ 2 = -16 := by
  intro z w
  simp only [z, w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, pow_two] <;> norm_num

/-- Stitz-Zeager Exercise 3.4.6: for `z = -5 + i`, `w = 4 + 2i`: `z + w = -1 + 3i`, `zw = -22 - 6i`,
`z² = 24 - 10i`, `1/z = -5/26 - i/26`, `z/w = -9/10 + 7i/10`, `w/z = -9/13 - 7i/13`, `z̄ = -5 - i`,
`z z̄ = 26`, `(z̄)² = 24 + 10i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.6, p. 307"]
theorem exer_3_4_6 :
    let z : ℂ := -5 + I
    let w : ℂ := 4 + 2 * I
    z + w = -1 + 3 * I ∧ z * w = -22 - 6 * I ∧ z ^ 2 = 24 - 10 * I ∧
    1 / z = -5 / 26 - 1 / 26 * I ∧ z / w = -9 / 10 + 7 / 10 * I ∧
    w / z = -9 / 13 - 7 / 13 * I ∧ conj z = -5 - I ∧ z * conj z = 26 ∧
    conj z ^ 2 = 24 + 10 * I := by
  intro z w
  simp only [z, w]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq, pow_two] <;> norm_num

/-- Stitz-Zeager Exercise 3.4.11: `√(-49) = 7i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.11, p. 307"]
theorem exer_3_4_11 : (-49 : ℂ) ^ (1 / 2 : ℂ) = 7 * I := by
  have h := w7d_sqrt_neg 49 (by norm_num)
  have h7 : Real.sqrt 49 = 7 := w7d_sqrt_sq 49 7 (by norm_num) (by norm_num) (by norm_num)
  rw [h7] at h
  push_cast at h
  rw [h]; ring

/-- Stitz-Zeager Exercise 3.4.12: `√(-9) = 3i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.12, p. 307"]
theorem exer_3_4_12 : (-9 : ℂ) ^ (1 / 2 : ℂ) = 3 * I := by
  have h := w7d_sqrt_neg 9 (by norm_num)
  have h7 : Real.sqrt 9 = 3 := w7d_sqrt_sq 9 3 (by norm_num) (by norm_num) (by norm_num)
  rw [h7] at h
  push_cast at h
  rw [h]; ring

/-- Stitz-Zeager Exercise 3.4.14: `√((-25)(-4)) = √100 = 10`, which differs from `√(-25) · √(-4) = -10`. -/
@[kb "stitzzeager2013" "Exercise 3.4.14, p. 307"]
theorem exer_3_4_14 :
    Real.sqrt ((-25) * (-4)) = 10 ∧ (-25 : ℂ) ^ (1 / 2 : ℂ) * (-4 : ℂ) ^ (1 / 2 : ℂ) = -10 := by
  have h25 := w7d_sqrt_neg 25 (by norm_num)
  have h4 := w7d_sqrt_neg 4 (by norm_num)
  have e25 : Real.sqrt 25 = 5 := w7d_sqrt_sq 25 5 (by norm_num) (by norm_num) (by norm_num)
  have e4 : Real.sqrt 4 = 2 := w7d_sqrt_sq 4 2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [show ((-25 : ℝ) * (-4)) = 100 by norm_num]
    exact w7d_sqrt_sq 100 10 (by norm_num) (by norm_num) (by norm_num)
  · rw [e25] at h25; rw [e4] at h4
    push_cast at h25 h4
    rw [h25, h4]
    linear_combination (10 : ℂ) * I_sq

/-- Stitz-Zeager Exercise 3.4.15: `√(-9) · √(-16) = 3i · 4i = -12`. -/
@[kb "stitzzeager2013" "Exercise 3.4.15, p. 307"]
theorem exer_3_4_15 : (-9 : ℂ) ^ (1 / 2 : ℂ) * (-16 : ℂ) ^ (1 / 2 : ℂ) = -12 := by
  have h9 := w7d_sqrt_neg 9 (by norm_num)
  have h16 := w7d_sqrt_neg 16 (by norm_num)
  have e9 : Real.sqrt 9 = 3 := w7d_sqrt_sq 9 3 (by norm_num) (by norm_num) (by norm_num)
  have e16 : Real.sqrt 16 = 4 := w7d_sqrt_sq 16 4 (by norm_num) (by norm_num) (by norm_num)
  rw [e9] at h9; rw [e16] at h16
  push_cast at h9 h16
  rw [h9, h16]
  linear_combination (12 : ℂ) * I_sq

/-- Stitz-Zeager Exercise 3.4.16: `√((-9)(-16)) = √144 = 12`. -/
@[kb "stitzzeager2013" "Exercise 3.4.16, p. 307"]
theorem exer_3_4_16 : Real.sqrt ((-9) * (-16)) = 12 := by
  rw [show ((-9 : ℝ) * (-16)) = 144 by norm_num]
  exact w7d_sqrt_sq 144 12 (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 3.4.17: `√(-(-9)) = √9 = 3`. -/
@[kb "stitzzeager2013" "Exercise 3.4.17, p. 307"]
theorem exer_3_4_17 : Real.sqrt (-(-9)) = 3 := by
  rw [show (-(-9 : ℝ)) = 9 by norm_num]
  exact w7d_sqrt_sq 9 3 (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 3.4.18: `-√(-9) = -3i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.18, p. 307"]
theorem exer_3_4_18 : -((-9 : ℂ) ^ (1 / 2 : ℂ)) = -3 * I := by
  rw [exer_3_4_12]; ring

/-- Stitz-Zeager Exercise 3.4.19: `i⁵ = i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.19, p. 307"]
theorem exer_3_4_19 : I ^ 5 = I := by
  rw [show 5 = 4 + 1 by norm_num, pow_add, I_pow_four]; simp

/-- Stitz-Zeager Exercise 3.4.20: `i⁶ = -1`. -/
@[kb "stitzzeager2013" "Exercise 3.4.20, p. 307"]
theorem exer_3_4_20 : I ^ 6 = -1 := by
  rw [show 6 = 4 + 2 by norm_num, pow_add, I_pow_four]; simp

/-- Stitz-Zeager Exercise 3.4.21: `i⁷ = -i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.21, p. 307"]
theorem exer_3_4_21 : I ^ 7 = -I := by
  rw [show 7 = 4 + 3 by norm_num, pow_add, I_pow_four]; simp [pow_succ]

/-- Stitz-Zeager Exercise 3.4.22: `i⁸ = 1`. -/
@[kb "stitzzeager2013" "Exercise 3.4.22, p. 307"]
theorem exer_3_4_22 : I ^ 8 = 1 := by
  rw [show 8 = 4 * 2 by norm_num, pow_mul, I_pow_four]; simp

/-- Stitz-Zeager Exercise 3.4.24: `i²⁶ = -1`. -/
@[kb "stitzzeager2013" "Exercise 3.4.24, p. 307"]
theorem exer_3_4_24 : I ^ 26 = -1 := by
  rw [show 26 = 4 * 6 + 2 by norm_num, pow_add, pow_mul, I_pow_four]; simp

/-- Stitz-Zeager Exercise 3.4.25: `i¹¹⁷ = i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.25, p. 307"]
theorem exer_3_4_25 : I ^ 117 = I := by
  rw [show 117 = 4 * 29 + 1 by norm_num, pow_add, pow_mul, I_pow_four]; simp

/-- Stitz-Zeager Exercise 3.4.26: `i³⁰⁴ = 1`. -/
@[kb "stitzzeager2013" "Exercise 3.4.26, p. 307"]
theorem exer_3_4_26 : I ^ 304 = 1 := by
  rw [show 304 = 4 * 76 by norm_num, pow_mul, I_pow_four]; simp

/-- Stitz-Zeager Exercise 3.4.7: for `z = √2 - i√2`, `w = √2 + i√2`: `z + w = 2√2`, `zw = 4`,
`z² = -4i`, `1/z = √2/4 + (√2/4)i`, `z/w = -i`, `w/z = i`, `z̄ = √2 + i√2`, `z z̄ = 4`, `(z̄)² = 4i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.7, p. 307"]
theorem exer_3_4_7 :
    let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
    let z : ℂ := s - s * I
    let w : ℂ := s + s * I
    z + w = 2 * s ∧ z * w = 4 ∧ z ^ 2 = -4 * I ∧ 1 / z = s / 4 + s / 4 * I ∧
    z / w = -I ∧ w / z = I ∧ conj z = s + s * I ∧ z * conj z = 4 ∧ conj z ^ 2 = 4 * I := by
  intro s z w
  have hs : s ^ 2 = 2 := by
    simp only [s]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs4 : s ^ 4 = 4 := by rw [show 4 = 2 * 2 by norm_num, pow_mul, hs]; norm_num
  have hcz : conj z = s + s * I := by
    simp only [z, s, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hz1 : z * (s / 4 + s / 4 * I) = 1 := by simp only [z]; w7alg
  have hw1 : w * (s / 4 - s / 4 * I) = 1 := by simp only [w]; w7alg
  have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hz1
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hw1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcz, ?_, ?_⟩
  · simp only [z, w]; ring
  · simp only [z, w]; w7alg
  · simp only [z]; w7alg
  · rw [one_div]; exact inv_eq_of_mul_eq_one_right hz1
  · rw [div_eq_iff hw0]; simp only [z, w]; w7alg
  · rw [div_eq_iff hz0]; simp only [z, w]; w7alg
  · rw [hcz]; simp only [z]; w7alg
  · rw [hcz]; w7alg

/-- Stitz-Zeager Exercise 3.4.8: for `z = 1 - i√3`, `w = -1 - i√3`: `z + w = -2i√3`, `zw = -4`,
`z² = -2 - 2i√3`, `1/z = 1/4 + (√3/4)i`, `z/w = 1/2 + (√3/2)i`, `w/z = 1/2 - (√3/2)i`,
`z̄ = 1 + i√3`, `z z̄ = 4`, `(z̄)² = -2 + 2i√3`. -/
@[kb "stitzzeager2013" "Exercise 3.4.8, p. 307"]
theorem exer_3_4_8 :
    let s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
    let z : ℂ := 1 - s * I
    let w : ℂ := -1 - s * I
    z + w = -2 * s * I ∧ z * w = -4 ∧ z ^ 2 = -2 - 2 * s * I ∧ 1 / z = 1 / 4 + s / 4 * I ∧
    z / w = 1 / 2 + s / 2 * I ∧ w / z = 1 / 2 - s / 2 * I ∧ conj z = 1 + s * I ∧
    z * conj z = 4 ∧ conj z ^ 2 = -2 + 2 * s * I := by
  intro s z w
  have hs : s ^ 2 = 3 := by
    simp only [s]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs4 : s ^ 4 = 9 := by rw [show 4 = 2 * 2 by norm_num, pow_mul, hs]; norm_num
  have hcz : conj z = 1 + s * I := by
    simp only [z, s, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one]; ring
  have hz1 : z * (1 / 4 + s / 4 * I) = 1 := by simp only [z]; w7alg
  have hw1 : w * (-1 / 4 + s / 4 * I) = 1 := by simp only [w]; w7alg
  have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hz1
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hw1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcz, ?_, ?_⟩
  · simp only [z, w]; ring
  · simp only [z, w]; w7alg
  · simp only [z]; w7alg
  · rw [one_div]; exact inv_eq_of_mul_eq_one_right hz1
  · rw [div_eq_iff hw0]; simp only [z, w]; w7alg
  · rw [div_eq_iff hz0]; simp only [z, w]; w7alg
  · rw [hcz]; simp only [z]; w7alg
  · rw [hcz]; w7alg

/-- Stitz-Zeager Exercise 3.4.9: for `z = 1/2 + (√3/2)i`, `w = -1/2 + (√3/2)i`: `z + w = i√3`,
`zw = -1`, `z² = -1/2 + (√3/2)i`, `1/z = 1/2 - (√3/2)i`, `z/w = 1/2 - (√3/2)i`,
`w/z = 1/2 + (√3/2)i`, `z̄ = 1/2 - (√3/2)i`, `z z̄ = 1`, `(z̄)² = -1/2 - (√3/2)i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.9, p. 307"]
theorem exer_3_4_9 :
    let s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
    let z : ℂ := 1 / 2 + s / 2 * I
    let w : ℂ := -1 / 2 + s / 2 * I
    z + w = s * I ∧ z * w = -1 ∧ z ^ 2 = -1 / 2 + s / 2 * I ∧ 1 / z = 1 / 2 - s / 2 * I ∧
    z / w = 1 / 2 - s / 2 * I ∧ w / z = 1 / 2 + s / 2 * I ∧ conj z = 1 / 2 - s / 2 * I ∧
    z * conj z = 1 ∧ conj z ^ 2 = -1 / 2 - s / 2 * I := by
  intro s z w
  have hs : s ^ 2 = 3 := by
    simp only [s]; rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs4 : s ^ 4 = 9 := by rw [show 4 = 2 * 2 by norm_num, pow_mul, hs]; norm_num
  have hcz : conj z = 1 / 2 - s / 2 * I := by
    simp only [z, s, map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_one,
      map_ofNat]; ring
  have hz1 : z * (1 / 2 - s / 2 * I) = 1 := by simp only [z]; w7alg
  have hw1 : w * (-1 / 2 - s / 2 * I) = 1 := by simp only [w]; w7alg
  have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hz1
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hw1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcz, ?_, ?_⟩
  · simp only [z, w]; ring
  · simp only [z, w]; w7alg
  · simp only [z]; w7alg
  · rw [one_div]; exact inv_eq_of_mul_eq_one_right hz1
  · rw [div_eq_iff hw0]; simp only [z, w]; w7alg
  · rw [div_eq_iff hz0]; simp only [z, w]; w7alg
  · rw [hcz]; simp only [z]; w7alg
  · rw [hcz]; w7alg

/-- Stitz-Zeager Exercise 3.4.10: for `z = -√2/2 + (√2/2)i`, `w = -√2/2 - (√2/2)i`: `z + w = -√2`,
`zw = 1`, `z² = -i`, `1/z = -√2/2 - (√2/2)i`, `z/w = -i`, `w/z = i`, `z̄ = -√2/2 - (√2/2)i`,
`z z̄ = 1`, `(z̄)² = i`. -/
@[kb "stitzzeager2013" "Exercise 3.4.10, p. 307"]
theorem exer_3_4_10 :
    let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) / 2
    let z : ℂ := -s + s * I
    let w : ℂ := -s - s * I
    z + w = -2 * s ∧ z * w = 1 ∧ z ^ 2 = -I ∧ 1 / z = -s - s * I ∧
    z / w = -I ∧ w / z = I ∧ conj z = -s - s * I ∧ z * conj z = 1 ∧ conj z ^ 2 = I := by
  intro s z w
  have hs : s ^ 2 = 1 / 2 := by
    simp only [s]; rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs4 : s ^ 4 = 1 / 4 := by rw [show 4 = 2 * 2 by norm_num, pow_mul, hs]; norm_num
  have hcz : conj z = -s - s * I := by
    simp only [z, s, map_add, map_neg, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]; ring
  have hz1 : z * (-s - s * I) = 1 := by simp only [z]; w7alg
  have hw1 : w * (-s + s * I) = 1 := by simp only [w]; w7alg
  have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hz1
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hw1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcz, ?_, ?_⟩
  · simp only [z, w]; ring
  · simp only [z, w]; w7alg
  · simp only [z]; w7alg
  · rw [one_div]; exact inv_eq_of_mul_eq_one_right hz1
  · rw [div_eq_iff hw0]; simp only [z, w]; w7alg
  · rw [div_eq_iff hz0]; simp only [z, w]; w7alg
  · rw [hcz]; simp only [z]; w7alg
  · rw [hcz]; w7alg

end UndergradKB.Precalculus.Course
