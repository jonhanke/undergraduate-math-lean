import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 11.7 and 11.10 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 11.7 -/

/-- Stitz-Zeager Exercise 11.7.57: `(5/2 + 5/2 i)^3 = -125/4 + 125/4 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.57, p. 1017"]
theorem exer_11_7_57 :
    ((5 / 2 : ℂ) + (5 / 2 : ℂ) * Complex.I) ^ 3 = -125 / 4 + (125 / 4 : ℂ) * Complex.I := by
  linear_combination ((125 / 8 : ℂ) * (3 + Complex.I)) * Complex.I_sq

/-- Stitz-Zeager Exercise 11.7.59: `(3/2 - 3/2 i)^3 = -27/4 - 27/4 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.59, p. 1017"]
theorem exer_11_7_59 :
    ((3 / 2 : ℂ) - (3 / 2 : ℂ) * Complex.I) ^ 3 = -27 / 4 - (27 / 4 : ℂ) * Complex.I := by
  linear_combination ((27 / 8 : ℂ) * (3 - Complex.I)) * Complex.I_sq

/-- Stitz-Zeager Exercise 11.7.78: the five numbers `cis(2πk/5)`, `k = 0..4`, are fifth roots of `1`;
their real parts are `1`, `(√5-1)/4 ≈ 0.309` and `-(1+√5)/4 ≈ -0.809` (twice each, by symmetry). -/
@[kb "stitzzeager2013" "Exercise 11.7.78, p. 1017"]
theorem exer_11_7_78 :
    (∀ k : ℕ, (Complex.exp (2 * π * Complex.I * k / 5)) ^ 5 = 1) ∧
    (cos (2 * π / 5) = (√5 - 1) / 4 ∧ (0.309 : ℝ) < cos (2 * π / 5) ∧ cos (2 * π / 5) < 0.3091) ∧
    (cos (4 * π / 5) = -((1 + √5) / 4) ∧ (-0.8091 : ℝ) < cos (4 * π / 5) ∧
      cos (4 * π / 5) < -0.809) := by
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hlo : (2.236 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : √5 < (2.2361 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have c2 : cos (2 * π / 5) = (√5 - 1) / 4 := by
    have h := Real.cos_two_mul (π / 5)
    rw [show 2 * (π / 5) = 2 * π / 5 by ring, Real.cos_pi_div_five] at h
    rw [h]
    nlinarith
  have c4 : cos (4 * π / 5) = -((1 + √5) / 4) := by
    have h : cos (4 * π / 5) = -cos (π / 5) := by
      rw [show 4 * π / 5 = π - π / 5 by ring, Real.cos_pi_sub]
    rw [h, Real.cos_pi_div_five]
  refine ⟨fun k => ?_, ⟨c2, ?_, ?_⟩, ⟨c4, ?_, ?_⟩⟩
  · rw [← Complex.exp_nat_mul]
    have := Complex.exp_nat_mul_two_pi_mul_I k
    rw [← this]
    congr 1
    push_cast
    ring
  · rw [c2]; linarith
  · rw [c2]; linarith
  · rw [c4]; linarith
  · rw [c4]; linarith

/-- Stitz-Zeager Exercise 11.7.79: `x^12 - 4096` as a product of linear and quadratic factors with
the roots `±2`, `±2i`, `1 ± i√3`, `-1 ± i√3`, `√3 ± i`, `-√3 ± i` paired up. -/
@[kb "stitzzeager2013" "Exercise 11.7.79, p. 1017"]
theorem exer_11_7_79 (x : ℝ) :
    (x - 2) * (x + 2) * (x ^ 2 + 4) * (x ^ 2 - 2 * x + 4) * (x ^ 2 + 2 * x + 4) *
      (x ^ 2 - 2 * √3 * x + 4) * (x ^ 2 + 2 * √3 * x + 4) = x ^ 12 - 4096 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key : (x ^ 2 - 2 * √3 * x + 4) * (x ^ 2 + 2 * √3 * x + 4) = x ^ 4 - 4 * x ^ 2 + 16 := by
    linear_combination (-4 * x ^ 2) * h3
  calc (x - 2) * (x + 2) * (x ^ 2 + 4) * (x ^ 2 - 2 * x + 4) * (x ^ 2 + 2 * x + 4) *
        (x ^ 2 - 2 * √3 * x + 4) * (x ^ 2 + 2 * √3 * x + 4)
      = (x - 2) * (x + 2) * (x ^ 2 + 4) * ((x ^ 2 - 2 * x + 4) * (x ^ 2 + 2 * x + 4)) *
        ((x ^ 2 - 2 * √3 * x + 4) * (x ^ 2 + 2 * √3 * x + 4)) := by ring
    _ = x ^ 12 - 4096 := by rw [key]; ring

/-! ## Section 11.10 -/

/-- Stitz-Zeager Exercise 11.10.12: `x = 3 cos t`, `y = 2 sin t + 1` lies on the ellipse
`(x/3)² + ((y-1)/2)² = 1`; for `π/2 ≤ t ≤ 2π` it runs from `(0, 3)` through `(-3, 1)` (at `t = π`) and
`(0, -1)` (at `t = 3π/2`) to `(3, 1)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.12, p. 1071"]
theorem exer_11_10_12 :
    (∀ t : ℝ, (3 * cos t / 3) ^ 2 + ((2 * sin t + 1 - 1) / 2) ^ 2 = 1) ∧
    (3 * cos (π / 2) = 0 ∧ 2 * sin (π / 2) + 1 = 3) ∧
    (3 * cos π = -3 ∧ 2 * sin π + 1 = 1) ∧
    (3 * cos (3 * π / 2) = 0 ∧ 2 * sin (3 * π / 2) + 1 = -1) ∧
    (3 * cos (2 * π) = 3 ∧ 2 * sin (2 * π) + 1 = 1) := by
  refine ⟨fun t => ?_, ⟨by simp, by rw [Real.sin_pi_div_two]; norm_num⟩, ⟨by simp, by simp⟩, ⟨?_, ?_⟩,
    ⟨by simp, by simp⟩⟩
  · have h := Real.sin_sq_add_cos_sq t
    linear_combination h
  · rw [show 3 * π / 2 = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; norm_num
  · rw [show 3 * π / 2 = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two]; norm_num

/-- Stitz-Zeager Exercise 11.10.21: the curve `x = t³ - 3t`, `y = t² - 4`, `-2 ≤ t ≤ 2`, starts at
`(-2, 0)`, ends at `(2, 0)`, and crosses itself at `(0, -1)` (reached at `t = ±√3`). -/
@[kb "stitzzeager2013" "Exercise 11.10.21, p. 1071"]
theorem exer_11_10_21 :
    ((-2 : ℝ) ^ 3 - 3 * (-2) = -2 ∧ (-2 : ℝ) ^ 2 - 4 = 0) ∧
    ((2 : ℝ) ^ 3 - 3 * 2 = 2 ∧ (2 : ℝ) ^ 2 - 4 = 0) ∧
    (√3 ^ 3 - 3 * √3 = 0 ∧ √3 ^ 2 - 4 = -1) ∧
    ((-√3) ^ 3 - 3 * (-√3) = 0 ∧ (-√3) ^ 2 - 4 = -1) ∧ √3 ≠ -√3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by norm_num, by norm_num, ⟨?_, by linarith⟩, ⟨?_, by nlinarith⟩, by linarith⟩
  · linear_combination √3 * h3
  · linear_combination (-√3) * h3

/-- Stitz-Zeager Exercise 11.10.22: the astroid `x = 4cos³ t`, `y = 4 sin³ t` satisfies
`(x² + y² - 16)³ + 432 x² y² = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.10.22, p. 1071"]
theorem exer_11_10_22 (t : ℝ) :
    ((4 * cos t ^ 3) ^ 2 + (4 * sin t ^ 3) ^ 2 - 16) ^ 3 +
      432 * (4 * cos t ^ 3) ^ 2 * (4 * sin t ^ 3) ^ 2 = 0 := by
  have hs : sin t ^ 2 = 1 - cos t ^ 2 := by linarith [Real.sin_sq_add_cos_sq t]
  have e1 : (4 * sin t ^ 3) ^ 2 = 16 * (sin t ^ 2) ^ 3 := by ring
  have e2 : (4 * cos t ^ 3) ^ 2 = 16 * (cos t ^ 2) ^ 3 := by ring
  rw [e1, e2, hs]
  ring

/-- Stitz-Zeager Exercise 11.10.23: the curve `x = eᵗ + e⁻ᵗ`, `y = eᵗ - e⁻ᵗ` lies on the right branch
`x² - y² = 4`, `x ≥ 2`, of a hyperbola. -/
@[kb "stitzzeager2013" "Exercise 11.10.23, p. 1071"]
theorem exer_11_10_23 (t : ℝ) :
    (exp t + exp (-t)) ^ 2 - (exp t - exp (-t)) ^ 2 = 4 ∧ 2 ≤ exp t + exp (-t) := by
  have hab : exp t * exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have ha : 0 < exp t := Real.exp_pos t
  have hb : 0 < exp (-t) := Real.exp_pos (-t)
  constructor
  · linear_combination 4 * hab
  · nlinarith [sq_nonneg (exp t - exp (-t))]

/-- Stitz-Zeager Exercise 11.10.24: the curve `x = cos 3t`, `y = sin 4t` stays in the square
`[-1,1]²` and is closed: `t = 0` and `t = 2π` give the same point `(1, 0)`. -/
@[kb "stitzzeager2013" "Exercise 11.10.24, p. 1071"]
theorem exer_11_10_24 :
    (∀ t : ℝ, |cos (3 * t)| ≤ 1 ∧ |sin (4 * t)| ≤ 1) ∧
    (cos (3 * 0) = 1 ∧ sin (4 * 0) = 0) ∧ (cos (3 * (2 * π)) = 1 ∧ sin (4 * (2 * π)) = 0) := by
  refine ⟨fun t => ⟨abs_cos_le_one _, abs_sin_le_one _⟩, by simp, ?_, ?_⟩
  · rw [show 3 * (2 * π) = ((3 : ℕ) : ℝ) * (2 * π) by push_cast; ring, Real.cos_nat_mul_two_pi]
  · rw [show 4 * (2 * π) = ((8 : ℕ) : ℝ) * π by push_cast; ring, Real.sin_nat_mul_pi]

/-- Stitz-Zeager Exercise 11.10.39: the piecewise parametrization of the triangle with vertices `(0,0)`,
`(3,0)`, `(0,4)`: it visits the vertices at `t = 0, 1, 2, 3`, and on the three segments of the parameter
interval it stays on the three sides. -/
@[kb "stitzzeager2013" "Exercise 11.10.39, p. 1072"]
theorem exer_11_10_39 (x y : ℝ → ℝ)
    (hx : ∀ t, x t = if t ≤ 1 then 3 * t else if t ≤ 2 then 6 - 3 * t else 0)
    (hy : ∀ t, y t = if t ≤ 1 then 0 else if t ≤ 2 then 4 * t - 4 else 12 - 4 * t) :
    (x 0 = 0 ∧ y 0 = 0) ∧ (x 1 = 3 ∧ y 1 = 0) ∧ (x 2 = 0 ∧ y 2 = 4) ∧ (x 3 = 0 ∧ y 3 = 0) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, y t = 0 ∧ 0 ≤ x t ∧ x t ≤ 3) ∧
    (∀ t ∈ Set.Icc (1 : ℝ) 2, 4 * x t + 3 * y t = 12 ∧ 0 ≤ x t ∧ x t ≤ 3) ∧
    (∀ t ∈ Set.Icc (2 : ℝ) 3, x t = 0 ∧ 0 ≤ y t ∧ y t ≤ 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx, hy]; norm_num
  · rw [hx, hy]; norm_num
  · rw [hx, hy]; norm_num
  · rw [hx, hy]; norm_num
  · intro t ht
    rw [hx, hy]
    split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2]
  · intro t ht
    rw [hx, hy]
    split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2]
  · intro t ht
    rw [hx, hy]
    split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2]

end UndergradKB.Precalculus.Course
