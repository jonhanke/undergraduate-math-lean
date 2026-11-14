import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Section 11.6 (conics: rotation of axes and polar equations). The rotation by `θ` writes
`x = x' cos θ - y' sin θ`, `y = x' sin θ + y' cos θ`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false

/-! ## Helpers -/

private theorem x11f_sqrt_pows (n : ℕ) (hn : 0 < n) : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)

/-- The polar graph `r = c / (a - u cos θ - v sin θ)` (with `0 < c`, `0 < a`, `u² + v² ≤ a²`), as the set
`a √(x² + y²) = u x + v y + c`. -/
private theorem x11f_conic (a u v c : ℝ) (hc : 0 < c) (ha : 0 < a) (huv : u ^ 2 + v ^ 2 ≤ a ^ 2) :
    {p : ℝ × ℝ | ∃ θ : ℝ, a - u * cos θ - v * sin θ ≠ 0 ∧
        p = polarPoint (c / (a - u * cos θ - v * sin θ)) θ} =
      {p : ℝ × ℝ | a * √(p.1 ^ 2 + p.2 ^ 2) = u * p.1 + v * p.2 + c} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hne, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcs := sin_sq_add_cos_sq θ
    have hden : 0 < a - u * cos θ - v * sin θ := by
      have h1 : (u * cos θ + v * sin θ) ^ 2 ≤ a ^ 2 := by
        nlinarith [sq_nonneg (u * sin θ - v * cos θ)]
      have h2 : u * cos θ + v * sin θ ≤ a := by
        by_contra hh; push Not at hh; nlinarith
      rcases lt_or_eq_of_le h2 with h3 | h3
      · linarith
      · exfalso; apply hne; linarith
    set D := a - u * cos θ - v * sin θ with hD
    set r := c / D with hr
    have hrpos : 0 < r := div_pos hc hden
    have hrD : r * D = c := by rw [hr]; field_simp
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * hcs
    rw [e, Real.sqrt_sq hrpos.le]
    rw [hD] at hrD
    linear_combination hrD
  · intro h
    set z : ℂ := ⟨x, y⟩ with hz
    have hx : x = ‖z‖ * cos (Complex.arg z) := (Complex.norm_mul_cos_arg z).symm
    have hy : y = ‖z‖ * sin (Complex.arg z) := (Complex.norm_mul_sin_arg z).symm
    have hn : ‖z‖ = √(x ^ 2 + y ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      simp [hz, sq]
    rw [← hn] at h
    have hk : ‖z‖ * (a - u * cos (Complex.arg z) - v * sin (Complex.arg z)) = c := by
      rw [hx, hy] at h; linear_combination h
    have hne : a - u * cos (Complex.arg z) - v * sin (Complex.arg z) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hk; linarith
    refine ⟨Complex.arg z, hne, ?_⟩
    have : ‖z‖ = c / (a - u * cos (Complex.arg z) - v * sin (Complex.arg z)) := by
      rw [eq_div_iff hne]; exact hk
    simp only [polarPoint, Prod.mk.injEq]
    rw [← this]
    exact ⟨hx, hy⟩

/-! ## Section 11.6 -/

/-- Stitz-Zeager Exercise 11.6.1: after rotating through `π/4`, the curve
`x² + 2xy + y² - √2 x + √2 y - 6 = 0` has the equation `x'² = -(y' - 3)`. -/
@[kb "stitzzeager2013" "Exercise 11.6.1, p. 998"]
theorem exer_11_6_1 (x' y' : ℝ) :
    let x := x' * cos (π / 4) - y' * sin (π / 4)
    let y := x' * sin (π / 4) + y' * cos (π / 4)
    x ^ 2 + 2 * x * y + y ^ 2 - √2 * x + √2 * y - 6 = 0 ↔ x' ^ 2 = -(y' - 3) := by
  intro x y
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : x ^ 2 + 2 * x * y + y ^ 2 - √2 * x + √2 * y - 6 = 2 * (x' ^ 2 - -(y' - 3)) := by
    simp only [x, y, cos_pi_div_four, sin_pi_div_four]
    linear_combination (x' ^ 2 + y') * h2
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.2: after rotating through `π/3`, the curve
`7x² - 4√3 xy + 3y² - 2x - 2√3 y - 5 = 0` has the equation `(x' - 2)²/9 + y'² = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.6.2, p. 998"]
theorem exer_11_6_2 (x' y' : ℝ) :
    let x := x' * cos (π / 3) - y' * sin (π / 3)
    let y := x' * sin (π / 3) + y' * cos (π / 3)
    7 * x ^ 2 - 4 * √3 * x * y + 3 * y ^ 2 - 2 * x - 2 * √3 * y - 5 = 0 ↔
      (x' - 2) ^ 2 / 9 + y' ^ 2 = 1 := by
  intro x y
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h33 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, h3]
  have h34 : √3 ^ 4 = 9 := by nlinarith
  have key : 7 * x ^ 2 - 4 * √3 * x * y + 3 * y ^ 2 - 2 * x - 2 * √3 * y - 5 =
      9 * ((x' - 2) ^ 2 / 9 + y' ^ 2 - 1) := by
    simp only [x, y, cos_pi_div_three, sin_pi_div_three]
    ring_nf
    simp only [h3, h33, h34]
    ring_nf
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.3: after rotating through `π/4`, the curve
`5x² + 6xy + 5y² - 4√2 x + 4√2 y = 0` has the equation `x'² + (y' + 2)²/4 = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.6.3, p. 998"]
theorem exer_11_6_3 (x' y' : ℝ) :
    let x := x' * cos (π / 4) - y' * sin (π / 4)
    let y := x' * sin (π / 4) + y' * cos (π / 4)
    5 * x ^ 2 + 6 * x * y + 5 * y ^ 2 - 4 * √2 * x + 4 * √2 * y = 0 ↔
      x' ^ 2 + (y' + 2) ^ 2 / 4 = 1 := by
  intro x y
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h23 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, h2]
  have h24 : √2 ^ 4 = 4 := by nlinarith
  have key : 5 * x ^ 2 + 6 * x * y + 5 * y ^ 2 - 4 * √2 * x + 4 * √2 * y =
      8 * (x' ^ 2 + (y' + 2) ^ 2 / 4 - 1) := by
    simp only [x, y, cos_pi_div_four, sin_pi_div_four]
    ring_nf
    simp only [h2, h23, h24]
    ring_nf
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.4: after rotating through `π/3`, the curve
`x² + 2√3 xy + 3y² + 2√3 x - 2y - 16 = 0` has the equation `x'² = y' + 4`. -/
@[kb "stitzzeager2013" "Exercise 11.6.4, p. 998"]
theorem exer_11_6_4 (x' y' : ℝ) :
    let x := x' * cos (π / 3) - y' * sin (π / 3)
    let y := x' * sin (π / 3) + y' * cos (π / 3)
    x ^ 2 + 2 * √3 * x * y + 3 * y ^ 2 + 2 * √3 * x - 2 * y - 16 = 0 ↔ x' ^ 2 = y' + 4 := by
  intro x y
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h33 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, h3]
  have h34 : √3 ^ 4 = 9 := by nlinarith
  have key : x ^ 2 + 2 * √3 * x * y + 3 * y ^ 2 + 2 * √3 * x - 2 * y - 16 =
      4 * (x' ^ 2 - (y' + 4)) := by
    simp only [x, y, cos_pi_div_three, sin_pi_div_three]
    ring_nf
    simp only [h3, h33, h34]
    ring_nf
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.5: after rotating through `π/6`, the curve `13x² - 34√3 xy + 47y² - 64 = 0`
has the equation `y'² - x'²/16 = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.6.5, p. 998"]
theorem exer_11_6_5 (x' y' : ℝ) :
    let x := x' * cos (π / 6) - y' * sin (π / 6)
    let y := x' * sin (π / 6) + y' * cos (π / 6)
    13 * x ^ 2 - 34 * √3 * x * y + 47 * y ^ 2 - 64 = 0 ↔ y' ^ 2 - x' ^ 2 / 16 = 1 := by
  intro x y
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h33 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, h3]
  have h34 : √3 ^ 4 = 9 := by nlinarith
  have key : 13 * x ^ 2 - 34 * √3 * x * y + 47 * y ^ 2 - 64 = 64 * (y' ^ 2 - x' ^ 2 / 16 - 1) := by
    simp only [x, y, cos_pi_div_six, sin_pi_div_six]
    ring_nf
    simp only [h3, h33, h34]
    ring_nf
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.6: after rotating through `π/3`, the curve `x² - 2√3 xy - y² + 8 = 0`
has the equation `x'²/4 - y'²/4 = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.6.6, p. 998"]
theorem exer_11_6_6 (x' y' : ℝ) :
    let x := x' * cos (π / 3) - y' * sin (π / 3)
    let y := x' * sin (π / 3) + y' * cos (π / 3)
    x ^ 2 - 2 * √3 * x * y - y ^ 2 + 8 = 0 ↔ x' ^ 2 / 4 - y' ^ 2 / 4 = 1 := by
  intro x y
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h33 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, h3]
  have h34 : √3 ^ 4 = 9 := by nlinarith
  have key : x ^ 2 - 2 * √3 * x * y - y ^ 2 + 8 = -8 * (x' ^ 2 / 4 - y' ^ 2 / 4 - 1) := by
    simp only [x, y, cos_pi_div_three, sin_pi_div_three]
    ring_nf
    simp only [h3, h33, h34]
    ring_nf
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.7: after rotating through `arctan (1/2)`, the curve
`x² - 4xy + 4y² - 2√5 x - √5 y = 0` has the equation `y'² = x'`. -/
@[kb "stitzzeager2013" "Exercise 11.6.7, p. 998"]
theorem exer_11_6_7 (x' y' : ℝ) :
    let x := x' * cos (arctan (1 / 2)) - y' * sin (arctan (1 / 2))
    let y := x' * sin (arctan (1 / 2)) + y' * cos (arctan (1 / 2))
    x ^ 2 - 4 * x * y + 4 * y ^ 2 - 2 * √5 * x - √5 * y = 0 ↔ y' ^ 2 = x' := by
  intro x y
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h53 : √5 ^ 3 = 5 * √5 := by rw [pow_succ, h5]
  have h54 : √5 ^ 4 = 25 := by nlinarith
  have hs : (0 : ℝ) < √5 := by positivity
  have hq : √(1 + (1 / 2 : ℝ) ^ 2) = √5 / 2 := by
    rw [show 1 + (1 / 2 : ℝ) ^ 2 = 5 / 4 by norm_num, Real.sqrt_div (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hc : cos (arctan (1 / 2)) = 2 * √5 / 5 := by
    rw [Real.cos_arctan, hq]; field_simp; nlinarith
  have hsn : sin (arctan (1 / 2)) = √5 / 5 := by
    rw [Real.sin_arctan, hq]; field_simp; nlinarith
  have key : x ^ 2 - 4 * x * y + 4 * y ^ 2 - 2 * √5 * x - √5 * y = 5 * (y' ^ 2 - x') := by
    simp only [x, y, hc, hsn]
    ring_nf
    simp only [h5, h53, h54]
    ring_nf
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.8: after rotating through `arctan 2`, the curve `8x² + 12xy + 17y² - 20 = 0`
has the equation `x'² + y'²/4 = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.6.8, p. 998"]
theorem exer_11_6_8 (x' y' : ℝ) :
    let x := x' * cos (arctan 2) - y' * sin (arctan 2)
    let y := x' * sin (arctan 2) + y' * cos (arctan 2)
    8 * x ^ 2 + 12 * x * y + 17 * y ^ 2 - 20 = 0 ↔ x' ^ 2 + y' ^ 2 / 4 = 1 := by
  intro x y
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h53 : √5 ^ 3 = 5 * √5 := by rw [pow_succ, h5]
  have h54 : √5 ^ 4 = 25 := by nlinarith
  have hs : (0 : ℝ) < √5 := by positivity
  have hq : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have hc : cos (arctan 2) = √5 / 5 := by
    rw [Real.cos_arctan, hq]; field_simp; nlinarith
  have hsn : sin (arctan 2) = 2 * √5 / 5 := by
    rw [Real.sin_arctan, hq]; field_simp; nlinarith
  have key : 8 * x ^ 2 + 12 * x * y + 17 * y ^ 2 - 20 = 20 * (x' ^ 2 + y' ^ 2 / 4 - 1) := by
    simp only [x, y, hc, hsn]
    ring_nf
    simp only [h5, h53, h54]
    ring_nf
  rw [key]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 11.6.9: the polar graph `r = 2/(1 - cos θ)` is the parabola `y² = 4(x + 1)`
(focus at the pole, directrix `x = -2`, vertex `(-1, 0)`). -/
@[kb "stitzzeager2013" "Exercise 11.6.9, p. 998"]
theorem exer_11_6_9 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 1 - cos θ ≠ 0 ∧ p = polarPoint (2 / (1 - cos θ)) θ} =
      {p | p.2 ^ 2 = 4 * (p.1 + 1)} := by
  have h := x11f_conic 1 1 0 2 (by norm_num) (by norm_num) (by norm_num)
  simp only [zero_mul, sub_zero, one_mul, zero_mul, add_zero] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hs0 := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  constructor
  · intro h1
    nlinarith
  · intro h1
    have : x + 2 ≥ 0 := by nlinarith [sq_nonneg y]
    nlinarith

/-- Stitz-Zeager Exercise 11.6.10: the polar graph `r = 3/(2 + sin θ)` is the ellipse
`x²/3 + (y + 1)²/4 = 1` (focus at the pole, center `(0, -1)`, vertices `(0, 1)`, `(0, -3)`). -/
@[kb "stitzzeager2013" "Exercise 11.6.10, p. 998"]
theorem exer_11_6_10 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 2 + sin θ ≠ 0 ∧ p = polarPoint (3 / (2 + sin θ)) θ} =
      {p | p.1 ^ 2 / 3 + (p.2 + 1) ^ 2 / 4 = 1} := by
  have h := x11f_conic 2 0 (-1) 3 (by norm_num) (by norm_num) (by norm_num)
  simp only [zero_mul, zero_add, sub_zero, neg_mul, one_mul, sub_neg_eq_add, zero_mul] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hs0 := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  constructor
  · intro h1
    nlinarith
  · intro h1
    have : 3 - y ≥ 0 := by nlinarith [sq_nonneg x, sq_nonneg (y + 1)]
    nlinarith

/-- Stitz-Zeager Exercise 11.6.11: the polar graph `r = 3/(2 - cos θ)` is the ellipse
`(x - 1)²/4 + y²/3 = 1` (focus at the pole, center `(1, 0)`, vertices `(-1, 0)`, `(3, 0)`). -/
@[kb "stitzzeager2013" "Exercise 11.6.11, p. 998"]
theorem exer_11_6_11 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 2 - cos θ ≠ 0 ∧ p = polarPoint (3 / (2 - cos θ)) θ} =
      {p | (p.1 - 1) ^ 2 / 4 + p.2 ^ 2 / 3 = 1} := by
  have h := x11f_conic 2 1 0 3 (by norm_num) (by norm_num) (by norm_num)
  simp only [zero_mul, sub_zero, one_mul, add_zero] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hs0 := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  constructor
  · intro h1
    nlinarith
  · intro h1
    have : x + 3 ≥ 0 := by nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
    nlinarith

/-- Stitz-Zeager Exercise 11.6.12: the polar graph `r = 2/(1 + sin θ)` is the parabola `x² = -4(y - 1)`
(focus at the pole, directrix `y = 2`, vertex `(0, 1)`). -/
@[kb "stitzzeager2013" "Exercise 11.6.12, p. 998"]
theorem exer_11_6_12 :
    {p : ℝ × ℝ | ∃ θ : ℝ, 1 + sin θ ≠ 0 ∧ p = polarPoint (2 / (1 + sin θ)) θ} =
      {p | p.1 ^ 2 = -4 * (p.2 - 1)} := by
  have h := x11f_conic 1 0 (-1) 2 (by norm_num) (by norm_num) (by norm_num)
  simp only [zero_mul, zero_add, sub_zero, neg_mul, one_mul, sub_neg_eq_add, zero_mul] at h
  rw [h]
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hs0 := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  constructor
  · intro h1
    nlinarith
  · intro h1
    have : 2 - y ≥ 0 := by nlinarith [sq_nonneg x]
    nlinarith

/-- Stitz-Zeager Exercise 11.6.17: the rotation matrix `A(θ) = [[cos θ, -sin θ], [sin θ, cos θ]]` at
`θ = π/4` is `[[√2/2, -√2/2], [√2/2, √2/2]]`. -/
@[kb "stitzzeager2013" "Exercise 11.6.17, p. 998"]
theorem exer_11_6_17 :
    !![cos (π / 4), -sin (π / 4); sin (π / 4), cos (π / 4)] =
      !![√2 / 2, -(√2 / 2); √2 / 2, √2 / 2] := by
  rw [cos_pi_div_four, sin_pi_div_four]

/-- Stitz-Zeager Exercise 11.6.19: the rotation matrix satisfies `A(θ)⁻¹ = A(-θ)`. -/
@[kb "stitzzeager2013" "Exercise 11.6.19, p. 998"]
theorem exer_11_6_19 (θ : ℝ) :
    (!![cos θ, -sin θ; sin θ, cos θ] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      !![cos (-θ), -sin (-θ); sin (-θ), cos (-θ)] := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_fin_two]
  simp only [cos_neg, sin_neg]
  have h := sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith

end UndergradKB.Precalculus.Course
