import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Algebra.Order.Floor.Ring
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers, Sections 1.5 and 1.6 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 1.5 -/

/-- Stitz-Zeager Exercise 1.5.1: for `f(x) = 3x + 1`, `g(x) = 4 - x` the six requested values of the combined
functions. -/
@[kb "stitzzeager2013" "Exercise 1.5.1, p. 96"]
theorem exer_1_5_1 (f g : ℝ → ℝ) (hf : ∀ x, f x = 3 * x + 1) (hg : ∀ x, g x = 4 - x) :
    (f + g) 2 = 9 ∧ (f - g) (-1) = -7 ∧ (g - f) 1 = -1 ∧ (f * g) (1 / 2) = 35 / 4 ∧
      (f / g) 0 = 1 / 4 ∧ (f / g) (-2) = -5 / 6 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]
  norm_num

/-- Stitz-Zeager Exercise 1.5.5: for `f(x) = √(x+3)`, `g(x) = 2x - 1`, five of the requested values:
`(f+g)(2) = 3 + √5`, `(f-g)(-1) = 3 + √2`, `(g-f)(1) = -1`, `(fg)(1/2) = 0`, `(f/g)(0) = -√3`. -/
@[kb "stitzzeager2013" "Exercise 1.5.5, p. 96"]
theorem exer_1_5_5 (f g : ℝ → ℝ) (hf : ∀ x, f x = √(x + 3)) (hg : ∀ x, g x = 2 * x - 1) :
    (f + g) 2 = 3 + √5 ∧ (f - g) (-1) = 3 + √2 ∧ (g - f) 1 = -1 ∧ (f * g) (1 / 2) = 0 ∧
      (f / g) 0 = -√3 := by
  have h4 : √(1 + 3 : ℝ) = 2 := by
    rw [show (1 + 3 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h1 : √(-1 + 3 : ℝ) = √2 := by norm_num
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show (2 + 3 : ℝ) = 5 by norm_num]; ring
  · rw [h1]; ring
  · rw [h4]; ring
  · rw [show (2 * (1 / 2) - 1 : ℝ) = 0 by norm_num]; simp
  · norm_num; ring

/-- Stitz-Zeager Exercise 1.5.6 (partly): for `f(x) = √(4-x)`, `g(x) = √(x+2)`, `(f+g)(2) = 2 + √2`,
`(f-g)(-1) = -1 + √5`, `(g-f)(1) = 0`, `(f/g)(0) = √2`, and `g(-2) = 0`, so `(f/g)(-2)` does not exist.
ERRATUM: the book's answer list shows `(f/g)(-2) = 0` (as extracted), but the quotient is undefined there. -/
@[kb "stitzzeager2013" "Exercise 1.5.6, p. 96"]
theorem exer_1_5_6 (f g : ℝ → ℝ) (hf : ∀ x, f x = √(4 - x)) (hg : ∀ x, g x = √(x + 2)) :
    (f + g) 2 = 2 + √2 ∧ (f - g) (-1) = -1 + √5 ∧ (g - f) 1 = 0 ∧ (f / g) 0 = √2 ∧
      g (-2) = 0 ∧ f (-2) ≠ 0 := by
  have h2 : √(4 - 2 : ℝ) = √2 := by norm_num
  have h4 : √(2 + 2 : ℝ) = 2 := by
    rw [show (2 + 2 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h5 : √(4 - (-1) : ℝ) = √5 := by norm_num
  have h1 : √(-1 + 2 : ℝ) = 1 := by norm_num
  have h3 : √(4 - 1 : ℝ) = √(1 + 2) := by norm_num
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h2, h4]; ring
  · rw [h5, h1]; ring
  · rw [h3]; ring
  · have : √(4 - 0 : ℝ) = 2 := by
      rw [show (4 - 0 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [this, show (0 + 2 : ℝ) = 2 by norm_num]
    have h2' : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hp : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    linarith
  · norm_num
  · rw [Real.sqrt_ne_zero']; norm_num

/-- Stitz-Zeager Exercise 1.5.7: for `f(x) = 2x`, `g(x) = 1/(2x+1)` the six requested values. -/
@[kb "stitzzeager2013" "Exercise 1.5.7, p. 96"]
theorem exer_1_5_7 (f g : ℝ → ℝ) (hf : ∀ x, f x = 2 * x) (hg : ∀ x, g x = 1 / (2 * x + 1)) :
    (f + g) 2 = 21 / 5 ∧ (f - g) (-1) = -1 ∧ (g - f) 1 = -5 / 3 ∧ (f * g) (1 / 2) = 1 / 2 ∧
      (f / g) 0 = 0 ∧ (f / g) (-2) = 12 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]
  norm_num

/-- Stitz-Zeager Exercise 1.5.8: for `f(x) = x²`, `g(x) = 3/(2x-3)` the six requested values. -/
@[kb "stitzzeager2013" "Exercise 1.5.8, p. 96"]
theorem exer_1_5_8 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2) (hg : ∀ x, g x = 3 / (2 * x - 3)) :
    (f + g) 2 = 7 ∧ (f - g) (-1) = 8 / 5 ∧ (g - f) 1 = -4 ∧ (f * g) (1 / 2) = -3 / 8 ∧
      (f / g) 0 = 0 ∧ (f / g) (-2) = -28 / 3 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]
  norm_num

/-- Stitz-Zeager Exercise 1.5.11: for `f(x) = 2x + 1`, `g(x) = x - 2`: the sum, difference and product formulas
(all on `ℝ`), the quotient formula, and the quotient's domain `(-∞,2) ∪ (2,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.5.11, p. 96"]
theorem exer_1_5_11 (f g : ℝ → ℝ) (hf : ∀ x, f x = 2 * x + 1) (hg : ∀ x, g x = x - 2) :
    (∀ x, (f + g) x = 3 * x - 1) ∧ (∀ x, (f - g) x = x + 3) ∧ (∀ x, (f * g) x = 2 * x ^ 2 - 3 * x - 2) ∧
      (∀ x, (f / g) x = (2 * x + 1) / (x - 2)) ∧ {x : ℝ | g x ≠ 0} = Iio 2 ∪ Ioi 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp only [Pi.add_apply, hf, hg]; ring
  · intro x; simp only [Pi.sub_apply, hf, hg]; ring
  · intro x; simp only [Pi.mul_apply, hf, hg]; ring
  · intro x; simp only [Pi.div_apply, hf, hg]
  · ext x
    simp only [mem_ofPred_eq, hg, mem_union, mem_Iio, mem_Ioi, ne_eq, sub_eq_zero]
    grind

/-- Stitz-Zeager Exercise 1.5.13: for `f(x) = x²`, `g(x) = 3x - 1`: the four formulas and the quotient's domain
`(-∞,1/3) ∪ (1/3,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.5.13, p. 97"]
theorem exer_1_5_13 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2) (hg : ∀ x, g x = 3 * x - 1) :
    (∀ x, (f + g) x = x ^ 2 + 3 * x - 1) ∧ (∀ x, (f - g) x = x ^ 2 - 3 * x + 1) ∧
      (∀ x, (f * g) x = 3 * x ^ 3 - x ^ 2) ∧ (∀ x, (f / g) x = x ^ 2 / (3 * x - 1)) ∧
      {x : ℝ | g x ≠ 0} = Iio (1 / 3) ∪ Ioi (1 / 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp only [Pi.add_apply, hf, hg]; ring
  · intro x; simp only [Pi.sub_apply, hf, hg]; ring
  · intro x; simp only [Pi.mul_apply, hf, hg]; ring
  · intro x; simp only [Pi.div_apply, hf, hg]
  · ext x
    simp only [mem_ofPred_eq, hg, mem_union, mem_Iio, mem_Ioi, ne_eq]
    grind

/-- Stitz-Zeager Exercise 1.5.16: for `f(x) = -x² + x + 6`, `g(x) = x² - 9`: the formulas, the quotient simplifying to
`-(x+2)/(x+3)` off `x = ±3`, and the quotient's domain `(-∞,-3) ∪ (-3,3) ∪ (3,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.5.16, p. 97"]
theorem exer_1_5_16 (f g : ℝ → ℝ) (hf : ∀ x, f x = -x ^ 2 + x + 6) (hg : ∀ x, g x = x ^ 2 - 9) :
    (∀ x, (f + g) x = x - 3) ∧ (∀ x, (f - g) x = -2 * x ^ 2 + x + 15) ∧
      (∀ x, (f * g) x = -x ^ 4 + x ^ 3 + 15 * x ^ 2 - 9 * x - 54) ∧
      (∀ x, g x ≠ 0 → (f / g) x = -(x + 2) / (x + 3)) ∧
      {x : ℝ | g x ≠ 0} = Iio (-3) ∪ Ioo (-3) 3 ∪ Ioi 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp only [Pi.add_apply, hf, hg]; ring
  · intro x; simp only [Pi.sub_apply, hf, hg]; ring
  · intro x; simp only [Pi.mul_apply, hf, hg]; ring
  · intro x hx
    simp only [Pi.div_apply, hf, hg] at hx ⊢
    have h3 : x + 3 ≠ 0 := by
      intro h; apply hx; have : x = -3 := by linarith
      subst this; norm_num
    have h4 : x - 3 ≠ 0 := by
      intro h; apply hx; have : x = 3 := by linarith
      subst this; norm_num
    field_simp
    ring
  · ext x
    simp only [mem_ofPred_eq, hg, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
    have : x ^ 2 - 9 = (x + 3) * (x - 3) := by ring
    rw [this]
    constructor
    · intro h
      have h1 : x + 3 ≠ 0 := left_ne_zero_of_mul h
      have h2 : x - 3 ≠ 0 := right_ne_zero_of_mul h
      grind
    · intro h; exact mul_ne_zero (by grind) (by grind)

/-- Stitz-Zeager Exercise 1.5.19: for `f(x) = x`, `g(x) = √(x+1)`: `f + g` and `f - g` and `f g` are defined on
`[-1, ∞)`, `f/g` on `(-1, ∞)` where it equals `x / √(x+1)`. -/
@[kb "stitzzeager2013" "Exercise 1.5.19, p. 97"]
theorem exer_1_5_19 (f g : ℝ → ℝ) (hf : ∀ x, f x = x) (hg : ∀ x, g x = √(x + 1)) :
    {x : ℝ | 0 ≤ x + 1} = Ici (-1) ∧ {x : ℝ | 0 ≤ x + 1 ∧ g x ≠ 0} = Ioi (-1) ∧
      (∀ x, (f + g) x = x + √(x + 1)) ∧ (∀ x, (f * g) x = x * √(x + 1)) ∧
      (∀ x, (f / g) x = x / √(x + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith
  · ext x
    simp only [mem_ofPred_eq, hg, mem_Ioi, ne_eq, Real.sqrt_eq_zero']
    constructor
    · rintro ⟨h0, h⟩; push Not at h; linarith
    · intro h; exact ⟨by linarith, by push Not; linarith⟩
  · intro x; simp only [Pi.add_apply, hf, hg]
  · intro x; simp only [Pi.mul_apply, hf, hg]
  · intro x; simp only [Pi.div_apply, hf, hg]

/-- Stitz-Zeager Exercise 1.5.20: for `f = g = √(x-5)`: `f + g = 2√(x-5)`, `f - g = 0`, `f g = x - 5` on
`[5, ∞)`, and `f/g = 1` on `(5, ∞)`, the domain of the quotient. -/
@[kb "stitzzeager2013" "Exercise 1.5.20, p. 97"]
theorem exer_1_5_20 (f g : ℝ → ℝ) (hf : ∀ x, f x = √(x - 5)) (hg : ∀ x, g x = √(x - 5)) :
    {x : ℝ | 0 ≤ x - 5} = Ici 5 ∧ {x : ℝ | 0 ≤ x - 5 ∧ g x ≠ 0} = Ioi 5 ∧
      (∀ x, (f + g) x = 2 * √(x - 5)) ∧ (∀ x, (f - g) x = 0) ∧
      (∀ x, 5 ≤ x → (f * g) x = x - 5) ∧ (∀ x, 5 < x → (f / g) x = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith
  · ext x
    simp only [mem_ofPred_eq, hg, mem_Ioi, ne_eq, Real.sqrt_eq_zero']
    constructor
    · rintro ⟨h0, h⟩; push Not at h; linarith
    · intro h; exact ⟨by linarith, by push Not; linarith⟩
  · intro x; simp only [Pi.add_apply, hf, hg]; ring
  · intro x; simp only [Pi.sub_apply, hf, hg]; ring
  · intro x hx; simp only [Pi.mul_apply, hf, hg]
    exact Real.mul_self_sqrt (by linarith)
  · intro x hx; simp only [Pi.div_apply, hf, hg]
    exact div_self (Real.sqrt_ne_zero'.mpr (by linarith))

/-- Stitz-Zeager Exercise 1.5.24: the difference quotient of `f(x) = 3x² - x` is `6x + 3h - 1`. -/
@[kb "stitzzeager2013" "Exercise 1.5.24, p. 97"]
theorem exer_1_5_24 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * x ^ 2 - x) :
    ∀ x h, h ≠ 0 → (f (x + h) - f x) / h = 6 * x + 3 * h - 1 := by
  intro x h hh
  simp only [hf]
  field_simp
  ring

/-- Stitz-Zeager Exercise 1.5.28: the difference quotient of `f(x) = x³ + 1` is `3x² + 3xh + h²`. -/
@[kb "stitzzeager2013" "Exercise 1.5.28, p. 97"]
theorem exer_1_5_28 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 3 + 1) :
    ∀ x h, h ≠ 0 → (f (x + h) - f x) / h = 3 * x ^ 2 + 3 * x * h + h ^ 2 := by
  intro x h hh
  simp only [hf]
  field_simp
  ring

/-- Stitz-Zeager Exercise 1.5.30: the difference quotient of `f(x) = ax² + bx + c` is `2ax + ah + b`. -/
@[kb "stitzzeager2013" "Exercise 1.5.30, p. 97"]
theorem exer_1_5_30 (a b c : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c) :
    ∀ x h, h ≠ 0 → (f (x + h) - f x) / h = 2 * a * x + a * h + b := by
  intro x h hh
  simp only [hf]
  field_simp
  ring

/-- Stitz-Zeager Exercise 1.5.31: the difference quotient of `f(x) = 2/x` is `-2 / (x (x+h))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.31, p. 97"]
theorem exer_1_5_31 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 / x) :
    ∀ x h, h ≠ 0 → x ≠ 0 → x + h ≠ 0 → (f (x + h) - f x) / h = -2 / (x * (x + h)) := by
  intro x h hh hx hxh
  simp only [hf]
  field_simp
  ring

/-- Stitz-Zeager Exercise 1.5.35: the difference quotient of `f(x) = 1/(4x-3)` is `-4 / ((4x-3)(4x+4h-3))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.35, p. 97"]
theorem exer_1_5_35 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / (4 * x - 3)) :
    ∀ x h, h ≠ 0 → 4 * x - 3 ≠ 0 → 4 * x + 4 * h - 3 ≠ 0 →
      (f (x + h) - f x) / h = -4 / ((4 * x - 3) * (4 * x + 4 * h - 3)) := by
  intro x h hh hx hxh
  simp only [hf]
  have : 4 * (x + h) - 3 = 4 * x + 4 * h - 3 := by ring
  rw [this, div_sub_div _ _ hxh hx, div_div,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hxh hx) hh) (mul_ne_zero hx hxh)]
  ring

/-- Stitz-Zeager Exercise 1.5.38: the difference quotient of `f(x) = x²/(2x+1)` is
`(2x² + 2xh + 2x + h) / ((2x+1)(2x+2h+1))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.38, p. 97"]
theorem exer_1_5_38 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 / (2 * x + 1)) :
    ∀ x h, h ≠ 0 → 2 * x + 1 ≠ 0 → 2 * x + 2 * h + 1 ≠ 0 →
      (f (x + h) - f x) / h =
        (2 * x ^ 2 + 2 * x * h + 2 * x + h) / ((2 * x + 1) * (2 * x + 2 * h + 1)) := by
  intro x h hh hx hxh
  simp only [hf]
  have : 2 * (x + h) + 1 = 2 * x + 2 * h + 1 := by ring
  rw [this, div_sub_div _ _ hxh hx, div_div,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hxh hx) hh) (mul_ne_zero hx hxh)]
  ring

/-- Rationalising a difference of square roots: if `a² - b² = c ≠ 0` and `a, b ≥ 0` then `(a - b)/c = 1/(a + b)`. -/
private theorem sqrt_dq_aux (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 - b ^ 2 = c) (hc : c ≠ 0) :
    (a - b) / c = 1 / (a + b) := by
  have hab : a + b ≠ 0 := by
    intro h0
    have : a = 0 := by linarith
    have : b = 0 := by linarith
    apply hc; rw [← h]; simp_all
  field_simp
  linear_combination h

/-- Stitz-Zeager Exercise 1.5.39: the difference quotient of `f(x) = √(x-9)` is `1 / (√(x+h-9) + √(x-9))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.39, p. 97"]
theorem exer_1_5_39 (f : ℝ → ℝ) (hf : ∀ x, f x = √(x - 9)) :
    ∀ x h, h ≠ 0 → 9 ≤ x → 9 ≤ x + h →
      (f (x + h) - f x) / h = 1 / (√(x + h - 9) + √(x - 9)) := by
  intro x h hh hx hxh
  simp only [hf]
  exact sqrt_dq_aux _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]; ring) hh

/-- Stitz-Zeager Exercise 1.5.42: the difference quotient of `f(x) = √(4-x)` is `-1 / (√(4-x-h) + √(4-x))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.42, p. 97"]
theorem exer_1_5_42 (f : ℝ → ℝ) (hf : ∀ x, f x = √(4 - x)) :
    ∀ x h, h ≠ 0 → x ≤ 4 → x + h ≤ 4 →
      (f (x + h) - f x) / h = -1 / (√(4 - x - h) + √(4 - x)) := by
  intro x h hh hx hxh
  simp only [hf]
  have e : 4 - (x + h) = 4 - x - h := by ring
  rw [e]
  have := sqrt_dq_aux (√(4 - x - h)) (√(4 - x)) (-h) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]; ring) (neg_ne_zero.mpr hh)
  rw [div_neg] at this
  rw [neg_div, ← this]
  ring

/-- Stitz-Zeager Exercise 1.5.46 (T-shirts, `C(x) = 2x + 26`, `p(x) = 30 - 2x`): `C(0) = 26`, `C(10) = 46` so the cost
per shirt is `4.6`, `p(5) = 20`, revenue `R = -2x² + 30x`, profit `P = -2x² + 28x - 26`, and `P(x) = 0` exactly at
`x = 1` and `x = 13`.
ERRATUM: book says `C(10) = 4.6`, correct is `C(10) = 46` (the per-shirt cost `C(10)/10` is `4.6`). -/
@[kb "stitzzeager2013" "Exercise 1.5.46, p. 97"]
theorem exer_1_5_46 (C p R P : ℝ → ℝ) (hC : ∀ x, C x = 2 * x + 26) (hp : ∀ x, p x = 30 - 2 * x)
    (hR : ∀ x, R x = x * p x) (hP : ∀ x, P x = R x - C x) :
    C 0 = 26 ∧ C 10 = 46 ∧ C 10 / 10 = 4.6 ∧ p 5 = 20 ∧ (∀ x, R x = -2 * x ^ 2 + 30 * x) ∧
      (∀ x, P x = -2 * x ^ 2 + 28 * x - 26) ∧ ∀ x, P x = 0 ↔ x = 1 ∨ x = 13 := by
  have hP' : ∀ x, P x = -2 * x ^ 2 + 28 * x - 26 := by
    intro x; rw [hP, hR, hp, hC]; ring
  refine ⟨by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hp]; norm_num,
    fun x => by rw [hR, hp]; ring, hP', fun x => ?_⟩
  rw [hP', show -2 * x ^ 2 + 28 * x - 26 = -2 * ((x - 1) * (x - 13)) by ring]
  simp [sub_eq_zero]

/-- Stitz-Zeager Exercise 1.5.47 (tonic, `C(x) = 10x + 100`, `p(x) = 35 - x`): `C(0) = 100`, `C(10) = 200` so `20` per
bottle, `p(5) = 30`, `R = -x² + 35x`, `P = -x² + 25x - 100`, and `P(x) = 0` exactly at `x = 5` and `x = 20`.
ERRATUM: book says `C(10) = 20`, correct is `C(10) = 200` (the per-bottle cost `C(10)/10` is `20`). -/
@[kb "stitzzeager2013" "Exercise 1.5.47, p. 97"]
theorem exer_1_5_47 (C p R P : ℝ → ℝ) (hC : ∀ x, C x = 10 * x + 100) (hp : ∀ x, p x = 35 - x)
    (hR : ∀ x, R x = x * p x) (hP : ∀ x, P x = R x - C x) :
    C 0 = 100 ∧ C 10 = 200 ∧ C 10 / 10 = 20 ∧ p 5 = 30 ∧ (∀ x, R x = -x ^ 2 + 35 * x) ∧
      (∀ x, P x = -x ^ 2 + 25 * x - 100) ∧ ∀ x, P x = 0 ↔ x = 5 ∨ x = 20 := by
  have hP' : ∀ x, P x = -x ^ 2 + 25 * x - 100 := by
    intro x; rw [hP, hR, hp, hC]; ring
  refine ⟨by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hp]; norm_num,
    fun x => by rw [hR, hp]; ring, hP', fun x => ?_⟩
  rw [hP', show -x ^ 2 + 25 * x - 100 = -((x - 5) * (x - 20)) by ring]
  simp [sub_eq_zero]

/-- Stitz-Zeager Exercise 1.5.49 (pies, `C(x) = 3x + 36`, `p(x) = 12 - x/2`): `C(0) = 36`, `C(10) = 66` so `6.6` per
pie, `p(5) = 9.5`, `R = -0.5x² + 12x`, `P = -0.5x² + 9x - 36`, and `P(x) = 0` exactly at `x = 6` and `x = 12`.
ERRATUM: book says `C(10) = 6.6`, correct is `C(10) = 66` (the per-pie cost `C(10)/10` is `6.6`). -/
@[kb "stitzzeager2013" "Exercise 1.5.49, p. 97"]
theorem exer_1_5_49 (C p R P : ℝ → ℝ) (hC : ∀ x, C x = 3 * x + 36) (hp : ∀ x, p x = 12 - 0.5 * x)
    (hR : ∀ x, R x = x * p x) (hP : ∀ x, P x = R x - C x) :
    C 0 = 36 ∧ C 10 = 66 ∧ C 10 / 10 = 6.6 ∧ p 5 = 9.5 ∧ (∀ x, R x = -0.5 * x ^ 2 + 12 * x) ∧
      (∀ x, P x = -0.5 * x ^ 2 + 9 * x - 36) ∧ ∀ x, P x = 0 ↔ x = 6 ∨ x = 12 := by
  have hP' : ∀ x, P x = -0.5 * x ^ 2 + 9 * x - 36 := by
    intro x; rw [hP, hR, hp, hC]; ring
  refine ⟨by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hp]; norm_num,
    fun x => by rw [hR, hp]; ring, hP', fun x => ?_⟩
  rw [hP', show -0.5 * x ^ 2 + 9 * x - 36 = -0.5 * ((x - 6) * (x - 12)) by ring, mul_eq_zero,
    mul_eq_zero, sub_eq_zero, sub_eq_zero]
  norm_num

/-! The finite functions of Exercises 1.5.51 - 62. -/

/-- The function `f` of Exercises 1.5.51 - 62 (zero off the seven listed points). -/
def exer15F : ℤ → ℚ
  | -3 => 4 | -2 => 2 | -1 => 0 | 0 => 1 | 1 => 3 | 2 => 4 | 3 => -1 | _ => 0

/-- The function `g` of Exercises 1.5.51 - 62 (zero off the seven listed points). -/
def exer15G : ℤ → ℚ
  | -3 => -2 | -2 => 0 | -1 => -4 | 0 => 0 | 1 => -3 | 2 => 1 | 3 => 2 | _ => 0

/-- Stitz-Zeager Exercise 1.5.51: `(f + g)(-3) = 2` for the two finite functions. -/
@[kb "stitzzeager2013" "Exercise 1.5.51, p. 98"]
theorem exer_1_5_51 : (exer15F + exer15G) (-3) = 2 := by
  norm_num [exer15F, exer15G]

/-- Stitz-Zeager Exercise 1.5.56: `(g f)(-3) = -8` for the two finite functions. -/
@[kb "stitzzeager2013" "Exercise 1.5.56, p. 98"]
theorem exer_1_5_56 : (exer15G * exer15F) (-3) = -8 := by
  norm_num [exer15F, exer15G]

/-- Stitz-Zeager Exercise 1.5.57: `(f/g)(-2)` does not exist, because `g(-2) = 0` while `-2` is in the domain of `f`. -/
@[kb "stitzzeager2013" "Exercise 1.5.57, p. 98"]
theorem exer_1_5_57 : exer15G (-2) = 0 ∧ exer15F (-2) = 2 := by
  norm_num [exer15F, exer15G]

/-- Stitz-Zeager Exercise 1.5.59: `(f/g)(2) = 4` for the two finite functions. -/
@[kb "stitzzeager2013" "Exercise 1.5.59, p. 98"]
theorem exer_1_5_59 : (exer15F / exer15G) 2 = 4 := by
  norm_num [exer15F, exer15G]

/-- Stitz-Zeager Exercise 1.5.62: `(g/f)(-3) = -1/2` for the two finite functions. -/
@[kb "stitzzeager2013" "Exercise 1.5.62, p. 98"]
theorem exer_1_5_62 : (exer15G / exer15F) (-3) = -1 / 2 := by
  norm_num [exer15F, exer15G]

/-! ## Section 1.6 -/

/-- Stitz-Zeager Exercise 1.6.2: `f(x) = (x - 2)/3` has x-intercept `2`, y-intercept `(0, -2/3)` and is neither even
nor odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.2, p. 119"]
theorem exer_1_6_2 (f : ℝ → ℝ) (hf : ∀ x, f x = (x - 2) / 3) :
    {x : ℝ | f x = 0} = {2} ∧ f 0 = -2 / 3 ∧ ¬ Function.Even f ∧ ¬ Function.Odd f := by
  refine ⟨?_, by rw [hf]; norm_num, fun h => ?_, fun h => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, hf, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  · have := h 1; rw [hf, hf] at this; norm_num at this
  · have := h 1; rw [hf, hf] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.6.4: `f(x) = 4 - x²` has x-intercepts `±2`, y-intercept `(0,4)` and is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.4, p. 119"]
theorem exer_1_6_4 (f : ℝ → ℝ) (hf : ∀ x, f x = 4 - x ^ 2) :
    {x : ℝ | f x = 0} = {-2, 2} ∧ f 0 = 4 ∧ Function.Even f := by
  refine ⟨?_, by rw [hf]; norm_num, fun a => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, hf, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : (x + 2) * (x - 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · rw [hf, hf]; ring

/-- Stitz-Zeager Exercise 1.6.7: `f(x) = x(x-1)(x+2)` has x-intercepts `-2, 0, 1`, y-intercept `(0,0)` and no
symmetry. -/
@[kb "stitzzeager2013" "Exercise 1.6.7, p. 119"]
theorem exer_1_6_7 (f : ℝ → ℝ) (hf : ∀ x, f x = x * (x - 1) * (x + 2)) :
    {x : ℝ | f x = 0} = {-2, 0, 1} ∧ f 0 = 0 ∧ ¬ Function.Even f ∧ ¬ Function.Odd f := by
  refine ⟨?_, by rw [hf]; norm_num, fun h => ?_, fun h => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, hf, mem_insert_iff, mem_singleton_iff, mul_eq_zero, sub_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · right; left; exact h
      · right; right; exact h
      · left; linarith
    · rintro (h | h | h)
      · right; linarith
      · left; left; exact h
      · left; right; exact h
  · have := h 1; rw [hf, hf] at this; norm_num at this
  · have := h 1; rw [hf, hf] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.6.8: `f(x) = √(x - 2)` has domain `[2, ∞)`, x-intercept `2`, and no y-intercept
(`0` is outside the domain). -/
@[kb "stitzzeager2013" "Exercise 1.6.8, p. 119"]
theorem exer_1_6_8 : {x : ℝ | 0 ≤ x - 2} = Ici 2 ∧ {x : ℝ | 0 ≤ x - 2 ∧ √(x - 2) = 0} = {2} ∧
    ¬ (0 ≤ (0 : ℝ) - 2) := by
  refine ⟨?_, ?_, by norm_num⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith
  · ext x
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨h0, h⟩
      have := (Real.sqrt_eq_zero h0).mp h
      linarith
    · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 1.6.10: `f(x) = 3 - 2√(x+2)` has domain `[-2, ∞)`, x-intercept `1/4`, y-intercept
`(0, 3 - 2√2)` and no symmetry. -/
@[kb "stitzzeager2013" "Exercise 1.6.10, p. 119"]
theorem exer_1_6_10 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 - 2 * √(x + 2)) :
    {x : ℝ | -2 ≤ x ∧ f x = 0} = {1 / 4} ∧ f 0 = 3 - 2 * √2 ∧ ¬ Function.Even f ∧ ¬ Function.Odd f := by
  have h2 : √(0 + 2 : ℝ) = √2 := by norm_num
  have h4 : √(2 + 2 : ℝ) = 2 := by
    rw [show (2 + 2 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h0 : √(-2 + 2 : ℝ) = 0 := by norm_num
  refine ⟨?_, by rw [hf, h2], fun h => ?_, fun h => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, hf, mem_singleton_iff]
    constructor
    · rintro ⟨hx, h⟩
      have h1 : √(x + 2) = 3 / 2 := by linarith
      rw [Real.sqrt_eq_iff_mul_self_eq (by linarith) (by norm_num)] at h1
      linarith
    · rintro rfl
      refine ⟨by norm_num, ?_⟩
      rw [show (1 / 4 + 2 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      norm_num
  · have := h 2; rw [hf, hf] at this; rw [h4, h0] at this; norm_num at this
  · have := h 2; rw [hf, hf] at this; rw [h4, h0] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.6.12: `f(x) = 1/(x²+1)` has no x-intercept, y-intercept `(0,1)` and is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.12, p. 119"]
theorem exer_1_6_12 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / (x ^ 2 + 1)) :
    (∀ x, f x ≠ 0) ∧ f 0 = 1 ∧ Function.Even f := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, fun a => ?_⟩
  · rw [hf]; positivity
  · rw [hf, hf, neg_sq]

/-- Stitz-Zeager Exercise 1.6.22: `f(x) = 7x + 2` is neither even nor odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.22, p. 119"]
theorem exer_1_6_22 : ¬ Function.Even (fun x : ℝ => 7 * x + 2) ∧ ¬ Function.Odd (fun x : ℝ => 7 * x + 2) := by
  constructor <;> intro h <;> have := h 1 <;> norm_num at this

/-- Stitz-Zeager Exercise 1.6.26: `f(x) = x² - x - 6` is neither even nor odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.26, p. 119"]
theorem exer_1_6_26 :
    ¬ Function.Even (fun x : ℝ => x ^ 2 - x - 6) ∧ ¬ Function.Odd (fun x : ℝ => x ^ 2 - x - 6) := by
  constructor <;> intro h <;> have := h 1 <;> norm_num at this

/-- Stitz-Zeager Exercise 1.6.28: `f(x) = -x⁵ + 2x³ - x` is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.28, p. 119"]
theorem exer_1_6_28 : Function.Odd (fun x : ℝ => -x ^ 5 + 2 * x ^ 3 - x) := by
  intro a; ring

/-- Stitz-Zeager Exercise 1.6.29: `f(x) = x⁶ - x⁴ + x² + 9` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.29, p. 119"]
theorem exer_1_6_29 : Function.Even (fun x : ℝ => x ^ 6 - x ^ 4 + x ^ 2 + 9) := by
  intro a; ring

/-- Stitz-Zeager Exercise 1.6.30: `f(x) = x³ + x² + x + 1` is neither even nor odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.30, p. 119"]
theorem exer_1_6_30 : ¬ Function.Even (fun x : ℝ => x ^ 3 + x ^ 2 + x + 1) ∧
    ¬ Function.Odd (fun x : ℝ => x ^ 3 + x ^ 2 + x + 1) := by
  constructor <;> intro h <;> have := h 1 <;> norm_num at this

/-- Stitz-Zeager Exercise 1.6.31: `f(x) = √(1 - x)` is neither even nor odd (compare `f(-3) = 2` with `f(3)`, where
`3` is outside the domain). -/
@[kb "stitzzeager2013" "Exercise 1.6.31, p. 119"]
theorem exer_1_6_31 : ¬ Function.Even (fun x : ℝ => √(1 - x)) ∧ ¬ Function.Odd (fun x : ℝ => √(1 - x)) := by
  have h4 : √(1 - -3 : ℝ) = 2 := by
    rw [show (1 - -3 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h0 : √(1 - 3 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
  constructor <;> intro h <;> have := h 3 <;> simp only [h4, h0] at this <;> norm_num at this

/-- Stitz-Zeager Exercise 1.6.32: `f(x) = √(1 - x²)` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.32, p. 119"]
theorem exer_1_6_32 : Function.Even (fun x : ℝ => √(1 - x ^ 2)) := by
  intro a; simp only [neg_sq]

/-- Stitz-Zeager Exercise 1.6.33: `f(x) = 0` is both even and odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.33, p. 119"]
theorem exer_1_6_33 : Function.Even (fun _ : ℝ => (0 : ℝ)) ∧ Function.Odd (fun _ : ℝ => (0 : ℝ)) :=
  ⟨fun _ => rfl, fun _ => by simp⟩

/-- Stitz-Zeager Exercise 1.6.36: `f(x) = 3/x²` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.36, p. 120"]
theorem exer_1_6_36 : Function.Even (fun x : ℝ => 3 / x ^ 2) := by
  intro a; simp only [neg_sq]

/-- Stitz-Zeager Exercise 1.6.37: `f(x) = (2x - 1)/(x + 1)` is neither even nor odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.37, p. 120"]
theorem exer_1_6_37 : ¬ Function.Even (fun x : ℝ => (2 * x - 1) / (x + 1)) ∧
    ¬ Function.Odd (fun x : ℝ => (2 * x - 1) / (x + 1)) := by
  constructor <;> intro h <;> have := h 2 <;> norm_num at this

/-- Stitz-Zeager Exercise 1.6.38: `f(x) = 3x/(x² + 1)` is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.38, p. 120"]
theorem exer_1_6_38 : Function.Odd (fun x : ℝ => 3 * x / (x ^ 2 + 1)) := by
  intro a; simp only [neg_sq, mul_neg, neg_div]

/-- Stitz-Zeager Exercise 1.6.39: `f(x) = (x² - 3)/(x - 4x³)` is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.39, p. 120"]
theorem exer_1_6_39 : Function.Odd (fun x : ℝ => (x ^ 2 - 3) / (x - 4 * x ^ 3)) := by
  intro a
  have : -a - 4 * (-a) ^ 3 = -(a - 4 * a ^ 3) := by ring
  simp only [this, neg_sq, div_neg]

/-- Stitz-Zeager Exercise 1.6.40: `f(x) = 9/√(4 - x²)` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.40, p. 120"]
theorem exer_1_6_40 : Function.Even (fun x : ℝ => 9 / √(4 - x ^ 2)) := by
  intro a; simp only [neg_sq]

/-- Stitz-Zeager Exercise 1.6.76: `f(x) = √(9 - x²)` on its domain `[-3,3]` has absolute maximum `f(0) = 3`, absolute
minimum `0` at `x = ±3`, is increasing on `[-3,0]` and decreasing on `[0,3]`. -/
@[kb "stitzzeager2013" "Exercise 1.6.76, p. 121"]
theorem exer_1_6_76 (f : ℝ → ℝ) (hf : ∀ x, f x = √(9 - x ^ 2)) :
    IsMaxOn f (Icc (-3) 3) 0 ∧ f 0 = 3 ∧ IsMinOn f (Icc (-3) 3) 3 ∧ IsMinOn f (Icc (-3) 3) (-3) ∧
      f 3 = 0 ∧ f (-3) = 0 ∧ StrictMonoOn f (Icc (-3) 0) ∧ StrictAntiOn f (Icc 0 3) := by
  have h3 : √(9 - 0 ^ 2 : ℝ) = 3 := by
    rw [show (9 - 0 ^ 2 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have e3 : f 3 = 0 := by rw [hf]; norm_num
  have e3' : f (-3) = 0 := by rw [hf]; norm_num
  refine ⟨?_, by rw [hf, h3], ?_, ?_, e3, e3', ?_, ?_⟩
  · rw [isMaxOn_iff]
    intro x hx
    rw [hf, hf, h3]
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [sq_nonneg x]
  · rw [isMinOn_iff]
    intro x _
    rw [e3, hf]; exact Real.sqrt_nonneg _
  · rw [isMinOn_iff]
    intro x _
    rw [e3', hf]; exact Real.sqrt_nonneg _
  · intro x hx y hy hxy
    rw [hf, hf]
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    exact Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
  · intro x hx y hy hxy
    rw [hf, hf]
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    exact Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)

/-- Stitz-Zeager Exercise 1.6.77: `f(x) = x√(9 - x²)` on `[-3,3]` has absolute maximum `9/2` at `x = 3√2/2`
(about `2.12`, value about `4.50`) and absolute minimum `-9/2` at `x = -3√2/2`. -/
@[kb "stitzzeager2013" "Exercise 1.6.77, p. 121"]
theorem exer_1_6_77 (f : ℝ → ℝ) (hf : ∀ x, f x = x * √(9 - x ^ 2)) :
    (∀ x ∈ Icc (-3 : ℝ) 3, -(9 / 2) ≤ f x ∧ f x ≤ 9 / 2) ∧ f (3 * √2 / 2) = 9 / 2 ∧
      f (-(3 * √2 / 2)) = -(9 / 2) := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : 0 ≤ √2 := Real.sqrt_nonneg _
  have key : √(9 - (3 * √2 / 2) ^ 2) = 3 * √2 / 2 := by
    rw [show 9 - (3 * √2 / 2) ^ 2 = (3 * √2 / 2) ^ 2 by nlinarith]
    exact Real.sqrt_sq (by positivity)
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨hx1, hx2⟩ := hx
    have hs : √(9 - x ^ 2) ^ 2 = 9 - x ^ 2 := Real.sq_sqrt (by nlinarith)
    rw [hf]
    constructor <;> nlinarith [sq_nonneg (x - √(9 - x ^ 2)), sq_nonneg (x + √(9 - x ^ 2))]
  · rw [hf, key]; nlinarith
  · rw [hf, neg_sq, key]; nlinarith

/-- Stitz-Zeager Exercise 1.6.92: the greatest integer function is neither even nor odd (`⌊1.1⌋ = 1`,
`⌊-1.1⌋ = -2`). -/
@[kb "stitzzeager2013" "Exercise 1.6.92, p. 123"]
theorem exer_1_6_92 :
    ¬ Function.Even (fun x : ℝ => (⌊x⌋ : ℝ)) ∧ ¬ Function.Odd (fun x : ℝ => (⌊x⌋ : ℝ)) := by
  have a : ⌊(-1.1 : ℝ)⌋ = -2 := by rw [Int.floor_eq_iff]; norm_num
  have b : ⌊(1.1 : ℝ)⌋ = 1 := by rw [Int.floor_eq_iff]; norm_num
  constructor <;> intro h <;> have := h 1.1 <;> simp only [a, b] at this <;> norm_num at this

end UndergradKB.Precalculus.Course
