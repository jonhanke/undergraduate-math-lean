import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Radicals

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 1.5 -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

/-! ## Section 1.5 -/

/-- Stitz-Zeager Exercise 1.5.2: values of `f ± g`, `fg`, `f/g` for `f(x) = x²`, `g(x) = -2x + 1`. -/
@[kb "stitzzeager2013" "Exercise 1.5.2, p. 96"]
theorem exer_1_5_2 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2) (hg : ∀ x, g x = -2 * x + 1) :
    (f + g) 2 = 1 ∧ (f - g) (-1) = -2 ∧ (g - f) 1 = -2 ∧ (f * g) (1 / 2) = 0 ∧ (f / g) 0 = 0 ∧
      (f / g) (-2) = 4 / 5 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]; norm_num

/-- Stitz-Zeager Exercise 1.5.3: values for `f(x) = x² - x`, `g(x) = 12 - x²`. -/
@[kb "stitzzeager2013" "Exercise 1.5.3, p. 96"]
theorem exer_1_5_3 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - x) (hg : ∀ x, g x = 12 - x ^ 2) :
    (f + g) 2 = 10 ∧ (f - g) (-1) = -9 ∧ (g - f) 1 = 11 ∧ (f * g) (1 / 2) = -47 / 16 ∧ (f / g) 0 = 0 ∧
      (f / g) (-2) = 3 / 4 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]; norm_num

/-- Stitz-Zeager Exercise 1.5.4: values for `f(x) = 2x³`, `g(x) = -x² - 2x - 3`. -/
@[kb "stitzzeager2013" "Exercise 1.5.4, p. 96"]
theorem exer_1_5_4 (f g : ℝ → ℝ) (hf : ∀ x, f x = 2 * x ^ 3) (hg : ∀ x, g x = -x ^ 2 - 2 * x - 3) :
    (f + g) 2 = 5 ∧ (f - g) (-1) = 0 ∧ (g - f) 1 = -8 ∧ (f * g) (1 / 2) = -17 / 16 ∧ (f / g) 0 = 0 ∧
      (f / g) (-2) = 16 / 3 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]; norm_num

/-- Stitz-Zeager Exercise 1.5.9: values for `f(x) = x²`, `g(x) = 1/x²`; `0` is not in the domain of `g`, so
`(f/g)(0)` does not exist. -/
@[kb "stitzzeager2013" "Exercise 1.5.9, p. 96"]
theorem exer_1_5_9 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2) (hg : ∀ x, g x = 1 / x ^ 2) :
    (f + g) 2 = 17 / 4 ∧ (f - g) (-1) = 0 ∧ (g - f) 1 = 0 ∧ (f * g) (1 / 2) = 1 ∧
      (0 : ℝ) ∉ {x : ℝ | x ^ 2 ≠ 0} ∧ (f / g) (-2) = 16 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]; norm_num

/-- Stitz-Zeager Exercise 1.5.10: values for `f(x) = x² + 1`, `g(x) = 1/(x² + 1)`. -/
@[kb "stitzzeager2013" "Exercise 1.5.10, p. 96"]
theorem exer_1_5_10 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + 1) (hg : ∀ x, g x = 1 / (x ^ 2 + 1)) :
    (f + g) 2 = 26 / 5 ∧ (f - g) (-1) = 3 / 2 ∧ (g - f) 1 = -3 / 2 ∧ (f * g) (1 / 2) = 1 ∧
      (f / g) 0 = 1 ∧ (f / g) (-2) = 25 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, hf, hg]; norm_num

/-- Stitz-Zeager Exercise 1.5.12: for `f(x) = 1 - 4x`, `g(x) = 2x - 1`: the sum, difference and product formulas, and
the quotient is defined exactly off `x = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 1.5.12, p. 96"]
theorem exer_1_5_12 (f g : ℝ → ℝ) (hf : ∀ x, f x = 1 - 4 * x) (hg : ∀ x, g x = 2 * x - 1) :
    (∀ x, (f + g) x = -2 * x) ∧ (∀ x, (f - g) x = 2 - 6 * x) ∧
      (∀ x, (f * g) x = -8 * x ^ 2 + 6 * x - 1) ∧ (∀ x, (f / g) x = (1 - 4 * x) / (2 * x - 1)) ∧
      {x : ℝ | 2 * x - 1 ≠ 0} = Iio (1 / 2) ∪ Ioi (1 / 2) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, ?_⟩
  · simp only [Pi.add_apply, hf, hg]; ring
  · simp only [Pi.sub_apply, hf, hg]; ring
  · simp only [Pi.mul_apply, hf, hg]; ring
  · simp only [Pi.div_apply, hf, hg]
  · ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.5.14: for `f(x) = x² - x`, `g(x) = 7x`: the formulas, and `f/g = (x-1)/7` on the domain
`x ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 1.5.14, p. 96"]
theorem exer_1_5_14 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - x) (hg : ∀ x, g x = 7 * x) :
    (∀ x, (f + g) x = x ^ 2 + 6 * x) ∧ (∀ x, (f - g) x = x ^ 2 - 8 * x) ∧
      (∀ x, (f * g) x = 7 * x ^ 3 - 7 * x ^ 2) ∧ (∀ x, x ≠ 0 → (f / g) x = (x - 1) / 7) ∧
      {x : ℝ | 7 * x ≠ 0} = Iio 0 ∪ Ioi 0 := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_, ?_⟩
  · simp only [Pi.add_apply, hf, hg]; ring
  · simp only [Pi.sub_apply, hf, hg]; ring
  · simp only [Pi.mul_apply, hf, hg]; ring
  · simp only [Pi.div_apply, hf, hg]; field_simp
  · ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.5.15: for `f(x) = x² - 4`, `g(x) = 3x + 6`: the formulas, and `f/g = (x-2)/3` on the
domain `x ≠ -2`. -/
@[kb "stitzzeager2013" "Exercise 1.5.15, p. 96"]
theorem exer_1_5_15 (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - 4) (hg : ∀ x, g x = 3 * x + 6) :
    (∀ x, (f + g) x = x ^ 2 + 3 * x + 2) ∧ (∀ x, (f - g) x = x ^ 2 - 3 * x - 10) ∧
      (∀ x, (f * g) x = 3 * x ^ 3 + 6 * x ^ 2 - 12 * x - 24) ∧
      (∀ x, x ≠ -2 → (f / g) x = (x - 2) / 3) ∧ {x : ℝ | 3 * x + 6 ≠ 0} = Iio (-2) ∪ Ioi (-2) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_, ?_⟩
  · simp only [Pi.add_apply, hf, hg]; ring
  · simp only [Pi.sub_apply, hf, hg]; ring
  · simp only [Pi.mul_apply, hf, hg]; ring
  · have h : x + 2 ≠ 0 := fun h => hx (by linarith)
    simp only [Pi.div_apply, hf, hg]
    rw [show 3 * x + 6 = 3 * (x + 2) by ring, show x ^ 2 - 4 = (x - 2) * (x + 2) by ring]
    field_simp
  · ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.5.17: for `f(x) = x/2`, `g(x) = 2/x`: the formulas on `x ≠ 0`, and the common domain is
`x ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 1.5.17, p. 96"]
theorem exer_1_5_17 (f g : ℝ → ℝ) (hf : ∀ x, f x = x / 2) (hg : ∀ x, g x = 2 / x) :
    (∀ x, x ≠ 0 → (f + g) x = (x ^ 2 + 4) / (2 * x)) ∧ (∀ x, x ≠ 0 → (f - g) x = (x ^ 2 - 4) / (2 * x)) ∧
      (∀ x, x ≠ 0 → (f * g) x = 1) ∧ (∀ x, x ≠ 0 → (f / g) x = x ^ 2 / 4) ∧
      {x : ℝ | x ≠ 0 ∧ 2 / x ≠ 0} = Iio 0 ∪ Ioi 0 := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · simp only [Pi.add_apply, hf, hg]; field_simp; norm_num
  · simp only [Pi.sub_apply, hf, hg]; field_simp; norm_num
  · simp only [Pi.mul_apply, hf, hg]; field_simp
  · simp only [Pi.div_apply, hf, hg]; field_simp; norm_num
  · ext x
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, ne_eq, div_eq_zero_iff]
    grind

/-- Stitz-Zeager Exercise 1.5.18: for `f(x) = x - 1`, `g(x) = 1/(x - 1)`: the formulas on `x ≠ 1`, and the common
domain is `x ≠ 1`. -/
@[kb "stitzzeager2013" "Exercise 1.5.18, p. 96"]
theorem exer_1_5_18 (f g : ℝ → ℝ) (hf : ∀ x, f x = x - 1) (hg : ∀ x, g x = 1 / (x - 1)) :
    (∀ x, x ≠ 1 → (f + g) x = (x ^ 2 - 2 * x + 2) / (x - 1)) ∧
      (∀ x, x ≠ 1 → (f - g) x = (x ^ 2 - 2 * x) / (x - 1)) ∧ (∀ x, x ≠ 1 → (f * g) x = 1) ∧
      (∀ x, x ≠ 1 → (f / g) x = x ^ 2 - 2 * x + 1) ∧
      {x : ℝ | x - 1 ≠ 0 ∧ 1 / (x - 1) ≠ 0} = Iio 1 ∪ Ioi 1 := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have h : x - 1 ≠ 0 := fun h => hx (by linarith)
    simp only [Pi.add_apply, hf, hg]; field_simp; ring
  · have h : x - 1 ≠ 0 := fun h => hx (by linarith)
    simp only [Pi.sub_apply, hf, hg]; field_simp; ring
  · have h : x - 1 ≠ 0 := fun h => hx (by linarith)
    simp only [Pi.mul_apply, hf, hg]; field_simp
  · have h : x - 1 ≠ 0 := fun h => hx (by linarith)
    simp only [Pi.div_apply, hf, hg]; field_simp; ring
  · ext x
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, ne_eq, div_eq_zero_iff]
    grind

/-! ### Difference quotients -/

/-- Stitz-Zeager Exercise 1.5.21: the difference quotient of `f(x) = 2x - 5` is `2`. -/
@[kb "stitzzeager2013" "Exercise 1.5.21, p. 96"]
theorem exer_1_5_21 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x - 5) :
    ∀ x k : ℝ, k ≠ 0 → (f (x + k) - f x) / k = 2 := by
  intro x k hk; simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.22: the difference quotient of `f(x) = -3x + 5` is `-3`. -/
@[kb "stitzzeager2013" "Exercise 1.5.22, p. 96"]
theorem exer_1_5_22 (f : ℝ → ℝ) (hf : ∀ x, f x = -3 * x + 5) :
    ∀ x k : ℝ, k ≠ 0 → (f (x + k) - f x) / k = -3 := by
  intro x k hk; simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.23: the difference quotient of the constant function `6` is `0`. -/
@[kb "stitzzeager2013" "Exercise 1.5.23, p. 96"]
theorem exer_1_5_23 (f : ℝ → ℝ) (hf : ∀ x, f x = 6) :
    ∀ x k : ℝ, k ≠ 0 → (f (x + k) - f x) / k = 0 := by
  intro x k hk; simp [hf]

/-- Stitz-Zeager Exercise 1.5.25: the difference quotient of `f(x) = -x² + 2x - 1` is `-2x - h + 2`. -/
@[kb "stitzzeager2013" "Exercise 1.5.25, p. 96"]
theorem exer_1_5_25 (f : ℝ → ℝ) (hf : ∀ x, f x = -x ^ 2 + 2 * x - 1) :
    ∀ x k : ℝ, k ≠ 0 → (f (x + k) - f x) / k = -2 * x - k + 2 := by
  intro x k hk; simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.26: the difference quotient of `f(x) = 4x²` is `8x + 4h`. -/
@[kb "stitzzeager2013" "Exercise 1.5.26, p. 96"]
theorem exer_1_5_26 (f : ℝ → ℝ) (hf : ∀ x, f x = 4 * x ^ 2) :
    ∀ x k : ℝ, k ≠ 0 → (f (x + k) - f x) / k = 8 * x + 4 * k := by
  intro x k hk; simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.27: the difference quotient of `f(x) = x - x²` is `-2x - h + 1`. -/
@[kb "stitzzeager2013" "Exercise 1.5.27, p. 97"]
theorem exer_1_5_27 (f : ℝ → ℝ) (hf : ∀ x, f x = x - x ^ 2) :
    ∀ x k : ℝ, k ≠ 0 → (f (x + k) - f x) / k = -2 * x - k + 1 := by
  intro x k hk; simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.29: the difference quotient of `f(x) = mx + b` (`m ≠ 0`) is `m`. -/
@[kb "stitzzeager2013" "Exercise 1.5.29, p. 97"]
theorem exer_1_5_29 (f : ℝ → ℝ) (m b : ℝ) (hm : m ≠ 0) (hf : ∀ x, f x = m * x + b) :
    ∀ x k : ℝ, k ≠ 0 → (f (x + k) - f x) / k = m := by
  intro x k hk; simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.32: the difference quotient of `f(x) = 3/(1 - x)` is `3/((1 - x - h)(1 - x))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.32, p. 97"]
theorem exer_1_5_32 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 / (1 - x)) :
    ∀ x k : ℝ, k ≠ 0 → 1 - x ≠ 0 → 1 - x - k ≠ 0 →
      (f (x + k) - f x) / k = 3 / ((1 - x - k) * (1 - x)) := by
  intro x k hk h1 h2
  have h3 : 1 - (x + k) ≠ 0 := by intro h; apply h2; linarith
  simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.33: the difference quotient of `f(x) = 1/x²` is `-(2x + h)/(x²(x+h)²)`. -/
@[kb "stitzzeager2013" "Exercise 1.5.33, p. 97"]
theorem exer_1_5_33 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / x ^ 2) :
    ∀ x k : ℝ, k ≠ 0 → x ≠ 0 → x + k ≠ 0 →
      (f (x + k) - f x) / k = -(2 * x + k) / (x ^ 2 * (x + k) ^ 2) := by
  intro x k hk h1 h2
  simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.34: the difference quotient of `f(x) = 2/(x+5)` is `-2/((x+5)(x+h+5))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.34, p. 97"]
theorem exer_1_5_34 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 / (x + 5)) :
    ∀ x k : ℝ, k ≠ 0 → x + 5 ≠ 0 → x + k + 5 ≠ 0 →
      (f (x + k) - f x) / k = -2 / ((x + 5) * (x + k + 5)) := by
  intro x k hk h1 h2
  have h3 : x + k + 5 ≠ 0 := h2
  simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.36: the difference quotient of `f(x) = 3x/(x+1)` is `3/((x+1)(x+h+1))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.36, p. 97"]
theorem exer_1_5_36 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * x / (x + 1)) :
    ∀ x k : ℝ, k ≠ 0 → x + 1 ≠ 0 → x + k + 1 ≠ 0 →
      (f (x + k) - f x) / k = 3 / ((x + 1) * (x + k + 1)) := by
  intro x k hk h1 h2
  simp only [hf]; field_simp; ring

/-- Stitz-Zeager Exercise 1.5.37: the difference quotient of `f(x) = x/(x-9)` is `-9/((x-9)(x+h-9))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.37, p. 97"]
theorem exer_1_5_37 (f : ℝ → ℝ) (hf : ∀ x, f x = x / (x - 9)) :
    ∀ x k : ℝ, k ≠ 0 → x - 9 ≠ 0 → x + k - 9 ≠ 0 →
      (f (x + k) - f x) / k = -9 / ((x - 9) * (x + k - 9)) := by
  intro x k hk h1 h2
  have h3 : x + k - 9 ≠ 0 := h2
  simp only [hf]; field_simp; ring

/-- Rationalisation: for nonnegative `A, B` with `A² - B² = c h` and `c, h ≠ 0`, `(A - B)/h = c/(A + B)`. -/
private theorem dq_aux (A B c k : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : k ≠ 0) (hc : A ^ 2 - B ^ 2 = c * k)
    (hc0 : c ≠ 0) : (A - B) / k = c / (A + B) := by
  have hAB : A + B ≠ 0 := by
    intro h
    have hA0 : A = 0 := by linarith
    have hB0 : B = 0 := by linarith
    apply mul_ne_zero hc0 hk
    rw [← hc, hA0, hB0]; norm_num
  rw [div_eq_div_iff hk hAB]
  linear_combination hc

/-- Stitz-Zeager Exercise 1.5.40: the difference quotient of `f(x) = √(2x+1)` is
`2/(√(2x+2h+1) + √(2x+1))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.40, p. 97"]
theorem exer_1_5_40 (f : ℝ → ℝ) (hf : ∀ x, f x = √(2 * x + 1)) :
    ∀ x k : ℝ, k ≠ 0 → 0 ≤ 2 * x + 1 → 0 ≤ 2 * (x + k) + 1 →
      (f (x + k) - f x) / k = 2 / (√(2 * (x + k) + 1) + √(2 * x + 1)) := by
  intro x k hk h1 h2
  simp only [hf]
  exact dq_aux _ _ 2 k (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hk
    (by rw [Real.sq_sqrt h2, Real.sq_sqrt h1]; ring) two_ne_zero

/-- Stitz-Zeager Exercise 1.5.41: the difference quotient of `f(x) = √(-4x+5)` is
`-4/(√(-4(x+h)+5) + √(-4x+5))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.41, p. 97"]
theorem exer_1_5_41 (f : ℝ → ℝ) (hf : ∀ x, f x = √(-4 * x + 5)) :
    ∀ x k : ℝ, k ≠ 0 → 0 ≤ -4 * x + 5 → 0 ≤ -4 * (x + k) + 5 →
      (f (x + k) - f x) / k = -4 / (√(-4 * (x + k) + 5) + √(-4 * x + 5)) := by
  intro x k hk h1 h2
  simp only [hf]
  exact dq_aux _ _ (-4) k (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hk
    (by rw [Real.sq_sqrt h2, Real.sq_sqrt h1]; ring) (by norm_num)

/-- Stitz-Zeager Exercise 1.5.43: the difference quotient of `f(x) = √(ax+b)` (`a ≠ 0`) is
`a/(√(a(x+h)+b) + √(ax+b))`. -/
@[kb "stitzzeager2013" "Exercise 1.5.43, p. 97"]
theorem exer_1_5_43 (f : ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hf : ∀ x, f x = √(a * x + b)) :
    ∀ x k : ℝ, k ≠ 0 → 0 ≤ a * x + b → 0 ≤ a * (x + k) + b →
      (f (x + k) - f x) / k = a / (√(a * (x + k) + b) + √(a * x + b)) := by
  intro x k hk h1 h2
  simp only [hf]
  exact dq_aux _ _ a k (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hk
    (by rw [Real.sq_sqrt h2, Real.sq_sqrt h1]; ring) ha

/-- Stitz-Zeager Exercise 1.5.44: the difference quotient of `f(x) = x√x` is
`(3x² + 3xh + h²)/((x+h)√(x+h) + x√x)`. -/
@[kb "stitzzeager2013" "Exercise 1.5.44, p. 97"]
theorem exer_1_5_44 (f : ℝ → ℝ) (hf : ∀ x, f x = x * √x) :
    ∀ x k : ℝ, k ≠ 0 → 0 ≤ x → 0 ≤ x + k →
      (f (x + k) - f x) / k =
        (3 * x ^ 2 + 3 * x * k + k ^ 2) / ((x + k) * √(x + k) + x * √x) := by
  intro x k hk h1 h2
  simp only [hf]
  have e1 : ((x + k) * √(x + k)) ^ 2 = (x + k) ^ 3 := by
    rw [mul_pow, Real.sq_sqrt h2]; ring
  have e2 : (x * √x) ^ 2 = x ^ 3 := by
    rw [mul_pow, Real.sq_sqrt h1]; ring
  have hc : 3 * x ^ 2 + 3 * x * k + k ^ 2 ≠ 0 := by
    have : 0 < 3 * x ^ 2 + 3 * x * k + k ^ 2 := by
      have := mul_nonneg h1 h2
      have := sq_pos_of_ne_zero hk
      nlinarith
    exact this.ne'
  exact dq_aux _ _ _ k (mul_nonneg h2 (Real.sqrt_nonneg _)) (mul_nonneg h1 (Real.sqrt_nonneg _)) hk
    (by rw [e1, e2]; ring) hc

/-- Stitz-Zeager Exercise 1.5.45: the difference quotient of the cube root `f(x) = ∛x` is
`1/(a² + ab + b²)` with `a = ∛(x+h)`, `b = ∛x`. -/
@[kb "stitzzeager2013" "Exercise 1.5.45, p. 97"]
theorem exer_1_5_45 (f : ℝ → ℝ) (hf : ∀ x, f x = principalRoot 3 x) :
    ∀ x k : ℝ, k ≠ 0 →
      (f (x + k) - f x) / k = 1 / (principalRoot 3 (x + k) ^ 2 + principalRoot 3 (x + k) * principalRoot 3 x
        + principalRoot 3 x ^ 2) := by
  intro x k hk
  simp only [hf]
  have ha : principalRoot 3 (x + k) ^ 3 = x + k := principalRoot_pow (by norm_num) (Or.inl (by decide))
  have hb : principalRoot 3 x ^ 3 = x := principalRoot_pow (by norm_num) (Or.inl (by decide))
  set a := principalRoot 3 (x + k)
  set b := principalRoot 3 x
  have e : (a - b) * (a ^ 2 + a * b + b ^ 2) = k := by linear_combination ha - hb
  have hq : a ^ 2 + a * b + b ^ 2 ≠ 0 := by
    intro h; rw [h, mul_zero] at e; exact hk e.symm
  rw [div_eq_div_iff hk hq]
  linear_combination e

/-! ### Cost, revenue and profit -/

/-- Stitz-Zeager Exercise 1.5.48: for `C(x) = 18x + 240` and `p(x) = 90 - 3x` (cents): `C(0) = 240`, the average
cost of 10 cups is `42`, `p(5) = 75`, `R(x) = -3x² + 90x`, `P(x) = -3x² + 72x - 240`, and `P(x) = 0` at `x = 4`
and `x = 20`. -/
@[kb "stitzzeager2013" "Exercise 1.5.48, p. 97"]
theorem exer_1_5_48 (C p R P : ℝ → ℝ) (hC : ∀ x, C x = 18 * x + 240) (hp : ∀ x, p x = 90 - 3 * x)
    (hR : ∀ x, R x = x * p x) (hP : ∀ x, P x = R x - C x) :
    C 0 = 240 ∧ C 10 / 10 = 42 ∧ p 5 = 75 ∧ (∀ x, R x = -3 * x ^ 2 + 90 * x) ∧
      (∀ x, P x = -3 * x ^ 2 + 72 * x - 240) ∧ (∀ x, P x = 0 ↔ x = 4 ∨ x = 20) := by
  have hR' : ∀ x, R x = -3 * x ^ 2 + 90 * x := fun x => by rw [hR, hp]; ring
  have hP' : ∀ x, P x = -3 * x ^ 2 + 72 * x - 240 := fun x => by rw [hP, hR', hC]; ring
  refine ⟨by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hp]; norm_num, hR', hP', fun x => ?_⟩
  rw [hP']
  constructor
  · intro h
    have : (x - 4) * (x - 20) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 1.5.50: for `C(x) = 20x + 1000` and `p(x) = 140 - 2x`: `C(0) = 1000`, the average cost of
10 scooters is `120`, `p(5) = 130`, `R(x) = -2x² + 140x`, `P(x) = -2x² + 120x - 1000`, and `P(x) = 0` at `x = 10` and
`x = 50`. -/
@[kb "stitzzeager2013" "Exercise 1.5.50, p. 98"]
theorem exer_1_5_50 (C p R P : ℝ → ℝ) (hC : ∀ x, C x = 20 * x + 1000) (hp : ∀ x, p x = 140 - 2 * x)
    (hR : ∀ x, R x = x * p x) (hP : ∀ x, P x = R x - C x) :
    C 0 = 1000 ∧ C 10 / 10 = 120 ∧ p 5 = 130 ∧ (∀ x, R x = -2 * x ^ 2 + 140 * x) ∧
      (∀ x, P x = -2 * x ^ 2 + 120 * x - 1000) ∧ (∀ x, P x = 0 ↔ x = 10 ∨ x = 50) := by
  have hR' : ∀ x, R x = -2 * x ^ 2 + 140 * x := fun x => by rw [hR, hp]; ring
  have hP' : ∀ x, P x = -2 * x ^ 2 + 120 * x - 1000 := fun x => by rw [hP, hR', hC]; ring
  refine ⟨by rw [hC]; norm_num, by rw [hC]; norm_num, by rw [hp]; norm_num, hR', hP', fun x => ?_⟩
  rw [hP']
  constructor
  · intro h
    have : (x - 10) * (x - 50) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-! ### Functions given by finite tables -/

/-- The function `f` of Exercises 51-62 (defined on `-3, ..., 3`; the value elsewhere is junk). -/
private def fT : ℤ → ℚ
  | -3 => 4 | -2 => 2 | -1 => 0 | 0 => 1 | 1 => 3 | 2 => 4 | 3 => -1 | _ => 0

/-- The function `g` of Exercises 51-62 (defined on `-3, ..., 3`; the value elsewhere is junk). -/
private def gT : ℤ → ℚ
  | -3 => -2 | -2 => 0 | -1 => -4 | 0 => 0 | 1 => -3 | 2 => 1 | 3 => 2 | _ => 0

/-- Stitz-Zeager Exercise 1.5.52: `(f - g)(2) = 3` for the tables of `f` and `g`. -/
@[kb "stitzzeager2013" "Exercise 1.5.52, p. 98"]
theorem exer_1_5_52 : (fT - gT) 2 = 3 := by
  simp [fT, gT]; norm_num

/-- Stitz-Zeager Exercise 1.5.53: `(fg)(-1) = 0` for the tables of `f` and `g`. -/
@[kb "stitzzeager2013" "Exercise 1.5.53, p. 98"]
theorem exer_1_5_53 : (fT * gT) (-1) = 0 := by
  simp [fT, gT]

/-- Stitz-Zeager Exercise 1.5.54: `(g + f)(1) = 0` for the tables of `f` and `g`. -/
@[kb "stitzzeager2013" "Exercise 1.5.54, p. 98"]
theorem exer_1_5_54 : (gT + fT) 1 = 0 := by
  simp [fT, gT]

/-- Stitz-Zeager Exercise 1.5.55: `(g - f)(3) = 3` for the tables of `f` and `g`. -/
@[kb "stitzzeager2013" "Exercise 1.5.55, p. 98"]
theorem exer_1_5_55 : (gT - fT) 3 = 3 := by
  simp [fT, gT]; norm_num

/-- Stitz-Zeager Exercise 1.5.58: `(f/g)(-1) = 0` for the tables of `f` and `g` (here `g(-1) = -4 ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 1.5.58, p. 98"]
theorem exer_1_5_58 : gT (-1) ≠ 0 ∧ (fT / gT) (-1) = 0 := by
  simp [fT, gT]

/-- Stitz-Zeager Exercise 1.5.60: `(g/f)(-1)` does not exist, because `f(-1) = 0` (while `g(-1) = -4`). -/
@[kb "stitzzeager2013" "Exercise 1.5.60, p. 98"]
theorem exer_1_5_60 : fT (-1) = 0 ∧ gT (-1) = -4 := by
  simp [fT, gT]

end UndergradKB.Precalculus.Course
