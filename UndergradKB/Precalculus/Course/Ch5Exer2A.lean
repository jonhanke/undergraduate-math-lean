import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.1 (values) -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 5.1: function composition, values -/

/-- Stitz-Zeager Exercise 5.1.2: for `f(x) = 4 - x`, `g(x) = 1 - x²` the six composition values. -/
@[kb "stitzzeager2013" "Exercise 5.1.2, p. 381"]
theorem exer_5_1_2 (f g : ℝ → ℝ) (hf : f = fun x => 4 - x) (hg : g = fun x => 1 - x ^ 2) :
    (g ∘ f) 0 = -15 ∧ (g ∘ f) (-3) = -48 ∧ (f ∘ g) (-1) = 4 ∧ (f ∘ g) (1 / 2) = 13 / 4 ∧
    (f ∘ f) 2 = 2 ∧ (f ∘ f) (-2) = -2 := by
  subst hf hg; norm_num [Function.comp]

/-- Stitz-Zeager Exercise 5.1.4: for `f(x) = |x - 1|`, `g(x) = x² - 5` the six composition values. -/
@[kb "stitzzeager2013" "Exercise 5.1.4, p. 381"]
theorem exer_5_1_4 (f g : ℝ → ℝ) (hf : f = fun x => |x - 1|) (hg : g = fun x => x ^ 2 - 5) :
    (g ∘ f) 0 = -4 ∧ (g ∘ f) (-3) = 11 ∧ (f ∘ g) (-1) = 5 ∧ (f ∘ g) (1 / 2) = 23 / 4 ∧
    (f ∘ f) 2 = 0 ∧ (f ∘ f) (-2) = 2 := by
  subst hf hg
  norm_num [Function.comp, abs_of_nonneg, abs_of_nonpos]

/-- Stitz-Zeager Exercise 5.1.5: for `f(x) = 4x + 5`, `g(x) = √x`: `(g∘f)(0) = √5`, `(g∘f)(-3)` and `(f∘g)(-1)`
are not real (negative radicands), `(f∘g)(1/2) = 5 + 2√2`, `(f∘f)(2) = 57`, `(f∘f)(-2) = -7`. -/
@[kb "stitzzeager2013" "Exercise 5.1.5, p. 381"]
theorem exer_5_1_5 (f g : ℝ → ℝ) (hf : f = fun x => 4 * x + 5) (hg : g = Real.sqrt) :
    (g ∘ f) 0 = Real.sqrt 5 ∧ f (-3) < 0 ∧ (-1 : ℝ) < 0 ∧ (f ∘ g) (1 / 2) = 5 + 2 * Real.sqrt 2 ∧
    (f ∘ f) 2 = 57 ∧ (f ∘ f) (-2) = -7 := by
  subst hf hg
  have h2 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [show (1 / 2 : ℝ) = 2 / 4 by norm_num, Real.sqrt_div (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨by norm_num [Function.comp], by norm_num, by norm_num, ?_, by norm_num [Function.comp],
    by norm_num [Function.comp]⟩
  simp only [Function.comp, h2]; ring

/-- Stitz-Zeager Exercise 5.1.7: for `f(x) = 6 - x - x²`, `g(x) = x√(x+10)`: `(g∘f)(0) = 24`, `(g∘f)(-3) = 0`,
`(f∘g)(-1) = 0`, `(f∘g)(1/2) = 27/8 - √42/4`, `(f∘f)(2) = 6`, `(f∘f)(-2) = -14`. -/
@[kb "stitzzeager2013" "Exercise 5.1.7, p. 381"]
theorem exer_5_1_7 (f g : ℝ → ℝ) (hf : f = fun x => 6 - x - x ^ 2)
    (hg : g = fun x => x * Real.sqrt (x + 10)) :
    (g ∘ f) 0 = 24 ∧ (g ∘ f) (-3) = 0 ∧ (f ∘ g) (-1) = 0 ∧
    (f ∘ g) (1 / 2) = 27 / 8 - Real.sqrt 42 / 4 ∧ (f ∘ f) 2 = 6 ∧ (f ∘ f) (-2) = -14 := by
  subst hf hg
  have h4 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h3 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h42 : Real.sqrt (1 / 2 + 10) = Real.sqrt 42 / 2 := by
    rw [show (1 / 2 + 10 : ℝ) = 42 / 4 by norm_num, Real.sqrt_div (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_, by norm_num [Function.comp], by norm_num [Function.comp]⟩
  · norm_num [Function.comp]; rw [h4]; norm_num
  · norm_num [Function.comp]
  · norm_num [Function.comp]; rw [h3]; norm_num
  · simp only [Function.comp, h42]
    have : Real.sqrt 42 ^ 2 = 42 := Real.sq_sqrt (by norm_num)
    nlinarith

/-- Stitz-Zeager Exercise 5.1.8: for `f(x) = ∛(x+1)` (real cube root), `g(x) = 4x² - x`: `(g∘f)(0) = 3`,
`(g∘f)(-3) = 4 ∛4 + ∛2`, `(f∘g)(-1) = ∛6`, `(f∘g)(1/2) = ∛12 / 2`, `(f∘f)(2) = ∛(∛3 + 1)`, `(f∘f)(-2) = 0`. -/
@[kb "stitzzeager2013" "Exercise 5.1.8, p. 381"]
theorem exer_5_1_8 (f g : ℝ → ℝ) (hf : f = fun x => UndergradKB.Precalculus.principalRoot 3 (x + 1))
    (hg : g = fun x => 4 * x ^ 2 - x) :
    (g ∘ f) 0 = 3 ∧
    (g ∘ f) (-3) = 4 * UndergradKB.Precalculus.principalRoot 3 4 + UndergradKB.Precalculus.principalRoot 3 2 ∧
    (f ∘ g) (-1) = UndergradKB.Precalculus.principalRoot 3 6 ∧
    (f ∘ g) (1 / 2) = UndergradKB.Precalculus.principalRoot 3 12 / 2 ∧
    (f ∘ f) 2 = UndergradKB.Precalculus.principalRoot 3 (UndergradKB.Precalculus.principalRoot 3 3 + 1) ∧
    (f ∘ f) (-2) = 0 := by
  subst hf hg
  have h3 : Odd 3 := by decide
  have one : UndergradKB.Precalculus.principalRoot 3 1 = 1 :=
    ((UndergradKB.Precalculus.principalRoot_eq_iff_odd h3 1 1).2 (by norm_num)).symm
  have m1 : UndergradKB.Precalculus.principalRoot 3 (-1) = -1 :=
    ((UndergradKB.Precalculus.principalRoot_eq_iff_odd h3 (-1) (-1)).2 (by norm_num)).symm
  have m2 : UndergradKB.Precalculus.principalRoot 3 (-2) = -UndergradKB.Precalculus.principalRoot 3 2 := by
    have := UndergradKB.Precalculus.principalRoot_mul (n := 3) (by norm_num) (x := -1) (y := 2) (Or.inl h3)
    rw [m1] at this; rw [show (-2 : ℝ) = -1 * 2 by norm_num, this]; ring
  have sq2 : UndergradKB.Precalculus.principalRoot 3 2 ^ 2 = UndergradKB.Precalculus.principalRoot 3 4 := by
    rw [← UndergradKB.Precalculus.principalRoot_pow_nat (by norm_num) 2 (Or.inl h3)]; norm_num
  have e12 : UndergradKB.Precalculus.principalRoot 3 (3 / 2 : ℝ) =
      UndergradKB.Precalculus.principalRoot 3 12 / 2 := by
    rw [show (3 / 2 : ℝ) = 12 / 8 by norm_num,
      UndergradKB.Precalculus.principalRoot_div (by norm_num) (by norm_num) (Or.inl h3)]
    have : UndergradKB.Precalculus.principalRoot 3 8 = 2 :=
      ((UndergradKB.Precalculus.principalRoot_eq_iff_odd h3 8 2).2 (by norm_num)).symm
    rw [this]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Function.comp, one]
  · norm_num [Function.comp, m2]; rw [sq2]
  · norm_num [Function.comp]
  · norm_num [Function.comp]; rw [← e12]
  · norm_num [Function.comp]
  · norm_num [Function.comp, m1]
    have := (UndergradKB.Precalculus.principalRoot_eq_iff_odd h3 0 0).2 (by norm_num)
    simpa using this.symm

/-- Stitz-Zeager Exercise 5.1.10: for `f(x) = x/(x+5)`, `g(x) = 2/(7-x²)` the six composition values. -/
@[kb "stitzzeager2013" "Exercise 5.1.10, p. 381"]
theorem exer_5_1_10 (f g : ℝ → ℝ) (hf : f = fun x => x / (x + 5)) (hg : g = fun x => 2 / (7 - x ^ 2)) :
    (g ∘ f) 0 = 2 / 7 ∧ (g ∘ f) (-3) = 8 / 19 ∧ (f ∘ g) (-1) = 1 / 16 ∧ (f ∘ g) (1 / 2) = 8 / 143 ∧
    (f ∘ f) 2 = 2 / 37 ∧ (f ∘ f) (-2) = -2 / 13 := by
  subst hf hg; norm_num [Function.comp]

/-- Stitz-Zeager Exercise 5.1.11: for `f(x) = 2x/(5-x²)`, `g(x) = √(4x+1)`: `(g∘f)(0) = 1`, `(g∘f)(-3) = √7`,
`(f∘g)(-1)` is not real (`4(-1)+1 < 0`), `(f∘g)(1/2) = √3`, `(f∘f)(2) = -8/11`, `(f∘f)(-2) = 8/11`. -/
@[kb "stitzzeager2013" "Exercise 5.1.11, p. 381"]
theorem exer_5_1_11 (f g : ℝ → ℝ) (hf : f = fun x => 2 * x / (5 - x ^ 2))
    (hg : g = fun x => Real.sqrt (4 * x + 1)) :
    (g ∘ f) 0 = 1 ∧ (g ∘ f) (-3) = Real.sqrt 7 ∧ 4 * (-1 : ℝ) + 1 < 0 ∧
    (f ∘ g) (1 / 2) = Real.sqrt 3 ∧ (f ∘ f) 2 = -8 / 11 ∧ (f ∘ f) (-2) = 8 / 11 := by
  subst hf hg
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨by norm_num [Function.comp], by norm_num [Function.comp], by norm_num, ?_,
    by norm_num [Function.comp], by norm_num [Function.comp]⟩
  simp only [Function.comp]
  rw [show (4 * (1 / 2 : ℝ) + 1) = 3 by norm_num, h3]; norm_num

/-- Stitz-Zeager Exercise 5.1.12: for `f(x) = √(2x+5)`, `g(x) = 10x/(x²+1)`: `(g∘f)(0) = 5√5/3`, `(g∘f)(-3)`
and `(f∘g)(-1)` are not real (`2(-3)+5 < 0`, `2(-5)+5 < 0`), `(f∘g)(1/2) = √13`, `(f∘f)(2) = √11`,
`(f∘f)(-2) = √7`. -/
@[kb "stitzzeager2013" "Exercise 5.1.12, p. 381"]
theorem exer_5_1_12 (f g : ℝ → ℝ) (hf : f = fun x => Real.sqrt (2 * x + 5))
    (hg : g = fun x => 10 * x / (x ^ 2 + 1)) :
    (g ∘ f) 0 = 5 * Real.sqrt 5 / 3 ∧ 2 * (-3 : ℝ) + 5 < 0 ∧ 2 * g (-1) + 5 < 0 ∧
    (f ∘ g) (1 / 2) = Real.sqrt 13 ∧ (f ∘ f) 2 = Real.sqrt 11 ∧ (f ∘ f) (-2) = Real.sqrt 7 := by
  subst hf hg
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · simp only [Function.comp]
    rw [show (2 * (0 : ℝ) + 5) = 5 by norm_num, h5]; ring
  · norm_num [Function.comp]
  · have h9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    norm_num [Function.comp, h9]
  · norm_num [Function.comp]

/-! ## Section 5.1: function composition, formulas and domains -/

/-- Stitz-Zeager Exercise 5.1.14: for `f(x) = x²-x+1`, `g(x) = 3x-5`, all three compositions are polynomials
on `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.14, p. 381"]
theorem exer_5_1_14 (f g : ℝ → ℝ) (hf : f = fun x => x ^ 2 - x + 1) (hg : g = fun x => 3 * x - 5) :
    (∀ x, (g ∘ f) x = 3 * x ^ 2 - 3 * x - 2) ∧ (∀ x, (f ∘ g) x = 9 * x ^ 2 - 33 * x + 31) ∧
    (∀ x, (f ∘ f) x = x ^ 4 - 2 * x ^ 3 + 2 * x ^ 2 - x + 1) := by
  subst hf hg
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩ <;> simp only [Function.comp] <;> ring

/-- Stitz-Zeager Exercise 5.1.15: for `f(x) = x²-4`, `g(x) = |x|`: `(g∘f)(x) = |x²-4|`, `(f∘g)(x) = x²-4`,
`(f∘f)(x) = x⁴-8x²+12`, all on `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.15, p. 381"]
theorem exer_5_1_15 (f g : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 4) (hg : g = fun x => |x|) :
    (∀ x, (g ∘ f) x = |x ^ 2 - 4|) ∧ (∀ x, (f ∘ g) x = x ^ 2 - 4) ∧
    (∀ x, (f ∘ f) x = x ^ 4 - 8 * x ^ 2 + 12) := by
  subst hf hg
  refine ⟨fun x => rfl, fun x => ?_, fun x => ?_⟩ <;> simp only [Function.comp, sq_abs] <;> ring

/-- Stitz-Zeager Exercise 5.1.17: for `f(x) = |x+1|`, `g(x) = √x`: `(g∘f)(x) = √|x+1|` on `ℝ`,
`(f∘g)(x) = √x + 1` on `[0, ∞)`, `(f∘f)(x) = |x+1| + 1` on `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.17, p. 381"]
theorem exer_5_1_17 (f g : ℝ → ℝ) (hf : f = fun x => |x + 1|) (hg : g = Real.sqrt) :
    (∀ x, (g ∘ f) x = Real.sqrt |x + 1|) ∧ (∀ x : ℝ, 0 ≤ x → (f ∘ g) x = Real.sqrt x + 1) ∧
    (∀ x, (f ∘ f) x = |x + 1| + 1) := by
  subst hf hg
  refine ⟨fun x => rfl, fun x hx => ?_, fun x => ?_⟩
  · simp only [Function.comp]; exact abs_of_nonneg (by positivity)
  · simp only [Function.comp]; rw [abs_of_nonneg (by positivity)]

end UndergradKB.Precalculus.Course
