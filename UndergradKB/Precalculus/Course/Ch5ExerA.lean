import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Function.Iterate
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers, Sections 5.1 and 5.2 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 5.1: function composition -/

/-- Stitz-Zeager Exercise 5.1.1: for `f(x) = x²`, `g(x) = 2x+1`: `(g∘f)(0) = 1`, `(g∘f)(-3) = 19`, `(f∘g)(-1) = 1`,
`(f∘g)(1/2) = 4`, `(f∘f)(2) = 16`, `(f∘f)(-2) = 16`. -/
@[kb "stitzzeager2013" "Exercise 5.1.1, p. 381"]
theorem exer_5_1_1 :
    ((fun x : ℝ => 2 * x + 1) ∘ (fun x : ℝ => x ^ 2)) 0 = 1 ∧
    ((fun x : ℝ => 2 * x + 1) ∘ (fun x : ℝ => x ^ 2)) (-3) = 19 ∧
    ((fun x : ℝ => x ^ 2) ∘ (fun x : ℝ => 2 * x + 1)) (-1) = 1 ∧
    ((fun x : ℝ => x ^ 2) ∘ (fun x : ℝ => 2 * x + 1)) (1 / 2) = 4 ∧
    ((fun x : ℝ => x ^ 2) ∘ (fun x : ℝ => x ^ 2)) 2 = 16 ∧
    ((fun x : ℝ => x ^ 2) ∘ (fun x : ℝ => x ^ 2)) (-2) = 16 := by
  norm_num [Function.comp]

/-- Stitz-Zeager Exercise 5.1.3: for `f(x) = 4 - 3x`, `g(x) = |x|`: `(g∘f)(0) = 4`, `(g∘f)(-3) = 13`,
`(f∘g)(-1) = 1`, `(f∘g)(1/2) = 5/2`, `(f∘f)(2) = 10`, `(f∘f)(-2) = -26`. -/
@[kb "stitzzeager2013" "Exercise 5.1.3, p. 381"]
theorem exer_5_1_3 :
    ((fun x : ℝ => |x|) ∘ (fun x : ℝ => 4 - 3 * x)) 0 = 4 ∧
    ((fun x : ℝ => |x|) ∘ (fun x : ℝ => 4 - 3 * x)) (-3) = 13 ∧
    ((fun x : ℝ => 4 - 3 * x) ∘ (fun x : ℝ => |x|)) (-1) = 1 ∧
    ((fun x : ℝ => 4 - 3 * x) ∘ (fun x : ℝ => |x|)) (1 / 2) = 5 / 2 ∧
    ((fun x : ℝ => 4 - 3 * x) ∘ (fun x : ℝ => 4 - 3 * x)) 2 = 10 ∧
    ((fun x : ℝ => 4 - 3 * x) ∘ (fun x : ℝ => 4 - 3 * x)) (-2) = -26 := by
  norm_num [Function.comp, abs_of_nonneg]

/-- Stitz-Zeager Exercise 5.1.6: for `f(x) = √(3-x)`, `g(x) = x²+1`: `(g∘f)(0) = 4`, `(g∘f)(-3) = 7`,
`(f∘g)(-1) = 1`, `(f∘g)(1/2) = √7/2`, `(f∘f)(2) = √2`, `(f∘f)(-2) = √(3-√5)`. -/
@[kb "stitzzeager2013" "Exercise 5.1.6, p. 381"]
theorem exer_5_1_6 :
    ((fun x : ℝ => x ^ 2 + 1) ∘ (fun x : ℝ => Real.sqrt (3 - x))) 0 = 4 ∧
    ((fun x : ℝ => x ^ 2 + 1) ∘ (fun x : ℝ => Real.sqrt (3 - x))) (-3) = 7 ∧
    ((fun x : ℝ => Real.sqrt (3 - x)) ∘ (fun x : ℝ => x ^ 2 + 1)) (-1) = 1 ∧
    ((fun x : ℝ => Real.sqrt (3 - x)) ∘ (fun x : ℝ => x ^ 2 + 1)) (1 / 2) = Real.sqrt 7 / 2 ∧
    ((fun x : ℝ => Real.sqrt (3 - x)) ∘ (fun x : ℝ => Real.sqrt (3 - x))) 2 = Real.sqrt 2 ∧
    ((fun x : ℝ => Real.sqrt (3 - x)) ∘ (fun x : ℝ => Real.sqrt (3 - x))) (-2) =
      Real.sqrt (3 - Real.sqrt 5) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp]
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  · simp only [Function.comp]
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  · simp only [Function.comp]
    norm_num
  · simp only [Function.comp]
    rw [show (3 : ℝ) - ((1 / 2) ^ 2 + 1) = 7 / 4 by norm_num, Real.sqrt_div (by norm_num), h4]
  · simp only [Function.comp]
    rw [show (3 : ℝ) - 2 = 1 by norm_num, Real.sqrt_one]; norm_num
  · simp only [Function.comp]
    norm_num

/-- Stitz-Zeager Exercise 5.1.9: for `f(x) = 3/(1-x)`, `g(x) = 4x/(x²+1)`: `(g∘f)(0) = 6/5`, `(g∘f)(-3) = 48/25`,
`(f∘g)(-1) = 1`, `(f∘g)(1/2) = -5`, `(f∘f)(2) = 3/4`; and `(f∘f)(-2)` is undefined since `f(-2) = 1`. -/
@[kb "stitzzeager2013" "Exercise 5.1.9, p. 381"]
theorem exer_5_1_9 :
    ((fun x : ℝ => 4 * x / (x ^ 2 + 1)) ∘ (fun x : ℝ => 3 / (1 - x))) 0 = 6 / 5 ∧
    ((fun x : ℝ => 4 * x / (x ^ 2 + 1)) ∘ (fun x : ℝ => 3 / (1 - x))) (-3) = 48 / 25 ∧
    ((fun x : ℝ => 3 / (1 - x)) ∘ (fun x : ℝ => 4 * x / (x ^ 2 + 1))) (-1) = 1 ∧
    ((fun x : ℝ => 3 / (1 - x)) ∘ (fun x : ℝ => 4 * x / (x ^ 2 + 1))) (1 / 2) = -5 ∧
    ((fun x : ℝ => 3 / (1 - x)) ∘ (fun x : ℝ => 3 / (1 - x))) 2 = 3 / 4 ∧
    (3 / (1 - (-2 : ℝ)) = 1 ∧ (1 : ℝ) - 1 = 0) := by
  norm_num [Function.comp]

/-- Stitz-Zeager Exercise 5.1.13: for `f(x) = 2x+3`, `g(x) = x²-9` all three compositions are defined on `ℝ`:
`(g∘f)(x) = 4x²+12x`, `(f∘g)(x) = 2x²-15`, `(f∘f)(x) = 4x+9`. -/
@[kb "stitzzeager2013" "Exercise 5.1.13, p. 381"]
theorem exer_5_1_13 (x : ℝ) :
    ((fun x : ℝ => x ^ 2 - 9) ∘ (fun x : ℝ => 2 * x + 3)) x = 4 * x ^ 2 + 12 * x ∧
    ((fun x : ℝ => 2 * x + 3) ∘ (fun x : ℝ => x ^ 2 - 9)) x = 2 * x ^ 2 - 15 ∧
    ((fun x : ℝ => 2 * x + 3) ∘ (fun x : ℝ => 2 * x + 3)) x = 4 * x + 9 := by
  simp only [Function.comp]
  refine ⟨by ring, by ring, by ring⟩

/-- Stitz-Zeager Exercise 5.1.16: for `f(x) = 3x-5`, `g(x) = √x`: `(g∘f)(x) = √(3x-5)` is defined exactly on
`[5/3, ∞)`, `(f∘g)(x) = 3√x - 5` on `[0, ∞)`, and `(f∘f)(x) = 9x - 20` on all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.16, p. 381"]
theorem exer_5_1_16 :
    {x : ℝ | 0 ≤ 3 * x - 5} = Ici (5 / 3) ∧
    ((fun x : ℝ => 3 * x - 5) ∘ Real.sqrt) 4 = 1 ∧
    (∀ x : ℝ, ((fun x : ℝ => 3 * x - 5) ∘ (fun x : ℝ => 3 * x - 5)) x = 9 * x - 20) := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Ici]
    constructor <;> intro h <;> linarith
  · simp only [Function.comp]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
  · simp only [Function.comp]; ring

/-- Stitz-Zeager Exercise 5.1.18: for `f(x) = 3 - x²`, `g(x) = √(x+1)`: `(g∘f)(x) = √(4-x²)` has domain `[-2, 2]`;
`(f∘g)(x) = 2 - x` on `[-1, ∞)`; `(f∘f)(x) = -x⁴ + 6x² - 6` on `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.18, p. 381"]
theorem exer_5_1_18 :
    {x : ℝ | 0 ≤ (3 - x ^ 2) + 1} = Icc (-2) 2 ∧
    (∀ x : ℝ, -1 ≤ x → ((fun x : ℝ => 3 - x ^ 2) ∘ (fun x : ℝ => Real.sqrt (x + 1))) x = 2 - x) ∧
    (∀ x : ℝ, ((fun x : ℝ => 3 - x ^ 2) ∘ (fun x : ℝ => 3 - x ^ 2)) x = -x ^ 4 + 6 * x ^ 2 - 6) := by
  refine ⟨?_, fun x hx => ?_, fun x => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Icc]
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      nlinarith
  · simp only [Function.comp]
    rw [Real.sq_sqrt (by linarith)]; ring
  · simp only [Function.comp]; ring

/-- Stitz-Zeager Exercise 5.1.19: for `f(x) = |x|`, `g(x) = √(4-x)`: `(g∘f)(x) = √(4-|x|)` has domain `[-4, 4]`;
`(f∘g)(x) = |√(4-x)| = √(4-x)` has domain `(-∞, 4]`; `(f∘f)(x) = |x|` on `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.19, p. 381"]
theorem exer_5_1_19 :
    {x : ℝ | 0 ≤ 4 - |x|} = Icc (-4) 4 ∧
    (∀ x : ℝ, |Real.sqrt (4 - x)| = Real.sqrt (4 - x)) ∧
    {x : ℝ | 0 ≤ 4 - x} = Iic 4 ∧
    (∀ x : ℝ, ((fun x : ℝ => |x|) ∘ (fun x : ℝ => |x|)) x = |x|) := by
  refine ⟨?_, fun x => abs_of_nonneg (Real.sqrt_nonneg _), ?_, fun x => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Icc]
    rw [← abs_le]
    constructor <;> intro h <;> linarith
  · ext x
    simp only [mem_ofPred_eq, mem_Iic]
    constructor <;> intro h <;> linarith
  · simp only [Function.comp, abs_abs]

/-- Stitz-Zeager Exercise 5.1.20: for `f(x) = x²-x-1`, `g(x) = √(x-5)`: `(g∘f)(x) = √(x²-x-6)` is defined exactly on
`(-∞,-2] ∪ [3,∞)`; `(f∘g)(x) = x - 6 - √(x-5)` for `x ≥ 5`; `(f∘f)(x) = x⁴-2x³-2x²+3x+1` on `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.20, p. 381"]
theorem exer_5_1_20 :
    {x : ℝ | 0 ≤ (x ^ 2 - x - 1) - 5} = Iic (-2) ∪ Ici 3 ∧
    (∀ x : ℝ, 5 ≤ x → ((fun x : ℝ => x ^ 2 - x - 1) ∘ (fun x : ℝ => Real.sqrt (x - 5))) x =
      x - 6 - Real.sqrt (x - 5)) ∧
    (∀ x : ℝ, ((fun x : ℝ => x ^ 2 - x - 1) ∘ (fun x : ℝ => x ^ 2 - x - 1)) x =
      x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 + 3 * x + 1) := by
  refine ⟨?_, fun x hx => ?_, fun x => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [hc.1, hc.2]
    · rintro (h | h) <;> nlinarith
  · simp only [Function.comp]
    rw [Real.sq_sqrt (by linarith)]
    ring
  · simp only [Function.comp]; ring

/-- Stitz-Zeager Exercise 5.1.21: for `f(x) = 3x-1`, `g(x) = 1/(x+3)`: `(g∘f)(x) = 1/(3x+2)` is defined exactly for
`x ≠ -2/3`; `(f∘g)(x) = -x/(x+3)` for `x ≠ -3`; `(f∘f)(x) = 9x-4` on `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 5.1.21, p. 381"]
theorem exer_5_1_21 :
    {x : ℝ | 3 * x - 1 + 3 ≠ 0} = {-2 / 3}ᶜ ∧
    (∀ x : ℝ, ((fun x : ℝ => 1 / (x + 3)) ∘ (fun x : ℝ => 3 * x - 1)) x = 1 / (3 * x + 2)) ∧
    (∀ x : ℝ, x + 3 ≠ 0 → ((fun x : ℝ => 3 * x - 1) ∘ (fun x : ℝ => 1 / (x + 3))) x = -x / (x + 3)) ∧
    (∀ x : ℝ, ((fun x : ℝ => 3 * x - 1) ∘ (fun x : ℝ => 3 * x - 1)) x = 9 * x - 4) := by
  refine ⟨?_, fun x => ?_, fun x hx => ?_, fun x => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
    constructor
    · intro h h'; apply h; rw [h']; norm_num
    · intro h h'; apply h; linarith
  · simp only [Function.comp]; ring_nf
  · simp only [Function.comp]
    field_simp
    ring
  · simp only [Function.comp]; ring

/-- Stitz-Zeager Exercise 5.1.22: for `f(x) = 3x/(x-1)`, `g(x) = x/(x-3)`: `(g∘f)(x) = x` for `x ≠ 1`,
`(f∘g)(x) = x` for `x ≠ 3`, and `(f∘f)(x) = 9x/(2x+1)` for `x ≠ 1`, `x ≠ -1/2`. -/
@[kb "stitzzeager2013" "Exercise 5.1.22, p. 381"]
theorem exer_5_1_22 :
    (∀ x : ℝ, x ≠ 1 → ((fun x : ℝ => x / (x - 3)) ∘ (fun x : ℝ => 3 * x / (x - 1))) x = x) ∧
    (∀ x : ℝ, x ≠ 3 → ((fun x : ℝ => 3 * x / (x - 1)) ∘ (fun x : ℝ => x / (x - 3))) x = x) ∧
    (∀ x : ℝ, x ≠ 1 → x ≠ -1 / 2 →
      ((fun x : ℝ => 3 * x / (x - 1)) ∘ (fun x : ℝ => 3 * x / (x - 1))) x = 9 * x / (2 * x + 1)) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx hx2 => ?_⟩
  · have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    simp only [Function.comp]
    field_simp
    ring
  · have h1 : x - 3 ≠ 0 := sub_ne_zero.mpr hx
    simp only [Function.comp]
    field_simp
    ring
  · have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have h2 : 2 * x + 1 ≠ 0 := fun h => hx2 (by linarith)
    simp only [Function.comp]
    field_simp
    ring

/-- Stitz-Zeager Exercise 5.1.25: for `f(x) = -2x`, `g(x) = √x`, `h(x) = |x|`: `(h∘g∘f)(x) = |√(-2x)| = √(-2x)` with
domain `(-∞, 0]`. -/
@[kb "stitzzeager2013" "Exercise 5.1.25, p. 382"]
theorem exer_5_1_25 :
    {x : ℝ | 0 ≤ -2 * x} = Iic 0 ∧
    ∀ x : ℝ, ((fun x : ℝ => |x|) ∘ Real.sqrt ∘ (fun x : ℝ => -2 * x)) x = Real.sqrt (-2 * x) := by
  refine ⟨?_, fun x => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Iic]
    constructor <;> intro h <;> linarith
  · simp only [Function.comp]
    exact abs_of_nonneg (Real.sqrt_nonneg _)

/-- Stitz-Zeager Exercise 5.1.27: for `f(x) = -2x`, `g(x) = √x`, `h(x) = |x|`: `(g∘f∘h)(x) = √(-2|x|)` is defined
only at `x = 0`. -/
@[kb "stitzzeager2013" "Exercise 5.1.27, p. 382"]
theorem exer_5_1_27 : {x : ℝ | 0 ≤ -2 * |x|} = {0} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro h
    have : |x| ≤ 0 := by linarith
    exact abs_nonpos_iff.mp this
  · rintro rfl; simp

/-- Stitz-Zeager Exercise 5.1.29: for `f(x) = -2x`, `g(x) = √x`, `h(x) = |x|`: `(f∘h∘g)(x) = -2|√x| = -2√x` with
domain `[0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.1.29, p. 382"]
theorem exer_5_1_29 :
    {x : ℝ | 0 ≤ x} = Ici 0 ∧
    ∀ x : ℝ, ((fun x : ℝ => -2 * x) ∘ (fun x : ℝ => |x|) ∘ Real.sqrt) x = -2 * Real.sqrt x := by
  refine ⟨rfl, fun x => ?_⟩
  simp only [Function.comp]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Stitz-Zeager Exercise 5.1.43: `F(x) = -(1/2)(2x-7)³ + 1` is the composition of `g(x) = 2x`, `h(x) = x - 7`,
`f(x) = x³`, `j(x) = -x/2`, `k(x) = x + 1`, applied in that order. -/
@[kb "stitzzeager2013" "Exercise 5.1.43, p. 382"]
theorem exer_5_1_43 (x : ℝ) :
    ((fun x : ℝ => x + 1) ∘ (fun x : ℝ => -1 / 2 * x) ∘ (fun x : ℝ => x ^ 3) ∘ (fun x : ℝ => x - 7) ∘
      (fun x : ℝ => 2 * x)) x = -1 / 2 * (2 * x - 7) ^ 3 + 1 := by
  simp only [Function.comp]

/-- Stitz-Zeager Exercise 5.1.55: if `g(0) = 0`, then the `n`-fold composite `g ∘ g ∘ ⋯ ∘ g` sends `0` to `0` for
every `n` (the book's `g` has `g(0) = 0`). -/
@[kb "stitzzeager2013" "Exercise 5.1.55, p. 383"]
theorem exer_5_1_55 (g : ℤ → ℤ) (h : g 0 = 0) (n : ℕ) : g^[n] 0 = 0 :=
  Function.iterate_fixed h n

/-- Stitz-Zeager Exercise 5.1.63: with revenue `R(x) = 2x` per hour from `x(t) = -4t²+20t+92` hot dogs per hour,
`(R∘x)(t) = -8t²+40t+184`, and at noon (`t = 2`) the revenue is `232` dollars per hour. -/
@[kb "stitzzeager2013" "Exercise 5.1.63, p. 383"]
theorem exer_5_1_63 :
    (∀ t : ℝ, ((fun x : ℝ => 2 * x) ∘ (fun t : ℝ => -4 * t ^ 2 + 20 * t + 92)) t = -8 * t ^ 2 + 40 * t + 184) ∧
    ((fun x : ℝ => 2 * x) ∘ (fun t : ℝ => -4 * t ^ 2 + 20 * t + 92)) 2 = 232 := by
  refine ⟨fun t => ?_, ?_⟩
  · simp only [Function.comp]; ring
  · norm_num [Function.comp]

end UndergradKB.Precalculus.Course
