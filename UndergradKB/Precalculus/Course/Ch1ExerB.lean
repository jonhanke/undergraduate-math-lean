import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers, Section 1.4 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 1.4 -/

/-- Stitz-Zeager Exercise 1.4.4: doubling, adding `3`, then taking the square root gives `√(2x+3)`, defined exactly
on `[-3/2, ∞)`; for instance the value at `3` is `3`. -/
@[kb "stitzzeager2013" "Exercise 1.4.4, p. 75"]
theorem exer_1_4_4 : {x : ℝ | 0 ≤ 2 * x + 3} = Ici (-3 / 2) ∧ √(2 * 3 + 3 : ℝ) = 3 := by
  refine ⟨?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith
  · rw [show (2 * 3 + 3 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

/-- Stitz-Zeager Exercise 1.4.7: `4 / (√x - 13)` is defined exactly on `[0,169) ∪ (169,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.7, p. 75"]
theorem exer_1_4_7 : {x : ℝ | 0 ≤ x ∧ √x - 13 ≠ 0} = Ico 0 169 ∪ Ioi 169 := by
  have key : ∀ x : ℝ, 0 ≤ x → (√x = 13 ↔ x = 169) := by
    intro x hx
    rw [Real.sqrt_eq_iff_mul_self_eq hx (by norm_num)]
    constructor <;> intro h <;> linarith
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ico, mem_Ioi, ne_eq, sub_eq_zero]
  constructor
  · rintro ⟨h0, h⟩
    have : x ≠ 169 := fun h' => h ((key x h0).2 h')
    rcases lt_or_gt_of_ne this with h1 | h1
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr h1
  · rintro (⟨h0, h1⟩ | h1)
    · exact ⟨h0, fun h => by have := (key x h0).1 h; linarith⟩
    · have h0 : 0 ≤ x := by linarith
      exact ⟨h0, fun h => by have := (key x h0).1 h; linarith⟩

/-- Stitz-Zeager Exercise 1.4.8: `4 / √(x - 13)` is defined exactly on `(13, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.8, p. 75"]
theorem exer_1_4_8 : {x : ℝ | 0 ≤ x - 13 ∧ √(x - 13) ≠ 0} = Ioi 13 := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioi, ne_eq, Real.sqrt_eq_zero']
  constructor
  · rintro ⟨h0, h⟩; push Not at h; linarith
  · intro h; exact ⟨by linarith, by push Not; linarith⟩

/-- Stitz-Zeager Exercise 1.4.9: `4 / √x - 13` is defined exactly on `(0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.9, p. 75"]
theorem exer_1_4_9 : {x : ℝ | 0 ≤ x ∧ √x ≠ 0} = Ioi 0 := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioi, ne_eq, Real.sqrt_eq_zero']
  constructor
  · rintro ⟨h0, h⟩; push Not at h; exact h
  · intro h; exact ⟨h.le, by push Not; exact h⟩

/-- Stitz-Zeager Exercise 1.4.11: for `f(x) = 2x + 1`, the nine requested values and simplifications. -/
@[kb "stitzzeager2013" "Exercise 1.4.11, p. 76"]
theorem exer_1_4_11 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x + 1) :
    f 3 = 7 ∧ f (-1) = -1 ∧ f (3 / 2) = 4 ∧ (∀ x, f (4 * x) = 8 * x + 1) ∧
      (∀ x, 4 * f x = 8 * x + 4) ∧ (∀ x, f (-x) = -2 * x + 1) ∧ (∀ x, f (x - 4) = 2 * x - 7) ∧
      (∀ x, f x - 4 = 2 * x - 3) ∧ (∀ x, f (x ^ 2) = 2 * x ^ 2 + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hf] <;> first | (intro x; ring) | norm_num

/-- Stitz-Zeager Exercise 1.4.12: for `f(x) = 3 - 4x`, the nine requested values and simplifications. -/
@[kb "stitzzeager2013" "Exercise 1.4.12, p. 76"]
theorem exer_1_4_12 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 - 4 * x) :
    f 3 = -9 ∧ f (-1) = 7 ∧ f (3 / 2) = -3 ∧ (∀ x, f (4 * x) = 3 - 16 * x) ∧
      (∀ x, 4 * f x = 12 - 16 * x) ∧ (∀ x, f (-x) = 4 * x + 3) ∧ (∀ x, f (x - 4) = 19 - 4 * x) ∧
      (∀ x, f x - 4 = -4 * x - 1) ∧ (∀ x, f (x ^ 2) = 3 - 4 * x ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hf] <;> first | (intro x; ring) | norm_num

/-- Stitz-Zeager Exercise 1.4.13: for `f(x) = 2 - x²`, the nine requested values and simplifications. -/
@[kb "stitzzeager2013" "Exercise 1.4.13, p. 76"]
theorem exer_1_4_13 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 - x ^ 2) :
    f 3 = -7 ∧ f (-1) = 1 ∧ f (3 / 2) = -1 / 4 ∧ (∀ x, f (4 * x) = 2 - 16 * x ^ 2) ∧
      (∀ x, 4 * f x = 8 - 4 * x ^ 2) ∧ (∀ x, f (-x) = 2 - x ^ 2) ∧
      (∀ x, f (x - 4) = -x ^ 2 + 8 * x - 14) ∧ (∀ x, f x - 4 = -x ^ 2 - 2) ∧
      (∀ x, f (x ^ 2) = 2 - x ^ 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hf] <;> first | (intro x; ring) | norm_num

/-- Stitz-Zeager Exercise 1.4.14: for `f(x) = x² - 3x + 2`, the nine requested values and simplifications. -/
@[kb "stitzzeager2013" "Exercise 1.4.14, p. 76"]
theorem exer_1_4_14 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - 3 * x + 2) :
    f 3 = 2 ∧ f (-1) = 6 ∧ f (3 / 2) = -1 / 4 ∧ (∀ x, f (4 * x) = 16 * x ^ 2 - 12 * x + 2) ∧
      (∀ x, 4 * f x = 4 * x ^ 2 - 12 * x + 8) ∧ (∀ x, f (-x) = x ^ 2 + 3 * x + 2) ∧
      (∀ x, f (x - 4) = x ^ 2 - 11 * x + 30) ∧ (∀ x, f x - 4 = x ^ 2 - 3 * x - 2) ∧
      (∀ x, f (x ^ 2) = x ^ 4 - 3 * x ^ 2 + 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hf] <;> first | (intro x; ring) | norm_num

/-- Stitz-Zeager Exercise 1.4.15: for `f(x) = x / (x - 1)`, the nine requested values and simplifications, each
for the `x` where the expressions are defined. -/
@[kb "stitzzeager2013" "Exercise 1.4.15, p. 76"]
theorem exer_1_4_15 (f : ℝ → ℝ) (hf : ∀ x, f x = x / (x - 1)) :
    f 3 = 3 / 2 ∧ f (-1) = 1 / 2 ∧ f (3 / 2) = 3 ∧
      (∀ x, 4 * x - 1 ≠ 0 → f (4 * x) = 4 * x / (4 * x - 1)) ∧
      (∀ x, x - 1 ≠ 0 → 4 * f x = 4 * x / (x - 1)) ∧
      (∀ x, x + 1 ≠ 0 → f (-x) = x / (x + 1)) ∧
      (∀ x, x - 5 ≠ 0 → f (x - 4) = (x - 4) / (x - 5)) ∧
      (∀ x, x - 1 ≠ 0 → f x - 4 = (4 - 3 * x) / (x - 1)) ∧
      (∀ x, x ^ 2 - 1 ≠ 0 → f (x ^ 2) = x ^ 2 / (x ^ 2 - 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · intro x _; simp only [hf]
  · intro x _; simp only [hf]; ring
  · intro x h; simp only [hf]
    have : -x - 1 = -(x + 1) := by ring
    rw [this, neg_div_neg_eq]
  · intro x _; simp only [hf]; ring_nf
  · intro x h; simp only [hf]; field_simp; ring
  · intro x _; simp only [hf]

/-- Stitz-Zeager Exercise 1.4.16: for `f(x) = 2 / x³`, the requested values and simplifications (for nonzero
arguments). -/
@[kb "stitzzeager2013" "Exercise 1.4.16, p. 76"]
theorem exer_1_4_16 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 / x ^ 3) :
    f 3 = 2 / 27 ∧ f (-1) = -2 ∧ f (3 / 2) = 16 / 27 ∧
      (∀ x, x ≠ 0 → f (4 * x) = 1 / (32 * x ^ 3)) ∧ (∀ x, x ≠ 0 → 4 * f x = 8 / x ^ 3) ∧
      (∀ x, x ≠ 0 → f (-x) = -(2 / x ^ 3)) ∧ (∀ x, x ≠ 0 → f x - 4 = (2 - 4 * x ^ 3) / x ^ 3) ∧
      (∀ x, x ≠ 0 → f (x ^ 2) = 2 / x ^ 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · intro x hx; simp only [hf]; field_simp; ring
  · intro x hx; simp only [hf]; ring
  · intro x hx; simp only [hf]; field_simp
  · intro x hx; simp only [hf]; field_simp
  · intro x hx; simp only [hf]; field_simp

/-- Stitz-Zeager Exercise 1.4.17: the constant function `f(x) = 6` has value `6` everywhere, so `f(3) = 6`,
`4 f(x) = 24` and `f(x) - 4 = 2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.17, p. 76"]
theorem exer_1_4_17 (f : ℝ → ℝ) (hf : ∀ x, f x = 6) :
    f 3 = 6 ∧ f (3 / 2) = 6 ∧ (∀ x, f (4 * x) = 6) ∧ (∀ x, 4 * f x = 24) ∧ (∀ x, f x - 4 = 2) ∧
      (∀ x, f (x ^ 2) = 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hf] <;> first | (intro x; norm_num) | norm_num

/-- Stitz-Zeager Exercise 1.4.19: for `f(x) = 2x - 5` the requested values with a symbolic argument. -/
@[kb "stitzzeager2013" "Exercise 1.4.19, p. 76"]
theorem exer_1_4_19 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x - 5) :
    f 2 = -1 ∧ f (-2) = -9 ∧ (∀ a, f (2 * a) = 4 * a - 5) ∧ (∀ a, 2 * f a = 4 * a - 10) ∧
      (∀ a, f (a + 2) = 2 * a - 1) ∧ (∀ a, f a + f 2 = 2 * a - 6) ∧
      (∀ a, a ≠ 0 → f (2 / a) = 4 / a - 5) ∧ (∀ a, f a / 2 = (2 * a - 5) / 2) ∧
      (∀ a h, f (a + h) = 2 * a + 2 * h - 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · intro a; simp only [hf]; ring
  · intro a; simp only [hf]; ring
  · intro a; simp only [hf]; ring
  · intro a; simp only [hf]; ring
  · intro a ha; simp only [hf]; field_simp; ring
  · intro a; simp only [hf]
  · intro a h; simp only [hf]; ring

/-- Stitz-Zeager Exercise 1.4.22: for `f(x) = 3x² + 3x - 2` the requested values with a symbolic argument. -/
@[kb "stitzzeager2013" "Exercise 1.4.22, p. 76"]
theorem exer_1_4_22 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * x ^ 2 + 3 * x - 2) :
    f 2 = 16 ∧ f (-2) = 4 ∧ (∀ a, f (2 * a) = 12 * a ^ 2 + 6 * a - 2) ∧
      (∀ a, 2 * f a = 6 * a ^ 2 + 6 * a - 4) ∧ (∀ a, f (a + 2) = 3 * a ^ 2 + 15 * a + 16) ∧
      (∀ a, f a + f 2 = 3 * a ^ 2 + 3 * a + 14) ∧
      (∀ a, a ≠ 0 → f (2 / a) = 12 / a ^ 2 + 6 / a - 2) ∧
      (∀ a h, f (a + h) = 3 * a ^ 2 + 6 * a * h + 3 * h ^ 2 + 3 * a + 3 * h - 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · intro a; simp only [hf]; ring
  · intro a; simp only [hf]; ring
  · intro a; simp only [hf]; ring
  · intro a; simp only [hf]; ring
  · intro a ha; simp only [hf]; field_simp; ring
  · intro a h; simp only [hf]; ring

/-- Stitz-Zeager Exercise 1.4.23: for `f(x) = √(2x+1)`, `f(2) = √5`, `f(-2)` is not a real value (the radicand is
negative), `f(2a) = √(4a+1)` and `f(a+h) = √(2a+2h+1)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.23, p. 76"]
theorem exer_1_4_23 (f : ℝ → ℝ) (hf : ∀ x, f x = √(2 * x + 1)) :
    f 2 = √5 ∧ 2 * (-2 : ℝ) + 1 < 0 ∧ (∀ a, f (2 * a) = √(4 * a + 1)) ∧
      (∀ a, 2 * f a = 2 * √(2 * a + 1)) ∧ (∀ a, f (a + 2) = √(2 * a + 5)) ∧
      (∀ a h, f (a + h) = √(2 * a + 2 * h + 1)) := by
  refine ⟨?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · simp only [hf]; norm_num
  · intro a; simp only [hf]; ring_nf
  · intro a; simp only [hf]
  · intro a; simp only [hf]; ring_nf
  · intro a h; simp only [hf]; ring_nf

/-- Stitz-Zeager Exercise 1.4.26: for `f(x) = 2 / x`, the requested values (for nonzero arguments). -/
@[kb "stitzzeager2013" "Exercise 1.4.26, p. 76"]
theorem exer_1_4_26 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 / x) :
    f 2 = 1 ∧ f (-2) = -1 ∧ (∀ a, a ≠ 0 → f (2 * a) = 1 / a) ∧ (∀ a, a ≠ 0 → 2 * f a = 4 / a) ∧
      (∀ a, a ≠ 0 → f (2 / a) = a) ∧ (∀ a, a ≠ 0 → f a / 2 = 1 / a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · intro a ha; simp only [hf]; field_simp
  · intro a ha; simp only [hf]; ring
  · intro a ha; simp only [hf]; field_simp
  · intro a ha; simp only [hf]; field_simp

/-- Stitz-Zeager Exercise 1.4.29: for `f(x) = 2x² - 6`, `f(0) = -6` and `f(x) = 0` exactly when `x = ±√3`. -/
@[kb "stitzzeager2013" "Exercise 1.4.29, p. 76"]
theorem exer_1_4_29 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x ^ 2 - 6) :
    f 0 = -6 ∧ ∀ x, f x = 0 ↔ x = √3 ∨ x = -√3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨by simp [hf], fun x => ?_⟩
  simp only [hf]
  constructor
  · intro h
    have : (x - √3) * (x + √3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith

/-- Stitz-Zeager Exercise 1.4.30: for `f(x) = x² - x - 12`, `f(0) = -12` and `f(x) = 0` exactly when `x = -3` or
`x = 4`. -/
@[kb "stitzzeager2013" "Exercise 1.4.30, p. 76"]
theorem exer_1_4_30 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - x - 12) :
    f 0 = -12 ∧ ∀ x, f x = 0 ↔ x = -3 ∨ x = 4 := by
  refine ⟨by simp [hf], fun x => ?_⟩
  simp only [hf]
  constructor
  · intro h
    have : (x + 3) * (x - 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 1.4.32: for `f(x) = √(1 - 2x)`, `f(0) = 1`, and for `x ≤ 1/2` (the domain) `f(x) = 0`
exactly when `x = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.32, p. 76"]
theorem exer_1_4_32 (f : ℝ → ℝ) (hf : ∀ x, f x = √(1 - 2 * x)) :
    f 0 = 1 ∧ ∀ x, x ≤ 1 / 2 → (f x = 0 ↔ x = 1 / 2) := by
  refine ⟨by simp [hf], fun x hx => ?_⟩
  simp only [hf]
  rw [Real.sqrt_eq_zero (by linarith)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.33: for `f(x) = 3 / (4 - x)`, `f(0) = 3/4`, and on the domain `x ≠ 4` the value
`f(x)` is never `0`. -/
@[kb "stitzzeager2013" "Exercise 1.4.33, p. 76"]
theorem exer_1_4_33 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 / (4 - x)) :
    f 0 = 3 / 4 ∧ ∀ x, x ≠ 4 → f x ≠ 0 := by
  refine ⟨by simp [hf], fun x hx => ?_⟩
  simp only [hf]
  have : 4 - x ≠ 0 := fun h => hx (by linarith)
  exact div_ne_zero (by norm_num) this

/-- Stitz-Zeager Exercise 1.4.34: for `f(x) = (3x² - 12x) / (4 - x²)`, `f(0) = 0`, and on the domain `x ≠ ±2`
the value `f(x)` is `0` exactly when `x = 0` or `x = 4`. -/
@[kb "stitzzeager2013" "Exercise 1.4.34, p. 76"]
theorem exer_1_4_34 (f : ℝ → ℝ) (hf : ∀ x, f x = (3 * x ^ 2 - 12 * x) / (4 - x ^ 2)) :
    f 0 = 0 ∧ ∀ x, x ≠ 2 → x ≠ -2 → (f x = 0 ↔ x = 0 ∨ x = 4) := by
  refine ⟨by simp [hf], fun x h2 h2' => ?_⟩
  have hd : 4 - x ^ 2 ≠ 0 := by
    intro h
    have : (x - 2) * (x + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact h2 (by linarith)
    · exact h2' (by linarith)
  simp only [hf, div_eq_zero_iff, hd, or_false]
  constructor
  · intro h
    have : 3 * (x * (x - 4)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · norm_num at h
    · rcases mul_eq_zero.mp h with h | h
      · left; exact h
      · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 1.4.35: for the piecewise function `x + 5` (`x ≤ -3`), `√(9 - x²)` (`-3 < x ≤ 3`),
`-x + 5` (`x > 3`), the values at `-4, -3, 3, 3.001, -3.001, 2` are `1, 2, 0, 1.999, 1.999, √5`. -/
@[kb "stitzzeager2013" "Exercise 1.4.35, p. 76"]
theorem exer_1_4_35 (f : ℝ → ℝ)
    (hf : ∀ x, f x = if x ≤ -3 then x + 5 else if x ≤ 3 then √(9 - x ^ 2) else -x + 5) :
    f (-4) = 1 ∧ f (-3) = 2 ∧ f 3 = 0 ∧ f 3.001 = 1.999 ∧ f (-3.001) = 1.999 ∧ f 2 = √5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hf] <;> norm_num

/-- Stitz-Zeager Exercise 1.4.36: for the piecewise function `x²` (`x ≤ -1`), `√(1 - x²)` (`-1 < x ≤ 1`),
`x` (`x > 1`), the values at `4, -3, 1, 0, -1` are `4, 9, 0, 1, 1`, and `f(-0.999)` lies strictly between
`0.0446` and `0.0448`. -/
@[kb "stitzzeager2013" "Exercise 1.4.36, p. 77"]
theorem exer_1_4_36 (f : ℝ → ℝ)
    (hf : ∀ x, f x = if x ≤ -1 then x ^ 2 else if x ≤ 1 then √(1 - x ^ 2) else x) :
    f 4 = 4 ∧ f (-3) = 9 ∧ f 1 = 0 ∧ f 0 = 1 ∧ f (-1) = 1 ∧ 0.0446 < f (-0.999) ∧ f (-0.999) < 0.0448 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · simp only [hf]; norm_num
  · have e : f (-0.999) = √(1 - (-0.999) ^ 2) := by
      rw [hf, if_neg (by norm_num), if_pos (by norm_num)]
    rw [e, Real.lt_sqrt (by norm_num)]; norm_num
  · have e : f (-0.999) = √(1 - (-0.999) ^ 2) := by
      rw [hf, if_neg (by norm_num), if_pos (by norm_num)]
    rw [e, Real.sqrt_lt' (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 1.4.40: `3x / (x² + x - 2)` is defined exactly off `x = -2` and `x = 1`. -/
@[kb "stitzzeager2013" "Exercise 1.4.40, p. 77"]
theorem exer_1_4_40 : {x : ℝ | x ^ 2 + x - 2 ≠ 0} = Iio (-2) ∪ Ioo (-2) 1 ∪ Ioi 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  have : x ^ 2 + x - 2 = (x + 2) * (x - 1) := by ring
  rw [this]
  constructor
  · intro h
    have h1 : x + 2 ≠ 0 := left_ne_zero_of_mul h
    have h2 : x - 1 ≠ 0 := right_ne_zero_of_mul h
    grind
  · intro h
    exact mul_ne_zero (by grind) (by grind)

/-- Stitz-Zeager Exercise 1.4.43: `(x + 4) / (x² - 36)` is defined exactly off `x = ±6`. -/
@[kb "stitzzeager2013" "Exercise 1.4.43, p. 77"]
theorem exer_1_4_43 : {x : ℝ | x ^ 2 - 36 ≠ 0} = Iio (-6) ∪ Ioo (-6) 6 ∪ Ioi 6 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  have : x ^ 2 - 36 = (x + 6) * (x - 6) := by ring
  rw [this]
  constructor
  · intro h
    have h1 : x + 6 ≠ 0 := left_ne_zero_of_mul h
    have h2 : x - 6 ≠ 0 := right_ne_zero_of_mul h
    grind
  · intro h
    exact mul_ne_zero (by grind) (by grind)

/-- Stitz-Zeager Exercise 1.4.46: `√(2x + 5)` is defined exactly on `[-5/2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.46, p. 77"]
theorem exer_1_4_46 : {x : ℝ | 0 ≤ 2 * x + 5} = Ici (-5 / 2) := by
  ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.52: `6 / (4 - √(6x - 2))` is defined exactly on `[1/3, 3) ∪ (3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.52, p. 77"]
theorem exer_1_4_52 : {x : ℝ | 0 ≤ 6 * x - 2 ∧ 4 - √(6 * x - 2) ≠ 0} = Ico (1 / 3) 3 ∪ Ioi 3 := by
  have key : ∀ x : ℝ, 0 ≤ 6 * x - 2 → (√(6 * x - 2) = 4 ↔ x = 3) := by
    intro x hx
    rw [Real.sqrt_eq_iff_mul_self_eq hx (by norm_num)]
    constructor <;> intro h <;> linarith
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ico, mem_Ioi, ne_eq]
  constructor
  · rintro ⟨h0, h⟩
    have h3 : x ≠ 3 := fun h' => h (by rw [(key x h0).2 h']; norm_num [h'])
    have h4 : x ≠ 3 := h3
    rcases lt_or_gt_of_ne h4 with h1 | h1
    · exact Or.inl ⟨by linarith, h1⟩
    · exact Or.inr h1
  · rintro (⟨h0, h1⟩ | h1)
    · refine ⟨by linarith, fun h => ?_⟩
      have := (key x (by linarith)).1 (by linarith)
      linarith
    · refine ⟨by linarith, fun h => ?_⟩
      have := (key x (by linarith)).1 (by linarith)
      linarith

/-- Stitz-Zeager Exercise 1.4.58: `√(x - 7) + √(9 - x)` is defined exactly on `[7, 9]`. -/
@[kb "stitzzeager2013" "Exercise 1.4.58, p. 77"]
theorem exer_1_4_58 : {x : ℝ | 0 ≤ x - 7 ∧ 0 ≤ 9 - x} = Icc 7 9 := by
  ext x; simp only [mem_ofPred_eq, mem_Icc]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Stitz-Zeager Exercise 1.4.60: `1 / (4 - 1/v²)` is defined exactly off `v = 0` and `v = ±1/2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.60, p. 77"]
theorem exer_1_4_60 : {v : ℝ | v ≠ 0 ∧ 4 - 1 / v ^ 2 ≠ 0} =
    Iio (-1 / 2) ∪ Ioo (-1 / 2) 0 ∪ Ioo 0 (1 / 2) ∪ Ioi (1 / 2) := by
  ext v
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨h0, h⟩
    have h1 : v ≠ 1 / 2 := by
      rintro rfl; apply h; norm_num
    have h2 : v ≠ -1 / 2 := by
      rintro rfl; apply h; norm_num
    grind
  · intro h
    have h0 : v ≠ 0 := by grind
    refine ⟨h0, fun h' => ?_⟩
    have : 4 * v ^ 2 = 1 := by field_simp at h'; linarith
    have : (2 * v - 1) * (2 * v + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h <;> grind

/-- Stitz-Zeager Exercise 1.4.66: for `V(r) = (4π/3) r³`, `V(3) = 36π`, and for `r > 0` the equation
`V(r) = 32π/3` holds exactly when `r = 2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.66, p. 78"]
theorem exer_1_4_66 (V : ℝ → ℝ) (hV : ∀ r, V r = 4 * Real.pi / 3 * r ^ 3) :
    V 3 = 36 * Real.pi ∧ ∀ r, 0 < r → (V r = 32 * Real.pi / 3 ↔ r = 2) := by
  refine ⟨by rw [hV]; ring, fun r hr => ?_⟩
  rw [hV]
  constructor
  · intro h
    have hp := Real.pi_pos
    have h1 : Real.pi * (4 * (r ^ 3 - 8)) = 0 := by linarith
    have h2 : r ^ 3 - 8 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hp.ne'
      · linarith
    have : (r - 2) * (r ^ 2 + 2 * r + 4) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · nlinarith
  · rintro rfl; ring

/-- Stitz-Zeager Exercise 1.4.67: for `h(t) = -16t² + 64`, `h(0) = 64`, `h(t) = 0` exactly for `t = ±2`, and on
`0 ≤ t ≤ 2` only for `t = 2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.67, p. 78"]
theorem exer_1_4_67 (h : ℝ → ℝ) (hh : ∀ t, h t = -16 * t ^ 2 + 64) :
    h 0 = 64 ∧ (∀ t, h t = 0 ↔ t = 2 ∨ t = -2) ∧ (∀ t, 0 ≤ t → t ≤ 2 → (h t = 0 ↔ t = 2)) := by
  refine ⟨by rw [hh]; norm_num, fun t => ?_, fun t h0 h2 => ?_⟩
  · rw [hh]
    constructor
    · intro h
      have : (t - 2) * (t + 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · rw [hh]
    constructor
    · intro h
      have : (t - 2) * (t + 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 1.4.71: for `P(t) = 150t / (t + 15)`, `P(0) = 0` and `P(205) = 3075/22`, which lies
between `139` and `140`. -/
@[kb "stitzzeager2013" "Exercise 1.4.71, p. 78"]
theorem exer_1_4_71 (P : ℝ → ℝ) (hP : ∀ t, P t = 150 * t / (t + 15)) :
    P 0 = 0 ∧ P 205 = 3075 / 22 ∧ 139 < P 205 ∧ P 205 < 140 := by
  refine ⟨by rw [hP]; norm_num, ?_, ?_, ?_⟩ <;> rw [hP] <;> norm_num

/-- Stitz-Zeager Exercise 1.4.72: with the print-on-demand price schedule `15n` (`n ≤ 25`), `13.5n` (`25 < n ≤ 50`),
`12n` (`n > 50`), `20` copies cost `300`, `50` copies cost `675`, `51` copies cost `612`, and `56` copies are the most
that `675` buys among orders over `50`. -/
@[kb "stitzzeager2013" "Exercise 1.4.72, p. 78"]
theorem exer_1_4_72 (C : ℕ → ℝ)
    (hC : ∀ n, C n = if n ≤ 25 then (15 : ℝ) * n else if n ≤ 50 then (13.5 : ℝ) * n else (12 : ℝ) * n) :
    C 20 = 300 ∧ C 50 = 675 ∧ C 51 = 612 ∧ C 56 ≤ 675 ∧ 675 < C 57 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hC] <;> norm_num

/-- Stitz-Zeager Exercise 1.4.75(a): `⌊0.785⌋ = 0`, `⌊117⌋ = 117`, `⌊-2.001⌋ = -3`, `⌊π + 6⌋ = 9`. -/
@[kb "stitzzeager2013" "Exercise 1.4.75, p. 79"]
theorem exer_1_4_75_a :
    ⌊(0.785 : ℝ)⌋ = 0 ∧ ⌊(117 : ℝ)⌋ = 117 ∧ ⌊(-2.001 : ℝ)⌋ = -3 ∧ ⌊Real.pi + 6⌋ = 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Int.floor_eq_iff]; norm_num
  · exact Int.floor_intCast 117
  · rw [Int.floor_eq_iff]; norm_num
  · rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith [Real.pi_gt_three, Real.pi_lt_four]

end UndergradKB.Precalculus.Course
