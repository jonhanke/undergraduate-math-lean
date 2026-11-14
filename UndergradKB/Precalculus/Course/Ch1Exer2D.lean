import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Radicals

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 1.6-1.7 -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

/-! ## Section 1.6 -/

/-- Stitz-Zeager Exercise 1.6.1: `f(x) = 2 - x` has x-intercept `2`, y-intercept `2`, and no symmetry. -/
@[kb "stitzzeager2013" "Exercise 1.6.1, p. 119"]
theorem exer_1_6_1 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 - x) :
    {x : ℝ | f x = 0} = {2} ∧ f 0 = 2 ∧ ¬ (∀ x, f (-x) = f x) ∧ ¬ (∀ x, f (-x) = -f x) := by
  refine ⟨?_, by rw [hf]; norm_num, fun h => ?_, fun h => ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_singleton_iff, hf]; constructor <;> intro h <;> linarith
  · have := h 1; rw [hf, hf] at this; norm_num at this
  · have := h 0; rw [hf, hf] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.6.3: `f(x) = x² + 1` has no x-intercept, y-intercept `1`, and is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.3, p. 119"]
theorem exer_1_6_3 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + 1) :
    (∀ x, f x ≠ 0) ∧ f 0 = 1 ∧ ∀ x, f (-x) = f x := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, fun x => ?_⟩
  · rw [hf]; positivity
  · simp only [hf, neg_sq]

/-- Stitz-Zeager Exercise 1.6.5: the constant function `f(x) = 2` has no x-intercept, y-intercept `2`, and is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.5, p. 119"]
theorem exer_1_6_5 (f : ℝ → ℝ) (hf : ∀ x, f x = 2) :
    (∀ x, f x ≠ 0) ∧ f 0 = 2 ∧ ∀ x, f (-x) = f x := by
  refine ⟨fun x => ?_, hf 0, fun x => ?_⟩
  · rw [hf]; norm_num
  · simp only [hf]

/-- Stitz-Zeager Exercise 1.6.6: `f(x) = x³` has the only intercept `(0,0)` and is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.6, p. 119"]
theorem exer_1_6_6 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 3) :
    {x : ℝ | f x = 0} = {0} ∧ f 0 = 0 ∧ ∀ x, f (-x) = -f x := by
  refine ⟨?_, by rw [hf]; norm_num, fun x => ?_⟩
  · ext x; simp [hf]
  · simp only [hf]; ring

/-- Stitz-Zeager Exercise 1.6.9: `f(x) = √(5 - x)` has domain `(-∞, 5]`, x-intercept `5`, y-intercept `√5`, and no
symmetry (its domain is not symmetric about `0`). -/
@[kb "stitzzeager2013" "Exercise 1.6.9, p. 119"]
theorem exer_1_6_9 (f : ℝ → ℝ) (hf : ∀ x, f x = √(5 - x)) :
    {x : ℝ | 0 ≤ 5 - x} = Iic 5 ∧ {x : ℝ | 0 ≤ 5 - x ∧ f x = 0} = {5} ∧ f 0 = √5 ∧
      ∃ x : ℝ, 0 ≤ 5 - x ∧ ¬ 0 ≤ 5 - (-x) := by
  refine ⟨?_, ?_, by rw [hf]; norm_num, ⟨-6, by norm_num, by norm_num⟩⟩
  · ext x; simp only [mem_ofPred_eq, mem_Iic]; constructor <;> intro h <;> linarith
  · ext x
    simp only [mem_ofPred_eq, mem_singleton_iff, hf]
    constructor
    · rintro ⟨h0, h⟩
      have := (Real.sqrt_eq_zero h0).1 h
      linarith
    · rintro rfl; norm_num

/-- `∛(-y) = -∛y`. -/
private theorem pr3_neg (y : ℝ) : principalRoot 3 (-y) = -principalRoot 3 y := by
  have h : principalRoot 3 y ^ 3 = y := principalRoot_pow (by norm_num) (Or.inl (by decide))
  exact ((principalRoot_eq_iff_odd (by decide) (-y) (-principalRoot 3 y)).2 (by
    calc (-principalRoot 3 y) ^ 3 = -(principalRoot 3 y ^ 3) := by ring
      _ = -y := by rw [h])).symm

/-- Stitz-Zeager Exercise 1.6.11: `f(x) = ∛x` has the only intercept `(0,0)` and is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.11, p. 119"]
theorem exer_1_6_11 (f : ℝ → ℝ) (hf : ∀ x, f x = principalRoot 3 x) :
    {x : ℝ | f x = 0} = {0} ∧ f 0 = 0 ∧ ∀ x, f (-x) = -f x := by
  have h0 : ∀ x : ℝ, f x = 0 ↔ x = 0 := by
    intro x
    rw [hf, eq_comm, principalRoot_eq_iff_odd (by decide)]
    constructor <;> intro h <;> [skip; rw [h]] <;> simp_all [eq_comm]
  refine ⟨?_, (h0 0).2 rfl, fun x => ?_⟩
  · ext x; simp [h0]
  · simp only [hf, pr3_neg]

/-- Stitz-Zeager Exercise 1.6.21: `f(x) = 7x` is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.21, p. 119"]
theorem exer_1_6_21 (f : ℝ → ℝ) (hf : ∀ x, f x = 7 * x) : ∀ x, f (-x) = -f x := by
  intro x; simp only [hf]; ring

/-- Stitz-Zeager Exercise 1.6.23: the constant function `f(x) = 7` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.23, p. 119"]
theorem exer_1_6_23 (f : ℝ → ℝ) (hf : ∀ x, f x = 7) : ∀ x, f (-x) = f x := by
  intro x; simp only [hf]

/-- Stitz-Zeager Exercise 1.6.24: `f(x) = 3x² - 4` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.24, p. 119"]
theorem exer_1_6_24 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * x ^ 2 - 4) : ∀ x, f (-x) = f x := by
  intro x; simp only [hf, neg_sq]

/-- Stitz-Zeager Exercise 1.6.25: `f(x) = 4 - x²` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.25, p. 119"]
theorem exer_1_6_25 (f : ℝ → ℝ) (hf : ∀ x, f x = 4 - x ^ 2) : ∀ x, f (-x) = f x := by
  intro x; simp only [hf, neg_sq]

/-- Stitz-Zeager Exercise 1.6.27: `f(x) = 2x³ - x` is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.27, p. 119"]
theorem exer_1_6_27 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x ^ 3 - x) : ∀ x, f (-x) = -f x := by
  intro x; simp only [hf]; ring

/-- Stitz-Zeager Exercise 1.6.34: `f(x) = ∛x` is odd. -/
@[kb "stitzzeager2013" "Exercise 1.6.34, p. 119"]
theorem exer_1_6_34 (f : ℝ → ℝ) (hf : ∀ x, f x = principalRoot 3 x) : ∀ x, f (-x) = -f x := by
  intro x; simp only [hf, pr3_neg]

/-- Stitz-Zeager Exercise 1.6.35: `f(x) = ∛(x²)` is even. -/
@[kb "stitzzeager2013" "Exercise 1.6.35, p. 119"]
theorem exer_1_6_35 (f : ℝ → ℝ) (hf : ∀ x, f x = principalRoot 3 (x ^ 2)) : ∀ x, f (-x) = f x := by
  intro x; simp only [hf, neg_sq]

/-- Stitz-Zeager Exercise 1.6.41: `f(x) = ∛(x³ + x)/(5x)` is even (on its domain `x ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 1.6.41, p. 120"]
theorem exer_1_6_41 (f : ℝ → ℝ) (hf : ∀ x, f x = principalRoot 3 (x ^ 3 + x) / (5 * x)) :
    ∀ x, x ≠ 0 → f (-x) = f x := by
  intro x hx
  simp only [hf]
  rw [show (-x) ^ 3 + -x = -(x ^ 3 + x) by ring, pr3_neg, mul_neg, neg_div_neg_eq]

/-! ## Section 1.7 -/

/-- Stitz-Zeager Exercise 1.7.1: `(2,-3)` on `y = f(x)` gives `(2, 0)` on `y = f(x) + 3`. -/
@[kb "stitzzeager2013" "Exercise 1.7.1, p. 152"]
theorem exer_1_7_1 (f : ℝ → ℝ) (h : f 2 = -3) : f 2 + 3 = 0 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.3: `(2,-3)` on `y = f(x)` gives `(2, -4)` on `y = f(x) - 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.3, p. 152"]
theorem exer_1_7_3 (f : ℝ → ℝ) (h : f 2 = -3) : f 2 - 1 = -4 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.4: `(2,-3)` on `y = f(x)` gives `(3, -3)` on `y = f(x - 1)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.4, p. 152"]
theorem exer_1_7_4 (f : ℝ → ℝ) (h : f 2 = -3) : f (3 - 1) = -3 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.5: `(2,-3)` on `y = f(x)` gives `(2, -9)` on `y = 3f(x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.5, p. 152"]
theorem exer_1_7_5 (f : ℝ → ℝ) (h : f 2 = -3) : 3 * f 2 = -9 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.7: `(2,-3)` on `y = f(x)` gives `(2, 3)` on `y = -f(x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.7, p. 152"]
theorem exer_1_7_7 (f : ℝ → ℝ) (h : f 2 = -3) : -f 2 = 3 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.8: `(2,-3)` on `y = f(x)` gives `(-2, -3)` on `y = f(-x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.8, p. 152"]
theorem exer_1_7_8 (f : ℝ → ℝ) (h : f 2 = -3) : f (-(-2)) = -3 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.11: `(2,-3)` on `y = f(x)` gives `(2, 13)` on `y = 10 - f(x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.11, p. 152"]
theorem exer_1_7_11 (f : ℝ → ℝ) (h : f 2 = -3) : 10 - f 2 = 13 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.15: `(2,-3)` on `y = f(x)` gives `(-1, -7)` on `y = 2f(1 - x) - 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.15, p. 152"]
theorem exer_1_7_15 (f : ℝ → ℝ) (h : f 2 = -3) : 2 * f (1 - (-1)) - 1 = -7 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.17: `(2,-3)` on `y = f(x)` gives `(2/3, -2)` on `y = (f(3x) - 1)/2`. -/
@[kb "stitzzeager2013" "Exercise 1.7.17, p. 152"]
theorem exer_1_7_17 (f : ℝ → ℝ) (h : f 2 = -3) : (f (3 * (2 / 3)) - 1) / 2 = -2 := by
  norm_num [h]

/-! ### Transformed points of given graphs (Exercises 19-27: `f` passes through `(-2,2)`, `(0,0)`, `(2,2)`) -/

/-- Stitz-Zeager Exercise 1.7.19: `y = f(x) + 1` passes through `(-2,3)`, `(0,1)`, `(2,3)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.19, p. 152"]
theorem exer_1_7_19 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    f (-2) + 1 = 3 ∧ f 0 + 1 = 1 ∧ f 2 + 1 = 3 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.20: `y = f(x) - 2` passes through `(-2,0)`, `(0,-2)`, `(2,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.20, p. 152"]
theorem exer_1_7_20 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    f (-2) - 2 = 0 ∧ f 0 - 2 = -2 ∧ f 2 - 2 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.21: `y = f(x + 1)` passes through `(-3,2)`, `(-1,0)`, `(1,2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.21, p. 152"]
theorem exer_1_7_21 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    f (-3 + 1) = 2 ∧ f (-1 + 1) = 0 ∧ f (1 + 1) = 2 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.22: `y = f(x - 2)` passes through `(0,2)`, `(2,0)`, `(4,2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.22, p. 152"]
theorem exer_1_7_22 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    f (0 - 2) = 2 ∧ f (2 - 2) = 0 ∧ f (4 - 2) = 2 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.23: `y = 2f(x)` passes through `(-2,4)`, `(0,0)`, `(2,4)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.23, p. 152"]
theorem exer_1_7_23 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    2 * f (-2) = 4 ∧ 2 * f 0 = 0 ∧ 2 * f 2 = 4 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.24: `y = f(2x)` passes through `(-1,2)`, `(0,0)`, `(1,2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.24, p. 152"]
theorem exer_1_7_24 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    f (2 * (-1)) = 2 ∧ f (2 * 0) = 0 ∧ f (2 * 1) = 2 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.25: `y = 2 - f(x)` passes through `(-2,0)`, `(0,2)`, `(2,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.25, p. 152"]
theorem exer_1_7_25 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    2 - f (-2) = 0 ∧ 2 - f 0 = 2 ∧ 2 - f 2 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.26: `y = f(2 - x)` passes through `(0,2)`, `(2,0)`, `(4,2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.26, p. 152"]
theorem exer_1_7_26 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    f (2 - 0) = 2 ∧ f (2 - 2) = 0 ∧ f (2 - 4) = 2 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.27: `y = 2 - f(2 - x)` passes through `(0,0)`, `(2,2)`, `(4,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.27, p. 152"]
theorem exer_1_7_27 (f : ℝ → ℝ) (h : f (-2) = 2 ∧ f 0 = 0 ∧ f 2 = 2) :
    2 - f (2 - 0) = 0 ∧ 2 - f (2 - 2) = 2 ∧ 2 - f (2 - 4) = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-! ### Exercises 29-37: `f` passes through `(-2,0)`, `(0,4)`, `(2,0)`, `(4,-2)` -/

/-- Stitz-Zeager Exercise 1.7.29: `y = f(x) - 1` passes through `(-2,-1)`, `(0,3)`, `(2,-1)`, `(4,-3)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.29, p. 153"]
theorem exer_1_7_29 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    f (-2) - 1 = -1 ∧ f 0 - 1 = 3 ∧ f 2 - 1 = -1 ∧ f 4 - 1 = -3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; rw [h1, h2, h3, h4]; norm_num

/-- Stitz-Zeager Exercise 1.7.30: `y = f(x + 1)` passes through `(-3,0)`, `(-1,4)`, `(1,0)`, `(3,-2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.30, p. 153"]
theorem exer_1_7_30 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    f (-3 + 1) = 0 ∧ f (-1 + 1) = 4 ∧ f (1 + 1) = 0 ∧ f (3 + 1) = -2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; norm_num [h1, h2, h3, h4]

/-- Stitz-Zeager Exercise 1.7.31: `y = f(x)/2` passes through `(-2,0)`, `(0,2)`, `(2,0)`, `(4,-1)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.31, p. 153"]
theorem exer_1_7_31 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    1 / 2 * f (-2) = 0 ∧ 1 / 2 * f 0 = 2 ∧ 1 / 2 * f 2 = 0 ∧ 1 / 2 * f 4 = -1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; rw [h1, h2, h3, h4]; norm_num

/-- Stitz-Zeager Exercise 1.7.32: `y = f(2x)` passes through `(-1,0)`, `(0,4)`, `(1,0)`, `(2,-2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.32, p. 153"]
theorem exer_1_7_32 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    f (2 * (-1)) = 0 ∧ f (2 * 0) = 4 ∧ f (2 * 1) = 0 ∧ f (2 * 2) = -2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; norm_num [h1, h2, h3, h4]

/-- Stitz-Zeager Exercise 1.7.33: `y = -f(x)` passes through `(-2,0)`, `(0,-4)`, `(2,0)`, `(4,2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.33, p. 153"]
theorem exer_1_7_33 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    -f (-2) = 0 ∧ -f 0 = -4 ∧ -f 2 = 0 ∧ -f 4 = 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; rw [h1, h2, h3, h4]; norm_num

/-- Stitz-Zeager Exercise 1.7.34: `y = f(-x)` passes through `(2,0)`, `(0,4)`, `(-2,0)`, `(-4,-2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.34, p. 153"]
theorem exer_1_7_34 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    f (-2) = 0 ∧ f (-0) = 4 ∧ f (-(-2)) = 0 ∧ f (-(-4)) = -2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; norm_num [h1, h2, h3, h4]

/-- Stitz-Zeager Exercise 1.7.35: `y = f(x + 1) - 1` passes through `(-3,-1)`, `(-1,3)`, `(1,-1)`, `(3,-3)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.35, p. 153"]
theorem exer_1_7_35 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    f (-3 + 1) - 1 = -1 ∧ f (-1 + 1) - 1 = 3 ∧ f (1 + 1) - 1 = -1 ∧ f (3 + 1) - 1 = -3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; norm_num [h1, h2, h3, h4]

/-- Stitz-Zeager Exercise 1.7.36: `y = 1 - f(x)` passes through `(-2,1)`, `(0,-3)`, `(2,1)`, `(4,3)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.36, p. 153"]
theorem exer_1_7_36 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    1 - f (-2) = 1 ∧ 1 - f 0 = -3 ∧ 1 - f 2 = 1 ∧ 1 - f 4 = 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; rw [h1, h2, h3, h4]; norm_num

/-- Stitz-Zeager Exercise 1.7.37: `y = f(x + 1)/2 - 1` passes through `(-3,-1)`, `(-1,1)`, `(1,-1)`, `(3,-2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.37, p. 153"]
theorem exer_1_7_37 (f : ℝ → ℝ) (h : f (-2) = 0 ∧ f 0 = 4 ∧ f 2 = 0 ∧ f 4 = -2) :
    1 / 2 * f (-3 + 1) - 1 = -1 ∧ 1 / 2 * f (-1 + 1) - 1 = 1 ∧ 1 / 2 * f (1 + 1) - 1 = -1 ∧
      1 / 2 * f (3 + 1) - 1 = -2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; norm_num [h1, h2, h3, h4]

/-! ### Exercises 38-49: `f` passes through `(-3,0)`, `(0,3)`, `(3,0)` -/

/-- Stitz-Zeager Exercise 1.7.38: `g(x) = f(x) + 3` passes through `(-3,3)`, `(0,6)`, `(3,3)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.38, p. 153"]
theorem exer_1_7_38 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    f (-3) + 3 = 3 ∧ f 0 + 3 = 6 ∧ f 3 + 3 = 3 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.39: `h(x) = f(x) - 1/2` passes through `(-3,-1/2)`, `(0,5/2)`, `(3,-1/2)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.39, p. 153"]
theorem exer_1_7_39 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    f (-3) - 1 / 2 = -1 / 2 ∧ f 0 - 1 / 2 = 5 / 2 ∧ f 3 - 1 / 2 = -1 / 2 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.40: `j(x) = f(x - 2/3)` passes through `(-7/3,0)`, `(2/3,3)`, `(11/3,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.40, p. 153"]
theorem exer_1_7_40 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    f (-7 / 3 - 2 / 3) = 0 ∧ f (2 / 3 - 2 / 3) = 3 ∧ f (11 / 3 - 2 / 3) = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.41: `a(x) = f(x + 4)` passes through `(-7,0)`, `(-4,3)`, `(-1,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.41, p. 153"]
theorem exer_1_7_41 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    f (-7 + 4) = 0 ∧ f (-4 + 4) = 3 ∧ f (-1 + 4) = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.42: `b(x) = f(x + 1) - 1` passes through `(-4,-1)`, `(-1,2)`, `(2,-1)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.42, p. 153"]
theorem exer_1_7_42 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    f (-4 + 1) - 1 = -1 ∧ f (-1 + 1) - 1 = 2 ∧ f (2 + 1) - 1 = -1 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.43: `c(x) = (3/5) f(x)` passes through `(-3,0)`, `(0,9/5)`, `(3,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.43, p. 153"]
theorem exer_1_7_43 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    3 / 5 * f (-3) = 0 ∧ 3 / 5 * f 0 = 9 / 5 ∧ 3 / 5 * f 3 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.44: `d(x) = -2 f(x)` passes through `(-3,0)`, `(0,-6)`, `(3,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.44, p. 153"]
theorem exer_1_7_44 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    -2 * f (-3) = 0 ∧ -2 * f 0 = -6 ∧ -2 * f 3 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; rw [h1, h2, h3]; norm_num

/-- Stitz-Zeager Exercise 1.7.45: `k(x) = f(2x/3)` passes through `(-9/2,0)`, `(0,3)`, `(9/2,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.45, p. 153"]
theorem exer_1_7_45 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    f (2 * (-9 / 2) / 3) = 0 ∧ f (2 * 0 / 3) = 3 ∧ f (2 * (9 / 2) / 3) = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.46: `m(x) = -f(3x)/4` passes through `(-1,0)`, `(0,-3/4)`, `(1,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.46, p. 153"]
theorem exer_1_7_46 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    -(1 / 4) * f (3 * (-1)) = 0 ∧ -(1 / 4) * f (3 * 0) = -3 / 4 ∧ -(1 / 4) * f (3 * 1) = 0 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.47: `n(x) = 4f(x - 3) - 6` passes through `(0,-6)`, `(3,6)`, `(6,-6)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.47, p. 153"]
theorem exer_1_7_47 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    4 * f (0 - 3) - 6 = -6 ∧ 4 * f (3 - 3) - 6 = 6 ∧ 4 * f (6 - 3) - 6 = -6 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.48: `p(x) = 4 + f(1 - 2x)` passes through `(2,4)`, `(1/2,7)`, `(-1,4)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.48, p. 153"]
theorem exer_1_7_48 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    4 + f (1 - 2 * 2) = 4 ∧ 4 + f (1 - 2 * (1 / 2)) = 7 ∧ 4 + f (1 - 2 * (-1)) = 4 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-- Stitz-Zeager Exercise 1.7.49: `q(x) = -f((x+4)/2)/2 - 3` passes through `(-10,-3)`, `(-4,-9/2)`, `(2,-3)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.49, p. 153"]
theorem exer_1_7_49 (f : ℝ → ℝ) (h : f (-3) = 0 ∧ f 0 = 3 ∧ f 3 = 0) :
    -(1 / 2) * f ((-10 + 4) / 2) - 3 = -3 ∧ -(1 / 2) * f ((-4 + 4) / 2) - 3 = -9 / 2 ∧
      -(1 / 2) * f ((2 + 4) / 2) - 3 = -3 := by
  obtain ⟨h1, h2, h3⟩ := h; norm_num [h1, h2, h3]

/-! ### Exercises 50-53: `S` passes through `(-2,0)`, `(-1,-3)`, `(0,0)`, `(1,3)`, `(2,0)` -/

/-- Stitz-Zeager Exercise 1.7.50: `S₁(x) = S(x + 1)` passes through `(-3,0)`, `(-2,-3)`, `(-1,0)`, `(0,3)`, `(1,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.50, p. 154"]
theorem exer_1_7_50 (S : ℝ → ℝ) (h : S (-2) = 0 ∧ S (-1) = -3 ∧ S 0 = 0 ∧ S 1 = 3 ∧ S 2 = 0) :
    S (-3 + 1) = 0 ∧ S (-2 + 1) = -3 ∧ S (-1 + 1) = 0 ∧ S (0 + 1) = 3 ∧ S (1 + 1) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; norm_num [h1, h2, h3, h4, h5]

/-- Stitz-Zeager Exercise 1.7.51: `S₂(x) = S(-x + 1)` passes through `(-1,0)`, `(0,3)`, `(1,0)`, `(2,-3)`, `(3,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.51, p. 154"]
theorem exer_1_7_51 (S : ℝ → ℝ) (h : S (-2) = 0 ∧ S (-1) = -3 ∧ S 0 = 0 ∧ S 1 = 3 ∧ S 2 = 0) :
    S (-(-1) + 1) = 0 ∧ S (-0 + 1) = 3 ∧ S (-1 + 1) = 0 ∧ S (-2 + 1) = -3 ∧ S (-3 + 1) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; norm_num [h1, h2, h3, h4, h5]

/-- Stitz-Zeager Exercise 1.7.52: `S₃(x) = S(-x + 1)/2` passes through `(-1,0)`, `(0,3/2)`, `(1,0)`, `(2,-3/2)`,
`(3,0)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.52, p. 154"]
theorem exer_1_7_52 (S : ℝ → ℝ) (h : S (-2) = 0 ∧ S (-1) = -3 ∧ S 0 = 0 ∧ S 1 = 3 ∧ S 2 = 0) :
    1 / 2 * S (-(-1) + 1) = 0 ∧ 1 / 2 * S (-0 + 1) = 3 / 2 ∧ 1 / 2 * S (-1 + 1) = 0 ∧
      1 / 2 * S (-2 + 1) = -3 / 2 ∧ 1 / 2 * S (-3 + 1) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; norm_num [h1, h2, h3, h4, h5]

/-- Stitz-Zeager Exercise 1.7.53: `S₄(x) = S(-x + 1)/2 + 1` passes through `(-1,1)`, `(0,5/2)`, `(1,1)`, `(2,-1/2)`,
`(3,1)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.53, p. 154"]
theorem exer_1_7_53 (S : ℝ → ℝ) (h : S (-2) = 0 ∧ S (-1) = -3 ∧ S 0 = 0 ∧ S 1 = 3 ∧ S 2 = 0) :
    1 / 2 * S (-(-1) + 1) + 1 = 1 ∧ 1 / 2 * S (-0 + 1) + 1 = 5 / 2 ∧ 1 / 2 * S (-1 + 1) + 1 = 1 ∧
      1 / 2 * S (-2 + 1) + 1 = -1 / 2 ∧ 1 / 2 * S (-3 + 1) + 1 = 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; norm_num [h1, h2, h3, h4, h5]

/-! ### Formulas for transformed square roots -/

/-- Stitz-Zeager Exercise 1.7.56: reflecting `√x` across the x-axis and shifting up `1` gives `-√x + 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.56, p. 154"]
theorem exer_1_7_56 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => -f x + 1) = fun x => -√x + 1 := by
  funext x; simp only [hf]

/-- Stitz-Zeager Exercise 1.7.57: shifting `√x` up `1` and then reflecting across the x-axis gives `-(√x + 1)`,
which differs from the function of Exercise 1.7.56 (at `x = 0` the values are `-1` and `1`). -/
@[kb "stitzzeager2013" "Exercise 1.7.57, p. 154"]
theorem exer_1_7_57 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    ((fun x => -(f x + 1)) = fun x => -(√x + 1)) ∧ (fun x => -(√x + 1)) ≠ fun x => -√x + 1 := by
  refine ⟨?_, fun h => ?_⟩
  · funext x; simp only [hf]
  · have := congrFun h 0
    simp at this
    norm_num at this

/-- Stitz-Zeager Exercise 1.7.64: the transformed cube root can be written `g(x) = -2∛(x+3) - 1` or equivalently
`g(x) = 2∛(-x-3) - 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.64, p. 155"]
theorem exer_1_7_64 :
    (fun x : ℝ => -2 * principalRoot 3 (x + 3) - 1) = fun x => 2 * principalRoot 3 (-x - 3) - 1 := by
  funext x
  have h : principalRoot 3 (-x - 3) = -principalRoot 3 (x + 3) := by
    rw [show -x - 3 = -(x + 3) by ring]
    have h3 : principalRoot 3 (x + 3) ^ 3 = x + 3 := principalRoot_pow (by norm_num) (Or.inl (by decide))
    exact ((principalRoot_eq_iff_odd (by decide) (-(x + 3)) (-principalRoot 3 (x + 3))).2 (by
      calc (-principalRoot 3 (x + 3)) ^ 3 = -(principalRoot 3 (x + 3) ^ 3) := by ring
        _ = -(x + 3) := by rw [h3])).symm
  rw [h]; ring

end UndergradKB.Precalculus.Course
