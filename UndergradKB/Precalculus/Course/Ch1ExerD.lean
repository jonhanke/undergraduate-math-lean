import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers, Section 1.7 -/

namespace UndergradKB.Precalculus.Course

/-! ## Section 1.7 -/

/-- Stitz-Zeager Exercise 1.7.2: if `(2,-3)` is on the graph of `f`, then `(-1,-3)` is on the graph of
`y = f(x+3)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.2, p. 152"]
theorem exer_1_7_2 (f : ℝ → ℝ) (h : f 2 = -3) : f (-1 + 3) = -3 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.6: if `(2,-3)` is on the graph of `f`, then `(2/3,-3)` is on the graph of
`y = f(3x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.6, p. 152"]
theorem exer_1_7_6 (f : ℝ → ℝ) (h : f 2 = -3) : f (3 * (2 / 3)) = -3 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.9: if `(2,-3)` is on the graph of `f`, then `(5,-2)` is on the graph of
`y = f(x-3) + 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.9, p. 152"]
theorem exer_1_7_9 (f : ℝ → ℝ) (h : f 2 = -3) : f (5 - 3) + 1 = -2 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.10: if `(2,-3)` is on the graph of `f`, then `(1,-6)` is on the graph of
`y = 2 f(x+1)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.10, p. 152"]
theorem exer_1_7_10 (f : ℝ → ℝ) (h : f 2 = -3) : 2 * f (1 + 1) = -6 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.12: if `(2,-3)` is on the graph of `f`, then `(1,-10)` is on the graph of
`y = 3 f(2x) - 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.12, p. 152"]
theorem exer_1_7_12 (f : ℝ → ℝ) (h : f 2 = -3) : 3 * f (2 * 1) - 1 = -10 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.13: if `(2,-3)` is on the graph of `f`, then `(2,-3/2)` is on the graph of
`y = (1/2) f(4 - x)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.13, p. 152"]
theorem exer_1_7_13 (f : ℝ → ℝ) (h : f 2 = -3) : 1 / 2 * f (4 - 2) = -3 / 2 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.14: if `(2,-3)` is on the graph of `f`, then `(1/2,-12)` is on the graph of
`y = 5 f(2x+1) + 3`. -/
@[kb "stitzzeager2013" "Exercise 1.7.14, p. 152"]
theorem exer_1_7_14 (f : ℝ → ℝ) (h : f 2 = -3) : 5 * f (2 * (1 / 2) + 1) + 3 = -12 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.16: if `(2,-3)` is on the graph of `f`, then `(-1/2,-3)` is on the graph of
`y = f((7 - 2x)/4)`. -/
@[kb "stitzzeager2013" "Exercise 1.7.16, p. 152"]
theorem exer_1_7_16 (f : ℝ → ℝ) (h : f 2 = -3) : f ((7 - 2 * (-1 / 2)) / 4) = -3 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.18: if `(2,-3)` is on the graph of `f`, then `(1,1)` is on the graph of
`y = (4 - f(3x - 1))/7`. -/
@[kb "stitzzeager2013" "Exercise 1.7.18, p. 152"]
theorem exer_1_7_18 (f : ℝ → ℝ) (h : f 2 = -3) : (4 - f (3 * 1 - 1)) / 7 = 1 := by
  norm_num [h]

/-- Stitz-Zeager Exercise 1.7.54: shifting `√x` right `2` then down `3` gives `√(x-2) - 3`. -/
@[kb "stitzzeager2013" "Exercise 1.7.54, p. 154"]
theorem exer_1_7_54 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => f (x - 2) - 3) = fun x => √(x - 2) - 3 := by
  funext x; rw [hf]

/-- Stitz-Zeager Exercise 1.7.55: shifting `√x` down `3` then right `2` gives the same function `√(x-2) - 3`. -/
@[kb "stitzzeager2013" "Exercise 1.7.55, p. 154"]
theorem exer_1_7_55 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => (fun t => f t - 3) (x - 2)) = fun x => √(x - 2) - 3 := by
  funext x; simp only [hf]

/-- Stitz-Zeager Exercise 1.7.58: shifting `√x` left `1`, reflecting in the y-axis, then up `2` gives
`√(-x+1) + 2`. -/
@[kb "stitzzeager2013" "Exercise 1.7.58, p. 154"]
theorem exer_1_7_58 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => (fun t => f (t + 1)) (-x) + 2) = fun x => √(-x + 1) + 2 := by
  funext x; simp only [hf]

/-- Stitz-Zeager Exercise 1.7.59: reflecting `√x` in the y-axis, shifting left `1`, then up `2` gives
`√(-(x+1)) + 2 = √(-x-1) + 2`, which differs from the function of Exercise 1.7.58 (at `x = 0` the values are `2`
and `3`). -/
@[kb "stitzzeager2013" "Exercise 1.7.59, p. 154"]
theorem exer_1_7_59 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    ((fun x => (fun t => f (-t)) (x + 1) + 2) = fun x => √(-x - 1) + 2) ∧
      (fun x => √(-x - 1) + 2) ≠ fun x => √(-x + 1) + 2 := by
  refine ⟨?_, fun h => ?_⟩
  · funext x
    simp only [hf]
    rw [show -(x + 1) = -x - 1 by ring]
  · have := congrFun h 0
    have h0 : √(-0 - 1 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
    simp only [h0] at this
    norm_num at this

/-- Stitz-Zeager Exercise 1.7.60: shifting `√x` left `3`, stretching vertically by `2`, then down `4` gives
`2√(x+3) - 4`. -/
@[kb "stitzzeager2013" "Exercise 1.7.60, p. 154"]
theorem exer_1_7_60 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => 2 * f (x + 3) - 4) = fun x => 2 * √(x + 3) - 4 := by
  funext x; rw [hf]

/-- Stitz-Zeager Exercise 1.7.61: shifting `√x` left `3`, down `4`, then stretching vertically by `2` gives
`2(√(x+3) - 4) = 2√(x+3) - 8`. -/
@[kb "stitzzeager2013" "Exercise 1.7.61, p. 154"]
theorem exer_1_7_61 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => 2 * (f (x + 3) - 4)) = fun x => 2 * √(x + 3) - 8 := by
  funext x; rw [hf]; ring

/-- Stitz-Zeager Exercise 1.7.62: shifting `√x` right `3`, shrinking horizontally by `2`, then up `1` gives
`√(2x - 3) + 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.62, p. 154"]
theorem exer_1_7_62 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => (fun t => f (t - 3)) (2 * x) + 1) = fun x => √(2 * x - 3) + 1 := by
  funext x; simp only [hf]

/-- Stitz-Zeager Exercise 1.7.63: shrinking `√x` horizontally by `2`, shifting right `3`, then up `1` gives
`√(2(x-3)) + 1 = √(2x - 6) + 1`. -/
@[kb "stitzzeager2013" "Exercise 1.7.63, p. 154"]
theorem exer_1_7_63 (f : ℝ → ℝ) (hf : ∀ x, f x = √x) :
    (fun x => (fun t => f (2 * t)) (x - 3) + 1) = fun x => √(2 * x - 6) + 1 := by
  funext x
  simp only [hf]
  rw [show 2 * (x - 3) = 2 * x - 6 by ring]

end UndergradKB.Precalculus.Course
