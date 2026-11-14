import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 2.2 -/

/-- Stitz-Zeager Example 2.2.2(1): `f(x) = |x|` has the single zero `0`, `f(0) = 0`, range `[0,∞)`, is strictly
decreasing on `(-∞,0]` and strictly increasing on `[0,∞)`, and `0` is its absolute minimum value. -/
@[kb "stitzzeager2013" "Example 2.2.2, p. 187"]
theorem ex_2_2_2_a_abs :
    (∀ x : ℝ, |x| = 0 ↔ x = 0) ∧ |(0 : ℝ)| = 0 ∧ (range fun x : ℝ => |x|) = Ici 0 ∧
      StrictAntiOn (fun x : ℝ => |x|) (Iic 0) ∧ StrictMonoOn (fun x : ℝ => |x|) (Ici 0) ∧
      (∀ x : ℝ, |(0 : ℝ)| ≤ |x|) := by
  refine ⟨fun x => abs_eq_zero, abs_zero, ?_, ?_, ?_, fun x => by simp⟩
  · ext y
    exact ⟨by rintro ⟨x, rfl⟩; exact abs_nonneg x, fun hy => ⟨y, abs_of_nonneg hy⟩⟩
  · intro a ha b hb hab
    simp only [mem_Iic] at ha hb
    show |b| < |a|
    rw [abs_of_nonpos ha, abs_of_nonpos hb]; linarith
  · intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    show |a| < |b|
    rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact hab

/-- Stitz-Zeager Example 2.2.2(2): `g(x) = |x-3|` has the single zero `3`, `g(0) = 3`, the pieces `-x+3` (for
`x < 3`) and `x-3` (for `x ≥ 3`), range `[0,∞)`, is decreasing on `(-∞,3]`, increasing on `[3,∞)`, with minimum `0`. -/
@[kb "stitzzeager2013" "Example 2.2.2, p. 187"]
theorem ex_2_2_2_b_abs_shift :
    (∀ x : ℝ, |x - 3| = 0 ↔ x = 3) ∧ |(0 : ℝ) - 3| = 3 ∧
      (∀ x : ℝ, |x - 3| = if x < 3 then -x + 3 else x - 3) ∧
      (range fun x : ℝ => |x - 3|) = Ici 0 ∧
      StrictAntiOn (fun x : ℝ => |x - 3|) (Iic 3) ∧ StrictMonoOn (fun x : ℝ => |x - 3|) (Ici 3) ∧
      (∀ x : ℝ, |(3 : ℝ) - 3| ≤ |x - 3|) := by
  refine ⟨fun x => by rw [abs_eq_zero, sub_eq_zero], by norm_num, fun x => ?_, ?_, ?_, ?_, fun x => by simp⟩
  · split_ifs with h
    · rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith)]
  · ext y
    exact ⟨by rintro ⟨x, rfl⟩; exact abs_nonneg (x - 3), fun hy => ⟨y + 3, by
      show |y + 3 - 3| = y
      rw [add_sub_cancel_right]; exact abs_of_nonneg (mem_Ici.1 hy)⟩⟩
  · intro a ha b hb hab
    simp only [mem_Iic] at ha hb
    show |b - 3| < |a - 3|
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    show |a - 3| < |b - 3|
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- Stitz-Zeager Example 2.2.2(3): `h(x) = |x| - 3` has the zeros `±3`, `h(0) = -3`, range `[-3,∞)`, is decreasing
on `(-∞,0]`, increasing on `[0,∞)`, with absolute minimum value `-3` at `x = 0`. -/
@[kb "stitzzeager2013" "Example 2.2.2, p. 187"]
theorem ex_2_2_2_c_abs_down :
    (∀ x : ℝ, |x| - 3 = 0 ↔ x = 3 ∨ x = -3) ∧ |(0 : ℝ)| - 3 = -3 ∧
      (range fun x : ℝ => |x| - 3) = Ici (-3) ∧
      StrictAntiOn (fun x : ℝ => |x| - 3) (Iic 0) ∧ StrictMonoOn (fun x : ℝ => |x| - 3) (Ici 0) ∧
      (∀ x : ℝ, |(0 : ℝ)| - 3 ≤ |x| - 3) := by
  refine ⟨fun x => ?_, by simp, ?_, ?_, ?_, fun x => by simp⟩
  · rw [sub_eq_zero, abs_eq (by norm_num : (0 : ℝ) ≤ 3)]
  · ext y
    exact ⟨by rintro ⟨x, rfl⟩; have := abs_nonneg x; exact (by linarith : (-3 : ℝ) ≤ |x| - 3),
      fun hy => ⟨y + 3, by
        have hy' := mem_Ici.1 hy
        show |y + 3| - 3 = y
        rw [abs_of_nonneg (by linarith)]; ring⟩⟩
  · intro a ha b hb hab
    simp only [mem_Iic] at ha hb
    show |b| - 3 < |a| - 3
    rw [abs_of_nonpos ha, abs_of_nonpos hb]; linarith
  · intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    show |a| - 3 < |b| - 3
    rw [abs_of_nonneg ha, abs_of_nonneg hb]; linarith

/-- Stitz-Zeager Example 2.2.2(4): `i(x) = 4 - 2|3x+1|` has the zeros `1/3` and `-1`, `i(0) = 2`, the pieces `6x+6`
(for `x < -1/3`) and `-6x+2` (for `x ≥ -1/3`), corner `(-1/3, 4)`, range `(-∞,4]`, is increasing on `(-∞,-1/3]`,
decreasing on `[-1/3,∞)`, with maximum value `4` at `x = -1/3`, and no absolute minimum. -/
@[kb "stitzzeager2013" "Example 2.2.2, p. 187"]
theorem ex_2_2_2_d_abs_flipped :
    (∀ x : ℝ, 4 - 2 * |3 * x + 1| = 0 ↔ x = 1 / 3 ∨ x = -1) ∧ 4 - 2 * |3 * (0 : ℝ) + 1| = 2 ∧
      (∀ x : ℝ, 4 - 2 * |3 * x + 1| = if x < -1 / 3 then 6 * x + 6 else -6 * x + 2) ∧
      4 - 2 * |3 * (-1 / 3 : ℝ) + 1| = 4 ∧ (range fun x : ℝ => 4 - 2 * |3 * x + 1|) = Iic 4 ∧
      StrictMonoOn (fun x : ℝ => 4 - 2 * |3 * x + 1|) (Iic (-1 / 3)) ∧
      StrictAntiOn (fun x : ℝ => 4 - 2 * |3 * x + 1|) (Ici (-1 / 3)) ∧
      (∀ x : ℝ, 4 - 2 * |3 * x + 1| ≤ 4) ∧ (∀ m : ℝ, ∃ x : ℝ, 4 - 2 * |3 * x + 1| < m) := by
  refine ⟨fun x => ?_, by norm_num, fun x => ?_, by norm_num, ?_, ?_, ?_, fun x => ?_, fun m => ?_⟩
  · have : 4 - 2 * |3 * x + 1| = 0 ↔ |3 * x + 1| = 2 := by constructor <;> intro h <;> linarith
    rw [this, abs_eq (by norm_num : (0 : ℝ) ≤ 2)]
    constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith
  · split_ifs with h
    · rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith)]; ring
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      have := abs_nonneg (3 * x + 1)
      exact (by linarith : 4 - 2 * |3 * x + 1| ≤ 4)
    · intro hy
      have hy' := mem_Iic.1 hy
      refine ⟨(4 - y) / 6 - 1 / 3, ?_⟩
      show 4 - 2 * |3 * ((4 - y) / 6 - 1 / 3) + 1| = y
      rw [show 3 * ((4 - y) / 6 - 1 / 3) + 1 = (4 - y) / 2 by ring, abs_of_nonneg (by linarith)]
      ring
  · intro a ha b hb hab
    simp only [mem_Iic] at ha hb
    show 4 - 2 * |3 * a + 1| < 4 - 2 * |3 * b + 1|
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    show 4 - 2 * |3 * b + 1| < 4 - 2 * |3 * a + 1|
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · have := abs_nonneg (3 * x + 1); linarith
  · refine ⟨(|m| + 5) / 3, ?_⟩
    have h1 : 0 ≤ 3 * ((|m| + 5) / 3) + 1 := by have := abs_nonneg m; linarith
    rw [abs_of_nonneg h1]
    have := neg_abs_le m
    linarith

/-- Stitz-Zeager Example 2.2.3: the transformed forms. `g(x) = |x-3| = f(x-3)` moves `(-1,1), (0,0), (1,1)` to
`(2,1), (3,0), (4,1)`; `h(x) = |x| - 3` moves them to `(-1,-2), (0,-3), (1,-2)`; `i(x) = 4 - 2|3x+1| = -2 f(3x+1) + 4`
moves them to `(-2/3, 2)`, `(-1/3, 4)`, `(0, 2)`. -/
@[kb "stitzzeager2013" "Example 2.2.3, p. 191"]
theorem ex_2_2_3_transformed_points :
    (|(2 : ℝ) - 3| = 1 ∧ |(3 : ℝ) - 3| = 0 ∧ |(4 : ℝ) - 3| = 1) ∧
      (|(-1 : ℝ)| - 3 = -2 ∧ |(0 : ℝ)| - 3 = -3 ∧ |(1 : ℝ)| - 3 = -2) ∧
      (∀ x : ℝ, 4 - 2 * |3 * x + 1| = -2 * |3 * x + 1| + 4) ∧
      (-2 * |3 * (-2 / 3 : ℝ) + 1| + 4 = 2 ∧ -2 * |3 * (-1 / 3 : ℝ) + 1| + 4 = 4 ∧
        -2 * |3 * (0 : ℝ) + 1| + 4 = 2) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, fun x => by ring, ?_, ?_, ?_⟩ <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-! ## Section 2.5 -/

/-- Stitz-Zeager Example 2.5.1(2): for the energy data (years `1950, ..., 2000` with `34.6, 45.1, 67.8, 78.3, 84.6,
98.9` quads), the least squares line `y = a x + b` has the exact slope `a = 901/700` and intercept
`b = 409.3/6 - 1975 a`; the slope is about `1.287` and `b` is about `-2473.89`, and its total squared error is at
most that of any other line. -/
@[kb "stitzzeager2013" "Example 2.5.1, p. 238"]
theorem ex_2_5_1_least_squares_line :
    let err : ℝ → ℝ → ℝ := fun a b =>
      (a * 1950 + b - 34.6) ^ 2 + (a * 1960 + b - 45.1) ^ 2 + (a * 1970 + b - 67.8) ^ 2 +
        (a * 1980 + b - 78.3) ^ 2 + (a * 1990 + b - 84.6) ^ 2 + (a * 2000 + b - 98.9) ^ 2
    (∀ a' b' : ℝ, err (901 / 700) (409.3 / 6 - 1975 * (901 / 700)) ≤ err a' b') ∧
      (1.286 < (901 / 700 : ℝ) ∧ (901 / 700 : ℝ) < 1.288) ∧
      (-2473.9 < 409.3 / 6 - 1975 * (901 / 700 : ℝ) ∧ 409.3 / 6 - 1975 * (901 / 700 : ℝ) < -2473.8) := by
  intro err
  refine ⟨fun a' b' => ?_, by norm_num, by norm_num⟩
  show _ ≤ _
  simp only [err]
  nlinarith [sq_nonneg (6 * (b' - (409.3 / 6 - 1975 * (901 / 700)) + 1975 * (a' - 901 / 700))),
    sq_nonneg (a' - 901 / 700)]

/-- Stitz-Zeager Example 2.5.1(4,5): the regression line `y = 901/700 · x + b` predicts, for the year `2013`, a value
between `117.1` and `117.2` quads (the book's `116.841` uses a rounded line), and reaches `120` quads in the year `x` with `2015 < x < 2016`. -/
@[kb "stitzzeager2013" "Example 2.5.1, p. 238"]
theorem ex_2_5_1_predictions :
    (117.1 < (901 / 700 : ℝ) * 2013 + (409.3 / 6 - 1975 * (901 / 700)) ∧
      (901 / 700 : ℝ) * 2013 + (409.3 / 6 - 1975 * (901 / 700)) < 117.2) ∧
      ∃ x : ℝ, 2015 < x ∧ x < 2016 ∧
        (901 / 700 : ℝ) * x + (409.3 / 6 - 1975 * (901 / 700)) = 120 := by
  refine ⟨by norm_num, (120 - (409.3 / 6 - 1975 * (901 / 700))) / (901 / 700), ?_, ?_, ?_⟩ <;>
    norm_num

/-- Stitz-Zeager Example 2.5.2: for the quadratic model `T(x) = -0.321x² + 9.464x - 45.857`, the maximum is at the
vertex `x = 9.464/0.642`, between `14.74` and `14.75` (about 2:45 PM), with maximum value between `23.89` and `23.91`. -/
@[kb "stitzzeager2013" "Example 2.5.2, p. 241"]
theorem ex_2_5_2_warmest_temperature :
    let T : ℝ → ℝ := fun x => -0.321 * x ^ 2 + 9.464 * x - 45.857
    (∀ x : ℝ, T x ≤ T (9.464 / 0.642)) ∧ (14.74 < (9.464 / 0.642 : ℝ) ∧ (9.464 / 0.642 : ℝ) < 14.75) ∧
      (23.89 < T (9.464 / 0.642) ∧ T (9.464 / 0.642) < 23.91) := by
  intro T
  refine ⟨fun x => ?_, by norm_num, by simp only [T]; norm_num⟩
  simp only [T]
  nlinarith [sq_nonneg (x - 9.464 / 0.642)]

end UndergradKB.Precalculus.Course
