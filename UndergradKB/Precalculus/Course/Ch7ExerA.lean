import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Precalculus.Conics
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 7 (Stitz-Zeager): exercises with the book's answers, Sections 7.2 and 7.3 -/

namespace UndergradKB.Precalculus.Course

open UndergradKB.Precalculus

/-! ## Helpers -/

private theorem pv (h k p f d x y : ℝ) (hf : f = k + p) (hd : d = k - p) :
    edist2 (x, y) (h, f) = distToLine 0 1 d (x, y) ↔ (x - h) ^ 2 = 4 * p * (y - k) := by
  subst hf hd; exact parabola_vertical_equation h k p x y

private theorem ph (h k p f d x y : ℝ) (hf : f = h + p) (hd : d = h - p) :
    edist2 (x, y) (f, k) = distToLine 1 0 d (x, y) ↔ (y - k) ^ 2 = 4 * p * (x - h) := by
  subst hf hd; exact parabola_horizontal_equation h k p x y

/-! ## 7.2 Circles -/

/-- Stitz-Zeager Exercise 7.2.1: the circle with center `(-1,-5)` and radius `10` has equation
`(x+1)² + (y+5)² = 100`. -/
@[kb "stitzzeager2013" "Exercise 7.2.1, p. 514"]
theorem exer_7_2_1 : ∀ x y : ℝ, edist2 (x, y) (-1, -5) = 10 ↔ (x + 1) ^ 2 + (y + 5) ^ 2 = 100 := by
  intro x y
  rw [circle_mem_iff_equation (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.2: the circle with center `(4,-2)` and radius `3` has equation
`(x-4)² + (y+2)² = 9`. -/
@[kb "stitzzeager2013" "Exercise 7.2.2, p. 514"]
theorem exer_7_2_2 : ∀ x y : ℝ, edist2 (x, y) (4, -2) = 3 ↔ (x - 4) ^ 2 + (y + 2) ^ 2 = 9 := by
  intro x y
  rw [circle_mem_iff_equation (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.4: the circle with center `(5,-9)` and radius `ln 8` has equation
`(x-5)² + (y+9)² = (ln 8)²`. -/
@[kb "stitzzeager2013" "Exercise 7.2.4, p. 514"]
theorem exer_7_2_4 : ∀ x y : ℝ,
    edist2 (x, y) (5, -9) = Real.log 8 ↔ (x - 5) ^ 2 + (y + 9) ^ 2 = Real.log 8 ^ 2 := by
  intro x y
  rw [circle_mem_iff_equation (Real.log_pos (by norm_num))]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.7: `x² - 4x + y² + 10y = -25` is the circle with center `(2,-5)` and radius `2`. -/
@[kb "stitzzeager2013" "Exercise 7.2.7, p. 514"]
theorem exer_7_2_7 : ∀ x y : ℝ, x ^ 2 - 4 * x + y ^ 2 + 10 * y = -25 ↔ edist2 (x, y) (2, -5) = 2 := by
  intro x y
  rw [circle_mem_iff_equation (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.8: `-2x² - 36x - 2y² - 112 = 0` is the circle with center `(-9,0)` and radius `5`. -/
@[kb "stitzzeager2013" "Exercise 7.2.8, p. 514"]
theorem exer_7_2_8 : ∀ x y : ℝ, -2 * x ^ 2 - 36 * x - 2 * y ^ 2 - 112 = 0 ↔ edist2 (x, y) (-9, 0) = 5 := by
  intro x y
  rw [circle_mem_iff_equation (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.9: `x² + y² + 8x - 10y - 1 = 0` is the circle with center `(-4,5)` and radius `√42`. -/
@[kb "stitzzeager2013" "Exercise 7.2.9, p. 514"]
theorem exer_7_2_9 : ∀ x y : ℝ,
    x ^ 2 + y ^ 2 + 8 * x - 10 * y - 1 = 0 ↔ edist2 (x, y) (-4, 5) = √42 := by
  intro x y
  have h42 : √42 ^ 2 = 42 := Real.sq_sqrt (by norm_num)
  rw [circle_mem_iff_equation (Real.sqrt_pos.mpr (by norm_num)), h42]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.10: `x² + y² + 5x - y - 1 = 0` is the circle with center `(-5/2, 1/2)` and
radius `√30 / 2`. -/
@[kb "stitzzeager2013" "Exercise 7.2.10, p. 514"]
theorem exer_7_2_10 : ∀ x y : ℝ,
    x ^ 2 + y ^ 2 + 5 * x - y - 1 = 0 ↔ edist2 (x, y) (-5 / 2, 1 / 2) = √30 / 2 := by
  intro x y
  have h30 : (√30 / 2) ^ 2 = 30 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [circle_mem_iff_equation (by have := Real.sqrt_pos.mpr (show (0 : ℝ) < 30 by norm_num); positivity), h30]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.11: `4x² + 4y² - 24y + 36 = 0` is not a circle: its graph is the single point
`(0,3)`. -/
@[kb "stitzzeager2013" "Exercise 7.2.11, p. 514"]
theorem exer_7_2_11 : ∀ x y : ℝ, 4 * x ^ 2 + 4 * y ^ 2 - 24 * y + 36 = 0 ↔ x = 0 ∧ y = 3 := by
  intro x y
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg (y - 3)]
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 7.2.12: `x² + x + y² - (6/5) y = 1` is the circle with center `(-1/2, 3/5)` and
radius `√161 / 10`. -/
@[kb "stitzzeager2013" "Exercise 7.2.12, p. 514"]
theorem exer_7_2_12 : ∀ x y : ℝ,
    x ^ 2 + x + y ^ 2 - 6 / 5 * y = 1 ↔ edist2 (x, y) (-1 / 2, 3 / 5) = √161 / 10 := by
  intro x y
  have h : (√161 / 10) ^ 2 = 161 / 100 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [circle_mem_iff_equation (by have := Real.sqrt_pos.mpr (show (0 : ℝ) < 161 by norm_num); positivity), h]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.2.13: the circle with center `(3,5)` through `(-1,-2)` is `(x-3)² + (y-5)² = 65`. -/
@[kb "stitzzeager2013" "Exercise 7.2.13, p. 514"]
theorem exer_7_2_13 : ∀ x y : ℝ,
    edist2 (x, y) (3, 5) = edist2 (-1, -2) (3, 5) ↔ (x - 3) ^ 2 + (y - 5) ^ 2 = 65 := by
  intro x y
  unfold edist2
  rw [Real.sqrt_inj (by positivity) (by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.2.14: the circle with center `(3,6)` through `(-1,4)` is `(x-3)² + (y-6)² = 20`. -/
@[kb "stitzzeager2013" "Exercise 7.2.14, p. 514"]
theorem exer_7_2_14 : ∀ x y : ℝ,
    edist2 (x, y) (3, 6) = edist2 (-1, 4) (3, 6) ↔ (x - 3) ^ 2 + (y - 6) ^ 2 = 20 := by
  intro x y
  unfold edist2
  rw [Real.sqrt_inj (by positivity) (by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.2.15: the circle with a diameter from `(3,6)` to `(-1,4)` has center `(1,5)`, radius
`√5`, i.e. equation `(x-1)² + (y-5)² = 5`; both endpoints lie on it. -/
@[kb "stitzzeager2013" "Exercise 7.2.15, p. 514"]
theorem exer_7_2_15 : (∀ x y : ℝ, edist2 (x, y) (1, 5) = √5 ↔ (x - 1) ^ 2 + (y - 5) ^ 2 = 5) ∧
    edist2 (3, 6) (1, 5) = √5 ∧ edist2 (-1, 4) (1, 5) = √5 := by
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [circle_mem_iff_equation (Real.sqrt_pos.mpr (by norm_num)), h5]
  · unfold edist2; norm_num
  · unfold edist2; norm_num

/-- Stitz-Zeager Exercise 7.2.17: the Giant Wheel (diameter `128`, center `(0,72)` on the `y`-axis, ground the
`x`-axis) has equation `x² + (y-72)² = 4096`; its lowest point is at height `8` and its highest at `136`. -/
@[kb "stitzzeager2013" "Exercise 7.2.17, p. 514"]
theorem exer_7_2_17 : (∀ x y : ℝ, edist2 (x, y) (0, 72) = 64 ↔ x ^ 2 + (y - 72) ^ 2 = 4096) ∧
    edist2 (0, 8) (0, 72) = 64 ∧ edist2 (0, 136) (0, 72) = 64 := by
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [circle_mem_iff_equation (by norm_num)]
    constructor <;> intro h <;> linarith
  · unfold edist2
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]; norm_num
  · unfold edist2
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 7.2.18: the points `(±1,0)`, `(0,±1)`, `(±√2/2, ±√2/2)`, `(±1/2, ±√3/2)` and
`(±√3/2, ±1/2)` lie on the unit circle. -/
@[kb "stitzzeager2013" "Exercise 7.2.18, p. 514"]
theorem exer_7_2_18 :
    (∀ s : ℝ, (s = 1 ∨ s = -1) → s ^ 2 + 0 ^ 2 = 1 ∧ 0 ^ 2 + s ^ 2 = 1) ∧
    ∀ s t : ℝ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) →
      (s * (√2 / 2)) ^ 2 + (t * (√2 / 2)) ^ 2 = 1 ∧ (s * (1 / 2)) ^ 2 + (t * (√3 / 2)) ^ 2 = 1 ∧
      (s * (√3 / 2)) ^ 2 + (t * (1 / 2)) ^ 2 = 1 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_⟩
  · rintro s (rfl | rfl) <;> norm_num
  · intro s t hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith [h2, h3]

/-! ## 7.3 Parabolas -/

/-- Stitz-Zeager Exercise 7.3.1: `(x-3)² = -16y` is the parabola with vertex `(3,0)`, focus `(3,-4)` and
directrix `y = 4`. -/
@[kb "stitzzeager2013" "Exercise 7.3.1, p. 524"]
theorem exer_7_3_1 : ∀ x y : ℝ,
    edist2 (x, y) (3, -4) = distToLine 0 1 4 (x, y) ↔ (x - 3) ^ 2 = -16 * y := by
  intro x y
  rw [pv 3 0 (-4) (-4) 4 x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.3: `(y-2)² = -12(x+3)` is the parabola with vertex `(-3,2)`, focus `(-6,2)` and
directrix `x = 0`. -/
@[kb "stitzzeager2013" "Exercise 7.3.3, p. 524"]
theorem exer_7_3_3 : ∀ x y : ℝ,
    edist2 (x, y) (-6, 2) = distToLine 1 0 0 (x, y) ↔ (y - 2) ^ 2 = -12 * (x + 3) := by
  intro x y
  rw [ph (-3) 2 (-3) (-6) 0 x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.4: `(y+4)² = 4x` is the parabola with vertex `(0,-4)`, focus `(1,-4)` and
directrix `x = -1`. -/
@[kb "stitzzeager2013" "Exercise 7.3.4, p. 524"]
theorem exer_7_3_4 : ∀ x y : ℝ,
    edist2 (x, y) (1, -4) = distToLine 1 0 (-1) (x, y) ↔ (y + 4) ^ 2 = 4 * x := by
  intro x y
  rw [ph 0 (-4) 1 1 (-1) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.5: `(x-1)² = 4(y+3)` is the parabola with vertex `(1,-3)`, focus `(1,-2)` and
directrix `y = -4`. -/
@[kb "stitzzeager2013" "Exercise 7.3.5, p. 524"]
theorem exer_7_3_5 : ∀ x y : ℝ,
    edist2 (x, y) (1, -2) = distToLine 0 1 (-4) (x, y) ↔ (x - 1) ^ 2 = 4 * (y + 3) := by
  intro x y
  rw [pv 1 (-3) 1 (-2) (-4) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.6: `(x+2)² = -20(y-5)` is the parabola with vertex `(-2,5)`, focus `(-2,0)` and
directrix `y = 10`. -/
@[kb "stitzzeager2013" "Exercise 7.3.6, p. 524"]
theorem exer_7_3_6 : ∀ x y : ℝ,
    edist2 (x, y) (-2, 0) = distToLine 0 1 10 (x, y) ↔ (x + 2) ^ 2 = -20 * (y - 5) := by
  intro x y
  rw [pv (-2) 5 (-5) 0 10 x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.7: `(y-4)² = 18(x-2)` is the parabola with vertex `(2,4)`, focus `(13/2, 4)` and
directrix `x = -5/2`. -/
@[kb "stitzzeager2013" "Exercise 7.3.7, p. 524"]
theorem exer_7_3_7 : ∀ x y : ℝ,
    edist2 (x, y) (13 / 2, 4) = distToLine 1 0 (-5 / 2) (x, y) ↔ (y - 4) ^ 2 = 18 * (x - 2) := by
  intro x y
  rw [ph 2 4 (9 / 2) (13 / 2) (-5 / 2) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.9: `y² - 10y - 27x + 133 = 0` is the parabola `(y-5)² = 27(x-4)` with vertex
`(4,5)`, focus `(43/4, 5)` and directrix `x = -11/4`. -/
@[kb "stitzzeager2013" "Exercise 7.3.9, p. 524"]
theorem exer_7_3_9 : ∀ x y : ℝ,
    y ^ 2 - 10 * y - 27 * x + 133 = 0 ↔
      edist2 (x, y) (43 / 4, 5) = distToLine 1 0 (-11 / 4) (x, y) := by
  intro x y
  rw [ph 4 5 (27 / 4) (43 / 4) (-11 / 4) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.10: `25x² + 20x + 5y - 1 = 0` is the parabola `(x+2/5)² = -(1/5)(y-1)` with
vertex `(-2/5, 1)`, focus `(-2/5, 19/20)` and directrix `y = 21/20`. -/
@[kb "stitzzeager2013" "Exercise 7.3.10, p. 524"]
theorem exer_7_3_10 : ∀ x y : ℝ,
    25 * x ^ 2 + 20 * x + 5 * y - 1 = 0 ↔
      edist2 (x, y) (-2 / 5, 19 / 20) = distToLine 0 1 (21 / 20) (x, y) := by
  intro x y
  rw [pv (-2 / 5) 1 (-1 / 20) (19 / 20) (21 / 20) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.11: `x² + 2x - 8y + 49 = 0` is the parabola `(x+1)² = 8(y-6)` with vertex `(-1,6)`,
focus `(-1,8)` and directrix `y = 4`. -/
@[kb "stitzzeager2013" "Exercise 7.3.11, p. 524"]
theorem exer_7_3_11 : ∀ x y : ℝ,
    x ^ 2 + 2 * x - 8 * y + 49 = 0 ↔ edist2 (x, y) (-1, 8) = distToLine 0 1 4 (x, y) := by
  intro x y
  rw [pv (-1) 6 2 8 4 x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.12: `2y² + 4y + x - 8 = 0` is the parabola `(y+1)² = -(1/2)(x-10)` with vertex
`(10,-1)`, focus `(79/8, -1)` and directrix `x = 81/8`. -/
@[kb "stitzzeager2013" "Exercise 7.3.12, p. 524"]
theorem exer_7_3_12 : ∀ x y : ℝ,
    2 * y ^ 2 + 4 * y + x - 8 = 0 ↔
      edist2 (x, y) (79 / 8, -1) = distToLine 1 0 (81 / 8) (x, y) := by
  intro x y
  rw [ph 10 (-1) (-1 / 8) (79 / 8) (81 / 8) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.13: `x² - 10x + 12y + 1 = 0` is the parabola `(x-5)² = -12(y-2)` with vertex
`(5,2)`, focus `(5,-1)` and directrix `y = 5`. -/
@[kb "stitzzeager2013" "Exercise 7.3.13, p. 524"]
theorem exer_7_3_13 : ∀ x y : ℝ,
    x ^ 2 - 10 * x + 12 * y + 1 = 0 ↔ edist2 (x, y) (5, -1) = distToLine 0 1 5 (x, y) := by
  intro x y
  rw [pv 5 2 (-3) (-1) 5 x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.15: the parabola with vertex `(7,0)` and focus `(0,0)` has equation
`y² = -28(x-7)`. -/
@[kb "stitzzeager2013" "Exercise 7.3.15, p. 524"]
theorem exer_7_3_15 : ∀ x y : ℝ,
    edist2 (x, y) (0, 0) = distToLine 1 0 14 (x, y) ↔ y ^ 2 = -28 * (x - 7) := by
  intro x y
  rw [ph 7 0 (-7) 0 14 x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.16: the parabola with focus `(10,1)` and directrix `x = 5` has equation
`(y-1)² = 10(x - 15/2)`. -/
@[kb "stitzzeager2013" "Exercise 7.3.16, p. 524"]
theorem exer_7_3_16 : ∀ x y : ℝ,
    edist2 (x, y) (10, 1) = distToLine 1 0 5 (x, y) ↔ (y - 1) ^ 2 = 10 * (x - 15 / 2) := by
  intro x y
  rw [ph (15 / 2) 1 (5 / 2) 10 5 x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.17: the parabola `(x+8)² = (64/9)(y+9)` has vertex `(-8,-9)` and passes through
`(0,0)` and `(-16,0)`; conversely any parabola `(x+8)² = c (y+9)` through `(0,0)` has `c = 64/9`. -/
@[kb "stitzzeager2013" "Exercise 7.3.17, p. 524"]
theorem exer_7_3_17 : (0 + 8 : ℝ) ^ 2 = 64 / 9 * (0 + 9) ∧ (-16 + 8 : ℝ) ^ 2 = 64 / 9 * (0 + 9) ∧
    ∀ c : ℝ, (0 + 8 : ℝ) ^ 2 = c * (0 + 9) → c = 64 / 9 := by
  refine ⟨by norm_num, by norm_num, fun c h => by linarith⟩

/-- Stitz-Zeager Exercise 7.3.19: the flashlight mirror `x² = 4p y` (diameter 5, depth 5/2, so the rim point is
`(5/2, 5/2)`) has `p = 5/8 = 0.625`: the bulb goes `0.625` cm above the vertex. -/
@[kb "stitzzeager2013" "Exercise 7.3.19, p. 524"]
theorem exer_7_3_19 : ∀ p : ℝ, (5 / 2) ^ 2 = 4 * p * (5 / 2) ↔ p = 5 / 8 := by
  intro p
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.20: the Wi-Fi dish cross-section `x² = 4p y` with rim point `(45/2, 25)` has
`p = 81/16 = 5.0625`: the receiver goes `5.0625` cm from the vertex. -/
@[kb "stitzzeager2013" "Exercise 7.3.20, p. 524"]
theorem exer_7_3_20 : ∀ p : ℝ, (45 / 2) ^ 2 = 4 * p * 25 ↔ p = 81 / 16 := by
  intro p
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.3.21: a parabolic arch `y = a x² + 9` that is `9` feet tall in the middle and `6` feet
wide at the base (zero height at `x = ±3`) is `y = 9 - x²`, and one foot in from the base (`x = ±2`) it is `5`
feet high. -/
@[kb "stitzzeager2013" "Exercise 7.3.21, p. 524"]
theorem exer_7_3_21 : ∀ a : ℝ, a * 3 ^ 2 + 9 = 0 → a = -1 ∧ a * 2 ^ 2 + 9 = 5 ∧ a * (-2) ^ 2 + 9 = 5 := by
  intro a h
  have ha : a = -1 := by linarith
  subst ha; norm_num

end UndergradKB.Precalculus.Course
