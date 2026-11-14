import Mathlib.Analysis.Real.Sqrt
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 7 (Stitz-Zeager): worked examples

Circles, parabolas, ellipses and hyperbolas: the equations, focus/directrix descriptions and
numeric data established by the worked examples of Sections 7.2 to 7.5.
-/

namespace UndergradKB.Precalculus.Course

private lemma sqrt_eq_iff_sq' {A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r) :
    Real.sqrt A = r ↔ A = r ^ 2 := by
  constructor
  · intro h
    rw [← h, Real.sq_sqrt hA]
  · intro h
    rw [h, Real.sqrt_sq hr]

private lemma sqrt_eq_abs_iff' {A b : ℝ} (hA : 0 ≤ A) :
    Real.sqrt A = |b| ↔ A = b ^ 2 := by
  rw [sqrt_eq_iff_sq' hA (abs_nonneg b), sq_abs]

/-- Stitz-Zeager Example 7.2.1: the points at distance 5 from `(-2, 3)` are exactly the
solutions of `(x+2)^2 + (y-3)^2 = 25`. -/
@[kb "stitzzeager2013" "Example 7.2.1, p. 510"]
theorem ex_7_2_1_circle (x y : ℝ) :
    Real.sqrt ((x - (-2)) ^ 2 + (y - 3) ^ 2) = 5 ↔ (x + 2) ^ 2 + (y - 3) ^ 2 = 25 := by
  rw [sqrt_eq_iff_sq' (by positivity) (by norm_num)]
  norm_num [sub_neg_eq_add]

/-- Stitz-Zeager Example 7.2.2: `(x+2)^2 + (y-1)^2 = 4` is the circle of radius 2 about
`(-2, 1)`. -/
@[kb "stitzzeager2013" "Example 7.2.2, p. 510"]
theorem ex_7_2_2_center_radius (x y : ℝ) :
    (x + 2) ^ 2 + (y - 1) ^ 2 = 4 ↔ Real.sqrt ((x - (-2)) ^ 2 + (y - 1) ^ 2) = 2 := by
  rw [sqrt_eq_iff_sq' (by positivity) (by norm_num)]
  norm_num [sub_neg_eq_add]

/-- Stitz-Zeager Example 7.2.3: completing squares turns `3x^2 - 6x + 3y^2 + 4y - 4 = 0` into
the circle `(x-1)^2 + (y+2/3)^2 = 25/9` (center `(1, -2/3)`, radius `5/3`). -/
@[kb "stitzzeager2013" "Example 7.2.3, p. 511"]
theorem ex_7_2_3_complete_square (x y : ℝ) :
    3 * x ^ 2 - 6 * x + 3 * y ^ 2 + 4 * y - 4 = 0 ↔ (x - 1) ^ 2 + (y + 2 / 3) ^ 2 = 25 / 9 := by
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.2.5: the points of the unit circle with `y = √3/2` are
`(1/2, √3/2)` and `(-1/2, √3/2)`. -/
@[kb "stitzzeager2013" "Example 7.2.5, p. 513"]
theorem ex_7_2_5_unit_circle (x y : ℝ) :
    (x ^ 2 + y ^ 2 = 1 ∧ y = Real.sqrt 3 / 2) ↔ ((x = 1 / 2 ∨ x = -1 / 2) ∧ y = Real.sqrt 3 / 2) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨?_, rfl⟩
    have : (x - 1 / 2) * (x + 1 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro ⟨h | h, rfl⟩ <;> refine ⟨?_, rfl⟩ <;> rw [h] <;> nlinarith

/-- Stitz-Zeager Example 7.3.1: the parabola `(x+1)^2 = -8(y-3)` is the set of points equally
far from the focus `(-1, 1)` and the directrix `y = 5`. -/
@[kb "stitzzeager2013" "Example 7.3.1, p. 518"]
theorem ex_7_3_1_focus_directrix (x y : ℝ) :
    Real.sqrt ((x + 1) ^ 2 + (y - 1) ^ 2) = |y - 5| ↔ (x + 1) ^ 2 = -8 * (y - 3) := by
  rw [sqrt_eq_abs_iff' (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.3.2: the points equidistant from the focus `(2, 1)` and the line
`y = -4` satisfy `(x-2)^2 = 10 (y + 3/2)`. -/
@[kb "stitzzeager2013" "Example 7.3.2, p. 519"]
theorem ex_7_3_2_parabola_equation (x y : ℝ) :
    Real.sqrt ((x - 2) ^ 2 + (y - 1) ^ 2) = |y + 4| ↔ (x - 2) ^ 2 = 10 * (y + 3 / 2) := by
  rw [sqrt_eq_abs_iff' (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.3.3: the parabola `(y-2)^2 = 12(x+1)` is the set of points equally
far from the focus `(2, 2)` and the directrix `x = -4`. -/
@[kb "stitzzeager2013" "Example 7.3.3, p. 521"]
theorem ex_7_3_3_focus_directrix (x y : ℝ) :
    Real.sqrt ((x - 2) ^ 2 + (y - 2) ^ 2) = |x + 4| ↔ (y - 2) ^ 2 = 12 * (x + 1) := by
  rw [sqrt_eq_abs_iff' (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.3.4(a): `y^2 + 4y + 8x = 4` is the parabola `(y+2)^2 = -8(x-1)`. -/
@[kb "stitzzeager2013" "Example 7.3.4, p. 521"]
theorem ex_7_3_4_a_standard_form (x y : ℝ) :
    y ^ 2 + 4 * y + 8 * x = 4 ↔ (y + 2) ^ 2 = -8 * (x - 1) := by
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.3.4(b): that parabola has focus `(-1, -2)` and directrix `x = 3`. -/
@[kb "stitzzeager2013" "Example 7.3.4, p. 521"]
theorem ex_7_3_4_b_focus_directrix (x y : ℝ) :
    Real.sqrt ((x + 1) ^ 2 + (y + 2) ^ 2) = |x - 3| ↔ (y + 2) ^ 2 = -8 * (x - 1) := by
  rw [sqrt_eq_abs_iff' (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.3.5: on the dish `x^2 = 8y`, the rim point `x = 6` sits at height
`y = 9/2`. -/
@[kb "stitzzeager2013" "Example 7.3.5, p. 523"]
theorem ex_7_3_5_dish_depth (y : ℝ) : (6 : ℝ) ^ 2 = 8 * y ↔ y = 9 / 2 := by
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.4.1: for `(x+1)^2/9 + (y-2)^2/25 = 1`, the vertices `(-1, 7)`,
`(-1, -3)` and minor-axis endpoints `(-4, 2)`, `(2, 2)` lie on the curve, and `c = 4`. -/
@[kb "stitzzeager2013" "Example 7.4.1, p. 531"]
theorem ex_7_4_1_ellipse_points :
    ((-1 + 1) ^ 2 / 9 + (7 - 2) ^ 2 / 25 = (1 : ℝ)) ∧ ((-1 + 1) ^ 2 / 9 + (-3 - 2) ^ 2 / 25 = (1 : ℝ)) ∧
    ((-4 + 1) ^ 2 / 9 + (2 - 2) ^ 2 / 25 = (1 : ℝ)) ∧ ((2 + 1) ^ 2 / 9 + (2 - 2) ^ 2 / 25 = (1 : ℝ)) ∧
    Real.sqrt (25 - 9) = 4 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [show (25 : ℝ) - 9 = 4 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Stitz-Zeager Example 7.4.2: with `a^2 = 9` and focal distance `c = 1`, the ellipse has
`b^2 = 8`, and the vertex `(0, 1)` lies on `(x-3)^2/9 + (y-1)^2/8 = 1`. -/
@[kb "stitzzeager2013" "Example 7.4.2, p. 532"]
theorem ex_7_4_2_ellipse_equation (b2 : ℝ) :
    (Real.sqrt (9 - b2) = 1 ↔ b2 = 8) ∧ ((0 - 3) ^ 2 / 9 + (1 - 1) ^ 2 / 8 = (1 : ℝ)) := by
  refine ⟨?_, by norm_num⟩
  rw [Real.sqrt_eq_one]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 7.4.3(a): `x^2 + 4y^2 - 2x + 24y + 33 = 0` is the ellipse
`(x-1)^2/4 + (y+3)^2/1 = 1`. -/
@[kb "stitzzeager2013" "Example 7.4.3, p. 533"]
theorem ex_7_4_3_a_standard_form (x y : ℝ) :
    x ^ 2 + 4 * y ^ 2 - 2 * x + 24 * y + 33 = 0 ↔ (x - 1) ^ 2 / 4 + (y + 3) ^ 2 / 1 = 1 := by
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.4.3(b): that ellipse has vertices `(-1, -3)`, `(3, -3)` and minor-axis
endpoints `(1, -2)`, `(1, -4)`, and `c = √3`. -/
@[kb "stitzzeager2013" "Example 7.4.3, p. 533"]
theorem ex_7_4_3_b_points :
    ((-1 - 1) ^ 2 / 4 + (-3 + 3) ^ 2 / 1 = (1 : ℝ)) ∧ ((3 - 1) ^ 2 / 4 + (-3 + 3) ^ 2 / 1 = (1 : ℝ)) ∧
    ((1 - 1) ^ 2 / 4 + (-2 + 3) ^ 2 / 1 = (1 : ℝ)) ∧ ((1 - 1) ^ 2 / 4 + (-4 + 3) ^ 2 / 1 = (1 : ℝ)) ∧
    Real.sqrt (4 - 1) = Real.sqrt 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Stitz-Zeager Example 7.4.4: vertices `(±5, 0)` and eccentricity `1/4` force `b^2 = 375/16`
(the focal distance `c = √(25 - b^2)` has `c / 5 = 1/4`). -/
@[kb "stitzzeager2013" "Example 7.4.4, p. 534"]
theorem ex_7_4_4_eccentricity (b2 : ℝ) :
    Real.sqrt (25 - b2) / 5 = 1 / 4 ↔ b2 = 375 / 16 := by
  have key : Real.sqrt (25 - b2) / 5 = 1 / 4 ↔ Real.sqrt (25 - b2) = 5 / 4 := by
    constructor <;> intro h <;> linarith
  rw [key]
  constructor
  · intro h
    have h0 : 0 ≤ 25 - b2 := by
      by_contra hn
      rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hn).le] at h
      norm_num at h
    have := Real.sq_sqrt h0
    rw [h] at this
    linarith
  · intro h
    rw [h, show (25 : ℝ) - 375 / 16 = (5 / 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)

/-- Stitz-Zeager Example 7.4.5: for the gallery ellipse with `a = 50`, `b = 40`, the focal
distance is `c = 30`, so each person stands `50 - 30 = 20` feet from the wall. -/
@[kb "stitzzeager2013" "Example 7.4.5, p. 535"]
theorem ex_7_4_5_whispering_gallery :
    Real.sqrt (50 ^ 2 - 40 ^ 2) = 30 ∧ (50 - 30 : ℝ) = 20 := by
  refine ⟨?_, by norm_num⟩
  rw [show (50 : ℝ) ^ 2 - 40 ^ 2 = 30 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Stitz-Zeager Example 7.5.1(a): for `(x-2)^2/4 - y^2/25 = 1` the vertices `(0, 0)` and
`(4, 0)` lie on the curve, and `c = √29`. -/
@[kb "stitzzeager2013" "Example 7.5.1, p. 547"]
theorem ex_7_5_1_a_vertices_foci :
    ((0 - 2) ^ 2 / 4 - (0 : ℝ) ^ 2 / 25 = 1) ∧ ((4 - 2) ^ 2 / 4 - (0 : ℝ) ^ 2 / 25 = 1) ∧
    Real.sqrt (4 + 25) = Real.sqrt 29 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- Stitz-Zeager Example 7.5.1(b): the curve `(x-2)^2/4 - y^2/25 = 1` is the locus where the
product of `y - (5x/2 - 5)` and `y - (-5x/2 + 5)` equals `-25`, so it is asymptotic to the lines
`y = ±(5/2)(x-2)`. -/
@[kb "stitzzeager2013" "Example 7.5.1, p. 547"]
theorem ex_7_5_1_b_asymptotes (x y : ℝ) :
    (x - 2) ^ 2 / 4 - y ^ 2 / 25 = 1 ↔
      (y - (5 / 2 * x - 5)) * (y - (-5 / 2 * x + 5)) = -25 := by
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.5.2: vertices `(±5, 0)` and an asymptote of slope 2 give `b = 10`
(so `b^2 = 100`), and `x^2/25 - y^2/100 = 1` has asymptotes `y = ±2x`. -/
@[kb "stitzzeager2013" "Example 7.5.2, p. 548"]
theorem ex_7_5_2_hyperbola_equation (b x y : ℝ) (hb : 0 < b) :
    (b / 5 = 2 ↔ b ^ 2 = 100) ∧
      (x ^ 2 / 25 - y ^ 2 / 100 = 1 ↔ (y - 2 * x) * (y + 2 * x) = -100) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      have : b = 10 := by linarith
      rw [this]; norm_num
    · intro h
      nlinarith
  · constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.5.3(a): `9y^2 - x^2 - 6x = 10` is the hyperbola
`y^2/(1/9) - (x+3)^2/1 = 1`. -/
@[kb "stitzzeager2013" "Example 7.5.3, p. 549"]
theorem ex_7_5_3_a_standard_form (x y : ℝ) :
    9 * y ^ 2 - x ^ 2 - 6 * x = 10 ↔ y ^ 2 / (1 / 9) - (x + 3) ^ 2 / 1 = 1 := by
  have e : y ^ 2 / (1 / 9 : ℝ) - (x + 3) ^ 2 / 1 = 9 * y ^ 2 - (x + 3) ^ 2 := by ring
  rw [e]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.5.3(b): the vertices `(-3, ±1/3)` lie on the curve, `c = √10/3`,
and the curve is asymptotic to `y = ±(x/3 + 1)`. -/
@[kb "stitzzeager2013" "Example 7.5.3, p. 549"]
theorem ex_7_5_3_b_vertices_foci_asymptotes (x y : ℝ) :
    (9 * (1 / 3 : ℝ) ^ 2 - (-3 + 3) ^ 2 = 1) ∧ (9 * (-1 / 3 : ℝ) ^ 2 - (-3 + 3) ^ 2 = 1) ∧
    Real.sqrt (1 / 9 + 1) = Real.sqrt 10 / 3 ∧
    (9 * y ^ 2 - (x + 3) ^ 2 = 1 ↔ (y - (x / 3 + 1)) * (y + (x / 3 + 1)) = 1 / 9) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [show (1 / 9 + 1 : ℝ) = 10 / 9 by norm_num, Real.sqrt_div (by norm_num)]
    congr 1
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  · constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 7.5.4: the 9-second lead at 760 mph is a 1.9 mile difference
(`a = 19/20`), so `a^2 = 361/400` and `b^2 = 25 - a^2 = 9639/400`. -/
@[kb "stitzzeager2013" "Example 7.5.4, p. 550"]
theorem ex_7_5_4_sasquatch_hyperbola :
    (760 * (1 / 3600) * 9 = (19 / 10 : ℝ)) ∧ ((19 / 10 / 2) ^ 2 = (361 / 400 : ℝ)) ∧
    ((5 : ℝ) ^ 2 - 361 / 400 = 9639 / 400) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Stitz-Zeager Example 7.5.5: the 18-second lead gives difference 3.8 miles (`b = 19/10`),
so `b^2 = 361/100` and `a^2 = 9 - b^2 = 539/100`. -/
@[kb "stitzzeager2013" "Example 7.5.5, p. 551"]
theorem ex_7_5_5_sasquatch_second_hyperbola :
    (760 * (1 / 3600) * 18 = (19 / 5 : ℝ)) ∧ ((19 / 5 / 2) ^ 2 = (361 / 100 : ℝ)) ∧
    ((3 : ℝ) ^ 2 - 361 / 100 = 539 / 100) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end UndergradKB.Precalculus.Course
