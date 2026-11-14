import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Precalculus.Conics
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 7 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 7.2-7.5 -/

namespace UndergradKB.Precalculus.Course

open UndergradKB.Precalculus

/-! ## Helpers -/

/-- Closes the small numeric side conditions (square roots of numerals, inequalities between them). -/
local macro "kbs" : tactic =>
  `(tactic| first
    | (positivity; done)
    | (norm_num; done)
    | (simp [Real.sq_sqrt, mul_pow]; done)
    | (simp [Real.sq_sqrt, mul_pow]; norm_num; done)
    | (rw [Real.lt_sqrt (by norm_num)]; norm_num; done)
    | (rw [Real.sqrt_lt' (by norm_num)]; norm_num; done)
    | (exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num))
    | (nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]))

private theorem eH {a b c A B : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a) (hb : b ^ 2 = a ^ 2 - c ^ 2)
    (hA : a ^ 2 = A) (hB : b ^ 2 = B) (h k f1 f2 d x y : ℝ) (h1 : f1 = h - c) (h2 : f2 = h + c)
    (hd : d = 2 * a) :
    IsEllipsePt (f1, k) (f2, k) d (x, y) ↔ (x - h) ^ 2 / A + (y - k) ^ 2 / B = 1 := by
  subst h1 h2 hd hA hB
  exact ellipse_horizontal_equation ha hc hca hb h k x y

private theorem eV {a b c A B : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a) (hb : b ^ 2 = a ^ 2 - c ^ 2)
    (hA : a ^ 2 = A) (hB : b ^ 2 = B) (h k f1 f2 d x y : ℝ) (h1 : f1 = k - c) (h2 : f2 = k + c)
    (hd : d = 2 * a) :
    IsEllipsePt (h, f1) (h, f2) d (x, y) ↔ (x - h) ^ 2 / B + (y - k) ^ 2 / A = 1 := by
  subst h1 h2 hd hA hB
  exact ellipse_vertical_equation ha hc hca hb h k x y

private theorem hV {a b c A B : ℝ} (hb : 0 < b) (hbc : b < c) (ha : a ^ 2 = c ^ 2 - b ^ 2)
    (hA : a ^ 2 = A) (hB : b ^ 2 = B) (h k f1 f2 d x y : ℝ) (h1 : f1 = k - c) (h2 : f2 = k + c)
    (hd : d = 2 * b) :
    IsHyperbolaPt (h, f1) (h, f2) d (x, y) ↔ (y - k) ^ 2 / B - (x - h) ^ 2 / A = 1 := by
  subst h1 h2 hd hA hB
  exact hyperbola_vertical_equation hb hbc ha h k x y

private theorem hH {a b c A B : ℝ} (ha : 0 < a) (hac : a < c) (hb : b ^ 2 = c ^ 2 - a ^ 2)
    (hA : a ^ 2 = A) (hB : b ^ 2 = B) (h k f1 f2 d x y : ℝ) (h1 : f1 = h - c) (h2 : f2 = h + c)
    (hd : d = 2 * a) :
    IsHyperbolaPt (f1, k) (f2, k) d (x, y) ↔ (x - h) ^ 2 / A - (y - k) ^ 2 / B = 1 := by
  subst h1 h2 hd hA hB
  exact hyperbola_horizontal_equation ha hac hb h k x y

private theorem pv (h k p f d x y : ℝ) (hf : f = k + p) (hd : d = k - p) :
    edist2 (x, y) (h, f) = distToLine 0 1 d (x, y) ↔ (x - h) ^ 2 = 4 * p * (y - k) := by
  subst hf hd; exact parabola_vertical_equation h k p x y

private theorem ph (h k p f d x y : ℝ) (hf : f = h + p) (hd : d = h - p) :
    edist2 (x, y) (f, k) = distToLine 1 0 d (x, y) ↔ (y - k) ^ 2 = 4 * p * (x - h) := by
  subst hf hd; exact parabola_horizontal_equation h k p x y

/-! ## 7.2 Circles -/

/-- Stitz-Zeager Exercise 7.2.3: the circle with center `(-3, 7/13)` and radius `1/2` has equation
`(x+3)² + (y-7/13)² = 1/4`. -/
@[kb "stitzzeager2013" "Exercise 7.2.3, p. 514"]
theorem exer_7_2_3 : ∀ x y : ℝ, edist2 (x, y) (-3, 7 / 13) = 1 / 2 ↔
    (x + 3) ^ 2 + (y - 7 / 13) ^ 2 = 1 / 4 := by
  intro x y
  rw [circle_mem_iff_equation (by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.2.5: the circle with center `(-e, √2)` and radius `π` has equation
`(x+e)² + (y-√2)² = π²`. -/
@[kb "stitzzeager2013" "Exercise 7.2.5, p. 514"]
theorem exer_7_2_5 : ∀ x y : ℝ, edist2 (x, y) (-Real.exp 1, √2) = Real.pi ↔
    (x + Real.exp 1) ^ 2 + (y - √2) ^ 2 = Real.pi ^ 2 := by
  intro x y
  rw [circle_mem_iff_equation Real.pi_pos]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.2.6: the circle with center `(π, e²)` and radius the cube root of `91` has
equation `(x-π)² + (y-e²)² = 91^(2/3)`. -/
@[kb "stitzzeager2013" "Exercise 7.2.6, p. 514"]
theorem exer_7_2_6 : ∀ x y : ℝ, edist2 (x, y) (Real.pi, Real.exp 1 ^ 2) = (91 : ℝ) ^ ((1 : ℝ) / 3) ↔
    (x - Real.pi) ^ 2 + (y - Real.exp 1 ^ 2) ^ 2 = (91 : ℝ) ^ ((2 : ℝ) / 3) := by
  intro x y
  have hr : (0 : ℝ) < (91 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have h2 : ((91 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (91 : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [circle_mem_iff_equation hr, h2]

/-- Stitz-Zeager Exercise 7.2.16: the circle with a diameter from `(1/2, 4)` to `(3/2, -1)` is
`(x-1)² + (y-3/2)² = 13/2`. -/
@[kb "stitzzeager2013" "Exercise 7.2.16, p. 514"]
theorem exer_7_2_16 : ∀ x y : ℝ,
    (x - 1 / 2) * (x - 3 / 2) + (y - 4) * (y + 1) = 0 ↔ (x - 1) ^ 2 + (y - 3 / 2) ^ 2 = 13 / 2 := by
  intro x y
  constructor <;> intro h <;> nlinarith

/-! ## 7.3 Parabolas -/

/-- Stitz-Zeager Exercise 7.3.2: `(x+7/3)² = 2(y+5/2)` is the parabola with vertex `(-7/3,-5/2)`, focus
`(-7/3,-2)` and directrix `y = -3`. -/
@[kb "stitzzeager2013" "Exercise 7.3.2, p. 524"]
theorem exer_7_3_2 : ∀ x y : ℝ,
    edist2 (x, y) (-7 / 3, -2) = distToLine 0 1 (-3) (x, y) ↔ (x + 7 / 3) ^ 2 = 2 * (y + 5 / 2) := by
  intro x y
  rw [pv (-7 / 3) (-5 / 2) (1 / 2) (-2) (-3) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.3.8: `(y+3/2)² = -7(x+9/2)` is the parabola with vertex `(-9/2,-3/2)`, focus
`(-25/4,-3/2)` and directrix `x = -11/4`. -/
@[kb "stitzzeager2013" "Exercise 7.3.8, p. 524"]
theorem exer_7_3_8 : ∀ x y : ℝ,
    edist2 (x, y) (-25 / 4, -3 / 2) = distToLine 1 0 (-11 / 4) (x, y) ↔
      (y + 3 / 2) ^ 2 = -7 * (x + 9 / 2) := by
  intro x y
  rw [ph (-9 / 2) (-3 / 2) (-7 / 4) (-25 / 4) (-11 / 4) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.3.14: `3y² - 27y + 4x + 211/4 = 0` is the parabola with vertex `(2, 9/2)`, focus
`(5/3, 9/2)` and directrix `x = 7/3`. -/
@[kb "stitzzeager2013" "Exercise 7.3.14, p. 524"]
theorem exer_7_3_14 : ∀ x y : ℝ,
    edist2 (x, y) (5 / 3, 9 / 2) = distToLine 1 0 (7 / 3) (x, y) ↔
      3 * y ^ 2 - 27 * y + 4 * x + 211 / 4 = 0 := by
  intro x y
  rw [ph 2 (9 / 2) (-1 / 3) (5 / 3) (7 / 3) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.3.18: a parabola with latus rectum endpoints `(-2,-7)`, `(4,-7)` is either
`(x-1)² = 6(y+17/2)` (focus `(1,-7)`, directrix `y = -10`) or `(x-1)² = -6(y+11/2)` (focus `(1,-7)`,
directrix `y = -4`); the endpoints lie on both. -/
@[kb "stitzzeager2013" "Exercise 7.3.18, p. 524"]
theorem exer_7_3_18 :
    (∀ x y : ℝ, edist2 (x, y) (1, -7) = distToLine 0 1 (-10) (x, y) ↔ (x - 1) ^ 2 = 6 * (y + 17 / 2)) ∧
    (∀ x y : ℝ, edist2 (x, y) (1, -7) = distToLine 0 1 (-4) (x, y) ↔ (x - 1) ^ 2 = -6 * (y + 11 / 2)) ∧
    (-2 - 1 : ℝ) ^ 2 = 6 * (-7 + 17 / 2) ∧ (4 - 1 : ℝ) ^ 2 = 6 * (-7 + 17 / 2) ∧
    (-2 - 1 : ℝ) ^ 2 = -6 * (-7 + 11 / 2) ∧ (4 - 1 : ℝ) ^ 2 = -6 * (-7 + 11 / 2) := by
  refine ⟨fun x y => ?_, fun x y => ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · rw [pv 1 (-17 / 2) (3 / 2) (-7) (-10) x y (by norm_num) (by norm_num)]
    constructor <;> intro h <;> nlinarith
  · rw [pv 1 (-11 / 2) (-3 / 2) (-7) (-4) x y (by norm_num) (by norm_num)]
    constructor <;> intro h <;> nlinarith

/-! ## 7.4 Ellipses -/

/-- Stitz-Zeager Exercise 7.4.5: `(x-1)²/10 + (y-3)²/11 = 1` is the ellipse with foci `(1,2)`, `(1,4)`
(distance sum `2√11`, vertices `(1, 3 ± √11)`). -/
@[kb "stitzzeager2013" "Exercise 7.4.5, p. 537"]
theorem exer_7_4_5 : ∀ x y : ℝ, IsEllipsePt (1, 2) (1, 4) (2 * √11) (x, y) ↔
    (x - 1) ^ 2 / 10 + (y - 3) ^ 2 / 11 = 1 := by
  intro x y
  refine (eV (a := √11) (b := √10) (c := 1) (A := 11) (B := 10) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 1 3 2 4 (2 * √11) x y (by norm_num) (by norm_num) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.7: `(x+2)²/16 + (y-5)²/20 = 1` is the ellipse with foci `(-2,3)`, `(-2,7)`
(distance sum `2√20`, vertices `(-2, 5 ± 2√5)`). -/
@[kb "stitzzeager2013" "Exercise 7.4.7, p. 537"]
theorem exer_7_4_7 : ∀ x y : ℝ, IsEllipsePt (-2, 3) (-2, 7) (2 * √20) (x, y) ↔
    (x + 2) ^ 2 / 16 + (y - 5) ^ 2 / 20 = 1 := by
  intro x y
  refine (eV (a := √20) (b := 4) (c := 2) (A := 20) (B := 16) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) (-2) 5 3 7 (2 * √20) x y (by norm_num) (by norm_num) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.8: `(x-4)²/8 + (y-2)²/18 = 1` is the ellipse with foci `(4, 2 ± √10)`
(distance sum `2√18`). -/
@[kb "stitzzeager2013" "Exercise 7.4.8, p. 537"]
theorem exer_7_4_8 : ∀ x y : ℝ, IsEllipsePt (4, 2 - √10) (4, 2 + √10) (2 * √18) (x, y) ↔
    (x - 4) ^ 2 / 8 + (y - 2) ^ 2 / 18 = 1 := by
  intro x y
  refine (eV (a := √18) (b := √8) (c := √10) (A := 18) (B := 8) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 4 2 _ _ (2 * √18) x y (by ring) (by ring) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.13: `9x² + 4y² - 4y - 8 = 0` is the ellipse `x² + (y-1/2)²/(9/4) = 1` with
foci `(0, (1 ± √5)/2)` and distance sum `3`. -/
@[kb "stitzzeager2013" "Exercise 7.4.13, p. 537"]
theorem exer_7_4_13 : ∀ x y : ℝ, IsEllipsePt (0, 1 / 2 - √5 / 2) (0, 1 / 2 + √5 / 2) 3 (x, y) ↔
    9 * x ^ 2 + 4 * y ^ 2 - 4 * y - 8 = 0 := by
  intro x y
  refine (eV (a := 3 / 2) (b := 1) (c := √5 / 2) (A := 9 / 4) (B := 1) (by kbs) (by kbs)
    (by have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num); have := Real.sqrt_nonneg 5; nlinarith)
    (by have := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num); nlinarith)
    (by kbs) (by kbs) 0 (1 / 2) _ _ 3 x y (by ring) (by ring) (by norm_num)).trans ?_
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 7.4.19: the ellipse with center `(5,2)`, vertex `(0,2)` and eccentricity `1/2` is
`(x-5)²/25 + 4(y-2)²/75 = 1` (foci `(5/2, 2)`, `(15/2, 2)`, distance sum `10`). -/
@[kb "stitzzeager2013" "Exercise 7.4.19, p. 537"]
theorem exer_7_4_19 : ∀ x y : ℝ, IsEllipsePt (5 / 2, 2) (15 / 2, 2) 10 (x, y) ↔
    (x - 5) ^ 2 / 25 + 4 * (y - 2) ^ 2 / 75 = 1 := by
  intro x y
  refine (eH (a := 5) (b := √(75 / 4)) (c := 5 / 2) (A := 25) (B := 75 / 4) (by kbs) (by kbs) (by kbs)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num) (by kbs) (by rw [Real.sq_sqrt (by norm_num)])
    5 2 _ _ 10 x y (by norm_num) (by norm_num) (by norm_num)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.21: in a whispering gallery 200 feet wide and 75 feet tall, the foci are
`c = 25√7` feet from the center, so the two people stand `100 - 25√7 ≈ 33.856` feet from the ends. -/
@[kb "stitzzeager2013" "Exercise 7.4.21, p. 537"]
theorem exer_7_4_21 : ∀ c : ℝ, 0 < c → c ^ 2 = 100 ^ 2 - 75 ^ 2 →
    c = 25 * √7 ∧ 33.85 < 100 - c ∧ 100 - c < 33.86 := by
  intro c hc h
  have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hc' : c = 25 * √7 := by
    have hs : 0 ≤ √7 := Real.sqrt_nonneg 7
    nlinarith [sq_nonneg (c - 25 * √7), sq_nonneg (c + 25 * √7)]
  refine ⟨hc', ?_, ?_⟩
  · rw [hc']; have : √7 < 2.646 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  · rw [hc']; have : 2.6456 < √7 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith

/-! ## 7.5 Hyperbolas -/

/-- Stitz-Zeager Exercise 7.5.4: `(y-3)²/11 - (x-1)²/10 = 1` is the hyperbola with foci `(1, 3 ± √21)`
(difference of distances `2√11`, vertices `(1, 3 ± √11)`). -/
@[kb "stitzzeager2013" "Exercise 7.5.4, p. 553"]
theorem exer_7_5_4 : ∀ x y : ℝ, IsHyperbolaPt (1, 3 - √21) (1, 3 + √21) (2 * √11) (x, y) ↔
    (y - 3) ^ 2 / 11 - (x - 1) ^ 2 / 10 = 1 := by
  intro x y
  refine (hV (a := √10) (b := √11) (c := √21) (A := 10) (B := 11) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    1 3 _ _ _ x y (by ring) (by ring) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.30: with Stations A `(0,-50)`, B `(0,50)` (time difference 2 s at 6 km/s, so
distance difference `12`) the epicenter lies on `y²/36 - x²/2464 = 1`; with Stations A and C `(-150,-50)`
(difference `30`) it lies on `(x+75)²/225 - (y+50)²/5400 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.30, p. 554"]
theorem exer_7_5_30 :
    (∀ x y : ℝ, IsHyperbolaPt (0, -50) (0, 50) 12 (x, y) ↔ y ^ 2 / 36 - x ^ 2 / 2464 = 1) ∧
    (∀ x y : ℝ, IsHyperbolaPt (-150, -50) (0, -50) 30 (x, y) ↔
      (x + 75) ^ 2 / 225 - (y + 50) ^ 2 / 5400 = 1) := by
  refine ⟨fun x y => ?_, fun x y => ?_⟩
  · refine (hV (a := √2464) (b := 6) (c := 50) (A := 2464) (B := 36) (by kbs) (by kbs) (by kbs) (by kbs)
      (by kbs) 0 0 (-50) 50 12 x y (by norm_num) (by norm_num) (by norm_num)).trans ?_
    constructor <;> intro h <;> linarith
  · refine (hH (a := 15) (b := √5400) (c := 75) (A := 225) (B := 5400) (by kbs) (by kbs) (by kbs) (by kbs)
      (by kbs) (-75) (-50) (-150) 0 30 x y (by norm_num) (by norm_num) (by norm_num)).trans ?_
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.32: for the cooling tower modeled by `x²/12100 - (y-330)²/B = 1` with
`B = 52707600/1541`, the half-width `137.5` occurs at `y = 330 ± (3/4)√B`, and the upper value
(the tower's top) is about `469` feet (between `468.5` and `469`). -/
@[kb "stitzzeager2013" "Exercise 7.5.32, p. 554"]
theorem exer_7_5_32 : ∀ y : ℝ, (137.5 : ℝ) ^ 2 / 12100 - (y - 330) ^ 2 / (52707600 / 1541) = 1 ↔
    y = 330 + 3 / 4 * √(52707600 / 1541) ∨ y = 330 - 3 / 4 * √(52707600 / 1541) := by
  intro y
  have hs : √(52707600 / 1541) ^ 2 = 52707600 / 1541 := Real.sq_sqrt (by norm_num)
  have hy : (137.5 : ℝ) ^ 2 / 12100 - (y - 330) ^ 2 / (52707600 / 1541) = 1 ↔
      (y - 330) ^ 2 = (3 / 4 * √(52707600 / 1541)) ^ 2 := by
    rw [mul_pow, hs]
    constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith
  rw [hy, sq_eq_sq_iff_eq_or_eq_neg]
  constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith

/-- Stitz-Zeager Exercise 7.5.32 (numeric value): the top of the tower, `330 + (3/4)√B`, is between
`468.5` and `469` feet. -/
@[kb "stitzzeager2013" "Exercise 7.5.32, numeric, p. 554"]
theorem exer_7_5_32_height : 468.5 < 330 + 3 / 4 * √(52707600 / 1541) ∧
    330 + 3 / 4 * √(52707600 / 1541) < 469 := by
  have h1 : (184.9 : ℝ) < √(52707600 / 1541) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √(52707600 / 1541) < (185 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

end UndergradKB.Precalculus.Course
