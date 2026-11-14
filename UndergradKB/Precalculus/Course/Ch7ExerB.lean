import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Precalculus.Conics
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 7 (Stitz-Zeager): exercises with the book's answers, Sections 7.4 and 7.5 -/

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

private theorem hH {a b c A B : ℝ} (ha : 0 < a) (hac : a < c) (hb : b ^ 2 = c ^ 2 - a ^ 2)
    (hA : a ^ 2 = A) (hB : b ^ 2 = B) (h k f1 f2 d x y : ℝ) (h1 : f1 = h - c) (h2 : f2 = h + c)
    (hd : d = 2 * a) :
    IsHyperbolaPt (f1, k) (f2, k) d (x, y) ↔ (x - h) ^ 2 / A - (y - k) ^ 2 / B = 1 := by
  subst h1 h2 hd hA hB
  exact hyperbola_horizontal_equation ha hac hb h k x y

private theorem hV {a b c A B : ℝ} (hb : 0 < b) (hbc : b < c) (ha : a ^ 2 = c ^ 2 - b ^ 2)
    (hA : a ^ 2 = A) (hB : b ^ 2 = B) (h k f1 f2 d x y : ℝ) (h1 : f1 = k - c) (h2 : f2 = k + c)
    (hd : d = 2 * b) :
    IsHyperbolaPt (h, f1) (h, f2) d (x, y) ↔ (y - k) ^ 2 / B - (x - h) ^ 2 / A = 1 := by
  subst h1 h2 hd hA hB
  exact hyperbola_vertical_equation hb hbc ha h k x y

private theorem pv (h k p f d x y : ℝ) (hf : f = k + p) (hd : d = k - p) :
    edist2 (x, y) (h, f) = distToLine 0 1 d (x, y) ↔ (x - h) ^ 2 = 4 * p * (y - k) := by
  subst hf hd; exact parabola_vertical_equation h k p x y

private theorem ph (h k p f d x y : ℝ) (hf : f = h + p) (hd : d = h - p) :
    edist2 (x, y) (f, k) = distToLine 1 0 d (x, y) ↔ (y - k) ^ 2 = 4 * p * (x - h) := by
  subst hf hd; exact parabola_horizontal_equation h k p x y

/-! ## 7.4 Ellipses -/

/-- Stitz-Zeager Exercise 7.4.1: `x²/169 + y²/25 = 1` is the ellipse with foci `(±12,0)` (distance sum `26`,
vertices `(±13,0)`, minor-axis endpoints `(0,±5)`). -/
@[kb "stitzzeager2013" "Exercise 7.4.1, p. 537"]
theorem exer_7_4_1 : ∀ x y : ℝ, IsEllipsePt (-12, 0) (12, 0) 26 (x, y) ↔ x ^ 2 / 169 + y ^ 2 / 25 = 1 := by
  intro x y
  refine (eH (a := 13) (b := 5) (c := 12) (A := 169) (B := 25) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 0 0 (-12) 12 26 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.2: `x²/9 + y²/25 = 1` is the ellipse with foci `(0,±4)` (distance sum `10`,
vertices `(0,±5)`, minor-axis endpoints `(±3,0)`). -/
@[kb "stitzzeager2013" "Exercise 7.4.2, p. 537"]
theorem exer_7_4_2 : ∀ x y : ℝ, IsEllipsePt (0, -4) (0, 4) 10 (x, y) ↔ x ^ 2 / 9 + y ^ 2 / 25 = 1 := by
  intro x y
  refine (eV (a := 5) (b := 3) (c := 4) (A := 25) (B := 9) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 0 0 (-4) 4 10 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.3: `(x-2)²/4 + (y+3)²/9 = 1` is the ellipse with center `(2,-3)`, vertices
`(2,0)`, `(2,-6)` and foci `(2, -3 ± √5)`. -/
@[kb "stitzzeager2013" "Exercise 7.4.3, p. 537"]
theorem exer_7_4_3 : ∀ x y : ℝ, IsEllipsePt (2, -3 - √5) (2, -3 + √5) 6 (x, y) ↔
    (x - 2) ^ 2 / 4 + (y + 3) ^ 2 / 9 = 1 := by
  intro x y
  refine (eV (a := 3) (b := 2) (c := √5) (A := 9) (B := 4) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 2 (-3) (-3 - √5) (-3 + √5) 6 x y (by ring) (by ring) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.4: `(x+5)²/16 + (y-4)² = 1` is the ellipse with center `(-5,4)`, vertices
`(-9,4)`, `(-1,4)` and foci `(-5 ± √15, 4)`. -/
@[kb "stitzzeager2013" "Exercise 7.4.4, p. 537"]
theorem exer_7_4_4 : ∀ x y : ℝ, IsEllipsePt (-5 - √15, 4) (-5 + √15, 4) 8 (x, y) ↔
    (x + 5) ^ 2 / 16 + (y - 4) ^ 2 / 1 = 1 := by
  intro x y
  refine (eH (a := 4) (b := 1) (c := √15) (A := 16) (B := 1) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) (-5) 4 (-5 - √15) (-5 + √15) 8 x y (by ring) (by ring) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.6: `(x-1)²/9 + (y+3)²/4 = 1` is the ellipse with center `(1,-3)`, vertices
`(4,-3)`, `(-2,-3)` and foci `(1 ± √5, -3)`. -/
@[kb "stitzzeager2013" "Exercise 7.4.6, p. 537"]
theorem exer_7_4_6 : ∀ x y : ℝ, IsEllipsePt (1 - √5, -3) (1 + √5, -3) 6 (x, y) ↔
    (x - 1) ^ 2 / 9 + (y + 3) ^ 2 / 4 = 1 := by
  intro x y
  refine (eH (a := 3) (b := 2) (c := √5) (A := 9) (B := 4) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 1 (-3) (1 - √5) (1 + √5) 6 x y (by ring) (by ring) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.9: `9x² + 25y² - 54x - 50y - 119 = 0` is the ellipse `(x-3)²/25 + (y-1)²/9 = 1`
with center `(3,1)`, foci `(-1,1)` and `(7,1)` and distance sum `10`. -/
@[kb "stitzzeager2013" "Exercise 7.4.9, p. 537"]
theorem exer_7_4_9 : ∀ x y : ℝ, IsEllipsePt (-1, 1) (7, 1) 10 (x, y) ↔
    9 * x ^ 2 + 25 * y ^ 2 - 54 * x - 50 * y - 119 = 0 := by
  intro x y
  refine (eH (a := 5) (b := 3) (c := 4) (A := 25) (B := 9) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 3 1 (-1) 7 10 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.10: `12x² + 3y² - 30y + 39 = 0` is the ellipse `x²/3 + (y-5)²/12 = 1` with center
`(0,5)`, foci `(0,2)` and `(0,8)` and distance sum `2√12`. -/
@[kb "stitzzeager2013" "Exercise 7.4.10, p. 537"]
theorem exer_7_4_10 : ∀ x y : ℝ, IsEllipsePt (0, 2) (0, 8) (2 * √12) (x, y) ↔
    12 * x ^ 2 + 3 * y ^ 2 - 30 * y + 39 = 0 := by
  intro x y
  refine (eV (a := √12) (b := √3) (c := 3) (A := 12) (B := 3) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 0 5 2 8 _ x y (by kbs) (by kbs) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.11: `5x² + 18y² - 30x + 72y + 27 = 0` is the ellipse `(x-3)²/18 + (y+2)²/5 = 1`
with center `(3,-2)` and foci `(3 ± √13, -2)` (distance sum `2√18`). -/
@[kb "stitzzeager2013" "Exercise 7.4.11, p. 537"]
theorem exer_7_4_11 : ∀ x y : ℝ, IsEllipsePt (3 - √13, -2) (3 + √13, -2) (2 * √18) (x, y) ↔
    5 * x ^ 2 + 18 * y ^ 2 - 30 * x + 72 * y + 27 = 0 := by
  intro x y
  refine (eH (a := √18) (b := √5) (c := √13) (A := 18) (B := 5) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 3 (-2) _ _ _ x y rfl rfl rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.12: `x² - 2x + 2y² - 12y + 3 = 0` is the ellipse `(x-1)²/16 + (y-3)²/8 = 1`
with center `(1,3)`, vertices `(5,3)`, `(-3,3)` and foci `(1 ± 2√2, 3)`. -/
@[kb "stitzzeager2013" "Exercise 7.4.12, p. 537"]
theorem exer_7_4_12 : ∀ x y : ℝ, IsEllipsePt (1 - 2 * √2, 3) (1 + 2 * √2, 3) 8 (x, y) ↔
    x ^ 2 - 2 * x + 2 * y ^ 2 - 12 * y + 3 = 0 := by
  intro x y
  refine (eH (a := 4) (b := 2 * √2) (c := 2 * √2) (A := 16) (B := 8) (by kbs) (by kbs)
    (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]) (by kbs)
    (by kbs) (by kbs) 1 3 _ _ 8 x y rfl rfl (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.14: `6x² + 5y² - 24x + 20y + 14 = 0` is the ellipse `(x-2)²/5 + (y+2)²/6 = 1`
with center `(2,-2)` and foci `(2,-3)`, `(2,-1)` (distance sum `2√6`). -/
@[kb "stitzzeager2013" "Exercise 7.4.14, p. 537"]
theorem exer_7_4_14 : ∀ x y : ℝ, IsEllipsePt (2, -3) (2, -1) (2 * √6) (x, y) ↔
    6 * x ^ 2 + 5 * y ^ 2 - 24 * x + 20 * y + 14 = 0 := by
  intro x y
  refine (eV (a := √6) (b := √5) (c := 1) (A := 6) (B := 5) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 2 (-2) (-3) (-1) _ x y (by kbs) (by kbs) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.15: the ellipse with center `(3,7)`, vertex `(3,2)` and focus `(3,3)` (so
`a = 5`, `c = 4`, other focus `(3,11)`) is `(x-3)²/9 + (y-7)²/25 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.4.15, p. 537"]
theorem exer_7_4_15 : ∀ x y : ℝ, IsEllipsePt (3, 3) (3, 11) 10 (x, y) ↔
    (x - 3) ^ 2 / 9 + (y - 7) ^ 2 / 25 = 1 := by
  intro x y
  refine (eV (a := 5) (b := 3) (c := 4) (A := 25) (B := 9) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 3 7 3 11 10 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.16: the ellipse with foci `(0,±5)` and vertices `(0,±8)` is `x²/39 + y²/64 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.4.16, p. 537"]
theorem exer_7_4_16 : ∀ x y : ℝ, IsEllipsePt (0, -5) (0, 5) 16 (x, y) ↔ x ^ 2 / 39 + y ^ 2 / 64 = 1 := by
  intro x y
  refine (eV (a := 8) (b := √39) (c := 5) (A := 64) (B := 39) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 0 0 (-5) 5 16 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.17: the ellipse with foci `(±3,0)` and minor axis of length `10` is
`x²/34 + y²/25 = 1` (distance sum `2√34`). -/
@[kb "stitzzeager2013" "Exercise 7.4.17, p. 537"]
theorem exer_7_4_17 : ∀ x y : ℝ, IsEllipsePt (-3, 0) (3, 0) (2 * √34) (x, y) ↔ x ^ 2 / 34 + y ^ 2 / 25 = 1 := by
  intro x y
  refine (eH (a := √34) (b := 5) (c := 3) (A := 34) (B := 25) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 0 0 (-3) 3 _ x y (by kbs) (by kbs) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.18: the ellipse with vertices `(3,2)`, `(13,2)` and minor-axis endpoints `(8,4)`,
`(8,0)` has center `(8,2)`, foci `(8 ± √21, 2)` and equation `(x-8)²/25 + (y-2)²/4 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.4.18, p. 537"]
theorem exer_7_4_18 : ∀ x y : ℝ, IsEllipsePt (8 - √21, 2) (8 + √21, 2) 10 (x, y) ↔
    (x - 8) ^ 2 / 25 + (y - 2) ^ 2 / 4 = 1 := by
  intro x y
  refine (eH (a := 5) (b := 2) (c := √21) (A := 25) (B := 4) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 8 2 _ _ 10 x y rfl rfl (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.20: the ellipse lying in Quadrant IV, tangent to the axes at `(0,-9)` and `(8,0)`,
has center `(8,-9)`, foci `(8, -9 ± √17)` and equation `(x-8)²/64 + (y+9)²/81 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.4.20, p. 537"]
theorem exer_7_4_20 : ∀ x y : ℝ, IsEllipsePt (8, -9 - √17) (8, -9 + √17) 18 (x, y) ↔
    (x - 8) ^ 2 / 64 + (y + 9) ^ 2 / 81 = 1 := by
  intro x y
  refine (eV (a := 9) (b := 8) (c := √17) (A := 81) (B := 64) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (by kbs) 8 (-9) _ _ 18 x y (by ring) (by ring) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.4.22: the elliptical arch `x²/9 + y²/81 = 1` (6 feet wide, 9 feet tall): the height
(`y > 0`) one foot in from the base (`x = 2`) is `3√5`. -/
@[kb "stitzzeager2013" "Exercise 7.4.22, p. 538"]
theorem exer_7_4_22 : ∀ y : ℝ, 0 < y → ((2 : ℝ) ^ 2 / 9 + y ^ 2 / 81 = 1 ↔ y = 3 * √5) := by
  intro y hy
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 0 ≤ √5 := Real.sqrt_nonneg 5
  constructor
  · intro h
    have : (y - 3 * √5) * (y + 3 * √5) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · nlinarith
  · rintro rfl; nlinarith

/-- Stitz-Zeager Exercise 7.4.23: Earth's orbit has semimajor axis `a = 1` AU and eccentricity `e = 0.0167`, so
the focal distance is `c = a e`; the aphelion distance is `a + c = 1.0167` AU and the perihelion distance is
`a - c = 0.9833` AU. -/
@[kb "stitzzeager2013" "Exercise 7.4.23, p. 538"]
theorem exer_7_4_23 : ∀ a e c : ℝ, a = 1 → e = 167 / 10000 → c = a * e →
    a + c = 10167 / 10000 ∧ a - c = 9833 / 10000 := by
  intro a e c ha he hc
  subst ha he hc
  norm_num

/-! ## 7.5 Hyperbolas -/

/-- Stitz-Zeager Exercise 7.5.1: `x²/16 - y²/9 = 1` is the hyperbola with foci `(±5,0)` and vertices `(±4,0)`
(difference of focal distances `8`). -/
@[kb "stitzzeager2013" "Exercise 7.5.1, p. 553"]
theorem exer_7_5_1 : ∀ x y : ℝ, IsHyperbolaPt (-5, 0) (5, 0) 8 (x, y) ↔ x ^ 2 / 16 - y ^ 2 / 9 = 1 := by
  intro x y
  refine (hH (a := 4) (b := 3) (c := 5) (A := 16) (B := 9) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    0 0 (-5) 5 8 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.2: `y²/9 - x²/16 = 1` is the hyperbola with foci `(0,±5)` and vertices `(0,±3)`
(difference of focal distances `6`). -/
@[kb "stitzzeager2013" "Exercise 7.5.2, p. 553"]
theorem exer_7_5_2 : ∀ x y : ℝ, IsHyperbolaPt (0, -5) (0, 5) 6 (x, y) ↔ y ^ 2 / 9 - x ^ 2 / 16 = 1 := by
  intro x y
  refine (hV (a := 4) (b := 3) (c := 5) (A := 16) (B := 9) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    0 0 (-5) 5 6 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.3: `(x-2)²/4 - (y+3)²/9 = 1` is the hyperbola with center `(2,-3)`, vertices
`(0,-3)`, `(4,-3)` and foci `(2 ± √13, -3)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.3, p. 553"]
theorem exer_7_5_3 : ∀ x y : ℝ, IsHyperbolaPt (2 - √13, -3) (2 + √13, -3) 4 (x, y) ↔
    (x - 2) ^ 2 / 4 - (y + 3) ^ 2 / 9 = 1 := by
  intro x y
  refine (hH (a := 2) (b := 3) (c := √13) (A := 4) (B := 9) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    2 (-3) _ _ 4 x y rfl rfl (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.5: `(x+4)²/16 - (y-4)² = 1` is the hyperbola with center `(-4,4)`, vertices
`(-8,4)`, `(0,4)` and foci `(-4 ± √17, 4)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.5, p. 553"]
theorem exer_7_5_5 : ∀ x y : ℝ, IsHyperbolaPt (-4 - √17, 4) (-4 + √17, 4) 8 (x, y) ↔
    (x + 4) ^ 2 / 16 - (y - 4) ^ 2 / 1 = 1 := by
  intro x y
  refine (hH (a := 4) (b := 1) (c := √17) (A := 16) (B := 1) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (-4) 4 _ _ 8 x y (by ring) (by ring) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.6: `(x+1)²/9 - (y-3)²/4 = 1` is the hyperbola with center `(-1,3)`, vertices
`(2,3)`, `(-4,3)` and foci `(-1 ± √13, 3)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.6, p. 553"]
theorem exer_7_5_6 : ∀ x y : ℝ, IsHyperbolaPt (-1 - √13, 3) (-1 + √13, 3) 6 (x, y) ↔
    (x + 1) ^ 2 / 9 - (y - 3) ^ 2 / 4 = 1 := by
  intro x y
  refine (hH (a := 3) (b := 2) (c := √13) (A := 9) (B := 4) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (-1) 3 _ _ 6 x y (by ring) (by ring) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.7: `(y+2)²/16 - (x-5)²/20 = 1` is the hyperbola with center `(5,-2)`, vertices
`(5,2)`, `(5,-6)` and foci `(5,4)`, `(5,-8)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.7, p. 553"]
theorem exer_7_5_7 : ∀ x y : ℝ, IsHyperbolaPt (5, -8) (5, 4) 8 (x, y) ↔
    (y + 2) ^ 2 / 16 - (x - 5) ^ 2 / 20 = 1 := by
  intro x y
  refine (hV (a := √20) (b := 4) (c := 6) (A := 20) (B := 16) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    5 (-2) (-8) 4 8 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.8: `(x-4)²/8 - (y-2)²/18 = 1` is the hyperbola with center `(4,2)`, vertices
`(4 ± 2√2, 2)` and foci `(4 ± √26, 2)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.8, p. 553"]
theorem exer_7_5_8 : ∀ x y : ℝ, IsHyperbolaPt (4 - √26, 2) (4 + √26, 2) (2 * √8) (x, y) ↔
    (x - 4) ^ 2 / 8 - (y - 2) ^ 2 / 18 = 1 := by
  intro x y
  refine (hH (a := √8) (b := √18) (c := √26) (A := 8) (B := 18) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    4 2 _ _ _ x y rfl rfl rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.9: `12x² - 3y² + 30y - 111 = 0` is the hyperbola `x²/3 - (y-5)²/12 = 1` with
center `(0,5)` and foci `(±√15, 5)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.9, p. 553"]
theorem exer_7_5_9 : ∀ x y : ℝ, IsHyperbolaPt (-√15, 5) (√15, 5) (2 * √3) (x, y) ↔
    12 * x ^ 2 - 3 * y ^ 2 + 30 * y - 111 = 0 := by
  intro x y
  refine (hH (a := √3) (b := √12) (c := √15) (A := 3) (B := 12) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    0 5 _ _ _ x y (by ring) (by ring) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.10: `18y² - 5x² + 72y + 30x - 63 = 0` is the hyperbola
`(y+2)²/5 - (x-3)²/18 = 1` with center `(3,-2)` and foci `(3, -2 ± √23)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.10, p. 553"]
theorem exer_7_5_10 : ∀ x y : ℝ, IsHyperbolaPt (3, -2 - √23) (3, -2 + √23) (2 * √5) (x, y) ↔
    18 * y ^ 2 - 5 * x ^ 2 + 72 * y + 30 * x - 63 = 0 := by
  intro x y
  refine (hV (a := √18) (b := √5) (c := √23) (A := 18) (B := 5) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    3 (-2) _ _ _ x y (by ring) (by ring) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.11: `9x² - 25y² - 54x - 50y - 169 = 0` is the hyperbola
`(x-3)²/25 - (y+1)²/9 = 1` with center `(3,-1)`, vertices `(8,-1)`, `(-2,-1)` and foci `(3 ± √34, -1)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.11, p. 553"]
theorem exer_7_5_11 : ∀ x y : ℝ, IsHyperbolaPt (3 - √34, -1) (3 + √34, -1) 10 (x, y) ↔
    9 * x ^ 2 - 25 * y ^ 2 - 54 * x - 50 * y - 169 = 0 := by
  intro x y
  refine (hH (a := 5) (b := 3) (c := √34) (A := 25) (B := 9) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    3 (-1) _ _ 10 x y rfl rfl (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.12: `-6x² + 5y² - 24x + 40y + 26 = 0` is the hyperbola
`(y+4)²/6 - (x+2)²/5 = 1` with center `(-2,-4)` and foci `(-2, -4 ± √11)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.12, p. 553"]
theorem exer_7_5_12 : ∀ x y : ℝ, IsHyperbolaPt (-2, -4 - √11) (-2, -4 + √11) (2 * √6) (x, y) ↔
    -6 * x ^ 2 + 5 * y ^ 2 - 24 * x + 40 * y + 26 = 0 := by
  intro x y
  refine (hV (a := √5) (b := √6) (c := √11) (A := 5) (B := 6) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    (-2) (-4) _ _ _ x y (by ring) (by ring) rfl).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.13: the hyperbola with center `(3,7)`, vertex `(3,3)` and focus `(3,2)` (so
`b = 4`, `c = 5`, other focus `(3,12)`) is `(y-7)²/16 - (x-3)²/9 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.13, p. 553"]
theorem exer_7_5_13 : ∀ x y : ℝ, IsHyperbolaPt (3, 2) (3, 12) 8 (x, y) ↔
    (y - 7) ^ 2 / 16 - (x - 3) ^ 2 / 9 = 1 := by
  intro x y
  refine (hV (a := 3) (b := 4) (c := 5) (A := 9) (B := 16) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    3 7 2 12 8 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.14: the hyperbola with vertices `(0,1)`, `(8,1)` and focus `(-3,1)` (center `(4,1)`,
other focus `(11,1)`) is `(x-4)²/16 - (y-1)²/33 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.14, p. 553"]
theorem exer_7_5_14 : ∀ x y : ℝ, IsHyperbolaPt (-3, 1) (11, 1) 8 (x, y) ↔
    (x - 4) ^ 2 / 16 - (y - 1) ^ 2 / 33 = 1 := by
  intro x y
  refine (hH (a := 4) (b := √33) (c := 7) (A := 16) (B := 33) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    4 1 (-3) 11 8 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.15: the hyperbola with foci `(0,±8)` and vertices `(0,±5)` is
`y²/25 - x²/39 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.15, p. 553"]
theorem exer_7_5_15 : ∀ x y : ℝ, IsHyperbolaPt (0, -8) (0, 8) 10 (x, y) ↔ y ^ 2 / 25 - x ^ 2 / 39 = 1 := by
  intro x y
  refine (hV (a := √39) (b := 5) (c := 8) (A := 39) (B := 25) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    0 0 (-8) 8 10 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.16: the hyperbola with foci `(±5,0)` and conjugate axis of length `6` is
`x²/16 - y²/9 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.16, p. 553"]
theorem exer_7_5_16 : ∀ x y : ℝ, IsHyperbolaPt (-5, 0) (5, 0) 8 (x, y) ↔ x ^ 2 / 16 - y ^ 2 / 9 = 1 :=
  exer_7_5_1

/-- Stitz-Zeager Exercise 7.5.17: the hyperbola with vertices `(3,2)`, `(13,2)` and conjugate-axis endpoints
`(8,4)`, `(8,0)` (center `(8,2)`) is `(x-8)²/25 - (y-2)²/4 = 1`, with foci `(8 ± √29, 2)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.17, p. 553"]
theorem exer_7_5_17 : ∀ x y : ℝ, IsHyperbolaPt (8 - √29, 2) (8 + √29, 2) 10 (x, y) ↔
    (x - 8) ^ 2 / 25 - (y - 2) ^ 2 / 4 = 1 := by
  intro x y
  refine (hH (a := 5) (b := 2) (c := √29) (A := 25) (B := 4) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    8 2 _ _ 10 x y rfl rfl (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.18: the hyperbola with vertex `(-10,5)` and asymptotes `y = ±(1/2)(x-6) + 5`
(center `(6,5)`, `a = 16`, `b = 8`) is `(x-6)²/256 - (y-5)²/64 = 1`, with foci `(6 ± 8√5, 5)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.18, p. 553"]
theorem exer_7_5_18 : ∀ x y : ℝ, IsHyperbolaPt (6 - 8 * √5, 5) (6 + 8 * √5, 5) 32 (x, y) ↔
    (x - 6) ^ 2 / 256 - (y - 5) ^ 2 / 64 = 1 := by
  intro x y
  refine (hH (a := 16) (b := 8) (c := 8 * √5) (A := 256) (B := 64) (by kbs)
    (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]) (by kbs) (by kbs) (by kbs)
    6 5 _ _ 32 x y rfl rfl (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.19: `x² - 2x - 4y - 11 = 0` is the parabola `(x-1)² = 4(y+3)` with vertex `(1,-3)`,
focus `(1,-2)` and directrix `y = -4`. -/
@[kb "stitzzeager2013" "Exercise 7.5.19, p. 553"]
theorem exer_7_5_19 : ∀ x y : ℝ, x ^ 2 - 2 * x - 4 * y - 11 = 0 ↔
    edist2 (x, y) (1, -2) = distToLine 0 1 (-4) (x, y) := by
  intro x y
  rw [pv 1 (-3) 1 (-2) (-4) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.20: `x² + y² - 8x + 4y + 11 = 0` is the circle with center `(4,-2)` and radius `3`. -/
@[kb "stitzzeager2013" "Exercise 7.5.20, p. 553"]
theorem exer_7_5_20 : ∀ x y : ℝ, x ^ 2 + y ^ 2 - 8 * x + 4 * y + 11 = 0 ↔ edist2 (x, y) (4, -2) = 3 := by
  intro x y
  rw [circle_mem_iff_equation (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.21: `9x² + 4y² - 36x + 24y + 36 = 0` is the ellipse `(x-2)²/4 + (y+3)²/9 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.21, p. 553"]
theorem exer_7_5_21 : ∀ x y : ℝ, 9 * x ^ 2 + 4 * y ^ 2 - 36 * x + 24 * y + 36 = 0 ↔
    (x - 2) ^ 2 / 4 + (y + 3) ^ 2 / 9 = 1 := by
  intro x y
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.22: `9x² - 4y² - 36x - 24y - 36 = 0` is the hyperbola
`(x-2)²/4 - (y+3)²/9 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.22, p. 553"]
theorem exer_7_5_22 : ∀ x y : ℝ, 9 * x ^ 2 - 4 * y ^ 2 - 36 * x - 24 * y - 36 = 0 ↔
    (x - 2) ^ 2 / 4 - (y + 3) ^ 2 / 9 = 1 := by
  intro x y
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.23: `y² + 8y - 4x + 16 = 0` is the parabola `(y+4)² = 4x` (vertex `(0,-4)`,
focus `(1,-4)`, directrix `x = -1`). -/
@[kb "stitzzeager2013" "Exercise 7.5.23, p. 554"]
theorem exer_7_5_23 : ∀ x y : ℝ, y ^ 2 + 8 * y - 4 * x + 16 = 0 ↔
    edist2 (x, y) (1, -4) = distToLine 1 0 (-1) (x, y) := by
  intro x y
  rw [ph 0 (-4) 1 1 (-1) x y (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.24: `4x² + y² - 8x + 4 = 0` degenerates: `(x-1)² + y²/4 = 0`, whose graph is the
single point `(1,0)`. -/
@[kb "stitzzeager2013" "Exercise 7.5.24, p. 554"]
theorem exer_7_5_24 : ∀ x y : ℝ, 4 * x ^ 2 + y ^ 2 - 8 * x + 4 = 0 ↔ x = 1 ∧ y = 0 := by
  intro x y
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg y]
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 7.5.25: `4x² + 9y² - 8x + 54y + 49 = 0` is the ellipse `(x-1)²/9 + (y+3)²/4 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.25, p. 554"]
theorem exer_7_5_25 : ∀ x y : ℝ, 4 * x ^ 2 + 9 * y ^ 2 - 8 * x + 54 * y + 49 = 0 ↔
    (x - 1) ^ 2 / 9 + (y + 3) ^ 2 / 4 = 1 := by
  intro x y
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.26: `x² + y² - 6x + 4y + 14 = 0` has no graph. -/
@[kb "stitzzeager2013" "Exercise 7.5.26, p. 554"]
theorem exer_7_5_26 : ∀ x y : ℝ, x ^ 2 + y ^ 2 - 6 * x + 4 * y + 14 ≠ 0 := by
  intro x y h
  nlinarith [sq_nonneg (x - 3), sq_nonneg (y + 2)]

/-- Stitz-Zeager Exercise 7.5.27: `2x² + 4y² + 12x - 8y + 25 = 0` has no graph. -/
@[kb "stitzzeager2013" "Exercise 7.5.27, p. 554"]
theorem exer_7_5_27 : ∀ x y : ℝ, 2 * x ^ 2 + 4 * y ^ 2 + 12 * x - 8 * y + 25 ≠ 0 := by
  intro x y h
  nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 1)]

/-- Stitz-Zeager Exercise 7.5.28: `4x² - 5y² - 40x - 20y + 160 = 0` is the hyperbola
`(y+2)²/16 - (x-5)²/20 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.28, p. 554"]
theorem exer_7_5_28 : ∀ x y : ℝ, 4 * x ^ 2 - 5 * y ^ 2 - 40 * x - 20 * y + 160 = 0 ↔
    (y + 2) ^ 2 / 16 - (x - 5) ^ 2 / 20 = 1 := by
  intro x y
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 7.5.31(b): the hyperbola with vertices `(±3,0)` and eccentricity `2` (so `c = 6`) is
`x²/9 - y²/27 = 1`. -/
@[kb "stitzzeager2013" "Exercise 7.5.31(b), p. 554"]
theorem exer_7_5_31_b : ∀ x y : ℝ, IsHyperbolaPt (-6, 0) (6, 0) 6 (x, y) ↔ x ^ 2 / 9 - y ^ 2 / 27 = 1 := by
  intro x y
  refine (hH (a := 3) (b := √27) (c := 6) (A := 9) (B := 27) (by kbs) (by kbs) (by kbs) (by kbs) (by kbs)
    0 0 (-6) 6 6 x y (by kbs) (by kbs) (by kbs)).trans ?_
  constructor <;> intro h <;> linarith

end UndergradKB.Precalculus.Course
