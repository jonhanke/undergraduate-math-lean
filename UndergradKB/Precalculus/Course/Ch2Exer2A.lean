import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 2.1 -/

namespace UndergradKB.Precalculus.Course

/-! ## Section 2.1 -/

/-- Stitz-Zeager Exercise 2.1.2: the line of slope `-2` through `(-5,8)` is `y = -2x - 2`. -/
@[kb "stitzzeager2013" "Exercise 2.1.2, p. 175"]
theorem exer_2_1_2 (x y : ℝ) : (y - 8 = -2 * (x + 5) ↔ y = -2 * x - 2) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.3: the line of slope `-1` through `(-7,-1)` is `y = -x - 8`. -/
@[kb "stitzzeager2013" "Exercise 2.1.3, p. 175"]
theorem exer_2_1_3 (x y : ℝ) : (y + 1 = -(x + 7) ↔ y = -x - 8) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.4: the line of slope `2/3` through `(-2,1)` is `y = (2/3)x + 7/3`. -/
@[kb "stitzzeager2013" "Exercise 2.1.4, p. 175"]
theorem exer_2_1_4 (x y : ℝ) : (y - 1 = 2 / 3 * (x + 2) ↔ y = 2 / 3 * x + 7 / 3) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.6: the line of slope `1/7` through `(-1,4)` is `y = x/7 + 29/7`. -/
@[kb "stitzzeager2013" "Exercise 2.1.6, p. 175"]
theorem exer_2_1_6 (x y : ℝ) : (y - 4 = 1 / 7 * (x + 1) ↔ y = 1 / 7 * x + 29 / 7) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.7: the horizontal line through `(3,117)` is `y = 117`. -/
@[kb "stitzzeager2013" "Exercise 2.1.7, p. 175"]
theorem exer_2_1_7 (x y : ℝ) : (y - 117 = 0 * (x - 3) ↔ y = 117) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.8: the line of slope `-√2` through `(0,-3)` is `y = -√2 x - 3`. -/
@[kb "stitzzeager2013" "Exercise 2.1.8, p. 175"]
theorem exer_2_1_8 (x y : ℝ) :
    (y + 3 = -Real.sqrt 2 * (x - 0) ↔ y = -Real.sqrt 2 * x - 3) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.10: the line of slope `678` through `(-1,-12)` is `y = 678x + 666`. -/
@[kb "stitzzeager2013" "Exercise 2.1.10, p. 175"]
theorem exer_2_1_10 (x y : ℝ) : (y + 12 = 678 * (x + 1) ↔ y = 678 * x + 666) := by
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.11: the line through `(0,0)` and `(-3,5)` is `y = -5x/3`. -/
@[kb "stitzzeager2013" "Exercise 2.1.11, p. 175"]
theorem exer_2_1_11 (m b : ℝ) :
    (m * 0 + b = 0 ∧ m * (-3) + b = 5) ↔ (m = -5 / 3 ∧ b = 0) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.12: the line through `(-1,-2)` and `(3,-2)` is `y = -2`. -/
@[kb "stitzzeager2013" "Exercise 2.1.12, p. 175"]
theorem exer_2_1_12 (m b : ℝ) :
    (m * (-1) + b = -2 ∧ m * 3 + b = -2) ↔ (m = 0 ∧ b = -2) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.15: the line through `(-1,5)` and `(7,5)` is `y = 5`. -/
@[kb "stitzzeager2013" "Exercise 2.1.15, p. 175"]
theorem exer_2_1_15 (m b : ℝ) :
    (m * (-1) + b = 5 ∧ m * 7 + b = 5) ↔ (m = 0 ∧ b = 5) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.16: the line through `(4,-8)` and `(5,-8)` is `y = -8`. -/
@[kb "stitzzeager2013" "Exercise 2.1.16, p. 175"]
theorem exer_2_1_16 (m b : ℝ) :
    (m * 4 + b = -8 ∧ m * 5 + b = -8) ↔ (m = 0 ∧ b = -8) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.19: the line through `(√2,-√2)` and `(-√2,√2)` is `y = -x`. -/
@[kb "stitzzeager2013" "Exercise 2.1.19, p. 175"]
theorem exer_2_1_19 (m b : ℝ) :
    (m * Real.sqrt 2 + b = -Real.sqrt 2 ∧ m * (-Real.sqrt 2) + b = Real.sqrt 2) ↔
      (m = -1 ∧ b = 0) := by
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · rintro ⟨h1, h3⟩
    have hb : b = 0 := by linarith
    subst hb
    constructor
    · have : (m + 1) * Real.sqrt 2 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · rfl
  · rintro ⟨rfl, rfl⟩; constructor <;> ring

/-- Stitz-Zeager Exercise 2.1.21: `f(x) = 2x - 1` has slope `2`, y-intercept `-1`, and x-intercept
`1/2`. -/
@[kb "stitzzeager2013" "Exercise 2.1.21, p. 175"]
theorem exer_2_1_21 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x - 1) :
    (∀ x, f (x + 1) - f x = 2) ∧ f 0 = -1 ∧ (∀ x, f x = 0 ↔ x = 1 / 2) := by
  refine ⟨fun x => by simp only [hf]; ring, by simp [hf], fun x => ?_⟩
  rw [hf]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.22: `f(x) = 3 - x` has slope `-1`, y-intercept `3`, x-intercept `3`. -/
@[kb "stitzzeager2013" "Exercise 2.1.22, p. 175"]
theorem exer_2_1_22 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 - x) :
    (∀ x, f (x + 1) - f x = -1) ∧ f 0 = 3 ∧ (∀ x, f x = 0 ↔ x = 3) := by
  refine ⟨fun x => by simp only [hf]; ring, by simp [hf], fun x => ?_⟩
  rw [hf]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.23: `f(x) = 3` has slope `0`, y-intercept `3` and no x-intercept. -/
@[kb "stitzzeager2013" "Exercise 2.1.23, p. 175"]
theorem exer_2_1_23 (f : ℝ → ℝ) (hf : ∀ x, f x = 3) :
    (∀ x, f (x + 1) - f x = 0) ∧ f 0 = 3 ∧ (∀ x, f x ≠ 0) := by
  refine ⟨fun x => by simp [hf], by simp [hf], fun x => ?_⟩
  rw [hf]; norm_num

/-- Stitz-Zeager Exercise 2.1.24: `f(x) = 0` has slope `0`, y-intercept `0`, and every real number
is an x-intercept. -/
@[kb "stitzzeager2013" "Exercise 2.1.24, p. 175"]
theorem exer_2_1_24 (f : ℝ → ℝ) (hf : ∀ x, f x = 0) :
    (∀ x, f (x + 1) - f x = 0) ∧ f 0 = 0 ∧ (∀ x, f x = 0) := by
  refine ⟨fun x => by simp [hf], by simp [hf], hf⟩

/-- Stitz-Zeager Exercise 2.1.25: `f(x) = (2/3)x + 1/3` has slope `2/3`, y-intercept `1/3`,
x-intercept `-1/2`. -/
@[kb "stitzzeager2013" "Exercise 2.1.25, p. 175"]
theorem exer_2_1_25 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 / 3 * x + 1 / 3) :
    (∀ x, f (x + 1) - f x = 2 / 3) ∧ f 0 = 1 / 3 ∧ (∀ x, f x = 0 ↔ x = -1 / 2) := by
  refine ⟨fun x => by simp only [hf]; ring, by simp [hf], fun x => ?_⟩
  rw [hf]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.26: `f(x) = (1-x)/2` has slope `-1/2`, y-intercept `1/2`,
x-intercept `1`. -/
@[kb "stitzzeager2013" "Exercise 2.1.26, p. 175"]
theorem exer_2_1_26 (f : ℝ → ℝ) (hf : ∀ x, f x = (1 - x) / 2) :
    (∀ x, f (x + 1) - f x = -1 / 2) ∧ f 0 = 1 / 2 ∧ (∀ x, f x = 0 ↔ x = 1) := by
  refine ⟨fun x => by simp only [hf]; ring, by simp [hf], fun x => ?_⟩
  rw [hf]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 2.1.28: a linear distance function with `d(0) = 0` and speed `3` is
`d(t) = 3t`. -/
@[kb "stitzzeager2013" "Exercise 2.1.28, p. 175"]
theorem exer_2_1_28 (d : ℝ → ℝ) (hd : ∃ m b, ∀ t, d t = m * t + b) (h0 : d 0 = 0) (h1 : d 1 = 3) :
    ∀ t, d t = 3 * t := by
  obtain ⟨m, b, h⟩ := hd
  rw [h] at h0 h1
  have hm : m = 3 := by linarith
  have hb : b = 0 := by linarith
  intro t; rw [h, hm, hb]; ring

/-- Stitz-Zeager Exercise 2.1.29: envelopes stuffed after `t` hours at `6` per minute:
`E(t) = 360 t`. -/
@[kb "stitzzeager2013" "Exercise 2.1.29, p. 175"]
theorem exer_2_1_29 (E : ℝ → ℝ) (hd : ∃ m b, ∀ t, E t = m * t + b) (h0 : E 0 = 0)
    (h1 : E 1 = 6 * 60) : ∀ t, E t = 360 * t := by
  obtain ⟨m, b, h⟩ := hd
  rw [h] at h0 h1
  have hm : m = 360 := by linarith
  have hb : b = 0 := by linarith
  intro t; rw [h, hm, hb]; ring

/-- Stitz-Zeager Exercise 2.1.30: mulch cost `C(x) = 45x + 20` (fixed delivery `20`, `45` per yard). -/
@[kb "stitzzeager2013" "Exercise 2.1.30, p. 175"]
theorem exer_2_1_30 (C : ℝ → ℝ) (hd : ∃ m b, ∀ t, C t = m * t + b) (h0 : C 0 = 20)
    (h1 : C 1 = 65) : ∀ x, C x = 45 * x + 20 := by
  obtain ⟨m, b, h⟩ := hd
  rw [h] at h0 h1
  have hm : m = 45 := by linarith
  have hb : b = 20 := by linarith
  intro t; rw [h, hm, hb]

/-- Stitz-Zeager Exercise 2.1.31: plumber's daily charge `C(t) = 80t + 50` (fixed call `50`, `80`
per hour). -/
@[kb "stitzzeager2013" "Exercise 2.1.31, p. 176"]
theorem exer_2_1_31 (C : ℝ → ℝ) (hd : ∃ m b, ∀ t, C t = m * t + b) (h0 : C 0 = 50)
    (h1 : C 1 = 130) : ∀ t, C t = 80 * t + 50 := by
  obtain ⟨m, b, h⟩ := hd
  rw [h] at h0 h1
  have hm : m = 80 := by linarith
  have hb : b = 50 := by linarith
  intro t; rw [h, hm, hb]

/-- Stitz-Zeager Exercise 2.1.34: taxi fare with `F(0.2) = 2.5` and `F(0.4) = 2.95` is
`F(m) = 2.25 m + 2.05`, slope `2.25`, `F(0) = 2.05`. -/
@[kb "stitzzeager2013" "Exercise 2.1.34, p. 176"]
theorem exer_2_1_34 (F : ℝ → ℝ) (hd : ∃ m b, ∀ t, F t = m * t + b) (h1 : F (1 / 5) = 5 / 2)
    (h2 : F (2 / 5) = 59 / 20) : (∀ m, F m = 9 / 4 * m + 41 / 20) ∧ F 0 = 41 / 20 := by
  obtain ⟨m, b, h⟩ := hd
  rw [h] at h1 h2
  have hm : m = 9 / 4 := by linarith
  have hb : b = 41 / 20 := by linarith
  subst hm; subst hb
  exact ⟨fun t => h t, by rw [h]; ring⟩

/-- Stitz-Zeager Exercise 2.1.39: weekend pizza cost: `6p + 1.5` for `1 ≤ p ≤ 5`, `5.5p` for
`p ≥ 6`; five pizzas cost `31.5`, six cost `33`. -/
@[kb "stitzzeager2013" "Exercise 2.1.39, p. 176"]
theorem exer_2_1_39 (C : ℕ → ℝ)
    (hC : ∀ p : ℕ, C p = if p ≤ 5 then 6 * (p : ℝ) + 3 / 2 else 11 / 2 * (p : ℝ)) :
    (∀ p : ℕ, 1 ≤ p → p ≤ 5 → C p = 6 * p + 3 / 2) ∧ (∀ p : ℕ, 6 ≤ p → C p = 11 / 2 * p) ∧
      C 5 = 63 / 2 ∧ C 6 = 33 := by
  refine ⟨fun p _ h => by rw [hC, if_pos h], fun p h => by rw [hC, if_neg (by omega)], ?_, ?_⟩
  · rw [hC]; norm_num
  · rw [hC]; norm_num

/-- Stitz-Zeager Exercise 2.1.40: buffet bill `15n` for `1 ≤ n ≤ 9`, `12.5n` for `n ≥ 10`; a party
of `10` pays less than a party of `9`. -/
@[kb "stitzzeager2013" "Exercise 2.1.40, p. 177"]
theorem exer_2_1_40 (T : ℕ → ℝ)
    (hT : ∀ n : ℕ, T n = if n ≤ 9 then 15 * (n : ℝ) else 25 / 2 * (n : ℝ)) :
    (∀ n : ℕ, 1 ≤ n → n ≤ 9 → T n = 15 * n) ∧ (∀ n : ℕ, 10 ≤ n → T n = 25 / 2 * n) ∧
      T 10 < T 9 := by
  refine ⟨fun n _ h => by rw [hT, if_pos h], fun n h => by rw [hT, if_neg (by omega)], ?_⟩
  rw [hT, hT]; norm_num

/-- Stitz-Zeager Exercise 2.1.41: the mobile plan cost is `10` up to `500` minutes and
`10 + 0.15 (m - 500)` beyond; equivalently `10 + 0.15 max(m - 500, 0)`. -/
@[kb "stitzzeager2013" "Exercise 2.1.41, p. 177"]
theorem exer_2_1_41 (m : ℝ) (hm : 0 ≤ m) :
    (if m ≤ 500 then (10 : ℝ) else 10 + 15 / 100 * (m - 500)) = 10 + 15 / 100 * max (m - 500) 0 := by
  split_ifs with h
  · rw [max_eq_right (by linarith)]; ring
  · rw [max_eq_left (by linarith)]

/-- Stitz-Zeager Exercise 2.1.42: cricket price `0.12c` up to `100`, `12 + 0.1(c - 100)` beyond;
equivalently `0.12 min(c,100) + 0.1 max(c - 100, 0)`. -/
@[kb "stitzzeager2013" "Exercise 2.1.42, p. 177"]
theorem exer_2_1_42 (c : ℝ) (hc : 1 ≤ c) :
    (if c ≤ 100 then 12 / 100 * c else 12 + 1 / 10 * (c - 100)) =
      12 / 100 * min c 100 + 1 / 10 * max (c - 100) 0 := by
  split_ifs with h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring

/-- Stitz-Zeager Exercise 2.1.43: pool depth from the shallow end is `8` on `[0,15]`, `-d/2 + 31/2` on
`[15,27]`, `2` on `[27,37]`; from the deep end it is `2` on `[0,10]`, `s/2 - 3` on `[10,22]`, `8` on
`[22,37]`; the two descriptions agree under `s = 37 - d`. -/
@[kb "stitzzeager2013" "Exercise 2.1.43, p. 177"]
theorem exer_2_1_43 (Da Db : ℝ → ℝ)
    (ha : ∀ d, Da d = if d ≤ 15 then 8 else if d ≤ 27 then -(1 / 2) * d + 31 / 2 else 2)
    (hb : ∀ s, Db s = if s ≤ 10 then 2 else if s ≤ 22 then 1 / 2 * s - 3 else 8) :
    ∀ s, 0 ≤ s → s ≤ 37 → Db s = Da (37 - s) := by
  intro s h0 h1
  rw [hb, ha]
  by_cases a : s ≤ 10
  · rw [if_pos a, if_neg (by linarith)]
    by_cases a' : 37 - s ≤ 27
    · rw [if_pos a']; have : s = 10 := by linarith
      subst this; norm_num
    · rw [if_neg a']
  · by_cases b : s ≤ 22
    · rw [if_neg a, if_pos b]
      by_cases c : 37 - s ≤ 15
      · rw [if_pos c]; have : s = 22 := by linarith
        subst this; norm_num
      · rw [if_neg c, if_pos (by linarith)]; ring
    · rw [if_neg a, if_neg b, if_pos (by linarith)]

/-- Stitz-Zeager Exercise 2.1.45: the average rate of change of `1/x` on `[1,5]` is `-1/5`. -/
@[kb "stitzzeager2013" "Exercise 2.1.45, p. 177"]
theorem exer_2_1_45 : (1 / (5 : ℝ) - 1 / 1) / (5 - 1) = -1 / 5 := by norm_num

/-- Stitz-Zeager Exercise 2.1.46: the average rate of change of `√x` on `[0,16]` is `1/4`. -/
@[kb "stitzzeager2013" "Exercise 2.1.46, p. 177"]
theorem exer_2_1_46 : (Real.sqrt 16 - Real.sqrt 0) / (16 - 0) = 1 / 4 := by
  have : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [this]; simp; norm_num

/-- Stitz-Zeager Exercise 2.1.47: the average rate of change of `x²` on `[-3,3]` is `0`. -/
@[kb "stitzzeager2013" "Exercise 2.1.47, p. 177"]
theorem exer_2_1_47 : ((3 : ℝ) ^ 2 - (-3) ^ 2) / (3 - (-3)) = 0 := by norm_num

/-- Stitz-Zeager Exercise 2.1.48: the average rate of change of `(x+4)/(x-3)` on `[5,7]` is `-7/8`. -/
@[kb "stitzzeager2013" "Exercise 2.1.48, p. 177"]
theorem exer_2_1_48 : ((7 + 4) / (7 - 3) - (5 + 4) / (5 - 3) : ℝ) / (7 - 5) = -7 / 8 := by norm_num

/-- Stitz-Zeager Exercise 2.1.49: the average rate of change of `3x² + 2x - 7` on `[-4,2]` is `-4`. -/
@[kb "stitzzeager2013" "Exercise 2.1.49, p. 177"]
theorem exer_2_1_49 :
    ((3 * 2 ^ 2 + 2 * 2 - 7) - (3 * (-4) ^ 2 + 2 * (-4) - 7) : ℝ) / (2 - (-4)) = -4 := by
  norm_num

/-- Stitz-Zeager Exercise 2.1.51: the average rate of change of `1/x` on `[x,x+h]` is
`-1/(x(x+h))`. -/
@[kb "stitzzeager2013" "Exercise 2.1.51, p. 178"]
theorem exer_2_1_51 (x h : ℝ) (hx : x ≠ 0) (hxh : x + h ≠ 0) (hh : h ≠ 0) :
    (1 / (x + h) - 1 / x) / ((x + h) - x) = -1 / (x * (x + h)) := by
  have : (x + h) - x = h := by ring
  rw [this]; field_simp; ring

/-- Stitz-Zeager Exercise 2.1.52: the average rate of change of `(x+4)/(x-3)` on `[x,x+h]` is
`-7/((x-3)(x+h-3))`. -/
@[kb "stitzzeager2013" "Exercise 2.1.52, p. 178"]
theorem exer_2_1_52 (x h : ℝ) (hx : x - 3 ≠ 0) (hxh : x + h - 3 ≠ 0) (hh : h ≠ 0) :
    ((x + h + 4) / (x + h - 3) - (x + 4) / (x - 3)) / ((x + h) - x) =
      -7 / ((x - 3) * (x + h - 3)) := by
  have : (x + h) - x = h := by ring
  rw [this]; field_simp; ring

/-- Stitz-Zeager Exercise 2.1.53: the average rate of change of `3x² + 2x - 7` on `[x,x+h]` is
`6x + 3h + 2`. -/
@[kb "stitzzeager2013" "Exercise 2.1.53, p. 178"]
theorem exer_2_1_53 (x h : ℝ) (hh : h ≠ 0) :
    ((3 * (x + h) ^ 2 + 2 * (x + h) - 7) - (3 * x ^ 2 + 2 * x - 7)) / ((x + h) - x) =
      6 * x + 3 * h + 2 := by
  have : (x + h) - x = h := by ring
  rw [this, div_eq_iff hh]; ring

/-- Stitz-Zeager Exercise 2.1.60: the line parallel to `y = -6x + 5` through `(3,2)` is `y = -6x + 20`. -/
@[kb "stitzzeager2013" "Exercise 2.1.60, p. 178"]
theorem exer_2_1_60 (m b : ℝ) : (m = -6 ∧ m * 3 + b = 2) ↔ (m = -6 ∧ b = 20) := by
  constructor
  · rintro ⟨h1, h2⟩; subst h1; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.61: the line parallel to `y = (2/3)x - 7` through `(6,0)` is
`y = (2/3)x - 4`. -/
@[kb "stitzzeager2013" "Exercise 2.1.61, p. 179"]
theorem exer_2_1_61 (m b : ℝ) : (m = 2 / 3 ∧ m * 6 + b = 0) ↔ (m = 2 / 3 ∧ b = -4) := by
  constructor
  · rintro ⟨h1, h2⟩; subst h1; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.65: the line perpendicular to `y = x/3 + 2` through the origin is `y = -3x`. -/
@[kb "stitzzeager2013" "Exercise 2.1.65, p. 179"]
theorem exer_2_1_65 (m b : ℝ) : (m * (1 / 3) = -1 ∧ m * 0 + b = 0) ↔ (m = -3 ∧ b = 0) := by
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.67: the line perpendicular to `y = (2/3)x - 7` through `(6,0)` is
`y = -3x/2 + 9`. -/
@[kb "stitzzeager2013" "Exercise 2.1.67, p. 179"]
theorem exer_2_1_67 (m b : ℝ) : (m * (2 / 3) = -1 ∧ m * 6 + b = 0) ↔ (m = -(3 / 2) ∧ b = 9) := by
  constructor
  · rintro ⟨h1, h2⟩; have : m = -(3 / 2) := by linarith
    subst this; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Exercise 2.1.68: the line perpendicular to `y = (4-x)/3` through `(1,-1)` is `y = 3x - 4`. -/
@[kb "stitzzeager2013" "Exercise 2.1.68, p. 179"]
theorem exer_2_1_68 (m b : ℝ) : (m * (-(1 / 3)) = -1 ∧ m * 1 + b = -1) ↔ (m = 3 ∧ b = -4) := by
  constructor
  · rintro ⟨h1, h2⟩; have : m = 3 := by linarith
    subst this; constructor <;> linarith
  · rintro ⟨rfl, rfl⟩; norm_num

end UndergradKB.Precalculus.Course
