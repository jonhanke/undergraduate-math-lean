import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Group.Even
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Plane

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 1.1 -/

/-- Stitz-Zeager Exercise 1.1.2: `(-1,5] ∩ [0,8) = [0,5]`. -/
@[kb "stitzzeager2013" "Exercise 1.1.2, p. 26"]
theorem exer_1_1_2 : Ioc (-1 : ℝ) 5 ∩ Ico 0 8 = Icc 0 5 := by
  ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ico, mem_Icc]
  constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> grind

/-- Stitz-Zeager Exercise 1.1.3: `(-1,1) ∪ [0,6] = (-1,6]`. -/
@[kb "stitzzeager2013" "Exercise 1.1.3, p. 26"]
theorem exer_1_1_3 : Ioo (-1 : ℝ) 1 ∪ Icc 0 6 = Ioc (-1) 6 := by
  ext x; simp only [mem_union, mem_Ioo, mem_Icc, mem_Ioc]
  constructor <;> intro h <;> grind

/-- Stitz-Zeager Exercise 1.1.4: `(-∞,4] ∩ (0,∞) = (0,4]`. -/
@[kb "stitzzeager2013" "Exercise 1.1.4, p. 26"]
theorem exer_1_1_4 : Iic (4 : ℝ) ∩ Ioi 0 = Ioc 0 4 := by
  ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
  grind

/-- Stitz-Zeager Exercise 1.1.5: `(-∞,0) ∩ [1,5]` is empty. -/
@[kb "stitzzeager2013" "Exercise 1.1.5, p. 26"]
theorem exer_1_1_5 : Iio (0 : ℝ) ∩ Icc 1 5 = ∅ := by
  ext x; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_empty_iff_false, iff_false]
  grind

/-- Stitz-Zeager Exercise 1.1.7: `(-∞,5] ∩ [5,8) = {5}`. -/
@[kb "stitzzeager2013" "Exercise 1.1.7, p. 26"]
theorem exer_1_1_7 : Iic (5 : ℝ) ∩ Ico 5 8 = {5} := by
  ext x; simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_singleton_iff]
  grind

/-- Stitz-Zeager Exercise 1.1.10: `{x | x ≠ -3, 4}` is `(-∞,-3) ∪ (-3,4) ∪ (4,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.10, p. 26"]
theorem exer_1_1_10 :
    {x : ℝ | x ≠ -3 ∧ x ≠ 4} = Iio (-3) ∪ Ioo (-3) 4 ∪ Ioi 4 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  grind

/-- Stitz-Zeager Exercise 1.1.13: `{x | x ≠ 0, ±4}` is four open intervals. -/
@[kb "stitzzeager2013" "Exercise 1.1.13, p. 27"]
theorem exer_1_1_13 :
    {x : ℝ | x ≠ 0 ∧ x ≠ 4 ∧ x ≠ -4} = Iio (-4) ∪ Ioo (-4) 0 ∪ Ioo 0 4 ∪ Ioi 4 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  grind

/-- Stitz-Zeager Exercise 1.1.14: `x ≤ -1` or `x ≥ 1` is `(-∞,-1] ∪ [1,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.14, p. 27"]
theorem exer_1_1_14 : {x : ℝ | x ≤ -1 ∨ x ≥ 1} = Iic (-1) ∪ Ici 1 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici]

/-- Stitz-Zeager Exercise 1.1.15: `x < 3` or `x ≥ 2` holds for every real number. -/
@[kb "stitzzeager2013" "Exercise 1.1.15, p. 27"]
theorem exer_1_1_15 : {x : ℝ | x < 3 ∨ x ≥ 2} = univ := by
  ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]
  grind

/-- Stitz-Zeager Exercise 1.1.17: `x ≤ 5` or `x = 6` is `(-∞,5] ∪ {6}`. -/
@[kb "stitzzeager2013" "Exercise 1.1.17, p. 27"]
theorem exer_1_1_17 : {x : ℝ | x ≤ 5 ∨ x = 6} = Iic 5 ∪ {6} := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_singleton_iff]

/-- Stitz-Zeager Exercise 1.1.18: `x > 2` or `x = ±1` is `{-1} ∪ {1} ∪ (2,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.18, p. 27"]
theorem exer_1_1_18 : {x : ℝ | x > 2 ∨ x = 1 ∨ x = -1} = {-1} ∪ {1} ∪ Ioi 2 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_singleton_iff, mem_Ioi]
  grind

/-- Stitz-Zeager Exercise 1.1.19: `-3 < x < 3` or `x = 4` is `(-3,3) ∪ {4}`. -/
@[kb "stitzzeager2013" "Exercise 1.1.19, p. 27"]
theorem exer_1_1_19 : {x : ℝ | (-3 < x ∧ x < 3) ∨ x = 4} = Ioo (-3) 3 ∪ {4} := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_singleton_iff]

/-- Stitz-Zeager Exercise 1.1.22: for `(1,2)` and `(-3,5)` the distance is `5` and the midpoint `(-1, 7/2)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.22, p. 28"]
theorem exer_1_1_22 :
    Real.sqrt ((1 - (-3)) ^ 2 + (2 - 5) ^ 2 : ℝ) = 5 ∧
      (((1 : ℝ) + (-3)) / 2, ((2 : ℝ) + 5) / 2) = (-1, 7 / 2) := by
  refine ⟨?_, by norm_num⟩
  rw [show ((1 - (-3)) ^ 2 + (2 - 5) ^ 2 : ℝ) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Stitz-Zeager Exercise 1.1.23: for `(3,-10)` and `(-1,2)` the distance is `4√10` and the midpoint `(1,-4)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.23, p. 28"]
theorem exer_1_1_23 :
    Real.sqrt ((3 - (-1)) ^ 2 + (-10 - 2) ^ 2 : ℝ) = 4 * Real.sqrt 10 ∧
      (((3 : ℝ) + (-1)) / 2, ((-10 : ℝ) + 2) / 2) = (1, -4) := by
  refine ⟨?_, by norm_num⟩
  rw [show ((3 - (-1)) ^ 2 + (-10 - 2) ^ 2 : ℝ) = 4 ^ 2 * 10 by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Exercise 1.1.25: for `(-2/3, 3/2)` and `(7/3, 2)` the distance is `√37 / 2` and the midpoint
`(5/6, 7/4)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.25, p. 28"]
theorem exer_1_1_25 :
    Real.sqrt ((-2 / 3 - 7 / 3) ^ 2 + (3 / 2 - 2) ^ 2 : ℝ) = Real.sqrt 37 / 2 ∧
      (((-2 / 3 : ℝ) + 7 / 3) / 2, ((3 / 2 : ℝ) + 2) / 2) = (5 / 6, 7 / 4) := by
  refine ⟨?_, by norm_num⟩
  rw [show ((-2 / 3 - 7 / 3) ^ 2 + (3 / 2 - 2) ^ 2 : ℝ) = 37 / 2 ^ 2 by norm_num,
    Real.sqrt_div' _ (by norm_num), Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Exercise 1.1.26: for `(24/5, 6/5)` and `(-11/5, -19/5)` the distance is `√74` and the
midpoint `(13/10, -13/10)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.26, p. 28"]
theorem exer_1_1_26 :
    Real.sqrt ((24 / 5 - (-11 / 5)) ^ 2 + (6 / 5 - (-19 / 5)) ^ 2 : ℝ) = Real.sqrt 74 ∧
      (((24 / 5 : ℝ) + (-11 / 5)) / 2, ((6 / 5 : ℝ) + (-19 / 5)) / 2) = (13 / 10, -13 / 10) := by
  refine ⟨?_, by norm_num⟩
  congr 1; norm_num

/-- Stitz-Zeager Exercise 1.1.27: for `(√2, √3)` and `(-√8, -√12)` the distance is `3√5` and the midpoint
`(-√2/2, -√3/2)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.27, p. 28"]
theorem exer_1_1_27 :
    Real.sqrt ((√2 - (-√8)) ^ 2 + (√3 - (-√12)) ^ 2) = 3 * √5 ∧
      ((√2 + (-√8)) / 2, (√3 + (-√12)) / 2) = (-(√2 / 2), -(√3 / 2)) := by
  have h8 : √8 = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 0 ≤ √5 := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · rw [h8, h12, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    nlinarith
  · rw [h8, h12]; ext <;> simp <;> ring

/-- Stitz-Zeager Exercise 1.1.30: the points `(x,-1)` at distance `4` from `(3,2)` are `(3 ± √7, -1)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.30, p. 28"]
theorem exer_1_1_30 (x : ℝ) :
    Real.sqrt ((x - 3) ^ 2 + (-1 - 2) ^ 2) = 4 ↔ x = 3 + √7 ∨ x = 3 - √7 := by
  have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]
  constructor
  · intro h
    have : (x - 3 - √7) * (x - 3 + √7) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> nlinarith

/-- Stitz-Zeager Exercise 1.1.31: the only point `(0,y)` on the y-axis at distance `5` from `(-5,3)` is `(0,3)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.31, p. 28"]
theorem exer_1_1_31 (y : ℝ) : Real.sqrt ((0 - (-5)) ^ 2 + (y - 3) ^ 2) = 5 ↔ y = 3 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]
  constructor
  · intro h; nlinarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 1.1.33: the points `(x,-x)` at distance `1` from the origin are `(±√2/2, ∓√2/2)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.33, p. 28"]
theorem exer_1_1_33 (x : ℝ) :
    Real.sqrt (x ^ 2 + (-x) ^ 2) = 1 ↔ x = √2 / 2 ∨ x = -(√2 / 2) := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_eq_one]
  constructor
  · intro h
    have : (x - √2 / 2) * (x + √2 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> nlinarith

/-- Stitz-Zeager Exercise 1.1.37(a): `A(-3,2)`, `B(-6,4)`, `C(1,8)` have squared side lengths `13`, `52`, `65`,
and `13 + 52 = 65`, so the triangle is right-angled at `A`. -/
@[kb "stitzzeager2013" "Exercise 1.1.37, p. 28"]
theorem exer_1_1_37_a :
    ((-3 - -6) ^ 2 + (2 - 4) ^ 2 : ℝ) = 13 ∧ ((-3 - 1) ^ 2 + (2 - 8) ^ 2 : ℝ) = 52 ∧
      ((-6 - 1) ^ 2 + (4 - 8) ^ 2 : ℝ) = 65 ∧ (13 + 52 : ℝ) = 65 := by
  norm_num

/-- Stitz-Zeager Exercise 1.1.37(b): for `A(-3,1)`, `B(4,0)`, `C(0,-3)` the squared lengths satisfy
`|AC|² + |BC|² = |AB|²`, so the triangle is right-angled at `C`. -/
@[kb "stitzzeager2013" "Exercise 1.1.37, p. 28"]
theorem exer_1_1_37_b :
    ((-3 - 0) ^ 2 + (1 - -3) ^ 2 : ℝ) + ((4 - 0) ^ 2 + (0 - -3) ^ 2) = (-3 - 4) ^ 2 + (1 - 0) ^ 2 := by
  norm_num

/-! ## Section 1.2 -/

/-- Stitz-Zeager Exercise 1.2.3: the relation `{(m, 2m) | m = 0, ±1, ±2}` is the five listed points. -/
@[kb "stitzzeager2013" "Exercise 1.2.3, p. 41"]
theorem exer_1_2_3 :
    (Finset.Icc (-2 : ℤ) 2).image (fun m => (m, 2 * m)) =
      {(-2, -4), (-1, -2), (0, 0), (1, 2), (2, 4)} := by
  decide

/-- Stitz-Zeager Exercise 1.2.6: the relation `{(j, √j) | j = 0, 1, 4, 9}` is the four points
`(0,0), (1,1), (4,2), (9,3)`. -/
@[kb "stitzzeager2013" "Exercise 1.2.6, p. 41"]
theorem exer_1_2_6 :
    {p : ℝ × ℝ | ∃ j ∈ ({0, 1, 4, 9} : Set ℝ), p = (j, √j)} = {(0, 0), (1, 1), (4, 2), (9, 3)} := by
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h9 : √(9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  ext ⟨a, b⟩
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩
    rcases hj with rfl | rfl | rfl | rfl <;> simp [h4, h9]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨4, by simp [h4]⟩
    · exact ⟨9, by simp [h9]⟩

/-- Stitz-Zeager Exercise 1.2.41: `y = x² + 1` has no x-intercept, y-intercept `(0,1)`, and is symmetric about
the y-axis only. -/
@[kb "stitzzeager2013" "Exercise 1.2.41, p. 44"]
theorem exer_1_2_41 (S : Set (ℝ × ℝ)) (hS : S = {p | p.2 = p.1 ^ 2 + 1}) :
    (∀ x : ℝ, (x, 0) ∉ S) ∧ {y : ℝ | (0, y) ∈ S} = {1} ∧
      ¬ SymmetricX S ∧ SymmetricY S ∧ ¬ SymmetricO S := by
  subst hS
  refine ⟨fun x h => ?_, ?_, fun h => ?_, fun p hp => ?_, fun h => ?_⟩
  · simp only [mem_ofPred_eq] at h; nlinarith [sq_nonneg x]
  · ext y; simp
  · have := h (2, 5) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp
  · have := h (2, 5) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.2.42: `y = x² - 2x - 8` has x-intercepts `4` and `-2`, y-intercept `(0,-8)`, and no
symmetry of the three kinds. -/
@[kb "stitzzeager2013" "Exercise 1.2.42, p. 44"]
theorem exer_1_2_42 (S : Set (ℝ × ℝ)) (hS : S = {p | p.2 = p.1 ^ 2 - 2 * p.1 - 8}) :
    {x : ℝ | (x, 0) ∈ S} = {4, -2} ∧ {y : ℝ | (0, y) ∈ S} = {-8} ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ ¬ SymmetricO S := by
  subst hS
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : (x - 4) * (x + 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · ext y; simp
  · have := h (-3, 7) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (-3, 7) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (-3, 7) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.2.43: `y = x³ - x` has x-intercepts `-1, 0, 1`, y-intercept `(0,0)`, and is
symmetric about the origin only. -/
@[kb "stitzzeager2013" "Exercise 1.2.43, p. 44"]
theorem exer_1_2_43 (S : Set (ℝ × ℝ)) (hS : S = {p | p.2 = p.1 ^ 3 - p.1}) :
    {x : ℝ | (x, 0) ∈ S} = {-1, 0, 1} ∧ {y : ℝ | (0, y) ∈ S} = {0} ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ SymmetricO S := by
  subst hS
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_, fun p hp => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : (x + 1) * x * (x - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · left; linarith
        · right; left; exact h
      · right; right; linarith
    · rintro (rfl | rfl | rfl) <;> norm_num
  · ext y; simp
  · have := h (2, 6) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (2, 6) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · simp only [mem_ofPred_eq] at hp ⊢; linarith [hp]

/-- Stitz-Zeager Exercise 1.2.44: `y = x³/4 - 3x` has x-intercepts `0` and `±2√3`, y-intercept `(0,0)`, and is
symmetric about the origin only. -/
@[kb "stitzzeager2013" "Exercise 1.2.44, p. 44"]
theorem exer_1_2_44 (S : Set (ℝ × ℝ)) (hS : S = {p | p.2 = p.1 ^ 3 / 4 - 3 * p.1}) :
    {x : ℝ | (x, 0) ∈ S} = {0, 2 * √3, -(2 * √3)} ∧ {y : ℝ | (0, y) ∈ S} = {0} ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ SymmetricO S := by
  subst hS
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_, fun p hp => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : x * ((x - 2 * √3) * (x + 2 * √3)) = 0 := by
        linear_combination (-4) * h + (-4 * x) * h3
      rcases mul_eq_zero.mp this with h | h
      · left; exact h
      · rcases mul_eq_zero.mp h with h | h
        · right; left; linarith
        · right; right; linarith
    · rintro (rfl | rfl | rfl)
      · norm_num
      · linear_combination (-2 * √3) * h3
      · linear_combination (2 * √3) * h3
  · ext y; simp
  · have := h (4, 4) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (4, 4) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · simp only [mem_ofPred_eq] at hp ⊢; linarith [hp]

/-- Stitz-Zeager Exercise 1.2.45: `y = √(x - 2)` has x-intercept `2`, no y-intercept, and no symmetry. -/
@[kb "stitzzeager2013" "Exercise 1.2.45, p. 44"]
theorem exer_1_2_45 (S : Set (ℝ × ℝ)) (hS : S = {p | 2 ≤ p.1 ∧ p.2 = √(p.1 - 2)}) :
    {x : ℝ | (x, 0) ∈ S} = {2} ∧ {y : ℝ | (0, y) ∈ S} = ∅ ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ ¬ SymmetricO S := by
  subst hS
  have h1 : √((3 : ℝ) - 2) = 1 := by norm_num
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hx, h0⟩
      have := Real.sqrt_eq_zero'.mp h0.symm
      linarith
    · rintro rfl; norm_num
  · ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; rintro ⟨h, -⟩; linarith
  · have := h (3, 1) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this
    have h2 := this.2
    rw [h1] at h2; norm_num at h2
  · have := h (3, 1) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (3, 1) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.2.47: `3x - y = 7` has x-intercept `7/3`, y-intercept `(0,-7)` and no symmetry. -/
@[kb "stitzzeager2013" "Exercise 1.2.47, p. 44"]
theorem exer_1_2_47 (S : Set (ℝ × ℝ)) (hS : S = {p | 3 * p.1 - p.2 = 7}) :
    {x : ℝ | (x, 0) ∈ S} = {7 / 3} ∧ {y : ℝ | (0, y) ∈ S} = {-7} ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ ¬ SymmetricO S := by
  subst hS
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_singleton_iff]; constructor <;> intro h <;> linarith
  · ext y; simp only [mem_ofPred_eq, mem_singleton_iff]; constructor <;> intro h <;> linarith
  · have := h (3, 2) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (3, 2) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (3, 2) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.2.48: `3x - 2y = 10` has x-intercept `10/3`, y-intercept `(0,-5)` and no symmetry. -/
@[kb "stitzzeager2013" "Exercise 1.2.48, p. 44"]
theorem exer_1_2_48 (S : Set (ℝ × ℝ)) (hS : S = {p | 3 * p.1 - 2 * p.2 = 10}) :
    {x : ℝ | (x, 0) ∈ S} = {10 / 3} ∧ {y : ℝ | (0, y) ∈ S} = {-5} ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ ¬ SymmetricO S := by
  subst hS
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_singleton_iff]; constructor <;> intro h <;> linarith
  · ext y; simp only [mem_ofPred_eq, mem_singleton_iff]; constructor <;> intro h <;> linarith
  · have := h (2, -2) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (2, -2) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (2, -2) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this

/-- Stitz-Zeager Exercise 1.2.50: `x² - y² = 1` has x-intercepts `±1`, no y-intercept, and is symmetric about
both axes and the origin. -/
@[kb "stitzzeager2013" "Exercise 1.2.50, p. 44"]
theorem exer_1_2_50 (S : Set (ℝ × ℝ)) (hS : S = {p | p.1 ^ 2 - p.2 ^ 2 = 1}) :
    {x : ℝ | (x, 0) ∈ S} = {1, -1} ∧ {y : ℝ | (0, y) ∈ S} = ∅ ∧
      SymmetricX S ∧ SymmetricY S ∧ SymmetricO S := by
  subst hS
  refine ⟨?_, ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; intro h; nlinarith [sq_nonneg y]
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp

/-- Stitz-Zeager Exercise 1.2.51: `4y² - 9x² = 36` has no x-intercept, y-intercepts `(0, ±3)`, and is symmetric
about both axes and the origin. -/
@[kb "stitzzeager2013" "Exercise 1.2.51, p. 44"]
theorem exer_1_2_51 (S : Set (ℝ × ℝ)) (hS : S = {p | 4 * p.2 ^ 2 - 9 * p.1 ^ 2 = 36}) :
    (∀ x : ℝ, (x, 0) ∉ S) ∧ {y : ℝ | (0, y) ∈ S} = {3, -3} ∧
      SymmetricX S ∧ SymmetricY S ∧ SymmetricO S := by
  subst hS
  refine ⟨fun x h => ?_, ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · simp only [mem_ofPred_eq] at h; nlinarith [sq_nonneg x]
  · ext y
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : (y - 3) * (y + 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp

/-- Stitz-Zeager Exercise 1.2.52: `x³ y = -4` has no intercepts and is symmetric about the origin only. -/
@[kb "stitzzeager2013" "Exercise 1.2.52, p. 44"]
theorem exer_1_2_52 (S : Set (ℝ × ℝ)) (hS : S = {p | p.1 ^ 3 * p.2 = -4}) :
    (∀ x : ℝ, (x, 0) ∉ S) ∧ (∀ y : ℝ, (0, y) ∉ S) ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ SymmetricO S := by
  subst hS
  refine ⟨fun x h => ?_, fun y h => ?_, fun h => ?_, fun h => ?_, fun p hp => ?_⟩
  · simp only [mem_ofPred_eq] at h; norm_num at h
  · simp only [mem_ofPred_eq] at h; norm_num at h
  · have := h (1, -4) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (1, -4) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · simp only [mem_ofPred_eq] at hp ⊢; linarith [hp]

/-! ## Section 1.3 -/

/-- Stitz-Zeager Exercise 1.3.1: the seven listed points form a function with domain `{-3,...,3}` and
range `{0,1,4,9}`. -/
@[kb "stitzzeager2013" "Exercise 1.3.1, p. 61"]
theorem exer_1_3_1 (R : Finset (ℤ × ℤ))
    (hR : R = {(-3, 9), (-2, 4), (-1, 1), (0, 0), (1, 1), (2, 4), (3, 9)}) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧
      R.image Prod.fst = {-3, -2, -1, 0, 1, 2, 3} ∧ R.image Prod.snd = {0, 1, 4, 9} := by
  subst hR; decide

/-- Stitz-Zeager Exercise 1.3.2: the relation with the points `(4,2)` and `(4,-9)` is not a function. -/
@[kb "stitzzeager2013" "Exercise 1.3.2, p. 61"]
theorem exer_1_3_2 (R : Finset (ℤ × ℤ))
    (hR : R = {(-3, 0), (1, 6), (2, -3), (4, 2), (-5, 6), (4, -9), (6, 2)}) :
    ¬ ∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2 := by
  subst hR; decide

/-- Stitz-Zeager Exercise 1.3.3: the six listed points form a function with domain `{-7,-3,3,4,5,6}` and
range `{0,4,5,6,9}`. -/
@[kb "stitzzeager2013" "Exercise 1.3.3, p. 61"]
theorem exer_1_3_3 (R : Finset (ℤ × ℤ))
    (hR : R = {(-3, 0), (-7, 6), (5, 5), (6, 4), (4, 9), (3, 0)}) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧
      R.image Prod.fst = {-7, -3, 3, 4, 5, 6} ∧ R.image Prod.snd = {0, 4, 5, 6, 9} := by
  subst hR; decide

/-- Stitz-Zeager Exercise 1.3.4: the pattern `(1,2), (4,4), (9,6), ...`, i.e. `(k², 2k)` for `k ≥ 1`, is a function
whose domain is the perfect squares `≥ 1` and whose range is the positive even numbers. -/
@[kb "stitzzeager2013" "Exercise 1.3.4, p. 61"]
theorem exer_1_3_4 (R : Set (ℕ × ℕ)) (hR : R = {p | ∃ k : ℕ, 0 < k ∧ p = (k ^ 2, 2 * k)}) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧
      Prod.fst '' R = {n | ∃ k : ℕ, 0 < k ∧ n = k ^ 2} ∧ Prod.snd '' R = {m | 0 < m ∧ Even m} := by
  subst hR
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩ h
    simp only at h ⊢
    have : k = l := by nlinarith
    omega
  · ext n
    simp only [mem_image, mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨k, hk, hab⟩, rfl⟩
      exact ⟨k, hk, by simp_all⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k ^ 2, 2 * k, ⟨k, hk, rfl⟩, rfl⟩
  · ext m
    simp only [mem_image, mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨k, hk, hab⟩, rfl⟩
      simp only [Prod.mk.injEq] at hab
      refine ⟨by omega, k, by omega⟩
    · rintro ⟨hm, k, rfl⟩
      exact ⟨(k - 0) ^ 2, k + k, ⟨k, by omega, by simp; omega⟩, rfl⟩

/-- Stitz-Zeager Exercise 1.3.6: `{(x, 1) | x irrational}` is a function with domain the irrationals and
range `{1}`. -/
@[kb "stitzzeager2013" "Exercise 1.3.6, p. 61"]
theorem exer_1_3_6 (R : Set (ℝ × ℝ)) (hR : R = {p | Irrational p.1 ∧ p.2 = 1}) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧
      Prod.fst '' R = {x | Irrational x} ∧ Prod.snd '' R = {1} := by
  subst hR
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨-, hp⟩ q ⟨-, hq⟩ -
    rw [hp, hq]
  · ext x
    simp only [mem_image, mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨ha, -⟩, rfl⟩; exact ha
    · intro hx; exact ⟨x, 1, ⟨hx, rfl⟩, rfl⟩
  · ext y
    simp only [mem_image, mem_ofPred_eq, Prod.exists, mem_singleton_iff]
    constructor
    · rintro ⟨a, b, ⟨-, hb⟩, rfl⟩; exact hb
    · rintro rfl; exact ⟨√2, 1, ⟨irrational_sqrt_two, rfl⟩, rfl⟩

/-- Stitz-Zeager Exercise 1.3.9: `{(-2, y) | -3 < y < 4}` is not a function (two points share `x = -2`). -/
@[kb "stitzzeager2013" "Exercise 1.3.9, p. 61"]
theorem exer_1_3_9 (R : Set (ℝ × ℝ)) (hR : R = {p | p.1 = -2 ∧ -3 < p.2 ∧ p.2 < 4}) :
    ¬ ∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2 := by
  subst hR
  intro h
  have := h (-2, 0) (by simp only [mem_ofPred_eq]; norm_num) (-2, 1) (by simp only [mem_ofPred_eq]; norm_num) rfl
  norm_num at this

/-- Stitz-Zeager Exercise 1.3.10: `{(x, 3) | -2 ≤ x < 4}` is a function with domain `[-2,4)` and range `{3}`. -/
@[kb "stitzzeager2013" "Exercise 1.3.10, p. 61"]
theorem exer_1_3_10 (R : Set (ℝ × ℝ)) (hR : R = {p | p.2 = 3 ∧ -2 ≤ p.1 ∧ p.1 < 4}) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧ Prod.fst '' R = Ico (-2) 4 ∧ Prod.snd '' R = {3} := by
  subst hR
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨hp, -⟩ q ⟨hq, -⟩ -
    rw [hp, hq]
  · ext x
    simp only [mem_image, mem_ofPred_eq, Prod.exists, mem_Ico]
    constructor
    · rintro ⟨a, b, ⟨-, h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨x, 3, ⟨rfl, h1, h2⟩, rfl⟩
  · ext y
    simp only [mem_image, mem_ofPred_eq, Prod.exists, mem_singleton_iff]
    constructor
    · rintro ⟨a, b, ⟨hb, -⟩, rfl⟩; exact hb
    · rintro rfl; exact ⟨0, 3, ⟨rfl, by norm_num, by norm_num⟩, rfl⟩

/-- Stitz-Zeager Exercise 1.3.11: `{(x, x²) | x real}` is a function with domain `ℝ` and range `[0,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.3.11, p. 61"]
theorem exer_1_3_11 (R : Set (ℝ × ℝ)) (hR : R = {p | p.2 = p.1 ^ 2}) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧ Prod.fst '' R = univ ∧ Prod.snd '' R = Ici 0 := by
  subst hR
  refine ⟨?_, ?_, ?_⟩
  · rintro p hp q hq h
    simp only [mem_ofPred_eq] at hp hq
    rw [hp, hq, h]
  · ext x
    simp only [mem_image, mem_ofPred_eq, Prod.exists, mem_univ, iff_true]
    exact ⟨x, x ^ 2, rfl, rfl⟩
  · ext y
    simp only [mem_image, mem_ofPred_eq, Prod.exists, mem_Ici]
    constructor
    · rintro ⟨a, b, hb, rfl⟩; rw [hb]; positivity
    · intro hy; exact ⟨√y, y, by simp [Real.sq_sqrt hy], rfl⟩

/-- Stitz-Zeager Exercise 1.3.12: `{(x², x) | x real}` is not a function, since `(1,1)` and `(1,-1)` both belong. -/
@[kb "stitzzeager2013" "Exercise 1.3.12, p. 61"]
theorem exer_1_3_12 (R : Set (ℝ × ℝ)) (hR : R = {p | p.1 = p.2 ^ 2}) :
    ¬ ∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2 := by
  subst hR
  intro h
  have := h (1, 1) (by simp only [mem_ofPred_eq]; norm_num) (1, -1) (by simp only [mem_ofPred_eq]; norm_num) rfl
  norm_num at this

/-- Stitz-Zeager Exercise 1.3.33: `y = x³ - x` represents `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.33, p. 64"]
theorem exer_1_3_33 : ∀ x : ℝ, {y : ℝ | y = x ^ 3 - x}.Subsingleton := by
  intro x y hy z hz
  simp only [mem_ofPred_eq] at hy hz
  rw [hy, hz]

/-- Stitz-Zeager Exercise 1.3.35: `x³ y = -4` represents `y` as a function of `x` (for each `x` at most one `y`). -/
@[kb "stitzzeager2013" "Exercise 1.3.35, p. 64"]
theorem exer_1_3_35 : ∀ x : ℝ, {y : ℝ | x ^ 3 * y = -4}.Subsingleton := by
  intro x y hy z hz
  simp only [mem_ofPred_eq] at hy hz
  have hx : x ^ 3 ≠ 0 := by rintro h; rw [h] at hy; norm_num at hy
  exact mul_left_cancel₀ hx (hy.trans hz.symm)

/-- Two solutions with the same `x` show that an equation does not give `y` as a function of `x`. -/
private theorem not_fun_of {P : ℝ → ℝ → Prop} (x a b : ℝ) (ha : P x a) (hb : P x b) (hab : a ≠ b) :
    ¬ ∀ x, {y : ℝ | P x y}.Subsingleton := fun h => hab (h x ha hb)

/-- Stitz-Zeager Exercise 1.3.36: `x² - y² = 1` does not represent `y` as a function of `x`
(`(√2, 1)` and `(√2, -1)` both satisfy it). -/
@[kb "stitzzeager2013" "Exercise 1.3.36, p. 64"]
theorem exer_1_3_36 : ¬ ∀ x : ℝ, {y : ℝ | x ^ 2 - y ^ 2 = 1}.Subsingleton := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  exact not_fun_of (P := fun x y => x ^ 2 - y ^ 2 = 1) (√2) (1) (-1) (by rw [h2]; norm_num) (by rw [h2]; norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 1.3.38: `x = -6` does not represent `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.38, p. 64"]
theorem exer_1_3_38 : ¬ ∀ x : ℝ, {y : ℝ | x = -6}.Subsingleton := by
  exact not_fun_of (P := fun x y => x = -6) (-6) (0) (1) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 1.3.39: `x = y² + 4` does not represent `y` as a function of `x` (`(5, 1)`, `(5, -1)`). -/
@[kb "stitzzeager2013" "Exercise 1.3.39, p. 64"]
theorem exer_1_3_39 : ¬ ∀ x : ℝ, {y : ℝ | x = y ^ 2 + 4}.Subsingleton := by
  exact not_fun_of (P := fun x y => x = y ^ 2 + 4) (5) (1) (-1) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 1.3.41: `x² + y² = 4` does not represent `y` as a function of `x`
(`(0, 2)`, `(0, -2)`). -/
@[kb "stitzzeager2013" "Exercise 1.3.41, p. 64"]
theorem exer_1_3_41 : ¬ ∀ x : ℝ, {y : ℝ | x ^ 2 + y ^ 2 = 4}.Subsingleton := by
  exact not_fun_of (P := fun x y => x ^ 2 + y ^ 2 = 4) (0) (2) (-2) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 1.3.42: `y = √(4 - x²)` represents `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.42, p. 64"]
theorem exer_1_3_42 : ∀ x : ℝ, {y : ℝ | y = √(4 - x ^ 2)}.Subsingleton := by
  intro x y hy z hz
  simp only [mem_ofPred_eq] at hy hz
  rw [hy, hz]

/-- Stitz-Zeager Exercise 1.3.43: `x² - y² = 4` does not represent `y` as a function of `x`
(`(√8, 2)` and `(√8, -2)`). -/
@[kb "stitzzeager2013" "Exercise 1.3.43, p. 64"]
theorem exer_1_3_43 : ¬ ∀ x : ℝ, {y : ℝ | x ^ 2 - y ^ 2 = 4}.Subsingleton := by
  have h2 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  exact not_fun_of (P := fun x y => x ^ 2 - y ^ 2 = 4) (√8) (2) (-2) (by rw [h2]; norm_num) (by rw [h2]; norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 1.3.44: `x³ + y³ = 4` represents `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.44, p. 64"]
theorem exer_1_3_44 : ∀ x : ℝ, {y : ℝ | x ^ 3 + y ^ 3 = 4}.Subsingleton := by
  intro x y hy z hz
  simp only [mem_ofPred_eq] at hy hz
  have : y ^ 3 = z ^ 3 := by linarith
  exact (Odd.strictMono_pow (by decide : Odd 3)).injective this

/-- Stitz-Zeager Exercise 1.3.46: `2xy = 4` represents `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.46, p. 64"]
theorem exer_1_3_46 : ∀ x : ℝ, {y : ℝ | 2 * x * y = 4}.Subsingleton := by
  intro x y hy z hz
  simp only [mem_ofPred_eq] at hy hz
  have hx : 2 * x ≠ 0 := by rintro h; rw [h] at hy; norm_num at hy
  exact mul_left_cancel₀ hx (hy.trans hz.symm)

/-- Stitz-Zeager Exercise 1.3.47: `x² = y²` does not represent `y` as a function of `x` (`(1,1)`, `(1,-1)`). -/
@[kb "stitzzeager2013" "Exercise 1.3.47, p. 64"]
theorem exer_1_3_47 : ¬ ∀ x : ℝ, {y : ℝ | x ^ 2 = y ^ 2}.Subsingleton := by
  exact not_fun_of (P := fun x y => x ^ 2 = y ^ 2) (1) (1) (-1) (by norm_num) (by norm_num) (by norm_num)

end UndergradKB.Precalculus.Course
