import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Plane

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 1.1-1.2 -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

/-! ## Section 1.1 -/

/-- Stitz-Zeager Exercise 1.1.1: the chart of set-builder descriptions and interval notation. -/
@[kb "stitzzeager2013" "Exercise 1.1.1, p. 26"]
theorem exer_1_1_1 :
    {x : ℝ | -1 ≤ x ∧ x < 5} = Ico (-1) 5 ∧ {x : ℝ | 0 ≤ x ∧ x < 3} = Ico 0 3 ∧
    {x : ℝ | 2 < x ∧ x ≤ 7} = Ioc 2 7 ∧ {x : ℝ | -5 < x ∧ x ≤ 0} = Ioc (-5) 0 ∧
    {x : ℝ | -3 < x ∧ x < 3} = Ioo (-3) 3 ∧ {x : ℝ | 5 ≤ x ∧ x ≤ 7} = Icc 5 7 ∧
    {x : ℝ | x ≤ 3} = Iic 3 ∧ {x : ℝ | x < 9} = Iio 9 ∧ {x : ℝ | 4 < x} = Ioi 4 ∧
    {x : ℝ | -3 ≤ x} = Ici (-3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext x <;> simp

/-- Stitz-Zeager Exercise 1.1.6: `(-∞,0) ∪ [1,5]` is already in simplest form (as a set). -/
@[kb "stitzzeager2013" "Exercise 1.1.6, p. 26"]
theorem exer_1_1_6 : Iio (0 : ℝ) ∪ Icc 1 5 = {x : ℝ | x < 0 ∨ (1 ≤ x ∧ x ≤ 5)} := by
  ext x; simp

/-- Stitz-Zeager Exercise 1.1.8: `{x | x ≠ 5}` is `(-∞,5) ∪ (5,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.8, p. 26"]
theorem exer_1_1_8 : {x : ℝ | x ≠ 5} = Iio 5 ∪ Ioi 5 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.1.9: `{x | x ≠ -1}` is `(-∞,-1) ∪ (-1,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.9, p. 26"]
theorem exer_1_1_9 : {x : ℝ | x ≠ -1} = Iio (-1) ∪ Ioi (-1) := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.1.11: `{x | x ≠ 0, 2}` is three intervals. -/
@[kb "stitzzeager2013" "Exercise 1.1.11, p. 27"]
theorem exer_1_1_11 : {x : ℝ | x ≠ 0 ∧ x ≠ 2} = Iio 0 ∪ Ioo 0 2 ∪ Ioi 2 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.1.12: `{x | x ≠ ±2}` is three intervals. -/
@[kb "stitzzeager2013" "Exercise 1.1.12, p. 27"]
theorem exer_1_1_12 : {x : ℝ | x ≠ 2 ∧ x ≠ -2} = Iio (-2) ∪ Ioo (-2) 2 ∪ Ioi 2 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.1.16: `{x | x ≤ -3 or x > 0}` is `(-∞,-3] ∪ (0,∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.16, p. 27"]
theorem exer_1_1_16 : {x : ℝ | x ≤ -3 ∨ 0 < x} = Iic (-3) ∪ Ioi 0 := by
  ext x; simp

/-- Stitz-Zeager Exercise 1.1.21: quadrant and the three mirror images of the points of Exercise 20. -/
@[kb "stitzzeager2013" "Exercise 1.1.21, p. 27"]
theorem exer_1_1_21 :
    ((-3 < 0 ∧ (-7 : ℝ) < 0) ∧ PtSymmX (-3, -7) (-3, 7) ∧ PtSymmY (-3, -7) (3, -7) ∧
      PtSymmO (-3, -7) (3, 7)) ∧
    ((0 < (1.3 : ℝ) ∧ (-2 : ℝ) < 0) ∧ PtSymmX (1.3, -2) (1.3, 2) ∧ PtSymmY (1.3, -2) (-1.3, -2) ∧
      PtSymmO (1.3, -2) (-1.3, 2)) ∧
    ((0 < Real.pi ∧ 0 < √10) ∧ PtSymmX (Real.pi, √10) (Real.pi, -√10) ∧
      PtSymmY (Real.pi, √10) (-Real.pi, √10) ∧ PtSymmO (Real.pi, √10) (-Real.pi, -√10)) ∧
    ((0 : ℝ) = 0 ∧ (0 : ℝ) < 8 ∧ PtSymmX (0, 8) (0, -8) ∧ PtSymmY (0, 8) (0, 8) ∧
      PtSymmO (0, 8) (0, -8)) ∧
    ((-5.5 : ℝ) < 0 ∧ PtSymmX (-5.5, 0) (-5.5, 0) ∧ PtSymmY (-5.5, 0) (5.5, 0) ∧
      PtSymmO (-5.5, 0) (5.5, 0)) ∧
    ((-8 < 0 ∧ (0 : ℝ) < 4) ∧ PtSymmX (-8, 4) (-8, -4) ∧ PtSymmY (-8, 4) (8, 4) ∧
      PtSymmO (-8, 4) (8, -4)) ∧
    ((0 < (9.2 : ℝ) ∧ (-7.8 : ℝ) < 0) ∧ PtSymmX (9.2, -7.8) (9.2, 7.8) ∧
      PtSymmY (9.2, -7.8) (-9.2, -7.8) ∧ PtSymmO (9.2, -7.8) (-9.2, 7.8)) ∧
    ((0 < (7 : ℝ) ∧ (0 : ℝ) < 5) ∧ PtSymmX (7, 5) (7, -5) ∧ PtSymmY (7, 5) (-7, 5) ∧
      PtSymmO (7, 5) (-7, -5)) := by
  simp only [PtSymmX, PtSymmY, PtSymmO]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · refine ⟨⟨Real.pi_pos, by positivity⟩, ?_⟩; simp
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- Stitz-Zeager Exercise 1.1.24: for `(1/2,4)` and `(3/2,-1)` the distance is `√26` and the midpoint
`(1, 3/2)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.24, p. 28"]
theorem exer_1_1_24 :
    Real.sqrt ((1 / 2 - 3 / 2) ^ 2 + (4 - (-1)) ^ 2 : ℝ) = Real.sqrt 26 ∧
      (((1 / 2 : ℝ) + 3 / 2) / 2, ((4 : ℝ) + (-1)) / 2) = (1, 3 / 2) := by
  refine ⟨?_, by norm_num⟩
  congr 1; norm_num

/-- Stitz-Zeager Exercise 1.1.28: for `(2√45, √12)` and `(√20, √27)` the distance is `√83` and the midpoint
`(4√5, 5√3/2)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.28, p. 28"]
theorem exer_1_1_28 :
    Real.sqrt ((2 * √45 - √20) ^ 2 + (√12 - √27) ^ 2) = √83 ∧
      ((2 * √45 + √20) / 2, (√12 + √27) / 2) = (4 * √5, 5 * √3 / 2) := by
  have h45 : √45 = 3 * √5 := by
    rw [show (45 : ℝ) = 3 ^ 2 * 5 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h20 : √20 = 2 * √5 := by
    rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h27 : √27 = 3 * √3 := by
    rw [show (27 : ℝ) = 3 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [h45, h20, h12, h27]
  refine ⟨?_, by ext <;> simp <;> ring⟩
  congr 1; nlinarith

/-- Stitz-Zeager Exercise 1.1.29: the distance from the origin to `(x,y)` is `√(x²+y²)` and the midpoint is
`(x/2, y/2)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.29, p. 28"]
theorem exer_1_1_29 (x y : ℝ) :
    Real.sqrt ((0 - x) ^ 2 + (0 - y) ^ 2) = Real.sqrt (x ^ 2 + y ^ 2) ∧
      (((0 : ℝ) + x) / 2, ((0 : ℝ) + y) / 2) = (x / 2, y / 2) := by
  simp

/-- Stitz-Zeager Exercise 1.1.32: the points `(x,0)` at distance `2` from `(-1,1)` are `(-1 ± √3, 0)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.32, p. 28"]
theorem exer_1_1_32 (x : ℝ) :
    Real.sqrt ((x - (-1)) ^ 2 + (0 - 1) ^ 2) = 2 ↔ x = -1 + √3 ∨ x = -1 - √3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]
  constructor
  · intro h
    have : (x + 1 - √3) * (x + 1 + √3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> nlinarith

/-- Stitz-Zeager Exercise 1.1.34: Sasquatch, 3 miles west and 4 south of the origin, is at `(-3,-4)`, `5`
miles away; after running 7 miles east he is at `(4,-4)`. -/
@[kb "stitzzeager2013" "Exercise 1.1.34, p. 28"]
theorem exer_1_1_34 :
    Real.sqrt (((-3 : ℝ) - 0) ^ 2 + ((-4 : ℝ) - 0) ^ 2) = 5 ∧ ((-3 : ℝ) + 7, (-4 : ℝ)) = (4, -4) := by
  refine ⟨?_, by norm_num⟩
  rw [show (((-3 : ℝ) - 0) ^ 2 + ((-4 : ℝ) - 0) ^ 2) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Stitz-Zeager Exercise 1.1.35: the distance formula for vertical points, horizontal points and equal points. -/
@[kb "stitzzeager2013" "Exercise 1.1.35, p. 28"]
theorem exer_1_1_35 (a y₀ y₁ x₀ x₁ b : ℝ) :
    Real.sqrt ((a - a) ^ 2 + (y₁ - y₀) ^ 2) = |y₁ - y₀| ∧
    Real.sqrt ((x₁ - x₀) ^ 2 + (b - b) ^ 2) = |x₁ - x₀| ∧
    Real.sqrt ((x₀ - x₀) ^ 2 + (y₀ - y₀) ^ 2) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Real.sqrt_sq_eq_abs]

/-- Stitz-Zeager Exercise 1.1.36: the midpoint of `P` and `Q` is at distance half of `|PQ|` from each. -/
@[kb "stitzzeager2013" "Exercise 1.1.36, p. 28"]
theorem exer_1_1_36 (x₁ y₁ x₂ y₂ : ℝ) :
    Real.sqrt ((x₁ - (x₁ + x₂) / 2) ^ 2 + (y₁ - (y₁ + y₂) / 2) ^ 2) =
        Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) / 2 ∧
      Real.sqrt (((x₁ + x₂) / 2 - x₂) ^ 2 + ((y₁ + y₂) / 2 - y₂) ^ 2) =
        Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) / 2 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  constructor
  · rw [show (x₁ - (x₁ + x₂) / 2) ^ 2 + (y₁ - (y₁ + y₂) / 2) ^ 2 =
        ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) / 4 by ring, Real.sqrt_div' _ (by norm_num), h4]
  · rw [show ((x₁ + x₂) / 2 - x₂) ^ 2 + ((y₁ + y₂) / 2 - y₂) ^ 2 =
        ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) / 4 by ring, Real.sqrt_div' _ (by norm_num), h4]

/-! ## Section 1.2 -/

/-- Stitz-Zeager Exercise 1.2.46: `y = 2√(x+4) - 2` has x-intercept `-3`, y-intercept `2` and no symmetry. -/
@[kb "stitzzeager2013" "Exercise 1.2.46, p. 44"]
theorem exer_1_2_46 (S : Set (ℝ × ℝ)) (hS : S = {p | -4 ≤ p.1 ∧ p.2 = 2 * √(p.1 + 4) - 2}) :
    {x : ℝ | (x, 0) ∈ S} = {-3} ∧ {y : ℝ | (0, y) ∈ S} = {2} ∧
      ¬ SymmetricX S ∧ ¬ SymmetricY S ∧ ¬ SymmetricO S := by
  subst hS
  have h1 : √((-4 : ℝ) + 4) = 0 := by norm_num
  have h4 : √((0 : ℝ) + 4) = 2 := by
    rw [show ((0 : ℝ) + 4) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hx, h0⟩
      have h2 : √(x + 4) = 1 := by linarith
      have := Real.sqrt_eq_iff_mul_self_eq (by linarith) (by norm_num) |>.mp h2
      linarith
    · rintro rfl
      refine ⟨by norm_num, ?_⟩
      rw [show ((-3 : ℝ) + 4) = 1 by norm_num]; simp
  · ext y
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨-, h0⟩; rw [h4] at h0; linarith
    · rintro rfl; refine ⟨by norm_num, ?_⟩; rw [h4]; norm_num
  · have := h (-4, -2) (by simp only [mem_ofPred_eq]; rw [h1]; norm_num)
    simp only [mem_ofPred_eq] at this; rw [h1] at this; norm_num at this
  · have := h (-4, -2) (by simp only [mem_ofPred_eq]; rw [h1]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < 8 by norm_num)
    linarith
  · have := h (-4, -2) (by simp only [mem_ofPred_eq]; rw [h1]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
    have h8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    have : √8 = 2 := by linarith
    nlinarith

/-- Stitz-Zeager Exercise 1.2.49: the circle `(x+2)² + y² = 16` has x-intercepts `-6` and `2`, y-intercepts
`(0, ±2√3)`, is symmetric about the x-axis and about neither the y-axis nor the origin. -/
@[kb "stitzzeager2013" "Exercise 1.2.49, p. 45"]
theorem exer_1_2_49 (S : Set (ℝ × ℝ)) (hS : S = {p | (p.1 + 2) ^ 2 + p.2 ^ 2 = 16}) :
    {x : ℝ | (x, 0) ∈ S} = {-6, 2} ∧ {y : ℝ | (0, y) ∈ S} = {2 * √3, -(2 * √3)} ∧
      SymmetricX S ∧ ¬ SymmetricY S ∧ ¬ SymmetricO S := by
  subst hS
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, fun p hp => ?_, fun h => ?_, fun h => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : (x + 6) * (x - 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · ext y
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro h
      have : (y - 2 * √3) * (y + 2 * √3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> nlinarith
  · simp only [mem_ofPred_eq] at hp ⊢; simpa using hp
  · have := h (-6, 0) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this
  · have := h (-6, 0) (by simp only [mem_ofPred_eq]; norm_num)
    simp only [mem_ofPred_eq] at this; norm_num at this

end UndergradKB.Precalculus.Course
