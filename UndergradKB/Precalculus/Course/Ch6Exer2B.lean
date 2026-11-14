import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 6.1 (domains, ranges) -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 6.1: domains of logarithmic functions -/

/-- Stitz-Zeager Exercise 6.1.44: the domain of `f(x) = log₇(4x+8)` is `(-2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.44, p. 441"]
theorem exer_6_1_44 : {x : ℝ | 0 < 4 * x + 8} = Ioi (-2) := by
  ext x; simp only [mem_ofPred_eq, mem_Ioi]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.1.45: the domain of `f(x) = ln(4x-20)` is `(5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.45, p. 441"]
theorem exer_6_1_45 : {x : ℝ | 0 < 4 * x - 20} = Ioi 5 := by
  ext x; simp only [mem_ofPred_eq, mem_Ioi]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.1.47: the domain of `f(x) = log((x+2)/(x²-1))` is `(-2, -1) ∪ (1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.47, p. 442"]
theorem exer_6_1_47 : {x : ℝ | 0 < (x + 2) / (x ^ 2 - 1)} = Ioo (-2) (-1) ∪ Ioi 1 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · by_cases h : x < -1
      · left; exact ⟨by linarith, h⟩
      · right; push Not at h; nlinarith
    · nlinarith
  · rintro (⟨h1, h2⟩ | h)
    · left; exact ⟨by linarith, by nlinarith⟩
    · left; exact ⟨by linarith, by nlinarith⟩

/-- Stitz-Zeager Exercise 6.1.48: the domain of `f(x) = log((x²+9x+18)/(4x-20))` is `(-6, -3) ∪ (5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.48, p. 442"]
theorem exer_6_1_48 :
    {x : ℝ | 0 < (x ^ 2 + 9 * x + 18) / (4 * x - 20)} = Ioo (-6) (-3) ∪ Ioi 5 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; linarith
    · left
      have h5 : x < 5 := by linarith
      have : (x + 3) * (x + 6) < 0 := by nlinarith
      rcases mul_neg_iff.1 this with ⟨a, b⟩ | ⟨a, b⟩
      · linarith
      · exact ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | h)
    · right; exact ⟨by nlinarith, by linarith⟩
    · left; exact ⟨by nlinarith, by linarith⟩

/-- Stitz-Zeager Exercise 6.1.50: the domain of `f(x) = ln(4x-20) + ln(x²+9x+18)` is `(5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.50, p. 442"]
theorem exer_6_1_50 : {x : ℝ | 0 < 4 * x - 20 ∧ 0 < x ^ 2 + 9 * x + 18} = Ioi 5 := by
  ext x; simp only [mem_ofPred_eq, mem_Ioi]
  constructor
  · rintro ⟨h, _⟩; linarith
  · intro h; exact ⟨by linarith, by nlinarith⟩

/-- Stitz-Zeager Exercise 6.1.51: the domain of `f(x) = log √(x²+x+1)` is all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 6.1.51, p. 442"]
theorem exer_6_1_51 : {x : ℝ | 0 < Real.sqrt (x ^ 2 + x + 1)} = univ := by
  ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]
  exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg (x + 1 / 2)])

/-- Stitz-Zeager Exercise 6.1.52: the domain of `f(x) = √(4 log₄(x))` is `[1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.52, p. 442"]
theorem exer_6_1_52 : {x : ℝ | 0 < x ∧ 0 ≤ 4 * Real.logb 4 x} = Ici 1 := by
  ext x; simp only [mem_ofPred_eq, mem_Ici]
  constructor
  · rintro ⟨hx, h⟩
    exact (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 4) hx).1 (by linarith)
  · intro h
    exact ⟨by linarith, by linarith [(Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 4) (by linarith : (0 : ℝ) < x)).2 h]⟩

/-- Stitz-Zeager Exercise 6.1.56: `f(x) = √(-1-x) / log_{1/2}(x)` has no domain: it would need `x ≤ -1` and `x > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.1.56, p. 442"]
theorem exer_6_1_56 : {x : ℝ | 0 ≤ -1 - x ∧ 0 < x ∧ Real.logb (1 / 2) x ≠ 0} = ∅ := by
  ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2, _⟩; linarith

/-! ## Section 6.1: ranges and domains of transformed exponential and logarithmic functions -/

/-- Stitz-Zeager Exercise 6.1.58: `g(x) = 2^x - 1` is defined on `ℝ` with range `(-1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.58, p. 442"]
theorem exer_6_1_58 : range (fun x : ℝ => (2 : ℝ) ^ x - 1) = Ioi (-1) := by
  ext y; simp only [mem_range, mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x; linarith
  · intro hy
    refine ⟨Real.logb 2 (y + 1), ?_⟩
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring

/-- Stitz-Zeager Exercise 6.1.59: `g(x) = (1/3)^(x-1)` is defined on `ℝ` with range `(0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.59, p. 442"]
theorem exer_6_1_59 : range (fun x : ℝ => (1 / 3 : ℝ) ^ (x - 1)) = Ioi 0 := by
  ext y; simp only [mem_range, mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩; exact Real.rpow_pos_of_pos (by norm_num) _
  · intro hy
    refine ⟨Real.logb (1 / 3) y + 1, ?_⟩
    rw [add_sub_cancel_right, Real.rpow_logb (by norm_num) (by norm_num) hy]

/-- Stitz-Zeager Exercise 6.1.60: `g(x) = 3^(-x) + 2` is defined on `ℝ` with range `(2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.60, p. 442"]
theorem exer_6_1_60 : range (fun x : ℝ => (3 : ℝ) ^ (-x) + 2) = Ioi 2 := by
  ext y; simp only [mem_range, mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-x); linarith
  · intro hy
    refine ⟨-Real.logb 3 (y - 2), ?_⟩
    rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring

/-- Stitz-Zeager Exercise 6.1.61: `g(x) = 10^((x+1)/2) - 20` is defined on `ℝ` with range `(-20, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.61, p. 442"]
theorem exer_6_1_61 : range (fun x : ℝ => (10 : ℝ) ^ ((x + 1) / 2) - 20) = Ioi (-20) := by
  ext y; simp only [mem_range, mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 10) ((x + 1) / 2); linarith
  · intro hy
    refine ⟨2 * Real.logb 10 (y + 20) - 1, ?_⟩
    rw [show (2 * Real.logb 10 (y + 20) - 1 + 1) / 2 = Real.logb 10 (y + 20) by ring,
      Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring

/-- Stitz-Zeager Exercise 6.1.62: `g(x) = 8 - e^(-x)` is defined on `ℝ` with range `(-∞, 8)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.62, p. 442"]
theorem exer_6_1_62 : range (fun x : ℝ => 8 - Real.exp (-x)) = Iio 8 := by
  ext y; simp only [mem_range, mem_Iio]
  constructor
  · rintro ⟨x, rfl⟩; linarith [Real.exp_pos (-x)]
  · intro hy
    refine ⟨-Real.log (8 - y), ?_⟩
    rw [neg_neg, Real.exp_log (by linarith)]; ring

/-- Stitz-Zeager Exercise 6.1.63: `g(x) = 10 e^(-0.1x)` is defined on `ℝ` with range `(0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.63, p. 442"]
theorem exer_6_1_63 : range (fun x : ℝ => 10 * Real.exp (-0.1 * x)) = Ioi 0 := by
  ext y; simp only [mem_range, mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩; have := Real.exp_pos (-0.1 * x); positivity
  · intro hy
    refine ⟨-10 * Real.log (y / 10), ?_⟩
    rw [show -0.1 * (-10 * Real.log (y / 10)) = Real.log (y / 10) by ring, Real.exp_log (by positivity)]
    ring

/-- Stitz-Zeager Exercise 6.1.64: `g(x) = log₂(x+1)` has domain `(-1, ∞)` and range `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 6.1.64, p. 442"]
theorem exer_6_1_64 : {x : ℝ | 0 < x + 1} = Ioi (-1) ∧
    (fun x : ℝ => Real.logb 2 (x + 1)) '' Ioi (-1) = univ := by
  refine ⟨?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ioi]; constructor <;> intro h <;> linarith
  · ext y; simp only [mem_image, mem_Ioi, mem_univ, iff_true]
    refine ⟨(2 : ℝ) ^ y - 1, ?_, ?_⟩
    · linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) y]
    · rw [sub_add_cancel, Real.logb_rpow (by norm_num) (by norm_num)]

/-- Stitz-Zeager Exercise 6.1.65: `g(x) = log_{1/3}(x) + 1` has domain `(0, ∞)` and range `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 6.1.65, p. 442"]
theorem exer_6_1_65 : {x : ℝ | 0 < x} = Ioi 0 ∧
    (fun x : ℝ => Real.logb (1 / 3) x + 1) '' Ioi 0 = univ := by
  refine ⟨rfl, ?_⟩
  ext y; simp only [mem_image, mem_Ioi, mem_univ, iff_true]
  refine ⟨(1 / 3 : ℝ) ^ (y - 1), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  rw [Real.logb_rpow (by norm_num) (by norm_num)]; ring

/-- Stitz-Zeager Exercise 6.1.66: `g(x) = -log₃(x-2)` has domain `(2, ∞)` and range `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 6.1.66, p. 442"]
theorem exer_6_1_66 : {x : ℝ | 0 < x - 2} = Ioi 2 ∧
    (fun x : ℝ => -Real.logb 3 (x - 2)) '' Ioi 2 = univ := by
  refine ⟨?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ioi]; constructor <;> intro h <;> linarith
  · ext y; simp only [mem_image, mem_Ioi, mem_univ, iff_true]
    refine ⟨(3 : ℝ) ^ (-y) + 2, ?_, ?_⟩
    · linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-y)]
    · rw [add_sub_cancel_right, Real.logb_rpow (by norm_num) (by norm_num)]; ring

/-- Stitz-Zeager Exercise 6.1.67: `g(x) = 2 log(x+20) - 1` has domain `(-20, ∞)` and range `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 6.1.67, p. 442"]
theorem exer_6_1_67 : {x : ℝ | 0 < x + 20} = Ioi (-20) ∧
    (fun x : ℝ => 2 * Real.logb 10 (x + 20) - 1) '' Ioi (-20) = univ := by
  refine ⟨?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ioi]; constructor <;> intro h <;> linarith
  · ext y; simp only [mem_image, mem_Ioi, mem_univ, iff_true]
    refine ⟨(10 : ℝ) ^ ((y + 1) / 2) - 20, ?_, ?_⟩
    · linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 10) ((y + 1) / 2)]
    · rw [sub_add_cancel, Real.logb_rpow (by norm_num) (by norm_num)]; ring

/-- Stitz-Zeager Exercise 6.1.68: `g(x) = -ln(8-x)` has domain `(-∞, 8)` and range `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 6.1.68, p. 442"]
theorem exer_6_1_68 : {x : ℝ | 0 < 8 - x} = Iio 8 ∧
    (fun x : ℝ => -Real.log (8 - x)) '' Iio 8 = univ := by
  refine ⟨?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Iio]; constructor <;> intro h <;> linarith
  · ext y; simp only [mem_image, mem_Iio, mem_univ, iff_true]
    refine ⟨8 - Real.exp (-y), ?_, ?_⟩
    · linarith [Real.exp_pos (-y)]
    · rw [sub_sub_cancel, Real.log_exp]; ring

/-- Stitz-Zeager Exercise 6.1.69: `g(x) = -10 ln(x/10)` has domain `(0, ∞)` and range `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 6.1.69, p. 442"]
theorem exer_6_1_69 : {x : ℝ | 0 < x / 10} = Ioi 0 ∧
    (fun x : ℝ => -10 * Real.log (x / 10)) '' Ioi 0 = univ := by
  refine ⟨?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ioi]; constructor <;> intro h <;> linarith
  · ext y; simp only [mem_image, mem_Ioi, mem_univ, iff_true]
    refine ⟨10 * Real.exp (-y / 10), by positivity, ?_⟩
    rw [mul_div_cancel_left₀ _ (by norm_num), Real.log_exp]; ring

/-- Stitz-Zeager Exercise 6.1.70: the functions of Exercises 6.1.64-69 are the inverses of those of Exercises
6.1.58-63, respectively (each pair of compositions is the identity on the right domains). -/
@[kb "stitzzeager2013" "Exercise 6.1.70, p. 442"]
theorem exer_6_1_70 :
    ((∀ x : ℝ, Real.logb 2 ((2 : ℝ) ^ x - 1 + 1) = x) ∧
      ∀ x : ℝ, -1 < x → (2 : ℝ) ^ (Real.logb 2 (x + 1)) - 1 = x) ∧
    ((∀ x : ℝ, Real.logb (1 / 3) ((1 / 3 : ℝ) ^ (x - 1)) + 1 = x) ∧
      ∀ x : ℝ, 0 < x → (1 / 3 : ℝ) ^ (Real.logb (1 / 3) x + 1 - 1) = x) ∧
    ((∀ x : ℝ, -Real.logb 3 ((3 : ℝ) ^ (-x) + 2 - 2) = x) ∧
      ∀ x : ℝ, 2 < x → (3 : ℝ) ^ (-(-Real.logb 3 (x - 2))) + 2 = x) ∧
    ((∀ x : ℝ, 2 * Real.logb 10 ((10 : ℝ) ^ ((x + 1) / 2) - 20 + 20) - 1 = x) ∧
      ∀ x : ℝ, -20 < x → (10 : ℝ) ^ ((2 * Real.logb 10 (x + 20) - 1 + 1) / 2) - 20 = x) ∧
    ((∀ x : ℝ, -Real.log (8 - (8 - Real.exp (-x))) = x) ∧
      ∀ x : ℝ, x < 8 → 8 - Real.exp (-(-Real.log (8 - x))) = x) ∧
    ((∀ x : ℝ, -10 * Real.log (10 * Real.exp (-0.1 * x) / 10) = x) ∧
      ∀ x : ℝ, 0 < x → 10 * Real.exp (-0.1 * (-10 * Real.log (x / 10))) = x) := by
  refine ⟨⟨fun x => ?_, fun x hx => ?_⟩, ⟨fun x => ?_, fun x hx => ?_⟩, ⟨fun x => ?_, fun x hx => ?_⟩,
    ⟨fun x => ?_, fun x hx => ?_⟩, ⟨fun x => ?_, fun x hx => ?_⟩, ⟨fun x => ?_, fun x hx => ?_⟩⟩
  · rw [sub_add_cancel, Real.logb_rpow (by norm_num) (by norm_num)]
  · rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  · rw [Real.logb_rpow (by norm_num) (by norm_num)]; ring
  · rw [add_sub_cancel_right, Real.rpow_logb (by norm_num) (by norm_num) hx]
  · rw [add_sub_cancel_right, Real.logb_rpow (by norm_num) (by norm_num)]; ring
  · rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  · rw [sub_add_cancel, Real.logb_rpow (by norm_num) (by norm_num)]; ring
  · rw [show (2 * Real.logb 10 (x + 20) - 1 + 1) / 2 = Real.logb 10 (x + 20) by ring,
      Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  · rw [sub_sub_cancel, Real.log_exp]; ring
  · rw [neg_neg, Real.exp_log (by linarith)]; ring
  · rw [mul_div_cancel_left₀ _ (by norm_num), Real.log_exp]; ring
  · rw [show -0.1 * (-10 * Real.log (x / 10)) = Real.log (x / 10) by ring, Real.exp_log (by positivity)]
    ring

/-! ## Section 6.1: inverses -/

/-- Stitz-Zeager Exercise 6.1.71: `f(x) = 3^(x+2) - 4` has inverse `f⁻¹(x) = log₃(x+4) - 2` (for `x > -4`). -/
@[kb "stitzzeager2013" "Exercise 6.1.71, p. 442"]
theorem exer_6_1_71 :
    (∀ x : ℝ, Real.logb 3 ((3 : ℝ) ^ (x + 2) - 4 + 4) - 2 = x) ∧
    ∀ y : ℝ, -4 < y → (3 : ℝ) ^ (Real.logb 3 (y + 4) - 2 + 2) - 4 = y := by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · rw [sub_add_cancel, Real.logb_rpow (by norm_num) (by norm_num)]; ring
  · rw [sub_add_cancel, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring

/-- Stitz-Zeager Exercise 6.1.72: `f(x) = log₄(x-1)` (for `x > 1`) has inverse `f⁻¹(x) = 4^x + 1`. -/
@[kb "stitzzeager2013" "Exercise 6.1.72, p. 442"]
theorem exer_6_1_72 :
    (∀ x : ℝ, 1 < x → (4 : ℝ) ^ (Real.logb 4 (x - 1)) + 1 = x) ∧
    ∀ y : ℝ, Real.logb 4 ((4 : ℝ) ^ y + 1 - 1) = y := by
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  · rw [add_sub_cancel_right, Real.logb_rpow (by norm_num) (by norm_num)]

/-- Stitz-Zeager Exercise 6.1.73: `f(x) = -2^(-x) + 1` has inverse `f⁻¹(x) = -log₂(1-x)` (for `x < 1`). -/
@[kb "stitzzeager2013" "Exercise 6.1.73, p. 442"]
theorem exer_6_1_73 :
    (∀ x : ℝ, -Real.logb 2 (1 - (-(2 : ℝ) ^ (-x) + 1)) = x) ∧
    ∀ y : ℝ, y < 1 → -(2 : ℝ) ^ (-(-Real.logb 2 (1 - y))) + 1 = y := by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · rw [show 1 - (-(2 : ℝ) ^ (-x) + 1) = (2 : ℝ) ^ (-x) by ring,
      Real.logb_rpow (by norm_num) (by norm_num)]; ring
  · rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring

/-- Stitz-Zeager Exercise 6.1.74: `f(x) = 5 log(x) - 2` (for `x > 0`) has inverse `f⁻¹(x) = 10^((x+2)/5)`. -/
@[kb "stitzzeager2013" "Exercise 6.1.74, p. 442"]
theorem exer_6_1_74 :
    (∀ x : ℝ, 0 < x → (10 : ℝ) ^ ((5 * Real.logb 10 x - 2 + 2) / 5) = x) ∧
    ∀ y : ℝ, 5 * Real.logb 10 ((10 : ℝ) ^ ((y + 2) / 5)) - 2 = y := by
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · rw [show (5 * Real.logb 10 x - 2 + 2) / 5 = Real.logb 10 x by ring,
      Real.rpow_logb (by norm_num) (by norm_num) hx]
  · rw [Real.logb_rpow (by norm_num) (by norm_num)]; ring

end UndergradKB.Precalculus.Course
