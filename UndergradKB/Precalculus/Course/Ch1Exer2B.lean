import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Radicals

/-! # Course layer, Chapter 1 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 1.3-1.4 -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

/-! ## Section 1.3 -/

/-- Stitz-Zeager Exercise 1.3.5: the relation of pairs (odd integer, even integer) is not a function. -/
@[kb "stitzzeager2013" "Exercise 1.3.5, p. 61"]
theorem exer_1_3_5 (R : Set (ℤ × ℤ)) (hR : R = {p | Odd p.1 ∧ Even p.2}) :
    ¬ ∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2 := by
  subst hR
  intro h
  have := h (1, 0) ⟨odd_one, by decide⟩ (1, 2) ⟨odd_one, by decide⟩ rfl
  simp at this

/-- Stitz-Zeager Exercise 1.3.7: `{(2ⁿ, n)}` is a function with domain the powers of two and range all naturals. -/
@[kb "stitzzeager2013" "Exercise 1.3.7, p. 61"]
theorem exer_1_3_7 (R : Set (ℕ × ℕ)) (hR : R = Set.range (fun n : ℕ => (2 ^ n, n))) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧ Prod.fst '' R = {x | ∃ n : ℕ, x = 2 ^ n} ∧
      Prod.snd '' R = univ := by
  subst hR
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ h
    exact Nat.pow_right_injective (le_refl 2) h
  · ext x; simp [eq_comm]
  · ext y; simp

/-- Stitz-Zeager Exercise 1.3.8: `{(n, n²) | n ∈ ℤ}` is a function with domain all integers and range the perfect squares. -/
@[kb "stitzzeager2013" "Exercise 1.3.8, p. 61"]
theorem exer_1_3_8 (R : Set (ℤ × ℤ)) (hR : R = Set.range (fun n : ℤ => (n, n ^ 2))) :
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧ Prod.fst '' R = univ ∧
      Prod.snd '' R = {y | ∃ n : ℤ, y = n ^ 2} := by
  subst hR
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ h
    simp only at h; rw [h]
  · ext x; simp
  · ext y; simp [eq_comm]

/-- Stitz-Zeager Exercise 1.3.34: `y = √(x - 2)` represents `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.34, p. 64"]
theorem exer_1_3_34 : ∀ x : ℝ, {y : ℝ | y = √(x - 2)}.Subsingleton := by
  intro x y hy z hz
  rw [mem_ofPred_eq] at hy hz
  rw [hy, hz]

/-- Stitz-Zeager Exercise 1.3.37: `y = x / (x² - 9)` represents `y` as a function of `x` (for `x ≠ ±3`). -/
@[kb "stitzzeager2013" "Exercise 1.3.37, p. 64"]
theorem exer_1_3_37 : ∀ x : ℝ, x ^ 2 - 9 ≠ 0 → {y : ℝ | y * (x ^ 2 - 9) = x}.Subsingleton := by
  intro x hx y hy z hz
  rw [mem_ofPred_eq] at hy hz
  exact mul_right_cancel₀ hx (hy.trans hz.symm)

/-- Stitz-Zeager Exercise 1.3.40: `y = x² + 4` represents `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.40, p. 64"]
theorem exer_1_3_40 : ∀ x : ℝ, {y : ℝ | y = x ^ 2 + 4}.Subsingleton := by
  intro x y hy z hz
  rw [mem_ofPred_eq] at hy hz
  rw [hy, hz]

/-- Stitz-Zeager Exercise 1.3.45: `2x + 3y = 4` represents `y` as a function of `x`. -/
@[kb "stitzzeager2013" "Exercise 1.3.45, p. 64"]
theorem exer_1_3_45 : ∀ x : ℝ, {y : ℝ | 2 * x + 3 * y = 4}.Subsingleton := by
  intro x y hy z hz
  rw [mem_ofPred_eq] at hy hz
  linarith

/-! ## Section 1.4 -/

/-- Stitz-Zeager Exercise 1.4.1: multiply by `2`, add `3`, divide by `4` gives `f(x) = (2x+3)/4` on all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 1.4.1, p. 75"]
theorem exer_1_4_1 (f : ℝ → ℝ)
    (hf : f = (fun u => u / 4) ∘ (fun u => u + 3) ∘ (fun u => 2 * u)) :
    ∀ x, f x = (2 * x + 3) / 4 := by
  subst hf; intro x; simp [Function.comp]

/-- Stitz-Zeager Exercise 1.4.2: add `3`, multiply by `2`, divide by `4` gives `f(x) = (x+3)/2` on all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 1.4.2, p. 75"]
theorem exer_1_4_2 (f : ℝ → ℝ)
    (hf : f = (fun u => u / 4) ∘ (fun u => 2 * u) ∘ (fun u => u + 3)) :
    ∀ x, f x = 2 * (x + 3) / 4 ∧ f x = (x + 3) / 2 := by
  subst hf; intro x; simp only [Function.comp_apply]; constructor <;> first | trivial | ring

/-- Stitz-Zeager Exercise 1.4.3: divide by `4`, add `3`, multiply by `2` gives `f(x) = x/2 + 6` on all of `ℝ`. -/
@[kb "stitzzeager2013" "Exercise 1.4.3, p. 75"]
theorem exer_1_4_3 (f : ℝ → ℝ)
    (hf : f = (fun u => 2 * u) ∘ (fun u => u + 3) ∘ (fun u => u / 4)) :
    ∀ x, f x = 2 * (x / 4 + 3) ∧ f x = x / 2 + 6 := by
  subst hf; intro x; simp only [Function.comp_apply]; constructor <;> first | trivial | ring

/-- Stitz-Zeager Exercise 1.4.5: add `3`, multiply by `2`, take the square root gives `√(2x+6)`, defined exactly on
`[-3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.5, p. 75"]
theorem exer_1_4_5 (f : ℝ → ℝ)
    (hf : f = (fun u => √u) ∘ (fun u => 2 * u) ∘ (fun u => u + 3)) :
    (∀ x, f x = √(2 * x + 6)) ∧ {x : ℝ | 0 ≤ 2 * (x + 3)} = Ici (-3) := by
  subst hf
  refine ⟨fun x => ?_, ?_⟩
  · simp only [Function.comp]; congr 1; ring
  · ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.6: add `3`, take the square root, multiply by `2` gives `2√(x+3)`, defined exactly on
`[-3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.6, p. 75"]
theorem exer_1_4_6 (f : ℝ → ℝ)
    (hf : f = (fun u => 2 * u) ∘ (fun u => √u) ∘ (fun u => u + 3)) :
    (∀ x, f x = 2 * √(x + 3)) ∧ {x : ℝ | 0 ≤ x + 3} = Ici (-3) := by
  subst hf
  refine ⟨fun x => rfl, ?_⟩
  ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.10: reciprocal times `4`, square root, subtract `13` gives `√(4/x) - 13 = 2/√x - 13`,
defined exactly for `x > 0`. -/
@[kb "stitzzeager2013" "Exercise 1.4.10, p. 75"]
theorem exer_1_4_10 (f : ℝ → ℝ)
    (hf : f = (fun u => u - 13) ∘ (fun u => √u) ∘ (fun u => 4 / u)) :
    {x : ℝ | x ≠ 0 ∧ 0 ≤ 4 / x} = Ioi 0 ∧ ∀ x, 0 < x → f x = 2 / √x - 13 := by
  subst hf
  refine ⟨?_, fun x hx => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨h0, h⟩
      rcases lt_or_gt_of_ne h0 with h1 | h1
      · have : 4 / x < 0 := div_neg_of_pos_of_neg (by norm_num) h1
        linarith
      · exact h1
    · intro h; exact ⟨h.ne', by positivity⟩
  · have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    simp only [Function.comp]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4), h4]

/-- Stitz-Zeager Exercise 1.4.18: for `f(x) = 0` all the requested values are `0` (and `f(x) - 4 = -4`). -/
@[kb "stitzzeager2013" "Exercise 1.4.18, p. 76"]
theorem exer_1_4_18 (f : ℝ → ℝ) (hf : ∀ x, f x = 0) :
    f 3 = 0 ∧ f (-1) = 0 ∧ f (3 / 2) = 0 ∧ (∀ x, f (4 * x) = 0) ∧ (∀ x, 4 * f x = 0) ∧
      (∀ x, f (-x) = 0) ∧ (∀ x, f (x - 4) = 0) ∧ (∀ x, f x - 4 = -4) ∧ (∀ x, f (x ^ 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hf] <;> first | (intro x; norm_num) | norm_num

/-- Stitz-Zeager Exercise 1.4.20: for `f(x) = 5 - 2x` the requested values with a symbolic argument. -/
@[kb "stitzzeager2013" "Exercise 1.4.20, p. 76"]
theorem exer_1_4_20 (f : ℝ → ℝ) (hf : ∀ x, f x = 5 - 2 * x) (a k : ℝ) (ha : a ≠ 0) :
    f 2 = 1 ∧ f (-2) = 9 ∧ f (2 * a) = 5 - 4 * a ∧ 2 * f a = 10 - 4 * a ∧ f (a + 2) = 1 - 2 * a ∧
      f a + f 2 = 6 - 2 * a ∧ f (2 / a) = (5 * a - 4) / a ∧ f a / 2 = (5 - 2 * a) / 2 ∧
      f (a + k) = 5 - 2 * a - 2 * k := by
  simp only [hf]
  refine ⟨by norm_num, by norm_num, by ring, by ring, by ring, by ring, ?_, trivial, by ring⟩
  field_simp
  ring

/-- Stitz-Zeager Exercise 1.4.21: for `f(x) = 2x² - 1` the requested values with a symbolic argument. -/
@[kb "stitzzeager2013" "Exercise 1.4.21, p. 76"]
theorem exer_1_4_21 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x ^ 2 - 1) (a k : ℝ) (ha : a ≠ 0) :
    f 2 = 7 ∧ f (-2) = 7 ∧ f (2 * a) = 8 * a ^ 2 - 1 ∧ 2 * f a = 4 * a ^ 2 - 2 ∧
      f (a + 2) = 2 * a ^ 2 + 8 * a + 7 ∧ f a + f 2 = 2 * a ^ 2 + 6 ∧ f (2 / a) = (8 - a ^ 2) / a ^ 2 ∧
      f a / 2 = (2 * a ^ 2 - 1) / 2 ∧ f (a + k) = 2 * a ^ 2 + 4 * a * k + 2 * k ^ 2 - 1 := by
  simp only [hf]
  refine ⟨by norm_num, by norm_num, by ring, by ring, by ring, by ring, ?_, trivial, by ring⟩
  field_simp
  ring

/-- Stitz-Zeager Exercise 1.4.24: the constant function `f(x) = 117`. -/
@[kb "stitzzeager2013" "Exercise 1.4.24, p. 76"]
theorem exer_1_4_24 (f : ℝ → ℝ) (hf : ∀ x, f x = 117) (a k : ℝ) :
    f 2 = 117 ∧ f (-2) = 117 ∧ f (2 * a) = 117 ∧ 2 * f a = 234 ∧ f (a + 2) = 117 ∧ f a + f 2 = 234 ∧
      f (2 / a) = 117 ∧ f a / 2 = 117 / 2 ∧ f (a + k) = 117 := by
  simp only [hf]; norm_num

/-- Stitz-Zeager Exercise 1.4.25: for `f(x) = x/2` the requested values with a symbolic argument. -/
@[kb "stitzzeager2013" "Exercise 1.4.25, p. 76"]
theorem exer_1_4_25 (f : ℝ → ℝ) (hf : ∀ x, f x = x / 2) (a k : ℝ) (ha : a ≠ 0) :
    f 2 = 1 ∧ f (-2) = -1 ∧ f (2 * a) = a ∧ 2 * f a = a ∧ f (a + 2) = (a + 2) / 2 ∧
      f a + f 2 = (a + 2) / 2 ∧ f (2 / a) = 1 / a ∧ f a / 2 = a / 4 ∧ f (a + k) = (a + k) / 2 := by
  simp only [hf]
  refine ⟨by norm_num, by norm_num, by ring, by ring, trivial, by ring, ?_, by ring, trivial⟩
  field_simp

/-- Stitz-Zeager Exercise 1.4.27: for `f(x) = 2x - 1`, `f(0) = -1` and `f(x) = 0` exactly at `x = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.27, p. 76"]
theorem exer_1_4_27 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x - 1) :
    f 0 = -1 ∧ ∀ x, f x = 0 ↔ x = 1 / 2 := by
  refine ⟨by simp [hf], fun x => ?_⟩
  rw [hf]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.28: for `f(x) = 3 - (2/5)x`, `f(0) = 3` and `f(x) = 0` exactly at `x = 15/2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.28, p. 76"]
theorem exer_1_4_28 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 - 2 / 5 * x) :
    f 0 = 3 ∧ ∀ x, f x = 0 ↔ x = 15 / 2 := by
  refine ⟨by simp [hf], fun x => ?_⟩
  rw [hf]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.31: for `f(x) = √(x+4)`, `f(0) = 2` and, on the domain `x ≥ -4`, `f(x) = 0` exactly
at `x = -4`. -/
@[kb "stitzzeager2013" "Exercise 1.4.31, p. 76"]
theorem exer_1_4_31 (f : ℝ → ℝ) (hf : ∀ x, f x = √(x + 4)) :
    f 0 = 2 ∧ ∀ x, 0 ≤ x + 4 → (f x = 0 ↔ x = -4) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hf, show ((0 : ℝ) + 4) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  · rw [hf, Real.sqrt_eq_zero hx]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.39: `(x - 2)/(x + 1)` is defined exactly off `x = -1`. -/
@[kb "stitzzeager2013" "Exercise 1.4.39, p. 77"]
theorem exer_1_4_39 : {x : ℝ | x + 1 ≠ 0} = Iio (-1) ∪ Ioi (-1) := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.4.41: `2x/(x² + 3)` is defined for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 1.4.41, p. 77"]
theorem exer_1_4_41 : {x : ℝ | x ^ 2 + 3 ≠ 0} = univ := by
  ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]; positivity

/-- Stitz-Zeager Exercise 1.4.42: `2x/(x² - 3)` is defined exactly off `x = ±√3`. -/
@[kb "stitzzeager2013" "Exercise 1.4.42, p. 77"]
theorem exer_1_4_42 :
    {x : ℝ | x ^ 2 - 3 ≠ 0} = Iio (-√3) ∪ Ioo (-√3) (√3) ∪ Ioi (√3) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  have key : x ^ 2 - 3 = (x - √3) * (x + √3) := by linear_combination h3
  rw [key]
  constructor
  · intro h
    have h1 : x - √3 ≠ 0 := left_ne_zero_of_mul h
    have h2 : x + √3 ≠ 0 := right_ne_zero_of_mul h
    grind
  · intro h
    apply mul_ne_zero <;> intro hh <;> grind

/-- Stitz-Zeager Exercise 1.4.44: `(x - 2)/(x - 2)` is defined exactly off `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.44, p. 77"]
theorem exer_1_4_44 : {x : ℝ | x - 2 ≠ 0} = Iio 2 ∪ Ioi 2 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.4.45: `√(3 - x)` is defined exactly on `(-∞, 3]`. -/
@[kb "stitzzeager2013" "Exercise 1.4.45, p. 77"]
theorem exer_1_4_45 : {x : ℝ | 0 ≤ 3 - x} = Iic 3 := by
  ext x; simp only [mem_ofPred_eq, mem_Iic]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.47: `9x√(x + 3)` is defined exactly on `[-3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.47, p. 77"]
theorem exer_1_4_47 : {x : ℝ | 0 ≤ x + 3} = Ici (-3) := by
  ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.48: `√(7 - x)/(x² + 1)` is defined exactly on `(-∞, 7]`. -/
@[kb "stitzzeager2013" "Exercise 1.4.48, p. 77"]
theorem exer_1_4_48 : {x : ℝ | 0 ≤ 7 - x ∧ x ^ 2 + 1 ≠ 0} = Iic 7 := by
  ext x; simp only [mem_ofPred_eq, mem_Iic]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; exact ⟨by linarith, by positivity⟩

/-- Stitz-Zeager Exercise 1.4.49: `√(6x - 2)` is defined exactly on `[1/3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.49, p. 77"]
theorem exer_1_4_49 : {x : ℝ | 0 ≤ 6 * x - 2} = Ici (1 / 3) := by
  ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 1.4.50: `6/√(6x - 2)` is defined exactly on `(1/3, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.50, p. 77"]
theorem exer_1_4_50 : {x : ℝ | 0 ≤ 6 * x - 2 ∧ √(6 * x - 2) ≠ 0} = Ioi (1 / 3) := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioi, ne_eq, Real.sqrt_eq_zero']
  constructor
  · rintro ⟨h0, h⟩; linarith
  · intro h; constructor <;> linarith

/-- Stitz-Zeager Exercise 1.4.51: the cube root `∛(6x - 2)` is defined for every real `x` (it is the unique real
`r` with `r³ = 6x - 2`). -/
@[kb "stitzzeager2013" "Exercise 1.4.51, p. 77"]
theorem exer_1_4_51 :
    ∀ x : ℝ, ∃! r : ℝ, r = principalRoot 3 (6 * x - 2) ∧ r ^ 3 = 6 * x - 2 := by
  intro x
  refine ⟨principalRoot 3 (6 * x - 2), ⟨rfl, principalRoot_pow (by norm_num) (Or.inl (by decide))⟩, ?_⟩
  rintro r ⟨h, -⟩; exact h

/-- Stitz-Zeager Exercise 1.4.53: `√(6x - 2)/(x² - 36)` is defined exactly on `[1/3, 6) ∪ (6, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.53, p. 77"]
theorem exer_1_4_53 : {x : ℝ | 0 ≤ 6 * x - 2 ∧ x ^ 2 - 36 ≠ 0} = Ico (1 / 3) 6 ∪ Ioi 6 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ico, mem_Ioi]
  constructor
  · rintro ⟨h0, h⟩
    have h6 : x ≠ 6 := fun e => h (by rw [e]; norm_num)
    rcases lt_or_gt_of_ne h6 with h1 | h1
    · exact Or.inl ⟨by linarith, h1⟩
    · exact Or.inr h1
  · rintro (⟨h0, h1⟩ | h1)
    · exact ⟨by linarith, fun e => by nlinarith⟩
    · exact ⟨by linarith, fun e => by nlinarith⟩

/-- Stitz-Zeager Exercise 1.4.54: `∛(6x - 2)/(x² + 36)` is defined for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 1.4.54, p. 77"]
theorem exer_1_4_54 :
    {x : ℝ | x ^ 2 + 36 ≠ 0} = univ ∧
      ∀ x : ℝ, principalRoot 3 (6 * x - 2) ^ 3 = 6 * x - 2 := by
  refine ⟨?_, fun x => principalRoot_pow (by norm_num) (Or.inl (by decide))⟩
  ext x; simp only [mem_ofPred_eq, mem_univ, iff_true]; positivity

/-- Stitz-Zeager Exercise 1.4.55: `t/(t - 8)` is defined exactly off `t = 8`. -/
@[kb "stitzzeager2013" "Exercise 1.4.55, p. 77"]
theorem exer_1_4_55 : {t : ℝ | t - 8 ≠ 0} = Iio 8 ∪ Ioi 8 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.4.56: `√r/(r - 8)` is defined exactly on `[0, 8) ∪ (8, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.56, p. 77"]
theorem exer_1_4_56 : {r : ℝ | 0 ≤ r ∧ r - 8 ≠ 0} = Ico 0 8 ∪ Ioi 8 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Ico, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.4.57: `θ/√(θ - 8)` is defined exactly on `(8, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.57, p. 77"]
theorem exer_1_4_57 : {θ : ℝ | 0 ≤ θ - 8 ∧ √(θ - 8) ≠ 0} = Ioi 8 := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioi, ne_eq, Real.sqrt_eq_zero']
  constructor
  · rintro ⟨h0, h⟩; linarith
  · intro h; constructor <;> linarith

/-- Stitz-Zeager Exercise 1.4.59: `∛(y/(y - 8))` is defined exactly off `y = 8`. -/
@[kb "stitzzeager2013" "Exercise 1.4.59, p. 77"]
theorem exer_1_4_59 :
    {y : ℝ | y - 8 ≠ 0} = Iio 8 ∪ Ioi 8 ∧
      ∀ y : ℝ, principalRoot 3 (y / (y - 8)) ^ 3 = y / (y - 8) :=
  ⟨by ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]; grind,
    fun y => principalRoot_pow (by norm_num) (Or.inl (by decide))⟩

/-- Stitz-Zeager Exercise 1.4.61: `(√t - 8)/(5 - t)` is defined exactly on `[0, 5) ∪ (5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.61, p. 77"]
theorem exer_1_4_61 : {t : ℝ | 0 ≤ t ∧ 5 - t ≠ 0} = Ico 0 5 ∪ Ioi 5 := by
  ext x; simp only [mem_ofPred_eq, mem_union, mem_Ico, mem_Ioi]; grind

/-- Stitz-Zeager Exercise 1.4.62: `(w - 8)/(5 - √w)` is defined exactly on `[0, 25) ∪ (25, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 1.4.62, p. 77"]
theorem exer_1_4_62 : {w : ℝ | 0 ≤ w ∧ 5 - √w ≠ 0} = Ico 0 25 ∪ Ioi 25 := by
  have key : ∀ x : ℝ, 0 ≤ x → (√x = 5 ↔ x = 25) := by
    intro x hx
    rw [Real.sqrt_eq_iff_mul_self_eq hx (by norm_num)]
    constructor <;> intro h <;> linarith
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ico, mem_Ioi, ne_eq]
  constructor
  · rintro ⟨h0, h⟩
    have h3 : x ≠ 25 := fun h' => h (by rw [h']; have := (key 25 (by norm_num)).2 rfl; linarith)
    rcases lt_or_gt_of_ne h3 with h1 | h1
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr h1
  · rintro (⟨h0, h1⟩ | h1)
    · refine ⟨h0, fun h => ?_⟩
      have := (key x h0).1 (by linarith)
      linarith
    · refine ⟨by linarith, fun h => ?_⟩
      have := (key x (by linarith)).1 (by linarith)
      linarith

/-- Stitz-Zeager Exercise 1.4.63: `A(x) = x²` gives `A(3) = 9`, and `A(x) = 36` exactly for `x = ±6`, so `x = 6`
among positive `x`. -/
@[kb "stitzzeager2013" "Exercise 1.4.63, p. 78"]
theorem exer_1_4_63 (A : ℝ → ℝ) (hA : ∀ x, A x = x ^ 2) :
    A 3 = 9 ∧ (∀ x, A x = 36 ↔ x = 6 ∨ x = -6) ∧ ∀ x, 0 < x → (A x = 36 ↔ x = 6) := by
  refine ⟨by simp [hA]; norm_num, fun x => ?_, fun x hx => ?_⟩
  · rw [hA]
    constructor
    · intro h
      have : (x - 6) * (x + 6) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · rw [hA]
    constructor
    · intro h; nlinarith
    · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 1.4.64: `A(r) = πr²` gives `A(2) = 4π`, and `A(r) = 16π` exactly for `r = ±4`, so
`r = 4` among positive `r`. -/
@[kb "stitzzeager2013" "Exercise 1.4.64, p. 78"]
theorem exer_1_4_64 (A : ℝ → ℝ) (hA : ∀ r, A r = Real.pi * r ^ 2) :
    A 2 = 4 * Real.pi ∧ (∀ r, A r = 16 * Real.pi ↔ r = 4 ∨ r = -4) ∧
      ∀ r, 0 < r → (A r = 16 * Real.pi ↔ r = 4) := by
  have hp := Real.pi_pos
  have key : ∀ r : ℝ, A r = 16 * Real.pi ↔ r ^ 2 = 16 := by
    intro r; rw [hA]
    constructor
    · intro h; nlinarith
    · intro h; rw [h]; ring
  refine ⟨by rw [hA]; ring, fun r => ?_, fun r hr => ?_⟩
  · rw [key]
    constructor
    · intro h
      have : (r - 4) * (r + 4) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num
  · rw [key]
    constructor
    · intro h; nlinarith
    · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 1.4.65: `V(x) = x³` gives `V(5) = 125` and `V(x) = 27` exactly for `x = 3`. -/
@[kb "stitzzeager2013" "Exercise 1.4.65, p. 78"]
theorem exer_1_4_65 (V : ℝ → ℝ) (hV : ∀ x, V x = x ^ 3) :
    V 5 = 125 ∧ ∀ x, V x = 27 ↔ x = 3 := by
  refine ⟨by simp [hV]; norm_num, fun x => ?_⟩
  rw [hV]
  constructor
  · intro h
    have : (x - 3) * (x ^ 2 + 3 * x + 9) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · nlinarith [sq_nonneg (x + 3 / 2)]
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 1.4.68: `T(t) = -t²/2 + 8t + 3` has `T(0) = 3`, `T(6) = 33`, `T(12) = 27`. -/
@[kb "stitzzeager2013" "Exercise 1.4.68, p. 78"]
theorem exer_1_4_68 (T : ℝ → ℝ) (hT : ∀ t, T t = -(1 / 2) * t ^ 2 + 8 * t + 3) :
    T 0 = 3 ∧ T 6 = 33 ∧ T 12 = 27 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [hT] <;> norm_num

/-- Stitz-Zeager Exercise 1.4.69: `C(x) = x² - 10x + 27` has `C(0) = 27`, `C(2) = 11`, `C(5) = 2`. -/
@[kb "stitzzeager2013" "Exercise 1.4.69, p. 78"]
theorem exer_1_4_69 (C : ℝ → ℝ) (hC : ∀ x, C x = x ^ 2 - 10 * x + 27) :
    C 0 = 27 ∧ C 2 = 11 ∧ C 5 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [hC] <;> norm_num

/-- Stitz-Zeager Exercise 1.4.70: for `F(t) = -0.0076t² + 0.45t + 16`, `F(0) = 16`, `F(14) ≈ 20.81`, `F(28) ≈ 22.64`
(to two decimals). -/
@[kb "stitzzeager2013" "Exercise 1.4.70, p. 78"]
theorem exer_1_4_70 (F : ℝ → ℝ) (hF : ∀ t, F t = -0.0076 * t ^ 2 + 0.45 * t + 16) :
    F 0 = 16 ∧ |F 14 - 20.81| < 0.005 ∧ |F 28 - 22.64| < 0.005 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [hF] <;> norm_num [abs_lt]

/-- Stitz-Zeager Exercise 1.4.73: shipping `n` comic books costs `1.5n + 2.5` for `1 ≤ n ≤ 14` and nothing for
`n ≥ 15`; ten books cost `17.50`. -/
@[kb "stitzzeager2013" "Exercise 1.4.73, p. 79"]
theorem exer_1_4_73 (S : ℕ → ℝ) (hS : ∀ n, S n = if n ≤ 14 then (1.5 : ℝ) * n + 2.5 else (0 : ℝ)) :
    S 10 = 17.5 ∧ ∀ n, 15 ≤ n → S n = 0 := by
  refine ⟨by rw [hS]; norm_num, fun n hn => ?_⟩
  rw [hS, if_neg (by omega)]

/-- Stitz-Zeager Exercise 1.4.74: the plan costs `25` up to `1000` minutes and `25 + 0.1(m - 1000)` beyond; `750`
minutes cost `25` and 20 hours (`1200` minutes) cost `45`. -/
@[kb "stitzzeager2013" "Exercise 1.4.74, p. 79"]
theorem exer_1_4_74 (C : ℝ → ℝ) (hC : ∀ m, C m = if m ≤ 1000 then 25 else 25 + 0.1 * (m - 1000)) :
    C 750 = 25 ∧ C (20 * 60) = 45 := by
  refine ⟨?_, ?_⟩ <;> rw [hC] <;> norm_num

end UndergradKB.Precalculus.Course
