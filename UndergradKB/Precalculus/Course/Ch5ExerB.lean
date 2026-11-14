import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers, Sections 5.2 and 5.3 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 5.2: inverse functions -/

/-- A map with a left inverse on `s` is one-to-one on `s`. -/
private theorem x5_injOn {f g : ℝ → ℝ} {s : Set ℝ} (h : ∀ x ∈ s, g (f x) = x) : InjOn f s :=
  fun a ha b hb hab => by rw [← h a ha, ← h b hb, hab]

/-- Stitz-Zeager Exercise 5.2.1: `f(x) = 6x - 2` is one-to-one with inverse `f⁻¹(x) = (x+2)/6`. -/
@[kb "stitzzeager2013" "Exercise 5.2.1, p. 406"]
theorem exer_5_2_1 :
    Function.Injective (fun x : ℝ => 6 * x - 2) ∧ (∀ x : ℝ, ((6 * x - 2) + 2) / 6 = x) ∧
    ∀ y : ℝ, 6 * ((y + 2) / 6) - 2 = y := by
  refine ⟨fun a b h => by simp only at h; linarith, fun x => by ring, fun y => by ring⟩

/-- Stitz-Zeager Exercise 5.2.3: `f(x) = (x-2)/3 + 4` is one-to-one with inverse `f⁻¹(x) = 3x - 10`. -/
@[kb "stitzzeager2013" "Exercise 5.2.3, p. 406"]
theorem exer_5_2_3 :
    Function.Injective (fun x : ℝ => (x - 2) / 3 + 4) ∧ (∀ x : ℝ, 3 * ((x - 2) / 3 + 4) - 10 = x) ∧
    ∀ y : ℝ, ((3 * y - 10) - 2) / 3 + 4 = y := by
  refine ⟨fun a b h => by simp only at h; linarith, fun x => by ring, fun y => by ring⟩

/-- Stitz-Zeager Exercise 5.2.5: `f(x) = √(3x-1) + 5` (for `x ≥ 1/3`) is one-to-one with inverse
`f⁻¹(x) = (1/3)(x-5)² + 1/3` on `x ≥ 5`. -/
@[kb "stitzzeager2013" "Exercise 5.2.5, p. 406"]
theorem exer_5_2_5 :
    InjOn (fun x : ℝ => Real.sqrt (3 * x - 1) + 5) (Ici (1 / 3)) ∧
    (∀ x : ℝ, 1 / 3 ≤ x → 1 / 3 * (Real.sqrt (3 * x - 1) + 5 - 5) ^ 2 + 1 / 3 = x) ∧
    ∀ y : ℝ, 5 ≤ y → Real.sqrt (3 * (1 / 3 * (y - 5) ^ 2 + 1 / 3) - 1) + 5 = y := by
  have h1 : ∀ x : ℝ, 1 / 3 ≤ x → 1 / 3 * (Real.sqrt (3 * x - 1) + 5 - 5) ^ 2 + 1 / 3 = x := by
    intro x hx
    rw [add_sub_cancel_right, Real.sq_sqrt (by linarith)]
    ring
  refine ⟨x5_injOn (g := fun y => 1 / 3 * (y - 5) ^ 2 + 1 / 3) (fun x hx => h1 x hx), h1, fun y hy => ?_⟩
  rw [show 3 * (1 / 3 * (y - 5) ^ 2 + 1 / 3) - 1 = (y - 5) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  ring

/-- Stitz-Zeager Exercise 5.2.6: `f(x) = 2 - √(x-5)` (for `x ≥ 5`) is one-to-one with inverse
`f⁻¹(x) = (x-2)² + 5` on `x ≤ 2`. -/
@[kb "stitzzeager2013" "Exercise 5.2.6, p. 406"]
theorem exer_5_2_6 :
    InjOn (fun x : ℝ => 2 - Real.sqrt (x - 5)) (Ici 5) ∧
    (∀ x : ℝ, 5 ≤ x → (2 - Real.sqrt (x - 5) - 2) ^ 2 + 5 = x) ∧
    ∀ y : ℝ, y ≤ 2 → 2 - Real.sqrt ((y - 2) ^ 2 + 5 - 5) = y := by
  have h1 : ∀ x : ℝ, 5 ≤ x → (2 - Real.sqrt (x - 5) - 2) ^ 2 + 5 = x := by
    intro x hx
    rw [show 2 - Real.sqrt (x - 5) - 2 = -Real.sqrt (x - 5) by ring, neg_sq, Real.sq_sqrt (by linarith)]
    ring
  refine ⟨x5_injOn (g := fun y => (y - 2) ^ 2 + 5) (fun x hx => h1 x hx), h1, fun y hy => ?_⟩
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith)]
  ring

/-- Stitz-Zeager Exercise 5.2.11: `f(x) = x² - 10x` for `x ≥ 5` is one-to-one with inverse
`f⁻¹(x) = 5 + √(x+25)` on `x ≥ -25`. -/
@[kb "stitzzeager2013" "Exercise 5.2.11, p. 406"]
theorem exer_5_2_11 :
    InjOn (fun x : ℝ => x ^ 2 - 10 * x) (Ici 5) ∧
    (∀ x : ℝ, 5 ≤ x → 5 + Real.sqrt (x ^ 2 - 10 * x + 25) = x) ∧
    ∀ y : ℝ, -25 ≤ y → (5 + Real.sqrt (y + 25)) ^ 2 - 10 * (5 + Real.sqrt (y + 25)) = y := by
  have h1 : ∀ x : ℝ, 5 ≤ x → 5 + Real.sqrt (x ^ 2 - 10 * x + 25) = x := by
    intro x hx
    rw [show x ^ 2 - 10 * x + 25 = (x - 5) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    ring
  refine ⟨x5_injOn (g := fun y => 5 + Real.sqrt (y + 25)) (fun x hx => ?_), h1, fun y hy => ?_⟩
  · show 5 + Real.sqrt (x ^ 2 - 10 * x + 25) = x
    exact h1 x hx
  · have h := Real.sq_sqrt (show 0 ≤ y + 25 by linarith)
    nlinarith [h]

/-- Stitz-Zeager Exercise 5.2.12: `f(x) = 3(x+4)² - 5` for `x ≤ -4` is one-to-one with inverse
`f⁻¹(x) = -√((x+5)/3) - 4` on `x ≥ -5`. -/
@[kb "stitzzeager2013" "Exercise 5.2.12, p. 406"]
theorem exer_5_2_12 :
    InjOn (fun x : ℝ => 3 * (x + 4) ^ 2 - 5) (Iic (-4)) ∧
    (∀ x : ℝ, x ≤ -4 → -Real.sqrt ((3 * (x + 4) ^ 2 - 5 + 5) / 3) - 4 = x) ∧
    ∀ y : ℝ, -5 ≤ y → 3 * (-Real.sqrt ((y + 5) / 3) - 4 + 4) ^ 2 - 5 = y := by
  have h1 : ∀ x : ℝ, x ≤ -4 → -Real.sqrt ((3 * (x + 4) ^ 2 - 5 + 5) / 3) - 4 = x := by
    intro x hx
    rw [show (3 * (x + 4) ^ 2 - 5 + 5) / 3 = (x + 4) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  refine ⟨x5_injOn (g := fun y => -Real.sqrt ((y + 5) / 3) - 4) (fun x hx => h1 x hx), h1, fun y hy => ?_⟩
  rw [show -Real.sqrt ((y + 5) / 3) - 4 + 4 = -Real.sqrt ((y + 5) / 3) by ring, neg_sq,
    Real.sq_sqrt (by linarith)]
  ring

/-- Stitz-Zeager Exercise 5.2.13: `f(x) = x² - 6x + 5` for `x ≤ 3` is one-to-one with inverse
`f⁻¹(x) = 3 - √(x+4)` on `x ≥ -4`. -/
@[kb "stitzzeager2013" "Exercise 5.2.13, p. 406"]
theorem exer_5_2_13 :
    InjOn (fun x : ℝ => x ^ 2 - 6 * x + 5) (Iic 3) ∧
    (∀ x : ℝ, x ≤ 3 → 3 - Real.sqrt (x ^ 2 - 6 * x + 5 + 4) = x) ∧
    ∀ y : ℝ, -4 ≤ y → (3 - Real.sqrt (y + 4)) ^ 2 - 6 * (3 - Real.sqrt (y + 4)) + 5 = y := by
  have h1 : ∀ x : ℝ, x ≤ 3 → 3 - Real.sqrt (x ^ 2 - 6 * x + 5 + 4) = x := by
    intro x hx
    rw [show x ^ 2 - 6 * x + 5 + 4 = (x - 3) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  refine ⟨x5_injOn (g := fun y => 3 - Real.sqrt (y + 4)) (fun x hx => h1 x hx), h1, fun y hy => ?_⟩
  have h := Real.sq_sqrt (show 0 ≤ y + 4 by linarith)
  nlinarith [h]

/-- Stitz-Zeager Exercise 5.2.14: `f(x) = 4x² + 4x + 1` for `x < -1` is one-to-one with inverse
`f⁻¹(x) = -(√x + 1)/2` on `x > 1`. -/
@[kb "stitzzeager2013" "Exercise 5.2.14, p. 406"]
theorem exer_5_2_14 :
    InjOn (fun x : ℝ => 4 * x ^ 2 + 4 * x + 1) (Iio (-1)) ∧
    (∀ x : ℝ, x < -1 → -(Real.sqrt (4 * x ^ 2 + 4 * x + 1) + 1) / 2 = x) ∧
    ∀ y : ℝ, 1 < y → 4 * (-(Real.sqrt y + 1) / 2) ^ 2 + 4 * (-(Real.sqrt y + 1) / 2) + 1 = y := by
  have h1 : ∀ x : ℝ, x < -1 → -(Real.sqrt (4 * x ^ 2 + 4 * x + 1) + 1) / 2 = x := by
    intro x hx
    rw [show 4 * x ^ 2 + 4 * x + 1 = (2 * x + 1) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  refine ⟨x5_injOn (g := fun y => -(Real.sqrt y + 1) / 2) (fun x hx => h1 x hx), h1, fun y hy => ?_⟩
  have h := Real.sq_sqrt (show 0 ≤ y by linarith)
  nlinarith [h]

/-- Stitz-Zeager Exercise 5.2.15: `f(x) = 3/(4-x)` has inverse `f⁻¹(x) = (4x-3)/x` (for `x ≠ 4` in the domain of `f`
and `x ≠ 0` in its range). -/
@[kb "stitzzeager2013" "Exercise 5.2.15, p. 406"]
theorem exer_5_2_15 :
    (∀ x : ℝ, x ≠ 4 → (4 * (3 / (4 - x)) - 3) / (3 / (4 - x)) = x) ∧
    ∀ y : ℝ, y ≠ 0 → 3 / (4 - (4 * y - 3) / y) = y := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h : 4 - x ≠ 0 := fun h => hx (by linarith)
    field_simp
    ring
  · field_simp
    ring

/-- Stitz-Zeager Exercise 5.2.17: `f(x) = (2x-1)/(3x+4)` has inverse `f⁻¹(x) = (4x+1)/(2-3x)`. -/
@[kb "stitzzeager2013" "Exercise 5.2.17, p. 406"]
theorem exer_5_2_17 :
    (∀ x : ℝ, 3 * x + 4 ≠ 0 → (4 * ((2 * x - 1) / (3 * x + 4)) + 1) / (2 - 3 * ((2 * x - 1) / (3 * x + 4))) = x) ∧
    ∀ y : ℝ, 2 - 3 * y ≠ 0 →
      (2 * ((4 * y + 1) / (2 - 3 * y)) - 1) / (3 * ((4 * y + 1) / (2 - 3 * y)) + 4) = y := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h : 2 - 3 * ((2 * x - 1) / (3 * x + 4)) = 11 / (3 * x + 4) := by
      rw [eq_div_iff hx, sub_mul, mul_assoc, div_mul_cancel₀ _ hx]
      ring
    have hn : 4 * ((2 * x - 1) / (3 * x + 4)) + 1 = 11 * x / (3 * x + 4) := by
      rw [eq_div_iff hx, add_mul, mul_assoc, div_mul_cancel₀ _ hx]
      ring
    rw [hn, h, div_div_div_cancel_right₀ hx]
    ring
  · have h : 3 * ((4 * y + 1) / (2 - 3 * y)) + 4 = 11 / (2 - 3 * y) := by
      rw [eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have hn : 2 * ((4 * y + 1) / (2 - 3 * y)) - 1 = 11 * y / (2 - 3 * y) := by
      rw [eq_div_iff hy, sub_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    rw [hn, h, div_div_div_cancel_right₀ hy]
    ring

/-- Stitz-Zeager Exercise 5.2.19: `f(x) = (-3x-2)/(x+3)` is its own inverse: `f(f(x)) = x` for `x ≠ -3`. -/
@[kb "stitzzeager2013" "Exercise 5.2.19, p. 406"]
theorem exer_5_2_19 (x : ℝ) (hx : x + 3 ≠ 0) :
    (-3 * ((-3 * x - 2) / (x + 3)) - 2) / ((-3 * x - 2) / (x + 3) + 3) = x := by
  have h : (-3 * x - 2) / (x + 3) + 3 = 7 / (x + 3) := by
    field_simp
    ring
  rw [h]
  field_simp
  ring

/-- Stitz-Zeager Exercise 5.2.25: for the price function `p(x) = 450 - 15x`, `0 ≤ x ≤ 30`: its range is `[0, 450]`,
`p⁻¹(x) = (450-x)/15`, `p⁻¹(105) = 23`, the profit `P(x) = -15x² + 350x - 2000` composed with `p⁻¹` is
`-x²/15 + (110/3)x - 5000`, whose maximum value is `125/3`, attained at `x = 275`. -/
@[kb "stitzzeager2013" "Exercise 5.2.25, p. 406"]
theorem exer_5_2_25 :
    (fun x : ℝ => 450 - 15 * x) '' Icc 0 30 = Icc 0 450 ∧
    (∀ x : ℝ, (450 - (450 - 15 * x)) / 15 = x) ∧ (450 - (105 : ℝ)) / 15 = 23 ∧
    (∀ x : ℝ, -15 * ((450 - x) / 15) ^ 2 + 350 * ((450 - x) / 15) - 2000 =
      -(1 / 15) * x ^ 2 + 110 / 3 * x - 5000) ∧
    (∀ x : ℝ, -(1 / 15) * x ^ 2 + 110 / 3 * x - 5000 ≤ 125 / 3) ∧
    -(1 / 15) * (275 : ℝ) ^ 2 + 110 / 3 * 275 - 5000 = 125 / 3 := by
  refine ⟨?_, fun x => by ring, by norm_num, fun x => by ring, fun x => ?_, by norm_num⟩
  · ext y
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      exact ⟨(450 - y) / 15, ⟨by linarith, by linarith⟩, by ring⟩
  · nlinarith [sq_nonneg (x - 275)]

/-- Stitz-Zeager Exercise 5.2.27: `f(x) = x³ + 3x + 1` is strictly increasing, hence one-to-one, and `f(0) = 1`,
`f(1) = 5`, `f(-1) = -3`, so `f⁻¹(1) = 0`, `f⁻¹(5) = 1`, `f⁻¹(-3) = -1`. -/
@[kb "stitzzeager2013" "Exercise 5.2.27, p. 407"]
theorem exer_5_2_27 :
    StrictMono (fun x : ℝ => x ^ 3 + 3 * x + 1) ∧ (0 : ℝ) ^ 3 + 3 * 0 + 1 = 1 ∧
    (1 : ℝ) ^ 3 + 3 * 1 + 1 = 5 ∧ (-1 : ℝ) ^ 3 + 3 * (-1) + 1 = -3 := by
  refine ⟨fun a b h => ?_, by norm_num, by norm_num, by norm_num⟩
  simp only
  have h1 : 0 < a ^ 2 + a * b + b ^ 2 + 3 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  nlinarith [mul_pos (sub_pos.2 h) h1]

/-- Stitz-Zeager Exercise 5.2.30: if `f` is odd and `g` is its inverse, then `g` is odd. -/
@[kb "stitzzeager2013" "Exercise 5.2.30, p. 407"]
theorem exer_5_2_30 {f g : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hl : ∀ x, g (f x) = x)
    (hr : ∀ y, f (g y) = y) : ∀ y, g (-y) = -g y := by
  intro y
  calc g (-y) = g (-f (g y)) := by rw [hr]
    _ = g (f (-g y)) := by rw [hodd]
    _ = -g y := hl _

/-- Stitz-Zeager Exercise 5.2.31: if `f` and `g` have inverses `f'` and `g'`, then `f ∘ g` is one-to-one with inverse
`g' ∘ f'`. -/
@[kb "stitzzeager2013" "Exercise 5.2.31, p. 407"]
theorem exer_5_2_31 {f g f' g' : ℝ → ℝ} (hf : ∀ x, f' (f x) = x) (hf' : ∀ y, f (f' y) = y)
    (hg : ∀ x, g' (g x) = x) (hg' : ∀ y, g (g' y) = y) :
    Function.Injective (f ∘ g) ∧ (∀ x, (g' ∘ f') ((f ∘ g) x) = x) ∧ ∀ y, (f ∘ g) ((g' ∘ f') y) = y := by
  refine ⟨?_, fun x => ?_, fun y => ?_⟩
  · intro a b h
    have := congrArg (fun z => g' (f' z)) h
    simpa [Function.comp, hf, hg] using this
  · simp [Function.comp, hf, hg]
  · simp [Function.comp, hf', hg']

end UndergradKB.Precalculus.Course
