import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.2 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 5.2: inverse functions -/

/-- A map with a left inverse on `s` is one-to-one on `s`. -/
private theorem x5w7_injOn {f g : ℝ → ℝ} {s : Set ℝ} (h : ∀ x ∈ s, g (f x) = x) : InjOn f s :=
  fun a ha b hb hab => by rw [← h a ha, ← h b hb, hab]

/-- Stitz-Zeager Exercise 5.2.2: `f(x) = 42 - x` is one-to-one and is its own inverse. -/
@[kb "stitzzeager2013" "Exercise 5.2.2, p. 406"]
theorem exer_5_2_2 :
    Function.Injective (fun x : ℝ => 42 - x) ∧ (∀ x : ℝ, 42 - (42 - x) = x) := by
  refine ⟨fun a b h => by simp only at h; linarith, fun x => by ring⟩

/-- Stitz-Zeager Exercise 5.2.4: `f(x) = 1 - (4+3x)/5` is one-to-one with inverse `f⁻¹(x) = -(5/3)x + 1/3`. -/
@[kb "stitzzeager2013" "Exercise 5.2.4, p. 406"]
theorem exer_5_2_4 :
    Function.Injective (fun x : ℝ => 1 - (4 + 3 * x) / 5) ∧
    (∀ x : ℝ, -(5 / 3) * (1 - (4 + 3 * x) / 5) + 1 / 3 = x) ∧
    ∀ y : ℝ, 1 - (4 + 3 * (-(5 / 3) * y + 1 / 3)) / 5 = y := by
  refine ⟨fun a b h => by simp only at h; linarith, fun x => by ring, fun y => by ring⟩

/-- Stitz-Zeager Exercise 5.2.7: `f(x) = 3√(x-1) - 4` (for `x ≥ 1`) is one-to-one with inverse
`f⁻¹(x) = (1/9)(x+4)² + 1` on `x ≥ -4`. -/
@[kb "stitzzeager2013" "Exercise 5.2.7, p. 406"]
theorem exer_5_2_7 :
    InjOn (fun x : ℝ => 3 * Real.sqrt (x - 1) - 4) (Ici 1) ∧
    (∀ x : ℝ, 1 ≤ x → 1 / 9 * (3 * Real.sqrt (x - 1) - 4 + 4) ^ 2 + 1 = x) ∧
    ∀ y : ℝ, -4 ≤ y → 3 * Real.sqrt (1 / 9 * (y + 4) ^ 2 + 1 - 1) - 4 = y := by
  have h1 : ∀ x : ℝ, 1 ≤ x → 1 / 9 * (3 * Real.sqrt (x - 1) - 4 + 4) ^ 2 + 1 = x := by
    intro x hx
    rw [show 3 * Real.sqrt (x - 1) - 4 + 4 = 3 * Real.sqrt (x - 1) by ring, mul_pow,
      Real.sq_sqrt (by linarith)]
    ring
  refine ⟨x5w7_injOn (g := fun y => 1 / 9 * (y + 4) ^ 2 + 1) (fun x hx => h1 x hx), h1, fun y hy => ?_⟩
  rw [show 1 / 9 * (y + 4) ^ 2 + 1 - 1 = ((y + 4) / 3) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  ring

/-- Stitz-Zeager Exercise 5.2.8: `f(x) = 1 - 2√(2x+5)` (for `x ≥ -5/2`) is one-to-one with inverse
`f⁻¹(x) = (1/8)(x-1)² - 5/2` on `x ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 5.2.8, p. 406"]
theorem exer_5_2_8 :
    InjOn (fun x : ℝ => 1 - 2 * Real.sqrt (2 * x + 5)) (Ici (-5 / 2)) ∧
    (∀ x : ℝ, -5 / 2 ≤ x → 1 / 8 * (1 - 2 * Real.sqrt (2 * x + 5) - 1) ^ 2 - 5 / 2 = x) ∧
    ∀ y : ℝ, y ≤ 1 → 1 - 2 * Real.sqrt (2 * (1 / 8 * (y - 1) ^ 2 - 5 / 2) + 5) = y := by
  have h1 : ∀ x : ℝ, -5 / 2 ≤ x → 1 / 8 * (1 - 2 * Real.sqrt (2 * x + 5) - 1) ^ 2 - 5 / 2 = x := by
    intro x hx
    rw [show 1 - 2 * Real.sqrt (2 * x + 5) - 1 = -(2 * Real.sqrt (2 * x + 5)) by ring, neg_sq, mul_pow,
      Real.sq_sqrt (by linarith)]
    ring
  refine ⟨x5w7_injOn (g := fun y => 1 / 8 * (y - 1) ^ 2 - 5 / 2) (fun x hx => h1 x hx), h1, fun y hy => ?_⟩
  rw [show 2 * (1 / 8 * (y - 1) ^ 2 - 5 / 2) + 5 = ((1 - y) / 2) ^ 2 by ring,
    Real.sqrt_sq (by linarith)]
  ring

/-- Stitz-Zeager Exercise 5.2.9: `f(x) = ⁵√(3x-1)` (real fifth root) is one-to-one on `ℝ` with inverse
`f⁻¹(x) = (x⁵+1)/3`. -/
@[kb "stitzzeager2013" "Exercise 5.2.9, p. 406"]
theorem exer_5_2_9 :
    Function.Injective (fun x : ℝ => UndergradKB.Precalculus.principalRoot 5 (3 * x - 1)) ∧
    (∀ x : ℝ, (UndergradKB.Precalculus.principalRoot 5 (3 * x - 1) ^ 5 + 1) / 3 = x) ∧
    ∀ y : ℝ, UndergradKB.Precalculus.principalRoot 5 (3 * ((y ^ 5 + 1) / 3) - 1) = y := by
  have h5 : Odd 5 := by decide
  have h1 : ∀ x : ℝ, (UndergradKB.Precalculus.principalRoot 5 (3 * x - 1) ^ 5 + 1) / 3 = x := by
    intro x
    rw [UndergradKB.Precalculus.principalRoot_pow (by norm_num) (Or.inl h5)]; ring
  refine ⟨fun a b h => ?_, h1, fun y => ?_⟩
  · have := h1 a; simp only at h; rw [h, h1 b] at this; exact this.symm
  · rw [show 3 * ((y ^ 5 + 1) / 3) - 1 = y ^ 5 by ring]
    exact UndergradKB.Precalculus.principalRoot_pow_self_odd h5 y

/-- Stitz-Zeager Exercise 5.2.10: `f(x) = 3 - ∛(x-2)` (real cube root) is one-to-one on `ℝ` with inverse
`f⁻¹(x) = -(x-3)³ + 2`. -/
@[kb "stitzzeager2013" "Exercise 5.2.10, p. 406"]
theorem exer_5_2_10 :
    Function.Injective (fun x : ℝ => 3 - UndergradKB.Precalculus.principalRoot 3 (x - 2)) ∧
    (∀ x : ℝ, -(3 - UndergradKB.Precalculus.principalRoot 3 (x - 2) - 3) ^ 3 + 2 = x) ∧
    ∀ y : ℝ, 3 - UndergradKB.Precalculus.principalRoot 3 (-(y - 3) ^ 3 + 2 - 2) = y := by
  have h3 : Odd 3 := by decide
  have h1 : ∀ x : ℝ, -(3 - UndergradKB.Precalculus.principalRoot 3 (x - 2) - 3) ^ 3 + 2 = x := by
    intro x
    have := UndergradKB.Precalculus.principalRoot_pow (n := 3) (x := x - 2) (by norm_num) (Or.inl h3)
    rw [show -(3 - UndergradKB.Precalculus.principalRoot 3 (x - 2) - 3) ^ 3 =
      UndergradKB.Precalculus.principalRoot 3 (x - 2) ^ 3 by ring, this]; ring
  refine ⟨fun a b h => ?_, h1, fun y => ?_⟩
  · have := h1 a; simp only at h; rw [h, h1 b] at this; exact this.symm
  · rw [show -(y - 3) ^ 3 + 2 - 2 = (-(y - 3)) ^ 3 by ring,
      UndergradKB.Precalculus.principalRoot_pow_self_odd h3]
    ring

/-- Stitz-Zeager Exercise 5.2.16: `f(x) = x/(1-3x)` (for `x ≠ 1/3`) is one-to-one with inverse
`f⁻¹(x) = x/(3x+1)` (for `x ≠ -1/3`). -/
@[kb "stitzzeager2013" "Exercise 5.2.16, p. 406"]
theorem exer_5_2_16 :
    InjOn (fun x : ℝ => x / (1 - 3 * x)) {x | x ≠ 1 / 3} ∧
    (∀ x : ℝ, x ≠ 1 / 3 → 3 * (x / (1 - 3 * x)) + 1 ≠ 0 ∧
      (x / (1 - 3 * x)) / (3 * (x / (1 - 3 * x)) + 1) = x) ∧
    ∀ y : ℝ, y ≠ -1 / 3 → 1 - 3 * (y / (3 * y + 1)) ≠ 0 ∧
      (y / (3 * y + 1)) / (1 - 3 * (y / (3 * y + 1))) = y := by
  have h1 : ∀ x : ℝ, x ∈ {x : ℝ | x ≠ 1 / 3} →
      (x / (1 - 3 * x)) / (3 * (x / (1 - 3 * x)) + 1) = x := by
    intro x hx
    have h : 1 - 3 * x ≠ 0 := fun h => hx (by simp only [mem_ofPred_eq] at hx ⊢; linarith)
    have h' : 3 * (x / (1 - 3 * x)) + 1 = 1 / (1 - 3 * x) := by field_simp; ring
    rw [h', div_div_div_cancel_right₀ h]; simp
  refine ⟨x5w7_injOn (g := fun y => y / (3 * y + 1)) (fun x hx => h1 x hx), fun x hx => ⟨?_, h1 x hx⟩, fun y hy => ?_⟩
  · have h : 1 - 3 * x ≠ 0 := fun h => hx (by linarith)
    have h' : 3 * (x / (1 - 3 * x)) + 1 = 1 / (1 - 3 * x) := by field_simp; ring
    rw [h']; exact one_div_ne_zero h
  · have h : 3 * y + 1 ≠ 0 := fun h => hy (by linarith)
    have h' : 1 - 3 * (y / (3 * y + 1)) = 1 / (3 * y + 1) := by field_simp; ring
    rw [h']
    exact ⟨one_div_ne_zero h, by rw [div_div_div_cancel_right₀ h]; simp⟩

/-- Stitz-Zeager Exercise 5.2.18: `f(x) = (4x+2)/(3x-6)` (for `x ≠ 2`) is one-to-one with inverse
`f⁻¹(x) = (6x+2)/(3x-4)` (for `x ≠ 4/3`). -/
@[kb "stitzzeager2013" "Exercise 5.2.18, p. 406"]
theorem exer_5_2_18 :
    InjOn (fun x : ℝ => (4 * x + 2) / (3 * x - 6)) {x | x ≠ 2} ∧
    (∀ x : ℝ, x ≠ 2 → 3 * ((4 * x + 2) / (3 * x - 6)) - 4 ≠ 0 ∧
      (6 * ((4 * x + 2) / (3 * x - 6)) + 2) / (3 * ((4 * x + 2) / (3 * x - 6)) - 4) = x) ∧
    ∀ y : ℝ, y ≠ 4 / 3 → 3 * ((6 * y + 2) / (3 * y - 4)) - 6 ≠ 0 ∧
      (4 * ((6 * y + 2) / (3 * y - 4)) + 2) / (3 * ((6 * y + 2) / (3 * y - 4)) - 6) = y := by
  have key : ∀ x : ℝ, x ≠ 2 → 3 * ((4 * x + 2) / (3 * x - 6)) - 4 ≠ 0 ∧
      (6 * ((4 * x + 2) / (3 * x - 6)) + 2) / (3 * ((4 * x + 2) / (3 * x - 6)) - 4) = x := by
    intro x hx
    have h : 3 * x - 6 ≠ 0 := fun h => hx (by linarith)
    have h' : 3 * ((4 * x + 2) / (3 * x - 6)) - 4 = 30 / (3 * x - 6) := by field_simp; ring
    rw [h']
    refine ⟨div_ne_zero (by norm_num) h, ?_⟩
    have : 6 * ((4 * x + 2) / (3 * x - 6)) + 2 = 30 * x / (3 * x - 6) := by
      rw [eq_div_iff h]; have := div_mul_cancel₀ (4 * x + 2) h; linear_combination 6 * this
    rw [this, div_div_div_cancel_right₀ h]; field_simp
  refine ⟨x5w7_injOn (g := fun y => (6 * y + 2) / (3 * y - 4)) (fun x hx => (key x hx).2),
    fun x hx => key x hx, fun y hy => ?_⟩
  have h : 3 * y - 4 ≠ 0 := fun h => hy (by linarith)
  have h' : 3 * ((6 * y + 2) / (3 * y - 4)) - 6 = 30 / (3 * y - 4) := by field_simp; ring
  rw [h']
  refine ⟨div_ne_zero (by norm_num) h, ?_⟩
  have : 4 * ((6 * y + 2) / (3 * y - 4)) + 2 = 30 * y / (3 * y - 4) := by
    rw [eq_div_iff h]; have := div_mul_cancel₀ (6 * y + 2) h; linear_combination 4 * this
  rw [this, div_div_div_cancel_right₀ h]; field_simp

/-- Stitz-Zeager Exercise 5.2.20: `f(x) = (x-2)/(2x-1)` (for `x ≠ 1/2`) is one-to-one and is its own inverse
(its values are never `1/2`). -/
@[kb "stitzzeager2013" "Exercise 5.2.20, p. 406"]
theorem exer_5_2_20 :
    InjOn (fun x : ℝ => (x - 2) / (2 * x - 1)) {x | x ≠ 1 / 2} ∧
    ∀ x : ℝ, x ≠ 1 / 2 → 2 * ((x - 2) / (2 * x - 1)) - 1 ≠ 0 ∧
      ((x - 2) / (2 * x - 1) - 2) / (2 * ((x - 2) / (2 * x - 1)) - 1) = x := by
  have key : ∀ x : ℝ, x ≠ 1 / 2 → 2 * ((x - 2) / (2 * x - 1)) - 1 ≠ 0 ∧
      ((x - 2) / (2 * x - 1) - 2) / (2 * ((x - 2) / (2 * x - 1)) - 1) = x := by
    intro x hx
    have h : 2 * x - 1 ≠ 0 := fun h => hx (by linarith)
    have h' : 2 * ((x - 2) / (2 * x - 1)) - 1 = -3 / (2 * x - 1) := by field_simp; ring
    rw [h']
    refine ⟨div_ne_zero (by norm_num) h, ?_⟩
    have : (x - 2) / (2 * x - 1) - 2 = (-3 * x) / (2 * x - 1) := by
      rw [eq_div_iff h]; have := div_mul_cancel₀ (x - 2) h; linear_combination this
    rw [this, div_div_div_cancel_right₀ h]; field_simp
  exact ⟨x5w7_injOn (g := fun y => (y - 2) / (2 * y - 1)) (fun x hx => (key x hx).2), key⟩

end UndergradKB.Precalculus.Course
