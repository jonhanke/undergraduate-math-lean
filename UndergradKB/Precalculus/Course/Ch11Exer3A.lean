import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 11.2, 11.3 and 11.4 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 11.2 -/

/-- Stitz-Zeager Exercise 11.2.38: the triangle with vertices `(0,0)`, `(c cos α, c sin α)`, `(b,0)`
(sides `b`, `c` enclosing the angle `α`) has area `½ b c sin α` (shoelace formula). -/
@[kb "stitzzeager2013" "Exercise 11.2.38, p. 919"]
theorem exer_11_2_38 (α b c : ℝ) (hα0 : 0 < α) (hα1 : α < π) (hb : 0 < b) (hc : 0 < c) :
    (1 / 2) * |0 * (c * sin α - 0) + (c * cos α) * (0 - 0) + b * (0 - c * sin α)| =
      (1 / 2) * b * c * sin α := by
  have hs : 0 < sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hα1
  have h : 0 * (c * sin α - 0) + (c * cos α) * (0 - 0) + b * (0 - c * sin α) = -(b * c * sin α) := by
    ring
  rw [h, abs_neg, abs_of_pos (by positivity)]
  ring

/-! ## Section 11.3 -/

/-- Bounds for `cos 63°`. -/
theorem ch11e3a_cos63 : (0.436 : ℝ) < cos (63 * π / 180) ∧ cos (63 * π / 180) < 1 / 2 := by
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  constructor
  · have h : cos (63 * π / 180) = sin (27 * π / 180) := by
      rw [← Real.sin_pi_div_two_sub]
      congr 1
      ring
    rw [h]
    have hx0 : (0 : ℝ) < 27 * π / 180 := by linarith
    have hs := Real.sin_gt_sub_cube hx0
    have hx2 : 27 * π / 180 < 0.4725 := by linarith
    have hx3 : (0.471 : ℝ) < 27 * π / 180 := by linarith
    have h3 : (27 * π / 180) ^ 3 < 0.4725 ^ 3 := pow_lt_pow_left₀ hx2 hx0.le (by norm_num)
    norm_num at h3
    linarith
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := π / 3) (y := 63 * π / 180)
      (by positivity) (by linarith) (by linarith)
    rw [Real.cos_pi_div_three] at h
    exact h

/-- Stitz-Zeager Exercise 11.3.26 (applied to 11.11): `a = 18, α = 63°, b = 20`. The Law of Cosines gives
`c² - 40 cos(63°) c + 76 = 0`, which has two distinct positive zeros (two triangles). -/
@[kb "stitzzeager2013" "Exercise 11.3.26, p. 929"]
theorem exer_11_3_26_a : ∃ c₁ c₂ : ℝ, c₁ ≠ c₂ ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∀ c : ℝ,
    (0 < c ∧ 18 ^ 2 = 20 ^ 2 + c ^ 2 - 2 * 20 * c * cos (63 * π / 180)) ↔ (c = c₁ ∨ c = c₂) := by
  obtain ⟨hk1, hk2⟩ := ch11e3a_cos63
  set k := cos (63 * π / 180) with hk
  have hkk : (0.190096 : ℝ) < k ^ 2 := by nlinarith
  have hD : (0 : ℝ) ≤ 400 * k ^ 2 - 76 := by nlinarith
  set r := √(400 * k ^ 2 - 76) with hrdef
  have hr2 : r ^ 2 = 400 * k ^ 2 - 76 := Real.sq_sqrt hD
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by nlinarith)
  have hrk : r < 20 * k := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  refine ⟨20 * k - r, 20 * k + r, by linarith, by linarith, by linarith, fun c => ?_⟩
  constructor
  · rintro ⟨_, he⟩
    have hprod : (c - (20 * k - r)) * (c - (20 * k + r)) = 0 := by
      linear_combination (-1 : ℝ) * he - hr2
    rcases mul_eq_zero.mp hprod with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · refine ⟨by linarith, ?_⟩
      rw [h]
      linear_combination (-1 : ℝ) * hr2
    · refine ⟨by linarith, ?_⟩
      rw [h]
      linear_combination (-1 : ℝ) * hr2

/-- Stitz-Zeager Exercise 11.3.26 (applied to 11.13): `a = 16, α = 63°, b = 20`. The Law of Cosines gives
`c² - 40 cos(63°) c + 144 = 0`, with no positive real zero (no triangle). -/
@[kb "stitzzeager2013" "Exercise 11.3.26, p. 929"]
theorem exer_11_3_26_b : ¬ ∃ c : ℝ, 0 < c ∧
    16 ^ 2 = 20 ^ 2 + c ^ 2 - 2 * 20 * c * cos (63 * π / 180) := by
  obtain ⟨hk1, hk2⟩ := ch11e3a_cos63
  set k := cos (63 * π / 180) with hk
  rintro ⟨c, _, he⟩
  nlinarith [sq_nonneg (c - 20 * k)]

/-- Stitz-Zeager Exercise 11.3.26 (applied to 11.14): `a = 22, α = 63°, b = 20`. The Law of Cosines gives
`c² - 40 cos(63°) c - 84 = 0`, with exactly one positive real zero (one triangle). -/
@[kb "stitzzeager2013" "Exercise 11.3.26, p. 929"]
theorem exer_11_3_26_c : ∃! c : ℝ, 0 < c ∧
    22 ^ 2 = 20 ^ 2 + c ^ 2 - 2 * 20 * c * cos (63 * π / 180) := by
  obtain ⟨hk1, hk2⟩ := ch11e3a_cos63
  set k := cos (63 * π / 180) with hk
  have hD : (0 : ℝ) ≤ 400 * k ^ 2 + 84 := by nlinarith
  set r := √(400 * k ^ 2 + 84) with hrdef
  have hr2 : r ^ 2 = 400 * k ^ 2 + 84 := Real.sq_sqrt hD
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrk : 20 * k < r := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith
  refine ⟨20 * k + r, ⟨by linarith, ?_⟩, ?_⟩
  · linear_combination (-1 : ℝ) * hr2
  · rintro c ⟨hc, he⟩
    have hprod : (c - (20 * k + r)) * (c - (20 * k - r)) = 0 := by
      linear_combination (-1 : ℝ) * he - hr2
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exfalso; linarith

/-! ## Section 11.4 -/

/-- Stitz-Zeager Exercise 11.4.98: the squared distance between the points with polar coordinates
`(r₁, θ₁)` and `(r₂, θ₂)` is `r₁² + r₂² - 2 r₁ r₂ cos(θ₁ - θ₂)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.98, p. 943"]
theorem exer_11_4_98 (r₁ θ₁ r₂ θ₂ : ℝ) :
    (r₁ * cos θ₁ - r₂ * cos θ₂) ^ 2 + (r₁ * sin θ₁ - r₂ * sin θ₂) ^ 2 =
      r₁ ^ 2 + r₂ ^ 2 - 2 * r₁ * r₂ * cos (θ₁ - θ₂) := by
  rw [Real.cos_sub]
  have h1 := Real.sin_sq_add_cos_sq θ₁
  have h2 := Real.sin_sq_add_cos_sq θ₂
  linear_combination r₁ ^ 2 * h1 + r₂ ^ 2 * h2

end UndergradKB.Precalculus.Course
