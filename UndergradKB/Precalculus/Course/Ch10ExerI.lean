import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.TrigExtras

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.7
(trigonometric equations and inequalities) -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

private lemma cos_sol7 (y x : ℝ) (hy0 : -1 < y) (hy1 : y < 1) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = y ↔ x = arccos y ∨ x = 2 * π - arccos y := by
  obtain ⟨a, ha⟩ : ∃ a, a = arccos y := ⟨_, rfl⟩
  have hs : cos a = y := by rw [ha]; exact cos_arccos hy0.le hy1.le
  have ha0 : 0 < a := by rw [ha]; exact arccos_pos.mpr hy1
  have ha1 : a < π := by rw [ha]; exact arccos_lt_pi.mpr hy0
  rw [← ha, ← hs]
  have key : cos x = cos a ↔ cos a = cos x := eq_comm
  rw [key, cos_eq_cos_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, h | h⟩
    · have hk0 : (-1 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 1 := by exact_mod_cast hk1
      have : k = 0 := by omega
      subst this
      left; simpa using h
    · have hk0 : (0 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 2 := by nlinarith
      have h1 : (0 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 2 := by exact_mod_cast hk1
      have : k = 1 := by omega
      subst this
      right; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, Or.inl (by rw [h]; simp)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma sin_zero7 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) : sin x = 0 ↔ x = 0 ∨ x = π := by
  have hpi := Real.pi_pos
  rw [sin_eq_zero_iff]
  constructor
  · rintro ⟨n, h⟩
    have hk0 : (-1 : ℝ) < n := by nlinarith
    have hk1 : (n : ℝ) < 2 := by nlinarith
    have h1 : (-1 : ℤ) < n := by exact_mod_cast hk0
    have h2 : n < 2 := by exact_mod_cast hk1
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · left; simpa using h.symm
    · right; simpa using h.symm
  · rintro (h | h)
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; simp⟩

private lemma cos_one7 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) : cos x = 1 ↔ x = 0 := by
  have hpi := Real.pi_pos
  rw [cos_eq_one_iff]
  constructor
  · rintro ⟨n, h⟩
    have hk0 : (-1 : ℝ) < n := by nlinarith
    have hk1 : (n : ℝ) < 1 := by nlinarith
    have h1 : (-1 : ℤ) < n := by exact_mod_cast hk0
    have h2 : n < 1 := by exact_mod_cast hk1
    have : n = 0 := by omega
    subst this
    simpa using h.symm
  · rintro rfl
    exact ⟨0, by simp⟩

private lemma cos_half7 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = 1 / 2 ↔ x = π / 3 ∨ x = 5 * π / 3 := by
  have h3 : arccos (1 / 2) = π / 3 := by
    rw [← cos_pi_div_three]; exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [cos_sol7 _ x (by norm_num) (by norm_num) hx0 hx1, h3]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

private lemma cos_mhalf7 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = -(1 / 2) ↔ x = 2 * π / 3 ∨ x = 4 * π / 3 := by
  have h3 : arccos (-(1 / 2)) = 2 * π / 3 := by
    have : cos (2 * π / 3) = -(1 / 2) := by
      rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
    rw [← this]; exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [cos_sol7 _ x (by norm_num) (by norm_num) hx0 hx1, h3]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

private lemma sin_half7 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = 1 / 2 ↔ x = π / 6 ∨ x = 5 * π / 6 := by
  have hpi := Real.pi_pos
  have key : sin x = sin (π / 6) ↔ sin (π / 6) = sin x := eq_comm
  rw [show (1 / 2 : ℝ) = sin (π / 6) by rw [sin_pi_div_six], key, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · have hk0 : (-1 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 1 := by exact_mod_cast hk1
      have : k = 0 := by omega
      subst this
      left; rw [h]; push_cast; ring
    · have hk0 : (-1 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 1 := by exact_mod_cast hk1
      have : k = 0 := by omega
      subst this
      right; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma tan_iff7 {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    tan θ = tan a ↔ ∃ k : ℤ, θ = a + π * k := by
  constructor
  · intro h
    have ha : tan a ≠ 0 := by rw [tan_eq_sin_div_cos]; exact div_ne_zero hs hc
    have hθ : cos θ ≠ 0 := fun h0 => ha (h ▸ tan_eq_zero_of_cos_eq_zero h0)
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hθ hc] at h
    have : sin (θ - a) = 0 := by rw [sin_sub]; linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp this
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [mul_comm]; exact tan_add_int_mul_pi a k

/-- Stitz-Zeager Exercise 10.7.2: `cos 3x = 1/2` exactly when `x = π/9 + 2πk/3` or
`x = 5π/9 + 2πk/3` for an integer `k`. -/
@[kb "stitzzeager2013" "Exercise 10.7.2, p. 886"]
theorem exer_10_7_2 (x : ℝ) :
    cos (3 * x) = 1 / 2 ↔
      ∃ k : ℤ, x = π / 9 + 2 * π * k / 3 ∨ x = 5 * π / 9 + 2 * π * k / 3 := by
  have key : cos (3 * x) = 1 / 2 ↔ cos (π / 3) = cos (3 * x) := by
    rw [cos_pi_div_three]; exact eq_comm
  rw [key, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k - 1, Or.inr (by push_cast; linarith)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k + 1, Or.inr (by push_cast; linarith)⟩

/-- Stitz-Zeager Exercise 10.7.5: `csc 4x = -1` exactly when `x = 3π/8 + πk/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.5, p. 886"]
theorem exer_10_7_5 (x : ℝ) : (sin (4 * x))⁻¹ = -1 ↔ ∃ k : ℤ, x = 3 * π / 8 + π * k / 2 := by
  rw [inv_eq_iff_eq_inv, inv_neg, inv_one, sin_eq_neg_one_iff]
  constructor
  · rintro ⟨k, h⟩; exact ⟨k - 1, by push_cast; linarith⟩
  · rintro ⟨k, h⟩; exact ⟨k + 1, by push_cast; linarith⟩

/-- Stitz-Zeager Exercise 10.7.7: `cot 2x = -√3/3` exactly when `x = π/3 + πk/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.7, p. 886"]
theorem exer_10_7_7 (x : ℝ) :
    cos (2 * x) / sin (2 * x) = -(√3 / 3) ↔ ∃ k : ℤ, x = π / 3 + π * k / 2 := by
  have hp : 0 < √3 := by positivity
  have s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : cos (2 * x) / sin (2 * x) = (tan (2 * x))⁻¹ := by rw [tan_eq_sin_div_cos, inv_div]
  have hc : cos (-(π / 3)) ≠ 0 := by rw [cos_neg, cos_pi_div_three]; norm_num
  have hs : sin (-(π / 3)) ≠ 0 := by rw [sin_neg, sin_pi_div_three]; simp
  have ht : tan (-(π / 3)) = -√3 := by rw [tan_neg, tan_pi_div_three]
  have hv : (-(√3 / 3))⁻¹ = -√3 := by field_simp; nlinarith [s3]
  rw [e, inv_eq_iff_eq_inv, hv, ← ht, tan_iff7 hc hs]
  constructor
  · rintro ⟨k, h⟩; exact ⟨k - 1, by push_cast; linarith⟩
  · rintro ⟨k, h⟩; exact ⟨k + 1, by push_cast; linarith⟩

/-- Stitz-Zeager Exercise 10.7.8: `cos 9x = 9` has no solution. -/
@[kb "stitzzeager2013" "Exercise 10.7.8, p. 886"]
theorem exer_10_7_8 : ¬ ∃ x : ℝ, cos (9 * x) = 9 := by
  rintro ⟨x, h⟩
  have := cos_le_one (9 * x)
  linarith

/-- Stitz-Zeager Exercise 10.7.9: `sin(x/3) = √2/2` exactly when `x = 3π/4 + 6πk` or
`x = 9π/4 + 6πk`; the only solution in `[0, 2π)` is `3π/4` is shown by the first part with `k = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.7.9, p. 886"]
theorem exer_10_7_9 (x : ℝ) :
    sin (x / 3) = √2 / 2 ↔ ∃ k : ℤ, x = 3 * π / 4 + 6 * π * k ∨ x = 9 * π / 4 + 6 * π * k := by
  have key : sin (x / 3) = √2 / 2 ↔ sin (π / 4) = sin (x / 3) := by
    rw [sin_pi_div_four]; exact eq_comm
  rw [key, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩

/-- Stitz-Zeager Exercise 10.7.10: `cos(x + 5π/6) = 0` exactly when `x = -π/3 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.7.10, p. 886"]
theorem exer_10_7_10 (x : ℝ) : cos (x + 5 * π / 6) = 0 ↔ ∃ k : ℤ, x = -(π / 3) + π * k := by
  rw [cos_eq_zero_iff]
  constructor
  · rintro ⟨k, h⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, h⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.13: `csc x = 0` has no solution (`csc x` is defined only where
`sin x ≠ 0`, and then `1/sin x ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 10.7.13, p. 886"]
theorem exer_10_7_13 : ¬ ∃ x : ℝ, sin x ≠ 0 ∧ (sin x)⁻¹ = 0 := by
  rintro ⟨x, hs, h⟩
  exact hs (inv_eq_zero.mp h)

/-- Stitz-Zeager Exercise 10.7.15: `tan² x = 3` exactly when `x = π/3 + πk` or `x = 2π/3 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.7.15, p. 886"]
theorem exer_10_7_15 (x : ℝ) :
    tan x ^ 2 = 3 ↔ ∃ k : ℤ, x = π / 3 + π * k ∨ x = 2 * π / 3 + π * k := by
  have s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  have h1 : tan x ^ 2 = 3 ↔ tan x = tan (π / 3) ∨ tan x = tan (-(π / 3)) := by
    rw [tan_neg, tan_pi_div_three]
    constructor
    · intro h
      have : (tan x - √3) * (tan x + √3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] <;> nlinarith
  have hc1 : cos (π / 3) ≠ 0 := by rw [cos_pi_div_three]; norm_num
  have hs1 : sin (π / 3) ≠ 0 := by rw [sin_pi_div_three]; positivity
  have hc2 : cos (-(π / 3)) ≠ 0 := by rw [cos_neg]; exact hc1
  have hs2 : sin (-(π / 3)) ≠ 0 := by rw [sin_neg]; exact neg_ne_zero.mpr hs1
  rw [h1, tan_iff7 hc1 hs1, tan_iff7 hc2 hs2]
  constructor
  · rintro (⟨k, h⟩ | ⟨k, h⟩)
    · exact ⟨k, Or.inl h⟩
    · exact ⟨k - 1, Or.inr (by push_cast; linarith)⟩
  · rintro ⟨k, h | h⟩
    · exact Or.inl ⟨k, h⟩
    · exact Or.inr ⟨k + 1, by push_cast; linarith⟩

/-- Stitz-Zeager Exercise 10.7.17: `cos² x = 1/2` exactly when `x = π/4 + πk/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.17, p. 886"]
theorem exer_10_7_17 (x : ℝ) : cos x ^ 2 = 1 / 2 ↔ ∃ k : ℤ, x = π / 4 + π * k / 2 := by
  have h : cos x ^ 2 = 1 / 2 ↔ cos (2 * x) = 0 := by
    rw [cos_two_mul]; constructor <;> intro h <;> linarith
  rw [h, cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.19: on `[0, 2π)`, `sin x = cos x` exactly when `x = π/4` or `x = 5π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.7.19, p. 886"]
theorem exer_10_7_19 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = cos x ↔ x = π / 4 ∨ x = 5 * π / 4 := by
  have hpi := Real.pi_pos
  have h2 : 0 < √2 := by positivity
  have e : sin x = cos x ↔ sin (x - π / 4) = 0 := by
    rw [sin_sub, cos_pi_div_four, sin_pi_div_four]
    constructor
    · intro h; rw [h]; ring
    · intro h
      have : √2 / 2 * (sin x - cos x) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · linarith
  rw [e, sin_eq_zero_iff]
  constructor
  · rintro ⟨n, h⟩
    have hk0 : (-1 : ℝ) < n := by nlinarith
    have hk1 : (n : ℝ) < 2 := by nlinarith
    have h1 : (-1 : ℤ) < n := by exact_mod_cast hk0
    have h2 : n < 2 := by exact_mod_cast hk1
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · left; simp at h; linarith
    · right; simp at h; linarith
  · rintro (h | h)
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; simp; ring⟩

/-- Stitz-Zeager Exercise 10.7.20: on `[0, 2π)`, `sin 2x = sin x` exactly when `x ∈ {0, π/3, π, 5π/3}`. -/
@[kb "stitzzeager2013" "Exercise 10.7.20, p. 886"]
theorem exer_10_7_20 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin (2 * x) = sin x ↔ x = 0 ∨ x = π / 3 ∨ x = π ∨ x = 5 * π / 3 := by
  have e : sin (2 * x) = sin x ↔ sin x = 0 ∨ cos x = 1 / 2 := by
    rw [sin_two_mul]
    constructor
    · intro h
      have : sin x * (2 * cos x - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h]; ring
      · ring
  rw [e, sin_zero7 x hx0 hx1, cos_half7 x hx0 hx1]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

/-- Stitz-Zeager Exercise 10.7.23: on `[0, 2π)`, `cos 2x = cos x` exactly when `x ∈ {0, 2π/3, 4π/3}`. -/
@[kb "stitzzeager2013" "Exercise 10.7.23, p. 886"]
theorem exer_10_7_23 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (2 * x) = cos x ↔ x = 0 ∨ x = 2 * π / 3 ∨ x = 4 * π / 3 := by
  have e : cos (2 * x) = cos x ↔ cos x = 1 ∨ cos x = -(1 / 2) := by
    rw [cos_two_mul]
    constructor
    · intro h
      have : (cos x - 1) * (2 * cos x + 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] <;> norm_num
  rw [e, cos_one7 x hx0 hx1, cos_mhalf7 x hx0 hx1]

/-- Stitz-Zeager Exercise 10.7.24: on `[0, 2π)`, `cos 2x = 2 - 5 cos x` exactly when
`x = π/3` or `x = 5π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.24, p. 886"]
theorem exer_10_7_24 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (2 * x) = 2 - 5 * cos x ↔ x = π / 3 ∨ x = 5 * π / 3 := by
  have e : cos (2 * x) = 2 - 5 * cos x ↔ cos x = 1 / 2 := by
    rw [cos_two_mul]
    have h1 := neg_one_le_cos x
    constructor
    · intro h
      have : (2 * cos x - 1) * (cos x + 3) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · intro h; rw [h]; norm_num
  rw [e, cos_half7 x hx0 hx1]

/-- Stitz-Zeager Exercise 10.7.26: on `[0, 2π)`, `cos 2x = 5 sin x - 2` exactly when
`x = π/6` or `x = 5π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.26, p. 886"]
theorem exer_10_7_26 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (2 * x) = 5 * sin x - 2 ↔ x = π / 6 ∨ x = 5 * π / 6 := by
  have e : cos (2 * x) = 5 * sin x - 2 ↔ sin x = 1 / 2 := by
    have h1 := neg_one_le_sin x
    have h2 := sin_sq_add_cos_sq x
    have h3 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by rw [cos_two_mul]; nlinarith
    rw [h3]
    constructor
    · intro h
      have : (2 * sin x - 1) * (sin x + 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · intro h; rw [h]; norm_num
  rw [e, sin_half7 x hx0 hx1]

/-- Stitz-Zeager Exercise 10.7.59: for `-1 ≤ 2x ≤ 1`, `arccos(2x) = π` exactly when `x = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.59, p. 887"]
theorem exer_10_7_59 (x : ℝ) (hx : -1 ≤ 2 * x ∧ 2 * x ≤ 1) : arccos (2 * x) = π ↔ x = -(1 / 2) := by
  rw [arccos_eq_pi]
  constructor
  · intro h; linarith [hx.1]
  · intro h; rw [h]; norm_num

/-- Stitz-Zeager Exercise 10.7.60: for `-1 ≤ x ≤ 1`, `π - 2 arcsin x = 2π` exactly when `x = -1`. -/
@[kb "stitzzeager2013" "Exercise 10.7.60, p. 887"]
theorem exer_10_7_60 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : π - 2 * arcsin x = 2 * π ↔ x = -1 := by
  have e : π - 2 * arcsin x = 2 * π ↔ arcsin x = -(π / 2) := by
    constructor <;> intro h <;> linarith
  rw [e, arcsin_eq_neg_pi_div_two]
  constructor
  · intro h; linarith [hx.1]
  · intro h; rw [h]

/-- Stitz-Zeager Exercise 10.7.61: `4 arctan(3x - 1) - π = 0` exactly when `x = 2/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.61, p. 887"]
theorem exer_10_7_61 (x : ℝ) : 4 * arctan (3 * x - 1) - π = 0 ↔ x = 2 / 3 := by
  have e : 4 * arctan (3 * x - 1) - π = 0 ↔ arctan (3 * x - 1) = arctan 1 := by
    rw [arctan_one]; constructor <;> intro h <;> linarith
  rw [e]
  constructor
  · intro h; have := arctan_injective h; linarith
  · intro h; rw [h]; norm_num

/-- Stitz-Zeager Exercise 10.7.62: `6 arccot(2x) - 5π = 0` exactly when `x = -√3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.62, p. 887"]
theorem exer_10_7_62 (x : ℝ) : 6 * arccotR (2 * x) - 5 * π = 0 ↔ x = -(√3 / 2) := by
  unfold arccotR
  have e : 6 * (π / 2 - arctan (2 * x)) - 5 * π = 0 ↔ arctan (2 * x) = arctan (-√3) := by
    have : arctan (-√3) = -(π / 3) := by
      rw [arctan_neg, show √3 = tan (π / 3) from tan_pi_div_three.symm,
        arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    rw [this]; constructor <;> intro h <;> linarith
  rw [e]
  constructor
  · intro h; have := arctan_injective h; linarith
  · intro h; rw [h]; ring_nf

/-- Stitz-Zeager Exercise 10.7.65: for `-1 ≤ x ≤ 1`, `9 arcsin² x - π² = 0` exactly when
`x = √3/2` or `x = -√3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.65, p. 887"]
theorem exer_10_7_65 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    9 * arcsin x ^ 2 - π ^ 2 = 0 ↔ x = √3 / 2 ∨ x = -(√3 / 2) := by
  have hpi := Real.pi_pos
  have h3 : arcsin (√3 / 2) = π / 3 := by
    rw [← sin_pi_div_three]; exact arcsin_sin (by linarith) (by linarith)
  constructor
  · intro h
    have : (3 * arcsin x - π) * (3 * arcsin x + π) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left
      have : arcsin x = π / 3 := by linarith
      rw [← sin_arcsin hx.1 hx.2, this, sin_pi_div_three]
    · right
      have : arcsin x = -(π / 3) := by linarith
      rw [← sin_arcsin hx.1 hx.2, this, sin_neg, sin_pi_div_three]
  · rintro (h | h)
    · rw [h, h3]; ring
    · rw [h, arcsin_neg, h3]; ring

/-- Stitz-Zeager Exercise 10.7.66: for `-1 ≤ x ≤ 1`, `9 arccos² x - π² = 0` exactly when `x = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.66, p. 887"]
theorem exer_10_7_66 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : 9 * arccos x ^ 2 - π ^ 2 = 0 ↔ x = 1 / 2 := by
  have hpi := Real.pi_pos
  have h3 : arccos (1 / 2) = π / 3 := by
    rw [← cos_pi_div_three]; exact arccos_cos (by linarith) (by linarith)
  have h0 := arccos_nonneg x
  constructor
  · intro h
    have : (3 * arccos x - π) * (3 * arccos x + π) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · have : arccos x = π / 3 := by linarith
      rw [← cos_arccos hx.1 hx.2, this, cos_pi_div_three]
    · linarith
  · intro h; rw [h, h3]; ring

/-- Stitz-Zeager Exercise 10.7.67: `8 arccot² x + 3π² = 10π arccot x` exactly when `x = -1` or `x = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.7.67, p. 887"]
theorem exer_10_7_67 (x : ℝ) :
    8 * arccotR x ^ 2 + 3 * π ^ 2 = 10 * π * arccotR x ↔ x = -1 ∨ x = 0 := by
  unfold arccotR
  have e : 8 * (π / 2 - arctan x) ^ 2 + 3 * π ^ 2 = 10 * π * (π / 2 - arctan x) ↔
      arctan x * (4 * arctan x + π) = 0 := by
    constructor <;> intro h <;> nlinarith
  rw [e]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · right; exact arctan_eq_zero_iff.mp h
    · left
      have : arctan x = arctan (-1) := by rw [arctan_neg, arctan_one]; linarith
      exact arctan_injective this
  · rintro (h | h)
    · rw [h, arctan_neg, arctan_one]; ring
    · rw [h, arctan_zero]; ring

/-- Stitz-Zeager Exercise 10.7.68: `6 arctan² x = π arctan x + π²` exactly when `x = -√3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.68, p. 887"]
theorem exer_10_7_68 (x : ℝ) : 6 * arctan x ^ 2 = π * arctan x + π ^ 2 ↔ x = -√3 := by
  have hpi := Real.pi_pos
  have h3 : arctan (-√3) = -(π / 3) := by
    rw [arctan_neg, show √3 = tan (π / 3) from tan_pi_div_three.symm,
      arctan_tan (by linarith) (by linarith)]
  have hlt := arctan_lt_pi_div_two x
  constructor
  · intro h
    have : (3 * arctan x + π) * (2 * arctan x - π) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · have : arctan x = arctan (-√3) := by rw [h3]; linarith
      exact arctan_injective this
    · linarith
  · intro h; rw [h, h3]; ring

/-- Stitz-Zeager Exercise 10.7.69: for `0 ≤ x ≤ 2π`, `sin x ≤ 0` exactly when `x = 0` or `π ≤ x`.
ERRATUM: the book's answer `[π, 2π]` omits `x = 0`, where `sin 0 = 0 ≤ 0`. -/
@[kb "stitzzeager2013" "Exercise 10.7.69, p. 887"]
theorem exer_10_7_69 (x : ℝ) (hx : x ∈ Set.Icc 0 (2 * π)) : sin x ≤ 0 ↔ x = 0 ∨ π ≤ x := by
  have hpi := Real.pi_pos
  obtain ⟨hx0, hx1⟩ := hx
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hc.1)
    have := sin_pos_of_pos_of_lt_pi hx0' hc.2
    linarith
  · rintro (h | h)
    · rw [h]; simp
    · have e : sin x = -sin (x - π) := by rw [sin_sub_pi]; ring
      rcases eq_or_lt_of_le hx1 with h2 | h2
      · rw [h2, sin_two_pi]
      · rcases eq_or_lt_of_le h with h3 | h3
        · rw [← h3, sin_pi]
        · have := sin_pos_of_pos_of_lt_pi (x := x - π) (by linarith) (by linarith)
          linarith

/-- Stitz-Zeager Exercise 10.7.76: for `0 ≤ x ≤ 2π`, `2 cos x ≥ 1` exactly when `x ≤ π/3` or
`5π/3 ≤ x`. -/
@[kb "stitzzeager2013" "Exercise 10.7.76, p. 887"]
theorem exer_10_7_76 (x : ℝ) (hx : x ∈ Set.Icc 0 (2 * π)) : 2 * cos x ≥ 1 ↔ x ≤ π / 3 ∨ 5 * π / 3 ≤ x := by
  have hpi := Real.pi_pos
  obtain ⟨hx0, hx1⟩ := hx
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    by_cases hxp : x ≤ π
    · have := cos_lt_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ π / 3) hxp h1
      rw [cos_pi_div_three] at this
      linarith
    · have e : cos x = cos (2 * π - x) := by rw [cos_two_pi_sub]
      have := cos_lt_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ π / 3) (by linarith : 2 * π - x ≤ π)
        (by linarith : π / 3 < 2 * π - x)
      rw [cos_pi_div_three, ← e] at this
      linarith
  · rintro (h | h)
    · have := cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith : π / 3 ≤ π) h
      rw [cos_pi_div_three] at this
      linarith
    · have e : cos x = cos (2 * π - x) := by rw [cos_two_pi_sub]
      have := cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ 2 * π - x) (by linarith : π / 3 ≤ π)
        (by linarith : 2 * π - x ≤ π / 3)
      rw [cos_pi_div_three] at this
      linarith

/-- Stitz-Zeager Exercise 10.7.77: `sin 5x ≥ 5` has no solution. -/
@[kb "stitzzeager2013" "Exercise 10.7.77, p. 887"]
theorem exer_10_7_77 : ¬ ∃ x : ℝ, sin (5 * x) ≥ 5 := by
  rintro ⟨x, h⟩
  have := sin_le_one (5 * x)
  linarith

/-- Stitz-Zeager Exercise 10.7.78: `cos 3x ≤ 1` holds for every `x`, so the solution set in
`[0, 2π]` is the whole interval. -/
@[kb "stitzzeager2013" "Exercise 10.7.78, p. 887"]
theorem exer_10_7_78 : {x : ℝ | x ∈ Set.Icc 0 (2 * π) ∧ cos (3 * x) ≤ 1} = Set.Icc 0 (2 * π) := by
  ext x
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, cos_le_one _⟩

/-- Stitz-Zeager Exercise 10.7.94: for `-1 ≤ x ≤ 1`, `3 arccos x ≤ π` exactly when `1/2 ≤ x`. -/
@[kb "stitzzeager2013" "Exercise 10.7.94, p. 888"]
theorem exer_10_7_94 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : 3 * arccos x ≤ π ↔ 1 / 2 ≤ x := by
  have hpi := Real.pi_pos
  have h0 := arccos_nonneg x
  have h1 := arccos_le_pi x
  have hc := cos_arccos hx.1 hx.2
  constructor
  · intro h
    have := cos_le_cos_of_nonneg_of_le_pi h0 (by linarith : π / 3 ≤ π) (by linarith : arccos x ≤ π / 3)
    rw [hc, cos_pi_div_three] at this
    linarith [this]
  · intro h
    by_contra hcn
    push Not at hcn
    have := cos_lt_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ π / 3) h1 (by linarith : π / 3 < arccos x)
    rw [hc, cos_pi_div_three] at this
    linarith

/-- Stitz-Zeager Exercise 10.7.97: for `-1 ≤ x ≤ 1`, `2 arcsin² x > π arcsin x` exactly when `x < 0`. -/
@[kb "stitzzeager2013" "Exercise 10.7.97, p. 888"]
theorem exer_10_7_97 (x : ℝ) (_hx : -1 ≤ x ∧ x ≤ 1) : 2 * arcsin x ^ 2 > π * arcsin x ↔ x < 0 := by
  have hpi := Real.pi_pos
  have hle := arcsin_le_pi_div_two x
  rw [← arcsin_lt_zero]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

end UndergradKB.Precalculus.Course
