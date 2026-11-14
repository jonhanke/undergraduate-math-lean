import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 11.5 (regions 46, 47) -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Every point of the plane has polar coordinates `r ≥ 0`, `θ ∈ (-π, π]`. -/
theorem ch11e3g_polar (x y : ℝ) : ∃ r θ : ℝ, 0 ≤ r ∧ r ^ 2 = x ^ 2 + y ^ 2 ∧ -π < θ ∧ θ ≤ π ∧
    x = r * cos θ ∧ y = r * sin θ := by
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨hx, hy⟩ := h
    refine ⟨0, 0, le_refl _, by simp [hx, hy], by linarith [Real.pi_pos], by linarith [Real.pi_pos],
      by simp [hx], by simp [hy]⟩
  · have hz : (⟨x, y⟩ : ℂ) ≠ 0 := by
      intro h0
      apply h
      exact ⟨congrArg Complex.re h0, congrArg Complex.im h0⟩
    have hn : ‖(⟨x, y⟩ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨‖(⟨x, y⟩ : ℂ)‖, Complex.arg ⟨x, y⟩, norm_nonneg _, ?_, Complex.neg_pi_lt_arg _,
      Complex.arg_le_pi _, ?_, ?_⟩
    · rw [Complex.sq_norm, Complex.normSq_apply]
      simp only
      ring
    · rw [Complex.cos_arg hz]
      show x = ‖(⟨x, y⟩ : ℂ)‖ * (x / ‖(⟨x, y⟩ : ℂ)‖)
      field_simp
    · rw [Complex.sin_arg]
      show y = ‖(⟨x, y⟩ : ℂ)‖ * (y / ‖(⟨x, y⟩ : ℂ)‖)
      field_simp

/-- An angle in `[-π, π]` with nonnegative cosine lies in `[-π/2, π/2]`. -/
theorem ch11e3g_cosnn (θ : ℝ) (h1 : -π ≤ θ) (h2 : θ ≤ π) (h : 0 ≤ cos θ) :
    -(π / 2) ≤ θ ∧ θ ≤ π / 2 := by
  have hp := Real.pi_pos
  constructor
  · by_contra hn
    have hlt : θ < -(π / 2) := lt_of_not_ge hn
    have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := -θ) (by linarith) (by linarith)
    rw [Real.cos_neg] at this
    linarith
  · by_contra hn
    have hlt : π / 2 < θ := lt_of_not_ge hn
    have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := θ) hlt (by linarith)
    linarith

/-- An angle in `(-π, π]` with nonnegative sine is nonnegative. -/
theorem ch11e3g_sinnn (θ : ℝ) (h1 : -π < θ) (h : 0 ≤ sin θ) : 0 ≤ θ := by
  by_contra hn
  have hlt : θ < 0 := lt_of_not_ge hn
  have := Real.sin_neg_of_neg_of_neg_pi_lt hlt h1
  linarith

/-- Stitz-Zeager Exercise 11.5.46: the part of the cardioid `r = 2 - 2 sin θ` lying in Quadrants I and IV,
as the union of two angular ranges, is `{x ≥ 0, x² + y² + 2y ≤ 2 √(x² + y²)}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.46, p. 971"]
theorem exer_11_5_46 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 2 - 2 * sin θ ∧
      ((0 ≤ θ ∧ θ ≤ π / 2) ∨ (3 * π / 2 ≤ θ ∧ θ ≤ 2 * π)) ∧ p = (r * cos θ, r * sin θ)} =
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ^ 2 + p.2 ^ 2 + 2 * p.2 ≤ 2 * √(p.1 ^ 2 + p.2 ^ 2)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  constructor
  · rintro ⟨r, θ, hr0, hr1, hθ, rfl, rfl⟩
    have hc : 0 ≤ cos θ := by
      rcases hθ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, h2⟩
      · have := Real.cos_nonneg_of_mem_Icc (x := θ - 2 * π) ⟨by linarith, by linarith⟩
        rwa [Real.cos_sub_two_pi] at this
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    refine ⟨mul_nonneg hr0 hc, ?_⟩
    rw [e, Real.sqrt_sq hr0]
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  · rintro ⟨hx0, h1⟩
    obtain ⟨r, θ, hr, hr2, ht1, ht2, hx, hy⟩ := ch11e3g_polar x y
    have hsq : √(x ^ 2 + y ^ 2) = r := by rw [← hr2, Real.sqrt_sq hr]
    rw [hsq] at h1
    by_cases hr0 : r = 0
    · refine ⟨0, 0, le_refl _, by simp, Or.inl ⟨le_refl _, by linarith⟩, ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hcos : 0 ≤ cos θ := by
        by_contra hneg
        have hneg' : cos θ < 0 := lt_of_not_ge hneg
        nlinarith
      obtain ⟨hb1, hb2⟩ := ch11e3g_cosnn θ ht1.le ht2 hcos
      have hle : r ≤ 2 - 2 * sin θ := by
        have : r * r ≤ r * (2 - 2 * sin θ) := by nlinarith
        exact le_of_mul_le_mul_left this hrp
      by_cases hθ : 0 ≤ θ
      · exact ⟨r, θ, hr, hle, Or.inl ⟨hθ, hb2⟩, hx, hy⟩
      · have hθ' : θ < 0 := lt_of_not_ge hθ
        refine ⟨r, θ + 2 * π, hr, ?_, Or.inr ⟨by linarith, by linarith⟩, ?_, ?_⟩
        · rw [Real.sin_add_two_pi]; exact hle
        · rw [Real.cos_add_two_pi]; exact hx
        · rw [Real.sin_add_two_pi]; exact hy

/-- Stitz-Zeager Exercise 11.5.47: the petal of the rose `r = 3 cos 4θ` on the positive `x`-axis
(`0 ≤ r ≤ 3 cos 4θ`, `-π/8 ≤ θ ≤ π/8`) is `{|y| ≤ x, (x²+y²)^(5/2) ≤ 3 (x⁴ - 6x²y² + y⁴)}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.47, p. 971"]
theorem exer_11_5_47 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 3 * cos (4 * θ) ∧ -(π / 8) ≤ θ ∧ θ ≤ π / 8 ∧
      p = (r * cos θ, r * sin θ)} =
    {p : ℝ × ℝ | |p.2| ≤ p.1 ∧
      √(p.1 ^ 2 + p.2 ^ 2) ^ 5 ≤ 3 * (p.1 ^ 4 - 6 * p.1 ^ 2 * p.2 ^ 2 + p.2 ^ 4)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  have hid : ∀ r θ : ℝ, (r * cos θ) ^ 4 - 6 * (r * cos θ) ^ 2 * (r * sin θ) ^ 2 + (r * sin θ) ^ 4 =
      r ^ 4 * cos (4 * θ) := by
    intro r θ
    have h4 : cos (4 * θ) = 8 * cos θ ^ 4 - 8 * cos θ ^ 2 + 1 := by
      rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul, Real.cos_two_mul]
      ring
    have hs : sin θ ^ 2 = 1 - cos θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    rw [h4]
    linear_combination (r ^ 4 * (sin θ ^ 2 + (1 - cos θ ^ 2) - 6 * cos θ ^ 2)) * hs
  constructor
  · rintro ⟨r, θ, hr0, hr1, h1, h2, rfl, rfl⟩
    have hc : 0 ≤ cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hc2 : 0 ≤ cos (2 * θ) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    rw [Real.cos_two_mul] at hc2
    have hs := Real.sin_sq_add_cos_sq θ
    have hs1 : sin θ ≤ cos θ := by nlinarith
    have hs2 : -cos θ ≤ sin θ := by nlinarith
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * hs
    refine ⟨?_, ?_⟩
    · rw [abs_le]
      constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hs1),
        mul_nonneg hr0 (sub_nonneg.mpr hs2)]
    · rw [e, Real.sqrt_sq hr0, hid]
      nlinarith [mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 4)]
  · rintro ⟨h1, h2⟩
    obtain ⟨r, θ, hr, hr2, ht1, ht2, hx, hy⟩ := ch11e3g_polar x y
    have hsq : √(x ^ 2 + y ^ 2) = r := by rw [← hr2, Real.sqrt_sq hr]
    rw [hsq] at h2
    by_cases hr0 : r = 0
    · refine ⟨0, 0, le_refl _, by simp, by linarith, by linarith, ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hxy := abs_le.mp h1
      have hcos : 0 ≤ cos θ := by
        by_contra hneg
        have hneg' : cos θ < 0 := lt_of_not_ge hneg
        have : r * cos θ < 0 := mul_neg_of_pos_of_neg hrp hneg'
        linarith [abs_nonneg y]
      have hs := Real.sin_sq_add_cos_sq θ
      have hs1 : sin θ ≤ cos θ := by
        by_contra hneg
        have hneg' : cos θ < sin θ := lt_of_not_ge hneg
        nlinarith [mul_pos hrp (sub_pos.2 hneg')]
      have hs2 : -cos θ ≤ sin θ := by
        by_contra hneg
        have hneg' : sin θ < -cos θ := lt_of_not_ge hneg
        nlinarith [mul_pos hrp (sub_pos.2 hneg')]
      obtain ⟨b1, b2⟩ := ch11e3g_cosnn θ ht1.le ht2 hcos
      have hc2 : 0 ≤ cos (2 * θ) := by
        rw [Real.cos_two_mul]
        nlinarith [mul_nonneg (sub_nonneg.2 hs1) (show 0 ≤ cos θ + sin θ by linarith)]
      obtain ⟨c1, c2⟩ := ch11e3g_cosnn (2 * θ) (by linarith) (by linarith) hc2
      rw [hx, hy, hid] at h2
      have hle : r ≤ 3 * cos (4 * θ) := by
        have h5 : r ^ 4 * r ≤ r ^ 4 * (3 * cos (4 * θ)) := by nlinarith
        exact le_of_mul_le_mul_left h5 (by positivity)
      have hc4 : 0 ≤ cos (4 * θ) := by linarith
      obtain ⟨d1, d2⟩ := ch11e3g_cosnn (4 * θ) (by linarith) (by linarith) hc4
      exact ⟨r, θ, hr, hle, by linarith, by linarith, hx, hy⟩

end UndergradKB.Precalculus.Course
