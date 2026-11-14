import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 11.5 (more polar regions) -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Every point of the plane has polar coordinates `r ≥ 0`, `θ ∈ (-π, π]`. -/
theorem ch11e3f_polar (x y : ℝ) : ∃ r θ : ℝ, 0 ≤ r ∧ r ^ 2 = x ^ 2 + y ^ 2 ∧ -π < θ ∧ θ ≤ π ∧
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

/-- Stitz-Zeager Exercise 11.5.42: the part of the disk `r ≤ 5` in Quadrant III is
`{x² + y² ≤ 25, x ≤ 0, y ≤ 0}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.42, p. 971"]
theorem exer_11_5_42 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 5 ∧ π ≤ θ ∧ θ ≤ 3 * π / 2 ∧
      p = (r * cos θ, r * sin θ)} =
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 25 ∧ p.1 ≤ 0 ∧ p.2 ≤ 0} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  constructor
  · rintro ⟨r, θ, hr0, hr5, h1, h2, rfl, rfl⟩
    have hc : cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    have hs' : 0 ≤ sin (θ - π) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hs'
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    refine ⟨?_, by nlinarith [mul_nonneg hr0 (neg_nonneg.mpr hc)],
      by nlinarith [mul_nonneg hr0 hs']⟩
    rw [e]; nlinarith
  · rintro ⟨h1, hx0, hy0⟩
    obtain ⟨r, θ, hr, hr2, ht1, ht2, hx, hy⟩ := ch11e3f_polar x y
    have hr5 : r ≤ 5 := by nlinarith
    by_cases hr0 : r = 0
    · refine ⟨0, π, le_refl _, by norm_num, le_refl _, by linarith, ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hcos : cos θ ≤ 0 := by
        by_contra hneg
        have hneg' : 0 < cos θ := lt_of_not_ge hneg
        nlinarith
      have hsin : sin θ ≤ 0 := by
        by_contra hneg
        have hneg' : 0 < sin θ := lt_of_not_ge hneg
        nlinarith
      by_cases hθ : 0 < θ
      · have hθπ : θ = π := by
          by_contra hne
          have hlt : θ < π := lt_of_le_of_ne ht2 hne
          have := Real.sin_pos_of_pos_of_lt_pi hθ hlt
          linarith
        subst hθπ
        exact ⟨r, π, hr, hr5, le_refl _, by linarith, hx, hy⟩
      · have hθ0 : θ ≤ 0 := not_lt.mp hθ
        have hθ1 : θ ≤ -(π / 2) := by
          by_contra hneg
          have hneg' : -(π / 2) < θ := lt_of_not_ge hneg
          have := Real.cos_pos_of_mem_Ioo ⟨hneg', by linarith⟩
          linarith
        refine ⟨r, θ + 2 * π, hr, hr5, by linarith, by linarith, ?_, ?_⟩
        · rw [Real.cos_add_two_pi]; exact hx
        · rw [Real.sin_add_two_pi]; exact hy

/-- Stitz-Zeager Exercise 11.5.44: the part of the disk inside `r = 4 cos θ` in Quadrant IV, described with
negative radii: `{4 cos θ ≤ r ≤ 0, π/2 ≤ θ ≤ π}`, is `{x ≥ 0, y ≤ 0, x² + y² ≤ 4x}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.44, p. 971"]
theorem exer_11_5_44 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 4 * cos θ ≤ r ∧ r ≤ 0 ∧ π / 2 ≤ θ ∧ θ ≤ π ∧
      p = (r * cos θ, r * sin θ)} =
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.2 ≤ 0 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ 4 * p.1} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  constructor
  · rintro ⟨r, θ, hr1, hr0, h1, h2, rfl, rfl⟩
    have hc : cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
    have hs' : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h2
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    refine ⟨by nlinarith [mul_nonneg (neg_nonneg.mpr hr0) (neg_nonneg.mpr hc)],
      by nlinarith [mul_nonneg (neg_nonneg.mpr hr0) hs'], ?_⟩
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (neg_nonneg.mpr hr0)]
  · rintro ⟨hx0, hy0, h1⟩
    obtain ⟨r, θ, hr, hr2, ht1, ht2, hx, hy⟩ := ch11e3f_polar x y
    by_cases hr0 : r = 0
    · refine ⟨0, π / 2, by rw [Real.cos_pi_div_two]; norm_num, le_refl _, le_refl _, by linarith,
        ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hcos : 0 ≤ cos θ := by
        by_contra hneg
        have hneg' : cos θ < 0 := lt_of_not_ge hneg
        nlinarith
      have hsin : sin θ ≤ 0 := by
        by_contra hneg
        have hneg' : 0 < sin θ := lt_of_not_ge hneg
        nlinarith
      have hθ0 : θ ≤ 0 := by
        by_contra hneg
        have hpos : 0 < θ := lt_of_not_ge hneg
        have hθπ : θ = π := by
          by_contra hne
          have hlt : θ < π := lt_of_le_of_ne ht2 hne
          have := Real.sin_pos_of_pos_of_lt_pi hpos hlt
          linarith
        rw [hθπ, Real.cos_pi] at hcos
        linarith
      have hθ1 : -(π / 2) ≤ θ := by
        by_contra hneg
        have hneg' : θ < -(π / 2) := lt_of_not_ge hneg
        have := Real.cos_neg_of_pi_div_two_lt_of_lt (x := -θ) (by linarith) (by linarith)
        rw [Real.cos_neg] at this
        linarith
      have hle : r ≤ 4 * cos θ := by
        have : r * r ≤ r * (4 * cos θ) := by nlinarith
        exact le_of_mul_le_mul_left this hrp
      refine ⟨-r, θ + π, ?_, by linarith, by linarith, by linarith, ?_, ?_⟩
      · rw [Real.cos_add_pi]; linarith
      · rw [Real.cos_add_pi, hx]; ring
      · rw [Real.sin_add_pi, hy]; ring

/-- Stitz-Zeager Exercise 11.5.45: the top half of the cardioid `r = 3 - 3 cos θ` (`0 ≤ θ ≤ π`) is
`{y ≥ 0, x² + y² + 3x ≤ 3 √(x² + y²)}`. -/
@[kb "stitzzeager2013" "Exercise 11.5.45, p. 971"]
theorem exer_11_5_45 :
    {p : ℝ × ℝ | ∃ r θ : ℝ, 0 ≤ r ∧ r ≤ 3 - 3 * cos θ ∧ 0 ≤ θ ∧ θ ≤ π ∧
      p = (r * cos θ, r * sin θ)} =
    {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 + 3 * p.1 ≤ 3 * √(p.1 ^ 2 + p.2 ^ 2)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]
  have hp := Real.pi_pos
  constructor
  · rintro ⟨r, θ, hr0, hr1, h1, h2, rfl, rfl⟩
    have hs' : 0 ≤ sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
    have h := Real.sin_sq_add_cos_sq θ
    have e : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
    refine ⟨mul_nonneg hr0 hs', ?_⟩
    rw [e, Real.sqrt_sq hr0]
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  · rintro ⟨hy0, h1⟩
    obtain ⟨r, θ, hr, hr2, ht1, ht2, hx, hy⟩ := ch11e3f_polar x y
    have hsq : √(x ^ 2 + y ^ 2) = r := by rw [← hr2, Real.sqrt_sq hr]
    rw [hsq] at h1
    by_cases hr0 : r = 0
    · refine ⟨0, 0, le_refl _, by simp, le_refl _, hp.le, ?_, ?_⟩
      · rw [hx, hr0]; simp
      · rw [hy, hr0]; simp
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hsin : 0 ≤ sin θ := by
        by_contra hneg
        have hneg' : sin θ < 0 := lt_of_not_ge hneg
        nlinarith
      have hθ0 : 0 ≤ θ := by
        by_contra hneg
        have hneg' : θ < 0 := lt_of_not_ge hneg
        have := Real.sin_neg_of_neg_of_neg_pi_lt hneg' ht1
        linarith
      have hle : r ≤ 3 - 3 * cos θ := by
        have : r * r ≤ r * (3 - 3 * cos θ) := by nlinarith
        exact le_of_mul_le_mul_left this hrp
      exact ⟨r, θ, hr, hle, hθ0, ht2, hx, hy⟩

end UndergradKB.Precalculus.Course
