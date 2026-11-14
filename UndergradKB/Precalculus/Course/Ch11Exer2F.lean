import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.7 (part 1)

We write `⟨x, y⟩` for `x + y i`, and `r cis θ` as `r * exp (θ * I)`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false

/-! ## Helpers -/

private theorem w7_arg {x y r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioc (-π) π)
    (hx : x = r * cos θ) (hy : y = r * sin θ) :
    Complex.arg ⟨x, y⟩ = θ ∧ ‖(⟨x, y⟩ : ℂ)‖ = r := by
  have h : (⟨x, y⟩ : ℂ) = (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, hx, hy]
  refine ⟨by rw [h]; exact Complex.arg_mul_cos_add_sin_mul_I hr hθ, ?_⟩
  rw [Complex.norm_def, Complex.normSq_mk, hx, hy]
  rw [show r * cos θ * (r * cos θ) + r * sin θ * (r * sin θ) = r ^ 2 by
    nlinarith [sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq hr.le

private theorem w7_cis {r θ x y : ℝ} (hx : r * cos θ = x) (hy : r * sin θ = y) :
    ((r : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I) = ⟨x, y⟩ := by
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; exact hx
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]; exact hy

private theorem w7_s (n : ℕ) (hn : 0 < n) : √(n : ℝ) * √(n : ℝ) = n :=
  Real.mul_self_sqrt (by positivity)

/-! ## Section 11.7: polar representations -/

/-- Stitz-Zeager Exercise 11.7.3: `z = 6i` has `|z| = 6` and `Arg z = π/2`. -/
@[kb "stitzzeager2013" "Exercise 11.7.3, p. 1016"]
theorem exer_11_7_3 : ‖(⟨0, 6⟩ : ℂ)‖ = 6 ∧ Complex.arg ⟨0, 6⟩ = π / 2 := by
  have hp := pi_pos
  have := w7_arg (x := 0) (y := 6) (r := 6) (θ := π / 2) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_pi_div_two]; ring) (by rw [sin_pi_div_two]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.4: `z = -3√2 + 3√2 i` has `|z| = 6` and `Arg z = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 11.7.4, p. 1016"]
theorem exer_11_7_4 : ‖(⟨-(3 * √2), 3 * √2⟩ : ℂ)‖ = 6 ∧ Complex.arg ⟨-(3 * √2), 3 * √2⟩ = 3 * π / 4 := by
  have hp := pi_pos
  have e : 3 * π / 4 = π - π / 4 := by ring
  have := w7_arg (x := -(3 * √2)) (y := 3 * √2) (r := 6) (θ := 3 * π / 4) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [e, cos_pi_sub, cos_pi_div_four]; ring)
    (by rw [e, sin_pi_sub, sin_pi_div_four]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.6: `z = -2` has `|z| = 2` and `Arg z = π`. -/
@[kb "stitzzeager2013" "Exercise 11.7.6, p. 1016"]
theorem exer_11_7_6 : ‖(⟨-2, 0⟩ : ℂ)‖ = 2 ∧ Complex.arg ⟨-2, 0⟩ = π := by
  have hp := pi_pos
  have := w7_arg (x := -2) (y := 0) (r := 2) (θ := π) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_pi]; ring) (by rw [sin_pi]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.9: `z = -5i` has `|z| = 5` and `Arg z = -π/2`. -/
@[kb "stitzzeager2013" "Exercise 11.7.9, p. 1016"]
theorem exer_11_7_9 : ‖(⟨0, -5⟩ : ℂ)‖ = 5 ∧ Complex.arg ⟨0, -5⟩ = -(π / 2) := by
  have hp := pi_pos
  have := w7_arg (x := 0) (y := -5) (r := 5) (θ := -(π / 2)) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_neg, cos_pi_div_two]; ring)
    (by rw [sin_neg, sin_pi_div_two]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.10: `z = 2√2 - 2√2 i` has `|z| = 4` and `Arg z = -π/4`. -/
@[kb "stitzzeager2013" "Exercise 11.7.10, p. 1016"]
theorem exer_11_7_10 : ‖(⟨2 * √2, -(2 * √2)⟩ : ℂ)‖ = 4 ∧ Complex.arg ⟨2 * √2, -(2 * √2)⟩ = -(π / 4) := by
  have hp := pi_pos
  have := w7_arg (x := 2 * √2) (y := -(2 * √2)) (r := 4) (θ := -(π / 4)) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_neg, cos_pi_div_four]; ring)
    (by rw [sin_neg, sin_pi_div_four]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.11: `z = 6` has `|z| = 6` and `Arg z = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.7.11, p. 1016"]
theorem exer_11_7_11 : ‖(⟨6, 0⟩ : ℂ)‖ = 6 ∧ Complex.arg ⟨6, 0⟩ = 0 := by
  have hp := pi_pos
  have := w7_arg (x := 6) (y := 0) (r := 6) (θ := 0) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_zero]; ring) (by rw [sin_zero]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.12: `z = i ∛7` has `|z| = ∛7` and `Arg z = π/2`. -/
@[kb "stitzzeager2013" "Exercise 11.7.12, p. 1016"]
theorem exer_11_7_12 :
    ‖(⟨0, (7 : ℝ) ^ (1 / 3 : ℝ)⟩ : ℂ)‖ = (7 : ℝ) ^ (1 / 3 : ℝ) ∧
      Complex.arg ⟨0, (7 : ℝ) ^ (1 / 3 : ℝ)⟩ = π / 2 := by
  have hp := pi_pos
  have hr : 0 < (7 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have := w7_arg (x := 0) (y := (7 : ℝ) ^ (1 / 3 : ℝ)) (r := (7 : ℝ) ^ (1 / 3 : ℝ)) (θ := π / 2) hr
    ⟨by linarith, by linarith⟩ (by rw [cos_pi_div_two]; ring) (by rw [sin_pi_div_two]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.14: `z = √2 + i` has `|z| = √3` and `Arg z = arctan (√2/2)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.14, p. 1016"]
theorem exer_11_7_14 :
    ‖(⟨√2, 1⟩ : ℂ)‖ = √3 ∧ Complex.arg ⟨√2, 1⟩ = arctan (√2 / 2) := by
  have hp := pi_pos
  have h2 := w7_s 2 (by norm_num)
  have h3 := w7_s 3 (by norm_num)
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  push_cast at h2 h3
  have s2 : 0 < √2 := by positivity
  have s3 : 0 < √3 := by positivity
  have h5 : √(1 + (√2 / 2) ^ 2) = √3 / √2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    nlinarith
  have ha := arctan_lt_pi_div_two (√2 / 2)
  have hb := neg_pi_div_two_lt_arctan (√2 / 2)
  have := w7_arg (x := √2) (y := 1) (r := √3) (θ := arctan (√2 / 2)) s3
    ⟨by linarith, by linarith⟩ (by rw [cos_arctan, h5]; field_simp <;> nlinarith)
    (by rw [sin_arctan, h5]; field_simp <;> nlinarith)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.16: `z = -2 + 6i` has `|z| = 2√10` and `Arg z = π - arctan 3`. -/
@[kb "stitzzeager2013" "Exercise 11.7.16, p. 1016"]
theorem exer_11_7_16 :
    ‖(⟨-2, 6⟩ : ℂ)‖ = 2 * √10 ∧ Complex.arg ⟨-2, 6⟩ = π - arctan 3 := by
  have hp := pi_pos
  have h10 := w7_s 10 (by norm_num)
  push_cast at h10
  have s : 0 < √10 := by positivity
  have h5 : √(1 + (3 : ℝ) ^ 2) = √10 := by norm_num
  have ha := arctan_lt_pi_div_two 3
  have hb : 0 < arctan 3 := arctan_pos.2 (by norm_num)
  have := w7_arg (x := -2) (y := 6) (r := 2 * √10) (θ := π - arctan 3) (by positivity)
    ⟨by linarith, by linarith⟩ (by rw [cos_pi_sub, cos_arctan, h5]; field_simp <;> nlinarith)
    (by rw [sin_pi_sub, sin_arctan, h5]; field_simp <;> nlinarith)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.18: `z = -5 - 2i` has `|z| = √29` and `Arg z = arctan (2/5) - π`. -/
@[kb "stitzzeager2013" "Exercise 11.7.18, p. 1016"]
theorem exer_11_7_18 :
    ‖(⟨-5, -2⟩ : ℂ)‖ = √29 ∧ Complex.arg ⟨-5, -2⟩ = arctan (2 / 5) - π := by
  have hp := pi_pos
  have h29 := w7_s 29 (by norm_num)
  push_cast at h29
  have s : 0 < √29 := by positivity
  have h5 : √(1 + (2 / 5 : ℝ) ^ 2) = √29 / 5 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    nlinarith
  have ha := arctan_lt_pi_div_two (2 / 5)
  have hb : 0 < arctan (2 / 5) := arctan_pos.2 (by norm_num)
  have := w7_arg (x := -5) (y := -2) (r := √29) (θ := arctan (2 / 5) - π) s
    ⟨by linarith, by linarith⟩ (by rw [cos_sub_pi, cos_arctan, h5]; field_simp <;> nlinarith)
    (by rw [sin_sub_pi, sin_arctan, h5]; field_simp <;> nlinarith)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.19: `z = 4 - 2i` has `|z| = 2√5` and `Arg z = arctan (-1/2)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.19, p. 1016"]
theorem exer_11_7_19 :
    ‖(⟨4, -2⟩ : ℂ)‖ = 2 * √5 ∧ Complex.arg ⟨4, -2⟩ = arctan (-(1 / 2)) := by
  have hp := pi_pos
  have h5 := w7_s 5 (by norm_num)
  push_cast at h5
  have s : 0 < √5 := by positivity
  have h5' : √(1 + (-(1 / 2) : ℝ) ^ 2) = √5 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    nlinarith
  have ha := arctan_lt_pi_div_two (-(1 / 2))
  have hb := neg_pi_div_two_lt_arctan (-(1 / 2))
  have := w7_arg (x := 4) (y := -2) (r := 2 * √5) (θ := arctan (-(1 / 2))) (by positivity)
    ⟨by linarith, by linarith⟩ (by rw [cos_arctan, h5']; field_simp <;> nlinarith)
    (by rw [sin_arctan, h5']; field_simp <;> nlinarith)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.20: `z = 1 - 3i` has `|z| = √10` and `Arg z = arctan (-3)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.20, p. 1016"]
theorem exer_11_7_20 :
    ‖(⟨1, -3⟩ : ℂ)‖ = √10 ∧ Complex.arg ⟨1, -3⟩ = arctan (-3) := by
  have hp := pi_pos
  have h10 := w7_s 10 (by norm_num)
  push_cast at h10
  have s : 0 < √10 := by positivity
  have h5 : √(1 + (-3 : ℝ) ^ 2) = √10 := by norm_num
  have ha := arctan_lt_pi_div_two (-3)
  have hb := neg_pi_div_two_lt_arctan (-3)
  have := w7_arg (x := 1) (y := -3) (r := √10) (θ := arctan (-3)) s
    ⟨by linarith, by linarith⟩ (by rw [cos_arctan, h5]; field_simp <;> nlinarith)
    (by rw [sin_arctan, h5]; field_simp <;> nlinarith)
  exact ⟨this.2, this.1⟩

end UndergradKB.Precalculus.Course
