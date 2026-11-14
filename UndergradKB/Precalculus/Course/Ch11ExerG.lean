import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Section 11.7 (polar form of complex numbers). We write `⟨x, y⟩` for `x + y i`, and `r cis θ` as
`r * exp (θ * I)`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false

/-! ## Helpers -/

private theorem x11g_arg {x y r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioc (-π) π)
    (hx : x = r * cos θ) (hy : y = r * sin θ) :
    Complex.arg ⟨x, y⟩ = θ ∧ ‖(⟨x, y⟩ : ℂ)‖ = r := by
  have h : (⟨x, y⟩ : ℂ) = (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, hx, hy]
  refine ⟨by rw [h]; exact Complex.arg_mul_cos_add_sin_mul_I hr hθ, ?_⟩
  rw [Complex.norm_def, Complex.normSq_mk, hx, hy]
  rw [show r * cos θ * (r * cos θ) + r * sin θ * (r * sin θ) = r ^ 2 by
    nlinarith [sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq hr.le

private theorem x11g_cis {r θ x y : ℝ} (hx : r * cos θ = x) (hy : r * sin θ = y) :
    ((r : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I) = ⟨x, y⟩ := by
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; exact hx
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]; exact hy

private theorem x11g_s (n : ℕ) (hn : 0 < n) : √(n : ℝ) * √(n : ℝ) = n :=
  Real.mul_self_sqrt (by positivity)

/-! ## Section 11.7 -/

/-- Stitz-Zeager Exercise 11.7.1: `z = 9 + 9i` has `|z| = 9√2` and `Arg z = π/4`. -/
@[kb "stitzzeager2013" "Exercise 11.7.1, p. 1016"]
theorem exer_11_7_1 : ‖(⟨9, 9⟩ : ℂ)‖ = 9 * √2 ∧ Complex.arg ⟨9, 9⟩ = π / 4 := by
  have hp := pi_pos
  have h2 := x11g_s 2 (by norm_num)
  have := x11g_arg (x := 9) (y := 9) (r := 9 * √2) (θ := π / 4) (by positivity)
    ⟨by linarith, by linarith⟩ (by rw [cos_pi_div_four]; push_cast at h2; nlinarith)
    (by rw [sin_pi_div_four]; push_cast at h2; nlinarith)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.2: `z = 5 + 5√3 i` has `|z| = 10` and `Arg z = π/3`. -/
@[kb "stitzzeager2013" "Exercise 11.7.2, p. 1016"]
theorem exer_11_7_2 : ‖(⟨5, 5 * √3⟩ : ℂ)‖ = 10 ∧ Complex.arg ⟨5, 5 * √3⟩ = π / 3 := by
  have hp := pi_pos
  have := x11g_arg (x := 5) (y := 5 * √3) (r := 10) (θ := π / 3) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_pi_div_three]; ring)
    (by rw [sin_pi_div_three]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.5: `z = -6√3 + 6i` has `|z| = 12` and `Arg z = 5π/6`. -/
@[kb "stitzzeager2013" "Exercise 11.7.5, p. 1016"]
theorem exer_11_7_5 : ‖(⟨-(6 * √3), 6⟩ : ℂ)‖ = 12 ∧ Complex.arg ⟨-(6 * √3), 6⟩ = 5 * π / 6 := by
  have hp := pi_pos
  have e : 5 * π / 6 = π - π / 6 := by ring
  have := x11g_arg (x := -(6 * √3)) (y := 6) (r := 12) (θ := 5 * π / 6) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [e, cos_pi_sub, cos_pi_div_six]; ring)
    (by rw [e, sin_pi_sub, sin_pi_div_six]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.7: `z = -√3/2 - i/2` has `|z| = 1` and `Arg z = -5π/6`. -/
@[kb "stitzzeager2013" "Exercise 11.7.7, p. 1016"]
theorem exer_11_7_7 :
    ‖(⟨-(√3 / 2), -(1 / 2)⟩ : ℂ)‖ = 1 ∧ Complex.arg ⟨-(√3 / 2), -(1 / 2)⟩ = -(5 * π / 6) := by
  have hp := pi_pos
  have e : 5 * π / 6 = π - π / 6 := by ring
  have := x11g_arg (x := -(√3 / 2)) (y := -(1 / 2)) (r := 1) (θ := -(5 * π / 6)) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_neg, e, cos_pi_sub, cos_pi_div_six]; ring)
    (by rw [sin_neg, e, sin_pi_sub, sin_pi_div_six]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.8: `z = -3 - 3i` has `|z| = 3√2` and `Arg z = -3π/4`. -/
@[kb "stitzzeager2013" "Exercise 11.7.8, p. 1016"]
theorem exer_11_7_8 : ‖(⟨-3, -3⟩ : ℂ)‖ = 3 * √2 ∧ Complex.arg ⟨-3, -3⟩ = -(3 * π / 4) := by
  have hp := pi_pos
  have h2 := x11g_s 2 (by norm_num)
  push_cast at h2
  have e : 3 * π / 4 = π - π / 4 := by ring
  have := x11g_arg (x := -3) (y := -3) (r := 3 * √2) (θ := -(3 * π / 4)) (by positivity)
    ⟨by linarith, by linarith⟩ (by rw [cos_neg, e, cos_pi_sub, cos_pi_div_four]; nlinarith)
    (by rw [sin_neg, e, sin_pi_sub, sin_pi_div_four]; nlinarith)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.13: `z = 3 + 4i` has `|z| = 5` and `Arg z = arctan (4/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.13, p. 1016"]
theorem exer_11_7_13 : ‖(⟨3, 4⟩ : ℂ)‖ = 5 ∧ Complex.arg ⟨3, 4⟩ = arctan (4 / 3) := by
  have hp := pi_pos
  have h5 : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show 1 + (4 / 3 : ℝ) ^ 2 = (5 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have ha := arctan_lt_pi_div_two (4 / 3)
  have hb := neg_pi_div_two_lt_arctan (4 / 3)
  have := x11g_arg (x := 3) (y := 4) (r := 5) (θ := arctan (4 / 3)) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_arctan, h5]; norm_num)
    (by rw [sin_arctan, h5]; norm_num)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.15: `z = -7 + 24i` has `|z| = 25` and `Arg z = π - arctan (24/7)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.15, p. 1016"]
theorem exer_11_7_15 :
    ‖(⟨-7, 24⟩ : ℂ)‖ = 25 ∧ Complex.arg ⟨-7, 24⟩ = π - arctan (24 / 7) := by
  have hp := pi_pos
  have h5 : √(1 + (24 / 7 : ℝ) ^ 2) = 25 / 7 := by
    rw [show 1 + (24 / 7 : ℝ) ^ 2 = (25 / 7) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have ha := arctan_lt_pi_div_two (24 / 7)
  have hb : 0 < arctan (24 / 7) := arctan_pos.2 (by norm_num)
  have := x11g_arg (x := -7) (y := 24) (r := 25) (θ := π - arctan (24 / 7)) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_pi_sub, cos_arctan, h5]; norm_num)
    (by rw [sin_pi_sub, sin_arctan, h5]; norm_num)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.17: `z = -12 - 5i` has `|z| = 13` and `Arg z = arctan (5/12) - π`. -/
@[kb "stitzzeager2013" "Exercise 11.7.17, p. 1016"]
theorem exer_11_7_17 :
    ‖(⟨-12, -5⟩ : ℂ)‖ = 13 ∧ Complex.arg ⟨-12, -5⟩ = arctan (5 / 12) - π := by
  have hp := pi_pos
  have h5 : √(1 + (5 / 12 : ℝ) ^ 2) = 13 / 12 := by
    rw [show 1 + (5 / 12 : ℝ) ^ 2 = (13 / 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have ha := arctan_lt_pi_div_two (5 / 12)
  have hb : 0 < arctan (5 / 12) := arctan_pos.2 (by norm_num)
  have := x11g_arg (x := -12) (y := -5) (r := 13) (θ := arctan (5 / 12) - π) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_sub_pi, cos_arctan, h5]; norm_num)
    (by rw [sin_sub_pi, sin_arctan, h5]; norm_num)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Exercise 11.7.22: `2 cis (π/6) = √3 + i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.22, p. 1016"]
theorem exer_11_7_22 :
    ((2 : ℝ) : ℂ) * Complex.exp (↑(π / 6) * Complex.I) = ⟨√3, 1⟩ :=
  x11g_cis (by rw [cos_pi_div_six]; ring) (by rw [sin_pi_div_six]; ring)

/-- Stitz-Zeager Exercise 11.7.25: `4 cis (2π/3) = -2 + 2√3 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.25, p. 1016"]
theorem exer_11_7_25 :
    ((4 : ℝ) : ℂ) * Complex.exp (↑(2 * π / 3) * Complex.I) = ⟨-2, 2 * √3⟩ := by
  have e : 2 * π / 3 = π - π / 3 := by ring
  exact x11g_cis (by rw [e, cos_pi_sub, cos_pi_div_three]; ring)
    (by rw [e, sin_pi_sub, sin_pi_div_three]; ring)

/-- Stitz-Zeager Exercise 11.7.33: `8 cis (π/12) = 2(√2 + √2√3) + 2(√2√3 - √2) i`
(that is, `(√6 + √2)·2 + (√6 - √2)·2 i`). -/
@[kb "stitzzeager2013" "Exercise 11.7.33, p. 1016"]
theorem exer_11_7_33 :
    ((8 : ℝ) : ℂ) * Complex.exp (↑(π / 12) * Complex.I) =
      ⟨2 * (√2 + √2 * √3), 2 * (√2 * √3 - √2)⟩ := by
  have e : π / 12 = π / 3 - π / 4 := by ring
  exact x11g_cis (by rw [e, cos_sub, cos_pi_div_three, sin_pi_div_three, cos_pi_div_four,
      sin_pi_div_four]; ring)
    (by rw [e, sin_sub, cos_pi_div_three, sin_pi_div_three, cos_pi_div_four, sin_pi_div_four]; ring)

/-- Stitz-Zeager Exercise 11.7.35: `5 cis (arctan (4/3)) = 3 + 4i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.35, p. 1016"]
theorem exer_11_7_35 :
    ((5 : ℝ) : ℂ) * Complex.exp (↑(arctan (4 / 3)) * Complex.I) = ⟨3, 4⟩ := by
  have h5 : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show 1 + (4 / 3 : ℝ) ^ 2 = (5 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact x11g_cis (by rw [cos_arctan, h5]; norm_num) (by rw [sin_arctan, h5]; norm_num)

/-- Stitz-Zeager Exercise 11.7.39: `50 cis (π - arctan (7/24)) = -48 + 14i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.39, p. 1016"]
theorem exer_11_7_39 :
    ((50 : ℝ) : ℂ) * Complex.exp (↑(π - arctan (7 / 24)) * Complex.I) = ⟨-48, 14⟩ := by
  have h5 : √(1 + (7 / 24 : ℝ) ^ 2) = 25 / 24 := by
    rw [show 1 + (7 / 24 : ℝ) ^ 2 = (25 / 24) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact x11g_cis (by rw [cos_pi_sub, cos_arctan, h5]; norm_num)
    (by rw [sin_pi_sub, sin_arctan, h5]; norm_num)

/-- Stitz-Zeager Exercise 11.7.41: for `z = -3√3/2 + 3i/2 = 3 cis (5π/6)` and `w = 3√2 - 3√2 i = 6 cis (-π/4)`,
the product is `zw = 18 cis (7π/12)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.41, p. 1016"]
theorem exer_11_7_41 :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) * ⟨3 * √2, -(3 * √2)⟩ =
      ((18 : ℝ) : ℂ) * Complex.exp (↑(7 * π / 12) * Complex.I) := by
  have e5 : 5 * π / 6 = π - π / 6 := by ring
  have hz : (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) = ((3 : ℝ) : ℂ) * Complex.exp (↑(5 * π / 6) * Complex.I) :=
    (x11g_cis (by rw [e5, cos_pi_sub, cos_pi_div_six]; ring)
      (by rw [e5, sin_pi_sub, sin_pi_div_six]; ring)).symm
  have hw : (⟨3 * √2, -(3 * √2)⟩ : ℂ) = ((6 : ℝ) : ℂ) * Complex.exp (↑(-(π / 4)) * Complex.I) :=
    (x11g_cis (by rw [cos_neg, cos_pi_div_four]; ring)
      (by rw [sin_neg, sin_pi_div_four]; ring)).symm
  rw [hz, hw, mul_mul_mul_comm, ← Complex.exp_add]
  have e : (↑(5 * π / 6) : ℂ) * Complex.I + ↑(-(π / 4)) * Complex.I = ↑(7 * π / 12) * Complex.I := by
    push_cast; ring
  rw [e]; push_cast; ring

/-- Stitz-Zeager Exercise 11.7.44: for `z = 3 cis (5π/6)`, `z⁴ = 81 cis (-2π/3)`
(principal argument `-2π/3`). -/
@[kb "stitzzeager2013" "Exercise 11.7.44, p. 1016"]
theorem exer_11_7_44 :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ 4 = ((81 : ℝ) : ℂ) * Complex.exp (↑(-(2 * π / 3)) * Complex.I) := by
  have e5 : 5 * π / 6 = π - π / 6 := by ring
  have hz : (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) = ((3 : ℝ) : ℂ) * Complex.exp (↑(5 * π / 6) * Complex.I) :=
    (x11g_cis (by rw [e5, cos_pi_sub, cos_pi_div_six]; ring)
      (by rw [e5, sin_pi_sub, sin_pi_div_six]; ring)).symm
  rw [hz, mul_pow, ← Complex.exp_nat_mul]
  have : Complex.exp (↑(4 : ℕ) * (↑(5 * π / 6) * Complex.I)) =
      Complex.exp (↑(-(2 * π / 3)) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨2, ?_⟩
    push_cast; ring
  rw [this]; push_cast; ring

/-- Stitz-Zeager Exercise 11.7.54: `(-√3 - i)³ = -8i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.54, p. 1017"]
theorem exer_11_7_54 : (⟨-√3, -1⟩ : ℂ) ^ 3 = ⟨0, -8⟩ := by
  have h3 := x11g_s 3 (by norm_num)
  push_cast at h3
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Stitz-Zeager Exercise 11.7.56: `(√3 + i)⁴ = -8 + 8√3 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.56, p. 1017"]
theorem exer_11_7_56 : (⟨√3, 1⟩ : ℂ) ^ 4 = ⟨-8, 8 * √3⟩ := by
  have h3 := x11g_s 3 (by norm_num)
  push_cast at h3
  have h33 : √3 * √3 * √3 = 3 * √3 := by rw [h3]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Stitz-Zeager Exercise 11.7.62: `(2 + 2i)⁵ = -128 - 128i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.62, p. 1017"]
theorem exer_11_7_62 : (⟨2, 2⟩ : ℂ) ^ 5 = ⟨-128, -128⟩ := by
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> norm_num

/-- Stitz-Zeager Exercise 11.7.64: `(1 - i)⁸ = 16`. -/
@[kb "stitzzeager2013" "Exercise 11.7.64, p. 1017"]
theorem exer_11_7_64 : (⟨1, -1⟩ : ℂ) ^ 8 = 16 := by
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> norm_num

/-- Stitz-Zeager Exercise 11.7.65: the two square roots of `4i` are `±(√2 + √2 i)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.65, p. 1017"]
theorem exer_11_7_65 (w : ℂ) :
    w ^ 2 = ⟨0, 4⟩ ↔ w = ⟨√2, √2⟩ ∨ w = ⟨-√2, -√2⟩ := by
  have h2 := x11g_s 2 (by norm_num)
  push_cast at h2
  have ha : (⟨√2, √2⟩ : ℂ) ^ 2 = ⟨0, 4⟩ := by
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have hb : (⟨-√2, -√2⟩ : ℂ) = -⟨√2, √2⟩ := by
    apply Complex.ext <;> simp
  rw [← ha, hb]
  exact sq_eq_sq_iff_eq_or_eq_neg

/-- Stitz-Zeager Exercise 11.7.69: the three cube roots of `64` are `4`, `-2 + 2√3 i`, `-2 - 2√3 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.69, p. 1017"]
theorem exer_11_7_69 (w : ℂ) :
    w ^ 3 = 64 ↔ w = 4 ∨ w = ⟨-2, 2 * √3⟩ ∨ w = ⟨-2, -(2 * √3)⟩ := by
  have h3 := x11g_s 3 (by norm_num)
  push_cast at h3
  have hsum : (⟨-2, 2 * √3⟩ : ℂ) + ⟨-2, -(2 * √3)⟩ = -4 := by
    apply Complex.ext <;> simp <;> norm_num
  have hprod : (⟨-2, 2 * √3⟩ : ℂ) * ⟨-2, -(2 * √3)⟩ = 16 := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith
  have fac : w ^ 3 - 64 = (w - 4) * (w - ⟨-2, 2 * √3⟩) * (w - ⟨-2, -(2 * √3)⟩) := by
    linear_combination (w * (w - 4)) * hsum - (w - 4) * hprod
  constructor
  · intro h
    have : (w - 4) * (w - ⟨-2, 2 * √3⟩) * (w - ⟨-2, -(2 * √3)⟩) = 0 := by rw [← fac, h]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · left; exact sub_eq_zero.mp h2
      · right; left; exact sub_eq_zero.mp h2
    · right; right; exact sub_eq_zero.mp h1
  · intro h
    have : w ^ 3 - 64 = 0 := by
      rw [fac]
      rcases h with h | h | h <;> rw [h] <;> ring
    exact sub_eq_zero.mp this

/-- Stitz-Zeager Exercise 11.7.73: the four fourth roots of `16` are `2`, `-2`, `2i`, `-2i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.73, p. 1017"]
theorem exer_11_7_73 (w : ℂ) :
    w ^ 4 = 16 ↔ w = 2 ∨ w = -2 ∨ w = 2 * Complex.I ∨ w = -2 * Complex.I := by
  have fac : w ^ 4 - 16 = (w - 2) * (w + 2) * (w - 2 * Complex.I) * (w + 2 * Complex.I) := by
    linear_combination (4 * (w ^ 2 - 4)) * Complex.I_sq
  constructor
  · intro h
    have : (w - 2) * (w + 2) * (w - 2 * Complex.I) * (w + 2 * Complex.I) = 0 := by
      rw [← fac, h]; ring
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · left; exact sub_eq_zero.mp h3
        · right; left; exact eq_neg_of_add_eq_zero_left h3
      · right; right; left; exact sub_eq_zero.mp h2
    · right; right; right
      rw [neg_mul]; exact eq_neg_of_add_eq_zero_left h1
  · intro h
    have : w ^ 4 - 16 = 0 := by
      rw [fac]
      rcases h with h | h | h | h <;> rw [h] <;> ring
    exact sub_eq_zero.mp this

/-- Stitz-Zeager Exercise 11.7.83(e): `e^{iπ} + 1 = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.7.83e, p. 1018"]
theorem exer_11_7_83_e : Complex.exp (↑π * Complex.I) + 1 = 0 := by
  rw [Complex.exp_pi_mul_I]; ring

/-- Stitz-Zeager Exercise 11.7.83(f): for real `t`, `cos t = (e^{it} + e^{-it})/2` and
`sin t = (e^{it} - e^{-it})/(2i)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.83f, p. 1018"]
theorem exer_11_7_83_f (t : ℝ) :
    (cos t : ℂ) = (Complex.exp (↑t * Complex.I) + Complex.exp (-(↑t * Complex.I))) / 2 ∧
      (sin t : ℂ) = (Complex.exp (↑t * Complex.I) - Complex.exp (-(↑t * Complex.I))) / (2 * Complex.I) := by
  constructor
  · rw [Complex.ofReal_cos, Complex.cos]
    ring_nf
  · rw [Complex.ofReal_sin, Complex.sin]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

end UndergradKB.Precalculus.Course
