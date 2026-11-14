import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.7 (part 2)

We write `⟨x, y⟩` for `x + y i`, and `r cis θ` as `r * exp (θ * I)`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Helpers -/

private theorem w7_cis {r θ x y : ℝ} (hx : r * cos θ = x) (hy : r * sin θ = y) :
    ((r : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I) = ⟨x, y⟩ := by
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; exact hx
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]; exact hy

private theorem w7_s (n : ℕ) (hn : 0 < n) : √(n : ℝ) * √(n : ℝ) = n :=
  Real.mul_self_sqrt (by positivity)

private theorem w7_pc {r r' a c : ℝ} (hr : r = r') (k : ℤ) (h : a = c + 2 * π * k) :
    ((r : ℝ) : ℂ) * Complex.exp (↑a * Complex.I) = ((r' : ℝ) : ℂ) * Complex.exp (↑c * Complex.I) := by
  subst hr
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨k, by rw [h]; push_cast; ring⟩

private theorem w7_z : (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) =
    ((3 : ℝ) : ℂ) * Complex.exp (↑(5 * π / 6) * Complex.I) := by
  have e5 : 5 * π / 6 = π - π / 6 := by ring
  exact (w7_cis (by rw [e5, cos_pi_sub, cos_pi_div_six]; ring)
    (by rw [e5, sin_pi_sub, sin_pi_div_six]; ring)).symm

private theorem w7_w : (⟨3 * √2, -(3 * √2)⟩ : ℂ) =
    ((6 : ℝ) : ℂ) * Complex.exp (↑(-(π / 4)) * Complex.I) :=
  (w7_cis (by rw [cos_neg, cos_pi_div_four]; ring) (by rw [sin_neg, sin_pi_div_four]; ring)).symm

private theorem w7_zw (m n : ℤ) :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ m * (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ n =
      (((3 : ℝ) ^ m * 6 ^ n : ℝ) : ℂ) *
        Complex.exp (↑((m : ℝ) * (5 * π / 6) + (n : ℝ) * (-(π / 4))) * Complex.I) := by
  rw [w7_z, w7_w, mul_zpow, mul_zpow, ← Complex.exp_int_mul, ← Complex.exp_int_mul,
    mul_mul_mul_comm, ← Complex.exp_add]
  have : (m : ℂ) * (↑(5 * π / 6) * Complex.I) + (n : ℂ) * (↑(-(π / 4)) * Complex.I) =
      ↑((m : ℝ) * (5 * π / 6) + (n : ℝ) * (-(π / 4))) * Complex.I := by
    push_cast; ring
  rw [this]
  push_cast
  ring

/-! ## Section 11.7: rectangular forms -/

/-- Stitz-Zeager Exercise 11.7.21: `6 cis 0 = 6`. -/
@[kb "stitzzeager2013" "Exercise 11.7.21, p. 1016"]
theorem exer_11_7_21 : ((6 : ℝ) : ℂ) * Complex.exp (↑(0 : ℝ) * Complex.I) = ⟨6, 0⟩ :=
  w7_cis (by rw [cos_zero]; ring) (by rw [sin_zero]; ring)

/-- Stitz-Zeager Exercise 11.7.23: `7√2 cis (π/4) = 7 + 7i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.23, p. 1016"]
theorem exer_11_7_23 : ((7 * √2 : ℝ) : ℂ) * Complex.exp (↑(π / 4) * Complex.I) = ⟨7, 7⟩ := by
  have h2 := w7_s 2 (by norm_num)
  push_cast at h2
  exact w7_cis (by rw [cos_pi_div_four]; nlinarith) (by rw [sin_pi_div_four]; nlinarith)

/-- Stitz-Zeager Exercise 11.7.24: `3 cis (π/2) = 3i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.24, p. 1016"]
theorem exer_11_7_24 : ((3 : ℝ) : ℂ) * Complex.exp (↑(π / 2) * Complex.I) = ⟨0, 3⟩ :=
  w7_cis (by rw [cos_pi_div_two]; ring) (by rw [sin_pi_div_two]; ring)

/-- Stitz-Zeager Exercise 11.7.26: `√6 cis (3π/4) = -√3 + √3 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.26, p. 1016"]
theorem exer_11_7_26 : ((√6 : ℝ) : ℂ) * Complex.exp (↑(3 * π / 4) * Complex.I) = ⟨-√3, √3⟩ := by
  have h2 := w7_s 2 (by norm_num)
  push_cast at h2
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have e : 3 * π / 4 = π - π / 4 := by ring
  exact w7_cis (by rw [e, cos_pi_sub, cos_pi_div_four, h6]; linear_combination (-(√3 / 2)) * h2)
    (by rw [e, sin_pi_sub, sin_pi_div_four, h6]; linear_combination (√3 / 2) * h2)

/-- Stitz-Zeager Exercise 11.7.27: `9 cis π = -9`. -/
@[kb "stitzzeager2013" "Exercise 11.7.27, p. 1016"]
theorem exer_11_7_27 : ((9 : ℝ) : ℂ) * Complex.exp (↑π * Complex.I) = ⟨-9, 0⟩ :=
  w7_cis (by rw [cos_pi]; ring) (by rw [sin_pi]; ring)

/-- Stitz-Zeager Exercise 11.7.28: `3 cis (4π/3) = -3/2 - (3√3/2) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.28, p. 1016"]
theorem exer_11_7_28 :
    ((3 : ℝ) : ℂ) * Complex.exp (↑(4 * π / 3) * Complex.I) = ⟨-(3 / 2), -(3 * √3 / 2)⟩ := by
  have e : 4 * π / 3 = π / 3 + π := by ring
  exact w7_cis (by rw [e, cos_add_pi, cos_pi_div_three]; ring)
    (by rw [e, sin_add_pi, sin_pi_div_three]; ring)

/-- Stitz-Zeager Exercise 11.7.29: `7 cis (-3π/4) = -7√2/2 - (7√2/2) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.29, p. 1016"]
theorem exer_11_7_29 :
    ((7 : ℝ) : ℂ) * Complex.exp (↑(-(3 * π / 4)) * Complex.I) = ⟨-(7 * √2 / 2), -(7 * √2 / 2)⟩ := by
  have e : 3 * π / 4 = π - π / 4 := by ring
  exact w7_cis (by rw [cos_neg, e, cos_pi_sub, cos_pi_div_four]; ring)
    (by rw [sin_neg, e, sin_pi_sub, sin_pi_div_four]; ring)

/-- Stitz-Zeager Exercise 11.7.30: `√13 cis (3π/2) = -√13 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.30, p. 1016"]
theorem exer_11_7_30 : ((√13 : ℝ) : ℂ) * Complex.exp (↑(3 * π / 2) * Complex.I) = ⟨0, -√13⟩ := by
  have e : 3 * π / 2 = π / 2 + π := by ring
  exact w7_cis (by rw [e, cos_add_pi, cos_pi_div_two]; ring)
    (by rw [e, sin_add_pi, sin_pi_div_two]; ring)

/-- Stitz-Zeager Exercise 11.7.31: `(1/2) cis (7π/4) = √2/4 - (√2/4) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.31, p. 1016"]
theorem exer_11_7_31 :
    ((1 / 2 : ℝ) : ℂ) * Complex.exp (↑(7 * π / 4) * Complex.I) = ⟨√2 / 4, -(√2 / 4)⟩ := by
  have e : 7 * π / 4 = -(π / 4) + 2 * π := by ring
  exact w7_cis (by rw [e, cos_add_two_pi, cos_neg, cos_pi_div_four]; ring)
    (by rw [e, sin_add_two_pi, sin_neg, sin_pi_div_four]; ring)

/-- Stitz-Zeager Exercise 11.7.32: `12 cis (-π/3) = 6 - 6√3 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.32, p. 1016"]
theorem exer_11_7_32 :
    ((12 : ℝ) : ℂ) * Complex.exp (↑(-(π / 3)) * Complex.I) = ⟨6, -(6 * √3)⟩ :=
  w7_cis (by rw [cos_neg, cos_pi_div_three]; ring) (by rw [sin_neg, sin_pi_div_three]; ring)

/-- Stitz-Zeager Exercise 11.7.34: `2 cis (7π/8) = -√(2 + √2) + √(2 - √2) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.34, p. 1016"]
theorem exer_11_7_34 :
    ((2 : ℝ) : ℂ) * Complex.exp (↑(7 * π / 8) * Complex.I) = ⟨-√(2 + √2), √(2 - √2)⟩ := by
  have e : 7 * π / 8 = π - π / 8 := by ring
  exact w7_cis (by rw [e, cos_pi_sub, cos_pi_div_eight]; ring)
    (by rw [e, sin_pi_sub, sin_pi_div_eight]; ring)

/-- Stitz-Zeager Exercise 11.7.36: `√10 cis (arctan (1/3)) = 3 + i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.36, p. 1016"]
theorem exer_11_7_36 :
    ((√10 : ℝ) : ℂ) * Complex.exp (↑(arctan (1 / 3)) * Complex.I) = ⟨3, 1⟩ := by
  have h10 := w7_s 10 (by norm_num)
  push_cast at h10
  have s : 0 < √10 := by positivity
  have h5 : √(1 + (1 / 3 : ℝ) ^ 2) = √10 / 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    nlinarith
  exact w7_cis (by rw [cos_arctan, h5]; field_simp <;> nlinarith)
    (by rw [sin_arctan, h5]; field_simp <;> nlinarith)

/-- Stitz-Zeager Exercise 11.7.37: `15 cis (arctan (-2)) = 3√5 - 6√5 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.37, p. 1016"]
theorem exer_11_7_37 :
    ((15 : ℝ) : ℂ) * Complex.exp (↑(arctan (-2)) * Complex.I) = ⟨3 * √5, -(6 * √5)⟩ := by
  have h5 := w7_s 5 (by norm_num)
  push_cast at h5
  have s : 0 < √5 := by positivity
  have h : √(1 + (-2 : ℝ) ^ 2) = √5 := by norm_num
  exact w7_cis (by rw [cos_arctan, h]; field_simp <;> nlinarith)
    (by rw [sin_arctan, h]; field_simp <;> nlinarith)

/-- Stitz-Zeager Exercise 11.7.38: `√3 cis (arctan (-√2)) = 1 - √2 i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.38, p. 1016"]
theorem exer_11_7_38 :
    ((√3 : ℝ) : ℂ) * Complex.exp (↑(arctan (-√2)) * Complex.I) = ⟨1, -√2⟩ := by
  have h3 := w7_s 3 (by norm_num)
  push_cast at h3
  have s : 0 < √3 := by positivity
  have h2 := w7_s 2 (by norm_num)
  push_cast at h2
  have h : √(1 + (-√2 : ℝ) ^ 2) = √3 := by
    rw [neg_sq, Real.sq_sqrt (by norm_num)]; norm_num
  exact w7_cis (by rw [cos_arctan, h]; field_simp <;> nlinarith)
    (by rw [sin_arctan, h]; field_simp <;> nlinarith)

/-- Stitz-Zeager Exercise 11.7.40: `(1/2) cis (π + arctan (5/12)) = -6/13 - (5/26) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.40, p. 1016"]
theorem exer_11_7_40 :
    ((1 / 2 : ℝ) : ℂ) * Complex.exp (↑(π + arctan (5 / 12)) * Complex.I) = ⟨-(6 / 13), -(5 / 26)⟩ := by
  have h5 : √(1 + (5 / 12 : ℝ) ^ 2) = 13 / 12 := by
    rw [show 1 + (5 / 12 : ℝ) ^ 2 = (13 / 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [add_comm π]
  exact w7_cis (by rw [cos_add_pi, cos_arctan, h5]; norm_num) (by rw [sin_add_pi, sin_arctan, h5]; norm_num)

/-! ## Section 11.7: products, quotients and powers of `z = 3 cis (5π/6)`, `w = 6 cis (-π/4)` -/

/-- Stitz-Zeager Exercise 11.7.42: `z / w = (1/2) cis (-11π/12)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.42, p. 1016"]
theorem exer_11_7_42 :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) / (⟨3 * √2, -(3 * √2)⟩ : ℂ) =
      ((1 / 2 : ℝ) : ℂ) * Complex.exp (↑(-(11 * π / 12)) * Complex.I) := by
  have h := w7_zw 1 (-1)
  rw [zpow_one, zpow_neg_one, ← div_eq_mul_inv] at h
  rw [h]
  exact w7_pc (by norm_num) 1 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.43: `w / z = 2 cis (11π/12)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.43, p. 1016"]
theorem exer_11_7_43 :
    (⟨3 * √2, -(3 * √2)⟩ : ℂ) / (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) =
      ((2 : ℝ) : ℂ) * Complex.exp (↑(11 * π / 12) * Complex.I) := by
  have h := w7_zw (-1) 1
  rw [zpow_one, zpow_neg_one, mul_comm, ← div_eq_mul_inv] at h
  rw [h]
  exact w7_pc (by norm_num) (-1) (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.45: `w³ = 216 cis (-3π/4)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.45, p. 1016"]
theorem exer_11_7_45 :
    (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ 3 =
      ((216 : ℝ) : ℂ) * Complex.exp (↑(-(3 * π / 4)) * Complex.I) := by
  have h := w7_zw 0 3
  rw [zpow_zero, one_mul] at h
  have h' : (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ (3 : ℤ) = (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ 3 := zpow_ofNat _ 3
  rw [← h', h]
  exact w7_pc (by norm_num) 0 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.46: `z⁵ w² = 8748 cis (-π/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.46, p. 1016"]
theorem exer_11_7_46 :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ 5 * (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ 2 =
      ((8748 : ℝ) : ℂ) * Complex.exp (↑(-(π / 3)) * Complex.I) := by
  have h := w7_zw 5 2
  rw [zpow_ofNat, zpow_ofNat] at h
  rw [h]
  exact w7_pc (by norm_num) 2 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.47: `z³ w² = 972 cis 0` (that is, `972`). -/
@[kb "stitzzeager2013" "Exercise 11.7.47, p. 1016"]
theorem exer_11_7_47 :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ 3 * (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ 2 =
      ((972 : ℝ) : ℂ) * Complex.exp (↑(0 : ℝ) * Complex.I) := by
  have h := w7_zw 3 2
  rw [zpow_ofNat, zpow_ofNat] at h
  rw [h]
  exact w7_pc (by norm_num) 1 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.48: `z² / w = (3/2) cis (-π/12)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.48, p. 1016"]
theorem exer_11_7_48 :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ 2 / (⟨3 * √2, -(3 * √2)⟩ : ℂ) =
      ((3 / 2 : ℝ) : ℂ) * Complex.exp (↑(-(π / 12)) * Complex.I) := by
  have h := w7_zw 2 (-1)
  rw [zpow_neg_one, zpow_ofNat, ← div_eq_mul_inv] at h
  rw [h]
  exact w7_pc (by norm_num) 1 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.49: `w / z² = (2/3) cis (π/12)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.49, p. 1017"]
theorem exer_11_7_49 :
    (⟨3 * √2, -(3 * √2)⟩ : ℂ) / (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ 2 =
      ((2 / 3 : ℝ) : ℂ) * Complex.exp (↑(π / 12) * Complex.I) := by
  have h := w7_zw (-2) 1
  rw [zpow_one, zpow_neg, zpow_ofNat, mul_comm, ← div_eq_mul_inv] at h
  rw [h]
  exact w7_pc (by norm_num) (-1) (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.50: `z³ / w² = (3/4) cis π`. -/
@[kb "stitzzeager2013" "Exercise 11.7.50, p. 1017"]
theorem exer_11_7_50 :
    (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ 3 / (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ 2 =
      ((3 / 4 : ℝ) : ℂ) * Complex.exp (↑π * Complex.I) := by
  have h := w7_zw 3 (-2)
  rw [zpow_neg, zpow_ofNat, zpow_ofNat, ← div_eq_mul_inv] at h
  rw [h]
  exact w7_pc (by norm_num) 1 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.51: `w² / z³ = (4/3) cis π`. -/
@[kb "stitzzeager2013" "Exercise 11.7.51, p. 1017"]
theorem exer_11_7_51 :
    (⟨3 * √2, -(3 * √2)⟩ : ℂ) ^ 2 / (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ) ^ 3 =
      ((4 / 3 : ℝ) : ℂ) * Complex.exp (↑π * Complex.I) := by
  have h := w7_zw (-3) 2
  rw [zpow_neg, zpow_ofNat, zpow_ofNat, mul_comm, ← div_eq_mul_inv] at h
  rw [h]
  exact w7_pc (by norm_num) (-2) (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.7.52: `(w / z)⁶ = 64 cis (-π/2)`. -/
@[kb "stitzzeager2013" "Exercise 11.7.52, p. 1017"]
theorem exer_11_7_52 :
    ((⟨3 * √2, -(3 * √2)⟩ : ℂ) / (⟨-(3 * √3 / 2), 3 / 2⟩ : ℂ)) ^ 6 =
      ((64 : ℝ) : ℂ) * Complex.exp (↑(-(π / 2)) * Complex.I) := by
  have h := w7_zw (-6) 6
  rw [zpow_neg, zpow_ofNat, zpow_ofNat, mul_comm, ← div_eq_mul_inv, ← div_pow] at h
  rw [h]
  exact w7_pc (by norm_num) (-3) (by push_cast; ring)

/-! ## Section 11.7: powers in rectangular form -/

/-- Stitz-Zeager Exercise 11.7.53: `(-2 + 2√3 i)³ = 64`. -/
@[kb "stitzzeager2013" "Exercise 11.7.53, p. 1017"]
theorem exer_11_7_53 : (⟨-2, 2 * √3⟩ : ℂ) ^ 3 = 64 := by
  have h3 := w7_s 3 (by norm_num)
  push_cast at h3
  have h33 : √3 * √3 * √3 = 3 * √3 := by rw [h3]
  have h4 : √3 * √3 * √3 * √3 = 9 := by rw [h33]; nlinarith
  have h5 : √3 * √3 * √3 * √3 * √3 = 9 * √3 := by rw [h4]
  have h6 : √3 * √3 * √3 * √3 * √3 * √3 = 27 := by rw [h5]; nlinarith
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> linarith

/-- Stitz-Zeager Exercise 11.7.55: `(-3 + 3i)⁴ = -324`. -/
@[kb "stitzzeager2013" "Exercise 11.7.55, p. 1017"]
theorem exer_11_7_55 : (⟨-3, 3⟩ : ℂ) ^ 4 = -324 := by
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> norm_num

/-- Stitz-Zeager Exercise 11.7.58: `(-1/2 - (√3/2) i)⁶ = 1`. -/
@[kb "stitzzeager2013" "Exercise 11.7.58, p. 1017"]
theorem exer_11_7_58 : (⟨-(1 / 2), -(√3 / 2)⟩ : ℂ) ^ 6 = 1 := by
  have h3 := w7_s 3 (by norm_num)
  push_cast at h3
  have h33 : √3 * √3 * √3 = 3 * √3 := by rw [h3]
  have h4 : √3 * √3 * √3 * √3 = 9 := by rw [h33]; nlinarith
  have h5 : √3 * √3 * √3 * √3 * √3 = 9 * √3 := by rw [h4]
  have h6 : √3 * √3 * √3 * √3 * √3 * √3 = 27 := by rw [h5]; nlinarith
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> linarith

/-- Stitz-Zeager Exercise 11.7.60: `(√3/3 - i/3)⁴ = -8/81 - (8√3/81) i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.60, p. 1017"]
theorem exer_11_7_60 : (⟨√3 / 3, -(1 / 3)⟩ : ℂ) ^ 4 = ⟨-(8 / 81), -(8 * √3 / 81)⟩ := by
  have h3 := w7_s 3 (by norm_num)
  push_cast at h3
  have h33 : √3 * √3 * √3 = 3 * √3 := by rw [h3]
  have h4 : √3 * √3 * √3 * √3 = 9 := by rw [h33]; nlinarith
  have h5 : √3 * √3 * √3 * √3 * √3 = 9 * √3 := by rw [h4]
  have h6 : √3 * √3 * √3 * √3 * √3 * √3 = 27 := by rw [h5]; nlinarith
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> linarith

/-- Stitz-Zeager Exercise 11.7.61: `(√2/2 + (√2/2) i)⁴ = -1`. -/
@[kb "stitzzeager2013" "Exercise 11.7.61, p. 1017"]
theorem exer_11_7_61 : (⟨√2 / 2, √2 / 2⟩ : ℂ) ^ 4 = -1 := by
  have h2 := w7_s 2 (by norm_num)
  push_cast at h2
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Stitz-Zeager Exercise 11.7.63: `(√3 - i)⁵ = -16√3 - 16i`. -/
@[kb "stitzzeager2013" "Exercise 11.7.63, p. 1017"]
theorem exer_11_7_63 : (⟨√3, -1⟩ : ℂ) ^ 5 = ⟨-(16 * √3), -16⟩ := by
  have h3 := w7_s 3 (by norm_num)
  push_cast at h3
  have h33 : √3 * √3 * √3 = 3 * √3 := by rw [h3]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> nlinarith

end UndergradKB.Precalculus.Course
