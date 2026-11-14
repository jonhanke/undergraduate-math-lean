import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Section 11.4 (polar coordinates). The point named by `(r, θ)` is `polarPoint r θ = (r cos θ, r sin θ)`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ## Helpers -/

private theorem x11d_names_neg (r θ ψ : ℝ) (k : ℤ) (h : ψ = θ + (2 * k + 1) * π) :
    polarPoint (-r) ψ = polarPoint r θ := by
  rw [h]; exact (polar_point_same_names r θ k).2.1

private theorem x11d_names_same (r θ ψ : ℝ) (k : ℤ) (h : ψ = θ + k * (2 * π)) :
    polarPoint r ψ = polarPoint r θ := by
  rw [h]; exact (polar_point_same_names r θ k).1

/-- Uniqueness of the polar name with `r ≥ 0` and `0 ≤ θ < 2π` of a point other than the origin. -/
private theorem x11d_conv {r r' θ θ' : ℝ} (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ < 2 * π)
    (h0' : 0 ≤ r') (hθ0' : 0 ≤ θ') (hθ' : θ' < 2 * π) :
    polarPoint r' θ' = polarPoint r θ ↔ r' = r ∧ θ' = θ := by
  constructor
  · intro h
    rcases (polar_point_same_names r θ 0).2.2 hr.ne' r' θ' h with ⟨h1, n, hn⟩ | ⟨h1, n, hn⟩
    · refine ⟨h1, ?_⟩
      have hpi := pi_pos
      have e1 : (n : ℝ) < 1 := by nlinarith
      have e2 : (-1 : ℝ) < n := by nlinarith
      have : n = 0 := by
        have a : n < 1 := by exact_mod_cast e1
        have b : -1 < n := by exact_mod_cast e2
        omega
      subst this
      simpa using hn
    · exfalso; linarith
  · rintro ⟨rfl, rfl⟩; rfl

private theorem x11d_cos_arctan (x : ℝ) : cos (arctan x) = 1 / √(1 + x ^ 2) := Real.cos_arctan x

private theorem x11d_sqrt_sq {a b : ℝ} (hb : 0 < b) (h : a = b ^ 2) : √a = b := by
  rw [h, Real.sqrt_sq hb.le]

/-! ## Section 11.4 -/

/-- Stitz-Zeager Exercise 11.4.1: the point `(2, π/3)` is also named by `(-2, 4π/3)`, `(2, -5π/3)`,
`(2, 7π/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.1, p. 942"]
theorem exer_11_4_1 :
    polarPoint (-2) (4 * π / 3) = polarPoint 2 (π / 3) ∧
      polarPoint 2 (-(5 * π / 3)) = polarPoint 2 (π / 3) ∧
      polarPoint 2 (7 * π / 3) = polarPoint 2 (π / 3) :=
  ⟨x11d_names_neg 2 (π / 3) _ 0 (by push_cast; ring), x11d_names_same 2 (π / 3) _ (-1) (by push_cast; ring),
    x11d_names_same 2 (π / 3) _ 1 (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.5: the point `(12, -7π/6)` is also named by `(-12, 11π/6)`,
`(12, -19π/6)`, `(12, 17π/6)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.5, p. 942"]
theorem exer_11_4_5 :
    polarPoint (-12) (11 * π / 6) = polarPoint 12 (-(7 * π / 6)) ∧
      polarPoint 12 (-(19 * π / 6)) = polarPoint 12 (-(7 * π / 6)) ∧
      polarPoint 12 (17 * π / 6) = polarPoint 12 (-(7 * π / 6)) :=
  ⟨x11d_names_neg 12 _ _ 1 (by push_cast; ring), x11d_names_same 12 _ _ (-1) (by push_cast; ring),
    x11d_names_same 12 _ _ 2 (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.9: the point `(-20, 3π)` is also named by `(-20, π)`, `(20, -2π)`,
`(20, 4π)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.9, p. 942"]
theorem exer_11_4_9 :
    polarPoint (-20) π = polarPoint (-20) (3 * π) ∧ polarPoint 20 (-(2 * π)) = polarPoint (-20) (3 * π) ∧
      polarPoint 20 (4 * π) = polarPoint (-20) (3 * π) := by
  have h : polarPoint (-20) (3 * π) = polarPoint 20 (2 * π) := by
    have := x11d_names_neg 20 (2 * π) (3 * π) 0 (by push_cast; ring)
    exact this
  rw [h]
  refine ⟨?_, ?_, ?_⟩
  · have := x11d_names_neg 20 (2 * π) π (-1) (by push_cast; ring)
    exact this.symm ▸ rfl
  · exact x11d_names_same 20 (2 * π) _ (-2) (by push_cast; ring)
  · exact x11d_names_same 20 (2 * π) _ 1 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.4.16: the point `(-π, -π)` is also named by `(-π, π)`, `(π, -2π)`,
`(π, 2π)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.16, p. 942"]
theorem exer_11_4_16 :
    polarPoint (-π) π = polarPoint (-π) (-π) ∧ polarPoint π (-(2 * π)) = polarPoint (-π) (-π) ∧
      polarPoint π (2 * π) = polarPoint (-π) (-π) := by
  have h1 : polarPoint (-π) (-π) = polarPoint π 0 := by
    have := x11d_names_neg π 0 (-π) (-1) (by push_cast; ring)
    exact this
  rw [h1]
  refine ⟨?_, ?_, ?_⟩
  · exact x11d_names_neg π 0 π 0 (by push_cast; ring)
  · exact x11d_names_same π 0 _ (-1) (by push_cast; ring)
  · exact x11d_names_same π 0 _ 1 (by push_cast; ring)

/-- Stitz-Zeager Exercise 11.4.18: the polar point `(2, π/3)` is `(1, √3)` in rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.18, p. 942"]
theorem exer_11_4_18 : polarPoint 2 (π / 3) = (1, √3) := by
  simp only [polarPoint, cos_pi_div_three, sin_pi_div_three, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.19: the polar point `(11, -7π/6)` is `(-11√3/2, 11/2)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.19, p. 942"]
theorem exer_11_4_19 : polarPoint 11 (-(7 * π / 6)) = (-(11 * √3 / 2), 11 / 2) := by
  have e : -(7 * π / 6) = -(π / 6 + π) := by ring
  simp only [polarPoint, e, cos_neg, sin_neg, cos_add_pi, sin_add_pi, cos_pi_div_six, sin_pi_div_six,
    Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.22: the polar point `(-4, 5π/6)` is `(2√3, -2)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.22, p. 942"]
theorem exer_11_4_22 : polarPoint (-4) (5 * π / 6) = (2 * √3, -2) := by
  have e : 5 * π / 6 = π - π / 6 := by ring
  simp only [polarPoint, e, cos_pi_sub, sin_pi_sub, cos_pi_div_six, sin_pi_div_six, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.27: the polar point `(6, arctan 2)` is `(6√5/5, 12√5/5)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.27, p. 942"]
theorem exer_11_4_27 : polarPoint 6 (arctan 2) = (6 * √5 / 5, 12 * √5 / 5) := by
  have h5 : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have hs : (0 : ℝ) < √5 := by positivity
  have hss : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> field_simp <;> nlinarith

/-- Stitz-Zeager Exercise 11.4.31: the polar point `(2, π - arctan (1/2))` is `(-4√5/5, 2√5/5)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.31, p. 942"]
theorem exer_11_4_31 :
    polarPoint 2 (π - arctan (1 / 2)) = (-(4 * √5 / 5), 2 * √5 / 5) := by
  have h5 : √(1 + (1 / 2 : ℝ) ^ 2) = √5 / 2 := by
    rw [show 1 + (1 / 2 : ℝ) ^ 2 = 5 / 4 by norm_num, Real.sqrt_div (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : (0 : ℝ) < √5 := by positivity
  have hss : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  simp only [polarPoint, cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> field_simp <;> nlinarith

/-- Stitz-Zeager Exercise 11.4.36: the polar point `(13, arctan (12/5))` is `(5, 12)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.36, p. 942"]
theorem exer_11_4_36 : polarPoint 13 (arctan (12 / 5)) = (5, 12) := by
  have h5 : √(1 + (12 / 5 : ℝ) ^ 2) = 13 / 5 := x11d_sqrt_sq (by norm_num) (by norm_num)
  simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> norm_num

/-- Stitz-Zeager Exercise 11.4.38: the rectangular point `(3, √3)` has polar coordinates
`r ≥ 0`, `0 ≤ θ < 2π` exactly `(2√3, π/6)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.38, p. 942"]
theorem exer_11_4_38 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (3, √3) ↔ r = 2 * √3 ∧ θ = π / 6 := by
  have hpi := pi_pos
  have hs : (0 : ℝ) < √3 := by positivity
  have hss : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e : ((3 : ℝ), √3) = polarPoint (2 * √3) (π / 6) := by
    simp only [polarPoint, cos_pi_div_six, sin_pi_div_six, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e, x11d_conv (by positivity) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.39: the rectangular point `(7, -7)` has polar coordinates
`r ≥ 0`, `0 ≤ θ < 2π` exactly `(7√2, 7π/4)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.39, p. 942"]
theorem exer_11_4_39 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (7, -7) ↔ r = 7 * √2 ∧ θ = 7 * π / 4 := by
  have hpi := pi_pos
  have hs : (0 : ℝ) < √2 := by positivity
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : ((7 : ℝ), -7) = polarPoint (7 * √2) (7 * π / 4) := by
    have : 7 * π / 4 = -(π / 4) + 2 * π := by ring
    simp only [polarPoint, this, cos_add_two_pi, sin_add_two_pi, cos_neg, sin_neg, cos_pi_div_four,
      sin_pi_div_four, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e, x11d_conv (by positivity) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.43: the rectangular point `(-4, -4√3)` has polar coordinates
`r ≥ 0`, `0 ≤ θ < 2π` exactly `(8, 4π/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.43, p. 942"]
theorem exer_11_4_43 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-4, -(4 * √3)) ↔ r = 8 ∧ θ = 4 * π / 3 := by
  have hpi := pi_pos
  have e : ((-4 : ℝ), -(4 * √3)) = polarPoint 8 (4 * π / 3) := by
    have : 4 * π / 3 = π / 3 + π := by ring
    simp only [polarPoint, this, cos_add_pi, sin_add_pi, cos_pi_div_three, sin_pi_div_three,
      Prod.mk.injEq]
    constructor <;> ring
  rw [e, x11d_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.47: the rectangular point `(6, 8)` has polar coordinates
`r ≥ 0`, `0 ≤ θ < 2π` exactly `(10, arctan (4/3))`. -/
@[kb "stitzzeager2013" "Exercise 11.4.47, p. 943"]
theorem exer_11_4_47 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (6, 8) ↔ r = 10 ∧ θ = arctan (4 / 3) := by
  have hpi := pi_pos
  have h5 : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := x11d_sqrt_sq (by norm_num) (by norm_num)
  have e : ((6 : ℝ), 8) = polarPoint 10 (arctan (4 / 3)) := by
    simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 ≤ arctan (4 / 3) := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two (4 / 3)
  rw [e, x11d_conv (by norm_num) h0 (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.49: the rectangular point `(-8, 1)` has polar coordinates
`r ≥ 0`, `0 ≤ θ < 2π` exactly `(√65, π - arctan (1/8))`. -/
@[kb "stitzzeager2013" "Exercise 11.4.49, p. 943"]
theorem exer_11_4_49 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-8, 1) ↔ r = √65 ∧ θ = π - arctan (1 / 8) := by
  have hpi := pi_pos
  have h5 : √(1 + (1 / 8 : ℝ) ^ 2) = √65 / 8 := by
    rw [show 1 + (1 / 8 : ℝ) ^ 2 = 65 / 64 by norm_num, Real.sqrt_div (by norm_num)]
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : (0 : ℝ) < √65 := by positivity
  have hss : √65 * √65 = 65 := Real.mul_self_sqrt (by norm_num)
  have e : ((-8 : ℝ), 1) = polarPoint (√65) (π - arctan (1 / 8)) := by
    simp only [polarPoint, cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> field_simp
  have h0 : 0 ≤ arctan (1 / 8) := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two (1 / 8)
  rw [e, x11d_conv hs (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.51: the rectangular point `(-5, -12)` has polar coordinates
`r ≥ 0`, `0 ≤ θ < 2π` exactly `(13, π + arctan (12/5))`. -/
@[kb "stitzzeager2013" "Exercise 11.4.51, p. 943"]
theorem exer_11_4_51 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-5, -12) ↔ r = 13 ∧ θ = π + arctan (12 / 5) := by
  have hpi := pi_pos
  have h5 : √(1 + (12 / 5 : ℝ) ^ 2) = 13 / 5 := x11d_sqrt_sq (by norm_num) (by norm_num)
  have e : ((-5 : ℝ), -12) = polarPoint 13 (π + arctan (12 / 5)) := by
    rw [add_comm π]
    simp only [polarPoint, cos_add_pi, sin_add_pi, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 ≤ arctan (12 / 5) := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two (12 / 5)
  rw [e, x11d_conv (by norm_num) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.57: the point named by `(r, θ)` is on `x = 6` exactly when
`r cos θ = 6`, i.e. `r = 6 sec θ` (where `cos θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.57, p. 943"]
theorem exer_11_4_57 (r θ : ℝ) (h : cos θ ≠ 0) :
    (polarPoint r θ).1 = 6 ↔ r = 6 * (cos θ)⁻¹ := by
  simp only [polarPoint]
  rw [eq_mul_inv_iff_mul_eq₀ h]

/-- Stitz-Zeager Exercise 11.4.66: the point named by `(r, θ)` is on the line `y = 4x - 19` exactly when
`r = 19 / (4 cos θ - sin θ)` (where `4 cos θ - sin θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.66, p. 943"]
theorem exer_11_4_66 (r θ : ℝ) (h : 4 * cos θ - sin θ ≠ 0) :
    (polarPoint r θ).2 = 4 * (polarPoint r θ).1 - 19 ↔ r = 19 / (4 * cos θ - sin θ) := by
  simp only [polarPoint]
  rw [eq_div_iff h]
  constructor <;> intro h' <;> linarith

/-- Stitz-Zeager Exercise 11.4.70: the point named by `(r, θ)` is on `x² + y² - 2y = 0` exactly when
`r = 0` or `r = 2 sin θ`. -/
@[kb "stitzzeager2013" "Exercise 11.4.70, p. 943"]
theorem exer_11_4_70 (r θ : ℝ) :
    (polarPoint r θ).1 ^ 2 + (polarPoint r θ).2 ^ 2 - 2 * (polarPoint r θ).2 = 0 ↔
      r = 0 ∨ r = 2 * sin θ := by
  simp only [polarPoint]
  have h : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 - 2 * (r * sin θ) = r * (r - 2 * sin θ) := by
    nlinarith [sin_sq_add_cos_sq θ]
  rw [h, mul_eq_zero, sub_eq_zero]

/-- Stitz-Zeager Exercise 11.4.84: the polar graph `r = 4 cos θ` is the circle `(x - 2)² + y² = 4`. -/
@[kb "stitzzeager2013" "Exercise 11.4.84, p. 943"]
theorem exer_11_4_84 :
    {p : ℝ × ℝ | ∃ θ : ℝ, p = polarPoint (4 * cos θ) θ} = {p | (p.1 - 2) ^ 2 + p.2 ^ 2 = 4} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, h⟩
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    nlinarith [sin_sq_add_cos_sq θ]
  · intro h
    by_cases h0 : x ^ 2 + y ^ 2 = 0
    · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      refine ⟨π / 2, ?_⟩
      simp [polarPoint, hx, hy]
    · set z : ℂ := ⟨x, y⟩ with hz
      have hn : 0 < ‖z‖ := by
        rw [norm_pos_iff]
        intro hz0
        apply h0
        have h1 := congrArg Complex.re hz0
        have h2 := congrArg Complex.im hz0
        simp [hz] at h1 h2
        rw [h1, h2]; ring
      have hx : x = ‖z‖ * cos (Complex.arg z) := (Complex.norm_mul_cos_arg z).symm
      have hy : y = ‖z‖ * sin (Complex.arg z) := (Complex.norm_mul_sin_arg z).symm
      refine ⟨Complex.arg z, ?_⟩
      have e1 : x ^ 2 + y ^ 2 = ‖z‖ ^ 2 := by
        have hc := sin_sq_add_cos_sq (Complex.arg z)
        have : x ^ 2 + y ^ 2 = ‖z‖ ^ 2 * (sin (Complex.arg z) ^ 2 + cos (Complex.arg z) ^ 2) := by
          rw [hx, hy]; ring
        rw [this, hc, mul_one]
      have hr : ‖z‖ = 4 * cos (Complex.arg z) := by
        apply mul_left_cancel₀ hn.ne'
        nlinarith [e1, h, hx]
      simp only [polarPoint, Prod.mk.injEq]
      rw [← hr]
      exact ⟨hx, hy⟩

/-- Stitz-Zeager Exercise 11.4.88: the point named by `(r, θ)` is on `x = 7` exactly when
`r = 7 sec θ` (where `cos θ ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 11.4.88, p. 943"]
theorem exer_11_4_88 (r θ : ℝ) (h : cos θ ≠ 0) :
    r = 7 * (cos θ)⁻¹ ↔ (polarPoint r θ).1 = 7 := by
  simp only [polarPoint]
  rw [eq_mul_inv_iff_mul_eq₀ h]

/-- Stitz-Zeager Exercise 11.4.97: the origin has the polar names `(0, θ)` for every `θ`
(for example `(0, π)`, `(0, -117)`, `(0, 23π/4)`, `(0, 0)`). -/
@[kb "stitzzeager2013" "Exercise 11.4.97, p. 943"]
theorem exer_11_4_97 : ∀ θ : ℝ, polarPoint 0 θ = (0, 0) := by
  intro θ
  simp [polarPoint]

end UndergradKB.Precalculus.Course
