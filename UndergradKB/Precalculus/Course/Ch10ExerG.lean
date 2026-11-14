import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.TrigExtras

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.6
(exact values and algebraic expressions of inverse trigonometric functions)

`arccot` is `arccotR` (range `(0, π)`), `arcsec` is `arcsecCF` (range `[0, π/2) ∪ [π, 3π/2)`) and
`arccsc` is `arccscCF` (range `(0, π/2] ∪ (π, 3π/2]`), all from `UndergradKB.Precalculus.TrigExtras`. -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

private lemma arcsin_of {y x : ℝ} (h : sin x = y) (h1 : -(π / 2) ≤ x) (h2 : x ≤ π / 2) :
    arcsin y = x := by
  rw [← h]; exact arcsin_sin h1 h2

private lemma arccos_of {y x : ℝ} (h : cos x = y) (h1 : 0 ≤ x) (h2 : x ≤ π) : arccos y = x := by
  rw [← h]; exact arccos_cos h1 h2

private lemma arctan_of {y x : ℝ} (h : tan x = y) (h1 : -(π / 2) < x) (h2 : x < π / 2) :
    arctan y = x := by
  rw [← h]; exact arctan_tan h1 h2

private lemma arccot_of {y x : ℝ} (h : cos x / sin x = y) (h1 : 0 < x) (h2 : x < π) :
    arccotR y = x := by
  unfold arccotR
  have : y = tan (π / 2 - x) := by
    rw [tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]; exact h.symm
  rw [this, arctan_tan (by linarith) (by linarith)]; ring

private lemma sqrt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a = b ^ 2) : √a = b := by
  rw [h, Real.sqrt_sq hb]

private lemma arcsec_pos {x : ℝ} (h : 1 ≤ x) : arcsecCF x = arccos x⁻¹ := by
  unfold arcsecCF; simp [h]

private lemma arcsec_neg {x : ℝ} (h : ¬ 1 ≤ x) : arcsecCF x = 2 * π - arccos x⁻¹ := by
  unfold arcsecCF; simp [h]

private lemma arccsc_pos {x : ℝ} (h : 1 ≤ x) : arccscCF x = arcsin x⁻¹ := by
  unfold arccscCF; simp [h]

private lemma arccsc_neg {x : ℝ} (h : ¬ 1 ≤ x) : arccscCF x = π - arcsin x⁻¹ := by
  unfold arccscCF; simp [h]

private lemma three_half_le : (3 / 2 : ℝ) ≤ √3 := by
  have hp : 0 ≤ √3 := Real.sqrt_nonneg 3
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private lemma s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma s5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma c56 : cos (5 * π / 6) = -(√3 / 2) ∧ sin (5 * π / 6) = 1 / 2 := by
  rw [show 5 * π / 6 = π - π / 6 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_six, sin_pi_div_six]
  exact ⟨rfl, rfl⟩

private lemma c34 : cos (3 * π / 4) = -(√2 / 2) ∧ sin (3 * π / 4) = √2 / 2 := by
  rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four]
  exact ⟨rfl, rfl⟩

private lemma c23 : cos (2 * π / 3) = -(1 / 2) ∧ sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_three,
    sin_pi_div_three]; exact ⟨rfl, rfl⟩

private lemma inv_sqrt3 : (1 : ℝ) / √3 = √3 / 3 := by
  have hp : 0 < √3 := by positivity
  field_simp; nlinarith [s3]

/-- Stitz-Zeager Exercise 10.6.1: `arcsin(-1) = -π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.1, p. 853"]
theorem exer_10_6_1 : arcsin (-1) = -(π / 2) := arcsin_neg_one

/-- Stitz-Zeager Exercise 10.6.2: `arcsin(-√3/2) = -π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.2, p. 853"]
theorem exer_10_6_2 : arcsin (-(√3 / 2)) = -(π / 3) :=
  arcsin_of (by rw [sin_neg, sin_pi_div_three]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.3: `arcsin(-√2/2) = -π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.3, p. 853"]
theorem exer_10_6_3 : arcsin (-(√2 / 2)) = -(π / 4) :=
  arcsin_of (by rw [sin_neg, sin_pi_div_four]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.4: `arcsin(-1/2) = -π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.4, p. 853"]
theorem exer_10_6_4 : arcsin (-(1 / 2)) = -(π / 6) :=
  arcsin_of (by rw [sin_neg, sin_pi_div_six]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.8: `arcsin(√3/2) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.8, p. 853"]
theorem exer_10_6_8 : arcsin (√3 / 2) = π / 3 :=
  arcsin_of sin_pi_div_three (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.10: `arccos(-1) = π`. -/
@[kb "stitzzeager2013" "Exercise 10.6.10, p. 853"]
theorem exer_10_6_10 : arccos (-1) = π := arccos_neg_one

/-- Stitz-Zeager Exercise 10.6.11: `arccos(-√3/2) = 5π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.11, p. 853"]
theorem exer_10_6_11 : arccos (-(√3 / 2)) = 5 * π / 6 :=
  arccos_of c56.1 (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.12: `arccos(-√2/2) = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.12, p. 853"]
theorem exer_10_6_12 : arccos (-(√2 / 2)) = 3 * π / 4 :=
  arccos_of c34.1 (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.13: `arccos(-1/2) = 2π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.13, p. 853"]
theorem exer_10_6_13 : arccos (-(1 / 2)) = 2 * π / 3 :=
  arccos_of c23.1 (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.17: `arccos(√3/2) = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.17, p. 853"]
theorem exer_10_6_17 : arccos (√3 / 2) = π / 6 :=
  arccos_of cos_pi_div_six (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.19: `arctan(-√3) = -π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.19, p. 853"]
theorem exer_10_6_19 : arctan (-√3) = -(π / 3) :=
  arctan_of (by rw [tan_neg, tan_pi_div_three]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.20: `arctan(-1) = -π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.20, p. 853"]
theorem exer_10_6_20 : arctan (-1) = -(π / 4) := by
  rw [arctan_neg, arctan_one]

/-- Stitz-Zeager Exercise 10.6.21: `arctan(-√3/3) = -π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.21, p. 853"]
theorem exer_10_6_21 : arctan (-(√3 / 3)) = -(π / 6) :=
  arctan_of (by rw [tan_neg, tan_pi_div_six, inv_sqrt3]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.23: `arctan(√3/3) = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.23, p. 853"]
theorem exer_10_6_23 : arctan (√3 / 3) = π / 6 :=
  arctan_of (by rw [tan_pi_div_six, inv_sqrt3]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.26: `arccot(-√3) = 5π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.26, p. 853"]
theorem exer_10_6_26 : arccotR (-√3) = 5 * π / 6 := by
  refine arccot_of ?_ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [c56.1, c56.2]; field_simp

/-- Stitz-Zeager Exercise 10.6.27: `arccot(-1) = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.27, p. 853"]
theorem exer_10_6_27 : arccotR (-1) = 3 * π / 4 := by
  have hp : 0 < √2 := by positivity
  refine arccot_of ?_ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [c34.1, c34.2]; field_simp

/-- Stitz-Zeager Exercise 10.6.28: `arccot(-√3/3) = 2π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.28, p. 853"]
theorem exer_10_6_28 : arccotR (-(√3 / 3)) = 2 * π / 3 := by
  have hp : 0 < √3 := by positivity
  refine arccot_of ?_ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [c23.1, c23.2]; field_simp; nlinarith [s3]

/-- Stitz-Zeager Exercise 10.6.29: `arccot(0) = π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.29, p. 853"]
theorem exer_10_6_29 : arccotR 0 = π / 2 := by simp [arccotR]

/-- Stitz-Zeager Exercise 10.6.33: `arcsec 2 = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.33, p. 853"]
theorem exer_10_6_33 : arcsecCF 2 = π / 3 := by
  rw [arcsec_pos (by norm_num), show (2 : ℝ)⁻¹ = cos (π / 3) by rw [cos_pi_div_three]; norm_num]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.34: `arccsc 2 = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.34, p. 853"]
theorem exer_10_6_34 : arccscCF 2 = π / 6 := by
  rw [arccsc_pos (by norm_num), show (2 : ℝ)⁻¹ = sin (π / 6) by rw [sin_pi_div_six]; norm_num]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.35: `arcsec √2 = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.35, p. 853"]
theorem exer_10_6_35 : arcsecCF (√2) = π / 4 := by
  have hp : 0 < √2 := by positivity
  have h1 : 1 ≤ √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  rw [arcsec_pos h1, show (√2)⁻¹ = cos (π / 4) by
    rw [cos_pi_div_four]; field_simp; nlinarith [s2]]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.37: `arcsec(2√3/3) = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.37, p. 853"]
theorem exer_10_6_37 : arcsecCF (2 * √3 / 3) = π / 6 := by
  have hp : 0 < √3 := by positivity
  have h1 : 1 ≤ 2 * √3 / 3 := by
    linarith [three_half_le]
  rw [arcsec_pos h1, show (2 * √3 / 3)⁻¹ = cos (π / 6) by
    rw [cos_pi_div_six]; field_simp; nlinarith [s3]]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.38: `arccsc(2√3/3) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.38, p. 853"]
theorem exer_10_6_38 : arccscCF (2 * √3 / 3) = π / 3 := by
  have hp : 0 < √3 := by positivity
  have h1 : 1 ≤ 2 * √3 / 3 := by
    linarith [three_half_le]
  rw [arccsc_pos h1, show (2 * √3 / 3)⁻¹ = sin (π / 3) by
    rw [sin_pi_div_three]; field_simp; nlinarith [s3]]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.41: `arcsec(-2) = 4π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.41, p. 853"]
theorem exer_10_6_41 : arcsecCF (-2) = 4 * π / 3 := by
  rw [arcsec_neg (by norm_num), show (-2 : ℝ)⁻¹ = cos (2 * π / 3) by rw [c23.1]; norm_num,
    arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- Stitz-Zeager Exercise 10.6.43: `arcsec(-2√3/3) = 7π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.43, p. 853"]
theorem exer_10_6_43 : arcsecCF (-(2 * √3 / 3)) = 7 * π / 6 := by
  have hp : 0 < √3 := by positivity
  have h1 : ¬ (1 ≤ -(2 * √3 / 3)) := by
    have : 0 < 2 * √3 / 3 := by positivity
    intro h; linarith
  rw [arcsec_neg h1, show (-(2 * √3 / 3))⁻¹ = cos (5 * π / 6) by
    rw [c56.1]; field_simp; nlinarith [s3],
    arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- Stitz-Zeager Exercise 10.6.45: `arccsc(-2) = 7π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.45, p. 853"]
theorem exer_10_6_45 : arccscCF (-2) = 7 * π / 6 := by
  rw [arccsc_neg (by norm_num), show (-2 : ℝ)⁻¹ = -(sin (π / 6)) by
    rw [sin_pi_div_six]; norm_num, ← sin_neg,
    arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- Stitz-Zeager Exercise 10.6.48: `arccsc(-1) = 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.48, p. 853"]
theorem exer_10_6_48 : arccscCF (-1) = 3 * π / 2 := by
  rw [arccsc_neg (by norm_num), inv_neg, inv_one, arcsin_neg_one]; ring

/-- Stitz-Zeager Exercise 10.6.57: `sin(arcsin(1/2)) = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.57, p. 854"]
theorem exer_10_6_57 : sin (arcsin (1 / 2)) = 1 / 2 := sin_arcsin (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.60: `sin(arcsin(-0.42)) = -0.42`. -/
@[kb "stitzzeager2013" "Exercise 10.6.60, p. 854"]
theorem exer_10_6_60 : sin (arcsin (-0.42)) = -0.42 := sin_arcsin (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.61: `sin(arcsin(5/4))` is undefined, because `5/4` is outside the
domain `[-1, 1]` of arcsine (and sine never takes the value `5/4`). -/
@[kb "stitzzeager2013" "Exercise 10.6.61, p. 854"]
theorem exer_10_6_61 : ¬ (-1 ≤ (5 / 4 : ℝ) ∧ (5 / 4 : ℝ) ≤ 1) ∧ ∀ x : ℝ, sin x ≠ 5 / 4 := by
  refine ⟨by norm_num, fun x h => ?_⟩
  have := sin_le_one x
  linarith

/-- Stitz-Zeager Exercise 10.6.66: `cos(arccos π)` is undefined, because `π` is outside `[-1, 1]`. -/
@[kb "stitzzeager2013" "Exercise 10.6.66, p. 854"]
theorem exer_10_6_66 : ¬ (-1 ≤ π ∧ π ≤ 1) := by
  have := Real.pi_gt_three
  intro h; linarith [h.2]

/-- Stitz-Zeager Exercise 10.6.67: `tan(arctan(-1)) = -1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.67, p. 854"]
theorem exer_10_6_67 : tan (arctan (-1)) = -1 := tan_arctan _

/-- Stitz-Zeager Exercise 10.6.71: `tan(arctan(3π)) = 3π`. -/
@[kb "stitzzeager2013" "Exercise 10.6.71, p. 854"]
theorem exer_10_6_71 : tan (arctan (3 * π)) = 3 * π := tan_arctan _

/-- Stitz-Zeager Exercise 10.6.74: `cot(arccot(-7/24)) = -7/24`. -/
@[kb "stitzzeager2013" "Exercise 10.6.74, p. 854"]
theorem exer_10_6_74 : Real.cot (arccotR (-(7 / 24))) = -(7 / 24) :=
  (arccotR_properties.2.1) _

/-- Stitz-Zeager Exercise 10.6.77: `sec(arcsec 2) = 2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.77, p. 854"]
theorem exer_10_6_77 : (cos (arcsecCF 2))⁻¹ = 2 := by
  rw [exer_10_6_33, cos_pi_div_three]; norm_num

/-- Stitz-Zeager Exercise 10.6.89: `arcsin(sin(3π/4)) = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.89, p. 855"]
theorem exer_10_6_89 : arcsin (sin (3 * π / 4)) = π / 4 := by
  rw [c34.2, ← sin_pi_div_four]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.90: `arcsin(sin(11π/6)) = -π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.90, p. 855"]
theorem exer_10_6_90 : arcsin (sin (11 * π / 6)) = -(π / 6) := by
  have h : sin (11 * π / 6) = sin (-(π / 6)) := by
    rw [show 11 * π / 6 = -(π / 6) + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      sin_add_int_mul_two_pi]
  rw [h]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.91: `arcsin(sin(4π/3)) = -π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.91, p. 855"]
theorem exer_10_6_91 : arcsin (sin (4 * π / 3)) = -(π / 3) := by
  have h : sin (4 * π / 3) = sin (-(π / 3)) := by
    rw [show 4 * π / 3 = π / 3 + π by ring, sin_add_pi, sin_neg]
  rw [h]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.93: `arccos(cos(2π/3)) = 2π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.93, p. 855"]
theorem exer_10_6_93 : arccos (cos (2 * π / 3)) = 2 * π / 3 :=
  arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.94: `arccos(cos(3π/2)) = π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.94, p. 855"]
theorem exer_10_6_94 : arccos (cos (3 * π / 2)) = π / 2 := by
  have h : cos (3 * π / 2) = cos (π / 2) := by
    rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; simp
  rw [h]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.96: `arccos(cos(5π/4)) = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.96, p. 855"]
theorem exer_10_6_96 : arccos (cos (5 * π / 4)) = 3 * π / 4 := by
  have h : cos (5 * π / 4) = cos (3 * π / 4) := by
    rw [show 5 * π / 4 = π / 4 + π by ring, cos_add_pi, c34.1, cos_pi_div_four]
  rw [h]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.101: `arctan(tan(2π/3)) = -π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.101, p. 855"]
theorem exer_10_6_101 : arctan (tan (2 * π / 3)) = -(π / 3) := by
  have h : tan (2 * π / 3) = tan (-(π / 3)) := by
    rw [show 2 * π / 3 = -(π / 3) + ((1 : ℤ) : ℝ) * π by push_cast; ring, tan_add_int_mul_pi]
  rw [h]
  exact arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.106: `arccot(cot(2π/3)) = 2π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.106, p. 855"]
theorem exer_10_6_106 : arccotR (cos (2 * π / 3) / sin (2 * π / 3)) = 2 * π / 3 :=
  arccot_of rfl (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.108: `arcsec(sec(4π/3)) = 4π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.108, p. 855"]
theorem exer_10_6_108 : arcsecCF ((cos (4 * π / 3))⁻¹) = 4 * π / 3 := by
  rw [show 4 * π / 3 = π / 3 + π by ring, cos_add_pi, cos_pi_div_three]
  have : (-(1 / 2 : ℝ))⁻¹ = -2 := by norm_num
  rw [this, exer_10_6_41]; ring

/-- Stitz-Zeager Exercise 10.6.109: `arcsec(sec(5π/6)) = 7π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.109, p. 855"]
theorem exer_10_6_109 : arcsecCF ((cos (5 * π / 6))⁻¹) = 7 * π / 6 := by
  rw [c56.1, inv_neg]
  have hp : 0 < √3 := by positivity
  have : (√3 / 2)⁻¹ = 2 * √3 / 3 := by field_simp; nlinarith [s3]
  rw [this, exer_10_6_43]

/-- Stitz-Zeager Exercise 10.6.131: `sin(arccos(-1/2)) = √3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.131, p. 856"]
theorem exer_10_6_131 : sin (arccos (-(1 / 2))) = √3 / 2 := by
  rw [sin_arccos]
  exact sqrt_of_sq (by positivity) (by rw [div_pow, s3]; norm_num)

/-- Stitz-Zeager Exercise 10.6.132: `sin(arccos(3/5)) = 4/5`. -/
@[kb "stitzzeager2013" "Exercise 10.6.132, p. 856"]
theorem exer_10_6_132 : sin (arccos (3 / 5)) = 4 / 5 := by
  rw [sin_arccos]
  exact sqrt_of_sq (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.133: `sin(arctan(-2)) = -2√5/5`. -/
@[kb "stitzzeager2013" "Exercise 10.6.133, p. 856"]
theorem exer_10_6_133 : sin (arctan (-2)) = -(2 * √5 / 5) := by
  rw [sin_arctan]
  have h : √(1 + (-2 : ℝ) ^ 2) = √5 := by norm_num
  have hp : 0 < √5 := by positivity
  rw [h]; field_simp; nlinarith [s5]

/-- Stitz-Zeager Exercise 10.6.136: `cos(arcsin(-5/13)) = 12/13`. -/
@[kb "stitzzeager2013" "Exercise 10.6.136, p. 856"]
theorem exer_10_6_136 : cos (arcsin (-(5 / 13))) = 12 / 13 := by
  rw [cos_arcsin]
  exact sqrt_of_sq (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.137: `cos(arctan √7) = √2/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.137, p. 856"]
theorem exer_10_6_137 : cos (arctan (√7)) = √2 / 4 := by
  rw [cos_arctan, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
  have h : √(1 + (7 : ℝ)) = 2 * √2 := by
    rw [show (1 + 7 : ℝ) = 8 by norm_num]
    exact sqrt_of_sq (by positivity) (by rw [mul_pow, s2]; norm_num)
  have hp : 0 < √2 := by positivity
  rw [h]; field_simp; nlinarith [s2]

/-- Stitz-Zeager Exercise 10.6.140: `tan(arcsin(-2√5/5)) = -2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.140, p. 856"]
theorem exer_10_6_140 : tan (arcsin (-(2 * √5 / 5))) = -2 := by
  rw [tan_arcsin]
  have hp : 0 < √5 := by positivity
  have h : √(1 - (-(2 * √5 / 5)) ^ 2) = √5 / 5 := by
    refine sqrt_of_sq (by positivity) ?_
    rw [neg_sq, div_pow, div_pow, mul_pow, s5]; norm_num
  rw [h]; field_simp

/-- Stitz-Zeager Exercise 10.6.141: `tan(arccos(-1/2)) = -√3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.141, p. 856"]
theorem exer_10_6_141 : tan (arccos (-(1 / 2))) = -√3 := by
  rw [tan_arccos]
  have h : √(1 - (-(1 / 2 : ℝ)) ^ 2) = √3 / 2 := by
    refine sqrt_of_sq (by positivity) ?_
    rw [neg_sq, div_pow, div_pow, s3]; norm_num
  rw [h]; field_simp

/-- Stitz-Zeager Exercise 10.6.144: `cot(arcsin(12/13)) = 5/12`. -/
@[kb "stitzzeager2013" "Exercise 10.6.144, p. 856"]
theorem exer_10_6_144 : cos (arcsin (12 / 13)) / sin (arcsin (12 / 13)) = 5 / 12 := by
  rw [cos_arcsin, sin_arcsin (by norm_num) (by norm_num)]
  rw [sqrt_of_sq (a := 1 - (12 / 13 : ℝ) ^ 2) (b := 5 / 13) (by norm_num) (by norm_num)]
  norm_num

/-- Stitz-Zeager Exercise 10.6.148: `sec(arccos(√3/2)) = 2√3/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.148, p. 856"]
theorem exer_10_6_148 : (cos (arccos (√3 / 2)))⁻¹ = 2 * √3 / 3 := by
  have hp : 0 < √3 := by positivity
  rw [cos_arccos (by linarith [show √3 ≤ 2 by nlinarith [s3]]) (by nlinarith [s3])]
  field_simp; nlinarith [s3]

/-- Stitz-Zeager Exercise 10.6.150: `sec(arctan 10) = √101`. -/
@[kb "stitzzeager2013" "Exercise 10.6.150, p. 856"]
theorem exer_10_6_150 : (cos (arctan 10))⁻¹ = √101 := by
  rw [cos_arctan]
  norm_num

/-- Stitz-Zeager Exercise 10.6.155: `sin(arcsin(5/13) + π/4) = 17√2/26`. -/
@[kb "stitzzeager2013" "Exercise 10.6.155, p. 856"]
theorem exer_10_6_155 : sin (arcsin (5 / 13) + π / 4) = 17 * √2 / 26 := by
  rw [sin_add, sin_arcsin (by norm_num) (by norm_num), cos_arcsin,
    sqrt_of_sq (a := 1 - (5 / 13 : ℝ) ^ 2) (b := 12 / 13) (by norm_num) (by norm_num),
    cos_pi_div_four, sin_pi_div_four]
  ring

/-- Stitz-Zeager Exercise 10.6.158: `sin(2 arcsin(-4/5)) = -24/25`. -/
@[kb "stitzzeager2013" "Exercise 10.6.158, p. 856"]
theorem exer_10_6_158 : sin (2 * arcsin (-(4 / 5))) = -(24 / 25) := by
  rw [sin_two_mul, sin_arcsin (by norm_num) (by norm_num), cos_arcsin,
    sqrt_of_sq (a := 1 - (-(4 / 5) : ℝ) ^ 2) (b := 3 / 5) (by norm_num) (by norm_num)]
  norm_num

/-- Stitz-Zeager Exercise 10.6.160: `sin(2 arctan 2) = 4/5`. -/
@[kb "stitzzeager2013" "Exercise 10.6.160, p. 856"]
theorem exer_10_6_160 : sin (2 * arctan 2) = 4 / 5 := by
  rw [sin_two_mul, sin_arctan, cos_arctan]
  have h : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have hp : 0 < √5 := by positivity
  rw [h]; field_simp; nlinarith [s5]

/-- Stitz-Zeager Exercise 10.6.161: `cos(2 arcsin(3/5)) = 7/25`. -/
@[kb "stitzzeager2013" "Exercise 10.6.161, p. 856"]
theorem exer_10_6_161 : cos (2 * arcsin (3 / 5)) = 7 / 25 := by
  rw [cos_two_mul, cos_arcsin,
    sqrt_of_sq (a := 1 - (3 / 5 : ℝ) ^ 2) (b := 4 / 5) (by norm_num) (by norm_num)]
  norm_num

/-- Stitz-Zeager Exercise 10.6.162: `cos(2 arcsec(25/7)) = -527/625`. -/
@[kb "stitzzeager2013" "Exercise 10.6.162, p. 856"]
theorem exer_10_6_162 : cos (2 * arcsecCF (25 / 7)) = -(527 / 625) := by
  rw [arcsec_pos (by norm_num), cos_two_mul, show (25 / 7 : ℝ)⁻¹ = 7 / 25 by norm_num,
    cos_arccos (by norm_num) (by norm_num)]
  norm_num

/-- Stitz-Zeager Exercise 10.6.165: `sin(arccos x) = √(1 - x²)` for `-1 ≤ x ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.165, p. 857"]
theorem exer_10_6_165 (x : ℝ) (_ : -1 ≤ x ∧ x ≤ 1) : sin (arccos x) = √(1 - x ^ 2) :=
  sin_arccos x

/-- Stitz-Zeager Exercise 10.6.166: `cos(arctan x) = 1/√(1 + x²)` for all `x`. -/
@[kb "stitzzeager2013" "Exercise 10.6.166, p. 857"]
theorem exer_10_6_166 (x : ℝ) : cos (arctan x) = 1 / √(1 + x ^ 2) := cos_arctan x

/-- Stitz-Zeager Exercise 10.6.167: `tan(arcsin x) = x/√(1 - x²)` for `-1 < x < 1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.167, p. 857"]
theorem exer_10_6_167 (x : ℝ) (_ : -1 < x ∧ x < 1) : tan (arcsin x) = x / √(1 - x ^ 2) :=
  tan_arcsin x

/-- Stitz-Zeager Exercise 10.6.168: `sec(arctan x) = √(1 + x²)` for all `x`. -/
@[kb "stitzzeager2013" "Exercise 10.6.168, p. 857"]
theorem exer_10_6_168 (x : ℝ) : (cos (arctan x))⁻¹ = √(1 + x ^ 2) := by
  rw [cos_arctan]; simp

/-- Stitz-Zeager Exercise 10.6.170: `sin(2 arctan x) = 2x/(x² + 1)` for all `x`. -/
@[kb "stitzzeager2013" "Exercise 10.6.170, p. 857"]
theorem exer_10_6_170 (x : ℝ) : sin (2 * arctan x) = 2 * x / (x ^ 2 + 1) := by
  rw [sin_two_mul, sin_arctan, cos_arctan]
  have h : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h2 : √(1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hx : x ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  linear_combination (-x) * h2

/-- Stitz-Zeager Exercise 10.6.171: `sin(2 arccos x) = 2x√(1 - x²)` for `-1 ≤ x ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.171, p. 857"]
theorem exer_10_6_171 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    sin (2 * arccos x) = 2 * x * √(1 - x ^ 2) := by
  rw [sin_two_mul, sin_arccos, cos_arccos hx.1 hx.2]; ring

/-- Stitz-Zeager Exercise 10.6.172: `cos(2 arctan x) = (1 - x²)/(1 + x²)` for all `x`. -/
@[kb "stitzzeager2013" "Exercise 10.6.172, p. 857"]
theorem exer_10_6_172 (x : ℝ) : cos (2 * arctan x) = (1 - x ^ 2) / (1 + x ^ 2) := by
  rw [cos_two_mul, cos_arctan, div_pow]
  have h2 : √(1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hx : 1 + x ^ 2 ≠ 0 := by positivity
  rw [h2]; field_simp; ring

/-- Stitz-Zeager Exercise 10.6.173: `sin(arccos(2x)) = √(1 - 4x²)` for `-1/2 ≤ x ≤ 1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.173, p. 857"]
theorem exer_10_6_173 (x : ℝ) (_ : -(1 / 2) ≤ x ∧ x ≤ 1 / 2) :
    sin (arccos (2 * x)) = √(1 - 4 * x ^ 2) := by
  rw [sin_arccos]; congr 1; ring

/-- Stitz-Zeager Exercise 10.6.176: `cos(arctan(3x)) = 1/√(1 + 9x²)` for all `x`. -/
@[kb "stitzzeager2013" "Exercise 10.6.176, p. 857"]
theorem exer_10_6_176 (x : ℝ) : cos (arctan (3 * x)) = 1 / √(1 + 9 * x ^ 2) := by
  rw [cos_arctan]; congr 2; ring

/-- Stitz-Zeager Exercise 10.6.177: `sin(2 arcsin(7x)) = 14x√(1 - 49x²)` for `-1/7 ≤ x ≤ 1/7`. -/
@[kb "stitzzeager2013" "Exercise 10.6.177, p. 857"]
theorem exer_10_6_177 (x : ℝ) (hx : -(1 / 7) ≤ x ∧ x ≤ 1 / 7) :
    sin (2 * arcsin (7 * x)) = 14 * x * √(1 - 49 * x ^ 2) := by
  rw [sin_two_mul, sin_arcsin (by linarith [hx.1]) (by linarith [hx.2]), cos_arcsin]
  have : (1 - (7 * x) ^ 2 : ℝ) = 1 - 49 * x ^ 2 := by ring
  rw [this]; ring

/-- Stitz-Zeager Exercise 10.6.179: `cos(2 arcsin(4x)) = 1 - 32x²` for `-1/4 ≤ x ≤ 1/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.179, p. 857"]
theorem exer_10_6_179 (x : ℝ) (hx : -(1 / 4) ≤ x ∧ x ≤ 1 / 4) :
    cos (2 * arcsin (4 * x)) = 1 - 32 * x ^ 2 := by
  have h := sin_arcsin (x := 4 * x) (by linarith [hx.1]) (by linarith [hx.2])
  have h2 := sin_sq_add_cos_sq (arcsin (4 * x))
  rw [h] at h2
  rw [cos_two_mul]; nlinarith [h2]

/-- Stitz-Zeager Exercise 10.6.181: `sin(arcsin x + arccos x) = 1` for `-1 ≤ x ≤ 1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.181, p. 857"]
theorem exer_10_6_181 (x : ℝ) (_hx : -1 ≤ x ∧ x ≤ 1) : sin (arcsin x + arccos x) = 1 := by
  rw [arccos_eq_pi_div_two_sub_arcsin, add_sub_cancel, sin_pi_div_two]

end UndergradKB.Precalculus.Course
