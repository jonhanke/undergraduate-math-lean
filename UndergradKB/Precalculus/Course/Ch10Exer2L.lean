import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.TrigExtras
import UndergradKB.Precalculus.Course.Ch10Extra

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.6 (inverse trigonometric functions)

`arccot` is `arccotR` (range `(0, π)`). `arcsecCF`, `arccscCF` (ranges `[0, π/2) ∪ [π, 3π/2)` and
`(0, π/2] ∪ (π, 3π/2]`) are from `TrigExtras`; `arcsec`, `arccsc` (ranges `[0, π] \ {π/2}` and
`[-π/2, π/2] \ {0}`) are from `Ch10Extra`. -/

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


private lemma c1 : (1 : ℝ) / 2 = 2⁻¹ := by norm_num

private lemma arcsec_eq {x : ℝ} (h : arcsec x = arccos (1 / x)) : arcsec x = arccos (1 / x) := h

/-- Stitz-Zeager Exercise 10.6.5: `arcsin 0 = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.5, p. 853"]
theorem exer_10_6_5 : arcsin 0 = 0 := arcsin_zero

/-- Stitz-Zeager Exercise 10.6.6: `arcsin(1/2) = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.6, p. 853"]
theorem exer_10_6_6 : arcsin (1 / 2) = π / 6 :=
  arcsin_of sin_pi_div_six (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.7: `arcsin(√2/2) = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.7, p. 853"]
theorem exer_10_6_7 : arcsin (√2 / 2) = π / 4 :=
  arcsin_of sin_pi_div_four (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.9: `arcsin 1 = π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.9, p. 853"]
theorem exer_10_6_9 : arcsin 1 = π / 2 := arcsin_one

/-- Stitz-Zeager Exercise 10.6.14: `arccos 0 = π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.14, p. 853"]
theorem exer_10_6_14 : arccos 0 = π / 2 := arccos_zero

/-- Stitz-Zeager Exercise 10.6.15: `arccos(1/2) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.15, p. 853"]
theorem exer_10_6_15 : arccos (1 / 2) = π / 3 :=
  arccos_of cos_pi_div_three (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.16: `arccos(√2/2) = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.16, p. 853"]
theorem exer_10_6_16 : arccos (√2 / 2) = π / 4 :=
  arccos_of cos_pi_div_four (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.18: `arccos 1 = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.18, p. 853"]
theorem exer_10_6_18 : arccos 1 = 0 := arccos_one

/-- Stitz-Zeager Exercise 10.6.22: `arctan 0 = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.22, p. 853"]
theorem exer_10_6_22 : arctan 0 = 0 := arctan_zero

/-- Stitz-Zeager Exercise 10.6.24: `arctan 1 = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.24, p. 853"]
theorem exer_10_6_24 : arctan 1 = π / 4 := arctan_one

/-- Stitz-Zeager Exercise 10.6.25: `arctan √3 = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.25, p. 853"]
theorem exer_10_6_25 : arctan √3 = π / 3 :=
  arctan_of tan_pi_div_three (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.30: `arccot(√3/3) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.30, p. 853"]
theorem exer_10_6_30 : arccotR (√3 / 3) = π / 3 := by
  refine arccot_of ?_ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [cos_pi_div_three, sin_pi_div_three]
  have hp : 0 < √3 := by positivity
  field_simp; nlinarith [s3]

/-- Stitz-Zeager Exercise 10.6.31: `arccot 1 = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.31, p. 853"]
theorem exer_10_6_31 : arccotR 1 = π / 4 := by
  refine arccot_of ?_ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [cos_pi_div_four, sin_pi_div_four]
  have hp : 0 < √2 := by positivity
  field_simp

/-- Stitz-Zeager Exercise 10.6.32: `arccot √3 = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.32, p. 853"]
theorem exer_10_6_32 : arccotR √3 = π / 6 := by
  refine arccot_of ?_ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [cos_pi_div_six, sin_pi_div_six]
  field_simp

/-- Stitz-Zeager Exercise 10.6.36: `arccsc √2 = π/4` (range `(0, π/2] ∪ (π, 3π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.36, p. 853"]
theorem exer_10_6_36 : arccscCF √2 = π / 4 := by
  have h1 : (1 : ℝ) ≤ √2 := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  rw [arccsc_pos h1, show (√2)⁻¹ = sin (π / 4) by rw [sin_pi_div_four]; field_simp; nlinarith [s2]]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.39: `arcsec 1 = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.39, p. 853"]
theorem exer_10_6_39 : arcsecCF 1 = 0 := by
  rw [arcsec_pos le_rfl]; simp

/-- Stitz-Zeager Exercise 10.6.40: `arccsc 1 = π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.40, p. 853"]
theorem exer_10_6_40 : arccscCF 1 = π / 2 := by
  rw [arccsc_pos le_rfl]; simp

/-- Stitz-Zeager Exercise 10.6.42: `arcsec(-√2) = 5π/4` (range `[0, π/2) ∪ [π, 3π/2)`). -/
@[kb "stitzzeager2013" "Exercise 10.6.42, p. 853"]
theorem exer_10_6_42 : arcsecCF (-√2) = 5 * π / 4 := by
  have hp : 0 < √2 := by positivity
  have h1 : ¬ (1 ≤ -√2) := by intro h; linarith
  rw [arcsec_neg h1, show (-√2)⁻¹ = cos (3 * π / 4) by
    rw [c34.1]; field_simp; nlinarith [s2], arccos_cos (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])]
  ring

/-- Stitz-Zeager Exercise 10.6.44: `arcsec(-1) = π`. -/
@[kb "stitzzeager2013" "Exercise 10.6.44, p. 853"]
theorem exer_10_6_44 : arcsecCF (-1) = π := by
  rw [arcsec_neg (by norm_num)]; simp; ring

/-- Stitz-Zeager Exercise 10.6.46: `arccsc(-√2) = 5π/4` (range `(0, π/2] ∪ (π, 3π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.46, p. 853"]
theorem exer_10_6_46 : arccscCF (-√2) = 5 * π / 4 := by
  have hp : 0 < √2 := by positivity
  have h1 : ¬ (1 ≤ -√2) := by intro h; linarith
  rw [arccsc_neg h1, show (-√2)⁻¹ = sin (-(π / 4)) by
    rw [sin_neg, sin_pi_div_four]; field_simp; nlinarith [s2],
    arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- Stitz-Zeager Exercise 10.6.47: `arccsc(-2√3/3) = 4π/3` (range `(0, π/2] ∪ (π, 3π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.47, p. 853"]
theorem exer_10_6_47 : arccscCF (-(2 * √3 / 3)) = 4 * π / 3 := by
  have hp : 0 < √3 := by positivity
  have h1 : ¬ (1 ≤ -(2 * √3 / 3)) := by
    have : 0 < 2 * √3 / 3 := by positivity
    intro h; linarith
  rw [arccsc_neg h1, show (-(2 * √3 / 3))⁻¹ = sin (-(π / 3)) by
    rw [sin_neg, sin_pi_div_three]; field_simp; nlinarith [s3],
    arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- Stitz-Zeager Exercise 10.6.49: `arcsec(-2) = 2π/3` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.49, p. 854"]
theorem exer_10_6_49 : arcsec (-2) = 2 * π / 3 := by
  unfold arcsec
  rw [show (1 : ℝ) / -2 = cos (2 * π / 3) by rw [c23.1]; norm_num]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.50: `arcsec(-√2) = 3π/4` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.50, p. 854"]
theorem exer_10_6_50 : arcsec (-√2) = 3 * π / 4 := by
  have hp : 0 < √2 := by positivity
  unfold arcsec
  rw [show (1 : ℝ) / -√2 = cos (3 * π / 4) by
    rw [c34.1]; field_simp; nlinarith [s2]]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.51: `arcsec(-2√3/3) = 5π/6` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.51, p. 854"]
theorem exer_10_6_51 : arcsec (-(2 * √3 / 3)) = 5 * π / 6 := by
  have hp : 0 < √3 := by positivity
  unfold arcsec
  rw [show (1 : ℝ) / -(2 * √3 / 3) = cos (5 * π / 6) by
    rw [c56.1]; field_simp; nlinarith [s3]]
  exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.52: `arcsec(-1) = π` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.52, p. 854"]
theorem exer_10_6_52 : arcsec (-1) = π := by
  unfold arcsec; norm_num

/-- Stitz-Zeager Exercise 10.6.53: `arccsc(-2) = -π/6` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.53, p. 854"]
theorem exer_10_6_53 : arccsc (-2) = -(π / 6) := by
  unfold arccsc
  rw [show (1 : ℝ) / -2 = sin (-(π / 6)) by rw [sin_neg, sin_pi_div_six]; norm_num]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.54: `arccsc(-√2) = -π/4` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.54, p. 854"]
theorem exer_10_6_54 : arccsc (-√2) = -(π / 4) := by
  have hp : 0 < √2 := by positivity
  unfold arccsc
  rw [show (1 : ℝ) / -√2 = sin (-(π / 4)) by
    rw [sin_neg, sin_pi_div_four]; field_simp; nlinarith [s2]]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.55: `arccsc(-2√3/3) = -π/3` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.55, p. 854"]
theorem exer_10_6_55 : arccsc (-(2 * √3 / 3)) = -(π / 3) := by
  have hp : 0 < √3 := by positivity
  unfold arccsc
  rw [show (1 : ℝ) / -(2 * √3 / 3) = sin (-(π / 3)) by
    rw [sin_neg, sin_pi_div_three]; field_simp; nlinarith [s3]]
  exact arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.56: `arccsc(-1) = -π/2` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.56, p. 854"]
theorem exer_10_6_56 : arccsc (-1) = -(π / 2) := by
  unfold arccsc; norm_num

private lemma r2le : √2 / 2 ≤ 1 := by nlinarith [s2, Real.sqrt_nonneg 2]
private lemma r3le : √3 / 2 ≤ 1 := by nlinarith [s3, Real.sqrt_nonneg 3]

private lemma cot_arccot (x : ℝ) : cos (arccotR x) / sin (arccotR x) = x := by
  unfold arccotR
  rw [cos_pi_div_two_sub, sin_pi_div_two_sub, ← tan_eq_sin_div_cos, tan_arctan]

private lemma sec_arcsec_pos {x : ℝ} (hx : 1 ≤ x) : (cos (arcsecCF x))⁻¹ = x := by
  have h0 : 0 < x := by linarith
  rw [arcsec_pos hx, cos_arccos (by have := inv_pos.2 h0; linarith) (inv_le_one_of_one_le₀ hx),
    inv_inv]

private lemma sec_arcsec_neg {x : ℝ} (hx : x ≤ -1) : (cos (arcsecCF x))⁻¹ = x := by
  have h0 : x < 0 := by linarith
  have h1 : ¬ 1 ≤ x := by intro h; linarith
  have h2 : -1 ≤ x⁻¹ := by
    rw [inv_eq_one_div, le_div_iff_of_neg h0]; linarith
  rw [arcsec_neg h1, cos_two_pi_sub, cos_arccos h2 (by have := inv_lt_zero.2 h0; linarith), inv_inv]

private lemma sec_arcsec_lt {x : ℝ} (h0 : 0 < x) (hx : x < 1) : (cos (arcsecCF x))⁻¹ ≠ x := by
  have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ h0).2 hx.le
  rw [arcsec_neg (not_le.2 hx), arccos_eq_zero.2 h1, sub_zero, cos_two_pi, inv_one]
  exact ne_of_gt hx

private lemma csc_arccsc_pos {x : ℝ} (hx : 1 ≤ x) : (sin (arccscCF x))⁻¹ = x := by
  have h0 : 0 < x := by linarith
  rw [arccsc_pos hx, sin_arcsin (by have := inv_pos.2 h0; linarith) (inv_le_one_of_one_le₀ hx),
    inv_inv]

private lemma csc_arccsc_neg {x : ℝ} (hx : x ≤ -1) : (sin (arccscCF x))⁻¹ = x := by
  have h0 : x < 0 := by linarith
  have h1 : ¬ 1 ≤ x := by intro h; linarith
  have h2 : -1 ≤ x⁻¹ := by
    rw [inv_eq_one_div, le_div_iff_of_neg h0]; linarith
  rw [arccsc_neg h1, sin_pi_sub, sin_arcsin h2 (by have := inv_lt_zero.2 h0; linarith), inv_inv]

private lemma csc_arccsc_lt {x : ℝ} (h0 : 0 < x) (hx : x < 1) : (sin (arccscCF x))⁻¹ ≠ x := by
  have h1 : 1 ≤ x⁻¹ := (one_le_inv₀ h0).2 hx.le
  rw [arccsc_neg (not_le.2 hx), arcsin_eq_pi_div_two.2 h1, sin_pi_sub, sin_pi_div_two, inv_one]
  exact ne_of_gt hx

/-- Stitz-Zeager Exercise 10.6.58: `sin(arcsin(-√2/2)) = -√2/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.58, p. 854"]
theorem exer_10_6_58 : sin (arcsin (-(√2 / 2))) = -(√2 / 2) :=
  sin_arcsin (by have := r2le; have : 0 ≤ √2 / 2 := by positivity
                 linarith) (by have : 0 ≤ √2 / 2 := by positivity
                               linarith)

/-- Stitz-Zeager Exercise 10.6.59: `sin(arcsin(3/5)) = 3/5`. -/
@[kb "stitzzeager2013" "Exercise 10.6.59, p. 854"]
theorem exer_10_6_59 : sin (arcsin (3 / 5)) = 3 / 5 := sin_arcsin (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.62: `cos(arccos(√2/2)) = √2/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.62, p. 854"]
theorem exer_10_6_62 : cos (arccos (√2 / 2)) = √2 / 2 :=
  cos_arccos (by have : 0 ≤ √2 / 2 := by positivity
                 linarith) r2le

/-- Stitz-Zeager Exercise 10.6.63: `cos(arccos(-1/2)) = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.63, p. 854"]
theorem exer_10_6_63 : cos (arccos (-(1 / 2))) = -(1 / 2) := cos_arccos (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.64: `cos(arccos(5/13)) = 5/13`. -/
@[kb "stitzzeager2013" "Exercise 10.6.64, p. 854"]
theorem exer_10_6_64 : cos (arccos (5 / 13)) = 5 / 13 := cos_arccos (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.65: `cos(arccos(-0.998)) = -0.998`. -/
@[kb "stitzzeager2013" "Exercise 10.6.65, p. 854"]
theorem exer_10_6_65 : cos (arccos (-0.998)) = -0.998 := cos_arccos (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.68: `tan(arctan √3) = √3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.68, p. 854"]
theorem exer_10_6_68 : tan (arctan √3) = √3 := tan_arctan _

/-- Stitz-Zeager Exercise 10.6.69: `tan(arctan(5/12)) = 5/12`. -/
@[kb "stitzzeager2013" "Exercise 10.6.69, p. 854"]
theorem exer_10_6_69 : tan (arctan (5 / 12)) = 5 / 12 := tan_arctan _

/-- Stitz-Zeager Exercise 10.6.70: `tan(arctan(0.965)) = 0.965`. -/
@[kb "stitzzeager2013" "Exercise 10.6.70, p. 854"]
theorem exer_10_6_70 : tan (arctan 0.965) = 0.965 := tan_arctan _

/-- Stitz-Zeager Exercise 10.6.72: `cot(arccot 1) = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.72, p. 854"]
theorem exer_10_6_72 : cos (arccotR 1) / sin (arccotR 1) = 1 := cot_arccot 1

/-- Stitz-Zeager Exercise 10.6.73: `cot(arccot(-√3)) = -√3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.73, p. 854"]
theorem exer_10_6_73 : cos (arccotR (-√3)) / sin (arccotR (-√3)) = -√3 := cot_arccot _

/-- Stitz-Zeager Exercise 10.6.75: `cot(arccot(-0.001)) = -0.001`. -/
@[kb "stitzzeager2013" "Exercise 10.6.75, p. 854"]
theorem exer_10_6_75 : cos (arccotR (-0.001)) / sin (arccotR (-0.001)) = -0.001 := cot_arccot _

/-- Stitz-Zeager Exercise 10.6.76: `cot(arccot(17π/4)) = 17π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.76, p. 854"]
theorem exer_10_6_76 :
    cos (arccotR (17 * π / 4)) / sin (arccotR (17 * π / 4)) = 17 * π / 4 := cot_arccot _

/-- Stitz-Zeager Exercise 10.6.78: `sec(arcsec(-1)) = -1`. -/
@[kb "stitzzeager2013" "Exercise 10.6.78, p. 854"]
theorem exer_10_6_78 : (cos (arcsecCF (-1)))⁻¹ = -1 := sec_arcsec_neg le_rfl

/-- Stitz-Zeager Exercise 10.6.79: `sec(arcsec(1/2))` is undefined, since `1/2` is not in the domain
of arcsecant: the composite does not return `1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.79, p. 854"]
theorem exer_10_6_79 : (cos (arcsecCF (1 / 2)))⁻¹ ≠ 1 / 2 :=
  sec_arcsec_lt (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.80: `sec(arcsec(0.75))` is undefined (`0.75` is not in the domain). -/
@[kb "stitzzeager2013" "Exercise 10.6.80, p. 854"]
theorem exer_10_6_80 : (cos (arcsecCF 0.75))⁻¹ ≠ 0.75 :=
  sec_arcsec_lt (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 10.6.81: `sec(arcsec(117π)) = 117π`. -/
@[kb "stitzzeager2013" "Exercise 10.6.81, p. 854"]
theorem exer_10_6_81 : (cos (arcsecCF (117 * π)))⁻¹ = 117 * π :=
  sec_arcsec_pos (by nlinarith [Real.pi_gt_three])

/-- Stitz-Zeager Exercise 10.6.82: `csc(arccsc √2) = √2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.82, p. 854"]
theorem exer_10_6_82 : (sin (arccscCF √2))⁻¹ = √2 :=
  csc_arccsc_pos (by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num))

/-- Stitz-Zeager Exercise 10.6.83: `csc(arccsc(-2√3/3)) = -2√3/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.83, p. 854"]
theorem exer_10_6_83 : (sin (arccscCF (-(2 * √3 / 3))))⁻¹ = -(2 * √3 / 3) :=
  csc_arccsc_neg (by have := three_half_le; linarith)

/-- Stitz-Zeager Exercise 10.6.84: `csc(arccsc(√2/2))` is undefined (`√2/2` is not in the domain). -/
@[kb "stitzzeager2013" "Exercise 10.6.84, p. 854"]
theorem exer_10_6_84 : (sin (arccscCF (√2 / 2)))⁻¹ ≠ √2 / 2 :=
  csc_arccsc_lt (by positivity) (by nlinarith [s2, Real.sqrt_nonneg 2])

/-- Stitz-Zeager Exercise 10.6.85: `csc(arccsc 1.0001) = 1.0001`. -/
@[kb "stitzzeager2013" "Exercise 10.6.85, p. 854"]
theorem exer_10_6_85 : (sin (arccscCF 1.0001))⁻¹ = 1.0001 := csc_arccsc_pos (by norm_num)

/-- Stitz-Zeager Exercise 10.6.86: `csc(arccsc(π/4))` is undefined (`π/4` is not in the domain). -/
@[kb "stitzzeager2013" "Exercise 10.6.86, p. 854"]
theorem exer_10_6_86 : (sin (arccscCF (π / 4)))⁻¹ ≠ π / 4 :=
  csc_arccsc_lt (by positivity) (by linarith [Real.pi_lt_four])

private lemma sin_neg_Q3' {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) : sin θ < 0 := by
  have h : sin θ = -sin (θ - π) := by rw [sin_sub_pi]; ring
  have := sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
  linarith

private lemma sinsec_a {x : ℝ} (h1 : 0 ≤ x) (h2 : x < π / 2) : arcsecCF (cos x)⁻¹ = x := by
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  rw [arcsec_pos ((one_le_inv₀ hc).2 (cos_le_one x)), inv_inv, arccos_cos h1 (by linarith [Real.pi_pos])]

private lemma sinsec_c {x : ℝ} (h1 : π / 2 < x) (h2 : x ≤ π) : arcsecCF (cos x)⁻¹ = 2 * π - x := by
  have hc : cos x < 0 := cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [Real.pi_pos])
  have h3 : ¬ 1 ≤ (cos x)⁻¹ := by
    have := inv_lt_zero.2 hc; intro h; linarith
  rw [arcsec_neg h3, inv_inv, arccos_cos (by linarith) h2]

private lemma sinsec_b {x : ℝ} (h1 : π ≤ x) (h2 : x < 3 * π / 2) : arcsecCF (cos x)⁻¹ = x := by
  have hc : cos x < 0 := by
    have := cos_pos_of_mem_Ioo (x := x - π) ⟨by linarith [Real.pi_pos], by linarith⟩
    rw [cos_sub_pi] at this; linarith
  have h3 : ¬ 1 ≤ (cos x)⁻¹ := by
    have := inv_lt_zero.2 hc; intro h; linarith
  rw [arcsec_neg h3, inv_inv, ← cos_two_pi_sub, arccos_cos (by linarith) (by linarith)]
  ring

private lemma sinsec_d {x : ℝ} (h1 : 3 * π / 2 < x) (h2 : x ≤ 2 * π) :
    arcsecCF (cos x)⁻¹ = 2 * π - x := by
  have hc : 0 < cos x := by
    rw [← cos_two_pi_sub]
    exact cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [arcsec_pos ((one_le_inv₀ hc).2 (cos_le_one x)), inv_inv, ← cos_two_pi_sub,
    arccos_cos (by linarith) (by linarith [Real.pi_pos])]

private lemma sincsc_e {x : ℝ} (h1 : 0 < x) (h2 : x ≤ π / 2) : arccscCF (sin x)⁻¹ = x := by
  have hc : 0 < sin x := sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
  rw [arccsc_pos ((one_le_inv₀ hc).2 (sin_le_one x)), inv_inv, arcsin_sin (by linarith [Real.pi_pos]) h2]

private lemma sincsc_f {x : ℝ} (h1 : π / 2 < x) (h2 : x < π) : arccscCF (sin x)⁻¹ = π - x := by
  have hc : 0 < sin x := sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) h2
  rw [arccsc_pos ((one_le_inv₀ hc).2 (sin_le_one x)), inv_inv, ← sin_pi_sub,
    arcsin_sin (by linarith) (by linarith [Real.pi_pos])]

private lemma sincsc_g {x : ℝ} (h1 : π < x) (h2 : x ≤ 3 * π / 2) : arccscCF (sin x)⁻¹ = x := by
  have hc : sin x < 0 := sin_neg_Q3' h1 (by linarith [Real.pi_pos])
  have h3 : ¬ 1 ≤ (sin x)⁻¹ := by
    have := inv_lt_zero.2 hc; intro h; linarith
  rw [arccsc_neg h3, inv_inv, ← sin_pi_sub x, arcsin_sin (by linarith) (by linarith [Real.pi_pos])]
  ring

private lemma sincsc_h {x : ℝ} (h1 : 3 * π / 2 < x) (h2 : x < 2 * π) :
    arccscCF (sin x)⁻¹ = 3 * π - x := by
  have hc : sin x < 0 := sin_neg_Q3' (by linarith [Real.pi_pos]) h2
  have h3 : ¬ 1 ≤ (sin x)⁻¹ := by
    have := inv_lt_zero.2 hc; intro h; linarith
  rw [arccsc_neg h3, inv_inv, ← sin_sub_two_pi, arcsin_sin (by linarith) (by linarith [Real.pi_pos])]
  ring

private lemma asec_cos {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ π) : arcsec (cos x)⁻¹ = x := by
  unfold arcsec; rw [one_div, inv_inv, arccos_cos h1 h2]

private lemma asec_cos_hi {x : ℝ} (h1 : π ≤ x) (h2 : x ≤ 2 * π) :
    arcsec (cos x)⁻¹ = 2 * π - x := by
  unfold arcsec
  rw [one_div, inv_inv, ← cos_two_pi_sub, arccos_cos (by linarith) (by linarith [Real.pi_pos])]

private lemma acsc_sin {x : ℝ} (h1 : -(π / 2) ≤ x) (h2 : x ≤ π / 2) : arccsc (sin x)⁻¹ = x := by
  unfold arccsc; rw [one_div, inv_inv, arcsin_sin h1 h2]

private lemma acsc_sin_mid {x : ℝ} (h1 : π / 2 ≤ x) (h2 : x ≤ 3 * π / 2) :
    arccsc (sin x)⁻¹ = π - x := by
  unfold arccsc
  rw [one_div, inv_inv, ← sin_pi_sub, arcsin_sin (by linarith) (by linarith [Real.pi_pos])]

private lemma acsc_sin_hi {x : ℝ} (h1 : 3 * π / 2 ≤ x) (h2 : x ≤ 5 * π / 2) :
    arccsc (sin x)⁻¹ = x - 2 * π := by
  unfold arccsc
  rw [one_div, inv_inv, ← sin_sub_two_pi, arcsin_sin (by linarith) (by linarith [Real.pi_pos])]

/-- Stitz-Zeager Exercise 10.6.87: `arcsin(sin(π/6)) = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.87, p. 854"]
theorem exer_10_6_87 : arcsin (sin (π / 6)) = π / 6 :=
  arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.88: `arcsin(sin(-π/3)) = -π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.88, p. 854"]
theorem exer_10_6_88 : arcsin (sin (-(π / 3))) = -(π / 3) :=
  arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.92: `arccos(cos(π/4)) = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.92, p. 854"]
theorem exer_10_6_92 : arccos (cos (π / 4)) = π / 4 :=
  arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.95: `arccos(cos(-π/6)) = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.95, p. 854"]
theorem exer_10_6_95 : arccos (cos (-(π / 6))) = π / 6 := by
  rw [cos_neg]; exact arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.97: `arctan(tan(π/3)) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.97, p. 854"]
theorem exer_10_6_97 : arctan (tan (π / 3)) = π / 3 :=
  arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.98: `arctan(tan(-π/4)) = -π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.98, p. 854"]
theorem exer_10_6_98 : arctan (tan (-(π / 4))) = -(π / 4) :=
  arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.99: `arctan(tan π) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.99, p. 854"]
theorem exer_10_6_99 : arctan (tan π) = 0 := by rw [tan_pi, arctan_zero]

/-- Stitz-Zeager Exercise 10.6.100: `arctan(tan(π/2))` is undefined, because `cos(π/2) = 0`
(the composite is not `π/2`). -/
@[kb "stitzzeager2013" "Exercise 10.6.100, p. 854"]
theorem exer_10_6_100 : cos (π / 2) = 0 ∧ arctan (tan (π / 2)) ≠ π / 2 := by
  refine ⟨cos_pi_div_two, ?_⟩
  rw [tan_pi_div_two, arctan_zero]
  linarith [Real.pi_pos]

/-- Stitz-Zeager Exercise 10.6.102: `arccot(cot(π/3)) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.102, p. 854"]
theorem exer_10_6_102 : arccotR (cos (π / 3) / sin (π / 3)) = π / 3 :=
  arccot_of rfl (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.103: `arccot(cot(-π/4)) = 3π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.103, p. 854"]
theorem exer_10_6_103 : arccotR (cos (-(π / 4)) / sin (-(π / 4))) = 3 * π / 4 := by
  refine arccot_of ?_ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [c34.1, c34.2, cos_neg, sin_neg, cos_pi_div_four, sin_pi_div_four, neg_div, div_neg]

/-- Stitz-Zeager Exercise 10.6.104: `arccot(cot π)` is undefined, because `sin π = 0`
(the composite is not `π`). -/
@[kb "stitzzeager2013" "Exercise 10.6.104, p. 854"]
theorem exer_10_6_104 : sin π = 0 ∧ arccotR (cos π / sin π) ≠ π := by
  refine ⟨sin_pi, ?_⟩
  rw [sin_pi, div_zero]
  unfold arccotR
  rw [arctan_zero]
  linarith [Real.pi_pos]

/-- Stitz-Zeager Exercise 10.6.105: `arccot(cot(3π/2)) = π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.105, p. 854"]
theorem exer_10_6_105 : arccotR (cos (3 * π / 2) / sin (3 * π / 2)) = π / 2 := by
  rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]
  unfold arccotR
  simp

/-- Stitz-Zeager Exercise 10.6.107: `arcsec(sec(π/4)) = π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.107, p. 854"]
theorem exer_10_6_107 : arcsecCF (cos (π / 4))⁻¹ = π / 4 :=
  sinsec_a (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])



/-- Stitz-Zeager Exercise 10.6.110: `arcsec(sec(-π/2))` is undefined, because `cos(-π/2) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.110, p. 854"]
theorem exer_10_6_110 : cos (-(π / 2)) = 0 := by rw [cos_neg, cos_pi_div_two]

/-- Stitz-Zeager Exercise 10.6.111: `arcsec(sec(5π/3)) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.111, p. 854"]
theorem exer_10_6_111 : arcsecCF (cos (5 * π / 3))⁻¹ = π / 3 := by
  rw [sinsec_d (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.112: `arccsc(csc(π/6)) = π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.112, p. 854"]
theorem exer_10_6_112 : arccscCF (sin (π / 6))⁻¹ = π / 6 :=
  sincsc_e (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.113: `arccsc(csc(5π/4)) = 5π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.6.113, p. 854"]
theorem exer_10_6_113 : arccscCF (sin (5 * π / 4))⁻¹ = 5 * π / 4 :=
  sincsc_g (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.114: `arccsc(csc(2π/3)) = π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.6.114, p. 854"]
theorem exer_10_6_114 : arccscCF (sin (2 * π / 3))⁻¹ = π / 3 := by
  rw [sincsc_f (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.115: `arccsc(csc(-π/2)) = 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.6.115, p. 854"]
theorem exer_10_6_115 : arccscCF (sin (-(π / 2)))⁻¹ = 3 * π / 2 := by
  rw [sin_neg, sin_pi_div_two, arccsc_neg (by norm_num)]
  norm_num
  ring

/-- Stitz-Zeager Exercise 10.6.116: `arccsc(csc(11π/6)) = 7π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.6.116, p. 854"]
theorem exer_10_6_116 : arccscCF (sin (11 * π / 6))⁻¹ = 7 * π / 6 := by
  rw [sincsc_h (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.117: `arcsec(sec(11π/12)) = 13π/12`. -/
@[kb "stitzzeager2013" "Exercise 10.6.117, p. 854"]
theorem exer_10_6_117 : arcsecCF (cos (11 * π / 12))⁻¹ = 13 * π / 12 := by
  rw [sinsec_c (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.118: `arccsc(csc(9π/8)) = 9π/8`. -/
@[kb "stitzzeager2013" "Exercise 10.6.118, p. 854"]
theorem exer_10_6_118 : arccscCF (sin (9 * π / 8))⁻¹ = 9 * π / 8 :=
  sincsc_g (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.119: `arcsec(sec(π/4)) = π/4` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.119, p. 855"]
theorem exer_10_6_119 : arcsec (cos (π / 4))⁻¹ = π / 4 :=
  asec_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.120: `arcsec(sec(4π/3)) = 2π/3` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.120, p. 855"]
theorem exer_10_6_120 : arcsec (cos (4 * π / 3))⁻¹ = 2 * π / 3 := by
  rw [asec_cos_hi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.121: `arcsec(sec(5π/6)) = 5π/6` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.121, p. 855"]
theorem exer_10_6_121 : arcsec (cos (5 * π / 6))⁻¹ = 5 * π / 6 :=
  asec_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.122: `arcsec(sec(-π/2))` is undefined, because `cos(-π/2) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.6.122, p. 855"]
theorem exer_10_6_122 : cos (-(π / 2)) = 0 := by rw [cos_neg, cos_pi_div_two]

/-- Stitz-Zeager Exercise 10.6.123: `arcsec(sec(5π/3)) = π/3` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.123, p. 855"]
theorem exer_10_6_123 : arcsec (cos (5 * π / 3))⁻¹ = π / 3 := by
  rw [asec_cos_hi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.124: `arccsc(csc(π/6)) = π/6` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.124, p. 855"]
theorem exer_10_6_124 : arccsc (sin (π / 6))⁻¹ = π / 6 :=
  acsc_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.125: `arccsc(csc(5π/4)) = -π/4` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.125, p. 855"]
theorem exer_10_6_125 : arccsc (sin (5 * π / 4))⁻¹ = -(π / 4) := by
  rw [acsc_sin_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.126: `arccsc(csc(2π/3)) = π/3` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.126, p. 855"]
theorem exer_10_6_126 : arccsc (sin (2 * π / 3))⁻¹ = π / 3 := by
  rw [acsc_sin_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.127: `arccsc(csc(-π/2)) = -π/2` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.127, p. 855"]
theorem exer_10_6_127 : arccsc (sin (-(π / 2)))⁻¹ = -(π / 2) :=
  acsc_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.128: `arccsc(csc(11π/6)) = -π/6` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.128, p. 855"]
theorem exer_10_6_128 : arccsc (sin (11 * π / 6))⁻¹ = -(π / 6) := by
  rw [acsc_sin_hi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

/-- Stitz-Zeager Exercise 10.6.129: `arcsec(sec(11π/12)) = 11π/12` (range `[0, π/2) ∪ (π/2, π]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.129, p. 855"]
theorem exer_10_6_129 : arcsec (cos (11 * π / 12))⁻¹ = 11 * π / 12 :=
  asec_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Stitz-Zeager Exercise 10.6.130: `arccsc(csc(9π/8)) = -π/8` (range `[-π/2, 0) ∪ (0, π/2]`). -/
@[kb "stitzzeager2013" "Exercise 10.6.130, p. 855"]
theorem exer_10_6_130 : arccsc (sin (9 * π / 8))⁻¹ = -(π / 8) := by
  rw [acsc_sin_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]; ring

end UndergradKB.Precalculus.Course
