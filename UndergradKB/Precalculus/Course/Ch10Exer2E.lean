import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 10.3
(more identities)

Reciprocal functions are written `(cos θ)⁻¹`, `(sin θ)⁻¹`, `cos θ / sin θ`; identities are stated under
the hypotheses that all quantities are defined. -/

namespace UndergradKB.Precalculus.Course

open Real

/-- If `sin θ ≠ 0` then `1 - cos θ` and `1 + cos θ` do not vanish. -/
private lemma one_pm_cos {θ : ℝ} (hs : sin θ ≠ 0) : 1 - cos θ ≠ 0 ∧ 1 + cos θ ≠ 0 := by
  have h : (1 - cos θ) * (1 + cos θ) = sin θ ^ 2 := by linarith [sin_sq_add_cos_sq θ, show (1 - cos θ) * (1 + cos θ) = 1 - cos θ ^ 2 by ring]
  have hne : (1 - cos θ) * (1 + cos θ) ≠ 0 := by rw [h]; exact pow_ne_zero 2 hs
  exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/-- If `cos θ ≠ 0` then `1 - sin θ` and `1 + sin θ` do not vanish. -/
private lemma one_pm_sin {θ : ℝ} (hc : cos θ ≠ 0) : 1 - sin θ ≠ 0 ∧ 1 + sin θ ≠ 0 := by
  have h : (1 - sin θ) * (1 + sin θ) = cos θ ^ 2 := by linarith [sin_sq_add_cos_sq θ, show (1 - sin θ) * (1 + sin θ) = 1 - sin θ ^ 2 by ring]
  have hne : (1 - sin θ) * (1 + sin θ) ≠ 0 := by rw [h]; exact pow_ne_zero 2 hc
  exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/-- Stitz-Zeager Exercise 10.3.104: `(cos θ + 1)/(cos θ - 1) = (1 + sec θ)/(1 - sec θ)`. -/
@[kb "stitzzeager2013" "Exercise 10.3.104, p. 775"]
theorem exer_10_3_104 (θ : ℝ) (hc : cos θ ≠ 0) (h1 : cos θ ≠ 1) :
    (cos θ + 1) / (cos θ - 1) = (1 + (cos θ)⁻¹) / (1 - (cos θ)⁻¹) := by
  have h2 : cos θ - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp

/-- Stitz-Zeager Exercise 10.3.105: `(sin θ + 1)/(sin θ - 1) = (1 + csc θ)/(1 - csc θ)`. -/
@[kb "stitzzeager2013" "Exercise 10.3.105, p. 775"]
theorem exer_10_3_105 (θ : ℝ) (hs : sin θ ≠ 0) (h1 : sin θ ≠ 1) :
    (sin θ + 1) / (sin θ - 1) = (1 + (sin θ)⁻¹) / (1 - (sin θ)⁻¹) := by
  have h2 : sin θ - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp

/-- Stitz-Zeager Exercise 10.3.106: `(1 - cot θ)/(1 + cot θ) = (tan θ - 1)/(tan θ + 1)`. -/
@[kb "stitzzeager2013" "Exercise 10.3.106, p. 775"]
theorem exer_10_3_106 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) (h : sin θ + cos θ ≠ 0) :
    (1 - cos θ / sin θ) / (1 + cos θ / sin θ) = (tan θ - 1) / (tan θ + 1) := by
  rw [tan_eq_sin_div_cos]
  have h' : cos θ + sin θ ≠ 0 := by rwa [add_comm]
  field_simp

/-- Stitz-Zeager Exercise 10.3.107: `(1 - tan θ)/(1 + tan θ) = (cos θ - sin θ)/(cos θ + sin θ)`. -/
@[kb "stitzzeager2013" "Exercise 10.3.107, p. 775"]
theorem exer_10_3_107 (θ : ℝ) (hc : cos θ ≠ 0) (h : cos θ + sin θ ≠ 0) :
    (1 - tan θ) / (1 + tan θ) = (cos θ - sin θ) / (cos θ + sin θ) := by
  rw [tan_eq_sin_div_cos]
  field_simp

/-- Stitz-Zeager Exercise 10.3.113: `1/(1 - cos θ) + 1/(1 + cos θ) = 2 csc² θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.113, p. 775"]
theorem exer_10_3_113 (θ : ℝ) (hs : sin θ ≠ 0) :
    1 / (1 - cos θ) + 1 / (1 + cos θ) = 2 * ((sin θ)⁻¹) ^ 2 := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  field_simp
  linarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.114: `1/(sec θ + 1) + 1/(sec θ - 1) = 2 csc θ cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.114, p. 775"]
theorem exer_10_3_114 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) :
    1 / ((cos θ)⁻¹ + 1) + 1 / ((cos θ)⁻¹ - 1) = 2 * (sin θ)⁻¹ * (cos θ / sin θ) := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  have h3 : cos θ - 1 ≠ 0 := by intro h; apply h1; linarith
  have h4 : 1 + cos θ ≠ 0 := h2
  have h5 : (cos θ)⁻¹ + 1 ≠ 0 := by
    have : (cos θ)⁻¹ + 1 = (1 + cos θ) / cos θ := by field_simp
    rw [this]; exact div_ne_zero h4 hc
  have h6 : (cos θ)⁻¹ - 1 ≠ 0 := by
    have : (cos θ)⁻¹ - 1 = (1 - cos θ) / cos θ := by field_simp
    rw [this]; exact div_ne_zero h1 hc
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.115: `1/(csc θ + 1) + 1/(csc θ - 1) = 2 sec θ tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.115, p. 775"]
theorem exer_10_3_115 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) :
    1 / ((sin θ)⁻¹ + 1) + 1 / ((sin θ)⁻¹ - 1) = 2 * (cos θ)⁻¹ * tan θ := by
  obtain ⟨h1, h2⟩ := one_pm_sin hc
  have h5 : (sin θ)⁻¹ + 1 ≠ 0 := by
    have : (sin θ)⁻¹ + 1 = (1 + sin θ) / sin θ := by field_simp
    rw [this]; exact div_ne_zero h2 hs
  have h6 : (sin θ)⁻¹ - 1 ≠ 0 := by
    have : (sin θ)⁻¹ - 1 = (1 - sin θ) / sin θ := by field_simp
    rw [this]; exact div_ne_zero h1 hs
  rw [tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.116: `1/(csc θ - cot θ) - 1/(csc θ + cot θ) = 2 cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.116, p. 775"]
theorem exer_10_3_116 (θ : ℝ) (hs : sin θ ≠ 0) :
    1 / ((sin θ)⁻¹ - cos θ / sin θ) - 1 / ((sin θ)⁻¹ + cos θ / sin θ) = 2 * (cos θ / sin θ) := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  have h5 : (sin θ)⁻¹ - cos θ / sin θ ≠ 0 := by
    have : (sin θ)⁻¹ - cos θ / sin θ = (1 - cos θ) / sin θ := by field_simp
    rw [this]; exact div_ne_zero h1 hs
  have h6 : (sin θ)⁻¹ + cos θ / sin θ ≠ 0 := by
    have : (sin θ)⁻¹ + cos θ / sin θ = (1 + cos θ) / sin θ := by field_simp
    rw [this]; exact div_ne_zero h2 hs
  field_simp
  have hh : sin θ ^ 2 = 1 - cos θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
  rw [hh]; ring

/-- Stitz-Zeager Exercise 10.3.118: `1/(sec θ + tan θ) = sec θ - tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.118, p. 775"]
theorem exer_10_3_118 (θ : ℝ) (hc : cos θ ≠ 0) :
    1 / ((cos θ)⁻¹ + tan θ) = (cos θ)⁻¹ - tan θ := by
  obtain ⟨h1, h2⟩ := one_pm_sin hc
  have h5 : (cos θ)⁻¹ + tan θ ≠ 0 := by
    have : (cos θ)⁻¹ + tan θ = (1 + sin θ) / cos θ := by rw [tan_eq_sin_div_cos]; field_simp
    rw [this]; exact div_ne_zero h2 hc
  rw [tan_eq_sin_div_cos] at h5 ⊢
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.119: `1/(sec θ - tan θ) = sec θ + tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.119, p. 775"]
theorem exer_10_3_119 (θ : ℝ) (hc : cos θ ≠ 0) :
    1 / ((cos θ)⁻¹ - tan θ) = (cos θ)⁻¹ + tan θ := by
  obtain ⟨h1, h2⟩ := one_pm_sin hc
  have h5 : (cos θ)⁻¹ - tan θ ≠ 0 := by
    have : (cos θ)⁻¹ - tan θ = (1 - sin θ) / cos θ := by rw [tan_eq_sin_div_cos]; field_simp
    rw [this]; exact div_ne_zero h1 hc
  rw [tan_eq_sin_div_cos] at h5 ⊢
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.120: `1/(csc θ - cot θ) = csc θ + cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.120, p. 775"]
theorem exer_10_3_120 (θ : ℝ) (hs : sin θ ≠ 0) :
    1 / ((sin θ)⁻¹ - cos θ / sin θ) = (sin θ)⁻¹ + cos θ / sin θ := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  have h5 : (sin θ)⁻¹ - cos θ / sin θ ≠ 0 := by
    have : (sin θ)⁻¹ - cos θ / sin θ = (1 - cos θ) / sin θ := by field_simp
    rw [this]; exact div_ne_zero h1 hs
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.121: `1/(csc θ + cot θ) = csc θ - cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.121, p. 775"]
theorem exer_10_3_121 (θ : ℝ) (hs : sin θ ≠ 0) :
    1 / ((sin θ)⁻¹ + cos θ / sin θ) = (sin θ)⁻¹ - cos θ / sin θ := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  have h5 : (sin θ)⁻¹ + cos θ / sin θ ≠ 0 := by
    have : (sin θ)⁻¹ + cos θ / sin θ = (1 + cos θ) / sin θ := by field_simp
    rw [this]; exact div_ne_zero h2 hs
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.122: `1/(1 - sin θ) = sec² θ + sec θ tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.122, p. 775"]
theorem exer_10_3_122 (θ : ℝ) (hc : cos θ ≠ 0) :
    1 / (1 - sin θ) = ((cos θ)⁻¹) ^ 2 + (cos θ)⁻¹ * tan θ := by
  obtain ⟨h1, h2⟩ := one_pm_sin hc
  rw [tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.123: `1/(1 + sin θ) = sec² θ - sec θ tan θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.123, p. 775"]
theorem exer_10_3_123 (θ : ℝ) (hc : cos θ ≠ 0) :
    1 / (1 + sin θ) = ((cos θ)⁻¹) ^ 2 - (cos θ)⁻¹ * tan θ := by
  obtain ⟨h1, h2⟩ := one_pm_sin hc
  rw [tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.124: `1/(1 - cos θ) = csc² θ + csc θ cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.124, p. 775"]
theorem exer_10_3_124 (θ : ℝ) (hs : sin θ ≠ 0) :
    1 / (1 - cos θ) = ((sin θ)⁻¹) ^ 2 + (sin θ)⁻¹ * (cos θ / sin θ) := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.125: `1/(1 + cos θ) = csc² θ - csc θ cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.125, p. 775"]
theorem exer_10_3_125 (θ : ℝ) (hs : sin θ ≠ 0) :
    1 / (1 + cos θ) = ((sin θ)⁻¹) ^ 2 - (sin θ)⁻¹ * (cos θ / sin θ) := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.126: `cos θ/(1 + sin θ) = (1 - sin θ)/cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.126, p. 775"]
theorem exer_10_3_126 (θ : ℝ) (hc : cos θ ≠ 0) :
    cos θ / (1 + sin θ) = (1 - sin θ) / cos θ := by
  obtain ⟨h1, h2⟩ := one_pm_sin hc
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.127: `csc θ - cot θ = sin θ/(1 + cos θ)`. -/
@[kb "stitzzeager2013" "Exercise 10.3.127, p. 775"]
theorem exer_10_3_127 (θ : ℝ) (hs : sin θ ≠ 0) :
    (sin θ)⁻¹ - cos θ / sin θ = sin θ / (1 + cos θ) := by
  obtain ⟨h1, h2⟩ := one_pm_cos hs
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.128: `(1 - sin θ)/(1 + sin θ) = (sec θ - tan θ)²`. -/
@[kb "stitzzeager2013" "Exercise 10.3.128, p. 775"]
theorem exer_10_3_128 (θ : ℝ) (hc : cos θ ≠ 0) :
    (1 - sin θ) / (1 + sin θ) = ((cos θ)⁻¹ - tan θ) ^ 2 := by
  obtain ⟨h1, h2⟩ := one_pm_sin hc
  rw [tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.117: `cos θ/(1 - tan θ) + sin θ/(1 - cot θ) = sin θ + cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.3.117, p. 775"]
theorem exer_10_3_117 (θ : ℝ) (hc : cos θ ≠ 0) (hs : sin θ ≠ 0) (h : cos θ - sin θ ≠ 0) :
    cos θ / (1 - tan θ) + sin θ / (1 - cos θ / sin θ) = sin θ + cos θ := by
  have h' : sin θ - cos θ ≠ 0 := by intro h0; apply h; linarith
  have h1 : 1 - sin θ / cos θ ≠ 0 := by
    have : 1 - sin θ / cos θ = (cos θ - sin θ) / cos θ := by field_simp
    rw [this]; exact div_ne_zero h hc
  have h2 : 1 - cos θ / sin θ ≠ 0 := by
    have : 1 - cos θ / sin θ = (sin θ - cos θ) / sin θ := by field_simp
    rw [this]; exact div_ne_zero h' hs
  rw [tan_eq_sin_div_cos]
  field_simp
  have hh : sin θ ^ 2 = 1 - cos θ ^ 2 := by linarith [sin_sq_add_cos_sq θ]
  nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.3.134: for complementary angles `α + β = π/2`: `sec α = csc β` and
`tan α = cot β`. -/
@[kb "stitzzeager2013" "Exercise 10.3.134, p. 776"]
theorem exer_10_3_134 (α β : ℝ) (h : α + β = π / 2) :
    (cos α)⁻¹ = (sin β)⁻¹ ∧ tan α = cos β / sin β := by
  have hb : β = π / 2 - α := by linarith
  have ha : α = π / 2 - β := by linarith
  have e1 : sin α = cos β := by rw [ha, sin_pi_div_two_sub]
  have e2 : cos α = sin β := by rw [hb, sin_pi_div_two_sub]
  refine ⟨by rw [e2], ?_⟩
  rw [tan_eq_sin_div_cos, e1, e2]

/-- Stitz-Zeager Exercise 10.3.135: for `0 < θ < π/2`: `cos θ < sin θ / θ < 1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.135, p. 776"]
theorem exer_10_3_135 : ∀ θ : ℝ, 0 < θ → θ < π / 2 → cos θ < sin θ / θ ∧ sin θ / θ < 1 := by
  intro θ h1 h2
  have hs : sin θ < θ := sin_lt h1
  have ht : θ < tan θ := lt_tan h1 h2
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  refine ⟨?_, (div_lt_one h1).mpr hs⟩
  rw [lt_div_iff₀ h1]
  rw [tan_eq_sin_div_cos, lt_div_iff₀ hc] at ht
  linarith

/-- Stitz-Zeager Exercise 10.3.136: the inequalities `cos θ < sin θ / θ < 1` also hold for `-π/2 < θ < 0`. -/
@[kb "stitzzeager2013" "Exercise 10.3.136, p. 777"]
theorem exer_10_3_136 : ∀ θ : ℝ, -(π / 2) < θ → θ < 0 → cos θ < sin θ / θ ∧ sin θ / θ < 1 := by
  intro θ h1 h2
  obtain ⟨a, b⟩ := exer_10_3_135 (-θ) (by linarith) (by linarith)
  rw [cos_neg, sin_neg, neg_div_neg_eq] at a
  rw [sin_neg, neg_div_neg_eq] at b
  exact ⟨a, b⟩

/-- Stitz-Zeager Exercise 10.3.129: `ln|sec θ| = -ln|cos θ|`. -/
@[kb "stitzzeager2013" "Exercise 10.3.129, p. 776"]
theorem exer_10_3_129 (θ : ℝ) : Real.log |(cos θ)⁻¹| = -Real.log |cos θ| := by
  rw [abs_inv, Real.log_inv]

/-- Stitz-Zeager Exercise 10.3.130: `-ln|csc θ| = ln|sin θ|`. -/
@[kb "stitzzeager2013" "Exercise 10.3.130, p. 776"]
theorem exer_10_3_130 (θ : ℝ) : -Real.log |(sin θ)⁻¹| = Real.log |sin θ| := by
  rw [abs_inv, Real.log_inv, neg_neg]

/-- Stitz-Zeager Exercise 10.3.131: `-ln|sec θ - tan θ| = ln|sec θ + tan θ|`. -/
@[kb "stitzzeager2013" "Exercise 10.3.131, p. 776"]
theorem exer_10_3_131 (θ : ℝ) (hc : cos θ ≠ 0) :
    -Real.log |(cos θ)⁻¹ - tan θ| = Real.log |(cos θ)⁻¹ + tan θ| := by
  have hprod : ((cos θ)⁻¹ - tan θ) * ((cos θ)⁻¹ + tan θ) = 1 := by
    rw [tan_eq_sin_div_cos]; field_simp; linarith [sin_sq_add_cos_sq θ]
  have h : (cos θ)⁻¹ + tan θ = ((cos θ)⁻¹ - tan θ)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  rw [h, abs_inv, Real.log_inv]

/-- Stitz-Zeager Exercise 10.3.132: `-ln|csc θ + cot θ| = ln|csc θ - cot θ|`. -/
@[kb "stitzzeager2013" "Exercise 10.3.132, p. 776"]
theorem exer_10_3_132 (θ : ℝ) (hs : sin θ ≠ 0) :
    -Real.log |(sin θ)⁻¹ + cos θ / sin θ| = Real.log |(sin θ)⁻¹ - cos θ / sin θ| := by
  have hprod : ((sin θ)⁻¹ + cos θ / sin θ) * ((sin θ)⁻¹ - cos θ / sin θ) = 1 := by
    field_simp; linarith [sin_sq_add_cos_sq θ]
  have h : (sin θ)⁻¹ - cos θ / sin θ = ((sin θ)⁻¹ + cos θ / sin θ)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  rw [h, abs_inv, Real.log_inv]

end UndergradKB.Precalculus.Course
