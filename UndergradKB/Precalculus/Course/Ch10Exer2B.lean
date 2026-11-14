import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 10.3
(values and the remaining circular functions)

Reciprocal functions are written `(cos θ)⁻¹`, `(sin θ)⁻¹`, `cos θ / sin θ`. -/

namespace UndergradKB.Precalculus.Course

open Real

private lemma eq_of_pos_sq' {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (h : c ^ 2 = a ^ 2) : c = a :=
  (pow_left_inj₀ hc.le ha two_ne_zero).mp h

private lemma eq_of_neg_sq' {c a : ℝ} (hc : c < 0) (ha : a ≤ 0) (h : c ^ 2 = a ^ 2) : c = a := by
  have := eq_of_pos_sq' (c := -c) (a := -a) (by linarith) (by linarith) (by simpa using h)
  linarith

private lemma cos_pos_Q1' {θ : ℝ} (h1 : 0 < θ) (h2 : θ < π / 2) : 0 < cos θ :=
  cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩

private lemma cos_neg_Q23' {θ : ℝ} (h1 : π / 2 < θ) (h2 : θ < 3 * π / 2) : cos θ < 0 :=
  cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)

private lemma cos_pos_Q4' {θ : ℝ} (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : 0 < cos θ := by
  rw [← cos_sub_two_pi]
  apply cos_pos_of_mem_Ioo; constructor <;> linarith

private lemma sin_neg_Q34' {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) : sin θ < 0 := by
  have h : sin θ = -sin (θ - π) := by rw [sin_sub_pi]; ring
  have := sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
  linarith

/-- Closes the final field identities between numerals and square roots. -/
local macro "fin6" : tactic =>
  `(tactic| first
    | (norm_num; done)
    | (field_simp; done)
    | (field_simp; ring_nf; done)
    | (field_simp; nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 91 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 530 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 95 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 30 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 110 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]))

/-! ## Section 10.3 -/

/-- Stitz-Zeager Exercise 10.3.15: `csc(-7π/4) = √2`. -/
@[kb "stitzzeager2013" "Exercise 10.3.15, p. 771"]
theorem exer_10_3_15 : (sin (-(7 * π / 4)))⁻¹ = √2 := by
  have h : -(7 * π / 4) = π / 4 - 2 * π := by ring
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  rw [h, sin_sub_two_pi, sin_pi_div_four]
  field_simp
  nlinarith [h2]

/-- Stitz-Zeager Exercise 10.3.16: `cot(7π/6) = √3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.16, p. 771"]
theorem exer_10_3_16 : cos (7 * π / 6) / sin (7 * π / 6) = √3 := by
  have h : 7 * π / 6 = π / 6 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_six, sin_pi_div_six]
  field_simp

/-- Stitz-Zeager Exercise 10.3.19: `csc(π/2) = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.19, p. 771"]
theorem exer_10_3_19 : (sin (π / 2))⁻¹ = 1 := by simp

/-- Stitz-Zeager Exercise 10.3.22: `tan θ = 12/5` in Quadrant III gives `sin θ = -12/13`, `cos θ = -5/13`,
`csc θ = -13/12`, `sec θ = -13/5`, `cot θ = 5/12`. -/
@[kb "stitzzeager2013" "Exercise 10.3.22, p. 771"]
theorem exer_10_3_22 (θ : ℝ) (h : tan θ = 12 / 5) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin θ = -12 / 13 ∧ cos θ = -5 / 13 ∧ (sin θ)⁻¹ = -13 / 12 ∧ (cos θ)⁻¹ = -13 / 5 ∧
      cos θ / sin θ = 5 / 12 := by
  have hc := cos_neg_Q23' (by linarith [Real.pi_pos]) h2
  have hs : sin θ = 12 / 5 * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc.ne] at h; linarith
  have := sin_sq_add_cos_sq θ
  rw [hs] at this
  have hcv : cos θ = -5 / 13 := eq_of_neg_sq' hc (by norm_num) (by nlinarith)
  have hsv : sin θ = -12 / 13 := by rw [hs, hcv]; norm_num
  refine ⟨hsv, hcv, ?_, ?_, ?_⟩
  · rw [hsv]; norm_num
  · rw [hcv]; norm_num
  · rw [hsv, hcv]; norm_num

/-- Stitz-Zeager Exercise 10.3.23: `csc θ = 25/24` in Quadrant I gives `sin θ = 24/25`, `cos θ = 7/25`,
`tan θ = 24/7`, `sec θ = 25/7`, `cot θ = 7/24`. -/
@[kb "stitzzeager2013" "Exercise 10.3.23, p. 771"]
theorem exer_10_3_23 (θ : ℝ) (h : (sin θ)⁻¹ = 25 / 24) (h1 : 0 < θ) (h2 : θ < π / 2) :
    sin θ = 24 / 25 ∧ cos θ = 7 / 25 ∧ tan θ = 24 / 7 ∧ (cos θ)⁻¹ = 25 / 7 ∧
      cos θ / sin θ = 7 / 24 := by
  have hc := cos_pos_Q1' h1 h2
  have hsv : sin θ = 24 / 25 := by
    rw [inv_eq_iff_eq_inv] at h; rw [h]; norm_num
  have := sin_sq_add_cos_sq θ
  rw [hsv] at this
  have hcv : cos θ = 7 / 25 := eq_of_pos_sq' hc (by norm_num) (by nlinarith)
  refine ⟨hsv, hcv, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, hcv]; norm_num
  · rw [hcv]; norm_num
  · rw [hsv, hcv]; norm_num

/-- Stitz-Zeager Exercise 10.3.25: `csc θ = -10√91/91` in Quadrant III gives `sin θ = -√91/10`,
`cos θ = -3/10`, `tan θ = √91/3`, `sec θ = -10/3`, `cot θ = 3√91/91`. -/
@[kb "stitzzeager2013" "Exercise 10.3.25, p. 771"]
theorem exer_10_3_25 (θ : ℝ) (h : (sin θ)⁻¹ = -(10 * √91 / 91)) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin θ = -(√91 / 10) ∧ cos θ = -3 / 10 ∧ tan θ = √91 / 3 ∧ (cos θ)⁻¹ = -10 / 3 ∧
      cos θ / sin θ = 3 * √91 / 91 := by
  have hc := cos_neg_Q23' (by linarith [Real.pi_pos]) h2
  have h9 : √91 ^ 2 = 91 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √91 := by positivity
  have hsv : sin θ = -(√91 / 10) := by
    rw [inv_eq_iff_eq_inv] at h; rw [h]; field_simp; nlinarith [h9]
  have := sin_sq_add_cos_sq θ
  rw [hsv] at this
  have hcv : cos θ = -3 / 10 := eq_of_neg_sq' hc (by norm_num) (by rw [neg_sq, div_pow, h9] at this; nlinarith)
  refine ⟨hsv, hcv, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, hcv]; field_simp
  · rw [hcv]; norm_num
  · rw [hsv, hcv]; field_simp; nlinarith [h9]

private lemma cot_eq_inv_tan' (θ : ℝ) : cos θ / sin θ = (tan θ)⁻¹ := by
  rw [tan_eq_sin_div_cos, inv_div]

/-- Stitz-Zeager Exercise 10.3.26: `cot θ = -23` in Quadrant II gives `sin θ = √530/530`,
`cos θ = -23√530/530`, `tan θ = -1/23`, `csc θ = √530`, `sec θ = -√530/23`. -/
@[kb "stitzzeager2013" "Exercise 10.3.26, p. 771"]
theorem exer_10_3_26 (θ : ℝ) (h : cos θ / sin θ = -23) (h1 : π / 2 < θ) (h2 : θ < π) :
    sin θ = √530 / 530 ∧ cos θ = -(23 * √530 / 530) ∧ tan θ = -1 / 23 ∧ (sin θ)⁻¹ = √530 ∧
      (cos θ)⁻¹ = -(√530 / 23) := by
  have hs := sin_pos_of_pos_of_lt_pi (x := θ) (by linarith [Real.pi_pos]) h2
  have hcs : cos θ = -23 * sin θ := by
    rw [div_eq_iff hs.ne'] at h; linarith
  have := sin_sq_add_cos_sq θ
  rw [hcs] at this
  have h5 : √530 ^ 2 = 530 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √530 := by positivity
  have hsv : sin θ = √530 / 530 := eq_of_pos_sq' hs (by positivity) (by rw [div_pow, h5]; nlinarith)
  have hcv : cos θ = -(23 * √530 / 530) := by rw [hcs, hsv]; ring
  refine ⟨hsv, hcv, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, hcv]; field_simp
  · rw [hsv]; field_simp; nlinarith [h5]
  · rw [hcv]; field_simp; nlinarith [h5]

/-- Stitz-Zeager Exercise 10.3.28: `sec θ = -4` in Quadrant II gives `cos θ = -1/4`, `sin θ = √15/4`,
`tan θ = -√15`, `csc θ = 4√15/15`, `cot θ = -√15/15`. -/
@[kb "stitzzeager2013" "Exercise 10.3.28, p. 771"]
theorem exer_10_3_28 (θ : ℝ) (h : (cos θ)⁻¹ = -4) (h1 : π / 2 < θ) (h2 : θ < π) :
    cos θ = -1 / 4 ∧ sin θ = √15 / 4 ∧ tan θ = -√15 ∧ (sin θ)⁻¹ = 4 * √15 / 15 ∧
      cos θ / sin θ = -(√15 / 15) := by
  have hs := sin_pos_of_pos_of_lt_pi (x := θ) (by linarith [Real.pi_pos]) h2
  have hcv : cos θ = -1 / 4 := by
    rw [inv_eq_iff_eq_inv] at h; rw [h]; norm_num
  have := sin_sq_add_cos_sq θ
  rw [hcv] at this
  have h5 : √15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √15 := by positivity
  have hsv : sin θ = √15 / 4 := eq_of_pos_sq' hs (by positivity) (by rw [div_pow, h5]; nlinarith)
  refine ⟨hcv, hsv, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, hcv]; field_simp
  · rw [hsv]; field_simp; nlinarith [h5]
  · rw [hsv, hcv]; field_simp; nlinarith [h5]

/-- Stitz-Zeager Exercise 10.3.29: `cot θ = √5` in Quadrant III gives `sin θ = -√6/6`, `cos θ = -√30/6`,
`tan θ = √5/5`, `csc θ = -√6`, `sec θ = -√30/5`. -/
@[kb "stitzzeager2013" "Exercise 10.3.29, p. 771"]
theorem exer_10_3_29 (θ : ℝ) (h : cos θ / sin θ = √5) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin θ = -(√6 / 6) ∧ cos θ = -(√30 / 6) ∧ tan θ = √5 / 5 ∧ (sin θ)⁻¹ = -√6 ∧
      (cos θ)⁻¹ = -(√30 / 5) := by
  have hs := sin_neg_Q34' h1 (by linarith [Real.pi_pos])
  have hcs : cos θ = √5 * sin θ := by
    rw [div_eq_iff hs.ne] at h; linarith
  have := sin_sq_add_cos_sq θ
  rw [hcs] at this
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h30 : √30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  have h30' : √30 = √5 * √6 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hp : 0 < √5 := by positivity
  have hp6 : 0 < √6 := by positivity
  have hsv : sin θ = -(√6 / 6) :=
    eq_of_neg_sq' hs (by apply neg_nonpos.mpr; positivity) (by rw [neg_sq, div_pow, h6]; nlinarith)
  have hcv : cos θ = -(√30 / 6) := by rw [hcs, hsv, h30']; ring
  refine ⟨hsv, hcv, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, hcv, h30']; field_simp; nlinarith [h5]
  · rw [hsv]; field_simp; nlinarith [h6]
  · rw [hcv]; field_simp; nlinarith [h30]

/-- Stitz-Zeager Exercise 10.3.32: `csc θ = 5` with `π/2 < θ < π` gives `sin θ = 1/5`, `cos θ = -2√6/5`,
`tan θ = -√6/12`, `sec θ = -5√6/12`, `cot θ = -2√6`. -/
@[kb "stitzzeager2013" "Exercise 10.3.32, p. 771"]
theorem exer_10_3_32 (θ : ℝ) (h : (sin θ)⁻¹ = 5) (h1 : π / 2 < θ) (h2 : θ < π) :
    sin θ = 1 / 5 ∧ cos θ = -(2 * √6 / 5) ∧ tan θ = -(√6 / 12) ∧ (cos θ)⁻¹ = -(5 * √6 / 12) ∧
      cos θ / sin θ = -(2 * √6) := by
  have hc := cos_neg_Q23' h1 (by linarith [Real.pi_pos])
  have hsv : sin θ = 1 / 5 := by
    rw [inv_eq_iff_eq_inv] at h; rw [h]; norm_num
  have := sin_sq_add_cos_sq θ
  rw [hsv] at this
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √6 := by positivity
  have hcv : cos θ = -(2 * √6 / 5) :=
    eq_of_neg_sq' hc (by apply neg_nonpos.mpr; positivity) (by rw [neg_sq, div_pow, mul_pow, h6]; nlinarith)
  refine ⟨hsv, hcv, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, hcv]; field_simp; nlinarith [h6]
  · rw [hcv]; field_simp; nlinarith [h6]
  · rw [hsv, hcv]; field_simp

/-- Stitz-Zeager Exercise 10.3.33: `tan θ = √10` with `π < θ < 3π/2` gives `sin θ = -√110/11`,
`cos θ = -√11/11`, `csc θ = -√110/10`, `sec θ = -√11`, `cot θ = √10/10`. -/
@[kb "stitzzeager2013" "Exercise 10.3.33, p. 771"]
theorem exer_10_3_33 (θ : ℝ) (h : tan θ = √10) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin θ = -(√110 / 11) ∧ cos θ = -(√11 / 11) ∧ (sin θ)⁻¹ = -(√110 / 10) ∧ (cos θ)⁻¹ = -√11 ∧
      cos θ / sin θ = √10 / 10 := by
  have hc := cos_neg_Q23' (by linarith [Real.pi_pos]) h2
  have hs : sin θ = √10 * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc.ne] at h; linarith
  have := sin_sq_add_cos_sq θ
  rw [hs] at this
  have h10 : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have h11 : √11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h110 : √110 ^ 2 = 110 := Real.sq_sqrt (by norm_num)
  have h110' : √110 = √10 * √11 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hp : 0 < √11 := by positivity
  have hp10 : 0 < √10 := by positivity
  have hcv : cos θ = -(√11 / 11) :=
    eq_of_neg_sq' hc (by apply neg_nonpos.mpr; positivity) (by rw [neg_sq, div_pow, h11]; nlinarith)
  have hsv : sin θ = -(√110 / 11) := by rw [hs, hcv, h110']; ring
  refine ⟨hsv, hcv, ?_, ?_, ?_⟩
  · rw [hsv]; field_simp; nlinarith [h110]
  · rw [hcv]; field_simp; nlinarith [h11]
  · rw [cot_eq_inv_tan', h]; field_simp; nlinarith [h10]

/-- Stitz-Zeager Exercise 10.3.34: `sec θ = 2√5` with `3π/2 < θ < 2π` gives `cos θ = √5/10`,
`sin θ = -√95/10`, `tan θ = -√19`, `csc θ = -2√95/19`, `cot θ = -√19/19`. -/
@[kb "stitzzeager2013" "Exercise 10.3.34, p. 771"]
theorem exer_10_3_34 (θ : ℝ) (h : (cos θ)⁻¹ = 2 * √5) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    cos θ = √5 / 10 ∧ sin θ = -(√95 / 10) ∧ tan θ = -√19 ∧ (sin θ)⁻¹ = -(2 * √95 / 19) ∧
      cos θ / sin θ = -(√19 / 19) := by
  have hs := sin_neg_Q34' (by linarith [Real.pi_pos]) h2
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h19 : √19 ^ 2 = 19 := Real.sq_sqrt (by norm_num)
  have h95 : √95 ^ 2 = 95 := Real.sq_sqrt (by norm_num)
  have h95' : √95 = √5 * √19 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hp : 0 < √5 := by positivity
  have hp19 : 0 < √19 := by positivity
  have hcv : cos θ = √5 / 10 := by
    rw [inv_eq_iff_eq_inv] at h; rw [h]; field_simp; nlinarith [h5]
  have := sin_sq_add_cos_sq θ
  rw [hcv] at this
  have hsv : sin θ = -(√95 / 10) :=
    eq_of_neg_sq' hs (by apply neg_nonpos.mpr; positivity) (by rw [neg_sq, div_pow, h95]; rw [div_pow, h5] at this; nlinarith)
  have ht : tan θ = -√19 := by
    rw [tan_eq_sin_div_cos, hsv, hcv, h95']; field_simp
  refine ⟨hcv, hsv, ht, ?_, ?_⟩
  · rw [hsv]; field_simp; nlinarith [h95]
  · rw [cot_eq_inv_tan', ht]; field_simp; nlinarith [h19]

end UndergradKB.Precalculus.Course
