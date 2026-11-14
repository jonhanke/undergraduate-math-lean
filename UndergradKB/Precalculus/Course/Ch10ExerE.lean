import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.4
(second part: sums, identities, half and double angles) -/

namespace UndergradKB.Precalculus.Course

open Real

private lemma eq_pos_sq {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (h : c ^ 2 = a ^ 2) : c = a :=
  (pow_left_inj₀ hc.le ha two_ne_zero).mp h

private lemma eq_neg_sq {c a : ℝ} (hc : c < 0) (ha : a ≤ 0) (h : c ^ 2 = a ^ 2) : c = a := by
  have := eq_pos_sq (c := -c) (a := -a) (by linarith) (by linarith) (by simpa using h)
  linarith

private lemma sin_neg_Q34'' {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) : sin θ < 0 := by
  have h : sin θ = -sin (θ - π) := by rw [sin_sub_pi]; ring
  have := sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
  linarith

private lemma cos_pos_Q4'' {θ : ℝ} (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : 0 < cos θ := by
  rw [← cos_sub_two_pi]
  apply cos_pos_of_mem_Ioo; constructor <;> linarith

private lemma sqrt_half_sq (u : ℝ) (hu : 0 ≤ u) : (√u / 2) ^ 2 = u / 4 := by
  rw [div_pow, Real.sq_sqrt hu]; norm_num

private lemma cos_of_dbl {x c a : ℝ} (hd : cos (2 * x) = c) (hx : 0 < cos x) (ha : 0 ≤ a)
    (h : a ^ 2 = (1 + c) / 2) : cos x = a :=
  eq_pos_sq hx ha (by have := cos_two_mul x; rw [hd] at this; nlinarith)

private lemma cos_of_dbl_neg {x c a : ℝ} (hd : cos (2 * x) = c) (hx : cos x < 0) (ha : a ≤ 0)
    (h : a ^ 2 = (1 + c) / 2) : cos x = a :=
  eq_neg_sq hx ha (by have := cos_two_mul x; rw [hd] at this; nlinarith)

private lemma sin_of_dbl {x c a : ℝ} (hd : cos (2 * x) = c) (hx : 0 < sin x) (ha : 0 ≤ a)
    (h : a ^ 2 = (1 - c) / 2) : sin x = a :=
  eq_pos_sq hx ha (by
    have h1 := cos_two_mul x
    have h2 := sin_sq_add_cos_sq x
    rw [hd] at h1; nlinarith)

/-- Stitz-Zeager Exercise 10.4.22: `cos α = √5/5` (Quadrant IV) and `sin β = √10/10`
(`π/2 < β < π`) give the six sum and difference values `-√2/10, 7√2/10, -7, -√2/2, √2/2, -1`. -/
@[kb "stitzzeager2013" "Exercise 10.4.22, p. 794"]
theorem exer_10_4_22 (α β : ℝ) (hα : cos α = √5 / 5) (h1 : 3 * π / 2 < α) (h2 : α < 2 * π)
    (hβ : sin β = √10 / 10) (h3 : π / 2 < β) (h4 : β < π) :
    cos (α + β) = -(√2 / 10) ∧ sin (α + β) = 7 * √2 / 10 ∧ tan (α + β) = -7 ∧
      cos (α - β) = -(√2 / 2) ∧ sin (α - β) = √2 / 2 ∧ tan (α - β) = -1 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h10 : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have h2' : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp2 : 0 < √2 := by positivity
  have hm : √5 * √10 = 5 * √2 := by
    rw [← Real.sqrt_mul (by norm_num), show (5 : ℝ) * 10 = 5 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hsa : sin α = -(2 * √5 / 5) := by
    have hs := sin_neg_Q34'' (by linarith [Real.pi_pos]) h2
    have := sin_sq_add_cos_sq α
    rw [hα] at this
    exact eq_neg_sq hs (by apply neg_nonpos.mpr; positivity)
      (by rw [neg_sq, div_pow, mul_pow, h5]; nlinarith)
  have hcb : cos β = -(3 * √10 / 10) := by
    have hc := cos_neg_of_pi_div_two_lt_of_lt h3 (by linarith [Real.pi_pos])
    have := sin_sq_add_cos_sq β
    rw [hβ] at this
    exact eq_neg_sq hc (by apply neg_nonpos.mpr; positivity)
      (by rw [neg_sq, div_pow, mul_pow, h10]; nlinarith)
  have ha : cos (α + β) = -(√2 / 10) := by
    rw [cos_add, hα, hsa, hβ, hcb]; linear_combination (-1 / 50) * hm
  have hb : sin (α + β) = 7 * √2 / 10 := by
    rw [sin_add, hα, hsa, hβ, hcb]; linear_combination (7 / 50) * hm
  have hd : cos (α - β) = -(√2 / 2) := by
    rw [cos_sub, hα, hsa, hβ, hcb]; linear_combination (-1 / 10) * hm
  have he : sin (α - β) = √2 / 2 := by
    rw [sin_sub, hα, hsa, hβ, hcb]; linear_combination (1 / 10) * hm
  refine ⟨ha, hb, ?_, hd, he, ?_⟩
  · rw [tan_eq_sin_div_cos, ha, hb]; field_simp
  · rw [tan_eq_sin_div_cos, hd, he]; field_simp

/-- Stitz-Zeager Exercise 10.4.24: `sin α = 3/5` (`0 < α < π/2`) and `cos β = 12/13`
(`3π/2 < β < 2π`) give `sin(α+β) = 16/65`, `cos(α-β) = 33/65`, `tan(α-β) = 56/33`. -/
@[kb "stitzzeager2013" "Exercise 10.4.24, p. 794"]
theorem exer_10_4_24 (α β : ℝ) (hα : sin α = 3 / 5) (h1 : 0 < α) (h2 : α < π / 2)
    (hβ : cos β = 12 / 13) (h3 : 3 * π / 2 < β) (h4 : β < 2 * π) :
    sin (α + β) = 16 / 65 ∧ cos (α - β) = 33 / 65 ∧ tan (α - β) = 56 / 33 := by
  have hca : cos α = 4 / 5 := by
    have hc := cos_pos_of_mem_Ioo (x := α) ⟨by linarith [Real.pi_pos], h2⟩
    have := sin_sq_add_cos_sq α
    rw [hα] at this
    exact eq_pos_sq hc (by norm_num) (by nlinarith)
  have hsb : sin β = -(5 / 13) := by
    have hs := sin_neg_Q34'' (by linarith [Real.pi_pos]) h4
    have := sin_sq_add_cos_sq β
    rw [hβ] at this
    exact eq_neg_sq hs (by norm_num) (by nlinarith)
  have h5 : sin (α - β) = 56 / 65 := by rw [sin_sub, hα, hca, hβ, hsb]; norm_num
  have h6 : cos (α - β) = 33 / 65 := by rw [cos_sub, hα, hca, hβ, hsb]; norm_num
  refine ⟨?_, h6, ?_⟩
  · rw [sin_add, hα, hca, hβ, hsb]; norm_num
  · rw [tan_eq_sin_div_cos, h5, h6]; norm_num

/-- Stitz-Zeager Exercise 10.4.25: `sec α = -5/3` (`π/2 < α < π`) and `tan β = 24/7`
(`π < β < 3π/2`) give `csc(α-β) = -5/4`, `sec(α+β) = 125/117`, `cot(α+β) = 117/44`. -/
@[kb "stitzzeager2013" "Exercise 10.4.25, p. 795"]
theorem exer_10_4_25 (α β : ℝ) (hα : (cos α)⁻¹ = -5 / 3) (h1 : π / 2 < α) (h2 : α < π)
    (hβ : tan β = 24 / 7) (h3 : π < β) (h4 : β < 3 * π / 2) :
    (sin (α - β))⁻¹ = -5 / 4 ∧ (cos (α + β))⁻¹ = 125 / 117 ∧
      cos (α + β) / sin (α + β) = 117 / 44 := by
  have hca : cos α = -3 / 5 := by
    rw [inv_eq_iff_eq_inv] at hα; rw [hα]; norm_num
  have hsa : sin α = 4 / 5 := by
    have hs := sin_pos_of_pos_of_lt_pi (x := α) (by linarith [Real.pi_pos]) h2
    have := sin_sq_add_cos_sq α
    rw [hca] at this
    exact eq_pos_sq hs (by norm_num) (by nlinarith)
  have hcb0 : cos β < 0 := cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos]) (by linarith)
  have hsb' : sin β = 24 / 7 * cos β := by
    rw [tan_eq_sin_div_cos, div_eq_iff hcb0.ne] at hβ; linarith
  have hcb : cos β = -7 / 25 := by
    have := sin_sq_add_cos_sq β
    rw [hsb'] at this
    exact eq_neg_sq hcb0 (by norm_num) (by nlinarith)
  have hsb : sin β = -24 / 25 := by rw [hsb', hcb]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [sin_sub, hsa, hca, hcb, hsb]; norm_num
  · rw [cos_add, hsa, hca, hcb, hsb]; norm_num
  · rw [cos_add, sin_add, hsa, hca, hcb, hsb]; norm_num

/-- Stitz-Zeager Exercise 10.4.26: `cos(θ - π) = -cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.26, p. 795"]
theorem exer_10_4_26 (θ : ℝ) : cos (θ - π) = -cos θ := cos_sub_pi θ

/-- Stitz-Zeager Exercise 10.4.27: `sin(π - θ) = sin θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.27, p. 795"]
theorem exer_10_4_27 (θ : ℝ) : sin (π - θ) = sin θ := sin_pi_sub θ

/-- Stitz-Zeager Exercise 10.4.28: `tan(θ + π/2) = -cot θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.28, p. 795"]
theorem exer_10_4_28 (θ : ℝ) : tan (θ + π / 2) = -(cos θ / sin θ) := by
  rw [tan_eq_sin_div_cos, sin_add_pi_div_two, cos_add_pi_div_two, div_neg]

/-- Stitz-Zeager Exercise 10.4.29: `sin(α+β) + sin(α-β) = 2 sin α cos β`. -/
@[kb "stitzzeager2013" "Exercise 10.4.29, p. 795"]
theorem exer_10_4_29 (α β : ℝ) : sin (α + β) + sin (α - β) = 2 * sin α * cos β := by
  rw [sin_add, sin_sub]; ring

/-- Stitz-Zeager Exercise 10.4.30: `sin(α+β) - sin(α-β) = 2 cos α sin β`. -/
@[kb "stitzzeager2013" "Exercise 10.4.30, p. 795"]
theorem exer_10_4_30 (α β : ℝ) : sin (α + β) - sin (α - β) = 2 * cos α * sin β := by
  rw [sin_add, sin_sub]; ring

/-- Stitz-Zeager Exercise 10.4.31: `cos(α+β) + cos(α-β) = 2 cos α cos β`. -/
@[kb "stitzzeager2013" "Exercise 10.4.31, p. 795"]
theorem exer_10_4_31 (α β : ℝ) : cos (α + β) + cos (α - β) = 2 * cos α * cos β := by
  rw [cos_add, cos_sub]; ring

/-- Stitz-Zeager Exercise 10.4.32: `cos(α+β) - cos(α-β) = -2 sin α sin β`. -/
@[kb "stitzzeager2013" "Exercise 10.4.32, p. 795"]
theorem exer_10_4_32 (α β : ℝ) : cos (α + β) - cos (α - β) = -2 * sin α * sin β := by
  rw [cos_add, cos_sub]; ring

/-- Stitz-Zeager Exercise 10.4.33: `sin(α+β)/sin(α-β) = (1 + cot α tan β)/(1 - cot α tan β)`
(where everything is defined). -/
@[kb "stitzzeager2013" "Exercise 10.4.33, p. 795"]
theorem exer_10_4_33 (α β : ℝ) (hs : sin α ≠ 0) (hc : cos β ≠ 0) (hd : sin (α - β) ≠ 0) :
    sin (α + β) / sin (α - β) =
      (1 + cos α / sin α * tan β) / (1 - cos α / sin α * tan β) := by
  have hx : 1 - cos α / sin α * tan β = sin (α - β) / (sin α * cos β) := by
    rw [tan_eq_sin_div_cos, sin_sub]; field_simp
  have hx' : 1 - cos α / sin α * tan β ≠ 0 := by
    rw [hx]; exact div_ne_zero hd (mul_ne_zero hs hc)
  rw [div_eq_div_iff hd hx', hx, tan_eq_sin_div_cos, sin_add, sin_sub]
  field_simp

/-- Stitz-Zeager Exercise 10.4.34: `cos(α+β)/cos(α-β) = (1 - tan α tan β)/(1 + tan α tan β)`
(where everything is defined). -/
@[kb "stitzzeager2013" "Exercise 10.4.34, p. 795"]
theorem exer_10_4_34 (α β : ℝ) (ha : cos α ≠ 0) (hb : cos β ≠ 0) (hd : cos (α - β) ≠ 0) :
    cos (α + β) / cos (α - β) = (1 - tan α * tan β) / (1 + tan α * tan β) := by
  have hx : 1 + tan α * tan β = cos (α - β) / (cos α * cos β) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, cos_sub]; field_simp
  have hx' : 1 + tan α * tan β ≠ 0 := by
    rw [hx]; exact div_ne_zero hd (mul_ne_zero ha hb)
  rw [div_eq_div_iff hd hx', hx, tan_eq_sin_div_cos, tan_eq_sin_div_cos, cos_add, cos_sub]
  field_simp

/-- Stitz-Zeager Exercise 10.4.36: the difference quotient of sine splits as
`(sin(t+h) - sin t)/h = cos t (sin h/h) + sin t ((cos h - 1)/h)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.36, p. 795"]
theorem exer_10_4_36 (t h : ℝ) :
    (sin (t + h) - sin t) / h = cos t * (sin h / h) + sin t * ((cos h - 1) / h) := by
  rw [sin_add]; ring

/-- Stitz-Zeager Exercise 10.4.37: the difference quotient of cosine splits as
`(cos(t+h) - cos t)/h = cos t ((cos h - 1)/h) - sin t (sin h/h)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.37, p. 795"]
theorem exer_10_4_37 (t h : ℝ) :
    (cos (t + h) - cos t) / h = cos t * ((cos h - 1) / h) - sin t * (sin h / h) := by
  rw [cos_add]; ring

/-- Stitz-Zeager Exercise 10.4.39: `cos 75° = √(2 - √3)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.39, p. 795"]
theorem exer_10_4_39 : cos (75 * π / 180) = √(2 - √3) / 2 := by
  have h3 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hd : cos (2 * (75 * π / 180)) = -(√3 / 2) := by
    rw [show 2 * (75 * π / 180) = π - π / 6 by ring, cos_pi_sub, cos_pi_div_six]
  refine cos_of_dbl hd (cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    (by positivity) ?_
  rw [sqrt_half_sq _ (by linarith)]; ring

/-- Stitz-Zeager Exercise 10.4.41: `cos 67.5° = √(2 - √2)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.41, p. 795"]
theorem exer_10_4_41 : cos (3 * π / 8) = √(2 - √2) / 2 := by
  have h2 : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hd : cos (2 * (3 * π / 8)) = -(√2 / 2) := by
    rw [show 2 * (3 * π / 8) = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]
  refine cos_of_dbl hd (cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
    (by positivity) ?_
  rw [sqrt_half_sq _ (by linarith)]; ring

/-- Stitz-Zeager Exercise 10.4.44: `cos(7π/12) = -√(2 - √3)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.44, p. 795"]
theorem exer_10_4_44 : cos (7 * π / 12) = -(√(2 - √3) / 2) := by
  have h3 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hd : cos (2 * (7 * π / 12)) = -(√3 / 2) := by
    rw [show 2 * (7 * π / 12) = π / 6 + π by ring, cos_add_pi, cos_pi_div_six]
  refine cos_of_dbl_neg hd (cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])) (by have : 0 ≤ √(2 - √3) / 2 := by positivity
                                     linarith) ?_
  rw [neg_sq, sqrt_half_sq _ (by linarith)]; ring

/-- Stitz-Zeager Exercise 10.4.45: `sin(π/12) = √(2 - √3)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.45, p. 795"]
theorem exer_10_4_45 : sin (π / 12) = √(2 - √3) / 2 := by
  have h3 : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hd : cos (2 * (π / 12)) = √3 / 2 := by
    rw [show 2 * (π / 12) = π / 6 by ring, cos_pi_div_six]
  refine sin_of_dbl hd (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])) (by positivity) ?_
  rw [sqrt_half_sq _ (by linarith)]; ring

/-- Stitz-Zeager Exercise 10.4.46: `cos(π/8) = √(2 + √2)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.46, p. 795"]
theorem exer_10_4_46 : cos (π / 8) = √(2 + √2) / 2 := cos_pi_div_eight

/-- Stitz-Zeager Exercise 10.4.47: `sin(5π/8) = √(2 + √2)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.47, p. 795"]
theorem exer_10_4_47 : sin (5 * π / 8) = √(2 + √2) / 2 := by
  have hd : cos (2 * (5 * π / 8)) = -(√2 / 2) := by
    rw [show 2 * (5 * π / 8) = π / 4 + π by ring, cos_add_pi, cos_pi_div_four]
  refine sin_of_dbl hd (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])) (by positivity) ?_
  rw [sqrt_half_sq _ (by positivity)]; ring

/-- Stitz-Zeager Exercise 10.4.49: `sin θ = -7/25` with `3π/2 < θ < 2π`: `sin 2θ = -336/625`,
`cos 2θ = 527/625`, `tan 2θ = -336/527`, `sin(θ/2) = √2/10`, `cos(θ/2) = -7√2/10`,
`tan(θ/2) = -1/7`. -/
@[kb "stitzzeager2013" "Exercise 10.4.49, p. 796"]
theorem exer_10_4_49 (θ : ℝ) (h : sin θ = -7 / 25) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    sin (2 * θ) = -336 / 625 ∧ cos (2 * θ) = 527 / 625 ∧ tan (2 * θ) = -336 / 527 ∧
      sin (θ / 2) = √2 / 10 ∧ cos (θ / 2) = -(7 * √2 / 10) ∧ tan (θ / 2) = -1 / 7 := by
  have hc : cos θ = 24 / 25 := by
    have hc := cos_pos_Q4'' h1 h2
    have := sin_sq_add_cos_sq θ
    rw [h] at this
    exact eq_pos_sq hc (by norm_num) (by nlinarith)
  have h2' : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  have hd : cos (2 * (θ / 2)) = 24 / 25 := by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact hc
  have hsh : sin (θ / 2) = √2 / 10 :=
    sin_of_dbl hd (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
      (by positivity) (by rw [div_pow, h2']; norm_num)
  have hch : cos (θ / 2) = -(7 * √2 / 10) :=
    cos_of_dbl_neg hd (cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])) (by have : 0 ≤ 7 * √2 / 10 := by positivity
                                       linarith)
      (by rw [neg_sq, div_pow, mul_pow, h2']; norm_num)
  have e1 : sin (2 * θ) = -336 / 625 := by rw [sin_two_mul, h, hc]; norm_num
  have e2 : cos (2 * θ) = 527 / 625 := by rw [cos_two_mul, hc]; norm_num
  refine ⟨e1, e2, ?_, hsh, hch, ?_⟩
  · rw [tan_eq_sin_div_cos, e1, e2]; norm_num
  · rw [tan_eq_sin_div_cos, hsh, hch]; field_simp

/-- Stitz-Zeager Exercise 10.4.51: `tan θ = 12/5` with `π < θ < 3π/2`: `sin 2θ = 120/169`,
`cos 2θ = -119/169`, `tan 2θ = -120/119`, `sin(θ/2) = 3√13/13`, `cos(θ/2) = -2√13/13`,
`tan(θ/2) = -3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.51, p. 796"]
theorem exer_10_4_51 (θ : ℝ) (h : tan θ = 12 / 5) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin (2 * θ) = 120 / 169 ∧ cos (2 * θ) = -119 / 169 ∧ tan (2 * θ) = -120 / 119 ∧
      sin (θ / 2) = 3 * √13 / 13 ∧ cos (θ / 2) = -(2 * √13 / 13) ∧ tan (θ / 2) = -3 / 2 := by
  have hc0 : cos θ < 0 := cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos]) (by linarith)
  have hs' : sin θ = 12 / 5 * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc0.ne] at h; linarith
  have hc : cos θ = -5 / 13 := by
    have := sin_sq_add_cos_sq θ
    rw [hs'] at this
    exact eq_neg_sq hc0 (by norm_num) (by nlinarith)
  have hs : sin θ = -12 / 13 := by rw [hs', hc]; norm_num
  have h13 : √13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √13 := by positivity
  have hd : cos (2 * (θ / 2)) = -5 / 13 := by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact hc
  have hsh : sin (θ / 2) = 3 * √13 / 13 :=
    sin_of_dbl hd (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
      (by positivity) (by rw [div_pow, mul_pow, h13]; norm_num)
  have hch : cos (θ / 2) = -(2 * √13 / 13) :=
    cos_of_dbl_neg hd (cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])) (by have : 0 ≤ 2 * √13 / 13 := by positivity
                                       linarith)
      (by rw [neg_sq, div_pow, mul_pow, h13]; norm_num)
  have e1 : sin (2 * θ) = 120 / 169 := by rw [sin_two_mul, hs, hc]; norm_num
  have e2 : cos (2 * θ) = -119 / 169 := by rw [cos_two_mul, hc]; norm_num
  refine ⟨e1, e2, ?_, hsh, hch, ?_⟩
  · rw [tan_eq_sin_div_cos, e1, e2]; norm_num
  · rw [tan_eq_sin_div_cos, hsh, hch]; field_simp

/-- Stitz-Zeager Exercise 10.4.53: `cos θ = 3/5` with `0 < θ < π/2`: `sin 2θ = 24/25`,
`cos 2θ = -7/25`, `tan 2θ = -24/7`, `sin(θ/2) = √5/5`, `cos(θ/2) = 2√5/5`, `tan(θ/2) = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.53, p. 796"]
theorem exer_10_4_53 (θ : ℝ) (h : cos θ = 3 / 5) (h1 : 0 < θ) (h2 : θ < π / 2) :
    sin (2 * θ) = 24 / 25 ∧ cos (2 * θ) = -7 / 25 ∧ tan (2 * θ) = -24 / 7 ∧
      sin (θ / 2) = √5 / 5 ∧ cos (θ / 2) = 2 * √5 / 5 ∧ tan (θ / 2) = 1 / 2 := by
  have hs : sin θ = 4 / 5 := by
    have hs := sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
    have := sin_sq_add_cos_sq θ
    rw [h] at this
    exact eq_pos_sq hs (by norm_num) (by nlinarith)
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √5 := by positivity
  have hd : cos (2 * (θ / 2)) = 3 / 5 := by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact h
  have hsh : sin (θ / 2) = √5 / 5 :=
    sin_of_dbl hd (sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
      (by positivity) (by rw [div_pow, h5]; norm_num)
  have hch : cos (θ / 2) = 2 * √5 / 5 :=
    cos_of_dbl hd (cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (by positivity) (by rw [div_pow, mul_pow, h5]; norm_num)
  have e1 : sin (2 * θ) = 24 / 25 := by rw [sin_two_mul, hs, h]; norm_num
  have e2 : cos (2 * θ) = -7 / 25 := by rw [cos_two_mul, h]; norm_num
  refine ⟨e1, e2, ?_, hsh, hch, ?_⟩
  · rw [tan_eq_sin_div_cos, e1, e2]; norm_num
  · rw [tan_eq_sin_div_cos, hsh, hch]; field_simp

/-- Stitz-Zeager Exercise 10.4.59: `(cos θ + sin θ)² = 1 + sin 2θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.59, p. 796"]
theorem exer_10_4_59 (θ : ℝ) : (cos θ + sin θ) ^ 2 = 1 + sin (2 * θ) := by
  rw [sin_two_mul]; nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.4.60: `(cos θ - sin θ)² = 1 - sin 2θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.60, p. 796"]
theorem exer_10_4_60 (θ : ℝ) : (cos θ - sin θ) ^ 2 = 1 - sin (2 * θ) := by
  rw [sin_two_mul]; nlinarith [sin_sq_add_cos_sq θ]

/-- Stitz-Zeager Exercise 10.4.62: `csc 2θ = (cot θ + tan θ)/2` (where defined). -/
@[kb "stitzzeager2013" "Exercise 10.4.62, p. 796"]
theorem exer_10_4_62 (θ : ℝ) (hs : sin θ ≠ 0) (hc : cos θ ≠ 0) :
    (sin (2 * θ))⁻¹ = (cos θ / sin θ + tan θ) / 2 := by
  rw [sin_two_mul, tan_eq_sin_div_cos]
  have := sin_sq_add_cos_sq θ
  field_simp
  nlinarith [this]

/-- Stitz-Zeager Exercise 10.4.63: `8 sin⁴ θ = cos 4θ - 4 cos 2θ + 3`. -/
@[kb "stitzzeager2013" "Exercise 10.4.63, p. 796"]
theorem exer_10_4_63 (θ : ℝ) : 8 * sin θ ^ 4 = cos (4 * θ) - 4 * cos (2 * θ) + 3 := by
  have h4 : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; ring
  have hs : sin θ ^ 2 = 1 - cos θ ^ 2 := by nlinarith [sin_sq_add_cos_sq θ]
  have : sin θ ^ 4 = (1 - cos θ ^ 2) ^ 2 := by rw [← hs]; ring
  rw [h4, cos_two_mul, this]; ring

/-- Stitz-Zeager Exercise 10.4.64: `8 cos⁴ θ = cos 4θ + 4 cos 2θ + 3`. -/
@[kb "stitzzeager2013" "Exercise 10.4.64, p. 796"]
theorem exer_10_4_64 (θ : ℝ) : 8 * cos θ ^ 4 = cos (4 * θ) + 4 * cos (2 * θ) + 3 := by
  have h4 : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; ring
  rw [h4, cos_two_mul]; ring

/-- Stitz-Zeager Exercise 10.4.65: `sin 3θ = 3 sin θ - 4 sin³ θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.65, p. 796"]
theorem exer_10_4_65 (θ : ℝ) : sin (3 * θ) = 3 * sin θ - 4 * sin θ ^ 3 := sin_three_mul θ

/-- Stitz-Zeager Exercise 10.4.66: `sin 4θ = 4 sin θ cos³ θ - 4 sin³ θ cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.66, p. 796"]
theorem exer_10_4_66 (θ : ℝ) :
    sin (4 * θ) = 4 * sin θ * cos θ ^ 3 - 4 * sin θ ^ 3 * cos θ := by
  have h4 : sin (4 * θ) = 2 * sin (2 * θ) * cos (2 * θ) := by
    rw [← sin_two_mul]; congr 1; ring
  have hc : cos (2 * θ) = cos θ ^ 2 - sin θ ^ 2 := by
    rw [cos_two_mul]; nlinarith [sin_sq_add_cos_sq θ]
  rw [h4, sin_two_mul, hc]; ring

/-- Stitz-Zeager Exercise 10.4.69: `cos 4θ = 8 cos⁴ θ - 8 cos² θ + 1`. -/
@[kb "stitzzeager2013" "Exercise 10.4.69, p. 796"]
theorem exer_10_4_69 (θ : ℝ) : cos (4 * θ) = 8 * cos θ ^ 4 - 8 * cos θ ^ 2 + 1 := by
  have h4 : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; ring
  rw [h4, cos_two_mul]; ring

/-- Stitz-Zeager Exercise 10.4.70: `cos 8θ = 128 cos⁸ θ - 256 cos⁶ θ + 160 cos⁴ θ - 32 cos² θ + 1`. -/
@[kb "stitzzeager2013" "Exercise 10.4.70, p. 796"]
theorem exer_10_4_70 (θ : ℝ) :
    cos (8 * θ) = 128 * cos θ ^ 8 - 256 * cos θ ^ 6 + 160 * cos θ ^ 4 - 32 * cos θ ^ 2 + 1 := by
  have h8 : cos (8 * θ) = 2 * cos (4 * θ) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; ring
  have h4 : cos (4 * θ) = 8 * cos θ ^ 4 - 8 * cos θ ^ 2 + 1 := exer_10_4_69 θ
  rw [h8, h4]; ring

/-- Stitz-Zeager Exercise 10.4.72: `1/(cos θ - sin θ) + 1/(cos θ + sin θ) = 2 cos θ / cos 2θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.72, p. 796"]
theorem exer_10_4_72 (θ : ℝ) (h1 : cos θ - sin θ ≠ 0) (h2 : cos θ + sin θ ≠ 0) :
    1 / (cos θ - sin θ) + 1 / (cos θ + sin θ) = 2 * cos θ / cos (2 * θ) := by
  have hc : cos (2 * θ) = (cos θ - sin θ) * (cos θ + sin θ) := by
    rw [cos_two_mul]; nlinarith [sin_sq_add_cos_sq θ]
  rw [hc]; field_simp; ring

/-- Stitz-Zeager Exercise 10.4.73: `1/(cos θ - sin θ) - 1/(cos θ + sin θ) = 2 sin θ / cos 2θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.73, p. 796"]
theorem exer_10_4_73 (θ : ℝ) (h1 : cos θ - sin θ ≠ 0) (h2 : cos θ + sin θ ≠ 0) :
    1 / (cos θ - sin θ) - 1 / (cos θ + sin θ) = 2 * sin θ / cos (2 * θ) := by
  have hc : cos (2 * θ) = (cos θ - sin θ) * (cos θ + sin θ) := by
    rw [cos_two_mul]; nlinarith [sin_sq_add_cos_sq θ]
  rw [hc]; field_simp; ring

/-- Stitz-Zeager Exercise 10.4.74: `cos 3θ cos 5θ = (cos 2θ + cos 8θ)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.74, p. 797"]
theorem exer_10_4_74 (θ : ℝ) : cos (3 * θ) * cos (5 * θ) = (cos (2 * θ) + cos (8 * θ)) / 2 := by
  rw [show 2 * θ = 5 * θ - 3 * θ by ring, show 8 * θ = 5 * θ + 3 * θ by ring, cos_sub, cos_add]
  ring

/-- Stitz-Zeager Exercise 10.4.75: `sin 2θ sin 7θ = (cos 5θ - cos 9θ)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.75, p. 797"]
theorem exer_10_4_75 (θ : ℝ) : sin (2 * θ) * sin (7 * θ) = (cos (5 * θ) - cos (9 * θ)) / 2 := by
  rw [show 5 * θ = 7 * θ - 2 * θ by ring, show 9 * θ = 7 * θ + 2 * θ by ring, cos_sub, cos_add]
  ring

/-- Stitz-Zeager Exercise 10.4.76: `sin 9θ cos θ = (sin 8θ + sin 10θ)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.76, p. 797"]
theorem exer_10_4_76 (θ : ℝ) : sin (9 * θ) * cos θ = (sin (8 * θ) + sin (10 * θ)) / 2 := by
  rw [show 8 * θ = 9 * θ - θ by ring, show 10 * θ = 9 * θ + θ by ring, sin_sub, sin_add]
  ring

/-- Stitz-Zeager Exercise 10.4.77: `cos 2θ cos 6θ = (cos 4θ + cos 8θ)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.77, p. 797"]
theorem exer_10_4_77 (θ : ℝ) : cos (2 * θ) * cos (6 * θ) = (cos (4 * θ) + cos (8 * θ)) / 2 := by
  rw [show 4 * θ = 6 * θ - 2 * θ by ring, show 8 * θ = 6 * θ + 2 * θ by ring, cos_sub, cos_add]
  ring

/-- Stitz-Zeager Exercise 10.4.78: `sin 3θ sin 2θ = (cos θ - cos 5θ)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.78, p. 797"]
theorem exer_10_4_78 (θ : ℝ) : sin (3 * θ) * sin (2 * θ) = (cos θ - cos (5 * θ)) / 2 := by
  rw [show 5 * θ = 3 * θ + 2 * θ by ring, show θ = 3 * θ - 2 * θ by ring, cos_sub, cos_add]
  ring_nf

/-- Stitz-Zeager Exercise 10.4.79: `cos θ sin 3θ = (sin 2θ + sin 4θ)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.79, p. 797"]
theorem exer_10_4_79 (θ : ℝ) : cos θ * sin (3 * θ) = (sin (2 * θ) + sin (4 * θ)) / 2 := by
  rw [show 2 * θ = 3 * θ - θ by ring, show 4 * θ = 3 * θ + θ by ring, sin_sub, sin_add]
  ring

/-- Stitz-Zeager Exercise 10.4.80: `cos 3θ + cos 5θ = 2 cos 4θ cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.80, p. 797"]
theorem exer_10_4_80 (θ : ℝ) : cos (3 * θ) + cos (5 * θ) = 2 * cos (4 * θ) * cos θ := by
  rw [show 3 * θ = 4 * θ - θ by ring, show 5 * θ = 4 * θ + θ by ring, cos_sub, cos_add]
  ring

/-- Stitz-Zeager Exercise 10.4.81: `sin 2θ - sin 7θ = -2 cos(9θ/2) sin(5θ/2)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.81, p. 797"]
theorem exer_10_4_81 (θ : ℝ) :
    sin (2 * θ) - sin (7 * θ) = -2 * cos (9 / 2 * θ) * sin (5 / 2 * θ) := by
  rw [show 2 * θ = 9 / 2 * θ - 5 / 2 * θ by ring, show 7 * θ = 9 / 2 * θ + 5 / 2 * θ by ring,
    sin_sub, sin_add]
  ring

/-- Stitz-Zeager Exercise 10.4.82: `cos 5θ - cos 6θ = 2 sin(11θ/2) sin(θ/2)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.82, p. 797"]
theorem exer_10_4_82 (θ : ℝ) :
    cos (5 * θ) - cos (6 * θ) = 2 * sin (11 / 2 * θ) * sin (1 / 2 * θ) := by
  rw [show 5 * θ = 11 / 2 * θ - 1 / 2 * θ by ring, show 6 * θ = 11 / 2 * θ + 1 / 2 * θ by ring,
    cos_sub, cos_add]
  ring

/-- Stitz-Zeager Exercise 10.4.83: `sin 9θ - sin(-θ) = 2 cos 4θ sin 5θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.83, p. 797"]
theorem exer_10_4_83 (θ : ℝ) : sin (9 * θ) - sin (-θ) = 2 * cos (4 * θ) * sin (5 * θ) := by
  rw [sin_neg, show 9 * θ = 5 * θ + 4 * θ by ring, show θ = 5 * θ - 4 * θ by ring, sin_add, sin_sub]
  ring_nf

/-- Stitz-Zeager Exercise 10.4.84: `sin θ + cos θ = √2 cos(θ - π/4)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.84, p. 797"]
theorem exer_10_4_84 (θ : ℝ) : sin θ + cos θ = √2 * cos (θ - π / 4) := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [cos_sub, cos_pi_div_four, sin_pi_div_four]
  linear_combination (-(cos θ + sin θ) / 2) * h2

/-- Stitz-Zeager Exercise 10.4.85: `cos θ - sin θ = -√2 sin(θ - π/4)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.85, p. 797"]
theorem exer_10_4_85 (θ : ℝ) : cos θ - sin θ = -√2 * sin (θ - π / 4) := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [sin_sub, cos_pi_div_four, sin_pi_div_four]
  linear_combination ((sin θ - cos θ) / 2) * h2

/-- Stitz-Zeager Exercise 10.4.86: for `θ` in Quadrant I with `sin θ = x`: `cos θ = √(1-x²)`,
`sin 2θ = 2x√(1-x²)`, `cos 2θ = 1 - 2x²`. -/
@[kb "stitzzeager2013" "Exercise 10.4.86, p. 797"]
theorem exer_10_4_86 (θ x : ℝ) (h : sin θ = x) (h1 : 0 < θ) (h2 : θ < π / 2) :
    cos θ = √(1 - x ^ 2) ∧ sin (2 * θ) = 2 * x * √(1 - x ^ 2) ∧ cos (2 * θ) = 1 - 2 * x ^ 2 := by
  have hc := cos_pos_of_mem_Ioo (x := θ) ⟨by linarith [Real.pi_pos], h2⟩
  have hs := sin_sq_add_cos_sq θ
  rw [h] at hs
  have hcv : cos θ = √(1 - x ^ 2) := by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hc.le]; nlinarith
  refine ⟨hcv, ?_, ?_⟩
  · rw [sin_two_mul, h, hcv]
  · rw [cos_two_mul]; nlinarith

/-- Stitz-Zeager Exercise 10.4.90: `sin θ = x/2` with `-π/2 < θ < π/2` gives `cos 2θ = 1 - x²/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.90, p. 797"]
theorem exer_10_4_90 (θ x : ℝ) (h : sin θ = x / 2) : cos (2 * θ) = 1 - x ^ 2 / 2 := by
  have : cos (2 * θ) = 1 - 2 * sin θ ^ 2 := by
    rw [cos_two_mul]; nlinarith [sin_sq_add_cos_sq θ]
  rw [this, h]; ring

/-- Stitz-Zeager Exercise 10.4.91: `tan θ = x/7` with `-π/2 < θ < π/2` gives
`sin 2θ = 14x/(x² + 49)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.91, p. 797"]
theorem exer_10_4_91 (θ x : ℝ) (h : tan θ = x / 7) (h1 : -(π / 2) < θ) (h2 : θ < π / 2) :
    sin (2 * θ) = 14 * x / (x ^ 2 + 49) := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  have hs : sin θ = x / 7 * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc.ne'] at h; linarith
  have h3 := sin_sq_add_cos_sq θ
  rw [hs] at h3
  have hc2 : cos θ ^ 2 = 49 / (x ^ 2 + 49) := by
    have hx : x ^ 2 + 49 ≠ 0 := by positivity
    field_simp; nlinarith
  rw [sin_two_mul, hs]
  have : 2 * (x / 7 * cos θ) * cos θ = 2 * x / 7 * cos θ ^ 2 := by ring
  rw [this, hc2]
  have hx : x ^ 2 + 49 ≠ 0 := by positivity
  field_simp
  ring

/-- Stitz-Zeager Exercise 10.4.93: `cos²θ - sin²θ = 2cos²θ - 1 = 1 - 2sin²θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.93, p. 797"]
theorem exer_10_4_93 (θ : ℝ) :
    cos θ ^ 2 - sin θ ^ 2 = 2 * cos θ ^ 2 - 1 ∧ 2 * cos θ ^ 2 - 1 = 1 - 2 * sin θ ^ 2 := by
  have := sin_sq_add_cos_sq θ
  constructor <;> nlinarith

end UndergradKB.Precalculus.Course
