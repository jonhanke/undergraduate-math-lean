import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.4 (identities: remaining exact values, double and half angles, identities) -/

namespace UndergradKB.Precalculus.Course

open Real

private lemma eqp {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (h : c ^ 2 = a ^ 2) : c = a :=
  (pow_left_inj₀ hc.le ha two_ne_zero).mp h

private lemma eqn {c a : ℝ} (hc : c < 0) (ha : a ≤ 0) (h : c ^ 2 = a ^ 2) : c = a := by
  have := eqp (c := -c) (a := -a) (by linarith) (by linarith) (by simpa using h)
  linarith

private lemma cpi12 : cos (π / 12) = (√6 + √2) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h, cos_sub, cos_pi_div_three, cos_pi_div_four, sin_pi_div_three, sin_pi_div_four, h6]; ring

private lemma spi12 : sin (π / 12) = (√6 - √2) / 4 := by
  have h : π / 12 = π / 3 - π / 4 := by ring
  have h6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h, sin_sub, cos_pi_div_three, cos_pi_div_four, sin_pi_div_three, sin_pi_div_four, h6]; ring

private lemma s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma s5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
private lemma s6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
private lemma r6 : √6 = √3 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num

private lemma sin_neg_Q3 {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) : sin θ < 0 := by
  have h : sin θ = -sin (θ - π) := by rw [sin_sub_pi]; ring
  have := sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
  linarith

private lemma cos_pos_Q4 {θ : ℝ} (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : 0 < cos θ := by
  rw [← cos_sub_two_pi]
  apply cos_pos_of_mem_Ioo; constructor <;> linarith

private lemma cos_of_dbl {x c a : ℝ} (hd : cos (2 * x) = c) (hx : 0 < cos x) (ha : 0 ≤ a)
    (h : a ^ 2 = (1 + c) / 2) : cos x = a :=
  eqp hx ha (by have := cos_two_mul x; rw [hd] at this; nlinarith)

private lemma cos_of_dbl_neg {x c a : ℝ} (hd : cos (2 * x) = c) (hx : cos x < 0) (ha : a ≤ 0)
    (h : a ^ 2 = (1 + c) / 2) : cos x = a :=
  eqn hx ha (by have := cos_two_mul x; rw [hd] at this; nlinarith)

private lemma sin_of_dbl {x c a : ℝ} (hd : cos (2 * x) = c) (hx : 0 < sin x) (ha : 0 ≤ a)
    (h : a ^ 2 = (1 - c) / 2) : sin x = a :=
  eqp hx ha (by
    have h1 := cos_two_mul x
    have h2 := sin_sq_add_cos_sq x
    rw [hd] at h1; nlinarith)

private lemma sin_of_dbl_neg {x c a : ℝ} (hd : cos (2 * x) = c) (hx : sin x < 0) (ha : a ≤ 0)
    (h : a ^ 2 = (1 - c) / 2) : sin x = a :=
  eqn hx ha (by
    have h1 := cos_two_mul x
    have h2 := sin_sq_add_cos_sq x
    rw [hd] at h1; nlinarith)

/-- Stitz-Zeager Exercise 10.4.8: `sec 165° = √2 - √6`. -/
@[kb "stitzzeager2013" "Exercise 10.4.8, p. 794"]
theorem exer_10_4_8 : (cos (165 * π / 180))⁻¹ = √2 - √6 := by
  rw [show 165 * π / 180 = π - π / 12 by ring, cos_pi_sub, cpi12]
  apply inv_eq_of_mul_eq_one_right
  linear_combination (1 / 4) * s6 - (1 / 4) * s2

/-- Stitz-Zeager Exercise 10.4.10: `csc 195° = -(√2 + √6)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.10, p. 794"]
theorem exer_10_4_10 : (sin (195 * π / 180))⁻¹ = -(√2 + √6) := by
  rw [show 195 * π / 180 = π / 12 + π by ring, sin_add_pi, spi12]
  apply inv_eq_of_mul_eq_one_right
  linear_combination (1 / 4) * s6 - (1 / 4) * s2

/-- Stitz-Zeager Exercise 10.4.11: `cot 255° = 2 - √3`. -/
@[kb "stitzzeager2013" "Exercise 10.4.11, p. 794"]
theorem exer_10_4_11 : cos (255 * π / 180) / sin (255 * π / 180) = 2 - √3 := by
  rw [show 255 * π / 180 = (π / 2 - π / 12) + π by ring, cos_add_pi, sin_add_pi,
    cos_pi_div_two_sub, sin_pi_div_two_sub, neg_div_neg_eq, spi12, cpi12]
  have hne : (√6 + √2) / 4 ≠ 0 := by positivity
  rw [div_eq_iff hne, r6]
  linear_combination (√2 / 4) * s3

/-- Stitz-Zeager Exercise 10.4.19: `cot(11π/12) = -(2 + √3)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.19, p. 794"]
theorem exer_10_4_19 : cos (11 * π / 12) / sin (11 * π / 12) = -(2 + √3) := by
  rw [show 11 * π / 12 = π - π / 12 by ring, cos_pi_sub, sin_pi_sub, spi12, cpi12]
  have hne : (√6 - √2) / 4 ≠ 0 := by
    rw [r6]; have : 0 < √2 := by positivity
    have : 1 < √3 := by
      rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have : 0 < √3 * √2 - √2 := by nlinarith
    positivity
  rw [div_eq_iff hne, r6]
  linear_combination (√2 / 4) * s3

/-- Stitz-Zeager Exercise 10.4.23: `csc α = 3` (`0 < α < π/2`) and `tan β = -7` (Quadrant II)
give the six sum and difference values. -/
@[kb "stitzzeager2013" "Exercise 10.4.23, p. 794"]
theorem exer_10_4_23 (α β : ℝ) (hα : (sin α)⁻¹ = 3) (h1 : 0 < α) (h2 : α < π / 2)
    (hβ : tan β = -7) (h3 : π / 2 < β) (h4 : β < π) :
    cos (α + β) = -((4 + 7 * √2) / 30) ∧ sin (α + β) = (28 - √2) / 30 ∧
      tan (α + β) = (63 - 100 * √2) / 41 ∧ cos (α - β) = (-4 + 7 * √2) / 30 ∧
      sin (α - β) = -((28 + √2) / 30) ∧ tan (α - β) = -((63 + 100 * √2) / 41) := by
  have hp2 : 0 < √2 := by positivity
  have hsa : sin α = 1 / 3 := by
    have : sin α ≠ 0 := by intro h; rw [h] at hα; simp at hα
    field_simp at hα; linarith
  have hca : cos α = 2 * √2 / 3 := by
    have hc := cos_pos_of_mem_Ioo ⟨by linarith, h2⟩
    have := sin_sq_add_cos_sq α
    rw [hsa] at this
    exact eqp hc (by positivity) (by rw [div_pow, mul_pow, s2]; nlinarith)
  have hcb0 : cos β < 0 := cos_neg_of_pi_div_two_lt_of_lt h3 (by linarith)
  have hsb : sin β = -7 * cos β := by
    rw [tan_eq_sin_div_cos, div_eq_iff hcb0.ne] at hβ; linarith
  have hcb : cos β = -(√2 / 10) := by
    have := sin_sq_add_cos_sq β
    rw [hsb] at this
    exact eqn hcb0 (by have : 0 ≤ √2 / 10 := by positivity
                       linarith) (by rw [neg_sq, div_pow, s2]; nlinarith)
  have hsb' : sin β = 7 * √2 / 10 := by rw [hsb, hcb]; ring
  have e1 : cos (α + β) = -((4 + 7 * √2) / 30) := by
    rw [cos_add, hsa, hca, hsb', hcb]; linear_combination (-1 / 15) * s2
  have e2 : sin (α + β) = (28 - √2) / 30 := by
    rw [sin_add, hsa, hca, hsb', hcb]; linear_combination (14 / 30) * s2
  have e3 : cos (α - β) = (-4 + 7 * √2) / 30 := by
    rw [cos_sub, hsa, hca, hsb', hcb]; linear_combination (-1 / 15) * s2
  have e4 : sin (α - β) = -((28 + √2) / 30) := by
    rw [sin_sub, hsa, hca, hsb', hcb]; linear_combination (-14 / 30) * s2
  have n1 : (4 + 7 * √2) ≠ 0 := by positivity
  have n2 : (-4 + 7 * √2) ≠ 0 := by
    have : 1 < √2 := by
      rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  refine ⟨e1, e2, ?_, e3, e4, ?_⟩
  · rw [tan_eq_sin_div_cos, e1, e2, div_eq_iff (by simpa using n1)]
    field_simp
    linear_combination (-700) * s2
  · rw [tan_eq_sin_div_cos, e3, e4, div_eq_iff (by simpa using n2)]
    field_simp
    linear_combination 700 * s2

/-- Stitz-Zeager Exercise 10.4.35: ratio of `tan(α+β)` to `tan(α-β)` as a quotient of products. -/
@[kb "stitzzeager2013" "Exercise 10.4.35, p. 795"]
theorem exer_10_4_35 (α β : ℝ) (h1 : cos (α + β) ≠ 0) (h2 : cos (α - β) ≠ 0)
    (h3 : sin (α - β) ≠ 0) :
    tan (α + β) / tan (α - β) =
      (sin α * cos α + sin β * cos β) / (sin α * cos α - sin β * cos β) := by
  have k1 : sin α * cos α - sin β * cos β = cos (α + β) * sin (α - β) := by
    simp only [cos_add, sin_sub]; linear_combination (-(sin α * cos α)) * sin_sq_add_cos_sq β
      + (sin β * cos β) * sin_sq_add_cos_sq α
  have k2 : sin α * cos α + sin β * cos β = sin (α + β) * cos (α - β) := by
    simp only [sin_add, cos_sub]; linear_combination (-(sin α * cos α)) * sin_sq_add_cos_sq β
      - (sin β * cos β) * sin_sq_add_cos_sq α
  rw [k1, k2, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
  field_simp

/-- Stitz-Zeager Exercise 10.4.38: difference quotient of tangent. -/
@[kb "stitzzeager2013" "Exercise 10.4.38, p. 795"]
theorem exer_10_4_38 (t h : ℝ) (hh : h ≠ 0) (hct : cos t ≠ 0) (hch : cos h ≠ 0)
    (hcth : cos (t + h) ≠ 0) :
    (tan (t + h) - tan t) / h =
      tan h / h * ((cos t ^ 2)⁻¹ / (1 - tan t * tan h)) := by
  have e : 1 - tan t * tan h = cos (t + h) / (cos t * cos h) := by
    rw [cos_add, tan_eq_sin_div_cos, tan_eq_sin_div_cos]; field_simp
  rw [e, tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
  field_simp
  have key : sin (t + h) * cos t - cos (t + h) * sin t = sin h := by
    rw [← sin_sub]; congr 1; ring
  linear_combination key

private lemma sqrt23 : √(2 + √3) = (√6 + √2) / 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), r6]
  linear_combination (-1 / 4) * (√2 ^ 2 * s3 + (4 + 2 * √3) * s2)

/-- Stitz-Zeager Exercise 10.4.40: `sin 105° = √(2 + √3)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.40, p. 795"]
theorem exer_10_4_40 : sin (105 * π / 180) = √(2 + √3) / 2 := by
  rw [show 105 * π / 180 = π / 2 + π / 12 by ring, sin_add, sin_pi_div_two, cos_pi_div_two,
    cpi12, sqrt23]; ring

/-- Stitz-Zeager Exercise 10.4.42: `sin 157.5° = √(2 - √2)/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.42, p. 795"]
theorem exer_10_4_42 : sin (157.5 * π / 180) = √(2 - √2) / 2 := by
  rw [show (157.5 : ℝ) * π / 180 = π - π / 8 by ring, sin_pi_sub, sin_pi_div_eight]

private lemma sqrt_ratio : √(2 + √2) = (1 + √2) * √(2 - √2) := by
  have h1 : 0 < 2 - √2 := by
    have : √2 < 2 := by
      rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hy : 0 < √(2 - √2) := Real.sqrt_pos.mpr h1
  have hx : 0 < √(2 + √2) := Real.sqrt_pos.mpr (by positivity)
  refine eqp hx (by positivity) ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt h1.le]
  linear_combination √2 * s2

/-- Stitz-Zeager Exercise 10.4.43: `tan 112.5° = -1 - √2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.43, p. 795"]
theorem exer_10_4_43 : tan (112.5 * π / 180) = -1 - √2 := by
  rw [show (112.5 : ℝ) * π / 180 = π / 2 + π / 8 by ring, tan_eq_sin_div_cos, sin_add, cos_add,
    sin_pi_div_two, cos_pi_div_two, cos_pi_div_eight, sin_pi_div_eight, sqrt_ratio]
  have hy : 0 < √(2 - √2) := Real.sqrt_pos.mpr (by
    have : √2 < 2 := by
      rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith)
  have : (0 * (√(2 - √2) / 2) - 1 * (√(2 - √2) / 2)) ≠ 0 := by
    intro h; apply hy.ne'; linarith
  rw [div_eq_iff (by simpa using this)]
  ring

/-- Stitz-Zeager Exercise 10.4.48: `tan(7π/8) = 1 - √2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.48, p. 795"]
theorem exer_10_4_48 : tan (7 * π / 8) = 1 - √2 := by
  have hy : 0 < √(2 - √2) := Real.sqrt_pos.mpr (by
    have : √2 < 2 := by
      rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith)
  have hx : 0 < √(2 + √2) := Real.sqrt_pos.mpr (by positivity)
  rw [show 7 * π / 8 = π - π / 8 by ring, tan_eq_sin_div_cos, sin_pi_sub, cos_pi_sub,
    cos_pi_div_eight, sin_pi_div_eight, sqrt_ratio]
  have hne : -((1 + √2) * √(2 - √2) / 2) ≠ 0 := by
    have : 0 < (1 + √2) * √(2 - √2) / 2 := by positivity
    linarith
  rw [div_eq_iff hne]
  linear_combination (-(√(2 - √2) / 2)) * s2

private lemma s15 : √15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
private lemma s106 : √106 ^ 2 = 106 := Real.sq_sqrt (by norm_num)
private lemma s26 : √26 ^ 2 = 26 := Real.sq_sqrt (by norm_num)

private lemma hdbl (θ c : ℝ) (h : cos θ = c) : cos (2 * (θ / 2)) = c := by
  rw [mul_div_cancel₀ _ two_ne_zero]; exact h

private lemma halfI {θ : ℝ} (h1 : 0 < θ) (h2 : θ < π) : 0 < sin (θ / 2) ∧ 0 < cos (θ / 2) :=
  ⟨sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos]),
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩⟩

private lemma halfII {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) : 0 < sin (θ / 2) ∧ cos (θ / 2) < 0 :=
  ⟨sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) (by linarith),
    cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)⟩

private lemma half_tan {θ : ℝ} (hs : sin (θ / 2) ≠ 0) (hc : cos (θ / 2) ≠ 0) :
    tan (θ / 2) = (1 - cos θ) / sin θ := by
  have h1 : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
    rw [← sin_two_mul]; congr 1; ring
  have h2 : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    have := cos_two_mul (θ / 2)
    rw [mul_div_cancel₀ _ two_ne_zero] at this
    have h3 := sin_sq_add_cos_sq (θ / 2)
    rw [this]; nlinarith
  rw [tan_eq_sin_div_cos, h1, h2]
  field_simp
  ring

private lemma sinQ1 {θ c s : ℝ} (h : cos θ = c) (h1 : 0 < θ) (h2 : θ < π) (hs : 0 ≤ s)
    (hh : s ^ 2 = 1 - c ^ 2) : sin θ = s :=
  eqp (sin_pos_of_pos_of_lt_pi h1 h2) hs (by have := sin_sq_add_cos_sq θ; rw [h] at this; linarith)

private lemma sinNeg {θ c s : ℝ} (h : cos θ = c) (h1 : π < θ) (h2 : θ < 2 * π) (hs : s ≤ 0)
    (hh : s ^ 2 = 1 - c ^ 2) : sin θ = s :=
  eqn (sin_neg_Q3 h1 h2) hs (by have := sin_sq_add_cos_sq θ; rw [h] at this; linarith)

private lemma cosNeg {θ s c : ℝ} (h : sin θ = s) (h1 : π / 2 < θ) (h2 : θ < 3 * π / 2) (hc : c ≤ 0)
    (hh : c ^ 2 = 1 - s ^ 2) : cos θ = c :=
  eqn (cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)) hc
    (by have := sin_sq_add_cos_sq θ; rw [h] at this; linarith)

/-- Stitz-Zeager Exercise 10.4.50: `cos θ = 28/53`, `0 < θ < π/2`: double and half angle values. -/
@[kb "stitzzeager2013" "Exercise 10.4.50, p. 796"]
theorem exer_10_4_50 (θ : ℝ) (h : cos θ = 28 / 53) (h1 : 0 < θ) (h2 : θ < π / 2) :
    sin (2 * θ) = 2520 / 2809 ∧ cos (2 * θ) = -1241 / 2809 ∧ tan (2 * θ) = -2520 / 1241 ∧
      sin (θ / 2) = 5 * √106 / 106 ∧ cos (θ / 2) = 9 * √106 / 106 ∧ tan (θ / 2) = 5 / 9 := by
  have hs : sin θ = 45 / 53 := sinQ1 h h1 (by linarith [pi_pos]) (by norm_num) (by norm_num)
  obtain ⟨hsp, hcp⟩ := halfI h1 (by linarith [pi_pos])
  have hsh : sin (θ / 2) = 5 * √106 / 106 :=
    sin_of_dbl (hdbl θ _ h) hsp (by positivity) (by rw [div_pow, mul_pow, s106]; norm_num)
  have hch : cos (θ / 2) = 9 * √106 / 106 :=
    cos_of_dbl (hdbl θ _ h) hcp (by positivity) (by rw [div_pow, mul_pow, s106]; norm_num)
  refine ⟨by rw [sin_two_mul, hs, h]; norm_num, by rw [cos_two_mul, h]; norm_num,
    by rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, hs, h]; norm_num, hsh, hch, ?_⟩
  rw [half_tan hsp.ne' hcp.ne', h, hs]; norm_num

/-- Stitz-Zeager Exercise 10.4.52: `csc θ = 4`, `π/2 < θ < π`: double and half angle values. -/
@[kb "stitzzeager2013" "Exercise 10.4.52, p. 796"]
theorem exer_10_4_52 (θ : ℝ) (h : (sin θ)⁻¹ = 4) (h1 : π / 2 < θ) (h2 : θ < π) :
    sin (2 * θ) = -(√15 / 8) ∧ cos (2 * θ) = 7 / 8 ∧ tan (2 * θ) = -(√15 / 7) ∧
      sin (θ / 2) = √(8 + 2 * √15) / 4 ∧ cos (θ / 2) = √(8 - 2 * √15) / 4 ∧
      tan (θ / 2) = 4 + √15 := by
  have hs : sin θ = 1 / 4 := by
    have : sin θ = 4⁻¹ := by rw [← h, inv_inv]
    rw [this]; norm_num
  have hc : cos θ = -(√15 / 4) :=
    cosNeg hs h1 (by linarith) (by have : 0 ≤ √15 / 4 := by positivity
                                   linarith)
      (by rw [neg_sq, div_pow, s15]; norm_num)
  have h15 : √15 ≤ 4 := by nlinarith [s15, Real.sqrt_nonneg 15]
  obtain ⟨hsp, hcp⟩ := halfI (by linarith [pi_pos]) h2
  have hsh : sin (θ / 2) = √(8 + 2 * √15) / 4 :=
    sin_of_dbl (hdbl θ _ hc) hsp (by positivity)
      (by rw [div_pow, Real.sq_sqrt (by positivity)]; ring)
  have hch : cos (θ / 2) = √(8 - 2 * √15) / 4 :=
    cos_of_dbl (hdbl θ _ hc) hcp (by positivity)
      (by rw [div_pow, Real.sq_sqrt (by linarith)]; ring)
  refine ⟨by rw [sin_two_mul, hs, hc]; ring, by rw [cos_two_mul, hc, neg_sq, div_pow, s15]; norm_num,
    ?_, hsh, hch, ?_⟩
  · rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, hs, hc, neg_sq, div_pow, s15]
    have : √15 ≠ 0 := by positivity
    field_simp; norm_num
  · rw [half_tan hsp.ne' hcp.ne', hc, hs]; field_simp; ring

/-- Stitz-Zeager Exercise 10.4.54: `sin θ = -4/5`, `π < θ < 3π/2`: double and half angle values. -/
@[kb "stitzzeager2013" "Exercise 10.4.54, p. 796"]
theorem exer_10_4_54 (θ : ℝ) (h : sin θ = -4 / 5) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin (2 * θ) = 24 / 25 ∧ cos (2 * θ) = -7 / 25 ∧ tan (2 * θ) = -24 / 7 ∧
      sin (θ / 2) = 2 * √5 / 5 ∧ cos (θ / 2) = -(√5 / 5) ∧ tan (θ / 2) = -2 := by
  have hc : cos θ = -3 / 5 := cosNeg h (by linarith [pi_pos]) h2 (by norm_num) (by norm_num)
  obtain ⟨hsp, hcp⟩ := halfII h1 (by linarith [pi_pos])
  have hsh : sin (θ / 2) = 2 * √5 / 5 :=
    sin_of_dbl (hdbl θ _ hc) hsp (by positivity) (by rw [div_pow, mul_pow, s5]; norm_num)
  have hch : cos (θ / 2) = -(√5 / 5) :=
    cos_of_dbl_neg (hdbl θ _ hc) hcp (by have : 0 ≤ √5 / 5 := by positivity
                                         linarith)
      (by rw [neg_sq, div_pow, s5]; norm_num)
  refine ⟨by rw [sin_two_mul, h, hc]; norm_num, by rw [cos_two_mul, hc]; norm_num,
    by rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, h, hc]; norm_num, hsh, hch, ?_⟩
  rw [half_tan hsp.ne' hcp.ne, hc, h]; norm_num

/-- Stitz-Zeager Exercise 10.4.55: `cos θ = 12/13`, `3π/2 < θ < 2π`: double and half angle values. -/
@[kb "stitzzeager2013" "Exercise 10.4.55, p. 796"]
theorem exer_10_4_55 (θ : ℝ) (h : cos θ = 12 / 13) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    sin (2 * θ) = -120 / 169 ∧ cos (2 * θ) = 119 / 169 ∧ tan (2 * θ) = -120 / 119 ∧
      sin (θ / 2) = √26 / 26 ∧ cos (θ / 2) = -(5 * √26 / 26) ∧ tan (θ / 2) = -1 / 5 := by
  have hs : sin θ = -5 / 13 := sinNeg h (by linarith [pi_pos]) h2 (by norm_num) (by norm_num)
  obtain ⟨hsp, hcp⟩ := halfII (by linarith [pi_pos]) h2
  have hsh : sin (θ / 2) = √26 / 26 :=
    sin_of_dbl (hdbl θ _ h) hsp (by positivity) (by rw [div_pow, s26]; norm_num)
  have hch : cos (θ / 2) = -(5 * √26 / 26) :=
    cos_of_dbl_neg (hdbl θ _ h) hcp (by have : 0 ≤ 5 * √26 / 26 := by positivity
                                        linarith)
      (by rw [neg_sq, div_pow, mul_pow, s26]; norm_num)
  refine ⟨by rw [sin_two_mul, hs, h]; norm_num, by rw [cos_two_mul, h]; norm_num,
    by rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, hs, h]; norm_num, hsh, hch, ?_⟩
  rw [half_tan hsp.ne' hcp.ne, h, hs]; norm_num

/-- Stitz-Zeager Exercise 10.4.56: `sin θ = 5/13`, `π/2 < θ < π`: double and half angle values. -/
@[kb "stitzzeager2013" "Exercise 10.4.56, p. 796"]
theorem exer_10_4_56 (θ : ℝ) (h : sin θ = 5 / 13) (h1 : π / 2 < θ) (h2 : θ < π) :
    sin (2 * θ) = -120 / 169 ∧ cos (2 * θ) = 119 / 169 ∧ tan (2 * θ) = -120 / 119 ∧
      sin (θ / 2) = 5 * √26 / 26 ∧ cos (θ / 2) = √26 / 26 ∧ tan (θ / 2) = 5 := by
  have hc : cos θ = -12 / 13 := cosNeg h h1 (by linarith [pi_pos]) (by norm_num) (by norm_num)
  obtain ⟨hsp, hcp⟩ := halfI (by linarith [pi_pos]) h2
  have hsh : sin (θ / 2) = 5 * √26 / 26 :=
    sin_of_dbl (hdbl θ _ hc) hsp (by positivity) (by rw [div_pow, mul_pow, s26]; norm_num)
  have hch : cos (θ / 2) = √26 / 26 :=
    cos_of_dbl (hdbl θ _ hc) hcp (by positivity) (by rw [div_pow, s26]; norm_num)
  refine ⟨by rw [sin_two_mul, h, hc]; norm_num, by rw [cos_two_mul, hc]; norm_num,
    by rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, h, hc]; norm_num, hsh, hch, ?_⟩
  rw [half_tan hsp.ne' hcp.ne', hc, h]; norm_num

/-- Stitz-Zeager Exercise 10.4.57: `sec θ = √5`, `3π/2 < θ < 2π`: double and half angle values. -/
@[kb "stitzzeager2013" "Exercise 10.4.57, p. 796"]
theorem exer_10_4_57 (θ : ℝ) (h : (cos θ)⁻¹ = √5) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    sin (2 * θ) = -4 / 5 ∧ cos (2 * θ) = -3 / 5 ∧ tan (2 * θ) = 4 / 3 ∧
      sin (θ / 2) = √(50 - 10 * √5) / 10 ∧ cos (θ / 2) = -(√(50 + 10 * √5) / 10) ∧
      tan (θ / 2) = (5 - 5 * √5) / 10 := by
  have h5 : √5 ≠ 0 := by positivity
  have hc : cos θ = √5 / 5 := by
    have : cos θ = (√5)⁻¹ := by rw [← h, inv_inv]
    rw [this]; field_simp; linarith [s5]
  have hs : sin θ = -(2 * √5 / 5) :=
    sinNeg hc (by linarith [pi_pos]) h2 (by have : 0 ≤ 2 * √5 / 5 := by positivity
                                            linarith)
      (by rw [neg_sq, div_pow, mul_pow, div_pow, s5]; norm_num)
  have h55 : √5 ≤ 5 := by nlinarith [s5, Real.sqrt_nonneg 5]
  obtain ⟨hsp, hcp⟩ := halfII (by linarith [pi_pos]) h2
  have hsh : sin (θ / 2) = √(50 - 10 * √5) / 10 :=
    sin_of_dbl (hdbl θ _ hc) hsp (by positivity)
      (by rw [div_pow, Real.sq_sqrt (by linarith)]; ring)
  have hch : cos (θ / 2) = -(√(50 + 10 * √5) / 10) :=
    cos_of_dbl_neg (hdbl θ _ hc) hcp (by have : 0 ≤ √(50 + 10 * √5) / 10 := by positivity
                                         linarith)
      (by rw [neg_sq, div_pow, Real.sq_sqrt (by positivity)]; ring)
  refine ⟨by rw [sin_two_mul, hs, hc]; linear_combination (-4 / 25) * s5,
    by rw [cos_two_mul, hc, div_pow, s5]; norm_num, ?_, hsh, hch, ?_⟩
  · rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, hs, hc, div_pow, s5]
    rw [div_eq_div_iff (by norm_num) (by norm_num)]
    linear_combination (-4 / 25 * 5 * 3 / 5) * s5
  · rw [half_tan hsp.ne' hcp.ne, hc, hs]
    field_simp
    nlinarith [s5]

/-- Stitz-Zeager Exercise 10.4.58: `tan θ = -2`, `π/2 < θ < π`: double and half angle values. -/
@[kb "stitzzeager2013" "Exercise 10.4.58, p. 796"]
theorem exer_10_4_58 (θ : ℝ) (h : tan θ = -2) (h1 : π / 2 < θ) (h2 : θ < π) :
    sin (2 * θ) = -4 / 5 ∧ cos (2 * θ) = -3 / 5 ∧ tan (2 * θ) = 4 / 3 ∧
      sin (θ / 2) = √(50 + 10 * √5) / 10 ∧ cos (θ / 2) = √(50 - 10 * √5) / 10 ∧
      tan (θ / 2) = (5 + 5 * √5) / 10 := by
  have h5 : √5 ≠ 0 := by positivity
  have hcn : cos θ < 0 := cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [pi_pos])
  have hsc : sin θ = -2 * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hcn.ne] at h; linarith
  have hc : cos θ = -(√5 / 5) := by
    have := sin_sq_add_cos_sq θ
    rw [hsc] at this
    have hp : 0 ≤ √5 / 5 := by positivity
    exact eqn hcn (by linarith) (by rw [neg_sq, div_pow, s5]; nlinarith)
  have hs : sin θ = 2 * √5 / 5 := by rw [hsc, hc]; ring
  have h55 : √5 ≤ 5 := by nlinarith [s5, Real.sqrt_nonneg 5]
  obtain ⟨hsp, hcp⟩ := halfI (by linarith [pi_pos]) h2
  have hsh : sin (θ / 2) = √(50 + 10 * √5) / 10 :=
    sin_of_dbl (hdbl θ _ hc) hsp (by positivity)
      (by rw [div_pow, Real.sq_sqrt (by positivity)]; ring)
  have hch : cos (θ / 2) = √(50 - 10 * √5) / 10 :=
    cos_of_dbl (hdbl θ _ hc) hcp (by positivity)
      (by rw [div_pow, Real.sq_sqrt (by linarith)]; ring)
  refine ⟨by rw [sin_two_mul, hs, hc]; linear_combination (-4 / 25) * s5,
    by rw [cos_two_mul, hc, neg_sq, div_pow, s5]; norm_num, ?_, hsh, hch, ?_⟩
  · rw [tan_eq_sin_div_cos, sin_two_mul, cos_two_mul, hs, hc, neg_sq, div_pow, s5]
    rw [div_eq_div_iff (by norm_num) (by norm_num)]
    linear_combination (-4 / 25 * 5 * 3 / 5) * s5
  · rw [half_tan hsp.ne' hcp.ne', hc, hs]
    field_simp
    nlinarith [s5]

/-- Stitz-Zeager Exercise 10.4.61: `tan 2θ = 1/(1 - tan θ) - 1/(1 + tan θ)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.61, p. 796"]
theorem exer_10_4_61 (θ : ℝ) (h1 : 1 - tan θ ≠ 0) (h2 : 1 + tan θ ≠ 0) :
    tan (2 * θ) = 1 / (1 - tan θ) - 1 / (1 + tan θ) := by
  have h3 : 1 - tan θ ^ 2 ≠ 0 := by
    rw [show 1 - tan θ ^ 2 = (1 - tan θ) * (1 + tan θ) by ring]; exact mul_ne_zero h1 h2
  rw [tan_two_mul]
  field_simp
  ring

/-- Stitz-Zeager Exercise 10.4.67: `32 sin²θ cos⁴θ = 2 + cos 2θ - 2 cos 4θ - cos 6θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.67, p. 796"]
theorem exer_10_4_67 (θ : ℝ) :
    32 * sin θ ^ 2 * cos θ ^ 4 = 2 + cos (2 * θ) - 2 * cos (4 * θ) - cos (6 * θ) := by
  have h4 : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, cos_two_mul]
  have h6 : cos (6 * θ) = 4 * cos (2 * θ) ^ 3 - 3 * cos (2 * θ) := by
    rw [show 6 * θ = 3 * (2 * θ) by ring, cos_three_mul]
  rw [h4, h6, cos_two_mul, sin_sq]
  ring

/-- Stitz-Zeager Exercise 10.4.68: `32 sin⁴θ cos²θ = 2 - cos 2θ - 2 cos 4θ + cos 6θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.68, p. 796"]
theorem exer_10_4_68 (θ : ℝ) :
    32 * sin θ ^ 4 * cos θ ^ 2 = 2 - cos (2 * θ) - 2 * cos (4 * θ) + cos (6 * θ) := by
  have h4 : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, cos_two_mul]
  have h6 : cos (6 * θ) = 4 * cos (2 * θ) ^ 3 - 3 * cos (2 * θ) := by
    rw [show 6 * θ = 3 * (2 * θ) by ring, cos_three_mul]
  rw [h4, h6, cos_two_mul, show sin θ ^ 4 = (sin θ ^ 2) ^ 2 by ring, sin_sq]
  ring

/-- Stitz-Zeager Exercise 10.4.71: `sec 2θ = cos θ/(cos θ + sin θ) + sin θ/(cos θ - sin θ)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.71, p. 796"]
theorem exer_10_4_71 (θ : ℝ) (h1 : cos θ - sin θ ≠ 0) (h2 : cos θ + sin θ ≠ 0) :
    (cos (2 * θ))⁻¹ = cos θ / (cos θ + sin θ) + sin θ / (cos θ - sin θ) := by
  have e : cos (2 * θ) = (cos θ - sin θ) * (cos θ + sin θ) := by
    rw [cos_two_mul]; linear_combination sin_sq_add_cos_sq θ
  rw [e]
  field_simp
  linear_combination (-1 : ℝ) * sin_sq_add_cos_sq θ

/-- Stitz-Zeager Exercise 10.4.88: with `θ` in Quadrant I and `tan θ = x`, the values of `cos θ`,
`sin θ`, `sin 2θ`, `cos 2θ` in terms of `x`. -/
@[kb "stitzzeager2013" "Exercise 10.4.88, p. 797"]
theorem exer_10_4_88 (θ x : ℝ) (h : tan θ = x) (h1 : 0 < θ) (h2 : θ < π / 2) :
    cos θ = 1 / √(x ^ 2 + 1) ∧ sin θ = x / √(x ^ 2 + 1) ∧ sin (2 * θ) = 2 * x / (x ^ 2 + 1) ∧
      cos (2 * θ) = (1 - x ^ 2) / (x ^ 2 + 1) := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h2⟩
  have hs : sin θ = x * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc.ne'] at h; exact h
  have hq : (x ^ 2 + 1) * cos θ ^ 2 = 1 := by
    have := sin_sq_add_cos_sq θ
    rw [hs] at this; linarith
  have hpos : 0 < x ^ 2 + 1 := by positivity
  have hr : 0 < √(x ^ 2 + 1) := Real.sqrt_pos.mpr hpos
  have hcc : cos θ = 1 / √(x ^ 2 + 1) := by
    refine eqp hc (by positivity) ?_
    rw [div_pow, Real.sq_sqrt hpos.le]
    field_simp; linarith
  have hc2 : cos θ ^ 2 = 1 / (x ^ 2 + 1) := by
    field_simp; linarith
  refine ⟨hcc, by rw [hs, hcc]; ring, ?_, ?_⟩
  · rw [sin_two_mul, hs]
    have : 2 * (x * cos θ) * cos θ = 2 * x * cos θ ^ 2 := by ring
    rw [this, hc2]; field_simp
  · rw [cos_two_mul, hc2]; field_simp; ring

/-- Stitz-Zeager Exercise 10.4.92: `sec θ = x/4`, `0 < θ < π/2`: `ln|sec θ + tan θ| = ln((x + √(x²-16))/4)`. -/
@[kb "stitzzeager2013" "Exercise 10.4.92, p. 797"]
theorem exer_10_4_92 (θ x : ℝ) (h : (cos θ)⁻¹ = x / 4) (h1 : 0 < θ) (h2 : θ < π / 2) :
    Real.log |(cos θ)⁻¹ + tan θ| = Real.log ((x + √(x ^ 2 - 16)) / 4) := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h2⟩
  have ht : 0 < tan θ := tan_pos_of_pos_of_lt_pi_div_two h1 h2
  have hx : 0 < x := by
    have : 0 < (cos θ)⁻¹ := inv_pos.mpr hc
    linarith
  have hsq : tan θ ^ 2 = x ^ 2 / 16 - 1 := by
    have h5 : cos θ ^ 2 ≠ 0 := by positivity
    have h6 : (cos θ ^ 2)⁻¹ = x ^ 2 / 16 := by rw [← inv_pow, h]; ring
    rw [tan_eq_sin_div_cos, div_pow, sin_sq, ← h6]
    field_simp
  have hnn : 0 ≤ x ^ 2 - 16 := by nlinarith [sq_nonneg (tan θ)]
  have htt : tan θ = √(x ^ 2 - 16) / 4 := by
    refine eqp ht (by positivity) ?_
    rw [div_pow, Real.sq_sqrt hnn, hsq]; ring
  rw [h, htt, abs_of_pos (by positivity)]
  congr 1; ring

/-- Stitz-Zeager Exercise 10.4.94: for `cos θ = -1/5` in Quadrant III, the sign of `sin(θ/2)`
depends on the coterminal range: negative for `3π < θ < 7π/2`, positive for `π < θ < 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.4.94, p. 797"]
theorem exer_10_4_94 (θ : ℝ) (h : cos θ = -1 / 5) :
    (3 * π < θ → θ < 7 * π / 2 → sin (θ / 2) = -(√15 / 5)) ∧
      (π < θ → θ < 3 * π / 2 → sin (θ / 2) = √15 / 5) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · exact sin_of_dbl_neg (hdbl θ _ h) (sin_neg_Q3 (by linarith) (by linarith [pi_pos]))
      (by have : 0 ≤ √15 / 5 := by positivity
          linarith) (by rw [neg_sq, div_pow, s15]; norm_num)
  · exact sin_of_dbl (hdbl θ _ h) (sin_pos_of_pos_of_lt_pi (by linarith [pi_pos])
      (by linarith)) (by positivity) (by rw [div_pow, s15]; norm_num)

/-- Stitz-Zeager Exercise 10.4.95: `√(2 + √3)/2 = (√6 + √2)/4`. -/
@[kb "stitzzeager2013" "Exercise 10.4.95, p. 798"]
theorem exer_10_4_95 : √(2 + √3) / 2 = (√6 + √2) / 4 := by
  rw [sqrt23]; ring

/-- Stitz-Zeager Exercise 10.4.98: even/odd identities for tangent, secant, cosecant, cotangent. -/
@[kb "stitzzeager2013" "Exercise 10.4.98, p. 798"]
theorem exer_10_4_98 (θ : ℝ) :
    tan (-θ) = -tan θ ∧ (cos (-θ))⁻¹ = (cos θ)⁻¹ ∧ (sin (-θ))⁻¹ = -(sin θ)⁻¹ ∧
      cos (-θ) / sin (-θ) = -(cos θ / sin θ) := by
  refine ⟨tan_neg θ, by rw [cos_neg], by rw [sin_neg, inv_neg], by rw [cos_neg, sin_neg, div_neg]⟩

/-- Stitz-Zeager Exercise 10.4.99: cofunction identities for tangent, secant, cosecant, cotangent. -/
@[kb "stitzzeager2013" "Exercise 10.4.99, p. 798"]
theorem exer_10_4_99 (θ : ℝ) :
    tan (π / 2 - θ) = cos θ / sin θ ∧ (cos (π / 2 - θ))⁻¹ = (sin θ)⁻¹ ∧
      (sin (π / 2 - θ))⁻¹ = (cos θ)⁻¹ ∧ cos (π / 2 - θ) / sin (π / 2 - θ) = tan θ := by
  refine ⟨by rw [tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub],
    by rw [cos_pi_div_two_sub], by rw [sin_pi_div_two_sub],
    by rw [cos_pi_div_two_sub, sin_pi_div_two_sub, tan_eq_sin_div_cos]⟩

/-- Stitz-Zeager Exercise 10.4.100: difference identities for sine and tangent. -/
@[kb "stitzzeager2013" "Exercise 10.4.100, p. 798"]
theorem exer_10_4_100 (α β : ℝ) (ha : cos α ≠ 0) (hb : cos β ≠ 0) (hd : 1 + tan α * tan β ≠ 0) :
    sin (α - β) = sin α * cos β - cos α * sin β ∧
      tan (α - β) = (tan α - tan β) / (1 + tan α * tan β) := by
  refine ⟨sin_sub α β, ?_⟩
  have e : 1 + tan α * tan β = (cos α * cos β + sin α * sin β) / (cos α * cos β) := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]; field_simp
  have hn : cos α * cos β + sin α * sin β ≠ 0 := by
    intro h0; apply hd; rw [e, h0]; simp
  have hd' : 1 + sin α / cos α * (sin β / cos β) ≠ 0 := by
    rwa [tan_eq_sin_div_cos, tan_eq_sin_div_cos] at hd
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos, sin_sub, cos_sub,
    div_eq_div_iff hn hd']
  field_simp

/-- Stitz-Zeager Exercise 10.4.101: product-to-sum identities. -/
@[kb "stitzzeager2013" "Exercise 10.4.101, p. 798"]
theorem exer_10_4_101 (α β : ℝ) :
    cos α * cos β = (cos (α - β) + cos (α + β)) / 2 ∧
      sin α * sin β = (cos (α - β) - cos (α + β)) / 2 ∧
      sin α * cos β = (sin (α + β) + sin (α - β)) / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [cos_add, cos_sub, sin_add, sin_sub] <;> ring

/-- Stitz-Zeager Exercise 10.4.102: sum-to-product identities. -/
@[kb "stitzzeager2013" "Exercise 10.4.102, p. 798"]
theorem exer_10_4_102 (α β : ℝ) :
    cos α + cos β = 2 * cos ((α + β) / 2) * cos ((α - β) / 2) ∧
      cos α - cos β = -2 * sin ((α + β) / 2) * sin ((α - β) / 2) ∧
      sin α + sin β = 2 * sin ((α + β) / 2) * cos ((α - β) / 2) ∧
      sin α - sin β = 2 * cos ((α + β) / 2) * sin ((α - β) / 2) := by
  have e1 : α = (α + β) / 2 + (α - β) / 2 := by ring
  have e2 : β = (α + β) / 2 - (α - β) / 2 := by ring
  generalize (α + β) / 2 = u at e1 e2 ⊢
  generalize (α - β) / 2 = v at e1 e2 ⊢
  subst e1 e2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cos_add, cos_sub, sin_add, sin_sub] <;> ring

end UndergradKB.Precalculus.Course
