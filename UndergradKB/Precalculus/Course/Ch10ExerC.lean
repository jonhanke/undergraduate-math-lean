import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.3

Reciprocal functions are written `(cos θ)⁻¹`, `(sin θ)⁻¹`, `cos θ / sin θ`. "Undefined" is stated as
the vanishing of the denominator. -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 10.3 -/

private lemma eq_of_pos_sq' {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (h : c ^ 2 = a ^ 2) : c = a :=
  (pow_left_inj₀ hc.le ha two_ne_zero).mp h

private lemma eq_of_neg_sq' {c a : ℝ} (hc : c < 0) (ha : a ≤ 0) (h : c ^ 2 = a ^ 2) : c = a := by
  have := eq_of_pos_sq' (c := -c) (a := -a) (by linarith) (by linarith) (by simpa using h)
  linarith

private lemma cos_pos_Q4' {θ : ℝ} (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : 0 < cos θ := by
  rw [← cos_sub_two_pi]
  apply cos_pos_of_mem_Ioo; constructor <;> linarith

private lemma sin_neg_Q34' {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) : sin θ < 0 := by
  have h : sin θ = -sin (θ - π) := by rw [sin_sub_pi]; ring
  have := sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
  linarith

/-- tangent equations with nonzero right side: `tan θ = tan a` exactly when `θ = a + πk`. -/
private lemma tan_iff {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    tan θ = tan a ↔ ∃ k : ℤ, θ = a + π * k := by
  constructor
  · intro h
    have ha : tan a ≠ 0 := by rw [tan_eq_sin_div_cos]; exact div_ne_zero hs hc
    have hθ : cos θ ≠ 0 := fun h0 => ha (h ▸ tan_eq_zero_of_cos_eq_zero h0)
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hθ hc] at h
    have : sin (θ - a) = 0 := by rw [sin_sub]; linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp this
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [mul_comm]; exact tan_add_int_mul_pi a k

/-- cotangent equations: `cos θ / sin θ = cos a / sin a` exactly when `θ = a + πk`. -/
private lemma cot_iff {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    cos θ / sin θ = cos a / sin a ↔ ∃ k : ℤ, θ = a + π * k := by
  have e : ∀ x : ℝ, cos x / sin x = (tan x)⁻¹ := fun x => by rw [tan_eq_sin_div_cos, inv_div]
  rw [e, e, inv_inj]
  exact tan_iff hc hs

/-- Stitz-Zeager Exercise 10.3.1: `tan(π/4) = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.1, p. 771"]
theorem exer_10_3_1 : tan (π / 4) = 1 := tan_pi_div_four

/-- Stitz-Zeager Exercise 10.3.2: `sec(π/6) = 2√3/3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.2, p. 771"]
theorem exer_10_3_2 : (cos (π / 6))⁻¹ = 2 * √3 / 3 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  rw [cos_pi_div_six]; field_simp; nlinarith [h3]

/-- Stitz-Zeager Exercise 10.3.3: `csc(5π/6) = 2`. -/
@[kb "stitzzeager2013" "Exercise 10.3.3, p. 771"]
theorem exer_10_3_3 : (sin (5 * π / 6))⁻¹ = 2 := by
  have h : 5 * π / 6 = π - π / 6 := by ring
  rw [h, sin_pi_sub, sin_pi_div_six]; norm_num

/-- Stitz-Zeager Exercise 10.3.4: `cot(4π/3) = √3/3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.4, p. 771"]
theorem exer_10_3_4 : cos (4 * π / 3) / sin (4 * π / 3) = √3 / 3 := by
  have h : 4 * π / 3 = π / 3 + π := by ring
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_three, sin_pi_div_three]
  field_simp; nlinarith [h3]

/-- Stitz-Zeager Exercise 10.3.5: `tan(-11π/6) = √3/3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.5, p. 771"]
theorem exer_10_3_5 : tan (-(11 * π / 6)) = √3 / 3 := by
  have h : -(11 * π / 6) = π / 6 + ((-2 : ℤ) : ℝ) * π := by push_cast; ring
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  rw [h, tan_add_int_mul_pi, tan_pi_div_six]
  field_simp; nlinarith [h3]

/-- Stitz-Zeager Exercise 10.3.6: `sec(-3π/2)` is undefined because `cos(-3π/2) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.3.6, p. 771"]
theorem exer_10_3_6 : cos (-(3 * π / 2)) = 0 :=
  cos_eq_zero_iff.mpr ⟨-2, by push_cast; ring⟩

/-- Stitz-Zeager Exercise 10.3.7: `csc(-π/3) = -2√3/3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.7, p. 771"]
theorem exer_10_3_7 : (sin (-(π / 3)))⁻¹ = -(2 * √3 / 3) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  rw [sin_neg, sin_pi_div_three]; field_simp; nlinarith [h3]

/-- Stitz-Zeager Exercise 10.3.8: `cot(13π/2) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.3.8, p. 771"]
theorem exer_10_3_8 : cos (13 * π / 2) / sin (13 * π / 2) = 0 := by
  have : cos (13 * π / 2) = 0 := cos_eq_zero_iff.mpr ⟨6, by push_cast; ring⟩
  rw [this]; simp

/-- Stitz-Zeager Exercise 10.3.9: `tan(117π) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.3.9, p. 771"]
theorem exer_10_3_9 : tan (117 * π) = 0 := by
  have h : 117 * π = 0 + ((117 : ℤ) : ℝ) * π := by push_cast; ring
  rw [h, tan_add_int_mul_pi, tan_zero]

/-- Stitz-Zeager Exercise 10.3.10: `sec(-5π/3) = 2`. -/
@[kb "stitzzeager2013" "Exercise 10.3.10, p. 771"]
theorem exer_10_3_10 : (cos (-(5 * π / 3)))⁻¹ = 2 := by
  have h : -(5 * π / 3) = π / 3 + ((-1 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [h, cos_add_int_mul_two_pi, cos_pi_div_three]; norm_num

/-- Stitz-Zeager Exercise 10.3.11: `csc(3π)` is undefined because `sin(3π) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.3.11, p. 771"]
theorem exer_10_3_11 : sin (3 * π) = 0 :=
  sin_eq_zero_iff.mpr ⟨3, by push_cast; ring⟩

/-- Stitz-Zeager Exercise 10.3.12: `cot(-5π)` is undefined because `sin(-5π) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.3.12, p. 771"]
theorem exer_10_3_12 : sin (-(5 * π)) = 0 :=
  sin_eq_zero_iff.mpr ⟨-5, by push_cast; ring⟩

/-- Stitz-Zeager Exercise 10.3.13: `tan(31π/2)` is undefined because `cos(31π/2) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.3.13, p. 771"]
theorem exer_10_3_13 : cos (31 * π / 2) = 0 :=
  cos_eq_zero_iff.mpr ⟨15, by push_cast; ring⟩

/-- Stitz-Zeager Exercise 10.3.14: `sec(π/4) = √2`. -/
@[kb "stitzzeager2013" "Exercise 10.3.14, p. 771"]
theorem exer_10_3_14 : (cos (π / 4))⁻¹ = √2 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  rw [cos_pi_div_four]; field_simp; nlinarith [h2]

/-- Stitz-Zeager Exercise 10.3.17: `tan(2π/3) = -√3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.17, p. 771"]
theorem exer_10_3_17 : tan (2 * π / 3) = -√3 := by
  have h : 2 * π / 3 = π - π / 3 := by ring
  rw [h, tan_eq_sin_div_cos, sin_pi_sub, cos_pi_sub, sin_pi_div_three, cos_pi_div_three]
  field_simp

/-- Stitz-Zeager Exercise 10.3.18: `sec(-7π) = -1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.18, p. 771"]
theorem exer_10_3_18 : (cos (-(7 * π)))⁻¹ = -1 := by
  have h : -(7 * π) = π + ((-4 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [h, cos_add_int_mul_two_pi, cos_pi]; norm_num

/-- Stitz-Zeager Exercise 10.3.20: `cot(3π/4) = -1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.20, p. 771"]
theorem exer_10_3_20 : cos (3 * π / 4) / sin (3 * π / 4) = -1 := by
  have h : 3 * π / 4 = π - π / 4 := by ring
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  rw [h, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four]
  field_simp

/-- Stitz-Zeager Exercise 10.3.21: `sin θ = 3/5` in Quadrant II gives `cos θ = -4/5`,
`tan θ = -3/4`, `csc θ = 5/3`, `sec θ = -5/4`, `cot θ = -4/3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.21, p. 771"]
theorem exer_10_3_21 (θ : ℝ) (h : sin θ = 3 / 5) (h1 : π / 2 < θ) (h2 : θ < π) :
    cos θ = -4 / 5 ∧ tan θ = -3 / 4 ∧ (sin θ)⁻¹ = 5 / 3 ∧ (cos θ)⁻¹ = -5 / 4 ∧
      cos θ / sin θ = -4 / 3 := by
  have hc := cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [Real.pi_pos])
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have hv : cos θ = -4 / 5 := eq_of_neg_sq' hc (by norm_num) (by nlinarith)
  refine ⟨hv, ?_, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, h, hv]; norm_num
  · rw [h]; norm_num
  · rw [hv]; norm_num
  · rw [h, hv]; norm_num

/-- Stitz-Zeager Exercise 10.3.24: `sec θ = 7` in Quadrant IV gives `cos θ = 1/7`,
`sin θ = -4√3/7`, `tan θ = -4√3`. -/
@[kb "stitzzeager2013" "Exercise 10.3.24, p. 771"]
theorem exer_10_3_24 (θ : ℝ) (h : (cos θ)⁻¹ = 7) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    cos θ = 1 / 7 ∧ sin θ = -(4 * √3 / 7) ∧ tan θ = -(4 * √3) := by
  have hc : cos θ = 1 / 7 := by
    rw [inv_eq_iff_eq_inv] at h; rw [h]; norm_num
  have hs := sin_neg_Q34' (by linarith [Real.pi_pos]) h2
  have := sin_sq_add_cos_sq θ
  rw [hc] at this
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsv : sin θ = -(4 * √3 / 7) :=
    eq_of_neg_sq' hs (by have : 0 ≤ √3 := Real.sqrt_nonneg 3; apply neg_nonpos.mpr; positivity)
      (by rw [neg_sq, div_pow, mul_pow, h3]; nlinarith)
  refine ⟨hc, hsv, ?_⟩
  rw [tan_eq_sin_div_cos, hsv, hc]; field_simp

/-- Stitz-Zeager Exercise 10.3.27: `tan θ = -2` in Quadrant IV gives `cos θ = √5/5` and
`sin θ = -2√5/5`. -/
@[kb "stitzzeager2013" "Exercise 10.3.27, p. 771"]
theorem exer_10_3_27 (θ : ℝ) (h : tan θ = -2) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    cos θ = √5 / 5 ∧ sin θ = -(2 * √5 / 5) ∧ (sin θ)⁻¹ = -(√5 / 2) ∧ (cos θ)⁻¹ = √5 ∧
      cos θ / sin θ = -1 / 2 := by
  have hc := cos_pos_Q4' h1 h2
  have hs : sin θ = -2 * cos θ := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc.ne'] at h; linarith
  have := sin_sq_add_cos_sq θ
  rw [hs] at this
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √5 := by positivity
  have hcv : cos θ = √5 / 5 := eq_of_pos_sq' hc (by positivity) (by rw [div_pow, h5]; nlinarith)
  have hsv : sin θ = -(2 * √5 / 5) := by rw [hs, hcv]; ring
  refine ⟨hcv, hsv, ?_, ?_, ?_⟩
  · rw [hsv]; field_simp; nlinarith [h5]
  · rw [hcv]; field_simp; nlinarith [h5]
  · rw [hsv, hcv]; field_simp

/-- Stitz-Zeager Exercise 10.3.30: `cos θ = 1/3` in Quadrant I gives `sin θ = 2√2/3`,
`tan θ = 2√2`, `csc θ = 3√2/4`, `sec θ = 3`, `cot θ = √2/4`. -/
@[kb "stitzzeager2013" "Exercise 10.3.30, p. 771"]
theorem exer_10_3_30 (θ : ℝ) (h : cos θ = 1 / 3) (h1 : 0 < θ) (h2 : θ < π / 2) :
    sin θ = 2 * √2 / 3 ∧ tan θ = 2 * √2 ∧ (sin θ)⁻¹ = 3 * √2 / 4 ∧ (cos θ)⁻¹ = 3 ∧
      cos θ / sin θ = √2 / 4 := by
  have hs := sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h2' : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  have hsv : sin θ = 2 * √2 / 3 :=
    eq_of_pos_sq' hs (by positivity) (by rw [div_pow, mul_pow, h2']; nlinarith)
  refine ⟨hsv, ?_, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, h]; field_simp
  · rw [hsv]; field_simp; nlinarith [h2']
  · rw [h]; norm_num
  · rw [hsv, h]; field_simp; nlinarith [h2']

/-- Stitz-Zeager Exercise 10.3.31: `cot θ = 2` with `0 < θ < π/2` gives `sin θ = √5/5`,
`cos θ = 2√5/5`, `tan θ = 1/2`, `csc θ = √5`, `sec θ = √5/2`. -/
@[kb "stitzzeager2013" "Exercise 10.3.31, p. 771"]
theorem exer_10_3_31 (θ : ℝ) (h : cos θ / sin θ = 2) (h1 : 0 < θ) (h2 : θ < π / 2) :
    sin θ = √5 / 5 ∧ cos θ = 2 * √5 / 5 ∧ tan θ = 1 / 2 ∧ (sin θ)⁻¹ = √5 ∧
      (cos θ)⁻¹ = √5 / 2 := by
  have hs := sin_pos_of_pos_of_lt_pi h1 (by linarith [Real.pi_pos])
  have hcv : cos θ = 2 * sin θ := by
    rw [div_eq_iff hs.ne'] at h; linarith
  have := sin_sq_add_cos_sq θ
  rw [hcv] at this
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √5 := by positivity
  have hsv : sin θ = √5 / 5 := eq_of_pos_sq' hs (by positivity) (by rw [div_pow, h5]; nlinarith)
  have hc2 : cos θ = 2 * √5 / 5 := by rw [hcv, hsv]; ring
  refine ⟨hsv, hc2, ?_, ?_, ?_⟩
  · rw [tan_eq_sin_div_cos, hsv, hc2]; field_simp
  · rw [hsv]; field_simp; nlinarith [h5]
  · rw [hc2]; field_simp; nlinarith [h5]

/-- Stitz-Zeager Exercise 10.3.43: `tan θ = √3` exactly when `θ = π/3 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.43, p. 772"]
theorem exer_10_3_43 (θ : ℝ) : tan θ = √3 ↔ ∃ k : ℤ, θ = π / 3 + π * k := by
  rw [← tan_pi_div_three]
  exact tan_iff (by rw [cos_pi_div_three]; norm_num) (by rw [sin_pi_div_three]; positivity)

/-- Stitz-Zeager Exercise 10.3.44: `sec θ = 2` exactly when `θ = π/3 + 2πk` or `θ = 5π/3 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.44, p. 772"]
theorem exer_10_3_44 (θ : ℝ) :
    (cos θ)⁻¹ = 2 ↔ ∃ k : ℤ, θ = π / 3 + 2 * π * k ∨ θ = 5 * π / 3 + 2 * π * k := by
  have e : (cos θ)⁻¹ = 2 ↔ cos (π / 3) = cos θ := by
    rw [inv_eq_iff_eq_inv, cos_pi_div_three]; norm_num; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.3.45: `csc θ = -1` exactly when `θ = 3π/2 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.45, p. 772"]
theorem exer_10_3_45 (θ : ℝ) : (sin θ)⁻¹ = -1 ↔ ∃ k : ℤ, θ = 3 * π / 2 + 2 * π * k := by
  rw [inv_eq_iff_eq_inv, inv_neg, inv_one, sin_eq_neg_one_iff]
  constructor
  · rintro ⟨k, h⟩; exact ⟨k - 1, by push_cast; linarith⟩
  · rintro ⟨k, h⟩; exact ⟨k + 1, by push_cast; linarith⟩

/-- Stitz-Zeager Exercise 10.3.47: `tan θ = 0` (with `cos θ ≠ 0`, so `tan θ` is defined) exactly
when `θ = πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.47, p. 772"]
theorem exer_10_3_47 (θ : ℝ) : (cos θ ≠ 0 ∧ tan θ = 0) ↔ ∃ k : ℤ, θ = π * k := by
  constructor
  · rintro ⟨hc, h⟩
    rw [tan_eq_sin_div_cos, div_eq_zero_iff] at h
    rcases h with h | h
    · obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h
      exact ⟨n, by linarith⟩
    · exact absurd h hc
  · rintro ⟨k, rfl⟩
    have hs : sin (π * k) = 0 := sin_eq_zero_iff.mpr ⟨k, by ring⟩
    have hc : cos (π * k) ≠ 0 := by
      intro h0
      have := sin_sq_add_cos_sq (π * k)
      rw [hs, h0] at this; norm_num at this
    exact ⟨hc, by rw [tan_eq_sin_div_cos, hs, zero_div]⟩

/-- Stitz-Zeager Exercise 10.3.48: `sec θ = 1` exactly when `θ = 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.48, p. 772"]
theorem exer_10_3_48 (θ : ℝ) : (cos θ)⁻¹ = 1 ↔ ∃ k : ℤ, θ = 2 * π * k := by
  rw [inv_eq_one, cos_eq_one_iff]
  constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.3.49: `csc θ = 2` exactly when `θ = π/6 + 2πk` or `θ = 5π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.49, p. 772"]
theorem exer_10_3_49 (θ : ℝ) :
    (sin θ)⁻¹ = 2 ↔ ∃ k : ℤ, θ = π / 6 + 2 * π * k ∨ θ = 5 * π / 6 + 2 * π * k := by
  have e : (sin θ)⁻¹ = 2 ↔ sin (π / 6) = sin θ := by
    rw [inv_eq_iff_eq_inv, sin_pi_div_six]; norm_num; exact eq_comm
  rw [e, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩

/-- Stitz-Zeager Exercise 10.3.50: `cot θ = 0` (with `sin θ ≠ 0`, so `cot θ` is defined) exactly when
`θ = π/2 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.50, p. 772"]
theorem exer_10_3_50 (θ : ℝ) : (sin θ ≠ 0 ∧ cos θ / sin θ = 0) ↔ ∃ k : ℤ, θ = π / 2 + π * k := by
  constructor
  · rintro ⟨hs, h⟩
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp h
      exact ⟨k, by rw [hk]; ring⟩
    · exact absurd h hs
  · rintro ⟨k, h⟩
    have hc : cos θ = 0 := cos_eq_zero_iff.mpr ⟨k, by rw [h]; ring⟩
    refine ⟨?_, by rw [hc, zero_div]⟩
    intro h0
    have := sin_sq_add_cos_sq θ
    rw [hc, h0] at this; norm_num at this

/-- Stitz-Zeager Exercise 10.3.51: `tan θ = -1` exactly when `θ = 3π/4 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.51, p. 772"]
theorem exer_10_3_51 (θ : ℝ) : tan θ = -1 ↔ ∃ k : ℤ, θ = 3 * π / 4 + π * k := by
  have h : 3 * π / 4 = π - π / 4 := by ring
  have hp : 0 < √2 := by positivity
  have hc : cos (3 * π / 4) ≠ 0 := by rw [h, cos_pi_sub, cos_pi_div_four]; simp
  have hs : sin (3 * π / 4) ≠ 0 := by rw [h, sin_pi_sub, sin_pi_div_four]; positivity
  have ht : tan (3 * π / 4) = -1 := by
    rw [h, tan_eq_sin_div_cos, sin_pi_sub, cos_pi_sub, sin_pi_div_four, cos_pi_div_four]
    field_simp
  rw [← ht]; exact tan_iff hc hs

/-- Stitz-Zeager Exercise 10.3.52: `sec θ = 0` never happens (for `θ` where `sec θ` is defined). -/
@[kb "stitzzeager2013" "Exercise 10.3.52, p. 772"]
theorem exer_10_3_52 : ¬ ∃ θ : ℝ, cos θ ≠ 0 ∧ (cos θ)⁻¹ = 0 := by
  rintro ⟨θ, hc, h⟩
  exact hc (inv_eq_zero.mp h)

/-- Stitz-Zeager Exercise 10.3.54: `sec θ = -1` exactly when `θ = (2k+1)π`. -/
@[kb "stitzzeager2013" "Exercise 10.3.54, p. 772"]
theorem exer_10_3_54 (θ : ℝ) : (cos θ)⁻¹ = -1 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π := by
  rw [inv_eq_iff_eq_inv, inv_neg, inv_one, cos_eq_neg_one_iff]
  constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.3.56: `csc θ = -2` exactly when `θ = 7π/6 + 2πk` or `θ = 11π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.56, p. 772"]
theorem exer_10_3_56 (θ : ℝ) :
    (sin θ)⁻¹ = -2 ↔ ∃ k : ℤ, θ = 7 * π / 6 + 2 * π * k ∨ θ = 11 * π / 6 + 2 * π * k := by
  have e : (sin θ)⁻¹ = -2 ↔ sin (-(π / 6)) = sin θ := by
    rw [inv_eq_iff_eq_inv, sin_neg, sin_pi_div_six, inv_neg]; norm_num; exact eq_comm
  rw [e, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inl (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.3.57: `cot θ = -1` exactly when `θ = 3π/4 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.3.57, p. 772"]
theorem exer_10_3_57 (θ : ℝ) : cos θ / sin θ = -1 ↔ ∃ k : ℤ, θ = 3 * π / 4 + π * k := by
  have h : 3 * π / 4 = π - π / 4 := by ring
  have hp : 0 < √2 := by positivity
  have hc : cos (3 * π / 4) ≠ 0 := by rw [h, cos_pi_sub, cos_pi_div_four]; simp
  have hs : sin (3 * π / 4) ≠ 0 := by rw [h, sin_pi_sub, sin_pi_div_four]; positivity
  have ht : cos (3 * π / 4) / sin (3 * π / 4) = -1 := by
    rw [h, sin_pi_sub, cos_pi_sub, sin_pi_div_four, cos_pi_div_four]
    field_simp
  rw [← ht]; exact cot_iff hc hs

end UndergradKB.Precalculus.Course
