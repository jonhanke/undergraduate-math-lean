import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.2 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 10.2 -/

private lemma eq_of_pos_sq {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (h : c ^ 2 = a ^ 2) : c = a :=
  (pow_left_inj₀ hc.le ha two_ne_zero).mp h

private lemma eq_of_neg_sq {c a : ℝ} (hc : c < 0) (ha : a ≤ 0) (h : c ^ 2 = a ^ 2) : c = a := by
  have := eq_of_pos_sq (c := -c) (a := -a) (by linarith) (by linarith) (by simpa using h)
  linarith

private lemma cos_pos_Q4 {θ : ℝ} (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) : 0 < cos θ := by
  rw [← cos_sub_two_pi]
  apply cos_pos_of_mem_Ioo; constructor <;> linarith

private lemma sin_neg_Q34 {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) : sin θ < 0 := by
  have h : sin θ = -sin (θ - π) := by rw [sin_sub_pi]; ring
  have := sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
  linarith

private lemma sin_pos_2pi {θ : ℝ} (h1 : 2 * π < θ) (h2 : θ < 5 * π / 2) : 0 < sin θ := by
  rw [← sin_sub_two_pi]
  apply sin_pos_of_pos_of_lt_pi
  · linarith
  · have := Real.pi_pos; linarith

/-- Stitz-Zeager Exercise 10.2.2: `cos(π/4) = √2/2` and `sin(π/4) = √2/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.2, p. 748"]
theorem exer_10_2_2 : cos (π / 4) = √2 / 2 ∧ sin (π / 4) = √2 / 2 :=
  ⟨cos_pi_div_four, sin_pi_div_four⟩

/-- Stitz-Zeager Exercise 10.2.5: `cos(2π/3) = -1/2` and `sin(2π/3) = √3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.5, p. 748"]
theorem exer_10_2_5 : cos (2 * π / 3) = -(1 / 2) ∧ sin (2 * π / 3) = √3 / 2 := by
  have h : 2 * π / 3 = π - π / 3 := by ring
  rw [h, cos_pi_sub, sin_pi_sub, cos_pi_div_three, sin_pi_div_three]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.6: `cos(3π/4) = -√2/2` and `sin(3π/4) = √2/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.6, p. 748"]
theorem exer_10_2_6 : cos (3 * π / 4) = -(√2 / 2) ∧ sin (3 * π / 4) = √2 / 2 := by
  have h : 3 * π / 4 = π - π / 4 := by ring
  rw [h, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.8: `cos(7π/6) = -√3/2` and `sin(7π/6) = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.8, p. 748"]
theorem exer_10_2_8 : cos (7 * π / 6) = -(√3 / 2) ∧ sin (7 * π / 6) = -(1 / 2) := by
  have h : 7 * π / 6 = π / 6 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_six, sin_pi_div_six]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.10: `cos(4π/3) = -1/2` and `sin(4π/3) = -√3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.10, p. 748"]
theorem exer_10_2_10 : cos (4 * π / 3) = -(1 / 2) ∧ sin (4 * π / 3) = -(√3 / 2) := by
  have h : 4 * π / 3 = π / 3 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_three, sin_pi_div_three]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.11: `cos(3π/2) = 0` and `sin(3π/2) = -1`. -/
@[kb "stitzzeager2013" "Exercise 10.2.11, p. 748"]
theorem exer_10_2_11 : cos (3 * π / 2) = 0 ∧ sin (3 * π / 2) = -1 := by
  have h : 3 * π / 2 = π / 2 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_two, sin_pi_div_two]; norm_num

/-- Stitz-Zeager Exercise 10.2.12: `cos(5π/3) = 1/2` and `sin(5π/3) = -√3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.12, p. 748"]
theorem exer_10_2_12 : cos (5 * π / 3) = 1 / 2 ∧ sin (5 * π / 3) = -(√3 / 2) := by
  have h : 5 * π / 3 = 2 * π - π / 3 := by ring
  rw [h, cos_two_pi_sub, sin_two_pi_sub, cos_pi_div_three, sin_pi_div_three]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.13: `cos(7π/4) = √2/2` and `sin(7π/4) = -√2/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.13, p. 748"]
theorem exer_10_2_13 : cos (7 * π / 4) = √2 / 2 ∧ sin (7 * π / 4) = -(√2 / 2) := by
  have h : 7 * π / 4 = 2 * π - π / 4 := by ring
  rw [h, cos_two_pi_sub, sin_two_pi_sub, cos_pi_div_four, sin_pi_div_four]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.14: `cos(23π/6) = √3/2` and `sin(23π/6) = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.14, p. 748"]
theorem exer_10_2_14 : cos (23 * π / 6) = √3 / 2 ∧ sin (23 * π / 6) = -(1 / 2) := by
  have h : 23 * π / 6 = -(π / 6) + ((2 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [h, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi, cos_neg, sin_neg, cos_pi_div_six,
    sin_pi_div_six]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.15: `cos(-13π/2) = 0` and `sin(-13π/2) = -1`. -/
@[kb "stitzzeager2013" "Exercise 10.2.15, p. 748"]
theorem exer_10_2_15 : cos (-(13 * π / 2)) = 0 ∧ sin (-(13 * π / 2)) = -1 := by
  have h : -(13 * π / 2) = -(π / 2) + ((-3 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [h, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi, cos_neg, sin_neg, cos_pi_div_two,
    sin_pi_div_two]; norm_num

/-- Stitz-Zeager Exercise 10.2.16: `cos(-43π/6) = -√3/2` and `sin(-43π/6) = 1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.16, p. 748"]
theorem exer_10_2_16 : cos (-(43 * π / 6)) = -(√3 / 2) ∧ sin (-(43 * π / 6)) = 1 / 2 := by
  have h : -(43 * π / 6) = (-(π / 6) + π) + ((-4 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [h, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi, cos_add_pi, sin_add_pi, cos_neg, sin_neg,
    cos_pi_div_six, sin_pi_div_six]; norm_num

/-- Stitz-Zeager Exercise 10.2.17: `cos(-3π/4) = -√2/2` and `sin(-3π/4) = -√2/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.17, p. 748"]
theorem exer_10_2_17 : cos (-(3 * π / 4)) = -(√2 / 2) ∧ sin (-(3 * π / 4)) = -(√2 / 2) := by
  have h : -(3 * π / 4) = π / 4 - π := by ring
  rw [h, cos_sub_pi, sin_sub_pi, cos_pi_div_four, sin_pi_div_four]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.18: `cos(-π/6) = √3/2` and `sin(-π/6) = -1/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.18, p. 748"]
theorem exer_10_2_18 : cos (-(π / 6)) = √3 / 2 ∧ sin (-(π / 6)) = -(1 / 2) := by
  rw [cos_neg, sin_neg, cos_pi_div_six, sin_pi_div_six]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.19: `cos(10π/3) = -1/2` and `sin(10π/3) = -√3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.19, p. 748"]
theorem exer_10_2_19 : cos (10 * π / 3) = -(1 / 2) ∧ sin (10 * π / 3) = -(√3 / 2) := by
  have h : 10 * π / 3 = (π / 3 + π) + ((1 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [h, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi, cos_add_pi, sin_add_pi, cos_pi_div_three,
    sin_pi_div_three]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.20: `cos(117π) = -1` and `sin(117π) = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.2.20, p. 748"]
theorem exer_10_2_20 : cos (117 * π) = -1 ∧ sin (117 * π) = 0 := by
  have h : 117 * π = π + ((58 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [h, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi, cos_pi, sin_pi]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.21: `sin θ = -7/25` with `θ` in Quadrant IV gives `cos θ = 24/25`. -/
@[kb "stitzzeager2013" "Exercise 10.2.21, p. 748"]
theorem exer_10_2_21 (θ : ℝ) (h : sin θ = -7 / 25) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    cos θ = 24 / 25 := by
  have hc := cos_pos_Q4 h1 h2
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  exact eq_of_pos_sq hc (by norm_num) (by nlinarith)

/-- Stitz-Zeager Exercise 10.2.22: `cos θ = 4/9` with `θ` in Quadrant I gives `sin θ = √65/9`. -/
@[kb "stitzzeager2013" "Exercise 10.2.22, p. 748"]
theorem exer_10_2_22 (θ : ℝ) (h : cos θ = 4 / 9) (h1 : 0 < θ) (h2 : θ < π / 2) :
    sin θ = √65 / 9 := by
  have hs := sin_pos_of_pos_of_lt_pi h1 (by have := Real.pi_pos; linarith)
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h65 : √65 ^ 2 = 65 := Real.sq_sqrt (by norm_num)
  exact eq_of_pos_sq hs (by positivity) (by rw [div_pow, h65]; nlinarith)

/-- Stitz-Zeager Exercise 10.2.23: `sin θ = 5/13` with `θ` in Quadrant II gives `cos θ = -12/13`. -/
@[kb "stitzzeager2013" "Exercise 10.2.23, p. 748"]
theorem exer_10_2_23 (θ : ℝ) (h : sin θ = 5 / 13) (h1 : π / 2 < θ) (h2 : θ < π) :
    cos θ = -(12 / 13) := by
  have hc := cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [Real.pi_pos])
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  exact eq_of_neg_sq hc (by norm_num) (by nlinarith)

/-- Stitz-Zeager Exercise 10.2.24: `cos θ = -2/11` with `θ` in Quadrant III gives
`sin θ = -√117/11`. -/
@[kb "stitzzeager2013" "Exercise 10.2.24, p. 748"]
theorem exer_10_2_24 (θ : ℝ) (h : cos θ = -2 / 11) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin θ = -(√117 / 11) := by
  have hs := sin_neg_Q34 h1 (by linarith [Real.pi_pos])
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h117 : √117 ^ 2 = 117 := Real.sq_sqrt (by norm_num)
  exact eq_of_neg_sq hs (by have := Real.sqrt_nonneg 117; apply neg_nonpos.mpr; positivity)
    (by rw [neg_sq, div_pow, h117]; nlinarith)

/-- Stitz-Zeager Exercise 10.2.25: `sin θ = -2/3` with `θ` in Quadrant III gives `cos θ = -√5/3`. -/
@[kb "stitzzeager2013" "Exercise 10.2.25, p. 748"]
theorem exer_10_2_25 (θ : ℝ) (h : sin θ = -2 / 3) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    cos θ = -(√5 / 3) := by
  have hc := cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos]) (by linarith)
    (x := θ)
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  exact eq_of_neg_sq hc (by apply neg_nonpos.mpr; positivity)
    (by rw [neg_sq, div_pow, h5]; nlinarith)

/-- Stitz-Zeager Exercise 10.2.26: `cos θ = 28/53` with `θ` in Quadrant IV gives `sin θ = -45/53`. -/
@[kb "stitzzeager2013" "Exercise 10.2.26, p. 748"]
theorem exer_10_2_26 (θ : ℝ) (h : cos θ = 28 / 53) (h1 : 3 * π / 2 < θ) (h2 : θ < 2 * π) :
    sin θ = -(45 / 53) := by
  have hs := sin_neg_Q34 (by linarith [Real.pi_pos]) h2
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  exact eq_of_neg_sq hs (by norm_num) (by nlinarith)

/-- Stitz-Zeager Exercise 10.2.27: `sin θ = 2√5/5` with `π/2 < θ < π` gives `cos θ = -√5/5`. -/
@[kb "stitzzeager2013" "Exercise 10.2.27, p. 748"]
theorem exer_10_2_27 (θ : ℝ) (h : sin θ = 2 * √5 / 5) (h1 : π / 2 < θ) (h2 : θ < π) :
    cos θ = -(√5 / 5) := by
  have hc := cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [Real.pi_pos])
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  exact eq_of_neg_sq hc (by apply neg_nonpos.mpr; positivity)
    (by rw [neg_sq, div_pow, h5]; nlinarith)

/-- Stitz-Zeager Exercise 10.2.28: `cos θ = √10/10` with `2π < θ < 5π/2` gives `sin θ = 3√10/10`. -/
@[kb "stitzzeager2013" "Exercise 10.2.28, p. 748"]
theorem exer_10_2_28 (θ : ℝ) (h : cos θ = √10 / 10) (h1 : 2 * π < θ) (h2 : θ < 5 * π / 2) :
    sin θ = 3 * √10 / 10 := by
  have hs := sin_pos_2pi h1 h2
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h10 : √10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  exact eq_of_pos_sq hs (by positivity) (by nlinarith [h10, this])

/-- Stitz-Zeager Exercise 10.2.29: `sin θ = -0.42` with `π < θ < 3π/2` gives
`cos θ = -√0.8236 ≈ -0.9075`. -/
@[kb "stitzzeager2013" "Exercise 10.2.29, p. 748"]
theorem exer_10_2_29 (θ : ℝ) (h : sin θ = -0.42) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    cos θ = -√0.8236 ∧ 0.9075 < √0.8236 ∧ √0.8236 < 0.9076 := by
  have hc := cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos]) (by linarith) (x := θ)
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h8 : √0.8236 ^ 2 = 0.8236 := Real.sq_sqrt (by norm_num)
  refine ⟨eq_of_neg_sq hc (by have := Real.sqrt_nonneg 0.8236; linarith)
    (by rw [neg_sq, h8]; nlinarith), ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 10.2.30: `cos θ = -0.98` with `π/2 < θ < π` gives
`sin θ = √0.0396 ≈ 0.1990`. -/
@[kb "stitzzeager2013" "Exercise 10.2.30, p. 748"]
theorem exer_10_2_30 (θ : ℝ) (h : cos θ = -0.98) (h1 : π / 2 < θ) (h2 : θ < π) :
    sin θ = √0.0396 ∧ 0.1989 < √0.0396 ∧ √0.0396 < 0.1991 := by
  have hs := sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) h2
  have := sin_sq_add_cos_sq θ
  rw [h] at this
  have h8 : √0.0396 ^ 2 = 0.0396 := Real.sq_sqrt (by norm_num)
  refine ⟨eq_of_pos_sq hs (Real.sqrt_nonneg _) (by rw [h8]; nlinarith), ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 10.2.31: `sin θ = 1/2` exactly when `θ = π/6 + 2πk` or `θ = 5π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.31, p. 749"]
theorem exer_10_2_31 (θ : ℝ) :
    sin θ = 1 / 2 ↔ ∃ k : ℤ, θ = π / 6 + 2 * π * k ∨ θ = 5 * π / 6 + 2 * π * k := by
  have e : sin θ = 1 / 2 ↔ sin (π / 6) = sin θ := by rw [sin_pi_div_six]; exact eq_comm
  rw [e, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩

/-- Stitz-Zeager Exercise 10.2.32: `cos θ = -√3/2` exactly when `θ = 5π/6 + 2πk` or
`θ = 7π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.32, p. 749"]
theorem exer_10_2_32 (θ : ℝ) :
    cos θ = -(√3 / 2) ↔ ∃ k : ℤ, θ = 5 * π / 6 + 2 * π * k ∨ θ = 7 * π / 6 + 2 * π * k := by
  have hv : cos (5 * π / 6) = -(√3 / 2) := by
    have h : 5 * π / 6 = π - π / 6 := by ring
    rw [h, cos_pi_sub, cos_pi_div_six]
  have e : cos θ = -(√3 / 2) ↔ cos (5 * π / 6) = cos θ := by rw [hv]; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.2.33: `sin θ = 0` exactly when `θ = πk` for an integer `k`. -/
@[kb "stitzzeager2013" "Exercise 10.2.33, p. 749"]
theorem exer_10_2_33 (θ : ℝ) : sin θ = 0 ↔ ∃ k : ℤ, θ = π * k := by
  rw [sin_eq_zero_iff]
  constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.2.34: `cos θ = √2/2` exactly when `θ = π/4 + 2πk` or `θ = 7π/4 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.34, p. 749"]
theorem exer_10_2_34 (θ : ℝ) :
    cos θ = √2 / 2 ↔ ∃ k : ℤ, θ = π / 4 + 2 * π * k ∨ θ = 7 * π / 4 + 2 * π * k := by
  have e : cos θ = √2 / 2 ↔ cos (π / 4) = cos θ := by rw [cos_pi_div_four]; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.2.35: `sin θ = √3/2` exactly when `θ = π/3 + 2πk` or `θ = 2π/3 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.35, p. 749"]
theorem exer_10_2_35 (θ : ℝ) :
    sin θ = √3 / 2 ↔ ∃ k : ℤ, θ = π / 3 + 2 * π * k ∨ θ = 2 * π / 3 + 2 * π * k := by
  have e : sin θ = √3 / 2 ↔ sin (π / 3) = sin θ := by rw [sin_pi_div_three]; exact eq_comm
  rw [e, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩

/-- Stitz-Zeager Exercise 10.2.36: `cos θ = -1` exactly when `θ = (2k+1)π`. -/
@[kb "stitzzeager2013" "Exercise 10.2.36, p. 749"]
theorem exer_10_2_36 (θ : ℝ) : cos θ = -1 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π := by
  rw [cos_eq_neg_one_iff]
  constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.2.37: `sin θ = -1` exactly when `θ = 3π/2 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.37, p. 749"]
theorem exer_10_2_37 (θ : ℝ) : sin θ = -1 ↔ ∃ k : ℤ, θ = 3 * π / 2 + 2 * π * k := by
  rw [sin_eq_neg_one_iff]
  constructor
  · rintro ⟨k, h⟩; exact ⟨k - 1, by push_cast; linarith⟩
  · rintro ⟨k, h⟩; exact ⟨k + 1, by push_cast; linarith⟩

/-- Stitz-Zeager Exercise 10.2.38: `cos θ = √3/2` exactly when `θ = π/6 + 2πk` or `θ = 11π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.38, p. 749"]
theorem exer_10_2_38 (θ : ℝ) :
    cos θ = √3 / 2 ↔ ∃ k : ℤ, θ = π / 6 + 2 * π * k ∨ θ = 11 * π / 6 + 2 * π * k := by
  have e : cos θ = √3 / 2 ↔ cos (π / 6) = cos θ := by rw [cos_pi_div_six]; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.2.39: `cos θ = -1.001` has no solution. -/
@[kb "stitzzeager2013" "Exercise 10.2.39, p. 749"]
theorem exer_10_2_39 : ¬ ∃ θ : ℝ, cos θ = -1.001 := by
  rintro ⟨θ, h⟩
  have := neg_one_le_cos θ
  norm_num at h; linarith

/-- Stitz-Zeager Exercise 10.2.40: `cos t = 0` exactly when `t = π/2 + πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.40, p. 749"]
theorem exer_10_2_40 (t : ℝ) : cos t = 0 ↔ ∃ k : ℤ, t = π / 2 + π * k := by
  rw [cos_eq_zero_iff]
  constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.2.41: `sin t = -√2/2` exactly when `t = 5π/4 + 2πk` or
`t = 7π/4 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.41, p. 749"]
theorem exer_10_2_41 (t : ℝ) :
    sin t = -(√2 / 2) ↔ ∃ k : ℤ, t = 5 * π / 4 + 2 * π * k ∨ t = 7 * π / 4 + 2 * π * k := by
  have e : sin t = -(√2 / 2) ↔ sin (-(π / 4)) = sin t := by
    rw [sin_neg, sin_pi_div_four]; exact eq_comm
  rw [e, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inl (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.2.42: `cos t = 3` has no solution. -/
@[kb "stitzzeager2013" "Exercise 10.2.42, p. 749"]
theorem exer_10_2_42 : ¬ ∃ t : ℝ, cos t = 3 := by
  rintro ⟨t, h⟩
  have := cos_le_one t
  linarith

/-- Stitz-Zeager Exercise 10.2.43: `sin t = -1/2` exactly when `t = 7π/6 + 2πk` or
`t = 11π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.43, p. 749"]
theorem exer_10_2_43 (t : ℝ) :
    sin t = -(1 / 2) ↔ ∃ k : ℤ, t = 7 * π / 6 + 2 * π * k ∨ t = 11 * π / 6 + 2 * π * k := by
  have e : sin t = -(1 / 2) ↔ sin (-(π / 6)) = sin t := by
    rw [sin_neg, sin_pi_div_six]; exact eq_comm
  rw [e, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inl (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.2.44: `cos t = 1/2` exactly when `t = π/3 + 2πk` or `t = 5π/3 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.44, p. 749"]
theorem exer_10_2_44 (t : ℝ) :
    cos t = 1 / 2 ↔ ∃ k : ℤ, t = π / 3 + 2 * π * k ∨ t = 5 * π / 3 + 2 * π * k := by
  have e : cos t = 1 / 2 ↔ cos (π / 3) = cos t := by rw [cos_pi_div_three]; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Exercise 10.2.45: `sin t = -2` has no solution. -/
@[kb "stitzzeager2013" "Exercise 10.2.45, p. 749"]
theorem exer_10_2_45 : ¬ ∃ t : ℝ, sin t = -2 := by
  rintro ⟨t, h⟩
  have := neg_one_le_sin t
  linarith

/-- Stitz-Zeager Exercise 10.2.46: `cos t = 1` exactly when `t = 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.46, p. 749"]
theorem exer_10_2_46 (t : ℝ) : cos t = 1 ↔ ∃ k : ℤ, t = 2 * π * k := by
  rw [cos_eq_one_iff]
  constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.2.47: `sin t = 1` exactly when `t = π/2 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.47, p. 749"]
theorem exer_10_2_47 (t : ℝ) : sin t = 1 ↔ ∃ k : ℤ, t = π / 2 + 2 * π * k := by
  rw [sin_eq_one_iff]
  constructor <;> rintro ⟨k, h⟩ <;> exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.2.48: `cos t = -√2/2` exactly when `t = 3π/4 + 2πk` or
`t = 5π/4 + 2πk`. -/
@[kb "stitzzeager2013" "Exercise 10.2.48, p. 749"]
theorem exer_10_2_48 (t : ℝ) :
    cos t = -(√2 / 2) ↔ ∃ k : ℤ, t = 3 * π / 4 + 2 * π * k ∨ t = 5 * π / 4 + 2 * π * k := by
  have hv : cos (3 * π / 4) = -(√2 / 2) := by
    have h : 3 * π / 4 = π - π / 4 := by ring
    rw [h, cos_pi_sub, cos_pi_div_four]
  have e : cos t = -(√2 / 2) ↔ cos (3 * π / 4) = cos t := by rw [hv]; exact eq_comm
  rw [e, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [h]; push_cast; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k + 1, Or.inr (by rw [h]; push_cast; ring)⟩

end UndergradKB.Precalculus.Course
