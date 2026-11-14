import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): worked examples -/

namespace UndergradKB.Precalculus.Course

open Set Polynomial

/-- Two real polynomials that agree at all positive reals are equal. -/
private theorem poly_eq_of_pos (P Q : ℝ[X]) (h : ∀ x : ℝ, 0 < x → P.eval x = Q.eval x) : P = Q :=
  Polynomial.eq_of_infinite_eval_eq P Q ((Set.Ioi_infinite (0 : ℝ)).mono fun x hx => h x hx)

/-- If `q(a) ≠ 0` then `a` is a root of `q * (X - a)^n` of multiplicity exactly `n`. -/
private theorem rootMultiplicity_of_factor (q : ℝ[X]) (a : ℝ) (n : ℕ) (hq : q.eval a ≠ 0) :
    (q * (X - C a) ^ n).rootMultiplicity a = n := by
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  rw [rootMultiplicity_mul_X_sub_C_pow hq0,
    rootMultiplicity_eq_zero (by simpa [IsRoot] using hq)]
  simp

/-! ## Section 3.1 -/

/-- Stitz-Zeager Example 3.1.1(1): `(4 + x³)/x` is not a polynomial function: no polynomial agrees with it on its
domain `x ≠ 0`. -/
@[kb "stitzzeager2013" "Example 3.1.1, p. 247"]
theorem ex_3_1_1_a_not_polynomial :
    ¬ ∃ P : ℝ[X], ∀ x : ℝ, x ≠ 0 → P.eval x = (4 + x ^ 3) / x := by
  rintro ⟨P, hP⟩
  have h : P * X = X ^ 3 + 4 := by
    apply poly_eq_of_pos
    intro x hx
    have := hP x hx.ne'
    simp only [eval_mul, eval_X, eval_add, eval_pow, eval_ofNat]
    rw [this]; field_simp; ring
  have := congrArg (eval 0) h
  simp at this

/-- Stitz-Zeager Example 3.1.1(2): `(x³ + 4x)/x` agrees with `x² + 4` wherever it is defined, but its domain
excludes `0`, so it is not a polynomial function (whose domain is all reals). -/
@[kb "stitzzeager2013" "Example 3.1.1, p. 247"]
theorem ex_3_1_1_b_not_polynomial :
    (∀ x : ℝ, x ≠ 0 → (x ^ 3 + 4 * x) / x = (X ^ 2 + 4 : ℝ[X]).eval x) ∧
      {x : ℝ | x ≠ 0} ≠ Set.univ := by
  refine ⟨fun x hx => ?_, fun h => ?_⟩
  · simp only [eval_add, eval_pow, eval_X, eval_ofNat]
    field_simp
  · have : (0 : ℝ) ∈ {x : ℝ | x ≠ 0} := h ▸ Set.mem_univ 0
    exact this rfl

/-- Stitz-Zeager Example 3.1.1(3): `(4x + x³)/(x² + 4)` equals `x`, so it is a polynomial function. -/
@[kb "stitzzeager2013" "Example 3.1.1, p. 247"]
theorem ex_3_1_1_c_polynomial : ∀ x : ℝ, (4 * x + x ^ 3) / (x ^ 2 + 4) = (X : ℝ[X]).eval x := by
  intro x
  have : x ^ 2 + 4 ≠ 0 := by positivity
  rw [eval_X, div_eq_iff this]; ring

/-- Stitz-Zeager Example 3.1.1(5): `|x|` is not a polynomial function. -/
@[kb "stitzzeager2013" "Example 3.1.1, p. 247"]
theorem ex_3_1_1_e_abs_not_polynomial : ¬ ∃ P : ℝ[X], ∀ x : ℝ, P.eval x = |x| := by
  rintro ⟨P, hP⟩
  have h : P = X := by
    apply poly_eq_of_pos
    intro x hx
    rw [hP x, abs_of_pos hx]; simp
  have := hP (-1)
  rw [h] at this
  norm_num at this

/-- Stitz-Zeager Example 3.1.2(1): `4x⁵ - 3x² + 2x - 5` has degree `5`, leading coefficient `4`
and constant term `-5`. -/
@[kb "stitzzeager2013" "Example 3.1.2, p. 249"]
theorem ex_3_1_2_a_degree :
    (4 * X ^ 5 - 3 * X ^ 2 + 2 * X - 5 : ℝ[X]).natDegree = 5 ∧
      (4 * X ^ 5 - 3 * X ^ 2 + 2 * X - 5 : ℝ[X]).leadingCoeff = 4 ∧
      (4 * X ^ 5 - 3 * X ^ 2 + 2 * X - 5 : ℝ[X]).coeff 0 = -5 := by
  have h : (4 * X ^ 5 - 3 * X ^ 2 + 2 * X - 5 : ℝ[X]).natDegree = 5 := by compute_degree!
  refine ⟨h, ?_, ?_⟩
  · rw [leadingCoeff, h]; simp [coeff_X, coeff_one, coeff_X_pow]
  · simp [coeff_X, coeff_one, coeff_X_pow]

/-- Stitz-Zeager Example 3.1.2(2): `12x + x³` has degree `3`, leading coefficient `1`, constant term `0`. -/
@[kb "stitzzeager2013" "Example 3.1.2, p. 249"]
theorem ex_3_1_2_b_degree :
    (12 * X + X ^ 3 : ℝ[X]).natDegree = 3 ∧ (12 * X + X ^ 3 : ℝ[X]).leadingCoeff = 1 ∧
      (12 * X + X ^ 3 : ℝ[X]).coeff 0 = 0 := by
  have h : (12 * X + X ^ 3 : ℝ[X]).natDegree = 3 := by compute_degree!
  refine ⟨h, ?_, ?_⟩
  · rw [leadingCoeff, h]; simp [coeff_X, coeff_X_pow]
  · simp [coeff_X, coeff_X_pow]

/-- Stitz-Zeager Example 3.1.2(3): `(4 - x)/5 = -x/5 + 4/5` has degree `1`, leading coefficient `-1/5`,
constant term `4/5`. -/
@[kb "stitzzeager2013" "Example 3.1.2, p. 249"]
theorem ex_3_1_2_c_degree :
    (C (-1 / 5) * X + C (4 / 5) : ℝ[X]).natDegree = 1 ∧
      (C (-1 / 5) * X + C (4 / 5) : ℝ[X]).leadingCoeff = -1 / 5 ∧
      (C (-1 / 5) * X + C (4 / 5) : ℝ[X]).coeff 0 = 4 / 5 ∧
      ∀ x : ℝ, (4 - x) / 5 = (C (-1 / 5) * X + C (4 / 5) : ℝ[X]).eval x := by
  have h : (C (-1 / 5) * X + C (4 / 5) : ℝ[X]).natDegree = 1 := by compute_degree!
  refine ⟨h, ?_, ?_, fun x => ?_⟩
  · rw [leadingCoeff, h]; simp [coeff_X]
  · simp [coeff_X]
  · simp; ring

/-- Stitz-Zeager Example 3.1.2(4): `(2x-1)³(x-2)(3x+2)` has degree `5`, leading coefficient `24`,
constant term `4`. -/
@[kb "stitzzeager2013" "Example 3.1.2, p. 249"]
theorem ex_3_1_2_d_degree :
    ((2 * X - 1) ^ 3 * (X - 2) * (3 * X + 2) : ℝ[X]).natDegree = 5 ∧
      ((2 * X - 1) ^ 3 * (X - 2) * (3 * X + 2) : ℝ[X]).leadingCoeff = 24 ∧
      ((2 * X - 1) ^ 3 * (X - 2) * (3 * X + 2) : ℝ[X]).coeff 0 = 4 := by
  have e : ((2 * X - 1) ^ 3 * (X - 2) * (3 * X + 2) : ℝ[X]) =
      24 * X ^ 5 - 68 * X ^ 4 + 34 * X ^ 3 + 21 * X ^ 2 - 20 * X + 4 := by ring
  rw [e]
  have h : (24 * X ^ 5 - 68 * X ^ 4 + 34 * X ^ 3 + 21 * X ^ 2 - 20 * X + 4 : ℝ[X]).natDegree = 5 := by
    compute_degree!
  refine ⟨h, ?_, ?_⟩
  · rw [leadingCoeff, h]; simp [coeff_X, coeff_one, coeff_X_pow]
  · simp [coeff_X, coeff_one, coeff_X_pow]

/-- Stitz-Zeager Example 3.1.3(1): the open box has volume `x(10-2x)(12-2x) = 4x³ - 44x² + 120x`,
for `0 < x < 5`. -/
@[kb "stitzzeager2013" "Example 3.1.3, p. 250"]
theorem ex_3_1_3_box_volume (x : ℝ) :
    x * (10 - 2 * x) * (12 - 2 * x) = 4 * x ^ 3 - 44 * x ^ 2 + 120 * x := by ring

/-- Stitz-Zeager Example 3.1.4: by the Intermediate Value Theorem `x² - 2` has a zero in `[1,3]`, and it is `√2`. -/
@[kb "stitzzeager2013" "Example 3.1.4, p. 254"]
theorem ex_3_1_4_sqrt_two_via_ivt : ∃ c ∈ Icc (1 : ℝ) 3, c ^ 2 - 2 = 0 ∧ c = Real.sqrt 2 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2 - 2) (Icc 1 3) := by fun_prop
  have h0 : (0 : ℝ) ∈ Icc ((fun x : ℝ => x ^ 2 - 2) 1) ((fun x : ℝ => x ^ 2 - 2) 3) := by
    constructor <;> norm_num
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 3) hcont h0
  refine ⟨c, hc, hc0, ?_⟩
  have hc2 : c ^ 2 = 2 := by simp only at hc0; linarith
  rw [← hc2, Real.sqrt_sq (by linarith [hc.1])]

/-- Stitz-Zeager Example 3.1.5: for `f x = x³(x-3)²(x+2)(x²+1)`, the zeros are `-2, 0, 3`,
`f` is negative exactly on `(-2,0)` and positive elsewhere off the zeros (sign diagram `+ - + +`). -/
@[kb "stitzzeager2013" "Example 3.1.5, p. 254"]
theorem ex_3_1_5_sign_diagram :
    let f : ℝ → ℝ := fun x => x ^ 3 * (x - 3) ^ 2 * (x + 2) * (x ^ 2 + 1)
    (∀ x, f x = 0 ↔ x = -2 ∨ x = 0 ∨ x = 3) ∧
      (∀ x, 0 < f x ↔ x < -2 ∨ (0 < x ∧ x ≠ 3)) ∧ (∀ x, f x < 0 ↔ -2 < x ∧ x < 0) ∧
      0 < f (-3) ∧ f (-1) < 0 ∧ 0 < f 1 ∧ 0 < f 4 := by
  intro f
  have key : ∀ x, f x = (x ^ 2 * (x - 3) ^ 2 * (x ^ 2 + 1)) * (x * (x + 2)) := fun x => by
    simp only [f]; ring
  have hC : ∀ x : ℝ, 0 ≤ x ^ 2 * (x - 3) ^ 2 * (x ^ 2 + 1) := fun x => by positivity
  have hCpos : ∀ x : ℝ, x ≠ 0 → x ≠ 3 → 0 < x ^ 2 * (x - 3) ^ 2 * (x ^ 2 + 1) := fun x h0 h3 => by
    have : x - 3 ≠ 0 := sub_ne_zero.mpr h3
    positivity
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, by norm_num [f], by norm_num [f], by norm_num [f],
    by norm_num [f]⟩
  · rw [key]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · have h' : x ^ 2 * (x - 3) ^ 2 * (x ^ 2 + 1) = 0 := h
        rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · right; left; exact pow_eq_zero_iff (two_ne_zero) |>.mp h3
          · right; right; have := pow_eq_zero_iff (two_ne_zero) |>.mp h3; linarith
        · nlinarith [sq_nonneg x]
      · rcases mul_eq_zero.mp h with h | h
        · right; left; exact h
        · left; linarith
    · rintro (h | h | h) <;> subst h <;> norm_num
  · rw [key]
    constructor
    · intro h
      have hx0 : x ≠ 0 := by rintro rfl; norm_num at h
      have hx3 : x ≠ 3 := by rintro rfl; norm_num at h
      have hD : 0 < x * (x + 2) := by
        by_contra hneg
        push_neg at hneg
        nlinarith [hC x]
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · left; nlinarith
      · right; exact ⟨hpos, hx3⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact mul_pos (hCpos x (ne_of_lt (by linarith)) (ne_of_lt (by linarith)))
          (by nlinarith)
      · exact mul_pos (hCpos x h1.ne' h2) (by nlinarith)
  · rw [key]
    constructor
    · intro h
      have hx0 : x ≠ 0 := by rintro rfl; norm_num at h
      have hx3 : x ≠ 3 := by rintro rfl; norm_num at h
      have hCp := hCpos x hx0 hx3
      have hD : x * (x + 2) < 0 := by
        by_contra hneg
        push_neg at hneg
        nlinarith
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      have hx0 : x ≠ 0 := ne_of_lt h2
      have hx3 : x ≠ 3 := ne_of_lt (by linarith)
      exact mul_neg_of_pos_of_neg (hCpos x hx0 hx3) (by nlinarith)

/-- Stitz-Zeager Example 3.1.6: `-3(2x-1)(x+1)²` has leading coefficient `-6` and degree `3`, the zero
`1/2` has multiplicity `1`, the zero `-1` has multiplicity `2`, and `f 0 = 3`. -/
@[kb "stitzzeager2013" "Example 3.1.6, p. 257"]
theorem ex_3_1_6_multiplicities :
    let f : ℝ[X] := -3 * (2 * X - 1) * (X + 1) ^ 2
    f.natDegree = 3 ∧ f.leadingCoeff = -6 ∧ f.rootMultiplicity (1 / 2) = 1 ∧
      f.rootMultiplicity (-1) = 2 ∧ f.eval 0 = 3 := by
  intro f
  have e : f = (-6 * (X - C (-1)) ^ 2) * (X - C (1 / 2)) ^ 1 := by
    apply Polynomial.funext
    intro x; simp only [f]; simp <;> ring
  have e2 : f = (-3 * (2 * X - 1)) * (X - C (-1)) ^ 2 := by
    apply Polynomial.funext
    intro x; simp only [f]; simp <;> ring
  have e3 : f = -6 * X ^ 3 - 9 * X ^ 2 + 3 := by
    simp only [f]; ring
  have h : f.natDegree = 3 := by rw [e3]; compute_degree!
  refine ⟨h, ?_, ?_, ?_, by simp [f]⟩
  · rw [leadingCoeff, h, e3]; simp [coeff_X, coeff_one, coeff_X_pow]
  · rw [e]; apply rootMultiplicity_of_factor; simp <;> norm_num
  · rw [e2]; apply rootMultiplicity_of_factor; simp <;> norm_num

/-! ## Section 3.2 -/

/-- Stitz-Zeager Example 3.2.1(1): `5x³ - 2x² + 1 = (x-3)(5x² + 13x + 39) + 118`. -/
@[kb "stitzzeager2013" "Example 3.2.1, p. 273"]
theorem ex_3_2_1_a (x : ℝ) : 5 * x ^ 3 - 2 * x ^ 2 + 1 = (x - 3) * (5 * x ^ 2 + 13 * x + 39) + 118 := by
  ring

/-- Stitz-Zeager Example 3.2.1(2): `x³ + 8 = (x+2)(x² - 2x + 4)`. -/
@[kb "stitzzeager2013" "Example 3.2.1, p. 273"]
theorem ex_3_2_1_b (x : ℝ) : x ^ 3 + 8 = (x + 2) * (x ^ 2 - 2 * x + 4) := by ring

/-- Stitz-Zeager Example 3.2.1(3): `4 - 8x - 12x² = (2x-3)(-6x-13) - 35`. -/
@[kb "stitzzeager2013" "Example 3.2.1, p. 273"]
theorem ex_3_2_1_c (x : ℝ) : 4 - 8 * x - 12 * x ^ 2 = (2 * x - 3) * (-6 * x - 13) - 35 := by ring

/-- Stitz-Zeager Example 3.2.2(1): for `p x = 2x³ - 5x + 3`, `p(-2) = -3`. -/
@[kb "stitzzeager2013" "Example 3.2.2, p. 274"]
theorem ex_3_2_2_a_remainder : 2 * (-2 : ℝ) ^ 3 - 5 * (-2) + 3 = -3 := by norm_num

/-- Stitz-Zeager Example 3.2.2(2): `2x³ - 5x + 3 = (x-1)(2x²+2x-3)`, with real zeros `1` and `(-1 ± √7)/2`. -/
@[kb "stitzzeager2013" "Example 3.2.2, p. 274"]
theorem ex_3_2_2_b_factor_and_zeros (x : ℝ) :
    2 * x ^ 3 - 5 * x + 3 = (x - 1) * (2 * x ^ 2 + 2 * x - 3) ∧
      (2 * x ^ 3 - 5 * x + 3 = 0 ↔
        x = 1 ∨ x = (-1 + Real.sqrt 7) / 2 ∨ x = (-1 - Real.sqrt 7) / 2) := by
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  refine ⟨by ring, ?_⟩
  constructor
  · intro h
    have h' : (x - 1) * ((x - (-1 + Real.sqrt 7) / 2) * (x - (-1 - Real.sqrt 7) / 2)) = 0 := by
      linear_combination (1 / 2 : ℝ) * h - ((x - 1) / 4) * h7
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · right; left; linarith
      · right; right; linarith
  · rintro (h | h | h)
    · subst h; norm_num
    · subst h; linear_combination (((-1 + Real.sqrt 7) / 2 - 1) / 2) * h7
    · subst h; linear_combination (((-1 - Real.sqrt 7) / 2 - 1) / 2) * h7

/-- Stitz-Zeager Example 3.2.3: `4x⁴ - 4x³ - 11x² + 12x - 3 = (x - 1/2)²(4x² - 12)`, so the real zeros are
`1/2`, `±√3`, and `1/2` has multiplicity `2`. -/
@[kb "stitzzeager2013" "Example 3.2.3, p. 275"]
theorem ex_3_2_3_double_zero :
    (∀ x : ℝ, 4 * x ^ 4 - 4 * x ^ 3 - 11 * x ^ 2 + 12 * x - 3 = (x - 1 / 2) ^ 2 * (4 * x ^ 2 - 12)) ∧
      (∀ x : ℝ, 4 * x ^ 4 - 4 * x ^ 3 - 11 * x ^ 2 + 12 * x - 3 = 0 ↔
        x = 1 / 2 ∨ x = Real.sqrt 3 ∨ x = -Real.sqrt 3) ∧
      (4 * X ^ 4 - 4 * X ^ 3 - 11 * X ^ 2 + 12 * X - 3 : ℝ[X]).rootMultiplicity (1 / 2) = 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨fun x => by ring, fun x => ?_, ?_⟩
  · have e : 4 * x ^ 4 - 4 * x ^ 3 - 11 * x ^ 2 + 12 * x - 3 = (x - 1 / 2) ^ 2 * (4 * x ^ 2 - 12) := by
      ring
    rw [e]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · left; have := pow_eq_zero_iff (two_ne_zero) |>.mp h1; linarith
      · have : (x - Real.sqrt 3) * (x + Real.sqrt 3) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h2 | h2
        · right; left; linarith
        · right; right; linarith
    · rintro (h | h | h) <;> subst h <;> nlinarith
  · have e : (4 * X ^ 4 - 4 * X ^ 3 - 11 * X ^ 2 + 12 * X - 3 : ℝ[X]) =
        (4 * X ^ 2 - 12) * (X - C (1 / 2)) ^ 2 := by
      apply Polynomial.funext
      intro x; simp; ring
    rw [e]
    apply rootMultiplicity_of_factor
    simp; norm_num

/-! ## Section 3.3 -/

/-- Stitz-Zeager Example 3.3.1: all real zeros of `2x⁴ + 4x³ - x² - 6x - 3` lie in `[-4,4]`. -/
@[kb "stitzzeager2013" "Example 3.3.1, p. 281"]
theorem ex_3_3_1_cauchy_bound (x : ℝ) (h : 2 * x ^ 4 + 4 * x ^ 3 - x ^ 2 - 6 * x - 3 = 0) :
    x ∈ Icc (-4 : ℝ) 4 := by
  constructor
  · by_contra hx
    push_neg at hx
    nlinarith [sq_nonneg x, sq_nonneg (x + 4), sq_nonneg (x ^ 2), mul_self_nonneg (x ^ 2 + 2 * x)]
  · by_contra hx
    push_neg at hx
    nlinarith [sq_nonneg x, sq_nonneg (x - 4), sq_nonneg (x ^ 2), mul_self_nonneg (x ^ 2 + 2 * x)]

/-- Stitz-Zeager Examples 3.3.3 and 3.3.6: `2x⁴ + 4x³ - x² - 6x - 3 = (x+1)²(2x²-3)`; its real zeros are
`-1` (multiplicity `2`) and `±√6/2` (multiplicity `1`). -/
@[kb "stitzzeager2013" "Example 3.3.3, p. 282"]
theorem ex_3_3_3_zeros_and_multiplicities :
    (∀ x : ℝ, 2 * x ^ 4 + 4 * x ^ 3 - x ^ 2 - 6 * x - 3 = (x + 1) ^ 2 * (2 * x ^ 2 - 3)) ∧
      (∀ x : ℝ, 2 * x ^ 4 + 4 * x ^ 3 - x ^ 2 - 6 * x - 3 = 0 ↔
        x = -1 ∨ x = Real.sqrt 6 / 2 ∨ x = -(Real.sqrt 6 / 2)) ∧
      (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).rootMultiplicity (-1) = 2 ∧
      (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).rootMultiplicity (Real.sqrt 6 / 2) = 1 ∧
      (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]).rootMultiplicity (-(Real.sqrt 6 / 2)) = 1 := by
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have ha : (Real.sqrt 6 / 2) ^ 2 = 3 / 2 := by nlinarith
  have hfac : ∀ x : ℝ, 2 * x ^ 4 + 4 * x ^ 3 - x ^ 2 - 6 * x - 3 = (x + 1) ^ 2 * (2 * x ^ 2 - 3) :=
    fun x => by ring
  refine ⟨hfac, fun x => ?_, ?_, ?_, ?_⟩
  · rw [hfac]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · left; have := pow_eq_zero_iff (two_ne_zero) |>.mp h1; linarith
      · have : (x - Real.sqrt 6 / 2) * (x + Real.sqrt 6 / 2) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h2 | h2
        · right; left; linarith
        · right; right; linarith
    · rintro (h | h | h) <;> subst h <;> nlinarith
  · have e : (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]) =
        (2 * X ^ 2 - 3) * (X - C (-1)) ^ 2 := by
      apply Polynomial.funext
      intro x; simp; ring
    rw [e]
    apply rootMultiplicity_of_factor
    simp; norm_num
  · have e : (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]) =
        (2 * (X - C (-(Real.sqrt 6 / 2))) * (X + 1) ^ 2) * (X - C (Real.sqrt 6 / 2)) ^ 1 := by
      apply Polynomial.funext
      intro x; simp
      linear_combination (2 * (x + 1) ^ 2) * ha
    rw [e]
    apply rootMultiplicity_of_factor
    simp only [eval_mul, eval_sub, eval_C, eval_X, eval_add, eval_pow, eval_one, eval_ofNat]
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (pow_ne_zero _ ?_) <;> intro h <;> nlinarith
  · have e : (2 * X ^ 4 + 4 * X ^ 3 - X ^ 2 - 6 * X - 3 : ℝ[X]) =
        (2 * (X - C (Real.sqrt 6 / 2)) * (X + 1) ^ 2) * (X - C (-(Real.sqrt 6 / 2))) ^ 1 := by
      apply Polynomial.funext
      intro x; simp
      linear_combination (2 * (x + 1) ^ 2) * ha
    rw [e]
    apply rootMultiplicity_of_factor
    simp only [eval_mul, eval_sub, eval_C, eval_X, eval_add, eval_pow, eval_one, eval_ofNat]
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (pow_ne_zero _ ?_) <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 3.3.4: all real zeros of `x⁴ + x² - 12` lie in `[-13,13]`; the zeros are
`±√3`, each of multiplicity `1`. -/
@[kb "stitzzeager2013" "Example 3.3.4, p. 284"]
theorem ex_3_3_4_quadratic_in_disguise :
    (∀ x : ℝ, x ^ 4 + x ^ 2 - 12 = 0 ↔ x = Real.sqrt 3 ∨ x = -Real.sqrt 3) ∧
      (∀ x : ℝ, x ^ 4 + x ^ 2 - 12 = 0 → x ∈ Icc (-13 : ℝ) 13) ∧
      (X ^ 4 + X ^ 2 - 12 : ℝ[X]).rootMultiplicity (Real.sqrt 3) = 1 ∧
      (X ^ 4 + X ^ 2 - 12 : ℝ[X]).rootMultiplicity (-Real.sqrt 3) = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have zeros : ∀ x : ℝ, x ^ 4 + x ^ 2 - 12 = 0 ↔ x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by
    intro x
    have e : x ^ 4 + x ^ 2 - 12 = (x ^ 2 - 3) * (x ^ 2 + 4) := by ring
    rw [e]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · have : (x - Real.sqrt 3) * (x + Real.sqrt 3) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h2 | h2
        · left; linarith
        · right; linarith
      · nlinarith [sq_nonneg x]
    · rintro (h | h) <;> subst h <;> nlinarith
  refine ⟨zeros, fun x h => ?_, ?_, ?_⟩
  · rcases (zeros x).mp h with h1 | h1 <;> subst h1 <;> constructor <;> nlinarith
  · have e : (X ^ 4 + X ^ 2 - 12 : ℝ[X]) =
        ((X + C (Real.sqrt 3)) * (X ^ 2 + 4)) * (X - C (Real.sqrt 3)) ^ 1 := by
      apply Polynomial.funext
      intro x; simp
      linear_combination ((x ^ 2 + 4)) * h3
    rw [e]
    apply rootMultiplicity_of_factor
    simp only [eval_mul, eval_sub, eval_C, eval_X, eval_add, eval_pow, eval_ofNat]
    refine mul_ne_zero ?_ ?_ <;> intro h <;> nlinarith [sq_nonneg (Real.sqrt 3)]
  · have e : (X ^ 4 + X ^ 2 - 12 : ℝ[X]) =
        ((X - C (Real.sqrt 3)) * (X ^ 2 + 4)) * (X - C (-Real.sqrt 3)) ^ 1 := by
      apply Polynomial.funext
      intro x; simp
      linear_combination ((x ^ 2 + 4)) * h3
    rw [e]
    apply rootMultiplicity_of_factor
    simp only [eval_mul, eval_sub, eval_C, eval_X, eval_add, eval_pow, eval_ofNat]
    refine mul_ne_zero ?_ ?_ <;> intro h <;> nlinarith [sq_nonneg (Real.sqrt 3)]

/-- Stitz-Zeager Example 3.3.6(1): values of `f x = 2x⁴ + 4x³ - x² - 6x - 3` used to locate the positive
zero: `f(1/2) = -45/8`, `f 1 = -4`, `f(3/2) = 75/8`, and `f x > 0` for `x > 3/2` (so `3/2` bounds the zeros). -/
@[kb "stitzzeager2013" "Example 3.3.6, p. 287"]
theorem ex_3_3_6_values_and_bound :
    (2 * (1 / 2 : ℝ) ^ 4 + 4 * (1 / 2) ^ 3 - (1 / 2) ^ 2 - 6 * (1 / 2) - 3 = -45 / 8) ∧
      (2 * (1 : ℝ) ^ 4 + 4 * 1 ^ 3 - 1 ^ 2 - 6 * 1 - 3 = -4) ∧
      (2 * (3 / 2 : ℝ) ^ 4 + 4 * (3 / 2) ^ 3 - (3 / 2) ^ 2 - 6 * (3 / 2) - 3 = 75 / 8) ∧
      (∀ x : ℝ, 3 / 2 < x → 0 < 2 * x ^ 4 + 4 * x ^ 3 - x ^ 2 - 6 * x - 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun x hx => ?_⟩
  nlinarith [sq_nonneg x, sq_nonneg (x - 3 / 2), mul_pos (by linarith : (0 : ℝ) < x - 3 / 2) (by linarith : (0 : ℝ) < x),
    sq_nonneg (x ^ 2)]

/-- Stitz-Zeager Example 3.3.7(1,2): `2x⁵ + 6x³ + 3 = 3x⁴ + 8x²` exactly for `x = -1/2` or `x = 1`, and
`2x⁵ + 6x³ + 3 ≤ 3x⁴ + 8x²` exactly on `(-∞,-1/2] ∪ {1}`. -/
@[kb "stitzzeager2013" "Example 3.3.7, p. 289"]
theorem ex_3_3_7_equation_and_inequality :
    (∀ x : ℝ, 2 * x ^ 5 - 3 * x ^ 4 + 6 * x ^ 3 - 8 * x ^ 2 + 3 =
        (x - 1) ^ 2 * (x + 1 / 2) * (2 * x ^ 2 + 6)) ∧
      (∀ x : ℝ, 2 * x ^ 5 + 6 * x ^ 3 + 3 = 3 * x ^ 4 + 8 * x ^ 2 ↔ x = -1 / 2 ∨ x = 1) ∧
      {x : ℝ | 2 * x ^ 5 + 6 * x ^ 3 + 3 ≤ 3 * x ^ 4 + 8 * x ^ 2} = Iic (-1 / 2) ∪ {1} := by
  have fac : ∀ x : ℝ, 2 * x ^ 5 - 3 * x ^ 4 + 6 * x ^ 3 - 8 * x ^ 2 + 3 =
      (x - 1) ^ 2 * (x + 1 / 2) * (2 * x ^ 2 + 6) := fun x => by ring
  refine ⟨fac, fun x => ?_, ?_⟩
  · have : 2 * x ^ 5 + 6 * x ^ 3 + 3 = 3 * x ^ 4 + 8 * x ^ 2 ↔
        (x - 1) ^ 2 * (x + 1 / 2) * (2 * x ^ 2 + 6) = 0 := by
      rw [← fac]; constructor <;> intro h <;> linarith
    rw [this]
    have h6 : 2 * x ^ 2 + 6 ≠ 0 := by positivity
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · right; have := pow_eq_zero_iff (two_ne_zero) |>.mp h2; linarith
        · left; linarith
      · exact absurd h1 h6
    · rintro (h | h) <;> subst h <;> norm_num
  · ext x
    simp only [mem_setOf_eq, mem_union, mem_Iic, mem_singleton_iff]
    have : 2 * x ^ 5 + 6 * x ^ 3 + 3 ≤ 3 * x ^ 4 + 8 * x ^ 2 ↔
        (x - 1) ^ 2 * (x + 1 / 2) * (2 * x ^ 2 + 6) ≤ 0 := by
      rw [← fac]; constructor <;> intro h <;> linarith
    rw [this]
    have h6 : 0 < 2 * x ^ 2 + 6 := by positivity
    constructor
    · intro h
      by_cases hx : x = 1
      · right; exact hx
      · left
        have hsq : 0 < (x - 1) ^ 2 := by
          have : x - 1 ≠ 0 := sub_ne_zero.mpr hx
          positivity
        by_contra hc
        push_neg at hc
        have : 0 < (x + 1 / 2) := by linarith
        have : 0 < (x - 1) ^ 2 * (x + 1 / 2) * (2 * x ^ 2 + 6) := by positivity
        linarith
    · rintro (h | h)
      · have : (x + 1 / 2) ≤ 0 := by linarith
        have h1 : (x - 1) ^ 2 * (x + 1 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) this
        exact mul_nonpos_of_nonpos_of_nonneg h1 h6.le
      · subst h; norm_num

/-- Stitz-Zeager Example 3.3.8: profit `P x = -5x³ + 35x² - 45x - 25 = -5(x-5)(x²-2x-1)` is positive on
`[0, 10.07]` exactly for `1 + √2 < x < 5`; also `P 2.41 < 0 < P 2.42`. -/
@[kb "stitzzeager2013" "Example 3.3.8, p. 290"]
theorem ex_3_3_8_profit :
    (∀ x : ℝ, -5 * x ^ 3 + 35 * x ^ 2 - 45 * x - 25 = -5 * ((x - 5) * (x ^ 2 - 2 * x - 1))) ∧
      (∀ x : ℝ, x ∈ Icc (0 : ℝ) (1007 / 100) →
        (0 < -5 * x ^ 3 + 35 * x ^ 2 - 45 * x - 25 ↔ 1 + Real.sqrt 2 < x ∧ x < 5)) ∧
      (-5 * (241 / 100 : ℝ) ^ 3 + 35 * (241 / 100) ^ 2 - 45 * (241 / 100) - 25 < 0) ∧
      (0 < -5 * (242 / 100 : ℝ) ^ 3 + 35 * (242 / 100) ^ 2 - 45 * (242 / 100) - 25) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have fac : ∀ x : ℝ, -5 * x ^ 3 + 35 * x ^ 2 - 45 * x - 25 = -5 * ((x - 5) * (x ^ 2 - 2 * x - 1)) :=
    fun x => by ring
  refine ⟨fac, fun x hx => ?_, by norm_num, by norm_num⟩
  rw [fac]
  have h2gt : 1 < Real.sqrt 2 := by nlinarith
  have h2lt : Real.sqrt 2 < 2 := by nlinarith
  have hq : x ^ 2 - 2 * x - 1 = (x - (1 + Real.sqrt 2)) * (x - (1 - Real.sqrt 2)) := by
    linear_combination h2
  rw [hq]
  obtain ⟨h0, h1⟩ := hx
  have hneg : 0 < x - (1 - Real.sqrt 2) ↔ 1 - Real.sqrt 2 < x := by constructor <;> intro h <;> linarith
  constructor
  · intro h
    by_contra hc
    rw [not_and_or] at hc
    rcases hc with hc | hc
    · push_neg at hc
      have hA : x - (1 + Real.sqrt 2) ≤ 0 := by linarith
      have hB : 0 < x - (1 - Real.sqrt 2) := by linarith
      have hD : (x - (1 + Real.sqrt 2)) * (x - (1 - Real.sqrt 2)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hA hB.le
      have hx5 : x - 5 < 0 := by linarith
      have := mul_nonneg_of_nonpos_of_nonpos hx5.le hD
      linarith
    · push_neg at hc
      have hA : 0 ≤ x - 5 := by linarith
      have hB : 0 < x - (1 + Real.sqrt 2) := by linarith
      have hC : 0 < x - (1 - Real.sqrt 2) := by linarith
      have := mul_nonneg hA (mul_pos hB hC).le
      linarith
  · rintro ⟨ha, hb⟩
    have hA : x - 5 < 0 := by linarith
    have hB : 0 < x - (1 + Real.sqrt 2) := by linarith
    have hC : 0 < x - (1 - Real.sqrt 2) := by linarith
    nlinarith [mul_pos hB hC, mul_neg_of_neg_of_pos hA (mul_pos hB hC)]

/-! ## Section 3.4 -/

/-- Stitz-Zeager Example 3.4.1(1-3): `(1-2i)-(3+4i) = -2-6i`, `(1-2i)(3+4i) = 11-2i`,
`(1-2i)/(3-4i) = 11/25 - (2/25) i`. -/
@[kb "stitzzeager2013" "Example 3.4.1, p. 300"]
theorem ex_3_4_1_a_arithmetic :
    ((1 : ℂ) - 2 * Complex.I) - (3 + 4 * Complex.I) = -2 - 6 * Complex.I ∧
      ((1 : ℂ) - 2 * Complex.I) * (3 + 4 * Complex.I) = 11 - 2 * Complex.I ∧
      ((1 : ℂ) - 2 * Complex.I) / (3 - 4 * Complex.I) = 11 / 25 - (2 / 25) * Complex.I := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hne : (3 : ℂ) - 4 * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  refine ⟨by ring, by linear_combination (-8 : ℂ) * hI, ?_⟩
  rw [div_eq_iff hne]
  linear_combination (-(8 : ℂ) / 25 * 1 + 0) * hI + (0 : ℂ) * hI

/-- Stitz-Zeager Example 3.4.1(4,5): `(i√3)(i√12) = -6`, while the real radical `√((-3)(-12)) = 6`. -/
@[kb "stitzzeager2013" "Example 3.4.1, p. 300"]
theorem ex_3_4_1_b_radicals :
    (Complex.I * Real.sqrt 3) * (Complex.I * Real.sqrt 12) = (-6 : ℂ) ∧
      Real.sqrt ((-3) * (-12)) = 6 := by
  constructor
  · have h : (Real.sqrt 3 : ℂ) * Real.sqrt 12 = 6 := by
      have : Real.sqrt 3 * Real.sqrt 12 = 6 := by
        rw [← Real.sqrt_mul (by norm_num), show (3 : ℝ) * 12 = 6 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      exact_mod_cast this
    calc (Complex.I * Real.sqrt 3) * (Complex.I * Real.sqrt 12)
        = Complex.I ^ 2 * ((Real.sqrt 3 : ℂ) * Real.sqrt 12) := by ring
      _ = -6 := by rw [Complex.I_sq, h]; ring
  · rw [show ((-3 : ℝ) * (-12)) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Stitz-Zeager Example 3.4.1(6): `(x - (1+2i))(x - (1-2i)) = x² - 2x + 5`. -/
@[kb "stitzzeager2013" "Example 3.4.1, p. 300"]
theorem ex_3_4_1_c_conjugate_pair (x : ℂ) :
    (x - (1 + 2 * Complex.I)) * (x - (1 - 2 * Complex.I)) = x ^ 2 - 2 * x + 5 := by
  linear_combination (-4 : ℂ) * Complex.I_sq

/-- Stitz-Zeager Example 3.4.2: `12x⁵ - 20x⁴ + 19x³ - 6x² - 2x + 1` factors over `ℝ` as
`12 (x-1/2)² (x+1/3)(x²-x+1)` and over `ℂ` with the zeros `(1 ± i√3)/2`. -/
@[kb "stitzzeager2013" "Example 3.4.2, p. 302"]
theorem ex_3_4_2_factorizations :
    (∀ x : ℝ, 12 * x ^ 5 - 20 * x ^ 4 + 19 * x ^ 3 - 6 * x ^ 2 - 2 * x + 1 =
        12 * (x - 1 / 2) ^ 2 * (x + 1 / 3) * (x ^ 2 - x + 1)) ∧
      (∀ x : ℂ, 12 * x ^ 5 - 20 * x ^ 4 + 19 * x ^ 3 - 6 * x ^ 2 - 2 * x + 1 =
        12 * (x - 1 / 2) ^ 2 * (x + 1 / 3) *
          (x - (1 + Complex.I * Real.sqrt 3) / 2) * (x - (1 - Complex.I * Real.sqrt 3) / 2)) := by
  refine ⟨fun x => by ring, fun x => ?_⟩
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hq : (x - (1 + Complex.I * Real.sqrt 3) / 2) * (x - (1 - Complex.I * Real.sqrt 3) / 2) =
      x ^ 2 - x + 1 := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-(1 : ℂ) / 4) * (Real.sqrt 3 : ℂ) ^ 2 * hI + (-(1 : ℂ) / 4 * (-1)) * h3
  calc 12 * x ^ 5 - 20 * x ^ 4 + 19 * x ^ 3 - 6 * x ^ 2 - 2 * x + 1
      = 12 * (x - 1 / 2) ^ 2 * (x + 1 / 3) * (x ^ 2 - x + 1) := by ring
    _ = _ := by rw [← hq]; ring

/-- Stitz-Zeager Example 3.4.3(1,3,4): `2+2i` is a zero of `x⁴ + 64`, which factors over `ℂ` through
`2±2i`, `-2±2i` and over `ℝ` as `(x²-4x+8)(x²+4x+8)`. -/
@[kb "stitzzeager2013" "Example 3.4.3, p. 304"]
theorem ex_3_4_3_x4_plus_64 :
    ((2 + 2 * Complex.I : ℂ) ^ 4 + 64 = 0) ∧
      (∀ x : ℝ, x ^ 4 + 64 = (x ^ 2 - 4 * x + 8) * (x ^ 2 + 4 * x + 8)) ∧
      (∀ x : ℂ, x ^ 4 + 64 = (x - (2 - 2 * Complex.I)) * (x - (2 + 2 * Complex.I)) *
        (x - (-2 + 2 * Complex.I)) * (x - (-2 - 2 * Complex.I))) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  refine ⟨?_, fun x => by ring, fun x => ?_⟩
  · have h4 : Complex.I ^ 4 = 1 := by
      calc Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
        _ = 1 := by rw [hI]; norm_num
    have h3 : Complex.I ^ 3 = -Complex.I := by
      calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
        _ = -Complex.I := by rw [hI]; ring
    have : (2 + 2 * Complex.I : ℂ) ^ 4 = 16 + 64 * Complex.I + 96 * Complex.I ^ 2 +
        64 * Complex.I ^ 3 + 16 * Complex.I ^ 4 := by ring
    rw [this, h3, hI, h4]; ring
  · have e1 : (x - (2 - 2 * Complex.I)) * (x - (2 + 2 * Complex.I)) = x ^ 2 - 4 * x + 8 := by
      linear_combination (-4 : ℂ) * hI
    have e2 : (x - (-2 + 2 * Complex.I)) * (x - (-2 - 2 * Complex.I)) = x ^ 2 + 4 * x + 8 := by
      linear_combination (-4 : ℂ) * hI
    calc x ^ 4 + 64 = (x ^ 2 - 4 * x + 8) * (x ^ 2 + 4 * x + 8) := by ring
      _ = _ := by rw [← e1, ← e2]; ring

/-- Stitz-Zeager Example 3.4.4: the polynomial `-9x⁴ + 6x³ - 82x² + 54x - 9 = -9 (x-1/3)² (x²+9)` has the double zero
`1/3` (multiplicity `2`), the zero `3i`, and tends to `-∞` in both directions. -/
@[kb "stitzzeager2013" "Example 3.4.4, p. 305"]
theorem ex_3_4_4_constructed_polynomial :
    (∀ x : ℝ, -9 * x ^ 4 + 6 * x ^ 3 - 82 * x ^ 2 + 54 * x - 9 = -9 * (x - 1 / 3) ^ 2 * (x ^ 2 + 9)) ∧
      (-9 * (3 * Complex.I) ^ 4 + 6 * (3 * Complex.I) ^ 3 - 82 * (3 * Complex.I) ^ 2 +
        54 * (3 * Complex.I) - 9 = 0) ∧
      (-9 * X ^ 4 + 6 * X ^ 3 - 82 * X ^ 2 + 54 * X - 9 : ℝ[X]).rootMultiplicity (1 / 3) = 2 ∧
      Filter.Tendsto (fun x : ℝ => -9 * x ^ 4 + 6 * x ^ 3 - 82 * x ^ 2 + 54 * x - 9)
        Filter.atTop Filter.atBot ∧
      Filter.Tendsto (fun x : ℝ => -9 * x ^ 4 + 6 * x ^ 3 - 82 * x ^ 2 + 54 * x - 9)
        Filter.atBot Filter.atBot := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hbound : ∀ x : ℝ, -9 * x ^ 4 + 6 * x ^ 3 - 82 * x ^ 2 + 54 * x - 9 ≤ -x ^ 2 + 9 := by
    intro x
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1 / 3), sq_nonneg (9 * x ^ 2 - 3 * x),
      sq_nonneg (x - 1), sq_nonneg (3 * x - 1), sq_nonneg (x ^ 2 - x / 3)]
  have hsq_top : Filter.Tendsto (fun x : ℝ => -x ^ 2 + 9) Filter.atTop Filter.atBot := by
    have h2 : Filter.Tendsto (fun x : ℝ => -x ^ 2) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero)
    exact Filter.tendsto_atBot_add_const_right _ (9 : ℝ) h2
  have hsq_bot : Filter.Tendsto (fun x : ℝ => -x ^ 2 + 9) Filter.atBot Filter.atBot := by
    have h1 : Filter.Tendsto (fun x : ℝ => |x| ^ 2) Filter.atBot Filter.atTop :=
      (Filter.tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero).comp Filter.tendsto_abs_atBot_atTop
    have h2 : Filter.Tendsto (fun x : ℝ => -x ^ 2) Filter.atBot Filter.atBot := by
      have := Filter.tendsto_neg_atTop_atBot.comp h1
      simpa [Function.comp_def, sq_abs] using this
    exact Filter.tendsto_atBot_add_const_right _ (9 : ℝ) h2
  refine ⟨fun x => by ring, ?_, ?_, ?_, ?_⟩
  · have h3 : (3 * Complex.I) ^ 2 = -9 := by linear_combination 9 * hI
    have h4 : (3 * Complex.I) ^ 4 = 81 := by
      calc (3 * Complex.I) ^ 4 = ((3 * Complex.I) ^ 2) ^ 2 := by ring
        _ = 81 := by rw [h3]; norm_num
    have h5 : (3 * Complex.I) ^ 3 = -27 * Complex.I := by
      calc (3 * Complex.I) ^ 3 = (3 * Complex.I) ^ 2 * (3 * Complex.I) := by ring
        _ = -27 * Complex.I := by rw [h3]; ring
    rw [h4, h5, h3]; ring
  · have e : (-9 * X ^ 4 + 6 * X ^ 3 - 82 * X ^ 2 + 54 * X - 9 : ℝ[X]) =
        (-9 * (X ^ 2 + 9)) * (X - C (1 / 3)) ^ 2 := by
      apply Polynomial.funext
      intro x; simp; ring
    rw [e]
    apply rootMultiplicity_of_factor
    simp; norm_num
  · exact Filter.tendsto_atBot_mono hbound hsq_top
  · exact Filter.tendsto_atBot_mono hbound hsq_bot

end UndergradKB.Precalculus.Course
