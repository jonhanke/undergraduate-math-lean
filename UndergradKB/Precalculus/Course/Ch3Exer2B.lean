import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 3.2 -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter

private lemma w7b_rm (q : ℝ[X]) (a : ℝ) (n : ℕ) (h : q.eval a ≠ 0) :
    (q * (X - C a) ^ n).rootMultiplicity a = n := by
  have hq : q ≠ 0 := fun h0 => h (by simp [h0])
  rw [rootMultiplicity_mul_X_sub_C_pow hq, rootMultiplicity_eq_zero (by simpa [IsRoot] using h)]
  simp

private lemma w7b_rm' (p q : ℝ[X]) (a : ℝ) (n : ℕ) (hp : p = q * (X - C a) ^ n)
    (h : q.eval a ≠ 0) : p.rootMultiplicity a = n := by
  rw [hp]; exact w7b_rm q a n h

/-! ## Section 3.2 -/

/-- Stitz-Zeager Exercise 3.2.5: `9x³ + 5 = (2x - 3)((9/2)x² + (27/4)x + 81/8) + 283/8`. -/
@[kb "stitzzeager2013" "Exercise 3.2.5, p. 277"]
theorem exer_3_2_5 (x : ℝ) :
    9 * x ^ 3 + 5 = (2 * x - 3) * (9 / 2 * x ^ 2 + 27 / 4 * x + 81 / 8) + 283 / 8 := by ring

/-- Stitz-Zeager Exercise 3.2.8: `x² - 5 = (x - 5)(x + 5) + 20`. -/
@[kb "stitzzeager2013" "Exercise 3.2.8, p. 277"]
theorem exer_3_2_8 (x : ℝ) : x ^ 2 - 5 = (x - 5) * (x + 5) + 20 := by ring

/-- Stitz-Zeager Exercise 3.2.14: `4x² - 1 = (x - 1/2)(4x + 2) + 0`. -/
@[kb "stitzzeager2013" "Exercise 3.2.14, p. 277"]
theorem exer_3_2_14 (x : ℝ) : 4 * x ^ 2 - 1 = (x - 1 / 2) * (4 * x + 2) + 0 := by ring

/-- Stitz-Zeager Exercise 3.2.15: `2x³ + x² + 2x + 1 = (x + 1/2)(2x² + 2) + 0`. -/
@[kb "stitzzeager2013" "Exercise 3.2.15, p. 277"]
theorem exer_3_2_15 (x : ℝ) : 2 * x ^ 3 + x ^ 2 + 2 * x + 1 = (x + 1 / 2) * (2 * x ^ 2 + 2) + 0 := by
  ring

/-- Stitz-Zeager Exercise 3.2.16: `3x³ - x + 4 = (x - 2/3)(3x² + 2x + 1/3) + 38/9`. -/
@[kb "stitzzeager2013" "Exercise 3.2.16, p. 277"]
theorem exer_3_2_16 (x : ℝ) :
    3 * x ^ 3 - x + 4 = (x - 2 / 3) * (3 * x ^ 2 + 2 * x + 1 / 3) + 38 / 9 := by ring

/-- Stitz-Zeager Exercise 3.2.17: `2x³ - 3x + 1 = (x - 1/2)(2x² + x - 5/2) - 1/4`. -/
@[kb "stitzzeager2013" "Exercise 3.2.17, p. 277"]
theorem exer_3_2_17 (x : ℝ) :
    2 * x ^ 3 - 3 * x + 1 = (x - 1 / 2) * (2 * x ^ 2 + x - 5 / 2) - 1 / 4 := by ring

/-- Stitz-Zeager Exercise 3.2.18: `4x⁴ - 12x³ + 13x² - 12x + 9 = (x - 3/2)(4x³ - 6x² + 4x - 6) + 0`. -/
@[kb "stitzzeager2013" "Exercise 3.2.18, p. 277"]
theorem exer_3_2_18 (x : ℝ) :
    4 * x ^ 4 - 12 * x ^ 3 + 13 * x ^ 2 - 12 * x + 9 =
      (x - 3 / 2) * (4 * x ^ 3 - 6 * x ^ 2 + 4 * x - 6) + 0 := by ring

/-- Stitz-Zeager Exercise 3.2.20: `x⁶ - 6x⁴ + 12x² - 8 = (x + √2)(x⁵ - √2x⁴ - 4x³ + 4√2x² + 4x - 4√2) + 0`. -/
@[kb "stitzzeager2013" "Exercise 3.2.20, p. 277"]
theorem exer_3_2_20 (x : ℝ) :
    x ^ 6 - 6 * x ^ 4 + 12 * x ^ 2 - 8 =
      (x + Real.sqrt 2) * (x ^ 5 - Real.sqrt 2 * x ^ 4 - 4 * x ^ 3 + 4 * Real.sqrt 2 * x ^ 2 +
        4 * x - 4 * Real.sqrt 2) + 0 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination (x ^ 4 - 4 * x ^ 2 + 4) * h

/-- Stitz-Zeager Exercise 3.2.22: `p(x) = 4x² - 33x - 180` has `p(12) = 0` and
`p(x) = (x - 12)(4x + 15)`. -/
@[kb "stitzzeager2013" "Exercise 3.2.22, p. 277"]
theorem exer_3_2_22 (p : ℝ → ℝ) (hp : ∀ x, p x = 4 * x ^ 2 - 33 * x - 180) :
    p 12 = 0 ∧ ∀ x, p x = (x - 12) * (4 * x + 15) := by
  refine ⟨by rw [hp]; norm_num, fun x => by rw [hp]; ring⟩

/-- Stitz-Zeager Exercise 3.2.23: `p(x) = 2x³ - x + 6` has `p(-3) = -45`. -/
@[kb "stitzzeager2013" "Exercise 3.2.23, p. 277"]
theorem exer_3_2_23 (p : ℝ → ℝ) (hp : ∀ x, p x = 2 * x ^ 3 - x + 6) : p (-3) = -45 := by
  rw [hp]; norm_num

/-- Stitz-Zeager Exercise 3.2.24: `p(x) = x³ + 2x² + 3x + 4` has `p(-1) = 2`. -/
@[kb "stitzzeager2013" "Exercise 3.2.24, p. 277"]
theorem exer_3_2_24 (p : ℝ → ℝ) (hp : ∀ x, p x = x ^ 3 + 2 * x ^ 2 + 3 * x + 4) : p (-1) = 2 := by
  rw [hp]; norm_num

/-- Stitz-Zeager Exercise 3.2.25: `p(x) = 3x³ - 6x² + 4x - 8` has `p(2) = 0` and
`p(x) = (x - 2)(3x² + 4)`. -/
@[kb "stitzzeager2013" "Exercise 3.2.25, p. 277"]
theorem exer_3_2_25 (p : ℝ → ℝ) (hp : ∀ x, p x = 3 * x ^ 3 - 6 * x ^ 2 + 4 * x - 8) :
    p 2 = 0 ∧ ∀ x, p x = (x - 2) * (3 * x ^ 2 + 4) := by
  refine ⟨by rw [hp]; norm_num, fun x => by rw [hp]; ring⟩

/-- Stitz-Zeager Exercise 3.2.26: `p(x) = 8x³ + 12x² + 6x + 1` has `p(-1/2) = 0` and
`p(x) = (x + 1/2)(8x² + 8x + 2)`. -/
@[kb "stitzzeager2013" "Exercise 3.2.26, p. 277"]
theorem exer_3_2_26 (p : ℝ → ℝ) (hp : ∀ x, p x = 8 * x ^ 3 + 12 * x ^ 2 + 6 * x + 1) :
    p (-1 / 2) = 0 ∧ ∀ x, p x = (x + 1 / 2) * (8 * x ^ 2 + 8 * x + 2) := by
  refine ⟨by rw [hp]; norm_num, fun x => by rw [hp]; ring⟩

/-- Stitz-Zeager Exercise 3.2.27: `p(x) = x⁴ - 2x² + 4` has `p(3/2) = 73/16`. -/
@[kb "stitzzeager2013" "Exercise 3.2.27, p. 277"]
theorem exer_3_2_27 (p : ℝ → ℝ) (hp : ∀ x, p x = x ^ 4 - 2 * x ^ 2 + 4) : p (3 / 2) = 73 / 16 := by
  rw [hp]; norm_num

/-- Stitz-Zeager Exercise 3.2.28: `p(x) = 6x⁴ - x² + 2` has `p(-2/3) = 74/27`. -/
@[kb "stitzzeager2013" "Exercise 3.2.28, p. 277"]
theorem exer_3_2_28 (p : ℝ → ℝ) (hp : ∀ x, p x = 6 * x ^ 4 - x ^ 2 + 2) : p (-2 / 3) = 74 / 27 := by
  rw [hp]; norm_num

/-- Stitz-Zeager Exercise 3.2.29: `p(x) = x⁴ + x³ - 6x² - 7x - 7` has `p(-√7) = 0` and
`p(x) = (x + √7)(x³ + (1 - √7)x² + (1 - √7)x - √7)`. -/
@[kb "stitzzeager2013" "Exercise 3.2.29, p. 277"]
theorem exer_3_2_29 (p : ℝ → ℝ) (hp : ∀ x, p x = x ^ 4 + x ^ 3 - 6 * x ^ 2 - 7 * x - 7) :
    p (-Real.sqrt 7) = 0 ∧ ∀ x, p x = (x + Real.sqrt 7) *
      (x ^ 3 + (1 - Real.sqrt 7) * x ^ 2 + (1 - Real.sqrt 7) * x - Real.sqrt 7) := by
  have h : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, fun x => ?_⟩
  · rw [hp]; linear_combination (Real.sqrt 7 ^ 2 - Real.sqrt 7 + 1) * h
  · rw [hp]; linear_combination (x ^ 2 + x + 1) * h

/-- Stitz-Zeager Exercise 3.2.39: `125x⁵ - 275x⁴ - 2265x³ - 3213x² - 1728x - 324 =
125(x + 3/5)³(x + 2)(x - 6)`, so `-3/5` is a zero of multiplicity `3`. -/
@[kb "stitzzeager2013" "Exercise 3.2.39, p. 278"]
theorem exer_3_2_39 (p : ℝ[X])
    (hp : p = 125 * X ^ 5 - 275 * X ^ 4 - 2265 * X ^ 3 - 3213 * X ^ 2 - 1728 * X - 324) :
    p = 125 * (X + C (3 / 5 : ℝ)) ^ 3 * (X + 2) * (X - 6) ∧
      p.rootMultiplicity (-3 / 5) = 3 := by
  have hc : (C (3 / 5 : ℝ)) * 5 = (3 : ℝ[X]) := by
    rw [← map_ofNat C 5, ← C_mul, ← map_ofNat C 3]; norm_num
  have e : p = 125 * (X + C (3 / 5 : ℝ)) ^ 3 * (X + 2) * (X - 6) := by
    rw [hp]
    linear_combination (-((3 * (5 * X + 3) ^ 2 + 3 * (5 * X + 3) * (5 * C (3 / 5 : ℝ) - 3) +
      (5 * C (3 / 5 : ℝ) - 3) ^ 2) * ((X + 2) * (X - 6)))) * hc
  exact ⟨e, by
    refine w7b_rm' p (125 * (X + 2) * (X - 6)) (-3 / 5) 3 ?_ (by simp; norm_num)
    rw [e]
    have : (C (-3 / 5 : ℝ)) = -C (3 / 5 : ℝ) := by rw [← C_neg]; norm_num
    rw [this]; simp only [sub_neg_eq_add]; ring⟩

private lemma w7b_top_neg (p : ℝ[X]) (hd : 0 < p.natDegree) (hl : p.leadingCoeff < 0) :
    Tendsto (fun x : ℝ => p.eval x) atTop atBot := by
  apply Polynomial.tendsto_atBot_of_leadingCoeff_nonpos
  · have hp : p ≠ 0 := fun h => by rw [h] at hl; simp at hl
    rw [degree_eq_natDegree hp]; exact_mod_cast hd
  · exact hl.le

/-- Stitz-Zeager Exercise 3.2.42: `p(x) = -5(x - 1)(x - 3)²` has degree `3`, leading term `-5x³`,
zeros `1` (simple) and `3` (multiplicity `2`), and no others. -/
@[kb "stitzzeager2013" "Exercise 3.2.42, p. 278"]
theorem exer_3_2_42 (p : ℝ[X]) (hp : p = -5 * (X - 1) * (X - 3) ^ 2) :
    p.natDegree = 3 ∧ p.leadingCoeff = -5 ∧ p.rootMultiplicity 1 = 1 ∧ p.rootMultiplicity 3 = 2 ∧
      ∀ x : ℝ, p.eval x = 0 ↔ x = 1 ∨ x = 3 := by
  have e : p = -5 * X ^ 3 + 35 * X ^ 2 - 75 * X + 45 := by rw [hp]; ring
  have hd : p.natDegree = 3 := by rw [e]; compute_degree!
  refine ⟨hd, by rw [leadingCoeff, hd, e]; compute_degree!,
    w7b_rm' p (-5 * (X - 3) ^ 2) 1 1 ?_ (by simp; norm_num),
    w7b_rm' p (-5 * (X - 1)) 3 2 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [hp]; simp only [map_one]; ring
  · rw [hp]; simp only [map_ofNat]
  · simp [hp, sub_eq_zero]

/-- Stitz-Zeager Exercise 3.2.43: `p(x) = 7(x + 3)²(x - 3)(x - 6)` has leading term `7x⁴`, zeros
`±3` and `6`, and `(-3, 0)` is a local minimum of its graph. -/
@[kb "stitzzeager2013" "Exercise 3.2.43, p. 278"]
theorem exer_3_2_43 (p : ℝ[X]) (hp : p = 7 * (X + 3) ^ 2 * (X - 3) * (X - 6)) :
    p.natDegree = 4 ∧ p.leadingCoeff = 7 ∧ (∀ x : ℝ, p.eval x = 0 ↔ x = -3 ∨ x = 3 ∨ x = 6) ∧
      (∀ x : ℝ, |x + 3| < 1 → p.eval (-3) ≤ p.eval x) := by
  have e : p = 7 * X ^ 4 - 21 * X ^ 3 - 189 * X ^ 2 + 189 * X + 1134 := by rw [hp]; ring
  have hd : p.natDegree = 4 := by rw [e]; compute_degree!
  have hf : ∀ x : ℝ, p.eval x = 7 * ((x + 3) ^ 2 * ((x - 3) * (x - 6))) := by
    intro x; simp [hp]; ring
  refine ⟨hd, by rw [leadingCoeff, hd, e]; compute_degree!, fun x => ?_, fun x hx => ?_⟩
  · rw [hf]
    constructor
    · intro h
      have h' : (x + 3) ^ 2 * ((x - 3) * (x - 6)) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h1 | h1
      · left; have := pow_eq_zero_iff (two_ne_zero) |>.mp h1; linarith
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · right; left; linarith
        · right; right; linarith
    · rintro (h | h | h) <;> rw [h] <;> norm_num
  · rw [hf, hf]
    rw [abs_lt] at hx
    have a1 : x - 3 < 0 := by linarith
    have a3 : x - 6 < 0 := by linarith
    have := mul_pos_of_neg_of_neg a1 a3
    have h1 : 0 ≤ (x + 3) ^ 2 * ((x - 3) * (x - 6)) := mul_nonneg (sq_nonneg _) this.le
    norm_num
    linarith

/-- Stitz-Zeager Exercise 3.2.45: for `a < 0`, `p(x) = a(x + 6)²(x - 1)(x - 117)` has degree `4`,
tends to `-∞` as `x → ∞`, has exactly the three zeros `-6`, `1`, `117`, and crosses the x-axis at `1`
(a simple zero). -/
@[kb "stitzzeager2013" "Exercise 3.2.45, p. 278"]
theorem exer_3_2_45 (a : ℝ) (ha : a < 0) (p : ℝ[X])
    (hp : p = C a * (X + 6) ^ 2 * (X - 1) * (X - 117)) :
    p.natDegree = 4 ∧ Tendsto (fun x : ℝ => p.eval x) atTop atBot ∧
      (∀ x : ℝ, p.eval x = 0 ↔ x = -6 ∨ x = 1 ∨ x = 117) ∧ p.rootMultiplicity 1 = 1 := by
  have ha0 : a ≠ 0 := ha.ne
  have e : p = C a * (X ^ 4 - 106 * X ^ 3 - 1263 * X ^ 2 - 2844 * X + 4212) := by
    rw [hp]; ring
  have hd : p.natDegree = 4 := by rw [e]; compute_degree!
  have hl : p.leadingCoeff = a := by rw [leadingCoeff, hd, e]; compute_degree!
  refine ⟨hd, w7b_top_neg p (by omega) (by rw [hl]; exact ha), fun x => ?_,
    w7b_rm' p (C a * (X + 6) ^ 2 * (X - 117)) 1 1 ?_ (by simp [ha0]; norm_num)⟩
  · simp [hp, ha0, sub_eq_zero, add_eq_zero_iff_eq_neg]
    tauto
  · rw [hp]; simp only [map_one]; ring

/-- Stitz-Zeager Exercise 3.2.44: `p(x) = -(x + 2)²(x - 3)(x + 3)(x - 4)` has leading term `-x⁵`,
zeros `±3`, `-2`, `4`, and `(-2, 0)` is a local maximum of its graph. -/
@[kb "stitzzeager2013" "Exercise 3.2.44, p. 278"]
theorem exer_3_2_44 (p : ℝ[X]) (hp : p = -(X + 2) ^ 2 * (X - 3) * (X + 3) * (X - 4)) :
    p.natDegree = 5 ∧ p.leadingCoeff = -1 ∧
      (∀ x : ℝ, p.eval x = 0 ↔ x = -3 ∨ x = -2 ∨ x = 3 ∨ x = 4) ∧
      (∀ x : ℝ, |x + 2| < 1 → p.eval x ≤ p.eval (-2)) := by
  have e : p = -X ^ 5 + 21 * X ^ 3 + 16 * X ^ 2 - 108 * X - 144 := by rw [hp]; ring
  have hd : p.natDegree = 5 := by rw [e]; compute_degree!
  have hf : ∀ x : ℝ, p.eval x = -((x + 2) ^ 2 * (x - 3) * (x + 3) * (x - 4)) := by
    intro x; simp [hp]
  refine ⟨hd, by rw [leadingCoeff, hd, e]; compute_degree!, fun x => ?_, fun x hx => ?_⟩
  · rw [hf]
    constructor
    · intro h
      have h' : (x + 2) ^ 2 * (x - 3) * (x + 3) * (x - 4) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · rcases mul_eq_zero.mp h2 with h3 | h3
          · right; left; have := pow_eq_zero_iff (two_ne_zero) |>.mp h3; linarith
          · right; right; left; linarith
        · left; linarith
      · right; right; right; linarith
    · rintro (h | h | h | h) <;> rw [h] <;> norm_num
  · rw [hf, hf]
    rw [abs_lt] at hx
    have h1 : 0 ≤ (x + 2) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (x - 3) * (x + 3) * (x - 4) := by
      have a1 : x - 3 < 0 := by linarith
      have a2 : 0 < x + 3 := by linarith
      have a3 : x - 4 < 0 := by linarith
      have := mul_pos_of_neg_of_neg a1 a3
      nlinarith
    have : (x + 2) ^ 2 * (x - 3) * (x + 3) * (x - 4) = (x + 2) ^ 2 * ((x - 3) * (x + 3) * (x - 4)) := by
      ring
    rw [this]; norm_num
    exact mul_nonneg h1 h2

end UndergradKB.Precalculus.Course
