import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): exercises with the book's answers, Sections 3.1-3.2 -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter

private lemma aux_rm (q : ℝ[X]) (a : ℝ) (n : ℕ) (h : q.eval a ≠ 0) :
    (q * (X - C a) ^ n).rootMultiplicity a = n := by
  have hq : q ≠ 0 := fun h0 => h (by simp [h0])
  rw [rootMultiplicity_mul_X_sub_C_pow hq, rootMultiplicity_eq_zero (by simpa [IsRoot] using h)]
  simp

private lemma aux_rm' (p q : ℝ[X]) (a : ℝ) (n : ℕ) (hp : p = q * (X - C a) ^ n)
    (h : q.eval a ≠ 0) : p.rootMultiplicity a = n := by
  rw [hp]; exact aux_rm q a n h

/-! ## Section 3.1 -/

/-- Stitz-Zeager Exercise 3.1.1: `f(x) = 4 - x - 3x²` has degree `2`, leading coefficient `-3` and
constant term `4`, and tends to `-∞` at both ends. -/
@[kb "stitzzeager2013" "Exercise 3.1.1, p. 258"]
theorem exer_3_1_1 (f : ℝ[X]) (hf : f = 4 - X - 3 * X ^ 2) :
    f.natDegree = 2 ∧ f.leadingCoeff = -3 ∧ f.coeff 0 = 4 ∧
    Tendsto (fun x : ℝ => f.eval x) atBot atBot ∧ Tendsto (fun x : ℝ => f.eval x) atTop atBot := by
  subst hf
  have hd : (4 - X - 3 * X ^ 2 : ℝ[X]).natDegree = 2 := by compute_degree!
  refine ⟨hd, ?_, by rw [coeff_zero_eq_eval_zero]; simp, ?_, ?_⟩
  · rw [leadingCoeff, hd]; compute_degree!
  · rw [tendsto_atBot_atBot]
    refine fun b => ⟨-(|b| + 4), fun a ha => ?_⟩
    simp only [eval_sub, eval_ofNat, eval_X, eval_mul, eval_pow]
    nlinarith [neg_abs_le b, le_abs_self b, abs_nonneg b]
  · rw [tendsto_atTop_atBot]
    refine fun b => ⟨|b| + 4, fun a ha => ?_⟩
    simp only [eval_sub, eval_ofNat, eval_X, eval_mul, eval_pow]
    nlinarith [neg_abs_le b, le_abs_self b, abs_nonneg b]

/-- Stitz-Zeager Exercise 3.1.2: `g(x) = 3x⁵ - 2x² + x + 1` has degree `5`, leading coefficient `3`,
constant term `1`, and tends to `+∞` as `x → +∞`. -/
@[kb "stitzzeager2013" "Exercise 3.1.2, p. 258"]
theorem exer_3_1_2 (g : ℝ[X]) (hg : g = 3 * X ^ 5 - 2 * X ^ 2 + X + 1) :
    g.natDegree = 5 ∧ g.leadingCoeff = 3 ∧ g.coeff 0 = 1 ∧
    Tendsto (fun x : ℝ => g.eval x) atTop atTop := by
  subst hg
  have hd : (3 * X ^ 5 - 2 * X ^ 2 + X + 1 : ℝ[X]).natDegree = 5 := by compute_degree!
  have hl : (3 * X ^ 5 - 2 * X ^ 2 + X + 1 : ℝ[X]).leadingCoeff = 3 := by
    rw [leadingCoeff, hd]; compute_degree!
  refine ⟨hd, hl, by rw [coeff_zero_eq_eval_zero]; simp, ?_⟩
  apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
  · rw [degree_eq_natDegree (by intro h; rw [h] at hd; simp at hd), hd]; norm_num
  · rw [hl]; norm_num

/-- Stitz-Zeager Exercise 3.1.7: `P(x) = (x-1)(x-2)(x-3)(x-4)` has degree `4`, leading coefficient `1`
and constant term `24`. -/
@[kb "stitzzeager2013" "Exercise 3.1.7, p. 258"]
theorem exer_3_1_7 (P : ℝ[X]) (hP : P = (X - 1) * (X - 2) * (X - 3) * (X - 4)) :
    P.natDegree = 4 ∧ P.leadingCoeff = 1 ∧ P.coeff 0 = 24 := by
  have e : P = X ^ 4 - 10 * X ^ 3 + 35 * X ^ 2 - 50 * X + 24 := by rw [hP]; ring
  have hd : P.natDegree = 4 := by rw [e]; compute_degree!
  refine ⟨hd, ?_, by rw [coeff_zero_eq_eval_zero, hP]; simp; norm_num⟩
  rw [leadingCoeff, hd, e]; compute_degree!

/-- Stitz-Zeager Exercise 3.1.8: `p(t) = -t²(3 - 5t)(t² + t + 4)` has degree `5`, leading
coefficient `5` and constant term `0`. -/
@[kb "stitzzeager2013" "Exercise 3.1.8, p. 258"]
theorem exer_3_1_8 (p : ℝ[X]) (hp : p = -X ^ 2 * (3 - 5 * X) * (X ^ 2 + X + 4)) :
    p.natDegree = 5 ∧ p.leadingCoeff = 5 ∧ p.coeff 0 = 0 := by
  have e : p = 5 * X ^ 5 + 2 * X ^ 4 + 17 * X ^ 3 - 12 * X ^ 2 := by rw [hp]; ring
  have hd : p.natDegree = 5 := by rw [e]; compute_degree!
  refine ⟨hd, ?_, by rw [coeff_zero_eq_eval_zero, hp]; simp⟩
  rw [leadingCoeff, hd, e]; compute_degree!

/-- Stitz-Zeager Exercise 3.1.9: `f(x) = -2x³(x+1)(x+2)²` has degree `6`, leading coefficient `-2`
and constant term `0`. -/
@[kb "stitzzeager2013" "Exercise 3.1.9, p. 258"]
theorem exer_3_1_9 (f : ℝ[X]) (hf : f = -2 * X ^ 3 * (X + 1) * (X + 2) ^ 2) :
    f.natDegree = 6 ∧ f.leadingCoeff = -2 ∧ f.coeff 0 = 0 := by
  have e : f = -2 * X ^ 6 - 10 * X ^ 5 - 16 * X ^ 4 - 8 * X ^ 3 := by rw [hf]; ring
  have hd : f.natDegree = 6 := by rw [e]; compute_degree!
  refine ⟨hd, ?_, by rw [coeff_zero_eq_eval_zero, hf]; simp⟩
  rw [leadingCoeff, hd, e]; compute_degree!

/-- Stitz-Zeager Exercise 3.1.11: `a(x) = x(x+2)²` has real zeros `0` (multiplicity `1`) and `-2`
(multiplicity `2`), and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.11, p. 258"]
theorem exer_3_1_11 (a : ℝ[X]) (ha : a = X * (X + 2) ^ 2) :
    a.rootMultiplicity 0 = 1 ∧ a.rootMultiplicity (-2) = 2 ∧
      ∀ x : ℝ, a.eval x = 0 ↔ x = 0 ∨ x = -2 := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · have := aux_rm ((X + 2) ^ 2) 0 1 (by simp)
    rw [ha]; simpa [mul_comm] using this
  · have := aux_rm X (-2) 2 (by simp)
    rw [ha]; simpa [sub_neg_eq_add, mul_comm, map_ofNat C 2] using this
  · simp [ha, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.1.12: `g(x) = x(x+2)³` has zeros `0` (multiplicity `1`) and `-2`
(multiplicity `3`), and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.12, p. 258"]
theorem exer_3_1_12 (g : ℝ[X]) (hg : g = X * (X + 2) ^ 3) :
    g.rootMultiplicity 0 = 1 ∧ g.rootMultiplicity (-2) = 3 ∧
      ∀ x : ℝ, g.eval x = 0 ↔ x = 0 ∨ x = -2 := by
  refine ⟨aux_rm' _ ((X + 2) ^ 3) 0 1 ?_ (by simp), aux_rm' _ X (-2) 3 ?_ (by simp), fun x => ?_⟩
  · rw [hg]; simp only [map_zero]; ring
  · rw [hg]; simp only [map_neg, map_ofNat]; ring
  · simp [hg, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.1.13: `f(x) = -2(x-2)²(x+1)` has zeros `2` (multiplicity `2`) and `-1`
(multiplicity `1`), and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.13, p. 258"]
theorem exer_3_1_13 (f : ℝ[X]) (hf : f = -2 * (X - 2) ^ 2 * (X + 1)) :
    f.rootMultiplicity 2 = 2 ∧ f.rootMultiplicity (-1) = 1 ∧
      ∀ x : ℝ, f.eval x = 0 ↔ x = 2 ∨ x = -1 := by
  refine ⟨aux_rm' _ (-2 * (X + 1)) 2 2 ?_ (by simp; norm_num),
    aux_rm' _ (-2 * (X - 2) ^ 2) (-1) 1 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [hf]; simp only [map_ofNat]; ring
  · rw [hf]; simp only [map_neg, map_one]; ring
  · simp [hf, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.1.15: `F(x) = x³(x+2)²` has zeros `0` (multiplicity `3`) and `-2`
(multiplicity `2`), and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.15, p. 258"]
theorem exer_3_1_15 (F : ℝ[X]) (hF : F = X ^ 3 * (X + 2) ^ 2) :
    F.rootMultiplicity 0 = 3 ∧ F.rootMultiplicity (-2) = 2 ∧
      ∀ x : ℝ, F.eval x = 0 ↔ x = 0 ∨ x = -2 := by
  refine ⟨aux_rm' _ ((X + 2) ^ 2) 0 3 ?_ (by simp), aux_rm' _ (X ^ 3) (-2) 2 ?_ (by simp),
    fun x => ?_⟩
  · rw [hF]; simp only [map_zero]; ring
  · rw [hF]; simp only [map_neg, map_ofNat]; ring
  · simp [hF, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.1.16: `P(x) = (x-1)(x-2)(x-3)(x-4)` has the four simple zeros
`1, 2, 3, 4` and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.16, p. 258"]
theorem exer_3_1_16 (P : ℝ[X]) (hP : P = (X - 1) * (X - 2) * (X - 3) * (X - 4)) :
    P.rootMultiplicity 1 = 1 ∧ P.rootMultiplicity 2 = 1 ∧ P.rootMultiplicity 3 = 1 ∧
      P.rootMultiplicity 4 = 1 ∧ ∀ x : ℝ, P.eval x = 0 ↔ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  refine ⟨aux_rm' _ ((X - 2) * (X - 3) * (X - 4)) 1 1 ?_ (by simp; norm_num),
    aux_rm' _ ((X - 1) * (X - 3) * (X - 4)) 2 1 ?_ (by simp; norm_num),
    aux_rm' _ ((X - 1) * (X - 2) * (X - 4)) 3 1 ?_ (by simp; norm_num),
    aux_rm' _ ((X - 1) * (X - 2) * (X - 3)) 4 1 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [hP]; simp only [map_one]; ring
  · rw [hP]; simp only [map_ofNat]; ring
  · rw [hP]; simp only [map_ofNat]; ring
  · rw [hP]; simp only [map_ofNat]; ring
  · simp [hP, sub_eq_zero]; tauto

/-- Stitz-Zeager Exercise 3.1.17: `Q(x) = (x+5)²(x-3)⁴` has zeros `-5` (multiplicity `2`) and `3`
(multiplicity `4`), and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.17, p. 258"]
theorem exer_3_1_17 (Q : ℝ[X]) (hQ : Q = (X + 5) ^ 2 * (X - 3) ^ 4) :
    Q.rootMultiplicity (-5) = 2 ∧ Q.rootMultiplicity 3 = 4 ∧
      ∀ x : ℝ, Q.eval x = 0 ↔ x = -5 ∨ x = 3 := by
  refine ⟨aux_rm' _ ((X - 3) ^ 4) (-5) 2 ?_ (by simp; norm_num),
    aux_rm' _ ((X + 5) ^ 2) 3 4 ?_ (by simp; norm_num), fun x => ?_⟩
  · rw [hQ]; simp only [map_neg, map_ofNat]; ring
  · rw [hQ]; simp only [map_ofNat]
  · simp [hQ, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Stitz-Zeager Exercise 3.1.18: `h(x) = x²(x-2)²(x+2)²` has the zeros `-2`, `0`, `2`, each of
multiplicity `2`, and no others. -/
@[kb "stitzzeager2013" "Exercise 3.1.18, p. 258"]
theorem exer_3_1_18 (h : ℝ[X]) (hh : h = X ^ 2 * (X - 2) ^ 2 * (X + 2) ^ 2) :
    h.rootMultiplicity (-2) = 2 ∧ h.rootMultiplicity 0 = 2 ∧ h.rootMultiplicity 2 = 2 ∧
      ∀ x : ℝ, h.eval x = 0 ↔ x = -2 ∨ x = 0 ∨ x = 2 := by
  refine ⟨aux_rm' _ (X ^ 2 * (X - 2) ^ 2) (-2) 2 ?_ (by simp; norm_num),
    aux_rm' _ ((X - 2) ^ 2 * (X + 2) ^ 2) 0 2 ?_ (by simp),
    aux_rm' _ (X ^ 2 * (X + 2) ^ 2) 2 2 ?_ (by simp), fun x => ?_⟩
  · rw [hh]; simp only [map_neg, map_ofNat]; ring
  · rw [hh]; simp only [map_zero]; ring
  · rw [hh]; simp only [map_ofNat]; ring
  · simp [hh, sub_eq_zero, add_eq_zero_iff_eq_neg]; tauto

/-- Stitz-Zeager Exercise 3.1.19: `H(t) = (3 - t)(t² + 1)` has the single real zero `t = 3`. -/
@[kb "stitzzeager2013" "Exercise 3.1.19, p. 258"]
theorem exer_3_1_19 (t : ℝ) : (3 - t) * (t ^ 2 + 1) = 0 ↔ t = 3 := by
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · nlinarith [sq_nonneg t]
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 3.1.20: `Z(b) = b(42 - b²)` has the three simple real zeros
`-√42`, `0`, `√42`. -/
@[kb "stitzzeager2013" "Exercise 3.1.20, p. 258"]
theorem exer_3_1_20 (b : ℝ) :
    b * (42 - b ^ 2) = 0 ↔ b = -√42 ∨ b = 0 ∨ b = √42 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 42 by norm_num)
  constructor
  · intro hb
    rcases mul_eq_zero.1 hb with h0 | h0
    · right; left; exact h0
    · have : (b - √42) * (b + √42) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h1 | h1
      · right; right; linarith
      · left; linarith
  · rintro (rfl | rfl | rfl)
    · rw [neg_sq, h]; ring
    · norm_num
    · rw [h]; ring

/-- Stitz-Zeager Exercise 3.1.22: the range of `g(x) = (x+2)⁴ + 1` is `[1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 3.1.22, p. 258"]
theorem exer_3_1_22 : Set.range (fun x : ℝ => (x + 2) ^ 4 + 1) = Set.Ici 1 := by
  ext y
  simp only [Set.mem_range, Set.mem_Ici]
  constructor
  · rintro ⟨x, rfl⟩
    have : 0 ≤ (x + 2) ^ 4 := by positivity
    linarith
  · intro hy
    have h0 : 0 ≤ y - 1 := by linarith
    refine ⟨√(√(y - 1)) - 2, ?_⟩
    have h1 : √(√(y - 1)) ^ 2 = √(y - 1) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : √(y - 1) ^ 2 = y - 1 := Real.sq_sqrt h0
    have : (√(√(y - 1)) - 2 + 2) ^ 4 = y - 1 := by
      rw [sub_add_cancel, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h1, h2]
    linarith

/-- Stitz-Zeager Exercise 3.1.23: the range of `g(x) = 2 - 3(x-1)⁴` is `(-∞, 2]`. -/
@[kb "stitzzeager2013" "Exercise 3.1.23, p. 258"]
theorem exer_3_1_23 : Set.range (fun x : ℝ => 2 - 3 * (x - 1) ^ 4) = Set.Iic 2 := by
  ext y
  simp only [Set.mem_range, Set.mem_Iic]
  constructor
  · rintro ⟨x, rfl⟩
    have : 0 ≤ (x - 1) ^ 4 := by positivity
    linarith
  · intro hy
    have h0 : 0 ≤ (2 - y) / 3 := by linarith
    refine ⟨√(√((2 - y) / 3)) + 1, ?_⟩
    have h1 : √(√((2 - y) / 3)) ^ 2 = √((2 - y) / 3) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : √((2 - y) / 3) ^ 2 = (2 - y) / 3 := Real.sq_sqrt h0
    have : (√(√((2 - y) / 3)) + 1 - 1) ^ 4 = (2 - y) / 3 := by
      rw [add_sub_cancel_right, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h1, h2]
    show 2 - 3 * (√(√((2 - y) / 3)) + 1 - 1) ^ 4 = y
    rw [this]; ring

/-- Stitz-Zeager Exercise 3.1.27: `f(x) = x³ - 9x + 5` has a real zero in each of `[-4,-3]`, `[0,1]`
and `[2,3]` (by the Intermediate Value Theorem). -/
@[kb "stitzzeager2013" "Exercise 3.1.27, p. 258"]
theorem exer_3_1_27 :
    (∃ c ∈ Set.Icc (-4 : ℝ) (-3), c ^ 3 - 9 * c + 5 = 0) ∧
    (∃ c ∈ Set.Icc (0 : ℝ) 1, c ^ 3 - 9 * c + 5 = 0) ∧
    (∃ c ∈ Set.Icc (2 : ℝ) 3, c ^ 3 - 9 * c + 5 = 0) := by
  have hc : Continuous (fun x : ℝ => x ^ 3 - 9 * x + 5) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc (show (-4 : ℝ) ≤ -3 by norm_num) hc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc ((-4 : ℝ) ^ 3 - 9 * (-4) + 5) ((-3 : ℝ) ^ 3 - 9 * (-3) + 5) by
        constructor <;> norm_num)
    exact ⟨c, hc1, hc2⟩
  · obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc ((1 : ℝ) ^ 3 - 9 * 1 + 5) ((0 : ℝ) ^ 3 - 9 * 0 + 5) by
        constructor <;> norm_num)
    exact ⟨c, hc1, hc2⟩
  · obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc (show (2 : ℝ) ≤ 3 by norm_num) hc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc ((2 : ℝ) ^ 3 - 9 * 2 + 5) ((3 : ℝ) ^ 3 - 9 * 3 + 5) by
        constructor <;> norm_num)
    exact ⟨c, hc1, hc2⟩

/-- Stitz-Zeager Exercise 3.1.30: the profit `R(x) - C(x)` with `R(x) = -5x³ + 35x² + 155x` and
`C(x) = 200x + 25` is `-5x³ + 35x² - 45x - 25`. -/
@[kb "stitzzeager2013" "Exercise 3.1.30, p. 259"]
theorem exer_3_1_30 (x : ℝ) :
    (-5 * x ^ 3 + 35 * x ^ 2 + 155 * x) - (200 * x + 25) = -5 * x ^ 3 + 35 * x ^ 2 - 45 * x - 25 := by
  ring

/-- Stitz-Zeager Exercise 3.1.33: for a parcel with length plus girth equal to `130` and square face
of side `x`, the volume is `x²(130 - 4x) = -4x³ + 130x²`, maximal (`549250/27 ≈ 20342.59`) exactly
at `x = 65/3` (box `65/3 × 65/3 × 130/3`); with `108` instead of `130` the maximum is `11664` at
`x = 18` (box `18 × 18 × 36`). -/
@[kb "stitzzeager2013" "Exercise 3.1.33, p. 259"]
theorem exer_3_1_33 (x : ℝ) (h0 : 0 ≤ x) :
    x ^ 2 * (130 - 4 * x) = -4 * x ^ 3 + 130 * x ^ 2 ∧
    x ^ 2 * (130 - 4 * x) ≤ 549250 / 27 ∧ (65 / 3 : ℝ) ^ 2 * (130 - 4 * (65 / 3)) = 549250 / 27 ∧
    (130 - 4 * (65 / 3) : ℝ) = 130 / 3 ∧
    x ^ 2 * (108 - 4 * x) = -4 * x ^ 3 + 108 * x ^ 2 ∧
    x ^ 2 * (108 - 4 * x) ≤ 11664 ∧ (18 : ℝ) ^ 2 * (108 - 4 * 18) = 11664 ∧
    (108 - 4 * 18 : ℝ) = 36 := by
  refine ⟨by ring, ?_, by norm_num, by norm_num, by ring, ?_, by norm_num, by norm_num⟩
  · nlinarith [mul_nonneg (sq_nonneg (x - 65 / 3)) (show 0 ≤ x + 65 / 6 by linarith)]
  · nlinarith [mul_nonneg (sq_nonneg (x - 18)) (show 0 ≤ x + 9 by linarith)]

/-- Stitz-Zeager Exercise 3.1.36: a linear function `mx + b` with `m > 0` rises to `+∞` on the right
and falls to `-∞` on the left; with `m < 0` it is the reverse. -/
@[kb "stitzzeager2013" "Exercise 3.1.36, p. 260"]
theorem exer_3_1_36 (m b : ℝ) (hm : m ≠ 0) :
    (0 < m → Tendsto (fun x : ℝ => m * x + b) atTop atTop ∧
      Tendsto (fun x : ℝ => m * x + b) atBot atBot) ∧
    (m < 0 → Tendsto (fun x : ℝ => m * x + b) atTop atBot ∧
      Tendsto (fun x : ℝ => m * x + b) atBot atTop) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · rw [tendsto_atTop_atTop]
    refine fun c => ⟨(c - b) / m, fun a ha => ?_⟩
    have := mul_le_mul_of_nonneg_left ha h.le
    rw [mul_div_cancel₀ _ hm] at this
    linarith
  · rw [tendsto_atBot_atBot]
    refine fun c => ⟨(c - b) / m, fun a ha => ?_⟩
    have := mul_le_mul_of_nonneg_left ha h.le
    rw [mul_div_cancel₀ _ hm] at this
    linarith
  · rw [tendsto_atTop_atBot]
    refine fun c => ⟨(c - b) / m, fun a ha => ?_⟩
    have := mul_le_mul_of_nonpos_left ha h.le
    rw [mul_div_cancel₀ _ hm] at this
    linarith
  · rw [tendsto_atBot_atTop]
    refine fun c => ⟨(c - b) / m, fun a ha => ?_⟩
    have := mul_le_mul_of_nonpos_left ha h.le
    rw [mul_div_cancel₀ _ hm] at this
    linarith

end UndergradKB.Precalculus.Course
