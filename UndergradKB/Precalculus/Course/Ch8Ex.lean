import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 8 (Stitz-Zeager): worked examples

Linear systems, matrix arithmetic and inverses, Cramer's rule, partial fractions and non-linear
systems: the solution sets and identities established by the worked examples of Chapter 8.
-/

namespace UndergradKB.Precalculus.Course

open Matrix

/-! ### 8.1 Systems of linear equations -/

/-- Stitz-Zeager Example 8.1.1(1): `2x - y = 1, y = 3` has the unique solution `(2, 3)`. -/
@[kb "stitzzeager2013" "Example 8.1.1, p. 562"]
theorem ex_8_1_1_1 (x y : ℝ) : (2 * x - y = 1 ∧ y = 3) ↔ (x = 2 ∧ y = 3) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.1.1(2): `3x + 4y = -2, -3x - y = 5` has the unique solution
`(-2, 1)`. -/
@[kb "stitzzeager2013" "Example 8.1.1, p. 562"]
theorem ex_8_1_1_2 (x y : ℝ) : (3 * x + 4 * y = -2 ∧ -3 * x - y = 5) ↔ (x = -2 ∧ y = 1) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.1.1(3): `x/3 - 4y/5 = 7/5, 2x/9 + y/3 = 1/2` has the unique
solution `(3, -1/2)`. -/
@[kb "stitzzeager2013" "Example 8.1.1, p. 562"]
theorem ex_8_1_1_3 (x y : ℝ) :
    (x / 3 - 4 * y / 5 = 7 / 5 ∧ 2 * x / 9 + y / 3 = 1 / 2) ↔ (x = 3 ∧ y = -1 / 2) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.1.1(4): `2x - 4y = 6, 3x - 6y = 9` describe the same line; the
solutions are the points with `x = 2y + 3`. -/
@[kb "stitzzeager2013" "Example 8.1.1, p. 562"]
theorem ex_8_1_1_4 (x y : ℝ) : (2 * x - 4 * y = 6 ∧ 3 * x - 6 * y = 9) ↔ x = 2 * y + 3 := by
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; subst h; constructor <;> ring

/-- Stitz-Zeager Example 8.1.1(5): `6x + 3y = 9, 4x + 2y = 12` is inconsistent. -/
@[kb "stitzzeager2013" "Example 8.1.1, p. 562"]
theorem ex_8_1_1_5 : ¬ ∃ x y : ℝ, 6 * x + 3 * y = 9 ∧ 4 * x + 2 * y = 12 := by
  rintro ⟨x, y, h1, h2⟩
  linarith

/-- Stitz-Zeager Example 8.1.1(6): `x - y = 0, x + y = 2, -2x + y = -2` has no solution
(the three lines are not concurrent). -/
@[kb "stitzzeager2013" "Example 8.1.1, p. 562"]
theorem ex_8_1_1_6 : ¬ ∃ x y : ℝ, x - y = 0 ∧ x + y = 2 ∧ -2 * x + y = -2 := by
  rintro ⟨x, y, h1, h2, h3⟩
  linarith

/-- Stitz-Zeager Example 8.1.2(1): the first 3-by-3 system has the unique solution
`(-1, 0, 6)`. -/
@[kb "stitzzeager2013" "Example 8.1.2, p. 569"]
theorem ex_8_1_2_1 (x y z : ℝ) :
    (3 * x - y + z = 3 ∧ 2 * x - 4 * y + 3 * z = 16 ∧ x - y + z = 5) ↔
      (x = -1 ∧ y = 0 ∧ z = 6) := by
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.1.2(2): `2x + 3y - z = 1, 10x - z = 2, 4x - 9y + 2z = 5` has no
solution. -/
@[kb "stitzzeager2013" "Example 8.1.2, p. 569"]
theorem ex_8_1_2_2 :
    ¬ ∃ x y z : ℝ, 2 * x + 3 * y - z = 1 ∧ 10 * x - z = 2 ∧ 4 * x - 9 * y + 2 * z = 5 := by
  rintro ⟨x, y, z, h1, h2, h3⟩
  linarith

/-- Stitz-Zeager Example 8.1.2(3): the underdetermined system
`3x1 + x2 + x4 = 6, 2x1 + x2 - x3 = 4, x2 - 3x3 - 2x4 = 0` has solutions
`(2 - s - t, 3s + 2t, s, t)`. -/
@[kb "stitzzeager2013" "Example 8.1.2, p. 569"]
theorem ex_8_1_2_3 (x1 x2 x3 x4 : ℝ) :
    (3 * x1 + x2 + x4 = 6 ∧ 2 * x1 + x2 - x3 = 4 ∧ x2 - 3 * x3 - 2 * x4 = 0) ↔
      (x1 = 2 - x3 - x4 ∧ x2 = 3 * x3 + 2 * x4) := by
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Stitz-Zeager Example 8.1.3(a): the mixture system `x + y + w = 500`,
`3x/10 + 9y/10 = 200` has solutions `x = 1250/3 - 3w/2`, `y = 250/3 + w/2`. -/
@[kb "stitzzeager2013" "Example 8.1.3, p. 572"]
theorem ex_8_1_3_a_general (x y w : ℝ) :
    (x + y + w = 500 ∧ 3 / 10 * x + 9 / 10 * y = 200) ↔
      (x = 1250 / 3 - 3 / 2 * w ∧ y = 250 / 3 + 1 / 2 * w) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- Stitz-Zeager Example 8.1.3(b): with nonnegative amounts, the solutions are those with
`0 ≤ w ≤ 2500/9`. -/
@[kb "stitzzeager2013" "Example 8.1.3, p. 572"]
theorem ex_8_1_3_b_nonneg (x y w : ℝ) :
    (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ w ∧ x + y + w = 500 ∧ 3 / 10 * x + 9 / 10 * y = 200) ↔
      (0 ≤ w ∧ w ≤ 2500 / 9 ∧ x = 1250 / 3 - 3 / 2 * w ∧ y = 250 / 3 + 1 / 2 * w) := by
  constructor
  · rintro ⟨hx, hy, hw, h1, h2⟩
    exact ⟨hw, by linarith, by linarith, by linarith⟩
  · rintro ⟨hw, hw2, h1, h2⟩
    refine ⟨by linarith, by linarith, hw, ?_, ?_⟩ <;> linarith

/-- Stitz-Zeager Example 8.1.3(c): using all `100` mL of the 90% stock forces `w = 100/3` mL
of water and `x = 1100/3` mL of the 30% stock. -/
@[kb "stitzzeager2013" "Example 8.1.3, p. 572"]
theorem ex_8_1_3_c_use_all (x w : ℝ) :
    (x + 100 + w = 500 ∧ 3 / 10 * x + 9 / 10 * 100 = 200) ↔ (x = 1100 / 3 ∧ w = 100 / 3) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩; norm_num

/-! ### 8.2 Augmented matrices -/

/-- Stitz-Zeager Example 8.2.1: `3x - y + z = 8, x + 2y - z = 4, 2x + 3y - 4z = 10` has the
unique solution `(3, 0, -1)`. -/
@[kb "stitzzeager2013" "Example 8.2.1, p. 581"]
theorem ex_8_2_1 (x y z : ℝ) :
    (3 * x - y + z = 8 ∧ x + 2 * y - z = 4 ∧ 2 * x + 3 * y - 4 * z = 10) ↔
      (x = 3 ∧ y = 0 ∧ z = -1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.2.2: the system `x2 - 3x1 + x4 = 2, 2x1 + 4x3 = 5, 4x2 - x4 = 3`
is solved by taking `x1` free: `x2 = 1 + 3x1/5`, `x3 = 5/4 - x1/2`, `x4 = 1 + 12x1/5`. -/
@[kb "stitzzeager2013" "Example 8.2.2, p. 583"]
theorem ex_8_2_2 (x1 x2 x3 x4 : ℝ) :
    (x2 - 3 * x1 + x4 = 2 ∧ 2 * x1 + 4 * x3 = 5 ∧ 4 * x2 - x4 = 3) ↔
      (x2 = 1 + 3 / 5 * x1 ∧ x3 = 5 / 4 - 1 / 2 * x1 ∧ x4 = 1 + 12 / 5 * x1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Stitz-Zeager Example 8.2.3: the unique quadratic `a x^2 + b x + c` through `(-1, 3)`,
`(2, 4)`, `(5, -2)` has `a = -7/18`, `b = 13/18`, `c = 37/9`. -/
@[kb "stitzzeager2013" "Example 8.2.3, p. 585"]
theorem ex_8_2_3 (a b c : ℝ) :
    (a * (-1) ^ 2 + b * (-1) + c = 3 ∧ a * 2 ^ 2 + b * 2 + c = 4 ∧
        a * 5 ^ 2 + b * 5 + c = -2) ↔ (a = -7 / 18 ∧ b = 13 / 18 ∧ c = 37 / 9) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    norm_num at h1 h2 h3
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-! ### 8.3 Matrix arithmetic -/

/-- Stitz-Zeager Example 8.3.1: the matrix equation `3A - M = 5A + (N + P/3)` with
`M = [[2,-1],[3,5]]`, `N = [[-4,2],[6,-2]]`, `P = [[9,12],[-3,39]]` is solved by
`A = [[-1/2,-5/2],[-4,-8]]`. -/
@[kb "stitzzeager2013" "Example 8.3.1, p. 593"]
theorem ex_8_3_1 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (3 : ℝ) • A - !![2, -1; 3, 5] =
        (5 : ℝ) • A + (!![-4, 2; 6, -2] + (1 / 3 : ℝ) • !![9, 12; -3, 39]) ↔
      A = !![-1 / 2, -5 / 2; -4, -8] := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num

/-- Stitz-Zeager Example 8.3.2(1): a product of two nonzero matrices can be zero. -/
@[kb "stitzzeager2013" "Example 8.3.2, p. 598"]
theorem ex_8_3_2_1 :
    (!![-23, -1, 17; 46, 2, -34] : Matrix (Fin 2) (Fin 3) ℝ) * (!![-3, 2; 1, 5; -4, 3] : Matrix (Fin 3) (Fin 2) ℝ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- Stitz-Zeager Example 8.3.2(2): for `C = [[1,-2],[3,4]]`, `C^2 - 5C + 10 I = 0`. -/
@[kb "stitzzeager2013" "Example 8.3.2, p. 598"]
theorem ex_8_3_2_2 :
    (!![1, -2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 - (5 : ℝ) • !![1, -2; 3, 4] +
        (10 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two] <;> norm_num

/-- Stitz-Zeager Example 8.3.2(3): for a `4 × 4` matrix `M`,
`(M - 2I)(M + 3I) = M^2 + M - 6I`. -/
@[kb "stitzzeager2013" "Example 8.3.2, p. 598"]
theorem ex_8_3_2_3 (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (M - (2 : ℝ) • 1) * (M + (3 : ℝ) • 1) = M ^ 2 + M - (6 : ℝ) • 1 := by
  simp only [sub_mul, mul_add, mul_smul_comm, smul_mul_assoc, one_mul, mul_one, pow_two]
  module

/-- Stitz-Zeager Example 8.3.3(2): the rotation matrix `R` by `45` degrees sends a point of the
hyperbola `x^2 - y^2 = 4` to a point `(u, v)` with `u v = 2`. -/
@[kb "stitzzeager2013" "Example 8.3.3, p. 599"]
theorem ex_8_3_3_rotation_hyperbola (x y : ℝ) (h : x ^ 2 - y ^ 2 = 4) :
    ((!![Real.sqrt 2 / 2, -(Real.sqrt 2 / 2); Real.sqrt 2 / 2, Real.sqrt 2 / 2] : Matrix (Fin 2) (Fin 2) ℝ)
        *ᵥ ![x, y]) 0 *
      ((!![Real.sqrt 2 / 2, -(Real.sqrt 2 / 2); Real.sqrt 2 / 2, Real.sqrt 2 / 2] :
        Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![x, y]) 1 = 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith

/-! ### 8.4 Matrix inverses -/

/-- Stitz-Zeager Example 8.4.1(1): the inverse of `[[3,1,2],[0,-1,5],[2,1,4]]` is
`(1/13) [[9,2,-7],[-10,-8,15],[-2,1,3]]`. -/
@[kb "stitzzeager2013" "Example 8.4.1, p. 615"]
theorem ex_8_4_1_1_inverse :
    (!![3, 1, 2; 0, -1, 5; 2, 1, 4] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ =
      (1 / 13 : ℝ) • !![9, 2, -7; -10, -8, 15; -2, 1, 3] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- Stitz-Zeager Example 8.4.1(2a): `3x + y + 2z = 26, -y + 5z = 39, 2x + y + 4z = 117` has the
unique solution `(-39, 91, 26)`. -/
@[kb "stitzzeager2013" "Example 8.4.1, p. 615"]
theorem ex_8_4_1_2_a (x y z : ℝ) :
    (3 * x + y + 2 * z = 26 ∧ -y + 5 * z = 39 ∧ 2 * x + y + 4 * z = 117) ↔
      (x = -39 ∧ y = 91 ∧ z = 26) := by
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.4.1(2b): the same coefficients with right sides `4, 2, 5` give the
unique solution `(5/13, 19/13, 9/13)`. -/
@[kb "stitzzeager2013" "Example 8.4.1, p. 615"]
theorem ex_8_4_1_2_b (x y z : ℝ) :
    (3 * x + y + 2 * z = 4 ∧ -y + 5 * z = 2 ∧ 2 * x + y + 4 * z = 5) ↔
      (x = 5 / 13 ∧ y = 19 / 13 ∧ z = 9 / 13) := by
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.4.1(2c): right sides `1, 0, 0` give the unique solution
`(9/13, -10/13, -2/13)`. -/
@[kb "stitzzeager2013" "Example 8.4.1, p. 615"]
theorem ex_8_4_1_2_c (x y z : ℝ) :
    (3 * x + y + 2 * z = 1 ∧ -y + 5 * z = 0 ∧ 2 * x + y + 4 * z = 0) ↔
      (x = 9 / 13 ∧ y = -10 / 13 ∧ z = -2 / 13) := by
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.4.2(1a): with all resistances `1` and batteries `10` V and `5` V the
mesh-current system has the unique solution `(85/8, 25/4, 25/8, 5)`. -/
@[kb "stitzzeager2013" "Example 8.4.2, p. 617"]
theorem ex_8_4_2_1_a (i1 i2 i3 i4 : ℝ) :
    (2 * i1 - i2 - i4 = 10 ∧ -i1 + 3 * i2 - i3 - i4 = 0 ∧ -i2 + 2 * i3 - i4 = -5 ∧
        -i1 - i2 - i3 + 4 * i4 = 0) ↔
      (i1 = 85 / 8 ∧ i2 = 25 / 4 ∧ i3 = 25 / 8 ∧ i4 = 5) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.4.2(1b): with batteries `10` V and `0` V the unique solution is
`(65/4, 25/2, 45/4, 10)`. -/
@[kb "stitzzeager2013" "Example 8.4.2, p. 617"]
theorem ex_8_4_2_1_b (i1 i2 i3 i4 : ℝ) :
    (2 * i1 - i2 - i4 = 10 ∧ -i1 + 3 * i2 - i3 - i4 = 0 ∧ -i2 + 2 * i3 - i4 = 0 ∧
        -i1 - i2 - i3 + 4 * i4 = 0) ↔
      (i1 = 65 / 4 ∧ i2 = 25 / 2 ∧ i3 = 45 / 4 ∧ i4 = 10) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; norm_num

/-! ### 8.5 Cramer's rule -/

/-- Stitz-Zeager Example 8.5.1(1): for `2x1 - 3x2 = 4, 5x1 + x2 = -2` the determinants are
`17`, `-2`, `-24`, and the solution is `(-2/17, -24/17)`. -/
@[kb "stitzzeager2013" "Example 8.5.1, p. 631"]
theorem ex_8_5_1_1 (x1 x2 : ℝ) :
    Matrix.det !![2, -3; 5, 1] = (17 : ℝ) ∧ Matrix.det !![4, -3; -2, 1] = (-2 : ℝ) ∧
    Matrix.det !![2, 4; 5, -2] = (-24 : ℝ) ∧
    ((2 * x1 - 3 * x2 = 4 ∧ 5 * x1 + x2 = -2) ↔ (x1 = -2 / 17 ∧ x2 = -24 / 17)) := by
  refine ⟨by simp [Matrix.det_fin_two_of]; norm_num, by simp [Matrix.det_fin_two_of]; norm_num,
    by simp [Matrix.det_fin_two_of]; norm_num, ?_⟩
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩; norm_num

/-- Stitz-Zeager Example 8.5.1(2): for `2x - 3y + z = -1, x - y + z = 1, 3x - 4z = 0` the
determinant is `-10`, replacing the `z` column gives `-12`, and `z = 6/5`. -/
@[kb "stitzzeager2013" "Example 8.5.1, p. 631"]
theorem ex_8_5_1_2 (x y z : ℝ) :
    Matrix.det !![2, -3, 1; 1, -1, 1; 3, 0, -4] = (-10 : ℝ) ∧
    Matrix.det !![2, -3, -1; 1, -1, 1; 3, 0, 0] = (-12 : ℝ) ∧
    ((2 * x - 3 * y + z = -1 ∧ x - y + z = 1 ∧ 3 * x - 4 * z = 0) ↔
      (x = 8 / 5 ∧ y = 9 / 5 ∧ z = 6 / 5)) := by
  refine ⟨by simp [Matrix.det_fin_three]; norm_num, by simp [Matrix.det_fin_three]; norm_num, ?_⟩
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩; norm_num

/-! ### 8.6 Partial fractions -/

/-- Stitz-Zeager Example 8.6.1(1): `(x+5)/(2x^2 - x - 1) = 2/(x-1) - 3/(2x+1)`. -/
@[kb "stitzzeager2013" "Example 8.6.1, p. 643"]
theorem ex_8_6_1_1 (x : ℝ) (h1 : 2 * x + 1 ≠ 0) (h2 : x - 1 ≠ 0) :
    (x + 5) / (2 * x ^ 2 - x - 1) = 2 / (x - 1) - 3 / (2 * x + 1) := by
  have : 2 * x ^ 2 - x - 1 = (2 * x + 1) * (x - 1) := by ring
  rw [this, div_sub_div _ _ h2 h1, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h2 h1)]
  ring

/-- Stitz-Zeager Example 8.6.1(2): `3/(x^3 - 2x^2 + x) = 3/x - 3/(x-1) + 3/(x-1)^2`. -/
@[kb "stitzzeager2013" "Example 8.6.1, p. 643"]
theorem ex_8_6_1_2 (x : ℝ) (h1 : x ≠ 0) (h2 : x - 1 ≠ 0) :
    3 / (x ^ 3 - 2 * x ^ 2 + x) = 3 / x - 3 / (x - 1) + 3 / (x - 1) ^ 2 := by
  have : x ^ 3 - 2 * x ^ 2 + x = x * (x - 1) ^ 2 := by ring
  rw [this]
  field_simp
  ring

/-- Stitz-Zeager Example 8.6.1(3): `3/(x^3 - x^2 + x) = 3/x + (-3x + 3)/(x^2 - x + 1)`. -/
@[kb "stitzzeager2013" "Example 8.6.1, p. 643"]
theorem ex_8_6_1_3 (x : ℝ) (h1 : x ≠ 0) :
    3 / (x ^ 3 - x ^ 2 + x) = 3 / x + (-3 * x + 3) / (x ^ 2 - x + 1) := by
  have h2 : x ^ 2 - x + 1 ≠ 0 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have : x ^ 3 - x ^ 2 + x = x * (x ^ 2 - x + 1) := by ring
  rw [this, div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  ring

/-- Stitz-Zeager Example 8.6.1(4): `4x^3/(x^2 - 2) = 4x + 8x/(x^2 - 2)`. -/
@[kb "stitzzeager2013" "Example 8.6.1, p. 643"]
theorem ex_8_6_1_4 (x : ℝ) (h : x ^ 2 - 2 ≠ 0) :
    4 * x ^ 3 / (x ^ 2 - 2) = 4 * x + 8 * x / (x ^ 2 - 2) := by
  field_simp
  ring

/-- Stitz-Zeager Example 8.6.1(5):
`(x^3 + 5x - 1)/(x^4 + 6x^2 + 9) = x/(x^2 + 3) + (2x - 1)/(x^2 + 3)^2`. -/
@[kb "stitzzeager2013" "Example 8.6.1, p. 643"]
theorem ex_8_6_1_5 (x : ℝ) :
    (x ^ 3 + 5 * x - 1) / (x ^ 4 + 6 * x ^ 2 + 9) = x / (x ^ 2 + 3) + (2 * x - 1) / (x ^ 2 + 3) ^ 2 := by
  have h : x ^ 2 + 3 ≠ 0 := by positivity
  have : x ^ 4 + 6 * x ^ 2 + 9 = (x ^ 2 + 3) ^ 2 := by ring
  rw [this]
  field_simp
  ring

/-- Stitz-Zeager Example 8.6.1(6):
`8x^2/(x^4 + 16) = √2 x/(x^2 - 2√2 x + 4) - √2 x/(x^2 + 2√2 x + 4)`. -/
@[kb "stitzzeager2013" "Example 8.6.1, p. 643"]
theorem ex_8_6_1_6 (x : ℝ) :
    8 * x ^ 2 / (x ^ 4 + 16) =
      Real.sqrt 2 * x / (x ^ 2 - 2 * Real.sqrt 2 * x + 4) -
        Real.sqrt 2 * x / (x ^ 2 + 2 * Real.sqrt 2 * x + 4) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 2 with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  have h1 : x ^ 2 - 2 * s * x + 4 ≠ 0 := by nlinarith [sq_nonneg (x - s)]
  have h2 : x ^ 2 + 2 * s * x + 4 ≠ 0 := by nlinarith [sq_nonneg (x + s)]
  have hfac : x ^ 4 + 16 = (x ^ 2 - 2 * s * x + 4) * (x ^ 2 + 2 * s * x + 4) := by
    linear_combination (4 * x ^ 2) * hs
  rw [hfac, div_sub_div _ _ h1 h2, div_left_inj' (mul_ne_zero h1 h2)]
  linear_combination (-4 * x ^ 2) * hs

/-! ### 8.7 Non-linear systems -/

/-- Stitz-Zeager Example 8.7.1(1): `x^2 + y^2 = 4, 4x^2 + 9y^2 = 36` has solutions `(0, ±2)`. -/
@[kb "stitzzeager2013" "Example 8.7.1, p. 649"]
theorem ex_8_7_1_1 (x y : ℝ) :
    (x ^ 2 + y ^ 2 = 4 ∧ 4 * x ^ 2 + 9 * y ^ 2 = 36) ↔ (x = 0 ∧ (y = 2 ∨ y = -2)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y ^ 2 = 4 := by linarith
    have hx : x ^ 2 = 0 := by linarith
    refine ⟨pow_eq_zero_iff (two_ne_zero) |>.mp hx, ?_⟩
    have : (y - 2) * (y + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num

/-- Stitz-Zeager Example 8.7.1(2): `x^2 + y^2 = 4, 4x^2 - 9y^2 = 36` has no real solution. -/
@[kb "stitzzeager2013" "Example 8.7.1, p. 649"]
theorem ex_8_7_1_2 : ¬ ∃ x y : ℝ, x ^ 2 + y ^ 2 = 4 ∧ 4 * x ^ 2 - 9 * y ^ 2 = 36 := by
  rintro ⟨x, y, h1, h2⟩
  nlinarith [sq_nonneg y]

/-- Stitz-Zeager Example 8.7.1(3): `x^2 + y^2 = 4, y - 2x = 0` has the two solutions
`±(2√5/5, 4√5/5)`. -/
@[kb "stitzzeager2013" "Example 8.7.1, p. 649"]
theorem ex_8_7_1_3 (x y : ℝ) :
    (x ^ 2 + y ^ 2 = 4 ∧ y - 2 * x = 0) ↔
      ((x = 2 * Real.sqrt 5 / 5 ∧ y = 4 * Real.sqrt 5 / 5) ∨
        (x = -(2 * Real.sqrt 5 / 5) ∧ y = -(4 * Real.sqrt 5 / 5))) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y = 2 * x := by linarith
    subst hy
    have : (x - 2 * Real.sqrt 5 / 5) * (x + 2 * Real.sqrt 5 / 5) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> nlinarith

/-- Stitz-Zeager Example 8.7.1(4): `x^2 + y^2 = 4, y - x^2 = 0` has the solutions with
`y = (-1 + √17)/2` and `x = ±√y`. -/
@[kb "stitzzeager2013" "Example 8.7.1, p. 649"]
theorem ex_8_7_1_4 (x y : ℝ) :
    (x ^ 2 + y ^ 2 = 4 ∧ y - x ^ 2 = 0) ↔
      (y = (-1 + Real.sqrt 17) / 2 ∧ (x = Real.sqrt y ∨ x = -Real.sqrt y)) := by
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17n : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg 17
  have hpos : 0 < (-1 + Real.sqrt 17) / 2 := by
    have : (4 : ℝ) < Real.sqrt 17 := by nlinarith
    linarith
  constructor
  · rintro ⟨h1, h2⟩
    have hy0 : 0 ≤ y := by nlinarith [sq_nonneg x]
    have hyy : y ^ 2 + y = 4 := by nlinarith
    have hy : y = (-1 + Real.sqrt 17) / 2 := by
      have : (y - (-1 + Real.sqrt 17) / 2) * (y + (1 + Real.sqrt 17) / 2) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · nlinarith
    refine ⟨hy, ?_⟩
    have hx : x ^ 2 = y := by linarith
    have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0
    have : (x - Real.sqrt y) * (x + Real.sqrt y) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro ⟨hy, hx⟩
    have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by rw [hy]; exact hpos.le)
    have hx2 : x ^ 2 = y := by rcases hx with h | h <;> rw [h] <;> nlinarith
    refine ⟨?_, by linarith⟩
    rw [hx2, hy]
    nlinarith

/-- Stitz-Zeager Example 8.7.2(1): `x^2 + 2xy - 16 = 0, y^2 + 2xy - 16 = 0` has the two
solutions `±(4√3/3, 4√3/3)`. -/
@[kb "stitzzeager2013" "Example 8.7.2, p. 651"]
theorem ex_8_7_2_1 (x y : ℝ) :
    (x ^ 2 + 2 * x * y - 16 = 0 ∧ y ^ 2 + 2 * x * y - 16 = 0) ↔
      ((x = 4 * Real.sqrt 3 / 3 ∧ y = 4 * Real.sqrt 3 / 3) ∨
        (x = -(4 * Real.sqrt 3 / 3) ∧ y = -(4 * Real.sqrt 3 / 3))) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have : (y - x) * (y + x) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · have hy : y = x := by linarith
      subst hy
      have : (y - 4 * Real.sqrt 3 / 3) * (y + 4 * Real.sqrt 3 / 3) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; constructor <;> linarith
      · right; constructor <;> linarith
    · have hy : y = -x := by linarith
      subst hy
      nlinarith [sq_nonneg x]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor <;> nlinarith

/-- Stitz-Zeager Example 8.7.3(1): the boundary curves `y^2 = x + 4` and `y = x - 2` meet
exactly at `(0, -2)` and `(5, 3)`. -/
@[kb "stitzzeager2013" "Example 8.7.3, p. 655"]
theorem ex_8_7_3_1_boundary_intersections (x y : ℝ) :
    (y ^ 2 = x + 4 ∧ y = x - 2) ↔ ((x = 0 ∧ y = -2) ∨ (x = 5 ∧ y = 3)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hx : x = y + 2 := by linarith
    subst hx
    have : (y + 2) * (y - 3) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- Stitz-Zeager Example 8.7.3(2): the region `x^2 + y^2 ≥ 4`, `x^2 - 2x + y^2 - 2y ≤ 0`
is the set on or outside the unit-origin circle of radius 2 and on or inside the circle of
radius `√2` about `(1, 1)`. -/
@[kb "stitzzeager2013" "Example 8.7.3, p. 655"]
theorem ex_8_7_3_2_region (x y : ℝ) :
    (x ^ 2 + y ^ 2 ≥ 4 ∧ x ^ 2 - 2 * x + y ^ 2 - 2 * y ≤ 0) ↔
      (x ^ 2 + y ^ 2 ≥ 4 ∧ (x - 1) ^ 2 + (y - 1) ^ 2 ≤ 2) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by nlinarith⟩

end UndergradKB.Precalculus.Course
