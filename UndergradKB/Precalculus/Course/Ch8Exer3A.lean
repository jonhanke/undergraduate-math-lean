import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 8 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 8.1 to 8.5 -/

namespace UndergradKB.Precalculus.Course

open Matrix Filter Topology

/-- Stitz-Zeager Exercise 8.1.34: for a 100 mL mixture at 60% from stocks at 20% and 40%, the system
`x + y = 100`, `0.2x + 0.4y = 60` has the triangular form `x + y = 100`, `y = 200`, with the single solution
`(-100, 200)` (a negative amount of the first stock, so the mixture is impossible). -/
@[kb "stitzzeager2013" "Exercise 8.1.34, p. 575"]
theorem exer_8_1_34 (x y : ℝ) :
    ((x + y = 100 ∧ (1 / 5) * x + (2 / 5) * y = 60) ↔ (x + y = 100 ∧ y = 200)) ∧
    ((x + y = 100 ∧ (1 / 5) * x + (2 / 5) * y = 60) ↔ (x = -100 ∧ y = 200)) := by
  constructor
  · constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; subst h1; subst h2; norm_num

/-- Stitz-Zeager Exercise 8.2.33: two different row echelon forms of the augmented matrix
`[[1, 2 | 3], [4, 12 | 8]]`, namely `[[1, 2 | 3], [0, 1 | -1]]` and `[[1, 3 | 2], [0, 1 | -1]]`; all three
systems have the same solution `(5, -1)`. -/
@[kb "stitzzeager2013" "Exercise 8.2.33, p. 587"]
theorem exer_8_2_33 (x y : ℝ) :
    ((x + 2 * y = 3 ∧ 4 * x + 12 * y = 8) ↔ (x + 2 * y = 3 ∧ y = -1)) ∧
    ((x + 2 * y = 3 ∧ 4 * x + 12 * y = 8) ↔ (x + 3 * y = 2 ∧ y = -1)) ∧
    ((x + 2 * y = 3 ∧ 4 * x + 12 * y = 8) ↔ (x = 5 ∧ y = -1)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; subst h1; subst h2; norm_num

/-- Stitz-Zeager Exercise 8.3.11: `E + D` is undefined, because `E` is `3 × 3` and `D` is `3 × 2`: the numbers of
columns differ. -/
@[kb "stitzzeager2013" "Exercise 8.3.11, p. 603"]
theorem exer_8_3_11 : Fintype.card (Fin 3) ≠ Fintype.card (Fin 2) := by simp

/-- Stitz-Zeager Exercise 8.3.20: `CDE` is undefined: `CD` is `2 × 2` (`C` is `2 × 3`, `D` is `3 × 2`) while
`E` is `3 × 3`, so the inner dimensions `2` and `3` differ. -/
@[kb "stitzzeager2013" "Exercise 8.3.20, p. 603"]
theorem exer_8_3_20 : Fintype.card (Fin 2) ≠ Fintype.card (Fin 3) := by simp

/-- Stitz-Zeager Exercise 8.3.25: the transition matrix `Q = [[0.9, 0.2], [0.1, 0.8]]` sends the state `(T, P)`
to `(0.9 T + 0.2 P, 0.1 T + 0.8 P)`: 90% of the Tribune readers and 20% of the Picayune readers read the
Tribune next week, and the total number of readers is unchanged. -/
@[kb "stitzzeager2013" "Exercise 8.3.25, p. 604"]
theorem exer_8_3_25 (T P : ℝ) :
    !![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] *ᵥ ![T, P] = ![9 / 10 * T + 1 / 5 * P, 1 / 10 * T + 4 / 5 * P] ∧
    (9 / 10 * T + 1 / 5 * P) + (1 / 10 * T + 4 / 5 * P) = T + P := by
  refine ⟨?_, by ring⟩
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem x8w8a_step (u v : ℝ) :
    !![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] *ᵥ ![u, v] = ![9 / 10 * u + 1 / 5 * v, 1 / 10 * u + 4 / 5 * v] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Stitz-Zeager Exercise 8.3.26: starting from all 150 residents with the Tribune, week `n` has
`Qⁿ X = (100 + 50 (7/10)ⁿ, 50 - 50 (7/10)ⁿ)`, which tends to the steady state `(100, 50)` as `n → ∞`. -/
@[kb "stitzzeager2013" "Exercise 8.3.26, p. 604"]
theorem exer_8_3_26 :
    (∀ n : ℕ, (!![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ n) *ᵥ ![150, 0] =
      ![100 + 50 * (7 / 10) ^ n, 50 - 50 * (7 / 10) ^ n]) ∧
    Tendsto (fun n : ℕ => (!![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ n) *ᵥ ![150, 0]) atTop (𝓝 ![100, 50]) := by
  have hform : ∀ n : ℕ, (!![(9 : ℝ) / 10, 1 / 5; 1 / 10, 4 / 5] ^ n) *ᵥ ![150, 0] =
      ![100 + 50 * (7 / 10) ^ n, 50 - 50 * (7 / 10) ^ n] := by
    intro n
    induction n with
    | zero => ext i; fin_cases i <;> simp <;> norm_num
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, x8w8a_step]
      ext i; fin_cases i <;> simp <;> ring
  refine ⟨hform, ?_⟩
  have ht : Tendsto (fun n : ℕ => (7 / 10 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simp only [hform]
  refine tendsto_pi_nhds.2 (fun i => ?_)
  fin_cases i
  · have := (ht.const_mul 50).const_add 100
    simpa using this
  · have := (ht.const_mul 50).const_sub 50
    simpa using this

/-- Stitz-Zeager Exercise 8.4.15 (a), (c): for the rotation matrix `R` by 45° with entries `±√2/2`, the inverse is
`R⁻¹ = [[√2/2, √2/2], [-√2/2, √2/2]]`; it sends `(x, y)` to `(√2/2 (x+y), √2/2 (y-x))`, and it maps points of the
curve `y = 2/x` to points of the curve `x² - y² = 4`. -/
@[kb "stitzzeager2013" "Exercise 8.4.15, p. 621"]
theorem exer_8_4_15 :
    let s := Real.sqrt 2
    let R : Matrix (Fin 2) (Fin 2) ℝ := !![s / 2, -(s / 2); s / 2, s / 2]
    let S : Matrix (Fin 2) (Fin 2) ℝ := !![s / 2, s / 2; -(s / 2), s / 2]
    R * S = 1 ∧ S * R = 1 ∧ (∀ x y : ℝ, S *ᵥ ![x, y] = ![s / 2 * (x + y), s / 2 * (y - x)]) ∧
    ∀ x y : ℝ, x ≠ 0 → y = 2 / x → (s / 2 * (x + y)) ^ 2 - (s / 2 * (y - x)) ^ 2 = 4 := by
  intro s R S
  have hs : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [R, S, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [hs]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [R, S, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [hs]
  · intro x y
    ext i; fin_cases i <;> simp [S, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  · intro x y hx hy
    have hxy : x * y = 2 := by rw [hy]; field_simp
    linear_combination (x * y) * hs + 2 * hxy

/-- Stitz-Zeager Exercise 8.5.28: the solutions of `G X = 0`, for `G = [[1,2,3],[2,3,11],[3,4,19]]`, are
exactly `(x, y, z) = (-13t, 5t, t)`. -/
@[kb "stitzzeager2013" "Exercise 8.5.28, p. 638"]
theorem exer_8_5_28 (x y z : ℝ) :
    (x + 2 * y + 3 * z = 0 ∧ 2 * x + 3 * y + 11 * z = 0 ∧ 3 * x + 4 * y + 19 * z = 0) ↔
      ∃ t : ℝ, x = -13 * t ∧ y = 5 * t ∧ z = t := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨z, by linarith, by linarith, rfl⟩
  · rintro ⟨t, rfl, rfl, rfl⟩
    refine ⟨by ring, by ring, by ring⟩

/-- Stitz-Zeager Exercise 8.5.29: the solutions of `(G - I) X = 0` are exactly `(x, y, z) = (-4t, -3t/2, t)`, and
every such solution satisfies `G X = X`. -/
@[kb "stitzzeager2013" "Exercise 8.5.29, p. 638"]
theorem exer_8_5_29 (x y z : ℝ) :
    ((0 * x + 2 * y + 3 * z = 0 ∧ 2 * x + 2 * y + 11 * z = 0 ∧ 3 * x + 4 * y + 18 * z = 0) ↔
      ∃ t : ℝ, x = -4 * t ∧ y = -3 / 2 * t ∧ z = t) ∧
    ((0 * x + 2 * y + 3 * z = 0 ∧ 2 * x + 2 * y + 11 * z = 0 ∧ 3 * x + 4 * y + 18 * z = 0) →
      (x + 2 * y + 3 * z = x ∧ 2 * x + 3 * y + 11 * z = y ∧ 3 * x + 4 * y + 19 * z = z)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨z, by linarith, by linarith, rfl⟩
    · rintro ⟨t, rfl, rfl, rfl⟩
      refine ⟨by ring, by ring, by ring⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, by linarith⟩

/-- Stitz-Zeager Exercise 8.5.30: the solutions of `(G - 22 I) X = 0` are exactly `(x, y, z) = (t, 3t, 5t)`, and
every such solution satisfies `G X = 22 X`. -/
@[kb "stitzzeager2013" "Exercise 8.5.30, p. 638"]
theorem exer_8_5_30 (x y z : ℝ) :
    ((-21 * x + 2 * y + 3 * z = 0 ∧ 2 * x - 19 * y + 11 * z = 0 ∧ 3 * x + 4 * y - 3 * z = 0) ↔
      ∃ t : ℝ, x = t ∧ y = 3 * t ∧ z = 5 * t) ∧
    ((-21 * x + 2 * y + 3 * z = 0 ∧ 2 * x - 19 * y + 11 * z = 0 ∧ 3 * x + 4 * y - 3 * z = 0) →
      (x + 2 * y + 3 * z = 22 * x ∧ 2 * x + 3 * y + 11 * z = 22 * y ∧ 3 * x + 4 * y + 19 * z = 22 * z)) := by
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨x, rfl, by linarith, by linarith⟩
    · rintro ⟨t, rfl, rfl, rfl⟩
      refine ⟨by ring, by ring, by ring⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, by linarith⟩

end UndergradKB.Precalculus.Course
