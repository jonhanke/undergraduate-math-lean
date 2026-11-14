import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 4 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

/-- Stitz-Zeager Example 4.3.6(1): Hooke's law `F = k x` determines the constant `k = F / x`
(for `x ≠ 0`). -/
@[kb "stitzzeager2013" "Example 4.3.6, p. 362"]
theorem ex_4_3_6_a (F x k : ℝ) (hx : x ≠ 0) : F = k * x ↔ k = F / x := by
  constructor
  · intro h; rw [h]; field_simp
  · intro h; rw [h]; field_simp

/-- Stitz-Zeager Example 4.3.6(2): Boyle's law `P = k / V` determines `k = P V` (for `V ≠ 0`). -/
@[kb "stitzzeager2013" "Example 4.3.6, p. 362"]
theorem ex_4_3_6_b (P V k : ℝ) (hV : V ≠ 0) : P = k / V ↔ k = P * V := by
  constructor
  · intro h; rw [h]; field_simp
  · intro h; rw [h]; field_simp

/-- Stitz-Zeager Example 4.3.6(3): the cone volume `π r² h / 3` has the joint-variation form
`V = k h r²` with `k = π / 3`. -/
@[kb "stitzzeager2013" "Example 4.3.6, p. 362"]
theorem ex_4_3_6_c : ∃ k : ℝ, ∀ r h : ℝ, Real.pi * r ^ 2 * h / 3 = k * h * r ^ 2 :=
  ⟨Real.pi / 3, fun r h => by ring⟩

/-- Stitz-Zeager Example 4.3.6(4): Ohm's law `I = k V / R` determines `k = I R / V`
(for `V ≠ 0`, `R ≠ 0`). -/
@[kb "stitzzeager2013" "Example 4.3.6, p. 362"]
theorem ex_4_3_6_d (I V R k : ℝ) (hV : V ≠ 0) (hR : R ≠ 0) :
    I = k * V / R ↔ k = I * R / V := by
  constructor
  · intro h; rw [h]; field_simp
  · intro h; rw [h]; field_simp

/-- Stitz-Zeager Example 4.3.6(5): Newton's gravitation `F = k m M / r²` determines
`k = F r² / (m M)` (for `m M ≠ 0`, `r ≠ 0`). -/
@[kb "stitzzeager2013" "Example 4.3.6, p. 362"]
theorem ex_4_3_6_e (F m M r k : ℝ) (hm : m ≠ 0) (hM : M ≠ 0) (hr : r ≠ 0) :
    F = k * m * M / r ^ 2 ↔ k = F * r ^ 2 / (m * M) := by
  constructor
  · intro h; rw [h]; field_simp
  · intro h; rw [h]; field_simp

/-- Stitz-Zeager Example 4.3.7(2): for every entry `(V, P)` of Boyle's data table, the product
`P V` lies close to `1400`, supporting `P = 1400 / V`. -/
@[kb "stitzzeager2013" "Example 4.3.7, p. 363"]
theorem ex_4_3_7_product_near_1400 :
    ∀ p ∈ ([(48, 29.13), (46, 30.56), (44, 31.94), (42, 33.5), (40, 35.31), (38, 37), (36, 39.31),
      (34, 41.63), (32, 44.19), (30, 47.06), (28, 50.31), (26, 54.31), (24, 58.81), (23, 61.31),
      (22, 64.06), (21, 67.06), (20, 70.69), (19, 74.13), (18, 77.88), (17, 82.75), (16, 87.88),
      (15, 93.06), (14, 100.44), (13, 107.81), (12, 117.56)] : List (ℚ × ℚ)),
      1395 < p.1 * p.2 ∧ p.1 * p.2 < 1420 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end UndergradKB.Precalculus.Course
