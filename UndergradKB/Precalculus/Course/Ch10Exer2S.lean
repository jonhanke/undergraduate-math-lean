import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.TrigExtras

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.7 (trigonometric inequalities on `[-π, π]`)

Solution sets are stated as `↔` with the book's union of intervals; where Lean's `x⁻¹` or `cot` would take
the value `0` at a pole, the book's domain hypothesis (nonvanishing denominator) is part of the statement.
The private `pcR_*` lemmas are the interval toolkit of `Ch10Exer2R` (copied, so that this file stands alone). -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

syntax "ao_w7s" : tactic
macro_rules
  | `(tactic| ao_w7s) => `(tactic| first | linarith | (refine ⟨?_, ?_⟩ <;> ao_w7s) | (left; ao_w7s) | (right; ao_w7s))

/-- Split every hypothesis `∨`/`∧`, then close all goals with `ao_w7s`. -/
macro "iff_w7s" : tactic =>
  `(tactic| (constructor <;> intro hh <;> (try casesm* _ ∨ _, _ ∧ _) <;> ao_w7s))

private lemma pcR_cosRed (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    ∃ y, 0 ≤ y ∧ y ≤ π ∧ cos x = cos y ∧ ((x ≤ π ∧ y = x) ∨ (π < x ∧ y = 2 * π - x)) := by
  by_cases h : x ≤ π
  · exact ⟨x, h0, h, rfl, Or.inl ⟨h, rfl⟩⟩
  · replace h := not_le.mp h
    exact ⟨2 * π - x, by linarith, by linarith, (cos_two_pi_sub x).symm, Or.inr ⟨h, rfl⟩⟩

private lemma pcR_sinRed (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    ∃ y, -(π / 2) ≤ y ∧ y ≤ π / 2 ∧ sin x = sin y ∧
      ((x ≤ π / 2 ∧ y = x) ∨ (π / 2 < x ∧ x ≤ 3 * π / 2 ∧ y = π - x) ∨ (3 * π / 2 < x ∧ y = x - 2 * π)) := by
  have hp := pi_pos
  by_cases h : x ≤ π / 2
  · exact ⟨x, by linarith, h, rfl, Or.inl ⟨h, rfl⟩⟩
  · replace h := not_le.mp h
    by_cases h' : x ≤ 3 * π / 2
    · exact ⟨π - x, by linarith, by linarith, (sin_pi_sub x).symm, Or.inr (Or.inl ⟨h, h', rfl⟩)⟩
    · replace h' := not_le.mp h'
      exact ⟨x - 2 * π, by linarith, by linarith, (sin_sub_two_pi x).symm, Or.inr (Or.inr ⟨h', rfl⟩)⟩

private lemma pcR_cosLe (a y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (hy0 : 0 ≤ y) (hy1 : y ≤ π) :
    cos y ≤ cos a ↔ a ≤ y := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_le.mpr (cos_lt_cos_of_nonneg_of_le_pi hy0 ha1 (not_le.mp h')))
  · intro h
    exact cos_le_cos_of_nonneg_of_le_pi ha0 hy1 h

private lemma pcR_cosLt (a y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (hy0 : 0 ≤ y) (hy1 : y ≤ π) :
    cos y < cos a ↔ a < y := by
  rw [← not_le, pcR_cosLe y a hy0 hy1 ha0 ha1, not_le]

private lemma pcR_cG (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos a < cos x ↔ x < a ∨ 2 * π - a < x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, ← not_le, pcR_cosLe a y ha0 ha1 hy0 hy1, not_le]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_cGe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos a ≤ cos x ↔ x ≤ a ∨ 2 * π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, ← not_lt, pcR_cosLt a y ha0 ha1 hy0 hy1, not_lt]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_cL (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x < cos a ↔ a < x ∧ x < 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLt a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_cLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x ≤ cos a ↔ a ≤ x ∧ x ≤ 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLe a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_sG (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a < sin x ↔ a < x ∧ x < π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_sGe (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a ≤ sin x ↔ a ≤ x ∧ x ≤ π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_sL (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x < sin a ↔ x < a ∨ π - a < x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_sLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x ≤ sin a ↔ x ≤ a ∨ π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7s

private lemma pcR_cos34 : cos (3 * π / 4) = -(√2 / 2) := by
  rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]

private lemma pcR_cneg (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) : cos x < 0 ↔ π / 2 < x ∧ x < 3 * π / 2 := by
  have h := pcR_cL (π / 2) x (by positivity) (by linarith [pi_pos]) h0 h1
  rw [cos_pi_div_two] at h
  rw [h]; constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩

private lemma pcR_cpos (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) : 0 < cos x ↔ x < π / 2 ∨ 3 * π / 2 < x := by
  have h := pcR_cG (π / 2) x (by positivity) (by linarith [pi_pos]) h0 h1
  rw [cos_pi_div_two] at h
  rw [h]; constructor <;> rintro (a | a) <;> first | (left; linarith) | (right; linarith)

private lemma pcR_sq_gt (c t : ℝ) (ht : 0 ≤ t) : t ^ 2 < c ^ 2 ↔ t < c ∨ c < -t := by
  rw [sq_lt_sq, abs_of_nonneg ht, lt_abs]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

private lemma pcR_sq_ge (c t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ c ^ 2 ↔ t ≤ c ∨ c ≤ -t := by
  rw [sq_le_sq, abs_of_nonneg ht, le_abs]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

private lemma pcR_inv_le (c t : ℝ) (hc : c ≠ 0) (ht : 0 < t) : c⁻¹ ≤ t ↔ c < 0 ∨ 1 ≤ t * c := by
  rcases lt_or_gt_of_ne hc with h | h
  · have : c⁻¹ < 0 := inv_lt_zero.2 h
    constructor
    · intro _; left; exact h
    · intro _; linarith
  · have : 0 < c⁻¹ := inv_pos.2 h
    constructor
    · intro h'
      right
      have := mul_le_mul_of_nonneg_right h' h.le
      rw [inv_mul_cancel₀ hc] at this
      linarith
    · rintro (h' | h')
      · linarith
      · rw [inv_le_iff_one_le_mul₀ h]; linarith


lemma pcS_cot_ge (y c : ℝ) (h0 : 0 < y) (h1 : y < π) : c ≤ cot y ↔ y ≤ arccotR c := by
  have hp := pi_pos
  have e : cot y = tan (π / 2 - y) := by
    rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
  rw [e, ← arctan_le_arctan_iff, arctan_tan (by linarith) (by linarith)]
  unfold arccotR
  constructor <;> intro h <;> linarith

lemma pcS_arccot_neg_one : arccotR (-1) = 3 * π / 4 := by
  unfold arccotR
  rw [arctan_neg, arctan_one]; ring

/-- Stitz-Zeager Exercise 10.7.81: on `[-π, π]`, `cos x > √3/2` exactly for `x` in `(-π/6, π/6)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.81, p. 888"]
theorem exer_10_7_81 (x : ℝ) (hx0 : -π ≤ x) (hx1 : x ≤ π) :
    √3 / 2 < cos x ↔ x ∈ Set.Ioo (-(π / 6)) (π / 6) := by
  have hp := pi_pos
  rw [← cos_pi_div_six]
  simp only [Set.mem_Ioo]
  rcases le_or_gt 0 x with h | h
  · rw [pcR_cG (π / 6) x (by positivity) (by linarith) h (by linarith)]; iff_w7s
  · rw [← cos_add_two_pi x, pcR_cG (π / 6) (x + 2 * π) (by positivity) (by linarith) (by linarith) (by linarith)]
    iff_w7s

/-- Stitz-Zeager Exercise 10.7.82: on `[-π, π]`, `sin x > 1/3` exactly for `x` in
`(arcsin (1/3), π - arcsin (1/3))`. -/
@[kb "stitzzeager2013" "Exercise 10.7.82, p. 888"]
theorem exer_10_7_82 (x : ℝ) (hx0 : -π ≤ x) (hx1 : x ≤ π) :
    1 / 3 < sin x ↔ x ∈ Set.Ioo (arcsin (1 / 3)) (π - arcsin (1 / 3)) := by
  have hp := pi_pos
  have hsa : sin (arcsin (1 / 3 : ℝ)) = 1 / 3 := sin_arcsin (by norm_num) (by norm_num)
  have ha0 : 0 < arcsin (1 / 3 : ℝ) := arcsin_pos.2 (by norm_num)
  have ha1 : arcsin (1 / 3 : ℝ) ≤ π / 2 := arcsin_le_pi_div_two _
  simp only [Set.mem_Ioo]
  rcases le_or_gt 0 x with h | h
  · have key := pcR_sG (arcsin (1 / 3)) x ha0.le ha1 h (by linarith)
    rw [hsa] at key
    rw [key]
  · have key := pcR_sG (arcsin (1 / 3)) (x + 2 * π) ha0.le ha1 (by linarith) (by linarith)
    rw [hsa, sin_add_two_pi] at key
    rw [key]; iff_w7s

/-- Stitz-Zeager Exercise 10.7.83: on `[-π, π]` where `sec` is defined (`cos x ≠ 0`), `sec x ≤ 2` exactly for
`x` in `[-π, -π/2) ∪ [-π/3, π/3] ∪ (π/2, π]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.83, p. 888"]
theorem exer_10_7_83 (x : ℝ) (hx0 : -π ≤ x) (hx1 : x ≤ π) (hc : cos x ≠ 0) :
    (cos x)⁻¹ ≤ 2 ↔ x ∈ Set.Ico (-π) (-(π / 2)) ∪ Set.Icc (-(π / 3)) (π / 3) ∪ Set.Ioc (π / 2) π := by
  have hp := pi_pos
  rw [pcR_inv_le _ _ hc (by norm_num)]
  have e : (1 ≤ 2 * cos x) ↔ (cos (π / 3) ≤ cos x) := by
    rw [cos_pi_div_three]; constructor <;> intro <;> linarith
  rw [e]
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Icc, Set.mem_Ioc]
  rcases le_or_gt 0 x with h | h
  · rw [pcR_cneg x h (by linarith), pcR_cGe (π / 3) x (by positivity) (by linarith) h (by linarith)]
    iff_w7s
  · rw [← cos_add_two_pi x, pcR_cneg (x + 2 * π) (by linarith) (by linarith),
      pcR_cGe (π / 3) (x + 2 * π) (by positivity) (by linarith) (by linarith) (by linarith)]
    iff_w7s

/-- Stitz-Zeager Exercise 10.7.84: on `[-π, π]`, `sin² x < 3/4` exactly for `x` in
`[-π, -2π/3) ∪ (-π/3, π/3) ∪ (2π/3, π]`. (The book's printed answer is the complementary set.) -/
@[kb "stitzzeager2013" "Exercise 10.7.84, p. 888"]
theorem exer_10_7_84 (x : ℝ) (hx0 : -π ≤ x) (hx1 : x ≤ π) :
    sin x ^ 2 < 3 / 4 ↔ x ∈ Set.Ico (-π) (-(2 * π / 3)) ∪ Set.Ioo (-(π / 3)) (π / 3) ∪ Set.Ioc (2 * π / 3) π := by
  have hp := pi_pos
  have e : sin x ^ 2 < 3 / 4 ↔ (1 / 2 : ℝ) ^ 2 < cos x ^ 2 := by
    have := sin_sq_add_cos_sq x
    constructor <;> intro h <;> nlinarith
  rw [e, pcR_sq_gt _ _ (by norm_num)]
  have c1 : cos (π / 3) = 1 / 2 := cos_pi_div_three
  have c2 : cos (2 * π / 3) = 1 / 2 * (-1) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]; ring
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioo, Set.mem_Ioc]
  have k : ∀ y, 0 ≤ y → y ≤ 2 * π →
      (((1 / 2 : ℝ) < cos y ∨ cos y < -(1 / 2)) ↔ (y < π / 3 ∨ 5 * π / 3 < y) ∨ (2 * π / 3 < y ∧ y < 4 * π / 3)) := by
    intro y a b
    have a1 := pcR_cG (π / 3) y (by positivity) (by linarith) a b
    have a2 := pcR_cL (2 * π / 3) y (by positivity) (by linarith) a b
    rw [c1] at a1
    rw [c2] at a2
    have a2' : cos y < -(1 / 2) ↔ 2 * π / 3 < y ∧ y < 2 * π - 2 * π / 3 := by
      rw [← a2]; constructor <;> intro h <;> linarith
    rw [a1, a2']
    constructor <;> rintro ((h | h) | h) <;> first | (left; left; linarith) | (left; right; linarith) | (right; ao_w7s)
  rcases le_or_gt 0 x with h | h
  · rw [k x h (by linarith)]; iff_w7s
  · have := k (x + 2 * π) (by linarith) (by linarith)
    rw [cos_add_two_pi] at this
    rw [this]; iff_w7s

/-- Stitz-Zeager Exercise 10.7.85: on `[-π, π]` where `cot` is defined (`sin x ≠ 0`), `cot x ≥ -1` exactly for
`x` in `(-π, -π/4] ∪ (0, 3π/4]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.85, p. 888"]
theorem exer_10_7_85 (x : ℝ) (hx0 : -π ≤ x) (hx1 : x ≤ π) (hs : sin x ≠ 0) :
    -1 ≤ cot x ↔ x ∈ Set.Ioc (-π) (-(π / 4)) ∪ Set.Ioc 0 (3 * π / 4) := by
  have hp := pi_pos
  have n0 : x ≠ 0 := by rintro rfl; simp at hs
  have n1 : x ≠ π := by rintro rfl; simp at hs
  have n2 : x ≠ -π := by rintro rfl; simp at hs
  simp only [Set.mem_union, Set.mem_Ioc]
  rcases lt_or_gt_of_ne n0 with h | h
  · have e : cot x = cot (x + π) := by
      rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_add_pi, sin_add_pi, neg_div_neg_eq]
    have h2 : -π < x := lt_of_le_of_ne hx0 (Ne.symm n2)
    rw [e, pcS_cot_ge (x + π) (-1) (by linarith) (by linarith), pcS_arccot_neg_one]; iff_w7s
  · have h2 : x < π := lt_of_le_of_ne hx1 n1
    rw [pcS_cot_ge x (-1) h h2, pcS_arccot_neg_one]; iff_w7s

/-- Stitz-Zeager Exercise 10.7.86: on `[-π, π]`, `cos x ≥ sin x` exactly for `x` in `[-3π/4, π/4]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.86, p. 888"]
theorem exer_10_7_86 (x : ℝ) (hx0 : -π ≤ x) (hx1 : x ≤ π) :
    sin x ≤ cos x ↔ x ∈ Set.Icc (-(3 * π / 4)) (π / 4) := by
  have hp := pi_pos
  have s0 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  have s2 : √2 * (√2 / 2) = 1 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have e : sin x ≤ cos x ↔ ¬ cos (x + π / 4) < 0 := by
    rw [cos_add, cos_pi_div_four, sin_pi_div_four, not_lt]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [e]
  simp only [Set.mem_Icc]
  rcases le_or_gt 0 (x + π / 4) with h | h
  · rw [pcR_cneg _ h (by linarith), not_and_or, not_lt, not_lt]; iff_w7s
  · rw [← cos_add_two_pi (x + π / 4), pcR_cneg _ (by linarith) (by linarith), not_and_or, not_lt, not_lt]
    iff_w7s


end UndergradKB.Precalculus.Course
