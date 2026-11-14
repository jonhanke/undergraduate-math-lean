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
Section 10.7 (trigonometric inequalities on `[-2π, 2π]`)

Solution sets are stated as `↔` with the book's union of intervals; where Lean's `x⁻¹` or `cot` would take
the value `0` at a pole, the book's domain hypothesis (nonvanishing denominator) is part of the statement.
The private `pcR_*` lemmas are the interval toolkit of `Ch10Exer2R` (copied, so that this file stands alone). -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

syntax "ao_w7t" : tactic
macro_rules
  | `(tactic| ao_w7t) => `(tactic| first | linarith | (refine ⟨?_, ?_⟩ <;> ao_w7t) | (left; ao_w7t) | (right; ao_w7t))

/-- Split every hypothesis `∨`/`∧`, then close all goals with `ao_w7t`. -/
macro "iff_w7t" : tactic =>
  `(tactic| (constructor <;> intro hh <;> (try casesm* _ ∨ _, _ ∧ _) <;> ao_w7t))

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
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

private lemma pcR_cGe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos a ≤ cos x ↔ x ≤ a ∨ 2 * π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, ← not_lt, pcR_cosLt a y ha0 ha1 hy0 hy1, not_lt]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

private lemma pcR_cL (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x < cos a ↔ a < x ∧ x < 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLt a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

private lemma pcR_cLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x ≤ cos a ↔ a ≤ x ∧ x ≤ 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLe a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

private lemma pcR_sG (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a < sin x ↔ a < x ∧ x < π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

private lemma pcR_sGe (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a ≤ sin x ↔ a ≤ x ∧ x ≤ π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

private lemma pcR_sL (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x < sin a ↔ x < a ∨ π - a < x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

private lemma pcR_sLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x ≤ sin a ↔ x ≤ a ∨ π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7t

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


private lemma pcR_cos2le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos (2 * x) ≤ 0 ↔ (π / 4 ≤ x ∧ x ≤ 3 * π / 4) ∨ (5 * π / 4 ≤ x ∧ x ≤ 7 * π / 4) := by
  have hp := pi_pos
  have key : ∀ y, 0 ≤ y → y ≤ 2 * π → (cos y ≤ 0 ↔ π / 2 ≤ y ∧ y ≤ 3 * π / 2) := fun y a b => by
    have := pcR_cLe (π / 2) y (by positivity) (by linarith) a b
    rw [cos_pi_div_two, show 2 * π - π / 2 = 3 * π / 2 by ring] at this
    exact this
  rcases le_or_gt x π with h | h
  · rw [key (2 * x) (by linarith) (by linarith)]; iff_w7t
  · rw [← cos_sub_two_pi (2 * x), key (2 * x - 2 * π) (by linarith) (by linarith)]; iff_w7t

lemma pcT_cot_ge (y c : ℝ) (h0 : 0 < y) (h1 : y < π) : c ≤ cot y ↔ y ≤ arccotR c := by
  have hp := pi_pos
  have e : cot y = tan (π / 2 - y) := by
    rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
  rw [e, ← arctan_le_arctan_iff, arctan_tan (by linarith) (by linarith)]
  unfold arccotR
  constructor <;> intro h <;> linarith

lemma pcT_sinsign (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 2 * π) :
    (0 < sin y ↔ 0 < y ∧ y < π) ∧ (sin y < 0 ↔ π < y ∧ y < 2 * π) := by
  have hp := pi_pos
  constructor
  · have := pcR_sG 0 y le_rfl (by positivity) h0 h1
    simpa using this
  · rcases le_or_gt y π with h | h
    · have : 0 ≤ sin y := sin_nonneg_of_nonneg_of_le_pi h0 h
      constructor
      · intro hh; linarith
      · rintro ⟨a, b⟩; linarith
    · have k := pcR_sG 0 (y - π) le_rfl (by positivity) (by linarith) (by linarith)
      simp only [sin_zero, sin_sub_pi, sub_zero] at k
      constructor
      · intro hh
        have := k.mp (by linarith)
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨a, b⟩
        have := k.mpr ⟨by linarith, by linarith⟩
        linarith

lemma pcT_cos2_shift (x : ℝ) : cos (2 * (x + 2 * π)) = cos (2 * x) := by
  rw [show 2 * (x + 2 * π) = 2 * x + 2 * π + 2 * π by ring, cos_add_two_pi, cos_add_two_pi]

lemma pcT_sin2_shift (x : ℝ) : sin (2 * (x + 2 * π)) = sin (2 * x) := by
  rw [show 2 * (x + 2 * π) = 2 * x + 2 * π + 2 * π by ring, sin_add_two_pi, sin_add_two_pi]

lemma pcT_inv_gt1 (s : ℝ) : 1 < s⁻¹ ↔ 0 < s ∧ s < 1 := by
  constructor
  · intro h
    have h0 : 0 < s := by
      by_contra h'
      have := inv_nonpos.2 (not_lt.mp h')
      linarith
    exact ⟨h0, (one_lt_inv₀ h0).1 h⟩
  · rintro ⟨h0, h1⟩
    exact (one_lt_inv₀ h0).2 h1

/-- Stitz-Zeager Exercise 10.7.87: on `[-2π, 2π]`, `csc x > 1` exactly for `x` in
`(-2π, -3π/2) ∪ (-3π/2, -π) ∪ (0, π/2) ∪ (π/2, π)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.87, p. 888"]
theorem exer_10_7_87 (x : ℝ) (hx0 : -(2 * π) ≤ x) (hx1 : x ≤ 2 * π) :
    1 < (sin x)⁻¹ ↔ x ∈ Set.Ioo (-(2 * π)) (-(3 * π / 2)) ∪ Set.Ioo (-(3 * π / 2)) (-π) ∪
      Set.Ioo 0 (π / 2) ∪ Set.Ioo (π / 2) π := by
  have hp := pi_pos
  rw [pcT_inv_gt1]
  simp only [Set.mem_union, Set.mem_Ioo]
  have k : ∀ y, 0 ≤ y → y ≤ 2 * π →
      ((0 < sin y ∧ sin y < 1) ↔ (0 < y ∧ y < π / 2) ∨ (π / 2 < y ∧ y < π)) := by
    intro y a b
    have a1 := (pcT_sinsign y a b).1
    have a2 := pcR_sL (π / 2) y (by positivity) le_rfl a b
    rw [sin_pi_div_two, show π - π / 2 = π / 2 by ring] at a2
    rw [a1, a2]; iff_w7t
  rcases le_or_gt 0 x with h | h
  · rw [k x h (by linarith)]; iff_w7t
  · have := k (x + 2 * π) (by linarith) (by linarith)
    rw [sin_add_two_pi] at this
    rw [this]; iff_w7t

/-- Stitz-Zeager Exercise 10.7.88: on `[-2π, 2π]`, `cos x ≤ 5/3` holds throughout. -/
@[kb "stitzzeager2013" "Exercise 10.7.88, p. 888"]
theorem exer_10_7_88 (x : ℝ) (hx0 : -(2 * π) ≤ x) (hx1 : x ≤ 2 * π) :
    cos x ≤ 5 / 3 ↔ x ∈ Set.Icc (-(2 * π)) (2 * π) := by
  simp only [Set.mem_Icc]
  constructor
  · intro _; exact ⟨hx0, hx1⟩
  · intro _; linarith [cos_le_one x]

/-- Stitz-Zeager Exercise 10.7.89: on `[-2π, 2π]` where `cot` is defined (`sin x ≠ 0`), `cot x ≥ 5` exactly for `x` in
`(-2π, arccot 5 - 2π] ∪ (-π, arccot 5 - π] ∪ (0, arccot 5] ∪ (π, π + arccot 5]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.89, p. 888"]
theorem exer_10_7_89 (x : ℝ) (hx0 : -(2 * π) ≤ x) (hx1 : x ≤ 2 * π) (hs : sin x ≠ 0) :
    5 ≤ cot x ↔ x ∈ Set.Ioc (-(2 * π)) (arccotR 5 - 2 * π) ∪ Set.Ioc (-π) (arccotR 5 - π) ∪
      Set.Ioc 0 (arccotR 5) ∪ Set.Ioc π (π + arccotR 5) := by
  have hp := pi_pos
  obtain ⟨a0, a1⟩ := arccotR_properties.1 5
  have n0 : x ≠ 0 := by rintro rfl; simp at hs
  have n1 : x ≠ π := by rintro rfl; simp at hs
  have n2 : x ≠ -π := by rintro rfl; simp at hs
  have n3 : x ≠ 2 * π := by rintro rfl; simp at hs
  have n4 : x ≠ -(2 * π) := by
    rintro rfl
    simp [sin_neg] at hs
  have h3 : x < 2 * π := lt_of_le_of_ne hx1 n3
  have h4 : -(2 * π) < x := lt_of_le_of_ne hx0 (Ne.symm n4)
  have eadd : ∀ z, cot (z + π) = cot z := fun z => by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_add_pi, sin_add_pi, neg_div_neg_eq]
  simp only [Set.mem_union, Set.mem_Ioc]
  rcases lt_or_gt_of_ne n2 with a | a
  · have e : cot x = cot (x + π + π) := by rw [eadd, eadd]
    rw [e, pcT_cot_ge (x + π + π) 5 (by linarith) (by linarith)]; iff_w7t
  · rcases lt_or_gt_of_ne n0 with b | b
    · rw [← eadd x, pcT_cot_ge (x + π) 5 (by linarith) (by linarith)]; iff_w7t
    · rcases lt_or_gt_of_ne n1 with c | c
      · rw [pcT_cot_ge x 5 b c]; iff_w7t
      · have e : cot x = cot (x - π) := by rw [← eadd (x - π)]; congr 1; ring
        rw [e, pcT_cot_ge (x - π) 5 (by linarith) (by linarith)]; iff_w7t

/-- Stitz-Zeager Exercise 10.7.90: on `[-2π, 2π]` where `tan` is defined (`cos x ≠ 0`), `tan² x ≥ 1` exactly for `x` in
`[-7π/4, -3π/2) ∪ (-3π/2, -5π/4] ∪ [-3π/4, -π/2) ∪ (-π/2, -π/4] ∪ [π/4, π/2) ∪ (π/2, 3π/4] ∪ [5π/4, 3π/2) ∪ (3π/2, 7π/4]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.90, p. 888"]
theorem exer_10_7_90 (x : ℝ) (hx0 : -(2 * π) ≤ x) (hx1 : x ≤ 2 * π) (hc : cos x ≠ 0) :
    1 ≤ tan x ^ 2 ↔ x ∈ Set.Ico (-(7 * π / 4)) (-(3 * π / 2)) ∪ Set.Ioc (-(3 * π / 2)) (-(5 * π / 4)) ∪
      Set.Ico (-(3 * π / 4)) (-(π / 2)) ∪ Set.Ioc (-(π / 2)) (-(π / 4)) ∪
      Set.Ico (π / 4) (π / 2) ∪ Set.Ioc (π / 2) (3 * π / 4) ∪
      Set.Ico (5 * π / 4) (3 * π / 2) ∪ Set.Ioc (3 * π / 2) (7 * π / 4) := by
  have hp := pi_pos
  have hc2 : 0 < cos x ^ 2 := by positivity
  have e : 1 ≤ tan x ^ 2 ↔ cos (2 * x) ≤ 0 := by
    rw [tan_eq_sin_div_cos, div_pow, one_le_div hc2, cos_two_mul]
    have := sin_sq_add_cos_sq x
    constructor <;> intro h <;> nlinarith
  rw [e]
  have n1 : x ≠ π / 2 := by rintro rfl; simp at hc
  have n2 : x ≠ 3 * π / 2 := by
    rintro rfl
    have : cos (3 * π / 2) = 0 := by
      rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; simp
    exact hc this
  have n3 : x ≠ -(π / 2) := by rintro rfl; simp at hc
  have n4 : x ≠ -(3 * π / 2) := by
    rintro rfl
    have : cos (3 * π / 2) = 0 := by
      rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; simp
    exact hc (by rw [cos_neg]; exact this)
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
  rcases le_or_gt 0 x with h | h
  · rw [pcR_cos2le x h hx1]
    rcases lt_or_gt_of_ne n1 with p | p <;> rcases lt_or_gt_of_ne n2 with q | q <;> iff_w7t
  · rw [← pcT_cos2_shift x, pcR_cos2le (x + 2 * π) (by linarith) (by linarith)]
    rcases lt_or_gt_of_ne n3 with p | p <;> rcases lt_or_gt_of_ne n4 with q | q <;> iff_w7t

lemma pcT_sin_sub (y : ℝ) :
    sin (2 * y) - sin y = sin y * (2 * cos y - 1) := by
  rw [sin_two_mul]; ring

lemma pcT_core91 (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 2 * π) :
    sin y ≤ sin (2 * y) ↔ (0 ≤ y ∧ y ≤ π / 3) ∨ (π ≤ y ∧ y ≤ 5 * π / 3) ∨ y = 2 * π := by
  have hp := pi_pos
  obtain ⟨hpos, hneg⟩ := pcT_sinsign y h0 h1
  have a1 := pcR_cG (π / 3) y (by positivity) (by linarith) h0 h1
  have a2 := pcR_cGe (π / 3) y (by positivity) (by linarith) h0 h1
  rw [cos_pi_div_three] at a1 a2
  have e := pcT_sin_sub y
  rcases lt_trichotomy (sin y) 0 with hs | hs | hs
  · have hy := hneg.mp hs
    have k : sin y ≤ sin (2 * y) ↔ cos y ≤ 1 / 2 := by
      constructor <;> intro h <;> nlinarith
    rw [k, ← not_lt, a1]
    constructor
    · intro h
      right; left
      refine ⟨by linarith, ?_⟩
      by_contra hh
      exact h (Or.inr (by linarith))
    · rintro (⟨a, b⟩ | ⟨a, b⟩ | a) <;> rintro (c | c) <;> linarith [hy.1, hy.2]
  · have hy : y = 0 ∨ y = π ∨ y = 2 * π := by
      have n1 : ¬ (0 < sin y) := by linarith
      have n2 : ¬ (sin y < 0) := by linarith
      rw [hpos] at n1
      rw [hneg] at n2
      rcases lt_trichotomy y π with a | a | a
      · left
        by_contra hh
        exact n1 ⟨lt_of_le_of_ne h0 (Ne.symm hh), a⟩
      · right; left; exact a
      · right; right
        by_contra hh
        exact n2 ⟨a, lt_of_le_of_ne h1 hh⟩
    have : sin y ≤ sin (2 * y) := by rw [sin_two_mul, hs]; simp
    constructor
    · intro _
      rcases hy with h | h | h
      · left; constructor <;> linarith
      · right; left; constructor <;> linarith
      · right; right; exact h
    · intro _; exact this
  · have hy := hpos.mp hs
    have k : sin y ≤ sin (2 * y) ↔ 1 / 2 ≤ cos y := by
      constructor <;> intro h <;> nlinarith
    rw [k, a2]
    constructor
    · rintro (h | h)
      · left; exact ⟨h0, h⟩
      · exfalso; linarith [hy.2]
    · rintro (⟨a, b⟩ | ⟨a, b⟩ | a)
      · left; exact b
      · exfalso; linarith [hy.2]
      · exfalso; linarith [hy.2]

/-- Stitz-Zeager Exercise 10.7.91: on `[-2π, 2π]`, `sin 2x ≥ sin x` exactly for `x` in
`[-2π, -5π/3] ∪ [-π, -π/3] ∪ [0, π/3] ∪ [π, 5π/3] ∪ {2π}`. (The book's answer omits the endpoint `2π`, where both
sides are `0`.) -/
@[kb "stitzzeager2013" "Exercise 10.7.91, p. 888"]
theorem exer_10_7_91 (x : ℝ) (hx0 : -(2 * π) ≤ x) (hx1 : x ≤ 2 * π) :
    sin x ≤ sin (2 * x) ↔ x ∈ Set.Icc (-(2 * π)) (-(5 * π / 3)) ∪ Set.Icc (-π) (-(π / 3)) ∪
      Set.Icc 0 (π / 3) ∪ Set.Icc π (5 * π / 3) ∪ {2 * π} := by
  have hp := pi_pos
  simp only [Set.mem_union, Set.mem_Icc, Set.mem_singleton_iff]
  rcases le_or_gt 0 x with h | h
  · rw [pcT_core91 x h hx1]; iff_w7t
  · have := pcT_core91 (x + 2 * π) (by linarith) (by linarith)
    rw [sin_add_two_pi, pcT_sin2_shift] at this
    rw [this]; iff_w7t

lemma pcT_core92 (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 2 * π) :
    cos (2 * y) ≤ sin y ↔ (π / 6 ≤ y ∧ y ≤ 5 * π / 6) ∨ y = 3 * π / 2 := by
  have hp := pi_pos
  have a1 := pcR_sGe (π / 6) y (by positivity) (by linarith) h0 h1
  rw [sin_pi_div_six] at a1
  have a2 : sin y ≤ -1 ↔ y = 3 * π / 2 := by
    constructor
    · intro h
      rcases le_or_gt y π with h' | h'
      · have := sin_nonneg_of_nonneg_of_le_pi h0 h'
        linarith
      · have k := pcR_sGe (π / 2) (y - π) (by positivity) le_rfl (by linarith) (by linarith)
        rw [sin_pi_div_two, sin_sub_pi] at k
        have := k.mp (by linarith)
        linarith [this.1, this.2]
    · rintro rfl
      rw [show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]
  have e : cos (2 * y) ≤ sin y ↔ 1 / 2 ≤ sin y ∨ sin y ≤ -1 := by
    rw [cos_two_mul]
    have := sin_sq_add_cos_sq y
    have h1' := neg_one_le_sin y
    constructor
    · intro h
      by_contra hh
      push Not at hh
      nlinarith [hh.1, hh.2]
    · rintro (h | h) <;> nlinarith
  rw [e, a1, a2]; iff_w7t

/-- Stitz-Zeager Exercise 10.7.92: on `[-2π, 2π]`, `cos 2x ≤ sin x` exactly for `x` in
`[-11π/6, -7π/6] ∪ [π/6, 5π/6] ∪ {-π/2, 3π/2}`. -/
@[kb "stitzzeager2013" "Exercise 10.7.92, p. 888"]
theorem exer_10_7_92 (x : ℝ) (hx0 : -(2 * π) ≤ x) (hx1 : x ≤ 2 * π) :
    cos (2 * x) ≤ sin x ↔ x ∈ Set.Icc (-(11 * π / 6)) (-(7 * π / 6)) ∪ Set.Icc (π / 6) (5 * π / 6) ∪
      {-(π / 2), 3 * π / 2} := by
  have hp := pi_pos
  simp only [Set.mem_union, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases le_or_gt 0 x with h | h
  · rw [pcT_core92 x h hx1]; iff_w7t
  · have := pcT_core92 (x + 2 * π) (by linarith) (by linarith)
    rw [sin_add_two_pi, pcT_cos2_shift] at this
    rw [this]; iff_w7t

/-- Stitz-Zeager Exercise 10.7.93: for `x` with `2x` in the domain of `arcsin` (`|x| ≤ 1/2`), `arcsin (2x) > 0`
exactly for `x` in `(0, 1/2]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.93, p. 888"]
theorem exer_10_7_93 (x : ℝ) (hx0 : -(1 / 2) ≤ x) (hx1 : x ≤ 1 / 2) :
    0 < arcsin (2 * x) ↔ x ∈ Set.Ioc 0 (1 / 2) := by
  rw [arcsin_pos]
  simp only [Set.mem_Ioc]
  constructor
  · intro h; exact ⟨by linarith, hx1⟩
  · rintro ⟨h, _⟩; linarith

end UndergradKB.Precalculus.Course
