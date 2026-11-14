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
Section 10.7 (trigonometric inequalities on `[0, 2π]`)

Solution sets are stated as `↔` with the book's union of intervals. Where Lean's `x⁻¹` or `cot` would take
the value `0` at a pole, the book's domain hypothesis (nonvanishing denominator) is part of the statement.
The file also holds the toolkit (`pcR_*` lemmas) used by the later parts. -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

/-- Close a goal built from `∧`, `∨` and linear (in)equalities in `π` and `x` by `linarith`. -/
syntax "ao_w7r" : tactic
macro_rules
  | `(tactic| ao_w7r) => `(tactic| first | linarith | (refine ⟨?_, ?_⟩ <;> ao_w7r) | (left; ao_w7r) | (right; ao_w7r))

/-- Split every hypothesis `∨`/`∧`, then close all goals with `ao_w7r`. -/
macro "iff_w7r" : tactic =>
  `(tactic| (constructor <;> intro hh <;> (try casesm* _ ∨ _, _ ∧ _) <;> ao_w7r))

lemma pcR_cosRed (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    ∃ y, 0 ≤ y ∧ y ≤ π ∧ cos x = cos y ∧ ((x ≤ π ∧ y = x) ∨ (π < x ∧ y = 2 * π - x)) := by
  by_cases h : x ≤ π
  · exact ⟨x, h0, h, rfl, Or.inl ⟨h, rfl⟩⟩
  · replace h := not_le.mp h
    exact ⟨2 * π - x, by linarith, by linarith, (cos_two_pi_sub x).symm, Or.inr ⟨h, rfl⟩⟩

lemma pcR_sinRed (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
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

lemma pcR_cosLe (a y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (hy0 : 0 ≤ y) (hy1 : y ≤ π) :
    cos y ≤ cos a ↔ a ≤ y := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_le.mpr (cos_lt_cos_of_nonneg_of_le_pi hy0 ha1 (not_le.mp h')))
  · intro h
    exact cos_le_cos_of_nonneg_of_le_pi ha0 hy1 h

lemma pcR_cosLt (a y : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (hy0 : 0 ≤ y) (hy1 : y ≤ π) :
    cos y < cos a ↔ a < y := by
  rw [← not_le, pcR_cosLe y a hy0 hy1 ha0 ha1, not_le]

lemma pcR_cG (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos a < cos x ↔ x < a ∨ 2 * π - a < x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, ← not_le, pcR_cosLe a y ha0 ha1 hy0 hy1, not_le]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_cGe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos a ≤ cos x ↔ x ≤ a ∨ 2 * π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, ← not_lt, pcR_cosLt a y ha0 ha1 hy0 hy1, not_lt]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_cL (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x < cos a ↔ a < x ∧ x < 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLt a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_cLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x ≤ cos a ↔ a ≤ x ∧ x ≤ 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLe a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_sG (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a < sin x ↔ a < x ∧ x < π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_sGe (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a ≤ sin x ↔ a ≤ x ∧ x ≤ π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_sL (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x < sin a ↔ x < a ∨ π - a < x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_sLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x ≤ sin a ↔ x ≤ a ∨ π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7r

lemma pcR_cos34 : cos (3 * π / 4) = -(√2 / 2) := by
  rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]

lemma pcR_cneg (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) : cos x < 0 ↔ π / 2 < x ∧ x < 3 * π / 2 := by
  have h := pcR_cL (π / 2) x (by positivity) (by linarith [pi_pos]) h0 h1
  rw [cos_pi_div_two] at h
  rw [h]; constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩

lemma pcR_cpos (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) : 0 < cos x ↔ x < π / 2 ∨ 3 * π / 2 < x := by
  have h := pcR_cG (π / 2) x (by positivity) (by linarith [pi_pos]) h0 h1
  rw [cos_pi_div_two] at h
  rw [h]; constructor <;> rintro (a | a) <;> first | (left; linarith) | (right; linarith)

lemma pcR_sq_gt (c t : ℝ) (ht : 0 ≤ t) : t ^ 2 < c ^ 2 ↔ t < c ∨ c < -t := by
  rw [sq_lt_sq, abs_of_nonneg ht, lt_abs]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

lemma pcR_sq_ge (c t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ c ^ 2 ↔ t ≤ c ∨ c ≤ -t := by
  rw [sq_le_sq, abs_of_nonneg ht, le_abs]
  constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)

lemma pcR_inv_le (c t : ℝ) (hc : c ≠ 0) (ht : 0 < t) : c⁻¹ ≤ t ↔ c < 0 ∨ 1 ≤ t * c := by
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

lemma pcR_cos2le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos (2 * x) ≤ 0 ↔ (π / 4 ≤ x ∧ x ≤ 3 * π / 4) ∨ (5 * π / 4 ≤ x ∧ x ≤ 7 * π / 4) := by
  have hp := pi_pos
  have key : ∀ y, 0 ≤ y → y ≤ 2 * π → (cos y ≤ 0 ↔ π / 2 ≤ y ∧ y ≤ 3 * π / 2) := fun y a b => by
    have := pcR_cLe (π / 2) y (by positivity) (by linarith) a b
    rw [cos_pi_div_two, show 2 * π - π / 2 = 3 * π / 2 by ring] at this
    exact this
  rcases le_or_gt x π with h | h
  · rw [key (2 * x) (by linarith) (by linarith)]; iff_w7r
  · rw [← cos_sub_two_pi (2 * x), key (2 * x - 2 * π) (by linarith) (by linarith)]; iff_w7r

/-- Stitz-Zeager Exercise 10.7.70: on `[0, 2π]`, `tan x ≥ √3` exactly for `x` in `[π/3, π/2) ∪ [4π/3, 3π/2)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.70, p. 887"]
theorem exer_10_7_70 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) :
    √3 ≤ tan x ↔ x ∈ Set.Ico (π / 3) (π / 2) ∪ Set.Ico (4 * π / 3) (3 * π / 2) := by
  have hp := pi_pos
  have hs : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  simp only [Set.mem_union, Set.mem_Ico]
  have mono : ∀ y, -(π / 2) < y → y < π / 2 → (√3 ≤ tan y ↔ π / 3 ≤ y) := fun y a b => by
    rw [← tan_pi_div_three]
    exact strictMonoOn_tan.le_iff_le ⟨by linarith, by linarith⟩ ⟨a, b⟩
  have t1 : tan (π / 2) = 0 := tan_pi_div_two
  have t2 : tan (3 * π / 2) = 0 := by
    rw [← tan_periodic.sub_eq (3 * π / 2), show 3 * π / 2 - π = π / 2 by ring, tan_pi_div_two]
  have t3 : ∀ y, tan (y - 2 * π) = tan y := fun y => by
    have := tan_sub_int_mul_pi y 2
    push_cast at this
    exact this
  rcases lt_trichotomy x (π / 2) with h | h | h
  · rw [mono x (by linarith) h]; iff_w7r
  · subst h
    rw [t1]; constructor
    · intro hh; linarith
    · intro hh; rcases hh with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
  · rcases lt_trichotomy x (3 * π / 2) with h' | h' | h'
    · have e : tan x = tan (x - π) := (tan_periodic.sub_eq x).symm
      rw [e, mono (x - π) (by linarith) (by linarith)]; iff_w7r
    · subst h'
      rw [t2]; constructor
      · intro hh; linarith
      · intro hh; rcases hh with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
    · rw [← t3 x, mono (x - 2 * π) (by linarith) (by linarith)]; iff_w7r

/-- Stitz-Zeager Exercise 10.7.71: on `[0, 2π]` (where `sec` is defined, `cos x ≠ 0`), `sec² x ≤ 4`
exactly for `x` in `[0, π/3] ∪ [2π/3, 4π/3] ∪ [5π/3, 2π]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.71, p. 887"]
theorem exer_10_7_71 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) (hc : cos x ≠ 0) :
    ((cos x)⁻¹) ^ 2 ≤ 4 ↔ x ∈ Set.Icc 0 (π / 3) ∪ Set.Icc (2 * π / 3) (4 * π / 3) ∪ Set.Icc (5 * π / 3) (2 * π) := by
  have hp := pi_pos
  have hc2 : 0 < cos x ^ 2 := by positivity
  have e : ((cos x)⁻¹) ^ 2 ≤ 4 ↔ (1 / 2 : ℝ) ^ 2 ≤ cos x ^ 2 := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ hc2]
    constructor <;> intro h <;> nlinarith
  rw [e, pcR_sq_ge _ _ (by norm_num)]
  have a1 := pcR_cGe (π / 3) x (by positivity) (by linarith) hx0 hx1
  have a2 := pcR_cLe (2 * π / 3) x (by positivity) (by linarith) hx0 hx1
  have c1 : cos (π / 3) = 1 / 2 := cos_pi_div_three
  have c2 : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  rw [c1] at a1
  rw [c2] at a2
  simp only [Set.mem_union, Set.mem_Icc]
  have b1 : (1 / 2 : ℝ) ≤ cos x ↔ x ≤ π / 3 ∨ 2 * π - π / 3 ≤ x := a1
  have b2 : cos x ≤ -(1 / 2 : ℝ) ↔ 2 * π / 3 ≤ x ∧ x ≤ 2 * π - 2 * π / 3 := a2
  rw [b1, b2]; iff_w7r

/-- Stitz-Zeager Exercise 10.7.72: on `[0, 2π]`, `cos² x > 1/2` exactly for `x` in
`[0, π/4) ∪ (3π/4, 5π/4) ∪ (7π/4, 2π]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.72, p. 887"]
theorem exer_10_7_72 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) :
    1 / 2 < cos x ^ 2 ↔ x ∈ Set.Ico 0 (π / 4) ∪ Set.Ioo (3 * π / 4) (5 * π / 4) ∪ Set.Ioc (7 * π / 4) (2 * π) := by
  have hp := pi_pos
  have s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : (1 / 2 : ℝ) = (√2 / 2) ^ 2 := by nlinarith
  rw [e, pcR_sq_gt _ _ (by positivity)]
  have a1 := pcR_cG (π / 4) x (by positivity) (by linarith) hx0 hx1
  have a2 := pcR_cL (3 * π / 4) x (by positivity) (by linarith) hx0 hx1
  rw [cos_pi_div_four] at a1
  rw [pcR_cos34] at a2
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioo, Set.mem_Ioc]
  rw [a1, a2]; iff_w7r

/-- Stitz-Zeager Exercise 10.7.73: on `[0, 2π]`, `cos 2x ≤ 0` exactly for `x` in `[π/4, 3π/4] ∪ [5π/4, 7π/4]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.73, p. 887"]
theorem exer_10_7_73 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) :
    cos (2 * x) ≤ 0 ↔ x ∈ Set.Icc (π / 4) (3 * π / 4) ∪ Set.Icc (5 * π / 4) (7 * π / 4) := by
  simp only [Set.mem_union, Set.mem_Icc]
  exact pcR_cos2le x hx0 hx1

/-- Stitz-Zeager Exercise 10.7.74: on `[0, 2π]`, `sin (x + π/3) > 1/2` exactly for `x` in
`[0, π/2) ∪ (11π/6, 2π]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.74, p. 887"]
theorem exer_10_7_74 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) :
    1 / 2 < sin (x + π / 3) ↔ x ∈ Set.Ico 0 (π / 2) ∪ Set.Ioc (11 * π / 6) (2 * π) := by
  have hp := pi_pos
  rw [← sin_pi_div_six]
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
  rcases le_or_gt x (5 * π / 3) with h | h
  · rw [pcR_sG (π / 6) (x + π / 3) (by positivity) (by linarith) (by linarith) (by linarith)]; iff_w7r
  · rw [← sin_sub_two_pi (x + π / 3),
      pcR_sG (π / 6) (x + π / 3 - 2 * π) (by positivity) (by linarith) (by linarith) (by linarith)]
    iff_w7r

/-- Stitz-Zeager Exercise 10.7.75: on `[0, 2π]` where `cot` is defined (`sin x ≠ 0`), `cot² x ≥ 1/3` exactly for
`x` in `(0, π/3] ∪ [2π/3, π) ∪ (π, 4π/3] ∪ [5π/3, 2π)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.75, p. 887"]
theorem exer_10_7_75 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) (hs : sin x ≠ 0) :
    1 / 3 ≤ (cot x) ^ 2 ↔ x ∈ Set.Ioc 0 (π / 3) ∪ Set.Ico (2 * π / 3) π ∪ Set.Ioc π (4 * π / 3) ∪ Set.Ico (5 * π / 3) (2 * π) := by
  have hp := pi_pos
  have hs2 : 0 < sin x ^ 2 := by positivity
  have e : 1 / 3 ≤ (cot x) ^ 2 ↔ (1 / 2 : ℝ) ^ 2 ≤ cos x ^ 2 := by
    rw [cot_eq_cos_div_sin, div_pow, le_div_iff₀ hs2]
    have := sin_sq_add_cos_sq x
    constructor <;> intro h <;> nlinarith
  rw [e, pcR_sq_ge _ _ (by norm_num)]
  have a1 := pcR_cGe (π / 3) x (by positivity) (by linarith) hx0 hx1
  have a2 := pcR_cLe (2 * π / 3) x (by positivity) (by linarith) hx0 hx1
  have c1 : cos (π / 3) = 1 / 2 := cos_pi_div_three
  have c2 : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  rw [c1] at a1
  rw [c2] at a2
  have b1 : (1 / 2 : ℝ) ≤ cos x ↔ x ≤ π / 3 ∨ 2 * π - π / 3 ≤ x := a1
  have b2 : cos x ≤ -(1 / 2 : ℝ) ↔ 2 * π / 3 ≤ x ∧ x ≤ 2 * π - 2 * π / 3 := a2
  have n0 : x ≠ 0 := by rintro rfl; simp at hs
  have n2 : x ≠ 2 * π := by rintro rfl; simp at hs
  have n1 : x ≠ π := by rintro rfl; simp at hs
  have h0 : 0 < x := lt_of_le_of_ne hx0 (Ne.symm n0)
  have h2 : x < 2 * π := lt_of_le_of_ne hx1 n2
  simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ico]
  rw [b1, b2]
  rcases lt_or_gt_of_ne n1 with h | h <;> iff_w7r

/-- Stitz-Zeager Exercise 10.7.79: on `[0, 2π]` where `sec` is defined (`cos x ≠ 0`), `sec x ≤ √2` exactly for
`x` in `[0, π/4] ∪ (π/2, 3π/2) ∪ [7π/4, 2π]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.79, p. 887"]
theorem exer_10_7_79 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) (hc : cos x ≠ 0) :
    (cos x)⁻¹ ≤ √2 ↔ x ∈ Set.Icc 0 (π / 4) ∪ Set.Ioo (π / 2) (3 * π / 2) ∪ Set.Icc (7 * π / 4) (2 * π) := by
  have hp := pi_pos
  have s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s0 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  rw [pcR_inv_le _ _ hc s0, pcR_cneg x hx0 hx1]
  have e : 1 ≤ √2 * cos x ↔ √2 / 2 ≤ cos x := by
    constructor <;> intro h <;> nlinarith
  rw [e]
  have a1 := pcR_cGe (π / 4) x (by positivity) (by linarith) hx0 hx1
  rw [cos_pi_div_four] at a1
  rw [a1]
  simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioo]
  iff_w7r

lemma pcR_cot_le (x c : ℝ) (h0 : 0 < x) (h1 : x < π) : cot x ≤ c ↔ arccotR c ≤ x := by
  have hp := pi_pos
  have e : cot x = tan (π / 2 - x) := by
    rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_pi_div_two_sub, cos_pi_div_two_sub]
  rw [e, ← arctan_le_arctan_iff, arctan_tan (by linarith) (by linarith)]
  unfold arccotR
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 10.7.80: on `[0, 2π]` where `cot` is defined (`sin x ≠ 0`), `cot x ≤ 4` exactly for `x` in
`[arccot 4, π) ∪ [π + arccot 4, 2π)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.80, p. 887"]
theorem exer_10_7_80 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * π) (hs : sin x ≠ 0) :
    cot x ≤ 4 ↔ x ∈ Set.Ico (arccotR 4) π ∪ Set.Ico (π + arccotR 4) (2 * π) := by
  have hp := pi_pos
  obtain ⟨a0, a1⟩ := arccotR_properties.1 4
  have n0 : x ≠ 0 := by rintro rfl; simp at hs
  have n2 : x ≠ 2 * π := by rintro rfl; simp at hs
  have n1 : x ≠ π := by rintro rfl; simp at hs
  have h0 : 0 < x := lt_of_le_of_ne hx0 (Ne.symm n0)
  have h2 : x < 2 * π := lt_of_le_of_ne hx1 n2
  simp only [Set.mem_union, Set.mem_Ico]
  rcases lt_or_gt_of_ne n1 with h | h
  · rw [pcR_cot_le x 4 h0 h]; iff_w7r
  · have e : cot x = cot (x - π) := by
      rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_sub_pi, sin_sub_pi, neg_div_neg_eq]
    rw [e, pcR_cot_le (x - π) 4 (by linarith) (by linarith)]; iff_w7r

end UndergradKB.Precalculus.Course
