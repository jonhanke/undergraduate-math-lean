import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.TrigExtras
import UndergradKB.Precalculus.Course.Ch10Extra

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.7 (inverse trigonometric equations and inequalities)

Solution sets are stated as `↔` with the book's union of intervals; where Lean's `x⁻¹` or `cot` would take
the value `0` at a pole, the book's domain hypothesis (nonvanishing denominator) is part of the statement.
The private `pcR_*` lemmas are the interval toolkit of `Ch10Exer2R` (copied, so that this file stands alone). -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

syntax "ao_w7u" : tactic
macro_rules
  | `(tactic| ao_w7u) => `(tactic| first | linarith | (refine ⟨?_, ?_⟩ <;> ao_w7u) | (left; ao_w7u) | (right; ao_w7u))

/-- Split every hypothesis `∨`/`∧`, then close all goals with `ao_w7u`. -/
macro "iff_w7u" : tactic =>
  `(tactic| (constructor <;> intro hh <;> (try casesm* _ ∨ _, _ ∧ _) <;> ao_w7u))

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
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

private lemma pcR_cGe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos a ≤ cos x ↔ x ≤ a ∨ 2 * π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, ← not_lt, pcR_cosLt a y ha0 ha1 hy0 hy1, not_lt]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

private lemma pcR_cL (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x < cos a ↔ a < x ∧ x < 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLt a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

private lemma pcR_cLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x ≤ cos a ↔ a ≤ x ∧ x ≤ 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLe a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

private lemma pcR_sG (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a < sin x ↔ a < x ∧ x < π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

private lemma pcR_sGe (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a ≤ sin x ↔ a ≤ x ∧ x ≤ π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

private lemma pcR_sL (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x < sin a ↔ x < a ∨ π - a < x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

private lemma pcR_sLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x ≤ sin a ↔ x ≤ a ∨ π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7u

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


private lemma pcU_arccos_eq {t a : ℝ} (ha0 : 0 < a) (ha1 : a < π) (h : arccos t = a) : t = cos a := by
  rcases le_or_gt t 1 with h1 | h1
  · rcases le_or_gt (-1) t with h2 | h2
    · rw [← h, cos_arccos h2 h1]
    · rw [arccos_of_le_neg_one h2.le] at h; linarith
  · rw [arccos_of_one_le h1.le] at h; linarith

private lemma pcU_arcsin_eq {t a : ℝ} (ha0 : -(π / 2) < a) (ha1 : a < π / 2) (h : arcsin t = a) : t = sin a := by
  rcases le_or_gt t 1 with h1 | h1
  · rcases le_or_gt (-1) t with h2 | h2
    · rw [← h, sin_arcsin h2 h1]
    · rw [arcsin_of_le_neg_one h2.le] at h; linarith
  · rw [arcsin_of_one_le h1.le] at h; linarith

/-- Stitz-Zeager Exercise 10.7.63: `4 arcsec (x/2) = π` has the single solution `x = 2√2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.63, p. 887"]
theorem exer_10_7_63 (x : ℝ) : 4 * arcsec (x / 2) = π ↔ x = 2 * √2 := by
  have hp := pi_pos
  have s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s0 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  unfold arcsec
  constructor
  · intro h
    have ht := pcU_arccos_eq (t := 1 / (x / 2)) (a := π / 4) (by positivity) (by linarith) (by linarith)
    rw [cos_pi_div_four] at ht
    have hx : x ≠ 0 := by
      rintro rfl
      simp at ht
      linarith
    field_simp at ht
    nlinarith
  · rintro rfl
    have e : 1 / (2 * √2 / 2) = cos (π / 4) := by
      rw [cos_pi_div_four]; field_simp; nlinarith
    rw [e, arccos_cos (by positivity) (by linarith)]
    ring

/-- Stitz-Zeager Exercise 10.7.64: `12 arccsc (x/3) = 2π` has the single solution `x = 6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.64, p. 887"]
theorem exer_10_7_64 (x : ℝ) : 12 * arccsc (x / 3) = 2 * π ↔ x = 6 := by
  have hp := pi_pos
  unfold arccsc
  constructor
  · intro h
    have ht := pcU_arcsin_eq (t := 1 / (x / 3)) (a := π / 6) (by linarith) (by linarith) (by linarith)
    rw [sin_pi_div_six] at ht
    have hx : x ≠ 0 := by
      rintro rfl
      simp at ht
    field_simp at ht
    linarith
  · rintro rfl
    have e : 1 / ((6 : ℝ) / 3) = sin (π / 6) := by
      rw [sin_pi_div_six]; norm_num
    rw [e, arcsin_sin (by linarith) (by linarith)]
    ring

/-- Stitz-Zeager Exercise 10.7.95: `6 arccot (7x) ≥ π` exactly for `x ≤ √3/7`. -/
@[kb "stitzzeager2013" "Exercise 10.7.95, p. 888"]
theorem exer_10_7_95 (x : ℝ) : π ≤ 6 * arccotR (7 * x) ↔ x ∈ Set.Iic (√3 / 7) := by
  have hp := pi_pos
  have h3 : arctan (√3) = π / 3 := by
    rw [← tan_pi_div_three]; exact arctan_tan (by linarith) (by linarith)
  have e : π ≤ 6 * arccotR (7 * x) ↔ arctan (7 * x) ≤ arctan (√3) := by
    unfold arccotR
    rw [h3]; constructor <;> intro h <;> linarith
  rw [e, arctan_le_arctan_iff]
  simp only [Set.mem_Iic]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 10.7.96: `π > 2 arctan x` for every real `x`. -/
@[kb "stitzzeager2013" "Exercise 10.7.96, p. 888"]
theorem exer_10_7_96 (x : ℝ) : π > 2 * arctan x ↔ x ∈ (Set.univ : Set ℝ) := by
  have := arctan_lt_pi_div_two x
  simp only [Set.mem_univ, iff_true]
  linarith

/-- Stitz-Zeager Exercise 10.7.98: for `x` in the domain `[-1, 1]` of `arccos`,
`12 arccos² x + 2π² > 11π arccos x` exactly for `x` in `[-1, -1/2) ∪ (√2/2, 1]`. -/
@[kb "stitzzeager2013" "Exercise 10.7.98, p. 888"]
theorem exer_10_7_98 (x : ℝ) (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    12 * arccos x ^ 2 + 2 * π ^ 2 > 11 * π * arccos x ↔ x ∈ Set.Ico (-1) (-(1 / 2)) ∪ Set.Ioc (√2 / 2) 1 := by
  have hp := pi_pos
  have ht0 : 0 ≤ arccos x := arccos_nonneg x
  have ht1 : arccos x ≤ π := arccos_le_pi x
  have hcx : cos (arccos x) = x := cos_arccos hx0 hx1
  have A : arccos x < π / 4 ↔ √2 / 2 < x := by
    have := pcR_cosLe (π / 4) (arccos x) (by positivity) (by linarith) ht0 ht1
    rw [hcx, cos_pi_div_four] at this
    constructor
    · intro h; by_contra hh; have := this.mp (not_lt.mp hh); linarith
    · intro h; by_contra hh; have := this.mpr (not_lt.mp hh); linarith
  have B : 2 * π / 3 < arccos x ↔ x < -(1 / 2) := by
    have := pcR_cosLe (arccos x) (2 * π / 3) ht0 ht1 (by positivity) (by linarith)
    have c2 : cos (2 * π / 3) = -(1 / 2) := by
      rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
    rw [hcx, c2] at this
    constructor
    · intro h; by_contra hh; have := this.mp (not_lt.mp hh); linarith
    · intro h; by_contra hh; have := this.mpr (not_lt.mp hh); linarith
  have e : 12 * arccos x ^ 2 + 2 * π ^ 2 > 11 * π * arccos x ↔ arccos x < π / 4 ∨ 2 * π / 3 < arccos x := by
    constructor
    · intro h
      by_contra hh
      push Not at hh
      nlinarith [mul_nonneg (show 0 ≤ 4 * arccos x - π by linarith [hh.1]) (show 0 ≤ 2 * π - 3 * arccos x by linarith [hh.2])]
    · rintro (h | h)
      · nlinarith [mul_pos (show 0 < π - 4 * arccos x by linarith) (show 0 < 2 * π - 3 * arccos x by linarith)]
      · nlinarith [mul_pos (show 0 < 4 * arccos x - π by linarith) (show 0 < 3 * arccos x - 2 * π by linarith)]
  rw [e, A, B]
  simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
  constructor
  · rintro (h | h)
    · right; exact ⟨h, hx1⟩
    · left; exact ⟨hx0, h⟩
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · right; exact h
    · left; exact h

end UndergradKB.Precalculus.Course
