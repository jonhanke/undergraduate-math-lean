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
Section 10.7 (domains of trigonometric expressions)

Solution sets are stated as `↔` with the book's union of intervals; where Lean's `x⁻¹` or `cot` would take
the value `0` at a pole, the book's domain hypothesis (nonvanishing denominator) is part of the statement.
The private `pcR_*` lemmas are the interval toolkit of `Ch10Exer2R` (copied, so that this file stands alone). -/

namespace UndergradKB.Precalculus.Course

open Real UndergradKB.Precalculus

syntax "ao_w7v" : tactic
macro_rules
  | `(tactic| ao_w7v) => `(tactic| first | linarith | (refine ⟨?_, ?_⟩ <;> ao_w7v) | (left; ao_w7v) | (right; ao_w7v))

/-- Split every hypothesis `∨`/`∧`, then close all goals with `ao_w7v`. -/
macro "iff_w7v" : tactic =>
  `(tactic| (constructor <;> intro hh <;> (try casesm* _ ∨ _, _ ∧ _) <;> ao_w7v))

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
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

private lemma pcR_cGe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos a ≤ cos x ↔ x ≤ a ∨ 2 * π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, ← not_lt, pcR_cosLt a y ha0 ha1 hy0 hy1, not_lt]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

private lemma pcR_cL (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x < cos a ↔ a < x ∧ x < 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLt a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

private lemma pcR_cLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos x ≤ cos a ↔ a ≤ x ∧ x ≤ 2 * π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hc, hcase⟩ := pcR_cosRed x h0 h1
  rw [hc, pcR_cosLe a y ha0 ha1 hy0 hy1]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

private lemma pcR_sG (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a < sin x ↔ a < x ∧ x < π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

private lemma pcR_sGe (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin a ≤ sin x ↔ a ≤ x ∧ x ≤ π - a := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨by linarith, ha1⟩ ⟨hy0, hy1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

private lemma pcR_sL (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x < sin a ↔ x < a ∨ π - a < x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.lt_iff_lt ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

private lemma pcR_sLe (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    sin x ≤ sin a ↔ x ≤ a ∨ π - a ≤ x := by
  have hp := pi_pos
  obtain ⟨y, hy0, hy1, hs, hcase⟩ := pcR_sinRed x h0 h1
  rw [hs, strictMonoOn_sin.le_iff_le ⟨hy0, hy1⟩ ⟨by linarith, ha1⟩]
  rcases hcase with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, rfl⟩ <;> iff_w7v

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


/-- Periodic description of a set: if `P` is `p`-periodic, and on one window `[c, c+p)` it agrees with a set `T`,
then `P x` iff `x` lies in the union of the shifted copies `S k` (`x ∈ S k ↔ x - k p ∈ T`). -/
private lemma pcV_per {p c : ℝ} (hp : 0 < p) (P : ℝ → Prop) (hP : ∀ (x : ℝ) (k : ℤ), P (x - k * p) ↔ P x)
    (T : Set ℝ) (S : ℤ → Set ℝ) (hS : ∀ (k : ℤ) (x : ℝ), x ∈ S k ↔ x - k * p ∈ T)
    (hT : ∀ r ∈ T, c ≤ r ∧ r < c + p) (hbase : ∀ r, c ≤ r → r < c + p → (P r ↔ r ∈ T)) (x : ℝ) :
    P x ↔ x ∈ ⋃ k, S k := by
  rw [Set.mem_iUnion]
  constructor
  · intro hx
    have h1 : ((⌊(x - c) / p⌋ : ℤ) : ℝ) ≤ (x - c) / p := Int.floor_le _
    have h2 : (x - c) / p < ((⌊(x - c) / p⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hp] at h1
    rw [div_lt_iff₀ hp] at h2
    refine ⟨⌊(x - c) / p⌋, (hS _ x).2 ?_⟩
    exact (hbase _ (by linarith) (by linarith)).1 ((hP x _).2 hx)
  · rintro ⟨k, hk⟩
    have hk' := (hS k x).1 hk
    have hr := hT _ hk'
    exact (hP x k).1 ((hbase _ hr.1 hr.2).2 hk')

private lemma pcV_one (y : ℝ) (h0 : 0 ≤ y) (h1 : y < 2 * π) : cos y - 1 ≠ 0 ↔ 0 < y := by
  have hp := pi_pos
  have := pcR_cL 0 y le_rfl hp.le h0 h1.le
  rw [cos_zero] at this
  constructor
  · intro h
    have h' : cos y < 1 := lt_of_le_of_ne (cos_le_one y) (fun e => h (by linarith))
    exact (this.mp h').1
  · intro h e
    have := this.mpr ⟨h, by linarith⟩
    linarith

private lemma pcV_tan2 (r : ℝ) (hc : cos r ≠ 0) : 1 ≤ tan r ^ 2 ↔ cos (2 * r) ≤ 0 := by
  have hc2 : 0 < cos r ^ 2 := by positivity
  rw [tan_eq_sin_div_cos, div_pow, one_le_div hc2, cos_two_mul]
  have := sin_sq_add_cos_sq r
  constructor <;> intro h <;> nlinarith

private lemma pcV_cos2le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 2 * π) :
    cos (2 * x) ≤ 0 ↔ (π / 4 ≤ x ∧ x ≤ 3 * π / 4) ∨ (5 * π / 4 ≤ x ∧ x ≤ 7 * π / 4) := by
  have hp := pi_pos
  have key : ∀ y, 0 ≤ y → y ≤ 2 * π → (cos y ≤ 0 ↔ π / 2 ≤ y ∧ y ≤ 3 * π / 2) := fun y a b => by
    have := pcR_cLe (π / 2) y (by positivity) (by linarith) a b
    rw [cos_pi_div_two, show 2 * π - π / 2 = 3 * π / 2 by ring] at this
    exact this
  rcases le_or_gt x π with h | h
  · rw [key (2 * x) (by linarith) (by linarith)]; iff_w7v
  · rw [← cos_sub_two_pi (2 * x), key (2 * x - 2 * π) (by linarith) (by linarith)]; iff_w7v

private lemma pcV_nz_zpow (z : ℝ) (k : ℤ) : (-1 : ℝ) ^ k * z ≠ 0 ↔ z ≠ 0 := by
  have h : (-1 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  simp [h]

/-- Stitz-Zeager Exercise 10.7.99: `1 / (cos x - 1)` is defined (`cos x - 1 ≠ 0`) exactly for `x` in the union of the
open intervals `(2kπ, (2k+2)π)`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.99, p. 888"]
theorem exer_10_7_99 (x : ℝ) :
    cos x - 1 ≠ 0 ↔ x ∈ ⋃ k : ℤ, Set.Ioo (2 * (k : ℝ) * π) ((2 * (k : ℝ) + 2) * π) := by
  have hp := pi_pos
  refine pcV_per (p := 2 * π) (c := 0) (by positivity) (fun y => cos y - 1 ≠ 0) ?_ (Set.Ioo 0 (2 * π))
    (fun k : ℤ => Set.Ioo (2 * (k : ℝ) * π) ((2 * (k : ℝ) + 2) * π)) ?_ ?_ ?_ x
  · intro y k; simp only [cos_sub_int_mul_two_pi]
  · intro k y; simp only [Set.mem_Ioo]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  · rintro r ⟨a, b⟩; constructor <;> linarith
  · intro r a b
    rw [pcV_one r a (by linarith)]
    simp only [Set.mem_Ioo]
    constructor
    · intro h; exact ⟨h, by linarith⟩
    · rintro ⟨h, _⟩; exact h

/-- Stitz-Zeager Exercise 10.7.100: `cos x / (sin x + 1)` is defined (`sin x + 1 ≠ 0`) exactly for `x` in the union of
the open intervals `((4k-1)π/2, (4k+3)π/2)`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.100, p. 888"]
theorem exer_10_7_100 (x : ℝ) :
    sin x + 1 ≠ 0 ↔ x ∈ ⋃ k : ℤ, Set.Ioo ((4 * (k : ℝ) - 1) * π / 2) ((4 * (k : ℝ) + 3) * π / 2) := by
  have hp := pi_pos
  refine pcV_per (p := 2 * π) (c := -(π / 2)) (by positivity) (fun y => sin y + 1 ≠ 0) ?_
    (Set.Ioo (-(π / 2)) (3 * π / 2))
    (fun k : ℤ => Set.Ioo ((4 * (k : ℝ) - 1) * π / 2) ((4 * (k : ℝ) + 3) * π / 2)) ?_ ?_ ?_ x
  · intro y k; simp only [sin_sub_int_mul_two_pi]
  · intro k y; simp only [Set.mem_Ioo]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  · rintro r ⟨a, b⟩; constructor <;> linarith
  · intro r a b
    have e : sin r + 1 ≠ 0 ↔ cos (r + π / 2) - 1 ≠ 0 := by
      rw [cos_add_pi_div_two]
      constructor <;> intro h e <;> apply h <;> linarith
    rw [e, pcV_one (r + π / 2) (by linarith) (by linarith)]
    simp only [Set.mem_Ioo]
    constructor
    · intro h; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h, _⟩; linarith

/-- Stitz-Zeager Exercise 10.7.101: `√(tan² x - 1)` is defined (`cos x ≠ 0` and `tan² x ≥ 1`) exactly for `x` in the
union of `[(4k+1)π/4, (2k+1)π/2) ∪ ((2k+1)π/2, (4k+3)π/4]`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.101, p. 888"]
theorem exer_10_7_101 (x : ℝ) :
    (cos x ≠ 0 ∧ 1 ≤ tan x ^ 2) ↔ x ∈ ⋃ k : ℤ, (Set.Ico ((4 * (k : ℝ) + 1) * π / 4) ((2 * (k : ℝ) + 1) * π / 2) ∪
      Set.Ioc ((2 * (k : ℝ) + 1) * π / 2) ((4 * (k : ℝ) + 3) * π / 4)) := by
  have hp := pi_pos
  refine pcV_per (p := π) (c := 0) hp (fun y => cos y ≠ 0 ∧ 1 ≤ tan y ^ 2)
    ?_ (Set.Ico (π / 4) (π / 2) ∪ Set.Ioc (π / 2) (3 * π / 4))
    (fun k : ℤ => Set.Ico ((4 * (k : ℝ) + 1) * π / 4) ((2 * (k : ℝ) + 1) * π / 2) ∪
      Set.Ioc ((2 * (k : ℝ) + 1) * π / 2) ((4 * (k : ℝ) + 3) * π / 4)) ?_ ?_ ?_ x
  · intro y k
    simp only [tan_sub_int_mul_pi, cos_sub_int_mul_pi]
    rw [pcV_nz_zpow]
  · intro k y
    simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
    iff_w7v
  · intro r hr
    simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc] at hr
    rcases hr with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> linarith
  · intro r a b
    simp only [zero_add] at b
    simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
    rcases lt_trichotomy r (π / 2) with h | h | h
    · have hc : cos r ≠ 0 := ((pcR_cpos r a (by linarith)).2 (Or.inl h)).ne'
      rw [and_iff_right hc, pcV_tan2 r hc, pcV_cos2le r a (by linarith)]
      iff_w7v
    · subst h
      simp only [cos_pi_div_two, ne_eq, not_true_eq_false, false_and, false_iff]
      rintro (⟨a, b⟩ | ⟨a, b⟩) <;> linarith
    · have hc : cos r ≠ 0 := ((pcR_cneg r a (by linarith)).2 ⟨h, by linarith⟩).ne
      rw [and_iff_right hc, pcV_tan2 r hc, pcV_cos2le r a (by linarith)]
      iff_w7v

/-- Stitz-Zeager Exercise 10.7.102: `√(2 - sec x)` is defined (`cos x ≠ 0` and `2 - sec x ≥ 0`) exactly for `x` in the
union of `[(6k-1)π/3, (6k+1)π/3] ∪ ((4k+1)π/2, (4k+3)π/2)`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.102, p. 888"]
theorem exer_10_7_102 (x : ℝ) :
    (cos x ≠ 0 ∧ 0 ≤ 2 - (cos x)⁻¹) ↔ x ∈ ⋃ k : ℤ, (Set.Icc ((6 * (k : ℝ) - 1) * π / 3) ((6 * (k : ℝ) + 1) * π / 3) ∪
      Set.Ioo ((4 * (k : ℝ) + 1) * π / 2) ((4 * (k : ℝ) + 3) * π / 2)) := by
  have hp := pi_pos
  refine pcV_per (p := 2 * π) (c := -(π / 3)) (by positivity) (fun y => cos y ≠ 0 ∧ 0 ≤ 2 - (cos y)⁻¹)
    ?_ (Set.Icc (-(π / 3)) (π / 3) ∪ Set.Ioo (π / 2) (3 * π / 2))
    (fun k : ℤ => Set.Icc ((6 * (k : ℝ) - 1) * π / 3) ((6 * (k : ℝ) + 1) * π / 3) ∪
      Set.Ioo ((4 * (k : ℝ) + 1) * π / 2) ((4 * (k : ℝ) + 3) * π / 2)) ?_ ?_ ?_ x
  · intro y k; simp only [cos_sub_int_mul_two_pi]
  · intro k y
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioo]
    iff_w7v
  · intro r hr
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioo] at hr
    rcases hr with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> linarith
  · intro r a b
    have e1 : (cos r ≠ 0 ∧ 0 ≤ 2 - (cos r)⁻¹) ↔ (cos r < 0 ∨ 1 / 2 ≤ cos r) := by
      constructor
      · rintro ⟨hc, h⟩
        rcases (pcR_inv_le _ 2 hc (by norm_num)).1 (by linarith) with a | a
        · left; exact a
        · right; linarith
      · rintro (h | h)
        · exact ⟨h.ne, by linarith [inv_lt_zero.2 h]⟩
        · have hc : cos r ≠ 0 := by intro e; rw [e] at h; norm_num at h
          refine ⟨hc, ?_⟩
          have := (pcR_inv_le _ 2 hc (by norm_num)).2 (Or.inr (by linarith))
          linarith
    rw [e1]
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioo]
    have c1 : cos (π / 3) = 1 / 2 := cos_pi_div_three
    rcases le_or_gt 0 r with h | h
    · have a1 := pcR_cGe (π / 3) r (by positivity) (by linarith) h (by linarith)
      rw [c1] at a1
      rw [a1, pcR_cneg r h (by linarith)]
      iff_w7v
    · have a1 := pcR_cGe (π / 3) (r + 2 * π) (by positivity) (by linarith) (by linarith) (by linarith)
      rw [c1, cos_add_two_pi] at a1
      have a2 := pcR_cneg (r + 2 * π) (by linarith) (by linarith)
      rw [cos_add_two_pi] at a2
      rw [a1, a2]
      iff_w7v

/-- Stitz-Zeager Exercise 10.7.103: `csc (2x)` is defined (`sin 2x ≠ 0`) exactly for `x` in the union of the open
intervals `(kπ/2, (k+1)π/2)`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.103, p. 888"]
theorem exer_10_7_103 (x : ℝ) :
    sin (2 * x) ≠ 0 ↔ x ∈ ⋃ k : ℤ, Set.Ioo ((k : ℝ) * π / 2) (((k : ℝ) + 1) * π / 2) := by
  have hp := pi_pos
  refine pcV_per (p := π / 2) (c := 0) (by positivity) (fun y => sin (2 * y) ≠ 0) ?_ (Set.Ioo 0 (π / 2))
    (fun k : ℤ => Set.Ioo ((k : ℝ) * π / 2) (((k : ℝ) + 1) * π / 2)) ?_ ?_ ?_ x
  · intro y k
    have : 2 * (y - k * (π / 2)) = 2 * y - k * π := by ring
    simp only [this, sin_sub_int_mul_pi]
    rw [pcV_nz_zpow]
  · intro k y; simp only [Set.mem_Ioo]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  · rintro r ⟨a, b⟩; constructor <;> linarith
  · intro r a b
    simp only [zero_add] at b
    simp only [Set.mem_Ioo]
    constructor
    · intro h
      refine ⟨lt_of_le_of_ne a (fun e => h (by rw [← e]; simp)), b⟩
    · rintro ⟨h, _⟩
      exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'

/-- Stitz-Zeager Exercise 10.7.104: `sin x / (2 + cos x)` is defined for every real `x` (`2 + cos x ≠ 0`). -/
@[kb "stitzzeager2013" "Exercise 10.7.104, p. 888"]
theorem exer_10_7_104 (x : ℝ) : 2 + cos x ≠ 0 ↔ x ∈ (Set.univ : Set ℝ) := by
  have := neg_one_le_cos x
  simp only [Set.mem_univ, iff_true]
  intro h; linarith

/-- Stitz-Zeager Exercise 10.7.105: `3 csc x + 4 sec x` is defined (`sin x ≠ 0` and `cos x ≠ 0`) exactly for `x` in the
union of the open intervals `(kπ/2, (k+1)π/2)`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.105, p. 888"]
theorem exer_10_7_105 (x : ℝ) :
    (sin x ≠ 0 ∧ cos x ≠ 0) ↔ x ∈ ⋃ k : ℤ, Set.Ioo ((k : ℝ) * π / 2) (((k : ℝ) + 1) * π / 2) := by
  rw [← exer_10_7_103, sin_two_mul]
  simp

/-- Stitz-Zeager Exercise 10.7.106: `ln |cos x|` is defined (`cos x ≠ 0`) exactly for `x` in the union of the open
intervals `((2k-1)π/2, (2k+1)π/2)`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.106, p. 888"]
theorem exer_10_7_106 (x : ℝ) :
    cos x ≠ 0 ↔ x ∈ ⋃ k : ℤ, Set.Ioo ((2 * (k : ℝ) - 1) * π / 2) ((2 * (k : ℝ) + 1) * π / 2) := by
  have hp := pi_pos
  refine pcV_per (p := π) (c := -(π / 2)) hp (fun y => cos y ≠ 0) ?_ (Set.Ioo (-(π / 2)) (π / 2))
    (fun k : ℤ => Set.Ioo ((2 * (k : ℝ) - 1) * π / 2) ((2 * (k : ℝ) + 1) * π / 2)) ?_ ?_ ?_ x
  · intro y k
    simp only [cos_sub_int_mul_pi]
    rw [pcV_nz_zpow]
  · intro k y; simp only [Set.mem_Ioo]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  · rintro r ⟨a, b⟩; constructor <;> linarith
  · intro r a b
    simp only [Set.mem_Ioo]
    constructor
    · intro h
      refine ⟨lt_of_le_of_ne a (fun e => h (by rw [← e]; simp)), by linarith⟩
    · rintro ⟨h1, h2⟩
      exact (cos_pos_of_mem_Ioo ⟨h1, h2⟩).ne'

/-- Stitz-Zeager Exercise 10.7.107: `arcsin (tan x)` is defined (`cos x ≠ 0` and `-1 ≤ tan x ≤ 1`) exactly for `x` in the
union of the closed intervals `[(4k-1)π/4, (4k+1)π/4]`, `k ∈ ℤ`. -/
@[kb "stitzzeager2013" "Exercise 10.7.107, p. 888"]
theorem exer_10_7_107 (x : ℝ) :
    (cos x ≠ 0 ∧ -1 ≤ tan x ∧ tan x ≤ 1) ↔
      x ∈ ⋃ k : ℤ, Set.Icc ((4 * (k : ℝ) - 1) * π / 4) ((4 * (k : ℝ) + 1) * π / 4) := by
  have hp := pi_pos
  refine pcV_per (p := π) (c := -(π / 2)) hp (fun y => cos y ≠ 0 ∧ -1 ≤ tan y ∧ tan y ≤ 1) ?_
    (Set.Icc (-(π / 4)) (π / 4))
    (fun k : ℤ => Set.Icc ((4 * (k : ℝ) - 1) * π / 4) ((4 * (k : ℝ) + 1) * π / 4)) ?_ ?_ ?_ x
  · intro y k
    simp only [tan_sub_int_mul_pi, cos_sub_int_mul_pi]
    rw [pcV_nz_zpow]
  · intro k y; simp only [Set.mem_Icc]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
  · rintro r ⟨a, b⟩; constructor <;> linarith
  · intro r a b
    simp only [Set.mem_Icc]
    have m1 : tan (-(π / 4)) = -1 := by rw [tan_neg, tan_pi_div_four]
    constructor
    · rintro ⟨hc, h1, h2⟩
      have hr : -(π / 2) < r := lt_of_le_of_ne a (fun e => hc (by rw [← e]; simp))
      have mono := fun u v : ℝ => fun (hu : -(π / 2) < u) (hu' : u < π / 2) (hv : -(π / 2) < v)
        (hv' : v < π / 2) => strictMonoOn_tan.le_iff_le ⟨hu, hu'⟩ ⟨hv, hv'⟩
      have k1 := (mono (-(π / 4)) r (by linarith) (by linarith) hr (by linarith)).1 (by rw [m1]; exact h1)
      have k2 := (mono r (π / 4) hr (by linarith) (by linarith) (by linarith)).1 (by rw [tan_pi_div_four]; exact h2)
      exact ⟨k1, k2⟩
    · rintro ⟨h1, h2⟩
      have hc : cos r ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
      refine ⟨hc, ?_, ?_⟩
      · have := strictMonoOn_tan.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h1
        rw [m1] at this; exact this
      · have := strictMonoOn_tan.monotoneOn (a := r) (b := π / 4) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h2
        rw [tan_pi_div_four] at this; exact this

end UndergradKB.Precalculus.Course
