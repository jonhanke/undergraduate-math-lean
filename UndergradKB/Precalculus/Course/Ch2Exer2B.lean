import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 2.2 -/

namespace UndergradKB.Precalculus.Course

/-! ## Section 2.2 -/

private lemma range_eq_of_surj (f g : ℝ → ℝ) (S : Set ℝ) (h : ∀ x, f x ∈ S)
    (hg : ∀ y ∈ S, f (g y) = y) : Set.range f = S := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact h x
  · intro hy; exact ⟨g y, hg y hy⟩

/-- Stitz-Zeager Exercise 2.2.3: `|4 - x| = 7` iff `x = -3` or `x = 11`. -/
@[kb "stitzzeager2013" "Exercise 2.2.3, p. 195"]
theorem exer_2_2_3 (x : ℝ) : |4 - x| = 7 ↔ x = -3 ∨ x = 11 := by
  constructor
  · intro h
    rcases abs_cases (4 - x) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.4: `4 - |x| = 3` iff `x = ±1`. -/
@[kb "stitzzeager2013" "Exercise 2.2.4, p. 195"]
theorem exer_2_2_4 (x : ℝ) : 4 - |x| = 3 ↔ x = -1 ∨ x = 1 := by
  constructor
  · intro h
    rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.8: `(2/3)|5 - 2x| - 1/2 = 5` iff `x = -13/8` or `x = 53/8`. -/
@[kb "stitzzeager2013" "Exercise 2.2.8, p. 195"]
theorem exer_2_2_8 (x : ℝ) :
    2 / 3 * |5 - 2 * x| - 1 / 2 = 5 ↔ x = -13 / 8 ∨ x = 53 / 8 := by
  constructor
  · intro h
    rcases abs_cases (5 - 2 * x) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.17: `|3x + 1| = |4x|` iff `x = -1/7` or `x = 1`. -/
@[kb "stitzzeager2013" "Exercise 2.2.17, p. 195"]
theorem exer_2_2_17 (x : ℝ) : |3 * x + 1| = |4 * x| ↔ x = -1 / 7 ∨ x = 1 := by
  constructor
  · intro h
    rcases abs_cases (3 * x + 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (4 * x) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    first | (left; linarith) | (right; linarith) | (exfalso; linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.18: `|1 - 2x| = |x + 1|` iff `x = 0` or `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 2.2.18, p. 195"]
theorem exer_2_2_18 (x : ℝ) : |1 - 2 * x| = |x + 1| ↔ x = 0 ∨ x = 2 := by
  constructor
  · intro h
    rcases abs_cases (1 - 2 * x) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (x + 1) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    first | (left; linarith) | (right; linarith) | (exfalso; linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.20: `|2 - 5x| = 5|x + 1|` iff `x = -3/10`. -/
@[kb "stitzzeager2013" "Exercise 2.2.20, p. 195"]
theorem exer_2_2_20 (x : ℝ) : |2 - 5 * x| = 5 * |x + 1| ↔ x = -3 / 10 := by
  constructor
  · intro h
    rcases abs_cases (2 - 5 * x) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (x + 1) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 2.2.21: `3|x - 1| = 2|x + 1|` iff `x = 1/5` or `x = 5`. -/
@[kb "stitzzeager2013" "Exercise 2.2.21, p. 195"]
theorem exer_2_2_21 (x : ℝ) : 3 * |x - 1| = 2 * |x + 1| ↔ x = 1 / 5 ∨ x = 5 := by
  constructor
  · intro h
    rcases abs_cases (x - 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (x + 1) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    first | (left; linarith) | (right; linarith) | (exfalso; linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 2.2.22: `f(x) = |x + 4|` has its only zero at `-4`, y-intercept `4`, range
`[0, ∞)`, is decreasing on `(-∞, -4]`, increasing on `[-4, ∞)`, with absolute minimum `0` at `-4`. -/
@[kb "stitzzeager2013" "Exercise 2.2.22, p. 195"]
theorem exer_2_2_22 (f : ℝ → ℝ) (hf : ∀ x, f x = |x + 4|) :
    (∀ x, f x = 0 ↔ x = -4) ∧ f 0 = 4 ∧ Set.range f = Set.Ici 0 ∧
      AntitoneOn f (Set.Iic (-4)) ∧ MonotoneOn f (Set.Ici (-4)) ∧ ∀ x, f (-4) ≤ f x := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_, fun x => ?_⟩
  · rw [hf, abs_eq_zero]; constructor <;> intro h <;> linarith
  · refine range_eq_of_surj f (fun y => y - 4) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; exact Set.mem_Ici.mpr (abs_nonneg _)
    · rw [hf]; rw [show y - 4 + 4 = y by ring]; exact abs_of_nonneg hy
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [hf, hf]; norm_num

/-- Stitz-Zeager Exercise 2.2.23: `f(x) = |x| + 4` has no zeros, y-intercept `4`, range `[4, ∞)`,
decreasing on `(-∞, 0]`, increasing on `[0, ∞)`, absolute minimum `4` at `0`. -/
@[kb "stitzzeager2013" "Exercise 2.2.23, p. 195"]
theorem exer_2_2_23 (f : ℝ → ℝ) (hf : ∀ x, f x = |x| + 4) :
    (∀ x, f x ≠ 0) ∧ f 0 = 4 ∧ Set.range f = Set.Ici 4 ∧
      AntitoneOn f (Set.Iic 0) ∧ MonotoneOn f (Set.Ici 0) ∧ ∀ x, f 0 ≤ f x := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_, fun x => ?_⟩
  · rw [hf]; have := abs_nonneg x; linarith
  · refine range_eq_of_surj f (fun y => y - 4) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; have := abs_nonneg x; exact (Set.mem_Ici.mpr (by linarith))
    · have hy' := Set.mem_Ici.mp hy
      rw [hf]; rw [abs_of_nonneg (by linarith)]; ring
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]
    rw [abs_of_nonpos ha', abs_of_nonpos hb']; linarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]
    rw [abs_of_nonneg ha', abs_of_nonneg hb']; linarith
  · rw [hf, hf]; simp

/-- Stitz-Zeager Exercise 2.2.24: `f(x) = |4x|` has its only zero at `0`, range `[0, ∞)`, is
decreasing on `(-∞, 0]`, increasing on `[0, ∞)`, absolute minimum `0` at `0`. -/
@[kb "stitzzeager2013" "Exercise 2.2.24, p. 195"]
theorem exer_2_2_24 (f : ℝ → ℝ) (hf : ∀ x, f x = |4 * x|) :
    (∀ x, f x = 0 ↔ x = 0) ∧ f 0 = 0 ∧ Set.range f = Set.Ici 0 ∧
      AntitoneOn f (Set.Iic 0) ∧ MonotoneOn f (Set.Ici 0) := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_⟩
  · rw [hf, abs_eq_zero]; constructor <;> intro h <;> linarith
  · refine range_eq_of_surj f (fun y => y / 4) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; exact Set.mem_Ici.mpr (abs_nonneg _)
    · rw [hf]; rw [show 4 * (y / 4) = y by ring]; exact abs_of_nonneg hy
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- Stitz-Zeager Exercise 2.2.25: `f(x) = -3|x|` has its only zero at `0`, range `(-∞, 0]`, is
increasing on `(-∞, 0]`, decreasing on `[0, ∞)`, absolute maximum `0` at `0`. -/
@[kb "stitzzeager2013" "Exercise 2.2.25, p. 195"]
theorem exer_2_2_25 (f : ℝ → ℝ) (hf : ∀ x, f x = -3 * |x|) :
    (∀ x, f x = 0 ↔ x = 0) ∧ f 0 = 0 ∧ Set.range f = Set.Iic 0 ∧
      MonotoneOn f (Set.Iic 0) ∧ AntitoneOn f (Set.Ici 0) ∧ ∀ x, f x ≤ f 0 := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_, fun x => ?_⟩
  · rw [hf]
    constructor
    · intro h
      have : |x| = 0 := by linarith
      exact abs_eq_zero.mp this
    · rintro rfl; norm_num
  · refine range_eq_of_surj f (fun y => y / 3) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; have := abs_nonneg x; exact Set.mem_Iic.mpr (by linarith)
    · have hy' := Set.mem_Iic.mp hy
      rw [hf, abs_of_nonpos (by linarith)]; ring
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]
    rw [abs_of_nonpos ha', abs_of_nonpos hb']; linarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]
    rw [abs_of_nonneg ha', abs_of_nonneg hb']; linarith
  · rw [hf, hf]; have := abs_nonneg x; simp only [abs_zero]; linarith

/-- Stitz-Zeager Exercise 2.2.26: `f(x) = 3|x + 4| - 4` has zeros `-16/3` and `-8/3`, y-intercept
`8`, range `[-4, ∞)`, and absolute minimum `-4` at `-4`. -/
@[kb "stitzzeager2013" "Exercise 2.2.26, p. 195"]
theorem exer_2_2_26 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * |x + 4| - 4) :
    (∀ x, f x = 0 ↔ x = -16 / 3 ∨ x = -8 / 3) ∧ f 0 = 8 ∧ Set.range f = Set.Ici (-4) ∧
      AntitoneOn f (Set.Iic (-4)) ∧ MonotoneOn f (Set.Ici (-4)) := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_⟩
  · rw [hf]
    constructor
    · intro h
      rcases abs_cases (x + 4) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; linarith
      · left; linarith
    · rintro (rfl | rfl) <;> norm_num
  · refine range_eq_of_surj f (fun y => (y + 4) / 3 - 4) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; have := abs_nonneg (x + 4); exact Set.mem_Ici.mpr (by linarith)
    · have hy' := Set.mem_Ici.mp hy
      rw [hf, show (y + 4) / 3 - 4 + 4 = (y + 4) / 3 by ring, abs_of_nonneg (by linarith)]; ring
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- Stitz-Zeager Exercise 2.2.27: `f(x) = |2x - 1|/3` has its only zero at `1/2`, y-intercept `1/3`,
range `[0, ∞)`, is decreasing on `(-∞, 1/2]` and increasing on `[1/2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.2.27, p. 195"]
theorem exer_2_2_27 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / 3 * |2 * x - 1|) :
    (∀ x, f x = 0 ↔ x = 1 / 2) ∧ f 0 = 1 / 3 ∧ Set.range f = Set.Ici 0 ∧
      AntitoneOn f (Set.Iic (1 / 2)) ∧ MonotoneOn f (Set.Ici (1 / 2)) := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_⟩
  · rw [hf]
    constructor
    · intro h
      have : |2 * x - 1| = 0 := by linarith
      have := abs_eq_zero.mp this; linarith
    · rintro rfl; norm_num
  · refine range_eq_of_surj f (fun y => (3 * y + 1) / 2) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; have := abs_nonneg (2 * x - 1); exact Set.mem_Ici.mpr (by linarith)
    · have hy' := Set.mem_Ici.mp hy
      rw [hf, show 2 * ((3 * y + 1) / 2) - 1 = 3 * y by ring, abs_of_nonneg (by linarith)]; ring
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- Stitz-Zeager Exercise 2.2.28: for `f(x) = |x + 4|/(x + 4)` (domain `x ≠ -4`), `f = -1` left of
`-4`, `f = 1` right of `-4`, `f(0) = 1`, there are no zeros, and the range is `{-1, 1}`. -/
@[kb "stitzzeager2013" "Exercise 2.2.28, p. 195"]
theorem exer_2_2_28 (f : ℝ → ℝ) (hf : ∀ x, f x = |x + 4| / (x + 4)) :
    (∀ x, x < -4 → f x = -1) ∧ (∀ x, -4 < x → f x = 1) ∧ f 0 = 1 ∧
      (∀ x, x ≠ -4 → f x ≠ 0) ∧ f '' {x | x ≠ -4} = {-1, 1} := by
  have h1 : ∀ x : ℝ, x < -4 → f x = -1 := by
    intro x hx
    rw [hf, abs_of_neg (by linarith)]
    have : x + 4 ≠ 0 := by linarith
    field_simp
  have h2 : ∀ x : ℝ, -4 < x → f x = 1 := by
    intro x hx
    rw [hf, abs_of_pos (by linarith)]
    have : x + 4 ≠ 0 := by linarith
    field_simp
  refine ⟨h1, h2, h2 0 (by norm_num), ?_, ?_⟩
  · intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [h1 x h]; norm_num
    · rw [h2 x h]; norm_num
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases lt_or_gt_of_ne hx with h | h
      · left; exact h1 x h
      · right; exact h2 x h
    · rintro (rfl | rfl)
      · exact ⟨-5, by norm_num, h1 _ (by norm_num)⟩
      · exact ⟨0, by norm_num, h2 _ (by norm_num)⟩

/-- Stitz-Zeager Exercise 2.2.29: for `f(x) = |2 - x|/(2 - x)` (domain `x ≠ 2`), `f = 1` left of `2`,
`f = -1` right of `2`, `f(0) = 1`, there are no zeros, and the range is `{-1, 1}`. -/
@[kb "stitzzeager2013" "Exercise 2.2.29, p. 195"]
theorem exer_2_2_29 (f : ℝ → ℝ) (hf : ∀ x, f x = |2 - x| / (2 - x)) :
    (∀ x, x < 2 → f x = 1) ∧ (∀ x, 2 < x → f x = -1) ∧ f 0 = 1 ∧
      (∀ x, x ≠ 2 → f x ≠ 0) ∧ f '' {x | x ≠ 2} = {-1, 1} := by
  have h1 : ∀ x : ℝ, x < 2 → f x = 1 := by
    intro x hx
    rw [hf, abs_of_pos (by linarith)]
    have : 2 - x ≠ 0 := by linarith
    field_simp
  have h2 : ∀ x : ℝ, 2 < x → f x = -1 := by
    intro x hx
    rw [hf, abs_of_neg (by linarith)]
    have : 2 - x ≠ 0 := by linarith
    field_simp
  refine ⟨h1, h2, h1 0 (by norm_num), ?_, ?_⟩
  · intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [h1 x h]; norm_num
    · rw [h2 x h]; norm_num
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases lt_or_gt_of_ne hx with h | h
      · right; exact h1 x h
      · left; exact h2 x h
    · rintro (rfl | rfl)
      · exact ⟨3, by norm_num, h2 _ (by norm_num)⟩
      · exact ⟨0, by norm_num, h1 _ (by norm_num)⟩

/-- Stitz-Zeager Exercise 2.2.31: `f(x) = |x + 2| - x` equals `-2x - 2` for `x < -2` and `2` for
`x ≥ -2`; no zeros, y-intercept `2`, range `[2, ∞)`, decreasing on `(-∞, -2]`, constant on `[-2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.2.31, p. 195"]
theorem exer_2_2_31 (f : ℝ → ℝ) (hf : ∀ x, f x = |x + 2| - x) :
    (∀ x, x < -2 → f x = -2 * x - 2) ∧ (∀ x, -2 ≤ x → f x = 2) ∧ (∀ x, f x ≠ 0) ∧ f 0 = 2 ∧
      Set.range f = Set.Ici 2 ∧ AntitoneOn f (Set.Iic (-2)) := by
  have h1 : ∀ x : ℝ, x < -2 → f x = -2 * x - 2 := by
    intro x hx; rw [hf, abs_of_neg (by linarith)]; ring
  have h2 : ∀ x : ℝ, -2 ≤ x → f x = 2 := by
    intro x hx; rw [hf, abs_of_nonneg (by linarith)]; ring
  refine ⟨h1, h2, fun x => ?_, h2 0 (by norm_num), ?_, ?_⟩
  · rcases lt_or_ge x (-2) with h | h
    · rw [h1 x h]; intro h'; linarith
    · rw [h2 x h]; norm_num
  · refine range_eq_of_surj f (fun y => -(y + 2) / 2) _ (fun x => ?_) (fun y hy => ?_)
    · rcases lt_or_ge x (-2) with h | h
      · rw [h1 x h]; exact Set.mem_Ici.mpr (by linarith)
      · rw [h2 x h]; exact Set.mem_Ici.mpr le_rfl
    · have hy' := Set.mem_Ici.mp hy
      rcases lt_or_ge (-(y + 2) / 2) (-2) with h | h
      · rw [h1 _ h]; ring
      · rw [h2 _ h]; linarith
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    rw [hf a, hf b, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- Stitz-Zeager Exercise 2.2.33: `f(x) = |x + 4| + |x - 2|` equals `-2x - 2` for `x < -4`, `6` on
`[-4, 2)`, `2x + 2` for `x ≥ 2`; it has no zeros, `f(0) = 6`, and the range is `[6, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.2.33, p. 195"]
theorem exer_2_2_33 (f : ℝ → ℝ) (hf : ∀ x, f x = |x + 4| + |x - 2|) :
    (∀ x, x < -4 → f x = -2 * x - 2) ∧ (∀ x, -4 ≤ x → x < 2 → f x = 6) ∧
      (∀ x, 2 ≤ x → f x = 2 * x + 2) ∧ (∀ x, f x ≠ 0) ∧ f 0 = 6 ∧
      Set.range f = Set.Ici 6 := by
  have h1 : ∀ x : ℝ, x < -4 → f x = -2 * x - 2 := by
    intro x hx; rw [hf, abs_of_neg (by linarith), abs_of_neg (by linarith)]; ring
  have h2 : ∀ x : ℝ, -4 ≤ x → x < 2 → f x = 6 := by
    intro x hx hx'; rw [hf, abs_of_nonneg (by linarith), abs_of_neg (by linarith)]; ring
  have h3 : ∀ x : ℝ, 2 ≤ x → f x = 2 * x + 2 := by
    intro x hx; rw [hf, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
  refine ⟨h1, h2, h3, fun x => ?_, h2 0 (by norm_num) (by norm_num), ?_⟩
  · rcases lt_or_ge x (-4) with h | h
    · rw [h1 x h]; intro h'; linarith
    · rcases lt_or_ge x 2 with h' | h'
      · rw [h2 x h h']; norm_num
      · rw [h3 x h']; intro h''; linarith
  · refine range_eq_of_surj f (fun y => (y - 2) / 2) _ (fun x => ?_) (fun y hy => ?_)
    · rcases lt_or_ge x (-4) with h | h
      · rw [h1 x h]; exact Set.mem_Ici.mpr (by linarith)
      · rcases lt_or_ge x 2 with h' | h'
        · rw [h2 x h h']; exact Set.mem_Ici.mpr le_rfl
        · rw [h3 x h']; exact Set.mem_Ici.mpr (by linarith)
    · have hy' := Set.mem_Ici.mp hy
      rw [h3 _ (by linarith)]; ring

end UndergradKB.Precalculus.Course
