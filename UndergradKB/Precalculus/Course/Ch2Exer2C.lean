import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 2 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 2.3-2.5 -/

namespace UndergradKB.Precalculus.Course

/-! ## Section 2.3 -/

private lemma range_eq_of_surj' (f g : ℝ → ℝ) (S : Set ℝ) (h : ∀ x, f x ∈ S)
    (hg : ∀ y ∈ S, f (g y) = y) : Set.range f = S := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact h x
  · intro hy; exact ⟨g y, hg y hy⟩

/-- Stitz-Zeager Exercise 2.3.1: `f(x) = x² + 2` has no zeros, y-intercept `2`, range `[2, ∞)`,
is decreasing on `(-∞, 0]`, increasing on `[0, ∞)`, with a minimum at the vertex `(0, 2)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.1, p. 212"]
theorem exer_2_3_1 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + 2) :
    (∀ x, f x ≠ 0) ∧ f 0 = 2 ∧ Set.range f = Set.Ici 2 ∧ AntitoneOn f (Set.Iic 0) ∧
      MonotoneOn f (Set.Ici 0) ∧ ∀ x, f 0 ≤ f x := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_, fun x => ?_⟩
  · rw [hf]; nlinarith [sq_nonneg x]
  · refine range_eq_of_surj' f (fun y => Real.sqrt (y - 2)) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; exact Set.mem_Ici.mpr (by nlinarith [sq_nonneg x])
    · have hy' := Set.mem_Ici.mp hy
      rw [hf, Real.sq_sqrt (by linarith)]; ring
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]; nlinarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]; nlinarith
  · rw [hf, hf]; nlinarith [sq_nonneg x]

/-- Stitz-Zeager Exercise 2.3.2: `f(x) = -(x + 2)²` equals `-x² - 4x - 4`, has its only zero at `-2`,
y-intercept `-4`, range `(-∞, 0]`, is increasing on `(-∞, -2]`, decreasing on `[-2, ∞)`, with a
maximum at the vertex `(-2, 0)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.2, p. 212"]
theorem exer_2_3_2 (f : ℝ → ℝ) (hf : ∀ x, f x = -(x + 2) ^ 2) :
    (∀ x, f x = -x ^ 2 - 4 * x - 4) ∧ (∀ x, f x = 0 ↔ x = -2) ∧ f 0 = -4 ∧
      Set.range f = Set.Iic 0 ∧ MonotoneOn f (Set.Iic (-2)) ∧ AntitoneOn f (Set.Ici (-2)) ∧
      ∀ x, f x ≤ f (-2) := by
  refine ⟨fun x => by rw [hf]; ring, fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_, fun x => ?_⟩
  · rw [hf]
    constructor
    · intro h
      have : (x + 2) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (two_ne_zero) |>.mp this
      linarith
    · rintro rfl; norm_num
  · refine range_eq_of_surj' f (fun y => Real.sqrt (-y) - 2) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; exact Set.mem_Iic.mpr (by nlinarith [sq_nonneg (x + 2)])
    · have hy' := Set.mem_Iic.mp hy
      rw [hf, show Real.sqrt (-y) - 2 + 2 = Real.sqrt (-y) by ring, Real.sq_sqrt (by linarith)]
      ring
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hf]; nlinarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hf]; nlinarith
  · rw [hf, hf]; nlinarith [sq_nonneg (x + 2)]

/-- Stitz-Zeager Exercise 2.3.9: `f(x) = x² - x/100 - 1` has standard form `(x - 1/200)² - 40001/40000`,
zeros `(1 ± √40001)/200`, y-intercept `-1`, range `[-40001/40000, ∞)`, decreasing on `(-∞, 1/200]`,
increasing on `[1/200, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.9, p. 212"]
theorem exer_2_3_9 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - 1 / 100 * x - 1) :
    (∀ x, f x = (x - 1 / 200) ^ 2 - 40001 / 40000) ∧
      (∀ x, f x = 0 ↔ x = (1 + Real.sqrt 40001) / 200 ∨ x = (1 - Real.sqrt 40001) / 200) ∧
      f 0 = -1 ∧ Set.range f = Set.Ici (-(40001 / 40000)) ∧
      AntitoneOn f (Set.Iic (1 / 200)) ∧ MonotoneOn f (Set.Ici (1 / 200)) := by
  have hs : Real.sqrt 40001 ^ 2 = 40001 := Real.sq_sqrt (by norm_num)
  have hstd : ∀ x, f x = (x - 1 / 200) ^ 2 - 40001 / 40000 := fun x => by rw [hf]; ring
  refine ⟨hstd, fun x => ?_, by rw [hf]; norm_num, ?_, ?_, ?_⟩
  · rw [hf]
    constructor
    · intro h
      have : (x - (1 + Real.sqrt 40001) / 200) * (x - (1 - Real.sqrt 40001) / 200) = 0 := by
        linear_combination h + (-1 / 40000) * hs
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> linear_combination (1 / 40000) * hs
  · refine range_eq_of_surj' f (fun y => 1 / 200 + Real.sqrt (y + 40001 / 40000)) _
      (fun x => ?_) (fun y hy => ?_)
    · rw [hstd]; exact Set.mem_Ici.mpr (by nlinarith [sq_nonneg (x - 1 / 200)])
    · have hy' := Set.mem_Ici.mp hy
      rw [hstd, show 1 / 200 + Real.sqrt (y + 40001 / 40000) - 1 / 200 =
        Real.sqrt (y + 40001 / 40000) by ring, Real.sq_sqrt (by linarith)]
      ring
  · intro a ha b hb hab
    have ha' := Set.mem_Iic.mp ha; have hb' := Set.mem_Iic.mp hb
    simp only [hstd]; nlinarith
  · intro a ha b hb hab
    have ha' := Set.mem_Ici.mp ha; have hb' := Set.mem_Ici.mp hb
    simp only [hstd]; nlinarith

/-- Stitz-Zeager Exercise 2.3.16: the vertex of `F(t) = -0.0076t² + 0.45t + 16` is at `t = 1125/38`
(about `29.60`) with value `6889/304` (about `22.66`), and it is the maximum of `F`. -/
@[kb "stitzzeager2013" "Exercise 2.3.16, p. 213"]
theorem exer_2_3_16 (F : ℝ → ℝ) (hF : ∀ t, F t = -0.0076 * t ^ 2 + 0.45 * t + 16) :
    F (1125 / 38) = 6889 / 304 ∧ 29.60 < (1125 / 38 : ℝ) ∧ (1125 / 38 : ℝ) < 29.61 ∧
      22.66 < (6889 / 304 : ℝ) ∧ (6889 / 304 : ℝ) < 22.67 ∧ ∀ t, F t ≤ F (1125 / 38) := by
  refine ⟨by rw [hF]; norm_num, by norm_num, by norm_num, by norm_num, by norm_num, fun t => ?_⟩
  rw [hF, hF]; nlinarith [sq_nonneg (t - 1125 / 38)]

/-- Stitz-Zeager Exercise 2.3.25: a marble shot up at `15` m/s from the ground, `s(t) = -4.9t² + 15t`,
peaks at height `1125/98` (about `11.48`) and returns to the ground at `t = 150/49` (about `3.06`);
shot from a `25` m tower, `s(t) = -4.9t² + 15t + 25` is zero for `t > 0` exactly at
`t = (15 + √715)/9.8`, about `4.26`. -/
@[kb "stitzzeager2013" "Exercise 2.3.25, p. 214"]
theorem exer_2_3_25 (s s' : ℝ → ℝ) (hs : ∀ t, s t = -4.9 * t ^ 2 + 15 * t)
    (hs' : ∀ t, s' t = -4.9 * t ^ 2 + 15 * t + 25) :
    (s (75 / 49) = 1125 / 98 ∧ (∀ t, s t ≤ 1125 / 98) ∧ 11.475 < (1125 / 98 : ℝ) ∧
      (1125 / 98 : ℝ) < 11.485) ∧
    (∀ t, 0 < t → (s t = 0 ↔ t = 150 / 49)) ∧
    (∀ t, 0 < t → (s' t = 0 ↔ t = (15 + Real.sqrt 715) / (49 / 5))) ∧
    (4.258 < (15 + Real.sqrt 715) / (49 / 5) ∧ (15 + Real.sqrt 715) / (49 / 5) < 4.2592) := by
  have h715 : Real.sqrt 715 ^ 2 = 715 := Real.sq_sqrt (by norm_num)
  have hlo : 26.73 < Real.sqrt 715 := by
    rw [show (26.73 : ℝ) = Real.sqrt (26.73 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hhi : Real.sqrt 715 < 26.74 := by
    rw [show (26.74 : ℝ) = Real.sqrt (26.74 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨⟨by rw [hs]; norm_num, fun t => ?_, by norm_num, by norm_num⟩, fun t ht => ?_,
    fun t ht => ?_, by constructor <;> linarith⟩
  · rw [hs]; nlinarith [sq_nonneg (t - 75 / 49)]
  · rw [hs]
    constructor
    · intro h
      have : t * (-4.9 * t + 15) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · rintro rfl; norm_num
  · rw [hs']
    constructor
    · intro h
      have : (t - (15 + Real.sqrt 715) / (49 / 5)) * (t - (15 - Real.sqrt 715) / (49 / 5)) = 0 := by
        linear_combination (-1 / 4.9) * h + (-1 / 96.04) * h715
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exfalso; linarith
    · rintro rfl
      linear_combination (-1 / 19.6) * h715

/-- Stitz-Zeager Exercise 2.3.27: `f(x) = |1 - x²|` has zeros `±1`, y-intercept `1`, is nonnegative,
and has range `[0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.27, p. 214"]
theorem exer_2_3_27 (f : ℝ → ℝ) (hf : ∀ x, f x = |1 - x ^ 2|) :
    (∀ x, f x = 0 ↔ x = -1 ∨ x = 1) ∧ f 0 = 1 ∧ Set.range f = Set.Ici 0 := by
  refine ⟨fun x => ?_, by rw [hf]; norm_num, ?_⟩
  · rw [hf, abs_eq_zero]
    constructor
    · intro h
      have : (x - 1) * (x + 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · right; linarith
      · left; linarith
    · rintro (rfl | rfl) <;> norm_num
  · refine range_eq_of_surj' f (fun y => Real.sqrt (1 + y)) _ (fun x => ?_) (fun y hy => ?_)
    · rw [hf]; exact Set.mem_Ici.mpr (abs_nonneg _)
    · have hy' := Set.mem_Ici.mp hy
      rw [hf, Real.sq_sqrt (by linarith), show 1 - (1 + y) = -y by ring, abs_neg]
      exact abs_of_nonneg hy'

/-- Stitz-Zeager Exercise 2.3.32: `y² - 4y = x² - 4` holds iff `x = ±(y - 2)`. -/
@[kb "stitzzeager2013" "Exercise 2.3.32, p. 214"]
theorem exer_2_3_32 (x y : ℝ) : y ^ 2 - 4 * y = x ^ 2 - 4 ↔ x = y - 2 ∨ x = -(y - 2) := by
  constructor
  · intro h
    have : (x - (y - 2)) * (x + (y - 2)) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (h | h) <;> subst h <;> ring

end UndergradKB.Precalculus.Course
