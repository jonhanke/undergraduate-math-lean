import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Precalculus.RationalExponents
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.3 (equations) -/

namespace UndergradKB.Precalculus.Course

open Set UndergradKB.Precalculus

private theorem x5w7f_aux {a b : ℝ} (h : a = Real.sqrt b) :
    0 ≤ a ∧ ((a = 0 ∧ b < 0) ∨ a ^ 2 = b) := by
  refine ⟨h ▸ Real.sqrt_nonneg _, ?_⟩
  by_cases hb : 0 ≤ b
  · right; rw [h]; exact Real.sq_sqrt hb
  · left; push Not at hb; exact ⟨by rw [h]; exact Real.sqrt_eq_zero_of_nonpos hb.le, hb⟩

private theorem x5w7f_rs {a b : ℝ} (ha : 0 ≤ a) (h : a ^ 2 = b) : Real.sqrt b = a := by
  rw [← h]; exact Real.sqrt_sq ha

/-- Stitz-Zeager Exercise 5.3.22: `x^(3/2) = 8` (book's power, defined for `x ≥ 0`) holds exactly for `x = 4`. -/
@[kb "stitzzeager2013" "Exercise 5.3.22, p. 419"]
theorem exer_5_3_22 : ∀ x : ℝ, (BookRatPowDefined x 3 2 ∧ bookRatPow x 3 2 = 8) ↔ x = 4 := by
  intro x; constructor
  · rintro ⟨⟨_, h, _⟩, h8⟩
    have hx : 0 ≤ x := h.resolve_left (by decide)
    have hr := principalRoot_pow (n := 2) (x := x) (by norm_num) (Or.inr hx)
    have h0 := principalRoot_nonneg (n := 2) hx
    simp only [bookRatPow, zpow_ofNat] at h8
    have : principalRoot 2 x = 2 := by nlinarith [sq_nonneg (principalRoot 2 x - 2)]
    rw [this] at hr; linarith
  · rintro rfl
    have h2 : principalRoot 2 4 = 2 :=
      ((principalRoot_eq_iff_nonneg (n := 2) (by norm_num) (x := 4) (by norm_num) 2).2
        ⟨by norm_num, by norm_num⟩).symm
    refine ⟨⟨by norm_num, Or.inr (by norm_num), Or.inl (by norm_num)⟩, ?_⟩
    simp only [bookRatPow, h2]; norm_num

/-- Stitz-Zeager Exercise 5.3.23: `x^(2/3) = 4` (book's power) holds exactly for `x = 8` or `x = -8`. -/
@[kb "stitzzeager2013" "Exercise 5.3.23, p. 419"]
theorem exer_5_3_23 : ∀ x : ℝ, bookRatPow x 2 3 = 4 ↔ x = 8 ∨ x = -8 := by
  have h3 : Odd 3 := by decide
  intro x; constructor
  · intro h
    have hr := principalRoot_pow (n := 3) (x := x) (by norm_num) (Or.inl h3)
    simp only [bookRatPow, zpow_ofNat] at h
    have : (principalRoot 3 x - 2) * (principalRoot 3 x + 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h' | h'
    · left; have : principalRoot 3 x = 2 := by linarith
      rw [this] at hr; linarith
    · right; have : principalRoot 3 x = -2 := by linarith
      rw [this] at hr; linarith
  · have e8 : principalRoot 3 8 = 2 :=
      ((principalRoot_eq_iff_odd h3 8 2).2 (by norm_num)).symm
    have em8 : principalRoot 3 (-8) = -2 :=
      ((principalRoot_eq_iff_odd h3 (-8) (-2)).2 (by norm_num)).symm
    rintro (rfl | rfl)
    · simp only [bookRatPow, e8]; norm_num
    · simp only [bookRatPow, em8]; norm_num

/-- Stitz-Zeager Exercise 5.3.26: `5 - (4-2x)^(2/3) = 1` (book's power) holds exactly for `x = -2` or `x = 6`. -/
@[kb "stitzzeager2013" "Exercise 5.3.26, p. 419"]
theorem exer_5_3_26 : ∀ x : ℝ, 5 - bookRatPow (4 - 2 * x) 2 3 = 1 ↔ x = -2 ∨ x = 6 := by
  have h3 : Odd 3 := by decide
  intro x; constructor
  · intro h
    have hr := principalRoot_pow (n := 3) (x := 4 - 2 * x) (by norm_num) (Or.inl h3)
    simp only [bookRatPow, zpow_ofNat] at h
    have : (principalRoot 3 (4 - 2 * x) - 2) * (principalRoot 3 (4 - 2 * x) + 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h' | h'
    · left; have : principalRoot 3 (4 - 2 * x) = 2 := by linarith
      rw [this] at hr; linarith
    · right; have : principalRoot 3 (4 - 2 * x) = -2 := by linarith
      rw [this] at hr; linarith
  · have e8 : principalRoot 3 8 = 2 :=
      ((principalRoot_eq_iff_odd h3 8 2).2 (by norm_num)).symm
    have em8 : principalRoot 3 (-8) = -2 :=
      ((principalRoot_eq_iff_odd h3 (-8) (-2)).2 (by norm_num)).symm
    rintro (rfl | rfl)
    · simp only [bookRatPow]; rw [show (4 - 2 * (-2 : ℝ)) = 8 by norm_num, e8]; norm_num
    · simp only [bookRatPow]; rw [show (4 - 2 * (6 : ℝ)) = -8 by norm_num, em8]; norm_num

/-- Stitz-Zeager Exercise 5.3.28: `∛x ≤ x` has solution set `[-1, 0] ∪ [1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.28, p. 419"]
theorem exer_5_3_28 : {x : ℝ | principalRoot 3 x ≤ x} = Icc (-1) 0 ∪ Ici 1 := by
  have h3 : Odd 3 := by decide
  have mono : ∀ a b : ℝ, a ≤ b ↔ a ^ 3 ≤ b ^ 3 := fun a b => (h3.strictMono_pow.le_iff_le).symm
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Icc, mem_Ici]
  set r := principalRoot 3 x with hr
  have hx : r ^ 3 = x := principalRoot_pow (by norm_num) (Or.inl h3)
  have c1 : -1 ≤ x ↔ -1 ≤ r := by rw [mono (-1) r, ← hx]; norm_num
  have c2 : x ≤ 0 ↔ r ≤ 0 := by rw [mono r 0, ← hx]; norm_num
  have c3 : 1 ≤ x ↔ 1 ≤ r := by rw [mono 1 r, ← hx]; norm_num
  rw [c1, c2, c3]
  constructor
  · intro h
    rw [← hx] at h
    by_cases h1 : r < -1
    · exfalso
      nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < -r) (by linarith : (0 : ℝ) < 1 - r))
        (by linarith : (0 : ℝ) < -1 - r)]
    · by_cases h0 : r ≤ 0
      · left; exact ⟨not_lt.1 h1, h0⟩
      · push Not at h0
        by_cases h2 : r < 1
        · exfalso
          nlinarith [mul_pos (mul_pos h0 (by linarith : (0 : ℝ) < 1 - r)) (by linarith : (0 : ℝ) < 1 + r)]
        · right; exact not_lt.1 h2
  · rintro (⟨h1, h2⟩ | h)
    · rw [← hx]; nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 1 + r)) (by linarith : (0 : ℝ) ≤ 1 - r)]
    · rw [← hx]; nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) (by linarith : (0 : ℝ) ≤ r - 1)) (by linarith : (0 : ℝ) ≤ r + 1)]

end UndergradKB.Precalculus.Course
