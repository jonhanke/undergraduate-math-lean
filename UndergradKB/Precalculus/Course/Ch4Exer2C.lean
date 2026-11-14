import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Rational

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 4.3 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 4.3: rational inequalities -/

/-- Stitz-Zeager Exercise 4.3.7: `1/(x+2) ≥ 0` (with `x ≠ -2`) has solution set `(-2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.7, p. 365"]
theorem exer_4_3_7 : {x : ℝ | x + 2 ≠ 0 ∧ 0 ≤ 1 / (x + 2)} = Ioi (-2) := by
  ext x
  simp only [mem_setOf_eq, mem_Ioi]
  constructor
  · rintro ⟨hx, h⟩
    rcases lt_or_gt_of_ne hx with h1 | h1
    · have : 1 / (x + 2) < 0 := one_div_neg.mpr h1
      linarith
    · linarith
  · intro h
    exact ⟨by linarith, (one_div_pos.mpr (by linarith)).le⟩

/-- Stitz-Zeager Exercise 4.3.10: `4x/(x²+4) ≥ 0` has solution set `[0, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.10, p. 365"]
theorem exer_4_3_10 : {x : ℝ | 0 ≤ 4 * x / (x ^ 2 + 4)} = Ici 0 := by
  ext x
  simp only [mem_setOf_eq, mem_Ici]
  have hd : 0 < x ^ 2 + 4 := by positivity
  constructor
  · intro h
    refine le_of_not_gt fun hx => ?_
    have : 4 * x / (x ^ 2 + 4) < 0 := div_neg_of_neg_of_pos (by linarith) hd
    linarith
  · intro h
    exact div_nonneg (by linarith) hd.le

/-- Stitz-Zeager Exercise 4.3.13: `(x³+2x²+x)/(x²-x-2) ≥ 0` (where defined) has solution set `(-1, 0] ∪ (2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.13, p. 365"]
theorem exer_4_3_13 :
    {x : ℝ | x ^ 2 - x - 2 ≠ 0 ∧ 0 ≤ (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2)} =
      Ioc (-1) 0 ∪ Ioi 2 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Ioc, mem_Ioi]
  have key : ∀ x : ℝ, x + 1 ≠ 0 → x - 2 ≠ 0 →
      (x ^ 3 + 2 * x ^ 2 + x) / (x ^ 2 - x - 2) = (x ^ 2 + x) / (x - 2) := by
    intro x h1 h2
    have h3 : x ^ 2 - x - 2 ≠ 0 := by
      rw [show x ^ 2 - x - 2 = (x + 1) * (x - 2) by ring]; exact mul_ne_zero h1 h2
    rw [div_eq_div_iff h3 h2]
    ring
  constructor
  · rintro ⟨hd, h⟩
    have h1 : x + 1 ≠ 0 := fun h0 => hd (by rw [show x ^ 2 - x - 2 = (x + 1) * (x - 2) by ring, h0, zero_mul])
    have h2 : x - 2 ≠ 0 := fun h0 => hd (by rw [show x ^ 2 - x - 2 = (x + 1) * (x - 2) by ring, h0, mul_zero])
    rw [key x h1 h2, div_nonneg_iff] at h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · right
      rcases lt_or_gt_of_ne h2 with h3 | h3
      · linarith
      · linarith
    · left
      have : x < 2 := by
        rcases lt_or_gt_of_ne h2 with h3 | h3
        · linarith
        · linarith
      refine ⟨?_, by nlinarith⟩
      rcases lt_or_gt_of_ne h1 with h3 | h3
      · nlinarith
      · linarith
  · intro h
    have h1 : x + 1 ≠ 0 := by rcases h with ⟨h, _⟩ | h <;> intro h0 <;> linarith
    have h2 : x - 2 ≠ 0 := by rcases h with ⟨_, h⟩ | h <;> intro h0 <;> linarith
    refine ⟨by rw [show x ^ 2 - x - 2 = (x + 1) * (x - 2) by ring]; exact mul_ne_zero h1 h2, ?_⟩
    rw [key x h1 h2]
    rcases h with ⟨ha, hb⟩ | h
    · exact div_nonneg_of_nonpos (by nlinarith) (by linarith)
    · exact div_nonneg (by nlinarith) (by linarith)

/-- Stitz-Zeager Exercise 4.3.14: `(x²+5x+6)/(x²-1) > 0` has solution set `(-∞, -3) ∪ (-2, -1) ∪ (1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.14, p. 365"]
theorem exer_4_3_14 :
    {x : ℝ | 0 < (x ^ 2 + 5 * x + 6) / (x ^ 2 - 1)} = Iio (-3) ∪ Ioo (-2) (-1) ∪ Ioi 1 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  rw [div_pos_iff]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rcases le_or_gt x 1 with h1 | h1
      · have hx : x < -1 := by
          refine lt_of_not_ge fun hc => ?_
          nlinarith
        rcases lt_or_ge x (-3) with h2 | h2
        · left; left; exact h2
        · left; right
          refine ⟨?_, hx⟩
          refine lt_of_not_ge fun hc => ?_
          nlinarith
      · right; exact h1
    · exfalso
      nlinarith
  · rintro ((h | ⟨h1, h2⟩) | h)
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩

/-- Stitz-Zeager Exercise 4.3.17: `(-x³+4x)/(x²-9) ≥ 4x` (where defined) has solution set
`(-∞, -3) ∪ [-2√2, 0] ∪ [2√2, 3)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.17, p. 365"]
theorem exer_4_3_17 :
    {x : ℝ | x ^ 2 - 9 ≠ 0 ∧ 4 * x ≤ (-x ^ 3 + 4 * x) / (x ^ 2 - 9)} =
      Iio (-3) ∪ Icc (-(2 * Real.sqrt 2)) 0 ∪ Ico (2 * Real.sqrt 2) 3 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hl : 2 < 2 * Real.sqrt 2 := by nlinarith
  have hu : 2 * Real.sqrt 2 < 3 := by nlinarith
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Icc, mem_Ico]
  have key : ∀ x : ℝ, x ^ 2 - 9 ≠ 0 →
      (-x ^ 3 + 4 * x) / (x ^ 2 - 9) - 4 * x = (-5 * x * (x ^ 2 - 8)) / (x ^ 2 - 9) := by
    intro x h
    rw [div_sub' h, div_eq_div_iff h h]
    ring
  constructor
  · rintro ⟨hd, h⟩
    have h0 : 0 ≤ (-5 * x * (x ^ 2 - 8)) / (x ^ 2 - 9) := by rw [← key x hd]; linarith
    rw [div_nonneg_iff] at h0
    rcases h0 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hb' : 9 < x ^ 2 := by
        rcases lt_or_gt_of_ne hd with h1 | h1
        · linarith
        · linarith
      left; left
      refine lt_of_not_ge fun hc => ?_
      nlinarith
    · have hb' : x ^ 2 < 9 := by
        rcases lt_or_gt_of_ne hd with h1 | h1
        · linarith
        · linarith
      rcases lt_or_ge 0 x with hx | hx
      · right
        refine ⟨?_, by nlinarith⟩
        refine le_of_not_gt fun hc => ?_
        have : x * x < 8 := by nlinarith
        nlinarith
      · left; right
        refine ⟨?_, hx⟩
        refine le_of_not_gt fun hc => ?_
        have : x * x > 8 := by nlinarith
        nlinarith
  · intro h
    have hd : x ^ 2 - 9 ≠ 0 := by
      rcases h with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · intro h0; nlinarith
      · intro h0; nlinarith
      · intro h0; nlinarith
    refine ⟨hd, ?_⟩
    rw [← sub_nonneg, key x hd]
    rcases h with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · exact div_nonneg (by nlinarith) (by nlinarith)
    · have hx2 : x ^ 2 ≤ 8 := by nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : 0 ≤ 2 * Real.sqrt 2 - x)]
      exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
        (by nlinarith)
    · have hx2 : 8 ≤ x ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : 0 ≤ x + 2 * Real.sqrt 2)]
      exact div_nonneg_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
        (by nlinarith)

/-- Stitz-Zeager Exercise 4.3.19: `(x⁴-4x³+x²-2x-15)/(x³-4x²) ≥ x` (where defined) has solution set
`[-3, 0) ∪ (0, 4) ∪ [5, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.19, p. 365"]
theorem exer_4_3_19 :
    {x : ℝ | x ^ 3 - 4 * x ^ 2 ≠ 0 ∧ x ≤ (x ^ 4 - 4 * x ^ 3 + x ^ 2 - 2 * x - 15) / (x ^ 3 - 4 * x ^ 2)} =
      Ico (-3) 0 ∪ Ioo 0 4 ∪ Ici 5 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Ico, mem_Ioo, mem_Ici]
  have key : ∀ x : ℝ, x ^ 3 - 4 * x ^ 2 ≠ 0 →
      (x ^ 4 - 4 * x ^ 3 + x ^ 2 - 2 * x - 15) / (x ^ 3 - 4 * x ^ 2) - x =
        ((x - 5) * (x + 3)) / (x ^ 3 - 4 * x ^ 2) := by
    intro x h
    rw [div_sub' h, div_eq_div_iff h h]
    ring
  have hD : ∀ x : ℝ, x ≠ 0 → x ^ 3 - 4 * x ^ 2 = x ^ 2 * (x - 4) := fun x _ => by ring
  constructor
  · rintro ⟨hd, h⟩
    have hx0 : x ≠ 0 := by intro h0; rw [h0] at hd; norm_num at hd
    have hx2 : 0 < x ^ 2 := by positivity
    have hx4 : x - 4 ≠ 0 := by
      intro h0; apply hd; rw [hD x hx0, h0, mul_zero]
    have h0 : 0 ≤ ((x - 5) * (x + 3)) / (x ^ 3 - 4 * x ^ 2) := by rw [← key x hd]; linarith
    rw [div_nonneg_iff, hD x hx0] at h0
    rcases h0 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · right
      have : 0 < x - 4 := by
        rcases lt_or_gt_of_ne hx4 with h1 | h1
        · exfalso; nlinarith
        · exact h1
      refine le_of_not_gt fun hc => ?_
      nlinarith
    · left
      have : x - 4 < 0 := by
        rcases lt_or_gt_of_ne hx4 with h1 | h1
        · exact h1
        · exfalso; nlinarith
      have h3 : -3 ≤ x := by
        refine le_of_not_gt fun hc => ?_
        nlinarith
      rcases lt_or_gt_of_ne hx0 with h1 | h1
      · left; exact ⟨h3, h1⟩
      · right; exact ⟨h1, by linarith⟩
  · intro h
    have hx0 : x ≠ 0 := by rcases h with (⟨_, h⟩ | ⟨h, _⟩) | h <;> intro h0 <;> linarith
    have hx2 : 0 < x ^ 2 := by positivity
    have hx4 : x - 4 ≠ 0 := by rcases h with (⟨_, h⟩ | ⟨_, h⟩) | h <;> intro h0 <;> linarith
    have hd : x ^ 3 - 4 * x ^ 2 ≠ 0 := by
      rw [hD x hx0]; exact mul_ne_zero hx2.ne' hx4
    refine ⟨hd, ?_⟩
    rw [← sub_nonneg, key x hd, hD x hx0]
    rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h
    · exact div_nonneg_of_nonpos (by nlinarith) (by nlinarith)
    · exact div_nonneg_of_nonpos (by nlinarith) (by nlinarith)
    · exact div_nonneg (by nlinarith) (by nlinarith)

/-- Stitz-Zeager Exercise 4.3.20: `(5x³-12x²+9x+10)/(x²-1) ≥ 3x-1` (where defined) has solution set
`(-1, -1/2] ∪ (1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.20, p. 365"]
theorem exer_4_3_20 :
    {x : ℝ | x ^ 2 - 1 ≠ 0 ∧ 3 * x - 1 ≤ (5 * x ^ 3 - 12 * x ^ 2 + 9 * x + 10) / (x ^ 2 - 1)} =
      Ioc (-1) (-1 / 2) ∪ Ioi 1 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Ioc, mem_Ioi]
  have key : ∀ x : ℝ, x ^ 2 - 1 ≠ 0 →
      (5 * x ^ 3 - 12 * x ^ 2 + 9 * x + 10) / (x ^ 2 - 1) - (3 * x - 1) =
        ((x - 3) ^ 2 * (2 * x + 1)) / (x ^ 2 - 1) := by
    intro x h
    rw [div_sub' h, div_eq_div_iff h h]
    ring
  constructor
  · rintro ⟨hd, h⟩
    have h0 : 0 ≤ ((x - 3) ^ 2 * (2 * x + 1)) / (x ^ 2 - 1) := by rw [← key x hd]; linarith
    rw [div_nonneg_iff] at h0
    rcases h0 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · right
      have hb' : 1 < x ^ 2 := by
        rcases lt_or_gt_of_ne hd with h1 | h1
        · linarith
        · linarith
      by_cases h3 : x = 3
      · rw [h3]; norm_num
      · have h4 : 0 < (x - 3) ^ 2 := by
          have : x - 3 ≠ 0 := sub_ne_zero.mpr h3
          positivity
        have : 0 ≤ 2 * x + 1 := by
          refine le_of_not_gt fun hc => ?_
          nlinarith
        refine lt_of_not_ge fun hc => ?_
        nlinarith
    · left
      have hb' : x ^ 2 < 1 := by
        rcases lt_or_gt_of_ne hd with h1 | h1
        · linarith
        · linarith
      have h4 : 0 < (x - 3) ^ 2 := by
        have : x - 3 ≠ 0 := by intro h5; nlinarith
        positivity
      refine ⟨by nlinarith, ?_⟩
      refine le_of_not_gt fun hc => ?_
      nlinarith
  · intro h
    have hd : x ^ 2 - 1 ≠ 0 := by
      rcases h with ⟨h1, h2⟩ | h
      · intro h0; nlinarith
      · intro h0; nlinarith
    refine ⟨hd, ?_⟩
    rw [← sub_nonneg, key x hd]
    rcases h with ⟨h1, h2⟩ | h
    · exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith))
        (by nlinarith)
    · exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by nlinarith)

end UndergradKB.Precalculus.Course
