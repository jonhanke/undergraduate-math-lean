import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import UndergradKB.Precalculus.RationalExponents

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7, lead), Section 5.3 -/

namespace UndergradKB.Precalculus.Course

open UndergradKB.Precalculus

/-- Stitz-Zeager Exercise 5.3.30: on its domain `x ≠ 2`, the inequality
`-(4/3)(x-2)^(-4/3) + (8/9) x (x-2)^(-7/3) ≥ 0` (the book's rational powers, real cube roots) has solution set
`(2, 6]`. -/
@[kb "stitzzeager2013" "Exercise 5.3.30, p. 420"]
theorem exer_5_3_30 (x : ℝ) (hx : x ≠ 2) :
    0 ≤ -(4 / 3) * bookRatPow (x - 2) (-4) 3 + 8 / 9 * x * bookRatPow (x - 2) (-7) 3 ↔ 2 < x ∧ x ≤ 6 := by
  set r := principalRoot 3 (x - 2) with hr
  have hodd : Odd 3 := by decide
  have hr3 : r ^ 3 = x - 2 := principalRoot_pow (by norm_num) (Or.inl hodd)
  have hr0 : r ≠ 0 := by
    intro h; rw [h] at hr3; apply hx; linarith [show (0 : ℝ) ^ 3 = 0 by norm_num]
  have hE : -(4 / 3) * bookRatPow (x - 2) (-4) 3 + 8 / 9 * x * bookRatPow (x - 2) (-7) 3 =
      (24 - 4 * x) / (9 * r ^ 7) := by
    simp only [bookRatPow, ← hr, zpow_neg, zpow_ofNat]
    field_simp
    rw [hr3]; ring
  rw [hE]
  have h7 : r ^ 7 = (x - 2) ^ 2 * r := by
    rw [← hr3]; ring
  have hsq : 0 < (x - 2) ^ 2 := by
    have : x - 2 ≠ 0 := sub_ne_zero.2 hx
    positivity
  constructor
  · intro h
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exfalso
      have hrneg : r < 0 := by
        by_contra hc
        push Not at hc
        have : 0 ≤ r ^ 3 := pow_nonneg hc 3
        linarith
      have hden : 9 * r ^ 7 < 0 := by
        rw [h7]; nlinarith
      have hnum : 0 < 24 - 4 * x := by linarith
      have : (24 - 4 * x) / (9 * r ^ 7) < 0 := div_neg_of_pos_of_neg hnum hden
      linarith
    · refine ⟨hgt, ?_⟩
      have hrpos : 0 < r := by
        by_contra hc
        push Not at hc
        have : r ^ 3 ≤ 0 := by
          have := pow_nonneg (neg_nonneg.2 hc) 3
          nlinarith
        linarith
      have hden : 0 < 9 * r ^ 7 := by positivity
      have := (div_nonneg_iff.1 h)
      rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
      · linarith
      · linarith
  · rintro ⟨h1, h2⟩
    have hrpos : 0 < r := by
      by_contra hc
      push Not at hc
      have : r ^ 3 ≤ 0 := by
        have := pow_nonneg (neg_nonneg.2 hc) 3
        nlinarith
      linarith
    apply div_nonneg (by linarith)
    positivity

end UndergradKB.Precalculus.Course
