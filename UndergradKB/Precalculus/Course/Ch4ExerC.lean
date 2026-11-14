import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Rational

/-! # Course layer, Chapter 4 (Stitz-Zeager): exercises with the book's answers, Section 4.3 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 4.3: rational equations -/

/-- Stitz-Zeager Exercise 4.3.1: `x/(5x+4) = 3` holds (for `5x+4 ≠ 0`) exactly when `x = -6/7`. -/
@[kb "stitzzeager2013" "Exercise 4.3.1, p. 365"]
theorem exer_4_3_1 (x : ℝ) (h : 5 * x + 4 ≠ 0) : x / (5 * x + 4) = 3 ↔ x = -6 / 7 := by
  rw [div_eq_iff h]
  constructor
  · intro h'; linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.3.2: `(3x-1)/(x²+1) = 1` holds exactly when `x = 1` or `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 4.3.2, p. 365"]
theorem exer_4_3_2 (x : ℝ) : (3 * x - 1) / (x ^ 2 + 1) = 1 ↔ x = 1 ∨ x = 2 := by
  rw [div_eq_iff (by positivity)]
  constructor
  · intro h
    have h' : (x - 1) * (x - 2) = 0 := by linear_combination (-1 : ℝ) * h
    rcases mul_eq_zero.mp h' with h'' | h''
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 4.3.3: for `x ≠ ±3`, `1/(x+3) + 1/(x-3) = (x²-3)/(x²-9)` holds exactly when `x = -1`
(the other root `x = 3` of the cleared equation is extraneous). -/
@[kb "stitzzeager2013" "Exercise 4.3.3, p. 365"]
theorem exer_4_3_3 (x : ℝ) (h1 : x + 3 ≠ 0) (h2 : x - 3 ≠ 0) :
    1 / (x + 3) + 1 / (x - 3) = (x ^ 2 - 3) / (x ^ 2 - 9) ↔ x = -1 := by
  have h9 : x ^ 2 - 9 ≠ 0 := by
    rw [show x ^ 2 - 9 = (x + 3) * (x - 3) by ring]; exact mul_ne_zero h1 h2
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h9]
  constructor
  · intro h
    have h' : (x ^ 2 - 9) * ((x - 3) * (x + 1)) = 0 := by linear_combination (-1 : ℝ) * h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' h9
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact absurd h3 h2
      · linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.3.4: for `x ≠ -1`, `(2x+17)/(x+1) = x+5` holds exactly when `x = -6` or `x = 2`. -/
@[kb "stitzzeager2013" "Exercise 4.3.4, p. 365"]
theorem exer_4_3_4 (x : ℝ) (h : x + 1 ≠ 0) : (2 * x + 17) / (x + 1) = x + 5 ↔ x = -6 ∨ x = 2 := by
  rw [div_eq_iff h]
  constructor
  · intro h'
    have h'' : (x + 6) * (x - 2) = 0 := by linear_combination (-1 : ℝ) * h'
    rcases mul_eq_zero.mp h'' with h3 | h3
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 4.3.5: `(x²-2x+1)/(x³+x²-2x) = 1` has no solution (the only root `x = 1` of the cleared
equation makes the denominator zero). -/
@[kb "stitzzeager2013" "Exercise 4.3.5, p. 365"]
theorem exer_4_3_5 (x : ℝ) (hx : x ^ 3 + x ^ 2 - 2 * x ≠ 0) :
    (x ^ 2 - 2 * x + 1) / (x ^ 3 + x ^ 2 - 2 * x) ≠ 1 := by
  intro h
  rw [div_eq_iff hx] at h
  have h' : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination (-1 : ℝ) * h
  rcases mul_eq_zero.mp h' with h3 | h3
  · apply hx
    have : x = 1 := by linarith
    rw [this]; norm_num
  · nlinarith [sq_nonneg (x + 1 / 2)]

/-- Stitz-Zeager Exercise 4.3.6: for `x² ≠ 9`, `(-x³+4x)/(x²-9) = 4x` holds exactly when `x = 0` or `x = ±2√2`. -/
@[kb "stitzzeager2013" "Exercise 4.3.6, p. 365"]
theorem exer_4_3_6 (x : ℝ) (hx : x ^ 2 - 9 ≠ 0) :
    (-x ^ 3 + 4 * x) / (x ^ 2 - 9) = 4 * x ↔ x = 0 ∨ x = 2 * Real.sqrt 2 ∨ x = -(2 * Real.sqrt 2) := by
  have hs : (2 * Real.sqrt 2) ^ 2 = 8 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [div_eq_iff hx]
  constructor
  · intro h
    have h' : x * (x ^ 2 - 8) = 0 := by linear_combination (-1 / 5 : ℝ) * h
    rcases mul_eq_zero.mp h' with h3 | h3
    · left; exact h3
    · right
      have h4 : (x - 2 * Real.sqrt 2) * (x + 2 * Real.sqrt 2) = 0 := by linear_combination h3 - hs
      rcases mul_eq_zero.mp h4 with h5 | h5
      · left; linarith
      · right; linarith
  · rintro (h | h | h)
    · rw [h]; norm_num
    · have h2 : x ^ 2 = 8 := by rw [h]; exact hs
      linear_combination (-5 * x) * h2
    · have h2 : x ^ 2 = 8 := by rw [h]; rw [neg_sq]; exact hs
      linear_combination (-5 * x) * h2

/-! ## Section 4.3: rational inequalities -/

/-- Stitz-Zeager Exercise 4.3.8: `(x-3)/(x+2) ≤ 0` (with `x ≠ -2`) has solution set `(-2, 3]`. -/
@[kb "stitzzeager2013" "Exercise 4.3.8, p. 365"]
theorem exer_4_3_8 : {x : ℝ | x + 2 ≠ 0 ∧ (x - 3) / (x + 2) ≤ 0} = Ioc (-2) 3 := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioc]
  constructor
  · rintro ⟨hx, h⟩
    rw [div_nonpos_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact ⟨lt_of_le_of_ne (by linarith) (fun h => hx (by linarith)), by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ne_of_gt (by linarith), div_nonpos_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)⟩

/-- Stitz-Zeager Exercise 4.3.9: `x/(x²-1) > 0` has solution set `(-1, 0) ∪ (1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.9, p. 365"]
theorem exer_4_3_9 : {x : ℝ | 0 < x / (x ^ 2 - 1)} = Ioo (-1) 0 ∪ Ioi 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      by_contra hc
      push Not at hc
      nlinarith
    · left
      refine ⟨?_, h1⟩
      by_contra hc
      push Not at hc
      nlinarith
  · rintro (⟨h1, h2⟩ | h)
    · exact Or.inr ⟨h2, by nlinarith⟩
    · exact Or.inl ⟨by linarith, by nlinarith⟩

/-- Stitz-Zeager Exercise 4.3.11: `(x²-x-12)/(x²+x-6) > 0` has solution set `(-∞,-3) ∪ (-3,2) ∪ (4,∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.11, p. 365"]
theorem exer_4_3_11 :
    {x : ℝ | 0 < (x ^ 2 - x - 12) / (x ^ 2 + x - 6)} = Iio (-3) ∪ Ioo (-3) 2 ∪ Ioi 4 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo, mem_Ioi]
  by_cases h3 : x = -3
  · subst h3; norm_num
  by_cases h2 : x = 2
  · subst h2; norm_num
  have h1' : x + 3 ≠ 0 := fun h => h3 (by linarith)
  have h2' : x - 2 ≠ 0 := sub_ne_zero.mpr h2
  have hq : x ^ 2 + x - 6 ≠ 0 := by
    rw [show x ^ 2 + x - 6 = (x + 3) * (x - 2) by ring]; exact mul_ne_zero h1' h2'
  have key : (x ^ 2 - x - 12) / (x ^ 2 + x - 6) = (x - 4) / (x - 2) := by
    rw [div_eq_div_iff hq h2']; ring
  rw [key, div_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; linarith
    · have : x ≠ -3 := h3
      rcases lt_or_gt_of_ne this with h | h
      · left; left; exact h
      · left; right; exact ⟨h, by linarith⟩
  · rintro ((h | ⟨h1, h2⟩) | h)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

/-- Stitz-Zeager Exercise 4.3.12: `(3x²-5x-2)/(x²-9) < 0` has solution set `(-3, -1/3) ∪ (2, 3)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.12, p. 365"]
theorem exer_4_3_12 :
    {x : ℝ | (3 * x ^ 2 - 5 * x - 2) / (x ^ 2 - 9) < 0} = Ioo (-3) (-1 / 3) ∪ Ioo 2 3 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ioo]
  rw [div_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h3 : -3 < x := by
        by_contra hc; push Not at hc; nlinarith
      have h4 : x < 3 := by
        by_contra hc; push Not at hc; nlinarith
      rcases lt_or_ge x (-1 / 3) with h | h
      · left; exact ⟨h3, h⟩
      · right
        refine ⟨?_, h4⟩
        by_contra hc; push Not at hc; nlinarith
    · exfalso
      have h3 : -1 / 3 < x := by
        by_contra hc; push Not at hc; nlinarith
      have h4 : x < 2 := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩
    · exact Or.inl ⟨by nlinarith, by nlinarith⟩

/-- Stitz-Zeager Exercise 4.3.15: `(3x-1)/(x²+1) ≤ 1` has solution set `(-∞, 1] ∪ [2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.15, p. 365"]
theorem exer_4_3_15 : {x : ℝ | (3 * x - 1) / (x ^ 2 + 1) ≤ 1} = Iic 1 ∪ Ici 2 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici]
  rw [div_le_one (by positivity)]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [hc.1, hc.2]
  · rintro (h | h) <;> nlinarith

/-- Stitz-Zeager Exercise 4.3.16: `(2x+17)/(x+1) > x+5` (with `x ≠ -1`) has solution set `(-∞,-6) ∪ (-1,2)`. -/
@[kb "stitzzeager2013" "Exercise 4.3.16, p. 365"]
theorem exer_4_3_16 :
    {x : ℝ | x + 1 ≠ 0 ∧ x + 5 < (2 * x + 17) / (x + 1)} = Iio (-6) ∪ Ioo (-1) 2 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo]
  constructor
  · rintro ⟨hx, h⟩
    rcases lt_or_gt_of_ne hx with h1 | h1
    · rw [lt_div_iff_of_neg h1] at h
      left
      by_contra hc; push Not at hc
      nlinarith
    · rw [lt_div_iff₀ h1] at h
      right
      refine ⟨by linarith, ?_⟩
      by_contra hc; push Not at hc
      nlinarith
  · rintro ((h | ⟨h1, h2⟩))
    · have h1 : x + 1 < 0 := by linarith
      refine ⟨ne_of_lt h1, ?_⟩
      rw [lt_div_iff_of_neg h1]
      nlinarith
    · have h3 : 0 < x + 1 := by linarith
      refine ⟨ne_of_gt h3, ?_⟩
      rw [lt_div_iff₀ h3]
      nlinarith

/-- Stitz-Zeager Exercise 4.3.18: `1/(x²+1) < 0` has no solution. -/
@[kb "stitzzeager2013" "Exercise 4.3.18, p. 365"]
theorem exer_4_3_18 : {x : ℝ | 1 / (x ^ 2 + 1) < 0} = ∅ := by
  ext x
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
  positivity

/-! ## Section 4.3: applications -/

/-- Stitz-Zeager Exercise 4.3.21: Mike runs `3` miles at `6` mph and finishes `10` minutes (`1/6` hour) before Carl;
Carl's speed `v` satisfies `3/v = 3/6 + 1/6` exactly when `v = 4.5` mph. -/
@[kb "stitzzeager2013" "Exercise 4.3.21, p. 365"]
theorem exer_4_3_21 (v : ℝ) (hv : 0 < v) : 3 / v = 3 / 6 + 1 / 6 ↔ v = 9 / 2 := by
  rw [div_eq_iff hv.ne']
  constructor
  · intro h; linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.3.22: a swallow flies `3/4` mile with a `6` mph tailwind and back against it in
`4` minutes (`1/15` hour); its airspeed `v > 6` satisfies the equation exactly when `v = 24` mph. -/
@[kb "stitzzeager2013" "Exercise 4.3.22, p. 365"]
theorem exer_4_3_22 (v : ℝ) (hv : 6 < v) :
    3 / 4 / (v + 6) + 3 / 4 / (v - 6) = 4 / 60 ↔ v = 24 := by
  have h1 : v + 6 ≠ 0 := by intro h; linarith
  have h2 : v - 6 ≠ 0 := by intro h; linarith
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (by norm_num)]
  constructor
  · intro h
    have h' : (v - 24) * (4 * v + 6) = 0 := by linear_combination (-1 : ℝ) * h
    rcases mul_eq_zero.mp h' with h3 | h3
    · linarith
    · linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.3.23: two `40` gal/min pumps run for half an hour, then one of them for another half hour,
removing `3600` gallons. -/
@[kb "stitzzeager2013" "Exercise 4.3.23, p. 365"]
theorem exer_4_3_23 : 2 * (40 : ℝ) * 30 + 40 * 30 = 3600 := by norm_num

/-- Stitz-Zeager Exercise 4.3.24: a faucet filling a sink in `5` minutes with a drain emptying it in `8` minutes
fills it in `t` minutes exactly when `t (1/5 - 1/8) = 1`, i.e. `t = 40/3` minutes. -/
@[kb "stitzzeager2013" "Exercise 4.3.24, p. 365"]
theorem exer_4_3_24 (t : ℝ) : t * (1 / 5 - 1 / 8) = 1 ↔ t = 40 / 3 := by
  constructor
  · intro h; linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.3.25: Daniel and Donnie together clean the pen in `45` minutes and Daniel alone in `60`;
Donnie alone needs `d` minutes with `45 (1/60 + 1/d) = 1` exactly when `d = 180` minutes (3 hours). -/
@[kb "stitzzeager2013" "Exercise 4.3.25, p. 365"]
theorem exer_4_3_25 (d : ℝ) (hd : 0 < d) : 45 * (1 / 60 + 1 / d) = 1 ↔ d = 180 := by
  constructor
  · intro h
    have h' : 1 / d = 1 / 180 := by linarith
    rw [one_div, one_div] at h'
    exact inv_inj.mp h'
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 4.3.32: the population model `P(t) = 150t/(t+15)` is below `100` exactly on `(-15, 30)`
(for `t ≠ -15`); on the applied domain `t ≥ 0` this is `0 ≤ t < 30`. -/
@[kb "stitzzeager2013" "Exercise 4.3.32, p. 366"]
theorem exer_4_3_32 :
    (∀ t : ℝ, t + 15 ≠ 0 → (150 * t / (t + 15) < 100 ↔ -15 < t ∧ t < 30)) ∧
    (∀ t : ℝ, 0 ≤ t → (150 * t / (t + 15) < 100 ↔ t < 30)) := by
  refine ⟨fun t hx => ?_, fun t ht => ?_⟩
  · rcases lt_or_gt_of_ne hx with h | h
    · rw [div_lt_iff_of_neg h]
      constructor
      · intro h'; linarith
      · rintro ⟨h1, _⟩; linarith
    · rw [div_lt_iff₀ h]
      constructor
      · intro h'; exact ⟨by linarith, by linarith⟩
      · rintro ⟨_, h2⟩; linarith
  · have h : 0 < t + 15 := by linarith
    rw [div_lt_iff₀ h]
    constructor <;> intro h' <;> linarith

/-- Stitz-Zeager Exercise 4.3.37: the drag `D` varies jointly with the density `ρ` and the square of the velocity `ν`
when `D = k ρ ν²` for a constant `k`. -/
@[kb "stitzzeager2013" "Exercise 4.3.37, p. 367"]
theorem exer_4_3_37 (D ρ ν : ℝ → ℝ) :
    UndergradKB.Precalculus.VariesJointly D ρ (fun t => ν t ^ 2) ↔ ∃ k : ℝ, ∀ t, D t = k * ρ t * ν t ^ 2 :=
  Iff.rfl

/-- Stitz-Zeager Exercise 4.3.39: the frequency `f = (1/(2L)) √(T/μ)` equals `(1/2) √T · L⁻¹ · (√μ)⁻¹`, so it varies
directly with the square root of the tension and inversely with the length and the square root of the linear mass. -/
@[kb "stitzzeager2013" "Exercise 4.3.39, p. 367"]
theorem exer_4_3_39 (T μ L : ℝ) (hT : 0 ≤ T) :
    1 / (2 * L) * Real.sqrt (T / μ) = (1 / 2) * Real.sqrt T * L⁻¹ * (Real.sqrt μ)⁻¹ := by
  rw [Real.sqrt_div hT]
  ring

/-- Stitz-Zeager Exercise 4.3.40(b): a person `5` ft `10` in (70 inches) tall weighing `235` pounds with Body Mass
Index `33.7` has constant of proportionality `k = 33.7 · 70²/235`, which lies strictly between `702.68` and `702.69`. -/
@[kb "stitzzeager2013" "Exercise 4.3.40, p. 367"]
theorem exer_4_3_40_b (k : ℝ) (h : (33.7 : ℝ) = k * 235 / 70 ^ 2) : 702.68 < k ∧ k < 702.69 := by
  norm_num at h
  constructor <;> linarith

end UndergradKB.Precalculus.Course
