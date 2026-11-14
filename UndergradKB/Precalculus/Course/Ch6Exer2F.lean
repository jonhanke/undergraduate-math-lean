import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 6.3 (equations, inequalities) -/

namespace UndergradKB.Precalculus.Course

open Set

private theorem x6w7f_rpow_eq {a c x : ℝ} (ha : 0 < a) (hc : 0 < c) :
    a ^ x = c ↔ x * Real.log a = Real.log c := by
  constructor
  · intro h
    have := congrArg Real.log h
    rwa [Real.log_rpow ha] at this
  · intro h
    calc a ^ x = Real.exp (Real.log a * x) := Real.rpow_def_of_pos ha x
      _ = Real.exp (Real.log c) := by rw [mul_comm, h]
      _ = c := Real.exp_log hc

private theorem x6w7f_exp_eq {y c : ℝ} (hc : 0 < c) : Real.exp y = c ↔ y = Real.log c := by
  constructor
  · intro h; rw [← h, Real.log_exp]
  · intro h; rw [h, Real.exp_log hc]

private theorem x6w7f_log_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a = b ↔ Real.log a = Real.log b :=
  ⟨fun h => by rw [h], fun h => Real.log_injOn_pos (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb) h⟩

/-- Stitz-Zeager Exercise 6.3.22: `25 (4/5)^x = 10` holds exactly for `x = ln(2/5)/ln(4/5)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.22, p. 468"]
theorem exer_6_3_22 : ∀ x : ℝ, 25 * (4 / 5 : ℝ) ^ x = 10 ↔ x = Real.log (2 / 5) / Real.log (4 / 5) := by
  intro x
  have hL : Real.log (4 / 5) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have key : 25 * (4 / 5 : ℝ) ^ x = 10 ↔ (4 / 5 : ℝ) ^ x = 2 / 5 := by
    constructor <;> intro h <;> linarith
  rw [key, x6w7f_rpow_eq (by norm_num) (by norm_num), eq_div_iff hL.ne]

/-- Stitz-Zeager Exercise 6.3.24: `7e^(2x) = 28e^(-6x)` holds exactly for `x = (ln 2)/4`. -/
@[kb "stitzzeager2013" "Exercise 6.3.24, p. 468"]
theorem exer_6_3_24 : ∀ x : ℝ, 7 * Real.exp (2 * x) = 28 * Real.exp (-6 * x) ↔ x = Real.log 2 / 4 := by
  intro x
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have e1 : Real.exp (-6 * x) * Real.exp (6 * x) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have e2 : Real.exp (2 * x) * Real.exp (6 * x) = Real.exp (8 * x) := by
    rw [← Real.exp_add]; ring_nf
  have hp : 0 < Real.exp (6 * x) := Real.exp_pos _
  have key : 7 * Real.exp (2 * x) = 28 * Real.exp (-6 * x) ↔ Real.exp (8 * x) = 4 := by
    constructor
    · intro h
      have := congrArg (· * Real.exp (6 * x)) h
      nlinarith
    · intro h
      have : 7 * Real.exp (2 * x) * Real.exp (6 * x) = 28 * Real.exp (-6 * x) * Real.exp (6 * x) := by
        rw [mul_assoc, e2, h, mul_assoc, e1]; ring
      exact mul_right_cancel₀ hp.ne' this
  rw [key, x6w7f_exp_eq (by norm_num), h4]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.25: `3^(x-1) = 2^x` holds exactly for `x = ln 3/(ln 3 - ln 2)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.25, p. 468"]
theorem exer_6_3_25 : ∀ x : ℝ, (3 : ℝ) ^ (x - 1) = (2 : ℝ) ^ x ↔
    x = Real.log 3 / (Real.log 3 - Real.log 2) := by
  intro x
  have hd : 0 < Real.log 3 - Real.log 2 := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3); linarith
  rw [x6w7f_log_eq (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _),
    Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.26: `3^(x-1) = (1/2)^(x+5)` holds exactly for
`x = (ln 3 - 5 ln 2)/(ln 3 + ln 2)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.26, p. 468"]
theorem exer_6_3_26 : ∀ x : ℝ, (3 : ℝ) ^ (x - 1) = (1 / 2 : ℝ) ^ (x + 5) ↔
    x = (Real.log 3 - 5 * Real.log 2) / (Real.log 3 + Real.log 2) := by
  intro x
  have hd : 0 < Real.log 3 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  rw [x6w7f_log_eq (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _),
    Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), one_div, Real.log_inv, eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.27: `7^(3+7x) = 3^(4-2x)` holds exactly for
`x = (4 ln 3 - 3 ln 7)/(7 ln 7 + 2 ln 3)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.27, p. 468"]
theorem exer_6_3_27 : ∀ x : ℝ, (7 : ℝ) ^ (3 + 7 * x) = (3 : ℝ) ^ (4 - 2 * x) ↔
    x = (4 * Real.log 3 - 3 * Real.log 7) / (7 * Real.log 7 + 2 * Real.log 3) := by
  intro x
  have hd : 0 < 7 * Real.log 7 + 2 * Real.log 3 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    have := Real.log_pos (by norm_num : (1 : ℝ) < 7); linarith
  rw [x6w7f_log_eq (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _),
    Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), eq_div_iff hd.ne']
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.29: `e^(2x) = e^x + 6` holds exactly for `x = ln 3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.29, p. 468"]
theorem exer_6_3_29 : ∀ x : ℝ, Real.exp (2 * x) = Real.exp x + 6 ↔ x = Real.log 3 := by
  intro x
  have e : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have hp := Real.exp_pos x
  rw [e]
  constructor
  · intro h
    have : (Real.exp x - 3) * (Real.exp x + 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact (x6w7f_exp_eq (by norm_num)).1 (by linarith)
    · linarith
  · intro h
    have : Real.exp x = 3 := (x6w7f_exp_eq (by norm_num)).2 h
    rw [this]; norm_num

/-- Stitz-Zeager Exercise 6.3.32: `e^x + 15 e^(-x) = 8` holds exactly for `x = ln 3` or `x = ln 5`. -/
@[kb "stitzzeager2013" "Exercise 6.3.32, p. 468"]
theorem exer_6_3_32 : ∀ x : ℝ, Real.exp x + 15 * Real.exp (-x) = 8 ↔ x = Real.log 3 ∨ x = Real.log 5 := by
  intro x
  have hp := Real.exp_pos x
  have key : Real.exp x + 15 * Real.exp (-x) = 8 ↔ (Real.exp x - 3) * (Real.exp x - 5) = 0 := by
    rw [Real.exp_neg]
    constructor
    · intro h; field_simp at h; nlinarith
    · intro h; field_simp; nlinarith
  rw [key, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; exact (x6w7f_exp_eq (by norm_num)).1 (by linarith)
    · right; exact (x6w7f_exp_eq (by norm_num)).1 (by linarith)
  · rintro (h | h)
    · left; have : Real.exp x = 3 := (x6w7f_exp_eq (by norm_num)).2 h
      linarith
    · right; have : Real.exp x = 5 := (x6w7f_exp_eq (by norm_num)).2 h
      linarith

/-- Stitz-Zeager Exercise 6.3.33: `3^x + 25 · 3^(-x) = 10` holds exactly for `x = ln 5/ln 3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.33, p. 468"]
theorem exer_6_3_33 : ∀ x : ℝ, (3 : ℝ) ^ x + 25 * (3 : ℝ) ^ (-x) = 10 ↔ x = Real.log 5 / Real.log 3 := by
  intro x
  have hp : 0 < (3 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have key : (3 : ℝ) ^ x + 25 * (3 : ℝ) ^ (-x) = 10 ↔ (3 : ℝ) ^ x = 5 := by
    rw [Real.rpow_neg (by norm_num)]
    constructor
    · intro h
      have h' : ((3 : ℝ) ^ x - 5) ^ 2 = 0 := by field_simp at h; nlinarith
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h'
      linarith
    · intro h; rw [h]; norm_num
  rw [key, x6w7f_rpow_eq (by norm_num) (by norm_num), eq_div_iff hL.ne']

/-- Stitz-Zeager Exercise 6.3.35: `1000 (1.005)^(12t) ≥ 3000` has solution set `[ln 3/(12 ln 1.005), ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.35, p. 468"]
theorem exer_6_3_35 :
    {t : ℝ | 1000 * (1.005 : ℝ) ^ (12 * t) ≥ 3000} = Ici (Real.log 3 / (12 * Real.log 1.005)) := by
  have hL : 0 < Real.log 1.005 := Real.log_pos (by norm_num)
  ext t
  simp only [mem_ofPred_eq, mem_Ici]
  have hp : 0 < (1.005 : ℝ) ^ (12 * t) := Real.rpow_pos_of_pos (by norm_num) _
  have key : 1000 * (1.005 : ℝ) ^ (12 * t) ≥ 3000 ↔ 3 ≤ (1.005 : ℝ) ^ (12 * t) := by
    constructor <;> intro h <;> linarith
  rw [key, ← Real.log_le_log_iff (by norm_num) hp, Real.log_rpow (by norm_num), div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.36: `2^(x³-x) < 1` has solution set `(-∞, -1) ∪ (0, 1)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.36, p. 468"]
theorem exer_6_3_36 : {x : ℝ | (2 : ℝ) ^ (x ^ 3 - x) < 1} = Iio (-1) ∪ Ioo 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioo]
  rw [Real.rpow_lt_one_iff_of_pos (by norm_num)]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · by_cases h1 : x < -1
      · left; exact h1
      · right; push Not at h1
        have h0 : 0 < x := by
          by_contra h0; push Not at h0; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x + 1) (neg_nonneg.2 h0), sq_nonneg x]
        refine ⟨h0, ?_⟩
        by_contra h2; push Not at h2; nlinarith [mul_nonneg h0.le (by nlinarith : (0 : ℝ) ≤ x ^ 2 - 1)]
    · norm_num at h
  · rintro (h | ⟨h1, h2⟩)
    · left; refine ⟨by norm_num, ?_⟩; nlinarith [mul_pos (by linarith : (0 : ℝ) < -x) (by nlinarith : (0 : ℝ) < x ^ 2 - 1)]
    · left; refine ⟨by norm_num, ?_⟩; nlinarith [mul_pos h1 (by nlinarith : (0 : ℝ) < 1 - x ^ 2)]

/-- Stitz-Zeager Exercise 6.3.37: `25 (4/5)^x ≥ 10` has solution set `(-∞, ln(2/5)/ln(4/5)]`. -/
@[kb "stitzzeager2013" "Exercise 6.3.37, p. 468"]
theorem exer_6_3_37 :
    {x : ℝ | 25 * (4 / 5 : ℝ) ^ x ≥ 10} = Iic (Real.log (2 / 5) / Real.log (4 / 5)) := by
  have hL : Real.log (4 / 5) < 0 := Real.log_neg (by norm_num) (by norm_num)
  ext x
  simp only [mem_ofPred_eq, mem_Iic]
  have hp : 0 < (4 / 5 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have key : 25 * (4 / 5 : ℝ) ^ x ≥ 10 ↔ 2 / 5 ≤ (4 / 5 : ℝ) ^ x := by
    constructor <;> intro h <;> linarith
  rw [key, ← Real.log_le_log_iff (by norm_num) hp, Real.log_rpow (by norm_num), le_div_iff_of_neg hL]

/-- Stitz-Zeager Exercise 6.3.38: `150/(1 + 29e^(-0.8t)) ≤ 130` has solution set `(-∞, (5/4) ln(377/2)]`. -/
@[kb "stitzzeager2013" "Exercise 6.3.38, p. 468"]
theorem exer_6_3_38 :
    {t : ℝ | 150 / (1 + 29 * Real.exp (-0.8 * t)) ≤ 130} = Iic (5 / 4 * Real.log (377 / 2)) := by
  ext t
  simp only [mem_ofPred_eq, mem_Iic]
  have hp : 0 < 1 + 29 * Real.exp (-0.8 * t) := by positivity
  have key : 150 / (1 + 29 * Real.exp (-0.8 * t)) ≤ 130 ↔ 2 / 377 ≤ Real.exp (-0.8 * t) := by
    rw [div_le_iff₀ hp]
    constructor <;> intro h <;> linarith
  have hl : Real.log (377 / 2) = -Real.log (2 / 377) := by
    rw [show (377 / 2 : ℝ) = (2 / 377)⁻¹ by norm_num, Real.log_inv]
  rw [key, Real.log_le_iff_le_exp (by norm_num) |>.symm, hl]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.39: `70 + 90e^(-0.1t) ≤ 75` has solution set `[10 ln 18, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 6.3.39, p. 468"]
theorem exer_6_3_39 :
    {t : ℝ | 70 + 90 * Real.exp (-0.1 * t) ≤ 75} = Ici (10 * Real.log 18) := by
  ext t
  simp only [mem_ofPred_eq, mem_Ici]
  have key : 70 + 90 * Real.exp (-0.1 * t) ≤ 75 ↔ Real.exp (-0.1 * t) ≤ 1 / 18 := by
    constructor <;> intro h <;> linarith
  rw [key, ← Real.le_log_iff_exp_le (by norm_num), one_div, Real.log_inv]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.42: for `x ≥ 0`, `e^(√x) = x + 1` holds exactly for `x = 0`. -/
@[kb "stitzzeager2013" "Exercise 6.3.42, p. 468"]
theorem exer_6_3_42 : ∀ x : ℝ, 0 ≤ x → (Real.exp (Real.sqrt x) = x + 1 ↔ x = 0) := by
  intro x hx
  constructor
  · intro h
    have hs := Real.sq_sqrt hx
    have hs0 := Real.sqrt_nonneg x
    have hex := Real.sum_le_exp_of_nonneg hs0 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hex
    norm_num at hex
    by_contra hne
    have hpos : 0 < Real.sqrt x := lt_of_le_of_ne hs0 (fun h' => hne (by rw [← hs, ← h']; ring))
    have : 0 < Real.sqrt x * ((Real.sqrt x - 3 / 2) ^ 2 + 15 / 4) := by positivity
    nlinarith
  · rintro rfl; simp

/-- Stitz-Zeager Exercise 6.3.43: `e^(-x) - x e^(-x) ≥ 0` has solution set `(-∞, 1]`. -/
@[kb "stitzzeager2013" "Exercise 6.3.43, p. 468"]
theorem exer_6_3_43 : {x : ℝ | 0 ≤ Real.exp (-x) - x * Real.exp (-x)} = Iic 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_Iic]
  have hp := Real.exp_pos (-x)
  have e : Real.exp (-x) - x * Real.exp (-x) = (1 - x) * Real.exp (-x) := by ring
  rw [e]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith
  · intro h; exact mul_nonneg (by linarith) hp.le

/-- Stitz-Zeager Exercise 6.3.44: `3^(x-1) < 2^x` has solution set `(-∞, ln 3/(ln 3 - ln 2))` (about `2.7095`). -/
@[kb "stitzzeager2013" "Exercise 6.3.44, p. 468"]
theorem exer_6_3_44 :
    {x : ℝ | (3 : ℝ) ^ (x - 1) < (2 : ℝ) ^ x} = Iio (Real.log 3 / (Real.log 3 - Real.log 2)) := by
  have hd : 0 < Real.log 3 - Real.log 2 := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3); linarith
  ext x
  simp only [mem_ofPred_eq, mem_Iio]
  rw [← Real.log_lt_log_iff (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _),
    Real.log_rpow (by norm_num), Real.log_rpow (by norm_num), lt_div_iff₀ hd]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.46: `e^(3x-1) > 6` has solution set `x > (ln 6 + 1)/3`. -/
@[kb "stitzzeager2013" "Exercise 6.3.46, p. 468"]
theorem exer_6_3_46 : {x : ℝ | 6 < Real.exp (3 * x - 1)} = Ioi ((Real.log 6 + 1) / 3) := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioi]
  rw [← Real.log_lt_iff_lt_exp (by norm_num), div_lt_iff₀ (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.3.48: for `f(x) = 5eˣ/(eˣ+1)` and `g(x) = 5x/(x+1)`: (a) `f⁻¹(x) = ln(x/(5-x))` is a
two-sided inverse (`f⁻¹(f(x)) = x`, and `f(f⁻¹(y)) = y` for `0 < y < 5`); (b) the range of `f` is `(0, 5)`;
(c) `f = g ∘ exp`, and `g⁻¹(y) = y/(5-y)` satisfies `g(g⁻¹(y)) = y`, so `f⁻¹ = ln ∘ g⁻¹`. -/
@[kb "stitzzeager2013" "Exercise 6.3.48, p. 469"]
theorem exer_6_3_48 (f g : ℝ → ℝ) (hf : f = fun x => 5 * Real.exp x / (Real.exp x + 1))
    (hg : g = fun x => 5 * x / (x + 1)) :
    (∀ x, Real.log (f x / (5 - f x)) = x) ∧
    (∀ y : ℝ, 0 < y → y < 5 → f (Real.log (y / (5 - y))) = y) ∧
    range f = Ioo 0 5 ∧ (∀ x, f x = g (Real.exp x)) ∧
    (∀ y : ℝ, 0 < y → y < 5 → g (y / (5 - y)) = y) := by
  subst hf hg
  have hr : ∀ y : ℝ, 0 < y → y < 5 → (5 * (y / (5 - y)) / (y / (5 - y) + 1) = y) := by
    intro y h1 h2
    have h5 : 5 - y ≠ 0 := by linarith
    have : y / (5 - y) + 1 = 5 / (5 - y) := by field_simp; ring
    rw [this]; field_simp
  have hb : ∀ y : ℝ, 0 < y → y < 5 →
      (fun x : ℝ => 5 * Real.exp x / (Real.exp x + 1)) (Real.log (y / (5 - y))) = y := by
    intro y h1 h2
    simp only
    rw [Real.exp_log (div_pos h1 (by linarith))]
    exact hr y h1 h2
  refine ⟨fun x => ?_, hb, ?_, fun x => rfl, hr⟩
  · have hp := Real.exp_pos x
    have h1 : 5 - 5 * Real.exp x / (Real.exp x + 1) = 5 / (Real.exp x + 1) := by field_simp; ring
    simp only
    rw [h1, div_div_div_cancel_right₀ (by positivity)]
    have : 5 * Real.exp x / 5 = Real.exp x := by ring
    rw [this, Real.log_exp]
  · ext y
    simp only [mem_range, mem_Ioo]
    constructor
    · rintro ⟨x, rfl⟩
      have hp := Real.exp_pos x
      refine ⟨by positivity, ?_⟩
      rw [div_lt_iff₀ (by positivity)]; linarith
    · rintro ⟨h1, h2⟩
      exact ⟨_, hb y h1 h2⟩

end UndergradKB.Precalculus.Course
