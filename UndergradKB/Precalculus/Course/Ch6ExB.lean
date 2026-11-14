import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.InverseFunctions

/-! # Course layer, Chapter 6 (Stitz-Zeager): worked examples, Sections 6.4 and 6.5 -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology Real UndergradKB.Precalculus

/-! ## Helpers -/

private theorem eq_iff_log_aux' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a = b ↔ Real.log a = Real.log b :=
  ⟨fun h => by rw [h], fun h => Real.log_injOn_pos (mem_Ioi.2 ha) (mem_Ioi.2 hb) h⟩

private theorem exp_eq_iff_aux' {u c : ℝ} (hc : 0 < c) : Real.exp u = c ↔ u = Real.log c :=
  ⟨fun h => by rw [← h, Real.log_exp], fun h => by rw [h, Real.exp_log hc]⟩

private theorem logb_eq_iff_aux {b y x : ℝ} (hb : 1 < b) (hy : 0 < y) : logb b y = x ↔ b ^ x = y :=
  Real.logb_eq_iff_rpow_eq (by linarith) (by linarith) hy

/-! ## Section 6.4 -/

/-- Stitz-Zeager Example 6.4.1(1): `log₁₁₇ (1-3x) = log₁₁₇ (x²-3)` (both arguments positive) holds only for
`x = -4`; the other root `x = 1` of `1-3x = x²-3` is extraneous. -/
@[kb "stitzzeager2013" "Example 6.4.1, p. 471"]
theorem ex_6_4_1_a (x : ℝ) :
    (0 < 1 - 3 * x ∧ 0 < x ^ 2 - 3 ∧ logb 117 (1 - 3 * x) = logb 117 (x ^ 2 - 3)) ↔ x = -4 := by
  constructor
  · rintro ⟨h1, h2, h⟩
    have h' := Real.logb_injOn_pos (by norm_num : (1 : ℝ) < 117) (mem_Ioi.2 h1) (mem_Ioi.2 h2) h
    have : (x + 4) * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exfalso; nlinarith
  · rintro rfl
    refine ⟨by norm_num, by norm_num, ?_⟩
    norm_num

/-- Stitz-Zeager Example 6.4.1(2): `2 - ln (x-3) = 1` (with `x > 3`) holds exactly when `x = e + 3`. -/
@[kb "stitzzeager2013" "Example 6.4.1, p. 471"]
theorem ex_6_4_1_b (x : ℝ) : (0 < x - 3 ∧ 2 - Real.log (x - 3) = 1) ↔ x = Real.exp 1 + 3 := by
  constructor
  · rintro ⟨h1, h⟩
    have : Real.log (x - 3) = 1 := by linarith
    have h3 : Real.exp 1 = x - 3 := (exp_eq_iff_aux' h1).mpr this.symm
    linarith
  · rintro rfl
    refine ⟨by have := Real.exp_pos 1; linarith, ?_⟩
    rw [add_sub_cancel_right, Real.log_exp]
    norm_num

/-- Stitz-Zeager Example 6.4.1(3): `log₆ (x+4) + log₆ (3-x) = 1` (both arguments positive) holds exactly for
`x = -3` or `x = 2`. -/
@[kb "stitzzeager2013" "Example 6.4.1, p. 471"]
theorem ex_6_4_1_c (x : ℝ) :
    (0 < x + 4 ∧ 0 < 3 - x ∧ logb 6 (x + 4) + logb 6 (3 - x) = 1) ↔ x = -3 ∨ x = 2 := by
  constructor
  · rintro ⟨h1, h2, h⟩
    rw [← Real.logb_mul h1.ne' h2.ne', logb_eq_iff_aux (by norm_num) (by positivity)] at h
    rw [Real.rpow_one] at h
    have : (x + 3) * (x - 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl)
    · refine ⟨by norm_num, by norm_num, ?_⟩
      rw [← Real.logb_mul (by norm_num) (by norm_num), logb_eq_iff_aux (by norm_num) (by norm_num)]
      norm_num
    · refine ⟨by norm_num, by norm_num, ?_⟩
      rw [← Real.logb_mul (by norm_num) (by norm_num), logb_eq_iff_aux (by norm_num) (by norm_num)]
      norm_num

/-- Stitz-Zeager Example 6.4.1(4): `log₇ (1-2x) = 1 - log₇ (3-x)` (both arguments positive) holds exactly for
`x = -1/2`; the root `x = 4` is extraneous. -/
@[kb "stitzzeager2013" "Example 6.4.1, p. 471"]
theorem ex_6_4_1_d (x : ℝ) :
    (0 < 1 - 2 * x ∧ 0 < 3 - x ∧ logb 7 (1 - 2 * x) = 1 - logb 7 (3 - x)) ↔ x = -1 / 2 := by
  constructor
  · rintro ⟨h1, h2, h⟩
    have h' : logb 7 ((1 - 2 * x) * (3 - x)) = 1 := by
      rw [Real.logb_mul h1.ne' h2.ne']; linarith
    rw [logb_eq_iff_aux (by norm_num) (by positivity), Real.rpow_one] at h'
    have : (2 * x + 1) * (x - 4) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exfalso; linarith
  · rintro rfl
    refine ⟨by norm_num, by norm_num, ?_⟩
    have : logb 7 ((1 - 2 * (-1 / 2)) * (3 - (-1 / 2))) = 1 := by
      rw [logb_eq_iff_aux (by norm_num) (by norm_num)]; norm_num
    rw [Real.logb_mul (by norm_num) (by norm_num)] at this
    linarith

/-- Stitz-Zeager Example 6.4.1(5): `log₂ (x+3) = log₂ (6-x) + 3` (both arguments positive) holds exactly for
`x = 5`. -/
@[kb "stitzzeager2013" "Example 6.4.1, p. 471"]
theorem ex_6_4_1_e (x : ℝ) :
    (0 < x + 3 ∧ 0 < 6 - x ∧ logb 2 (x + 3) = logb 2 (6 - x) + 3) ↔ x = 5 := by
  constructor
  · rintro ⟨h1, h2, h⟩
    have h' : logb 2 ((x + 3) / (6 - x)) = 3 := by
      rw [Real.logb_div h1.ne' h2.ne']; linarith
    rw [logb_eq_iff_aux (by norm_num) (by positivity)] at h'
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
    rw [h8, eq_div_iff h2.ne'] at h'
    linarith
  · rintro rfl
    refine ⟨by norm_num, by norm_num, ?_⟩
    have : logb 2 (((5 : ℝ) + 3) / (6 - 5)) = 3 := by
      rw [logb_eq_iff_aux (by norm_num) (by norm_num)]; norm_num
    rw [Real.logb_div (by norm_num) (by norm_num)] at this
    linarith

/-- Stitz-Zeager Example 6.4.1(6): for `x > 0`, `1 + 2 log₄ (x+1) = 2 log₂ x` holds exactly when
`x = 1 + √3`; the other root `1 - √3` is negative. -/
@[kb "stitzzeager2013" "Example 6.4.1, p. 471"]
theorem ex_6_4_1_f (x : ℝ) (hx : 0 < x) :
    1 + 2 * logb 4 (x + 1) = 2 * logb 2 x ↔ x = 1 + √3 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
  have key : 1 + 2 * logb 4 (x + 1) = 2 * logb 2 x ↔ Real.log (2 * (x + 1)) = Real.log (x ^ 2) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    simp only [Real.logb]
    rw [h4]
    push_cast
    constructor
    · intro h
      field_simp at h
      linarith
    · intro h
      field_simp
      linarith
  rw [key, ← eq_iff_log_aux' (by positivity) (by positivity)]
  constructor
  · intro h
    have : (x - (1 + √3)) * (x - (1 - √3)) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exfalso; nlinarith
  · rintro rfl
    nlinarith

/-- Stitz-Zeager Example 6.4.2(1): `1/(ln x + 1) ≤ 1` (with `x > 0`, `ln x ≠ -1`) holds exactly on
`(0, 1/e) ∪ [1, ∞)`. -/
@[kb "stitzzeager2013" "Example 6.4.2, p. 474"]
theorem ex_6_4_2_a :
    {x : ℝ | 0 < x ∧ Real.log x + 1 ≠ 0 ∧ 1 / (Real.log x + 1) ≤ 1} =
      Ioo 0 (Real.exp (-1)) ∪ Ici 1 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Ioo, mem_Ici]
  constructor
  · rintro ⟨hx, hne, h⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      refine ⟨hx, ?_⟩
      rw [← Real.log_lt_iff_lt_exp hx]
      linarith
    · right
      rw [div_le_one hgt] at h
      have : 0 ≤ Real.log x := by linarith
      exact (Real.log_nonneg_iff hx).mp this
  · rintro (⟨hx, h⟩ | h)
    · have hl : Real.log x < -1 := (Real.log_lt_iff_lt_exp hx).mpr h
      refine ⟨hx, by linarith, ?_⟩
      have : 1 / (Real.log x + 1) < 0 := by
        apply div_neg_of_pos_of_neg one_pos; linarith
      linarith
    · have hx : 0 < x := by linarith
      have : 0 ≤ Real.log x := (Real.log_nonneg_iff hx).mpr h
      refine ⟨hx, by linarith, ?_⟩
      rw [div_le_one (by linarith)]
      linarith

/-- Stitz-Zeager Example 6.4.2(2): `(log₂ x)² < 2 log₂ x + 3` (with `x > 0`) holds exactly for `1/2 < x < 8`. -/
@[kb "stitzzeager2013" "Example 6.4.2, p. 474"]
theorem ex_6_4_2_b :
    {x : ℝ | 0 < x ∧ (logb 2 x) ^ 2 < 2 * logb 2 x + 3} = Ioo (1 / 2) 8 := by
  ext x
  simp only [mem_setOf_eq, mem_Ioo]
  have e1 : ∀ hx : 0 < x, (-1 < logb 2 x ↔ 1 / 2 < x) := by
    intro hx
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hx]
    norm_num [Real.rpow_neg]
  have e2 : ∀ hx : 0 < x, (logb 2 x < 3 ↔ x < 8) := by
    intro hx
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) hx]
    norm_num
  constructor
  · rintro ⟨hx, h⟩
    have h1 : -1 < logb 2 x := by nlinarith
    have h2 : logb 2 x < 3 := by nlinarith
    exact ⟨(e1 hx).mp h1, (e2 hx).mp h2⟩
  · rintro ⟨h1, h2⟩
    have hx : 0 < x := by linarith
    have a := (e1 hx).mpr h1
    have b := (e2 hx).mpr h2
    exact ⟨hx, by nlinarith⟩

/-- Stitz-Zeager Example 6.4.2(3): `x log (x+1) ≥ x` (with `x > -1`) holds exactly on `(-1, 0] ∪ [9, ∞)`. -/
@[kb "stitzzeager2013" "Example 6.4.2, p. 474"]
theorem ex_6_4_2_c :
    {x : ℝ | -1 < x ∧ x ≤ x * logb 10 (x + 1)} = Ioc (-1) 0 ∪ Ici 9 := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Ioc, mem_Ici]
  constructor
  · rintro ⟨hx, h⟩
    have hp : 0 < x + 1 := by linarith
    rcases le_or_gt x 0 with h0 | h0
    · left; exact ⟨hx, h0⟩
    · right
      have h1 : 1 ≤ logb 10 (x + 1) := by nlinarith
      rw [Real.le_logb_iff_rpow_le (by norm_num) hp, Real.rpow_one] at h1
      linarith
  · rintro (⟨hx, h0⟩ | h9)
    · refine ⟨hx, ?_⟩
      have hp : 0 < x + 1 := by linarith
      have h1 : logb 10 (x + 1) ≤ 1 := by
        rw [Real.logb_le_iff_le_rpow (by norm_num) hp, Real.rpow_one]
        linarith
      nlinarith
    · have hp : 0 < x + 1 := by linarith
      refine ⟨by linarith, ?_⟩
      have h1 : 1 ≤ logb 10 (x + 1) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) hp, Real.rpow_one]
        linarith
      nlinarith

/-- Stitz-Zeager Example 6.4.3: for a hydrogen-ion concentration `h > 0`, the pH `-log h` lies in `[7.8, 8.5]`
exactly when `10^(-8.5) ≤ h ≤ 10^(-7.8)`. -/
@[kb "stitzzeager2013" "Example 6.4.3, p. 476"]
theorem ex_6_4_3 (h : ℝ) (hh : 0 < h) :
    (39 / 5 ≤ -logb 10 h ∧ -logb 10 h ≤ 17 / 2) ↔
      (10 : ℝ) ^ (-(17 / 2) : ℝ) ≤ h ∧ h ≤ (10 : ℝ) ^ (-(39 / 5) : ℝ) := by
  have e1 : 39 / 5 ≤ -logb 10 h ↔ logb 10 h ≤ -(39 / 5) := by constructor <;> intro h <;> linarith
  have e2 : -logb 10 h ≤ 17 / 2 ↔ -(17 / 2) ≤ logb 10 h := by constructor <;> intro h <;> linarith
  rw [e1, e2, Real.logb_le_iff_le_rpow (by norm_num) hh, Real.le_logb_iff_rpow_le (by norm_num) hh]
  exact and_comm

/-- Stitz-Zeager Example 6.4.4: `f(x) = log x/(1 - log x)` (domain `x > 0`, `x ≠ 10`; range `y ≠ -1`) has
inverse `f⁻¹(x) = 10^(x/(x+1))`. -/
@[kb "stitzzeager2013" "Example 6.4.4, p. 476"]
theorem ex_6_4_4 :
    InverseOn (fun x : ℝ => logb 10 x / (1 - logb 10 x)) (fun x : ℝ => (10 : ℝ) ^ (x / (x + 1)))
      {x | 0 < x ∧ x ≠ 10} {y | y ≠ -1} := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨hx0, hx10⟩ := hx
    have hu : logb 10 x ≠ 1 := by
      intro h
      apply hx10
      have := (logb_eq_iff_aux (by norm_num) hx0).mp h
      simpa using this.symm
    have h1 : 1 - logb 10 x ≠ 0 := fun h => hu (by linarith)
    refine ⟨?_, ?_⟩
    · intro h
      rw [div_eq_iff h1] at h
      apply hu
      linarith
    · simp only
      have e : logb 10 x / (1 - logb 10 x) + 1 = 1 / (1 - logb 10 x) := by
        field_simp
        ring
      rw [e, div_div_div_cancel_right₀ h1, div_one]
      exact Real.rpow_logb (by norm_num) (by norm_num) hx0
  · simp only [mem_setOf_eq] at hy
    have h1 : y + 1 ≠ 0 := fun h => hy (by linarith)
    have hpos : 0 < (10 : ℝ) ^ (y / (y + 1)) := by positivity
    refine ⟨⟨hpos, ?_⟩, ?_⟩
    · intro h
      have h' := congrArg (logb 10) h
      rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_self_eq_one (by norm_num)] at h'
      rw [div_eq_one_iff_eq h1] at h'
      linarith
    · simp only
      rw [Real.logb_rpow (by norm_num) (by norm_num)]
      have e : 1 - y / (y + 1) = 1 / (y + 1) := by
        field_simp
        ring
      rw [e]
      field_simp

/-! ## Section 6.5 -/

/-- Stitz-Zeager Example 6.5.1(1): compounding `$2000` at `7.125%` monthly gives
`2000 (1 + 0.07125/12)^(12t) = 2000 (1.0059375)^(12t)`. -/
@[kb "stitzzeager2013" "Example 6.5.1, p. 482"]
theorem ex_6_5_1_a (t : ℝ) :
    2000 * (1 + (0.07125 : ℝ) / 12) ^ (12 * t) = 2000 * (1.0059375 : ℝ) ^ (12 * t) := by
  norm_num

/-- Stitz-Zeager Example 6.5.1(2): after 5 years the balance `2000 (1.0059375)^60` lies between `2852` and
`2853` dollars. -/
@[kb "stitzzeager2013" "Example 6.5.1, p. 482"]
theorem ex_6_5_1_b : 2852 < 2000 * (1.0059375 : ℝ) ^ 60 ∧ 2000 * (1.0059375 : ℝ) ^ 60 < 2853 := by
  constructor <;> norm_num

/-- Stitz-Zeager Example 6.5.1(3): the balance `2000 (1.0059375)^(12t)` equals `4000` exactly when
`t = ln 2 / (12 ln 1.0059375)`. -/
@[kb "stitzzeager2013" "Example 6.5.1, p. 482"]
theorem ex_6_5_1_c (t : ℝ) :
    2000 * (1.0059375 : ℝ) ^ (12 * t) = 4000 ↔ t = Real.log 2 / (12 * Real.log 1.0059375) := by
  have hl : 0 < Real.log (1.0059375 : ℝ) := Real.log_pos (by norm_num)
  have e : 2000 * (1.0059375 : ℝ) ^ (12 * t) = 4000 ↔ (1.0059375 : ℝ) ^ (12 * t) = 2 := by
    constructor <;> intro h <;> linarith
  rw [e, ← Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
  simp only [Real.logb]
  rw [div_eq_iff hl.ne', eq_div_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.5.2: for the growth law `N = 12 e^(kt)`, the condition `N(7) = 5000` holds exactly
when `k = (1/7) ln (1250/3)`. -/
@[kb "stitzzeager2013" "Example 6.5.2, p. 484"]
theorem ex_6_5_2 (k : ℝ) : 12 * Real.exp (7 * k) = 5000 ↔ k = Real.log (1250 / 3) / 7 := by
  have e : 12 * Real.exp (7 * k) = 5000 ↔ Real.exp (7 * k) = 1250 / 3 := by
    constructor <;> intro h <;> linarith
  rw [e, exp_eq_iff_aux' (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.5.3: for the decay law `A = 5 e^(kt)`, the half-life condition `A(8) = 5/2` holds
exactly when `k = -(ln 2)/8`, and then `5 e^(kt) = 5 (1/2)^(t/8)`. -/
@[kb "stitzzeager2013" "Example 6.5.3, p. 485"]
theorem ex_6_5_3 :
    (∀ k : ℝ, 5 * Real.exp (8 * k) = 5 / 2 ↔ k = -Real.log 2 / 8) ∧
    ∀ t : ℝ, 5 * Real.exp (-Real.log 2 / 8 * t) = 5 * (1 / 2 : ℝ) ^ (t / 8) := by
  have hl : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  refine ⟨fun k => ?_, fun t => ?_⟩
  · have e : 5 * Real.exp (8 * k) = 5 / 2 ↔ Real.exp (8 * k) = 1 / 2 := by
      constructor <;> intro h <;> linarith
    rw [e, exp_eq_iff_aux' (by norm_num), hl]
    constructor <;> intro h <;> linarith
  · rw [Real.rpow_def_of_pos (by norm_num), hl]
    congr 2
    ring

/-- Stitz-Zeager Example 6.5.4(1): for Newton's warming law `T = 350 - 310 e^(-kt)`, the condition `T(2) = 125`
holds exactly when `k = -(1/2) ln (45/62)`. -/
@[kb "stitzzeager2013" "Example 6.5.4, p. 486"]
theorem ex_6_5_4_a (k : ℝ) :
    350 - 310 * Real.exp (-k * 2) = 125 ↔ k = -(1 / 2) * Real.log (45 / 62) := by
  have e : 350 - 310 * Real.exp (-k * 2) = 125 ↔ Real.exp (-k * 2) = 45 / 62 := by
    constructor <;> intro h <;> linarith
  rw [e, exp_eq_iff_aux' (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.5.4(2): with `k = -(1/2) ln (45/62)`, the roast temperature `350 - 310 e^(-kt)` equals
`165` exactly when `t = ln (62/37) / k`. -/
@[kb "stitzzeager2013" "Example 6.5.4, p. 486"]
theorem ex_6_5_4_b (t : ℝ) :
    350 - 310 * Real.exp (-(-(1 / 2) * Real.log (45 / 62)) * t) = 165 ↔
      t = Real.log (62 / 37) / (-(1 / 2) * Real.log (45 / 62)) := by
  have hneg : Real.log (45 / 62) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hk : -(1 / 2) * Real.log (45 / 62) ≠ 0 := by linarith
  have hl : Real.log (37 / 62) = -Real.log (62 / 37) := by
    rw [show (37 / 62 : ℝ) = (62 / 37)⁻¹ by norm_num, Real.log_inv]
  have e : 350 - 310 * Real.exp (-(-(1 / 2) * Real.log (45 / 62)) * t) = 165 ↔
      Real.exp (-(-(1 / 2) * Real.log (45 / 62)) * t) = 37 / 62 := by
    constructor <;> intro h <;> linarith
  rw [e, exp_eq_iff_aux' (by norm_num), hl, eq_div_iff hk]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.5.5(1,2): the rumor model `N(t) = 84/(1 + 2799 e^(-t))` has `N(0) = 3/100` (three people, counted in hundreds)
and tends to `84` as `t → ∞`. -/
@[kb "stitzzeager2013" "Example 6.5.5, p. 487"]
theorem ex_6_5_5_a :
    (fun t : ℝ => 84 / (1 + 2799 * Real.exp (-t))) 0 = 3 / 100 ∧
    Tendsto (fun t : ℝ => 84 / (1 + 2799 * Real.exp (-t))) atTop (𝓝 84) := by
  refine ⟨by norm_num, ?_⟩
  have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (2799 : ℝ)
  have h2 := h1.const_add (1 : ℝ)
  have h3 := (tendsto_const_nhds (x := (84 : ℝ))).div h2 (by norm_num)
  rw [mul_zero, add_zero, div_one] at h3
  exact h3

/-- Stitz-Zeager Example 6.5.5(3): `84/(1 + 2799 e^(-t)) = 42` holds exactly when `t = ln 2799`. -/
@[kb "stitzzeager2013" "Example 6.5.5, p. 487"]
theorem ex_6_5_5_b (t : ℝ) : 84 / (1 + 2799 * Real.exp (-t)) = 42 ↔ t = Real.log 2799 := by
  have hpos := Real.exp_pos (-t)
  have hne : 1 + 2799 * Real.exp (-t) ≠ 0 := by positivity
  have hl : Real.log (1 / 2799) = -Real.log 2799 := by rw [one_div, Real.log_inv]
  rw [div_eq_iff hne]
  have e : 84 = 42 * (1 + 2799 * Real.exp (-t)) ↔ Real.exp (-t) = 1 / 2799 := by
    constructor <;> intro h <;> linarith
  rw [e, exp_eq_iff_aux' (by norm_num), hl]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.5.6(1): the entropy `7 log₂ 62` of a 7-character password over 62 symbols lies strictly
between `41.6` and `41.8` bits. -/
@[kb "stitzzeager2013" "Example 6.5.6, p. 489"]
theorem ex_6_5_6_a : 41.6 < 7 * logb 2 62 ∧ 7 * logb 2 62 < 41.8 := by
  have h70 : logb 2 ((62 : ℝ) ^ 35) = 35 * logb 2 62 := by
    rw [Real.logb_pow]; norm_num
  have hpos : (0 : ℝ) < 62 ^ 35 := by positivity
  have lo : ∀ M : ℝ, 0 < M → (2 : ℝ) ^ (208 : ℝ) < M → (208 : ℝ) < logb 2 M := fun M hM h =>
    (Real.lt_logb_iff_rpow_lt (show (1 : ℝ) < 2 by norm_num) hM).mpr h
  have hi : ∀ M : ℝ, 0 < M → M < (2 : ℝ) ^ (209 : ℝ) → logb 2 M < 209 := fun M hM h =>
    (Real.logb_lt_iff_lt_rpow (show (1 : ℝ) < 2 by norm_num) hM).mpr h
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 62 ^ 35 := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; exact hpos
  have h70' : logb 2 M = 35 * logb 2 62 := by rw [hM]; exact h70
  have hlo : (2 : ℝ) ^ (208 : ℝ) < M := by rw [hM]; norm_num
  have hhi : M < (2 : ℝ) ^ (209 : ℝ) := by rw [hM]; norm_num
  constructor
  · have := lo M hMpos hlo
    linarith
  · have := hi M hMpos hhi
    linarith

/-- Stitz-Zeager Example 6.5.6(2): for `N > 0`, the entropy equation `50 = 7 log₂ N` holds exactly when
`N = 2^(50/7)`, and this number lies strictly between `141` and `142`. -/
@[kb "stitzzeager2013" "Example 6.5.6, p. 489"]
theorem ex_6_5_6_b :
    (∀ N : ℝ, 0 < N → (50 = 7 * logb 2 N ↔ N = (2 : ℝ) ^ (50 / 7 : ℝ))) ∧
    141 < (2 : ℝ) ^ (50 / 7 : ℝ) ∧ (2 : ℝ) ^ (50 / 7 : ℝ) < 142 := by
  have hy : 0 < (2 : ℝ) ^ (50 / 7 : ℝ) := by positivity
  have h7 : ((2 : ℝ) ^ (50 / 7 : ℝ)) ^ 7 = 2 ^ 50 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨fun N hN => ?_, ?_, ?_⟩
  · have e : 50 = 7 * logb 2 N ↔ logb 2 N = 50 / 7 := by
      constructor <;> intro h <;> linarith
    rw [e, logb_eq_iff_aux (by norm_num) hN, eq_comm]
  · by_contra hc
    push_neg at hc
    have := pow_le_pow_left₀ hy.le hc 7
    rw [h7] at this
    norm_num at this
  · by_contra hc
    push_neg at hc
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 142) hc 7
    rw [h7] at this
    norm_num at this

/-- Stitz-Zeager Example 6.5.7: for the blood model `pH = 6.1 + log (800/x)` with `x > 0`, the pH equals `7.4`
exactly when `x = 800 / 10^(13/10)`. -/
@[kb "stitzzeager2013" "Example 6.5.7, p. 490"]
theorem ex_6_5_7 (x : ℝ) (hx : 0 < x) :
    7.4 = 6.1 + logb 10 (800 / x) ↔ x = 800 / (10 : ℝ) ^ (13 / 10 : ℝ) := by
  have hp : 0 < 800 / x := by positivity
  have e : (7.4 : ℝ) = 6.1 + logb 10 (800 / x) ↔ logb 10 (800 / x) = 13 / 10 := by
    constructor <;> intro h <;> linarith
  have h10 : 0 < (10 : ℝ) ^ (13 / 10 : ℝ) := by positivity
  rw [e, logb_eq_iff_aux (by norm_num) hp]
  constructor
  · intro h
    rw [eq_div_iff hx.ne'] at h
    rw [eq_div_iff h10.ne']
    linarith
  · intro h
    rw [h]
    field_simp

end UndergradKB.Precalculus.Course
