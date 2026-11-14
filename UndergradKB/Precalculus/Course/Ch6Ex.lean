import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.InverseFunctions

/-! # Course layer, Chapter 6 (Stitz-Zeager): worked examples -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology Real UndergradKB.Precalculus

/-! ## Helpers -/

private theorem logb_eq_of_rpow {b x y : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (hx : 0 < x) (h : b ^ y = x) :
    logb b x = y :=
  (Real.logb_eq_iff_rpow_eq hb hb1 hx).mpr h

private theorem tendsto_div_zero_atTop_aux (a b : ℝ) :
    Tendsto (fun x : ℝ => a / (x + b)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ b tendsto_id)

private theorem tendsto_div_zero_atBot_aux (a b : ℝ) :
    Tendsto (fun x : ℝ => a / (x + b)) atBot (𝓝 0) :=
  tendsto_const_nhds.div_atBot (tendsto_atBot_add_const_right _ b tendsto_id)

private theorem ex_6_1_3_b' : logb 2 8 = 3 :=
  logb_eq_of_rpow (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Section 6.1 -/

/-- Stitz-Zeager Example 6.1.1: the car value `V(x) = 25 (4/5)^x` starts at `25` and tends to `0`, so `y = 0` is
a horizontal asymptote. -/
@[kb "stitzzeager2013" "Example 6.1.1, p. 432"]
theorem ex_6_1_1 :
    (fun x : ℝ => 25 * (4 / 5 : ℝ) ^ x) 0 = 25 ∧
    Tendsto (fun x : ℝ => 25 * (4 / 5 : ℝ) ^ x) atTop (𝓝 0) := by
  refine ⟨by simp, ?_⟩
  have hl : Real.log (4 / 5) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have h1 : Tendsto (fun x : ℝ => Real.log (4 / 5) * x) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg hl
  have h2 := Real.tendsto_exp_atBot.comp h1
  have h3 := h2.const_mul (25 : ℝ)
  rw [mul_zero] at h3
  refine h3.congr (fun x => ?_)
  simp [Real.rpow_def_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)]

/-- Stitz-Zeager Example 6.1.2: the coffee temperature `T(t) = 70 + 90 e^(-t/10)` has `T(0) = 160`, stays above
`70`, and tends to `70`, so `y = 70` is a horizontal asymptote. -/
@[kb "stitzzeager2013" "Example 6.1.2, p. 433"]
theorem ex_6_1_2 :
    (fun t : ℝ => 70 + 90 * Real.exp (-(1 / 10) * t)) 0 = 160 ∧
    (∀ t : ℝ, 70 < 70 + 90 * Real.exp (-(1 / 10) * t)) ∧
    Tendsto (fun t : ℝ => 70 + 90 * Real.exp (-(1 / 10) * t)) atTop (𝓝 70) := by
  refine ⟨by norm_num, fun t => by have := Real.exp_pos (-(1 / 10) * t); linarith, ?_⟩
  have h1 : Tendsto (fun x : ℝ => -(1 / 10) * x) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num)
  have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (90 : ℝ)
  have h3 := h2.const_add (70 : ℝ)
  simpa using h3

/-- Stitz-Zeager Example 6.1.3(1): `log₃ 81 = 4`. -/
@[kb "stitzzeager2013" "Example 6.1.3, p. 436"]
theorem ex_6_1_3_a : logb 3 81 = 4 :=
  logb_eq_of_rpow (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Example 6.1.3(2): `log₂ (1/8) = -3`. -/
@[kb "stitzzeager2013" "Example 6.1.3, p. 436"]
theorem ex_6_1_3_b : logb 2 (1 / 8) = -3 :=
  logb_eq_of_rpow (by norm_num) (by norm_num) (by norm_num) (by norm_num [Real.rpow_neg])

/-- Stitz-Zeager Example 6.1.3(3): `log_√5 25 = 4`. -/
@[kb "stitzzeager2013" "Example 6.1.3, p. 436"]
theorem ex_6_1_3_c : logb (√5) 25 = 4 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  refine logb_eq_of_rpow (Real.sqrt_pos.mpr (by norm_num)) ?_ (by norm_num) ?_
  · intro h
    rw [h] at h5
    norm_num at h5
  · rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith [h5]

/-- Stitz-Zeager Example 6.1.3(4): `ln (∛(e²)) = 2/3`. -/
@[kb "stitzzeager2013" "Example 6.1.3, p. 436"]
theorem ex_6_1_3_d : Real.log (Real.exp 2 ^ ((1 : ℝ) / 3)) = 2 / 3 := by
  rw [Real.log_rpow (Real.exp_pos 2), Real.log_exp]
  norm_num

/-- Stitz-Zeager Example 6.1.3(5): `log 0.001 = -3` (common logarithm). -/
@[kb "stitzzeager2013" "Example 6.1.3, p. 436"]
theorem ex_6_1_3_e : logb 10 (1 / 1000) = -3 :=
  logb_eq_of_rpow (by norm_num) (by norm_num) (by norm_num) (by norm_num [Real.rpow_neg])

/-- Stitz-Zeager Example 6.1.3(6): `2^(log₂ 8) = 8`. -/
@[kb "stitzzeager2013" "Example 6.1.3, p. 436"]
theorem ex_6_1_3_f : (2 : ℝ) ^ logb 2 8 = 8 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Example 6.1.3(7): `117^(-log₁₁₇ 6) = 1/6`. -/
@[kb "stitzzeager2013" "Example 6.1.3, p. 436"]
theorem ex_6_1_3_g : (117 : ℝ) ^ (-logb 117 6) = 1 / 6 := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  simp

/-- Stitz-Zeager Example 6.1.4(1): `f(x) = 2 log(3 - x) - 1` is defined exactly for `x < 3`. -/
@[kb "stitzzeager2013" "Example 6.1.4, p. 437"]
theorem ex_6_1_4_a : {x : ℝ | 0 < 3 - x} = Iio 3 := by
  ext x
  simp only [mem_setOf_eq, mem_Iio]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.1.4(2): `g(x) = ln (x/(x-1))` is defined exactly for `x < 0` or `x > 1`, and
`g(x) → 0` as `x → ∞` and as `x → -∞`. -/
@[kb "stitzzeager2013" "Example 6.1.4, p. 437"]
theorem ex_6_1_4_b :
    {x : ℝ | 0 < x / (x - 1)} = Iio 0 ∪ Ioi 1 ∧
    Tendsto (fun x : ℝ => Real.log (x / (x - 1))) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => Real.log (x / (x - 1))) atBot (𝓝 0) := by
  have key : ∀ x : ℝ, x ≠ 1 → x / (x - 1) = 1 + 1 / (x + -1) := by
    intro x hx
    have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    have h2 : x + -1 ≠ 0 := by intro h; apply h1; linarith
    field_simp
    ring
  have hc : ContinuousAt Real.log 1 := Real.continuousAt_log one_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
    rw [div_pos_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · right; linarith
      · left; exact h1
    · rintro (h | h)
      · right; exact ⟨h, by linarith⟩
      · left; exact ⟨by linarith, by linarith⟩
  · have h1 : Tendsto (fun x : ℝ => 1 + 1 / (x + -1)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_div_zero_atTop_aux 1 (-1))
      simpa using this
    have h2 := (hc.tendsto.comp h1)
    rw [Real.log_one] at h2
    refine h2.congr' ((eventually_gt_atTop 1).mono fun x hx => ?_)
    simp only [Function.comp]
    rw [key x hx.ne']
  · have h1 : Tendsto (fun x : ℝ => 1 + 1 / (x + -1)) atBot (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_div_zero_atBot_aux 1 (-1))
      simpa using this
    have h2 := (hc.tendsto.comp h1)
    rw [Real.log_one] at h2
    refine h2.congr' ((eventually_lt_atBot 1).mono fun x hx => ?_)
    simp only [Function.comp]
    rw [key x hx.ne]

/-- Stitz-Zeager Example 6.1.5: `f(x) = 2^(x-1) - 3` has range `(-3, ∞)` and inverse
`f⁻¹(x) = log₂(x+3) + 1`. -/
@[kb "stitzzeager2013" "Example 6.1.5, p. 438"]
theorem ex_6_1_5 :
    InverseOn (fun x : ℝ => (2 : ℝ) ^ (x - 1) - 3) (fun x : ℝ => logb 2 (x + 3) + 1) univ (Ioi (-3)) := by
  refine ⟨fun x _ => ⟨?_, ?_⟩, fun y hy => ⟨mem_univ _, ?_⟩⟩
  · have := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (x - 1)
    simp only [mem_Ioi]
    linarith
  · simp only [sub_add_cancel]
    rw [Real.logb_rpow (by norm_num) (by norm_num)]
    ring
  · simp only [mem_Ioi] at hy
    simp only [add_sub_cancel_right]
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
    ring

/-! ## Section 6.2 -/

/-- Stitz-Zeager Example 6.2.1(1): for `x > 0`, `log₂ (8/x) = -log₂ x + 3`. -/
@[kb "stitzzeager2013" "Example 6.2.1, p. 450"]
theorem ex_6_2_1_a (x : ℝ) (hx : 0 < x) : logb 2 (8 / x) = -logb 2 x + 3 := by
  rw [Real.logb_div (by norm_num) hx.ne', ex_6_1_3_b']
  ring

/-- Stitz-Zeager Example 6.2.1(2): for `x > 0`, `log_{0.1} (10 x²) = 2 log_{0.1} x - 1`. -/
@[kb "stitzzeager2013" "Example 6.2.1, p. 450"]
theorem ex_6_2_1_b (x : ℝ) (hx : 0 < x) : logb (1 / 10) (10 * x ^ 2) = 2 * logb (1 / 10) x - 1 := by
  have h10 : logb (1 / 10) 10 = -1 :=
    logb_eq_of_rpow (by norm_num) (by norm_num) (by norm_num) (by norm_num [Real.rpow_neg])
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, h10]
  push_cast
  ring

/-- Stitz-Zeager Example 6.2.1(3): for `x > 0`, `ln ((3/(ex))²) = -2 ln x + 2 ln 3 - 2`. -/
@[kb "stitzzeager2013" "Example 6.2.1, p. 450"]
theorem ex_6_2_1_c (x : ℝ) (hx : 0 < x) :
    Real.log ((3 / (Real.exp 1 * x)) ^ 2) = -2 * Real.log x + 2 * Real.log 3 - 2 := by
  rw [Real.log_pow, Real.log_div (by norm_num) (by positivity), Real.log_mul (by positivity) hx.ne',
    Real.log_exp]
  push_cast
  ring

/-- Stitz-Zeager Example 6.2.1(4): for positive `x, y, z`,
`log ∛(100x²/(yz⁵)) = 2/3 + (2/3) log x - (1/3) log y - (5/3) log z` (common logarithm). -/
@[kb "stitzzeager2013" "Example 6.2.1, p. 450"]
theorem ex_6_2_1_d (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    logb 10 ((100 * x ^ 2 / (y * z ^ 5)) ^ ((1 : ℝ) / 3)) =
      2 / 3 + 2 / 3 * logb 10 x - 1 / 3 * logb 10 y - 5 / 3 * logb 10 z := by
  have h100 : Real.log 100 = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp only [Real.logb]
  rw [Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, h100]
  push_cast
  field_simp
  ring

/-- Stitz-Zeager Example 6.2.1(5): for `x > 2`, `log₁₁₇ (x² - 4) = log₁₁₇ (x+2) + log₁₁₇ (x-2)`. -/
@[kb "stitzzeager2013" "Example 6.2.1, p. 450"]
theorem ex_6_2_1_e (x : ℝ) (hx : 2 < x) :
    logb 117 (x ^ 2 - 4) = logb 117 (x + 2) + logb 117 (x - 2) := by
  rw [← Real.logb_mul (by linarith) (by linarith)]
  congr 1
  ring

/-- Stitz-Zeager Example 6.2.2(1): for `x > 1`, `log₃ (x-1) - log₃ (x+1) = log₃ ((x-1)/(x+1))`. -/
@[kb "stitzzeager2013" "Example 6.2.2, p. 453"]
theorem ex_6_2_2_a (x : ℝ) (hx : 1 < x) :
    logb 3 (x - 1) - logb 3 (x + 1) = logb 3 ((x - 1) / (x + 1)) :=
  (Real.logb_div (by linarith) (by linarith)).symm

/-- Stitz-Zeager Example 6.2.2(2): for positive `x, y, z`, `log x + 2 log y - log z = log (x y²/z)`. -/
@[kb "stitzzeager2013" "Example 6.2.2, p. 453"]
theorem ex_6_2_2_b (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    logb 10 x + 2 * logb 10 y - logb 10 z = logb 10 (x * y ^ 2 / z) := by
  rw [Real.logb_div (by positivity) hz.ne', Real.logb_mul hx.ne' (by positivity), Real.logb_pow]
  push_cast
  ring

/-- Stitz-Zeager Example 6.2.2(3): for `x > 0`, `4 log₂ x + 3 = log₂ (8x⁴)`. -/
@[kb "stitzzeager2013" "Example 6.2.2, p. 453"]
theorem ex_6_2_2_c (x : ℝ) (hx : 0 < x) : 4 * logb 2 x + 3 = logb 2 (8 * x ^ 4) := by
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, ex_6_1_3_b']
  push_cast
  ring

/-- Stitz-Zeager Example 6.2.2(4): for `x > 0`, `-ln x - 1/2 = ln (1/(x √e))`. -/
@[kb "stitzzeager2013" "Example 6.2.2, p. 453"]
theorem ex_6_2_2_d (x : ℝ) (hx : 0 < x) :
    -Real.log x - 1 / 2 = Real.log (1 / (x * √(Real.exp 1))) := by
  have hs : 0 < √(Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
  rw [Real.log_div (by norm_num) (by positivity), Real.log_mul hx.ne' hs.ne',
    Real.log_sqrt (Real.exp_pos 1).le, Real.log_exp]
  simp
  ring

/-- Stitz-Zeager Example 6.2.3(1): `3² = 10^(2 log 3)` (change of base to the common base). -/
@[kb "stitzzeager2013" "Example 6.2.3, p. 455"]
theorem ex_6_2_3_a : (3 : ℝ) ^ 2 = 10 ^ (2 * logb 10 3) := by
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Stitz-Zeager Example 6.2.3(2): `2^x = e^(x ln 2)` for every real `x`. -/
@[kb "stitzzeager2013" "Example 6.2.3, p. 455"]
theorem ex_6_2_3_b (x : ℝ) : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]

/-- Stitz-Zeager Example 6.2.3(3): `log₄ 5 = ln 5 / ln 4`. -/
@[kb "stitzzeager2013" "Example 6.2.3, p. 455"]
theorem ex_6_2_3_c : logb 4 5 = Real.log 5 / Real.log 4 := rfl

/-- Stitz-Zeager Example 6.2.3(4): for `x > 0`, `ln x = log x / log e` (common logarithms). -/
@[kb "stitzzeager2013" "Example 6.2.3, p. 455"]
theorem ex_6_2_3_d (x : ℝ) : Real.log x = logb 10 x / logb 10 (Real.exp 1) := by
  have h10 : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp only [Real.logb, Real.log_exp]
  field_simp

/-! ## Section 6.3 -/

private theorem rpow_inj_aux {b u v : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) : b ^ u = b ^ v ↔ u = v := by
  constructor
  · intro h
    have h1 := congrArg Real.log h
    rw [Real.log_rpow hb, Real.log_rpow hb] at h1
    exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one hb hb1) h1
  · rintro rfl; rfl

private theorem eq_iff_log_aux {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : a = b ↔ Real.log a = Real.log b :=
  ⟨fun h => by rw [h], fun h => Real.log_injOn_pos (mem_Ioi.2 ha) (mem_Ioi.2 hb) h⟩

private theorem exp_eq_iff_aux {u c : ℝ} (hc : 0 < c) : Real.exp u = c ↔ u = Real.log c :=
  ⟨fun h => by rw [← h, Real.log_exp], fun h => by rw [h, Real.exp_log hc]⟩

/-- Stitz-Zeager Example 6.3.1(1): `2^(3x) = 16^(1-x)` holds exactly when `x = 4/7`. -/
@[kb "stitzzeager2013" "Example 6.3.1, p. 460"]
theorem ex_6_3_1_a (x : ℝ) : (2 : ℝ) ^ (3 * x) = 16 ^ (1 - x) ↔ x = 4 / 7 := by
  have h16 : (16 : ℝ) ^ (1 - x) = 2 ^ (4 * (1 - x)) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  rw [h16, rpow_inj_aux (by norm_num) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.3.1(2): `2000 = 1000 · 3^(-t/10)` holds exactly when `t = -10 ln 2 / ln 3`. -/
@[kb "stitzzeager2013" "Example 6.3.1, p. 460"]
theorem ex_6_3_1_b (t : ℝ) :
    2000 = 1000 * (3 : ℝ) ^ (-(1 / 10) * t) ↔ t = -(10 * Real.log 2) / Real.log 3 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have e : 2000 = 1000 * (3 : ℝ) ^ (-(1 / 10) * t) ↔ (3 : ℝ) ^ (-(1 / 10) * t) = 2 := by
    constructor <;> intro h <;> linarith
  rw [e, ← Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
  simp only [Real.logb]
  rw [eq_div_iff h3.ne', div_eq_iff h3.ne']
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.3.1(3): `9 · 3^x = 7^(2x)` holds exactly when `x = 2 ln 3 / (2 ln 7 - ln 3)`. -/
@[kb "stitzzeager2013" "Example 6.3.1, p. 460"]
theorem ex_6_3_1_c (x : ℝ) :
    9 * (3 : ℝ) ^ x = 7 ^ (2 * x) ↔ x = 2 * Real.log 3 / (2 * Real.log 7 - Real.log 3) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h37 : Real.log 3 < Real.log 7 := Real.log_lt_log (by norm_num) (by norm_num)
  have hd : 2 * Real.log 7 - Real.log 3 ≠ 0 := by linarith
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hp1 : 0 < 9 * (3 : ℝ) ^ x := by positivity
  have hp2 : 0 < (7 : ℝ) ^ (2 * x) := by positivity
  rw [eq_iff_log_aux hp1 hp2, Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by norm_num),
    Real.log_rpow (by norm_num), h9, eq_div_iff hd]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Example 6.3.1(4): `75 = 100/(1 + 3e^(-2t))` holds exactly when `t = ln 3`. -/
@[kb "stitzzeager2013" "Example 6.3.1, p. 460"]
theorem ex_6_3_1_d (t : ℝ) : 75 = 100 / (1 + 3 * Real.exp (-2 * t)) ↔ t = Real.log 3 := by
  have hpos := Real.exp_pos (-2 * t)
  have hne : 1 + 3 * Real.exp (-2 * t) ≠ 0 := by positivity
  have hl : Real.log (1 / 9) = -2 * Real.log 3 := by
    rw [one_div, Real.log_inv, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [eq_div_iff hne]
  have e : 75 * (1 + 3 * Real.exp (-2 * t)) = 100 ↔ Real.exp (-2 * t) = 1 / 9 := by
    constructor <;> intro h <;> linarith
  rw [e, exp_eq_iff_aux (by norm_num), hl]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.3.1(5): `25^x = 5^x + 6` holds exactly when `x = ln 3 / ln 5`. -/
@[kb "stitzzeager2013" "Example 6.3.1, p. 460"]
theorem ex_6_3_1_e (x : ℝ) : (25 : ℝ) ^ x = 5 ^ x + 6 ↔ x = Real.log 3 / Real.log 5 := by
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have e25 : (25 : ℝ) ^ x = ((5 : ℝ) ^ x) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), show (25 : ℝ) = 5 ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num), mul_comm]
    norm_num
  have hu : 0 < (5 : ℝ) ^ x := by positivity
  rw [e25]
  have e : ((5 : ℝ) ^ x) ^ 2 = 5 ^ x + 6 ↔ (5 : ℝ) ^ x = 3 := by
    constructor
    · intro h; nlinarith
    · intro h; rw [h]; norm_num
  rw [e, ← Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num), eq_comm]
  exact Iff.rfl

/-- Stitz-Zeager Example 6.3.1(6): `(e^x - e^(-x))/2 = 5` holds exactly when `x = ln (5 + √26)`. -/
@[kb "stitzzeager2013" "Example 6.3.1, p. 460"]
theorem ex_6_3_1_f (x : ℝ) :
    (Real.exp x - Real.exp (-x)) / 2 = 5 ↔ x = Real.log (5 + √26) := by
  have hs : √26 ^ 2 = 26 := Real.sq_sqrt (by norm_num)
  have hs0 : 5 < √26 := by
    rw [show (5 : ℝ) = √25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hu := Real.exp_pos x
  have hinv : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  rw [← exp_eq_iff_aux (by linarith : (0 : ℝ) < 5 + √26), hinv]
  constructor
  · intro h
    have h2 : Real.exp x ^ 2 - 10 * Real.exp x - 1 = 0 := by
      field_simp at h
      nlinarith
    have : (Real.exp x - (5 + √26)) * (Real.exp x - (5 - √26)) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  · intro h
    rw [h]
    field_simp
    nlinarith

/-- Stitz-Zeager Example 6.3.2(1): `2^(x²-3x) - 16 ≥ 0` holds exactly on `(-∞, -1] ∪ [4, ∞)`. -/
@[kb "stitzzeager2013" "Example 6.3.2, p. 463"]
theorem ex_6_3_2_a :
    {x : ℝ | 0 ≤ (2 : ℝ) ^ (x ^ 2 - 3 * x) - 16} = Iic (-1) ∪ Ici 4 := by
  have h16 : (16 : ℝ) = 2 ^ (4 : ℝ) := by norm_num
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici]
  rw [sub_nonneg, h16, Real.rpow_le_rpow_left_iff (by norm_num)]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [hc.1, hc.2]
  · rintro (h | h) <;> nlinarith

/-- Stitz-Zeager Example 6.3.2(2): `e^x/(e^x - 4) ≤ 3` (with `e^x ≠ 4`) holds exactly on
`(-∞, ln 4) ∪ [ln 6, ∞)`. -/
@[kb "stitzzeager2013" "Example 6.3.2, p. 463"]
theorem ex_6_3_2_b :
    {x : ℝ | Real.exp x ≠ 4 ∧ Real.exp x / (Real.exp x - 4) ≤ 3} =
      Iio (Real.log 4) ∪ Ici (Real.log 6) := by
  ext x
  simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ici]
  have hu := Real.exp_pos x
  rw [Real.lt_log_iff_exp_lt (by norm_num), Real.log_le_iff_le_exp (by norm_num)]
  constructor
  · rintro ⟨h4, h⟩
    rcases lt_or_gt_of_ne h4 with hlt | hgt
    · left; exact hlt
    · right
      have hpos : 0 < Real.exp x - 4 := by linarith
      rw [div_le_iff₀ hpos] at h
      linarith
  · rintro (h | h)
    · refine ⟨by linarith, ?_⟩
      have hneg : Real.exp x - 4 < 0 := by linarith
      rw [div_le_iff_of_neg hneg]
      linarith
    · refine ⟨by linarith, ?_⟩
      have hpos : 0 < Real.exp x - 4 := by linarith
      rw [div_le_iff₀ hpos]
      linarith

/-- Stitz-Zeager Example 6.3.2(3): `x e^(2x) < 4x` holds exactly for `0 < x < ln 2`. -/
@[kb "stitzzeager2013" "Example 6.3.2, p. 463"]
theorem ex_6_3_2_c : {x : ℝ | x * Real.exp (2 * x) < 4 * x} = Ioo 0 (Real.log 2) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  ext x
  simp only [mem_setOf_eq, mem_Ioo]
  have hu := Real.exp_pos (2 * x)
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · exfalso
      have : Real.exp (2 * x) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    · subst hx; simp at h
    · refine ⟨hx, ?_⟩
      have h2 : Real.exp (2 * x) < 4 := by nlinarith
      have := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mpr h2
      linarith
  · rintro ⟨hx, hx2⟩
    have : 2 * x < Real.log 4 := by linarith
    have h2 := (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mp this
    nlinarith

/-- Stitz-Zeager Example 6.3.3: the coffee `T(t) = 70 + 90 e^(-t/10)` is warmer than `100` exactly when
`t < 10 ln 3`. -/
@[kb "stitzzeager2013" "Example 6.3.3, p. 466"]
theorem ex_6_3_3 (t : ℝ) : 100 < 70 + 90 * Real.exp (-(1 / 10) * t) ↔ t < 10 * Real.log 3 := by
  have hl : Real.log (1 / 3) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have e : 100 < 70 + 90 * Real.exp (-(1 / 10) * t) ↔ 1 / 3 < Real.exp (-(1 / 10) * t) := by
    constructor <;> intro h <;> linarith
  rw [e, ← Real.log_lt_iff_lt_exp (by norm_num), hl]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 6.3.4: `f(x) = 5e^x/(e^x + 1)` has range `(0, 5)` and inverse `f⁻¹(x) = ln (x/(5-x))`. -/
@[kb "stitzzeager2013" "Example 6.3.4, p. 466"]
theorem ex_6_3_4 :
    InverseOn (fun x : ℝ => 5 * Real.exp x / (Real.exp x + 1)) (fun x : ℝ => Real.log (x / (5 - x)))
      univ (Ioo 0 5) := by
  refine ⟨fun x _ => ⟨?_, ?_⟩, fun y hy => ⟨mem_univ _, ?_⟩⟩
  · have hu := Real.exp_pos x
    simp only [mem_Ioo]
    constructor
    · positivity
    · rw [div_lt_iff₀ (by positivity)]
      linarith
  · have hu := Real.exp_pos x
    have h1 : Real.exp x + 1 ≠ 0 := by positivity
    have h2 : 5 - 5 * Real.exp x / (Real.exp x + 1) = 5 / (Real.exp x + 1) := by
      field_simp
      ring
    simp only
    rw [h2, show 5 * Real.exp x / (Real.exp x + 1) / (5 / (Real.exp x + 1)) = Real.exp x by
      field_simp, Real.log_exp]
  · obtain ⟨hy0, hy5⟩ := hy
    have h1 : 5 - y ≠ 0 := by linarith
    have hq : 0 < y / (5 - y) := div_pos hy0 (by linarith)
    simp only
    rw [Real.exp_log hq]
    have h2 : y / (5 - y) + 1 = 5 / (5 - y) := by
      field_simp
      ring
    rw [h2]
    field_simp

end UndergradKB.Precalculus.Course
