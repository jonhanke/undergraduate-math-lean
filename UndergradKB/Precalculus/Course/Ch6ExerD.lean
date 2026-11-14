import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers, Section 6.4 -/

namespace UndergradKB.Precalculus.Course

open Set Real

/-! ## Helpers -/

private theorem logb_eq_aux {b a c : ℝ} (hb : 1 < b) (ha : 0 < a) : logb b a = c ↔ b ^ c = a :=
  Real.logb_eq_iff_rpow_eq (by linarith) (by linarith) ha

private theorem logb_inj_aux {b a c : ℝ} (hb : 1 < b) (ha : 0 < a) (hc : 0 < c) :
    logb b a = logb b c ↔ a = c := by
  constructor
  · intro h
    rw [← Real.rpow_logb (b := b) (by linarith) (by linarith) ha, h,
      Real.rpow_logb (by linarith) (by linarith) hc]
  · intro h; rw [h]

private theorem log_inj_aux {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : Real.log a = Real.log c ↔ a = c :=
  ⟨fun h => Real.log_injOn_pos (mem_Ioi.2 ha) (mem_Ioi.2 hc) h, fun h => by rw [h]⟩

private theorem exp_eq_aux {u c : ℝ} (hc : 0 < c) : exp u = c ↔ u = Real.log c :=
  ⟨fun h => by rw [← h, Real.log_exp], fun h => by rw [h, Real.exp_log hc]⟩

private theorem rpow_mul_zpow_aux {a : ℝ} (ha : 0 < a) (u : ℝ) (n : ℤ) :
    a ^ u * a ^ n = a ^ (u + n) := by
  rw [← Real.rpow_intCast, ← Real.rpow_add ha]

private theorem rpow_two_aux (a : ℝ) : a ^ (2 : ℝ) = a ^ 2 := Real.rpow_two a

/-! ## Section 6.4 -/

/-- Stitz-Zeager Exercises 6.4.1 - 6.4.4: `log(3x-1) = log(4-x)` iff `x = 5/4`; `log₂ x³ = log₂ x` iff
`x = 1`; `ln(8-x²) = ln(2-x)` iff `x = -2`; `log₅(18-x²) = log₅(6-x)` iff `x = -3` or `x = 4`
(the arguments of each logarithm must be positive). -/
@[kb "stitzzeager2013" "Exercise 6.4.1, p. 478"]
theorem exer_6_4_1_to_4 :
    (∀ x : ℝ, (0 < 3 * x - 1 ∧ 0 < 4 - x ∧ logb 10 (3 * x - 1) = logb 10 (4 - x)) ↔ x = 5 / 4) ∧
    (∀ x : ℝ, (0 < x ^ 3 ∧ 0 < x ∧ logb 2 (x ^ 3) = logb 2 x) ↔ x = 1) ∧
    (∀ x : ℝ, (0 < 8 - x ^ 2 ∧ 0 < 2 - x ∧ Real.log (8 - x ^ 2) = Real.log (2 - x)) ↔ x = -2) ∧
    (∀ x : ℝ, (0 < 18 - x ^ 2 ∧ 0 < 6 - x ∧ logb 5 (18 - x ^ 2) = logb 5 (6 - x)) ↔
      (x = -3 ∨ x = 4)) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · constructor
    · rintro ⟨h1, h2, h⟩
      rw [logb_inj_aux (by norm_num) h1 h2] at h
      linarith
    · intro h; subst h; norm_num
  · constructor
    · rintro ⟨h1, h2, h⟩
      rw [logb_inj_aux (by norm_num) h1 h2] at h
      have : (x - 1) * (x * (x + 1)) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exfalso; nlinarith
    · intro h; subst h; norm_num
  · constructor
    · rintro ⟨h1, h2, h⟩
      rw [log_inj_aux h1 h2] at h
      have : (x - 3) * (x + 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exfalso; linarith
      · linarith
    · intro h; subst h; norm_num
  · constructor
    · rintro ⟨h1, h2, h⟩
      rw [logb_inj_aux (by norm_num) h1 h2] at h
      have : (x - 4) * (x + 3) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (h | h) <;> subst h <;> norm_num

/-- Stitz-Zeager Exercises 6.4.5 - 6.4.8: `log₃(7-2x) = 2` iff `x = -1`; `log_{1/2}(2x-1) = -3` iff
`x = 9/2`; `ln(x²-99) = 0` iff `x = ±10`; `log(x²-3x) = 1` iff `x = -2` or `x = 5` (with the
argument of the logarithm positive). -/
@[kb "stitzzeager2013" "Exercise 6.4.5, p. 478"]
theorem exer_6_4_5_to_8 :
    (∀ x : ℝ, (0 < 7 - 2 * x ∧ logb 3 (7 - 2 * x) = 2) ↔ x = -1) ∧
    (∀ x : ℝ, (0 < 2 * x - 1 ∧ logb (1 / 2) (2 * x - 1) = -3) ↔ x = 9 / 2) ∧
    (∀ x : ℝ, (0 < x ^ 2 - 99 ∧ Real.log (x ^ 2 - 99) = 0) ↔ (x = 10 ∨ x = -10)) ∧
    (∀ x : ℝ, (0 < x ^ 2 - 3 * x ∧ logb 10 (x ^ 2 - 3 * x) = 1) ↔ (x = -2 ∨ x = 5)) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · constructor
    · rintro ⟨h1, h⟩
      rw [logb_eq_aux (by norm_num) h1, rpow_two_aux] at h
      linarith
    · intro h; subst h
      refine ⟨by norm_num, ?_⟩
      rw [logb_eq_aux (by norm_num) (by norm_num), rpow_two_aux]; norm_num
  · have e : (1 / 2 : ℝ) ^ (-3 : ℝ) = 8 := by
      rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    constructor
    · rintro ⟨h1, h⟩
      rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) h1, e] at h
      linarith
    · intro h; subst h
      refine ⟨by norm_num, ?_⟩
      rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num), e]; norm_num
  · constructor
    · rintro ⟨h1, h⟩
      rw [Real.log_eq_zero] at h
      rcases h with h | h | h
      · linarith
      · have : (x - 10) * (x + 10) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      · linarith
    · rintro (h | h) <;> subst h <;> norm_num
  · constructor
    · rintro ⟨h1, h⟩
      rw [logb_eq_aux (by norm_num) h1, Real.rpow_one] at h
      have : (x - 5) * (x + 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (h | h) <;> subst h
      · refine ⟨by norm_num, ?_⟩
        rw [logb_eq_aux (by norm_num) (by norm_num), Real.rpow_one]; norm_num
      · refine ⟨by norm_num, ?_⟩
        rw [logb_eq_aux (by norm_num) (by norm_num), Real.rpow_one]; norm_num

/-- Stitz-Zeager Exercises 6.4.9, 6.4.13, 6.4.14: `log₁₂₅((3x-2)/(2x+3)) = 1/3` iff `x = -17/7`;
`6 - 3 log₅(2x) = 0` iff `x = 25/2`; `3 ln x - 2 = 1 - ln x` iff `x = e^(3/4)`
(arguments of the logarithms positive). -/
@[kb "stitzzeager2013" "Exercise 6.4.9, p. 478"]
theorem exer_6_4_9_13_14 :
    (∀ x : ℝ, (0 < (3 * x - 2) / (2 * x + 3) ∧ logb 125 ((3 * x - 2) / (2 * x + 3)) = 1 / 3) ↔
      x = -17 / 7) ∧
    (∀ x : ℝ, (0 < 2 * x ∧ 6 - 3 * logb 5 (2 * x) = 0) ↔ x = 25 / 2) ∧
    (∀ x : ℝ, (0 < x ∧ 3 * Real.log x - 2 = 1 - Real.log x) ↔ x = exp (3 / 4)) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have e : (125 : ℝ) ^ (1 / 3 : ℝ) = 5 := by
      rw [show (125 : ℝ) = 5 ^ 3 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    constructor
    · rintro ⟨h1, h⟩
      rw [logb_eq_aux (by norm_num) h1, e] at h
      have hd : 2 * x + 3 ≠ 0 := by
        intro h0; rw [h0, div_zero] at h; norm_num at h
      rw [eq_div_iff hd] at h
      linarith
    · intro h; subst h
      have : (3 * (-17 / 7 : ℝ) - 2) / (2 * (-17 / 7) + 3) = 5 := by norm_num
      rw [this]
      refine ⟨by norm_num, ?_⟩
      rw [logb_eq_aux (by norm_num) (by norm_num), e]
  · constructor
    · rintro ⟨h1, h⟩
      have h' : logb 5 (2 * x) = 2 := by linarith
      rw [logb_eq_aux (by norm_num) h1, rpow_two_aux] at h'
      linarith
    · intro h; subst h
      refine ⟨by norm_num, ?_⟩
      have : logb 5 (2 * (25 / 2 : ℝ)) = 2 := by
        rw [logb_eq_aux (by norm_num) (by norm_num), rpow_two_aux]; norm_num
      rw [this]; norm_num
  · constructor
    · rintro ⟨h1, h⟩
      have h' : Real.log x = 3 / 4 := by linarith
      rw [← h', Real.exp_log h1]
    · intro h; subst h
      refine ⟨Real.exp_pos _, ?_⟩
      rw [Real.log_exp]; norm_num

/-- Stitz-Zeager Exercises 6.4.10, 6.4.11, 6.4.12: `log(x / 10⁻³) = 4.7` iff `x = 10^1.7`;
`-log x = 5.4` iff `x = 10^(-5.4)`; `10 log(x / 10⁻¹²) = 150` iff `x = 10³` (positive `x`). -/
@[kb "stitzzeager2013" "Exercise 6.4.10, p. 478"]
theorem exer_6_4_10_11_12 :
    (∀ x : ℝ, 0 < x → (logb 10 (x / 10 ^ (-3 : ℤ)) = 4.7 ↔ x = (10 : ℝ) ^ (1.7 : ℝ))) ∧
    (∀ x : ℝ, 0 < x → (-logb 10 x = 5.4 ↔ x = (10 : ℝ) ^ (-5.4 : ℝ))) ∧
    (∀ x : ℝ, 0 < x → (10 * logb 10 (x / 10 ^ (-12 : ℤ)) = 150 ↔ x = 1000)) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [logb_eq_aux (by norm_num) (by positivity), eq_div_iff (by positivity),
      rpow_mul_zpow_aux (by norm_num)]
    constructor <;> intro h
    · rw [← h]; norm_num
    · rw [h]; norm_num
  · have e : -logb 10 x = 5.4 ↔ logb 10 x = -5.4 := by constructor <;> intro h <;> linarith
    rw [e, logb_eq_aux (by norm_num) hx]
    exact eq_comm
  · have e : 10 * logb 10 (x / 10 ^ (-12 : ℤ)) = 150 ↔ logb 10 (x / 10 ^ (-12 : ℤ)) = 15 := by
      constructor <;> intro h <;> linarith
    rw [e, logb_eq_aux (by norm_num) (by positivity), eq_div_iff (by positivity)]
    have h15 : (10 : ℝ) ^ (15 : ℝ) * 10 ^ (-12 : ℤ) = 1000 := by
      rw [rpow_mul_zpow_aux (by norm_num)]
      rw [show (15 : ℝ) + ((-12 : ℤ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h15]
    exact eq_comm

/-- Stitz-Zeager Exercises 6.4.15, 6.4.16, 6.4.17: `log₃(x-4) + log₃(x+4) = 2` iff `x = 5`;
`log₅(2x+1) + log₅(x+2) = 1` iff `x = 1/2`; `log₁₆₉(3x+7) - log₁₆₉(5x-9) = 1/2` iff `x = 2`
(each logarithm's argument positive). -/
@[kb "stitzzeager2013" "Exercise 6.4.15, p. 478"]
theorem exer_6_4_15_16_17 :
    (∀ x : ℝ, (0 < x - 4 ∧ 0 < x + 4 ∧ logb 3 (x - 4) + logb 3 (x + 4) = 2) ↔ x = 5) ∧
    (∀ x : ℝ, (0 < 2 * x + 1 ∧ 0 < x + 2 ∧ logb 5 (2 * x + 1) + logb 5 (x + 2) = 1) ↔ x = 1 / 2) ∧
    (∀ x : ℝ, (0 < 3 * x + 7 ∧ 0 < 5 * x - 9 ∧ logb 169 (3 * x + 7) - logb 169 (5 * x - 9) = 1 / 2) ↔
      x = 2) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · constructor
    · rintro ⟨h1, h2, h⟩
      rw [← Real.logb_mul h1.ne' h2.ne', logb_eq_aux (by norm_num) (by positivity), rpow_two_aux] at h
      nlinarith
    · intro h; subst h
      refine ⟨by norm_num, by norm_num, ?_⟩
      rw [← Real.logb_mul (by norm_num) (by norm_num), logb_eq_aux (by norm_num) (by norm_num),
        rpow_two_aux]
      norm_num
  · constructor
    · rintro ⟨h1, h2, h⟩
      rw [← Real.logb_mul h1.ne' h2.ne', logb_eq_aux (by norm_num) (by positivity), Real.rpow_one] at h
      have : (2 * x - 1) * (x + 3) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exfalso; linarith
    · intro h; subst h
      refine ⟨by norm_num, by norm_num, ?_⟩
      rw [← Real.logb_mul (by norm_num) (by norm_num), logb_eq_aux (by norm_num) (by norm_num),
        Real.rpow_one]
      norm_num
  · have e : (169 : ℝ) ^ (1 / 2 : ℝ) = 13 := by
      rw [← Real.sqrt_eq_rpow, show (169 : ℝ) = 13 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    constructor
    · rintro ⟨h1, h2, h⟩
      rw [← Real.logb_div h1.ne' h2.ne', logb_eq_aux (by norm_num) (by positivity), e] at h
      rw [eq_div_iff h2.ne'] at h
      linarith
    · intro h; subst h
      refine ⟨by norm_num, by norm_num, ?_⟩
      rw [← Real.logb_div (by norm_num) (by norm_num), logb_eq_aux (by norm_num) (by norm_num), e]
      norm_num

/-- Stitz-Zeager Exercises 6.4.18, 6.4.19, 6.4.20: for `x > 0`, `ln(x+1) - ln x = 3` iff
`x = 1/(e³-1)`; `2 log₇ x = log₇ 2 + log₇(x+12)` iff `x = 6`; `log x - log 2 = log(x+8) - log(x+2)`
iff `x = 4`. -/
@[kb "stitzzeager2013" "Exercise 6.4.18, p. 478"]
theorem exer_6_4_18_19_20 :
    (∀ x : ℝ, 0 < x → (Real.log (x + 1) - Real.log x = 3 ↔ x = 1 / (exp 3 - 1))) ∧
    (∀ x : ℝ, 0 < x → (2 * logb 7 x = logb 7 2 + logb 7 (x + 12) ↔ x = 6)) ∧
    (∀ x : ℝ, 0 < x → (logb 10 x - logb 10 2 = logb 10 (x + 8) - logb 10 (x + 2) ↔ x = 4)) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h3 : 1 < exp 3 := by
      have := Real.add_one_lt_exp (by norm_num : (3 : ℝ) ≠ 0); linarith
    have e : Real.log ((x + 1) / x) = 3 ↔ exp 3 = (x + 1) / x := by
      rw [exp_eq_aux (by positivity)]; exact eq_comm
    rw [← Real.log_div (by linarith) hx.ne', e, eq_div_iff hx.ne']
    have hne : exp 3 - 1 ≠ 0 := by linarith
    constructor
    · intro h; rw [eq_div_iff hne]; linarith
    · intro h; rw [h]; field_simp; ring
  · have e2 : 2 * logb 7 x = logb 7 (x ^ 2) := by rw [Real.logb_pow]; push_cast; ring
    rw [e2, ← Real.logb_mul (by norm_num) (by positivity), logb_inj_aux (by norm_num) (by positivity)
      (by positivity)]
    constructor
    · intro h
      have : (x - 6) * (x + 4) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exfalso; linarith
    · intro h; subst h; norm_num
  · rw [← Real.logb_div hx.ne' (by norm_num), ← Real.logb_div (by positivity) (by positivity),
      logb_inj_aux (by norm_num) (by positivity) (by positivity)]
    have hx2 : x + 2 ≠ 0 := by positivity
    constructor
    · intro h
      rw [div_eq_div_iff (by norm_num) hx2] at h
      have : (x - 4) * (x + 4) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exfalso; linarith
    · intro h; subst h; norm_num

/-- Stitz-Zeager Exercises 6.4.21, 6.4.22, 6.4.23, 6.4.24: `log₃ x = log_{1/3} x + 8` iff `x = 81`;
`ln(ln x) = 3` iff `x = e^(e³)`; `(log x)² = 2 log x + 15` iff `x = 10⁻³` or `x = 10⁵`;
`ln(x²) = (ln x)²` iff `x = 1` or `x = e²` (with `x > 0`, and `ln x > 0` for the iterated logarithm). -/
@[kb "stitzzeager2013" "Exercise 6.4.21, p. 478"]
theorem exer_6_4_21_to_24 :
    (∀ x : ℝ, 0 < x → (logb 3 x = logb (1 / 3) x + 8 ↔ x = 81)) ∧
    (∀ x : ℝ, (0 < x ∧ 0 < Real.log x ∧ Real.log (Real.log x) = 3) ↔ x = exp (exp 3)) ∧
    (∀ x : ℝ, 0 < x → ((logb 10 x) ^ 2 = 2 * logb 10 x + 15 ↔ x = 1 / 1000 ∨ x = 100000)) ∧
    (∀ x : ℝ, 0 < x → (Real.log (x ^ 2) = (Real.log x) ^ 2 ↔ x = 1 ∨ x = exp 2)) := by
  refine ⟨fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have e : logb (1 / 3) x = -logb 3 x := by
      rw [Real.logb, Real.logb, one_div, Real.log_inv, div_neg]
    rw [e]
    have e4 : logb 3 x = -logb 3 x + 8 ↔ logb 3 x = 4 := by
      constructor <;> intro h <;> linarith
    rw [e4, logb_eq_aux (by norm_num) hx]
    have : (3 : ℝ) ^ (4 : ℝ) = 81 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [this]; exact eq_comm
  · constructor
    · rintro ⟨h1, h2, h3⟩
      have : Real.log x = exp 3 := by
        have := Real.exp_log h2
        rw [h3] at this
        exact this.symm
      rw [← this, Real.exp_log h1]
    · intro h; subst h
      have hl : Real.log (exp (exp 3)) = exp 3 := Real.log_exp _
      refine ⟨Real.exp_pos _, ?_, ?_⟩
      · rw [hl]; exact Real.exp_pos _
      · rw [hl, Real.log_exp]
  · have e5 : (10 : ℝ) ^ (5 : ℝ) = 100000 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have e3 : (10 : ℝ) ^ (-3 : ℝ) = 1 / 1000 := by
      rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
    constructor
    · intro h
      have : (logb 10 x - 5) * (logb 10 x + 3) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · right
        have : logb 10 x = 5 := by linarith
        rw [logb_eq_aux (by norm_num) hx, e5] at this
        exact this.symm
      · left
        have : logb 10 x = -3 := by linarith
        rw [logb_eq_aux (by norm_num) hx, e3] at this
        exact this.symm
    · rintro (h | h)
      · have : logb 10 x = -3 := by rw [logb_eq_aux (by norm_num) hx, e3, h]
        rw [this]; norm_num
      · have : logb 10 x = 5 := by rw [logb_eq_aux (by norm_num) hx, e5, h]
        rw [this]; norm_num
  · rw [Real.log_pow]
    push_cast
    constructor
    · intro h
      have : Real.log x * (Real.log x - 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h0 | h0
      · left
        rw [← Real.exp_log hx, h0, Real.exp_zero]
      · right
        rw [← Real.exp_log hx, show Real.log x = 2 by linarith]
    · rintro (h | h)
      · subst h; simp
      · subst h; rw [Real.log_exp]; ring

/-- Stitz-Zeager Exercises 6.4.25, 6.4.26, 6.4.30, 6.4.35: solution sets (with `x > 0` for logarithms):
`(1 - ln x)/x² < 0` is `(e, ∞)`; `x ln x - x > 0` is `(e, ∞)`; `ln(x²) ≤ (ln x)²` is `(0, 1] ∪ [e², ∞)`;
`ln(2x+1) < 3` is `(-1/2, (e³-1)/2)`. -/
@[kb "stitzzeager2013" "Exercise 6.4.25, p. 478"]
theorem exer_6_4_25_26_30_35 :
    {x : ℝ | 0 < x ∧ (1 - Real.log x) / x ^ 2 < 0} = Ioi (exp 1) ∧
    {x : ℝ | 0 < x ∧ 0 < x * Real.log x - x} = Ioi (exp 1) ∧
    {x : ℝ | 0 < x ∧ Real.log (x ^ 2) ≤ (Real.log x) ^ 2} = Ioc 0 1 ∪ Ici (exp 2) ∧
    {x : ℝ | 0 < 2 * x + 1 ∧ Real.log (2 * x + 1) < 3} = Ioo (-1 / 2) ((exp 3 - 1) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨hx, h⟩
      rw [div_neg_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; have : 0 < x ^ 2 := by positivity
        linarith
      · exact (Real.lt_log_iff_exp_lt hx).1 (by linarith)
    · intro h
      have hx : 0 < x := lt_trans (Real.exp_pos 1) h
      refine ⟨hx, ?_⟩
      have := (Real.lt_log_iff_exp_lt hx).2 h
      exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  · ext x
    simp only [mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨hx, h⟩
      have : 0 < x * (Real.log x - 1) := by linarith
      have h1 : 0 < Real.log x - 1 := (pos_iff_pos_of_mul_pos this).1 hx
      exact (Real.lt_log_iff_exp_lt hx).1 (by linarith)
    · intro h
      have hx : 0 < x := lt_trans (Real.exp_pos 1) h
      refine ⟨hx, ?_⟩
      have := (Real.lt_log_iff_exp_lt hx).2 h
      nlinarith
  · ext x
    simp only [mem_ofPred_eq, mem_union, mem_Ioc, mem_Ici]
    rw [Real.log_pow]
    push_cast
    constructor
    · rintro ⟨hx, h⟩
      have : 0 ≤ Real.log x * (Real.log x - 2) := by nlinarith
      rcases le_or_gt (Real.log x) 0 with h1 | h1
      · exact Or.inl ⟨hx, (Real.log_nonpos_iff hx.le).1 h1⟩
      · right
        have : 2 ≤ Real.log x := by
          by_contra hc
          push Not at hc
          nlinarith
        exact (Real.le_log_iff_exp_le hx).1 this
    · rintro (⟨hx, h⟩ | h)
      · refine ⟨hx, ?_⟩
        have := (Real.log_nonpos_iff hx.le).2 h
        nlinarith
      · have hx : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) h
        refine ⟨hx, ?_⟩
        have := (Real.le_log_iff_exp_le hx).2 h
        nlinarith
  · ext x
    simp only [mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      rw [Real.log_lt_iff_lt_exp h1] at h2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      refine ⟨by linarith, ?_⟩
      rw [Real.log_lt_iff_lt_exp (by linarith)]
      linarith

/-- Stitz-Zeager Exercises 6.4.27, 6.4.29: with `x > 0`, `10 log(x / 10⁻¹²) ≥ 90` has solution set
`[10⁻³, ∞)`, and `2.3 < -log x < 5.4` has solution set `(10^(-5.4), 10^(-2.3))`. -/
@[kb "stitzzeager2013" "Exercise 6.4.27, p. 478"]
theorem exer_6_4_27_29 :
    {x : ℝ | 0 < x ∧ 90 ≤ 10 * logb 10 (x / 10 ^ (-12 : ℤ))} = Ici (1 / 1000) ∧
    {x : ℝ | 0 < x ∧ 2.3 < -logb 10 x ∧ -logb 10 x < 5.4} =
      Ioo ((10 : ℝ) ^ (-5.4 : ℝ)) ((10 : ℝ) ^ (-2.3 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Ici]
    have e9 : (10 : ℝ) ^ (9 : ℝ) = 10 ^ 9 := by
      rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    constructor
    · rintro ⟨hx, h⟩
      have h' : (9 : ℝ) ≤ logb 10 (x / 10 ^ (-12 : ℤ)) := by linarith
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), e9, le_div_iff₀ (by positivity)] at h'
      norm_num at h'
      linarith
    · intro h
      have hx : 0 < x := lt_of_lt_of_le (by norm_num) h
      refine ⟨hx, ?_⟩
      have : (9 : ℝ) ≤ logb 10 (x / 10 ^ (-12 : ℤ)) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), e9, le_div_iff₀ (by positivity)]
        norm_num
        linarith
      linarith
  · ext x
    simp only [mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨hx, h1, h2⟩
      have a : logb 10 x < -2.3 := by linarith
      have b : -5.4 < logb 10 x := by linarith
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) hx] at a
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) hx] at b
      exact ⟨b, a⟩
    · rintro ⟨h1, h2⟩
      have hx : 0 < x := lt_trans (Real.rpow_pos_of_pos (by norm_num) _) h1
      refine ⟨hx, ?_, ?_⟩
      · have : logb 10 x < -2.3 := (Real.logb_lt_iff_lt_rpow (by norm_num) hx).2 h2
        linarith
      · have : -5.4 < logb 10 x := (Real.lt_logb_iff_rpow_lt (by norm_num) hx).2 h1
        linarith

/-- Stitz-Zeager Exercise 6.4.28: with `x > 0`, `5.6 ≤ log(x / 10⁻³) ≤ 7.1` has solution set
`[10^2.6, 10^4.1]`. -/
@[kb "stitzzeager2013" "Exercise 6.4.28, p. 478"]
theorem exer_6_4_28 :
    {x : ℝ | 0 < x ∧ 5.6 ≤ logb 10 (x / 10 ^ (-3 : ℤ)) ∧ logb 10 (x / 10 ^ (-3 : ℤ)) ≤ 7.1} =
      Icc ((10 : ℝ) ^ (2.6 : ℝ)) ((10 : ℝ) ^ (4.1 : ℝ)) := by
  ext x
  simp only [mem_ofPred_eq, mem_Icc]
  have hz : (0 : ℝ) < 10 ^ (-3 : ℤ) := by positivity
  have k1 : (10 : ℝ) ^ (5.6 : ℝ) * 10 ^ (-3 : ℤ) = 10 ^ (2.6 : ℝ) := by
    rw [rpow_mul_zpow_aux (by norm_num)]; norm_num
  have k2 : (10 : ℝ) ^ (7.1 : ℝ) * 10 ^ (-3 : ℤ) = 10 ^ (4.1 : ℝ) := by
    rw [rpow_mul_zpow_aux (by norm_num)]; norm_num
  constructor
  · rintro ⟨hx, h1, h2⟩
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), le_div_iff₀ hz, k1] at h1
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), div_le_iff₀ hz, k2] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hx : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) h1
    refine ⟨hx, ?_, ?_⟩
    · rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), le_div_iff₀ hz, k1]; exact h1
    · rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), div_le_iff₀ hz, k2]; exact h2

/-- Stitz-Zeager Exercise 6.4.36: for `0 < y < 3`, `ln(3-y) - ln y = 2x + ln 5` iff `y = 3/(5 e^(2x) + 1)`. -/
@[kb "stitzzeager2013" "Exercise 6.4.36, p. 479"]
theorem exer_6_4_36 (x y : ℝ) (hy : 0 < y) (hy3 : y < 3) :
    Real.log (3 - y) - Real.log y = 2 * x + Real.log 5 ↔ y = 3 / (5 * exp (2 * x) + 1) := by
  have hp := Real.exp_pos (2 * x)
  have e : Real.log (3 - y) - Real.log y = 2 * x + Real.log 5 ↔ (3 - y) / y = exp (2 * x) * 5 := by
    rw [← Real.log_div (by linarith) hy.ne', show 2 * x + Real.log 5 = Real.log (exp (2 * x) * 5) by
      rw [Real.log_mul hp.ne' (by norm_num), Real.log_exp]]
    exact log_inj_aux (by apply div_pos <;> linarith) (by positivity)
  rw [e, div_eq_iff hy.ne', eq_div_iff (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 6.4.38: the inverse of `f(x) = ½ ln((1+x)/(1-x))` (defined on `(-1, 1)`) is
`g(x) = (e^(2x) - 1)/(e^(2x) + 1)`, defined on all of `ℝ`: both compositions are the identity. -/
@[kb "stitzzeager2013" "Exercise 6.4.38, p. 479"]
theorem exer_6_4_38 :
    let f : ℝ → ℝ := fun x => 1 / 2 * Real.log ((1 + x) / (1 - x))
    let g : ℝ → ℝ := fun x => (exp (2 * x) - 1) / (exp (2 * x) + 1)
    (∀ x : ℝ, f (g x) = x) ∧ ∀ y : ℝ, -1 < y → y < 1 → g (f y) = y := by
  intro f g
  refine ⟨fun x => ?_, fun y h1 h2 => ?_⟩
  · have hp := Real.exp_pos (2 * x)
    have e : (1 + g x) / (1 - g x) = exp (2 * x) := by
      simp only [g]
      field_simp
      ring
    simp only [f]
    rw [e, Real.log_exp]; ring
  · have hy1 : 0 < 1 + y := by linarith
    have hy2 : 0 < 1 - y := by linarith
    have e : exp (2 * f y) = (1 + y) / (1 - y) := by
      simp only [f]
      rw [show 2 * (1 / 2 * Real.log ((1 + y) / (1 - y))) = Real.log ((1 + y) / (1 - y)) by ring,
        Real.exp_log (by positivity)]
    simp only [g]
    rw [e]
    field_simp
    ring

end UndergradKB.Precalculus.Course
