import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 6.5 -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology

/-- Two-sided numerical bounds for `exp x` on `[0, 1]` (twelve Taylor terms). -/
private theorem x6w7i_expb {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (∑ m ∈ Finset.range 12, x ^ m / (m.factorial : ℝ)) - 3e-9 ≤ Real.exp x ∧
    Real.exp x ≤ (∑ m ∈ Finset.range 12, x ^ m / (m.factorial : ℝ)) + 3e-9 := by
  have hx1 : |x| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  have h := Real.exp_bound (x := x) hx1 (n := 12) (by norm_num)
  have hx : |x| ^ 12 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
  have hc : (((12 : ℕ).succ : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) ≤ 3e-9 := by
    norm_num [Nat.factorial]
  have h2 : |x| ^ 12 * (((12 : ℕ).succ : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) ≤ 3e-9 := by
    calc _ ≤ 1 * (((12 : ℕ).succ : ℝ) / (((12 : ℕ).factorial : ℝ) * 12)) :=
          mul_le_mul_of_nonneg_right hx (by positivity)
      _ ≤ 3e-9 := by linarith
  obtain ⟨a, b⟩ := abs_le.1 h
  constructor <;> linarith

private theorem x6w7i_exp_eq {y c : ℝ} (hc : 0 < c) : Real.exp y = c ↔ y = Real.log c := by
  constructor
  · intro h; rw [← h, Real.log_exp]
  · intro h; rw [h, Real.exp_log hc]

/-- Stitz-Zeager Exercise 6.5.6: `$5000` at `2.125%` compounded continuously, `A(t) = 5000 e^(0.02125t)`:
`A(5) ≈ 5560.50`, `A(10) ≈ 6183.83`, `A(30) ≈ 9458.73`, `A(35) ≈ 10519.05` (each within a cent), doubling time
`ln 2/0.02125 ≈ 33` years, average rates of change `≈ 116.91` (years 4 to 5) and `≈ 221.17` (years 34 to 35). -/
@[kb "stitzzeager2013" "Exercise 6.5.6, p. 494"]
theorem exer_6_5_6 (A : ℝ → ℝ) (hA : A = fun t => 5000 * Real.exp (0.02125 * t)) :
    |A 5 - 5560.50| < 0.01 ∧ |A 10 - 6183.83| < 0.01 ∧ |A 30 - 9458.73| < 0.01 ∧
    |A 35 - 10519.05| < 0.01 ∧ (∀ t, A t = 10000 ↔ t = Real.log 2 / 0.02125) ∧
    32.5 < Real.log 2 / 0.02125 ∧ Real.log 2 / 0.02125 < 33.5 ∧
    |A 5 - A 4 - 116.91| < 0.02 ∧ |A 35 - A 34 - 221.17| < 0.02 := by
  subst hA
  have e1 := x6w7i_expb (x := 0.085) (by norm_num) (by norm_num)
  have e2 := x6w7i_expb (x := 0.10625) (by norm_num) (by norm_num)
  have e3 := x6w7i_expb (x := 0.2125) (by norm_num) (by norm_num)
  have e4 := x6w7i_expb (x := 0.6375) (by norm_num) (by norm_num)
  have e5 := x6w7i_expb (x := 0.7225) (by norm_num) (by norm_num)
  have e6 := x6w7i_expb (x := 0.74375) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at e1 e2 e3 e4 e5 e6
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e2.1, e2.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e3.1, e3.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e4.1, e4.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e6.1, e6.2]
  · intro t
    have hp : 0 < Real.exp (0.02125 * t) := Real.exp_pos _
    simp only
    have key : 5000 * Real.exp (0.02125 * t) = 10000 ↔ Real.exp (0.02125 * t) = 2 := by
      constructor <;> intro h <;> linarith
    rw [key, x6w7i_exp_eq (by norm_num), eq_div_iff (by norm_num)]
    constructor <;> intro h <;> linarith
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  · simp only; norm_num; rw [abs_lt]; constructor <;> linarith [e5.1, e5.2, e6.1, e6.2]

/-- Stitz-Zeager Exercise 6.5.13: with `A(t) = P (1 + r/n)^(nt)`, the doubling time `t = ln 2/(n ln(1 + r/n))` does
not depend on the principal `P > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.5.13, p. 495"]
theorem exer_6_5_13 (P r n : ℝ) (hP : 0 < P) (hr : 0 < r) (hn : 0 < n) :
    ∀ t : ℝ, P * (1 + r / n) ^ (n * t) = 2 * P ↔ t = Real.log 2 / (n * Real.log (1 + r / n)) := by
  intro t
  have h1 : 1 < 1 + r / n := by have := div_pos hr hn; linarith
  have hL : 0 < Real.log (1 + r / n) := Real.log_pos h1
  have key : P * (1 + r / n) ^ (n * t) = 2 * P ↔ (1 + r / n) ^ (n * t) = 2 := by
    constructor <;> intro h <;> nlinarith
  have hp : 0 < (1 + r / n) ^ (n * t) := Real.rpow_pos_of_pos (by linarith) _
  rw [key, eq_div_iff (by positivity)]
  constructor
  · intro h
    have := congrArg Real.log h
    rw [Real.log_rpow (by linarith)] at this
    linarith
  · intro h
    calc (1 + r / n) ^ (n * t) = Real.exp (Real.log (1 + r / n) * (n * t)) :=
          Real.rpow_def_of_pos (by linarith) _
      _ = Real.exp (Real.log 2) := by rw [← h]; ring_nf
      _ = 2 := Real.exp_log (by norm_num)

/-- Half-life data: for `A(t) = A₀ e^(kt)` with `k = ln(1/2)/h`, `A(h) = A₀/2`, and `A(t) = A₀/10` (90% decayed)
exactly for `t = ln(0.1)/k`. -/
private theorem x6w7i_half (A₀ h : ℝ) (hh : 0 < h) :
    A₀ * Real.exp (Real.log (1 / 2) / h * h) = A₀ / 2 ∧
    (0 < A₀ → ∀ t : ℝ, A₀ * Real.exp (Real.log (1 / 2) / h * t) = A₀ * 0.1 ↔
      t = Real.log 0.1 / (Real.log (1 / 2) / h)) := by
  have hk : Real.log (1 / 2) / h < 0 := by
    apply div_neg_of_neg_of_pos _ hh
    exact Real.log_neg (by norm_num) (by norm_num)
  refine ⟨?_, fun hA t => ?_⟩
  · rw [div_mul_cancel₀ _ hh.ne', Real.exp_log (by norm_num)]; ring
  · have key : A₀ * Real.exp (Real.log (1 / 2) / h * t) = A₀ * 0.1 ↔
        Real.exp (Real.log (1 / 2) / h * t) = 0.1 := by
      constructor
      · intro hh'; exact mul_left_cancel₀ hA.ne' hh'
      · intro hh'; rw [hh']
    rw [key, x6w7i_exp_eq (by norm_num), eq_div_iff hk.ne]
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.5.15: Phosphorus 32 (half-life 14 days, `A₀ = 2`): `k = ln(1/2)/14 ≈ -0.0495`
(it lies in `(-0.04955, -0.04945)`), `A(14) = 1`, and 90% has decayed exactly at `t = ln(0.1)/k`. -/
@[kb "stitzzeager2013" "Exercise 6.5.15, p. 495"]
theorem exer_6_5_15 (A : ℝ → ℝ) (hA : A = fun t => 2 * Real.exp (Real.log (1 / 2) / 14 * t)) :
    (-0.04955 < Real.log (1 / 2) / 14 ∧ Real.log (1 / 2) / 14 < -0.04945) ∧ A 14 = 1 ∧
    ∀ t, A t = 2 * 0.1 ↔ t = Real.log 0.1 / (Real.log (1 / 2) / 14) := by
  subst hA
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have h := x6w7i_half 2 14 (by norm_num)
  refine ⟨?_, ?_, fun t => (h.2 (by norm_num) t)⟩
  · rw [one_div, Real.log_inv]; constructor <;> linarith
  · have := h.1; simp only; linarith

/-- Stitz-Zeager Exercise 6.5.16: Chromium 51 (half-life 27.7 days, `A₀ = 75`): `k = ln(1/2)/27.7 ≈ -0.0250`
(in `(-0.02505, -0.02495)`), `A(27.7) = 37.5`, and 90% has decayed exactly at `t = ln(0.1)/k`. -/
@[kb "stitzzeager2013" "Exercise 6.5.16, p. 495"]
theorem exer_6_5_16 (A : ℝ → ℝ) (hA : A = fun t => 75 * Real.exp (Real.log (1 / 2) / 27.7 * t)) :
    (-0.02505 < Real.log (1 / 2) / 27.7 ∧ Real.log (1 / 2) / 27.7 < -0.02495) ∧ A 27.7 = 75 / 2 ∧
    ∀ t, A t = 75 * 0.1 ↔ t = Real.log 0.1 / (Real.log (1 / 2) / 27.7) := by
  subst hA
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have h := x6w7i_half 75 27.7 (by norm_num)
  have hk : Real.log (1 / 2) / 27.7 = -Real.log 2 / 27.7 := by rw [one_div, Real.log_inv]
  refine ⟨?_, ?_, fun t => (h.2 (by norm_num) t)⟩
  · rw [hk]; constructor
    · rw [lt_div_iff₀ (by norm_num)]; linarith
    · rw [div_lt_iff₀ (by norm_num)]; linarith
  · have := h.1; simp only; linarith

/-- Stitz-Zeager Exercise 6.5.17: Americium 241 (half-life 432.7 years, `A₀ = 0.29`): `k = ln(1/2)/432.7 ≈ -0.0016`
(in `(-0.00165, -0.00155)`), `A(432.7) = 0.145`, and 90% has decayed exactly at `t = ln(0.1)/k`. -/
@[kb "stitzzeager2013" "Exercise 6.5.17, p. 495"]
theorem exer_6_5_17 (A : ℝ → ℝ) (hA : A = fun t => 0.29 * Real.exp (Real.log (1 / 2) / 432.7 * t)) :
    (-0.00165 < Real.log (1 / 2) / 432.7 ∧ Real.log (1 / 2) / 432.7 < -0.00155) ∧ A 432.7 = 0.29 / 2 ∧
    ∀ t, A t = 0.29 * 0.1 ↔ t = Real.log 0.1 / (Real.log (1 / 2) / 432.7) := by
  subst hA
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have h := x6w7i_half 0.29 432.7 (by norm_num)
  have hk : Real.log (1 / 2) / 432.7 = -Real.log 2 / 432.7 := by rw [one_div, Real.log_inv]
  refine ⟨?_, ?_, fun t => (h.2 (by norm_num) t)⟩
  · rw [hk]; constructor
    · rw [lt_div_iff₀ (by norm_num)]; linarith
    · rw [div_lt_iff₀ (by norm_num)]; linarith
  · have := h.1; simp only; linarith

/-- Stitz-Zeager Exercise 6.5.18: Uranium 235 (half-life 704 million years, `A₀ = 1`): `k = ln(1/2)/704 ≈ -0.0010`
(in `(-0.00105, -0.00095)`), `A(704) = 1/2`, and 90% has decayed exactly at `t = ln(0.1)/k`. -/
@[kb "stitzzeager2013" "Exercise 6.5.18, p. 495"]
theorem exer_6_5_18 (A : ℝ → ℝ) (hA : A = fun t => 1 * Real.exp (Real.log (1 / 2) / 704 * t)) :
    (-0.00105 < Real.log (1 / 2) / 704 ∧ Real.log (1 / 2) / 704 < -0.00095) ∧ A 704 = 1 / 2 ∧
    ∀ t, A t = 1 * 0.1 ↔ t = Real.log 0.1 / (Real.log (1 / 2) / 704) := by
  subst hA
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have h := x6w7i_half 1 704 (by norm_num)
  refine ⟨?_, ?_, fun t => (h.2 (by norm_num) t)⟩
  · rw [one_div, Real.log_inv]; constructor <;> linarith
  · have := h.1; simp only; linarith

/-- Stitz-Zeager Exercise 6.5.24: yeast with `N₀ = 2.5` million per cc growing to `6` after two hours:
`k = (1/2) ln(6/2.5) ≈ 0.4377` (it lies in `(0.43765, 0.43775)`), `N(2) = 6`, and the doubling time `ln 2/k`
lies in `(1.575, 1.585)` hours. -/
@[kb "stitzzeager2013" "Exercise 6.5.24, p. 496"]
theorem exer_6_5_24 (N : ℝ → ℝ) (k : ℝ) (hk : k = 1 / 2 * Real.log (6 / 2.5))
    (hN : N = fun t => 2.5 * Real.exp (k * t)) :
    (0.43765 < k ∧ k < 0.43775) ∧ N 2 = 6 ∧ (∀ t, N t = 5 ↔ t = Real.log 2 / k) ∧
    1.575 < Real.log 2 / k ∧ Real.log 2 / k < 1.585 := by
  have lo : 0.8753 < Real.log (6 / 2.5) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := x6w7i_expb (x := 0.8753) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢
    linarith [this.2]
  have hi : Real.log (6 / 2.5) < 0.8755 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := x6w7i_expb (x := 0.8755) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢
    linarith [this.1]
  have hkb : 0.43765 < k ∧ k < 0.43775 := by rw [hk]; constructor <;> linarith
  have hkp : 0 < k := by linarith [hkb.1]
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  subst hN
  refine ⟨hkb, ?_, fun t => ?_, ?_, ?_⟩
  · simp only
    rw [hk, show 1 / 2 * Real.log (6 / 2.5) * 2 = Real.log (6 / 2.5) by ring, Real.exp_log (by norm_num)]
    norm_num
  · simp only
    have key : 2.5 * Real.exp (k * t) = 5 ↔ Real.exp (k * t) = 2 := by
      constructor <;> intro h <;> linarith
    rw [key, x6w7i_exp_eq (by norm_num), eq_div_iff hkp.ne']
    constructor <;> intro h <;> linarith
  · rw [lt_div_iff₀ hkp]; nlinarith [hkb.1, hkb.2]
  · rw [div_lt_iff₀ hkp]; nlinarith [hkb.1, hkb.2]

/-- Stitz-Zeager Exercise 6.5.26: Painesville, `N₀ = 2649` in 1860 and `7272` in 1920: `k = (1/60) ln(7272/2649)`
lies in `(0.01675, 0.01685)` (about `0.0168`), and the model `N(t) = 2649 e^(0.0168 t)` with the rounded `k` gives
`N(150) ≈ 32923` (within `5`) for 2010. -/
@[kb "stitzzeager2013" "Exercise 6.5.26, p. 497"]
theorem exer_6_5_26 :
    (0.01675 < 1 / 60 * Real.log (7272 / 2649) ∧ 1 / 60 * Real.log (7272 / 2649) < 0.01685) ∧
    |2649 * Real.exp (0.0168 * 150) - 32923| < 5 := by
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  constructor
  · have hlo : 1.005 < Real.log (7272 / 2649) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num), show (1.005 : ℝ) = 1 + 0.005 by norm_num, Real.exp_add]
      have := x6w7i_expb (x := 0.005) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      nlinarith [Real.exp_pos 0.005]
    have hhi : Real.log (7272 / 2649) < 1.011 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num), show (1.011 : ℝ) = 1 + 0.011 by norm_num, Real.exp_add]
      have := x6w7i_expb (x := 0.011) (by norm_num) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      nlinarith [Real.exp_pos 0.011]
    constructor <;> linarith
  · have e := x6w7i_expb (x := 0.63) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at e
    have h4 : Real.exp (0.0168 * 150) = Real.exp 0.63 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    have hp := Real.exp_pos 0.63
    have a1 : (1.877610 : ℝ) ^ 4 ≤ Real.exp 0.63 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith [e.1]) 4
    have a2 : Real.exp 0.63 ^ 4 ≤ (1.877612 : ℝ) ^ 4 := pow_le_pow_left₀ hp.le (by linarith [e.2]) 4
    rw [abs_lt]; norm_num at a1 a2; constructor <;> linarith

/-- Stitz-Zeager Exercise 6.5.28: Carbon-14 (half-life 5730 years): `A(t) = N e^(-(ln 2/5730) t)`; after 20000
years the fraction left lies in `(0.0888, 0.0891)` (about `8.9%`); and `A(t) = 0.42 N` exactly at
`t = -5730 ln(0.42)/ln 2`. -/
@[kb "stitzzeager2013" "Exercise 6.5.28, p. 497"]
theorem exer_6_5_28 (N : ℝ) (hN : 0 < N) (A : ℝ → ℝ)
    (hA : A = fun t => N * Real.exp (-(Real.log 2 / 5730) * t)) :
    (0.0888 < A 20000 / N ∧ A 20000 / N < 0.0891) ∧
    ∀ t, A t = 0.42 * N ↔ t = -5730 * Real.log 0.42 / Real.log 2 := by
  subst hA
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, fun t => ?_⟩
  · simp only
    rw [mul_div_cancel_left₀ _ hN.ne']
    set y := Real.log 2 / 5730 * 20000 with hy
    have hy1 : 0.80645 * 3 < y := by rw [hy]; linarith
    have hy2 : y < 0.80646 * 3 := by rw [hy]; linarith
    have hexp : Real.exp (-(Real.log 2 / 5730) * 20000) = (Real.exp (y / 3) ^ 3)⁻¹ := by
      rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * (y / 3) = y by push_cast; ring, ← Real.exp_neg]
      congr 1; rw [hy]; ring
    rw [hexp]
    have b1 := x6w7i_expb (x := 0.80645) (by norm_num) (by norm_num)
    have b2 := x6w7i_expb (x := 0.80646) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at b1 b2
    have m1 : Real.exp 0.80645 ≤ Real.exp (y / 3) := Real.exp_le_exp.2 (by linarith)
    have m2 : Real.exp (y / 3) ≤ Real.exp 0.80646 := Real.exp_le_exp.2 (by linarith)
    have c1 : (2.2399 : ℝ) ^ 3 ≤ Real.exp (y / 3) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [b1.1]) 3
    have c2 : Real.exp (y / 3) ^ 3 ≤ (2.2401 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith [b2.2]) 3
    norm_num at c1 c2
    have hp : 0 < Real.exp (y / 3) ^ 3 := by positivity
    constructor
    · rw [lt_inv_comm₀ (by norm_num) hp]; linarith
    · rw [inv_lt_comm₀ hp (by norm_num)]; linarith
  · simp only
    have hp := Real.exp_pos (-(Real.log 2 / 5730) * t)
    have key : N * Real.exp (-(Real.log 2 / 5730) * t) = 0.42 * N ↔
        Real.exp (-(Real.log 2 / 5730) * t) = 0.42 := by
      constructor
      · intro h; nlinarith
      · intro h; rw [h]; ring
    rw [key, x6w7i_exp_eq (by norm_num), eq_div_iff hL.ne']
    constructor <;> intro h <;> nlinarith

/-- Stitz-Zeager Exercise 6.5.29: Rubidium-87 (half-life 50 billion years, initial `2.3` micrograms): the decay
constant `k = -ln(2)/50` equals `-0.0138629` to within `10⁻⁷`, and `A(50) = 1.15`. -/
@[kb "stitzzeager2013" "Exercise 6.5.29, p. 498"]
theorem exer_6_5_29 (A : ℝ → ℝ) (hA : A = fun t => 2.3 * Real.exp (-(Real.log 2 / 50) * t)) :
    |-(Real.log 2 / 50) - (-0.0138629)| < 1e-7 ∧ A 50 = 1.15 := by
  subst hA
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  refine ⟨?_, ?_⟩
  · rw [abs_lt]; constructor <;> linarith
  · simp only
    rw [show -(Real.log 2 / 50) * 50 = -Real.log 2 by ring, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num

/-- Stitz-Zeager Exercise 6.5.32: Fritzy's pursuit curve `y(x) = x²/4 - ln(x)/4 - 1/4` tends to `∞` as `x → 0⁺`
(he never catches Chewbacca). -/
@[kb "stitzzeager2013" "Exercise 6.5.32, p. 498"]
theorem exer_6_5_32 :
    Tendsto (fun x : ℝ => 1 / 4 * x ^ 2 - 1 / 4 * Real.log x - 1 / 4) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun x : ℝ => -(1 / 4) * Real.log x) (𝓝[>] 0) atTop :=
    Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (by norm_num)
  have h2 : Tendsto (fun x : ℝ => 1 / 4 * x ^ 2 - 1 / 4) (𝓝[>] 0) (𝓝 (1 / 4 * 0 ^ 2 - 1 / 4)) := by
    have : Continuous (fun x : ℝ => 1 / 4 * x ^ 2 - 1 / 4) := by fun_prop
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h3 := h1.atTop_add h2
  exact Filter.Tendsto.congr (fun x => by ring) h3

/-- Stitz-Zeager Exercise 6.5.37 (b): the logistic model `P(t) = 18691/(1 + 9.8505 e^(-0.03617t))` stays below its
limit `18691` (so the printed value `18717` for `P(150)` is impossible), `17500 < P(150) < 18100` (about `17914`),
and `P(t) → 18691` as `t → ∞`. -/
@[kb "stitzzeager2013" "Exercise 6.5.37, p. 499"]
theorem exer_6_5_37 (P : ℝ → ℝ) (hP : P = fun t => 18691 / (1 + 9.8505 * Real.exp (-0.03617 * t))) :
    (∀ t, P t < 18691) ∧ 17500 < P 150 ∧ P 150 < 18100 ∧ Tendsto P atTop (𝓝 18691) := by
  subst hP
  have e1 := Real.exp_one_gt_d9
  have e2 := Real.exp_one_lt_d9
  have h5 : Real.exp (-0.03617 * 150) = (Real.exp 1 ^ 5 * Real.exp (851 / 2000))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]; congr 1; norm_num
  have b := x6w7i_expb (x := 851 / 2000) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at b
  have n1 : (148 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
  have p1 : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) e1.le 5
  have p2 : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) e2.le 5
  have hE1 : (1 : ℝ) ≤ Real.exp (851 / 2000) := Real.one_le_exp (by norm_num)
  have hE2 : Real.exp (851 / 2000) ≤ 1.5305 := by linarith [b.2]
  have hX1 : (148 : ℝ) ≤ Real.exp 1 ^ 5 * Real.exp (851 / 2000) := by
    nlinarith [pow_pos (Real.exp_pos 1) 5]
  have n2 : (2.7182818286 : ℝ) ^ 5 * 1.5305 ≤ 260 := by norm_num
  have hX2 : Real.exp 1 ^ 5 * Real.exp (851 / 2000) ≤ 260 := by
    calc _ ≤ (2.7182818286 : ℝ) ^ 5 * 1.5305 := mul_le_mul p2 hE2 (Real.exp_pos _).le (by positivity)
      _ ≤ 260 := n2
  set X := Real.exp 1 ^ 5 * Real.exp (851 / 2000) with hXdef
  have hXp : 0 < X := by linarith
  have i1 : X⁻¹ ≤ (148 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hX1
  have i2 : (260 : ℝ)⁻¹ ≤ X⁻¹ := inv_anti₀ hXp hX2
  have hp : 0 < 1 + 9.8505 * X⁻¹ := by have := inv_pos.2 hXp; linarith
  refine ⟨fun t => ?_, ?_, ?_, ?_⟩
  · simp only
    have := Real.exp_pos (-0.03617 * t)
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  · simp only
    rw [h5]
    rw [lt_div_iff₀ hp]
    norm_num at i1
    nlinarith
  · simp only
    rw [h5]
    rw [div_lt_iff₀ hp]
    norm_num at i2
    nlinarith
  · have hexp : Tendsto (fun t : ℝ => Real.exp (-0.03617 * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_id.const_mul_atTop_of_neg (by norm_num))
    have := (tendsto_const_nhds (x := (18691 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hexp.const_mul 9.8505)) (by norm_num)
    have h3 : Tendsto ((fun _ : ℝ => (18691 : ℝ)) / fun t : ℝ => 1 + 9.8505 * Real.exp (-0.03617 * t))
        atTop (𝓝 18691) := by simpa using this
    exact h3

end UndergradKB.Precalculus.Course
