import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.Group
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 6.3 (approximate roots) -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Taylor upper bound (10 terms) for `exp q`, `|q| ≤ 1`. -/
private theorem x6w8b_exp_le (q c : ℝ) (hq : |q| ≤ 1)
    (h : (∑ m ∈ Finset.range 10, q ^ m / (m.factorial : ℝ)) + q ^ 10 * (11 / 36288000) ≤ c) :
    Real.exp q ≤ c := by
  have h1 := (abs_le.1 (Real.exp_bound hq (n := 10) (by norm_num))).2
  have e : |q| ^ 10 = q ^ 10 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, pow_mul, sq_abs]
  have h2 : |q| ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * ((10 : ℕ) : ℝ))) =
      q ^ 10 * (11 / 36288000) := by
    rw [e]; norm_num [Nat.factorial]
  linarith [h1, h2]

/-- Taylor lower bound (10 terms) for `exp q`, `|q| ≤ 1`. -/
private theorem x6w8b_exp_ge (q c : ℝ) (hq : |q| ≤ 1)
    (h : c ≤ (∑ m ∈ Finset.range 10, q ^ m / (m.factorial : ℝ)) - q ^ 10 * (11 / 36288000)) :
    c ≤ Real.exp q := by
  have h1 := (abs_le.1 (Real.exp_bound hq (n := 10) (by norm_num))).1
  have e : |q| ^ 10 = q ^ 10 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, pow_mul, sq_abs]
  have h2 : |q| ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * ((10 : ℕ) : ℝ))) =
      q ^ 10 * (11 / 36288000) := by
    rw [e]; norm_num [Nat.factorial]
  linarith [h1, h2]

private theorem x6w8b_expU (t c : ℝ) (k : ℕ) (hk : 0 < k) (hq : |t / k| ≤ 1)
    (h : ((∑ m ∈ Finset.range 10, (t / k) ^ m / (m.factorial : ℝ)) + (t / k) ^ 10 * (11 / 36288000)) ^ k ≤ c) :
    Real.exp t ≤ c := by
  have h1 := x6w8b_exp_le (t / k) _ hq le_rfl
  have e : Real.exp t = Real.exp (t / k) ^ k := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [e]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le h1 k) h

private theorem x6w8b_expL (t c : ℝ) (k : ℕ) (hk : 0 < k) (hq : |t / k| ≤ 1)
    (hb : 0 ≤ (∑ m ∈ Finset.range 10, (t / k) ^ m / (m.factorial : ℝ)) - (t / k) ^ 10 * (11 / 36288000))
    (h : c ≤ ((∑ m ∈ Finset.range 10, (t / k) ^ m / (m.factorial : ℝ)) - (t / k) ^ 10 * (11 / 36288000)) ^ k) :
    c ≤ Real.exp t := by
  have h1 := x6w8b_exp_ge (t / k) _ hq le_rfl
  have e : Real.exp t = Real.exp (t / k) ^ k := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [e]
  exact le_trans h (pow_le_pow_left₀ hb h1 k)

private theorem x6w8b_e4 : 54.5981 < Real.exp 4 ∧ Real.exp 4 < 54.5982 := by
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have g1 := Real.exp_one_gt_d9
  have g2 := Real.exp_one_lt_d9
  rw [h4]
  constructor
  · calc (54.5981 : ℝ) < 2.7182818283 ^ 4 := by norm_num
      _ < Real.exp 1 ^ 4 := by gcongr
  · calc Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
      _ < 54.5982 := by norm_num

/-- Stitz-Zeager Exercise 6.3.40: `2^x = x²` has the solutions `x = 2`, `x = 4` and one more near `-0.76666`:
there is a solution in `(-0.766665, -0.766655)` (intermediate value theorem; the half unit of the last printed
digit). -/
@[kb "stitzzeager2013" "Exercise 6.3.40, p. 468"]
theorem exer_6_3_40 :
    (∃ x ∈ Ioo (-0.766665 : ℝ) (-0.766655), (2 : ℝ) ^ x = x ^ 2) ∧
    (2 : ℝ) ^ (2 : ℝ) = 2 ^ 2 ∧ (2 : ℝ) ^ (4 : ℝ) = 4 ^ 2 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hf : Continuous (fun x : ℝ => Real.exp (Real.log 2 * x) - x ^ 2) := by fun_prop
  have hfa : Real.exp (Real.log 2 * (-0.766665)) - (-0.766665 : ℝ) ^ 2 < 0 := by
    have h1 : Real.exp (Real.log 2 * (-0.766665)) ≤ Real.exp (0.6931471803 * (-0.766665)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (0.6931471803 * (-0.766665)) ≤ 0.5877749 :=
      x6w8b_expU _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have h3 : (0.5877749 : ℝ) < (-0.766665 : ℝ) ^ 2 := by norm_num
    linarith
  have hfb : 0 < Real.exp (Real.log 2 * (-0.766655)) - (-0.766655 : ℝ) ^ 2 := by
    have h1 : Real.exp (0.6931471808 * (-0.766655)) ≤ Real.exp (Real.log 2 * (-0.766655)) :=
      Real.exp_le_exp.2 (by linarith)
    have h2 : 0.58777 ≤ Real.exp (0.6931471808 * (-0.766655)) :=
      x6w8b_expL _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have h3 : (-0.766655 : ℝ) ^ 2 < 0.58777 := by norm_num
    linarith
  have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.exp (Real.log 2 * x) - x ^ 2) (-0.766665))
      ((fun x : ℝ => Real.exp (Real.log 2 * x) - x ^ 2) (-0.766655)) := ⟨hfa, hfb⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (-0.766665 : ℝ) ≤ -0.766655)
    hf.continuousOn hmem
  refine ⟨x, hx, ?_⟩
  rw [Real.rpow_def_of_pos (by norm_num)]
  exact sub_eq_zero.1 hfx

private theorem x6w8b_expm4 (s : ℝ) : Real.exp (-4 + s) = Real.exp s / Real.exp 4 := by
  rw [Real.exp_add, Real.exp_neg]; ring

private theorem x6w8b_cont (a b : ℝ) (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => Real.exp x - Real.log x - 5) (Icc a b) := by
  have h1 : ContinuousOn Real.log (Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; exact (lt_of_lt_of_le ha hx.1).ne')
  exact (Real.continuous_exp.continuousOn.sub h1).sub continuousOn_const

/-- Stitz-Zeager Exercise 6.3.41: `eˣ = ln x + 5` has two solutions, near `0.01866` and near `1.7115`:
there is a solution in each of `(0.018655, 0.018665)` and `(1.71145, 1.71155)` (intermediate value theorem). -/
@[kb "stitzzeager2013" "Exercise 6.3.41, p. 468"]
theorem exer_6_3_41 :
    (∃ x ∈ Ioo (0.018655 : ℝ) 0.018665, Real.exp x = Real.log x + 5) ∧
    (∃ x ∈ Ioo (1.71145 : ℝ) 1.71155, Real.exp x = Real.log x + 5) := by
  have e4 := x6w8b_e4
  constructor
  · have hta : Real.log 0.018655 < -3.9814 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num), show (-3.9814 : ℝ) = -4 + 0.0186 by norm_num,
        x6w8b_expm4, lt_div_iff₀ (Real.exp_pos 4)]
      have := Real.add_one_le_exp (0.0186 : ℝ)
      linarith [e4.2]
    have htb : -3.98113 < Real.log 0.018665 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num), show (-3.98113 : ℝ) = -4 + 0.01887 by norm_num,
        x6w8b_expm4, div_lt_iff₀ (Real.exp_pos 4)]
      have hU : Real.exp 0.01887 ≤ 1.01905 :=
        x6w8b_expU _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith [e4.1]
    have hga : 0 < Real.exp 0.018655 - Real.log 0.018655 - 5 := by
      have := Real.add_one_le_exp (0.018655 : ℝ)
      linarith
    have hgb : Real.exp 0.018665 - Real.log 0.018665 - 5 < 0 := by
      have hU : Real.exp 0.018665 ≤ 1.01885 :=
        x6w8b_expU _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.exp x - Real.log x - 5) 0.018665)
        ((fun x : ℝ => Real.exp x - Real.log x - 5) 0.018655) := ⟨hgb, hga⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' (by norm_num : (0.018655 : ℝ) ≤ 0.018665)
      (x6w8b_cont _ _ (by norm_num)) hmem
    refine ⟨x, hx, ?_⟩
    have : Real.exp x - Real.log x - 5 = 0 := hfx
    linarith
  · have hV : 0.53715 < Real.log 1.71145 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have : Real.exp 0.53715 ≤ 1.7112 :=
        x6w8b_expU _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have hEa : Real.exp 1.71145 ≤ 5.5371 :=
      x6w8b_expU _ _ 2 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have hW : Real.log 1.71155 < 0.53747 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have : 1.7116 ≤ Real.exp 0.53747 :=
        x6w8b_expL _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have hEb : 5.5375 ≤ Real.exp 1.71155 :=
      x6w8b_expL _ _ 2 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.exp x - Real.log x - 5) 1.71145)
        ((fun x : ℝ => Real.exp x - Real.log x - 5) 1.71155) := ⟨by simp only; linarith, by simp only; linarith⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1.71145 : ℝ) ≤ 1.71155)
      (x6w8b_cont _ _ (by norm_num)) hmem
    refine ⟨x, hx, ?_⟩
    have : Real.exp x - Real.log x - 5 = 0 := hfx
    linarith

/-- Stitz-Zeager Exercise 6.3.45: the boundary points of the solution set of `eˣ < x³ - x` are near `2.3217` and
`4.3717`: `eˣ = x³ - x` has a solution in each of `(2.32165, 2.32175)` and `(4.37165, 4.37175)`; moreover
`x = 3` is a solution of the inequality, while `x = 2` and `x = 5` are not. -/
@[kb "stitzzeager2013" "Exercise 6.3.45, p. 468"]
theorem exer_6_3_45 :
    (∃ r ∈ Ioo (2.32165 : ℝ) 2.32175, Real.exp r = r ^ 3 - r) ∧
    (∃ r ∈ Ioo (4.37165 : ℝ) 4.37175, Real.exp r = r ^ 3 - r) ∧
    ¬ (Real.exp 2 < 2 ^ 3 - 2) ∧ Real.exp 3 < 3 ^ 3 - 3 ∧ ¬ (Real.exp 5 < 5 ^ 3 - 5) := by
  have hc : Continuous (fun x : ℝ => Real.exp x - x ^ 3 + x) := by fun_prop
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : 10.1923 ≤ Real.exp 2.32165 :=
      x6w8b_expL _ _ 3 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have h2 : Real.exp 2.32175 ≤ 10.1936 :=
      x6w8b_expU _ _ 3 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.exp x - x ^ 3 + x) 2.32175)
        ((fun x : ℝ => Real.exp x - x ^ 3 + x) 2.32165) := ⟨by simp only; norm_num; linarith,
          by simp only; norm_num; linarith⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' (by norm_num : (2.32165 : ℝ) ≤ 2.32175)
      hc.continuousOn hmem
    refine ⟨x, hx, ?_⟩
    have : Real.exp x - x ^ 3 + x = 0 := hfx
    linarith
  · have h1 : Real.exp 4.37165 ≤ 79.1752 :=
      x6w8b_expU _ _ 5 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have h2 : 79.18204 ≤ Real.exp 4.37175 :=
      x6w8b_expL _ _ 8 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.exp x - x ^ 3 + x) 4.37165)
        ((fun x : ℝ => Real.exp x - x ^ 3 + x) 4.37175) := ⟨by simp only; norm_num; linarith,
          by simp only; norm_num; linarith⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (4.37165 : ℝ) ≤ 4.37175)
      hc.continuousOn hmem
    refine ⟨x, hx, ?_⟩
    have : Real.exp x - x ^ 3 + x = 0 := hfx
    linarith
  · have h : 7 ≤ Real.exp 2 :=
      x6w8b_expL _ _ 2 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num; linarith
  · have h : Real.exp 3 ≤ 20.1 :=
      x6w8b_expU _ _ 3 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num; linarith
  · have h : 148 ≤ Real.exp 5 :=
      x6w8b_expL _ _ 5 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    norm_num; linarith

end UndergradKB.Precalculus.Course
