import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers, Section 6.5 -/

namespace UndergradKB.Precalculus.Course

open Set Real Filter Topology

/-! ## Helpers -/

private theorem exp_bounds_aux (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)) - |x| ^ n * ((n.succ : ℝ) / (n.factorial * n)) ≤
        exp x ∧
      exp x ≤ (∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)) +
        |x| ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by
  have h := Real.exp_bound hx hn
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

private theorem log_one_add_aux (u : ℝ) (hu : 0 < u) :
    u / (1 + u) ≤ Real.log (1 + u) ∧ Real.log (1 + u) ≤ u := by
  constructor
  · have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + u by linarith)
    have e : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
    linarith
  · have := Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith)
    linarith

private theorem exp_eq_iff_aux {u c : ℝ} (hc : 0 < c) : exp u = c ↔ u = Real.log c :=
  ⟨fun h => by rw [← h, Real.log_exp], fun h => by rw [h, Real.exp_log hc]⟩

private theorem doubling_aux (u c lo hi : ℝ) (hu : 0 < u) (hc : 0 < c) (hhi : 0 < hi)
    (h1 : lo * (c * u) < 0.6931471803) (h2 : 0.6931471808 < hi * (c * (u / (1 + u)))) :
    lo < Real.log 2 / (c * Real.log (1 + u)) ∧ Real.log 2 / (c * Real.log (1 + u)) < hi := by
  obtain ⟨b1, b2⟩ := log_one_add_aux u hu
  have hpos : 0 < Real.log (1 + u) := lt_of_lt_of_le (by positivity) b1
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left b2 hc.le]
  · rw [div_lt_iff₀ (by positivity)]
    have : c * (u / (1 + u)) ≤ c * Real.log (1 + u) := mul_le_mul_of_nonneg_left b1 hc.le
    nlinarith [mul_le_mul_of_nonneg_left this hhi.le]

private theorem doubling_cont_aux (r lo hi : ℝ) (hr : 0 < r) (h1 : lo * r < 0.6931471803)
    (h2 : 0.6931471808 < hi * r) : lo < Real.log 2 / r ∧ Real.log 2 / r < hi := by
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  constructor
  · rw [lt_div_iff₀ hr]; linarith
  · rw [div_lt_iff₀ hr]; linarith

private theorem rpow_nat_aux (b : ℝ) (n : ℕ) (t : ℝ) (h : t = n) : b ^ t = b ^ n := by
  rw [h, Real.rpow_natCast]

/-! ## Section 6.5 -/

/-- Stitz-Zeager Exercise 6.5.1: `500` at `0.75%` compounded monthly, `A(t) = 500 (1 + 0.0075/12)^(12t)`:
`A(5) ≈ 519.10`, `A(10) ≈ 538.93`, and the doubling time (where `A(t) = 1000`) is about `92` years. -/
@[kb "stitzzeager2013" "Exercise 6.5.1, p. 494"]
theorem exer_6_5_1 :
    let A : ℝ → ℝ := fun t => 500 * (1 + 0.0075 / 12) ^ (12 * t)
    (519.095 < A 5 ∧ A 5 < 519.105) ∧ (538.925 < A 10 ∧ A 10 < 538.935) ∧
      (∀ t : ℝ, A t = 1000 ↔ t = Real.log 2 / (12 * Real.log (1 + 0.0075 / 12))) ∧
      (92.4 < Real.log 2 / (12 * Real.log (1 + 0.0075 / 12)) ∧
        Real.log 2 / (12 * Real.log (1 + 0.0075 / 12)) < 92.5) := by
  intro A
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [A]
    rw [rpow_nat_aux _ 60 _ (by norm_num)]
    constructor <;> norm_num
  · simp only [A]
    rw [rpow_nat_aux _ 120 _ (by norm_num)]
    constructor <;> norm_num
  · intro t
    simp only [A]
    have hpos : 0 < Real.log (1 + 0.0075 / 12) := Real.log_pos (by norm_num)
    rw [Real.rpow_def_of_pos (by norm_num)]
    have e : 500 * exp (Real.log (1 + 0.0075 / 12) * (12 * t)) = 1000 ↔
        exp (Real.log (1 + 0.0075 / 12) * (12 * t)) = 2 := by
      constructor <;> intro h <;> linarith
    rw [e, exp_eq_iff_aux (by norm_num), eq_div_iff (by positivity)]
    constructor <;> intro h <;> linarith
  · exact doubling_aux _ 12 92.4 92.5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

/-- Stitz-Zeager Exercise 6.5.2: `500` at `0.75%` compounded continuously, `A(t) = 500 e^(0.0075t)`:
`A(t) = 1000` iff `t = ln 2 / 0.0075`, which lies between `92.4` and `92.5` (about `92` years). -/
@[kb "stitzzeager2013" "Exercise 6.5.2, p. 494"]
theorem exer_6_5_2 :
    let A : ℝ → ℝ := fun t => 500 * exp (0.0075 * t)
    (∀ t : ℝ, A t = 1000 ↔ t = Real.log 2 / 0.0075) ∧
      (92.4 < Real.log 2 / 0.0075 ∧ Real.log 2 / 0.0075 < 92.5) := by
  intro A
  refine ⟨fun t => ?_, doubling_cont_aux _ 92.4 92.5 (by norm_num) (by norm_num) (by norm_num)⟩
  simp only [A]
  have e : 500 * exp (0.0075 * t) = 1000 ↔ exp (0.0075 * t) = 2 := by
    constructor <;> intro h <;> linarith
  rw [e, exp_eq_iff_aux (by norm_num), eq_div_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.5.3: `1000` at `1.25%` compounded monthly, `A(t) = 1000 (1 + 0.0125/12)^(12t)`:
`A(5) ≈ 1064.46`, `A(10) ≈ 1133.07`, and the doubling time is between `55.4` and `55.6` years (about `55`). -/
@[kb "stitzzeager2013" "Exercise 6.5.3, p. 494"]
theorem exer_6_5_3 :
    let A : ℝ → ℝ := fun t => 1000 * (1 + 0.0125 / 12) ^ (12 * t)
    (1064.455 < A 5 ∧ A 5 < 1064.465) ∧ (1133.065 < A 10 ∧ A 10 < 1133.075) ∧
      (55.4 < Real.log 2 / (12 * Real.log (1 + 0.0125 / 12)) ∧
        Real.log 2 / (12 * Real.log (1 + 0.0125 / 12)) < 55.6) := by
  intro A
  refine ⟨?_, ?_, ?_⟩
  · simp only [A]
    rw [rpow_nat_aux _ 60 _ (by norm_num)]
    constructor <;> norm_num
  · simp only [A]
    rw [rpow_nat_aux _ 120 _ (by norm_num)]
    constructor <;> norm_num
  · exact doubling_aux _ 12 55.4 55.6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

/-- Stitz-Zeager Exercise 6.5.5: `5000` at `2.125%` compounded monthly: `A(5) = 5000 (1 + 0.02125/12)^60`
is about `5559.98`. -/
@[kb "stitzzeager2013" "Exercise 6.5.5, p. 494"]
theorem exer_6_5_5 :
    let A : ℝ → ℝ := fun t => 5000 * (1 + 0.02125 / 12) ^ (12 * t)
    5559.975 < A 5 ∧ A 5 < 5559.985 := by
  intro A
  simp only [A]
  rw [rpow_nat_aux _ 60 _ (by norm_num)]
  constructor <;> norm_num

/-- Stitz-Zeager Exercise 6.5.8: the principal needed to reach `2000` in 3 years at `0.25%` compounded
continuously is `2000 / e^(0.0025 · 3)`, about `1985.06`. -/
@[kb "stitzzeager2013" "Exercise 6.5.8, p. 494"]
theorem exer_6_5_8 : 1985.05 < 2000 / exp (0.0025 * 3) ∧ 2000 / exp (0.0025 * 3) < 1985.07 := by
  have h := exp_bounds_aux 0.0075 (by norm_num [abs_of_pos]) 5 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  have hp : 0 < exp (0.0025 * 3) := Real.exp_pos _
  rw [show (0.0025 * 3 : ℝ) = 0.0075 by norm_num] at hp ⊢
  constructor
  · rw [lt_div_iff₀ hp]; linarith [h.2]
  · rw [div_lt_iff₀ hp]; linarith [h.1]

/-- Stitz-Zeager Exercise 6.5.9: the principal needed to reach `5000` in 10 years at `2.25%` compounded
monthly is `5000 / (1 + 0.0225/12)^120`, about `3993.42`. -/
@[kb "stitzzeager2013" "Exercise 6.5.9, p. 494"]
theorem exer_6_5_9 : 3993.415 < 5000 / (1 + (0.0225 : ℝ) / 12) ^ 120 ∧
    5000 / (1 + (0.0225 : ℝ) / 12) ^ 120 < 3993.425 := by
  constructor <;> norm_num

/-- Stitz-Zeager Exercise 6.5.10: at `0.25%` compounded monthly, `A(t) = P (1 + 0.0025/12)^(12t)`;
`A(8)` for `P = 2000` is about `2040.40`; the doubling time is about `277.3` years (shown within
`277.2` and `277.4`); and `P = 2000 / (1 + 0.0025/12)^36 ≈ 1985.06` gives `2000` after three years. -/
@[kb "stitzzeager2013" "Exercise 6.5.10, p. 494"]
theorem exer_6_5_10 :
    (2040.395 < 2000 * (1 + (0.0025 : ℝ) / 12) ^ 96 ∧ 2000 * (1 + (0.0025 : ℝ) / 12) ^ 96 < 2040.405) ∧
    (277.2 < Real.log 2 / (12 * Real.log (1 + 0.0025 / 12)) ∧
      Real.log 2 / (12 * Real.log (1 + 0.0025 / 12)) < 277.4) ∧
    (1985.055 < 2000 / (1 + (0.0025 : ℝ) / 12) ^ 36 ∧ 2000 / (1 + (0.0025 : ℝ) / 12) ^ 36 < 1985.065) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> norm_num
  · exact doubling_aux _ 12 277.2 277.4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · constructor <;> norm_num

/-- Stitz-Zeager Exercise 6.5.11: at `2.25%` compounded monthly, `A(8)` for `P = 2000` is about `2394.03`;
the doubling time is between `30.8` and `30.9` years; the principal giving `2000` after three years is
about `1869.57`; and the annual percentage yield `(1 + 0.0225/12)^12 - 1` is about `2.27%`. -/
@[kb "stitzzeager2013" "Exercise 6.5.11, p. 495"]
theorem exer_6_5_11 :
    (2394.025 < 2000 * (1 + (0.0225 : ℝ) / 12) ^ 96 ∧ 2000 * (1 + (0.0225 : ℝ) / 12) ^ 96 < 2394.035) ∧
    (30.8 < Real.log 2 / (12 * Real.log (1 + 0.0225 / 12)) ∧
      Real.log 2 / (12 * Real.log (1 + 0.0225 / 12)) < 30.9) ∧
    (1869.565 < 2000 / (1 + (0.0225 : ℝ) / 12) ^ 36 ∧ 2000 / (1 + (0.0225 : ℝ) / 12) ^ 36 < 1869.575) ∧
    (1.0227 < (1 + (0.0225 : ℝ) / 12) ^ 12 ∧ (1 + (0.0225 : ℝ) / 12) ^ 12 < 1.0228) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> norm_num
  · exact doubling_aux _ 12 30.8 30.9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · constructor <;> norm_num
  · constructor <;> norm_num

/-- Stitz-Zeager Exercise 6.5.12: `5000` at `29.9%` compounded continuously, `A(t) = 5000 e^(0.299 t)`.
After 3 years the amount is about `12261.18` and after 6 years about `30067.29`.
ERRATUM: the book prints `$12,226.18` for `A(3)`; the correct value is `12,261.18`. -/
@[kb "stitzzeager2013" "Exercise 6.5.12, p. 495"]
theorem exer_6_5_12 :
    let A : ℝ → ℝ := fun t => 5000 * exp (0.299 * t)
    (12261.175 < A 3 ∧ A 3 < 12261.185) ∧ (30067.285 < A 6 ∧ A 6 < 30067.295) := by
  intro A
  simp only [A]
  have h := exp_bounds_aux 0.897 (by norm_num [abs_of_pos]) 14 (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
  have e6 : exp (0.299 * 6) = exp (0.299 * 3) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [show (0.299 * 3 : ℝ) = 0.897 by norm_num] at e6 ⊢
  rw [e6]
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨by linarith, by linarith⟩, ⟨?_, ?_⟩⟩
  · nlinarith [Real.exp_pos 0.897]
  · nlinarith [Real.exp_pos 0.897]

/-- Stitz-Zeager Exercise 6.5.14: Cobalt 60 (half-life `5.27` years, `50` g initially): the decay constant
`k = ln(1/2)/5.27` is about `-0.1315` (shown within `-0.13155` and `-0.13145`), and `50 e^(k · 5.27) = 25`. -/
@[kb "stitzzeager2013" "Exercise 6.5.14, p. 495"]
theorem exer_6_5_14 :
    let k : ℝ := Real.log (1 / 2) / 5.27
    (-0.13155 < k ∧ k < -0.13145) ∧ 50 * exp (k * 5.27) = 25 := by
  intro k
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have hk : k = -Real.log 2 / 5.27 := by simp only [k]; rw [one_div, Real.log_inv]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hk, lt_div_iff₀ (by norm_num)]; linarith
  · rw [hk, div_lt_iff₀ (by norm_num)]; linarith
  · have : k * 5.27 = Real.log (1 / 2) := by simp only [k]; field_simp
    rw [this, Real.exp_log (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.5.19: for decay `A₀ e^(kt)` with `k < 0`, `90%` has decayed exactly when
`t = ln(0.1)/k = -ln 10 / k`, whatever the initial amount `A₀ > 0`. -/
@[kb "stitzzeager2013" "Exercise 6.5.19, p. 496"]
theorem exer_6_5_19 (A₀ k t : ℝ) (hA : 0 < A₀) (hk : k < 0) :
    A₀ * exp (k * t) = A₀ / 10 ↔ t = -Real.log 10 / k := by
  have e : A₀ * exp (k * t) = A₀ / 10 ↔ exp (k * t) = 1 / 10 := by
    constructor
    · intro h; field_simp at h ⊢; nlinarith
    · intro h; rw [h]; ring
  rw [e, exp_eq_iff_aux (by norm_num), one_div, Real.log_inv, eq_div_iff hk.ne]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.5.20: the car value model `25 (4/5)^t` can be written `25 e^(ln(4/5) t)`. -/
@[kb "stitzzeager2013" "Exercise 6.5.20, p. 496"]
theorem exer_6_5_20 (t : ℝ) : 25 * ((4 : ℝ) / 5) ^ t = 25 * exp (Real.log (4 / 5) * t) := by
  rw [Real.rpow_def_of_pos (by norm_num)]

/-- Stitz-Zeager Exercise 6.5.21: the model `G(t) = 9743.77 e^(0.0514 t)` gives `G(0) = 9743.77`,
`G(7) ≈ 13963.24` and `G(10) ≈ 16291.25` (billions of dollars). -/
@[kb "stitzzeager2013" "Exercise 6.5.21, p. 496"]
theorem exer_6_5_21 :
    let G : ℝ → ℝ := fun t => 9743.77 * exp (0.0514 * t)
    G 0 = 9743.77 ∧ (13963.235 < G 7 ∧ G 7 < 13963.245) ∧ (16291.245 < G 10 ∧ G 10 < 16291.255) := by
  intro G
  refine ⟨by simp [G], ?_, ?_⟩
  · simp only [G]
    have h := exp_bounds_aux 0.3598 (by norm_num [abs_of_pos]) 10 (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
    rw [show (0.0514 * 7 : ℝ) = 0.3598 by norm_num]
    constructor <;> linarith [h.1, h.2]
  · simp only [G]
    have h := exp_bounds_aux 0.514 (by norm_num [abs_of_pos]) 10 (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos] at h
    rw [show (0.0514 * 10 : ℝ) = 0.514 by norm_num]
    constructor <;> linarith [h.1, h.2]

/-- Stitz-Zeager Exercise 6.5.22: the tumor diameter `D(t) = 15 e^(0.0277 t)` has `D(0) = 15`, and doubles
(`D(t) = 30`) exactly at `t = ln 2 / 0.0277`, which lies between `25.0` and `25.1` days. -/
@[kb "stitzzeager2013" "Exercise 6.5.22, p. 496"]
theorem exer_6_5_22 :
    let D : ℝ → ℝ := fun t => 15 * exp (0.0277 * t)
    D 0 = 15 ∧ (∀ t : ℝ, D t = 30 ↔ t = Real.log 2 / 0.0277) ∧
      (25.0 < Real.log 2 / 0.0277 ∧ Real.log 2 / 0.0277 < 25.1) := by
  intro D
  refine ⟨by simp [D], fun t => ?_, doubling_cont_aux _ 25.0 25.1 (by norm_num) (by norm_num) (by norm_num)⟩
  simp only [D]
  have e : 15 * exp (0.0277 * t) = 30 ↔ exp (0.0277 * t) = 2 := by
    constructor <;> intro h <;> linarith
  rw [e, exp_eq_iff_aux (by norm_num), eq_div_iff (by norm_num)]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.5.23: the bacteria model with doubling time `20` minutes has
`k = ln 2 / 20`, between `0.03465` and `0.03466`, and `N(t) = 1000 e^(kt)` doubles in `20` minutes.
ERRATUM: the book gives `k ≈ 0.0346` to four decimal places; the correct rounding is `0.0347`. -/
@[kb "stitzzeager2013" "Exercise 6.5.23, p. 496"]
theorem exer_6_5_23 :
    let k : ℝ := Real.log 2 / 20
    (0.03465 < k ∧ k < 0.03466) ∧ 1000 * exp (k * 20) = 2000 := by
  intro k
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [k]; rw [lt_div_iff₀ (by norm_num)]; linarith
  · simp only [k]; rw [div_lt_iff₀ (by norm_num)]; linarith
  · have : k * 20 = Real.log 2 := by simp only [k]; ring
    rw [this, Real.exp_log (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.5.25: wolves, `N(t) = 52 e^(kt)` with `k = (1/3) ln(118/52)`: `N(3) = 118`, and
`N(6) = 118²/52`, which is about `268` (between `267.5` and `268`). -/
@[kb "stitzzeager2013" "Exercise 6.5.25, p. 497"]
theorem exer_6_5_25 :
    let k : ℝ := 1 / 3 * Real.log (118 / 52)
    52 * exp (k * 3) = 118 ∧ 52 * exp (k * 6) = 118 ^ 2 / 52 ∧
      (267.5 < (118 : ℝ) ^ 2 / 52 ∧ (118 : ℝ) ^ 2 / 52 < 268) := by
  intro k
  refine ⟨?_, ?_, by constructor <;> norm_num⟩
  · have : k * 3 = Real.log (118 / 52) := by simp only [k]; ring
    rw [this, Real.exp_log (by norm_num)]; norm_num
  · have : k * 6 = Real.log (118 / 52) + Real.log (118 / 52) := by simp only [k]; ring
    rw [this, Real.exp_add, Real.exp_log (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 6.5.27: `P(t) = 120 / (1 + 3.167 e^(-0.05t))` has `P(0) = 120/4.167` (about `29`),
`P(t) = 60` exactly when `t = 20 ln 3.167`, and `P(t) → 120` as `t → ∞`. -/
@[kb "stitzzeager2013" "Exercise 6.5.27, p. 497"]
theorem exer_6_5_27 :
    let P : ℝ → ℝ := fun t => 120 / (1 + 3.167 * exp (-0.05 * t))
    P 0 = 120 / 4.167 ∧ (28.5 < P 0 ∧ P 0 < 29.5) ∧
      (∀ t : ℝ, P t = 60 ↔ t = 20 * Real.log 3.167) ∧ Tendsto P atTop (𝓝 120) := by
  intro P
  refine ⟨?_, ?_, fun t => ?_, ?_⟩
  · simp only [P]; norm_num
  · simp only [P]; norm_num
  · simp only [P]
    have hp := Real.exp_pos (-0.05 * t)
    rw [div_eq_iff (by positivity)]
    have e : 120 = 60 * (1 + 3.167 * exp (-0.05 * t)) ↔ exp (-0.05 * t) = 1 / 3.167 := by
      constructor <;> intro h <;> linarith
    rw [e, exp_eq_iff_aux (by norm_num), one_div, Real.log_inv]
    constructor <;> intro h <;> linarith
  · have h1 : Tendsto (fun t : ℝ => exp (-(0.05 * t))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by norm_num))
    have h2 : Tendsto (fun t : ℝ => 1 + 3.167 * exp (-0.05 * t)) atTop (𝓝 (1 + 3.167 * 0)) := by
      refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
      simpa [neg_mul] using h1
    have h3 : Tendsto (fun t : ℝ => (120 : ℝ) / (1 + 3.167 * exp (-0.05 * t))) atTop
        (𝓝 (120 / (1 + 3.167 * 0))) := tendsto_const_nhds.div h2 (by norm_num)
    simpa [P] using h3

/-- Stitz-Zeager Exercise 6.5.30: for a radioactive substance with half-life `h > 0`, the amount `N e^(kt)`
is halved at time `h` exactly when `k = -ln 2 / h`. -/
@[kb "stitzzeager2013" "Exercise 6.5.30, p. 498"]
theorem exer_6_5_30 (N h k : ℝ) (hN : 0 < N) (hh : 0 < h) :
    N * exp (k * h) = N / 2 ↔ k = -Real.log 2 / h := by
  have e : N * exp (k * h) = N / 2 ↔ exp (k * h) = 1 / 2 := by
    constructor
    · intro h'; field_simp at h' ⊢; nlinarith
    · intro h'; rw [h']; ring
  rw [e, exp_eq_iff_aux (by norm_num), one_div, Real.log_inv, eq_div_iff hh.ne']

/-- Stitz-Zeager Exercise 6.5.31: Newton's law of cooling for the roast, `T(t) = 75 + 105 e^(kt)` with
`k = ln(95/105)/20`, gives `T(0) = 180`, `T(20) = 170`, and `T(t) = 140` exactly when
`t = 20 ln(65/105) / ln(95/105)`. -/
@[kb "stitzzeager2013" "Exercise 6.5.31, p. 498"]
theorem exer_6_5_31 :
    let k : ℝ := Real.log (95 / 105) / 20
    let T : ℝ → ℝ := fun t => 75 + 105 * exp (k * t)
    T 0 = 180 ∧ T 20 = 170 ∧ ∀ t : ℝ, T t = 140 ↔ t = 20 * Real.log (65 / 105) / Real.log (95 / 105) := by
  intro k T
  have hl : Real.log (95 / 105) < 0 := Real.log_neg (by norm_num) (by norm_num)
  refine ⟨by simp [T]; norm_num, ?_, fun t => ?_⟩
  · simp only [T]
    have : k * 20 = Real.log (95 / 105) := by simp only [k]; ring
    rw [this, Real.exp_log (by norm_num)]; norm_num
  · simp only [T]
    have e : 75 + 105 * exp (k * t) = 140 ↔ exp (k * t) = 65 / 105 := by
      constructor <;> intro h <;> linarith
    rw [e, exp_eq_iff_aux (by norm_num)]
    simp only [k]
    rw [eq_div_iff hl.ne]
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Exercise 6.5.33: the current `i(t) = 2 - 2 e^(-10t)` tends to the steady state `2` amps. -/
@[kb "stitzzeager2013" "Exercise 6.5.33, p. 498"]
theorem exer_6_5_33 : Tendsto (fun t : ℝ => 2 - 2 * exp (-10 * t)) atTop (𝓝 2) := by
  have h1 : Tendsto (fun t : ℝ => exp (-(10 * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by norm_num))
  have h2 := (tendsto_const_nhds (x := (2 : ℝ))).sub (h1.const_mul 2)
  simpa [neg_mul] using h2

/-- Stitz-Zeager Exercise 6.5.35: the Gateway Arch curve `y = 757.7 - (127.7/2)(e^(x/127.7) + e^(-x/127.7))`
has its highest point at `x = 0`, where `y = 630`. -/
@[kb "stitzzeager2013" "Exercise 6.5.35, p. 499"]
theorem exer_6_5_35 :
    let y : ℝ → ℝ := fun x => 757.7 - 127.7 / 2 * (exp (x / 127.7) + exp (-x / 127.7))
    y 0 = 630 ∧ ∀ x : ℝ, y x ≤ 630 := by
  intro y
  refine ⟨by simp [y]; norm_num, fun x => ?_⟩
  simp only [y]
  have e : exp (x / 127.7) * exp (-x / 127.7) = 1 := by
    rw [← Real.exp_add, show x / 127.7 + -x / 127.7 = 0 by ring, Real.exp_zero]
  have h1 := Real.exp_pos (x / 127.7)
  have h2 := Real.exp_pos (-x / 127.7)
  have : 2 ≤ exp (x / 127.7) + exp (-x / 127.7) := by
    by_contra hc
    push Not at hc
    nlinarith [sq_nonneg (exp (x / 127.7) - exp (-x / 127.7))]
  linarith

end UndergradKB.Precalculus.Course
