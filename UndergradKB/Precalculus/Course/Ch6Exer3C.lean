import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.Group
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 6 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 6.4 (approximate roots) -/

namespace UndergradKB.Precalculus.Course

open Set

/-- Taylor upper bound (10 terms) for `exp q`, `|q| ≤ 1`. -/
private theorem x6w8c_exp_le (q c : ℝ) (hq : |q| ≤ 1)
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
private theorem x6w8c_exp_ge (q c : ℝ) (hq : |q| ≤ 1)
    (h : c ≤ (∑ m ∈ Finset.range 10, q ^ m / (m.factorial : ℝ)) - q ^ 10 * (11 / 36288000)) :
    c ≤ Real.exp q := by
  have h1 := (abs_le.1 (Real.exp_bound hq (n := 10) (by norm_num))).1
  have e : |q| ^ 10 = q ^ 10 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul, pow_mul, sq_abs]
  have h2 : |q| ^ 10 * (((10 : ℕ).succ : ℝ) / (((10 : ℕ).factorial : ℝ) * ((10 : ℕ) : ℝ))) =
      q ^ 10 * (11 / 36288000) := by
    rw [e]; norm_num [Nat.factorial]
  linarith [h1, h2]

private theorem x6w8c_expU (t c : ℝ) (k : ℕ) (hk : 0 < k) (hq : |t / k| ≤ 1)
    (h : ((∑ m ∈ Finset.range 10, (t / k) ^ m / (m.factorial : ℝ)) + (t / k) ^ 10 * (11 / 36288000)) ^ k ≤ c) :
    Real.exp t ≤ c := by
  have h1 := x6w8c_exp_le (t / k) _ hq le_rfl
  have e : Real.exp t = Real.exp (t / k) ^ k := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [e]
  exact le_trans (pow_le_pow_left₀ (Real.exp_pos _).le h1 k) h

private theorem x6w8c_expL (t c : ℝ) (k : ℕ) (hk : 0 < k) (hq : |t / k| ≤ 1)
    (hb : 0 ≤ (∑ m ∈ Finset.range 10, (t / k) ^ m / (m.factorial : ℝ)) - (t / k) ^ 10 * (11 / 36288000))
    (h : c ≤ ((∑ m ∈ Finset.range 10, (t / k) ^ m / (m.factorial : ℝ)) - (t / k) ^ 10 * (11 / 36288000)) ^ k) :
    c ≤ Real.exp t := by
  have h1 := x6w8c_exp_ge (t / k) _ hq le_rfl
  have e : Real.exp t = Real.exp (t / k) ^ k := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [e]
  exact le_trans h (pow_le_pow_left₀ hb h1 k)

/-- `exp (8 + s) ≤ c` from the Taylor upper bound for `exp s` and `exp 1 < 2.7182818286`. -/
private theorem x6w8c_exp8_le (s c : ℝ) (hs : |s| ≤ 1)
    (h : (2.7182818286 : ℝ) ^ 8 * ((∑ m ∈ Finset.range 10, s ^ m / (m.factorial : ℝ)) + s ^ 10 * (11 / 36288000)) ≤ c) :
    Real.exp (8 + s) ≤ c := by
  have e : Real.exp (8 + s) = Real.exp 1 ^ 8 * Real.exp s := by
    rw [Real.exp_add, ← Real.exp_nat_mul]; norm_num
  have h1 := x6w8c_exp_le s _ hs le_rfl
  have h2 : Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 8
  rw [e]
  have hU : 0 ≤ (∑ m ∈ Finset.range 10, s ^ m / (m.factorial : ℝ)) + s ^ 10 * (11 / 36288000) :=
    le_trans (Real.exp_pos s).le h1
  calc Real.exp 1 ^ 8 * Real.exp s
      ≤ (2.7182818286 : ℝ) ^ 8 * ((∑ m ∈ Finset.range 10, s ^ m / (m.factorial : ℝ)) + s ^ 10 * (11 / 36288000)) :=
        mul_le_mul h2 h1 (Real.exp_pos s).le (by positivity)
    _ ≤ c := h

private theorem x6w8c_exp8_ge (s c : ℝ) (hs : |s| ≤ 1)
    (hU : 0 ≤ (∑ m ∈ Finset.range 10, s ^ m / (m.factorial : ℝ)) - s ^ 10 * (11 / 36288000))
    (h : c ≤ (2.7182818283 : ℝ) ^ 8 * ((∑ m ∈ Finset.range 10, s ^ m / (m.factorial : ℝ)) - s ^ 10 * (11 / 36288000))) :
    c ≤ Real.exp (8 + s) := by
  have e : Real.exp (8 + s) = Real.exp 1 ^ 8 * Real.exp s := by
    rw [Real.exp_add, ← Real.exp_nat_mul]; norm_num
  have h1 := x6w8c_exp_ge s _ hs le_rfl
  have h2 : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 8
  rw [e]
  calc c ≤ (2.7182818283 : ℝ) ^ 8 * ((∑ m ∈ Finset.range 10, s ^ m / (m.factorial : ℝ)) - s ^ 10 * (11 / 36288000)) := h
    _ ≤ Real.exp 1 ^ 8 * Real.exp s :=
        mul_le_mul h2 h1 hU (by positivity)

private theorem x6w8c_r4 (a : ℝ) (ha : 0 < a) : 0 < a ^ (1 / 4 : ℝ) ∧ (a ^ (1 / 4 : ℝ)) ^ 4 = a := by
  refine ⟨Real.rpow_pos_of_pos ha _, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num

private theorem x6w8c_le_r (a r0 : ℝ) (ha : 0 < a) (hr0 : 0 ≤ r0) (h : r0 ^ 4 ≤ a) : r0 ≤ a ^ (1 / 4 : ℝ) := by
  by_contra hlt
  push_neg at hlt
  have h1 := pow_lt_pow_left₀ hlt (x6w8c_r4 a ha).1.le (by norm_num : (4 : ℕ) ≠ 0)
  rw [(x6w8c_r4 a ha).2] at h1
  linarith

private theorem x6w8c_r_le (a r1 : ℝ) (ha : 0 < a) (hr1 : 0 ≤ r1) (h : a ≤ r1 ^ 4) : a ^ (1 / 4 : ℝ) ≤ r1 := by
  by_contra hlt
  push_neg at hlt
  have h1 := pow_lt_pow_left₀ hlt hr1 (by norm_num : (4 : ℕ) ≠ 0)
  rw [(x6w8c_r4 a ha).2] at h1
  linarith

private theorem x6w8c_cont (a b : ℝ) (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => Real.log x - x ^ (1 / 4 : ℝ)) (Icc a b) := by
  have h1 : ContinuousOn Real.log (Icc a b) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; exact (lt_of_lt_of_le ha hx.1).ne')
  exact h1.sub (continuousOn_id.rpow_const (fun x _ => Or.inr (by norm_num)))

/-- Stitz-Zeager Exercise 6.4.31: `ln x = e⁻ˣ` has a solution in `(1.30975, 1.30985)` (around the printed `1.3098`),
and it is the only solution (`ln x - e⁻ˣ` is strictly increasing). -/
@[kb "stitzzeager2013" "Exercise 6.4.31, p. 478"]
theorem exer_6_4_31 :
    (∃ x ∈ Ioo (1.30975 : ℝ) 1.30985, Real.log x = Real.exp (-x)) ∧
    ∀ y z : ℝ, 0 < y → 0 < z → Real.log y = Real.exp (-y) → Real.log z = Real.exp (-z) → y = z := by
  refine ⟨?_, ?_⟩
  · have hc : ContinuousOn (fun x : ℝ => Real.log x - Real.exp (-x)) (Icc 1.30975 1.30985) := by
      have h1 : ContinuousOn Real.log (Icc (1.30975 : ℝ) 1.30985) :=
        Real.continuousOn_log.mono (fun x hx => by
          simp only [mem_compl_iff, mem_singleton_iff]; exact (lt_of_lt_of_le (by norm_num) hx.1).ne')
      exact h1.sub (by fun_prop)
    have hlogA : Real.log 1.30975 < 0.269855 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have : 1.30976 ≤ Real.exp 0.269855 :=
        x6w8c_expL _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have hexpA : 0.26987 ≤ Real.exp (-1.30975) :=
      x6w8c_expL _ _ 2 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have hlogB : 0.26989 < Real.log 1.30985 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have : Real.exp 0.26989 ≤ 1.30983 :=
        x6w8c_expU _ _ 1 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have hexpB : Real.exp (-1.30985) ≤ 0.269875 :=
      x6w8c_expU _ _ 2 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.log x - Real.exp (-x)) 1.30975)
        ((fun x : ℝ => Real.log x - Real.exp (-x)) 1.30985) :=
      ⟨by simp only; linarith, by simp only; linarith⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1.30975 : ℝ) ≤ 1.30985) hc hmem
    refine ⟨x, hx, ?_⟩
    have : Real.log x - Real.exp (-x) = 0 := hfx
    linarith
  · intro y z hy hz hy' hz'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := Real.log_lt_log hy h
      have h2 : Real.exp (-z) < Real.exp (-y) := Real.exp_lt_exp.2 (by linarith)
      linarith
    · have h1 := Real.log_lt_log hz h
      have h2 : Real.exp (-y) < Real.exp (-z) := Real.exp_lt_exp.2 (by linarith)
      linarith

/-- Stitz-Zeager Exercise 6.4.32: `ln x = ∜x` has two solutions, near `4.177` and near `5503.665`: there is a
solution in each of `(4.1765, 4.1775)` and `(5503.6645, 5503.6655)` (intermediate value theorem). -/
@[kb "stitzzeager2013" "Exercise 6.4.32, p. 478"]
theorem exer_6_4_32 :
    (∃ x ∈ Ioo (4.1765 : ℝ) 4.1775, Real.log x = x ^ (1 / 4 : ℝ)) ∧
    (∃ x ∈ Ioo (5503.6645 : ℝ) 5503.6655, Real.log x = x ^ (1 / 4 : ℝ)) := by
  constructor
  · have hA : Real.log 4.1765 < 1.42951 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have : 4.17655 ≤ Real.exp 1.42951 :=
        x6w8c_expL _ _ 2 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have rA : 1.42955 ≤ (4.1765 : ℝ) ^ (1 / 4 : ℝ) :=
      x6w8c_le_r _ _ (by norm_num) (by norm_num) (by norm_num)
    have hB : 1.42968 < Real.log 4.1775 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have : Real.exp 1.42968 ≤ 4.1774 :=
        x6w8c_expU _ _ 2 (by norm_num) (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have rB : (4.1775 : ℝ) ^ (1 / 4 : ℝ) ≤ 1.42965 :=
      x6w8c_r_le _ _ (by norm_num) (by norm_num) (by norm_num)
    have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.log x - x ^ (1 / 4 : ℝ)) 4.1765)
        ((fun x : ℝ => Real.log x - x ^ (1 / 4 : ℝ)) 4.1775) :=
      ⟨by simp only; linarith, by simp only; linarith⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (4.1765 : ℝ) ≤ 4.1775)
      (x6w8c_cont _ _ (by norm_num)) hmem
    refine ⟨x, hx, ?_⟩
    have : Real.log x - x ^ (1 / 4 : ℝ) = 0 := hfx
    linarith
  · have hA : 8 + 0.61316941 < Real.log 5503.6645 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have : Real.exp (8 + 0.61316941) ≤ 5503.66448 :=
        x6w8c_exp8_le _ _ (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have rA : (5503.6645 : ℝ) ^ (1 / 4 : ℝ) ≤ 8.61316939 :=
      x6w8c_r_le _ _ (by norm_num) (by norm_num) (by norm_num)
    have hB : Real.log 5503.6655 < 8 + 0.61316965 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have : 5503.66565 ≤ Real.exp (8 + 0.61316965) :=
        x6w8c_exp8_ge _ _ (by rw [abs_le]; constructor <;> norm_num)
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
          (by norm_num [Finset.sum_range_succ, Nat.factorial])
      linarith
    have rB : 8.61316977 ≤ (5503.6655 : ℝ) ^ (1 / 4 : ℝ) :=
      x6w8c_le_r _ _ (by norm_num) (by norm_num) (by norm_num)
    have hmem : (0 : ℝ) ∈ Ioo ((fun x : ℝ => Real.log x - x ^ (1 / 4 : ℝ)) 5503.6655)
        ((fun x : ℝ => Real.log x - x ^ (1 / 4 : ℝ)) 5503.6645) :=
      ⟨by simp only; linarith, by simp only; linarith⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' (by norm_num : (5503.6645 : ℝ) ≤ 5503.6655)
      (x6w8c_cont _ _ (by norm_num)) hmem
    refine ⟨x, hx, ?_⟩
    have : Real.log x - x ^ (1 / 4 : ℝ) = 0 := hfx
    linarith

private theorem x6w8c_pA (x : ℝ) : 0 < (2 - x) * (2 * x - 1) * (x + 3) ↔ x < -3 ∨ (1 / 2 < x ∧ x < 2) := by
  constructor
  · intro h
    by_cases h1 : x < -3
    · exact Or.inl h1
    · right
      have h1' : -3 ≤ x := not_lt.1 h1
      by_contra hc
      rcases le_or_gt x (1 / 2) with h2 | h2
      · have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x))
          (by linarith : (0 : ℝ) ≤ x + 3)
        nlinarith [this]
      · have h3 : 2 ≤ x := by
          by_contra h3
          exact hc ⟨h2, by linarith⟩
        have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 2 * x - 1))
          (by linarith : (0 : ℝ) ≤ x + 3)
        nlinarith [this]
  · rintro (h | ⟨h1, h2⟩)
    · have := mul_pos (mul_pos (by linarith : (0 : ℝ) < 2 - x) (by linarith : (0 : ℝ) < 1 - 2 * x))
        (by linarith : (0 : ℝ) < -x - 3)
      nlinarith [this]
    · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

private theorem x6w8c_pB (r1 r2 r3 x : ℝ) (h12 : r1 < r2) (h23 : r2 < r3) :
    0 < (x - r1) * (x - r2) * (x - r3) ↔ (r1 < x ∧ x < r2) ∨ r3 < x := by
  constructor
  · intro h
    rcases le_or_gt x r1 with h1 | h1
    · have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r1 - x) (by linarith : (0 : ℝ) ≤ r2 - x))
        (by linarith : (0 : ℝ) ≤ r3 - x)
      nlinarith [this]
    · rcases lt_or_ge x r2 with h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · rcases lt_or_ge r3 x with h3 | h3
        · exact Or.inr h3
        · have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ x - r1) (by linarith : (0 : ℝ) ≤ x - r2))
            (by linarith : (0 : ℝ) ≤ r3 - x)
          nlinarith [this]
  · rintro (⟨h1, h2⟩ | h)
    · have := mul_pos (mul_pos (by linarith : (0 : ℝ) < x - r1) (by linarith : (0 : ℝ) < r2 - x))
        (by linarith : (0 : ℝ) < r3 - x)
      nlinarith [this]
    · exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- Stitz-Zeager Exercise 6.4.34: the solution set of `ln(-2x³ - x² + 13x - 6) < 0` is
`(r₁, -3) ∪ (1/2, r₂) ∪ (r₃, 2)` where `r₁, r₂, r₃` are the three roots of `-2x³ - x² + 13x - 7`, with
`r₁ ∈ (-3.0282, -3.0281)`, `r₂ ∈ (0.5991, 0.5992)` and `r₃ ∈ (1.9289, 1.9291)`. -/
@[kb "stitzzeager2013" "Exercise 6.4.34, p. 478"]
theorem exer_6_4_34 :
    ∃ r1 r2 r3 : ℝ, r1 ∈ Ioo (-3.0282 : ℝ) (-3.0281) ∧ r2 ∈ Ioo (0.5991 : ℝ) 0.5992 ∧
      r3 ∈ Ioo (1.9289 : ℝ) 1.9291 ∧
      -2 * r1 ^ 3 - r1 ^ 2 + 13 * r1 - 7 = 0 ∧ -2 * r2 ^ 3 - r2 ^ 2 + 13 * r2 - 7 = 0 ∧
      -2 * r3 ^ 3 - r3 ^ 2 + 13 * r3 - 7 = 0 ∧
      {x : ℝ | 0 < -2 * x ^ 3 - x ^ 2 + 13 * x - 6 ∧ Real.log (-2 * x ^ 3 - x ^ 2 + 13 * x - 6) < 0} =
        Ioo r1 (-3) ∪ Ioo (1 / 2) r2 ∪ Ioo r3 2 := by
  have hf : Continuous (fun x : ℝ => -2 * x ^ 3 - x ^ 2 + 13 * x - 7) := by fun_prop
  have hm1 : (0 : ℝ) ∈ Ioo ((fun x : ℝ => -2 * x ^ 3 - x ^ 2 + 13 * x - 7) (-3.0281))
      ((fun x : ℝ => -2 * x ^ 3 - x ^ 2 + 13 * x - 7) (-3.0282)) := ⟨by norm_num, by norm_num⟩
  obtain ⟨r1, hr1, hq1⟩ := intermediate_value_Ioo' (by norm_num : (-3.0282 : ℝ) ≤ -3.0281)
    hf.continuousOn hm1
  have hm2 : (0 : ℝ) ∈ Ioo ((fun x : ℝ => -2 * x ^ 3 - x ^ 2 + 13 * x - 7) 0.5991)
      ((fun x : ℝ => -2 * x ^ 3 - x ^ 2 + 13 * x - 7) 0.5992) := ⟨by norm_num, by norm_num⟩
  obtain ⟨r2, hr2, hq2⟩ := intermediate_value_Ioo (by norm_num : (0.5991 : ℝ) ≤ 0.5992)
    hf.continuousOn hm2
  have h1 : -2 * r1 ^ 3 - r1 ^ 2 + 13 * r1 - 7 = 0 := hq1
  have h2 : -2 * r2 ^ 3 - r2 ^ 2 + 13 * r2 - 7 = 0 := hq2
  obtain ⟨r3, hr3⟩ : ∃ r3 : ℝ, r3 = -1 / 2 - r1 - r2 := ⟨_, rfl⟩
  obtain ⟨hr1a, hr1b⟩ := hr1
  obtain ⟨hr2a, hr2b⟩ := hr2
  have hr3a : 1.9289 < r3 := by rw [hr3]; linarith
  have hr3b : r3 < 1.9291 := by rw [hr3]; linarith
  have hne : r1 - r2 ≠ 0 := by intro h; linarith
  have hA : 13 + 2 * (r1 * r2 + r1 * r3 + r2 * r3) = 0 := by
    have : (r1 - r2) * (13 + 2 * (r1 * r2 + r1 * r3 + r2 * r3)) = 0 := by
      subst hr3; linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hne
    · exact h
  have hB : -7 - 2 * (r1 * r2 * r3) = 0 := by
    subst hr3; linear_combination h1 - r1 * hA
  have hfac : ∀ x : ℝ, -2 * x ^ 3 - x ^ 2 + 13 * x - 7 = -2 * ((x - r1) * (x - r2) * (x - r3)) := by
    intro x
    subst hr3
    linear_combination x * hA + hB
  have h3 : -2 * r3 ^ 3 - r3 ^ 2 + 13 * r3 - 7 = 0 := by
    rw [hfac r3]; ring
  have h12 : r1 < r2 := by linarith
  have h23 : r2 < r3 := by linarith
  refine ⟨r1, r2, r3, ⟨hr1a, hr1b⟩, ⟨hr2a, hr2b⟩, ⟨hr3a, hr3b⟩, h1, h2, h3, ?_⟩
  ext x
  have hp : -2 * x ^ 3 - x ^ 2 + 13 * x - 6 = (2 - x) * (2 * x - 1) * (x + 3) := by ring
  have hq := hfac x
  have hS : (0 < -2 * x ^ 3 - x ^ 2 + 13 * x - 6 ∧ Real.log (-2 * x ^ 3 - x ^ 2 + 13 * x - 6) < 0) ↔
      (0 < -2 * x ^ 3 - x ^ 2 + 13 * x - 6 ∧ -2 * x ^ 3 - x ^ 2 + 13 * x - 6 < 1) := by
    constructor
    · rintro ⟨a, b⟩
      refine ⟨a, ?_⟩
      have := (Real.log_lt_iff_lt_exp a).1 b
      rwa [Real.exp_zero] at this
    · rintro ⟨a, b⟩
      refine ⟨a, (Real.log_lt_iff_lt_exp a).2 ?_⟩
      rwa [Real.exp_zero]
  simp only [mem_setOf_eq, mem_union, mem_Ioo]
  rw [hS]
  constructor
  · rintro ⟨hpos, hlt⟩
    have hA' := (x6w8c_pA x).1 (by rw [← hp]; exact hpos)
    have hB' := (x6w8c_pB r1 r2 r3 x h12 h23).1 (by linarith)
    rcases hA' with a | ⟨a1, a2⟩
    · rcases hB' with ⟨b1, b2⟩ | b
      · exact Or.inl (Or.inl ⟨b1, a⟩)
      · exfalso; linarith
    · rcases hB' with ⟨b1, b2⟩ | b
      · exact Or.inl (Or.inr ⟨a1, b2⟩)
      · exact Or.inr ⟨b, a2⟩
  · intro hx
    have hAB : (x < -3 ∨ (1 / 2 < x ∧ x < 2)) ∧ ((r1 < x ∧ x < r2) ∨ r3 < x) := by
      rcases hx with (⟨a, b⟩ | ⟨a, b⟩) | ⟨a, b⟩
      · exact ⟨Or.inl b, Or.inl ⟨a, by linarith⟩⟩
      · exact ⟨Or.inr ⟨a, by linarith⟩, Or.inl ⟨by linarith, b⟩⟩
      · exact ⟨Or.inr ⟨by linarith, b⟩, Or.inr a⟩
    have hpos : 0 < -2 * x ^ 3 - x ^ 2 + 13 * x - 6 := by
      rw [hp]; exact (x6w8c_pA x).2 hAB.1
    have hB' := (x6w8c_pB r1 r2 r3 x h12 h23).2 hAB.2
    exact ⟨hpos, by linarith⟩

end UndergradKB.Precalculus.Course
