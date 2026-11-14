import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 5.3 (models) -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology

/-- A number `t` with `t ^ n = c`, `lo ^ n < c < hi ^ n` (all bounds nonnegative) lies strictly between `lo`, `hi`. -/
private theorem x5w7i_bound {t c lo hi : ℝ} {n : ℕ} (hhi : 0 ≤ hi)
    (ht : 0 ≤ t) (h : t ^ n = c) (h1 : lo ^ n < c) (h2 : c < hi ^ n) (hlo : 0 ≤ lo) : lo < t ∧ t < hi := by
  constructor
  · by_contra hc
    have := pow_le_pow_left₀ ht (not_lt.1 hc) n
    rw [h] at this; linarith
  · by_contra hc
    have := pow_le_pow_left₀ hhi (not_lt.1 hc) n
    rw [h] at this; linarith

/-- Stitz-Zeager Exercise 5.3.41: on the isoquant `300 = 1.23 x^0.4 y^0.6` the capital is
`y = (300/(1.23 x^0.4))^(5/3)`, and for `x = 100` it is about `441.94` (it lies in `(441.93, 441.94)`). -/
@[kb "stitzzeager2013" "Exercise 5.3.41, p. 421"]
theorem exer_5_3_41 :
    (∀ x y : ℝ, 0 < x → 0 < y → (300 = 1.23 * x ^ (0.4 : ℝ) * y ^ (0.6 : ℝ) ↔
      y = (300 / (1.23 * x ^ (0.4 : ℝ))) ^ (5 / 3 : ℝ))) ∧
    ∀ y : ℝ, 0 < y → 300 = 1.23 * (100 : ℝ) ^ (0.4 : ℝ) * y ^ (0.6 : ℝ) → 441.93 < y ∧ y < 441.94 := by
  have back : ∀ u : ℝ, 0 < u → (u ^ (5 / 3 : ℝ)) ^ (0.6 : ℝ) = u := by
    intro u hu
    rw [← Real.rpow_mul hu.le, show (5 / 3 : ℝ) * 0.6 = 1 by norm_num, Real.rpow_one]
  have fwd : ∀ y : ℝ, 0 < y → (y ^ (0.6 : ℝ)) ^ (5 / 3 : ℝ) = y := by
    intro y hy
    rw [← Real.rpow_mul hy.le, show (0.6 : ℝ) * (5 / 3) = 1 by norm_num, Real.rpow_one]
  constructor
  · intro x y hx hy
    have hxp : 0 < 1.23 * x ^ (0.4 : ℝ) := by positivity
    have hu : 0 < 300 / (1.23 * x ^ (0.4 : ℝ)) := by positivity
    constructor
    · intro h
      have : y ^ (0.6 : ℝ) = 300 / (1.23 * x ^ (0.4 : ℝ)) := by
        rw [eq_div_iff hxp.ne']; linarith
      rw [← this, fwd y hy]
    · intro h
      have : y ^ (0.6 : ℝ) = 300 / (1.23 * x ^ (0.4 : ℝ)) := by rw [h, back _ hu]
      rw [this]; field_simp
  · intro y hy h
    have ht : ((100 : ℝ) ^ (0.4 : ℝ)) ^ (5 : ℕ) = 10000 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        show (0.4 : ℝ) * ((5 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hs : (y ^ (0.6 : ℝ)) ^ (5 : ℕ) = y ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le,
        show (0.6 : ℝ) * ((5 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e : (300 : ℝ) ^ 5 = (1.23 : ℝ) ^ 5 * 10000 * y ^ 3 := by
      have h5 : (300 : ℝ) ^ 5 = (1.23 * (100 : ℝ) ^ (0.4 : ℝ) * y ^ (0.6 : ℝ)) ^ 5 := by rw [← h]
      rw [h5, mul_pow, mul_pow, ht, hs]
    have : y ^ 3 = (300 : ℝ) ^ 5 / ((1.23 : ℝ) ^ 5 * 10000) := by
      rw [eq_div_iff (by norm_num)]; linarith
    exact x5w7i_bound (n := 3) (by norm_num) hy.le this (by norm_num) (by norm_num) (by norm_num)

/-- Stitz-Zeager Exercise 5.3.42: for relativistic mass `m(x) = m_r / √(1 - x²/c²)` (with `m_r, c > 0`):
(a) the domain is `[0, c)`; (b) `m(.1c) = m_r/√.99`, `m(.5c) = m_r/√.75`, `m(.9c) = m_r/√.19`,
`m(.999c) = m_r/√.001999`; (c) `m(x) → ∞` as `x → c⁻`; (d) `m(x) ≤ 100 m_r` exactly when `x ≤ c √.9999`, and
`0.99994 < √.9999 < 0.99995`. -/
@[kb "stitzzeager2013" "Exercise 5.3.42, p. 421"]
theorem exer_5_3_42 (m : ℝ → ℝ) (mr c : ℝ) (hmr : 0 < mr) (hc : 0 < c)
    (hm : m = fun x => mr / Real.sqrt (1 - x ^ 2 / c ^ 2)) :
    {x : ℝ | 0 ≤ x ∧ 0 < 1 - x ^ 2 / c ^ 2} = Ico 0 c ∧
    (m (0.1 * c) = mr / Real.sqrt 0.99 ∧ m (0.5 * c) = mr / Real.sqrt 0.75 ∧
      m (0.9 * c) = mr / Real.sqrt 0.19 ∧ m (0.999 * c) = mr / Real.sqrt 0.001999) ∧
    Tendsto m (𝓝[<] c) atTop ∧
    (∀ x : ℝ, 0 ≤ x → x < c → (m x ≤ 100 * mr ↔ x ≤ c * Real.sqrt 0.9999)) ∧
    (0.99994 < Real.sqrt 0.9999 ∧ Real.sqrt 0.9999 < 0.99995) := by
  subst hm
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have posiff : ∀ x : ℝ, 0 ≤ x → (0 < 1 - x ^ 2 / c ^ 2 ↔ x < c) := by
    intro x hx
    rw [sub_pos, div_lt_one hc2]
    constructor
    · intro h; by_contra hcx; push Not at hcx; nlinarith
    · intro h; nlinarith
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · ext x; simp only [mem_ofPred_eq, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (posiff x h1).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (posiff x h1).2 h2⟩
  · simp only; congr 2; field_simp; norm_num
  · simp only; congr 2; field_simp; norm_num
  · simp only; congr 2; field_simp; norm_num
  · simp only; congr 2; field_simp; norm_num
  · have hg : Tendsto (fun x : ℝ => Real.sqrt (1 - x ^ 2 / c ^ 2)) (𝓝[<] c) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hcont : Continuous (fun x : ℝ => Real.sqrt (1 - x ^ 2 / c ^ 2)) := by fun_prop
        have := hcont.tendsto c
        have h0 : Real.sqrt (1 - c ^ 2 / c ^ 2) = 0 := by
          rw [div_self hc2.ne']; simp
        rw [h0] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT hc] with x hx
        exact Real.sqrt_pos.2 ((posiff x hx.1.le).2 hx.2)
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp hg
    have h2 := this.const_mul_atTop hmr
    simpa [Function.comp_def, div_eq_mul_inv] using h2
  · intro x hx hxc
    have hp : 0 < Real.sqrt (1 - x ^ 2 / c ^ 2) := Real.sqrt_pos.2 ((posiff x hx).2 hxc)
    simp only
    rw [div_le_iff₀ hp, show 100 * mr * Real.sqrt (1 - x ^ 2 / c ^ 2) = mr * (100 * Real.sqrt (1 - x ^ 2 / c ^ 2)) by ring]
    rw [le_mul_iff_one_le_right hmr]
    have e1 : 1 ≤ 100 * Real.sqrt (1 - x ^ 2 / c ^ 2) ↔ 1 / 100 ≤ Real.sqrt (1 - x ^ 2 / c ^ 2) := by
      rw [← div_le_iff₀' (by norm_num : (0 : ℝ) < 100)]
    rw [e1, Real.le_sqrt (by norm_num) (by linarith [(posiff x hx).2 hxc])]
    have e2 : x ≤ c * Real.sqrt 0.9999 ↔ x / c ≤ Real.sqrt 0.9999 := by
      rw [div_le_iff₀ hc, mul_comm]
    rw [e2, Real.le_sqrt (by positivity) (by norm_num), div_pow (x) c 2]
    constructor
    · intro h
      norm_num at h ⊢; linarith
    · intro h
      norm_num at h ⊢; linarith
  · constructor
    · rw [Real.lt_sqrt (by norm_num)]; norm_num
    · rw [Real.sqrt_lt' (by norm_num)]; norm_num

end UndergradKB.Precalculus.Course
