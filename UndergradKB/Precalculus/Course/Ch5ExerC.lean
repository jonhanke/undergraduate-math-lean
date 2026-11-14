import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.Interval.Set.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 5 (Stitz-Zeager): exercises with the book's answers, Section 5.3 -/

namespace UndergradKB.Precalculus.Course

open Set

/-! ## Section 5.3: domains, radical equations and inequalities -/

/-- Stitz-Zeager Exercise 5.3.1: `f(x) = √(1-x²)` has domain `[-1, 1]`, vanishes at `±1` and is positive between. -/
@[kb "stitzzeager2013" "Exercise 5.3.1, p. 419"]
theorem exer_5_3_1 :
    {x : ℝ | 0 ≤ 1 - x ^ 2} = Icc (-1) 1 ∧ Real.sqrt (1 - (1 : ℝ) ^ 2) = 0 ∧
    Real.sqrt (1 - (-1 : ℝ) ^ 2) = 0 ∧ ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < Real.sqrt (1 - x ^ 2) := by
  refine ⟨?_, by norm_num, by norm_num, fun x hx => ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_Icc]
    constructor
    · intro h
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      nlinarith
  · apply Real.sqrt_pos.mpr
    nlinarith [hx.1, hx.2]

/-- Stitz-Zeager Exercise 5.3.2: `f(x) = √(x²-1)` has domain `(-∞, -1] ∪ [1, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.2, p. 419"]
theorem exer_5_3_2 : {x : ℝ | 0 ≤ x ^ 2 - 1} = Iic (-1) ∪ Ici 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [hc.1, hc.2]
  · rintro (h | h) <;> nlinarith

/-- Stitz-Zeager Exercise 5.3.17: `x + 1 = √(3x+7)` holds exactly when `x = 3`. -/
@[kb "stitzzeager2013" "Exercise 5.3.17, p. 419"]
theorem exer_5_3_17 (x : ℝ) : x + 1 = Real.sqrt (3 * x + 7) ↔ x = 3 := by
  rw [eq_comm, Real.sqrt_eq_cases]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h : (x - 3) * (x + 2) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h with h3 | h3
      · linarith
      · linarith
    · exfalso; linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 5.3.18: `2x + 1 = √(3 - 3x)` holds exactly when `x = 1/4`. -/
@[kb "stitzzeager2013" "Exercise 5.3.18, p. 419"]
theorem exer_5_3_18 (x : ℝ) : 2 * x + 1 = Real.sqrt (3 - 3 * x) ↔ x = 1 / 4 := by
  rw [eq_comm, Real.sqrt_eq_cases]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h : (4 * x - 1) * (x + 2) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h with h3 | h3
      · linarith
      · linarith
    · exfalso; linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 5.3.19: `x + √(3x+10) = -2` holds exactly when `x = -3`. -/
@[kb "stitzzeager2013" "Exercise 5.3.19, p. 419"]
theorem exer_5_3_19 (x : ℝ) : x + Real.sqrt (3 * x + 10) = -2 ↔ x = -3 := by
  have : x + Real.sqrt (3 * x + 10) = -2 ↔ Real.sqrt (3 * x + 10) = -2 - x := by
    constructor <;> intro h <;> linarith
  rw [this, Real.sqrt_eq_cases]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h : (x - 2) * (x + 3) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h with h3 | h3
      · linarith
      · linarith
    · exfalso; linarith
  · rintro rfl; norm_num

/-- Stitz-Zeager Exercise 5.3.20: `3x + √(6-9x) = 2` holds exactly when `x = -1/3` or `x = 2/3`. -/
@[kb "stitzzeager2013" "Exercise 5.3.20, p. 419"]
theorem exer_5_3_20 (x : ℝ) : 3 * x + Real.sqrt (6 - 9 * x) = 2 ↔ x = -1 / 3 ∨ x = 2 / 3 := by
  have : 3 * x + Real.sqrt (6 - 9 * x) = 2 ↔ Real.sqrt (6 - 9 * x) = 2 - 3 * x := by
    constructor <;> intro h <;> linarith
  rw [this, Real.sqrt_eq_cases]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h : (3 * x + 1) * (3 * x - 2) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h with h3 | h3
      · left; linarith
      · right; linarith
    · exfalso; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- Stitz-Zeager Exercise 5.3.21: `2x - 1 = √(x+3)` holds exactly when `x = (5 + √57)/8`. -/
@[kb "stitzzeager2013" "Exercise 5.3.21, p. 419"]
theorem exer_5_3_21 (x : ℝ) : 2 * x - 1 = Real.sqrt (x + 3) ↔ x = (5 + Real.sqrt 57) / 8 := by
  have hs : Real.sqrt 57 ^ 2 = 57 := Real.sq_sqrt (by norm_num)
  have hs7 : 7 < Real.sqrt 57 := by
    rw [show (7 : ℝ) = Real.sqrt 49 by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [eq_comm, Real.sqrt_eq_cases]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h : (x - (5 + Real.sqrt 57) / 8) * (x - (5 - Real.sqrt 57) / 8) = 0 := by
        linear_combination h1 / 4 - hs / 64
      rcases mul_eq_zero.mp h with h3 | h3
      · linarith
      · exfalso; linarith
    · exfalso; linarith
  · rintro rfl
    left
    constructor
    · linear_combination hs / 16
    · linarith

/-- Stitz-Zeager Exercise 5.3.24: `√(x-2) + √(x-5) = 3` holds exactly when `x = 6`. -/
@[kb "stitzzeager2013" "Exercise 5.3.24, p. 419"]
theorem exer_5_3_24 (x : ℝ) : Real.sqrt (x - 2) + Real.sqrt (x - 5) = 3 ↔ x = 6 := by
  constructor
  · intro h
    have ha := Real.sqrt_nonneg (x - 2)
    have hb := Real.sqrt_nonneg (x - 5)
    by_cases hx : 5 ≤ x
    · have h1 := Real.sq_sqrt (show 0 ≤ x - 2 by linarith)
      have h2 := Real.sq_sqrt (show 0 ≤ x - 5 by linarith)
      have h3 : Real.sqrt (x - 2) - Real.sqrt (x - 5) = 1 := by
        have : (Real.sqrt (x - 2) - Real.sqrt (x - 5)) * 3 = 3 := by
          nlinarith
        linarith
      have h4 : Real.sqrt (x - 2) = 2 := by linarith
      rw [h4] at h1
      linarith
    · push Not at hx
      have h2 : Real.sqrt (x - 5) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
      have h3 : Real.sqrt (x - 2) = 3 := by linarith
      by_cases hx2 : 2 ≤ x
      · have h1 := Real.sq_sqrt (show 0 ≤ x - 2 by linarith)
        rw [h3] at h1
        linarith
      · push Not at hx2
        rw [Real.sqrt_eq_zero_of_nonpos (by linarith)] at h3
        norm_num at h3
  · rintro rfl
    rw [show (6 : ℝ) - 2 = 2 ^ 2 by norm_num, show (6 : ℝ) - 5 = 1 by norm_num, Real.sqrt_sq (by norm_num),
      Real.sqrt_one]
    norm_num

/-- Stitz-Zeager Exercise 5.3.25: `√(2x+1) = 3 + √(4-x)` holds exactly when `x = 4`. -/
@[kb "stitzzeager2013" "Exercise 5.3.25, p. 419"]
theorem exer_5_3_25 (x : ℝ) : Real.sqrt (2 * x + 1) = 3 + Real.sqrt (4 - x) ↔ x = 4 := by
  constructor
  · intro h
    have ha := Real.sqrt_nonneg (2 * x + 1)
    have hb := Real.sqrt_nonneg (4 - x)
    by_cases hx : x ≤ 4
    · by_cases hx2 : 0 ≤ 2 * x + 1
      · have h1 := Real.sq_sqrt hx2
        have h2 := Real.sq_sqrt (show 0 ≤ 4 - x by linarith)
        rw [h] at h1
        nlinarith
      · push Not at hx2
        rw [Real.sqrt_eq_zero_of_nonpos hx2.le] at h
        linarith
    · push Not at hx
      have h2 : Real.sqrt (4 - x) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
      rw [h2] at h
      have h1 := Real.sq_sqrt (show 0 ≤ 2 * x + 1 by linarith)
      rw [h] at h1
      linarith
  · rintro rfl
    rw [show (2 : ℝ) * 4 + 1 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num), sub_self, Real.sqrt_zero]
    norm_num

/-- Stitz-Zeager Exercise 5.3.27: `10 - √(x-2) ≤ 11` holds for every `x` of the domain `[2, ∞)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.27, p. 419"]
theorem exer_5_3_27 : {x : ℝ | 2 ≤ x ∧ 10 - Real.sqrt (x - 2) ≤ 11} = Ici 2 := by
  ext x
  simp only [mem_ofPred_eq, mem_Ici]
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h
    exact ⟨h, by linarith [Real.sqrt_nonneg (x - 2)]⟩

/-! ## Section 5.3: applications -/

/-- Stitz-Zeager Exercise 5.3.37(a): a cone of volume `100` with base radius `r` has height `h = 300/(πr²)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.37, p. 420"]
theorem exer_5_3_37_a (r h : ℝ) (hr : 0 < r) : 1 / 3 * Real.pi * r ^ 2 * h = 100 ↔ h = 300 / (Real.pi * r ^ 2) := by
  have hp := Real.pi_pos
  rw [eq_div_iff (by positivity)]
  constructor <;> intro h' <;> linarith

/-- Stitz-Zeager Exercise 5.3.37(b): with that height, the cone's surface area `πr√(r²+h²)` equals
`√(π²r⁶ + 90000)/r`. -/
@[kb "stitzzeager2013" "Exercise 5.3.37, p. 420"]
theorem exer_5_3_37_b (r : ℝ) (hr : 0 < r) :
    Real.pi * r * Real.sqrt (r ^ 2 + (300 / (Real.pi * r ^ 2)) ^ 2) =
      Real.sqrt (Real.pi ^ 2 * r ^ 6 + 90000) / r := by
  have hp := Real.pi_pos
  have hA : r ^ 2 + (300 / (Real.pi * r ^ 2)) ^ 2 =
      (Real.pi ^ 2 * r ^ 6 + 90000) / (Real.pi * r ^ 2) ^ 2 := by
    field_simp
    norm_num
  rw [hA, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  field_simp

/-- Stitz-Zeager Exercise 5.3.39(a): at air temperature `28` degrees the wind-chill formula becomes
`W(V) = 53.142 - 23.78 V^0.16`. -/
@[kb "stitzzeager2013" "Exercise 5.3.39, p. 420"]
theorem exer_5_3_39_a (V : ℝ) :
    35.74 + 0.6215 * 28 - 35.75 * V ^ (0.16 : ℝ) + 0.4275 * 28 * V ^ (0.16 : ℝ) =
      53.142 - 23.78 * V ^ (0.16 : ℝ) := by
  ring

/-- Stitz-Zeager Exercise 5.3.40: the pendulum period `2π√(L/9.8)` equals `1/2` second exactly when
`L = 9.8 (1/(4π))²`, which is between `0.061` and `0.063` meters (about 6.2 cm). -/
@[kb "stitzzeager2013" "Exercise 5.3.40, p. 421"]
theorem exer_5_3_40 :
    (∀ L : ℝ, 0 ≤ L → (2 * Real.pi * Real.sqrt (L / 9.8) = 1 / 2 ↔ L = 9.8 * (1 / (4 * Real.pi)) ^ 2)) ∧
    0.061 < 9.8 * (1 / (4 * Real.pi)) ^ 2 ∧ 9.8 * (1 / (4 * Real.pi)) ^ 2 < 0.063 := by
  have hp := Real.pi_pos
  refine ⟨fun L hL => ?_, ?_, ?_⟩
  · have hq : 0 ≤ L / 9.8 := by positivity
    constructor
    · intro h
      have h1 : Real.sqrt (L / 9.8) = 1 / (4 * Real.pi) := by
        field_simp
        linarith
      have h2 := Real.sq_sqrt hq
      rw [h1] at h2
      rw [h2]
      ring
    · intro h
      have h1 : L / 9.8 = (1 / (4 * Real.pi)) ^ 2 := by rw [h]; ring
      rw [h1, Real.sqrt_sq (by positivity)]
      field_simp
      norm_num
  · have h1 := Real.pi_lt_d2
    have h2 := Real.pi_gt_d2
    rw [show 9.8 * (1 / (4 * Real.pi)) ^ 2 = 9.8 / (16 * Real.pi ^ 2) by ring, lt_div_iff₀ (by positivity)]
    nlinarith
  · have h1 := Real.pi_lt_d2
    have h2 := Real.pi_gt_d2
    rw [show 9.8 * (1 / (4 * Real.pi)) ^ 2 = 9.8 / (16 * Real.pi ^ 2) by ring, div_lt_iff₀ (by positivity)]
    nlinarith

/-- Stitz-Zeager Exercise 5.3.42(d): an object of rest mass `mr` and speed `x < c` has observed mass
`mr/√(1-x²/c²)` at most `100 mr` exactly when `x² ≤ (9999/10000) c²`, i.e. `x ≤ 0.99995 c` approximately. -/
@[kb "stitzzeager2013" "Exercise 5.3.42, p. 421"]
theorem exer_5_3_42_d (mr c x : ℝ) (hmr : 0 < mr) (hc : 0 < c) (hx0 : 0 ≤ x) (hxc : x < c) :
    mr / Real.sqrt (1 - x ^ 2 / c ^ 2) ≤ 100 * mr ↔ x ^ 2 ≤ 9999 / 10000 * c ^ 2 := by
  have hpos : 0 < 1 - x ^ 2 / c ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]
    nlinarith
  have hs : 0 < Real.sqrt (1 - x ^ 2 / c ^ 2) := Real.sqrt_pos.mpr hpos
  rw [div_le_iff₀ hs]
  have h1 : mr ≤ 100 * mr * Real.sqrt (1 - x ^ 2 / c ^ 2) ↔ 1 / 100 ≤ Real.sqrt (1 - x ^ 2 / c ^ 2) := by
    constructor
    · intro h
      by_contra hc'
      push Not at hc'
      nlinarith
    · intro h
      nlinarith
  rw [h1, Real.le_sqrt' (by norm_num)]
  constructor
  · intro h
    have : x ^ 2 / c ^ 2 ≤ 9999 / 10000 := by linarith
    rwa [div_le_iff₀ (by positivity)] at this
  · intro h
    have : x ^ 2 / c ^ 2 ≤ 9999 / 10000 := by
      rw [div_le_iff₀ (by positivity)]; exact h
    linarith

/-- Stitz-Zeager Exercise 5.3.43: `k(x) = 2x/√(x²-1)` (taken on `x > 1`, with values `> 2`) has inverse
`k⁻¹(x) = x/√(x²-4)`. -/
@[kb "stitzzeager2013" "Exercise 5.3.43, p. 421"]
theorem exer_5_3_43 :
    (∀ x : ℝ, 1 < x →
      (2 * x / Real.sqrt (x ^ 2 - 1)) / Real.sqrt ((2 * x / Real.sqrt (x ^ 2 - 1)) ^ 2 - 4) = x) ∧
    ∀ y : ℝ, 2 < y →
      2 * (y / Real.sqrt (y ^ 2 - 4)) / Real.sqrt ((y / Real.sqrt (y ^ 2 - 4)) ^ 2 - 1) = y := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h0 : 0 < x ^ 2 - 1 := by nlinarith
    have hs := Real.sqrt_pos.mpr h0
    have hs2 := Real.sq_sqrt h0.le
    have h1 : (2 * x / Real.sqrt (x ^ 2 - 1)) ^ 2 - 4 = (2 / Real.sqrt (x ^ 2 - 1)) ^ 2 := by
      rw [div_pow, div_pow, hs2]
      field_simp
      ring
    rw [h1, Real.sqrt_sq (by positivity)]
    field_simp
  · have h0 : 0 < y ^ 2 - 4 := by nlinarith
    have hs := Real.sqrt_pos.mpr h0
    have hs2 := Real.sq_sqrt h0.le
    have h1 : (y / Real.sqrt (y ^ 2 - 4)) ^ 2 - 1 = (2 / Real.sqrt (y ^ 2 - 4)) ^ 2 := by
      rw [div_pow, div_pow, hs2]
      field_simp
      ring
    rw [h1, Real.sqrt_sq (by positivity)]
    field_simp

/-- Stitz-Zeager Exercise 5.3.44(a): if the fox runs twice as fast as the rabbit (`v₂ = 2v₁`), the pursuit curve
`y = ½(x^{1+v₁/v₂}/(1+v₁/v₂) - x^{1-v₁/v₂}/(1-v₁/v₂)) + v₁v₂/(v₂²-v₁²)` is `y = x^{3/2}/3 - √x + 2/3`. -/
@[kb "stitzzeager2013" "Exercise 5.3.44, p. 422"]
theorem exer_5_3_44_a (x v₁ : ℝ) (hv : 0 < v₁) :
    1 / 2 * (x ^ (1 + v₁ / (2 * v₁)) / (1 + v₁ / (2 * v₁)) - x ^ (1 - v₁ / (2 * v₁)) / (1 - v₁ / (2 * v₁))) +
      v₁ * (2 * v₁) / ((2 * v₁) ^ 2 - v₁ ^ 2) = 1 / 3 * x ^ ((3 : ℝ) / 2) - Real.sqrt x + 2 / 3 := by
  have h12 : v₁ / (2 * v₁) = 1 / 2 := by
    field_simp
  have e3 : v₁ * (2 * v₁) / ((2 * v₁) ^ 2 - v₁ ^ 2) = 2 / 3 := by
    have : (2 * v₁) ^ 2 - v₁ ^ 2 = 3 * v₁ ^ 2 := by ring
    rw [this, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  rw [h12, e3, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  ring

/-- Stitz-Zeager Exercise 5.3.44(b): if the rabbit runs twice as fast as the fox (`v₁ = 2v₂`), the pursuit curve is
`y = x³/6 + 1/(2x) - 2/3`. -/
@[kb "stitzzeager2013" "Exercise 5.3.44, p. 422"]
theorem exer_5_3_44_b (x v₂ : ℝ) (hv : 0 < v₂) :
    1 / 2 * (x ^ (1 + 2 * v₂ / v₂) / (1 + 2 * v₂ / v₂) - x ^ (1 - 2 * v₂ / v₂) / (1 - 2 * v₂ / v₂)) +
      2 * v₂ * v₂ / (v₂ ^ 2 - (2 * v₂) ^ 2) = x ^ 3 / 6 + 1 / (2 * x) - 2 / 3 := by
  have h2 : 2 * v₂ / v₂ = 2 := by
    field_simp
  have e3 : 2 * v₂ * v₂ / (v₂ ^ 2 - (2 * v₂) ^ 2) = -2 / 3 := by
    have : v₂ ^ 2 - (2 * v₂) ^ 2 = -3 * v₂ ^ 2 := by ring
    rw [this, div_eq_div_iff (by nlinarith) (by norm_num)]
    ring
  have hx3 : x ^ (3 : ℝ) = x ^ 3 := by exact_mod_cast Real.rpow_natCast x 3
  rw [h2, e3, show (1 : ℝ) + 2 = 3 by norm_num, show (1 : ℝ) - 2 = -1 by norm_num, hx3, Real.rpow_neg_one]
  ring

end UndergradKB.Precalculus.Course
