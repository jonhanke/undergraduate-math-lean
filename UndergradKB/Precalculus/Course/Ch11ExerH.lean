import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Vectors
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers

Sections 11.8 (vectors) and 11.9 (dot product and projection). Plane vectors are pairs `ℝ × ℝ`, with
`vecMag` the magnitude, `dotProd2` the dot product and `vecProj` the projection. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false

/-! ## Helpers -/

private theorem x11h_mag {a b c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 + b ^ 2 = c ^ 2) : vecMag (a, b) = c := by
  unfold vecMag; simp only; rw [h, Real.sqrt_sq hc]

private theorem x11h_sq (p : ℝ × ℝ) : vecMag p ^ 2 = p.1 ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem x11h_par (v w : ℝ × ℝ) :
    vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  rw [x11h_sq, x11h_sq, x11h_sq, x11h_sq]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Uniqueness of the polar name with `r ≥ 0` and `0 ≤ θ < 2π` of a point other than the origin. -/
private theorem x11h_conv {r r' θ θ' : ℝ} (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ < 2 * π)
    (h0' : 0 ≤ r') (hθ0' : 0 ≤ θ') (hθ' : θ' < 2 * π) :
    polarPoint r' θ' = polarPoint r θ ↔ r' = r ∧ θ' = θ := by
  constructor
  · intro h
    rcases (polar_point_same_names r θ 0).2.2 hr.ne' r' θ' h with ⟨h1, n, hn⟩ | ⟨h1, n, hn⟩
    · refine ⟨h1, ?_⟩
      have hpi := pi_pos
      have e1 : (n : ℝ) < 1 := by nlinarith
      have e2 : (-1 : ℝ) < n := by nlinarith
      have : n = 0 := by
        have a : n < 1 := by exact_mod_cast e1
        have b : -1 < n := by exact_mod_cast e2
        omega
      subst this
      simpa using hn
    · exfalso; linarith
  · rintro ⟨rfl, rfl⟩; rfl

/-! ## Section 11.8 -/

/-- Stitz-Zeager Exercise 11.8.1: for `v = ⟨12, -5⟩`, `w = ⟨3, 4⟩`: `v + w = ⟨15, -1⟩`, `w - 2v = ⟨-21, 14⟩`,
`‖v + w‖ = √226`, `‖v‖ + ‖w‖ = 18`, `‖v‖w - ‖w‖v = ⟨-21, 77⟩`, `‖w‖ v̂ = ⟨60/13, -25/13⟩`, and the
parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.1, p. 1039"]
theorem exer_11_8_1 (v w : ℝ × ℝ) (hv : v = (12, -5)) (hw : w = (3, 4)) :
    v + w = (15, -1) ∧ w - (2 : ℝ) • v = (-21, 14) ∧ vecMag (v + w) = √226 ∧
      vecMag v + vecMag w = 18 ∧ vecMag v • w - vecMag w • v = (-21, 77) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (60 / 13, -25 / 13) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have mv : vecMag v = 13 := by rw [hv]; exact x11h_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 5 := by rw [hw]; exact x11h_mag (by norm_num) (by norm_num)
  subst hv hw
  refine ⟨by norm_num, by norm_num [Prod.ext_iff], ?_, by rw [mv, mw]; norm_num, ?_, ?_, ?_⟩
  · unfold vecMag; norm_num
  · rw [mv, mw]; norm_num [Prod.ext_iff]
  · rw [mv, mw]; norm_num [Prod.ext_iff]
  · exact x11h_par _ _

/-- Stitz-Zeager Exercise 11.8.2: for `v = ⟨-7, 24⟩`, `w = ⟨-5, -12⟩`: `v + w = ⟨-12, 12⟩`,
`w - 2v = ⟨9, -60⟩`, `‖v + w‖ = 12√2`, `‖v‖ + ‖w‖ = 38`, `‖v‖w - ‖w‖v = ⟨-34, -612⟩`,
`‖w‖ v̂ = ⟨-91/25, 312/25⟩`, and the parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.2, p. 1039"]
theorem exer_11_8_2 (v w : ℝ × ℝ) (hv : v = (-7, 24)) (hw : w = (-5, -12)) :
    v + w = (-12, 12) ∧ w - (2 : ℝ) • v = (9, -60) ∧ vecMag (v + w) = 12 * √2 ∧
      vecMag v + vecMag w = 38 ∧ vecMag v • w - vecMag w • v = (-34, -612) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (-91 / 25, 312 / 25) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have mv : vecMag v = 25 := by rw [hv]; exact x11h_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 13 := by rw [hw]; exact x11h_mag (by norm_num) (by norm_num)
  subst hv hw
  refine ⟨by norm_num, by norm_num [Prod.ext_iff], ?_, by rw [mv, mw]; norm_num, ?_, ?_, ?_⟩
  · have : vecMag ((-7, 24) + (-5, -12) : ℝ × ℝ) = vecMag (-12, 12) := by norm_num
    rw [this]
    unfold vecMag; simp only
    rw [show ((-12 : ℝ) ^ 2 + 12 ^ 2) = 12 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  · rw [mv, mw]; norm_num [Prod.ext_iff]
  · rw [mv, mw]; norm_num [Prod.ext_iff]
  · exact x11h_par _ _

/-- Stitz-Zeager Exercise 11.8.3: for `v = ⟨2, -1⟩`, `w = ⟨-2, 4⟩`: `v + w = ⟨0, 3⟩`, `w - 2v = ⟨-6, 6⟩`,
`‖v + w‖ = 3`, `‖v‖ + ‖w‖ = 3√5`, `‖v‖w - ‖w‖v = ⟨-6√5, 6√5⟩`, `‖w‖ v̂ = ⟨4, -2⟩`, and the
parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.3, p. 1039"]
theorem exer_11_8_3 (v w : ℝ × ℝ) (hv : v = (2, -1)) (hw : w = (-2, 4)) :
    v + w = (0, 3) ∧ w - (2 : ℝ) • v = (-6, 6) ∧ vecMag (v + w) = 3 ∧
      vecMag v + vecMag w = 3 * √5 ∧ vecMag v • w - vecMag w • v = (-6 * √5, 6 * √5) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (4, -2) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h5p : 0 < √5 := by positivity
  have mv : vecMag v = √5 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = 2 * √5 := by
    rw [hw]; unfold vecMag; simp only
    rw [show ((-2 : ℝ) ^ 2 + 4 ^ 2) = 2 ^ 2 * 5 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  subst hv hw
  refine ⟨by norm_num, by norm_num [Prod.ext_iff], ?_, by rw [mv, mw]; ring, ?_, ?_, ?_⟩
  · exact x11h_mag (by norm_num) (by norm_num)
  · rw [mv, mw]; simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> nlinarith
  · rw [mv, mw]; simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> field_simp <;> nlinarith
  · exact x11h_par _ _

/-- Stitz-Zeager Exercise 11.8.4: for `v = ⟨10, 4⟩`, `w = ⟨-2, 5⟩`: `v + w = ⟨8, 9⟩`,
`w - 2v = ⟨-22, -3⟩`, `‖v + w‖ = √145`, and the parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.4, p. 1039"]
theorem exer_11_8_4 (v w : ℝ × ℝ) (hv : v = (10, 4)) (hw : w = (-2, 5)) :
    v + w = (8, 9) ∧ w - (2 : ℝ) • v = (-22, -3) ∧ vecMag (v + w) = √145 ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  subst hv hw
  refine ⟨by norm_num, by norm_num [Prod.ext_iff], ?_, ?_⟩
  · unfold vecMag; norm_num
  · exact x11h_par _ _

/-- Stitz-Zeager Exercise 11.8.6: for `v = ⟨3/5, 4/5⟩`, `w = ⟨-4/5, 3/5⟩` (both unit vectors):
`v + w = ⟨-1/5, 7/5⟩`, `w - 2v = ⟨-2, -1⟩`, `‖v + w‖ = √2`, `‖v‖ + ‖w‖ = 2`, `‖w‖ v̂ = ⟨3/5, 4/5⟩`,
and the parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.6, p. 1039"]
theorem exer_11_8_6 (v w : ℝ × ℝ) (hv : v = (3 / 5, 4 / 5)) (hw : w = (-4 / 5, 3 / 5)) :
    v + w = (-1 / 5, 7 / 5) ∧ w - (2 : ℝ) • v = (-2, -1) ∧ vecMag (v + w) = √2 ∧
      vecMag v + vecMag w = 2 ∧ vecMag w • ((vecMag v)⁻¹ • v) = (3 / 5, 4 / 5) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have mv : vecMag v = 1 := by rw [hv]; exact x11h_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 1 := by rw [hw]; exact x11h_mag (by norm_num) (by norm_num)
  subst hv hw
  refine ⟨by norm_num [Prod.ext_iff], by norm_num [Prod.ext_iff], ?_, by rw [mv, mw]; norm_num, ?_, ?_⟩
  · unfold vecMag; norm_num
  · rw [mv, mw]; norm_num
  · exact x11h_par _ _

/-- Stitz-Zeager Exercise 11.8.11: the vector of magnitude `6` in Quadrant I at `60°` to the positive
x-axis is `⟨3, 3√3⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.11, p. 1039"]
theorem exer_11_8_11 : ((6 : ℝ) * cos (π / 3), 6 * sin (π / 3)) = (3, 3 * √3) := by
  rw [cos_pi_div_three, sin_pi_div_three]
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- Stitz-Zeager Exercise 11.8.13: the vector of magnitude `2/3` in Quadrant I at `60°` to the positive
y-axis (so at `30°` to the x-axis) is `⟨√3/3, 1/3⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.13, p. 1039"]
theorem exer_11_8_13 : ((2 / 3 : ℝ) * cos (π / 6), 2 / 3 * sin (π / 6)) = (√3 / 3, 1 / 3) := by
  rw [cos_pi_div_six, sin_pi_div_six]
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- Stitz-Zeager Exercise 11.8.15: the vector of magnitude `4` in Quadrant II at `30°` to the negative
x-axis (angle `5π/6`) is `⟨-2√3, 2⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.15, p. 1039"]
theorem exer_11_8_15 : ((4 : ℝ) * cos (5 * π / 6), 4 * sin (5 * π / 6)) = (-(2 * √3), 2) := by
  have e : 5 * π / 6 = π - π / 6 := by ring
  rw [e, cos_pi_sub, sin_pi_sub, cos_pi_div_six, sin_pi_div_six]
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- Stitz-Zeager Exercise 11.8.18: the vector of magnitude `5√6` in Quadrant III at `45°` to the negative
x-axis (angle `5π/4`) is `⟨-5√3, -5√3⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.18, p. 1039"]
theorem exer_11_8_18 :
    (5 * √6 * cos (5 * π / 4), 5 * √6 * sin (5 * π / 4)) = (-(5 * √3), -(5 * √3)) := by
  have e : 5 * π / 4 = π / 4 + π := by ring
  have h2 : √6 = √2 * √3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [e, cos_add_pi, sin_add_pi, cos_pi_div_four, sin_pi_div_four, h2]
  simp only [Prod.mk.injEq]; constructor <;> linear_combination (-5 / 2 * √3) * h22

/-- Stitz-Zeager Exercise 11.8.21: the vector of magnitude `5√2` in Quadrant IV at `45°` to the negative
y-axis (angle `7π/4`) is `⟨5, -5⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.21, p. 1040"]
theorem exer_11_8_21 : (5 * √2 * cos (7 * π / 4), 5 * √2 * sin (7 * π / 4)) = (5, -5) := by
  have e : 7 * π / 4 = -(π / 4) + 2 * π := by ring
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [e, cos_add_two_pi, sin_add_two_pi, cos_neg, sin_neg, cos_pi_div_four, sin_pi_div_four]
  simp only [Prod.mk.injEq]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.22: the vector of magnitude `2√5` in Quadrant I at angle `arctan 2` to the
positive x-axis is `⟨2, 4⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.22, p. 1040"]
theorem exer_11_8_22 : (2 * √5 * cos (arctan 2), 2 * √5 * sin (arctan 2)) = (2, 4) := by
  have h5 : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have hs : (0 : ℝ) < √5 := by positivity
  rw [Real.cos_arctan, Real.sin_arctan, h5]
  simp only [Prod.mk.injEq]; constructor <;> field_simp <;> norm_num

/-- Stitz-Zeager Exercise 11.8.24: the vector of magnitude `5` in Quadrant III at angle `arctan (4/3)` to the
negative x-axis (angle `π + arctan (4/3)`) is `⟨-3, -4⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.24, p. 1040"]
theorem exer_11_8_24 : (5 * cos (π + arctan (4 / 3)), 5 * sin (π + arctan (4 / 3))) = (-3, -4) := by
  have h5 : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show 1 + (4 / 3 : ℝ) ^ 2 = (5 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [add_comm π, cos_add_pi, sin_add_pi, Real.cos_arctan, Real.sin_arctan, h5]
  simp only [Prod.mk.injEq]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 11.8.34: the vector `⟨-2√3, 2⟩` has `‖v‖ = 4` and, among `r ≥ 0`, `0 ≤ θ < 2π`
with `v = ⟨r cos θ, r sin θ⟩`, exactly `θ = 5π/6` (`150°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.34, p. 1040"]
theorem exer_11_8_34 :
    vecMag (-(2 * √3), 2) = 4 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-(2 * √3), 2) ↔ r = 4 ∧ θ = 5 * π / 6) := by
  have hp := pi_pos
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨x11h_mag (by norm_num) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e0 : 5 * π / 6 = π - π / 6 := by ring
  have e : (-(2 * √3), (2 : ℝ)) = polarPoint 4 (5 * π / 6) := by
    simp only [polarPoint, e0, cos_pi_sub, sin_pi_sub, cos_pi_div_six, sin_pi_div_six, Prod.mk.injEq]
    constructor <;> ring
  rw [e, x11h_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.42: the vector `⟨3, 4⟩` has `‖v‖ = 5` and, among `r ≥ 0`, `0 ≤ θ < 2π` with
`v = ⟨r cos θ, r sin θ⟩`, exactly `θ = arctan (4/3)` (about `53.13°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.42, p. 1040"]
theorem exer_11_8_42 :
    vecMag (3, 4) = 5 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (3, 4) ↔ r = 5 ∧ θ = arctan (4 / 3)) := by
  have hp := pi_pos
  refine ⟨x11h_mag (by norm_num) (by norm_num), fun r θ hr hθ hθ2 => ?_⟩
  have h5 : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show 1 + (4 / 3 : ℝ) ^ 2 = (5 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e : ((3 : ℝ), 4) = polarPoint 5 (arctan (4 / 3)) := by
    simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 ≤ arctan (4 / 3) := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two (4 / 3)
  rw [e, x11h_conv (by norm_num) h0 (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.45: the vector `⟨-7, 24⟩` has `‖v‖ = 25` and, among `r ≥ 0`, `0 ≤ θ < 2π` with
`v = ⟨r cos θ, r sin θ⟩`, exactly `θ = π - arctan (24/7)` (about `106.26°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.45, p. 1041"]
theorem exer_11_8_45 :
    vecMag (-7, 24) = 25 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-7, 24) ↔ r = 25 ∧ θ = π - arctan (24 / 7)) := by
  have hp := pi_pos
  refine ⟨x11h_mag (by norm_num) (by norm_num), fun r θ hr hθ hθ2 => ?_⟩
  have h5 : √(1 + (24 / 7 : ℝ) ^ 2) = 25 / 7 := by
    rw [show 1 + (24 / 7 : ℝ) ^ 2 = (25 / 7) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e : ((-7 : ℝ), 24) = polarPoint 25 (π - arctan (24 / 7)) := by
    simp only [polarPoint, cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 < arctan (24 / 7) := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two (24 / 7)
  rw [e, x11h_conv (by norm_num) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.58: a `600` lb statue hung from two cables at `60°` to the ceiling: the
tensions `T₁, T₂` balance the weight exactly when both equal `200√3` (about `346` lb). -/
@[kb "stitzzeager2013" "Exercise 11.8.58, p. 1041"]
theorem exer_11_8_58 (T₁ T₂ : ℝ) :
    (T₁ * (-cos (π / 3)) + T₂ * cos (π / 3) = 0 ∧ T₁ * sin (π / 3) + T₂ * sin (π / 3) = 600) ↔
      T₁ = 200 * √3 ∧ T₂ = 200 * √3 ∧ 346 < 200 * √3 ∧ 200 * √3 < 347 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < √3 := by positivity
  have hb1 : (1.7300 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hb2 : √3 < 1.7350 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [cos_pi_div_three, sin_pi_div_three]
  constructor
  · rintro ⟨h1, h2⟩
    have e : T₁ = T₂ := by linarith
    subst e
    have : T₁ * √3 = 600 := by linarith
    have hT : T₁ = 200 * √3 := by nlinarith
    refine ⟨hT, hT, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, -, -⟩
    constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.60: a `300` lb star on cables at `72°` (left) and `18°` (right) to the ceiling:
the tensions balance exactly when the left tension is `300 cos 18°` (about `285.317`) and the right one is
`300 sin 18°` (about `92.705`). -/
@[kb "stitzzeager2013" "Exercise 11.8.60, p. 1042"]
theorem exer_11_8_60 (T₁ T₂ : ℝ) :
    (T₁ * (-cos (2 * π / 5)) + T₂ * cos (π / 10) = 0 ∧
        T₁ * sin (2 * π / 5) + T₂ * sin (π / 10) = 300) ↔
      T₁ = 300 * cos (π / 10) ∧ T₂ = 300 * sin (π / 10) := by
  have e1 : cos (2 * π / 5) = sin (π / 10) := by
    rw [← cos_pi_div_two_sub]; congr 1; ring
  have e2 : sin (2 * π / 5) = cos (π / 10) := by
    rw [← sin_pi_div_two_sub]; congr 1; ring
  have hcs := sin_sq_add_cos_sq (π / 10)
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · linear_combination cos (π / 10) * h2 - sin (π / 10) * h1 - T₁ * hcs
    · linear_combination sin (π / 10) * h2 + cos (π / 10) * h1 - T₂ * hcs
  · rintro ⟨rfl, rfl⟩
    constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.63: for every nonzero vector `v`, the vector `(1/‖v‖) v` has length `1`. -/
@[kb "stitzzeager2013" "Exercise 11.8.63, p. 1042"]
theorem exer_11_8_63 (v : ℝ × ℝ) (hv : v ≠ 0) : vecMag ((vecMag v)⁻¹ • v) = 1 := by
  have hp : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    rcases Classical.em (v.1 = 0) with h1 | h1
    · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
      positivity
    · positivity
  have hm : 0 < vecMag v := Real.sqrt_pos.mpr hp
  have hm2 := x11h_sq v
  unfold vecMag at hm hm2 ⊢
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hm2 ⊢
  rw [Real.sqrt_eq_one]
  field_simp
  nlinarith

/-- Stitz-Zeager Exercise 11.8.65: the line `y = m x + b` is exactly the set of terminal points of
`⟨0, b⟩ + t ⟨1, m⟩`, `t ∈ ℝ`. -/
@[kb "stitzzeager2013" "Exercise 11.8.65, p. 1042"]
theorem exer_11_8_65 (m b : ℝ) :
    {p : ℝ × ℝ | p.2 = m * p.1 + b} = {p | ∃ t : ℝ, p = (0, b) + t • (1, m)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨x, by simp, by rw [h]; ring⟩
  · rintro ⟨t, h1, h2⟩
    have : x = t := by linarith
    subst this
    linarith

/-- Stitz-Zeager Exercise 11.8.67: the properties of scalar multiplication of plane vectors:
`(k + l)v = kv + lv`, `k(v + w) = kv + kw`, `(kl)v = k(lv)`, `1v = v`, `0v = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.8.67, p. 1042"]
theorem exer_11_8_67 (k l : ℝ) (v w : ℝ × ℝ) :
    (k + l) • v = k • v + l • v ∧ k • (v + w) = k • v + k • w ∧ (k * l) • v = k • l • v ∧
      (1 : ℝ) • v = v ∧ (0 : ℝ) • v = 0 :=
  ⟨add_smul k l v, smul_add k v w, mul_smul k l v, one_smul ℝ v, zero_smul ℝ v⟩

/-! ## Section 11.9 -/

/-- Stitz-Zeager Exercise 11.9.1: for `v = ⟨-2, -7⟩`, `w = ⟨5, -9⟩`: `v · w = 53`, the angle between them
is `45°`, `proj_w v = ⟨5/2, -9/2⟩`, and `q = v - proj_w v` satisfies `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.1, p. 1055"]
theorem exer_11_9_1 (v w : ℝ × ℝ) (hv : v = (-2, -7)) (hw : w = (5, -9)) :
    dotProd2 v w = 53 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = π / 4 ∧
      vecProj v w = (5 / 2, -9 / 2) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = √53 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = √2 * √53 := by
    rw [hw]; unfold vecMag; simp only
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h53 : √53 * √53 = 53 := Real.mul_self_sqrt (by norm_num)
  have hd : dotProd2 v w = 53 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (5 / 2, -9 / 2) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]
    have hs : (0 : ℝ) < √53 := by positivity
    have key : √2 * (√53 * (√2 * √53)) = 106 := by
      calc _ = (√2 * √2) * (√53 * √53) := by ring
        _ = 106 := by rw [h2, h53]; norm_num
    have e : (53 : ℝ) / (√53 * (√2 * √53)) = cos (π / 4) := by
      rw [cos_pi_div_four, div_eq_div_iff (by positivity) (by norm_num)]
      linarith
    rw [e]
    exact arccos_cos (by positivity) (by linarith [pi_pos])
  · rw [hproj, hv, hw]; unfold dotProd2; norm_num

/-- Stitz-Zeager Exercise 11.9.2: for `v = ⟨-6, -5⟩`, `w = ⟨10, -12⟩`: `v · w = 0`, the angle is `90°`,
`proj_w v = 0`, and `q = v`. -/
@[kb "stitzzeager2013" "Exercise 11.9.2, p. 1055"]
theorem exer_11_9_2 (v w : ℝ × ℝ) (hv : v = (-6, -5)) (hw : w = (10, -12)) :
    dotProd2 v w = 0 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = π / 2 ∧
      vecProj v w = (0, 0) ∧ v - vecProj v w = v := by
  have hd : dotProd2 v w = 0 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = 0 := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [hd, zero_div, arccos_zero]
  · rw [hproj]; rfl
  · rw [hproj, sub_zero]

/-- Stitz-Zeager Exercise 11.9.3: for `v = ⟨1, √3⟩`, `w = ⟨1, -√3⟩`: `v · w = -2`, the angle is `120°`,
`proj_w v = ⟨-1/2, √3/2⟩`, and `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.3, p. 1055"]
theorem exer_11_9_3 (v w : ℝ × ℝ) (hv : v = (1, √3)) (hw : w = (1, -√3)) :
    dotProd2 v w = -2 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = 2 * π / 3 ∧
      vecProj v w = (-1 / 2, √3 / 2) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 2 := by
    rw [hv]; exact x11h_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 2 := by
    rw [hw]; exact x11h_mag (by norm_num) (by nlinarith)
  have hd : dotProd2 v w = -2 := by rw [hv, hw]; unfold dotProd2; simp only; nlinarith
  have hproj : vecProj v w = (-1 / 2, √3 / 2) := by
    rw [hv, hw]; unfold vecProj dotProd2; simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    have : (1 : ℝ) * 1 + √3 * -√3 = -2 := by nlinarith
    have h4 : (1 : ℝ) * 1 + -√3 * -√3 = 4 := by nlinarith
    rw [this, h4]
    constructor <;> nlinarith
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, show (-2 : ℝ) / (2 * 2) = -(1 / 2) by norm_num]
    have : 2 * π / 3 = π - π / 3 := by ring
    rw [this, ← cos_pi_div_three, ← cos_pi_sub]
    exact arccos_cos (by linarith [pi_pos]) (by linarith [pi_pos])
  · rw [hproj, hv, hw]; unfold dotProd2
    simp only [Prod.fst_sub, Prod.snd_sub]
    nlinarith

/-- Stitz-Zeager Exercise 11.9.4: for `v = ⟨3, 4⟩`, `w = ⟨-6, -8⟩`: `v · w = -50`, the angle is `180°`,
`proj_w v = v`, and `q = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.4, p. 1055"]
theorem exer_11_9_4 (v w : ℝ × ℝ) (hv : v = (3, 4)) (hw : w = (-6, -8)) :
    dotProd2 v w = -50 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = π ∧
      vecProj v w = (3, 4) ∧ v - vecProj v w = 0 := by
  have mv : vecMag v = 5 := by rw [hv]; exact x11h_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 10 := by rw [hw]; exact x11h_mag (by norm_num) (by norm_num)
  have hd : dotProd2 v w = -50 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (3, 4) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, show (-50 : ℝ) / (5 * 10) = -1 by norm_num, arccos_neg_one]
  · rw [hproj, hv]; simp

/-- Stitz-Zeager Exercise 11.9.8: for `v = ⟨3, 4⟩`, `w = ⟨5, 12⟩`: `v · w = 63`, the angle is `arccos (63/65)`
(about `14.25°`), `proj_w v = ⟨315/169, 756/169⟩`, and `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.8, p. 1055"]
theorem exer_11_9_8 (v w : ℝ × ℝ) (hv : v = (3, 4)) (hw : w = (5, 12)) :
    dotProd2 v w = 63 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (63 / 65) ∧
      vecProj v w = (315 / 169, 756 / 169) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have mv : vecMag v = 5 := by rw [hv]; exact x11h_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 13 := by rw [hw]; exact x11h_mag (by norm_num) (by norm_num)
  have hd : dotProd2 v w = 63 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (315 / 169, 756 / 169) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]; norm_num
  · rw [hproj, hv, hw]; unfold dotProd2; norm_num

/-- Stitz-Zeager Exercise 11.9.14: for `v = -24 i + 7 j = ⟨-24, 7⟩`, `w = 2 i = ⟨2, 0⟩`: `v · w = -48`,
the angle is `arccos (-24/25)` (about `163.74°`), `proj_w v = ⟨-24, 0⟩`, and `q = ⟨0, 7⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.9.14, p. 1055"]
theorem exer_11_9_14 (v w : ℝ × ℝ) (hv : v = (-24, 7)) (hw : w = (2, 0)) :
    dotProd2 v w = -48 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (-24 / 25) ∧
      vecProj v w = (-24, 0) ∧ v - vecProj v w = (0, 7) := by
  have mv : vecMag v = 25 := by rw [hv]; exact x11h_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 2 := by rw [hw]; exact x11h_mag (by norm_num) (by norm_num)
  have hd : dotProd2 v w = -48 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (-24, 0) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]; norm_num
  · rw [hproj, hv]; norm_num [Prod.ext_iff]

/-- Stitz-Zeager Exercise 11.9.16: for `v = ⟨5, 12⟩`, `w = ⟨-3, 4⟩`: `v · w = 33`, the angle is
`arccos (33/65)` (about `59.49°`), `proj_w v = ⟨-99/25, 132/25⟩`, and `q = ⟨224/25, 168/25⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.9.16, p. 1055"]
theorem exer_11_9_16 (v w : ℝ × ℝ) (hv : v = (5, 12)) (hw : w = (-3, 4)) :
    dotProd2 v w = 33 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (33 / 65) ∧
      vecProj v w = (-99 / 25, 132 / 25) ∧ v - vecProj v w = (224 / 25, 168 / 25) := by
  have mv : vecMag v = 13 := by rw [hv]; exact x11h_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 5 := by rw [hw]; exact x11h_mag (by norm_num) (by norm_num)
  have hd : dotProd2 v w = 33 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (-99 / 25, 132 / 25) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]; norm_num
  · rw [hproj, hv]; norm_num [Prod.ext_iff]

/-- Stitz-Zeager Exercise 11.9.20: for `v = ⟨1/2, -√3/2⟩`, `w = ⟨√2/2, -√2/2⟩` (unit vectors): the dot product
is `(√2 + √2√3)/4 = cos 15°`, so the angle is `15°`. -/
@[kb "stitzzeager2013" "Exercise 11.9.20, p. 1055"]
theorem exer_11_9_20 (v w : ℝ × ℝ) (hv : v = (1 / 2, -(√3 / 2))) (hw : w = (√2 / 2, -(√2 / 2))) :
    dotProd2 v w = (√2 + √2 * √3) / 4 ∧
      arccos (dotProd2 v w / (vecMag v * vecMag w)) = π / 12 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 1 := by rw [hv]; exact x11h_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 1 := by rw [hw]; exact x11h_mag (by norm_num) (by nlinarith)
  have hd : dotProd2 v w = (√2 + √2 * √3) / 4 := by
    rw [hv, hw]; unfold dotProd2; simp only; ring
  refine ⟨hd, ?_⟩
  rw [hd, mv, mw, mul_one, div_one]
  have e : π / 12 = π / 3 - π / 4 := by ring
  have hc : cos (π / 12) = (√2 + √2 * √3) / 4 := by
    rw [e, cos_sub, cos_pi_div_three, sin_pi_div_three, cos_pi_div_four, sin_pi_div_four]; ring
  rw [← hc]
  exact arccos_cos (by positivity) (by linarith [pi_pos])

/-- Stitz-Zeager Exercise 11.9.21: towing a trailer with a `1500` lb force along `300` ft in the direction of
motion does `450 000` ft-lb of work. -/
@[kb "stitzzeager2013" "Exercise 11.9.21, p. 1055"]
theorem exer_11_9_21 : dotProd2 (1500, 0) (300, 0) = 450000 := by
  unfold dotProd2; norm_num

/-- Stitz-Zeager Exercise 11.9.22: lifting a `10` lb book `3` ft straight up does `30` ft-lb of work. -/
@[kb "stitzzeager2013" "Exercise 11.9.22, p. 1055"]
theorem exer_11_9_22 : dotProd2 (0, 10) (0, 3) = 30 := by
  unfold dotProd2; norm_num

/-- Stitz-Zeager Exercise 11.9.23: pulling a wagon `25` ft with a `13` lb force at `15°` does
`325 cos 15° = 325(√2 + √2√3)/4`, about `313.93` ft-lb (`313.925 < W < 313.927`; ERRATUM: book says `313.92`, correct is `313.93`). -/
@[kb "stitzzeager2013" "Exercise 11.9.23, p. 1055"]
theorem exer_11_9_23 :
    13 * 25 * cos (π / 12) = 325 * (√2 + √2 * √3) / 4 ∧
      313.925 < 325 * (√2 + √2 * √3) / 4 ∧ 325 * (√2 + √2 * √3) / 4 < 313.927 := by
  have e : π / 12 = π / 3 - π / 4 := by ring
  have h2a : (1.4142135 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2b : √2 < 1.4142136 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3a : (1.7320508 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3b : √3 < 1.7320509 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hp1 : √2 * √3 < 1.4142136 * 1.7320509 := mul_lt_mul'' h2b h3b (by positivity) (by positivity)
  have hp2 : 1.4142135 * 1.7320508 < √2 * √3 := mul_lt_mul'' h2a h3a (by norm_num) (by norm_num)
  refine ⟨?_, by linarith, by linarith⟩
  rw [e, cos_sub, cos_pi_div_three, sin_pi_div_three, cos_pi_div_four, sin_pi_div_four]; ring

/-- Stitz-Zeager Exercise 11.9.28: the parallelogram law `‖v‖² + ‖w‖² = (‖v + w‖² + ‖v - w‖²)/2`. -/
@[kb "stitzzeager2013" "Exercise 11.9.28, p. 1056"]
theorem exer_11_9_28 (v w : ℝ × ℝ) :
    vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  rw [x11h_sq, x11h_sq, x11h_sq, x11h_sq]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Stitz-Zeager Exercise 11.9.29: the Cauchy-Schwarz inequality `|u · v| ≤ ‖u‖‖v‖` and the triangle
inequality `‖u + v‖ ≤ ‖u‖ + ‖v‖` for plane vectors. -/
@[kb "stitzzeager2013" "Exercise 11.9.29, p. 1056"]
theorem exer_11_9_29 (u v : ℝ × ℝ) :
    |dotProd2 u v| ≤ vecMag u * vecMag v ∧ vecMag (u + v) ≤ vecMag u + vecMag v := by
  have hcs : |dotProd2 u v| ≤ vecMag u * vecMag v := by
    have h : (dotProd2 u v) ^ 2 ≤ (u.1 ^ 2 + u.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2) := by
      unfold dotProd2; nlinarith [sq_nonneg (u.1 * v.2 - u.2 * v.1)]
    unfold vecMag
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.abs_le_sqrt h
  refine ⟨hcs, ?_⟩
  have hu := x11h_sq u
  have hv := x11h_sq v
  have huv := x11h_sq (u + v)
  have h1 : 0 ≤ vecMag u := Real.sqrt_nonneg _
  have h2 : 0 ≤ vecMag v := Real.sqrt_nonneg _
  apply le_of_sq_le_sq _ (by positivity)
  · rw [huv]
    simp only [Prod.fst_add, Prod.snd_add]
    have h3 : dotProd2 u v ≤ vecMag u * vecMag v := (le_abs_self _).trans hcs
    unfold dotProd2 at h3
    nlinarith [h3, hu, hv]

end UndergradKB.Precalculus.Course
