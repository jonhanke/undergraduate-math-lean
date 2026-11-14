import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Vectors
import UndergradKB.Precalculus.PolarComplex
import UndergradKB.Precalculus.Course.Ch11ExerH

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.8

Plane vectors are pairs `ℝ × ℝ`; `vecMag` is the magnitude. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Helpers -/

private theorem w8_mag {a b c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 + b ^ 2 = c ^ 2) : vecMag (a, b) = c := by
  unfold vecMag; simp only; rw [h, Real.sqrt_sq hc]

private theorem w8_sq (p : ℝ × ℝ) : vecMag p ^ 2 = p.1 ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem w8_par (v w : ℝ × ℝ) :
    vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  rw [w8_sq, w8_sq, w8_sq, w8_sq]
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Uniqueness of the polar name with `r ≥ 0` and `0 ≤ θ < 2π` of a point other than the origin. -/
private theorem w8_conv {r r' θ θ' : ℝ} (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ < 2 * π)
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

private theorem w8_q1 (x y : ℝ) (hx : 0 < x) :
    polarPoint (√(x ^ 2 + y ^ 2)) (arctan (y / x)) = (x, y) := by
  have hR : 0 < √(x ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ x ^ 2 + y ^ 2 by positivity)
  have h1 : √(1 + (y / x) ^ 2) = √(x ^ 2 + y ^ 2) / x := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    nlinarith
  simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h1, Prod.mk.injEq]
  constructor <;> field_simp

private theorem w8_q2 (x y : ℝ) (hx : 0 < x) :
    polarPoint (√(x ^ 2 + y ^ 2)) (π - arctan (y / x)) = (-x, y) := by
  have := w8_q1 x y hx
  simp only [polarPoint, Prod.mk.injEq] at this ⊢
  rw [cos_pi_sub, sin_pi_sub]
  constructor
  · rw [mul_neg, this.1]
  · exact this.2

private theorem w8_q4 (x y : ℝ) (hx : 0 < x) :
    polarPoint (√(x ^ 2 + y ^ 2)) (2 * π - arctan (y / x)) = (x, -y) := by
  have := w8_q1 x y hx
  simp only [polarPoint, Prod.mk.injEq] at this ⊢
  rw [cos_two_pi_sub, sin_two_pi_sub]
  constructor
  · exact this.1
  · rw [mul_neg, this.2]

/-! ## Section 11.8: vector arithmetic -/

/-- Stitz-Zeager Exercise 11.8.5: for `v = ⟨-√3, 1⟩`, `w = ⟨2√3, 2⟩`: `v + w = ⟨√3, 3⟩`,
`w - 2v = ⟨4√3, 0⟩`, `‖v + w‖ = 2√3`, `‖v‖ + ‖w‖ = 6`, `‖v‖w - ‖w‖v = ⟨8√3, 0⟩`, `‖w‖ v̂ = ⟨-2√3, 2⟩`,
and the parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.5, p. 1039"]
theorem exer_11_8_5 (v w : ℝ × ℝ) (hv : v = (-√3, 1)) (hw : w = (2 * √3, 2)) :
    v + w = (√3, 3) ∧ w - (2 : ℝ) • v = (4 * √3, 0) ∧ vecMag (v + w) = 2 * √3 ∧
      vecMag v + vecMag w = 6 ∧ vecMag v • w - vecMag w • v = (8 * √3, 0) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (-(2 * √3), 2) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 2 := by rw [hv]; exact w8_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 4 := by rw [hw]; exact w8_mag (by norm_num) (by nlinarith)
  subst hv hw
  refine ⟨by simp only [Prod.mk_add_mk]; ext <;> simp <;> ring, ?_, ?_, by rw [mv, mw]; norm_num, ?_, ?_, ?_⟩
  · simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]; constructor <;> ring
  · simp only [Prod.mk_add_mk]
    exact w8_mag (by positivity) (by nlinarith)
  · rw [mv, mw]; simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  · rw [mv, mw]; simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  · exact w8_par _ _

/-- Stitz-Zeager Exercise 11.8.7: for `v = ⟨√2/2, -√2/2⟩`, `w = ⟨-√2/2, √2/2⟩`: `v + w = 0`,
`w - 2v = ⟨-3√2/2, 3√2/2⟩`, `‖v + w‖ = 0`, `‖v‖ + ‖w‖ = 2`, `‖v‖w - ‖w‖v = ⟨-√2, √2⟩`,
`‖w‖ v̂ = ⟨√2/2, -√2/2⟩`, and the parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.7, p. 1039"]
theorem exer_11_8_7 (v w : ℝ × ℝ) (hv : v = (√2 / 2, -(√2 / 2))) (hw : w = (-(√2 / 2), √2 / 2)) :
    v + w = (0, 0) ∧ w - (2 : ℝ) • v = (-(3 * √2 / 2), 3 * √2 / 2) ∧ vecMag (v + w) = 0 ∧
      vecMag v + vecMag w = 2 ∧ vecMag v • w - vecMag w • v = (-√2, √2) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (√2 / 2, -(√2 / 2)) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 1 := by rw [hv]; exact w8_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 1 := by rw [hw]; exact w8_mag (by norm_num) (by nlinarith)
  subst hv hw
  refine ⟨by simp only [Prod.mk_add_mk]; ext <;> simp, ?_, ?_, by rw [mv, mw]; norm_num, ?_, ?_, ?_⟩
  · simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]; constructor <;> ring
  · simp only [Prod.mk_add_mk]
    exact w8_mag (by norm_num) (by nlinarith)
  · rw [mv, mw]; simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  · rw [mv, mw]; simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq, inv_one]
    constructor <;> ring
  · exact w8_par _ _

/-- Stitz-Zeager Exercise 11.8.8: for `v = ⟨1/2, √3/2⟩`, `w = ⟨-1, -√3⟩`: `v + w = ⟨-1/2, -√3/2⟩`,
`w - 2v = ⟨-2, -2√3⟩`, `‖v + w‖ = 1`, `‖v‖ + ‖w‖ = 3`, `‖v‖w - ‖w‖v = ⟨-2, -2√3⟩`, `‖w‖ v̂ = ⟨1, √3⟩`,
and the parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.8, p. 1039"]
theorem exer_11_8_8 (v w : ℝ × ℝ) (hv : v = (1 / 2, √3 / 2)) (hw : w = (-1, -√3)) :
    v + w = (-(1 / 2), -(√3 / 2)) ∧ w - (2 : ℝ) • v = (-2, -(2 * √3)) ∧ vecMag (v + w) = 1 ∧
      vecMag v + vecMag w = 3 ∧ vecMag v • w - vecMag w • v = (-2, -(2 * √3)) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (1, √3) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 1 := by rw [hv]; exact w8_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 2 := by rw [hw]; exact w8_mag (by norm_num) (by nlinarith)
  subst hv hw
  refine ⟨by simp only [Prod.mk_add_mk]; ext <;> simp <;> ring, ?_, ?_, by rw [mv, mw]; norm_num, ?_, ?_, ?_⟩
  · simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]; constructor <;> ring
  · simp only [Prod.mk_add_mk]
    exact w8_mag (by norm_num) (by nlinarith)
  · rw [mv, mw]; simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  · rw [mv, mw]; simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq, inv_one]
    constructor <;> ring
  · exact w8_par _ _

/-- Stitz-Zeager Exercise 11.8.9: for `v = 3i + 4j`, `w = -2j`: `v + w = ⟨3, 2⟩`, `w - 2v = ⟨-6, -10⟩`,
`‖v + w‖ = √13`, `‖v‖ + ‖w‖ = 7`, `‖v‖w - ‖w‖v = ⟨-6, -18⟩`, `‖w‖ v̂ = ⟨6/5, 8/5⟩`, and the parallelogram
law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.9, p. 1039"]
theorem exer_11_8_9 (v w : ℝ × ℝ) (hv : v = (3, 4)) (hw : w = (0, -2)) :
    v + w = (3, 2) ∧ w - (2 : ℝ) • v = (-6, -10) ∧ vecMag (v + w) = √13 ∧
      vecMag v + vecMag w = 7 ∧ vecMag v • w - vecMag w • v = (-6, -18) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (6 / 5, 8 / 5) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have mv : vecMag v = 5 := by rw [hv]; exact w8_mag (by norm_num) (by norm_num)
  have mw : vecMag w = 2 := by rw [hw]; exact w8_mag (by norm_num) (by norm_num)
  subst hv hw
  refine ⟨by norm_num [Prod.ext_iff], by norm_num [Prod.ext_iff], ?_, by rw [mv, mw]; norm_num, ?_, ?_, ?_⟩
  · unfold vecMag; norm_num
  · rw [mv, mw]; norm_num [Prod.ext_iff]
  · rw [mv, mw]; norm_num [Prod.ext_iff]
  · exact w8_par _ _

/-- Stitz-Zeager Exercise 11.8.10: for `v = (i + j)/2`, `w = (i - j)/2`: `v + w = ⟨1, 0⟩`,
`w - 2v = ⟨-1/2, -3/2⟩`, `‖v + w‖ = 1`, `‖v‖ + ‖w‖ = √2`, `‖v‖w - ‖w‖v = ⟨0, -√2/2⟩`, `‖w‖ v̂ = ⟨1/2, 1/2⟩`,
and the parallelogram law holds. -/
@[kb "stitzzeager2013" "Exercise 11.8.10, p. 1039"]
theorem exer_11_8_10 (v w : ℝ × ℝ) (hv : v = (1 / 2, 1 / 2)) (hw : w = (1 / 2, -(1 / 2))) :
    v + w = (1, 0) ∧ w - (2 : ℝ) • v = (-(1 / 2), -(3 / 2)) ∧ vecMag (v + w) = 1 ∧
      vecMag v + vecMag w = √2 ∧ vecMag v • w - vecMag w • v = (0, -(√2 / 2)) ∧
      vecMag w • ((vecMag v)⁻¹ • v) = (1 / 2, 1 / 2) ∧
      vecMag v ^ 2 + vecMag w ^ 2 = (vecMag (v + w) ^ 2 + vecMag (v - w) ^ 2) / 2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  have mv : vecMag v = √2 / 2 := by rw [hv]; exact w8_mag (by positivity) (by nlinarith)
  have mw : vecMag w = √2 / 2 := by rw [hw]; exact w8_mag (by positivity) (by nlinarith)
  subst hv hw
  refine ⟨by norm_num [Prod.ext_iff], by norm_num [Prod.ext_iff], ?_, by rw [mv, mw]; ring, ?_, ?_, ?_⟩
  · simp only [Prod.mk_add_mk]
    exact w8_mag (by norm_num) (by norm_num)
  · rw [mv, mw]; simp only [Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> ring
  · rw [mv, mw]; simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor <;> field_simp
  · exact w8_par _ _

/-! ## Section 11.8: component form from magnitude and direction -/

/-- Stitz-Zeager Exercise 11.8.12: the vector of magnitude `3` in Quadrant I at `45°` is `⟨3√2/2, 3√2/2⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.12, p. 1039"]
theorem exer_11_8_12 : ((3 : ℝ) * cos (π / 4), 3 * sin (π / 4)) = (3 * √2 / 2, 3 * √2 / 2) := by
  rw [cos_pi_div_four, sin_pi_div_four]
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- Stitz-Zeager Exercise 11.8.14: the vector of magnitude `12` along the positive y-axis is `⟨0, 12⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.14, p. 1039"]
theorem exer_11_8_14 : ((12 : ℝ) * cos (π / 2), 12 * sin (π / 2)) = (0, 12) := by
  rw [cos_pi_div_two, sin_pi_div_two]
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- Stitz-Zeager Exercise 11.8.16: the vector of magnitude `2√3` in Quadrant II at `30°` to the positive
y-axis (angle `2π/3`) is `⟨-√3, 3⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.16, p. 1039"]
theorem exer_11_8_16 : (2 * √3 * cos (2 * π / 3), 2 * √3 * sin (2 * π / 3)) = (-√3, 3) := by
  have e : 2 * π / 3 = π - π / 3 := by ring
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [e, cos_pi_sub, sin_pi_sub, cos_pi_div_three, sin_pi_div_three]
  simp only [Prod.mk.injEq]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.17: the vector of magnitude `7/2` along the negative x-axis is `⟨-7/2, 0⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.17, p. 1039"]
theorem exer_11_8_17 : ((7 / 2 : ℝ) * cos π, 7 / 2 * sin π) = (-(7 / 2), 0) := by
  rw [cos_pi, sin_pi]
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- Stitz-Zeager Exercise 11.8.19: the vector of magnitude `6.25` along the negative y-axis is `⟨0, -6.25⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.19, p. 1039"]
theorem exer_11_8_19 : ((6.25 : ℝ) * cos (3 * π / 2), 6.25 * sin (3 * π / 2)) = (0, -6.25) := by
  have e : 3 * π / 2 = π / 2 + π := by ring
  rw [e, cos_add_pi, sin_add_pi, cos_pi_div_two, sin_pi_div_two]
  simp only [Prod.mk.injEq]; constructor <;> ring

/-- Stitz-Zeager Exercise 11.8.20: the vector of magnitude `4√3` in Quadrant IV at `30°` to the positive
x-axis (angle `-π/6`) is `⟨6, -2√3⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.20, p. 1040"]
theorem exer_11_8_20 : (4 * √3 * cos (-(π / 6)), 4 * √3 * sin (-(π / 6))) = (6, -(2 * √3)) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [cos_neg, sin_neg, cos_pi_div_six, sin_pi_div_six]
  simp only [Prod.mk.injEq]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.23: the vector of magnitude `√10` in Quadrant II at angle `arctan 3` to the
negative x-axis (angle `π - arctan 3`) is `⟨-1, 3⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.23, p. 1040"]
theorem exer_11_8_23 : (√10 * cos (π - arctan 3), √10 * sin (π - arctan 3)) = (-1, 3) := by
  have h5 : √(1 + (3 : ℝ) ^ 2) = √10 := by norm_num
  have hs : (0 : ℝ) < √10 := by positivity
  have hss : √10 * √10 = 10 := Real.mul_self_sqrt (by norm_num)
  rw [cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5]
  simp only [Prod.mk.injEq]; constructor <;> field_simp <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.25: the vector of magnitude `26` in Quadrant IV at angle `arctan (5/12)` to the
positive x-axis (angle `-arctan (5/12)`) is `⟨24, -10⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.8.25, p. 1040"]
theorem exer_11_8_25 : (26 * cos (-arctan (5 / 12)), 26 * sin (-arctan (5 / 12))) = (24, -10) := by
  have h5 : √(1 + (5 / 12 : ℝ) ^ 2) = 13 / 12 := by
    rw [show 1 + (5 / 12 : ℝ) ^ 2 = (13 / 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [cos_neg, sin_neg, Real.cos_arctan, Real.sin_arctan, h5]
  simp only [Prod.mk.injEq]; constructor <;> norm_num

/-! ## Section 11.8: magnitude and direction angle -/

/-- Stitz-Zeager Exercise 11.8.32: the vector `⟨1, √3⟩` has `‖v‖ = 2` and, among `r ≥ 0`, `0 ≤ θ < 2π`
with `v = ⟨r cos θ, r sin θ⟩`, exactly `θ = π/3` (`60°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.32, p. 1040"]
theorem exer_11_8_32 :
    vecMag (1, √3) = 2 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (1, √3) ↔ r = 2 ∧ θ = π / 3) := by
  have hp := pi_pos
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨w8_mag (by norm_num) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((1 : ℝ), √3) = polarPoint 2 (π / 3) := by
    simp only [polarPoint, cos_pi_div_three, sin_pi_div_three, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w8_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.33: the vector `⟨5, 5⟩` has `‖v‖ = 5√2` and exactly `θ = π/4` (`45°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.33, p. 1040"]
theorem exer_11_8_33 :
    vecMag (5, 5) = 5 * √2 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (5, 5) ↔ r = 5 * √2 ∧ θ = π / 4) := by
  have hp := pi_pos
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < √2 := by positivity
  refine ⟨w8_mag (by positivity) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((5 : ℝ), 5) = polarPoint (5 * √2) (π / 4) := by
    simp only [polarPoint, cos_pi_div_four, sin_pi_div_four, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e, w8_conv (by positivity) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.35: the vector `⟨-√2, √2⟩` has `‖v‖ = 2` and exactly `θ = 3π/4` (`135°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.35, p. 1040"]
theorem exer_11_8_35 :
    vecMag (-√2, √2) = 2 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-√2, √2) ↔ r = 2 ∧ θ = 3 * π / 4) := by
  have hp := pi_pos
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨w8_mag (by norm_num) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((-√2 : ℝ), √2) = polarPoint 2 (3 * π / 4) := by
    have : 3 * π / 4 = π - π / 4 := by ring
    simp only [polarPoint, this, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e, w8_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.36: the vector `⟨-√2/2, -√2/2⟩` has `‖v‖ = 1` and exactly `θ = 5π/4`
(`225°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.36, p. 1040"]
theorem exer_11_8_36 :
    vecMag (-(√2 / 2), -(√2 / 2)) = 1 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-(√2 / 2), -(√2 / 2)) ↔ r = 1 ∧ θ = 5 * π / 4) := by
  have hp := pi_pos
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨w8_mag (by norm_num) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((-(√2 / 2) : ℝ), -(√2 / 2)) = polarPoint 1 (5 * π / 4) := by
    have : 5 * π / 4 = π / 4 + π := by ring
    simp only [polarPoint, this, cos_add_pi, sin_add_pi, cos_pi_div_four, sin_pi_div_four, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w8_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.37: the vector `⟨-1/2, -√3/2⟩` has `‖v‖ = 1` and exactly `θ = 4π/3`
(`240°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.37, p. 1040"]
theorem exer_11_8_37 :
    vecMag (-(1 / 2), -(√3 / 2)) = 1 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-(1 / 2), -(√3 / 2)) ↔ r = 1 ∧ θ = 4 * π / 3) := by
  have hp := pi_pos
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨w8_mag (by norm_num) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((-(1 / 2) : ℝ), -(√3 / 2)) = polarPoint 1 (4 * π / 3) := by
    have : 4 * π / 3 = π / 3 + π := by ring
    simp only [polarPoint, this, cos_add_pi, sin_add_pi, cos_pi_div_three, sin_pi_div_three, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w8_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.38: the vector `⟨6, 0⟩` has `‖v‖ = 6` and exactly `θ = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.8.38, p. 1040"]
theorem exer_11_8_38 :
    vecMag (6, 0) = 6 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (6, 0) ↔ r = 6 ∧ θ = 0) := by
  have hp := pi_pos
  refine ⟨w8_mag (by norm_num) (by norm_num), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((6 : ℝ), 0) = polarPoint 6 0 := by
    simp only [polarPoint, cos_zero, sin_zero, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w8_conv (by norm_num) le_rfl (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.39: the vector `⟨-2.5, 0⟩` has `‖v‖ = 2.5` and exactly `θ = π` (`180°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.39, p. 1040"]
theorem exer_11_8_39 :
    vecMag (-2.5, 0) = 2.5 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-2.5, 0) ↔ r = 2.5 ∧ θ = π) := by
  have hp := pi_pos
  refine ⟨w8_mag (by norm_num) (by norm_num), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((-2.5 : ℝ), 0) = polarPoint 2.5 π := by
    simp only [polarPoint, cos_pi, sin_pi, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w8_conv (by norm_num) hp.le (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.40: the vector `⟨0, √7⟩` has `‖v‖ = √7` and exactly `θ = π/2` (`90°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.40, p. 1040"]
theorem exer_11_8_40 :
    vecMag (0, √7) = √7 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (0, √7) ↔ r = √7 ∧ θ = π / 2) := by
  have hp := pi_pos
  have h7 : √7 * √7 = 7 := Real.mul_self_sqrt (by norm_num)
  refine ⟨w8_mag (by positivity) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((0 : ℝ), √7) = polarPoint (√7) (π / 2) := by
    simp only [polarPoint, cos_pi_div_two, sin_pi_div_two, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w8_conv (by positivity) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.41: the vector `-10 j = ⟨0, -10⟩` has `‖v‖ = 10` and exactly `θ = 3π/2`
(`270°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.41, p. 1040"]
theorem exer_11_8_41 :
    vecMag (0, -10) = 10 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (0, -10) ↔ r = 10 ∧ θ = 3 * π / 2) := by
  have hp := pi_pos
  refine ⟨w8_mag (by norm_num) (by norm_num), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((0 : ℝ), -10) = polarPoint 10 (3 * π / 2) := by
    have : 3 * π / 2 = π / 2 + π := by ring
    simp only [polarPoint, this, cos_add_pi, sin_add_pi, cos_pi_div_two, sin_pi_div_two, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w8_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.43: the vector `⟨12, 5⟩` has `‖v‖ = 13` and exactly `θ = arctan (5/12)`
(about `22.62°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.43, p. 1040"]
theorem exer_11_8_43 :
    vecMag (12, 5) = 13 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (12, 5) ↔ r = 13 ∧ θ = arctan (5 / 12)) := by
  have hp := pi_pos
  refine ⟨w8_mag (by norm_num) (by norm_num), fun r θ hr hθ hθ2 => ?_⟩
  have h5 : √(1 + (5 / 12 : ℝ) ^ 2) = 13 / 12 := by
    rw [show 1 + (5 / 12 : ℝ) ^ 2 = (13 / 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e : ((12 : ℝ), 5) = polarPoint 13 (arctan (5 / 12)) := by
    simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 ≤ arctan (5 / 12) := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two (5 / 12)
  rw [e, w8_conv (by norm_num) h0 (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.44: the vector `⟨-4, 3⟩` has `‖v‖ = 5` and exactly `θ = π - arctan (3/4)`
(about `143.13°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.44, p. 1040"]
theorem exer_11_8_44 :
    vecMag (-4, 3) = 5 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-4, 3) ↔ r = 5 ∧ θ = π - arctan (3 / 4)) := by
  have hp := pi_pos
  refine ⟨w8_mag (by norm_num) (by norm_num), fun r θ hr hθ hθ2 => ?_⟩
  have h5 : √(1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
    rw [show 1 + (3 / 4 : ℝ) ^ 2 = (5 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e : ((-4 : ℝ), 3) = polarPoint 5 (π - arctan (3 / 4)) := by
    simp only [polarPoint, cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 < arctan (3 / 4) := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two (3 / 4)
  rw [e, w8_conv (by norm_num) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.46: the vector `⟨-2, -1⟩` has `‖v‖ = √5` and exactly
`θ = π + arctan (1/2)` (about `206.57°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.46, p. 1041"]
theorem exer_11_8_46 :
    vecMag (-2, -1) = √5 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-2, -1) ↔ r = √5 ∧ θ = π + arctan (1 / 2)) := by
  have hp := pi_pos
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < √5 := by positivity
  refine ⟨w8_mag (by positivity) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have h5' : √(1 + (1 / 2 : ℝ) ^ 2) = √5 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    nlinarith
  have e : ((-2 : ℝ), -1) = polarPoint (√5) (π + arctan (1 / 2)) := by
    rw [add_comm π]
    simp only [polarPoint, cos_add_pi, sin_add_pi, Real.cos_arctan, Real.sin_arctan, h5', Prod.mk.injEq]
    constructor <;> field_simp <;> nlinarith
  have h0 : 0 < arctan (1 / 2) := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two (1 / 2)
  rw [e, w8_conv hs (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.47: the vector `⟨-2, -6⟩` has `‖v‖ = 2√10` and exactly
`θ = π + arctan 3` (about `251.57°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.47, p. 1041"]
theorem exer_11_8_47 :
    vecMag (-2, -6) = 2 * √10 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-2, -6) ↔ r = 2 * √10 ∧ θ = π + arctan 3) := by
  have hp := pi_pos
  have h10 : √10 * √10 = 10 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < √10 := by positivity
  refine ⟨w8_mag (by positivity) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have h5 : √(1 + (3 : ℝ) ^ 2) = √10 := by norm_num
  have e : ((-2 : ℝ), -6) = polarPoint (2 * √10) (π + arctan 3) := by
    rw [add_comm π]
    simp only [polarPoint, cos_add_pi, sin_add_pi, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> field_simp <;> nlinarith
  have h0 : 0 < arctan 3 := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two 3
  rw [e, w8_conv (by positivity) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.48: the vector `i + j = ⟨1, 1⟩` has `‖v‖ = √2` and exactly `θ = π/4` (`45°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.48, p. 1041"]
theorem exer_11_8_48 :
    vecMag (1, 1) = √2 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (1, 1) ↔ r = √2 ∧ θ = π / 4) := by
  have hp := pi_pos
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < √2 := by positivity
  refine ⟨w8_mag (by positivity) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((1 : ℝ), 1) = polarPoint (√2) (π / 4) := by
    simp only [polarPoint, cos_pi_div_four, sin_pi_div_four, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e, w8_conv hs (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.49: the vector `i - 4j = ⟨1, -4⟩` has `‖v‖ = √17` and exactly
`θ = 2π - arctan 4` (about `284.04°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.49, p. 1041"]
theorem exer_11_8_49 :
    vecMag (1, -4) = √17 ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (1, -4) ↔ r = √17 ∧ θ = 2 * π - arctan 4) := by
  have hp := pi_pos
  have h17 : √17 * √17 = 17 := Real.mul_self_sqrt (by norm_num)
  have hs : (0 : ℝ) < √17 := by positivity
  refine ⟨w8_mag (by positivity) (by nlinarith), fun r θ hr hθ hθ2 => ?_⟩
  have e : ((1 : ℝ), -4) = polarPoint (√17) (2 * π - arctan 4) := by
    have := w8_q4 1 4 (by norm_num)
    norm_num at this
    exact this.symm
  have h0 : 0 < arctan 4 := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two 4
  rw [e, w8_conv hs (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.50: the vector `⟨123.4, -77.05⟩` has `‖v‖ = √(123.4² + 77.05²)` (about
`145.48`) and exactly `θ = 2π - arctan (77.05/123.4)` (about `328.02°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.50, p. 1041"]
theorem exer_11_8_50 :
    vecMag (123.4, -77.05) = √(123.4 ^ 2 + 77.05 ^ 2) ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (123.4, -77.05) ↔
        r = √(123.4 ^ 2 + 77.05 ^ 2) ∧ θ = 2 * π - arctan (77.05 / 123.4)) := by
  have hp := pi_pos
  have hs : (0 : ℝ) < √(123.4 ^ 2 + 77.05 ^ 2) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by unfold vecMag; simp only [neg_sq], fun r θ hr hθ hθ2 => ?_⟩
  have e := w8_q4 123.4 77.05 (by norm_num)
  have h0 : 0 < arctan (77.05 / 123.4) := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two (77.05 / 123.4)
  rw [← e, w8_conv hs (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.51: the vector `⟨965.15, 831.6⟩` has `‖v‖ = √(965.15² + 831.6²)` (about
`1274.00`) and exactly `θ = arctan (831.6/965.15)` (about `40.75°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.51, p. 1041"]
theorem exer_11_8_51 :
    vecMag (965.15, 831.6) = √(965.15 ^ 2 + 831.6 ^ 2) ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (965.15, 831.6) ↔
        r = √(965.15 ^ 2 + 831.6 ^ 2) ∧ θ = arctan (831.6 / 965.15)) := by
  have hp := pi_pos
  have hs : (0 : ℝ) < √(965.15 ^ 2 + 831.6 ^ 2) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨rfl, fun r θ hr hθ hθ2 => ?_⟩
  have e := w8_q1 965.15 831.6 (by norm_num)
  have h0 : 0 < arctan (831.6 / 965.15) := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two (831.6 / 965.15)
  rw [← e, w8_conv hs h0.le (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.8.52: the vector `⟨-114.1, 42.3⟩` has `‖v‖ = √(114.1² + 42.3²)` (about
`121.69`) and exactly `θ = π - arctan (42.3/114.1)` (about `159.66°`). -/
@[kb "stitzzeager2013" "Exercise 11.8.52, p. 1041"]
theorem exer_11_8_52 :
    vecMag (-114.1, 42.3) = √(114.1 ^ 2 + 42.3 ^ 2) ∧ ∀ r θ : ℝ, 0 ≤ r → 0 ≤ θ → θ < 2 * π →
      (polarPoint r θ = (-114.1, 42.3) ↔
        r = √(114.1 ^ 2 + 42.3 ^ 2) ∧ θ = π - arctan (42.3 / 114.1)) := by
  have hp := pi_pos
  have hs : (0 : ℝ) < √(114.1 ^ 2 + 42.3 ^ 2) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by unfold vecMag; simp only [neg_sq], fun r θ hr hθ hθ2 => ?_⟩
  have e := w8_q2 114.1 42.3 (by norm_num)
  have h0 : 0 < arctan (42.3 / 114.1) := arctan_pos.2 (by norm_num)
  have h1 := arctan_lt_pi_div_two (42.3 / 114.1)
  rw [← e, w8_conv hs (by linarith) (by linarith) hr hθ hθ2]

/-! ## Section 11.8: applications and properties -/

private theorem w8_sin_cos (y : ℝ) (h0 : 0 < y) (h1 : y ≤ 1) :
    y - y ^ 3 / 6 - y ^ 5 / 100 ≤ sin y ∧ sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 100 ∧
      1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ cos y ∧ cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
  have hs := Real.sin_bound (x := y) (by rw [abs_of_pos h0]; exact h1)
  have hc := Real.cos_bound (x := y) (by rw [abs_of_pos h0]; exact h1)
  rw [abs_of_pos h0] at hs hc
  have hs' := abs_le.mp hs
  have hc' := abs_le.mp hc
  refine ⟨by linarith [hs'.1], by linarith [hs'.2], by linarith [hc'.1], by linarith [hc'.2]⟩

/-- Stitz-Zeager Exercise 11.8.59: two cables each at `42°` to the ceiling and each rated for `100` lb carry
at most `2 · 100 sin 42°` lb, which is between `133` and `134` (so `133` lb rounded down). -/
@[kb "stitzzeager2013" "Exercise 11.8.59, p. 1041"]
theorem exer_11_8_59 (W : ℝ) :
    W = 2 * 100 * sin (42 * π / 180) → 133 < W ∧ W < 134 := by
  intro hW
  have h1 := pi_gt_d4
  have h2 := pi_lt_d4
  have h3 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2l : 1.4142 < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2u : √2 < 1.4143 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have e : sin (42 * π / 180) = √2 / 2 * (cos (π / 60) - sin (π / 60)) := by
    have : 42 * π / 180 = π / 4 - π / 60 := by ring
    rw [this, sin_sub, cos_pi_div_four, sin_pi_div_four]; ring
  obtain ⟨a1, a2, a3, a4⟩ := w8_sin_cos (π / 60) (by positivity) (by linarith)
  have hy1 : 0.05235 < π / 60 := by linarith
  have hy2 : π / 60 < 0.05237 := by linarith
  have hs : 0 ≤ sin (π / 60) := by linarith [sin_pos_of_pos_of_lt_pi (show 0 < π / 60 by positivity) (by linarith)]
  rw [hW, e]
  have hy : 0 < π / 60 := by positivity
  have d1 : 0.94 < cos (π / 60) - sin (π / 60) := by nlinarith [mul_pos hy hy, mul_pos (mul_pos hy hy) hy, mul_pos (mul_pos hy hy) (mul_pos hy hy)]
  have d2 : cos (π / 60) - sin (π / 60) < 0.9477 := by nlinarith [mul_pos hy hy, mul_pos (mul_pos hy hy) hy, mul_pos (mul_pos hy hy) (mul_pos hy hy)]
  constructor <;> nlinarith

/-- Stitz-Zeager Exercise 11.8.61: pulls of `100` lb at `N77°E` (angle `13°`) and `F` lb at `S68°E` (angle
`-22°`) give a due-east resultant exactly when `100 sin 13° = F sin 22°`, i.e. `F = 100 sin 13°/sin 22°`
(about `60` lb), and then the resultant is `100 cos 13° + F cos 22°` (about `153` lb). -/
@[kb "stitzzeager2013" "Exercise 11.8.61, p. 1042"]
theorem exer_11_8_61 (F R : ℝ) :
    (100 * sin (13 * π / 180) = F * sin (22 * π / 180) ∧
        R = 100 * cos (13 * π / 180) + F * cos (22 * π / 180)) ↔
      F = 100 * sin (13 * π / 180) / sin (22 * π / 180) ∧
        R = 100 * cos (13 * π / 180) + 100 * sin (13 * π / 180) / sin (22 * π / 180) * cos (22 * π / 180) := by
  have hpi := pi_pos
  have s : 0 < sin (22 * π / 180) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  constructor
  · rintro ⟨h1, h2⟩
    have hF : F = 100 * sin (13 * π / 180) / sin (22 * π / 180) := by
      rw [eq_div_iff s.ne']; linarith
    exact ⟨hF, by rw [← hF]; exact h2⟩
  · rintro ⟨hF, hR⟩
    refine ⟨?_, by rw [hR, hF]⟩
    rw [hF]; exact (div_mul_cancel₀ _ s.ne').symm

/-- Stitz-Zeager Exercise 11.8.64: if two nonzero vectors have equal or opposite unit vectors, then
`v = k w` for a nonzero scalar `k`, with `k > 0` for equal and `k < 0` for opposite directions. -/
@[kb "stitzzeager2013" "Exercise 11.8.64, p. 1042"]
theorem exer_11_8_64 (v w : ℝ × ℝ) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : (vecMag v)⁻¹ • v = (vecMag w)⁻¹ • w ∨ (vecMag v)⁻¹ • v = -((vecMag w)⁻¹ • w)) :
    ∃ k : ℝ, k ≠ 0 ∧ v = k • w ∧ ((vecMag v)⁻¹ • v = (vecMag w)⁻¹ • w → 0 < k) ∧
      ((vecMag v)⁻¹ • v = -((vecMag w)⁻¹ • w) → k < 0) := by
  have pos : ∀ u : ℝ × ℝ, u ≠ 0 → 0 < vecMag u := by
    intro u hu
    have hp : 0 < u.1 ^ 2 + u.2 ^ 2 := by
      rcases Classical.em (u.1 = 0) with h1 | h1
      · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
        positivity
      · positivity
    exact Real.sqrt_pos.mpr hp
  have mv := pos v hv
  have mw := pos w hw
  have u1 := exer_11_8_63 w hw
  have hv' : v = vecMag v • ((vecMag v)⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ mv.ne', one_smul]
  have hdis : (vecMag v)⁻¹ • v = (vecMag w)⁻¹ • w → (vecMag v)⁻¹ • v = -((vecMag w)⁻¹ • w) → False := by
    intro a b
    have : (vecMag w)⁻¹ • w = 0 := by
      have := a.symm.trans b
      have h2 : (2 : ℝ) • ((vecMag w)⁻¹ • w) = 0 := by
        rw [two_smul]; nth_rewrite 1 [this]; simp
      simpa using h2
    rw [this] at u1
    unfold vecMag at u1
    simp at u1
  rcases h with h | h
  · refine ⟨vecMag v / vecMag w, (div_pos mv mw).ne', ?_, fun _ => div_pos mv mw, fun b => (hdis h b).elim⟩
    conv_lhs => rw [hv']
    rw [h, smul_smul, div_eq_mul_inv]
  · refine ⟨-(vecMag v / vecMag w), by have := (div_pos mv mw).ne'; simpa using this, ?_,
      fun a => (hdis a h).elim, fun _ => by have := div_pos mv mw; linarith⟩
    conv_lhs => rw [hv']
    rw [h, smul_neg, smul_smul, neg_smul, div_eq_mul_inv]

/-- Stitz-Zeager Exercise 11.8.66: vector addition is associative and has the identity `0` (with
additive inverses). -/
@[kb "stitzzeager2013" "Exercise 11.8.66, p. 1042"]
theorem exer_11_8_66 (u v w : ℝ × ℝ) :
    (u + v) + w = u + (v + w) ∧ v + 0 = v ∧ 0 + v = v ∧ v + -v = 0 :=
  ⟨add_assoc u v w, add_zero v, zero_add v, add_neg_cancel v⟩

end UndergradKB.Precalculus.Course
