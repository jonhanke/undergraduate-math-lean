import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Vectors

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.9

Plane vectors are pairs `ℝ × ℝ`, with `vecMag` the magnitude, `dotProd2` the dot product and `vecProj` the
projection. -/

namespace UndergradKB.Precalculus.Course

open Real Set

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Helpers -/

private theorem w9_mag {a b c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 + b ^ 2 = c ^ 2) : vecMag (a, b) = c := by
  unfold vecMag; simp only; rw [h, Real.sqrt_sq hc]

private theorem w9_unit_proj (v w : ℝ × ℝ) (h : dotProd2 w w = 1) :
    vecProj v w = dotProd2 v w • w := by
  unfold vecProj; rw [h, div_one]

/-! ## Section 11.9: dot product, angle and projection -/

/-- Stitz-Zeager Exercise 11.9.5: for `v = ⟨-2, 1⟩`, `w = ⟨3, 6⟩`: `v · w = 0`, the angle is `90°`,
`proj_w v = 0`, and `q = v`. -/
@[kb "stitzzeager2013" "Exercise 11.9.5, p. 1055"]
theorem exer_11_9_5 (v w : ℝ × ℝ) (hv : v = (-2, 1)) (hw : w = (3, 6)) :
    dotProd2 v w = 0 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = π / 2 ∧
      vecProj v w = (0, 0) ∧ v - vecProj v w = v := by
  have hd : dotProd2 v w = 0 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = 0 := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [hd, zero_div, arccos_zero]
  · rw [hproj]; rfl
  · rw [hproj, sub_zero]

/-- Stitz-Zeager Exercise 11.9.6: for `v = ⟨-3√3, 3⟩`, `w = ⟨-√3, -1⟩`: `v · w = 6`, the angle is `60°`,
`proj_w v = ⟨-3√3/2, -3/2⟩`, and `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.6, p. 1055"]
theorem exer_11_9_6 (v w : ℝ × ℝ) (hv : v = (-(3 * √3), 3)) (hw : w = (-√3, -1)) :
    dotProd2 v w = 6 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = π / 3 ∧
      vecProj v w = (-(3 * √3 / 2), -(3 / 2)) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 6 := by rw [hv]; exact w9_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 2 := by rw [hw]; exact w9_mag (by norm_num) (by nlinarith)
  have hd : dotProd2 v w = 6 := by rw [hv, hw]; unfold dotProd2; simp only; nlinarith
  have hproj : vecProj v w = (-(3 * √3 / 2), -(3 / 2)) := by
    rw [hv, hw]; unfold vecProj dotProd2; simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    have e1 : -(3 * √3) * -√3 + 3 * -1 = 6 := by nlinarith
    have e2 : -√3 * -√3 + -1 * -1 = 4 := by nlinarith
    rw [e1, e2]
    constructor <;> nlinarith
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, show (6 : ℝ) / (6 * 2) = 1 / 2 by norm_num, ← cos_pi_div_three]
    exact arccos_cos (by linarith [pi_pos]) (by linarith [pi_pos])
  · rw [hproj, hv, hw]; unfold dotProd2
    simp only [Prod.fst_sub, Prod.snd_sub]
    nlinarith

/-- Stitz-Zeager Exercise 11.9.7: for `v = ⟨1, 17⟩`, `w = ⟨-1, 0⟩`: `v · w = -1`, the angle is
`arccos (-1/√290)` (about `93.37°`), `proj_w v = ⟨1, 0⟩`, and `q = ⟨0, 17⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.9.7, p. 1055"]
theorem exer_11_9_7 (v w : ℝ × ℝ) (hv : v = (1, 17)) (hw : w = (-1, 0)) :
    dotProd2 v w = -1 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (-1 / √290) ∧
      vecProj v w = (1, 0) ∧ v - vecProj v w = (0, 17) := by
  have mv : vecMag v = √290 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = 1 := by rw [hw]; exact w9_mag (by norm_num) (by norm_num)
  have hd : dotProd2 v w = -1 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (1, 0) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, mul_one]
  · rw [hproj, hv]; norm_num [Prod.ext_iff]

/-- Stitz-Zeager Exercise 11.9.9: for `v = ⟨-4, -2⟩`, `w = ⟨1, -5⟩`: `v · w = 6`, the angle is
`arccos (6/(√20 √26))` (about `74.74°`), `proj_w v = ⟨3/13, -15/13⟩`, and `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.9, p. 1055"]
theorem exer_11_9_9 (v w : ℝ × ℝ) (hv : v = (-4, -2)) (hw : w = (1, -5)) :
    dotProd2 v w = 6 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (6 / (√20 * √26)) ∧
      vecProj v w = (3 / 13, -15 / 13) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have mv : vecMag v = √20 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = √26 := by rw [hw]; unfold vecMag; norm_num
  have hd : dotProd2 v w = 6 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (3 / 13, -15 / 13) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]
  · rw [hproj, hv, hw]; unfold dotProd2; norm_num

/-- Stitz-Zeager Exercise 11.9.10: for `v = ⟨-5, 6⟩`, `w = ⟨4, -7⟩`: `v · w = -62`, the angle is
`arccos (-62/(√61 √65))` (about `169.94°`), `proj_w v = ⟨-248/65, 434/65⟩`, and `q = ⟨-77/65, -44/65⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.9.10, p. 1055"]
theorem exer_11_9_10 (v w : ℝ × ℝ) (hv : v = (-5, 6)) (hw : w = (4, -7)) :
    dotProd2 v w = -62 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (-62 / (√61 * √65)) ∧
      vecProj v w = (-248 / 65, 434 / 65) ∧ v - vecProj v w = (-77 / 65, -44 / 65) := by
  have mv : vecMag v = √61 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = √65 := by rw [hw]; unfold vecMag; norm_num
  have hd : dotProd2 v w = -62 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (-248 / 65, 434 / 65) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]
  · rw [hproj, hv]; norm_num [Prod.ext_iff]

/-- Stitz-Zeager Exercise 11.9.11: for `v = ⟨-8, 3⟩`, `w = ⟨2, 6⟩`: `v · w = 2`, the angle is
`arccos (2/(√73 √40))` (about `87.88°`), `proj_w v = ⟨1/10, 3/10⟩`, and `q = ⟨-81/10, 27/10⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.9.11, p. 1056"]
theorem exer_11_9_11 (v w : ℝ × ℝ) (hv : v = (-8, 3)) (hw : w = (2, 6)) :
    dotProd2 v w = 2 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (2 / (√73 * √40)) ∧
      vecProj v w = (1 / 10, 3 / 10) ∧ v - vecProj v w = (-81 / 10, 27 / 10) := by
  have mv : vecMag v = √73 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = √40 := by rw [hw]; unfold vecMag; norm_num
  have hd : dotProd2 v w = 2 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (1 / 10, 3 / 10) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]
  · rw [hproj, hv]; norm_num [Prod.ext_iff]

/-- Stitz-Zeager Exercise 11.9.12: for `v = ⟨34, -91⟩`, `w = ⟨0, 1⟩`: `v · w = -91`, the angle is
`arccos (-91/√9437)` (about `159.51°`), `proj_w v = ⟨0, -91⟩`, and `q = ⟨34, 0⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.9.12, p. 1056"]
theorem exer_11_9_12 (v w : ℝ × ℝ) (hv : v = (34, -91)) (hw : w = (0, 1)) :
    dotProd2 v w = -91 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (-91 / √9437) ∧
      vecProj v w = (0, -91) ∧ v - vecProj v w = (34, 0) := by
  have mv : vecMag v = √9437 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = 1 := by rw [hw]; exact w9_mag (by norm_num) (by norm_num)
  have hd : dotProd2 v w = -91 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (0, -91) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, mul_one]
  · rw [hproj, hv]; norm_num [Prod.ext_iff]

/-- Stitz-Zeager Exercise 11.9.13: for `v = 3i - j = ⟨3, -1⟩`, `w = 4j = ⟨0, 4⟩`: `v · w = -4`, the angle is
`arccos (-4/(√10 · 4))` (about `108.43°`), `proj_w v = ⟨0, -1⟩`, and `q = ⟨3, 0⟩`. -/
@[kb "stitzzeager2013" "Exercise 11.9.13, p. 1055"]
theorem exer_11_9_13 (v w : ℝ × ℝ) (hv : v = (3, -1)) (hw : w = (0, 4)) :
    dotProd2 v w = -4 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = arccos (-4 / (√10 * 4)) ∧
      vecProj v w = (0, -1) ∧ v - vecProj v w = (3, 0) := by
  have mv : vecMag v = √10 := by rw [hv]; unfold vecMag; norm_num
  have mw : vecMag w = 4 := by rw [hw]; exact w9_mag (by norm_num) (by norm_num)
  have hd : dotProd2 v w = -4 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = (0, -1) := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw]
  · rw [hproj, hv]; norm_num [Prod.ext_iff]

/-- Stitz-Zeager Exercise 11.9.15: for `v = (3/2) i + (3/2) j`, `w = i - j`: `v · w = 0`, the angle is `90°`,
`proj_w v = 0`, and `q = v`. -/
@[kb "stitzzeager2013" "Exercise 11.9.15, p. 1055"]
theorem exer_11_9_15 (v w : ℝ × ℝ) (hv : v = (3 / 2, 3 / 2)) (hw : w = (1, -1)) :
    dotProd2 v w = 0 ∧ arccos (dotProd2 v w / (vecMag v * vecMag w)) = π / 2 ∧
      vecProj v w = (0, 0) ∧ v - vecProj v w = v := by
  have hd : dotProd2 v w = 0 := by rw [hv, hw]; unfold dotProd2; norm_num
  have hproj : vecProj v w = 0 := by
    rw [hv, hw]; unfold vecProj dotProd2; norm_num [Prod.ext_iff]
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [hd, zero_div, arccos_zero]
  · rw [hproj]; rfl
  · rw [hproj, sub_zero]

/-- Stitz-Zeager Exercise 11.9.17: for the unit vectors `v = ⟨1/2, √3/2⟩`, `w = ⟨-√2/2, √2/2⟩`: the dot product
is `(√2√3 - √2)/4 = cos 75°`, so the angle is `75°`, `proj_w v = ⟨(1-√3)/4, (√3-1)/4⟩`, and `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.17, p. 1055"]
theorem exer_11_9_17 (v w : ℝ × ℝ) (hv : v = (1 / 2, √3 / 2)) (hw : w = (-(√2 / 2), √2 / 2)) :
    dotProd2 v w = (√2 * √3 - √2) / 4 ∧
      arccos (dotProd2 v w / (vecMag v * vecMag w)) = 5 * π / 12 ∧
      vecProj v w = ((1 - √3) / 4, (√3 - 1) / 4) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 1 := by rw [hv]; exact w9_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 1 := by rw [hw]; exact w9_mag (by norm_num) (by nlinarith)
  have hww : dotProd2 w w = 1 := by rw [hw]; unfold dotProd2; simp only; nlinarith
  have hd : dotProd2 v w = (√2 * √3 - √2) / 4 := by
    rw [hv, hw]; unfold dotProd2; simp only; ring
  have hproj : vecProj v w = ((1 - √3) / 4, (√3 - 1) / 4) := by
    rw [w9_unit_proj v w hww, hd, hw]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor
    · linear_combination (-(√3 - 1) / 8) * h2
    · linear_combination ((√3 - 1) / 8) * h2
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, mul_one, div_one]
    have e : 5 * π / 12 = π / 4 + π / 6 := by ring
    have hc : cos (5 * π / 12) = (√2 * √3 - √2) / 4 := by
      rw [e, cos_add, cos_pi_div_four, sin_pi_div_four, cos_pi_div_six, sin_pi_div_six]; ring
    rw [← hc]
    exact arccos_cos (by positivity) (by linarith [pi_pos])
  · rw [hproj, hv, hw]; unfold dotProd2
    simp only [Prod.fst_sub, Prod.snd_sub]
    nlinarith

/-- Stitz-Zeager Exercise 11.9.18: for the unit vectors `v = ⟨√2/2, √2/2⟩`, `w = ⟨1/2, -√3/2⟩`: the dot product
is `(√2 - √2√3)/4 = cos 105°`, so the angle is `105°`, `proj_w v = ⟨(√2 - √6)/8, (3√2 - √6)/8⟩`, and `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.18, p. 1055"]
theorem exer_11_9_18 (v w : ℝ × ℝ) (hv : v = (√2 / 2, √2 / 2)) (hw : w = (1 / 2, -(√3 / 2))) :
    dotProd2 v w = (√2 - √2 * √3) / 4 ∧
      arccos (dotProd2 v w / (vecMag v * vecMag w)) = 7 * π / 12 ∧
      vecProj v w = ((√2 - √2 * √3) / 8, (3 * √2 - √2 * √3) / 8) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 1 := by rw [hv]; exact w9_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 1 := by rw [hw]; exact w9_mag (by norm_num) (by nlinarith)
  have hww : dotProd2 w w = 1 := by rw [hw]; unfold dotProd2; simp only; nlinarith
  have hd : dotProd2 v w = (√2 - √2 * √3) / 4 := by
    rw [hv, hw]; unfold dotProd2; simp only; ring
  have hproj : vecProj v w = ((√2 - √2 * √3) / 8, (3 * √2 - √2 * √3) / 8) := by
    rw [w9_unit_proj v w hww, hd, hw]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor
    · ring
    · linear_combination (√2 / 8) * h3
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, mul_one, div_one]
    have e : 7 * π / 12 = π / 3 + π / 4 := by ring
    have hc : cos (7 * π / 12) = (√2 - √2 * √3) / 4 := by
      rw [e, cos_add, cos_pi_div_three, sin_pi_div_three, cos_pi_div_four, sin_pi_div_four]; ring
    rw [← hc]
    exact arccos_cos (by positivity) (by linarith [pi_pos])
  · rw [hproj, hv, hw]; unfold dotProd2
    simp only [Prod.fst_sub, Prod.snd_sub]
    linear_combination (-(√2) / 16) * h3

/-- Stitz-Zeager Exercise 11.9.19: for the unit vectors `v = ⟨√3/2, 1/2⟩`, `w = ⟨-√2/2, -√2/2⟩`: the dot product
is `-(√2√3 + √2)/4 = cos 165°`, so the angle is `165°`, `proj_w v = ⟨(√3+1)/4, (√3+1)/4⟩`, and `q · w = 0`. -/
@[kb "stitzzeager2013" "Exercise 11.9.19, p. 1055"]
theorem exer_11_9_19 (v w : ℝ × ℝ) (hv : v = (√3 / 2, 1 / 2)) (hw : w = (-(√2 / 2), -(√2 / 2))) :
    dotProd2 v w = -(√2 * √3 + √2) / 4 ∧
      arccos (dotProd2 v w / (vecMag v * vecMag w)) = 11 * π / 12 ∧
      vecProj v w = ((√3 + 1) / 4, (√3 + 1) / 4) ∧ dotProd2 (v - vecProj v w) w = 0 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have mv : vecMag v = 1 := by rw [hv]; exact w9_mag (by norm_num) (by nlinarith)
  have mw : vecMag w = 1 := by rw [hw]; exact w9_mag (by norm_num) (by nlinarith)
  have hww : dotProd2 w w = 1 := by rw [hw]; unfold dotProd2; simp only; nlinarith
  have hd : dotProd2 v w = -(√2 * √3 + √2) / 4 := by
    rw [hv, hw]; unfold dotProd2; simp only; ring
  have hproj : vecProj v w = ((√3 + 1) / 4, (√3 + 1) / 4) := by
    rw [w9_unit_proj v w hww, hd, hw]
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
    constructor
    · linear_combination ((√3 + 1) / 8) * h2
    · linear_combination ((√3 + 1) / 8) * h2
  refine ⟨hd, ?_, hproj, ?_⟩
  · rw [hd, mv, mw, mul_one, div_one]
    have e : 11 * π / 12 = π - π / 12 := by ring
    have e2 : π / 12 = π / 3 - π / 4 := by ring
    have hc : cos (11 * π / 12) = -(√2 * √3 + √2) / 4 := by
      rw [e, cos_pi_sub, e2, cos_sub, cos_pi_div_three, sin_pi_div_three, cos_pi_div_four,
        sin_pi_div_four]; ring
    rw [← hc]
    exact arccos_cos (by linarith [pi_pos]) (by linarith [pi_pos])
  · rw [hproj, hv, hw]; unfold dotProd2
    simp only [Prod.fst_sub, Prod.snd_sub]
    nlinarith

/-- Stitz-Zeager Exercise 11.9.24: the work done by a force of `100` lb at `13°` to the motion over `42` ft is
`100 · 42 cos 13°` ft-lb (about `4092.35`). -/
@[kb "stitzzeager2013" "Exercise 11.9.24, p. 1055"]
theorem exer_11_9_24 :
    dotProd2 (100 * cos (13 * π / 180), 100 * sin (13 * π / 180)) (42, 0) = 100 * 42 * cos (13 * π / 180) := by
  unfold dotProd2; simp only; ring

/-- Stitz-Zeager Exercise 11.9.25: pushing a `200` lb barrel `10` ft up a `12.5°` incline (force straight up,
displacement `10 ⟨cos 12.5°, sin 12.5°⟩`) does `2000 sin 12.5° = 2000 cos 77.5°` ft-lb (about `432.88`). -/
@[kb "stitzzeager2013" "Exercise 11.9.25, p. 1055"]
theorem exer_11_9_25 :
    dotProd2 (0, 200) (10 * cos (12.5 * π / 180), 10 * sin (12.5 * π / 180)) =
        200 * 10 * cos (77.5 * π / 180) ∧ 200 * 10 * cos (77.5 * π / 180) = 2000 * sin (12.5 * π / 180) := by
  have e : 77.5 * π / 180 = π / 2 - 12.5 * π / 180 := by ring
  have h : cos (77.5 * π / 180) = sin (12.5 * π / 180) := by rw [e, cos_pi_div_two_sub]
  refine ⟨?_, ?_⟩
  · unfold dotProd2; simp only; rw [h]; ring
  · rw [h]; ring

/-- Stitz-Zeager Exercise 11.9.26: the dot product distributes over vector addition. -/
@[kb "stitzzeager2013" "Exercise 11.9.26, p. 1056"]
theorem exer_11_9_26 (u v w : ℝ × ℝ) :
    dotProd2 u (v + w) = dotProd2 u v + dotProd2 u w := by
  unfold dotProd2; simp only [Prod.fst_add, Prod.snd_add]; ring

/-- Stitz-Zeager Exercise 11.9.27: the scalar property `(k v) · w = k (v · w) = v · (k w)`. -/
@[kb "stitzzeager2013" "Exercise 11.9.27, p. 1056"]
theorem exer_11_9_27 (k : ℝ) (v w : ℝ × ℝ) :
    dotProd2 (k • v) w = k * dotProd2 v w ∧ k * dotProd2 v w = dotProd2 v (k • w) := by
  unfold dotProd2; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> ring

end UndergradKB.Precalculus.Course
