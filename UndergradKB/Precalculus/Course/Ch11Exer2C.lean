import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.PolarComplex

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 7), Section 11.4

The point named by `(r, θ)` is `polarPoint r θ = (r cos θ, r sin θ)`. -/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ## Helpers -/

private theorem w4_same (r θ θ' : ℝ) (k : ℤ) (h : θ' = θ + k * (2 * π)) :
    polarPoint r θ' = polarPoint r θ := by
  rw [h]; exact (polar_point_same_names r θ k).1

private theorem w4_neg (r θ θ' : ℝ) (k : ℤ) (h : θ' = θ + (2 * k + 1) * π) :
    polarPoint (-r) θ' = polarPoint r θ := by
  rw [h]; exact (polar_point_same_names r θ k).2.1

private theorem w4_neg2 (r θ θ' : ℝ) (k : ℤ) (h : θ' = θ + (2 * k + 1) * π) :
    polarPoint r θ' = polarPoint (-r) θ := by
  have := w4_neg (-r) θ θ' k h
  rwa [neg_neg] at this

/-- Uniqueness of the polar name with `r ≥ 0` and `0 ≤ θ < 2π` of a point other than the origin. -/
private theorem w4_conv {r r' θ θ' : ℝ} (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ < 2 * π)
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

private theorem w4_sqrt_sq {a b : ℝ} (hb : 0 < b) (h : a = b ^ 2) : √a = b := by
  rw [h, Real.sqrt_sq hb.le]

/-! ## Section 11.4 -/

/-- Stitz-Zeager Exercise 11.4.2: the point (5, 7 * π / 4) in polar coordinates is also named by (-5, 3 * π / 4), (5, -(π / 4)), (5, 15 * π / 4). -/
@[kb "stitzzeager2013" "Exercise 11.4.2, p. 942"]
theorem exer_11_4_2 :
    polarPoint (-5) (3 * π / 4) = polarPoint 5 (7 * π / 4) ∧
      polarPoint 5 (-(π / 4)) = polarPoint 5 (7 * π / 4) ∧
      polarPoint 5 (15 * π / 4) = polarPoint 5 (7 * π / 4) :=
  ⟨w4_neg _ _ _ (-1) (by push_cast; ring),
    w4_same _ _ _ (-1) (by push_cast; ring),
    w4_same _ _ _ (1) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.3: the point (1 / 3, 3 * π / 2) in polar coordinates is also named by (-1 / 3, π / 2), (1 / 3, -(π / 2)), (1 / 3, 7 * π / 2). -/
@[kb "stitzzeager2013" "Exercise 11.4.3, p. 942"]
theorem exer_11_4_3 :
    polarPoint (-(1 / 3)) (π / 2) = polarPoint (1 / 3) (3 * π / 2) ∧
      polarPoint (1 / 3) (-(π / 2)) = polarPoint (1 / 3) (3 * π / 2) ∧
      polarPoint (1 / 3) (7 * π / 2) = polarPoint (1 / 3) (3 * π / 2) :=
  ⟨w4_neg _ _ _ (-1) (by push_cast; ring),
    w4_same _ _ _ (-1) (by push_cast; ring),
    w4_same _ _ _ (1) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.4: the point (5 / 2, 5 * π / 6) in polar coordinates is also named by (-5 / 2, 11 * π / 6), (5 / 2, -(7 * π / 6)), (5 / 2, 17 * π / 6). -/
@[kb "stitzzeager2013" "Exercise 11.4.4, p. 942"]
theorem exer_11_4_4 :
    polarPoint (-(5 / 2)) (11 * π / 6) = polarPoint (5 / 2) (5 * π / 6) ∧
      polarPoint (5 / 2) (-(7 * π / 6)) = polarPoint (5 / 2) (5 * π / 6) ∧
      polarPoint (5 / 2) (17 * π / 6) = polarPoint (5 / 2) (5 * π / 6) :=
  ⟨w4_neg _ _ _ (0) (by push_cast; ring),
    w4_same _ _ _ (-1) (by push_cast; ring),
    w4_same _ _ _ (1) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.6: the point (3, -(5 * π / 4)) in polar coordinates is also named by (-3, 7 * π / 4), (3, -(13 * π / 4)), (3, 11 * π / 4). -/
@[kb "stitzzeager2013" "Exercise 11.4.6, p. 942"]
theorem exer_11_4_6 :
    polarPoint (-3) (7 * π / 4) = polarPoint 3 (-(5 * π / 4)) ∧
      polarPoint 3 (-(13 * π / 4)) = polarPoint 3 (-(5 * π / 4)) ∧
      polarPoint 3 (11 * π / 4) = polarPoint 3 (-(5 * π / 4)) :=
  ⟨w4_neg _ _ _ (1) (by push_cast; ring),
    w4_same _ _ _ (-1) (by push_cast; ring),
    w4_same _ _ _ (2) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.7: the point (2 * √2, -π) in polar coordinates is also named by (-2 * √2, 0), (2 * √2, -(3 * π)), (2 * √2, 3 * π). -/
@[kb "stitzzeager2013" "Exercise 11.4.7, p. 942"]
theorem exer_11_4_7 :
    polarPoint (-(2 * √2)) 0 = polarPoint (2 * √2) (-π) ∧
      polarPoint (2 * √2) (-(3 * π)) = polarPoint (2 * √2) (-π) ∧
      polarPoint (2 * √2) (3 * π) = polarPoint (2 * √2) (-π) :=
  ⟨w4_neg _ _ _ (0) (by push_cast; ring),
    w4_same _ _ _ (-1) (by push_cast; ring),
    w4_same _ _ _ (2) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.8: the point (7 / 2, -(13 * π / 6)) in polar coordinates is also named by (-7 / 2, 5 * π / 6), (7 / 2, -(π / 6)), (7 / 2, 23 * π / 6). -/
@[kb "stitzzeager2013" "Exercise 11.4.8, p. 942"]
theorem exer_11_4_8 :
    polarPoint (-(7 / 2)) (5 * π / 6) = polarPoint (7 / 2) (-(13 * π / 6)) ∧
      polarPoint (7 / 2) (-(π / 6)) = polarPoint (7 / 2) (-(13 * π / 6)) ∧
      polarPoint (7 / 2) (23 * π / 6) = polarPoint (7 / 2) (-(13 * π / 6)) :=
  ⟨w4_neg _ _ _ (1) (by push_cast; ring),
    w4_same _ _ _ (1) (by push_cast; ring),
    w4_same _ _ _ (3) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.10: the point (-4, 5 * π / 4) in polar coordinates is also named by (-4, 13 * π / 4), (4, -(7 * π / 4)), (4, 9 * π / 4). -/
@[kb "stitzzeager2013" "Exercise 11.4.10, p. 942"]
theorem exer_11_4_10 :
    polarPoint (-4) (13 * π / 4) = polarPoint (-4) (5 * π / 4) ∧
      polarPoint 4 (-(7 * π / 4)) = polarPoint (-4) (5 * π / 4) ∧
      polarPoint 4 (9 * π / 4) = polarPoint (-4) (5 * π / 4) :=
  ⟨w4_same _ _ _ (1) (by push_cast; ring),
    w4_neg2 _ _ _ (-2) (by push_cast; ring),
    w4_neg2 _ _ _ (0) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.11: the point (-1, 2 * π / 3) in polar coordinates is also named by (-1, 8 * π / 3), (1, -(π / 3)), (1, 11 * π / 3). -/
@[kb "stitzzeager2013" "Exercise 11.4.11, p. 942"]
theorem exer_11_4_11 :
    polarPoint (-1) (8 * π / 3) = polarPoint (-1) (2 * π / 3) ∧
      polarPoint 1 (-(π / 3)) = polarPoint (-1) (2 * π / 3) ∧
      polarPoint 1 (11 * π / 3) = polarPoint (-1) (2 * π / 3) :=
  ⟨w4_same _ _ _ (1) (by push_cast; ring),
    w4_neg2 _ _ _ (-1) (by push_cast; ring),
    w4_neg2 _ _ _ (1) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.12: the point (-3, π / 2) in polar coordinates is also named by (-3, 5 * π / 2), (3, -(π / 2)), (3, 7 * π / 2). -/
@[kb "stitzzeager2013" "Exercise 11.4.12, p. 942"]
theorem exer_11_4_12 :
    polarPoint (-3) (5 * π / 2) = polarPoint (-3) (π / 2) ∧
      polarPoint 3 (-(π / 2)) = polarPoint (-3) (π / 2) ∧
      polarPoint 3 (7 * π / 2) = polarPoint (-3) (π / 2) :=
  ⟨w4_same _ _ _ (1) (by push_cast; ring),
    w4_neg2 _ _ _ (-1) (by push_cast; ring),
    w4_neg2 _ _ _ (1) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.13: the point (-3, -(11 * π / 6)) in polar coordinates is also named by (-3, π / 6), (3, -(5 * π / 6)), (3, 19 * π / 6). -/
@[kb "stitzzeager2013" "Exercise 11.4.13, p. 942"]
theorem exer_11_4_13 :
    polarPoint (-3) (π / 6) = polarPoint (-3) (-(11 * π / 6)) ∧
      polarPoint 3 (-(5 * π / 6)) = polarPoint (-3) (-(11 * π / 6)) ∧
      polarPoint 3 (19 * π / 6) = polarPoint (-3) (-(11 * π / 6)) :=
  ⟨w4_same _ _ _ (1) (by push_cast; ring),
    w4_neg2 _ _ _ (0) (by push_cast; ring),
    w4_neg2 _ _ _ (2) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.14: the point (-2.5, -(π / 4)) in polar coordinates is also named by (-2.5, 7 * π / 4), (2.5, -(5 * π / 4)), (2.5, 11 * π / 4). -/
@[kb "stitzzeager2013" "Exercise 11.4.14, p. 942"]
theorem exer_11_4_14 :
    polarPoint (-2.5) (7 * π / 4) = polarPoint (-2.5) (-(π / 4)) ∧
      polarPoint 2.5 (-(5 * π / 4)) = polarPoint (-2.5) (-(π / 4)) ∧
      polarPoint 2.5 (11 * π / 4) = polarPoint (-2.5) (-(π / 4)) :=
  ⟨w4_same _ _ _ (1) (by push_cast; ring),
    w4_neg2 _ _ _ (-1) (by push_cast; ring),
    w4_neg2 _ _ _ (1) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.15: the point (-√5, -(4 * π / 3)) in polar coordinates is also named by (-√5, 2 * π / 3), (√5, -(π / 3)), (√5, 11 * π / 3). -/
@[kb "stitzzeager2013" "Exercise 11.4.15, p. 942"]
theorem exer_11_4_15 :
    polarPoint (-√5) (2 * π / 3) = polarPoint (-√5) (-(4 * π / 3)) ∧
      polarPoint √5 (-(π / 3)) = polarPoint (-√5) (-(4 * π / 3)) ∧
      polarPoint √5 (11 * π / 3) = polarPoint (-√5) (-(4 * π / 3)) :=
  ⟨w4_same _ _ _ (1) (by push_cast; ring),
    w4_neg2 _ _ _ (0) (by push_cast; ring),
    w4_neg2 _ _ _ (2) (by push_cast; ring)⟩

/-- Stitz-Zeager Exercise 11.4.17: the polar point `(5, 7π/4)` is `(5√2/2, -5√2/2)` in rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.17, p. 942"]
theorem exer_11_4_17 : polarPoint 5 (7 * π / 4) = (5 * √2 / 2, -(5 * √2 / 2)) := by
  have e : 7 * π / 4 = -(π / 4) + 2 * π := by ring
  simp only [polarPoint, e, cos_add_two_pi, sin_add_two_pi, cos_neg, sin_neg, cos_pi_div_four,
    sin_pi_div_four, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.20: the polar point `(-20, 3π)` is `(20, 0)` in rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.20, p. 942"]
theorem exer_11_4_20 : polarPoint (-20) (3 * π) = (20, 0) := by
  have e : 3 * π = π + 2 * π := by ring
  simp only [polarPoint, e, cos_add_two_pi, sin_add_two_pi, cos_pi, sin_pi, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.21: the polar point `(3/5, π/2)` is `(0, 3/5)` in rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.21, p. 942"]
theorem exer_11_4_21 : polarPoint (3 / 5) (π / 2) = (0, 3 / 5) := by
  simp only [polarPoint, cos_pi_div_two, sin_pi_div_two, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.23: the polar point `(9, 7π/2)` is `(0, -9)` in rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.23, p. 942"]
theorem exer_11_4_23 : polarPoint 9 (7 * π / 2) = (0, -9) := by
  have e : 7 * π / 2 = (π / 2 + π) + 2 * π := by ring
  simp only [polarPoint, e, cos_add_two_pi, sin_add_two_pi, cos_add_pi, sin_add_pi, cos_pi_div_two,
    sin_pi_div_two, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.24: the polar point `(-5, -9π/4)` is `(-5√2/2, 5√2/2)` in rectangular
coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.24, p. 942"]
theorem exer_11_4_24 : polarPoint (-5) (-(9 * π / 4)) = (-(5 * √2 / 2), 5 * √2 / 2) := by
  have e : -(9 * π / 4) = -(π / 4) - 2 * π := by ring
  simp only [polarPoint, e, cos_sub_two_pi, sin_sub_two_pi, cos_neg, sin_neg, cos_pi_div_four,
    sin_pi_div_four, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.25: the polar point `(42, 13π/6)` is `(21√3, 21)` in rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.25, p. 942"]
theorem exer_11_4_25 : polarPoint 42 (13 * π / 6) = (21 * √3, 21) := by
  have e : 13 * π / 6 = π / 6 + 2 * π := by ring
  simp only [polarPoint, e, cos_add_two_pi, sin_add_two_pi, cos_pi_div_six, sin_pi_div_six,
    Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.26: the polar point `(-117, 117π)` is `(117, 0)` in rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.26, p. 942"]
theorem exer_11_4_26 : polarPoint (-117) (117 * π) = (117, 0) := by
  have h := (polar_point_same_names (-117) π 58).1
  have e : 117 * π = π + ((58 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [e, h]
  simp only [polarPoint, cos_pi, sin_pi, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.28: the polar point `(10, arctan 3)` is `(√10, 3√10)` in rectangular
coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.28, p. 942"]
theorem exer_11_4_28 : polarPoint 10 (arctan 3) = (√10, 3 * √10) := by
  have h5 : √(1 + (3 : ℝ) ^ 2) = √10 := by norm_num
  have hs : (0 : ℝ) < √10 := by positivity
  have hss : √10 * √10 = 10 := Real.mul_self_sqrt (by norm_num)
  simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> field_simp <;> nlinarith

/-- Stitz-Zeager Exercise 11.4.29: the polar point `(-3, arctan (4/3))` is `(-9/5, -12/5)` in rectangular
coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.29, p. 942"]
theorem exer_11_4_29 : polarPoint (-3) (arctan (4 / 3)) = (-(9 / 5), -(12 / 5)) := by
  have h5 : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := w4_sqrt_sq (by norm_num) (by norm_num)
  simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> norm_num

/-- Stitz-Zeager Exercise 11.4.30: the polar point `(5, arctan (-4/3))` is `(3, -4)` in rectangular
coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.30, p. 942"]
theorem exer_11_4_30 : polarPoint 5 (arctan (-(4 / 3))) = (3, -4) := by
  have h5 : √(1 + (-(4 / 3) : ℝ) ^ 2) = 5 / 3 := w4_sqrt_sq (by norm_num) (by norm_num)
  simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> norm_num

/-- Stitz-Zeager Exercise 11.4.32: the polar point `(-1/2, π - arctan 5)` is `(√26/52, -5√26/52)` in
rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.32, p. 942"]
theorem exer_11_4_32 : polarPoint (-(1 / 2)) (π - arctan 5) = (√26 / 52, -(5 * √26 / 52)) := by
  have h5 : √(1 + (5 : ℝ) ^ 2) = √26 := by norm_num
  have hs : (0 : ℝ) < √26 := by positivity
  have hss : √26 * √26 = 26 := Real.mul_self_sqrt (by norm_num)
  simp only [polarPoint, cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> field_simp <;> nlinarith

/-- Stitz-Zeager Exercise 11.4.33: the polar point `(-1, π + arctan (3/4))` is `(4/5, 3/5)` in rectangular
coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.33, p. 942"]
theorem exer_11_4_33 : polarPoint (-1) (π + arctan (3 / 4)) = (4 / 5, 3 / 5) := by
  have h5 : √(1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := w4_sqrt_sq (by norm_num) (by norm_num)
  rw [add_comm π]
  simp only [polarPoint, cos_add_pi, sin_add_pi, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> norm_num

/-- Stitz-Zeager Exercise 11.4.34: the polar point `(2/3, π + arctan (2√2))` is `(-2/9, -4√2/9)` in
rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.34, p. 942"]
theorem exer_11_4_34 :
    polarPoint (2 / 3) (π + arctan (2 * √2)) = (-(2 / 9), -(4 * √2 / 9)) := by
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h5 : √(1 + (2 * √2 : ℝ) ^ 2) = 3 := by
    rw [show 1 + (2 * √2 : ℝ) ^ 2 = 3 ^ 2 by nlinarith, Real.sqrt_sq (by norm_num)]
  rw [add_comm π]
  simp only [polarPoint, cos_add_pi, sin_add_pi, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.35: the polar point `(π, arctan π)` is `(π/√(1+π²), π²/√(1+π²))` in
rectangular coordinates. -/
@[kb "stitzzeager2013" "Exercise 11.4.35, p. 942"]
theorem exer_11_4_35 :
    polarPoint π (arctan π) = (π / √(1 + π ^ 2), π ^ 2 / √(1 + π ^ 2)) := by
  simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, Prod.mk.injEq]
  constructor <;> ring

/-- Stitz-Zeager Exercise 11.4.37: the rectangular point `(0, 5)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(5, π/2)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.37, p. 942"]
theorem exer_11_4_37 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (0, 5) ↔ r = 5 ∧ θ = π / 2 := by
  have hpi := pi_pos
  have e : ((0 : ℝ), 5) = polarPoint 5 (π / 2) := by
    simp only [polarPoint, cos_pi_div_two, sin_pi_div_two, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w4_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.40: the rectangular point `(-3, -√3)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(2√3, 7π/6)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.40, p. 942"]
theorem exer_11_4_40 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-3, -√3) ↔ r = 2 * √3 ∧ θ = 7 * π / 6 := by
  have hpi := pi_pos
  have hs : (0 : ℝ) < √3 := by positivity
  have hss : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have e : ((-3 : ℝ), -√3) = polarPoint (2 * √3) (7 * π / 6) := by
    have : 7 * π / 6 = π / 6 + π := by ring
    simp only [polarPoint, this, cos_add_pi, sin_add_pi, cos_pi_div_six, sin_pi_div_six, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e, w4_conv (by positivity) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.41: the rectangular point `(-3, 0)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(3, π)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.41, p. 942"]
theorem exer_11_4_41 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-3, 0) ↔ r = 3 ∧ θ = π := by
  have hpi := pi_pos
  have e : ((-3 : ℝ), 0) = polarPoint 3 π := by
    simp only [polarPoint, cos_pi, sin_pi, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w4_conv (by norm_num) hpi.le (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.42: the rectangular point `(-√2, √2)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(2, 3π/4)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.42, p. 942"]
theorem exer_11_4_42 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-√2, √2) ↔ r = 2 ∧ θ = 3 * π / 4 := by
  have hpi := pi_pos
  have hss : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : ((-√2 : ℝ), √2) = polarPoint 2 (3 * π / 4) := by
    have : 3 * π / 4 = π - π / 4 := by ring
    simp only [polarPoint, this, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four, Prod.mk.injEq]
    constructor <;> nlinarith
  rw [e, w4_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.44: the rectangular point `(√3/4, -1/4)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(1/2, 11π/6)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.44, p. 942"]
theorem exer_11_4_44 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (√3 / 4, -(1 / 4)) ↔ r = 1 / 2 ∧ θ = 11 * π / 6 := by
  have hpi := pi_pos
  have e : ((√3 / 4, -(1 / 4)) : ℝ × ℝ) = polarPoint (1 / 2) (11 * π / 6) := by
    have : 11 * π / 6 = -(π / 6) + 2 * π := by ring
    simp only [polarPoint, this, cos_add_two_pi, sin_add_two_pi, cos_neg, sin_neg, cos_pi_div_six,
      sin_pi_div_six, Prod.mk.injEq]
    constructor <;> ring
  rw [e, w4_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.45: the rectangular point `(-3/10, -3√3/10)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(3/5, 4π/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.45, p. 943"]
theorem exer_11_4_45 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-(3 / 10), -(3 * √3 / 10)) ↔ r = 3 / 5 ∧ θ = 4 * π / 3 := by
  have hpi := pi_pos
  have e : ((-(3 / 10), -(3 * √3 / 10)) : ℝ × ℝ) = polarPoint (3 / 5) (4 * π / 3) := by
    have : 4 * π / 3 = π / 3 + π := by ring
    simp only [polarPoint, this, cos_add_pi, sin_add_pi, cos_pi_div_three, sin_pi_div_three,
      Prod.mk.injEq]
    constructor <;> ring
  rw [e, w4_conv (by norm_num) (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.46: the rectangular point `(-√5, -√5)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(√10, 5π/4)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.46, p. 943"]
theorem exer_11_4_46 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-√5, -√5) ↔ r = √10 ∧ θ = 5 * π / 4 := by
  have hpi := pi_pos
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h10 : √10 = √5 * √2 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hs : (0 : ℝ) < √10 := by positivity
  have e : ((-√5 : ℝ), -√5) = polarPoint (√10) (5 * π / 4) := by
    have : 5 * π / 4 = π / 4 + π := by ring
    simp only [polarPoint, this, cos_add_pi, sin_add_pi, cos_pi_div_four, sin_pi_div_four, Prod.mk.injEq, h10]
    constructor <;> linear_combination (√5 / 2) * h2
  rw [e, w4_conv hs (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.48: the rectangular point `(√5, 2√5)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(5, arctan 2)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.48, p. 943"]
theorem exer_11_4_48 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (√5, 2 * √5) ↔ r = 5 ∧ θ = arctan 2 := by
  have hpi := pi_pos
  have h5 : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have hs : (0 : ℝ) < √5 := by positivity
  have hss : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have e : ((√5, 2 * √5) : ℝ × ℝ) = polarPoint 5 (arctan 2) := by
    simp only [polarPoint, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> field_simp <;> nlinarith
  have h0 : 0 ≤ arctan 2 := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two 2
  rw [e, w4_conv (by norm_num) h0 (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.50: the rectangular point `(-2√10, 6√10)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(20, π - arctan 3)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.50, p. 943"]
theorem exer_11_4_50 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-(2 * √10), 6 * √10) ↔ r = 20 ∧ θ = π - arctan 3 := by
  have hpi := pi_pos
  have h5 : √(1 + (3 : ℝ) ^ 2) = √10 := by norm_num
  have hs : (0 : ℝ) < √10 := by positivity
  have hss : √10 * √10 = 10 := Real.mul_self_sqrt (by norm_num)
  have e : ((-(2 * √10), 6 * √10) : ℝ × ℝ) = polarPoint 20 (π - arctan 3) := by
    simp only [polarPoint, cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> field_simp <;> nlinarith
  have h0 : 0 ≤ arctan 3 := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two 3
  rw [e, w4_conv (by norm_num) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.52: the rectangular point `(-√5/15, -2√5/15)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(1/3, π + arctan 2)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.52, p. 943"]
theorem exer_11_4_52 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-(√5 / 15), -(2 * √5 / 15)) ↔ r = 1 / 3 ∧ θ = π + arctan 2 := by
  have hpi := pi_pos
  have h5 : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have hs : (0 : ℝ) < √5 := by positivity
  have hss : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have e : ((-(√5 / 15), -(2 * √5 / 15)) : ℝ × ℝ) = polarPoint (1 / 3) (π + arctan 2) := by
    rw [add_comm π]
    simp only [polarPoint, cos_add_pi, sin_add_pi, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq]
    constructor <;> field_simp <;> nlinarith
  have h0 : 0 ≤ arctan 2 := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two 2
  rw [e, w4_conv (by norm_num) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.53: the rectangular point `(24, -7)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(25, 2π - arctan (7/24))`. -/
@[kb "stitzzeager2013" "Exercise 11.4.53, p. 943"]
theorem exer_11_4_53 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (24, -7) ↔ r = 25 ∧ θ = 2 * π - arctan (7 / 24) := by
  have hpi := pi_pos
  have h5 : √(1 + (7 / 24 : ℝ) ^ 2) = 25 / 24 := w4_sqrt_sq (by norm_num) (by norm_num)
  have e : ((24 : ℝ), -7) = polarPoint 25 (2 * π - arctan (7 / 24)) := by
    simp only [polarPoint, cos_two_pi_sub, sin_two_pi_sub, Real.cos_arctan, Real.sin_arctan, h5,
      Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 < arctan (7 / 24) := by simpa using arctan_strictMono (show (0 : ℝ) < 7 / 24 by norm_num)
  have h1 := arctan_lt_pi_div_two (7 / 24)
  rw [e, w4_conv (by norm_num) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.54: the rectangular point `(12, -9)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(15, 2π - arctan (3/4))`. -/
@[kb "stitzzeager2013" "Exercise 11.4.54, p. 943"]
theorem exer_11_4_54 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (12, -9) ↔ r = 15 ∧ θ = 2 * π - arctan (3 / 4) := by
  have hpi := pi_pos
  have h5 : √(1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := w4_sqrt_sq (by norm_num) (by norm_num)
  have e : ((12 : ℝ), -9) = polarPoint 15 (2 * π - arctan (3 / 4)) := by
    simp only [polarPoint, cos_two_pi_sub, sin_two_pi_sub, Real.cos_arctan, Real.sin_arctan, h5,
      Prod.mk.injEq]
    constructor <;> norm_num
  have h0 : 0 < arctan (3 / 4) := by simpa using arctan_strictMono (show (0 : ℝ) < 3 / 4 by norm_num)
  have h1 := arctan_lt_pi_div_two (3 / 4)
  rw [e, w4_conv (by norm_num) (by linarith) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.55: the rectangular point `(√2/4, √6/4)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(√2/2, π/3)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.55, p. 943"]
theorem exer_11_4_55 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (√2 / 4, √6 / 4) ↔ r = √2 / 2 ∧ θ = π / 3 := by
  have hpi := pi_pos
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h6 : √6 = √2 * √3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hs : (0 : ℝ) < √2 / 2 := by positivity
  have e : ((√2 / 4, √6 / 4) : ℝ × ℝ) = polarPoint (√2 / 2) (π / 3) := by
    simp only [polarPoint, cos_pi_div_three, sin_pi_div_three, Prod.mk.injEq, h6]
    constructor <;> ring
  rw [e, w4_conv hs (by positivity) (by linarith) hr hθ hθ2]

/-- Stitz-Zeager Exercise 11.4.56: the rectangular point `(-√65/5, 2√65/5)` has polar coordinates `r ≥ 0`,
`0 ≤ θ < 2π` exactly `(√13, π - arctan 2)`. -/
@[kb "stitzzeager2013" "Exercise 11.4.56, p. 943"]
theorem exer_11_4_56 (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ) (hθ2 : θ < 2 * π) :
    polarPoint r θ = (-(√65 / 5), 2 * √65 / 5) ↔ r = √13 ∧ θ = π - arctan 2 := by
  have hpi := pi_pos
  have h5 : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have h65 : √65 = √5 * √13 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hs5 : (0 : ℝ) < √5 := by positivity
  have hs : (0 : ℝ) < √13 := by positivity
  have hss : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have e : ((-(√65 / 5), 2 * √65 / 5) : ℝ × ℝ) = polarPoint (√13) (π - arctan 2) := by
    simp only [polarPoint, cos_pi_sub, sin_pi_sub, Real.cos_arctan, Real.sin_arctan, h5, Prod.mk.injEq, h65]
    constructor <;> field_simp <;> nlinarith
  have h0 : 0 ≤ arctan 2 := arctan_nonneg.mpr (by norm_num)
  have h1 := arctan_lt_pi_div_two 2
  rw [e, w4_conv hs (by linarith) (by linarith) hr hθ hθ2]


end UndergradKB.Precalculus.Course
