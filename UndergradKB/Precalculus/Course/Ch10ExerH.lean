import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.6
(solving trigonometric equations on `[0, 2π)` with inverse trigonometric functions) -/

namespace UndergradKB.Precalculus.Course

open Real

private lemma sin_sol_pos (y x : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = y ↔ x = arcsin y ∨ x = π - arcsin y := by
  obtain ⟨a, ha⟩ : ∃ a, a = arcsin y := ⟨_, rfl⟩
  have hs : sin a = y := by rw [ha]; exact sin_arcsin (by linarith) hy1.le
  have ha0 : 0 ≤ a := by rw [ha]; exact arcsin_nonneg.mpr hy0
  have ha1 : a < π / 2 := by rw [ha]; exact arcsin_lt_pi_div_two.mpr hy1
  rw [← ha, ← hs]
  have key : sin x = sin a ↔ sin a = sin x := eq_comm
  rw [key, sin_eq_sin_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, h | h⟩
    · have hk0 : (-1 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 1 := by exact_mod_cast hk1
      have : k = 0 := by omega
      subst this
      left; simpa using h
    · have hk0 : (-1 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 1 := by exact_mod_cast hk1
      have : k = 0 := by omega
      subst this
      right; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, Or.inl (by rw [h]; simp)⟩
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma sin_sol_neg (y x : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = -y ↔ x = π + arcsin y ∨ x = 2 * π - arcsin y := by
  obtain ⟨a, ha⟩ : ∃ a, a = arcsin y := ⟨_, rfl⟩
  have hs : sin (-a) = -y := by rw [sin_neg, ha, sin_arcsin (by linarith) hy1.le]
  have ha0 : 0 < a := by rw [ha]; exact arcsin_pos.mpr hy0
  have ha1 : a < π / 2 := by rw [ha]; exact arcsin_lt_pi_div_two.mpr hy1
  rw [← ha, ← hs]
  have key : sin x = sin (-a) ↔ sin (-a) = sin x := eq_comm
  rw [key, sin_eq_sin_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, h | h⟩
    · have hk0 : (0 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 2 := by nlinarith
      have h1 : (0 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 2 := by exact_mod_cast hk1
      have : k = 1 := by omega
      subst this
      right; rw [h]; push_cast; ring
    · have hk0 : (-1 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 1 := by exact_mod_cast hk1
      have : k = 0 := by omega
      subst this
      left; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inl (by rw [h]; push_cast; ring)⟩

private lemma cos_sol (y x : ℝ) (hy0 : -1 < y) (hy1 : y < 1) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = y ↔ x = arccos y ∨ x = 2 * π - arccos y := by
  obtain ⟨a, ha⟩ : ∃ a, a = arccos y := ⟨_, rfl⟩
  have hs : cos a = y := by rw [ha]; exact cos_arccos hy0.le hy1.le
  have ha0 : 0 < a := by rw [ha]; exact arccos_pos.mpr hy1
  have ha1 : a < π := by rw [ha]; exact arccos_lt_pi.mpr hy0
  rw [← ha, ← hs]
  have key : cos x = cos a ↔ cos a = cos x := eq_comm
  rw [key, cos_eq_cos_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, h | h⟩
    · have hk0 : (-1 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 1 := by exact_mod_cast hk1
      have : k = 0 := by omega
      subst this
      left; simpa using h
    · have hk0 : (0 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 2 := by nlinarith
      have h1 : (0 : ℤ) < k := by exact_mod_cast hk0
      have h2 : k < 2 := by exact_mod_cast hk1
      have : k = 1 := by omega
      subst this
      right; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, Or.inl (by rw [h]; simp)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma tan_iff' {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    tan θ = tan a ↔ ∃ k : ℤ, θ = a + π * k := by
  constructor
  · intro h
    have ha : tan a ≠ 0 := by rw [tan_eq_sin_div_cos]; exact div_ne_zero hs hc
    have hθ : cos θ ≠ 0 := fun h0 => ha (h ▸ tan_eq_zero_of_cos_eq_zero h0)
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hθ hc] at h
    have : sin (θ - a) = 0 := by rw [sin_sub]; linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp this
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [mul_comm]; exact tan_add_int_mul_pi a k

private lemma arctan_cs (y : ℝ) (hy : y ≠ 0) : cos (arctan y) ≠ 0 ∧ sin (arctan y) ≠ 0 := by
  have hc : 0 < cos (arctan y) := cos_arctan_pos y
  refine ⟨hc.ne', ?_⟩
  have h := tan_arctan y
  rw [tan_eq_sin_div_cos, div_eq_iff hc.ne'] at h
  rw [h]; exact mul_ne_zero hy hc.ne'

private lemma tan_sol_pos (y x : ℝ) (hy : 0 < y) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = y ↔ x = arctan y ∨ x = arctan y + π := by
  obtain ⟨a, ha⟩ : ∃ a, a = arctan y := ⟨_, rfl⟩
  have hs : tan a = y := by rw [ha]; exact tan_arctan y
  have ha0 : 0 < a := by rw [ha]; exact arctan_pos.mpr hy
  have ha1 : a < π / 2 := by rw [ha]; exact arctan_lt_pi_div_two y
  have hcs := arctan_cs y hy.ne'
  rw [← ha] at hcs
  rw [← ha, ← hs, tan_iff' hcs.1 hcs.2]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, h⟩
    have hk0 : (-1 : ℝ) < k := by nlinarith
    have hk1 : (k : ℝ) < 2 := by nlinarith
    have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
    have h2 : k < 2 := by exact_mod_cast hk1
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · left; simpa using h
    · right; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; push_cast; ring⟩

private lemma tan_sol_neg (y x : ℝ) (hy : y < 0) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = y ↔ x = arctan y + π ∨ x = arctan y + 2 * π := by
  obtain ⟨a, ha⟩ : ∃ a, a = arctan y := ⟨_, rfl⟩
  have hs : tan a = y := by rw [ha]; exact tan_arctan y
  have ha0 : a < 0 := by
    rw [ha, ← arctan_zero]; exact arctan_strictMono hy
  have ha1 : -(π / 2) < a := by rw [ha]; exact neg_pi_div_two_lt_arctan y
  have hcs := arctan_cs y hy.ne
  rw [← ha] at hcs
  rw [← ha, ← hs, tan_iff' hcs.1 hcs.2]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, h⟩
    have hk0 : (0 : ℝ) < k := by nlinarith
    have hk1 : (k : ℝ) < 3 := by nlinarith
    have h1 : (0 : ℤ) < k := by exact_mod_cast hk0
    have h2 : k < 3 := by exact_mod_cast hk1
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl
    · left; rw [h]; push_cast; ring
    · right; rw [h]; push_cast; ring
  · rintro (h | h)
    · exact ⟨1, by rw [h]; push_cast; ring⟩
    · exact ⟨2, by rw [h]; push_cast; ring⟩

private lemma cot_tan (x c : ℝ) : cos x / sin x = c ↔ tan x = c⁻¹ := by
  have e : cos x / sin x = (tan x)⁻¹ := by rw [tan_eq_sin_div_cos, inv_div]
  rw [e, inv_eq_iff_eq_inv]

/-- Stitz-Zeager Exercise 10.6.188: on `[0, 2π)`, `sin x = 7/11` exactly when `x = arcsin(7/11)`
or `x = π - arcsin(7/11)` (about `0.6898` and `2.4518`). -/
@[kb "stitzzeager2013" "Exercise 10.6.188, p. 857"]
theorem exer_10_6_188 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = 7 / 11 ↔ x = arcsin (7 / 11) ∨ x = π - arcsin (7 / 11) :=
  sin_sol_pos _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.189: on `[0, 2π)`, `cos x = -2/9` exactly when
`x = arccos(-2/9)` or `x = 2π - arccos(-2/9)` (about `1.7949` and `4.4883`). -/
@[kb "stitzzeager2013" "Exercise 10.6.189, p. 857"]
theorem exer_10_6_189 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = -(2 / 9) ↔ x = arccos (-(2 / 9)) ∨ x = 2 * π - arccos (-(2 / 9)) :=
  cos_sol _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.190: on `[0, 2π)`, `sin x = -0.569` exactly when
`x = π + arcsin(0.569)` or `x = 2π - arcsin(0.569)` (about `3.7469` and `5.6779`). -/
@[kb "stitzzeager2013" "Exercise 10.6.190, p. 857"]
theorem exer_10_6_190 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = -0.569 ↔ x = π + arcsin 0.569 ∨ x = 2 * π - arcsin 0.569 :=
  sin_sol_neg _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.191: on `[0, 2π)`, `cos x = 0.117` exactly when
`x = arccos(0.117)` or `x = 2π - arccos(0.117)` (about `1.4535` and `4.8297`). -/
@[kb "stitzzeager2013" "Exercise 10.6.191, p. 857"]
theorem exer_10_6_191 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = 0.117 ↔ x = arccos 0.117 ∨ x = 2 * π - arccos 0.117 :=
  cos_sol _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.192: on `[0, 2π)`, `sin x = 0.008` exactly when
`x = arcsin(0.008)` or `x = π - arcsin(0.008)` (about `0.0080` and `3.1336`). -/
@[kb "stitzzeager2013" "Exercise 10.6.192, p. 857"]
theorem exer_10_6_192 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = 0.008 ↔ x = arcsin 0.008 ∨ x = π - arcsin 0.008 :=
  sin_sol_pos _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.193: on `[0, 2π)`, `cos x = 359/360` exactly when
`x = arccos(359/360)` or `x = 2π - arccos(359/360)` (about `0.0746` and `6.2086`). -/
@[kb "stitzzeager2013" "Exercise 10.6.193, p. 857"]
theorem exer_10_6_193 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = 359 / 360 ↔ x = arccos (359 / 360) ∨ x = 2 * π - arccos (359 / 360) :=
  cos_sol _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.194: on `[0, 2π)`, `tan x = 117` exactly when `x = arctan 117` or
`x = arctan 117 + π` (about `1.5622` and `4.7038`). -/
@[kb "stitzzeager2013" "Exercise 10.6.194, p. 857"]
theorem exer_10_6_194 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = 117 ↔ x = arctan 117 ∨ x = arctan 117 + π :=
  tan_sol_pos _ x (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.195: on `[0, 2π)`, `cot x = -12` exactly when
`x = arctan(-1/12) + π` or `x = arctan(-1/12) + 2π` (about `3.0585` and `6.2000`). -/
@[kb "stitzzeager2013" "Exercise 10.6.195, p. 857"]
theorem exer_10_6_195 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x / sin x = -12 ↔ x = arctan (-(1 / 12)) + π ∨ x = arctan (-(1 / 12)) + 2 * π := by
  rw [cot_tan, show (-12 : ℝ)⁻¹ = -(1 / 12) by norm_num]
  exact tan_sol_neg _ x (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.196: on `[0, 2π)`, `sec x = 3/2` exactly when `x = arccos(2/3)` or
`x = 2π - arccos(2/3)` (about `0.8411` and `5.4422`). -/
@[kb "stitzzeager2013" "Exercise 10.6.196, p. 857"]
theorem exer_10_6_196 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    (cos x)⁻¹ = 3 / 2 ↔ x = arccos (2 / 3) ∨ x = 2 * π - arccos (2 / 3) := by
  rw [inv_eq_iff_eq_inv, show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num]
  exact cos_sol _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.197: on `[0, 2π)`, `csc x = -90/17` exactly when
`x = π + arcsin(17/90)` or `x = 2π - arcsin(17/90)` (about `3.3316` and `6.0932`). -/
@[kb "stitzzeager2013" "Exercise 10.6.197, p. 857"]
theorem exer_10_6_197 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    (sin x)⁻¹ = -(90 / 17) ↔ x = π + arcsin (17 / 90) ∨ x = 2 * π - arcsin (17 / 90) := by
  rw [inv_eq_iff_eq_inv, show (-(90 / 17 : ℝ))⁻¹ = -(17 / 90) by norm_num]
  exact sin_sol_neg _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.198: on `[0, 2π)`, `tan x = -√10` exactly when
`x = arctan(-√10) + π` or `x = arctan(-√10) + 2π` (about `1.8771` and `5.0187`). -/
@[kb "stitzzeager2013" "Exercise 10.6.198, p. 857"]
theorem exer_10_6_198 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = -√10 ↔ x = arctan (-√10) + π ∨ x = arctan (-√10) + 2 * π :=
  tan_sol_neg _ x (by have : 0 < √10 := by positivity
                      linarith) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.199: on `[0, 2π)`, `sin x = 3/8` exactly when `x = arcsin(3/8)` or
`x = π - arcsin(3/8)` (about `0.3844` and `2.7572`). -/
@[kb "stitzzeager2013" "Exercise 10.6.199, p. 857"]
theorem exer_10_6_199 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = 3 / 8 ↔ x = arcsin (3 / 8) ∨ x = π - arcsin (3 / 8) :=
  sin_sol_pos _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.200: on `[0, 2π)`, `cos x = -7/16` exactly when
`x = arccos(-7/16)` or `x = 2π - arccos(-7/16)` (about `2.0236` and `4.2596`). -/
@[kb "stitzzeager2013" "Exercise 10.6.200, p. 857"]
theorem exer_10_6_200 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = -(7 / 16) ↔ x = arccos (-(7 / 16)) ∨ x = 2 * π - arccos (-(7 / 16)) :=
  cos_sol _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.201: on `[0, 2π)`, `tan x = 0.03` exactly when `x = arctan(0.03)` or
`x = arctan(0.03) + π` (about `0.0300` and `3.1716`). -/
@[kb "stitzzeager2013" "Exercise 10.6.201, p. 857"]
theorem exer_10_6_201 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = 0.03 ↔ x = arctan 0.03 ∨ x = arctan 0.03 + π :=
  tan_sol_pos _ x (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.202: on `[0, 2π)`, `sin x = 0.3502` exactly when
`x = arcsin(0.3502)` or `x = π - arcsin(0.3502)` (about `0.3578` and `2.7838`; the book prints
`2.784`). -/
@[kb "stitzzeager2013" "Exercise 10.6.202, p. 857"]
theorem exer_10_6_202 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = 0.3502 ↔ x = arcsin 0.3502 ∨ x = π - arcsin 0.3502 :=
  sin_sol_pos _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.203: on `[0, 2π)`, `sin x = -0.721` exactly when
`x = π + arcsin(0.721)` or `x = 2π - arcsin(0.721)` (about `3.9468` and `5.4780`). -/
@[kb "stitzzeager2013" "Exercise 10.6.203, p. 858"]
theorem exer_10_6_203 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = -0.721 ↔ x = π + arcsin 0.721 ∨ x = 2 * π - arcsin 0.721 :=
  sin_sol_neg _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.204: on `[0, 2π)`, `cos x = 0.9824` exactly when
`x = arccos(0.9824)` or `x = 2π - arccos(0.9824)` (about `0.1879` and `6.0953`). -/
@[kb "stitzzeager2013" "Exercise 10.6.204, p. 858"]
theorem exer_10_6_204 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = 0.9824 ↔ x = arccos 0.9824 ∨ x = 2 * π - arccos 0.9824 :=
  cos_sol _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.205: on `[0, 2π)`, `cos x = -0.5637` exactly when
`x = arccos(-0.5637)` or `x = 2π - arccos(-0.5637)` (about `2.1697` and `4.1135`). -/
@[kb "stitzzeager2013" "Exercise 10.6.205, p. 858"]
theorem exer_10_6_205 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = -0.5637 ↔ x = arccos (-0.5637) ∨ x = 2 * π - arccos (-0.5637) :=
  cos_sol _ x (by norm_num) (by norm_num) hx0 hx1

/-- Stitz-Zeager Exercise 10.6.207: on `[0, 2π)`, `tan x = -0.6109` exactly when
`x = arctan(-0.6109) + π` or `x = arctan(-0.6109) + 2π` (about `2.5932` and `5.7348`). -/
@[kb "stitzzeager2013" "Exercise 10.6.207, p. 858"]
theorem exer_10_6_207 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = -0.6109 ↔ x = arctan (-0.6109) + π ∨ x = arctan (-0.6109) + 2 * π :=
  tan_sol_neg _ x (by norm_num) hx0 hx1

end UndergradKB.Precalculus.Course
