import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.7 (equations on [0, 2π), part 2)

Solutions on `[0, 2π)` are stated as `↔` with the finite list of solutions; for the expressions involving
`tan`, `sec`, `csc`, `cot` the domain hypotheses (nonvanishing denominators) are part of the statement,
because Lean's `x⁻¹` and `tan` take the value `0` where the book's functions are undefined. -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Close `x = a₁ ∨ x = a₂ ∨ ...` from a linear equation for `x` in terms of `π`. -/
macro "pick_sol_p" : tactic =>
  `(tactic| (push_cast at *; repeat' (first | (left; linarith; done) | right); try linarith))

/-- Pair the two directions of a `sin`/`cos` equality solved by Mathlib's `*_eq_*_iff`. -/
macro "key_tac_p" : tactic =>
  `(tactic| (constructor <;> rintro ⟨k, h | h⟩ <;>
    first | exact ⟨k, Or.inl (by linarith)⟩ | exact ⟨k, Or.inr (by linarith)⟩))

/-- Rearrange a disjunction of equalities. -/
macro "rearr_p" : tactic =>
  `(tactic| (simp only [or_assoc, or_comm, or_left_comm, or_self, or_self_left]; try done))

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


private lemma s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma s5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma sinP (a x : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = sin a ↔ x = a ∨ x = π - a := by
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

private lemma sinN (a x : ℝ) (ha0 : 0 < a) (ha1 : a ≤ π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = -sin a ↔ x = π + a ∨ x = 2 * π - a := by
  rw [← sin_neg]
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

private lemma cosP (a x : ℝ) (ha0 : 0 < a) (ha1 : a < π) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = cos a ↔ x = a ∨ x = 2 * π - a := by
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

private lemma tanP (a x : ℝ) (ha0 : 0 < a) (ha1 : a < π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = tan a ↔ x = a ∨ x = a + π := by
  have hc : cos a ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩).ne'
  have hs : sin a ≠ 0 := (sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])).ne'
  rw [tan_iff' hc hs]
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

private lemma tanN (a x : ℝ) (ha0 : 0 < a) (ha1 : a < π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = -tan a ↔ x = π - a ∨ x = 2 * π - a := by
  have hc : cos (-a) ≠ 0 := by
    rw [cos_neg]; exact (cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩).ne'
  have hs : sin (-a) ≠ 0 := by
    rw [sin_neg]; exact neg_ne_zero.2 (sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])).ne'
  rw [← tan_neg, tan_iff' hc hs]
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

private lemma sinEq {a b c x : ℝ} (hc : sin a = c) (hb : b = π - a) (ha0 : 0 ≤ a)
    (ha1 : a ≤ π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) : sin x = c ↔ x = a ∨ x = b := by
  subst hc hb; exact sinP a x ha0 ha1 hx0 hx1

private lemma sinNEq {a b d c x : ℝ} (hc : sin a = c) (hb : b = π + a) (hd : d = 2 * π - a)
    (ha0 : 0 < a) (ha1 : a ≤ π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x = -c ↔ x = b ∨ x = d := by
  subst hc hb hd; exact sinN a x ha0 ha1 hx0 hx1

private lemma cosEq {a b c x : ℝ} (hc : cos a = c) (hb : b = 2 * π - a) (ha0 : 0 < a)
    (ha1 : a < π) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) : cos x = c ↔ x = a ∨ x = b := by
  subst hc hb; exact cosP a x ha0 ha1 hx0 hx1

private lemma tanEq {a b c x : ℝ} (hc : tan a = c) (hb : b = a + π) (ha0 : 0 < a)
    (ha1 : a < π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) : tan x = c ↔ x = a ∨ x = b := by
  subst hc hb; exact tanP a x ha0 ha1 hx0 hx1

private lemma tanNEq {a b d c x : ℝ} (hc : tan a = c) (hb : b = π - a) (hd : d = 2 * π - a)
    (ha0 : 0 < a) (ha1 : a < π / 2) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    tan x = -c ↔ x = b ∨ x = d := by
  subst hc hb hd; exact tanN a x ha0 ha1 hx0 hx1

private lemma sin0 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 2 * π) : sin x = 0 ↔ x = 0 ∨ x = π := by
  rw [sin_eq_zero_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨n, hn⟩
    have hk0 : (-1 : ℝ) < n := by nlinarith
    have hk1 : (n : ℝ) < 2 := by nlinarith
    have h1 : (-1 : ℤ) < n := by exact_mod_cast hk0
    have h2 : n < 2 := by exact_mod_cast hk1
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · left; simpa using hn.symm
    · right; simpa using hn.symm
  · rintro (h | h)
    · exact ⟨0, by rw [h]; simp⟩
    · exact ⟨1, by rw [h]; simp⟩

private lemma cos0 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x = 0 ↔ x = π / 2 ∨ x = 3 * π / 2 := by
  rw [cos_eq_zero_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨k, hk⟩
    have hk0 : (-1 : ℝ) < k := by nlinarith
    have hk1 : (k : ℝ) < 2 := by nlinarith
    have h1 : (-1 : ℤ) < k := by exact_mod_cast hk0
    have h2 : k < 2 := by exact_mod_cast hk1
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · left; rw [hk]; push_cast; ring
    · right; rw [hk]; push_cast; ring
  · rintro (h | h)
    · exact ⟨0, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by rw [h]; push_cast; ring⟩

private lemma sec_sq {x : ℝ} (hc : cos x ≠ 0) : ((cos x)⁻¹) ^ 2 = 1 + tan x ^ 2 := by
  rw [tan_eq_sin_div_cos, inv_pow, div_pow]
  field_simp
  linarith [sin_sq_add_cos_sq x]

private lemma csc_sq {x : ℝ} (hs : sin x ≠ 0) : ((sin x)⁻¹) ^ 2 = 1 + (cos x / sin x) ^ 2 := by
  rw [inv_pow, div_pow]
  field_simp
  linarith [sin_sq_add_cos_sq x]

private lemma cos1 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 2 * π) : cos x = 1 ↔ x = 0 := by
  rw [cos_eq_one_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨n, hn⟩
    have hk0 : (-1 : ℝ) < n := by nlinarith
    have hk1 : (n : ℝ) < 1 := by nlinarith
    have h1 : (-1 : ℤ) < n := by exact_mod_cast hk0
    have h2 : n < 1 := by exact_mod_cast hk1
    have : n = 0 := by omega
    subst this
    simpa using hn.symm
  · intro h; exact ⟨0, by rw [h]; simp⟩

private lemma c23 : cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]

private lemma c34 : cos (3 * π / 4) = -(√2 / 2) := by
  rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]

/-- Stitz-Zeager Exercise 10.7.21: on `[0, 2π)`, `sin 2x = cos x` exactly when `x = π/6, π/2, 5π/6, 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.21, p. 886"]
theorem exer_10_7_21 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin (2 * x) = cos x ↔ x = π / 6 ∨ x = π / 2 ∨ x = 5 * π / 6 ∨ x = 3 * π / 2 := by
  have e : sin (2 * x) = cos x ↔ cos x = 0 ∨ sin x = 1 / 2 := by
    rw [sin_two_mul]
    constructor
    · intro h
      have h' : cos x * (2 * sin x - 1) = 0 := by linarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · rw [h]; ring
      · rw [h]; ring
  have hs := sinEq (a := π / 6) (b := 5 * π / 6) sin_pi_div_six (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  rw [e, cos0 hx0 hx1, hs]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.22: on `[0, 2π)`, `cos 2x = sin x` exactly when `x = π/6, 5π/6, 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.22, p. 886"]
theorem exer_10_7_22 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (2 * x) = sin x ↔ x = π / 6 ∨ x = 5 * π / 6 ∨ x = 3 * π / 2 := by
  have e : cos (2 * x) = sin x ↔ sin x = 1 / 2 ∨ sin x = -1 := by
    rw [cos_two_mul]
    have hh := sin_sq_add_cos_sq x
    constructor
    · intro h
      have h' : (2 * sin x - 1) * (sin x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · rw [h] at hh ⊢; nlinarith
      · rw [h] at hh ⊢; nlinarith
  have hs1 := sinEq (a := π / 6) (b := 5 * π / 6) sin_pi_div_six (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have hs2 := sinNEq (a := π / 2) (b := 3 * π / 2) (d := 3 * π / 2) (c := 1) sin_pi_div_two
    (by ring) (by ring) (by positivity) (le_refl _) hx0 hx1
  rw [e, hs1, hs2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.25: on `[0, 2π)`, `3 cos 2x + cos x + 2 = 0` exactly when
`cos x = -1/2` or `cos x = 1/3`: `x = 2π/3, 4π/3, arccos(1/3), 2π - arccos(1/3)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.25, p. 886"]
theorem exer_10_7_25 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    3 * cos (2 * x) + cos x + 2 = 0 ↔
      x = 2 * π / 3 ∨ x = 4 * π / 3 ∨ x = arccos (1 / 3) ∨ x = 2 * π - arccos (1 / 3) := by
  have e : 3 * cos (2 * x) + cos x + 2 = 0 ↔ cos x = 1 / 3 ∨ cos x = -(1 / 2) := by
    rw [cos_two_mul]
    constructor
    · intro h
      have h' : (3 * cos x - 1) * (2 * cos x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] <;> norm_num
  have h1 := cosEq (a := arccos (1 / 3)) (b := 2 * π - arccos (1 / 3))
    (cos_arccos (by norm_num) (by norm_num)) rfl (arccos_pos.2 (by norm_num))
    (arccos_lt_pi.2 (by norm_num)) hx0 hx1
  have h2 := cosEq (a := 2 * π / 3) (b := 4 * π / 3) (c := -(1 / 2)) c23 (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  rw [e, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.27: on `[0, 2π)`, `3 cos 2x = sin x + 2` exactly when
`x = 7π/6, 11π/6, arcsin(1/3), π - arcsin(1/3)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.27, p. 886"]
theorem exer_10_7_27 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    3 * cos (2 * x) = sin x + 2 ↔
      x = 7 * π / 6 ∨ x = 11 * π / 6 ∨ x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3) := by
  have e : 3 * cos (2 * x) = sin x + 2 ↔ sin x = 1 / 3 ∨ sin x = -(1 / 2) := by
    rw [cos_two_mul]
    have hh := sin_sq_add_cos_sq x
    constructor
    · intro h
      have h' : (3 * sin x - 1) * (2 * sin x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · rw [h] at hh ⊢; nlinarith
      · rw [h] at hh ⊢; nlinarith
  have h1 := sinEq (a := arcsin (1 / 3)) (b := π - arcsin (1 / 3))
    (sin_arcsin (by norm_num) (by norm_num)) rfl (arcsin_nonneg.2 (by norm_num))
    (arcsin_le_pi_div_two _) hx0 hx1
  have h2 := sinNEq (a := π / 6) (b := 7 * π / 6) (d := 11 * π / 6) (c := 1 / 2) sin_pi_div_six
    (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  rw [e, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.28: for `cos x ≠ 0` on `[0, 2π)`, `2 sec²x = 3 - tan x` exactly when
`x = 3π/4, 7π/4, arctan(1/2), arctan(1/2) + π`. -/
@[kb "stitzzeager2013" "Exercise 10.7.28, p. 886"]
theorem exer_10_7_28 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hc : cos x ≠ 0) :
    2 * ((cos x)⁻¹) ^ 2 = 3 - tan x ↔
      x = 3 * π / 4 ∨ x = 7 * π / 4 ∨ x = arctan (1 / 2) ∨ x = arctan (1 / 2) + π := by
  have e : 2 * ((cos x)⁻¹) ^ 2 = 3 - tan x ↔ tan x = 1 / 2 ∨ tan x = -1 := by
    rw [sec_sq hc]
    constructor
    · intro h
      have h' : (2 * tan x - 1) * (tan x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] <;> norm_num
  have h1 := tanEq (a := arctan (1 / 2)) (b := arctan (1 / 2) + π) (tan_arctan _) rfl
    (arctan_pos.2 (by norm_num)) (arctan_lt_pi_div_two _) hx0 hx1
  have h2 := tanNEq (a := π / 4) (b := 3 * π / 4) (d := 7 * π / 4) (c := 1) tan_pi_div_four
    (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  rw [e, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.29: for `cos x ≠ 0` on `[0, 2π)`, `tan²x = 1 - sec x` exactly when
`x = 0, 2π/3, 4π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.29, p. 886"]
theorem exer_10_7_29 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hc : cos x ≠ 0) :
    tan x ^ 2 = 1 - (cos x)⁻¹ ↔ x = 0 ∨ x = 2 * π / 3 ∨ x = 4 * π / 3 := by
  have hs := sec_sq hc
  have hu1 : (cos x)⁻¹ = 1 ↔ cos x = 1 := inv_eq_one
  have hu2 : (cos x)⁻¹ = -2 ↔ cos x = -(1 / 2) := by
    rw [inv_eq_iff_eq_inv]; norm_num
  have e : tan x ^ 2 = 1 - (cos x)⁻¹ ↔ cos x = 1 ∨ cos x = -(1 / 2) := by
    rw [← hu1, ← hu2]
    constructor
    · intro h
      have h' : ((cos x)⁻¹ - 1) * ((cos x)⁻¹ + 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] at hs ⊢ <;> nlinarith
  have h2 := cosEq (a := 2 * π / 3) (b := 4 * π / 3) (c := -(1 / 2)) c23 (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  rw [e, cos1 hx0 hx1, h2]

/-- Stitz-Zeager Exercise 10.7.30: for `sin x ≠ 0` on `[0, 2π)`, `cot²x = 3 csc x - 3` exactly when
`x = π/6, 5π/6, π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.30, p. 886"]
theorem exer_10_7_30 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hs : sin x ≠ 0) :
    (cos x / sin x) ^ 2 = 3 * (sin x)⁻¹ - 3 ↔ x = π / 6 ∨ x = 5 * π / 6 ∨ x = π / 2 := by
  have hq := csc_sq hs
  have hu1 : (sin x)⁻¹ = 1 ↔ sin x = 1 := inv_eq_one
  have hu2 : (sin x)⁻¹ = 2 ↔ sin x = 1 / 2 := by
    rw [inv_eq_iff_eq_inv]; norm_num
  have e : (cos x / sin x) ^ 2 = 3 * (sin x)⁻¹ - 3 ↔ sin x = 1 ∨ sin x = 1 / 2 := by
    rw [← hu1, ← hu2]
    constructor
    · intro h
      have h' : ((sin x)⁻¹ - 1) * ((sin x)⁻¹ - 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] at hq ⊢ <;> nlinarith
  have h1 := sinEq (a := π / 6) (b := 5 * π / 6) sin_pi_div_six (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have h2 := sinEq (a := π / 2) (b := π / 2) (c := 1) sin_pi_div_two (by ring) (by positivity)
    (le_refl _) hx0 hx1
  rw [e, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.31: for `cos x ≠ 0`, `sin x ≠ 0` on `[0, 2π)`, `sec x = 2 csc x` exactly
when `x = arctan 2` or `x = arctan 2 + π`. -/
@[kb "stitzzeager2013" "Exercise 10.7.31, p. 886"]
theorem exer_10_7_31 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hc : cos x ≠ 0) (hs : sin x ≠ 0) :
    (cos x)⁻¹ = 2 * (sin x)⁻¹ ↔ x = arctan 2 ∨ x = arctan 2 + π := by
  have e : (cos x)⁻¹ = 2 * (sin x)⁻¹ ↔ tan x = 2 := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc]
    constructor
    · intro h; field_simp at h; linarith
    · intro h; field_simp; linarith
  have h1 := tanEq (a := arctan 2) (b := arctan 2 + π) (tan_arctan _) rfl
    (arctan_pos.2 (by norm_num)) (arctan_lt_pi_div_two _) hx0 hx1
  rw [e, h1]

/-- Stitz-Zeager Exercise 10.7.32: for `sin x ≠ 0` on `[0, 2π)`, `cos x csc x cot x = 6 - cot²x` exactly
when `x = π/6, 5π/6, 7π/6, 11π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.32, p. 886"]
theorem exer_10_7_32 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hs : sin x ≠ 0) :
    cos x * (sin x)⁻¹ * (cos x / sin x) = 6 - (cos x / sin x) ^ 2 ↔
      x = π / 6 ∨ x = 5 * π / 6 ∨ x = 7 * π / 6 ∨ x = 11 * π / 6 := by
  have hs2 : sin x ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h1 : cos x * (sin x)⁻¹ * (cos x / sin x) = cos x ^ 2 / sin x ^ 2 := by
    field_simp
  have e : cos x * (sin x)⁻¹ * (cos x / sin x) = 6 - (cos x / sin x) ^ 2 ↔
      sin x = 1 / 2 ∨ sin x = -(1 / 2) := by
    rw [h1, div_pow]
    have hh := sin_sq_add_cos_sq x
    constructor
    · intro h
      have h2 : cos x ^ 2 / sin x ^ 2 = 3 := by linarith
      rw [div_eq_iff hs2] at h2
      have h' : (2 * sin x - 1) * (2 * sin x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · intro h
      have hsq : sin x ^ 2 = 1 / 4 := by rcases h with h | h <;> rw [h] <;> norm_num
      have hcq : cos x ^ 2 = 3 / 4 := by linarith
      rw [hsq, hcq]; norm_num
  have h1 := sinEq (a := π / 6) (b := 5 * π / 6) sin_pi_div_six (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have h2 := sinNEq (a := π / 6) (b := 7 * π / 6) (d := 11 * π / 6) (c := 1 / 2) sin_pi_div_six
    (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  rw [e, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.33: for `cos x ≠ 0` on `[0, 2π)`, `sin 2x = tan x` exactly when
`x = 0, π, π/4, 3π/4, 5π/4, 7π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.7.33, p. 886"]
theorem exer_10_7_33 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hc : cos x ≠ 0) :
    sin (2 * x) = tan x ↔
      x = 0 ∨ x = π ∨ x = π / 4 ∨ x = 3 * π / 4 ∨ x = 5 * π / 4 ∨ x = 7 * π / 4 := by
  have e : sin (2 * x) = tan x ↔ sin x = 0 ∨ cos x = √2 / 2 ∨ cos x = -(√2 / 2) := by
    rw [tan_eq_sin_div_cos, sin_two_mul, eq_div_iff hc]
    constructor
    · intro h
      have h' : sin x * ((cos x - √2 / 2) * (cos x + √2 / 2)) = 0 := by
        linear_combination (1 / 2) * h - (sin x / 4) * s2
      rcases mul_eq_zero.1 h' with h1 | h1
      · exact Or.inl h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
    · rintro (h | h | h)
      · rw [h]; ring
      · rw [h]; linear_combination (sin x / 2) * s2
      · rw [h]; linear_combination (sin x / 2) * s2
  have h0 := sin0 hx0 hx1
  have h1 := cosEq (a := π / 4) (b := 7 * π / 4) cos_pi_div_four (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have h2 := cosEq (a := 3 * π / 4) (b := 5 * π / 4) (c := -(√2 / 2)) c34 (by ring)
    (by positivity) (by linarith [pi_pos]) hx0 hx1
  rw [e, h0, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.34: for `sin x ≠ 0` on `[0, 2π)`, `cot⁴x = 4 csc²x - 7` exactly when
`sin x = ±1/2` or `sin x = ±√2/2`: `x = π/6, π/4, 3π/4, 5π/6, 7π/6, 5π/4, 7π/4, 11π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.34, p. 886"]
theorem exer_10_7_34 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hs : sin x ≠ 0) :
    (cos x / sin x) ^ 4 = 4 * ((sin x)⁻¹) ^ 2 - 7 ↔
      x = π / 6 ∨ x = π / 4 ∨ x = 3 * π / 4 ∨ x = 5 * π / 6 ∨ x = 7 * π / 6 ∨ x = 5 * π / 4 ∨
        x = 7 * π / 4 ∨ x = 11 * π / 6 := by
  have hs2 : sin x ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hs4 : sin x ^ 4 ≠ 0 := pow_ne_zero 4 hs
  have e : (cos x / sin x) ^ 4 = 4 * ((sin x)⁻¹) ^ 2 - 7 ↔
      (4 * sin x ^ 2 - 1) * (2 * sin x ^ 2 - 1) = 0 := by
    have h4 : (cos x / sin x) ^ 4 = (1 - sin x ^ 2) ^ 2 / sin x ^ 4 := by
      rw [div_pow, show cos x ^ 4 = (cos x ^ 2) ^ 2 by ring, cos_sq']
    have h2 : ((sin x)⁻¹) ^ 2 = 1 / sin x ^ 2 := by rw [inv_pow, one_div]
    rw [h4, h2, div_eq_iff hs4]
    have h3 : (4 * (1 / sin x ^ 2) - 7) * sin x ^ 4 = 4 * sin x ^ 2 - 7 * sin x ^ 4 := by
      field_simp
    rw [h3]
    constructor <;> intro h <;> nlinarith [h]
  have e2 : (4 * sin x ^ 2 - 1) * (2 * sin x ^ 2 - 1) = 0 ↔
      sin x = 1 / 2 ∨ sin x = -(1 / 2) ∨ sin x = √2 / 2 ∨ sin x = -(√2 / 2) := by
    constructor
    · intro hP
      have h' : (2 * sin x - 1) * (2 * sin x + 1) * ((sin x - √2 / 2) * (sin x + √2 / 2)) = 0 := by
        linear_combination (1 / 2) * hP - ((4 * sin x ^ 2 - 1) / 4) * s2
      rcases mul_eq_zero.1 h' with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl (by linarith))
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
        · exact Or.inr (Or.inr (Or.inr (by linarith)))
    · rintro (h | h | h | h)
      · rw [h]; norm_num
      · rw [h]; norm_num
      · rw [h]; linear_combination ((√2 ^ 2 - 1) / 2) * s2
      · rw [h]; linear_combination ((√2 ^ 2 - 1) / 2) * s2
  have a1 := sinEq (a := π / 6) (b := 5 * π / 6) sin_pi_div_six (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have a2 := sinNEq (a := π / 6) (b := 7 * π / 6) (d := 11 * π / 6) (c := 1 / 2) sin_pi_div_six
    (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  have a3 := sinEq (a := π / 4) (b := 3 * π / 4) sin_pi_div_four (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have a4 := sinNEq (a := π / 4) (b := 5 * π / 4) (d := 7 * π / 4) (c := √2 / 2) sin_pi_div_four
    (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  rw [e, e2, a1, a2, a3, a4]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.35: for `sin x ≠ 0` on `[0, 2π)`, `cos 2x + csc²x = 0` exactly when
`x = π/2` or `x = 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.35, p. 886"]
theorem exer_10_7_35 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hs : sin x ≠ 0) :
    cos (2 * x) + ((sin x)⁻¹) ^ 2 = 0 ↔ x = π / 2 ∨ x = 3 * π / 2 := by
  have hs2 : sin x ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hc2 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by rw [cos_two_mul, cos_sq']; ring
  have e : cos (2 * x) + ((sin x)⁻¹) ^ 2 = 0 ↔ sin x = 1 ∨ sin x = -1 := by
    rw [hc2, inv_pow]
    constructor
    · intro h
      field_simp at h
      have h' : (sin x - 1) * (sin x + 1) * (2 * sin x ^ 2 + 1) = 0 := by nlinarith [h]
      rcases mul_eq_zero.1 h' with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      · nlinarith [sq_nonneg (sin x)]
    · rintro (h | h) <;> rw [h] <;> norm_num
  have h1 := sinEq (a := π / 2) (b := π / 2) (c := 1) sin_pi_div_two (by ring) (by positivity)
    (le_refl _) hx0 hx1
  have h2 := sinNEq (a := π / 2) (b := 3 * π / 2) (d := 3 * π / 2) (c := 1) sin_pi_div_two
    (by ring) (by ring) (by positivity) (le_refl _) hx0 hx1
  rw [e, h1, h2]
  rearr_p

private lemma tan_zero_iff {x : ℝ} (hc : cos x ≠ 0) : tan x = 0 ↔ sin x = 0 := by
  rw [tan_eq_sin_div_cos]
  constructor
  · intro h
    rcases div_eq_zero_iff.1 h with h | h
    · exact h
    · exact absurd h hc
  · intro h; rw [h]; simp

/-- Stitz-Zeager Exercise 10.7.36: for `cos x ≠ 0` on `[0, 2π)`, `tan³x = 3 tan x` exactly when
`x = 0, π/3, 2π/3, π, 4π/3, 5π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.36, p. 886"]
theorem exer_10_7_36 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hc : cos x ≠ 0) :
    tan x ^ 3 = 3 * tan x ↔
      x = 0 ∨ x = π / 3 ∨ x = 2 * π / 3 ∨ x = π ∨ x = 4 * π / 3 ∨ x = 5 * π / 3 := by
  have e : tan x ^ 3 = 3 * tan x ↔ tan x = 0 ∨ tan x = √3 ∨ tan x = -√3 := by
    constructor
    · intro h
      have h' : tan x * ((tan x - √3) * (tan x + √3)) = 0 := by
        linear_combination h - (tan x) * s3
      rcases mul_eq_zero.1 h' with h1 | h1
      · exact Or.inl h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
    · rintro (h | h | h)
      · rw [h]; ring
      · rw [h]; linear_combination (√3) * s3
      · rw [h]; linear_combination (-√3) * s3
  have h0 := sin0 hx0 hx1
  have h1 := tanEq (a := π / 3) (b := 4 * π / 3) tan_pi_div_three (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have h2 := tanNEq (a := π / 3) (b := 2 * π / 3) (d := 5 * π / 3) (c := √3) tan_pi_div_three
    (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  rw [e, tan_zero_iff hc, h0, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.37: for `cos x ≠ 0` on `[0, 2π)`, `tan²x = (3/2) sec x` exactly when
`x = π/3` or `x = 5π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.37, p. 886"]
theorem exer_10_7_37 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hc : cos x ≠ 0) :
    tan x ^ 2 = 3 / 2 * (cos x)⁻¹ ↔ x = π / 3 ∨ x = 5 * π / 3 := by
  have hs := sec_sq hc
  have e : tan x ^ 2 = 3 / 2 * (cos x)⁻¹ ↔ cos x = 1 / 2 := by
    constructor
    · intro h
      have h' : (2 * (cos x)⁻¹ + 1) * ((cos x)⁻¹ - 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h1 | h1
      · exfalso
        have : cos x = -2 := by
          have h2 : (cos x)⁻¹ = -(1 / 2) := by linarith
          rw [inv_eq_iff_eq_inv] at h2; rw [h2]; norm_num
        linarith [neg_one_le_cos x]
      · have h2 : (cos x)⁻¹ = 2 := by linarith
        rw [inv_eq_iff_eq_inv] at h2; rw [h2]; norm_num
    · intro h
      rw [h] at hs ⊢
      norm_num at hs ⊢
      linarith
  have h1 := cosEq (a := π / 3) (b := 5 * π / 3) cos_pi_div_three (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  rw [e, h1]

/-- Stitz-Zeager Exercise 10.7.38: on `[0, 2π)`, `cos³x = -cos x` exactly when `x = π/2` or
`x = 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.38, p. 886"]
theorem exer_10_7_38 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos x ^ 3 = -cos x ↔ x = π / 2 ∨ x = 3 * π / 2 := by
  have e : cos x ^ 3 = -cos x ↔ cos x = 0 := by
    constructor
    · intro h
      have h' : cos x * (cos x ^ 2 + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h1 | h1
      · exact h1
      · nlinarith [sq_nonneg (cos x)]
    · intro h; rw [h]; ring
  rw [e, cos0 hx0 hx1]

/-- Stitz-Zeager Exercise 10.7.39: for `cos 2x ≠ 0` on `[0, 2π)`, `tan 2x - 2 cos x = 0` exactly when
`x = π/6, π/2, 5π/6, 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.39, p. 887"]
theorem exer_10_7_39 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hd : cos (2 * x) ≠ 0) :
    tan (2 * x) - 2 * cos x = 0 ↔ x = π / 6 ∨ x = π / 2 ∨ x = 5 * π / 6 ∨ x = 3 * π / 2 := by
  have hc2 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by rw [cos_two_mul, cos_sq']; ring
  have e : tan (2 * x) - 2 * cos x = 0 ↔ cos x = 0 ∨ sin x = 1 / 2 ∨ sin x = -1 := by
    rw [tan_eq_sin_div_cos, sub_eq_zero, div_eq_iff hd, sin_two_mul, hc2]
    constructor
    · intro h
      have h' : cos x * ((2 * sin x - 1) * (sin x + 1)) = 0 := by linear_combination (1 / 2) * h
      rcases mul_eq_zero.1 h' with h1 | h1
      · exact Or.inl h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
    · rintro (h | h | h)
      · rw [h]; ring
      · rw [h]; ring
      · rw [h]; ring
  have h1 := sinEq (a := π / 6) (b := 5 * π / 6) sin_pi_div_six (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have h2 := sinNEq (a := π / 2) (b := 3 * π / 2) (d := 3 * π / 2) (c := 1) sin_pi_div_two
    (by ring) (by ring) (by positivity) (le_refl _) hx0 hx1
  rw [e, cos0 hx0 hx1, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.40: for `sin x ≠ 0` on `[0, 2π)`, `csc³x + csc²x = 4 csc x + 4` exactly
when `x = π/6, 5π/6, 7π/6, 3π/2, 11π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.40, p. 887"]
theorem exer_10_7_40 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hs : sin x ≠ 0) :
    ((sin x)⁻¹) ^ 3 + ((sin x)⁻¹) ^ 2 = 4 * (sin x)⁻¹ + 4 ↔
      x = π / 6 ∨ x = 5 * π / 6 ∨ x = 7 * π / 6 ∨ x = 3 * π / 2 ∨ x = 11 * π / 6 := by
  have key : ∀ u : ℝ, u ^ 3 + u ^ 2 = 4 * u + 4 ↔ u = -1 ∨ u = 2 ∨ u = -2 := by
    intro u
    constructor
    · intro h
      have h' : (u + 1) * ((u - 2) * (u + 2)) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h1 | h1
      · exact Or.inl (by linarith)
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact Or.inr (Or.inl (by linarith))
        · exact Or.inr (Or.inr (by linarith))
    · rintro (h | h | h) <;> rw [h] <;> norm_num
  have i1 : (sin x)⁻¹ = -1 ↔ sin x = -1 := by rw [inv_eq_iff_eq_inv]; norm_num
  have i2 : (sin x)⁻¹ = 2 ↔ sin x = 1 / 2 := by rw [inv_eq_iff_eq_inv]; norm_num
  have i3 : (sin x)⁻¹ = -2 ↔ sin x = -(1 / 2) := by rw [inv_eq_iff_eq_inv]; norm_num
  have h1 := sinEq (a := π / 6) (b := 5 * π / 6) sin_pi_div_six (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have h2 := sinNEq (a := π / 6) (b := 7 * π / 6) (d := 11 * π / 6) (c := 1 / 2) sin_pi_div_six
    (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  have h3 := sinNEq (a := π / 2) (b := 3 * π / 2) (d := 3 * π / 2) (c := 1) sin_pi_div_two
    (by ring) (by ring) (by positivity) (le_refl _) hx0 hx1
  rw [key, i1, i2, i3, h1, h2, h3]
  rearr_p

private lemma tan_pi_eight : tan (π / 8) = √2 - 1 := by
  have t0 : 0 < tan (π / 8) :=
    tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith [pi_pos])
  have h := tan_two_mul (x := π / 8)
  rw [show 2 * (π / 8) = π / 4 by ring, tan_pi_div_four] at h
  have hne : 1 - tan (π / 8) ^ 2 ≠ 0 := by
    intro h0; rw [h0, div_zero] at h; norm_num at h
  rw [eq_div_iff hne] at h
  have h2 : (tan (π / 8) + 1) ^ 2 = √2 ^ 2 := by rw [s2]; nlinarith
  have := (sq_eq_sq₀ (by positivity) (by positivity)).1 h2
  linarith

private lemma tan_three_pi_eight : tan (3 * π / 8) = √2 + 1 := by
  rw [show 3 * π / 8 = π / 2 - π / 8 by ring, tan_pi_div_two_sub, tan_pi_eight]
  apply inv_eq_of_mul_eq_one_right
  linear_combination s2

/-- Stitz-Zeager Exercise 10.7.41: for `cos x ≠ 0` on `[0, 2π)`, `2 tan x = 1 - tan²x` exactly when
`x = π/8, 5π/8, 9π/8, 13π/8`. -/
@[kb "stitzzeager2013" "Exercise 10.7.41, p. 887"]
theorem exer_10_7_41 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    2 * tan x = 1 - tan x ^ 2 ↔ x = π / 8 ∨ x = 5 * π / 8 ∨ x = 9 * π / 8 ∨ x = 13 * π / 8 := by
  have e : 2 * tan x = 1 - tan x ^ 2 ↔ tan x = √2 - 1 ∨ tan x = -(√2 + 1) := by
    constructor
    · intro h
      have h' : (tan x - (√2 - 1)) * (tan x + (√2 + 1)) = 0 := by
        linear_combination h - s2
      rcases mul_eq_zero.1 h' with h1 | h1
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h) <;> rw [h] <;> linear_combination s2
  have h1 := tanEq (a := π / 8) (b := 9 * π / 8) tan_pi_eight (by ring) (by positivity)
    (by linarith [pi_pos]) hx0 hx1
  have h2 := tanNEq (a := 3 * π / 8) (b := 5 * π / 8) (d := 13 * π / 8) (c := √2 + 1)
    tan_three_pi_eight (by ring) (by ring) (by positivity) (by linarith [pi_pos]) hx0 hx1
  rw [e, h1, h2]
  rearr_p

/-- Stitz-Zeager Exercise 10.7.42: for `cos x ≠ 0`, the equation `tan x = sec x` has no solution. -/
@[kb "stitzzeager2013" "Exercise 10.7.42, p. 887"]
theorem exer_10_7_42 (x : ℝ) (hc : cos x ≠ 0) : ¬ (tan x = (cos x)⁻¹) := by
  intro h
  rw [tan_eq_sin_div_cos, ← one_div, div_left_inj' hc] at h
  have := sin_sq_add_cos_sq x
  rw [h] at this
  apply hc
  nlinarith [sq_nonneg (cos x)]

/-- Stitz-Zeager Exercise 10.7.58: for `cos x ≠ 0` on `[0, 2π)`, `tan x = cos x` exactly when
`x = arcsin((-1 + √5)/2)` or `x = π - arcsin((-1 + √5)/2)` (about `0.6662` and `2.4754`). -/
@[kb "stitzzeager2013" "Exercise 10.7.58, p. 888"]
theorem exer_10_7_58 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) (hc : cos x ≠ 0) :
    tan x = cos x ↔
      x = arcsin ((-1 + √5) / 2) ∨ x = π - arcsin ((-1 + √5) / 2) := by
  have p5 : (2 : ℝ) < √5 := by
    have : (4 : ℝ) < √5 ^ 2 := by rw [s5]; norm_num
    nlinarith [Real.sqrt_nonneg 5]
  have q5 : √5 < 3 := by nlinarith [Real.sqrt_nonneg 5, s5]
  have e : tan x = cos x ↔ sin x = (-1 + √5) / 2 := by
    rw [tan_eq_sin_div_cos, div_eq_iff hc]
    have hh := sin_sq_add_cos_sq x
    constructor
    · intro h
      have h' : (sin x - (-1 + √5) / 2) * (sin x + (1 + √5) / 2) = 0 := by
        linear_combination hh + h - (1 / 4) * s5
      rcases mul_eq_zero.1 h' with h1 | h1
      · linarith
      · exfalso; linarith [neg_one_le_sin x]
    · intro h
      have hcc : cos x * cos x = 1 - sin x ^ 2 := by rw [← sq]; exact cos_sq' x
      rw [hcc, h]; linear_combination (1 / 4) * s5
  have h1 := sinEq (a := arcsin ((-1 + √5) / 2)) (b := π - arcsin ((-1 + √5) / 2))
    (sin_arcsin (by linarith) (by linarith)) rfl (arcsin_nonneg.2 (by linarith))
    (arcsin_le_pi_div_two _) hx0 hx1
  rw [e, h1]

end UndergradKB.Precalculus.Course
