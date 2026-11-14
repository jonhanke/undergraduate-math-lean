import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 10 (Stitz-Zeager): worked examples

Worked examples of Chapter 10 (foundations of trigonometry): values via reference angles, the
right-triangle ratios, solutions of basic trigonometric equations, identities, and equations
involving the inverse circular functions.
-/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ### Section 10.2 -/

/-- Stitz-Zeager Example 10.2.3(1): `cos 225° = sin 225° = -√2/2` (225° is `5π/4`). -/
@[kb "stitzzeager2013" "Example 10.2.3, p. 734"]
theorem ex_10_2_3_a : cos (5 * π / 4) = -(√2 / 2) ∧ sin (5 * π / 4) = -(√2 / 2) := by
  have h : 5 * π / 4 = π / 4 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_four, sin_pi_div_four]
  exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Example 10.2.3(2): `cos (11π/6) = √3/2` and `sin (11π/6) = -1/2`. -/
@[kb "stitzzeager2013" "Example 10.2.3, p. 734"]
theorem ex_10_2_3_b : cos (11 * π / 6) = √3 / 2 ∧ sin (11 * π / 6) = -(1 / 2) := by
  have h : 11 * π / 6 = -(π / 6) + 2 * π := by ring
  rw [h, cos_add_two_pi, sin_add_two_pi, cos_neg, sin_neg, cos_pi_div_six, sin_pi_div_six]
  exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Example 10.2.3(3): `cos (-5π/4) = -√2/2` and `sin (-5π/4) = √2/2`. -/
@[kb "stitzzeager2013" "Example 10.2.3, p. 734"]
theorem ex_10_2_3_c : cos (-(5 * π / 4)) = -(√2 / 2) ∧ sin (-(5 * π / 4)) = √2 / 2 := by
  rw [cos_neg, sin_neg, (ex_10_2_3_a).1, (ex_10_2_3_a).2]
  simp

/-- Stitz-Zeager Example 10.2.3(4): `cos (7π/3) = 1/2` and `sin (7π/3) = √3/2`. -/
@[kb "stitzzeager2013" "Example 10.2.3, p. 734"]
theorem ex_10_2_3_d : cos (7 * π / 3) = 1 / 2 ∧ sin (7 * π / 3) = √3 / 2 := by
  have h : 7 * π / 3 = π / 3 + 2 * π := by ring
  rw [h, cos_add_two_pi, sin_add_two_pi, cos_pi_div_three, sin_pi_div_three]
  exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Example 10.2.4(1): an acute angle with cosine `5/13` has sine `12/13`. -/
@[kb "stitzzeager2013" "Example 10.2.4, p. 737"]
theorem ex_10_2_4_sin {α : ℝ} (h0 : 0 < α) (h1 : α < π / 2) (hc : cos α = 5 / 13) :
    sin α = 12 / 13 := by
  have hs : 0 < sin α := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have h := sin_sq_add_cos_sq α
  rw [hc] at h
  nlinarith

/-- Stitz-Zeager Example 10.2.4(2): for acute `α` with `cos α = 5/13`, the cosine and sine of
`π + α`, `2π - α`, `3π - α` and `π/2 + α`. -/
@[kb "stitzzeager2013" "Example 10.2.4, p. 737"]
theorem ex_10_2_4_parts {α : ℝ} (h0 : 0 < α) (h1 : α < π / 2) (hc : cos α = 5 / 13) :
    (cos (π + α) = -(5 / 13) ∧ sin (π + α) = -(12 / 13)) ∧
    (cos (2 * π - α) = 5 / 13 ∧ sin (2 * π - α) = -(12 / 13)) ∧
    (cos (3 * π - α) = -(5 / 13) ∧ sin (3 * π - α) = 12 / 13) ∧
    (cos (π / 2 + α) = -(12 / 13) ∧ sin (π / 2 + α) = 5 / 13) := by
  have hs := ex_10_2_4_sin h0 h1 hc
  have h3 : 3 * π - α = (π - α) + 2 * π := by ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [add_comm, cos_add_pi, hc]
  · rw [add_comm, sin_add_pi, hs]
  · rw [cos_two_pi_sub, hc]
  · rw [sin_two_pi_sub, hs]
  · rw [h3, cos_add_two_pi, cos_pi_sub, hc]
  · rw [h3, sin_add_two_pi, sin_pi_sub, hs]
  · rw [add_comm, cos_add_pi_div_two, hs]
  · rw [add_comm, sin_add_pi_div_two, hc]

/-- Stitz-Zeager Example 10.2.5(1): `cos θ = 1/2` exactly for `θ = π/3 + 2πk` or `θ = 5π/3 + 2πk`. -/
@[kb "stitzzeager2013" "Example 10.2.5, p. 740"]
theorem ex_10_2_5_a (θ : ℝ) :
    cos θ = 1 / 2 ↔ ∃ k : ℤ, θ = π / 3 + 2 * π * k ∨ θ = 5 * π / 3 + 2 * π * k := by
  constructor
  · intro h
    rw [← cos_pi_div_three] at h
    obtain ⟨k, hk | hk⟩ := cos_eq_cos_iff.1 h.symm
    · exact ⟨k, Or.inl (by rw [hk]; ring)⟩
    · exact ⟨k - 1, Or.inr (by rw [hk]; push_cast; ring)⟩
  · rintro ⟨k, rfl | rfl⟩
    · have : cos (π / 3 + 2 * π * k) = cos (π / 3) :=
        cos_eq_cos_iff.2 ⟨-k, Or.inl (by push_cast; ring)⟩
      rw [this, cos_pi_div_three]
    · have : cos (5 * π / 3 + 2 * π * k) = cos (π / 3) :=
        cos_eq_cos_iff.2 ⟨k + 1, Or.inr (by push_cast; ring)⟩
      rw [this, cos_pi_div_three]

/-- Stitz-Zeager Example 10.2.5(2): `sin θ = -1/2` exactly for `θ = 7π/6 + 2πk` or `θ = 11π/6 + 2πk`. -/
@[kb "stitzzeager2013" "Example 10.2.5, p. 740"]
theorem ex_10_2_5_b (θ : ℝ) :
    sin θ = -(1 / 2) ↔ ∃ k : ℤ, θ = 7 * π / 6 + 2 * π * k ∨ θ = 11 * π / 6 + 2 * π * k := by
  have e : -(1 / 2 : ℝ) = sin (-(π / 6)) := by rw [sin_neg, sin_pi_div_six]
  rw [e]
  constructor
  · intro h
    obtain ⟨k, hk | hk⟩ := sin_eq_sin_iff.1 h.symm
    · exact ⟨k - 1, Or.inr (by rw [hk]; push_cast; ring)⟩
    · exact ⟨k, Or.inl (by rw [hk]; ring)⟩
  · rintro ⟨k, rfl | rfl⟩
    · exact sin_eq_sin_iff.2 ⟨k, Or.inr (by push_cast; ring)⟩
    · exact sin_eq_sin_iff.2 ⟨-(k + 1), Or.inl (by push_cast; ring)⟩

/-- Stitz-Zeager Example 10.2.5(3): `cos θ = 0` exactly for `θ = π/2 + πk`, `k` an integer. -/
@[kb "stitzzeager2013" "Example 10.2.5, p. 740"]
theorem ex_10_2_5_c (θ : ℝ) : cos θ = 0 ↔ ∃ k : ℤ, θ = π / 2 + π * k := by
  rw [cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩

/-- Stitz-Zeager Example 10.2.8: in the right triangle with a `30°` angle and adjacent leg `7`, the
hypotenuse is `14√3/3`, the opposite leg is `7√3/3`, and the Pythagorean relation holds. -/
@[kb "stitzzeager2013" "Example 10.2.8, p. 745"]
theorem ex_10_2_8 {c : ℝ} (hc : cos (π / 6) = 7 / c) :
    c = 14 * √3 / 3 ∧ c * sin (π / 6) = 7 * √3 / 3 ∧ (7:ℝ) ^ 2 + (7 * √3 / 3) ^ 2 = c ^ 2 := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  rw [cos_pi_div_six] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hceq : c = 14 * √3 / 3 := by
    field_simp at hc
    nlinarith
  refine ⟨hceq, ?_, ?_⟩
  · rw [sin_pi_div_six, hceq]; ring
  · rw [hceq]; nlinarith

/-! ### Section 10.3 -/

/-- Stitz-Zeager Example 10.3.1(1): `sec 60° = 2`. -/
@[kb "stitzzeager2013" "Example 10.3.1, p. 757"]
theorem ex_10_3_1_a : (cos (π / 3))⁻¹ = 2 := by
  rw [cos_pi_div_three]; norm_num

/-- Stitz-Zeager Example 10.3.1(2): `csc (7π/4) = -√2`. -/
@[kb "stitzzeager2013" "Example 10.3.1, p. 757"]
theorem ex_10_3_1_b : (sin (7 * π / 4))⁻¹ = -√2 := by
  have h : 7 * π / 4 = -(π / 4) + 2 * π := by ring
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  rw [h, sin_add_two_pi, sin_neg, sin_pi_div_four]
  field_simp
  nlinarith

/-- Stitz-Zeager Example 10.3.1(4): for an angle coterminal with `3π/2`, cosine is `0` and sine is
`-1`, so the tangent is undefined (its quotient has a zero denominator). -/
@[kb "stitzzeager2013" "Example 10.3.1, p. 757"]
theorem ex_10_3_1_d (θ : ℝ) (k : ℤ) (hθ : θ = 3 * π / 2 + k * (2 * π)) :
    cos θ = 0 ∧ sin θ = -1 := by
  have h : 3 * π / 2 = π / 2 + π := by ring
  rw [hθ, h, cos_add_int_mul_two_pi, sin_add_int_mul_two_pi, cos_add_pi, sin_add_pi]
  simp

/-- Stitz-Zeager Example 10.3.1(5): if `csc θ = -√5` and `θ` is in Quadrant IV (cosine positive),
then `cos θ = 2√5/5`. -/
@[kb "stitzzeager2013" "Example 10.3.1, p. 757"]
theorem ex_10_3_1_e {θ : ℝ} (h : (sin θ)⁻¹ = -√5) (hc : 0 < cos θ) : cos θ = 2 * √5 / 5 := by
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5p : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
  have hs0 : sin θ ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have hs : sin θ * (-√5) = 1 := by
    rw [← h]; field_simp
  have hsq := sin_sq_add_cos_sq θ
  have hs2 : (sin θ) ^ 2 = 1 / 5 := by nlinarith
  have : (cos θ - 2 * √5 / 5) * (cos θ + 2 * √5 / 5) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · nlinarith

/-- Stitz-Zeager Example 10.3.1(6): if `tan θ = 3` and `π < θ < 3π/2`, then `sin θ = -3√10/10`. -/
@[kb "stitzzeager2013" "Example 10.3.1, p. 757"]
theorem ex_10_3_1_f {θ : ℝ} (h : tan θ = 3) (h1 : π < θ) (h2 : θ < 3 * π / 2) :
    sin θ = -(3 * √10 / 10) := by
  have h10 : (√10) ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have h10p : 0 < √10 := Real.sqrt_pos.2 (by norm_num)
  have hc : cos θ < 0 := cos_neg_of_pi_div_two_lt_of_lt (by linarith [pi_pos]) (by linarith)
  have hs : sin θ = 3 * cos θ := by
    rw [tan_eq_sin_div_cos] at h
    field_simp [hc.ne] at h
    linarith
  have hsq := sin_sq_add_cos_sq θ
  have hs2 : (sin θ) ^ 2 = 9 / 10 := by nlinarith
  have : (sin θ + 3 * √10 / 10) * (sin θ - 3 * √10 / 10) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h3 | h3
  · linarith
  · nlinarith

/-- Stitz-Zeager Example 10.3.2(1): `sec θ = 2` exactly for `θ = π/3 + 2πk` or `θ = 5π/3 + 2πk`. -/
@[kb "stitzzeager2013" "Example 10.3.2, p. 759"]
theorem ex_10_3_2_a (θ : ℝ) :
    (cos θ)⁻¹ = 2 ↔ ∃ k : ℤ, θ = π / 3 + 2 * π * k ∨ θ = 5 * π / 3 + 2 * π * k := by
  rw [← ex_10_2_5_a]
  constructor
  · intro h
    have h0 : cos θ ≠ 0 := by intro h0; rw [h0] at h; simp at h
    field_simp at h
    linarith
  · intro h
    rw [h]; norm_num

/-- Stitz-Zeager Example 10.3.3(1): `1 / csc θ = sin θ` when `sin θ ≠ 0`. -/
@[kb "stitzzeager2013" "Example 10.3.3, p. 761"]
theorem ex_10_3_3_a (θ : ℝ) : 1 / (sin θ)⁻¹ = sin θ := by
  simp

/-- Stitz-Zeager Example 10.3.3(2): `tan θ = sin θ · sec θ`. -/
@[kb "stitzzeager2013" "Example 10.3.3, p. 761"]
theorem ex_10_3_3_b (θ : ℝ) : tan θ = sin θ * (cos θ)⁻¹ := by
  rw [tan_eq_sin_div_cos]; ring

/-- Stitz-Zeager Example 10.3.3(3): `(sec θ - tan θ)(sec θ + tan θ) = 1` where `cos θ ≠ 0`. -/
@[kb "stitzzeager2013" "Example 10.3.3, p. 761"]
theorem ex_10_3_3_c {θ : ℝ} (h : cos θ ≠ 0) :
    ((cos θ)⁻¹ - tan θ) * ((cos θ)⁻¹ + tan θ) = 1 := by
  rw [tan_eq_sin_div_cos]
  have := sin_sq_add_cos_sq θ
  field_simp
  nlinarith

/-- Stitz-Zeager Example 10.3.3(4): `sec θ / (1 - tan θ) = 1 / (cos θ - sin θ)` when `cos θ ≠ 0`
and `tan θ ≠ 1`. -/
@[kb "stitzzeager2013" "Example 10.3.3, p. 761"]
theorem ex_10_3_3_d {θ : ℝ} (h : cos θ ≠ 0) (h1 : 1 - tan θ ≠ 0) :
    (cos θ)⁻¹ / (1 - tan θ) = 1 / (cos θ - sin θ) := by
  rw [tan_eq_sin_div_cos] at h1 ⊢
  have h2 : cos θ - sin θ ≠ 0 := by
    intro h3
    apply h1
    field_simp
    linarith
  field_simp

/-- Stitz-Zeager Example 10.3.3(5): `6 sec θ tan θ = 3/(1 - sin θ) - 3/(1 + sin θ)`, where
`cos θ ≠ 0`. -/
@[kb "stitzzeager2013" "Example 10.3.3, p. 761"]
theorem ex_10_3_3_e {θ : ℝ} (h : cos θ ≠ 0) :
    6 * (cos θ)⁻¹ * tan θ = 3 / (1 - sin θ) - 3 / (1 + sin θ) := by
  have hsq := sin_sq_add_cos_sq θ
  have h1 : 1 - sin θ ≠ 0 := by
    intro h1; apply h; nlinarith
  have h2 : 1 + sin θ ≠ 0 := by
    intro h1; apply h; nlinarith
  rw [tan_eq_sin_div_cos]
  have e : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith
  field_simp
  rw [e]
  ring

/-- Stitz-Zeager Example 10.3.3(6): `sin θ / (1 - cos θ) = (1 + cos θ) / sin θ` when
`sin θ ≠ 0`. -/
@[kb "stitzzeager2013" "Example 10.3.3, p. 761"]
theorem ex_10_3_3_f {θ : ℝ} (h : sin θ ≠ 0) :
    sin θ / (1 - cos θ) = (1 + cos θ) / sin θ := by
  have hsq := sin_sq_add_cos_sq θ
  have h1 : 1 - cos θ ≠ 0 := by
    intro h1; apply h; nlinarith
  field_simp
  nlinarith

/-! ### Section 10.4 -/

/-- Stitz-Zeager Example 10.4.4: `sin²θ cos²θ = 1/8 - (1/8) cos 4θ`. -/
@[kb "stitzzeager2013" "Example 10.4.4, p. 790"]
theorem ex_10_4_4 (θ : ℝ) : sin θ ^ 2 * cos θ ^ 2 = 1 / 8 - 1 / 8 * cos (4 * θ) := by
  have h : 4 * θ = 2 * (2 * θ) := by ring
  rw [h, cos_two_mul, cos_two_mul]
  have := sin_sq_add_cos_sq θ
  have e : sin θ ^ 2 = 1 - cos θ ^ 2 := by linarith
  rw [e]
  ring

/-- Stitz-Zeager Example 10.4.6(1): `cos 2θ cos 6θ = (1/2) cos 4θ + (1/2) cos 8θ`. -/
@[kb "stitzzeager2013" "Example 10.4.6, p. 793"]
theorem ex_10_4_6_a (θ : ℝ) :
    cos (2 * θ) * cos (6 * θ) = 1 / 2 * cos (4 * θ) + 1 / 2 * cos (8 * θ) := by
  have h1 : 2 * θ = 5 * θ - 3 * θ := by ring
  have h2 : 6 * θ = 5 * θ + θ := by ring
  have h3 : 4 * θ = 5 * θ - θ := by ring
  have h4 : 8 * θ = 5 * θ + 3 * θ := by ring
  have g1 : 2 * θ = 4 * θ - 2 * θ := by ring
  rw [show cos (2 * θ) * cos (6 * θ) = cos (6 * θ) * cos (2 * θ) by ring]
  have a1 : 6 * θ = 4 * θ + 2 * θ := by ring
  have a2 : 8 * θ = 6 * θ + 2 * θ := by ring
  have a3 : 4 * θ = 6 * θ - 2 * θ := by ring
  rw [a2, a3, cos_add, cos_sub]
  ring

/-- Stitz-Zeager Example 10.4.6(2): `sin θ - sin 3θ = -2 sin θ cos 2θ`. -/
@[kb "stitzzeager2013" "Example 10.4.6, p. 793"]
theorem ex_10_4_6_b (θ : ℝ) : sin θ - sin (3 * θ) = -2 * sin θ * cos (2 * θ) := by
  have a1 : 3 * θ = 2 * θ + θ := by ring
  have a2 : θ = 2 * θ - θ := by ring
  rw [a1, sin_add]
  have := cos_sq_add_sin_sq θ
  rw [cos_two_mul, sin_two_mul]
  nlinarith

/-! ### Section 10.7 -/

private theorem cos_five_pi_div_six : cos (5 * π / 6) = -(√3 / 2) := by
  rw [show 5 * π / 6 = π - π / 6 by ring, cos_pi_sub, cos_pi_div_six]

/-- Stitz-Zeager Example 10.7.1(1): the solutions of `cos 2x = -√3/2` in `[0, 2π)` are
`5π/12`, `7π/12`, `17π/12` and `19π/12`. -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_a {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    cos (2 * x) = -(√3 / 2) ↔
      x = 5 * π / 12 ∨ x = 7 * π / 12 ∨ x = 17 * π / 12 ∨ x = 19 * π / 12 := by
  have hp := pi_pos
  constructor
  · intro h
    rw [← cos_five_pi_div_six] at h
    obtain ⟨k, hk | hk⟩ := cos_eq_cos_iff.1 h.symm
    · have a : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b : (k : ℝ) < 2 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a
      have b' : k < 2 := by exact_mod_cast b
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · left; push_cast at hk; linarith
      · right; right; left; push_cast at hk; linarith
    · have a : (0 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b : (k : ℝ) < 3 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (0 : ℤ) < k := by exact_mod_cast a
      have b' : k < 3 := by exact_mod_cast b
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · right; left; push_cast at hk; linarith
      · right; right; right; push_cast at hk; linarith
  · intro h
    rw [← cos_five_pi_div_six]
    symm
    rcases h with rfl | rfl | rfl | rfl
    · exact cos_eq_cos_iff.2 ⟨0, Or.inl (by push_cast; ring)⟩
    · exact cos_eq_cos_iff.2 ⟨1, Or.inr (by push_cast; ring)⟩
    · exact cos_eq_cos_iff.2 ⟨1, Or.inl (by push_cast; ring)⟩
    · exact cos_eq_cos_iff.2 ⟨2, Or.inr (by push_cast; ring)⟩

/-- Stitz-Zeager Example 10.7.2(3): the solutions of `cos 2x = 3 cos x - 2` in `[0, 2π)` are
`0`, `π/3` and `5π/3`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_c {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    cos (2 * x) = 3 * cos x - 2 ↔ x = 0 ∨ x = π / 3 ∨ x = 5 * π / 3 := by
  have hp := pi_pos
  rw [cos_two_mul]
  have key : 2 * cos x ^ 2 - 1 = 3 * cos x - 2 ↔ cos x = 1 ∨ cos x = 1 / 2 := by
    constructor
    · intro h
      have : (cos x - 1) * (2 * cos x - 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> norm_num
  rw [key, ex_10_2_5_a, cos_eq_one_iff]
  constructor
  · rintro (⟨n, hn⟩ | ⟨k, hk | hk⟩)
    · have a : (-1 : ℝ) < n := by
        by_contra hh; push Not at hh; nlinarith
      have b : (n : ℝ) < 1 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < n := by exact_mod_cast a
      have b' : n < 1 := by exact_mod_cast b
      obtain rfl : n = 0 := by omega
      left; simp at hn; linarith
    · have a : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b : (k : ℝ) < 1 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a
      have b' : k < 1 := by exact_mod_cast b
      obtain rfl : k = 0 := by omega
      right; left; simpa using hk
    · have a : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b : (k : ℝ) < 1 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a
      have b' : k < 1 := by exact_mod_cast b
      obtain rfl : k = 0 := by omega
      right; right; simpa using hk
  · rintro (rfl | rfl | rfl)
    · left; exact ⟨0, by simp⟩
    · right; exact ⟨0, Or.inl (by simp)⟩
    · right; exact ⟨0, Or.inr (by simp)⟩

private theorem sin_le_half_iff {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ π / 2) :
    sin y ≤ 1 / 2 ↔ y ≤ π / 6 := by
  have hp := pi_pos
  rw [← sin_pi_div_six]
  exact strictMonoOn_sin.le_iff_le ⟨by linarith, h1⟩ ⟨by linarith, by linarith⟩

/-- Stitz-Zeager Example 10.7.3(1): within `[0, 2π)`, the inequality `2 sin x ≤ 1` holds exactly
on `[0, π/6] ∪ [5π/6, 2π)`. -/
@[kb "stitzzeager2013" "Example 10.7.3, p. 878"]
theorem ex_10_7_3_a :
    {x : ℝ | x ∈ Ico 0 (2 * π) ∧ 2 * sin x ≤ 1} = Icc 0 (π / 6) ∪ Ico (5 * π / 6) (2 * π) := by
  have hp := pi_pos
  ext x
  simp only [mem_ofPred_eq, mem_Ico, mem_union, mem_Icc]
  constructor
  · rintro ⟨⟨h0, h1⟩, h⟩
    have h' : sin x ≤ 1 / 2 := by linarith
    by_cases c1 : x ≤ π / 2
    · left; exact ⟨h0, (sin_le_half_iff h0 c1).1 h'⟩
    · push Not at c1
      by_cases c2 : x ≤ π
      · right
        have := (sin_le_half_iff (y := π - x) (by linarith) (by linarith)).1
          (by rw [sin_pi_sub]; exact h')
        exact ⟨by linarith, h1⟩
      · push Not at c2
        right; exact ⟨by linarith, h1⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · refine ⟨⟨h0, by linarith⟩, ?_⟩
      have := (sin_le_half_iff h0 (by linarith)).2 h1
      linarith
    · refine ⟨⟨by linarith, h1⟩, ?_⟩
      by_cases c2 : x ≤ π
      · have := (sin_le_half_iff (y := π - x) (by linarith) (by linarith)).2 (by linarith)
        rw [sin_pi_sub] at this
        linarith
      · push Not at c2
        have : 0 ≤ sin (x - π) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        rw [sin_sub_pi] at this
        linarith

/-- Stitz-Zeager Example 10.7.5(1): `arcsin (2x) = π/3` exactly when `x = √3/4`. -/
@[kb "stitzzeager2013" "Example 10.7.5, p. 882"]
theorem ex_10_7_5_a (x : ℝ) : arcsin (2 * x) = π / 3 ↔ x = √3 / 4 := by
  have hp := pi_pos
  rw [arcsin_eq_iff_eq_sin ⟨by linarith, by linarith⟩, sin_pi_div_three]
  constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 10.7.5(2): `4 arccos x - 3π = 0` exactly when `x = -√2/2`. -/
@[kb "stitzzeager2013" "Example 10.7.5, p. 882"]
theorem ex_10_7_5_b (x : ℝ) : 4 * arccos x - 3 * π = 0 ↔ x = -(√2 / 2) := by
  have hp := pi_pos
  have e : 4 * arccos x - 3 * π = 0 ↔ arcsin x = -(π / 4) := by
    rw [arccos_eq_pi_div_two_sub_arcsin]
    constructor <;> intro h <;> linarith
  rw [e, arcsin_eq_iff_eq_sin ⟨by linarith, by linarith⟩, sin_neg, sin_pi_div_four]

/-- Stitz-Zeager Example 10.7.5(4): `4 arctan² x - 3π arctan x - π² = 0` exactly when `x = -1`. -/
@[kb "stitzzeager2013" "Example 10.7.5, p. 882"]
theorem ex_10_7_5_d (x : ℝ) :
    4 * arctan x ^ 2 - 3 * π * arctan x - π ^ 2 = 0 ↔ x = -1 := by
  have hp := pi_pos
  have ha := arctan_lt_pi_div_two x
  constructor
  · intro h
    have : (4 * arctan x + π) * (arctan x - π) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · have : arctan x = -(π / 4) := by linarith
      have h2 := tan_arctan x
      rw [this, tan_neg, tan_pi_div_four] at h2
      linarith
    · linarith
  · rintro rfl
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, arctan_neg, arctan_one]
    ring

/-- Stitz-Zeager Example 10.7.5(5): for `x` in `[-1, 1]`, the inequality `π² - 4 arccos² x < 0`
holds exactly when `-1 ≤ x < 0`. -/
@[kb "stitzzeager2013" "Example 10.7.5, p. 882"]
theorem ex_10_7_5_e {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    π ^ 2 - 4 * arccos x ^ 2 < 0 ↔ x ∈ Ico (-1 : ℝ) 0 := by
  have hp := pi_pos
  have ha := arccos_nonneg x
  rw [mem_Ico]
  constructor
  · intro h
    have : π / 2 < arccos x := by nlinarith
    exact ⟨hx.1, pi_div_two_lt_arccos.1 this⟩
  · rintro ⟨-, h⟩
    have := pi_div_two_lt_arccos.2 h
    nlinarith

end UndergradKB.Precalculus.Course
