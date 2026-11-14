import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 10 (Stitz-Zeager): worked examples, wave 5

The graphing examples of Sections 10.5 and 10.6 (key points, periods, closed forms of sinusoids),
and the remaining parts of the equation, inequality and domain examples of Section 10.7.
Secant, cosecant and cotangent are written as `1 / cos`, `1 / sin` and `cos / sin`.
-/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ### Section 10.5 -/

/-- Stitz-Zeager Example 10.5.1(1): the cycle of `f x = 3 cos ((πx - π)/2) + 1` has key points
`(1,4), (2,1), (3,-2), (4,1), (5,4)`, and `f` has period `4`. -/
@[kb "stitzzeager2013" "Example 10.5.1, p. 805"]
theorem ex_10_5_1_a (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * cos ((π * x - π) / 2) + 1) :
    f 1 = 4 ∧ f 2 = 1 ∧ f 3 = -2 ∧ f 4 = 1 ∧ f 5 = 4 ∧ Function.Periodic f 4 := by
  have e : ∀ x, f (x + 4) = f x := by
    intro x
    rw [hf, hf, show (π * (x + 4) - π) / 2 = (π * x - π) / 2 + 2 * π by ring, cos_add_two_pi]
  refine ⟨?_, ?_, ?_, ?_, ?_, e⟩
  · rw [hf, show (π * 1 - π) / 2 = 0 by ring]; norm_num
  · rw [hf, show (π * 2 - π) / 2 = π / 2 by ring, cos_pi_div_two]; norm_num
  · rw [hf, show (π * 3 - π) / 2 = π by ring, cos_pi]; norm_num
  · rw [hf, show (π * 4 - π) / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; norm_num
  · rw [hf, show (π * 5 - π) / 2 = 2 * π by ring, cos_two_pi]; norm_num

/-- Stitz-Zeager Example 10.5.1(2): the cycle of `g x = sin (π - 2x) / 2 + 3/2` has key points
`(π/2, 3/2), (π/4, 2), (0, 3/2), (-π/4, 1), (-π/2, 3/2)`, and `g` has period `π`. -/
@[kb "stitzzeager2013" "Example 10.5.1, p. 805"]
theorem ex_10_5_1_b (g : ℝ → ℝ) (hg : ∀ x, g x = sin (π - 2 * x) / 2 + 3 / 2) :
    g (π / 2) = 3 / 2 ∧ g (π / 4) = 2 ∧ g 0 = 3 / 2 ∧ g (-(π / 4)) = 1 ∧
      g (-(π / 2)) = 3 / 2 ∧ Function.Periodic g π := by
  have e : ∀ x, g (x + π) = g x := by
    intro x
    rw [hg, hg, show π - 2 * (x + π) = (π - 2 * x) + (-(2 * π)) by ring]
    rw [sin_add, show (-(2 * π)) = -(2 * π) from rfl, sin_neg, cos_neg, sin_two_pi, cos_two_pi]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, e⟩
  · rw [hg, show π - 2 * (π / 2) = 0 by ring, sin_zero]; norm_num
  · rw [hg, show π - 2 * (π / 4) = π / 2 by ring, sin_pi_div_two]; norm_num
  · rw [hg, show π - 2 * 0 = π by ring, sin_pi]; norm_num
  · rw [hg, show π - 2 * (-(π / 4)) = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]; norm_num
  · rw [hg, show π - 2 * (-(π / 2)) = 2 * π by ring, sin_two_pi]; norm_num

/-- Stitz-Zeager Example 10.5.1 (via Theorem 10.23): the two functions of the example in the
standard sinusoid forms `3 cos (π/2 x + (-π/2)) + 1` and `(-1/2) sin (2x + (-π)) + 3/2`. -/
@[kb "stitzzeager2013" "Example 10.5.1, p. 805"]
theorem ex_10_5_1_forms (x : ℝ) :
    3 * cos ((π * x - π) / 2) + 1 = 3 * cos (π / 2 * x + (-(π / 2))) + 1 ∧
      sin (π - 2 * x) / 2 + 3 / 2 = (-1 / 2) * sin (2 * x + (-π)) + 3 / 2 := by
  constructor
  · congr 3; ring
  · rw [show π - 2 * x = -(2 * x + (-π)) by ring, sin_neg]; ring

/-- Stitz-Zeager Example 10.5.2: the cosine form `2 cos (πx/3 + π/3) + 1/2` and the sine form
`2 sin (πx/3 - 7π/6) + 1/2` give the same sinusoid; it passes through the five plotted key points
`(-1, 5/2), (1/2, 1/2), (2, -3/2), (7/2, 1/2), (5, 5/2)`. -/
@[kb "stitzzeager2013" "Example 10.5.2, p. 808"]
theorem ex_10_5_2_forms (x : ℝ) :
    2 * cos (π / 3 * x + π / 3) + 1 / 2 = 2 * sin (π / 3 * x - 7 * π / 6) + 1 / 2 := by
  have : π / 3 * x + π / 3 = (π / 3 * x - 7 * π / 6) + 3 * π / 2 := by ring
  rw [this, show 3 * π / 2 = π / 2 + π by ring, ← add_assoc, cos_add_pi, cos_add_pi_div_two]
  ring

/-- Stitz-Zeager Example 10.5.2: the key points of the cycle on the cosine form
`C x = 2 cos (πx/3 + π/3) + 1/2`, and its period `6`. -/
@[kb "stitzzeager2013" "Example 10.5.2, p. 808"]
theorem ex_10_5_2_points (C : ℝ → ℝ) (hC : ∀ x, C x = 2 * cos (π / 3 * x + π / 3) + 1 / 2) :
    C (-1) = 5 / 2 ∧ C (1 / 2) = 1 / 2 ∧ C 2 = -3 / 2 ∧ C (7 / 2) = 1 / 2 ∧ C 5 = 5 / 2 ∧
      Function.Periodic C 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hC, show π / 3 * (-1) + π / 3 = 0 by ring, cos_zero]; norm_num
  · rw [hC, show π / 3 * (1 / 2) + π / 3 = π / 2 by ring, cos_pi_div_two]; norm_num
  · rw [hC, show π / 3 * 2 + π / 3 = π by ring, cos_pi]; norm_num
  · rw [hC, show π / 3 * (7 / 2) + π / 3 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; norm_num
  · rw [hC, show π / 3 * 5 + π / 3 = 2 * π by ring, cos_two_pi]; norm_num
  · intro x
    rw [hC, hC, show π / 3 * (x + 6) + π / 3 = (π / 3 * x + π / 3) + 2 * π by ring, cos_add_two_pi]

/-- Stitz-Zeager Example 10.5.2 (closing remark): another sine form of the same sinusoid is
`-2 sin (πx/3 - π/6) + 1/2`. -/
@[kb "stitzzeager2013" "Example 10.5.2, p. 808"]
theorem ex_10_5_2_alt (x : ℝ) :
    2 * cos (π / 3 * x + π / 3) + 1 / 2 = -2 * sin (π / 3 * x - π / 6) + 1 / 2 := by
  have : π / 3 * x + π / 3 = (π / 3 * x - π / 6) + π / 2 := by ring
  rw [this, cos_add_pi_div_two]
  ring

/-- Stitz-Zeager Example 10.5.4(1): for `f x = 1 - 2 sec (2x)`, `f 0 = -1`, `f (π/2) = 3`,
`f π = -1`, the cosine vanishes at the asymptote locations `π/4`, `3π/4`, and `f` has period `π`. -/
@[kb "stitzzeager2013" "Example 10.5.4, p. 814"]
theorem ex_10_5_4_a (f : ℝ → ℝ) (hf : ∀ x, f x = 1 - 2 * (1 / cos (2 * x))) :
    f 0 = -1 ∧ f (π / 2) = 3 ∧ f π = -1 ∧ cos (2 * (π / 4)) = 0 ∧ cos (2 * (3 * π / 4)) = 0 ∧
      Function.Periodic f π := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf]; simp; norm_num
  · rw [hf, show 2 * (π / 2) = π by ring, cos_pi]; norm_num
  · rw [hf, show 2 * π = 2 * π from rfl, cos_two_pi]; norm_num
  · rw [show 2 * (π / 4) = π / 2 by ring, cos_pi_div_two]
  · rw [show 2 * (3 * π / 4) = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; norm_num
  · intro x
    rw [hf, hf, show 2 * (x + π) = 2 * x + 2 * π by ring, cos_add_two_pi]

/-- Stitz-Zeager Example 10.5.4(2): for `g x = (csc (π - πx) - 5)/3`, `g (1/2) = -4/3`,
`g (-1/2) = -2`, the sine in the cosecant vanishes at `1`, `0`, `-1` (the asymptotes), and `g` has
period `2`. -/
@[kb "stitzzeager2013" "Example 10.5.4, p. 814"]
theorem ex_10_5_4_b (g : ℝ → ℝ) (hg : ∀ x, g x = (1 / sin (π - π * x) - 5) / 3) :
    g (1 / 2) = -4 / 3 ∧ g (-(1 / 2)) = -2 ∧ sin (π - π * 1) = 0 ∧ sin (π - π * 0) = 0 ∧
      sin (π - π * (-1)) = 0 ∧ Function.Periodic g 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg, show π - π * (1 / 2) = π / 2 by ring, sin_pi_div_two]; norm_num
  · rw [hg, show π - π * (-(1 / 2)) = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]; norm_num
  · rw [show π - π * 1 = 0 by ring, sin_zero]
  · rw [show π - π * 0 = π by ring, sin_pi]
  · rw [show π - π * (-1) = 2 * π by ring, sin_two_pi]
  · intro x
    rw [hg, hg, show π - π * (x + 2) = (π - π * x) + (-(2 * π)) by ring, sin_add,
      sin_neg, cos_neg, sin_two_pi, cos_two_pi]
    ring_nf

/-- Stitz-Zeager Example 10.5.5(1): for `f x = 1 - tan (x/2)`, `f (-π/2) = 2`, `f 0 = 1`,
`f (π/2) = 0`, the cosine of the argument vanishes at the asymptotes `±π`, and `f` has period
`2π`. -/
@[kb "stitzzeager2013" "Example 10.5.5, p. 819"]
theorem ex_10_5_5_a (f : ℝ → ℝ) (hf : ∀ x, f x = 1 - tan (x / 2)) :
    f (-(π / 2)) = 2 ∧ f 0 = 1 ∧ f (π / 2) = 0 ∧ cos (π / 2) = 0 ∧ cos (-π / 2) = 0 ∧
      Function.Periodic f (2 * π) := by
  refine ⟨?_, ?_, ?_, cos_pi_div_two, ?_, ?_⟩
  · rw [hf, show -(π / 2) / 2 = -(π / 4) by ring, tan_neg, tan_pi_div_four]; norm_num
  · rw [hf]; simp
  · rw [hf, show π / 2 / 2 = π / 4 by ring, tan_pi_div_four]; norm_num
  · rw [neg_div, cos_neg, cos_pi_div_two]
  · intro x
    rw [hf, hf, show (x + 2 * π) / 2 = x / 2 + π by ring, tan_add_pi]

/-- Stitz-Zeager Example 10.5.5(2): for `g x = 2 cot (πx/2 + π) + 1` (cotangent written as
cosine over sine), `g (-3/2) = 3`, `g (-1) = 1`, `g (-1/2) = -1`, the sine of the argument vanishes
at `-2` and `0`, and `g` has period `2`. -/
@[kb "stitzzeager2013" "Example 10.5.5, p. 819"]
theorem ex_10_5_5_b (g : ℝ → ℝ)
    (hg : ∀ x, g x = 2 * (cos (π / 2 * x + π) / sin (π / 2 * x + π)) + 1) :
    g (-(3 / 2)) = 3 ∧ g (-1) = 1 ∧ g (-(1 / 2)) = -1 ∧ sin (π / 2 * (-2) + π) = 0 ∧
      sin (π / 2 * 0 + π) = 0 ∧ Function.Periodic g 2 := by
  have h1 : π / 2 * (-(3 / 2)) + π = π / 4 := by ring
  have h2 : π / 2 * (-1) + π = π / 2 := by ring
  have h3 : π / 2 * (-(1 / 2)) + π = π / 4 + π / 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg, h1, cos_pi_div_four, sin_pi_div_four]
    have : (√2 / 2) / (√2 / 2) = 1 := div_self (by positivity)
    rw [this]; norm_num
  · rw [hg, h2, cos_pi_div_two]; norm_num
  · rw [hg, h3, cos_add_pi_div_two, sin_add_pi_div_two, sin_pi_div_four, cos_pi_div_four]
    have : (-(√2 / 2)) / (√2 / 2) = -1 := by
      rw [neg_div, div_self (by positivity)]
    rw [this]; norm_num
  · rw [show π / 2 * (-2) + π = 0 by ring, sin_zero]
  · rw [show π / 2 * 0 + π = π by ring, sin_pi]
  · intro x
    rw [hg, hg, show π / 2 * (x + 2) + π = (π / 2 * x + π) + π by ring, cos_add_pi, sin_add_pi,
      neg_div_neg_eq]

/-! ### Section 10.6 -/

/-- Stitz-Zeager Example 10.6.6: a roof with rise `6` over run `12` has inclination
`θ = arctan (1/2)`, with `tan θ = 1/2`; in degrees it lies strictly between `22.5°` and `30°`
(the book's decimal value is about `26.56°`). -/
@[kb "stitzzeager2013" "Example 10.6.6, p. 849"]
theorem ex_10_6_6 :
    tan (arctan (6 / 12)) = 1 / 2 ∧ 0 < arctan (6 / 12) ∧ arctan (6 / 12) < π / 2 ∧
      π / 8 < arctan (6 / 12) ∧ arctan (6 / 12) < π / 6 := by
  have h : (6 : ℝ) / 12 = 1 / 2 := by norm_num
  rw [h]
  refine ⟨tan_arctan _, arctan_pos.2 (by norm_num), arctan_lt_pi_div_two _, ?_, ?_⟩
  · have hp := pi_pos
    have h8 : tan (π / 8) < 1 / 2 := by
      have hc : 0 < cos (π / 8) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hs : 0 < sin (π / 8) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have e1 : cos (π / 4) = 1 - 2 * sin (π / 8) ^ 2 := by
        rw [show π / 4 = 2 * (π / 8) by ring, cos_two_mul']
        nlinarith [sin_sq_add_cos_sq (π / 8)]
      rw [cos_pi_div_four] at e1
      have e2 := sin_sq_add_cos_sq (π / 8)
      rw [tan_eq_sin_div_cos, div_lt_div_iff₀ hc (by norm_num)]
      have s2 : (1.4 : ℝ) < √2 := by
        rw [show (1.4 : ℝ) = √(1.96) by
          rw [show (1.96 : ℝ) = 1.4 ^ 2 by norm_num]; exact (sqrt_sq (by norm_num)).symm]
        exact sqrt_lt_sqrt (by norm_num) (by norm_num)
      nlinarith
    calc π / 8 = arctan (tan (π / 8)) := (arctan_tan (by linarith) (by linarith)).symm
      _ < arctan (1 / 2) := arctan_strictMono h8
  · rw [← arctan_tan (x := π / 6) (by linarith [pi_pos]) (by linarith [pi_pos])]
    apply arctan_strictMono
    rw [tan_pi_div_six]
    have : (0 : ℝ) < √3 := by positivity
    rw [lt_div_iff₀ this]
    have : √3 < 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (sqrt_sq (by norm_num)).symm]
      exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith

/-! ### Section 10.7: equations -/

private theorem tan_eq_tan_aux {x a : ℝ} (hx : cos x ≠ 0) (ha : cos a ≠ 0) :
    tan x = tan a ↔ ∃ n : ℤ, x = a + n * π := by
  have h : tan x = tan a ↔ sin (x - a) = 0 := by
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hx ha, sin_sub]
    constructor <;> intro h <;> linarith
  rw [h, sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩

private theorem cos_two_pi_div_three : cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]

/-- Stitz-Zeager Example 10.7.1(2): `csc (x/3 - π) = √2` holds exactly for `x = 15π/4 + 6πk` or
`x = 21π/4 + 6πk` (`k` an integer). -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_b (x : ℝ) :
    1 / sin (x / 3 - π) = √2 ↔ ∃ k : ℤ, x = 15 * π / 4 + 6 * π * k ∨ x = 21 * π / 4 + 6 * π * k := by
  have s2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  have s0 : 0 < √2 := by positivity
  have key : 1 / sin (x / 3 - π) = √2 ↔ sin (π / 4) = sin (x / 3 - π) := by
    rw [sin_pi_div_four]
    constructor
    · intro h
      have hs : sin (x / 3 - π) ≠ 0 := by
        intro h0; rw [h0] at h; simp at h; linarith
      have h' : 1 = √2 * sin (x / 3 - π) := (div_eq_iff hs).1 h
      have e : 2 * sin (x / 3 - π) = √2 := by
        calc 2 * sin (x / 3 - π) = (√2 * √2) * sin (x / 3 - π) := by rw [s2]
          _ = √2 * (√2 * sin (x / 3 - π)) := by ring
          _ = √2 := by rw [← h']; ring
      linarith
    · intro h
      rw [← h]; field_simp; linarith
  rw [key, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩
  · rintro ⟨k, hk | hk⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩

/-- Stitz-Zeager Example 10.7.1(2): none of the solutions of `csc (x/3 - π) = √2` lies in
`[0, 2π)`. -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_b_none {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    1 / sin (x / 3 - π) ≠ √2 := by
  have hp := pi_pos
  intro h
  obtain ⟨k, hk | hk⟩ := (ex_10_7_1_b x).1 h
  · have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 0 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 0 := by exact_mod_cast b
    omega
  · have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 0 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 0 := by exact_mod_cast b
    omega

/-- Stitz-Zeager Example 10.7.1(3): `cot 3x = 0` (cosine over sine, with sine nonzero) holds
exactly for `x = π/6 + (π/3) k`, `k` an integer. -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_c (x : ℝ) :
    (sin (3 * x) ≠ 0 ∧ cos (3 * x) / sin (3 * x) = 0) ↔ ∃ k : ℤ, x = π / 6 + π / 3 * k := by
  have key : (sin (3 * x) ≠ 0 ∧ cos (3 * x) / sin (3 * x) = 0) ↔ cos (3 * x) = 0 := by
    constructor
    · rintro ⟨h1, h2⟩
      exact (div_eq_zero_iff.1 h2).resolve_right h1
    · intro h
      refine ⟨?_, by rw [h]; simp⟩
      intro hs
      have := sin_sq_add_cos_sq (3 * x)
      rw [h, hs] at this; norm_num at this
  rw [key, cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Example 10.7.1(3): the solutions of `cot 3x = 0` in `[0, 2π)` are
`π/6, π/2, 5π/6, 7π/6, 3π/2, 11π/6`. -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_c_list {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    (sin (3 * x) ≠ 0 ∧ cos (3 * x) / sin (3 * x) = 0) ↔
      x = π / 6 ∨ x = π / 2 ∨ x = 5 * π / 6 ∨ x = 7 * π / 6 ∨ x = 3 * π / 2 ∨
        x = 11 * π / 6 := by
  have hp := pi_pos
  rw [ex_10_7_1_c]
  constructor
  · rintro ⟨k, hk⟩
    have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 6 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 6 := by exact_mod_cast b
    obtain rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
      omega
    · left; push_cast at hk; linarith
    · right; left; push_cast at hk; linarith
    · right; right; left; push_cast at hk; linarith
    · right; right; right; left; push_cast at hk; linarith
    · right; right; right; right; left; push_cast at hk; linarith
    · right; right; right; right; right; push_cast at hk; linarith
  · rintro (h | h | h | h | h | h)
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by rw [h]; push_cast; ring⟩
    · exact ⟨2, by rw [h]; push_cast; ring⟩
    · exact ⟨3, by rw [h]; push_cast; ring⟩
    · exact ⟨4, by rw [h]; push_cast; ring⟩
    · exact ⟨5, by rw [h]; push_cast; ring⟩

/-- Stitz-Zeager Example 10.7.1(4): `sec² x = 4` holds exactly for `x = π/3 + πk` or
`x = 2π/3 + πk` (`k` an integer). -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_d (x : ℝ) :
    (1 / cos x) ^ 2 = 4 ↔ ∃ k : ℤ, x = π / 3 + π * k ∨ x = 2 * π / 3 + π * k := by
  have key : (1 / cos x) ^ 2 = 4 ↔ cos (2 * x) = cos (2 * π / 3) := by
    rw [cos_two_pi_div_three, cos_two_mul]
    constructor
    · intro h
      have hc : cos x ≠ 0 := by
        intro h0; rw [h0] at h; norm_num at h
      field_simp at h
      linarith
    · intro h
      have h2 : cos x ^ 2 = 1 / 4 := by linarith
      rw [div_pow, one_pow, h2]; norm_num
  rw [key, cos_eq_cos_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨-k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨k - 1, Or.inr (by push_cast; linarith)⟩
  · rintro ⟨k, hk | hk⟩
    · exact ⟨-k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨k + 1, Or.inr (by push_cast; linarith)⟩

/-- Stitz-Zeager Example 10.7.1(4): the solutions of `sec² x = 4` in `[0, 2π)` are
`π/3, 2π/3, 4π/3, 5π/3`. -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_d_list {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    (1 / cos x) ^ 2 = 4 ↔ x = π / 3 ∨ x = 2 * π / 3 ∨ x = 4 * π / 3 ∨ x = 5 * π / 3 := by
  have hp := pi_pos
  rw [ex_10_7_1_d]
  constructor
  · rintro ⟨k, hk | hk⟩
    · have a : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b : (k : ℝ) < 2 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a
      have b' : k < 2 := by exact_mod_cast b
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · left; push_cast at hk; linarith
      · right; right; left; push_cast at hk; linarith
    · have a : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b : (k : ℝ) < 2 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a
      have b' : k < 2 := by exact_mod_cast b
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · right; left; push_cast at hk; linarith
      · right; right; right; push_cast at hk; linarith
  · rintro (h | h | h | h)
    · exact ⟨0, Or.inl (by simp [h])⟩
    · exact ⟨0, Or.inr (by simp [h])⟩
    · exact ⟨1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩

/-- Stitz-Zeager Example 10.7.1(5): `tan (x/2) = -3` holds exactly for
`x = 2 arctan (-3) + 2πk`, `k` an integer. -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_e (x : ℝ) :
    tan (x / 2) = -3 ↔ ∃ k : ℤ, x = 2 * arctan (-3) + 2 * π * k := by
  constructor
  · intro h
    have hc : cos (x / 2) ≠ 0 := by
      intro h0; rw [tan_eq_sin_div_cos, h0] at h; norm_num at h
    obtain ⟨n, hn⟩ := (tan_eq_tan_aux hc (cos_arctan_pos (-3)).ne').1 (by rw [h, tan_arctan])
    exact ⟨n, by linarith⟩
  · rintro ⟨k, hk⟩
    rw [show x / 2 = arctan (-3) + k * π by rw [hk]; ring, (tan_periodic.int_mul k) (arctan (-3)),
      tan_arctan]

/-- Stitz-Zeager Example 10.7.1(5): the only solution of `tan (x/2) = -3` in `[0, 2π)` is
`2 arctan (-3) + 2π` (and `π < 2 arctan (-3) + 2π < 2π`). -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_e_unique {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    tan (x / 2) = -3 ↔ x = 2 * arctan (-3) + 2 * π := by
  have hp := pi_pos
  have l1 : arctan (-3) < 0 := by rw [arctan_neg]; linarith [arctan_pos.2 (show (0 : ℝ) < 3 by norm_num)]
  have l2 := neg_pi_div_two_lt_arctan (-3)
  rw [ex_10_7_1_e]
  constructor
  · rintro ⟨k, hk⟩
    have a : (0 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 2 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (0 : ℤ) < k := by exact_mod_cast a
    have b' : k < 2 := by exact_mod_cast b
    obtain rfl : k = 1 := by omega
    push_cast at hk; linarith
  · intro h; exact ⟨1, by push_cast; linarith⟩

/-- Stitz-Zeager Example 10.7.1(6): `sin 2x = 0.87` holds exactly for `x = (arcsin 0.87)/2 + πk`
or `x = π/2 - (arcsin 0.87)/2 + πk`, `k` an integer. -/
@[kb "stitzzeager2013" "Example 10.7.1, p. 869"]
theorem ex_10_7_1_f (x : ℝ) :
    sin (2 * x) = 0.87 ↔
      ∃ k : ℤ, x = arcsin 0.87 / 2 + π * k ∨ x = π / 2 - arcsin 0.87 / 2 + π * k := by
  have h : sin (arcsin 0.87) = 0.87 := sin_arcsin (by norm_num) (by norm_num)
  have key : sin (2 * x) = 0.87 ↔ sin (arcsin 0.87) = sin (2 * x) := by rw [h]; exact eq_comm
  rw [key, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩
  · rintro ⟨k, hk | hk⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩

private theorem tan_eq_iff_aux {x t : ℝ} (ht : t ≠ 0) :
    tan x = t ↔ ∃ n : ℤ, x = arctan t + n * π := by
  constructor
  · intro h
    have hc : cos x ≠ 0 := by
      intro h0; rw [tan_eq_sin_div_cos, h0] at h; simp at h; exact ht h.symm
    obtain ⟨n, hn⟩ := (tan_eq_tan_aux hc (cos_arctan_pos t).ne').1 (by rw [h, tan_arctan])
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    rw [hn, (tan_periodic.int_mul n) (arctan t), tan_arctan]

private theorem sin_eq_sin_Ico {a x : ℝ} (ha0 : 0 < a) (ha1 : a < π / 2) (h0 : 0 ≤ x)
    (h1 : x < 2 * π) : sin x = sin a ↔ x = a ∨ x = π - a := by
  have hp := pi_pos
  rw [eq_comm, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · left
      have a1 : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b1 : (k : ℝ) < 1 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a1
      have b' : k < 1 := by exact_mod_cast b1
      obtain rfl : k = 0 := by omega
      simpa using hk
    · right
      have a1 : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b1 : (k : ℝ) < 1 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a1
      have b' : k < 1 := by exact_mod_cast b1
      obtain rfl : k = 0 := by omega
      simp at hk; linarith
  · rintro (h | h)
    · exact ⟨0, Or.inl (by simp [h])⟩
    · exact ⟨0, Or.inr (by simp [h])⟩

/-- Stitz-Zeager Example 10.7.2(1): in `[0, 2π)`, `3 sin³ x = sin² x` holds exactly for
`x = 0`, `π`, `arcsin (1/3)` and `π - arcsin (1/3)`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_a {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    3 * sin x ^ 3 = sin x ^ 2 ↔
      x = 0 ∨ x = π ∨ x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3) := by
  have hp := pi_pos
  have key : 3 * sin x ^ 3 = sin x ^ 2 ↔ sin x = 0 ∨ sin x = 1 / 3 := by
    constructor
    · intro h
      have : sin x ^ 2 * (3 * sin x - 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h2 | h2
      · left; exact pow_eq_zero_iff (by norm_num) |>.1 h2
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> norm_num
  have a0 : 0 < arcsin (1 / 3) := arcsin_pos.2 (by norm_num)
  have a1 : arcsin (1 / 3) < π / 2 := by
    have := arcsin_lt_pi_div_two.2 (show (1 / 3 : ℝ) < 1 by norm_num)
    exact this
  have hs : sin x = 1 / 3 ↔ x = arcsin (1 / 3) ∨ x = π - arcsin (1 / 3) := by
    rw [← sin_eq_sin_Ico a0 a1 h0 h1, sin_arcsin (by norm_num) (by norm_num)]
  have hz : sin x = 0 ↔ x = 0 ∨ x = π := by
    rw [sin_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩
      have a : (-1 : ℝ) < n := by
        by_contra hh; push Not at hh; nlinarith
      have b : (n : ℝ) < 2 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < n := by exact_mod_cast a
      have b' : n < 2 := by exact_mod_cast b
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · left; simpa using hn.symm
      · right; simpa using hn.symm
    · rintro (h | h)
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
  rw [key, hs, hz]
  tauto

private theorem sec_sq_aux {x : ℝ} (hc : cos x ≠ 0) : (1 / cos x) ^ 2 = 1 + tan x ^ 2 := by
  rw [tan_eq_sin_div_cos]
  have := sin_sq_add_cos_sq x
  field_simp
  linarith

/-- Stitz-Zeager Example 10.7.2(2): in `[0, 2π)`, `sec² x = tan x + 3` holds exactly for
`x = 3π/4`, `7π/4`, `arctan 2` and `π + arctan 2`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_b {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    (1 / cos x) ^ 2 = tan x + 3 ↔
      x = 3 * π / 4 ∨ x = 7 * π / 4 ∨ x = arctan 2 ∨ x = π + arctan 2 := by
  have hp := pi_pos
  have key : (1 / cos x) ^ 2 = tan x + 3 ↔ tan x = -1 ∨ tan x = 2 := by
    constructor
    · intro h
      have hc : cos x ≠ 0 := by
        intro h0; rw [h0] at h; simp [tan_eq_sin_div_cos, h0] at h
      rw [sec_sq_aux hc] at h
      have : (tan x + 1) * (tan x - 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h2 | h2
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · have hc : cos x ≠ 0 := by
          intro h0; rw [tan_eq_sin_div_cos, h0] at h; simp at h
        rw [sec_sq_aux hc, h]; norm_num
      · have hc : cos x ≠ 0 := by
          intro h0; rw [tan_eq_sin_div_cos, h0] at h; simp at h
        rw [sec_sq_aux hc, h]; norm_num
  have a0 : 0 < arctan 2 := arctan_pos.2 (by norm_num)
  have a1 := arctan_lt_pi_div_two 2
  have e1 : arctan (-1) = -(π / 4) := by rw [arctan_neg, arctan_one]
  rw [key, tan_eq_iff_aux (by norm_num), tan_eq_iff_aux (by norm_num), e1]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · have a : (0 : ℝ) < n := by
        by_contra hh; push Not at hh; nlinarith
      have b : (n : ℝ) < 3 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (0 : ℤ) < n := by exact_mod_cast a
      have b' : n < 3 := by exact_mod_cast b
      obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
      · left; push_cast at hn; linarith
      · right; left; push_cast at hn; linarith
    · have a : (-1 : ℝ) < n := by
        by_contra hh; push Not at hh; nlinarith
      have b : (n : ℝ) < 2 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < n := by exact_mod_cast a
      have b' : n < 2 := by exact_mod_cast b
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · right; right; left; simpa using hn
      · right; right; right; push_cast at hn; linarith
  · rintro (h | h | h | h)
    · exact Or.inl ⟨1, by rw [h]; push_cast; ring⟩
    · exact Or.inl ⟨2, by rw [h]; push_cast; ring⟩
    · exact Or.inr ⟨0, by simp [h]⟩
    · exact Or.inr ⟨1, by rw [h]; push_cast; ring⟩

/-- Stitz-Zeager Example 10.7.2(4): `cos 3x = 2 - cos x` holds exactly for `x = 2πk`
(`k` an integer); in particular `x = 0` is the only solution in `[0, 2π)`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_d (x : ℝ) :
    cos (3 * x) = 2 - cos x ↔ ∃ k : ℤ, x = k * (2 * π) := by
  have key : cos (3 * x) = 2 - cos x ↔ cos x = 1 := by
    rw [cos_three_mul]
    constructor
    · intro h
      have : (cos x - 1) * ((2 * cos x + 1) ^ 2 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h2 | h2
      · linarith
      · nlinarith [sq_nonneg (2 * cos x + 1)]
    · intro h; rw [h]; norm_num
  rw [key, cos_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

/-- Stitz-Zeager Example 10.7.2(4): the only solution of `cos 3x = 2 - cos x` in `[0, 2π)` is
`x = 0`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_d_unique {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    cos (3 * x) = 2 - cos x ↔ x = 0 := by
  have hp := pi_pos
  rw [ex_10_7_2_d]
  constructor
  · rintro ⟨k, hk⟩
    have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 1 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 1 := by exact_mod_cast b
    obtain rfl : k = 0 := by omega
    simpa using hk
  · intro h; exact ⟨0, by simp [h]⟩

/-- Stitz-Zeager Example 10.7.2(5): `cos 3x = cos 5x` holds exactly for `x = (π/4) k`
(`k` an integer). -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_e (x : ℝ) : cos (3 * x) = cos (5 * x) ↔ ∃ k : ℤ, x = π / 4 * k := by
  rw [cos_eq_cos_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨4 * k, by push_cast; linarith⟩
    · exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Or.inr (by linarith)⟩

/-- Stitz-Zeager Example 10.7.2(5): the solutions of `cos 3x = cos 5x` in `[0, 2π)` are the
eight numbers `(π/4) j`, `j = 0, ..., 7`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_e_list {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    cos (3 * x) = cos (5 * x) ↔ ∃ j : ℕ, j < 8 ∧ x = π / 4 * j := by
  have hp := pi_pos
  rw [ex_10_7_2_e]
  constructor
  · rintro ⟨k, hk⟩
    have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 8 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 8 := by exact_mod_cast b
    refine ⟨k.toNat, by omega, ?_⟩
    rw [hk]
    congr 1
    have : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this.symm
  · rintro ⟨j, -, hj⟩
    exact ⟨j, by rw [hj]; push_cast; ring⟩

/-- Stitz-Zeager Example 10.7.2(6): in `[0, 2π)`, `sin 2x = √3 cos x` holds exactly for
`x = π/3`, `π/2`, `2π/3`, `3π/2`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_f {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    sin (2 * x) = √3 * cos x ↔
      x = π / 3 ∨ x = π / 2 ∨ x = 2 * π / 3 ∨ x = 3 * π / 2 := by
  have hp := pi_pos
  have key : sin (2 * x) = √3 * cos x ↔ cos x = 0 ∨ sin x = sin (π / 3) := by
    rw [sin_two_mul, sin_pi_div_three]
    constructor
    · intro h
      have : cos x * (2 * sin x - √3) = 0 := by linarith
      rcases mul_eq_zero.1 this with h2 | h2
      · left; exact h2
      · right; linarith
    · rintro (h | h)
      · rw [h]; ring
      · rw [h]; ring
  have hs := sin_eq_sin_Ico (a := π / 3) (by linarith) (by linarith) h0 h1
  have hc : cos x = 0 ↔ x = π / 2 ∨ x = 3 * π / 2 := by
    rw [cos_eq_zero_iff]
    constructor
    · rintro ⟨k, hk⟩
      have a : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith
      have b : (k : ℝ) < 2 := by
        by_contra hh; push Not at hh; nlinarith
      have a' : (-1 : ℤ) < k := by exact_mod_cast a
      have b' : k < 2 := by exact_mod_cast b
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · left; simp at hk; linarith
      · right; push_cast at hk; linarith
    · rintro (h | h)
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by rw [h]; push_cast; ring⟩
  rw [key, hc, hs, show π - π / 3 = 2 * π / 3 by ring]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inr h)

/-- Stitz-Zeager Example 10.7.2(7): `sin x cos (x/2) + cos x sin (x/2) = 1` holds exactly for
`x = π/3 + (4π/3) k`; in `[0, 2π)` these are `π/3` and `5π/3`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_g (x : ℝ) :
    sin x * cos (x / 2) + cos x * sin (x / 2) = 1 ↔ ∃ k : ℤ, x = π / 3 + 4 * π / 3 * k := by
  have key : sin x * cos (x / 2) + cos x * sin (x / 2) = 1 ↔ sin (π / 2) = sin (x + x / 2) := by
    rw [sin_add, sin_pi_div_two, eq_comm]
  rw [key, sin_eq_sin_iff]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact ⟨k, by linarith⟩
    · exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Or.inl (by linarith)⟩

/-- Stitz-Zeager Example 10.7.2(7): in `[0, 2π)`, the solutions of
`sin x cos (x/2) + cos x sin (x/2) = 1` are `π/3` and `5π/3`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_g_list {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    sin x * cos (x / 2) + cos x * sin (x / 2) = 1 ↔ x = π / 3 ∨ x = 5 * π / 3 := by
  have hp := pi_pos
  rw [ex_10_7_2_g]
  constructor
  · rintro ⟨k, hk⟩
    have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 2 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 2 := by exact_mod_cast b
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · left; simpa using hk
    · right; push_cast at hk; linarith
  · rintro (h | h)
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by rw [h]; push_cast; ring⟩

/-- Stitz-Zeager Example 10.7.2(8): `cos x - √3 sin x = 2 sin (x + 5π/6)` for every `x`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_h_form (x : ℝ) : cos x - √3 * sin x = 2 * sin (x + 5 * π / 6) := by
  rw [sin_add, show 5 * π / 6 = π - π / 6 by ring, sin_pi_sub, cos_pi_sub, sin_pi_div_six,
    cos_pi_div_six]
  ring

/-- Stitz-Zeager Example 10.7.2(8): `cos x - √3 sin x = 2` holds exactly for
`x = -π/3 + 2πk`; in `[0, 2π)` the only solution is `5π/3`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_h (x : ℝ) :
    cos x - √3 * sin x = 2 ↔ ∃ k : ℤ, x = -(π / 3) + 2 * π * k := by
  have key : cos x - √3 * sin x = 2 ↔ cos (x + π / 3) = 1 := by
    rw [cos_add, cos_pi_div_three, sin_pi_div_three]
    constructor <;> intro h <;> linarith
  rw [key, cos_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Example 10.7.2(8): the only solution of `cos x - √3 sin x = 2` in `[0, 2π)` is
`5π/3`. -/
@[kb "stitzzeager2013" "Example 10.7.2, p. 874"]
theorem ex_10_7_2_h_unique {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 2 * π) :
    cos x - √3 * sin x = 2 ↔ x = 5 * π / 3 := by
  have hp := pi_pos
  rw [ex_10_7_2_h]
  constructor
  · rintro ⟨k, hk⟩
    have a : (0 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 2 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (0 : ℤ) < k := by exact_mod_cast a
    have b' : k < 2 := by exact_mod_cast b
    obtain rfl : k = 1 := by omega
    push_cast at hk; linarith
  · intro h; exact ⟨1, by rw [h]; push_cast; ring⟩

end UndergradKB.Precalculus.Course
