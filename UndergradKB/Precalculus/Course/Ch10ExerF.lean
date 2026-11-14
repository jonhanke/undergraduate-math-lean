import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.5 -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Period, boundedness and extreme values of `A sin(ωx + φ) + B` (`A ≠ 0`, `ω > 0`):
`2π/ω` is the least positive period, and `B ± |A|` are the extreme values. -/
private lemma sinusoid_facts (A ω φ B : ℝ) (hA : A ≠ 0) (hω : 0 < ω) :
    Function.Periodic (fun x => A * sin (ω * x + φ) + B) (2 * π / ω) ∧
    (∀ p, 0 < p → Function.Periodic (fun x => A * sin (ω * x + φ) + B) p → 2 * π / ω ≤ p) ∧
    (∀ x, B - |A| ≤ A * sin (ω * x + φ) + B ∧ A * sin (ω * x + φ) + B ≤ B + |A|) ∧
    (∃ x, A * sin (ω * x + φ) + B = B + |A|) ∧ (∃ x, A * sin (ω * x + φ) + B = B - |A|) := by
  have hne : ω ≠ 0 := hω.ne'
  have e1 : ω * ((π / 2 - φ) / ω) + φ = π / 2 := by field_simp; ring
  have e1' : ω * ((-(π / 2) - φ) / ω) + φ = -(π / 2) := by field_simp; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show A * sin (ω * (x + 2 * π / ω) + φ) + B = A * sin (ω * x + φ) + B
    rw [show ω * (x + 2 * π / ω) + φ = (ω * x + φ) + 2 * π by field_simp; ring, sin_add_two_pi]
  · intro p hp hper
    have h0 := hper ((π / 2 - φ) / ω)
    simp only at h0
    have e1 : ω * ((π / 2 - φ) / ω) + φ = π / 2 := by field_simp; ring
    have e2 : ω * ((π / 2 - φ) / ω + p) + φ = π / 2 + ω * p := by field_simp; ring
    rw [e2, e1, sin_pi_div_two] at h0
    have h1 : sin (π / 2 + ω * p) = 1 := by
      have : A * sin (π / 2 + ω * p) = A * 1 := by linarith
      exact mul_left_cancel₀ hA this
    have h2 : cos (ω * p) = 1 := by
      rw [sin_add, sin_pi_div_two, cos_pi_div_two] at h1; linarith
    obtain ⟨k, hk⟩ := (cos_eq_one_iff _).mp h2
    have hωp : 0 < ω * p := mul_pos hω hp
    have hk0 : (0 : ℝ) < k := by
      by_contra hneg
      have hneg := not_lt.mp hneg
      nlinarith [Real.pi_pos]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k from by exact_mod_cast hk0)
    rw [div_le_iff₀ hω]
    nlinarith [Real.pi_pos]
  · intro x
    have : |A * sin (ω * x + φ)| ≤ |A| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)
    have := abs_le.mp this
    constructor <;> linarith
  · rcases lt_or_gt_of_ne hA with h | h
    · refine ⟨(-(π / 2) - φ) / ω, ?_⟩
      rw [e1', sin_neg, sin_pi_div_two, abs_of_neg h]; ring
    · refine ⟨(π / 2 - φ) / ω, ?_⟩
      rw [e1, sin_pi_div_two, abs_of_pos h]; ring
  · rcases lt_or_gt_of_ne hA with h | h
    · refine ⟨(π / 2 - φ) / ω, ?_⟩
      rw [e1, sin_pi_div_two, abs_of_neg h]; ring
    · refine ⟨(-(π / 2) - φ) / ω, ?_⟩
      rw [e1', sin_neg, sin_pi_div_two, abs_of_pos h]; ring

private lemma sinusoid_of (f : ℝ → ℝ) (A ω φ B : ℝ) (hA : A ≠ 0) (hω : 0 < ω)
    (hf : ∀ x, f x = A * sin (ω * x + φ) + B) :
    Function.Periodic f (2 * π / ω) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π / ω ≤ p) ∧
    (∀ x, B - |A| ≤ f x ∧ f x ≤ B + |A|) ∧ (∃ x, f x = B + |A|) ∧ (∃ x, f x = B - |A|) := by
  have : f = fun x => A * sin (ω * x + φ) + B := funext hf
  subst this
  exact sinusoid_facts A ω φ B hA hω

/-- Stitz-Zeager Exercise 10.5.1: `y = 3 sin x` has period `2π` and amplitude `3`
(values range over `[-3, 3]`, both extremes attained). -/
@[kb "stitzzeager2013" "Exercise 10.5.1, p. 821"]
theorem exer_10_5_1 (f : ℝ → ℝ) (hf : ∀ x, f x = 3 * sin x) :
    Function.Periodic f (2 * π) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p) ∧
    (∀ x, -3 ≤ f x ∧ f x ≤ 3) ∧ (∃ x, f x = 3) ∧ (∃ x, f x = -3) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f 3 1 0 0 (by norm_num) (by norm_num)
    (fun x => by rw [hf]; simp)
  simp only [div_one] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.2: `y = sin 3x` has period `2π/3` and amplitude `1`. -/
@[kb "stitzzeager2013" "Exercise 10.5.2, p. 821"]
theorem exer_10_5_2 (f : ℝ → ℝ) (hf : ∀ x, f x = sin (3 * x)) :
    Function.Periodic f (2 * π / 3) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π / 3 ≤ p) ∧
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) ∧ (∃ x, f x = 1) ∧ (∃ x, f x = -1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f 1 3 0 0 (by norm_num) (by norm_num)
    (fun x => by rw [hf]; simp)
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.3: `y = -2 cos x` has period `2π` and amplitude `2`. -/
@[kb "stitzzeager2013" "Exercise 10.5.3, p. 821"]
theorem exer_10_5_3 (f : ℝ → ℝ) (hf : ∀ x, f x = -2 * cos x) :
    Function.Periodic f (2 * π) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p) ∧
    (∀ x, -2 ≤ f x ∧ f x ≤ 2) ∧ (∃ x, f x = 2) ∧ (∃ x, f x = -2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f 2 1 (-(π / 2)) 0 (by norm_num) (by norm_num)
    (fun x => by
      rw [hf, show (1 : ℝ) * x + -(π / 2) = x - π / 2 by ring, sin_sub_pi_div_two]; ring)
  simp only [div_one] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.4: `y = cos(x - π/2)` has period `2π` and amplitude `1`
(phase shift `π/2`). -/
@[kb "stitzzeager2013" "Exercise 10.5.4, p. 821"]
theorem exer_10_5_4 (f : ℝ → ℝ) (hf : ∀ x, f x = cos (x - π / 2)) :
    Function.Periodic f (2 * π) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p) ∧
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) ∧ (∃ x, f x = 1) ∧ (∃ x, f x = -1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f 1 1 0 0 (by norm_num) (by norm_num)
    (fun x => by rw [hf, cos_sub_pi_div_two]; simp)
  simp only [div_one] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.6: `y = sin(2x - π)` has period `π` and amplitude `1`. -/
@[kb "stitzzeager2013" "Exercise 10.5.6, p. 821"]
theorem exer_10_5_6 (f : ℝ → ℝ) (hf : ∀ x, f x = sin (2 * x - π)) :
    Function.Periodic f π ∧ (∀ p, 0 < p → Function.Periodic f p → π ≤ p) ∧
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) ∧ (∃ x, f x = 1) ∧ (∃ x, f x = -1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f 1 2 (-π) 0 (by norm_num) (by norm_num)
    (fun x => by rw [hf, show (2 : ℝ) * x + -π = 2 * x - π by ring]; ring)
  rw [show 2 * π / 2 = π by ring] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.7: `y = -(1/3) cos(x/2 + π/3)` has period `4π` and amplitude `1/3`. -/
@[kb "stitzzeager2013" "Exercise 10.5.7, p. 821"]
theorem exer_10_5_7 (f : ℝ → ℝ) (hf : ∀ x, f x = -(1 / 3) * cos (1 / 2 * x + π / 3)) :
    Function.Periodic f (4 * π) ∧ (∀ p, 0 < p → Function.Periodic f p → 4 * π ≤ p) ∧
    (∀ x, -(1 / 3) ≤ f x ∧ f x ≤ 1 / 3) ∧ (∃ x, f x = 1 / 3) ∧ (∃ x, f x = -(1 / 3)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f (1 / 3) (1 / 2) (π / 3 - π / 2) 0 (by norm_num)
    (by norm_num)
    (fun x => by
      rw [hf, show 1 / 2 * x + (π / 3 - π / 2) = (1 / 2 * x + π / 3) - π / 2 by ring,
        sin_sub_pi_div_two]; ring)
  rw [show 2 * π / (1 / 2) = 4 * π by ring] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.8: `y = cos(3x - 2π) + 4` has period `2π/3`, amplitude `1`, and
vertical shift `4` (values range over `[3, 5]`). -/
@[kb "stitzzeager2013" "Exercise 10.5.8, p. 821"]
theorem exer_10_5_8 (f : ℝ → ℝ) (hf : ∀ x, f x = cos (3 * x - 2 * π) + 4) :
    Function.Periodic f (2 * π / 3) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π / 3 ≤ p) ∧
    (∀ x, 3 ≤ f x ∧ f x ≤ 5) ∧ (∃ x, f x = 5) ∧ (∃ x, f x = 3) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f 1 3 (π / 2 - 2 * π) 4 (by norm_num) (by norm_num)
    (fun x => by
      rw [hf, show 3 * x + (π / 2 - 2 * π) = (3 * x - 2 * π) + π / 2 by ring, sin_add_pi_div_two]
      ring)
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.12: `y = 4 sin(-2πx + π)` has period `1` and amplitude `4`. -/
@[kb "stitzzeager2013" "Exercise 10.5.12, p. 821"]
theorem exer_10_5_12 (f : ℝ → ℝ) (hf : ∀ x, f x = 4 * sin (-2 * π * x + π)) :
    Function.Periodic f 1 ∧ (∀ p, 0 < p → Function.Periodic f p → 1 ≤ p) ∧
    (∀ x, -4 ≤ f x ∧ f x ≤ 4) ∧ (∃ x, f x = 4) ∧ (∃ x, f x = -4) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f 4 (2 * π) 0 0 (by norm_num)
    (by positivity)
    (fun x => by
      rw [hf, show -2 * π * x + π = π - 2 * π * x by ring, sin_pi_sub]; ring_nf)
  rw [show 2 * π / (2 * π) = 1 by field_simp] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

private lemma cos_phase (y φ φ' : ℝ) (k : ℤ) (h : φ' = φ - π / 2 + 2 * π * k) :
    cos (y + φ') = sin (y + φ) := by
  have : y + φ' = (y + φ - π / 2) + k * (2 * π) := by rw [h]; ring
  rw [this, cos_add_int_mul_two_pi, cos_sub_pi_div_two]

private lemma cs_pi4 : cos (π / 4) = √2 / 2 ∧ sin (π / 4) = √2 / 2 :=
  ⟨cos_pi_div_four, sin_pi_div_four⟩

private lemma cs_11pi6 : cos (11 * π / 6) = √3 / 2 ∧ sin (11 * π / 6) = -(1 / 2) := by
  rw [show 11 * π / 6 = -(π / 6) + ((1 : ℤ) : ℝ) * (2 * π) by push_cast; ring,
    cos_add_int_mul_two_pi, sin_add_int_mul_two_pi, cos_neg, sin_neg, cos_pi_div_six,
    sin_pi_div_six]; exact ⟨rfl, rfl⟩

private lemma cs_3pi4 : cos (3 * π / 4) = -(√2 / 2) ∧ sin (3 * π / 4) = √2 / 2 := by
  rw [show 3 * π / 4 = π - π / 4 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four]
  exact ⟨rfl, rfl⟩

private lemma cs_4pi3 : cos (4 * π / 3) = -(1 / 2) ∧ sin (4 * π / 3) = -(√3 / 2) := by
  rw [show 4 * π / 3 = π / 3 + π by ring, cos_add_pi, sin_add_pi, cos_pi_div_three,
    sin_pi_div_three]; exact ⟨rfl, rfl⟩

private lemma cs_2pi3 : cos (2 * π / 3) = -(1 / 2) ∧ sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_three,
    sin_pi_div_three]; exact ⟨rfl, rfl⟩

private lemma cs_5pi6 : cos (5 * π / 6) = -(√3 / 2) ∧ sin (5 * π / 6) = 1 / 2 := by
  rw [show 5 * π / 6 = π - π / 6 by ring, cos_pi_sub, sin_pi_sub, cos_pi_div_six, sin_pi_div_six]
  exact ⟨rfl, rfl⟩

private lemma cs_7pi6 : cos (7 * π / 6) = -(√3 / 2) ∧ sin (7 * π / 6) = -(1 / 2) := by
  rw [show 7 * π / 6 = π / 6 + π by ring, cos_add_pi, sin_add_pi, cos_pi_div_six, sin_pi_div_six]
  exact ⟨rfl, rfl⟩

private lemma cs_7pi4 : cos (7 * π / 4) = √2 / 2 ∧ sin (7 * π / 4) = -(√2 / 2) := by
  rw [show 7 * π / 4 = 2 * π - π / 4 by ring, cos_two_pi_sub, sin_two_pi_sub, cos_pi_div_four,
    sin_pi_div_four]; exact ⟨rfl, rfl⟩

private lemma cs_5pi3 : cos (5 * π / 3) = 1 / 2 ∧ sin (5 * π / 3) = -(√3 / 2) := by
  rw [show 5 * π / 3 = 2 * π - π / 3 by ring, cos_two_pi_sub, sin_two_pi_sub, cos_pi_div_three,
    sin_pi_div_three]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.5.25: `√2 sin x + √2 cos x + 1 = 2 sin(x + π/4) + 1 = 2 cos(x + 7π/4) + 1`. -/
@[kb "stitzzeager2013" "Exercise 10.5.25, p. 821"]
theorem exer_10_5_25 (x : ℝ) :
    √2 * sin x + √2 * cos x + 1 = 2 * sin (x + π / 4) + 1 ∧
      √2 * sin x + √2 * cos x + 1 = 2 * cos (x + 7 * π / 4) + 1 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : √2 * sin x + √2 * cos x + 1 = 2 * sin (x + π / 4) + 1 := by
    rw [sin_add, cs_pi4.1, cs_pi4.2]; ring
  refine ⟨hs, ?_⟩
  rw [show x + 7 * π / 4 = x + (7 * π / 4) by ring, cos_phase x (π / 4) (7 * π / 4) 1
    (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.26: `3√3 sin 3x - 3 cos 3x = 6 sin(3x + 11π/6) = 6 cos(3x + 4π/3)`. -/
@[kb "stitzzeager2013" "Exercise 10.5.26, p. 821"]
theorem exer_10_5_26 (x : ℝ) :
    3 * √3 * sin (3 * x) - 3 * cos (3 * x) = 6 * sin (3 * x + 11 * π / 6) ∧
      3 * √3 * sin (3 * x) - 3 * cos (3 * x) = 6 * cos (3 * x + 4 * π / 3) := by
  have hs : 3 * √3 * sin (3 * x) - 3 * cos (3 * x) = 6 * sin (3 * x + 11 * π / 6) := by
    rw [show 3 * x + 11 * π / 6 = 3 * x + 11 * π / 6 by ring, sin_add, cs_11pi6.1, cs_11pi6.2]
    ring
  refine ⟨hs, ?_⟩
  rw [cos_phase (3 * x) (11 * π / 6) (4 * π / 3) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.27: `-sin x + cos x - 2 = √2 sin(x + 3π/4) - 2 = √2 cos(x + π/4) - 2`. -/
@[kb "stitzzeager2013" "Exercise 10.5.27, p. 821"]
theorem exer_10_5_27 (x : ℝ) :
    -sin x + cos x - 2 = √2 * sin (x + 3 * π / 4) - 2 ∧
      -sin x + cos x - 2 = √2 * cos (x + π / 4) - 2 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : -sin x + cos x - 2 = √2 * sin (x + 3 * π / 4) - 2 := by
    rw [sin_add, cs_3pi4.1, cs_3pi4.2]; linear_combination ((sin x - cos x) / 2) * h2
  refine ⟨hs, ?_⟩
  rw [cos_phase x (3 * π / 4) (π / 4) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.28: `-(1/2) sin 2x - (√3/2) cos 2x = sin(2x + 4π/3) = cos(2x + 5π/6)`. -/
@[kb "stitzzeager2013" "Exercise 10.5.28, p. 821"]
theorem exer_10_5_28 (x : ℝ) :
    -(1 / 2) * sin (2 * x) - √3 / 2 * cos (2 * x) = sin (2 * x + 4 * π / 3) ∧
      -(1 / 2) * sin (2 * x) - √3 / 2 * cos (2 * x) = cos (2 * x + 5 * π / 6) := by
  have hs : -(1 / 2) * sin (2 * x) - √3 / 2 * cos (2 * x) = sin (2 * x + 4 * π / 3) := by
    rw [sin_add, cs_4pi3.1, cs_4pi3.2]; ring
  refine ⟨hs, ?_⟩
  rw [cos_phase (2 * x) (4 * π / 3) (5 * π / 6) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.29: `2√3 cos x - 2 sin x = 4 sin(x + 2π/3) = 4 cos(x + π/6)`. -/
@[kb "stitzzeager2013" "Exercise 10.5.29, p. 821"]
theorem exer_10_5_29 (x : ℝ) :
    2 * √3 * cos x - 2 * sin x = 4 * sin (x + 2 * π / 3) ∧
      2 * √3 * cos x - 2 * sin x = 4 * cos (x + π / 6) := by
  have hs : 2 * √3 * cos x - 2 * sin x = 4 * sin (x + 2 * π / 3) := by
    rw [sin_add, cs_2pi3.1, cs_2pi3.2]; ring
  refine ⟨hs, ?_⟩
  rw [cos_phase x (2 * π / 3) (π / 6) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.30: `(3/2) cos 2x - (3√3/2) sin 2x + 6 = 3 sin(2x + 5π/6) + 6
= 3 cos(2x + π/3) + 6`. -/
@[kb "stitzzeager2013" "Exercise 10.5.30, p. 821"]
theorem exer_10_5_30 (x : ℝ) :
    3 / 2 * cos (2 * x) - 3 * √3 / 2 * sin (2 * x) + 6 = 3 * sin (2 * x + 5 * π / 6) + 6 ∧
      3 / 2 * cos (2 * x) - 3 * √3 / 2 * sin (2 * x) + 6 = 3 * cos (2 * x + π / 3) + 6 := by
  have hs : 3 / 2 * cos (2 * x) - 3 * √3 / 2 * sin (2 * x) + 6 =
      3 * sin (2 * x + 5 * π / 6) + 6 := by
    rw [sin_add, cs_5pi6.1, cs_5pi6.2]; ring
  refine ⟨hs, ?_⟩
  rw [cos_phase (2 * x) (5 * π / 6) (π / 3) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.31: `-(1/2) cos 5x - (√3/2) sin 5x = sin(5x + 7π/6) = cos(5x + 2π/3)`. -/
@[kb "stitzzeager2013" "Exercise 10.5.31, p. 821"]
theorem exer_10_5_31 (x : ℝ) :
    -(1 / 2) * cos (5 * x) - √3 / 2 * sin (5 * x) = sin (5 * x + 7 * π / 6) ∧
      -(1 / 2) * cos (5 * x) - √3 / 2 * sin (5 * x) = cos (5 * x + 2 * π / 3) := by
  have hs : -(1 / 2) * cos (5 * x) - √3 / 2 * sin (5 * x) = sin (5 * x + 7 * π / 6) := by
    rw [sin_add, cs_7pi6.1, cs_7pi6.2]; ring
  refine ⟨hs, ?_⟩
  rw [cos_phase (5 * x) (7 * π / 6) (2 * π / 3) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.32: `-6√3 cos 3x - 6 sin 3x - 3 = 12 sin(3x + 4π/3) - 3
= 12 cos(3x + 5π/6) - 3`. -/
@[kb "stitzzeager2013" "Exercise 10.5.32, p. 821"]
theorem exer_10_5_32 (x : ℝ) :
    -6 * √3 * cos (3 * x) - 6 * sin (3 * x) - 3 = 12 * sin (3 * x + 4 * π / 3) - 3 ∧
      -6 * √3 * cos (3 * x) - 6 * sin (3 * x) - 3 = 12 * cos (3 * x + 5 * π / 6) - 3 := by
  have hs : -6 * √3 * cos (3 * x) - 6 * sin (3 * x) - 3 = 12 * sin (3 * x + 4 * π / 3) - 3 := by
    rw [sin_add, cs_4pi3.1, cs_4pi3.2]; ring
  refine ⟨hs, ?_⟩
  rw [cos_phase (3 * x) (4 * π / 3) (5 * π / 6) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.33: `(5√2/2) sin x - (5√2/2) cos x = 5 sin(x + 7π/4) = 5 cos(x + 5π/4)`. -/
@[kb "stitzzeager2013" "Exercise 10.5.33, p. 822"]
theorem exer_10_5_33 (x : ℝ) :
    5 * √2 / 2 * sin x - 5 * √2 / 2 * cos x = 5 * sin (x + 7 * π / 4) ∧
      5 * √2 / 2 * sin x - 5 * √2 / 2 * cos x = 5 * cos (x + 5 * π / 4) := by
  have hs : 5 * √2 / 2 * sin x - 5 * √2 / 2 * cos x = 5 * sin (x + 7 * π / 4) := by
    rw [sin_add, cs_7pi4.1, cs_7pi4.2]; ring
  refine ⟨hs, ?_⟩
  rw [cos_phase x (7 * π / 4) (5 * π / 4) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.34: `3 sin(x/6) - 3√3 cos(x/6) = 6 sin(x/6 + 5π/3) = 6 cos(x/6 + 7π/6)`. -/
@[kb "stitzzeager2013" "Exercise 10.5.34, p. 822"]
theorem exer_10_5_34 (x : ℝ) :
    3 * sin (x / 6) - 3 * √3 * cos (x / 6) = 6 * sin (x / 6 + 5 * π / 3) ∧
      3 * sin (x / 6) - 3 * √3 * cos (x / 6) = 6 * cos (x / 6 + 7 * π / 6) := by
  have hs : 3 * sin (x / 6) - 3 * √3 * cos (x / 6) = 6 * sin (x / 6 + 5 * π / 3) := by
    rw [sin_add, cs_5pi3.1, cs_5pi3.2]; ring
  refine ⟨hs, ?_⟩
  rw [cos_phase (x / 6) (5 * π / 3) (7 * π / 6) 0 (by push_cast; ring)]
  exact hs

/-- Stitz-Zeager Exercise 10.5.35: `A sin(ωx + α) + B = A cos(ωx + (α - π/2)) + B`. -/
@[kb "stitzzeager2013" "Exercise 10.5.35, p. 822"]
theorem exer_10_5_35 (A ω α B x : ℝ) :
    A * sin (ω * x + α) + B = A * cos (ω * x + (α - π / 2)) + B := by
  rw [show ω * x + (α - π / 2) = (ω * x + α) - π / 2 by ring, cos_sub_pi_div_two]

end UndergradKB.Precalculus.Course
