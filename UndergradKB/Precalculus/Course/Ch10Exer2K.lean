import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Course.Ch10Extra

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.5 (periods, amplitudes and extreme values of the graphs of the trigonometric functions) -/

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


/-- Transformation `A g(ωx + φ) + B` of a function `g` with least positive period `P` has least
positive period `P/ω`. -/
private lemma period_transform (g : ℝ → ℝ) (P A ω φ B : ℝ) (hA : A ≠ 0) (hω : 0 < ω)
    (hg : Function.Periodic g P) (hl : ∀ c, 0 < c → Function.Periodic g c → P ≤ c)
    (f : ℝ → ℝ) (hf : ∀ x, f x = A * g (ω * x + φ) + B) :
    Function.Periodic f (P / ω) ∧ ∀ p, 0 < p → Function.Periodic f p → P / ω ≤ p := by
  refine ⟨fun x => ?_, fun p hp hper => ?_⟩
  · rw [hf, hf, show ω * (x + P / ω) + φ = (ω * x + φ) + P by field_simp; ring, hg]
  · rw [div_le_iff₀ hω, mul_comm]
    refine hl (ω * p) (mul_pos hω hp) (fun y => ?_)
    have h0 := hper ((y - φ) / ω)
    rw [hf, hf] at h0
    have e1 : ω * ((y - φ) / ω) + φ = y := by field_simp; ring
    have e2 : ω * ((y - φ) / ω + p) + φ = y + ω * p := by field_simp; ring
    rw [e1, e2] at h0
    have : A * g (y + ω * p) = A * g y := by linarith
    exact mul_left_cancel₀ hA this

private lemma sec_base : Function.Periodic (fun y => 1 / cos y) (2 * π) ∧
    ∀ c, 0 < c → Function.Periodic (fun y => 1 / cos y) c → 2 * π ≤ c :=
  ⟨fun x => by simp [Real.cos_add_two_pi],
    fun c hc hp => thm_10_24_sec_csc.2.2.2.2.2.2.1.2 ⟨hc, hp⟩⟩

private lemma csc_base : Function.Periodic (fun y => 1 / sin y) (2 * π) ∧
    ∀ c, 0 < c → Function.Periodic (fun y => 1 / sin y) c → 2 * π ≤ c :=
  ⟨fun x => by simp [Real.sin_add_two_pi],
    fun c hc hp => thm_10_24_sec_csc.2.2.2.2.2.2.2.2 ⟨hc, hp⟩⟩

private lemma tan_base : Function.Periodic tan π ∧
    ∀ c, 0 < c → Function.Periodic tan c → π ≤ c :=
  ⟨Real.tan_periodic, fun c hc hp => thm_10_25_tan_cot.2.2.2.2.2.2.1.2 ⟨hc, hp⟩⟩

private lemma cot_base : Function.Periodic (fun y => cos y / sin y) π ∧
    ∀ c, 0 < c → Function.Periodic (fun y => cos y / sin y) c → π ≤ c :=
  ⟨fun x => by simp [Real.cos_add_pi, Real.sin_add_pi],
    fun c hc hp => thm_10_25_tan_cot.2.2.2.2.2.2.2.2 ⟨hc, hp⟩⟩

/-- Stitz-Zeager Exercise 10.5.5: `y = -sin(x + π/3)` has period `2π` and amplitude `1`
(phase shift `-π/3`). -/
@[kb "stitzzeager2013" "Exercise 10.5.5, p. 821"]
theorem exer_10_5_5 (f : ℝ → ℝ) (hf : ∀ x, f x = -sin (x + π / 3)) :
    Function.Periodic f (2 * π) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p) ∧
    (∀ x, -1 ≤ f x ∧ f x ≤ 1) ∧ (∃ x, f x = 1) ∧ (∃ x, f x = -1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f (-1) 1 (π / 3) 0 (by norm_num) (by norm_num)
    (fun x => by rw [hf]; ring)
  simp only [div_one] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.9: `y = sin(-x - π/4) - 2` has period `2π`, amplitude `1`
and vertical shift `-2` (values fill `[-3, -1]`). -/
@[kb "stitzzeager2013" "Exercise 10.5.9, p. 821"]
theorem exer_10_5_9 (f : ℝ → ℝ) (hf : ∀ x, f x = sin (-x - π / 4) - 2) :
    Function.Periodic f (2 * π) ∧ (∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p) ∧
    (∀ x, -3 ≤ f x ∧ f x ≤ -1) ∧ (∃ x, f x = -1) ∧ (∃ x, f x = -3) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f (-1) 1 (π / 4) (-2) (by norm_num) (by norm_num)
    (fun x => by
      rw [hf, show -x - π / 4 = -(x + π / 4) by ring, sin_neg]; ring)
  simp only [div_one] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.10: `y = (2/3) cos(π/2 - 4x) + 1` has period `π/2`, amplitude `2/3`
and vertical shift `1`. -/
@[kb "stitzzeager2013" "Exercise 10.5.10, p. 821"]
theorem exer_10_5_10 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 / 3 * cos (π / 2 - 4 * x) + 1) :
    Function.Periodic f (π / 2) ∧ (∀ p, 0 < p → Function.Periodic f p → π / 2 ≤ p) ∧
    (∀ x, 1 / 3 ≤ f x ∧ f x ≤ 5 / 3) ∧ (∃ x, f x = 5 / 3) ∧ (∃ x, f x = 1 / 3) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f (2 / 3) 4 0 1 (by norm_num) (by norm_num)
    (fun x => by rw [hf, cos_pi_div_two_sub]; ring)
  rw [show 2 * π / 4 = π / 2 by ring] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.11: `y = -(3/2) cos(2x + π/3) - 1/2` has period `π`, amplitude `3/2`
and vertical shift `-1/2` (values fill `[-2, 1]`). -/
@[kb "stitzzeager2013" "Exercise 10.5.11, p. 821"]
theorem exer_10_5_11 (f : ℝ → ℝ) (hf : ∀ x, f x = -(3 / 2) * cos (2 * x + π / 3) - 1 / 2) :
    Function.Periodic f π ∧ (∀ p, 0 < p → Function.Periodic f p → π ≤ p) ∧
    (∀ x, -2 ≤ f x ∧ f x ≤ 1) ∧ (∃ x, f x = 1) ∧ (∃ x, f x = -2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sinusoid_of f (-(3 / 2)) 2 (π / 3 + π / 2) (-(1 / 2))
    (by norm_num) (by norm_num)
    (fun x => by
      rw [hf, show 2 * x + (π / 3 + π / 2) = (2 * x + π / 3) + π / 2 by ring, sin_add_pi_div_two]
      ring)
  rw [show 2 * π / 2 = π by ring] at h1 h2
  norm_num at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Stitz-Zeager Exercise 10.5.13: `y = tan(x - π/3)` has period `π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.13, p. 821"]
theorem exer_10_5_13 (f : ℝ → ℝ) (hf : ∀ x, f x = tan (x - π / 3)) :
    Function.Periodic f π ∧ ∀ p, 0 < p → Function.Periodic f p → π ≤ p := by
  have := period_transform tan π 1 1 (-(π / 3)) 0 (by norm_num) (by norm_num) tan_base.1
    tan_base.2 f (fun x => by rw [hf]; ring_nf)
  simpa using this

/-- Stitz-Zeager Exercise 10.5.14: `y = 2 tan(x/4 - 3)` has period `4π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.14, p. 821"]
theorem exer_10_5_14 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * tan (1 / 4 * x - 3)) :
    Function.Periodic f (4 * π) ∧ ∀ p, 0 < p → Function.Periodic f p → 4 * π ≤ p := by
  have := period_transform tan π 2 (1 / 4) (-3) 0 (by norm_num) (by norm_num) tan_base.1
    tan_base.2 f (fun x => by rw [hf]; ring_nf)
  rw [show π / (1 / 4) = 4 * π by ring] at this
  exact this

/-- Stitz-Zeager Exercise 10.5.15: `y = tan(-2x - π) + 1/3` has period `π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.5.15, p. 821"]
theorem exer_10_5_15 (f : ℝ → ℝ) (hf : ∀ x, f x = tan (-2 * x - π) + 1 / 3) :
    Function.Periodic f (π / 2) ∧ ∀ p, 0 < p → Function.Periodic f p → π / 2 ≤ p := by
  exact period_transform tan π (-1) 2 π (1 / 3) (by norm_num) (by norm_num) tan_base.1
    tan_base.2 f (fun x => by
      rw [hf, show -2 * x - π = -(2 * x + π) by ring, tan_neg]; ring)

/-- Stitz-Zeager Exercise 10.5.16: `y = sec(x - π/2)` has period `2π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.16, p. 821"]
theorem exer_10_5_16 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / cos (x - π / 2)) :
    Function.Periodic f (2 * π) ∧ ∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p := by
  have := period_transform (fun y => 1 / cos y) (2 * π) 1 1 (-(π / 2)) 0 (by norm_num)
    (by norm_num) sec_base.1 sec_base.2 f (fun x => by
      show f x = 1 * (1 / cos (1 * x + -(π / 2))) + 0
      rw [hf]; ring_nf)
  simpa using this

/-- Stitz-Zeager Exercise 10.5.17: `y = -csc(x + π/3)` has period `2π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.17, p. 821"]
theorem exer_10_5_17 (f : ℝ → ℝ) (hf : ∀ x, f x = -(1 / sin (x + π / 3))) :
    Function.Periodic f (2 * π) ∧ ∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p := by
  have := period_transform (fun y => 1 / sin y) (2 * π) (-1) 1 (π / 3) 0 (by norm_num)
    (by norm_num) csc_base.1 csc_base.2 f (fun x => by
      show f x = -1 * (1 / sin (1 * x + π / 3)) + 0
      rw [hf]; ring_nf)
  simpa using this

/-- Stitz-Zeager Exercise 10.5.18: `y = -(1/3) sec(x/2 + π/3)` has period `4π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.18, p. 821"]
theorem exer_10_5_18 (f : ℝ → ℝ) (hf : ∀ x, f x = -(1 / 3) * (1 / cos (1 / 2 * x + π / 3))) :
    Function.Periodic f (4 * π) ∧ ∀ p, 0 < p → Function.Periodic f p → 4 * π ≤ p := by
  have := period_transform (fun y => 1 / cos y) (2 * π) (-(1 / 3)) (1 / 2) (π / 3) 0
    (by norm_num) (by norm_num) sec_base.1 sec_base.2 f (fun x => by
      show f x = -(1 / 3) * (1 / cos (1 / 2 * x + π / 3)) + 0
      rw [hf]; ring)
  rw [show 2 * π / (1 / 2) = 4 * π by ring] at this
  exact this

/-- Stitz-Zeager Exercise 10.5.19: `y = csc(2x - π)` has period `π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.19, p. 821"]
theorem exer_10_5_19 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / sin (2 * x - π)) :
    Function.Periodic f π ∧ ∀ p, 0 < p → Function.Periodic f p → π ≤ p := by
  have := period_transform (fun y => 1 / sin y) (2 * π) 1 2 (-π) 0 (by norm_num)
    (by norm_num) csc_base.1 csc_base.2 f (fun x => by
      show f x = 1 * (1 / sin (2 * x + -π)) + 0
      rw [hf]; ring_nf)
  rw [show 2 * π / 2 = π by ring] at this
  exact this

/-- Stitz-Zeager Exercise 10.5.20: `y = sec(3x - 2π) + 4` has period `2π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.5.20, p. 821"]
theorem exer_10_5_20 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / cos (3 * x - 2 * π) + 4) :
    Function.Periodic f (2 * π / 3) ∧ ∀ p, 0 < p → Function.Periodic f p → 2 * π / 3 ≤ p := by
  exact period_transform (fun y => 1 / cos y) (2 * π) 1 3 (-(2 * π)) 4 (by norm_num)
    (by norm_num) sec_base.1 sec_base.2 f (fun x => by
      show f x = 1 * (1 / cos (3 * x + -(2 * π))) + 4
      rw [hf]; ring_nf)

/-- Stitz-Zeager Exercise 10.5.21: `y = csc(-x - π/4) - 2` has period `2π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.21, p. 821"]
theorem exer_10_5_21 (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / sin (-x - π / 4) - 2) :
    Function.Periodic f (2 * π) ∧ ∀ p, 0 < p → Function.Periodic f p → 2 * π ≤ p := by
  have := period_transform (fun y => 1 / sin y) (2 * π) (-1) 1 (π / 4) (-2) (by norm_num)
    (by norm_num) csc_base.1 csc_base.2 f (fun x => by
      show f x = -1 * (1 / sin (1 * x + π / 4)) + -2
      rw [hf, show -x - π / 4 = -(x + π / 4) by ring, sin_neg, one_mul, one_div, one_div, inv_neg]
      ring)
  simpa using this

/-- Stitz-Zeager Exercise 10.5.22: `y = cot(x + π/6)` has period `π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.22, p. 821"]
theorem exer_10_5_22 (f : ℝ → ℝ) (hf : ∀ x, f x = cos (x + π / 6) / sin (x + π / 6)) :
    Function.Periodic f π ∧ ∀ p, 0 < p → Function.Periodic f p → π ≤ p := by
  have := period_transform (fun y => cos y / sin y) π 1 1 (π / 6) 0 (by norm_num)
    (by norm_num) cot_base.1 cot_base.2 f (fun x => by
      show f x = 1 * (cos (1 * x + π / 6) / sin (1 * x + π / 6)) + 0
      rw [hf]; ring_nf)
  simpa using this

/-- Stitz-Zeager Exercise 10.5.23: `y = -11 cot(x/5)` has period `5π`. -/
@[kb "stitzzeager2013" "Exercise 10.5.23, p. 821"]
theorem exer_10_5_23 (f : ℝ → ℝ) (hf : ∀ x, f x = -11 * (cos (1 / 5 * x) / sin (1 / 5 * x))) :
    Function.Periodic f (5 * π) ∧ ∀ p, 0 < p → Function.Periodic f p → 5 * π ≤ p := by
  have := period_transform (fun y => cos y / sin y) π (-11) (1 / 5) 0 0 (by norm_num)
    (by norm_num) cot_base.1 cot_base.2 f (fun x => by
      show f x = -11 * (cos (1 / 5 * x + 0) / sin (1 / 5 * x + 0)) + 0
      rw [hf]; ring_nf)
  rw [show π / (1 / 5) = 5 * π by ring] at this
  exact this

/-- Stitz-Zeager Exercise 10.5.24: `y = (1/3) cot(2x + 3π/2) + 1` has period `π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.5.24, p. 821"]
theorem exer_10_5_24 (f : ℝ → ℝ)
    (hf : ∀ x, f x = 1 / 3 * (cos (2 * x + 3 * π / 2) / sin (2 * x + 3 * π / 2)) + 1) :
    Function.Periodic f (π / 2) ∧ ∀ p, 0 < p → Function.Periodic f p → π / 2 ≤ p := by
  exact period_transform (fun y => cos y / sin y) π (1 / 3) 2 (3 * π / 2) 1 (by norm_num)
    (by norm_num) cot_base.1 cot_base.2 f (fun x => by
      show f x = 1 / 3 * (cos (2 * x + 3 * π / 2) / sin (2 * x + 3 * π / 2)) + 1
      rw [hf])

end UndergradKB.Precalculus.Course
