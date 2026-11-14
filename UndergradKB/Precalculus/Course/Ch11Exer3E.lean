import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers (wave 8), Section 11.7 (cube roots) -/

namespace UndergradKB.Precalculus.Course

open Real

/-- If `c³ = 2` and `cos 3θ = sin 3θ = √2/2`, then `c (cos θ + i sin θ)` is a cube root of `√2 + i √2`. -/
theorem ch11e3e_cube (c θ : ℝ) (hc : c ^ 3 = 2) (h1 : cos (3 * θ) = √2 / 2)
    (h2 : sin (3 * θ) = √2 / 2) :
    ((c : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)) ^ 3 =
      (√2 : ℂ) + (√2 : ℂ) * Complex.I := by
  rw [mul_pow, Complex.cos_add_sin_mul_I_pow]
  have e : ((3 : ℕ) : ℂ) * (θ : ℂ) = ((3 * θ : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← Complex.ofReal_cos, ← Complex.ofReal_sin, h1, h2]
  have hc' : (c : ℂ) ^ 3 = 2 := by exact_mod_cast hc
  rw [hc']
  push_cast
  ring

/-- Stitz-Zeager Exercise 11.7.77: the three cube roots of `√2 + i √2` are `c · cis θ` with `c = ∛2` and
`θ = π/12, 3π/4, 17π/12`; their rectangular forms use `cos(π/12) = (√6+√2)/4`,
`sin(π/12) = (√6-√2)/4`, `cos(3π/4) = -√2/2`, `sin(3π/4) = √2/2`, `cos(17π/12) = (√2-√6)/4`,
`sin(17π/12) = -(√2+√6)/4`. -/
@[kb "stitzzeager2013" "Exercise 11.7.77, p. 1017"]
theorem exer_11_7_77 (c : ℝ) (hc : c ^ 3 = 2) :
    (cos (π / 12) = (√6 + √2) / 4 ∧ sin (π / 12) = (√6 - √2) / 4) ∧
    (cos (3 * π / 4) = -(√2 / 2) ∧ sin (3 * π / 4) = √2 / 2) ∧
    (cos (17 * π / 12) = (√2 - √6) / 4 ∧ sin (17 * π / 12) = -((√2 + √6) / 4)) ∧
    (∀ θ : ℝ, (θ = π / 12 ∨ θ = 3 * π / 4 ∨ θ = 17 * π / 12) →
      ((c : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)) ^ 3 =
        (√2 : ℂ) + (√2 : ℂ) * Complex.I) := by
  have h6 : √6 = √3 * √2 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have k1 : cos (π / 12) = (√6 + √2) / 4 := by
    rw [show π / 12 = π / 3 - π / 4 by ring, Real.cos_sub, Real.cos_pi_div_three,
      Real.sin_pi_div_three, Real.cos_pi_div_four, Real.sin_pi_div_four, h6]
    ring
  have k2 : sin (π / 12) = (√6 - √2) / 4 := by
    rw [show π / 12 = π / 3 - π / 4 by ring, Real.sin_sub, Real.cos_pi_div_three,
      Real.sin_pi_div_three, Real.cos_pi_div_four, Real.sin_pi_div_four, h6]
    ring
  have k3 : cos (3 * π / 4) = -(√2 / 2) := by
    rw [show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
  have k4 : sin (3 * π / 4) = √2 / 2 := by
    rw [show 3 * π / 4 = π - π / 4 by ring, Real.sin_pi_sub, Real.sin_pi_div_four]
  have k5 : cos (17 * π / 12) = (√2 - √6) / 4 := by
    rw [show 17 * π / 12 = (π / 4 + π / 6) + π by ring, Real.cos_add_pi, Real.cos_add,
      Real.cos_pi_div_six, Real.sin_pi_div_six, Real.cos_pi_div_four, Real.sin_pi_div_four, h6]
    ring
  have k6 : sin (17 * π / 12) = -((√2 + √6) / 4) := by
    rw [show 17 * π / 12 = (π / 4 + π / 6) + π by ring, Real.sin_add_pi, Real.sin_add,
      Real.cos_pi_div_six, Real.sin_pi_div_six, Real.cos_pi_div_four, Real.sin_pi_div_four, h6]
    ring
  refine ⟨⟨k1, k2⟩, ⟨k3, k4⟩, ⟨k5, k6⟩, ?_⟩
  intro θ hθ
  have s4 : cos (π / 4) = √2 / 2 := Real.cos_pi_div_four
  have s4' : sin (π / 4) = √2 / 2 := Real.sin_pi_div_four
  rcases hθ with rfl | rfl | rfl
  · refine ch11e3e_cube c _ hc ?_ ?_
    · rw [show 3 * (π / 12) = π / 4 by ring]; exact s4
    · rw [show 3 * (π / 12) = π / 4 by ring]; exact s4'
  · refine ch11e3e_cube c _ hc ?_ ?_
    · rw [show 3 * (3 * π / 4) = π / 4 + 2 * π by ring, Real.cos_add_two_pi]; exact s4
    · rw [show 3 * (3 * π / 4) = π / 4 + 2 * π by ring, Real.sin_add_two_pi]; exact s4'
  · refine ch11e3e_cube c _ hc ?_ ?_
    · rw [show 3 * (17 * π / 12) = π / 4 + 2 * π + 2 * π by ring, Real.cos_add_two_pi,
        Real.cos_add_two_pi]; exact s4
    · rw [show 3 * (17 * π / 12) = π / 4 + 2 * π + 2 * π by ring, Real.sin_add_two_pi,
        Real.sin_add_two_pi]; exact s4'

end UndergradKB.Precalculus.Course
