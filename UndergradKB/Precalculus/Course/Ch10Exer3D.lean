import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 10.2, 10.3 and 10.4
(exercises whose answer the book leaves to the reader, computed here) -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Stitz-Zeager Exercise 10.2.75: with the time delay `t₀`, the motion `x = r cos(ω(t - t₀))`,
`y = r sin(ω(t - t₀))` stays on the circle of radius `r` and is at `(r, 0)` at time `t = t₀`. -/
@[kb "stitzzeager2013" "Exercise 10.2.75, p. 751"]
theorem exer_10_2_75 (r ω t₀ : ℝ) :
    (r * cos (ω * (t₀ - t₀)) = r ∧ r * sin (ω * (t₀ - t₀)) = 0) ∧
    ∀ t : ℝ, (r * cos (ω * (t - t₀))) ^ 2 + (r * sin (ω * (t - t₀))) ^ 2 = r ^ 2 := by
  refine ⟨by simp, fun t => ?_⟩
  have h := Real.sin_sq_add_cos_sq (ω * (t - t₀))
  linear_combination r ^ 2 * h

/-- Stitz-Zeager Exercise 10.3.79: from `30` ft away, the top of the tree is seen at elevation `50°` and
its base at depression `10°`; the height of the tree is `30 (tan 50° + tan 10°)` feet. -/
@[kb "stitzzeager2013" "Exercise 10.3.79, p. 774"]
theorem exer_10_3_79 (h₁ h₂ : ℝ) (e₁ : tan (50 * π / 180) = h₁ / 30)
    (e₂ : tan (10 * π / 180) = h₂ / 30) :
    h₁ + h₂ = 30 * (tan (50 * π / 180) + tan (10 * π / 180)) := by
  rw [e₁, e₂]; ring

/-- Stitz-Zeager Exercise 10.3.80: from `50` ft above the lake the angles of depression `8.2°` and `25.9°`
put the boat at horizontal distances `d₁`, `d₂`; the boat travelled `d₁ - d₂ = 50 (cot 8.2° - cot 25.9°)`. -/
@[kb "stitzzeager2013" "Exercise 10.3.80, p. 774"]
theorem exer_10_3_80 (d₁ d₂ : ℝ) (e₁ : tan (8.2 * π / 180) = 50 / d₁)
    (e₂ : tan (25.9 * π / 180) = 50 / d₂) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    d₁ - d₂ = 50 / tan (8.2 * π / 180) - 50 / tan (25.9 * π / 180) := by
  rw [e₁, e₂]
  field_simp

/-- Stitz-Zeager Exercise 10.3.81: a taut wire of length `1000` ft making a `43°` angle with the ground:
the tower is `1000 sin 43°` tall and the wire meets the ground `1000 cos 43°` from its base. -/
@[kb "stitzzeager2013" "Exercise 10.3.81, p. 774"]
theorem exer_10_3_81 (h d : ℝ) (e₁ : sin (43 * π / 180) = h / 1000)
    (e₂ : cos (43 * π / 180) = d / 1000) :
    h = 1000 * sin (43 * π / 180) ∧ d = 1000 * cos (43 * π / 180) := by
  rw [e₁, e₂]; constructor <;> ring

/-- Stitz-Zeager Exercise 10.3.133: the ranges of tangent, cosecant and cotangent: `tan` and `cot`
take every real value, `csc` takes exactly the values `y` with `|y| ≥ 1`. -/
@[kb "stitzzeager2013" "Exercise 10.3.133, p. 776"]
theorem exer_10_3_133 :
    (∀ y : ℝ, ∃ x : ℝ, cos x ≠ 0 ∧ sin x / cos x = y) ∧
    (∀ y : ℝ, 1 ≤ |y| → ∃ x : ℝ, sin x ≠ 0 ∧ 1 / sin x = y) ∧
    (∀ x : ℝ, sin x ≠ 0 → 1 ≤ |1 / sin x|) ∧
    (∀ y : ℝ, ∃ x : ℝ, sin x ≠ 0 ∧ cos x / sin x = y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    refine ⟨arctan y, (Real.cos_arctan_pos y).ne', ?_⟩
    rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
  · intro y hy
    have hy0 : y ≠ 0 := by
      intro h; rw [h, abs_zero] at hy; norm_num at hy
    have hinv : |1 / y| ≤ 1 := by
      rw [one_div, abs_inv]
      exact inv_le_one_of_one_le₀ hy
    have h1 := abs_le.mp hinv
    refine ⟨arcsin (1 / y), ?_, ?_⟩
    · rw [Real.sin_arcsin h1.1 h1.2]
      exact one_div_ne_zero hy0
    · rw [Real.sin_arcsin h1.1 h1.2]
      field_simp
  · intro x hx
    have h1 := Real.abs_sin_le_one x
    have h2 : 0 < |sin x| := abs_pos.mpr hx
    rw [abs_div, abs_one, le_div_iff₀ h2]
    linarith
  · intro y
    have hc := Real.cos_arctan_pos y
    refine ⟨π / 2 - arctan y, ?_, ?_⟩
    · rw [Real.sin_pi_div_two_sub]; exact hc.ne'
    · rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, ← Real.tan_eq_sin_div_cos,
        Real.tan_arctan]

/-- Stitz-Zeager Exercise 10.4.96: `cos 5θ` and `cos 6θ` are polynomials in `cos θ`:
`cos 5θ = 16c⁵ - 20c³ + 5c`, `cos 6θ = 32c⁶ - 48c⁴ + 18c² - 1` with `c = cos θ`. -/
@[kb "stitzzeager2013" "Exercise 10.4.96, p. 798"]
theorem exer_10_4_96 (θ : ℝ) :
    cos (5 * θ) = 16 * cos θ ^ 5 - 20 * cos θ ^ 3 + 5 * cos θ ∧
    cos (6 * θ) = 32 * cos θ ^ 6 - 48 * cos θ ^ 4 + 18 * cos θ ^ 2 - 1 := by
  have h4 : cos (4 * θ) = 8 * cos θ ^ 4 - 8 * cos θ ^ 2 + 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul, Real.cos_two_mul]
    ring
  have h3 : cos (3 * θ) = 4 * cos θ ^ 3 - 3 * cos θ := Real.cos_three_mul θ
  have h5 : cos (5 * θ) = 2 * cos (4 * θ) * cos θ - cos (3 * θ) := by
    have a := Real.cos_add (4 * θ) θ
    have b := Real.cos_sub (4 * θ) θ
    rw [show 4 * θ + θ = 5 * θ by ring] at a
    rw [show 4 * θ - θ = 3 * θ by ring] at b
    linarith
  have h5' : cos (5 * θ) = 16 * cos θ ^ 5 - 20 * cos θ ^ 3 + 5 * cos θ := by
    rw [h5, h4, h3]; ring
  refine ⟨h5', ?_⟩
  have h6 : cos (6 * θ) = 2 * cos (5 * θ) * cos θ - cos (4 * θ) := by
    have a := Real.cos_add (5 * θ) θ
    have b := Real.cos_sub (5 * θ) θ
    rw [show 5 * θ + θ = 6 * θ by ring] at a
    rw [show 5 * θ - θ = 4 * θ by ring] at b
    linarith
  rw [h6, h5', h4]; ring

/-- Stitz-Zeager Exercise 10.4.97: `sin 5θ = 16 s⁵ - 20 s³ + 5 s` with `s = sin θ`, but `sin 4θ` is not a
polynomial in `sin θ` (the angles `π/6` and `5π/6` have the same sine and opposite values of `sin 4θ`). -/
@[kb "stitzzeager2013" "Exercise 10.4.97, p. 798"]
theorem exer_10_4_97 :
    (∀ θ : ℝ, sin (5 * θ) = 16 * sin θ ^ 5 - 20 * sin θ ^ 3 + 5 * sin θ) ∧
    ¬ ∃ p : Polynomial ℝ, ∀ θ : ℝ, sin (4 * θ) = p.eval (sin θ) := by
  constructor
  · intro θ
    have hc2 : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    have h4 : sin (4 * θ) = 2 * (2 * sin θ * cos θ) * (2 * cos θ ^ 2 - 1) := by
      rw [show 4 * θ = 2 * (2 * θ) by ring, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul]
    have h5 : sin (5 * θ) = 2 * sin (4 * θ) * cos θ - sin (3 * θ) := by
      have a := Real.sin_add (4 * θ) θ
      have b := Real.sin_sub (4 * θ) θ
      rw [show 4 * θ + θ = 5 * θ by ring] at a
      rw [show 4 * θ - θ = 3 * θ by ring] at b
      linarith
    rw [h5, h4, Real.sin_three_mul]
    linear_combination (8 * sin θ * (2 * (cos θ ^ 2 + (1 - sin θ ^ 2)) - 1)) * hc2
  · rintro ⟨p, hp⟩
    have h1 := hp (π / 6)
    have h2 := hp (5 * π / 6)
    have s1 : sin (5 * π / 6) = sin (π / 6) := by
      rw [show 5 * π / 6 = π - π / 6 by ring, Real.sin_pi_sub]
    rw [← s1] at h1
    have a1 : sin (4 * (π / 6)) = √3 / 2 := by
      rw [show 4 * (π / 6) = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
    have a2 : sin (4 * (5 * π / 6)) = -(√3 / 2) := by
      rw [show 4 * (5 * π / 6) = π / 3 + π + 2 * π by ring, Real.sin_add_two_pi, Real.sin_add_pi,
        Real.sin_pi_div_three]
    rw [a1] at h1
    rw [a2] at h2
    have hp3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
    linarith

end UndergradKB.Precalculus.Course
