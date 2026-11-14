import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 11 (Stitz-Zeager): worked examples

Worked examples of Chapter 11 (applications of trigonometry): sinusoid models, solving triangles,
polar coordinates, rotation of axes, complex numbers in polar form, vectors and parametric
equations.
-/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ### Section 11.1 -/

/-- Stitz-Zeager Example 11.1.1: the height of a rider on the 136-foot wheel (radius `64`, base `8`,
two turns in `127` seconds) is `64 sin (4π t / 127 - π/2) + 72`; it starts at `8` and is `136` after
a half period. -/
@[kb "stitzzeager2013" "Example 11.1.1, p. 894"]
theorem ex_11_1_1 :
    let h : ℝ → ℝ := fun t => 64 * sin (4 * π / 127 * t - π / 2) + 72
    h 0 = 8 ∧ h (127 / 4) = 136 ∧ Function.Periodic h (127 / 2) := by
  intro h
  refine ⟨?_, ?_, ?_⟩
  · simp [h]
    norm_num
  · simp only [h]
    have : 4 * π / 127 * (127 / 4) - π / 2 = π / 2 := by field_simp; ring
    rw [this, sin_pi_div_two]; norm_num
  · intro t
    simp only [h]
    have : 4 * π / 127 * (t + 127 / 2) - π / 2 = (4 * π / 127 * t - π / 2) + 2 * π := by
      field_simp; ring
    rw [this, sin_add_two_pi]

/-- Stitz-Zeager Example 11.1.3(1): the spring `x(t) = 3 sin (2t + π/2)` is at equilibrium at
`t = π/4`, and no earlier positive time has `x = 0`. -/
@[kb "stitzzeager2013" "Example 11.1.3, p. 899"]
theorem ex_11_1_3_a :
    3 * sin (2 * (π / 4) + π / 2) = 0 ∧
      ∀ t : ℝ, 0 < t → 3 * sin (2 * t + π / 2) = 0 → π / 4 ≤ t := by
  have hp := pi_pos
  refine ⟨?_, ?_⟩
  · rw [show 2 * (π / 4) + π / 2 = π by ring, sin_pi]; norm_num
  · intro t ht h
    rw [sin_add_pi_div_two] at h
    have h' : cos (2 * t) = 0 := by linarith
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 h'
    by_contra hlt
    push Not at hlt
    have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith
    have b : (k : ℝ) < 0 := by
      by_contra hh; push Not at hh; nlinarith
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 0 := by exact_mod_cast b
    omega

/-- Stitz-Zeager Example 11.1.3(2): with `φ = π - arcsin (3/5)`, the motion `5 sin (2t + φ)` starts
at `3` with `10 cos φ = -8` (initial upward speed `8`), never goes above `5` feet on the upper side
(its minimum is `-5`) and attains `-5` at `t = (1/2) arcsin (3/5) + π/4`. -/
@[kb "stitzzeager2013" "Example 11.1.3, p. 899"]
theorem ex_11_1_3_b :
    let φ : ℝ := π - arcsin (3 / 5)
    let x : ℝ → ℝ := fun t => 5 * sin (2 * t + φ)
    x 0 = 3 ∧ 10 * cos φ = -8 ∧ (∀ t, -5 ≤ x t) ∧ x (arcsin (3 / 5) / 2 + π / 4) = -5 := by
  intro φ x
  have hs : sin (arcsin (3 / 5 : ℝ)) = 3 / 5 := sin_arcsin (by norm_num) (by norm_num)
  have hc : cos (arcsin (3 / 5 : ℝ)) = 4 / 5 := by
    rw [cos_arcsin]
    rw [show (1 - (3 / 5 : ℝ) ^ 2) = (4 / 5) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [x, φ]; rw [mul_zero, zero_add, sin_pi_sub, hs]; norm_num
  · simp only [φ]; rw [cos_pi_sub, hc]; norm_num
  · intro t; simp only [x]; nlinarith [neg_one_le_sin (2 * t + φ)]
  · simp only [x, φ]
    have : 2 * (arcsin (3 / 5) / 2 + π / 4) + (π - arcsin (3 / 5)) = 3 * π / 2 := by ring
    rw [this, show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]
    norm_num

/-- Stitz-Zeager Example 11.1.4(1): `5e^{-t/5} cos t + 5√3 e^{-t/5} sin t = 10 e^{-t/5} sin (t + π/6)`. -/
@[kb "stitzzeager2013" "Example 11.1.4, p. 901"]
theorem ex_11_1_4_a (t : ℝ) :
    5 * exp (-t / 5) * cos t + 5 * exp (-t / 5) * √3 * sin t =
      10 * exp (-t / 5) * sin (t + π / 6) := by
  rw [sin_add, cos_pi_div_six, sin_pi_div_six]
  ring

/-- Stitz-Zeager Example 11.1.4(2): `√2 (t+3) cos 2t + √2 (t+3) sin 2t = 2 (t+3) sin (2t + π/4)`. -/
@[kb "stitzzeager2013" "Example 11.1.4, p. 901"]
theorem ex_11_1_4_b (t : ℝ) :
    (t + 3) * √2 * cos (2 * t) + (t + 3) * √2 * sin (2 * t) =
      2 * (t + 3) * sin (2 * t + π / 4) := by
  rw [sin_add, cos_pi_div_four, sin_pi_div_four]
  ring

/-- Stitz-Zeager Example 11.1.4(3): `5 sin 6t - 5 sin 8t` has period `π`, and equals
`-10 sin t cos 7t`. -/
@[kb "stitzzeager2013" "Example 11.1.4, p. 901"]
theorem ex_11_1_4_c :
    Function.Periodic (fun t : ℝ => 5 * sin (6 * t) - 5 * sin (8 * t)) π ∧
      ∀ t : ℝ, 5 * sin (6 * t) - 5 * sin (8 * t) = -10 * sin t * cos (7 * t) := by
  constructor
  · intro t
    have h1 : 6 * (t + π) = 6 * t + 2 * π + 2 * π + 2 * π := by ring
    have h2 : 8 * (t + π) = 8 * t + 2 * π + 2 * π + 2 * π + 2 * π := by ring
    simp only [h1, h2, sin_add_two_pi]
  · intro t
    have h1 : 6 * t = 7 * t - t := by ring
    have h2 : 8 * t = 7 * t + t := by ring
    rw [h1, h2, sin_sub, sin_add]
    ring

/-! ### Sections 11.2 and 11.3 -/

/-- Stitz-Zeager Example 11.2.1: a right triangle with hypotenuse `7` and a leg `4` has the other leg
`√33`. -/
@[kb "stitzzeager2013" "Example 11.2.1, p. 908"]
theorem ex_11_2_1 {b : ℝ} (hb : 0 < b) (h : 4 ^ 2 + b ^ 2 = (7 : ℝ) ^ 2) : b = √33 := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by norm_num) hb.le]
  nlinarith

/-- Stitz-Zeager Example 11.2.2(1): with `α = 120°`, `a = 7`, `β = 45°`, the Law of Sines gives
`b = 7√6/3` and the third angle is `15°`. -/
@[kb "stitzzeager2013" "Example 11.2.2, p. 910"]
theorem ex_11_2_2_a {b : ℝ} (h : b / sin (π / 4) = 7 / sin (2 * π / 3)) : b = 7 * √6 / 3 := by
  have e : 2 * π / 3 = π - π / 3 := by ring
  rw [e, sin_pi_sub, sin_pi_div_three, sin_pi_div_four] at h
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : √6 = √2 * √3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2p : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  have h3p : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  rw [h6]
  field_simp at h
  nlinarith

/-- Stitz-Zeager Example 11.2.2(3): with `α = 30°`, `a = 1`, `c = 4` there is no triangle, since the
Law of Sines would need `sin γ = 2`. -/
@[kb "stitzzeager2013" "Example 11.2.2, p. 910"]
theorem ex_11_2_2_c : ¬ ∃ γ : ℝ, sin γ / 4 = sin (π / 6) / 1 := by
  rintro ⟨γ, h⟩
  rw [sin_pi_div_six] at h
  have := sin_le_one γ
  linarith

/-- Stitz-Zeager Example 11.2.2(4): with `α = 30°`, `a = 2`, `c = 4` there is exactly one triangle,
the right triangle with `γ = 90°`. -/
@[kb "stitzzeager2013" "Example 11.2.2, p. 910"]
theorem ex_11_2_2_d {γ : ℝ} (hγ : γ ∈ Ioo 0 (5 * π / 6)) :
    sin γ / 4 = sin (π / 6) / 2 ↔ γ = π / 2 := by
  have hp := pi_pos
  rw [sin_pi_div_six]
  constructor
  · intro h
    have h1 : sin γ = 1 := by linarith
    obtain ⟨k, hk⟩ := sin_eq_one_iff.1 h1
    have a : (-1 : ℝ) < k := by
      by_contra hh; push Not at hh; nlinarith [hγ.1]
    have b : (k : ℝ) < 1 := by
      by_contra hh; push Not at hh; nlinarith [hγ.2]
    have a' : (-1 : ℤ) < k := by exact_mod_cast a
    have b' : k < 1 := by exact_mod_cast b
    obtain rfl : k = 0 := by omega
    simp at hk
    linarith
  · rintro rfl
    rw [sin_pi_div_two]; norm_num

/-- Stitz-Zeager Example 11.2.2(6): with `α = 30°`, `a = 4`, `c = 4` the only possible `γ` is `30°`
(the other candidate `150°` leaves no room for the angle `α`). -/
@[kb "stitzzeager2013" "Example 11.2.2, p. 910"]
theorem ex_11_2_2_f {γ : ℝ} (hγ : γ ∈ Ioo 0 (5 * π / 6)) :
    sin γ / 4 = sin (π / 6) / 4 ↔ γ = π / 6 := by
  have hp := pi_pos
  rw [sin_pi_div_six]
  constructor
  · intro h
    have h1 : sin γ = sin (π / 6) := by rw [sin_pi_div_six]; linarith
    obtain ⟨k, hk | hk⟩ := sin_eq_sin_iff.1 h1
    · have a : (-1 : ℝ) < k := by
        by_contra hh; push Not at hh; nlinarith [hγ.2]
      have b : (k : ℝ) < 1 := by
        by_contra hh; push Not at hh; nlinarith [hγ.1]
      have a' : (-1 : ℤ) < k := by exact_mod_cast a
      have b' : k < 1 := by exact_mod_cast b
      obtain rfl : k = 0 := by omega
      simp at hk
      linarith
    · exfalso
      rcases le_or_gt 0 k with hk0 | hk0
      · have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
        nlinarith [hγ.2]
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
        nlinarith [hγ.1]
  · rintro rfl
    rw [sin_pi_div_six]

/-- Stitz-Zeager Example 11.2.3: from observation points `5` miles apart with base angles `30°`
and `45°`, the island is `5(√6 + √2)/2` miles from the second point and `5(√3 + 1)/2` miles
from the nearest shore point. -/
@[kb "stitzzeager2013" "Example 11.2.3, p. 914"]
theorem ex_11_2_3 {d : ℝ} (h : d / sin (π / 6) = 5 / sin (π / 12)) :
    d = 5 * (√6 + √2) / 2 ∧ d * sin (π / 4) = 5 * (√3 + 1) / 2 := by
  have h12 : sin (π / 12) = (√6 - √2) / 4 := by
    have : π / 12 = π / 4 - π / 6 := by ring
    rw [this, sin_sub, sin_pi_div_four, cos_pi_div_six, cos_pi_div_four, sin_pi_div_six]
    have h6 : √6 = √2 * √3 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    rw [h6]; ring
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : √6 = √2 * √3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h2p : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  have h3p : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hpos : 0 < √6 - √2 := by
    rw [h6]; nlinarith
  rw [h12, sin_pi_div_six] at h
  have hd : d = 5 * (√6 + √2) / 2 := by
    field_simp at h
    rw [h6] at hpos ⊢
    nlinarith
  refine ⟨hd, ?_⟩
  rw [hd, sin_pi_div_four, h6]
  nlinarith

/-- Stitz-Zeager Example 11.3.1(2): a triangle with sides `a = 4`, `b = 7`, `c = 5` has angle cosines
`29/35`, `-1/5`, `5/7` at `α`, `β`, `γ`. -/
@[kb "stitzzeager2013" "Example 11.3.1, p. 923"]
theorem ex_11_3_1_b {ca cb cc : ℝ}
    (hα : (4 : ℝ) ^ 2 = 7 ^ 2 + 5 ^ 2 - 2 * 7 * 5 * ca)
    (hβ : (7 : ℝ) ^ 2 = 4 ^ 2 + 5 ^ 2 - 2 * 4 * 5 * cb)
    (hγ : (5 : ℝ) ^ 2 = 4 ^ 2 + 7 ^ 2 - 2 * 4 * 7 * cc) :
    ca = 29 / 35 ∧ cb = -(1 / 5) ∧ cc = 5 / 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- Stitz-Zeager Example 11.3.2: the pond's width `w`, with sight lines `950` and `1000` feet at
`60°`, is `50√381` feet. -/
@[kb "stitzzeager2013" "Example 11.3.2, p. 925"]
theorem ex_11_3_2 {w : ℝ} (hw : 0 < w)
    (h : w ^ 2 = 950 ^ 2 + 1000 ^ 2 - 2 * 950 * 1000 * cos (π / 3)) : w = 50 * √381 := by
  rw [cos_pi_div_three] at h
  have h381 : (√381) ^ 2 = 381 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √381 := Real.sqrt_pos.2 (by norm_num)
  have : (w - 50 * √381) * (w + 50 * √381) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · nlinarith

/-! ### Section 11.4 -/

/-- Stitz-Zeager Example 11.4.2(1): the point `(2, -2√3)` has polar form `(4, 5π/3)`. -/
@[kb "stitzzeager2013" "Example 11.4.2, p. 936"]
theorem ex_11_4_2_a :
    4 * cos (5 * π / 3) = 2 ∧ 4 * sin (5 * π / 3) = -(2 * √3) := by
  have h : 5 * π / 3 = -(π / 3) + 2 * π := by ring
  rw [h, cos_add_two_pi, sin_add_two_pi, cos_neg, sin_neg, cos_pi_div_three, sin_pi_div_three]
  constructor <;> ring

/-- Stitz-Zeager Example 11.4.2(2): the point `(-3, -3)` has polar form `(3√2, 5π/4)`. -/
@[kb "stitzzeager2013" "Example 11.4.2, p. 936"]
theorem ex_11_4_2_b :
    3 * √2 * cos (5 * π / 4) = -3 ∧ 3 * √2 * sin (5 * π / 4) = -3 := by
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : 5 * π / 4 = π / 4 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_four, sin_pi_div_four]
  constructor <;> nlinarith

/-- Stitz-Zeager Example 11.4.2(3): the point `(0, -3)` has polar form `(3, 3π/2)`. -/
@[kb "stitzzeager2013" "Example 11.4.2, p. 936"]
theorem ex_11_4_2_c : 3 * cos (3 * π / 2) = 0 ∧ 3 * sin (3 * π / 2) = -3 := by
  have h : 3 * π / 2 = π / 2 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_two, sin_pi_div_two]
  constructor <;> norm_num

/-- Stitz-Zeager Example 11.4.2(4): the point `(-3, 4)` has polar form `(5, π - arctan (4/3))`. -/
@[kb "stitzzeager2013" "Example 11.4.2, p. 936"]
theorem ex_11_4_2_d :
    5 * cos (π - arctan (4 / 3)) = -3 ∧ 5 * sin (π - arctan (4 / 3)) = 4 := by
  have h : √(1 + (4 / 3 : ℝ) ^ 2) = 5 / 3 := by
    rw [show 1 + (4 / 3 : ℝ) ^ 2 = (5 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [cos_pi_sub, sin_pi_sub, cos_arctan, sin_arctan, h]
  constructor <;> norm_num

/-- Stitz-Zeager Example 11.4.3(1a): in polar form the circle `(x-3)² + y² = 9` is `r = 0` or
`r = 6 cos θ`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_a (r θ : ℝ) :
    (r * cos θ - 3) ^ 2 + (r * sin θ) ^ 2 = 9 ↔ r = 0 ∨ r = 6 * cos θ := by
  have h := sin_sq_add_cos_sq θ
  have e : (r * cos θ - 3) ^ 2 + (r * sin θ) ^ 2 - 9 = r * (r - 6 * cos θ) := by
    linear_combination r ^ 2 * h
  constructor
  · intro h1
    have : r * (r - 6 * cos θ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h2 | h2
    · left; exact h2
    · right; linarith
  · rintro (h1 | h1)
    · rw [h1]; norm_num
    · have h3 : r * (r - 6 * cos θ) = 0 := by
        rw [show r - 6 * cos θ = 0 by linarith]; ring
      linarith

/-- Stitz-Zeager Example 11.4.3(1c): in polar form the parabola `y = x²` is `r = 0` or
`r cos²θ = sin θ`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_c (r θ : ℝ) :
    r * sin θ = (r * cos θ) ^ 2 ↔ r = 0 ∨ r * cos θ ^ 2 = sin θ := by
  constructor
  · intro h
    have : r * (r * cos θ ^ 2 - sin θ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h2 | h2
    · left; exact h2
    · right; linarith
  · rintro (h1 | h1)
    · rw [h1]; norm_num
    · calc r * sin θ = r * (r * cos θ ^ 2) := by rw [h1]
        _ = (r * cos θ) ^ 2 := by ring

/-! ### Section 11.6 -/

/-- Stitz-Zeager Example 11.6.1(1): rotating the axes by `π/3` sends `(2, -4)` to
`(1 - 2√3, -2 - √3)`. -/
@[kb "stitzzeager2013" "Example 11.6.1, p. 987"]
theorem ex_11_6_1_a :
    2 * cos (π / 3) + (-4) * sin (π / 3) = 1 - 2 * √3 ∧
      -2 * sin (π / 3) + (-4) * cos (π / 3) = -2 - √3 := by
  rw [cos_pi_div_three, sin_pi_div_three]
  constructor <;> ring

/-- Stitz-Zeager Example 11.6.1(2): after the rotation by `π/3`, the left side of
`21x² + 10√3 xy + 31y² = 144` becomes `36 x'² + 16 y'²`. -/
@[kb "stitzzeager2013" "Example 11.6.1, p. 987"]
theorem ex_11_6_1_b (x' y' : ℝ) :
    let x := x' * cos (π / 3) - y' * sin (π / 3)
    let y := x' * sin (π / 3) + y' * cos (π / 3)
    21 * x ^ 2 + 10 * √3 * x * y + 31 * y ^ 2 = 36 * x' ^ 2 + 16 * y' ^ 2 := by
  intro x y
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [x, y]
  rw [cos_pi_div_three, sin_pi_div_three]
  linear_combination (41 / 4 * x' ^ 2 + 11 / 4 * y' ^ 2 - 5 / 2 * x' * y' * √3) * h3

/-- Stitz-Zeager Example 11.6.3: the discriminants `B² - 4AC` of the three conics are negative
(ellipse), positive (hyperbola) and zero (parabola). -/
@[kb "stitzzeager2013" "Example 11.6.3, p. 992"]
theorem ex_11_6_3 :
    (10 * √3) ^ 2 - 4 * 21 * 31 < 0 ∧ (26 : ℝ) ^ 2 - 4 * 5 * 5 > 0 ∧
      (24 : ℝ) ^ 2 - 4 * 16 * 9 = 0 := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, by norm_num, by norm_num⟩
  nlinarith

/-! ### Section 11.7 -/

private theorem arg_polar {x y r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioc (-π) π)
    (hx : x = r * cos θ) (hy : y = r * sin θ) :
    Complex.arg ⟨x, y⟩ = θ ∧ ‖(⟨x, y⟩ : ℂ)‖ = r := by
  have h : (⟨x, y⟩ : ℂ) = (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext <;> simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, hx, hy]
  refine ⟨by rw [h]; exact Complex.arg_mul_cos_add_sin_mul_I hr hθ, ?_⟩
  rw [Complex.norm_def, Complex.normSq_mk, hx, hy]
  rw [show r * cos θ * (r * cos θ) + r * sin θ * (r * sin θ) = r ^ 2 by
    nlinarith [sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq hr.le

/-- Stitz-Zeager Example 11.7.1(1): `z = √3 - i` has `|z| = 2` and principal argument `-π/6`. -/
@[kb "stitzzeager2013" "Example 11.7.1, p. 1004"]
theorem ex_11_7_1_a : ‖(⟨√3, -1⟩ : ℂ)‖ = 2 ∧ Complex.arg ⟨√3, -1⟩ = -(π / 6) := by
  have hp := pi_pos
  have := arg_polar (x := √3) (y := -1) (r := 2) (θ := -(π / 6)) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_neg, cos_pi_div_six]; ring)
    (by rw [sin_neg, sin_pi_div_six]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Example 11.7.1(2): `z = -2 + 4i` has `|z| = 2√5` and principal argument
`π - arctan 2`. -/
@[kb "stitzzeager2013" "Example 11.7.1, p. 1004"]
theorem ex_11_7_1_b :
    ‖(⟨-2, 4⟩ : ℂ)‖ = 2 * √5 ∧ Complex.arg ⟨-2, 4⟩ = π - arctan 2 := by
  have hp := pi_pos
  have h5 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5p : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
  have hs : √(1 + (2 : ℝ) ^ 2) = √5 := by norm_num
  have ha := arctan_lt_pi_div_two 2
  have hb : 0 < arctan 2 := arctan_pos.2 (by norm_num)
  have := arg_polar (x := -2) (y := 4) (r := 2 * √5) (θ := π - arctan 2) (by positivity)
    ⟨by linarith, by linarith⟩
    (by
      rw [cos_pi_sub, cos_arctan, hs]
      field_simp)
    (by
      rw [sin_pi_sub, sin_arctan, hs]
      field_simp
      nlinarith)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Example 11.7.1(3): `z = 3i` has `|z| = 3` and principal argument `π/2`. -/
@[kb "stitzzeager2013" "Example 11.7.1, p. 1004"]
theorem ex_11_7_1_c : ‖(⟨0, 3⟩ : ℂ)‖ = 3 ∧ Complex.arg ⟨0, 3⟩ = π / 2 := by
  have hp := pi_pos
  have := arg_polar (x := 0) (y := 3) (r := 3) (θ := π / 2) (by norm_num)
    ⟨by linarith, by linarith⟩ (by rw [cos_pi_div_two]; ring) (by rw [sin_pi_div_two]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Example 11.7.1(4): `z = -117` has `|z| = 117` and principal argument `π`. -/
@[kb "stitzzeager2013" "Example 11.7.1, p. 1004"]
theorem ex_11_7_1_d : ‖(⟨-117, 0⟩ : ℂ)‖ = 117 ∧ Complex.arg ⟨-117, 0⟩ = π := by
  have hp := pi_pos
  have := arg_polar (x := -117) (y := 0) (r := 117) (θ := π) (by norm_num)
    ⟨by linarith, le_refl _⟩ (by rw [cos_pi]; ring) (by rw [sin_pi]; ring)
  exact ⟨this.2, this.1⟩

/-- Stitz-Zeager Example 11.7.2(1a): `4 cis (2π/3) = -2 + 2√3 i`. -/
@[kb "stitzzeager2013" "Example 11.7.2, p. 1008"]
theorem ex_11_7_2_a :
    (((4 : ℝ) : ℂ) * Complex.exp (↑(2 * π / 3) * Complex.I)).re = -2 ∧
      (((4 : ℝ) : ℂ) * Complex.exp (↑(2 * π / 3) * Complex.I)).im = 2 * √3 := by
  have h : 2 * π / 3 = π - π / 3 := by ring
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, h, cos_pi_sub, sin_pi_sub, cos_pi_div_three, sin_pi_div_three]
  constructor <;> ring

/-- Stitz-Zeager Example 11.7.2(1b): `2 cis (-3π/4) = -√2 - √2 i`. -/
@[kb "stitzzeager2013" "Example 11.7.2, p. 1008"]
theorem ex_11_7_2_b :
    (((2 : ℝ) : ℂ) * Complex.exp (↑(-(3 * π / 4)) * Complex.I)).re = -√2 ∧
      (((2 : ℝ) : ℂ) * Complex.exp (↑(-(3 * π / 4)) * Complex.I)).im = -√2 := by
  have h : 3 * π / 4 = π - π / 4 := by ring
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, cos_neg, sin_neg, h, cos_pi_sub, sin_pi_sub, cos_pi_div_four,
    sin_pi_div_four]
  constructor <;> ring

/-- Stitz-Zeager Example 11.7.2(1c,d): `3 cis 0 = 3` and `cis (π/2) = i`. -/
@[kb "stitzzeager2013" "Example 11.7.2, p. 1008"]
theorem ex_11_7_2_cd :
    3 * Complex.exp (↑(0 : ℝ) * Complex.I) = 3 ∧ Complex.exp (↑(π / 2) * Complex.I) = Complex.I := by
  constructor
  · simp
  · apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re, cos_pi_div_two]; simp
    · rw [Complex.exp_ofReal_mul_I_im, sin_pi_div_two]; simp

/-! ### Section 11.8 -/

/-- Stitz-Zeager Example 11.8.2: for `v = ⟨3, 4⟩` and `w = PQ` with `P(-3, 7)`, `Q(-2, 5)`, we get
`w = ⟨1, -2⟩` and `v + w = ⟨4, 2⟩`. -/
@[kb "stitzzeager2013" "Example 11.8.2, p. 1026"]
theorem ex_11_8_2 :
    ((-2 : ℝ) - (-3), (5 : ℝ) - 7) = (1, -2) ∧ ((3 : ℝ), (4 : ℝ)) + (1, -2) = (4, 2) := by
  constructor <;> norm_num

/-- Stitz-Zeager Example 11.8.3: the equation `5v - 2(v + ⟨1, -2⟩) = 0` has the unique solution
`v = ⟨2/3, -4/3⟩`. -/
@[kb "stitzzeager2013" "Example 11.8.3, p. 1031"]
theorem ex_11_8_3 (v : ℝ × ℝ) :
    (5 : ℝ) • v - (2 : ℝ) • (v + (1, -2)) = 0 ↔ v = (2 / 3, -(4 / 3)) := by
  obtain ⟨a, b⟩ := v
  simp only [Prod.mk_add_mk, Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_eq_zero, Prod.mk.injEq,
    smul_eq_mul]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Section 11.10 -/

/-- Stitz-Zeager Example 11.10.1: the curve `x = t² - 3`, `y = 2t - 1` for `t ≥ -2` is the part
`y ≥ -5` of the parabola `(y+1)² = 4(x+3)`. -/
@[kb "stitzzeager2013" "Example 11.10.1, p. 1061"]
theorem ex_11_10_1 :
    {p : ℝ × ℝ | ∃ t : ℝ, -2 ≤ t ∧ p = (t ^ 2 - 3, 2 * t - 1)} =
      {p : ℝ × ℝ | (p.2 + 1) ^ 2 = 4 * (p.1 + 3) ∧ -5 ≤ p.2} := by
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨(y + 1) / 2, by linarith, ?_, by ring⟩
    nlinarith

/-- Stitz-Zeager Example 11.10.2(2): the curve `x = 2e^{-t}`, `y = e^{-2t}` for `t ≥ 0` is the
part `0 < x ≤ 2` of the parabola `y = x²/4`. -/
@[kb "stitzzeager2013" "Example 11.10.2, p. 1062"]
theorem ex_11_10_2_b :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 ≤ t ∧ p = (2 * exp (-t), exp (-2 * t))} =
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ 2 ∧ p.2 = p.1 ^ 2 / 4} := by
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    refine ⟨by positivity, ?_, ?_⟩
    · have : exp (-t) ≤ 1 := by rw [exp_le_one_iff]; linarith
      linarith
    · rw [mul_pow, ← exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * -t = -2 * t by ring]
      ring_nf
  · rintro ⟨h0, h2, rfl⟩
    refine ⟨-log (x / 2), ?_, ?_, ?_⟩
    · have : log (x / 2) ≤ 0 := log_nonpos (by positivity) (by linarith)
      linarith
    · rw [neg_neg, exp_log (by positivity)]; ring
    · rw [show -2 * -log (x / 2) = 2 * log (x / 2) by ring]
      rw [show (2 : ℝ) * log (x / 2) = log (x / 2) + log (x / 2) by ring, exp_add,
        exp_log (by positivity)]
      ring

/-- Stitz-Zeager Example 11.10.2(3): the curve `x = sin t`, `y = csc t` for `0 < t < π` is the part
`0 < x ≤ 1` of the hyperbola `y = 1/x`. -/
@[kb "stitzzeager2013" "Example 11.10.2, p. 1062"]
theorem ex_11_10_2_c :
    {p : ℝ × ℝ | ∃ t : ℝ, 0 < t ∧ t < π ∧ p = (sin t, (sin t)⁻¹)} =
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = p.1⁻¹} := by
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨t, h0, h1, rfl, rfl⟩
    exact ⟨sin_pos_of_pos_of_lt_pi h0 h1, sin_le_one t, rfl⟩
  · rintro ⟨h0, h1, rfl⟩
    refine ⟨arcsin x, arcsin_pos.2 h0, ?_, ?_, ?_⟩
    · have : arcsin x ≤ π / 2 := arcsin_le_pi_div_two x
      linarith [pi_pos]
    · exact (sin_arcsin (by linarith) h1).symm
    · rw [sin_arcsin (by linarith) h1]

end UndergradKB.Precalculus.Course
