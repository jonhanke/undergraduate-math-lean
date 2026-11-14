import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 11 (Stitz-Zeager): worked examples, wave 5 (continued)

Polar graphs and regions (Section 11.5), rotation of axes and polar conics (Section 11.6), and the
plane-and-wind vector example (Section 11.8). A polar point `(r, θ)` has rectangular coordinates
`x = r cos θ`, `y = r sin θ`.
-/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ### Section 11.5 -/

/-- Stitz-Zeager Example 11.5.2(1): the cardioid-type curve `r = 4 - 2 sin θ` has `r = 4, 2, 4, 6, 4`
at `θ = 0, π/2, π, 3π/2, 2π`, always `2 ≤ r ≤ 6`, decreases on `[0, π/2]`, increases on
`[π/2, 3π/2]` and decreases on `[3π/2, 2π]`. -/
@[kb "stitzzeager2013" "Example 11.5.2, p. 954"]
theorem ex_11_5_2_a (r : ℝ → ℝ) (hr : ∀ θ, r θ = 4 - 2 * sin θ) :
    r 0 = 4 ∧ r (π / 2) = 2 ∧ r π = 4 ∧ r (3 * π / 2) = 6 ∧ r (2 * π) = 4 ∧
      (∀ θ, 2 ≤ r θ ∧ r θ ≤ 6) ∧ StrictAntiOn r (Icc 0 (π / 2)) ∧
      StrictMonoOn r (Icc (π / 2) (3 * π / 2)) ∧ StrictAntiOn r (Icc (3 * π / 2) (2 * π)) := by
  have hp := pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; simp
  · rw [hr, sin_pi_div_two]; norm_num
  · rw [hr]; simp
  · rw [hr, show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]; norm_num
  · rw [hr]; simp
  · intro θ
    rw [hr]
    constructor <;> nlinarith [sin_le_one θ, neg_one_le_sin θ]
  · intro a ha b hb hab
    have := strictMonoOn_sin ⟨by linarith [ha.1], ha.2⟩ ⟨by linarith [hb.1], hb.2⟩ hab
    rw [hr, hr]; linarith
  · intro a ha b hb hab
    have := strictMonoOn_sin (a := π - b) (b := π - a) ⟨by linarith [hb.2], by linarith [hb.1]⟩
      ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)
    rw [sin_pi_sub, sin_pi_sub] at this
    rw [hr, hr]; linarith
  · intro a ha b hb hab
    have := strictMonoOn_sin (a := a - 2 * π) (b := b - 2 * π) ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)
    rw [sin_sub_two_pi, sin_sub_two_pi] at this
    rw [hr, hr]; linarith

private theorem cos_le_neg_half {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ π) :
    (cos u ≤ -(1 / 2) ↔ 2 * π / 3 ≤ u) ∧ (cos u < -(1 / 2) ↔ 2 * π / 3 < u) := by
  have hp := pi_pos
  have c : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have m1 := strictAntiOn_cos (a := 2 * π / 3) (b := u)
  have m2 := strictAntiOn_cos.antitoneOn (a := 2 * π / 3) (b := u)
  have m3 := strictAntiOn_cos (a := u) (b := 2 * π / 3)
  have m4 := strictAntiOn_cos.antitoneOn (a := u) (b := 2 * π / 3)
  have i1 : (2 * π / 3 : ℝ) ∈ Icc 0 π := ⟨by linarith, by linarith⟩
  have i2 : u ∈ Icc 0 π := ⟨h0, h1⟩
  constructor
  · constructor
    · intro h
      by_contra hh
      push Not at hh
      have := m3 i2 i1 hh
      linarith
    · intro h
      have := m2 i1 i2 h
      linarith
  · constructor
    · intro h
      by_contra hh
      push Not at hh
      have := m4 i2 i1 hh
      linarith
    · intro h
      have := m1 i1 i2 h
      linarith

private theorem cos_half_circle {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * π) :
    (cos θ ≤ -(1 / 2) ↔ 2 * π / 3 ≤ θ ∧ θ ≤ 4 * π / 3) ∧
      (cos θ < -(1 / 2) ↔ 2 * π / 3 < θ ∧ θ < 4 * π / 3) := by
  have hp := pi_pos
  by_cases c : θ ≤ π
  · have := cos_le_neg_half h0 c
    refine ⟨?_, ?_⟩
    · rw [this.1]; constructor
      · intro h; exact ⟨h, by linarith⟩
      · intro h; exact h.1
    · rw [this.2]; constructor
      · intro h; exact ⟨h, by linarith⟩
      · intro h; exact h.1
  · push Not at c
    have := cos_le_neg_half (u := 2 * π - θ) (by linarith) (by linarith)
    rw [cos_two_pi_sub] at this
    refine ⟨?_, ?_⟩
    · rw [this.1]; constructor
      · intro h; exact ⟨by linarith, by linarith⟩
      · intro h; linarith [h.2]
    · rw [this.2]; constructor
      · intro h; exact ⟨by linarith, by linarith⟩
      · intro h; linarith [h.2]

/-- Stitz-Zeager Example 11.5.2(2): the limaçon `r = 2 + 4 cos θ` has `r = 6, 2, -2, 2, 6` at
`θ = 0, π/2, π, 3π/2, 2π`, vanishes at `2π/3` and `4π/3`, and on `[0, 2π]` is negative exactly for
`2π/3 < θ < 4π/3` (the inner loop). -/
@[kb "stitzzeager2013" "Example 11.5.2, p. 954"]
theorem ex_11_5_2_b (r : ℝ → ℝ) (hr : ∀ θ, r θ = 2 + 4 * cos θ) :
    r 0 = 6 ∧ r (π / 2) = 2 ∧ r π = -2 ∧ r (3 * π / 2) = 2 ∧ r (2 * π) = 6 ∧
      r (2 * π / 3) = 0 ∧ r (4 * π / 3) = 0 ∧
      ∀ θ, 0 ≤ θ → θ ≤ 2 * π → (r θ < 0 ↔ 2 * π / 3 < θ ∧ θ < 4 * π / 3) := by
  have hp := pi_pos
  have c1 : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have c2 : cos (4 * π / 3) = -(1 / 2) := by
    rw [show 4 * π / 3 = π / 3 + π by ring, cos_add_pi, cos_pi_div_three]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; norm_num
  · rw [hr, cos_pi_div_two]; norm_num
  · rw [hr]; simp; norm_num
  · rw [hr, show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; norm_num
  · rw [hr, cos_two_pi]; norm_num
  · rw [hr, c1]; norm_num
  · rw [hr, c2]; norm_num
  · intro θ h0 h1
    rw [hr, ← (cos_half_circle h0 h1).2]
    constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 11.5.2(3): the rose `r = 5 sin 2θ` satisfies `|r| ≤ 5`, has `r = 5, -5, 5, -5`
at `θ = π/4, 3π/4, 5π/4, 7π/4`, vanishes at `θ = 0` and `π/2`, and is positive on `(0, π/2)`. -/
@[kb "stitzzeager2013" "Example 11.5.2, p. 954"]
theorem ex_11_5_2_c (r : ℝ → ℝ) (hr : ∀ θ, r θ = 5 * sin (2 * θ)) :
    (∀ θ, |r θ| ≤ 5) ∧ r (π / 4) = 5 ∧ r (3 * π / 4) = -5 ∧ r (5 * π / 4) = 5 ∧
      r (7 * π / 4) = -5 ∧ r 0 = 0 ∧ r (π / 2) = 0 ∧ ∀ θ ∈ Ioo 0 (π / 2), 0 < r θ := by
  have hp := pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    rw [hr, abs_le]
    constructor <;> nlinarith [sin_le_one (2 * θ), neg_one_le_sin (2 * θ)]
  · rw [hr, show 2 * (π / 4) = π / 2 by ring, sin_pi_div_two]; norm_num
  · rw [hr, show 2 * (3 * π / 4) = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]; norm_num
  · rw [hr, show 2 * (5 * π / 4) = π / 2 + 2 * π by ring, sin_add_two_pi, sin_pi_div_two]
    norm_num
  · rw [hr, show 2 * (7 * π / 4) = π / 2 + π + 2 * π by ring, sin_add_two_pi, sin_add_pi,
      sin_pi_div_two]; norm_num
  · rw [hr]; simp
  · rw [hr, show 2 * (π / 2) = π by ring, sin_pi]; norm_num
  · rintro θ ⟨h0, h1⟩
    rw [hr]
    have := sin_pos_of_pos_of_lt_pi (x := 2 * θ) (by linarith) (by linarith)
    linarith

/-- Stitz-Zeager Example 11.5.2(4): the lemniscate `r² = 16 cos 2θ` has points at angle `θ` exactly
when `cos 2θ ≥ 0`; for `θ = 0` the points are `r = ±4`, for `θ = π/4` only the pole, and no point
has an angle in `(π/4, 3π/4)`. -/
@[kb "stitzzeager2013" "Example 11.5.2, p. 954"]
theorem ex_11_5_2_d :
    (∀ θ : ℝ, (∃ r : ℝ, r ^ 2 = 16 * cos (2 * θ)) ↔ 0 ≤ cos (2 * θ)) ∧
      (∀ r : ℝ, r ^ 2 = 16 * cos (2 * 0) ↔ r = 4 ∨ r = -4) ∧
      (∀ r : ℝ, r ^ 2 = 16 * cos (2 * (π / 4)) ↔ r = 0) ∧
      ∀ θ ∈ Ioo (π / 4) (3 * π / 4), ¬ ∃ r : ℝ, r ^ 2 = 16 * cos (2 * θ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ
    constructor
    · rintro ⟨r, hr⟩
      nlinarith [sq_nonneg r]
    · intro h
      exact ⟨√(16 * cos (2 * θ)), Real.sq_sqrt (by linarith)⟩
  · intro r
    rw [mul_zero, cos_zero]
    constructor
    · intro h
      have : (r - 4) * (r + 4) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h2 | h2
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> norm_num
  · intro r
    rw [show 2 * (π / 4) = π / 2 by ring, cos_pi_div_two]
    constructor
    · intro h; nlinarith [sq_nonneg r]
    · intro h; rw [h]; norm_num
  · rintro θ ⟨h0, h1⟩ ⟨r, hr⟩
    have hp := pi_pos
    have : cos (2 * θ) < 0 :=
      cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    nlinarith [sq_nonneg r]

/-- Stitz-Zeager Example 11.5.4(1): on `0 ≤ θ ≤ π/2` the bound `5 sin 2θ` is nonnegative (so the
region is the first-quadrant petal), it vanishes at both ends and equals `5` at `π/4`. -/
@[kb "stitzzeager2013" "Example 11.5.4, p. 968"]
theorem ex_11_5_4_a :
    (∀ θ ∈ Icc 0 (π / 2), 0 ≤ 5 * sin (2 * θ)) ∧ 5 * sin (2 * 0) = 0 ∧
      5 * sin (2 * (π / 2)) = 0 ∧ 5 * sin (2 * (π / 4)) = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro θ ⟨h0, h1⟩
    have := sin_nonneg_of_nonneg_of_le_pi (x := 2 * θ) (by linarith) (by linarith [pi_pos])
    linarith
  · simp
  · rw [show 2 * (π / 2) = π by ring, sin_pi]; norm_num
  · rw [show 2 * (π / 4) = π / 2 by ring, sin_pi_div_two]; norm_num

/-- Stitz-Zeager Example 11.5.4(2): the circle `r = 3` and the rose `r = 6 cos 2θ` meet at
`θ = π/6`, and for `0 ≤ θ ≤ π/2` one has `3 ≤ 6 cos 2θ` exactly when `θ ≤ π/6`. -/
@[kb "stitzzeager2013" "Example 11.5.4, p. 968"]
theorem ex_11_5_4_b :
    6 * cos (2 * (π / 6)) = 3 ∧ ∀ θ ∈ Icc 0 (π / 2), (3 ≤ 6 * cos (2 * θ) ↔ θ ≤ π / 6) := by
  have hp := pi_pos
  have c : cos (π / 3) = 1 / 2 := cos_pi_div_three
  refine ⟨by rw [show 2 * (π / 6) = π / 3 by ring, c]; norm_num, ?_⟩
  rintro θ ⟨h0, h1⟩
  have i1 : (π / 3 : ℝ) ∈ Icc 0 π := ⟨by linarith, by linarith⟩
  have i2 : 2 * θ ∈ Icc 0 π := ⟨by linarith, by linarith⟩
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have := strictAntiOn_cos i1 i2 (by linarith : π / 3 < 2 * θ)
    rw [c] at this; linarith
  · intro h
    have := strictAntiOn_cos.antitoneOn i2 i1 (by linarith : 2 * θ ≤ π / 3)
    rw [c] at this; linarith

/-- Stitz-Zeager Example 11.5.4(3): on the inner loop `2π/3 ≤ θ ≤ 4π/3` of the limaçon
`r = 2 + 4 cos θ`, the radius is `≤ 0`, with value `0` at both ends and `-2` at `θ = π`. -/
@[kb "stitzzeager2013" "Example 11.5.4, p. 968"]
theorem ex_11_5_4_c :
    (∀ θ ∈ Icc (2 * π / 3) (4 * π / 3), 2 + 4 * cos θ ≤ 0) ∧
      2 + 4 * cos (2 * π / 3) = 0 ∧ 2 + 4 * cos (4 * π / 3) = 0 ∧ 2 + 4 * cos π = -2 := by
  have hp := pi_pos
  have c1 : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have c2 : cos (4 * π / 3) = -(1 / 2) := by
    rw [show 4 * π / 3 = π / 3 + π by ring, cos_add_pi, cos_pi_div_three]
  refine ⟨?_, by rw [c1]; norm_num, by rw [c2]; norm_num, by rw [cos_pi]; norm_num⟩
  rintro θ ⟨h0, h1⟩
  have := (cos_half_circle (θ := θ) (by linarith) (by linarith)).1.2 ⟨h0, h1⟩
  linarith

/-- Stitz-Zeager Example 11.5.4(4): the curves `r = 2 sin θ` and `r = 2 - 2 sin θ` meet at `π/6`
(both give `1`); on `[0, π/2]` the first is the smaller one for `θ ≤ π/6` and the second for
`θ ≥ π/6`, and both radii are nonnegative. -/
@[kb "stitzzeager2013" "Example 11.5.4, p. 968"]
theorem ex_11_5_4_d :
    2 * sin (π / 6) = 1 ∧ 2 - 2 * sin (π / 6) = 1 ∧
      ∀ θ ∈ Icc 0 (π / 2), 0 ≤ 2 * sin θ ∧ 0 ≤ 2 - 2 * sin θ ∧
        (θ ≤ π / 6 → 2 * sin θ ≤ 2 - 2 * sin θ) ∧ (π / 6 ≤ θ → 2 - 2 * sin θ ≤ 2 * sin θ) := by
  have hp := pi_pos
  refine ⟨by rw [sin_pi_div_six]; norm_num, by rw [sin_pi_div_six]; norm_num, ?_⟩
  rintro θ ⟨h0, h1⟩
  have s0 := sin_nonneg_of_nonneg_of_le_pi (x := θ) h0 (by linarith)
  have s1 := sin_le_one θ
  have i1 : (π / 6 : ℝ) ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have i2 : θ ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith, h1⟩
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro h
    have := strictMonoOn_sin.monotoneOn i2 i1 h
    rw [sin_pi_div_six] at this; linarith
  · intro h
    have := strictMonoOn_sin.monotoneOn i1 i2 h
    rw [sin_pi_div_six] at this; linarith

/-! ### Section 11.6 -/

/-- Stitz-Zeager Example 11.6.2(1): for `5x² + 26xy + 5y² - 16√2 x + 16√2 y - 104 = 0` we have
`cot 2θ = (A - C)/B = 0` solved by `θ = π/4`; with the rotation `x = (x' - y')√2/2`,
`y = (x' + y')√2/2` the left side becomes `18x'² - 8y'² + 32y' - 104`, and the equation is the
hyperbola `x'²/4 - (y' - 2)²/9 = 1`. -/
@[kb "stitzzeager2013" "Example 11.6.2, p. 989"]
theorem ex_11_6_2_a :
    cos (2 * (π / 4)) = 0 ∧
      ∀ x' y' : ℝ,
        5 * ((x' - y') * (√2 / 2)) ^ 2 + 26 * ((x' - y') * (√2 / 2)) * ((x' + y') * (√2 / 2)) +
            5 * ((x' + y') * (√2 / 2)) ^ 2 - 16 * √2 * ((x' - y') * (√2 / 2)) +
            16 * √2 * ((x' + y') * (√2 / 2)) - 104 = 18 * x' ^ 2 - 8 * y' ^ 2 + 32 * y' - 104 ∧
          (18 * x' ^ 2 - 8 * y' ^ 2 + 32 * y' - 104 = 0 ↔ x' ^ 2 / 4 - (y' - 2) ^ 2 / 9 = 1) := by
  refine ⟨by rw [show 2 * (π / 4) = π / 2 by ring, cos_pi_div_two], ?_⟩
  intro x' y'
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_⟩
  · linear_combination (9 * x' ^ 2 - 4 * y' ^ 2 + 16 * y') * hs
  · constructor <;> intro h <;> linarith

/-- Stitz-Zeager Example 11.6.2(2): for `16x² + 24xy + 9y² + 15x - 20y = 0`, the angle
`θ = arctan (3/4)` has `cos θ = 4/5`, `sin θ = 3/5` and `cot 2θ = 7/24 = (A - C)/B`; the equation
`24t² + 14t - 24 = 0` for `t = tan θ` factors as `2(3t + 4)(4t - 3)`; and with the rotation
`x = (4x' - 3y')/5`, `y = (3x' + 4y')/5` the left side becomes `25x'² - 25y'` (the parabola
`y' = x'²`). -/
@[kb "stitzzeager2013" "Example 11.6.2, p. 989"]
theorem ex_11_6_2_b :
    cos (arctan (3 / 4)) = 4 / 5 ∧ sin (arctan (3 / 4)) = 3 / 5 ∧
      cos (2 * arctan (3 / 4)) / sin (2 * arctan (3 / 4)) = 7 / 24 ∧
      (∀ t : ℝ, 24 * t ^ 2 + 14 * t - 24 = 2 * (3 * t + 4) * (4 * t - 3)) ∧
      ∀ x' y' : ℝ,
        16 * ((4 * x' - 3 * y') / 5) ^ 2 + 24 * ((4 * x' - 3 * y') / 5) * ((3 * x' + 4 * y') / 5) +
            9 * ((3 * x' + 4 * y') / 5) ^ 2 + 15 * ((4 * x' - 3 * y') / 5) -
            20 * ((3 * x' + 4 * y') / 5) = 25 * x' ^ 2 - 25 * y' := by
  have h : √(1 + (3 / 4 : ℝ) ^ 2) = 5 / 4 := by
    rw [show 1 + (3 / 4 : ℝ) ^ 2 = (5 / 4) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have c : cos (arctan (3 / 4)) = 4 / 5 := by rw [cos_arctan, h]; norm_num
  have s : sin (arctan (3 / 4)) = 3 / 5 := by rw [sin_arctan, h]; norm_num
  refine ⟨c, s, ?_, fun t => by ring, fun x' y' => by ring⟩
  rw [cos_two_mul, sin_two_mul, c, s]; norm_num

/-- Stitz-Zeager Example 11.6.4(1): the conic `r = 4/(1 - sin θ)` (a parabola with directrix
`y = -4`) has `r = 4` at `θ = 0` and `π`, `r = 2` at `θ = 3π/2` (vertex `(0, -2)`), and every point
satisfies `x² = 8y + 16`. -/
@[kb "stitzzeager2013" "Example 11.6.4, p. 995"]
theorem ex_11_6_4_a :
    4 / (1 - sin 0) = (4 : ℝ) ∧ 4 / (1 - sin π) = (4 : ℝ) ∧ 4 / (1 - sin (3 * π / 2)) = (2 : ℝ) ∧
      ∀ r θ : ℝ, r * (1 - sin θ) = 4 → (r * cos θ) ^ 2 = 8 * (r * sin θ) + 16 := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · rw [show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]; norm_num
  · intro r θ h
    have e : r = 4 + r * sin θ := by linarith
    have h2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * sin_sq_add_cos_sq θ
    linear_combination h2 + (r + 4 + r * sin θ) * e

/-- Stitz-Zeager Example 11.6.4(2): the conic `r = 12/(3 - cos θ)` (an ellipse) has `r = 6` at
`θ = 0` and `r = 3` at `θ = π` (vertices `(6, 0)` and `(-3, 0)`), and every point satisfies the
ellipse equation centred at `(3/2, 0)` with semi-axes `9/2` and `3√2`:
`(x - 3/2)²/(81/4) + y²/18 = 1`. -/
@[kb "stitzzeager2013" "Example 11.6.4, p. 995"]
theorem ex_11_6_4_b :
    12 / (3 - cos 0) = (6 : ℝ) ∧ 12 / (3 - cos π) = (3 : ℝ) ∧
      ∀ r θ : ℝ, r * (3 - cos θ) = 12 →
        (r * cos θ - 3 / 2) ^ 2 / (81 / 4) + (r * sin θ) ^ 2 / 18 = 1 := by
  refine ⟨by simp; norm_num, by simp; norm_num, ?_⟩
  intro r θ h
  have h2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ
  have e : 3 * r = 12 + r * cos θ := by linarith
  have key : 8 * (r * cos θ - 3 / 2) ^ 2 + 9 * (r * sin θ) ^ 2 = 162 := by
    have : 9 * ((r * cos θ) ^ 2 + (r * sin θ) ^ 2) = (12 + r * cos θ) ^ 2 := by
      rw [h2, ← e]; ring
    nlinarith
  field_simp
  linarith

/-- Stitz-Zeager Example 11.6.4(3): the conic `r = 6/(1 + 2 sin θ)` (a hyperbola) has `r = 2` at
`θ = π/2` and `r = -6` at `θ = 3π/2` (vertices `(0, 2)` and `(0, 6)`), and every point satisfies
`(y - 4)²/4 - x²/12 = 1` (centre `(0, 4)`, asymptote slopes `±√3/3`). -/
@[kb "stitzzeager2013" "Example 11.6.4, p. 995"]
theorem ex_11_6_4_c :
    6 / (1 + 2 * sin (π / 2)) = (2 : ℝ) ∧ 6 / (1 + 2 * sin (3 * π / 2)) = (-6 : ℝ) ∧
      (-6) * cos (3 * π / 2) = 0 ∧ (-6) * sin (3 * π / 2) = 6 ∧
      ∀ r θ : ℝ, r * (1 + 2 * sin θ) = 6 →
        (r * sin θ - 4) ^ 2 / 4 - (r * cos θ) ^ 2 / 12 = 1 := by
  have h1 : 3 * π / 2 = π / 2 + π := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sin_pi_div_two]; norm_num
  · rw [h1, sin_add_pi, sin_pi_div_two]; norm_num
  · rw [h1, cos_add_pi, cos_pi_div_two]; norm_num
  · rw [h1, sin_add_pi, sin_pi_div_two]; norm_num
  · intro r θ h
    have h2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * sin_sq_add_cos_sq θ
    have e : r = 6 - 2 * (r * sin θ) := by linarith
    have key : (r * cos θ) ^ 2 = 36 - 24 * (r * sin θ) + 3 * (r * sin θ) ^ 2 := by
      have : r ^ 2 = (6 - 2 * (r * sin θ)) ^ 2 := by rw [← e]
      nlinarith
    rw [key]; ring

/-! ### Section 11.8 -/

/-- Stitz-Zeager Example 11.8.1: the plane's velocity `175` at bearing `N40°E` plus the wind `35` at
bearing `S60°E` (bearing `120°`) has squared speed `c² = 175² + 35² - 2·175·35 cos 100°
= 31850 - 12250 cos 100°`, which lies strictly between `183.5²` and `184.5²` (true speed about
`184` mph); also `v · (v + w) = (c² + 29400)/2`, the relation behind the bearing computation
`cos α = (c² + 29400)/(350 c)`. -/
@[kb "stitzzeager2013" "Example 11.8.1, p. 1025"]
theorem ex_11_8_1 :
    (175 * sin (2 * π / 9) + 35 * sin (2 * π / 3)) ^ 2 +
        (175 * cos (2 * π / 9) + 35 * cos (2 * π / 3)) ^ 2 = 31850 - 12250 * cos (5 * π / 9) ∧
      (183.5 : ℝ) ^ 2 < 31850 - 12250 * cos (5 * π / 9) ∧
      31850 - 12250 * cos (5 * π / 9) < (184.5 : ℝ) ^ 2 ∧
      (175 * sin (2 * π / 9)) * (175 * sin (2 * π / 9) + 35 * sin (2 * π / 3)) +
          (175 * cos (2 * π / 9)) * (175 * cos (2 * π / 9) + 35 * cos (2 * π / 3)) =
        (((175 * sin (2 * π / 9) + 35 * sin (2 * π / 3)) ^ 2 +
          (175 * cos (2 * π / 9) + 35 * cos (2 * π / 3)) ^ 2) + 29400) / 2 := by
  have h1 := sin_sq_add_cos_sq (2 * π / 9)
  have h2 := sin_sq_add_cos_sq (2 * π / 3)
  have h3 : cos (4 * π / 9) =
      cos (2 * π / 3) * cos (2 * π / 9) + sin (2 * π / 3) * sin (2 * π / 9) := by
    rw [show 4 * π / 9 = 2 * π / 3 - 2 * π / 9 by ring, cos_sub]
  have h4 : cos (5 * π / 9) = -cos (4 * π / 9) := by
    rw [show 5 * π / 9 = π - 4 * π / 9 by ring, cos_pi_sub]
  have e : (175 * sin (2 * π / 9) + 35 * sin (2 * π / 3)) ^ 2 +
        (175 * cos (2 * π / 9) + 35 * cos (2 * π / 3)) ^ 2 = 31850 - 12250 * cos (5 * π / 9) := by
    rw [h4]
    linear_combination 30625 * h1 + 1225 * h2 - 12250 * h3
  refine ⟨e, ?_, ?_, ?_⟩
  · have hx : cos (5 * π / 9) = -sin (π / 18) := by
      rw [h4, show 4 * π / 9 = π / 2 - π / 18 by ring, cos_pi_div_two_sub]
    have hp1 := pi_gt_d2
    have hp2 := pi_lt_d2
    have := sin_gt_sub_cube (x := π / 18) (by linarith)
    rw [hx]
    nlinarith [sq_nonneg (π / 18), pow_pos (show (0 : ℝ) < π / 18 by linarith) 3]
  · have hx : cos (5 * π / 9) = -sin (π / 18) := by
      rw [h4, show 4 * π / 9 = π / 2 - π / 18 by ring, cos_pi_div_two_sub]
    have hp2 := pi_lt_d2
    have := sin_lt (x := π / 18) (by linarith [pi_pos])
    rw [hx]
    nlinarith
  · rw [e, h4]
    linear_combination 30625 * h1 - 6125 * h3

end UndergradKB.Precalculus.Course
