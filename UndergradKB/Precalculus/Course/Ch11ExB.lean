import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 11 (Stitz-Zeager): worked examples, wave 5

The modelling, polar-coordinate and polar-graph examples of Sections 11.1, 11.4 and 11.5. A point
in polar coordinates `(r, θ)` is identified with `(r cos θ, r sin θ)` in the plane.
-/

namespace UndergradKB.Precalculus.Course

open Real Set

/-! ### Section 11.1 -/

/-- Stitz-Zeager Example 11.1.2: the hand-fitted model `H t = 9.25 sin (π t/6 - π/2) + 12.55` of
the daylight data has baseline `12.55` (the average of the extremes `3.3` and `21.8`), amplitude
`9.25`, period `12`, equals the baseline at `t = 3`, and attains `21.8` at `t = 6` and `3.3` at
`t = 12`. -/
@[kb "stitzzeager2013" "Example 11.1.2, p. 896"]
theorem ex_11_1_2 (H : ℝ → ℝ) (hH : ∀ t, H t = 9.25 * sin (π / 6 * t - π / 2) + 12.55) :
    (3.3 + 21.8) / 2 = (12.55 : ℝ) ∧ (21.8 : ℝ) - 12.55 = 9.25 ∧ (12.55 : ℝ) - 3.3 = 9.25 ∧
      Function.Periodic H 12 ∧ H 3 = 12.55 ∧ H 6 = 21.8 ∧ H 12 = 3.3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hH, hH, show π / 6 * (t + 12) - π / 2 = (π / 6 * t - π / 2) + 2 * π by ring,
      sin_add_two_pi]
  · rw [hH, show π / 6 * 3 - π / 2 = 0 by ring, sin_zero]; norm_num
  · rw [hH, show π / 6 * 6 - π / 2 = π / 2 by ring, sin_pi_div_two]; norm_num
  · rw [hH, show π / 6 * 12 - π / 2 = -(π / 2) + 2 * π by ring, sin_add_two_pi, sin_neg,
      sin_pi_div_two]; norm_num

/-! ### Section 11.4 -/

/-- Stitz-Zeager Example 11.4.1(1): `P(2, 240°)` is also `(2, -120°)` and `(-2, 60°)`
(angles in radians: `4π/3`, `-2π/3`, `π/3`). -/
@[kb "stitzzeager2013" "Example 11.4.1, p. 933"]
theorem ex_11_4_1_a :
    (2 * cos (4 * π / 3), 2 * sin (4 * π / 3)) = (2 * cos (-(2 * π / 3)), 2 * sin (-(2 * π / 3))) ∧
      (2 * cos (4 * π / 3), 2 * sin (4 * π / 3)) = (-2 * cos (π / 3), -2 * sin (π / 3)) := by
  have h : 4 * π / 3 = -(2 * π / 3) + 2 * π := by ring
  have h2 : 4 * π / 3 = π / 3 + π := by ring
  constructor
  · rw [h, cos_add_two_pi, sin_add_two_pi]
  · rw [h2, cos_add_pi, sin_add_pi]; ext <;> simp

/-- Stitz-Zeager Example 11.4.1(2): `P(-4, 7π/6)` is also `(4, π/6)` and `(-4, -5π/6)`. -/
@[kb "stitzzeager2013" "Example 11.4.1, p. 933"]
theorem ex_11_4_1_b :
    (-4 * cos (7 * π / 6), -4 * sin (7 * π / 6)) = (4 * cos (π / 6), 4 * sin (π / 6)) ∧
      (-4 * cos (7 * π / 6), -4 * sin (7 * π / 6)) =
        (-4 * cos (-(5 * π / 6)), -4 * sin (-(5 * π / 6))) := by
  have h : 7 * π / 6 = π / 6 + π := by ring
  have h2 : 7 * π / 6 = -(5 * π / 6) + 2 * π := by ring
  constructor
  · rw [h, cos_add_pi, sin_add_pi]; ext <;> simp
  · rw [h2, cos_add_two_pi, sin_add_two_pi]

/-- Stitz-Zeager Example 11.4.1(3): `P(117, -5π/2)` is also `(117, 3π/2)` and `(-117, π/2)`. -/
@[kb "stitzzeager2013" "Example 11.4.1, p. 933"]
theorem ex_11_4_1_c :
    (117 * cos (-(5 * π / 2)), 117 * sin (-(5 * π / 2))) = (117 * cos (3 * π / 2), 117 * sin (3 * π / 2)) ∧
      (117 * cos (-(5 * π / 2)), 117 * sin (-(5 * π / 2))) =
        (-117 * cos (π / 2), -117 * sin (π / 2)) := by
  have h : -(5 * π / 2) = π / 2 + (-3 * π) := by ring
  have h1 : 3 * π / 2 = π / 2 + π := by ring
  have c1 : cos (-(5 * π / 2)) = 0 := by
    rw [cos_neg, show 5 * π / 2 = π / 2 + 2 * π by ring, cos_add_two_pi, cos_pi_div_two]
  have s1 : sin (-(5 * π / 2)) = -1 := by
    rw [sin_neg, show 5 * π / 2 = π / 2 + 2 * π by ring, sin_add_two_pi, sin_pi_div_two]
  have c2 : cos (3 * π / 2) = 0 := by rw [h1, cos_add_pi, cos_pi_div_two]; simp
  have s2 : sin (3 * π / 2) = -1 := by rw [h1, sin_add_pi, sin_pi_div_two]
  rw [c1, s1, c2, s2, cos_pi_div_two, sin_pi_div_two]
  constructor <;> ext <;> simp

/-- Stitz-Zeager Example 11.4.1(4): `P(-3, -π/4)` is also `(3, 3π/4)` and `(-3, 7π/4)`. -/
@[kb "stitzzeager2013" "Example 11.4.1, p. 933"]
theorem ex_11_4_1_d :
    (-3 * cos (-(π / 4)), -3 * sin (-(π / 4))) = (3 * cos (3 * π / 4), 3 * sin (3 * π / 4)) ∧
      (-3 * cos (-(π / 4)), -3 * sin (-(π / 4))) = (-3 * cos (7 * π / 4), -3 * sin (7 * π / 4)) := by
  have h1 : 3 * π / 4 = π - π / 4 := by ring
  have h2 : 7 * π / 4 = -(π / 4) + 2 * π := by ring
  constructor
  · rw [h1, cos_pi_sub, sin_pi_sub, cos_neg, sin_neg]; ext <;> simp
  · rw [h2, cos_add_two_pi, sin_add_two_pi]

/-- Stitz-Zeager Example 11.4.3(1b): the line `y = -x` in polar form is `r = 0` or
`cos θ + sin θ = 0`, and the latter holds exactly for `θ = -π/4 + πk`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_b (r θ : ℝ) :
    r * sin θ = -(r * cos θ) ↔ r = 0 ∨ cos θ + sin θ = 0 := by
  constructor
  · intro h
    have : r * (cos θ + sin θ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h2 | h2
    · left; exact h2
    · right; exact h2
  · rintro (h | h)
    · rw [h]; ring
    · have : sin θ = -cos θ := by linarith
      rw [this]; ring

/-- Stitz-Zeager Example 11.4.3(1b): `cos θ + sin θ = 0` exactly when `θ = -π/4 + πk`,
`k` an integer; the line `θ = -π/4` consists of points with `y = -x`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_b_angle (θ : ℝ) :
    cos θ + sin θ = 0 ↔ ∃ k : ℤ, θ = -(π / 4) + π * k := by
  have key : cos θ + sin θ = 0 ↔ tan θ = -1 := by
    constructor
    · intro h
      have hc : cos θ ≠ 0 := by
        intro h0; rw [h0] at h
        have : sin θ = 0 := by linarith
        have := sin_sq_add_cos_sq θ
        rw [h0, ‹sin θ = 0›] at this; norm_num at this
      rw [tan_eq_sin_div_cos, div_eq_iff hc]; linarith
    · intro h
      have hc : cos θ ≠ 0 := by
        intro h0; rw [tan_eq_sin_div_cos, h0] at h; simp at h
      rw [tan_eq_sin_div_cos, div_eq_iff hc] at h; linarith
  rw [key]
  have e1 : arctan (-1) = -(π / 4) := by rw [arctan_neg, arctan_one]
  constructor
  · intro h
    have hc : cos θ ≠ 0 := by
      intro h0; rw [tan_eq_sin_div_cos, h0] at h; simp at h
    have hn : tan θ = tan (-(π / 4)) := by rw [h, tan_neg, tan_pi_div_four]
    have hc2 : cos (-(π / 4)) ≠ 0 := by rw [cos_neg, cos_pi_div_four]; positivity
    have h' : sin (θ - -(π / 4)) = 0 := by
      rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hc hc2] at hn
      rw [sin_sub]; linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 h'
    exact ⟨n, by linarith⟩
  · rintro ⟨k, hk⟩
    rw [hk, show -(π / 4) + π * k = -(π / 4) + k * π by ring, tan_periodic.int_mul k, tan_neg,
      tan_pi_div_four]

/-- Stitz-Zeager Example 11.4.3(1b): every point `(r, -π/4)` lies on the line `y = -x`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_b_line (r : ℝ) : r * sin (-(π / 4)) = -(r * cos (-(π / 4))) := by
  rw [sin_neg, cos_neg, sin_pi_div_four, cos_pi_div_four]; ring

/-- Stitz-Zeager Example 11.4.3(2a): the polar equation `r = -3` describes exactly the circle
`x² + y² = 9`: every such point satisfies it, and every point of the circle is `(-3 cos θ, -3 sin θ)`
for some `θ`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_d (x y : ℝ) :
    x ^ 2 + y ^ 2 = 9 ↔ ∃ θ : ℝ, x = -3 * cos θ ∧ y = -3 * sin θ := by
  constructor
  · intro h
    set z : ℂ := ⟨-x, -y⟩ with hz
    have hn : ‖z‖ = 3 := by
      rw [Complex.norm_def, Complex.normSq_apply]
      rw [show z.re * z.re + z.im * z.im = 3 ^ 2 by simp [hz]; nlinarith]
      exact Real.sqrt_sq (by norm_num)
    refine ⟨Complex.arg z, ?_, ?_⟩
    · have := Complex.norm_mul_cos_arg z
      rw [hn] at this
      simp [hz] at this; linarith
    · have := Complex.norm_mul_sin_arg z
      rw [hn] at this
      simp [hz] at this; linarith
  · rintro ⟨θ, rfl, rfl⟩
    have := sin_sq_add_cos_sq θ
    nlinarith

/-- Stitz-Zeager Example 11.4.3(2b): the polar equation `θ = 4π/3` describes points with
`y = √3 x` (since `tan (4π/3) = √3`). -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_e (r : ℝ) :
    tan (4 * π / 3) = √3 ∧ r * sin (4 * π / 3) = √3 * (r * cos (4 * π / 3)) := by
  have h : 4 * π / 3 = π / 3 + π := by ring
  have t : tan (4 * π / 3) = √3 := by rw [h, tan_add_pi, tan_pi_div_three]
  refine ⟨t, ?_⟩
  rw [h, sin_add_pi, cos_add_pi, sin_pi_div_three, cos_pi_div_three]
  ring

/-- Stitz-Zeager Example 11.4.3(2c): points of the polar curve `r = 1 - cos θ` satisfy
`(x² + y² + x)² = x² + y²` with `x = r cos θ`, `y = r sin θ`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_f (r θ : ℝ) (h : r = 1 - cos θ) :
    ((r * cos θ) ^ 2 + (r * sin θ) ^ 2 + r * cos θ) ^ 2 = (r * cos θ) ^ 2 + (r * sin θ) ^ 2 := by
  have h1 := sin_sq_add_cos_sq θ
  have h2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h1
  have h3 : r = r ^ 2 + r * cos θ := by
    have : r * r = r * (1 - cos θ) := by rw [← h]
    nlinarith
  rw [h2, ← h3]

/-! ### Section 11.5 -/

/-- The graph of `r = ρ` (all points `(ρ cos θ, ρ sin θ)`) is the circle `x² + y² = ρ²`. -/
private theorem circle_pts (ρ : ℝ) :
    {p : ℝ × ℝ | ∃ θ : ℝ, p = (ρ * cos θ, ρ * sin θ)} = {p | p.1 ^ 2 + p.2 ^ 2 = ρ ^ 2} := by
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨θ, rfl, rfl⟩
    have := sin_sq_add_cos_sq θ
    nlinarith
  · intro h
    set z : ℂ := ⟨x, y⟩ with hz
    have hn : ‖z‖ = |ρ| := by
      rw [Complex.norm_def, Complex.normSq_apply]
      rw [show z.re * z.re + z.im * z.im = |ρ| ^ 2 by
        rw [sq_abs]; simp [hz]; nlinarith]
      exact Real.sqrt_sq (abs_nonneg _)
    have c := Complex.norm_mul_cos_arg z
    have s := Complex.norm_mul_sin_arg z
    rw [hn] at c s
    simp only [hz] at c s
    rcases le_or_gt 0 ρ with hρ | hρ
    · rw [abs_of_nonneg hρ] at c s
      exact ⟨Complex.arg z, c.symm, s.symm⟩
    · rw [abs_of_neg hρ] at c s
      refine ⟨Complex.arg z + π, ?_, ?_⟩
      · rw [cos_add_pi]; linarith
      · rw [sin_add_pi]; linarith

/-- Stitz-Zeager Example 11.5.1(1): the graph of `r = 4` is the circle `x² + y² = 16`. -/
@[kb "stitzzeager2013" "Example 11.5.1, p. 950"]
theorem ex_11_5_1_a :
    {p : ℝ × ℝ | ∃ θ : ℝ, p = (4 * cos θ, 4 * sin θ)} = {p | p.1 ^ 2 + p.2 ^ 2 = 4 ^ 2} :=
  circle_pts 4

/-- Stitz-Zeager Example 11.5.1(2): the graph of `r = -3√2` is the circle `x² + y² = 18`
(radius `3√2`). -/
@[kb "stitzzeager2013" "Example 11.5.1, p. 950"]
theorem ex_11_5_1_b :
    {p : ℝ × ℝ | ∃ θ : ℝ, p = (-(3 * √2) * cos θ, -(3 * √2) * sin θ)} =
      {p | p.1 ^ 2 + p.2 ^ 2 = 18} := by
  rw [circle_pts]
  ext p
  simp only [mem_ofPred_eq]
  have : (-(3 * √2)) ^ 2 = (18 : ℝ) := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  rw [this]

/-- Stitz-Zeager Example 11.5.1(3): the graph of `θ = 5π/4` is the line `y = x`. -/
@[kb "stitzzeager2013" "Example 11.5.1, p. 950"]
theorem ex_11_5_1_c :
    {p : ℝ × ℝ | ∃ r : ℝ, p = (r * cos (5 * π / 4), r * sin (5 * π / 4))} =
      {p | p.2 = p.1} := by
  have h : 5 * π / 4 = π / 4 + π := by ring
  have s2 : 0 < √2 := by positivity
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_four, sin_pi_div_four]
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨r, rfl, rfl⟩; ring
  · intro hxy
    refine ⟨-(√2) * x, ?_, ?_⟩
    · have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      linear_combination (-x / 2) * this
    · have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      rw [hxy]; linear_combination (-x / 2) * this

/-- Stitz-Zeager Example 11.5.1(4): the graph of `θ = -3π/2` is the `y`-axis. -/
@[kb "stitzzeager2013" "Example 11.5.1, p. 950"]
theorem ex_11_5_1_d :
    {p : ℝ × ℝ | ∃ r : ℝ, p = (r * cos (-(3 * π / 2)), r * sin (-(3 * π / 2)))} =
      {p | p.1 = 0} := by
  have c : cos (-(3 * π / 2)) = 0 := by
    rw [cos_neg, show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; simp
  have s : sin (-(3 * π / 2)) = 1 := by
    rw [sin_neg, show 3 * π / 2 = π / 2 + π by ring, sin_add_pi, sin_pi_div_two]; simp
  rw [c, s]
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, Prod.mk.injEq, mul_zero, mul_one]
  constructor
  · rintro ⟨r, rfl, rfl⟩; rfl
  · intro h; exact ⟨y, h, rfl⟩

end UndergradKB.Precalculus.Course
