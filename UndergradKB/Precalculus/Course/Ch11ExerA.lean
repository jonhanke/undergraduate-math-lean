import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): exercises with the book's answers -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Helpers -/

private theorem x11_deriv_sin (A w φ t : ℝ) :
    deriv (fun s : ℝ => A * sin (w * s + φ)) t = A * w * cos (w * t + φ) := by
  have h := (((hasDerivAt_id t).const_mul w).add_const φ).sin.const_mul A
  simp only [id] at h
  rw [h.deriv]; ring

/-! ## Section 11.1 -/

/-- Stitz-Zeager Exercise 11.1.1: the note A (440 Hz) is modeled by `sin (880 π t)`, which has period
`1/440`. -/
@[kb "stitzzeager2013" "Exercise 11.1.1, p. 903"]
theorem exer_11_1_1 : (∀ t : ℝ, sin (880 * π * t) = sin (2 * π * 440 * t)) ∧
    ∀ t : ℝ, sin (880 * π * (t + 1 / 440)) = sin (880 * π * t) := by
  refine ⟨fun t => by ring_nf, fun t => ?_⟩
  have : 880 * π * (t + 1 / 440) = 880 * π * t + 2 * π := by ring
  rw [this, sin_add_two_pi]

/-- Stitz-Zeager Exercise 11.1.2: the voltage `220√2 sin (120 π t)` has amplitude `220√2`, period `1/60`,
and peaks at `t = 1/240`. -/
@[kb "stitzzeager2013" "Exercise 11.1.2, p. 903"]
theorem exer_11_1_2 :
    let V : ℝ → ℝ := fun t => 220 * √2 * sin (120 * π * t)
    (∀ t, |V t| ≤ 220 * √2) ∧ (∀ t, V (t + 1 / 60) = V t) ∧ V (1 / 240) = 220 * √2 := by
  intro V
  have h2 : (0 : ℝ) ≤ 220 * √2 := by positivity
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · show |220 * √2 * sin (120 * π * t)| ≤ 220 * √2
    rw [abs_mul, abs_of_nonneg h2]
    exact mul_le_of_le_one_right h2 (abs_sin_le_one _)
  · show 220 * √2 * sin (120 * π * (t + 1 / 60)) = 220 * √2 * sin (120 * π * t)
    have : 120 * π * (t + 1 / 60) = 120 * π * t + 2 * π := by ring
    rw [this, sin_add_two_pi]
  · show 220 * √2 * sin (120 * π * (1 / 240)) = 220 * √2
    have : 120 * π * (1 / 240) = π / 2 := by ring
    rw [this, sin_pi_div_two, mul_one]

/-- Stitz-Zeager Exercise 11.1.3: the London Eye height `67.5 sin (π t/15 - π/2) + 67.5` starts at ground
level, reaches `135` after 15 min, has period `30`, and stays in `[0, 135]`. -/
@[kb "stitzzeager2013" "Exercise 11.1.3, p. 903"]
theorem exer_11_1_3 :
    let h : ℝ → ℝ := fun t => 67.5 * sin (π / 15 * t - π / 2) + 67.5
    h 0 = 0 ∧ h 15 = 135 ∧ (∀ t, h (t + 30) = h t) ∧ ∀ t, 0 ≤ h t ∧ h t ≤ 135 := by
  intro h
  refine ⟨?_, ?_, fun t => ?_, fun t => ?_⟩
  · show 67.5 * sin (π / 15 * 0 - π / 2) + 67.5 = 0
    rw [mul_zero, zero_sub, sin_neg, sin_pi_div_two]; norm_num
  · show 67.5 * sin (π / 15 * 15 - π / 2) + 67.5 = 135
    have : π / 15 * 15 - π / 2 = π / 2 := by ring
    rw [this, sin_pi_div_two]; norm_num
  · show 67.5 * sin (π / 15 * (t + 30) - π / 2) + 67.5 = 67.5 * sin (π / 15 * t - π / 2) + 67.5
    have : π / 15 * (t + 30) - π / 2 = (π / 15 * t - π / 2) + 2 * π := by ring
    rw [this, sin_add_two_pi]
  · show 0 ≤ 67.5 * sin (π / 15 * t - π / 2) + 67.5 ∧ 67.5 * sin (π / 15 * t - π / 2) + 67.5 ≤ 135
    constructor <;> nlinarith [neg_one_le_sin (π / 15 * t - π / 2), sin_le_one (π / 15 * t - π / 2)]

/-- Stitz-Zeager Exercise 11.1.4: the horizontal displacement `67.5 cos (π t/15 - π/2)` of the passenger has
period `30`, starts at `0`, is `67.5` after 7.5 min, and with the height `h` of Exercise 3 stays on the
circle of radius `67.5` about the center. -/
@[kb "stitzzeager2013" "Exercise 11.1.4, p. 903"]
theorem exer_11_1_4 :
    let x : ℝ → ℝ := fun t => 67.5 * cos (π / 15 * t - π / 2)
    let h : ℝ → ℝ := fun t => 67.5 * sin (π / 15 * t - π / 2) + 67.5
    x 0 = 0 ∧ x 7.5 = 67.5 ∧ (∀ t, x (t + 30) = x t) ∧
      ∀ t, x t ^ 2 + (h t - 67.5) ^ 2 = 67.5 ^ 2 := by
  intro x h
  refine ⟨?_, ?_, fun t => ?_, fun t => ?_⟩
  · show 67.5 * cos (π / 15 * 0 - π / 2) = 0
    rw [mul_zero, zero_sub, cos_neg, cos_pi_div_two, mul_zero]
  · show 67.5 * cos (π / 15 * 7.5 - π / 2) = 67.5
    have : π / 15 * 7.5 - π / 2 = 0 := by ring
    rw [this, cos_zero, mul_one]
  · show 67.5 * cos (π / 15 * (t + 30) - π / 2) = 67.5 * cos (π / 15 * t - π / 2)
    have : π / 15 * (t + 30) - π / 2 = (π / 15 * t - π / 2) + 2 * π := by ring
    rw [this, cos_add_two_pi]
  · show (67.5 * cos (π / 15 * t - π / 2)) ^ 2 + (67.5 * sin (π / 15 * t - π / 2) + 67.5 - 67.5) ^ 2
      = 67.5 ^ 2
    nlinarith [sin_sq_add_cos_sq (π / 15 * t - π / 2)]

/-- Stitz-Zeager Exercise 11.1.5: the yo-yo height `28 sin (2π t/3 - π/2) + 30` starts at `2` inches, has
period `3`, and lies between `2` and `58`. -/
@[kb "stitzzeager2013" "Exercise 11.1.5, p. 903"]
theorem exer_11_1_5 :
    let h : ℝ → ℝ := fun t => 28 * sin (2 * π / 3 * t - π / 2) + 30
    h 0 = 2 ∧ h (3 / 2) = 58 ∧ (∀ t, h (t + 3) = h t) ∧ ∀ t, 2 ≤ h t ∧ h t ≤ 58 := by
  intro h
  refine ⟨?_, ?_, fun t => ?_, fun t => ?_⟩
  · show 28 * sin (2 * π / 3 * 0 - π / 2) + 30 = 2
    rw [mul_zero, zero_sub, sin_neg, sin_pi_div_two]; norm_num
  · show 28 * sin (2 * π / 3 * (3 / 2) - π / 2) + 30 = 58
    have : 2 * π / 3 * (3 / 2) - π / 2 = π / 2 := by ring
    rw [this, sin_pi_div_two]; norm_num
  · show 28 * sin (2 * π / 3 * (t + 3) - π / 2) + 30 = 28 * sin (2 * π / 3 * t - π / 2) + 30
    have : 2 * π / 3 * (t + 3) - π / 2 = (2 * π / 3 * t - π / 2) + 2 * π := by ring
    rw [this, sin_add_two_pi]
  · show 2 ≤ 28 * sin (2 * π / 3 * t - π / 2) + 30 ∧ 28 * sin (2 * π / 3 * t - π / 2) + 30 ≤ 58
    constructor <;> nlinarith [neg_one_le_sin (2 * π / 3 * t - π / 2), sin_le_one (2 * π / 3 * t - π / 2)]

/-- Stitz-Zeager Exercise 11.1.6(a): a 10 lb weight stretching a spring 2 ft gives `k = 5` lb/ft and mass
`5/16` slug (using `g = 32`), so the angular frequency is `√(k/m) = 4`. -/
@[kb "stitzzeager2013" "Exercise 11.1.6a, p. 903"]
theorem exer_11_1_6_a (k m : ℝ) (hk : k * 2 = 10) (hm : m * 32 = 10) :
    k = 5 ∧ m = 5 / 16 ∧ √(k / m) = 4 := by
  have hk' : k = 5 := by linarith
  have hm' : m = 5 / 16 := by linarith
  refine ⟨hk', hm', ?_⟩
  rw [hk', hm']
  rw [show (5 : ℝ) / (5 / 16) = 4 ^ 2 by norm_num]
  exact sqrt_sq (by norm_num)

/-- Stitz-Zeager Exercise 11.1.6(b): released from 1 ft below equilibrium at rest, `x(t) = sin (4t + π/2)`;
it starts at `1` with zero velocity, and first reaches equilibrium at `t = π/8` moving upward
(negative velocity). -/
@[kb "stitzzeager2013" "Exercise 11.1.6b, p. 903"]
theorem exer_11_1_6_b :
    let x : ℝ → ℝ := fun t => sin (4 * t + π / 2)
    x 0 = 1 ∧ deriv x 0 = 0 ∧ x (π / 8) = 0 ∧ deriv x (π / 8) < 0 ∧
      ∀ t, 0 ≤ t → x t = 0 → π / 8 ≤ t := by
  intro x
  have hd : ∀ t, deriv x t = 4 * cos (4 * t + π / 2) := by
    intro t
    have := x11_deriv_sin 1 4 (π / 2) t
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show sin (4 * 0 + π / 2) = 1
    simp
  · rw [hd]; simp
  · show sin (4 * (π / 8) + π / 2) = 0
    have : 4 * (π / 8) + π / 2 = π := by ring
    rw [this, sin_pi]
  · rw [hd]
    have : 4 * (π / 8) + π / 2 = π := by ring
    rw [this, cos_pi]; norm_num
  · intro t ht h0
    change sin (4 * t + π / 2) = 0 at h0
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h0
    have hpi := pi_pos
    have hn1 : (0 : ℝ) < n := by
      by_contra hc
      push Not at hc
      nlinarith
    have : (1 : ℝ) ≤ n := by
      have : (0 : ℤ) < n := by exact_mod_cast hn1
      exact_mod_cast this
    nlinarith

/-- Stitz-Zeager Exercise 11.1.6(c): released 6 in above equilibrium moving down at 2 ft/s,
`x(t) = (√2/2) sin (4t + 7π/4)`; the initial data hold, and the object crosses equilibrium heading down
(positive velocity) exactly at `t = π/16 + kπ/2`, the third time being `17π/16`. -/
@[kb "stitzzeager2013" "Exercise 11.1.6c, p. 903"]
theorem exer_11_1_6_c :
    let x : ℝ → ℝ := fun t => √2 / 2 * sin (4 * t + 7 * π / 4)
    x 0 = -1 / 2 ∧ deriv x 0 = 2 ∧
      (∀ t : ℝ, 0 < t → (x t = 0 ∧ 0 < deriv x t ↔ ∃ k : ℕ, t = π / 16 + k * (π / 2))) ∧
      17 * π / 16 = π / 16 + (2 : ℕ) * (π / 2) := by
  intro x
  have hd : ∀ t, deriv x t = √2 / 2 * 4 * cos (4 * t + 7 * π / 4) := fun t =>
    x11_deriv_sin (√2 / 2) 4 (7 * π / 4) t
  have h22 : √2 / 2 * (√2 / 2) = 1 / 2 := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hs : 0 < √2 := by positivity
  have hpi := pi_pos
  refine ⟨?_, ?_, ?_, by push_cast; ring⟩
  · show √2 / 2 * sin (4 * 0 + 7 * π / 4) = -1 / 2
    have : (4 : ℝ) * 0 + 7 * π / 4 = -(π / 4) + 2 * π := by ring
    rw [this, sin_add_two_pi, sin_neg, sin_pi_div_four]
    nlinarith
  · rw [hd]
    have : (4 : ℝ) * 0 + 7 * π / 4 = -(π / 4) + 2 * π := by ring
    rw [this, cos_add_two_pi, cos_neg, cos_pi_div_four]
    nlinarith
  · intro t ht
    show (√2 / 2 * sin (4 * t + 7 * π / 4) = 0 ∧ 0 < deriv x t) ↔ _
    rw [hd]
    constructor
    · rintro ⟨h0, hpos⟩
      have h0' : sin (4 * t + 7 * π / 4) = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exfalso; linarith
        · exact h
      obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h0'
      have hc : 0 < cos (4 * t + 7 * π / 4) := by
        by_contra hc; push Not at hc
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ √2 / 2 * 4) (neg_nonneg.mpr hc)]
      rw [← hn] at hc
      have hev : Even n := by
        by_contra hodd
        rw [Int.not_even_iff_odd] at hodd
        obtain ⟨m, hm⟩ := hodd
        have : (n : ℝ) * π = (m : ℝ) * (2 * π) + π := by rw [hm]; push_cast; ring
        rw [this, cos_int_mul_two_pi_add_pi] at hc
        linarith
      obtain ⟨m, hm⟩ := hev
      have hm1 : (0 : ℤ) < m := by
        by_contra hc; push Not at hc
        have : (n : ℝ) ≤ 0 := by exact_mod_cast (by omega : n ≤ 0)
        nlinarith
      obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ m - 1)
      refine ⟨j, ?_⟩
      have hm' : (n : ℝ) = 2 * (j + 1) := by
        have : n = 2 * ((j : ℤ) + 1) := by omega
        rw [this]; push_cast; ring
      nlinarith
    · rintro ⟨k, hk⟩
      have harg : 4 * t + 7 * π / 4 = ((2 * (k + 1) : ℕ) : ℤ) * π := by
        rw [hk]; push_cast; ring
      have hs0 : sin (4 * t + 7 * π / 4) = 0 := by rw [harg]; exact sin_int_mul_pi _
      have hc1 : cos (4 * t + 7 * π / 4) = 1 := by
        have : 4 * t + 7 * π / 4 = ((k + 1 : ℕ) : ℝ) * (2 * π) := by rw [hk]; push_cast; ring
        rw [this]; exact cos_nat_mul_two_pi _
      refine ⟨by rw [hs0, mul_zero], ?_⟩
      rw [hc1]; positivity

/-- Stitz-Zeager Exercise 11.1.7(a): a pendulum of length `l` with initial angle `θ₀` is modeled by
`θ₀ sin (√(g/l) t + π/2)`; it starts at `θ₀` and has period `2π√(l/g)`. -/
@[kb "stitzzeager2013" "Exercise 11.1.7a, p. 904"]
theorem exer_11_1_7_a (θ₀ g l : ℝ) (hg : 0 < g) (hl : 0 < l) :
    let θ : ℝ → ℝ := fun t => θ₀ * sin (√(g / l) * t + π / 2)
    θ 0 = θ₀ ∧ ∀ t, θ (t + 2 * π * √(l / g)) = θ t := by
  intro θ
  refine ⟨?_, fun t => ?_⟩
  · show θ₀ * sin (√(g / l) * 0 + π / 2) = θ₀
    simp
  · show θ₀ * sin (√(g / l) * (t + 2 * π * √(l / g)) + π / 2) = θ₀ * sin (√(g / l) * t + π / 2)
    have h1 : √(g / l) * √(l / g) = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show g / l * (l / g) = 1 by field_simp]
      exact Real.sqrt_one
    have : √(g / l) * (t + 2 * π * √(l / g)) + π / 2 = (√(g / l) * t + π / 2) + 2 * π := by
      linear_combination (2 * π) * h1
    rw [this, sin_add_two_pi]

/-- Stitz-Zeager Exercise 11.1.7(b): the clock pendulum released at `15° = π/12` with period `1/2` second
has displacement `(π/12) sin (4π t + π/2)`; it starts at `π/12` and has period `1/2`. -/
@[kb "stitzzeager2013" "Exercise 11.1.7b, p. 904"]
theorem exer_11_1_7_b :
    let θ : ℝ → ℝ := fun t => π / 12 * sin (4 * π * t + π / 2)
    θ 0 = π / 12 ∧ θ (1 / 8) = 0 ∧ ∀ t, θ (t + 1 / 2) = θ t := by
  intro θ
  refine ⟨?_, ?_, fun t => ?_⟩
  · show π / 12 * sin (4 * π * 0 + π / 2) = π / 12
    simp
  · show π / 12 * sin (4 * π * (1 / 8) + π / 2) = 0
    have : 4 * π * (1 / 8) + π / 2 = π := by ring
    rw [this, sin_pi, mul_zero]
  · show π / 12 * sin (4 * π * (t + 1 / 2) + π / 2) = π / 12 * sin (4 * π * t + π / 2)
    have : 4 * π * (t + 1 / 2) + π / 2 = (4 * π * t + π / 2) + 2 * π := by ring
    rw [this, sin_add_two_pi]

/-- Stitz-Zeager Exercise 11.1.8(c): with the Lake Erie model `T(t) = 20.5 sin (π t/6 - π) + 53.5`, the
April 15 prediction `T(4.5)` is about `39.00` and the September 15 prediction `T(9.5)` is about `73.30`
(ERRATUM: book says `73.38`, correct is `73.30`). -/
@[kb "stitzzeager2013" "Exercise 11.1.8c, p. 905"]
theorem exer_11_1_8_c :
    let T : ℝ → ℝ := fun t => 20.5 * sin (π / 6 * t - π) + 53.5
    38.99 < T 4.5 ∧ T 4.5 < 39.01 ∧ 73.29 < T 9.5 ∧ T 9.5 < 73.31 := by
  intro T
  have h2a : (1.414 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2b : √2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3a : (1.732 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3b : √3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have e1 : π / 6 * 4.5 - π = -(π / 4) := by ring
  have e2 : π / 6 * 9.5 - π = π / 3 + π / 4 := by ring
  have s2 : sin (π / 3 + π / 4) = √3 / 2 * (√2 / 2) + 1 / 2 * (√2 / 2) := by
    rw [sin_add, sin_pi_div_three, cos_pi_div_four, cos_pi_div_three, sin_pi_div_four]
  have hT1 : T 4.5 = 20.5 * (-(√2 / 2)) + 53.5 := by
    show 20.5 * sin (π / 6 * 4.5 - π) + 53.5 = _
    rw [e1, sin_neg, sin_pi_div_four]
  have hT2 : T 9.5 = 20.5 * (√3 / 2 * (√2 / 2) + 1 / 2 * (√2 / 2)) + 53.5 := by
    show 20.5 * sin (π / 6 * 9.5 - π) + 53.5 = _
    rw [e2, s2]
  rw [hT1, hT2]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Stitz-Zeager Exercise 11.1.9(c): with the moon model `F(t) = 0.475 sin (π t/15) + 0.505`, the predicted
illuminated fraction on June 1 is about `0.60`. -/
@[kb "stitzzeager2013" "Exercise 11.1.9c, p. 905"]
theorem exer_11_1_9_c :
    let F : ℝ → ℝ := fun t => 0.475 * sin (π / 15 * t) + 0.505
    0.6 < F 1 ∧ F 1 < 0.61 := by
  intro F
  have h1 := pi_gt_d2
  have h2 := pi_lt_d2
  have hx : 0 < π / 15 * 1 := by positivity
  have hx1 : π / 15 * 1 ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube hx
  have hs' := Real.sin_le hx.le
  show 0.6 < 0.475 * sin (π / 15 * 1) + 0.505 ∧ 0.475 * sin (π / 15 * 1) + 0.505 < 0.61
  constructor <;> nlinarith [mul_pos hx hx, mul_pos (mul_pos hx hx) hx]

end UndergradKB.Precalculus.Course
