import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7), Sections 10.1 and 10.2 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 10.1 -/

/-- Stitz-Zeager Exercise 10.1.11: `120°` is a Quadrant II angle, coterminal with `480°` and `-240°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.11, p. 721"]
theorem exer_10_1_11 : (90 < (120 : ℝ) ∧ (120 : ℝ) < 180) ∧
    (∃ k : ℤ, (480 : ℝ) = 120 + 360 * k) ∧ (∃ k : ℤ, (-240 : ℝ) = 120 + 360 * k) :=
  ⟨by norm_num, ⟨1, by norm_num⟩, ⟨-1, by norm_num⟩⟩

/-- Stitz-Zeager Exercise 10.1.17: `3π/4` is a Quadrant II angle, coterminal with `11π/4` and `-5π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.1.17, p. 721"]
theorem exer_10_1_17 : (π / 2 < 3 * π / 4 ∧ 3 * π / 4 < π) ∧
    (∃ k : ℤ, 11 * π / 4 = 3 * π / 4 + 2 * π * k) ∧ (∃ k : ℤ, -(5 * π / 4) = 3 * π / 4 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨1, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.18: `-π/3` is a Quadrant IV angle (coterminal with `5π/3`, which lies in
`(3π/2, 2π)`) and with `-7π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.1.18, p. 721"]
theorem exer_10_1_18 : (3 * π / 2 < 5 * π / 3 ∧ 5 * π / 3 < 2 * π) ∧
    (∃ k : ℤ, -(π / 3) = 5 * π / 3 + 2 * π * k) ∧ (∃ k : ℤ, -(7 * π / 3) = 5 * π / 3 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨-1, by push_cast; ring⟩, ⟨-2, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.20: `π/4` is a Quadrant I angle, coterminal with `9π/4` and `-7π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.1.20, p. 721"]
theorem exer_10_1_20 : (0 < π / 4 ∧ π / 4 < π / 2) ∧
    (∃ k : ℤ, 9 * π / 4 = π / 4 + 2 * π * k) ∧ (∃ k : ℤ, -(7 * π / 4) = π / 4 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨1, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.21: `-π/2` lies on the negative `y`-axis: coterminal with `3π/2` and `-5π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.1.21, p. 721"]
theorem exer_10_1_21 : (∃ k : ℤ, -(π / 2) = 3 * π / 2 + 2 * π * k) ∧
    (∃ k : ℤ, 3 * π / 2 = 3 * π / 2 + 2 * π * k) ∧ (∃ k : ℤ, -(5 * π / 2) = 3 * π / 2 + 2 * π * k) :=
  ⟨⟨-1, by push_cast; ring⟩, ⟨0, by push_cast; ring⟩, ⟨-2, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.22: `7π/6` is a Quadrant III angle, coterminal with `19π/6` and `-5π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.1.22, p. 721"]
theorem exer_10_1_22 : (π < 7 * π / 6 ∧ 7 * π / 6 < 3 * π / 2) ∧
    (∃ k : ℤ, 19 * π / 6 = 7 * π / 6 + 2 * π * k) ∧ (∃ k : ℤ, -(5 * π / 6) = 7 * π / 6 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨1, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.23: `-5π/3` is a Quadrant I angle: coterminal with `π/3` and `-11π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.1.23, p. 721"]
theorem exer_10_1_23 : (0 < π / 3 ∧ π / 3 < π / 2) ∧
    (∃ k : ℤ, -(5 * π / 3) = π / 3 + 2 * π * k) ∧ (∃ k : ℤ, -(11 * π / 3) = π / 3 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨-1, by push_cast; ring⟩, ⟨-2, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.25: `-2π` lies on the positive `x`-axis (a multiple of `2π`): coterminal with
`2π` and `-4π`. -/
@[kb "stitzzeager2013" "Exercise 10.1.25, p. 721"]
theorem exer_10_1_25 : (∃ k : ℤ, -(2 * π) = 2 * π * k) ∧ (∃ k : ℤ, 2 * π = -(2 * π) + 2 * π * k) ∧
    (∃ k : ℤ, -(4 * π) = -(2 * π) + 2 * π * k) :=
  ⟨⟨-1, by push_cast; ring⟩, ⟨2, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.26: `-π/4` is a Quadrant IV angle (coterminal with `7π/4`) and with `-9π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.1.26, p. 721"]
theorem exer_10_1_26 : (3 * π / 2 < 7 * π / 4 ∧ 7 * π / 4 < 2 * π) ∧
    (∃ k : ℤ, -(π / 4) = 7 * π / 4 + 2 * π * k) ∧ (∃ k : ℤ, -(9 * π / 4) = 7 * π / 4 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨-1, by push_cast; ring⟩, ⟨-2, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.28: `-13π/6` is a Quadrant IV angle (coterminal with `11π/6`) and with `-π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.1.28, p. 721"]
theorem exer_10_1_28 : (3 * π / 2 < 11 * π / 6 ∧ 11 * π / 6 < 2 * π) ∧
    (∃ k : ℤ, -(13 * π / 6) = 11 * π / 6 + 2 * π * k) ∧ (∃ k : ℤ, -(π / 6) = 11 * π / 6 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨-2, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.29: `0°` is `0` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.29, p. 721"]
theorem exer_10_1_29 : (0 : ℝ) * (π / 180) = 0 := by ring

/-- Stitz-Zeager Exercise 10.1.35: `45° = π/4` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.35, p. 721"]
theorem exer_10_1_35 : (45 : ℝ) * (π / 180) = π / 4 := by ring

/-- Stitz-Zeager Exercise 10.1.41: `π/3` radians is `60°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.41, p. 721"]
theorem exer_10_1_41 : (π / 3) * (180 / π) = 60 := by
  field_simp; ring

/-- Stitz-Zeager Exercise 10.1.44: `π/2` radians is `90°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.44, p. 721"]
theorem exer_10_1_44 : (π / 2) * (180 / π) = 90 := by
  field_simp; ring

/-- Stitz-Zeager Exercise 10.1.56: if the arc `s = rθ` and the sector area `A` satisfy
`A / (πr²) = s / (2πr)`, then `A = r²θ/2`. -/
@[kb "stitzzeager2013" "Exercise 10.1.56, p. 722"]
theorem exer_10_1_56 : ∀ r θ A s : ℝ, 0 < r → s = r * θ → A / (π * r ^ 2) = s / (2 * π * r) →
    A = 1 / 2 * r ^ 2 * θ := by
  intro r θ A s hr hs h
  have hp : π ≠ 0 := Real.pi_ne_zero
  have hr' : r ≠ 0 := hr.ne'
  have h1 : A = π * r ^ 2 * (s / (2 * π * r)) := by rw [← h]; field_simp
  rw [h1, hs]; field_simp

/-! ## Section 10.2 -/

/-- Stitz-Zeager Exercise 10.2.1: `cos 0 = 1` and `sin 0 = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.2.1, p. 748"]
theorem exer_10_2_1 : cos 0 = 1 ∧ sin 0 = 0 := by simp

/-- Stitz-Zeager Exercise 10.2.3: `cos(π/3) = 1/2` and `sin(π/3) = √3/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.3, p. 748"]
theorem exer_10_2_3 : cos (π / 3) = 1 / 2 ∧ sin (π / 3) = √3 / 2 :=
  ⟨cos_pi_div_three, sin_pi_div_three⟩

/-- Stitz-Zeager Exercise 10.2.4: `cos(π/2) = 0` and `sin(π/2) = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.2.4, p. 748"]
theorem exer_10_2_4 : cos (π / 2) = 0 ∧ sin (π / 2) = 1 := by simp

/-- Stitz-Zeager Exercise 10.2.7: `cos π = -1` and `sin π = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.2.7, p. 748"]
theorem exer_10_2_7 : cos π = -1 ∧ sin π = 0 := by simp

/-- Stitz-Zeager Exercise 10.2.9: `cos(5π/4) = -√2/2` and `sin(5π/4) = -√2/2`. -/
@[kb "stitzzeager2013" "Exercise 10.2.9, p. 748"]
theorem exer_10_2_9 : cos (5 * π / 4) = -(√2 / 2) ∧ sin (5 * π / 4) = -(√2 / 2) := by
  have h : 5 * π / 4 = π / 4 + π := by ring
  rw [h, cos_add_pi, sin_add_pi, cos_pi_div_four, sin_pi_div_four]
  exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.53: `sin(π°) ≈ 0.055` (here `π°` is `π² / 180` radians). -/
@[kb "stitzzeager2013" "Exercise 10.2.53, p. 749"]
theorem exer_10_2_53 : |sin (π * (π / 180)) - 0.055| ≤ 0.0005 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hx1 : (0.05483 : ℝ) < π * (π / 180) := by nlinarith
  have hx2 : π * (π / 180) < 0.05484 := by nlinarith
  have hpos : |π * (π / 180)| = π * (π / 180) := abs_of_pos (by linarith)
  have hb := Real.sin_bound (x := π * (π / 180)) (by rw [hpos]; linarith)
  rw [hpos, abs_le] at hb
  have h3 : (π * (π / 180)) ^ 3 < 0.00016493 := by
    calc (π * (π / 180)) ^ 3 < 0.05484 ^ 3 := by gcongr
      _ < 0.00016493 := by norm_num
  have h3' : (0.0001648 : ℝ) < (π * (π / 180)) ^ 3 := by
    calc (0.0001648 : ℝ) < 0.05483 ^ 3 := by norm_num
      _ < (π * (π / 180)) ^ 3 := by gcongr
  have h5 : (π * (π / 180)) ^ 5 < 0.00001 := by
    calc (π * (π / 180)) ^ 5 < 0.05484 ^ 5 := by gcongr
      _ < 0.00001 := by norm_num
  rw [abs_le]
  constructor <;> nlinarith [hb.1, hb.2]

/-- Stitz-Zeager Exercise 10.2.65: for the point `P(-7, 24)`, `r = 25`, so `cos θ = -7/25`, `sin θ = 24/25`. -/
@[kb "stitzzeager2013" "Exercise 10.2.65, p. 750"]
theorem exer_10_2_65 :
    -7 / √((-7) ^ 2 + 24 ^ 2) = -7 / 25 ∧ 24 / √((-7) ^ 2 + 24 ^ 2) = 24 / 25 := by
  have h : √(((-7 : ℝ)) ^ 2 + 24 ^ 2) = 25 := by
    rw [show ((-7 : ℝ)) ^ 2 + 24 ^ 2 = 25 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [h]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.66: for the point `Q(3, 4)`, `r = 5`, so `cos θ = 3/5`, `sin θ = 4/5`. -/
@[kb "stitzzeager2013" "Exercise 10.2.66, p. 750"]
theorem exer_10_2_66 : 3 / √(3 ^ 2 + 4 ^ 2) = 3 / 5 ∧ 4 / √(3 ^ 2 + 4 ^ 2) = 4 / 5 := by
  have h : √((3 : ℝ) ^ 2 + 4 ^ 2) = 5 := by
    rw [show (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [h]; exact ⟨rfl, rfl⟩

/-- Stitz-Zeager Exercise 10.2.67: for the point `R(5, -9)`, `r = √106`, so `cos θ = 5√106/106`,
`sin θ = -9√106/106`. -/
@[kb "stitzzeager2013" "Exercise 10.2.67, p. 750"]
theorem exer_10_2_67 : 5 / √(5 ^ 2 + (-9) ^ 2) = 5 * √106 / 106 ∧
    -9 / √(5 ^ 2 + (-9) ^ 2) = -(9 * √106 / 106) := by
  have h : √((5 : ℝ) ^ 2 + (-9) ^ 2) = √106 := by norm_num
  have h2 : √106 ^ 2 = 106 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √106 := by positivity
  rw [h]
  constructor <;> field_simp <;> nlinarith [h2]

/-- Stitz-Zeager Exercise 10.2.68: for the point `T(-2, -11)`, `r = 5√5`, so `cos θ = -2√5/25`,
`sin θ = -11√5/25`. -/
@[kb "stitzzeager2013" "Exercise 10.2.68, p. 750"]
theorem exer_10_2_68 : -2 / √((-2) ^ 2 + (-11) ^ 2) = -(2 * √5 / 25) ∧
    -11 / √((-2) ^ 2 + (-11) ^ 2) = -(11 * √5 / 25) := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √5 := by positivity
  have h : √(((-2 : ℝ)) ^ 2 + (-11) ^ 2) = 5 * √5 := by
    rw [show ((-2 : ℝ)) ^ 2 + (-11) ^ 2 = (5 * √5) ^ 2 by rw [mul_pow, h5]; norm_num]
    exact Real.sqrt_sq (by positivity)
  rw [h]
  constructor <;> field_simp <;> nlinarith [h5]

/-- Stitz-Zeager Exercise 10.2.69: the yo-yo edge (radius `2.25/2 = 1.125` in) spinning at `4500` rpm has
`ω = 4500 · 2π = 9000π` radians per minute. -/
@[kb "stitzzeager2013" "Exercise 10.2.69, p. 750"]
theorem exer_10_2_69 : (2.25 : ℝ) / 2 = 1.125 ∧ (4500 : ℝ) * (2 * π) = 9000 * π := by
  constructor <;> ring_nf

/-- Stitz-Zeager Exercise 10.2.70: the Around-the-World yo-yo (radius `28`, one turn per `3` s) has
`ω = 2π/3` radians per second. -/
@[kb "stitzzeager2013" "Exercise 10.2.70, p. 750"]
theorem exer_10_2_70 : (1 : ℝ) * (2 * π) / 3 = 2 * π / 3 := by ring

/-- Stitz-Zeager Exercise 10.2.71: the hard drive edge (radius `2.5/2 = 1.25` in) at `7200` rpm has
`ω = 14400π` radians per minute. -/
@[kb "stitzzeager2013" "Exercise 10.2.71, p. 750"]
theorem exer_10_2_71 : (2.5 : ℝ) / 2 = 1.25 ∧ (7200 : ℝ) * (2 * π) = 14400 * π := by
  constructor <;> ring_nf

/-- Stitz-Zeager Exercise 10.2.72: the Giant Wheel (radius `64` ft, `2` turns in `127` s) has
`ω = 4π/127` radians per second. -/
@[kb "stitzzeager2013" "Exercise 10.2.72, p. 751"]
theorem exer_10_2_72 : (128 : ℝ) / 2 = 64 ∧ (2 : ℝ) * (2 * π) / 127 = 4 * π / 127 := by
  constructor <;> ring_nf

/-- Stitz-Zeager Exercise 10.2.73: `√0/2, √1/2, √2/2, √3/2, √4/2` are the values `sin 0`, `sin(π/6)`,
`sin(π/4)`, `sin(π/3)`, `sin(π/2)`. -/
@[kb "stitzzeager2013" "Exercise 10.2.73, p. 751"]
theorem exer_10_2_73 : √0 / 2 = sin 0 ∧ √1 / 2 = sin (π / 6) ∧ √2 / 2 = sin (π / 4) ∧
    √3 / 2 = sin (π / 3) ∧ √4 / 2 = sin (π / 2) := by
  refine ⟨by simp, ?_, sin_pi_div_four.symm, sin_pi_div_three.symm, ?_⟩
  · rw [sin_pi_div_six]; simp
  · rw [sin_pi_div_two, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

/-- Stitz-Zeager Exercise 10.2.74: for complementary acute angles `α + β = π/2`: `sin α = cos β` and
`sin β = cos α`. -/
@[kb "stitzzeager2013" "Exercise 10.2.74, p. 751"]
theorem exer_10_2_74 : ∀ α β : ℝ, α + β = π / 2 → sin α = cos β ∧ sin β = cos α := by
  intro α β h
  have hα : α = π / 2 - β := by linarith
  have hβ : β = π / 2 - α := by linarith
  constructor
  · rw [hα, sin_pi_div_two_sub]
  · rw [hβ, sin_pi_div_two_sub]

end UndergradKB.Precalculus.Course
