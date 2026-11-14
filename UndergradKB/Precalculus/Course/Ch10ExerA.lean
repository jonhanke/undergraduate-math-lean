import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers, Section 10.1 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 10.1 -/

/-- Stitz-Zeager Exercise 10.1.1: `63.75° = 63° 45' 0"`. -/
@[kb "stitzzeager2013" "Exercise 10.1.1, p. 721"]
theorem exer_10_1_1 : (63.75 : ℝ) = 63 + 45 / 60 + 0 / 3600 := by norm_num

/-- Stitz-Zeager Exercise 10.1.2: `200.325° = 200° 19' 30"`. -/
@[kb "stitzzeager2013" "Exercise 10.1.2, p. 721"]
theorem exer_10_1_2 : (200.325 : ℝ) = 200 + 19 / 60 + 30 / 3600 := by norm_num

/-- Stitz-Zeager Exercise 10.1.3: `-317.06° = -317° 3' 36"`. -/
@[kb "stitzzeager2013" "Exercise 10.1.3, p. 721"]
theorem exer_10_1_3 : (-317.06 : ℝ) = -(317 + 3 / 60 + 36 / 3600) := by norm_num

/-- Stitz-Zeager Exercise 10.1.4: `179.999°` is `179° 59' 56"` to the nearest second. -/
@[kb "stitzzeager2013" "Exercise 10.1.4, p. 721"]
theorem exer_10_1_4 : |(179.999 : ℝ) - (179 + 59 / 60 + 56 / 3600)| ≤ 1 / 7200 := by
  rw [abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 10.1.5: `125° 50'` is `125.833°` to three decimals. -/
@[kb "stitzzeager2013" "Exercise 10.1.5, p. 721"]
theorem exer_10_1_5 : |((125 : ℝ) + 50 / 60) - 125.833| ≤ 0.0005 := by
  rw [abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 10.1.6: `-32° 10' 12" = -32.17°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.6, p. 721"]
theorem exer_10_1_6 : -((32 : ℝ) + 10 / 60 + 12 / 3600) = -32.17 := by norm_num

/-- Stitz-Zeager Exercise 10.1.7: `502° 35'` is `502.583°` to three decimals. -/
@[kb "stitzzeager2013" "Exercise 10.1.7, p. 721"]
theorem exer_10_1_7 : |((502 : ℝ) + 35 / 60) - 502.583| ≤ 0.0005 := by
  rw [abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 10.1.8: `237° 58' 43"` is `237.979°` to three decimals. -/
@[kb "stitzzeager2013" "Exercise 10.1.8, p. 721"]
theorem exer_10_1_8 : |((237 : ℝ) + 58 / 60 + 43 / 3600) - 237.979| ≤ 0.0005 := by
  rw [abs_le]; constructor <;> norm_num

/-- Stitz-Zeager Exercise 10.1.9: `330°` is a Quadrant IV angle (coterminal with `330` itself in
`(270, 360)`), coterminal with `690°` and `-30°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.9, p. 721"]
theorem exer_10_1_9 : (270 < (330 : ℝ) ∧ (330 : ℝ) < 360) ∧
    (∃ k : ℤ, (690 : ℝ) = 330 + 360 * k) ∧ (∃ k : ℤ, (-30 : ℝ) = 330 + 360 * k) :=
  ⟨by norm_num, ⟨1, by norm_num⟩, ⟨-1, by norm_num⟩⟩

/-- Stitz-Zeager Exercise 10.1.10: `-135°` is a Quadrant III angle (coterminal with `225°` in
`(180, 270)`), also coterminal with `-495°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.10, p. 721"]
theorem exer_10_1_10 : (180 < (225 : ℝ) ∧ (225 : ℝ) < 270) ∧
    (∃ k : ℤ, (-135 : ℝ) = 225 + 360 * k) ∧ (∃ k : ℤ, (-495 : ℝ) = 225 + 360 * k) :=
  ⟨by norm_num, ⟨-1, by norm_num⟩, ⟨-2, by norm_num⟩⟩

/-- Stitz-Zeager Exercise 10.1.12: `405°` is a Quadrant I angle: it is coterminal with `45°`
and `-315°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.12, p. 721"]
theorem exer_10_1_12 : (0 < (45 : ℝ) ∧ (45 : ℝ) < 90) ∧
    (∃ k : ℤ, (405 : ℝ) = 45 + 360 * k) ∧ (∃ k : ℤ, (-315 : ℝ) = 45 + 360 * k) :=
  ⟨by norm_num, ⟨1, by norm_num⟩, ⟨-1, by norm_num⟩⟩

/-- Stitz-Zeager Exercise 10.1.13: `-270°` lies on the positive `y`-axis: it is coterminal with `90°`
and `-630°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.13, p. 721"]
theorem exer_10_1_13 : (∃ k : ℤ, (-270 : ℝ) = 90 + 360 * k) ∧
    (∃ k : ℤ, (90 : ℝ) = 90 + 360 * k) ∧ (∃ k : ℤ, (-630 : ℝ) = 90 + 360 * k) :=
  ⟨⟨-1, by norm_num⟩, ⟨0, by norm_num⟩, ⟨-2, by norm_num⟩⟩

/-- Stitz-Zeager Exercise 10.1.14: `5π/6` is a Quadrant II angle, coterminal with `17π/6` and
`-7π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.1.14, p. 721"]
theorem exer_10_1_14 : (π / 2 < 5 * π / 6 ∧ 5 * π / 6 < π) ∧
    (∃ k : ℤ, 17 * π / 6 = 5 * π / 6 + 2 * π * k) ∧ (∃ k : ℤ, -(7 * π / 6) = 5 * π / 6 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨1, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.15: `-11π/3` is a Quadrant I angle: coterminal with `π/3` and `-5π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.1.15, p. 721"]
theorem exer_10_1_15 : (0 < π / 3 ∧ π / 3 < π / 2) ∧
    (∃ k : ℤ, -(11 * π / 3) = π / 3 + 2 * π * k) ∧ (∃ k : ℤ, -(5 * π / 3) = π / 3 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨-2, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.16: `5π/4` is a Quadrant III angle, coterminal with `13π/4` and
`-3π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.1.16, p. 721"]
theorem exer_10_1_16 : (π < 5 * π / 4 ∧ 5 * π / 4 < 3 * π / 2) ∧
    (∃ k : ℤ, 13 * π / 4 = 5 * π / 4 + 2 * π * k) ∧ (∃ k : ℤ, -(3 * π / 4) = 5 * π / 4 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨1, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.19: `7π/2` lies on the negative `y`-axis: it is coterminal with `3π/2`
and `-π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.1.19, p. 721"]
theorem exer_10_1_19 : (∃ k : ℤ, 7 * π / 2 = 3 * π / 2 + 2 * π * k) ∧
    (∃ k : ℤ, 3 * π / 2 = 3 * π / 2 + 2 * π * k) ∧ (∃ k : ℤ, -(π / 2) = 3 * π / 2 + 2 * π * k) :=
  ⟨⟨1, by push_cast; ring⟩, ⟨0, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.24: `3π` lies on the negative `x`-axis: it is coterminal with `π`
and `-π`. -/
@[kb "stitzzeager2013" "Exercise 10.1.24, p. 721"]
theorem exer_10_1_24 : (∃ k : ℤ, 3 * π = π + 2 * π * k) ∧ (∃ k : ℤ, π = π + 2 * π * k) ∧
    (∃ k : ℤ, -π = π + 2 * π * k) :=
  ⟨⟨1, by push_cast; ring⟩, ⟨0, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.27: `15π/4` is a Quadrant IV angle: coterminal with `7π/4` and `-π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.1.27, p. 721"]
theorem exer_10_1_27 : (3 * π / 2 < 7 * π / 4 ∧ 7 * π / 4 < 2 * π) ∧
    (∃ k : ℤ, 15 * π / 4 = 7 * π / 4 + 2 * π * k) ∧ (∃ k : ℤ, -(π / 4) = 7 * π / 4 + 2 * π * k) := by
  have := Real.pi_pos
  refine ⟨⟨by linarith, by linarith⟩, ⟨1, by push_cast; ring⟩, ⟨-1, by push_cast; ring⟩⟩

/-- Stitz-Zeager Exercise 10.1.30: `240° = 4π/3` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.30, p. 721"]
theorem exer_10_1_30 : (240 : ℝ) * (π / 180) = 4 * π / 3 := by ring

/-- Stitz-Zeager Exercise 10.1.31: `135° = 3π/4` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.31, p. 721"]
theorem exer_10_1_31 : (135 : ℝ) * (π / 180) = 3 * π / 4 := by ring

/-- Stitz-Zeager Exercise 10.1.32: `-270° = -3π/2` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.32, p. 721"]
theorem exer_10_1_32 : (-270 : ℝ) * (π / 180) = -(3 * π / 2) := by ring

/-- Stitz-Zeager Exercise 10.1.33: `-315° = -7π/4` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.33, p. 721"]
theorem exer_10_1_33 : (-315 : ℝ) * (π / 180) = -(7 * π / 4) := by ring

/-- Stitz-Zeager Exercise 10.1.34: `150° = 5π/6` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.34, p. 721"]
theorem exer_10_1_34 : (150 : ℝ) * (π / 180) = 5 * π / 6 := by ring

/-- Stitz-Zeager Exercise 10.1.36: `-225° = -5π/4` radians. -/
@[kb "stitzzeager2013" "Exercise 10.1.36, p. 721"]
theorem exer_10_1_36 : (-225 : ℝ) * (π / 180) = -(5 * π / 4) := by ring

/-- Stitz-Zeager Exercise 10.1.37: `π` radians is `180°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.37, p. 721"]
theorem exer_10_1_37 : π * (180 / π) = 180 := by
  field_simp

/-- Stitz-Zeager Exercise 10.1.38: `-2π/3` radians is `-120°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.38, p. 721"]
theorem exer_10_1_38 : (-(2 * π / 3)) * (180 / π) = -120 := by
  field_simp; ring

/-- Stitz-Zeager Exercise 10.1.39: `7π/6` radians is `210°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.39, p. 721"]
theorem exer_10_1_39 : (7 * π / 6) * (180 / π) = 210 := by
  field_simp; ring

/-- Stitz-Zeager Exercise 10.1.40: `11π/6` radians is `330°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.40, p. 721"]
theorem exer_10_1_40 : (11 * π / 6) * (180 / π) = 330 := by
  field_simp; ring

/-- Stitz-Zeager Exercise 10.1.42: `5π/3` radians is `300°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.42, p. 721"]
theorem exer_10_1_42 : (5 * π / 3) * (180 / π) = 300 := by
  field_simp; ring

/-- Stitz-Zeager Exercise 10.1.43: `-π/6` radians is `-30°`. -/
@[kb "stitzzeager2013" "Exercise 10.1.43, p. 721"]
theorem exer_10_1_43 : (-(π / 6)) * (180 / π) = -30 := by
  field_simp; ring

/-- Stitz-Zeager Exercise 10.1.50: a yo-yo of diameter `2.25` in spinning at `4500` rpm has edge
speed about `30.12` mph (`63360` inches per mile). -/
@[kb "stitzzeager2013" "Exercise 10.1.50, p. 722"]
theorem exer_10_1_50 : |(2 * π * (2.25 / 2) * 4500 * 60 / 63360 : ℝ) - 30.12| ≤ 0.01 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  rw [abs_le]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 10.1.51: edge speed `42` mph of that yo-yo needs about `6274.52` rpm. -/
@[kb "stitzzeager2013" "Exercise 10.1.51, p. 722"]
theorem exer_10_1_51 :
    6274.51 < (42 * 63360 / (60 * (2 * π * (2.25 / 2))) : ℝ) ∧
      (42 * 63360 / (60 * (2 * π * (2.25 / 2))) : ℝ) < 6274.53 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hp : 0 < π := Real.pi_pos
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- Stitz-Zeager Exercise 10.1.52: a yo-yo on a `28` in string, one revolution per `3` s, moves at
about `3.33` mph. -/
@[kb "stitzzeager2013" "Exercise 10.1.52, p. 722"]
theorem exer_10_1_52 : |(2 * π * 28 / 3 * 3600 / 63360 : ℝ) - 3.33| ≤ 0.01 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  rw [abs_le]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 10.1.53: a point on the edge of a `2.5` in disk at `7200` rpm moves at about
`53.55` mph. -/
@[kb "stitzzeager2013" "Exercise 10.1.53, p. 722"]
theorem exer_10_1_53 : |(2 * π * (2.5 / 2) * 7200 * 60 / 63360 : ℝ) - 53.55| ≤ 0.01 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  rw [abs_le]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 10.1.54: the rock leaves the tread at the car's speed, `70` mph: the tire
turns at angular speed `70/r` and the edge speed is `r` times that. -/
@[kb "stitzzeager2013" "Exercise 10.1.54, p. 722"]
theorem exer_10_1_54 (r : ℝ) (hr : 0 < r) : r * (70 / r) = 70 := by
  field_simp

/-- Stitz-Zeager Exercise 10.1.55: riders on the Giant Wheel (radius `64` ft, two turns in `127` s)
travel at about `4.32` mph (`5280` ft per mile). -/
@[kb "stitzzeager2013" "Exercise 10.1.55, p. 722"]
theorem exer_10_1_55 : |(2 * (2 * π * 64) / 127 * 3600 / 5280 : ℝ) - 4.32| ≤ 0.01 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  rw [abs_le]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 10.1.57: the sector with angle `π/6`, radius `12` has area `12π`. -/
@[kb "stitzzeager2013" "Exercise 10.1.57, p. 723"]
theorem exer_10_1_57 : (1 / 2 : ℝ) * 12 ^ 2 * (π / 6) = 12 * π := by ring

/-- Stitz-Zeager Exercise 10.1.58: the sector with angle `5π/4`, radius `100` has area `6250π`. -/
@[kb "stitzzeager2013" "Exercise 10.1.58, p. 723"]
theorem exer_10_1_58 : (1 / 2 : ℝ) * 100 ^ 2 * (5 * π / 4) = 6250 * π := by ring

/-- Stitz-Zeager Exercise 10.1.59: the sector with angle `330°`, radius `9.3` has area `79.2825π`,
about `249.07`. -/
@[kb "stitzzeager2013" "Exercise 10.1.59, p. 723"]
theorem exer_10_1_59 : (1 / 2 : ℝ) * 9.3 ^ 2 * (330 * (π / 180)) = 79.2825 * π ∧
    |79.2825 * π - 249.07| ≤ 0.005 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  refine ⟨by ring, ?_⟩
  rw [abs_le]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 10.1.60: the sector with angle `π`, radius `1` has area `π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.1.60, p. 723"]
theorem exer_10_1_60 : (1 / 2 : ℝ) * 1 ^ 2 * π = π / 2 := by ring

/-- Stitz-Zeager Exercise 10.1.61: the sector with angle `240°`, radius `5` has area `50π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.1.61, p. 723"]
theorem exer_10_1_61 : (1 / 2 : ℝ) * 5 ^ 2 * (240 * (π / 180)) = 50 * π / 3 := by ring

/-- Stitz-Zeager Exercise 10.1.62: the sector with angle `1°`, radius `117` has area `38.025π`,
about `119.46`. -/
@[kb "stitzzeager2013" "Exercise 10.1.62, p. 723"]
theorem exer_10_1_62 : (1 / 2 : ℝ) * 117 ^ 2 * (1 * (π / 180)) = 38.025 * π ∧
    |38.025 * π - 119.46| ≤ 0.005 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  refine ⟨by ring, ?_⟩
  rw [abs_le]; constructor <;> nlinarith

/-- Stitz-Zeager Exercise 10.1.63: lengthening a circle of radius `r` to radius `r + 1` adds `2π`
to its circumference, for every `r`. -/
@[kb "stitzzeager2013" "Exercise 10.1.63, p. 723"]
theorem exer_10_1_63 (r : ℝ) : 2 * π * (r + 1) - 2 * π * r = 2 * π := by ring

end UndergradKB.Precalculus.Course
