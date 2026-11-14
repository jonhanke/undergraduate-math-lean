import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): worked examples, wave 5 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ### Helpers: signs of cosine and sine from the quadrant of a reduced angle -/

private theorem cs_shift (θ r : ℝ) (k : ℤ) (h : θ = r + k * (2 * π)) :
    cos θ = cos r ∧ sin θ = sin r := by
  subst h; exact ⟨cos_add_int_mul_two_pi r k, sin_add_int_mul_two_pi r k⟩

private theorem Q1 (θ r : ℝ) (k : ℤ) (h : θ = r + k * (2 * π)) (h1 : 0 < r) (h2 : r < π / 2) :
    0 < cos θ ∧ 0 < sin θ := by
  rw [(cs_shift θ r k h).1, (cs_shift θ r k h).2]
  exact ⟨cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h2⟩,
    sin_pos_of_pos_of_lt_pi h1 (by linarith [pi_pos])⟩

private theorem Q2 (θ r : ℝ) (k : ℤ) (h : θ = r + k * (2 * π)) (h1 : π / 2 < r) (h2 : r < π) :
    cos θ < 0 ∧ 0 < sin θ := by
  rw [(cs_shift θ r k h).1, (cs_shift θ r k h).2]
  exact ⟨cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith [pi_pos]),
    sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) h2⟩

private theorem Q3 (θ r : ℝ) (k : ℤ) (h : θ = r + k * (2 * π)) (h1 : π < r)
    (h2 : r < 3 * π / 2) : cos θ < 0 ∧ sin θ < 0 := by
  rw [(cs_shift θ r k h).1, (cs_shift θ r k h).2]
  have hs := sin_pos_of_pos_of_lt_pi (x := r - π) (by linarith) (by linarith [pi_pos])
  rw [sin_sub_pi] at hs
  exact ⟨cos_neg_of_pi_div_two_lt_of_lt (by linarith [pi_pos]) (by linarith), by linarith⟩

private theorem Q4 (θ r : ℝ) (k : ℤ) (h : θ = r + k * (2 * π)) (h1 : 3 * π / 2 < r)
    (h2 : r < 2 * π) : 0 < cos θ ∧ sin θ < 0 := by
  rw [(cs_shift θ r k h).1, (cs_shift θ r k h).2]
  have hc := cos_pos_of_mem_Ioo (x := r - 2 * π) ⟨by linarith, by linarith [pi_pos]⟩
  have hs := sin_neg_of_neg_of_neg_pi_lt (x := r - 2 * π) (by linarith [pi_pos])
    (by linarith [pi_pos])
  rw [cos_sub_two_pi] at hc
  rw [sin_sub_two_pi] at hs
  exact ⟨hc, hs⟩

/-! ### 10.1 Angles -/

/-- Stitz-Zeager Example 10.1.1(1): `111.371° = 111° 22' 15.6"`, which rounds to `111° 22' 16"`. -/
@[kb "stitzzeager2013" "Example 10.1.1, p. 708"]
theorem ex_10_1_1_a :
    (111 : ℚ) + 22 / 60 + 15.6 / 3600 = 111.371 ∧
      |(111 : ℚ) + 22 / 60 + 16 / 3600 - 111.371| < 1 / 7200 := by
  constructor
  · norm_num
  · rw [abs_lt]; constructor <;> norm_num

/-- Stitz-Zeager Example 10.1.1(2): `37° 28' 17" = 134897/3600 ° ≈ 37.471°`. -/
@[kb "stitzzeager2013" "Example 10.1.1, p. 708"]
theorem ex_10_1_1_b :
    (37 : ℚ) + 28 / 60 + 17 / 3600 = 134897 / 3600 ∧
      |(134897 / 3600 : ℚ) - 37.471| < 0.0005 := by
  constructor
  · norm_num
  · rw [abs_lt]; constructor <;> norm_num

/-- Stitz-Zeager Example 10.1.1(4): a supplement of `111.371°` is `68.629°` (and it is positive). -/
@[kb "stitzzeager2013" "Example 10.1.1, p. 708"]
theorem ex_10_1_1_d : (111.371 : ℚ) + 68.629 = 180 ∧ (180 : ℚ) - 111.371 = 68.629 := by
  constructor <;> norm_num

/-- Stitz-Zeager Example 10.1.1(5): a complement of `37° 28' 17"` is `52° 31' 43"`. -/
@[kb "stitzzeager2013" "Example 10.1.1, p. 708"]
theorem ex_10_1_1_e :
    ((37 : ℚ) + 28 / 60 + 17 / 3600) + (52 + 31 / 60 + 43 / 3600) = 90 := by
  norm_num

/-- Stitz-Zeager Example 10.1.2(1): `60°` is a Quadrant I angle, and `420°, -300°, 780°` are
coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.2, p. 711"]
theorem ex_10_1_2_a :
    (0 < cos (60 * π / 180) ∧ 0 < sin (60 * π / 180)) ∧
      ∀ θ ∈ ({420, -300, 780} : Set ℝ), ∃ k : ℤ, θ = 60 + 360 * k := by
  refine ⟨Q1 _ (π / 3) 0 (by push_cast; ring) (by linarith [pi_pos]) (by linarith [pi_pos]), ?_⟩
  intro θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl | rfl
  · exact ⟨1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨2, by norm_num⟩

/-- Stitz-Zeager Example 10.1.2(2): `-225°` is a Quadrant II angle, and `135°, -585°, 495°` are
coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.2, p. 711"]
theorem ex_10_1_2_b :
    (cos (-225 * π / 180) < 0 ∧ 0 < sin (-225 * π / 180)) ∧
      ∀ θ ∈ ({135, -585, 495} : Set ℝ), ∃ k : ℤ, θ = -225 + 360 * k := by
  refine ⟨Q2 _ (3 * π / 4) (-1) (by push_cast; ring) (by linarith [pi_pos])
    (by linarith [pi_pos]), ?_⟩
  intro θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl | rfl
  · exact ⟨1, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨2, by norm_num⟩

/-- Stitz-Zeager Example 10.1.2(3): `540°` is a quadrantal angle (terminal side on the negative
`x`-axis), and `180°, -180°, 900°` are coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.2, p. 711"]
theorem ex_10_1_2_c :
    (cos (540 * π / 180) = -1 ∧ sin (540 * π / 180) = 0) ∧
      ∀ θ ∈ ({180, -180, 900} : Set ℝ), ∃ k : ℤ, θ = 540 + 360 * k := by
  refine ⟨?_, ?_⟩
  · have h : 540 * π / 180 = π + (1 : ℤ) * (2 * π) := by push_cast; ring
    rw [(cs_shift _ π 1 h).1, (cs_shift _ π 1 h).2]
    simp
  · intro θ hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
    rcases hθ with rfl | rfl | rfl
    · exact ⟨-1, by norm_num⟩
    · exact ⟨-2, by norm_num⟩
    · exact ⟨1, by norm_num⟩

/-- Stitz-Zeager Example 10.1.2(4): `-750°` is a Quadrant IV angle, and `-390°, -30°, 330°` are
coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.2, p. 711"]
theorem ex_10_1_2_d :
    (0 < cos (-750 * π / 180) ∧ sin (-750 * π / 180) < 0) ∧
      ∀ θ ∈ ({-390, -30, 330} : Set ℝ), ∃ k : ℤ, θ = -750 + 360 * k := by
  refine ⟨Q4 _ (11 * π / 6) (-3) (by push_cast; ring) (by linarith [pi_pos])
    (by linarith [pi_pos]), ?_⟩
  intro θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl | rfl
  · exact ⟨1, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨3, by norm_num⟩

/-- Stitz-Zeager Example 10.1.3(1): `π/6` is a Quadrant I angle, and `13π/6, -11π/6, 25π/6` are
coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.3, p. 714"]
theorem ex_10_1_3_a :
    (0 < cos (π / 6) ∧ 0 < sin (π / 6)) ∧
      ∀ θ ∈ ({13 * π / 6, -(11 * π / 6), 25 * π / 6} : Set ℝ),
        ∃ k : ℤ, θ = π / 6 + 2 * π * k := by
  refine ⟨Q1 _ (π / 6) 0 (by push_cast; ring) (by linarith [pi_pos]) (by linarith [pi_pos]), ?_⟩
  intro θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl | rfl
  · exact ⟨1, by push_cast; ring⟩
  · exact ⟨-1, by push_cast; ring⟩
  · exact ⟨2, by push_cast; ring⟩

/-- Stitz-Zeager Example 10.1.3(2): `-4π/3` is a Quadrant II angle, and `2π/3, -10π/3, 8π/3` are
coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.3, p. 714"]
theorem ex_10_1_3_b :
    (cos (-(4 * π / 3)) < 0 ∧ 0 < sin (-(4 * π / 3))) ∧
      ∀ θ ∈ ({2 * π / 3, -(10 * π / 3), 8 * π / 3} : Set ℝ),
        ∃ k : ℤ, θ = -(4 * π / 3) + 2 * π * k := by
  refine ⟨Q2 _ (2 * π / 3) (-1) (by push_cast; ring) (by linarith [pi_pos])
    (by linarith [pi_pos]), ?_⟩
  intro θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl | rfl
  · exact ⟨1, by push_cast; ring⟩
  · exact ⟨-1, by push_cast; ring⟩
  · exact ⟨2, by push_cast; ring⟩

/-- Stitz-Zeager Example 10.1.3(3): `9π/4` is a Quadrant I angle, and `π/4, -7π/4, 17π/4` are
coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.3, p. 714"]
theorem ex_10_1_3_c :
    (0 < cos (9 * π / 4) ∧ 0 < sin (9 * π / 4)) ∧
      ∀ θ ∈ ({π / 4, -(7 * π / 4), 17 * π / 4} : Set ℝ),
        ∃ k : ℤ, θ = 9 * π / 4 + 2 * π * k := by
  refine ⟨Q1 _ (π / 4) 1 (by push_cast; ring) (by linarith [pi_pos]) (by linarith [pi_pos]), ?_⟩
  intro θ hθ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
  rcases hθ with rfl | rfl | rfl
  · exact ⟨-1, by push_cast; ring⟩
  · exact ⟨-2, by push_cast; ring⟩
  · exact ⟨1, by push_cast; ring⟩

/-- Stitz-Zeager Example 10.1.3(4): `-5π/2` is a quadrantal angle (terminal side on the negative
`y`-axis: cosine `0`, sine `-1`), and `-π/2, 3π/2, 7π/2` are coterminal with it. -/
@[kb "stitzzeager2013" "Example 10.1.3, p. 714"]
theorem ex_10_1_3_d :
    (cos (-(5 * π / 2)) = 0 ∧ sin (-(5 * π / 2)) = -1) ∧
      ∀ θ ∈ ({-(π / 2), 3 * π / 2, 7 * π / 2} : Set ℝ),
        ∃ k : ℤ, θ = -(5 * π / 2) + 2 * π * k := by
  refine ⟨?_, ?_⟩
  · have h : -(5 * π / 2) = -(π / 2) + (-1 : ℤ) * (2 * π) := by push_cast; ring
    rw [(cs_shift _ _ (-1) h).1, (cs_shift _ _ (-1) h).2]
    simp
  · intro θ hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hθ
    rcases hθ with rfl | rfl | rfl
    · exact ⟨1, by push_cast; ring⟩
    · exact ⟨2, by push_cast; ring⟩
    · exact ⟨3, by push_cast; ring⟩

/-- Stitz-Zeager Example 10.1.4(1): the arc `t = 3π/4` is `3/8` of a revolution and ends at the
point `(-√2/2, √2/2)` in Quadrant II. -/
@[kb "stitzzeager2013" "Example 10.1.4, p. 717"]
theorem ex_10_1_4_a :
    3 * π / 4 = (3 / 8) * (2 * π) ∧
      cos (3 * π / 4) = -(√2 / 2) ∧ sin (3 * π / 4) = √2 / 2 := by
  have h : 3 * π / 4 = π - π / 4 := by ring
  refine ⟨by ring, ?_, ?_⟩
  · rw [h, cos_pi_sub, cos_pi_div_four]
  · rw [h, sin_pi_sub, sin_pi_div_four]

/-- Stitz-Zeager Example 10.1.4(2): the arc `t = -2π` is one clockwise revolution, ending back at
`(1, 0)`. -/
@[kb "stitzzeager2013" "Example 10.1.4, p. 717"]
theorem ex_10_1_4_b : cos (-(2 * π)) = 1 ∧ sin (-(2 * π)) = 0 := by
  simp

/-- Stitz-Zeager Example 10.1.4(3): the arc `t = -2` ends in Quadrant III (cosine and sine both
negative). -/
@[kb "stitzzeager2013" "Example 10.1.4, p. 717"]
theorem ex_10_1_4_c : cos (-2) < 0 ∧ sin (-2) < 0 :=
  Q3 _ (2 * π - 2) (-1) (by push_cast; ring) (by linarith [pi_gt_three])
    (by linarith [pi_lt_four])

/-- Stitz-Zeager Example 10.1.4(4): the arc `t = 117` makes `18` full counter-clockwise
revolutions, since `⌊117 / (2π)⌋ = 18`, and ends in Quadrant III (cosine and sine both
negative). -/
@[kb "stitzzeager2013" "Example 10.1.4, p. 717"]
theorem ex_10_1_4_d :
    ⌊(117 : ℝ) / (2 * π)⌋ = 18 ∧ cos 117 < 0 ∧ sin 117 < 0 := by
  have hl := pi_gt_d2
  have hu := pi_lt_d2
  refine ⟨?_, ?_⟩
  · rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
    · rw [div_lt_iff₀ (by positivity)]; push_cast; linarith
  · have := Q3 117 (117 - 36 * π) 18 (by push_cast; ring) (by linarith) (by linarith)
    exact this

/-! ### 10.3 Applications -/

/-- Stitz-Zeager Example 10.3.5(1): from `tan 60° = h / 30` the tower height is `h = 30 √3`,
which is about `52` feet (between `51.5` and `52.5`). -/
@[kb "stitzzeager2013" "Example 10.3.5, p. 766"]
theorem ex_10_3_5_a (h : ℝ) :
    tan (π / 3) = h / 30 ↔ h = 30 * √3 := by
  rw [tan_pi_div_three]
  constructor <;> intro H <;> linarith

/-- Stitz-Zeager Example 10.3.5(1), rounding: `30 √3` lies between `51.5` and `52.5`. -/
@[kb "stitzzeager2013" "Example 10.3.5, p. 766"]
theorem ex_10_3_5_a_round : (51.5 : ℝ) < 30 * √3 ∧ 30 * √3 < 52.5 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ √3 := Real.sqrt_nonneg 3
  constructor <;> nlinarith

/-- Stitz-Zeager Example 10.3.5(2): with `tan 45° = h / x` and `tan 30° = h / (x + 200)` the
distance is `x = h` and the tree height is `h = 200 √3 / (3 - √3) = 100 (√3 + 1)`. -/
@[kb "stitzzeager2013" "Example 10.3.5, p. 766"]
theorem ex_10_3_5_b (h x : ℝ) (hx : 0 < x) :
    (tan (π / 4) = h / x ∧ tan (π / 6) = h / (x + 200)) ↔
      (x = 100 * (√3 + 1) ∧ h = 100 * (√3 + 1)) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  rw [tan_pi_div_four, tan_pi_div_six]
  have hx2 : x + 200 ≠ 0 := by linarith
  constructor
  · rintro ⟨e1, e2⟩
    have hxh : x = h := by
      field_simp at e1; linarith
    subst hxh
    field_simp at e2
    have : (√3 - 1) * x = 200 := by linarith
    have hx3 : x = 100 * (√3 + 1) := by
      nlinarith
    exact ⟨hx3, hx3⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨by field_simp, ?_⟩
    field_simp
    nlinarith

/-- Stitz-Zeager Example 10.3.5(2), closed form and rounding: `200 √3 / (3 - √3) = 100 (√3 + 1)`
which lies between `273` and `274` (so the tree is about `273` feet). -/
@[kb "stitzzeager2013" "Example 10.3.5, p. 766"]
theorem ex_10_3_5_b_closed :
    200 * √3 / (3 - √3) = 100 * (√3 + 1) ∧ (272.5 : ℝ) < 100 * (√3 + 1) ∧
      100 * (√3 + 1) < 273.5 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  have hlt : √3 < 3 := by nlinarith
  refine ⟨?_, by nlinarith, by nlinarith⟩
  rw [div_eq_iff (by linarith)]
  nlinarith

/-- Stitz-Zeager Example 10.3.2(2): `tan θ = √3` exactly for `θ = π/3 + π k`, `k` an integer. -/
@[kb "stitzzeager2013" "Example 10.3.2, p. 759"]
theorem ex_10_3_2_b (θ : ℝ) : tan θ = √3 ↔ ∃ k : ℤ, θ = π / 3 + π * k := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h0 : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · intro h
    have hc : cos θ ≠ 0 := by
      intro hc
      rw [tan_eq_sin_div_cos, hc] at h
      simp at h
      linarith
    rw [tan_eq_sin_div_cos, div_eq_iff hc] at h
    have hs : sin (θ - π / 3) = 0 := by
      rw [sin_sub, cos_pi_div_three, sin_pi_div_three]
      linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 hs
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    have := (tan_periodic.int_mul k) (π / 3)
    rw [show π / 3 + π * (k : ℝ) = π / 3 + k * π by ring, this, tan_pi_div_three]

/-- Stitz-Zeager Example 10.3.2(3): `cot θ = -1` exactly for `θ = 3π/4 + π k`, `k` an integer. -/
@[kb "stitzzeager2013" "Example 10.3.2, p. 759"]
theorem ex_10_3_2_c (θ : ℝ) : cot θ = -1 ↔ ∃ k : ℤ, θ = 3 * π / 4 + π * k := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  constructor
  · intro h
    have hs : sin θ ≠ 0 := by
      intro hs
      rw [cot_eq_cos_div_sin, hs] at h
      simp at h
    rw [cot_eq_cos_div_sin, div_eq_iff hs] at h
    have hz : sin (θ + π / 4) = 0 := by
      rw [sin_add, cos_pi_div_four, sin_pi_div_four]
      have : sin θ * (√2 / 2) + cos θ * (√2 / 2) = (√2 / 2) * (sin θ + cos θ) := by ring
      rw [this]
      have : sin θ + cos θ = 0 := by linarith
      rw [this]; ring
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 hz
    refine ⟨n - 1, ?_⟩
    push_cast
    linarith
  · rintro ⟨k, rfl⟩
    have e1 : 3 * π / 4 + π * k = (π - π / 4) + k * π := by ring
    have hne : ((-1 : ℝ) ^ k) ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [e1, cot_eq_cos_div_sin, cos_add_int_mul_pi, sin_add_int_mul_pi,
      mul_div_mul_left _ _ hne, cos_pi_sub, sin_pi_sub, cos_pi_div_four, sin_pi_div_four]
    field_simp

end UndergradKB.Precalculus.Course
