import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 8), Sections 10.3 and 10.5 -/

namespace UndergradKB.Precalculus.Course

open Real

/-! ## Section 10.3 -/

/-- Right triangle, acute angle `θ`, adjacent leg `a = c cos θ`, opposite leg `b = c sin θ`:
`b = a tan θ` and `c = a / cos θ`. -/
theorem ch10e3b_tri_adj (θ a b c : ℝ) (h0 : 0 < θ) (h1 : θ < π / 2) (ha : a = c * cos θ)
    (hb : b = c * sin θ) : b = a * tan θ ∧ c = a / cos θ := by
  have hc : 0 < cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hne : cos θ ≠ 0 := hc.ne'
  constructor
  · rw [Real.tan_eq_sin_div_cos, ha, hb]
    field_simp
  · rw [ha]
    field_simp

/-- Right triangle, acute angle `θ`, opposite leg `b = c sin θ`, adjacent leg `a = c cos θ`:
`a = b cot θ` and `c = b / sin θ`. -/
theorem ch10e3b_tri_opp (θ a b c : ℝ) (h0 : 0 < θ) (h1 : θ < π / 2) (ha : a = c * cos θ)
    (hb : b = c * sin θ) : a = b * (cos θ / sin θ) ∧ c = b / sin θ := by
  have hs : 0 < sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hne : sin θ ≠ 0 := hs.ne'
  constructor
  · rw [ha, hb]
    field_simp
  · rw [hb]
    field_simp

/-- Stitz-Zeager Exercise 10.3.67: right triangle with angle `34°` adjacent to the leg `12`: the other
acute angle is `56°`, the opposite leg is `12 tan 34°` and the hypotenuse is `12 / cos 34°`. -/
@[kb "stitzzeager2013" "Exercise 10.3.67, p. 772"]
theorem exer_10_3_67 : π / 2 - 34 * π / 180 = 56 * π / 180 ∧
    ∀ b c : ℝ, 12 = c * cos (34 * π / 180) → b = c * sin (34 * π / 180) →
      b = 12 * tan (34 * π / 180) ∧ c = 12 / cos (34 * π / 180) := by
  have hp := Real.pi_pos
  refine ⟨by ring, fun b c ha hb => ?_⟩
  exact ch10e3b_tri_adj (34 * π / 180) 12 b c (by linarith) (by linarith) ha hb

/-- Stitz-Zeager Exercise 10.3.68: right triangle with angle `47°` opposite the leg `6`: the other
acute angle is `43°`, the other leg is `6 cot 47°` and the hypotenuse is `6 / sin 47°`. -/
@[kb "stitzzeager2013" "Exercise 10.3.68, p. 772"]
theorem exer_10_3_68 : π / 2 - 47 * π / 180 = 43 * π / 180 ∧
    ∀ a c : ℝ, 6 = c * sin (47 * π / 180) → a = c * cos (47 * π / 180) →
      a = 6 * (cos (47 * π / 180) / sin (47 * π / 180)) ∧ c = 6 / sin (47 * π / 180) := by
  have hp := Real.pi_pos
  refine ⟨by ring, fun a c hb ha => ?_⟩
  exact ch10e3b_tri_opp (47 * π / 180) a 6 c (by linarith) (by linarith) ha hb

/-- Stitz-Zeager Exercise 10.3.69: right triangle with angle `50°` adjacent to the leg `2.5`: the other
acute angle is `40°`, the opposite leg is `2.5 tan 50°` and the hypotenuse is `2.5 / cos 50°`. -/
@[kb "stitzzeager2013" "Exercise 10.3.69, p. 772"]
theorem exer_10_3_69 : π / 2 - 50 * π / 180 = 40 * π / 180 ∧
    ∀ b c : ℝ, 5 / 2 = c * cos (50 * π / 180) → b = c * sin (50 * π / 180) →
      b = 5 / 2 * tan (50 * π / 180) ∧ c = 5 / 2 / cos (50 * π / 180) := by
  have hp := Real.pi_pos
  refine ⟨by ring, fun b c ha hb => ?_⟩
  exact ch10e3b_tri_adj (50 * π / 180) (5 / 2) b c (by linarith) (by linarith) ha hb

/-! ## Section 10.5 -/

/-- Stitz-Zeager Exercise 10.5.36: if `(a, b) ≠ 0` lies on the terminal side of `φ`, then
`a sin(ωx) + b cos(ωx) + B = √(a²+b²) sin(ωx + φ) + B`. -/
@[kb "stitzzeager2013" "Exercise 10.5.36, p. 822"]
theorem exer_10_5_36 (a b φ : ℝ) (h : 0 < a ^ 2 + b ^ 2) (hc : cos φ = a / √(a ^ 2 + b ^ 2))
    (hs : sin φ = b / √(a ^ 2 + b ^ 2)) (ω B x : ℝ) :
    a * sin (ω * x) + b * cos (ω * x) + B = √(a ^ 2 + b ^ 2) * sin (ω * x + φ) + B := by
  have hr : √(a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  rw [Real.sin_add, hc, hs]
  field_simp

/-- Stitz-Zeager Exercise 10.5.38: `sin² x + cos² x = 1`. -/
@[kb "stitzzeager2013" "Exercise 10.5.38, p. 822"]
theorem exer_10_5_38 (x : ℝ) : sin x ^ 2 + cos x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x

/-- Stitz-Zeager Exercise 10.5.39: `sec² x - tan² x = 1` where `cos x ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 10.5.39, p. 822"]
theorem exer_10_5_39 (x : ℝ) (h : cos x ≠ 0) : (1 / cos x) ^ 2 - tan x ^ 2 = 1 := by
  have h1 := Real.sin_sq_add_cos_sq x
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  linarith

/-- Stitz-Zeager Exercise 10.5.40: `cos x = sin(π/2 - x)`. -/
@[kb "stitzzeager2013" "Exercise 10.5.40, p. 822"]
theorem exer_10_5_40 (x : ℝ) : cos x = sin (π / 2 - x) :=
  (Real.sin_pi_div_two_sub x).symm

/-- Stitz-Zeager Exercise 10.5.41: `tan(x + π) = tan x`. -/
@[kb "stitzzeager2013" "Exercise 10.5.41, p. 822"]
theorem exer_10_5_41 (x : ℝ) : tan (x + π) = tan x :=
  Real.tan_periodic x

/-- Stitz-Zeager Exercise 10.5.42: `sin 2x = 2 sin x cos x`. -/
@[kb "stitzzeager2013" "Exercise 10.5.42, p. 822"]
theorem exer_10_5_42 (x : ℝ) : sin (2 * x) = 2 * sin x * cos x :=
  Real.sin_two_mul x

/-- Stitz-Zeager Exercise 10.5.43: `tan(x/2) = sin x / (1 + cos x)` whenever `1 + cos x ≠ 0`. -/
@[kb "stitzzeager2013" "Exercise 10.5.43, p. 822"]
theorem exer_10_5_43 (x : ℝ) (hne : 1 + cos x ≠ 0) : tan (x / 2) = sin x / (1 + cos x) := by
  have h1 : sin x = 2 * sin (x / 2) * cos (x / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have h2 : 1 + cos x = 2 * cos (x / 2) ^ 2 := by
    have := Real.cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    linarith
  have hc : cos (x / 2) ≠ 0 := by
    intro h
    rw [h] at h2
    apply hne
    rw [h2]; ring
  rw [Real.tan_eq_sin_div_cos, h1, h2]
  field_simp

/-- Stitz-Zeager Exercise 10.5.44: `cos 3x + sin x` is periodic; `2π` is a period. -/
@[kb "stitzzeager2013" "Exercise 10.5.44, p. 822"]
theorem exer_10_5_44 (x : ℝ) : cos (3 * (x + 2 * π)) + sin (x + 2 * π) = cos (3 * x) + sin x := by
  rw [show 3 * (x + 2 * π) = 3 * x + ((3 : ℕ) : ℝ) * (2 * π) by push_cast; ring,
    Real.cos_add_nat_mul_two_pi, Real.sin_add_two_pi]

/-- Stitz-Zeager Exercise 10.5.45: the graph of `sin x / x` has the horizontal asymptote `y = 0`
as `x → ∞`. -/
@[kb "stitzzeager2013" "Exercise 10.5.45, p. 822"]
theorem exer_10_5_45 : Filter.Tendsto (fun x : ℝ => sin x / x) Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx, div_le_iff₀ hx, inv_mul_cancel₀ hx.ne']
  exact Real.abs_sin_le_one x

/-- Stitz-Zeager Exercise 10.5.51: a constant function repeats after every shift `p > 0` (in particular
117), so there is no smallest positive period. -/
@[kb "stitzzeager2013" "Exercise 10.5.51, p. 822"]
theorem exer_10_5_51 (c : ℝ) :
    (∀ x : ℝ, (fun _ : ℝ => c) (x + 117) = (fun _ : ℝ => c) x) ∧
    (∀ p : ℝ, 0 < p → ∀ x : ℝ, (fun _ : ℝ => c) (x + p) = (fun _ : ℝ => c) x) ∧
    ¬ ∃ p : ℝ, IsLeast {q : ℝ | 0 < q ∧ ∀ x : ℝ, (fun _ : ℝ => c) (x + q) = (fun _ : ℝ => c) x} p := by
  refine ⟨fun x => rfl, fun p _ x => rfl, ?_⟩
  rintro ⟨p, hp, hmin⟩
  have h := hmin ⟨by linarith [hp.1], fun x => rfl⟩
  have := hp.1
  show False
  have h2 : p ≤ p / 2 := hmin (show p / 2 ∈ _ from ⟨by linarith, fun x => rfl⟩)
  linarith

end UndergradKB.Precalculus.Course
