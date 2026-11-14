import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.7 (equations on [0, 2π), part 3)

Solutions on `[0, 2π)` are stated as `↔` with the finite list of solutions; for the expressions involving
`tan`, `sec`, `csc`, `cot` the domain hypotheses (nonvanishing denominators) are part of the statement,
because Lean's `x⁻¹` and `tan` take the value `0` where the book's functions are undefined. -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Close `x = a₁ ∨ x = a₂ ∨ ...` from a linear equation for `x` in terms of `π`. -/
macro "pick_sol_q" : tactic =>
  `(tactic| (push_cast at *; repeat' (first | (left; linarith; done) | right); try linarith))

/-- Pair the two directions of a `sin`/`cos` equality solved by Mathlib's `*_eq_*_iff`. -/
macro "key_tac_q" : tactic =>
  `(tactic| (constructor <;> rintro ⟨k, h | h⟩ <;>
    first | exact ⟨k, Or.inl (by linarith)⟩ | exact ⟨k, Or.inr (by linarith)⟩))

/-- Rearrange a disjunction of equalities. -/
macro "rearr_q" : tactic =>
  `(tactic| (simp only [or_assoc, or_comm, or_left_comm, or_self, or_self_left]; try done))

private lemma tan_iff' {a θ : ℝ} (hc : cos a ≠ 0) (hs : sin a ≠ 0) :
    tan θ = tan a ↔ ∃ k : ℤ, θ = a + π * k := by
  constructor
  · intro h
    have ha : tan a ≠ 0 := by rw [tan_eq_sin_div_cos]; exact div_ne_zero hs hc
    have hθ : cos θ ≠ 0 := fun h0 => ha (h ▸ tan_eq_zero_of_cos_eq_zero h0)
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff hθ hc] at h
    have : sin (θ - a) = 0 := by rw [sin_sub]; linarith
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp this
    exact ⟨n, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [mul_comm]; exact tan_add_int_mul_pi a k

private lemma gen_exer_10_7_46 (x : ℝ) : cos (5 * x) * cos (3 * x) - sin (5 * x) * sin (3 * x) = √3 / 2 ↔ ∃ k : ℤ, x = (1 / 48 + (-1 / 4 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 48 : ℝ) + 1 / 4 * (k : ℝ)) * π := by
  have e8 : cos (8 * x) = cos (5 * x) * cos (3 * x) - sin (5 * x) * sin (3 * x) := by
    rw [← cos_add]; congr 1; ring
  have h := cos_eq_cos_iff (x := 8 * x) (y := π / 6)
  rw [cos_pi_div_six] at h
  rw [← e8, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.46: on `[0, 2π)`, `cos 5x cos 3x - sin 5x sin 3x = √3/2` (that is, `cos 8x = √3/2`) has the sixteen solutions `x = π/48 + kπ/4 - ...`, listed in increasing order. -/
@[kb "stitzzeager2013" "Exercise 10.7.46, p. 887"]
theorem exer_10_7_46 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (5 * x) * cos (3 * x) - sin (5 * x) * sin (3 * x) = √3 / 2 ↔ x = π / 48 ∨ x = 11 * π / 48 ∨ x = 13 * π / 48 ∨ x = 23 * π / 48 ∨ x = 25 * π / 48 ∨ x = 35 * π / 48 ∨ x = 37 * π / 48 ∨ x = 47 * π / 48 ∨ x = 49 * π / 48 ∨ x = 59 * π / 48 ∨ x = 61 * π / 48 ∨ x = 71 * π / 48 ∨ x = 73 * π / 48 ∨ x = 83 * π / 48 ∨ x = 85 * π / 48 ∨ x = 95 * π / 48 := by
  rw [gen_exer_10_7_46 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-8 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-8 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 9 := by nlinarith [pi_pos]
      have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((9 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-2, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨3, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-3, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨4, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-4, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨5, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-5, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨6, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-6, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨7, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-7, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨8, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_47 (x : ℝ) : sin x + cos x = 1 ↔ ∃ k : ℤ, x = (1 / 2 + (-2 : ℝ) * (k : ℝ)) * π ∨ x = (0 + 2 * (k : ℝ)) * π := by
  have ec : cos (x - π / 4) = √2 / 2 * (cos x + sin x) := by
    rw [cos_sub, cos_pi_div_four, sin_pi_div_four]; ring
  have e : sin x + cos x = 1 ↔ cos (x - π / 4) = cos (π / 4) := by
    rw [ec, cos_pi_div_four]
    have hp : (√2 / 2 : ℝ) ≠ 0 := by positivity
    constructor
    · intro h; rw [add_comm, h]; ring
    · intro h
      have := mul_left_cancel₀ hp (h.trans (mul_one _).symm)
      linarith
  have h := cos_eq_cos_iff (x := x - π / 4) (y := π / 4)
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.47: on `[0, 2π)`, `sin x + cos x = 1` exactly when `x = 0` or `x = π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.47, p. 887"]
theorem exer_10_7_47 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x + cos x = 1 ↔ x = 0 ∨ x = π / 2 := by
  rw [gen_exer_10_7_47 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_48 (x : ℝ) : sin x + √3 * cos x = 1 ↔ ∃ k : ℤ, x = ((-1 / 6 : ℝ) + (-2 : ℝ) * (k : ℝ)) * π ∨ x = (1 / 2 + 2 * (k : ℝ)) * π := by
  have ec : sin (x + π / 3) = (sin x + √3 * cos x) / 2 := by
    rw [sin_add, cos_pi_div_three, sin_pi_div_three]; ring
  have e : sin x + √3 * cos x = 1 ↔ sin (x + π / 3) = 1 / 2 := by
    rw [ec]; constructor <;> intro h <;> linarith
  have h := sin_eq_sin_iff (x := x + π / 3) (y := π / 6)
  rw [sin_pi_div_six] at h
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.48: on `[0, 2π)`, `sin x + √3 cos x = 1` exactly when `x = π/2` or `x = 11π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.48, p. 887"]
theorem exer_10_7_48 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin x + √3 * cos x = 1 ↔ x = π / 2 ∨ x = 11 * π / 6 := by
  rw [gen_exer_10_7_48 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 0 := by nlinarith [pi_pos]
      have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((0 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_49 (x : ℝ) : √2 * cos x - √2 * sin x = 1 ↔ ∃ k : ℤ, x = (1 / 12 + (-2 : ℝ) * (k : ℝ)) * π ∨ x = ((-7 / 12 : ℝ) + 2 * (k : ℝ)) * π := by
  have ec : cos (x + π / 4) = (√2 * cos x - √2 * sin x) / 2 := by
    rw [cos_add, cos_pi_div_four, sin_pi_div_four]; ring
  have e : √2 * cos x - √2 * sin x = 1 ↔ cos (x + π / 4) = 1 / 2 := by
    rw [ec]; constructor <;> intro h <;> linarith
  have h := cos_eq_cos_iff (x := x + π / 4) (y := π / 3)
  rw [cos_pi_div_three] at h
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.49: on `[0, 2π)`, `√2 cos x - √2 sin x = 1` exactly when `x = π/12` or `x = 17π/12`. -/
@[kb "stitzzeager2013" "Exercise 10.7.49, p. 887"]
theorem exer_10_7_49 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    √2 * cos x - √2 * sin x = 1 ↔ x = π / 12 ∨ x = 17 * π / 12 := by
  rw [gen_exer_10_7_49 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 2 := by nlinarith [pi_pos]
      have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((2 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_50 (x : ℝ) : √3 * sin (2 * x) + cos (2 * x) = 1 ↔ ∃ k : ℤ, x = (0 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = (1 / 3 + 1 * (k : ℝ)) * π := by
  have ec : sin (2 * x + π / 6) = (√3 * sin (2 * x) + cos (2 * x)) / 2 := by
    rw [sin_add, cos_pi_div_six, sin_pi_div_six]; ring
  have e : √3 * sin (2 * x) + cos (2 * x) = 1 ↔ sin (2 * x + π / 6) = 1 / 2 := by
    rw [ec]; constructor <;> intro h <;> linarith
  have h := sin_eq_sin_iff (x := 2 * x + π / 6) (y := π / 6)
  rw [sin_pi_div_six] at h
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.50: on `[0, 2π)`, `√3 sin 2x + cos 2x = 1` exactly when `x = 0, π/3, π, 4π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.50, p. 887"]
theorem exer_10_7_50 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    √3 * sin (2 * x) + cos (2 * x) = 1 ↔ x = 0 ∨ x = π / 3 ∨ x = π ∨ x = 4 * π / 3 := by
  rw [gen_exer_10_7_50 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 2 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((2 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_51 (x : ℝ) : cos (2 * x) - √3 * sin (2 * x) = √2 ↔ ∃ k : ℤ, x = ((-1 / 24 : ℝ) + (-1 : ℝ) * (k : ℝ)) * π ∨ x = ((-7 / 24 : ℝ) + 1 * (k : ℝ)) * π := by
  have ec : cos (2 * x + π / 3) = (cos (2 * x) - √3 * sin (2 * x)) / 2 := by
    rw [cos_add, cos_pi_div_three, sin_pi_div_three]; ring
  have e : cos (2 * x) - √3 * sin (2 * x) = √2 ↔ cos (2 * x + π / 3) = √2 / 2 := by
    rw [ec]; constructor <;> intro h <;> linarith
  have h := cos_eq_cos_iff (x := 2 * x + π / 3) (y := π / 4)
  rw [cos_pi_div_four] at h
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.51: on `[0, 2π)`, `cos 2x - √3 sin 2x = √2` exactly when `x = 17π/24, 23π/24, 41π/24, 47π/24`. -/
@[kb "stitzzeager2013" "Exercise 10.7.51, p. 887"]
theorem exer_10_7_51 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (2 * x) - √3 * sin (2 * x) = √2 ↔ x = 17 * π / 24 ∨ x = 23 * π / 24 ∨ x = 41 * π / 24 ∨ x = 47 * π / 24 := by
  rw [gen_exer_10_7_51 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-3 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 0 := by nlinarith [pi_pos]
      have h1' : ((-3 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((0 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 3 := by nlinarith [pi_pos]
      have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((3 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-2, Or.inl (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_52 (x : ℝ) : 3 * √3 * sin (3 * x) - 3 * cos (3 * x) = 3 * √3 ↔ ∃ k : ℤ, x = (1 / 6 + (-2 / 3 : ℝ) * (k : ℝ)) * π ∨ x = (5 / 18 + 2 / 3 * (k : ℝ)) * π := by
  have ec : sin (3 * x - π / 6) = (√3 * sin (3 * x) - cos (3 * x)) / 2 := by
    rw [sin_sub, cos_pi_div_six, sin_pi_div_six]; ring
  have e : 3 * √3 * sin (3 * x) - 3 * cos (3 * x) = 3 * √3 ↔ sin (3 * x - π / 6) = √3 / 2 := by
    rw [ec]; constructor <;> intro h <;> linarith
  have h := sin_eq_sin_iff (x := 3 * x - π / 6) (y := π / 3)
  rw [sin_pi_div_three] at h
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.52: on `[0, 2π)`, `3√3 sin 3x - 3 cos 3x = 3√3` exactly when `x = π/6, 5π/18, 5π/6, 17π/18, 3π/2, 29π/18`. -/
@[kb "stitzzeager2013" "Exercise 10.7.52, p. 887"]
theorem exer_10_7_52 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    3 * √3 * sin (3 * x) - 3 * cos (3 * x) = 3 * √3 ↔ x = π / 6 ∨ x = 5 * π / 18 ∨ x = 5 * π / 6 ∨ x = 17 * π / 18 ∨ x = 3 * π / 2 ∨ x = 29 * π / 18 := by
  rw [gen_exer_10_7_52 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-3 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-3 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 3 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((3 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-2, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_53 (x : ℝ) : cos (3 * x) = cos (5 * x) ↔ ∃ k : ℤ, x = (0 + 1 * (k : ℝ)) * π ∨ x = (0 + 1 / 4 * (k : ℝ)) * π := by
  have h := cos_eq_cos_iff (x := 3 * x) (y := 5 * x)
  rw [h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.53: on `[0, 2π)`, `cos 3x = cos 5x` exactly when `x = kπ/4`, `k = 0..7`. -/
@[kb "stitzzeager2013" "Exercise 10.7.53, p. 888"]
theorem exer_10_7_53 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (3 * x) = cos (5 * x) ↔ x = 0 ∨ x = π / 4 ∨ x = π / 2 ∨ x = 3 * π / 4 ∨ x = π ∨ x = 5 * π / 4 ∨ x = 3 * π / 2 ∨ x = 7 * π / 4 := by
  rw [gen_exer_10_7_53 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 2 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((2 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 8 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((8 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨3, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨5, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨6, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨7, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_54 (x : ℝ) : cos (4 * x) = cos (2 * x) ↔ ∃ k : ℤ, x = (0 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = (0 + 1 / 3 * (k : ℝ)) * π := by
  have h := cos_eq_cos_iff (x := 4 * x) (y := 2 * x)
  rw [h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.54: on `[0, 2π)`, `cos 4x = cos 2x` exactly when `x = 0, π/3, 2π/3, π, 4π/3, 5π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.54, p. 888"]
theorem exer_10_7_54 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (4 * x) = cos (2 * x) ↔ x = 0 ∨ x = π / 3 ∨ x = 2 * π / 3 ∨ x = π ∨ x = 4 * π / 3 ∨ x = 5 * π / 3 := by
  rw [gen_exer_10_7_54 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 6 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((6 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨4, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨5, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_55 (x : ℝ) : sin (5 * x) = sin (3 * x) ↔ ∃ k : ℤ, x = (0 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = (1 / 8 + 1 / 4 * (k : ℝ)) * π := by
  have h := sin_eq_sin_iff (x := 5 * x) (y := 3 * x)
  rw [h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.55: on `[0, 2π)`, `sin 5x = sin 3x` exactly when `x = 0, π` or `x = π/8 + kπ/4`, `k = 0..7`. -/
@[kb "stitzzeager2013" "Exercise 10.7.55, p. 888"]
theorem exer_10_7_55 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin (5 * x) = sin (3 * x) ↔ x = 0 ∨ x = π / 8 ∨ x = 3 * π / 8 ∨ x = 5 * π / 8 ∨ x = 7 * π / 8 ∨ x = π ∨ x = 9 * π / 8 ∨ x = 11 * π / 8 ∨ x = 13 * π / 8 ∨ x = 15 * π / 8 := by
  rw [gen_exer_10_7_55 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 8 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((8 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨3, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨4, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨5, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨6, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨7, Or.inr (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_56 (x : ℝ) : cos (5 * x) = -cos (2 * x) ↔ ∃ k : ℤ, x = (1 / 7 + (-2 / 7 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 3 : ℝ) + 2 / 3 * (k : ℝ)) * π := by
  have e : cos (5 * x) = -cos (2 * x) ↔ cos (5 * x) = cos (π - 2 * x) := by
    rw [cos_pi_sub]
  have h := cos_eq_cos_iff (x := 5 * x) (y := π - 2 * x)
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.56: on `[0, 2π)`, `cos 5x = -cos 2x` exactly when `x = π/7, π/3, 3π/7, 5π/7, π, 9π/7, 11π/7, 5π/3, 13π/7`. -/
@[kb "stitzzeager2013" "Exercise 10.7.56, p. 888"]
theorem exer_10_7_56 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (5 * x) = -cos (2 * x) ↔ x = π / 7 ∨ x = π / 3 ∨ x = 3 * π / 7 ∨ x = 5 * π / 7 ∨ x = π ∨ x = 9 * π / 7 ∨ x = 11 * π / 7 ∨ x = 5 * π / 3 ∨ x = 13 * π / 7 := by
  rw [gen_exer_10_7_56 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-7 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-7 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 4 := by nlinarith [pi_pos]
      have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((4 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨-2, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨-3, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨-4, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨-5, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨3, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-6, Or.inl (by rw [h]; push_cast; ring)⟩

private lemma gen_exer_10_7_57 (x : ℝ) : sin (6 * x) + sin x = 0 ↔ ∃ k : ℤ, x = (0 + (-2 / 7 : ℝ) * (k : ℝ)) * π ∨ x = (1 / 5 + 2 / 5 * (k : ℝ)) * π := by
  have e : sin (6 * x) + sin x = 0 ↔ sin (6 * x) = sin (-x) := by
    rw [sin_neg]; constructor <;> intro h <;> linarith
  have h := sin_eq_sin_iff (x := 6 * x) (y := -x)
  rw [e, h]
  key_tac_q

/-- Stitz-Zeager Exercise 10.7.57: on `[0, 2π)`, `sin 6x + sin x = 0` exactly when `x = 2kπ/7` (`k = 0..6`) or `x = π/5 + 2kπ/5` (`k = 0..4`). -/
@[kb "stitzzeager2013" "Exercise 10.7.57, p. 888"]
theorem exer_10_7_57 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin (6 * x) + sin x = 0 ↔ x = 0 ∨ x = π / 5 ∨ x = 2 * π / 7 ∨ x = 4 * π / 7 ∨ x = 3 * π / 5 ∨ x = 6 * π / 7 ∨ x = π ∨ x = 8 * π / 7 ∨ x = 7 * π / 5 ∨ x = 10 * π / 7 ∨ x = 12 * π / 7 ∨ x = 9 * π / 5 := by
  rw [gen_exer_10_7_57 x]
  constructor
  · rintro ⟨k, hk⟩
    rcases hk with hk | hk
    · have h1 : ((-7 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
      have h1' : ((-7 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
    · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 5 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((5 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol_q
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨-2, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-3, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-4, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨3, Or.inr (by rw [h]; push_cast; ring)⟩
    · exact ⟨-5, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨-6, Or.inl (by rw [h]; push_cast; ring)⟩
    · exact ⟨4, Or.inr (by rw [h]; push_cast; ring)⟩

end UndergradKB.Precalculus.Course
