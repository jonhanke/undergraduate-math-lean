import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 10 (Stitz-Zeager): exercises with the book's answers (wave 7),
Section 10.7 (equations on [0, 2π), part 1)

Solutions on `[0, 2π)` are stated as `↔` with the finite list of solutions; for the expressions involving
`tan`, `sec`, `csc`, `cot` the domain hypotheses (nonvanishing denominators) are part of the statement,
because Lean's `x⁻¹` and `tan` take the value `0` where the book's functions are undefined. -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Close `x = a₁ ∨ x = a₂ ∨ ...` from a linear equation for `x` in terms of `π`. -/
macro "pick_sol" : tactic =>
  `(tactic| (push_cast at *; repeat' (first | (left; linarith; done) | right); try linarith))

/-- Pair the two directions of a `sin`/`cos` equality solved by Mathlib's `*_eq_*_iff`. -/
macro "key_tac" : tactic =>
  `(tactic| (constructor <;> rintro ⟨k, h | h⟩ <;>
    first | exact ⟨k, Or.inl (by linarith)⟩ | exact ⟨k, Or.inr (by linarith)⟩))

/-- Rearrange a disjunction of equalities. -/
macro "rearr" : tactic =>
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

private lemma gen_exer_10_7_1 (x : ℝ) : sin (5 * x) = 0 ↔ ∃ k : ℤ, x = (0 + 1 / 5 * (k : ℝ)) * π := by
  rw [sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.1: `sin(5x) = 0` exactly when `x = kπ/5` (`k` an integer); in `[0, 2π)` these are `kπ/5`, `k = 0..9`. -/
@[kb "stitzzeager2013" "Exercise 10.7.1, p. 886"]
theorem exer_10_7_1 :
    (∀ x : ℝ, sin (5 * x) = 0 ↔ ∃ k : ℤ, x = (0 + 1 / 5 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (sin (5 * x) = 0 ↔ x = 0 ∨ x = π / 5 ∨ x = 2 * π / 5 ∨ x = 3 * π / 5 ∨ x = 4 * π / 5 ∨ x = π ∨ x = 6 * π / 5 ∨ x = 7 * π / 5 ∨ x = 8 * π / 5 ∨ x = 9 * π / 5) :=
  ⟨gen_exer_10_7_1, fun x hx0 hx1 => by
    rw [gen_exer_10_7_1 x]
    constructor
    · rintro ⟨k, hk⟩
      have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 10 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((10 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h | h | h | h | h | h | h
      · exact ⟨0, by rw [h]; push_cast; ring⟩
      · exact ⟨1, by rw [h]; push_cast; ring⟩
      · exact ⟨2, by rw [h]; push_cast; ring⟩
      · exact ⟨3, by rw [h]; push_cast; ring⟩
      · exact ⟨4, by rw [h]; push_cast; ring⟩
      · exact ⟨5, by rw [h]; push_cast; ring⟩
      · exact ⟨6, by rw [h]; push_cast; ring⟩
      · exact ⟨7, by rw [h]; push_cast; ring⟩
      · exact ⟨8, by rw [h]; push_cast; ring⟩
      · exact ⟨9, by rw [h]; push_cast; ring⟩⟩

private lemma gen_exer_10_7_3 (x : ℝ) : sin (-(2 * x)) = √3 / 2 ↔ ∃ k : ℤ, x = ((-1 / 6 : ℝ) + 1 * (k : ℝ)) * π ∨ x = ((-1 / 3 : ℝ) + (-1 : ℝ) * (k : ℝ)) * π := by
  rw [← sin_pi_div_three, sin_eq_sin_iff]
  key_tac

/-- Stitz-Zeager Exercise 10.7.3: all solutions of `sin(-2x) = √3/2` are `x = 2π/3 + kπ` or `5π/6 + kπ`; in `[0, 2π)`: `2π/3, 5π/6, 5π/3, 11π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.3, p. 886"]
theorem exer_10_7_3 :
    (∀ x : ℝ, sin (-(2 * x)) = √3 / 2 ↔ ∃ k : ℤ, x = ((-1 / 6 : ℝ) + 1 * (k : ℝ)) * π ∨ x = ((-1 / 3 : ℝ) + (-1 : ℝ) * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (sin (-(2 * x)) = √3 / 2 ↔ x = 2 * π / 3 ∨ x = 5 * π / 6 ∨ x = 5 * π / 3 ∨ x = 11 * π / 6) :=
  ⟨gen_exer_10_7_3, fun x hx0 hx1 => by
    rw [gen_exer_10_7_3 x]
    constructor
    · rintro ⟨k, hk⟩
      rcases hk with hk | hk
      · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 3 := by nlinarith [pi_pos]
        have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((3 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
      · have h1 : ((-3 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 0 := by nlinarith [pi_pos]
        have h1' : ((-3 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((0 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h
      · exact ⟨-1, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨1, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨-2, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨2, Or.inl (by rw [h]; push_cast; ring)⟩⟩

private lemma gen_exer_10_7_4 (x : ℝ) : tan (6 * x) = 1 ↔ ∃ k : ℤ, x = (1 / 24 + 1 / 6 * (k : ℝ)) * π := by
  have hc : cos (π / 4) ≠ 0 := by rw [cos_pi_div_four]; positivity
  have hs : sin (π / 4) ≠ 0 := by rw [sin_pi_div_four]; positivity
  have h := tan_iff' hc hs (θ := 6 * x)
  rw [tan_pi_div_four] at h
  rw [h]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.4: all solutions of `tan(6x) = 1` are `x = π/24 + kπ/6`; twelve of them lie in `[0, 2π)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.4, p. 886"]
theorem exer_10_7_4 :
    (∀ x : ℝ, tan (6 * x) = 1 ↔ ∃ k : ℤ, x = (1 / 24 + 1 / 6 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (tan (6 * x) = 1 ↔ x = π / 24 ∨ x = 5 * π / 24 ∨ x = 3 * π / 8 ∨ x = 13 * π / 24 ∨ x = 17 * π / 24 ∨ x = 7 * π / 8 ∨ x = 25 * π / 24 ∨ x = 29 * π / 24 ∨ x = 11 * π / 8 ∨ x = 37 * π / 24 ∨ x = 41 * π / 24 ∨ x = 15 * π / 8) :=
  ⟨gen_exer_10_7_4, fun x hx0 hx1 => by
    rw [gen_exer_10_7_4 x]
    constructor
    · rintro ⟨k, hk⟩
      have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 12 := by nlinarith [pi_pos]
      have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((12 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h
      · exact ⟨0, by rw [h]; push_cast; ring⟩
      · exact ⟨1, by rw [h]; push_cast; ring⟩
      · exact ⟨2, by rw [h]; push_cast; ring⟩
      · exact ⟨3, by rw [h]; push_cast; ring⟩
      · exact ⟨4, by rw [h]; push_cast; ring⟩
      · exact ⟨5, by rw [h]; push_cast; ring⟩
      · exact ⟨6, by rw [h]; push_cast; ring⟩
      · exact ⟨7, by rw [h]; push_cast; ring⟩
      · exact ⟨8, by rw [h]; push_cast; ring⟩
      · exact ⟨9, by rw [h]; push_cast; ring⟩
      · exact ⟨10, by rw [h]; push_cast; ring⟩
      · exact ⟨11, by rw [h]; push_cast; ring⟩⟩

private lemma gen_exer_10_7_6 (x : ℝ) : (cos (3 * x))⁻¹ = √2 ↔ ∃ k : ℤ, x = (1 / 12 + (-2 / 3 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 12 : ℝ) + 2 / 3 * (k : ℝ)) * π := by
  have hp : (0 : ℝ) < √2 := by positivity
  have s2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : (cos (3 * x))⁻¹ = √2 ↔ cos (3 * x) = √2 / 2 := by
    constructor
    · intro h
      have : cos (3 * x) = (√2)⁻¹ := by rw [← h, inv_inv]
      rw [this]; field_simp; nlinarith
    · intro h; rw [h]; field_simp; nlinarith
  have h := cos_eq_cos_iff (x := 3 * x) (y := π / 4)
  rw [cos_pi_div_four] at h
  rw [e, h]
  key_tac

/-- Stitz-Zeager Exercise 10.7.6: all solutions of `sec(3x) = √2` are `x = π/12 + 2kπ/3` or `7π/12 + 2kπ/3`; six of them lie in `[0, 2π)`. -/
@[kb "stitzzeager2013" "Exercise 10.7.6, p. 886"]
theorem exer_10_7_6 :
    (∀ x : ℝ, (cos (3 * x))⁻¹ = √2 ↔ ∃ k : ℤ, x = (1 / 12 + (-2 / 3 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 12 : ℝ) + 2 / 3 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → ((cos (3 * x))⁻¹ = √2 ↔ x = π / 12 ∨ x = 7 * π / 12 ∨ x = 3 * π / 4 ∨ x = 5 * π / 4 ∨ x = 17 * π / 12 ∨ x = 23 * π / 12) :=
  ⟨gen_exer_10_7_6, fun x hx0 hx1 => by
    rw [gen_exer_10_7_6 x]
    constructor
    · rintro ⟨k, hk⟩
      rcases hk with hk | hk
      · have h1 : ((-3 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
        have h1' : ((-3 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
      · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 4 := by nlinarith [pi_pos]
        have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((4 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h | h | h
      · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨-2, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨3, Or.inr (by rw [h]; push_cast; ring)⟩⟩

private lemma gen_exer_10_7_11 (x : ℝ) : sin (2 * x - π / 3) = -(1 / 2) ↔ ∃ k : ℤ, x = (1 / 12 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = (3 / 4 + 1 * (k : ℝ)) * π := by
  have h := sin_eq_sin_iff (x := 2 * x - π / 3) (y := -(π / 6))
  rw [sin_neg, sin_pi_div_six] at h
  rw [h]
  key_tac

/-- Stitz-Zeager Exercise 10.7.11: all solutions of `sin(2x - π/3) = -1/2` are `x = 3π/4 + kπ` or `13π/12 + kπ`; in `[0, 2π)`: `π/12, 3π/4, 13π/12, 7π/4`. -/
@[kb "stitzzeager2013" "Exercise 10.7.11, p. 886"]
theorem exer_10_7_11 :
    (∀ x : ℝ, sin (2 * x - π / 3) = -(1 / 2) ↔ ∃ k : ℤ, x = (1 / 12 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = (3 / 4 + 1 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (sin (2 * x - π / 3) = -(1 / 2) ↔ x = π / 12 ∨ x = 3 * π / 4 ∨ x = 13 * π / 12 ∨ x = 7 * π / 4) :=
  ⟨gen_exer_10_7_11, fun x hx0 hx1 => by
    rw [gen_exer_10_7_11 x]
    constructor
    · rintro ⟨k, hk⟩
      rcases hk with hk | hk
      · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
        have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
      · have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 2 := by nlinarith [pi_pos]
        have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((2 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h
      · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨0, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩⟩

private lemma gen_exer_10_7_12 (x : ℝ) : 2 * cos (x + 7 * π / 4) = √3 ↔ ∃ k : ℤ, x = ((-19 / 12 : ℝ) + (-2 : ℝ) * (k : ℝ)) * π ∨ x = ((-23 / 12 : ℝ) + 2 * (k : ℝ)) * π := by
  have h := cos_eq_cos_iff (x := x + 7 * π / 4) (y := π / 6)
  rw [cos_pi_div_six] at h
  have e : 2 * cos (x + 7 * π / 4) = √3 ↔ cos (x + 7 * π / 4) = √3 / 2 := by
    constructor <;> intro h <;> linarith
  rw [e, h]
  key_tac

/-- Stitz-Zeager Exercise 10.7.12: all solutions of `2 cos(x + 7π/4) = √3` are `x = -19π/12 + 2kπ` or `π/12 + 2kπ`; in `[0, 2π)`: `π/12, 5π/12`. -/
@[kb "stitzzeager2013" "Exercise 10.7.12, p. 886"]
theorem exer_10_7_12 :
    (∀ x : ℝ, 2 * cos (x + 7 * π / 4) = √3 ↔ ∃ k : ℤ, x = ((-19 / 12 : ℝ) + (-2 : ℝ) * (k : ℝ)) * π ∨ x = ((-23 / 12 : ℝ) + 2 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (2 * cos (x + 7 * π / 4) = √3 ↔ x = π / 12 ∨ x = 5 * π / 12) :=
  ⟨gen_exer_10_7_12, fun x hx0 hx1 => by
    rw [gen_exer_10_7_12 x]
    constructor
    · rintro ⟨k, hk⟩
      rcases hk with hk | hk
      · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 0 := by nlinarith [pi_pos]
        have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((0 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
      · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 2 := by nlinarith [pi_pos]
        have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((2 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h
      · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩⟩

private lemma gen_exer_10_7_14 (x : ℝ) : tan (2 * x - π) = 1 ↔ ∃ k : ℤ, x = (5 / 8 + 1 / 2 * (k : ℝ)) * π := by
  have hc : cos (π / 4) ≠ 0 := by rw [cos_pi_div_four]; positivity
  have hs : sin (π / 4) ≠ 0 := by rw [sin_pi_div_four]; positivity
  have h := tan_iff' hc hs (θ := 2 * x - π)
  rw [tan_pi_div_four] at h
  rw [h]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.14: all solutions of `tan(2x - π) = 1` are `x = 5π/8 + kπ/2`; in `[0, 2π)`: `π/8, 5π/8, 9π/8, 13π/8`. -/
@[kb "stitzzeager2013" "Exercise 10.7.14, p. 886"]
theorem exer_10_7_14 :
    (∀ x : ℝ, tan (2 * x - π) = 1 ↔ ∃ k : ℤ, x = (5 / 8 + 1 / 2 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (tan (2 * x - π) = 1 ↔ x = π / 8 ∨ x = 5 * π / 8 ∨ x = 9 * π / 8 ∨ x = 13 * π / 8) :=
  ⟨gen_exer_10_7_14, fun x hx0 hx1 => by
    rw [gen_exer_10_7_14 x]
    constructor
    · rintro ⟨k, hk⟩
      have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
      have h2 : (k : ℝ) < 3 := by nlinarith [pi_pos]
      have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
      have h2' : k < ((3 : ℤ)) := by exact_mod_cast h2
      interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h
      · exact ⟨-1, by rw [h]; push_cast; ring⟩
      · exact ⟨0, by rw [h]; push_cast; ring⟩
      · exact ⟨1, by rw [h]; push_cast; ring⟩
      · exact ⟨2, by rw [h]; push_cast; ring⟩⟩

private lemma gen_exer_10_7_16 (x : ℝ) : ((cos x)⁻¹) ^ 2 = 4 / 3 ↔ ∃ k : ℤ, x = (1 / 6 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 6 : ℝ) + 1 * (k : ℝ)) * π := by
  have e : ((cos x)⁻¹) ^ 2 = 4 / 3 ↔ cos (2 * x) = 1 / 2 := by
    rw [cos_two_mul]
    by_cases hc : cos x = 0
    · rw [hc]; norm_num
    · rw [inv_pow, inv_eq_iff_eq_inv, show ((4 : ℝ) / 3)⁻¹ = 3 / 4 by norm_num]
      constructor <;> intro h <;> linarith
  have h := cos_eq_cos_iff (x := 2 * x) (y := π / 3)
  rw [cos_pi_div_three] at h
  rw [e, h]
  key_tac

/-- Stitz-Zeager Exercise 10.7.16: all solutions of `sec²(x) = 4/3` are `x = π/6 + kπ` or `5π/6 + kπ`; in `[0, 2π)`: `π/6, 5π/6, 7π/6, 11π/6`. -/
@[kb "stitzzeager2013" "Exercise 10.7.16, p. 886"]
theorem exer_10_7_16 :
    (∀ x : ℝ, ((cos x)⁻¹) ^ 2 = 4 / 3 ↔ ∃ k : ℤ, x = (1 / 6 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 6 : ℝ) + 1 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (((cos x)⁻¹) ^ 2 = 4 / 3 ↔ x = π / 6 ∨ x = 5 * π / 6 ∨ x = 7 * π / 6 ∨ x = 11 * π / 6) :=
  ⟨gen_exer_10_7_16, fun x hx0 hx1 => by
    rw [gen_exer_10_7_16 x]
    constructor
    · rintro ⟨k, hk⟩
      rcases hk with hk | hk
      · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
        have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
      · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 3 := by nlinarith [pi_pos]
        have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((3 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h
      · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩⟩

private lemma gen_exer_10_7_18 (x : ℝ) : sin x ^ 2 = 3 / 4 ↔ ∃ k : ℤ, x = (1 / 3 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 3 : ℝ) + 1 * (k : ℝ)) * π := by
  have e : sin x ^ 2 = 3 / 4 ↔ cos (2 * x) = -(1 / 2) := by
    rw [cos_two_mul]
    constructor <;> intro h <;> linarith [sin_sq_add_cos_sq x]
  have c23 : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  have h := cos_eq_cos_iff (x := 2 * x) (y := 2 * π / 3)
  rw [c23] at h
  rw [e, h]
  key_tac

/-- Stitz-Zeager Exercise 10.7.18: all solutions of `sin²(x) = 3/4` are `x = π/3 + kπ` or `2π/3 + kπ`; in `[0, 2π)`: `π/3, 2π/3, 4π/3, 5π/3`. -/
@[kb "stitzzeager2013" "Exercise 10.7.18, p. 886"]
theorem exer_10_7_18 :
    (∀ x : ℝ, sin x ^ 2 = 3 / 4 ↔ ∃ k : ℤ, x = (1 / 3 + (-1 : ℝ) * (k : ℝ)) * π ∨ x = ((-1 / 3 : ℝ) + 1 * (k : ℝ)) * π) ∧
      ∀ x : ℝ, 0 ≤ x → x < 2 * π → (sin x ^ 2 = 3 / 4 ↔ x = π / 3 ∨ x = 2 * π / 3 ∨ x = 4 * π / 3 ∨ x = 5 * π / 3) :=
  ⟨gen_exer_10_7_18, fun x hx0 hx1 => by
    rw [gen_exer_10_7_18 x]
    constructor
    · rintro ⟨k, hk⟩
      rcases hk with hk | hk
      · have h1 : ((-2 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
        have h1' : ((-2 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
      · have h1 : ((0 : ℝ)) < k := by nlinarith [pi_pos]
        have h2 : (k : ℝ) < 3 := by nlinarith [pi_pos]
        have h1' : ((0 : ℤ)) < k := by exact_mod_cast h1
        have h2' : k < ((3 : ℤ)) := by exact_mod_cast h2
        interval_cases k <;> pick_sol
    · intro h
      rcases h with h | h | h | h
      · exact ⟨0, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨1, Or.inr (by rw [h]; push_cast; ring)⟩
      · exact ⟨-1, Or.inl (by rw [h]; push_cast; ring)⟩
      · exact ⟨2, Or.inr (by rw [h]; push_cast; ring)⟩⟩

private lemma gen_exer_10_7_43 (x : ℝ) : sin (6 * x) * cos x = -(cos (6 * x) * sin x) ↔ ∃ k : ℤ, x = (0 + 1 / 7 * (k : ℝ)) * π := by
  have e : sin (6 * x) * cos x = -(cos (6 * x) * sin x) ↔ sin (7 * x) = 0 := by
    have : sin (7 * x) = sin (6 * x) * cos x + cos (6 * x) * sin x := by
      rw [← sin_add]; congr 1; ring
    rw [this]; constructor <;> intro h <;> linarith
  rw [e, sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.43: on `[0, 2π)`, `sin(6x) cos x = -cos(6x) sin x` (that is, `sin 7x = 0`) exactly when `x = kπ/7`, `k = 0..13`. -/
@[kb "stitzzeager2013" "Exercise 10.7.43, p. 887"]
theorem exer_10_7_43 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin (6 * x) * cos x = -(cos (6 * x) * sin x) ↔ x = 0 ∨ x = π / 7 ∨ x = 2 * π / 7 ∨ x = 3 * π / 7 ∨ x = 4 * π / 7 ∨ x = 5 * π / 7 ∨ x = 6 * π / 7 ∨ x = π ∨ x = 8 * π / 7 ∨ x = 9 * π / 7 ∨ x = 10 * π / 7 ∨ x = 11 * π / 7 ∨ x = 12 * π / 7 ∨ x = 13 * π / 7 := by
  rw [gen_exer_10_7_43 x]
  constructor
  · rintro ⟨k, hk⟩
    have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
    have h2 : (k : ℝ) < 14 := by nlinarith [pi_pos]
    have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
    have h2' : k < ((14 : ℤ)) := by exact_mod_cast h2
    interval_cases k <;> pick_sol
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by rw [h]; push_cast; ring⟩
    · exact ⟨2, by rw [h]; push_cast; ring⟩
    · exact ⟨3, by rw [h]; push_cast; ring⟩
    · exact ⟨4, by rw [h]; push_cast; ring⟩
    · exact ⟨5, by rw [h]; push_cast; ring⟩
    · exact ⟨6, by rw [h]; push_cast; ring⟩
    · exact ⟨7, by rw [h]; push_cast; ring⟩
    · exact ⟨8, by rw [h]; push_cast; ring⟩
    · exact ⟨9, by rw [h]; push_cast; ring⟩
    · exact ⟨10, by rw [h]; push_cast; ring⟩
    · exact ⟨11, by rw [h]; push_cast; ring⟩
    · exact ⟨12, by rw [h]; push_cast; ring⟩
    · exact ⟨13, by rw [h]; push_cast; ring⟩

private lemma gen_exer_10_7_44 (x : ℝ) : sin (3 * x) * cos x = cos (3 * x) * sin x ↔ ∃ k : ℤ, x = (0 + 1 / 2 * (k : ℝ)) * π := by
  have e : sin (3 * x) * cos x = cos (3 * x) * sin x ↔ sin (2 * x) = 0 := by
    have : sin (2 * x) = sin (3 * x) * cos x - cos (3 * x) * sin x := by
      rw [← sin_sub]; congr 1; ring
    rw [this]; constructor <;> intro h <;> linarith
  rw [e, sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.44: on `[0, 2π)`, `sin(3x) cos x = cos(3x) sin x` (that is, `sin 2x = 0`) exactly when `x = 0, π/2, π, 3π/2`. -/
@[kb "stitzzeager2013" "Exercise 10.7.44, p. 887"]
theorem exer_10_7_44 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    sin (3 * x) * cos x = cos (3 * x) * sin x ↔ x = 0 ∨ x = π / 2 ∨ x = π ∨ x = 3 * π / 2 := by
  rw [gen_exer_10_7_44 x]
  constructor
  · rintro ⟨k, hk⟩
    have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
    have h2 : (k : ℝ) < 4 := by nlinarith [pi_pos]
    have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
    have h2' : k < ((4 : ℤ)) := by exact_mod_cast h2
    interval_cases k <;> pick_sol
  · intro h
    rcases h with h | h | h | h
    · exact ⟨0, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by rw [h]; push_cast; ring⟩
    · exact ⟨2, by rw [h]; push_cast; ring⟩
    · exact ⟨3, by rw [h]; push_cast; ring⟩

private lemma gen_exer_10_7_45 (x : ℝ) : cos (2 * x) * cos x + sin (2 * x) * sin x = 1 ↔ ∃ k : ℤ, x = (0 + 2 * (k : ℝ)) * π := by
  have e : cos (2 * x) * cos x + sin (2 * x) * sin x = 1 ↔ cos x = 1 := by
    have : cos x = cos (2 * x) * cos x + sin (2 * x) * sin x := by
      rw [← cos_sub]; congr 1; ring
    rw [← this]
  rw [e, cos_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- Stitz-Zeager Exercise 10.7.45: on `[0, 2π)`, `cos 2x cos x + sin 2x sin x = 1` (that is, `cos x = 1`) exactly when `x = 0`. -/
@[kb "stitzzeager2013" "Exercise 10.7.45, p. 887"]
theorem exer_10_7_45 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 * π) :
    cos (2 * x) * cos x + sin (2 * x) * sin x = 1 ↔ x = 0 := by
  rw [gen_exer_10_7_45 x]
  constructor
  · rintro ⟨k, hk⟩
    have h1 : ((-1 : ℝ)) < k := by nlinarith [pi_pos]
    have h2 : (k : ℝ) < 1 := by nlinarith [pi_pos]
    have h1' : ((-1 : ℤ)) < k := by exact_mod_cast h1
    have h2' : k < ((1 : ℤ)) := by exact_mod_cast h2
    interval_cases k <;> (push_cast at hk; linarith)
  · intro h
    rcases h with h
    · exact ⟨0, by rw [h]; push_cast; ring⟩

end UndergradKB.Precalculus.Course
