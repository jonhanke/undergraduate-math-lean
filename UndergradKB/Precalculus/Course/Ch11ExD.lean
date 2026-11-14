import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 11 (Stitz-Zeager): worked examples, wave 6

Completes Example 11.4.3(2c), which wave 5 stated only in the polar-to-rectangular direction. -/

namespace UndergradKB.Precalculus.Course

open Real

/-- Stitz-Zeager Example 11.4.3(2c), both directions: the rectangular equation `(x² + y² + x)² = x² + y²` describes
exactly the points `(r cos θ, r sin θ)` of the polar curve `r = 1 - cos θ`. -/
@[kb "stitzzeager2013" "Example 11.4.3, p. 938"]
theorem ex_11_4_3_f_iff (x y : ℝ) :
    (x ^ 2 + y ^ 2 + x) ^ 2 = x ^ 2 + y ^ 2 ↔
      ∃ r θ : ℝ, r = 1 - cos θ ∧ x = r * cos θ ∧ y = r * sin θ := by
  constructor
  · intro h
    set z : ℂ := ⟨x, y⟩
    set ρ := ‖z‖
    have hc : ρ * cos (Complex.arg z) = x := Complex.norm_mul_cos_arg z
    have hs : ρ * sin (Complex.arg z) = y := Complex.norm_mul_sin_arg z
    have hρ2 : ρ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hρ0 : 0 ≤ ρ := norm_nonneg z
    set θ := Complex.arg z
    -- `x² + y² + x = ± ρ`
    have hsq : (ρ ^ 2 + x) ^ 2 = ρ ^ 2 := by rw [hρ2]; exact h
    have hpm : ρ ^ 2 + x = ρ ∨ ρ ^ 2 + x = -ρ := by
      have : (ρ ^ 2 + x - ρ) * (ρ ^ 2 + x + ρ) = 0 := by linear_combination hsq
      rcases mul_eq_zero.1 this with h1 | h1
      · left; linarith
      · right; linarith
    rcases eq_or_lt_of_le hρ0 with h0 | h0
    · -- the origin: `r = 0`, `θ = 0`
      have hx : x = 0 := by rw [← hc, ← h0, zero_mul]
      have hy : y = 0 := by rw [← hs, ← h0, zero_mul]
      exact ⟨0, 0, by simp, by simp [hx], by simp [hy]⟩
    rcases hpm with hp | hm
    · -- `ρ = 1 - cos θ`
      refine ⟨ρ, θ, ?_, hc.symm, hs.symm⟩
      have : ρ * (ρ - (1 - cos θ)) = 0 := by rw [← hc] at hp; linear_combination hp
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 h0.ne'
      · linarith
    · -- `-ρ = 1 - cos (θ + π)`
      refine ⟨-ρ, θ + π, ?_, by rw [cos_add_pi]; linarith, by rw [sin_add_pi]; linarith⟩
      rw [cos_add_pi]
      have : ρ * (ρ + 1 + cos θ) = 0 := by rw [← hc] at hm; linear_combination hm
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 h0.ne'
      · linarith
  · rintro ⟨r, θ, hr, rfl, rfl⟩
    have h1 := sin_sq_add_cos_sq θ
    have h2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h1
    have h3 : r = r ^ 2 + r * cos θ := by
      have : r * r = r * (1 - cos θ) := by rw [← hr]
      nlinarith
    rw [h2, ← h3]

end UndergradKB.Precalculus.Course
