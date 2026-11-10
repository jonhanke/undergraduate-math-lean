import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology FormalMultilinearSeries
open scoped ENNReal NNReal Nat

/-! ## Radius of convergence -/

theorem norm_ofScalars_real (c : ℕ → ℝ) (n : ℕ) : ‖ofScalars ℝ c n‖ = |c n| := by
  rw [ofScalars_norm, Real.norm_eq_abs]

/-- OpenStax Calculus 2:Theorem 6.1 (CA-361, CA-362). The three cases of convergence of a power series
`∑ c n (x-a)^n`, with `R = (ofScalars ℝ c).radius ∈ [0,∞]` its radius of convergence:
it converges absolutely when `|x-a| < R`, its terms do not tend to `0` (so the series diverges) when `|x-a| > R`;
`R = 0` exactly when the series converges only at the center `a`; `R = ∞` exactly when it converges for every `x`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.1, p. 479"]
theorem power_series_convergence_cases (c : ℕ → ℝ) (a : ℝ) :
    (∀ x : ℝ, (‖x - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius →
      Summable (fun n => |c n * (x - a) ^ n|)) ∧
    (∀ x : ℝ, (ofScalars ℝ c).radius < (‖x - a‖₊ : ℝ≥0∞) →
      ¬ Tendsto (fun n => c n * (x - a) ^ n) atTop (𝓝 0) ∧
      ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ range n, c i * (x - a) ^ i) atTop (𝓝 S)) ∧
    ((ofScalars ℝ c).radius = 0 ↔ ∀ x : ℝ, x ≠ a →
      ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ range n, c i * (x - a) ^ i) atTop (𝓝 S)) ∧
    ((ofScalars ℝ c).radius = ∞ ↔ ∀ x : ℝ, Summable (fun n => c n * (x - a) ^ n)) := by
  have hnorm : ∀ (x : ℝ) (n : ℕ), ‖ofScalars ℝ c n‖ * (‖x - a‖₊ : ℝ) ^ n = |c n * (x - a) ^ n| := by
    intro x n
    rw [norm_ofScalars_real, coe_nnnorm, abs_mul, abs_pow, Real.norm_eq_abs]
  have hA : ∀ x : ℝ, (‖x - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius →
      Summable (fun n => |c n * (x - a) ^ n|) := fun x hx => by
    have := (ofScalars ℝ c).summable_norm_mul_pow hx
    simpa only [hnorm] using this
  have hB : ∀ x : ℝ, (ofScalars ℝ c).radius < (‖x - a‖₊ : ℝ≥0∞) →
      ¬ Tendsto (fun n => c n * (x - a) ^ n) atTop (𝓝 0) := fun x hx h0 => by
    apply not_le_of_gt hx
    refine (ofScalars ℝ c).le_radius_of_tendsto (l := 0) ?_
    simp only [hnorm]
    have h' := (continuous_abs.tendsto 0).comp h0
    rw [abs_zero] at h'
    exact h'
  have hdiv : ∀ x : ℝ, ¬ Tendsto (fun n => c n * (x - a) ^ n) atTop (𝓝 0) →
      ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ range n, c i * (x - a) ^ i) atTop (𝓝 S) := fun x h S hS => by
    apply h
    have h1 : Tendsto (fun n => ∑ i ∈ range (n + 1), c i * (x - a) ^ i) atTop (𝓝 S) :=
      hS.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.sub hS
    rw [sub_self] at h2
    refine h2.congr (fun n => ?_)
    rw [Finset.sum_range_succ]
    ring
  refine ⟨hA, fun x hx => ⟨hB x hx, hdiv x (hB x hx)⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h x hx S
    apply hdiv x (hB x _) S
    rw [h]
    exact_mod_cast (nnnorm_pos.mpr (sub_ne_zero.mpr hx))
  · intro h
    by_contra hne
    obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hne)
    have hr0' : (0 : ℝ≥0) < r := by exact_mod_cast hr0
    have hsum := hA (a + r) (by
      have : ‖a + (r : ℝ) - a‖₊ = r := by
        rw [add_sub_cancel_left]; simp
      rw [this]; exact hrR)
    have : Summable (fun n => c n * ((a + r) - a) ^ n) := hsum.of_abs
    have hne' : (a + r) ≠ a := by
      intro h; have : (r : ℝ) = 0 := by linarith
      exact hr0'.ne' (by exact_mod_cast this)
    exact h (a + r) hne' _ this.hasSum.tendsto_sum_nat
  · intro h x
    by_cases hx : (‖x - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius
    · exact (hA x hx).of_abs
    · rw [h] at hx; exact absurd ENNReal.coe_lt_top hx
  · intro h
    refine radius_eq_top_of_summable_norm _ fun r => ?_
    have := (h (a + r)).abs
    simpa [norm_ofScalars_real, abs_mul, abs_pow] using this

end UndergradKB.Calculus
