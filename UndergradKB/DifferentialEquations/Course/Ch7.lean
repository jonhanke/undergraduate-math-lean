import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapter 7 (power series methods): course layer

Thin wrappers around Mathlib stating the power series and gamma function facts of the chapter
in the book's terms.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch7

open Filter Topology NNReal

/-- Lebl §7.1 Convergence of power series (DE-190). The sum of the series `∑ aₖ xᵏ` at `x` is the
sum of its terms, and the series always converges at the center `0`. -/
@[kb "lebldiffyqs2026" "§7.1 Convergence of power series, p. 328"]
theorem lebl_power_series_sum (a : ℕ → ℝ) (x : ℝ) :
    FormalMultilinearSeries.ofScalarsSum a x = ∑' k : ℕ, a k • x ^ k ∧
      Summable (fun k : ℕ => a k * (0 : ℝ) ^ k) := by
  refine ⟨FormalMultilinearSeries.ofScalars_sum_eq a x, ?_⟩
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  simp at hk
  simp [hk]

/-- Lebl Example 7.1.1 (DE-191). The exponential series `∑ xᵏ/k!` has infinite radius of
convergence and sum `e^x`. -/
@[kb "lebldiffyqs2026" "Example 7.1.1, p. 328"]
theorem lebl_exp_series (x : ℝ) :
    (NormedSpace.expSeries ℝ ℝ).radius = ⊤ ∧
      HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
  refine ⟨NormedSpace.expSeries_radius_eq_top ℝ ℝ, ?_⟩
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- Lebl §7.1 Absolute convergence, Example 7.1.2 (DE-192). Absolute convergence implies
convergence; an alternating series with terms decreasing to zero converges; and the harmonic
series `∑ 1/k` diverges. -/
@[kb "lebldiffyqs2026" "§7.1 Absolute convergence, p. 328"]
theorem lebl_absolute_convergence :
    (∀ f : ℕ → ℝ, Summable (fun k => ‖f k‖) → Summable f) ∧
      (∀ f : ℕ → ℝ, Antitone f → Tendsto f atTop (𝓝 0) →
        ∃ l, Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i) atTop (𝓝 l)) ∧
      ¬ Summable (fun k : ℕ => 1 / (k : ℝ)) :=
  ⟨fun _ h => h.of_norm, fun _ hf h0 => hf.tendsto_alternating_series_of_tendsto_zero h0,
    Real.not_summable_one_div_natCast⟩

/-- Lebl Theorem 7.1.2 (ratio test), Examples 7.1.3, 7.1.4 (DE-194). If
`|a_{k+1}/a_k| → A ≠ 0` the radius of `∑ aₖ xᵏ` is `1/A`; if the ratios tend to `0` it is
infinite; if they tend to infinity it is `0`. -/
@[kb "lebldiffyqs2026" "Theorem 7.1.2, p. 329"]
theorem lebl_ratio_test_radius (a : ℕ → ℝ) :
    (∀ A : ℝ≥0, A ≠ 0 → Tendsto (fun k => ‖a (k + 1)‖ / ‖a k‖) atTop (𝓝 A) →
      (FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ a).radius = ((A⁻¹ : ℝ≥0) : ENNReal)) ∧
    ((∀ᶠ k in atTop, a k ≠ 0) → Tendsto (fun k => ‖a (k + 1)‖ / ‖a k‖) atTop (𝓝 0) →
      (FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ a).radius = ⊤) ∧
    (Tendsto (fun k => ‖a (k + 1)‖ / ‖a k‖) atTop atTop →
      (FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ a).radius = 0) :=
  ⟨fun _ hA h => FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto ℝ a hA h,
    fun hne h => FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℝ a hne h,
    fun h => FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto ℝ a h⟩

/-- Lebl Theorem 7.1.2 (root test, Cauchy-Hadamard) (DE-194). The inverse of the radius of a
power series is `limsup ‖aₖ‖^{1/k}`. -/
@[kb "lebldiffyqs2026" "Theorem 7.1.2, p. 329"]
theorem lebl_root_test_radius (p : FormalMultilinearSeries ℝ ℝ ℝ) :
    p.radius⁻¹ = limsup (fun n => ((‖p n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ENNReal)) atTop :=
  p.radius_inv_eq_limsup

/-- Lebl §7.1.3 Analytic functions (DE-195). A function is analytic at `x₀` iff near `x₀` it is
given by a convergent power series. -/
@[kb "lebldiffyqs2026" "§7.1.3 Analytic functions, p. 330"]
theorem lebl_analytic_iff (f : ℝ → ℝ) (x₀ : ℝ) :
    AnalyticAt ℝ f x₀ ↔ ∃ p : FormalMultilinearSeries ℝ ℝ ℝ, HasFPowerSeriesAt f p x₀ :=
  Iff.rfl

/-- Lebl §7.1.5 Geometric series (DE-199). For `|x| < 1`, `∑ xᵏ = 1/(1-x)`; the series is
summable only for `|x| < 1`; and `1/(1-x)` has a power series on the unit ball. -/
@[kb "lebldiffyqs2026" "§7.1.5 Geometric series, p. 333"]
theorem lebl_geometric_series (x : ℝ) :
    (|x| < 1 → HasSum (fun k : ℕ => x ^ k) (1 - x)⁻¹) ∧
      (Summable (fun k : ℕ => x ^ k) ↔ ‖x‖ < 1) ∧
      HasFPowerSeriesOnBall (fun x : ℝ => 1 / (1 - x)) (FormalMultilinearSeries.ofScalars (𝕜 := ℝ) ℝ (1 : ℕ → ℝ)) 0 1 :=
  ⟨hasSum_geometric_of_abs_lt_one, summable_geometric_iff_norm_lt_one,
    Real.one_div_one_sub_hasFPowerSeriesOnBall_zero⟩

/-- Lebl §7.3.3 Gamma function (DE-210). `Γ(x) = ∫₀^∞ e^{-t} t^{x-1} dt` for `x > 0`,
`Γ(x+1) = x Γ(x)` for `x ≠ 0`, and `Γ(n+1) = n!`. -/
@[kb "lebldiffyqs2026" "§7.3.3 Gamma function, p. 348"]
theorem lebl_gamma (x : ℝ) (n : ℕ) :
    (0 < x → Real.Gamma x = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)) ∧
      (x ≠ 0 → Real.Gamma (x + 1) = x * Real.Gamma x) ∧
      Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) :=
  ⟨fun h => Real.Gamma_eq_integral h, fun h => Real.Gamma_add_one h,
    Real.Gamma_nat_eq_factorial n⟩

/-- Lebl §7.3.3 Reciprocal gamma (DE-211). `1/Γ` is entire, and satisfies
`1/Γ(s) = s / Γ(s+1)`. -/
@[kb "lebldiffyqs2026" "§7.3.3 Reciprocal gamma, p. 348"]
theorem lebl_reciprocal_gamma :
    (Differentiable ℂ fun s : ℂ => (Complex.Gamma s)⁻¹) ∧
      ∀ s : ℂ, (Complex.Gamma s)⁻¹ = s * (Complex.Gamma (s + 1))⁻¹ :=
  ⟨Complex.differentiable_one_div_Gamma,
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one⟩

end UndergradKB.DifferentialEquations.Course.Ch7
