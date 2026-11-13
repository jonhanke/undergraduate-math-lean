import Mathlib.Probability.CentralLimitTheorem
import UndergradKB.Common.Attr
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.LocalLimitBinomial
import UndergradKB.Probability.LocalLimit
import UndergradKB.Probability.LocalLimitLattice
import UndergradKB.Probability.CltBounded

/-!
# Course layer, Chapter 9 (Grinstead–Snell, Central Limit Theorem)

Thin wrappers stating the book's results of Chapter 9 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- Grinstead–Snell Theorem 9.4 (PR-100). Central limit theorem for an independent trials process
`X` with mean `μ` and variance `σ²`: `(S_n - n μ) / √n` converges in distribution to a normal
variable `Y` with mean `0` and variance `σ²` (equivalently `(S_n - n μ)/(σ √n)` tends to the
standard normal). -/
@[kb "grinsteadsnell2006" "Theorem 9.4, p. 351"]
theorem gs_theorem_9_4 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ) (hY : HasLaw Y (gaussianReal 0 (variance (X 0) P).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * ∫ ω', X 0 ω' ∂P))
      atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident

/-- Grinstead–Snell Theorem 9.6 (PR-100). Central limit theorem for centered, variance one
independent identically distributed summands: `S_n / √n` converges in distribution to the standard
normal. -/
@[kb "grinsteadsnell2006" "Theorem 9.6, p. 365"]
theorem gs_theorem_9_6 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ) (Y : Ω' → ℝ) (hY : HasLaw Y (gaussianReal 0 1) P')
    (h0 : ∫ ω, X 0 ω ∂P = 0) (h1 : ∫ ω, X 0 ω ^ 2 ∂P = 1) (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum hY h0 h1 hindep hident

/-- Grinstead–Snell Definition 9.1 (PR-096). The standardized sum `S_n* = (S_n - np)/√(npq)` has
mean `0`. -/
@[kb "grinsteadsnell2006" "Definition 9.1, p. 334"]
theorem gs_definition_9_1 : type_of% @UndergradKB.Probability.integral_standardize_sum :=
  @UndergradKB.Probability.integral_standardize_sum

/-- Grinstead–Snell Definition 9.1 (PR-096). The standardized sum has variance `1`. -/
@[kb "grinsteadsnell2006" "Definition 9.1, p. 334"]
theorem gs_definition_9_1_variance : type_of% @UndergradKB.Probability.variance_standardize_sum :=
  @UndergradKB.Probability.variance_standardize_sum

/-- Grinstead–Snell Theorem 9.1 (PR-097). Local limit theorem for the binomial: `√(npq) b(n,p,j)`
tends to the standard normal density. -/
@[kb "grinsteadsnell2006" "Theorem 9.1, p. 336"]
theorem gs_theorem_9_1 : type_of% @UndergradKB.Probability.local_limit_binomial :=
  @UndergradKB.Probability.local_limit_binomial

/-- Grinstead–Snell Theorem 9.1 (PR-097), nearest-integer form. -/
@[kb "grinsteadsnell2006" "Theorem 9.1, p. 336"]
theorem gs_theorem_9_1_nearest : type_of% @UndergradKB.Probability.local_limit_binomial_nearest :=
  @UndergradKB.Probability.local_limit_binomial_nearest

/-- Grinstead–Snell Theorem 9.2 (PR-098). Central limit theorem for Bernoulli trials,
`P(a ≤ S_n* ≤ b) → ∫_a^b φ`. -/
@[kb "grinsteadsnell2006" "Theorem 9.2, p. 338"]
theorem gs_theorem_9_2 : type_of% @UndergradKB.Probability.clt_bernoulli_interval :=
  @UndergradKB.Probability.clt_bernoulli_interval

/-- Grinstead–Snell Theorem 9.3 (PR-099). Local limit theorem for iid lattice variables. -/
@[kb "grinsteadsnell2006" "Theorem 9.3, p. 350"]
theorem gs_theorem_9_3 : type_of% @UndergradKB.Probability.local_limit_lattice :=
  @UndergradKB.Probability.local_limit_lattice

/-- Grinstead–Snell Theorem 9.3 (PR-099), ratio form. -/
@[kb "grinsteadsnell2006" "Theorem 9.3, p. 350"]
theorem gs_theorem_9_3_ratio : type_of% @UndergradKB.Probability.local_limit_lattice_ratio :=
  @UndergradKB.Probability.local_limit_lattice_ratio

/-- Grinstead–Snell Theorem 9.5 (PR-101). Central limit theorem for bounded, not identically
distributed variables (convergence in distribution). -/
@[kb "grinsteadsnell2006" "Theorem 9.5, p. 353"]
theorem gs_theorem_9_5 : type_of% @UndergradKB.Probability.clt_bounded :=
  @UndergradKB.Probability.clt_bounded

/-- Grinstead–Snell Theorem 9.5 (PR-101), interval form. -/
@[kb "grinsteadsnell2006" "Theorem 9.5, p. 353"]
theorem gs_theorem_9_5_interval : type_of% @UndergradKB.Probability.clt_bounded_interval :=
  @UndergradKB.Probability.clt_bounded_interval

end UndergradKB.Probability.Course
