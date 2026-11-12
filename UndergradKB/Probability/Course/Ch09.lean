import Mathlib.Probability.CentralLimitTheorem
import UndergradKB.Common.Attr

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

end UndergradKB.Probability.Course
