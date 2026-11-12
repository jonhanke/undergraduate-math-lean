import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Density
import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 6 (Grinstead–Snell, Expected Value and Variance)

Thin wrappers stating the book's results of Chapter 6 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Grinstead–Snell Definition 6.1 (PR-064). On a finite sample space the expected value of a
random variable is the sum of its values weighted by the probabilities of the outcomes; for a
countable sample space the same holds when the sum converges absolutely (integrability). -/
@[kb "grinsteadsnell2006" "Definition 6.1, p. 234"]
theorem gs_definition_6_1 {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) :
    ((∀ [Finite Ω], ∫ ω, X ω ∂P = ∑' ω, P.real {ω} • X ω) ∧
      (∀ [Countable Ω], Integrable X P → ∫ ω, X ω ∂P = ∑' ω, P.real {ω} • X ω)) := by
  refine ⟨fun {_} => ?_, fun {_} h => integral_countable h⟩
  have := Fintype.ofFinite Ω
  rw [integral_fintype Integrable.of_finite, tsum_fintype]

/-- Grinstead–Snell Theorem 6.1 (PR-065). If `X` has law `μ`, then `E(φ(X))` is the integral of
`φ` against `μ`. -/
@[kb "grinsteadsnell2006" "Theorem 6.1, p. 238"]
theorem gs_theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ : Measure ℝ) (hX : HasLaw X μ P) (φ : ℝ → ℝ)
    (hφ : AEStronglyMeasurable φ μ) :
    ∫ ω, φ (X ω) ∂P = ∫ x, φ x ∂μ := by
  rw [← hX.map_eq, integral_map hX.aemeasurable (hX.map_eq ▸ hφ)]

/-- Grinstead–Snell Definition 6.4 (PR-066). The expected value of a continuous random variable
with density `f` is the integral of `x f(x)`. -/
@[kb "grinsteadsnell2006" "Definition 6.4, p. 276"]
theorem gs_definition_6_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P] :
    ∫ ω, X ω ∂P = ∫ x, (pdf X P volume x).toReal * x :=
  (pdf.integral_pdf_smul (X := X) (f := fun x : ℝ => x) aestronglyMeasurable_id).symm

/-- Grinstead–Snell Theorem 6.11 (PR-065). For a random variable with density `f`, `E(φ(X))` is
the integral of `φ(x) f(x)`. -/
@[kb "grinsteadsnell2006" "Theorem 6.11, p. 278"]
theorem gs_theorem_6_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P] (φ : ℝ → ℝ) (hφ : AEStronglyMeasurable φ volume) :
    ∫ ω, φ (X ω) ∂P = ∫ x, (pdf X P volume x).toReal * φ x :=
  (pdf.integral_pdf_smul (X := X) hφ).symm

/-- Grinstead–Snell Theorem 6.2 (PR-067). Expectation is additive and homogeneous, with no
independence assumption. -/
@[kb "grinsteadsnell2006" "Theorem 6.2, p. 239"]
theorem gs_theorem_6_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) (c : ℝ) :
    ∫ ω, (X ω + Y ω) ∂P = ∫ ω, X ω ∂P + ∫ ω, Y ω ∂P ∧
      ∫ ω, c * X ω ∂P = c * ∫ ω, X ω ∂P :=
  ⟨integral_add hX hY, integral_const_mul c X⟩

/-- Grinstead–Snell Theorem 6.3 (PR-068). The number of successes in `n` Bernoulli trials (a
binomial random variable) has expected value `n p`. -/
@[kb "grinsteadsnell2006" "Theorem 6.3, p. 241"]
theorem gs_theorem_6_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (n : ℕ) (p : unitInterval) (hX : HasLaw X (binomial n p |>.map Nat.cast) P) :
    ∫ ω, X ω ∂P = n * p :=
  by rw [integral_of_hasLaw_binomial hX, mul_comm]

/-- Grinstead–Snell Theorem 6.4 (PR-069). For independent random variables
`E(XY) = E(X) E(Y)`. -/
@[kb "grinsteadsnell2006" "Theorem 6.4, p. 241"]
theorem gs_theorem_6_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (hX : AEStronglyMeasurable X P)
    (hY : AEStronglyMeasurable Y P) :
    ∫ ω, X ω * Y ω ∂P = (∫ ω, X ω ∂P) * ∫ ω, Y ω ∂P :=
  hXY.integral_fun_mul_eq_mul_integral hX hY

/-- Grinstead–Snell Definition 6.3 (PR-071). The variance of `X` is `E((X - μ)²)` where `μ` is
the mean, and the standard deviation is its square root. -/
@[kb "grinsteadsnell2006" "Definition 6.3, p. 265"]
theorem gs_definition_6_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEMeasurable X P) :
    variance X P = ∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P :=
  variance_eq_integral hX

/-- Grinstead–Snell Theorem 6.6 (PR-072). `V(X) = E(X²) - E(X)²`. -/
@[kb "grinsteadsnell2006" "Theorem 6.6, p. 266"]
theorem gs_theorem_6_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) :
    variance X P = ∫ ω, X ω ^ 2 ∂P - (∫ ω, X ω ∂P) ^ 2 := by
  simpa using variance_eq_sub hX

/-- Grinstead–Snell Theorem 6.7 (PR-073). `V(cX) = c² V(X)` and `V(X + c) = V(X)`. -/
@[kb "grinsteadsnell2006" "Theorem 6.7, p. 267"]
theorem gs_theorem_6_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEStronglyMeasurable X P) (c : ℝ) :
    variance (fun ω => c * X ω) P = c ^ 2 * variance X P ∧
      variance (fun ω => X ω + c) P = variance X P :=
  ⟨variance_const_mul c X P, variance_add_const hX c⟩

/-- Grinstead–Snell Theorem 6.8 (PR-074). For independent random variables with finite variance
the variances add. -/
@[kb "grinsteadsnell2006" "Theorem 6.8, p. 267"]
theorem gs_theorem_6_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (h : IndepFun X Y P) :
    variance (fun ω => X ω + Y ω) P = variance X P + variance Y P :=
  h.variance_fun_add hX hY

/-- Grinstead–Snell Example 6.27 (PR-082). The normal law with mean `μ` and standard deviation
`s` has mean `μ` and variance `s²` (in particular the standard normal has mean 0 and
variance 1). -/
@[kb "grinsteadsnell2006" "Example 6.27, p. 281"]
theorem gs_example_6_27 (μ : ℝ) (s : ℝ≥0) :
    ∫ x, x ∂gaussianReal μ (s ^ 2) = μ ∧ variance id (gaussianReal μ (s ^ 2)) = (s : ℝ) ^ 2 := by
  refine ⟨integral_id_gaussianReal, ?_⟩
  simp [variance_id_gaussianReal (μ := μ) (v := s ^ 2)]

end UndergradKB.Probability.Course
