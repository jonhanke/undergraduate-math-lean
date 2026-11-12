import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 10 (Grinstead–Snell, Generating Functions)

Thin wrappers stating the book's results of Chapter 10 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory

/-- Grinstead–Snell §10.1 moment generating function (PR-102). The moment generating function is
`g(t) = E(e^(tX))`, and when it is finite near `0` its `n`-th derivative at `0` is the moment
`E(X^n)`. -/
@[kb "grinsteadsnell2006" "§10.1 moment generating function, p. 374"]
theorem gs_section_10_1_moment_generating_function {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (t : ℝ)
    (h : 0 ∈ interior (integrableExpSet X P)) (n : ℕ) :
    mgf X P t = ∫ ω, Real.exp (t * X ω) ∂P ∧ iteratedDeriv n (mgf X P) 0 = moment X n P :=
  ⟨rfl, iteratedDeriv_mgf_zero h n⟩

/-- Grinstead–Snell §10.2 generating function of a sum (PR-104). The moment generating function
of a sum of independent random variables is the product of their moment generating functions. -/
@[kb "grinsteadsnell2006" "§10.2 generating function of a sum, p. 378"]
theorem gs_section_10_2_generating_function_of_a_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y P) (Z : ι → Ω → ℝ) (hZ : iIndepFun Z P)
    (hZm : ∀ i, Measurable (Z i)) (s : Finset ι) (t : ℝ) :
    mgf (X + Y) P t = mgf X P t * mgf Y P t ∧
      mgf (∑ i ∈ s, Z i) P t = ∏ i ∈ s, mgf (Z i) P t :=
  ⟨hXY.mgf_add' hX.aestronglyMeasurable hY.aestronglyMeasurable, hZ.mgf_sum hZm s⟩

/-- Grinstead–Snell §10.3 characteristic function (PR-109). The characteristic function of a
random variable `X` with law `μ` is `τ ↦ E(e^(i τ X))`. -/
@[kb "grinsteadsnell2006" "§10.3 characteristic function, p. 405"]
theorem gs_section_10_3_characteristic_function {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (μ : Measure ℝ) (hX : HasLaw X μ P) (τ : ℝ) :
    charFun μ τ = ∫ ω, Complex.exp (τ * X ω * Complex.I) ∂P := by
  rw [charFun_apply_real, ← hX.map_eq, integral_map hX.aemeasurable (by fun_prop)]

end UndergradKB.Probability.Course
