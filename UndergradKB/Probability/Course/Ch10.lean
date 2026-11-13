import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesLimits
import UndergradKB.Probability.ExamplesBranching
import UndergradKB.Probability.GeneratingFunctions
import UndergradKB.Probability.Branching
import UndergradKB.Probability.MgfSeries

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

/-- Grinstead–Snell Theorem 10.1 (PR-103). The generating function determines the distribution. -/
@[kb "grinsteadsnell2006" "Theorem 10.1, p. 376"]
theorem gs_theorem_10_1 : type_of% @UndergradKB.Probability.eq_of_genFun_eq :=
  @UndergradKB.Probability.eq_of_genFun_eq

/-- Grinstead–Snell Theorem 10.2 (PR-106). The extinction probability of a branching process is the
smallest root of `z = h(z)`. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem gs_theorem_10_2 : type_of% @UndergradKB.Probability.extinction_smallest_root :=
  @UndergradKB.Probability.extinction_smallest_root

/-- Grinstead–Snell Theorem 10.2 (PR-106), mean offspring at most `1`: extinction is certain. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem gs_theorem_10_2_eq_one : type_of% @UndergradKB.Probability.extinction_prob_eq_one :=
  @UndergradKB.Probability.extinction_prob_eq_one

/-- Grinstead–Snell Theorem 10.2 (PR-106), mean offspring above `1`: extinction probability below `1`. -/
@[kb "grinsteadsnell2006" "Theorem 10.2, p. 388"]
theorem gs_theorem_10_2_lt_one : type_of% @UndergradKB.Probability.extinction_prob_lt_one :=
  @UndergradKB.Probability.extinction_prob_lt_one

/-- Grinstead–Snell Theorem 10.3 (PR-107). For a bounded variable `∑ μ_k t^k/k!` converges to `g(t)`. -/
@[kb "grinsteadsnell2006" "Theorem 10.3, p. 404"]
theorem gs_theorem_10_3 : type_of% @UndergradKB.Probability.hasSum_moments_mgf :=
  @UndergradKB.Probability.hasSum_moments_mgf

/-- Grinstead–Snell Theorem 10.4 (PR-108). For a bounded variable the moment generating function
determines the distribution. -/
@[kb "grinsteadsnell2006" "Theorem 10.4, p. 405"]
theorem gs_theorem_10_4 : type_of% @UndergradKB.Probability.map_eq_of_mgf_eq_of_bounded :=
  @UndergradKB.Probability.map_eq_of_mgf_eq_of_bounded

/-- Grinstead–Snell Example 10.8 (PR-158). Tree measure of the branching process with `p₀ = 1/2, p₁ = p₂ = 1/4`. -/
@[kb "grinsteadsnell2006" "Example 10.8, p. 386"]
theorem gs_example_10_8 : type_of% @UndergradKB.Probability.exampleOffspring_two_two :=
  @UndergradKB.Probability.exampleOffspring_two_two

/-- Grinstead–Snell Example 10.8 (PR-158). The probability of dying out by a given generation. -/
@[kb "grinsteadsnell2006" "Example 10.8, p. 386"]
theorem gs_example_10_8_b : type_of% @UndergradKB.Probability.exampleOffspring_extinctProb :=
  @UndergradKB.Probability.exampleOffspring_extinctProb

/-- Grinstead–Snell Example 10.10 (PR-158). The generating function iterates by composition. -/
@[kb "grinsteadsnell2006" "Example 10.10, p. 392"]
theorem gs_example_10_10 : type_of% @UndergradKB.Probability.exampleOffspring_gf_comp :=
  @UndergradKB.Probability.exampleOffspring_gf_comp

/-- Grinstead–Snell Example 10.10 (PR-158). The mean number of offspring and the extinction probability. -/
@[kb "grinsteadsnell2006" "Example 10.10, p. 392"]
theorem gs_example_10_10_b : type_of% @UndergradKB.Probability.exampleOffspring_extinction :=
  @UndergradKB.Probability.exampleOffspring_extinction

/-- Grinstead–Snell Example 10.11 (PR-142). The generating function and mean of the geometric offspring law. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem gs_example_10_11 : type_of% @UndergradKB.Probability.geomOffspring_gf_mean :=
  @UndergradKB.Probability.geomOffspring_gf_mean

/-- Grinstead–Snell Example 10.11 (PR-142). The extinction probability for the geometric offspring law. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem gs_example_10_11_b : type_of% @UndergradKB.Probability.geomOffspring_extinction :=
  @UndergradKB.Probability.geomOffspring_extinction

/-- Grinstead–Snell Example 10.11 (PR-142). For the geometric offspring law, `d < 1` exactly when `m > 1`. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem gs_example_10_11_c : type_of% @UndergradKB.Probability.geomOffspring_d_lt_one_iff :=
  @UndergradKB.Probability.geomOffspring_d_lt_one_iff

end UndergradKB.Probability.Course
