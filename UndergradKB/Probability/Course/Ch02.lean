import Mathlib.Probability.Density
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Exponential
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesContinuous
import UndergradKB.Probability.ExamplesGeometric
import UndergradKB.Probability.ContinuousDistributions

/-!
# Course layer, Chapter 2 (Grinstead–Snell, Continuous Probability Densities)

Thin wrappers stating the book's results of Chapter 2 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory Set

/-- Grinstead–Snell Definition 2.1 (PR-011). A continuous random variable with density `pdf X`
has law `volume.withDensity (pdf X)`, so `P(a ≤ X ≤ b)` is the integral of the density over
`[a, b]`. -/
@[kb "grinsteadsnell2006" "Definition 2.1, p. 67"]
theorem gs_definition_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) [HasPDF X P] (a b : ℝ) :
    P.map X = volume.withDensity (pdf X P volume) ∧
      P (X ⁻¹' Icc a b) = ∫⁻ x in Icc a b, pdf X P volume x := by
  refine ⟨map_eq_withDensity_pdf X P volume, ?_⟩
  rw [← Measure.map_apply_of_aemeasurable (HasPDF.aemeasurable X P volume) measurableSet_Icc,
    map_eq_withDensity_pdf X P volume, withDensity_apply _ measurableSet_Icc]

/-- Grinstead–Snell Definition 2.2 (PR-012). The cumulative distribution function of a random
variable with law `μ` is `F(x) = P(X ≤ x)`. -/
@[kb "grinsteadsnell2006" "Definition 2.2, p. 69"]
theorem gs_definition_2_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hX : HasLaw X μ P) (x : ℝ) :
    cdf μ x = P.real (X ⁻¹' Iic x) := by
  rw [cdf_eq_real, ← hX.map_eq, map_measureReal_apply_of_aemeasurable hX.aemeasurable
    measurableSet_Iic]

/-- Grinstead–Snell Example 2.7 (PR-014). A random point uniform on `[0,1]` has density `1` there
(almost everywhere), and every single point has probability zero. -/
@[kb "grinsteadsnell2006" "Example 2.7, p. 63"]
theorem gs_example_2_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : pdf.IsUniform X (Icc 0 1) P) :
    pdf X P volume =ᵐ[volume] (Icc (0 : ℝ) 1).indicator (1 : ℝ → ENNReal) ∧
      ∀ a : ℝ, P (X ⁻¹' {a}) = 0 := by
  refine ⟨?_, fun a => ?_⟩
  · simpa using hX.pdf_eq measurableSet_Icc
  · rw [hX.measure_preimage (measurableSet_singleton a)]
    rw [measure_mono_null Set.inter_subset_right (Real.volume_singleton), ENNReal.zero_div]

/-- Grinstead–Snell Example 2.17 (PR-017). The exponential density with rate `r > 0` integrates
to one, and its distribution function is `1 - e^(-r x)` for `x ≥ 0` and `0` below. -/
@[kb "grinsteadsnell2006" "Example 2.17, p. 74"]
theorem gs_example_2_17 {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (expMeasure r) ∧ ∫⁻ x, exponentialPDF r x = 1 ∧
      ∀ x : ℝ, cdf (expMeasure r) x = if 0 ≤ x then 1 - Real.exp (-(r * x)) else 0 :=
  have := isProbabilityMeasure_expMeasure hr
  ⟨this, lintegral_exponentialPDF_eq_one hr, cdf_expMeasure_eq hr⟩

/-- Grinstead–Snell Theorem 2.1 (PR-013). If `X` has density `f` then its cdf is the integral of `f`
up to `x`. -/
@[kb "grinsteadsnell2006" "Theorem 2.1, p. 69"]
theorem gs_theorem_2_1 : type_of% @UndergradKB.Probability.cdf_withDensity_eq_integral :=
  @UndergradKB.Probability.cdf_withDensity_eq_integral

/-- Grinstead–Snell Theorem 2.1 (PR-013), derivative form: `F'(x) = f(x)` where `f` is continuous. -/
@[kb "grinsteadsnell2006" "Theorem 2.1, p. 69"]
theorem gs_theorem_2_1_deriv : type_of% @UndergradKB.Probability.hasDerivAt_cdf_withDensity :=
  @UndergradKB.Probability.hasDerivAt_cdf_withDensity

/-- Grinstead–Snell Example 2.6 (PR-156). Bertrand's paradox, endpoint-angle model. -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem gs_example_2_6 : type_of% @UndergradKB.Probability.bertrand_angle :=
  @UndergradKB.Probability.bertrand_angle

/-- Grinstead–Snell Example 2.6 (PR-156). Bertrand's paradox, midpoint-distance model. -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem gs_example_2_6_b : type_of% @UndergradKB.Probability.bertrand_distance :=
  @UndergradKB.Probability.bertrand_distance

/-- Grinstead–Snell Example 2.6 (PR-156). Bertrand's paradox, midpoint-distance model on `[0, 1]`. -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem gs_example_2_6_c : type_of% @UndergradKB.Probability.bertrand_distance_unit :=
  @UndergradKB.Probability.bertrand_distance_unit

/-- Grinstead–Snell Example 2.6 (PR-156). Bertrand's paradox, uniform midpoint in the disk. -/
@[kb "grinsteadsnell2006" "Example 2.6, p. 55"]
theorem gs_example_2_6_d : type_of% @UndergradKB.Probability.bertrand_midpoint :=
  @UndergradKB.Probability.bertrand_midpoint

/-- Grinstead–Snell Example 2.13 (PR-135). The distribution function of the square of a uniform point. -/
@[kb "grinsteadsnell2006" "Example 2.13, p. 70"]
theorem gs_example_2_13 : type_of% @UndergradKB.Probability.uniform_sq_cdf :=
  @UndergradKB.Probability.uniform_sq_cdf

/-- Grinstead–Snell Example 2.13 (PR-135). The density of the square of a uniform point. -/
@[kb "grinsteadsnell2006" "Example 2.13, p. 70"]
theorem gs_example_2_13_b : type_of% @UndergradKB.Probability.uniform_sq_density :=
  @UndergradKB.Probability.uniform_sq_density

/-- Grinstead–Snell Example 2.16 (PR-153). The distribution function of the waiting time `|X - Y|`. -/
@[kb "grinsteadsnell2006" "Example 2.16, p. 73"]
theorem gs_example_2_16 : type_of% @UndergradKB.Probability.unitSquare_abs_sub_cdf :=
  @UndergradKB.Probability.unitSquare_abs_sub_cdf

/-- Grinstead–Snell Example 2.16 (PR-153). The density of the waiting time `|X - Y|`. -/
@[kb "grinsteadsnell2006" "Example 2.16, p. 73"]
theorem gs_example_2_16_b : type_of% @UndergradKB.Probability.unitSquare_abs_sub_cdf_eq_integral :=
  @UndergradKB.Probability.unitSquare_abs_sub_cdf_eq_integral

end UndergradKB.Probability.Course
