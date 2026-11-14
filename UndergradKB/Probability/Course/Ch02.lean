import Mathlib.Probability.Density
import Mathlib.Probability.CDF
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Exponential
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesSchoolC
import UndergradKB.Probability.ExamplesContinuous
import UndergradKB.Probability.ExamplesGeometric
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.Buffon
import UndergradKB.Probability.JointLaws
import UndergradKB.Probability.Transforms
import UndergradKB.Probability.ExamplesNormalApprox
import UndergradKB.Probability.ExamplesSchoolD

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

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 2.12 (PR-189). For the dart distance with density `2r` on `[0,1]`, the probability that `a ≤ r ≤ b` is `b² - a²` whenever `0 ≤ a ≤ b ≤ 1` (in particular the total mass is... -/
@[kb "grinsteadsnell2006" "Example 2.12, p. 68"]
theorem gs_example_2_12 : type_of% @UndergradKB.Probability.dart_radius_interval :=
  @UndergradKB.Probability.dart_radius_interval


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell Example 2.3 (PR-016). Buffon's needle with needle length equal to the line spacing `1`: the distance `X` from the needle's centre to the nearest line is uniform on `[0, 1/2]`, the acute angle `Θ` with the lines is uniform on `[0, π/2]`, and they are independent; the needle crosses a line iff `X ≤ sin Θ / 2`, which happens with probability `2/π`. -/
@[kb "grinsteadsnell2006" "Example 2.3, p. 52"]
theorem gs_example_2_3 : type_of% @UndergradKB.Probability.buffon_crossing_prob :=
  @UndergradKB.Probability.buffon_crossing_prob

/-- Grinstead–Snell Example 2.18 (PR-010). Infinitely many tosses of a fair coin: there is a probability measure on the sequence space `ℕ → Bool` under which the tosses are independent and each is heads with probability `1/2`; the sample space is uncountable. -/
@[kb "grinsteadsnell2006" "Example 2.18, p. 77"]
theorem gs_example_2_18 : type_of% @UndergradKB.Probability.infinite_fair_coin_tosses :=
  @UndergradKB.Probability.infinite_fair_coin_tosses

/-- Grinstead–Snell Examples 2.8 and 2.11 (PR-015). A point `X` uniform on the unit disk lies within distance `r` of the centre with probability `r²`, for `0 ≤ r ≤ 1`. -/
@[kb "grinsteadsnell2006" "Example 2.8, p. 64"]
theorem gs_example_2_8 : type_of% @UndergradKB.Probability.measureReal_norm_le_of_uniform_disk :=
  @UndergradKB.Probability.measureReal_norm_le_of_uniform_disk

/-- Grinstead–Snell Examples 2.8 and 2.11 (PR-015), density form: the distance `‖X‖` of a uniform point of the unit disk from the centre has density `2x` on `[0,1]`, i.e. `P(‖X‖ ≤ r) = ∫₀ʳ 2x dx`. -/
@[kb "grinsteadsnell2006" "Example 2.11, p. 67"]
theorem gs_example_2_11 : type_of% @UndergradKB.Probability.measureReal_norm_le_eq_integral_of_uniform_disk :=
  @UndergradKB.Probability.measureReal_norm_le_eq_integral_of_uniform_disk

/-- Grinstead–Snell Example 2.5 (PR-205). The sum of `100` independent numbers chosen uniformly in `[0, 1]` has mean `50` and variance `100/12`. -/
@[kb "grinsteadsnell2006" "Example 2.5, p. 55"]
theorem gs_example_2_5 : type_of% @UndergradKB.Probability.hundred_uniform_sum_moments :=
  @UndergradKB.Probability.hundred_uniform_sum_moments

/-- Grinstead–Snell Example 2.2 (PR-195). For a point `(x, y)` chosen uniformly in the unit square (Lebesgue measure on `[0,1] × [0,1]`, total mass `1`), the event `y ≤ x²` has probability `1/3`. -/
@[kb "grinsteadsnell2006" "Example 2.2, p. 50"]
theorem gs_example_2_2 : type_of% @UndergradKB.Probability.parabola_probability :=
  @UndergradKB.Probability.parabola_probability

end UndergradKB.Probability.Course
