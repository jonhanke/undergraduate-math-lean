import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesSchoolB
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.Sums
import UndergradKB.Probability.CauchyAverage
import UndergradKB.Probability.NormalFamilies
import UndergradKB.Probability.ExamplesTests
import UndergradKB.Probability.ExamplesBridge

/-!
# Course layer, Chapter 7 (Grinstead–Snell, Sums of Random Variables)

Thin wrappers stating the book's results of Chapter 7 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Grinstead–Snell Example 7.5 (PR-091). The sum of two independent normal random variables is
normal, with the means added and the variances added. -/
@[kb "grinsteadsnell2006" "Example 7.5, p. 302"]
theorem gs_example_7_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gaussianReal m₁ v₁) P) (hY : HasLaw Y (gaussianReal m₂ v₂) P) :
    P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂) :=
  gaussianReal_add_gaussianReal_of_indepFun hXY hX hY

/-- Grinstead–Snell Definition 7.1 (PR-087). For independent integer-valued `X`, `Y` the distribution
of `X + Y` is the convolution `m(j) = ∑_k m₁(k) m₂(j - k)`. -/
@[kb "grinsteadsnell2006" "Definition 7.1, p. 294"]
theorem gs_definition_7_1 : type_of% @UndergradKB.Probability.measure_add_eq_tsum_int :=
  @UndergradKB.Probability.measure_add_eq_tsum_int

/-- Grinstead–Snell Theorem 7.1 (PR-088). For independent `X`, `Y` with densities `f`, `g` the sum has
density `(f * g)(z) = ∫ f(z - y) g(y) dy`. -/
@[kb "grinsteadsnell2006" "Theorem 7.1, p. 299"]
theorem gs_theorem_7_1 : type_of% @UndergradKB.Probability.map_add_eq_withDensity_convolution :=
  @UndergradKB.Probability.map_add_eq_withDensity_convolution

/-- Grinstead–Snell Example 7.1 (PR-151). The distribution of the sum of two rolls of a fair die. -/
@[kb "grinsteadsnell2006" "Example 7.1, p. 294"]
theorem gs_example_7_1 : type_of% @UndergradKB.Probability.two_dice_sum_distribution :=
  @UndergradKB.Probability.two_dice_sum_distribution

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 7.2 (PR-169). One card. -/
@[kb "grinsteadsnell2006" "Example 7.2, p. 295"]
theorem gs_example_7_2 : type_of% @UndergradKB.Probability.bridge_card_point_law :=
  @UndergradKB.Probability.bridge_card_point_law

/-- Grinstead–Snell Example 7.2 (PR-169). The hand. -/
@[kb "grinsteadsnell2006" "Example 7.2, p. 295"]
theorem gs_example_7_2_b : type_of% @UndergradKB.Probability.bridge_hand_mean :=
  @UndergradKB.Probability.bridge_hand_mean


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell Example 7.6 (PR-092). The sum of two independent standard Cauchy random variables is Cauchy with scale parameter `2`. -/
@[kb "grinsteadsnell2006" "Example 7.6, p. 302"]
theorem gs_example_7_6 : type_of% @UndergradKB.Probability.cauchy_sum_two :=
  @UndergradKB.Probability.cauchy_sum_two

/-- Grinstead–Snell Example 7.6 (PR-092). The average of two independent standard Cauchy random variables is again standard Cauchy. -/
@[kb "grinsteadsnell2006" "Example 7.6, p. 302"]
theorem gs_example_7_6_b : type_of% @UndergradKB.Probability.cauchy_average_two :=
  @UndergradKB.Probability.cauchy_average_two

/-- Grinstead–Snell Example 7.7 (PR-060), gamma convolution. Two independent variables with gamma laws of the same rate `r` and shapes `a`, `b` have a sum with the gamma law of shape `a + b` and rate `r`. -/
@[kb "grinsteadsnell2006" "Example 7.7, p. 303"]
theorem gs_example_7_7 : type_of% @UndergradKB.Probability.map_add_gammaMeasure :=
  @UndergradKB.Probability.map_add_gammaMeasure

/-- Grinstead–Snell §5.2 chi-squared density and Example 7.7 (PR-060), `n` degrees of freedom. The sum of squares of `n ≥ 1` independent standard normal variables has the gamma law with shape `n/2` and rate `1/2` (chi-squared with `n` degrees of freedom). -/
@[kb "grinsteadsnell2006" "Example 7.7, p. 303"]
theorem gs_example_7_7_b : type_of% @UndergradKB.Probability.hasLaw_sum_sq_gammaMeasure :=
  @UndergradKB.Probability.hasLaw_sum_sq_gammaMeasure

/-- Grinstead–Snell Example 7.4 (PR-090), density identity. The convolution of two exponential densities of rate `r` is the gamma density with shape `2`: `∫ f (z - y) f y dy = r² z e^{-r z}` for `z ≥ 0` and `0` otherwise. -/
@[kb "grinsteadsnell2006" "Example 7.4, p. 300"]
theorem gs_example_7_4 : type_of% @UndergradKB.Probability.lintegral_gammaPDF_one_conv :=
  @UndergradKB.Probability.lintegral_gammaPDF_one_conv

/-- Grinstead–Snell Example 7.4 (PR-090), law statement. The sum of two independent exponential variables of rate `r` has the gamma law with shape `2` and rate `r`. -/
@[kb "grinsteadsnell2006" "Example 7.4, p. 300"]
theorem gs_example_7_4_b : type_of% @UndergradKB.Probability.map_add_expMeasure :=
  @UndergradKB.Probability.map_add_expMeasure

/-- Grinstead–Snell Examples 2.4, 2.14, 7.3, 7.9 (PR-089), density identity. The convolution of the indicator of `[0,1]` with itself is the triangular density. -/
@[kb "grinsteadsnell2006" "Example 7.3, p. 300"]
theorem gs_example_7_3 : type_of% @UndergradKB.Probability.lintegral_unitDensity_conv :=
  @UndergradKB.Probability.lintegral_unitDensity_conv

/-- Grinstead–Snell Examples 2.4, 2.14, 7.3, 7.9 (PR-089), as a real integral. For every `z`, `∫ 1_{[0,1]}(z - y) 1_{[0,1]}(y) dy` is the triangular density at `z`. -/
@[kb "grinsteadsnell2006" "Example 7.3, p. 300"]
theorem gs_example_7_3_b : type_of% @UndergradKB.Probability.integral_indicator_Icc_conv :=
  @UndergradKB.Probability.integral_indicator_Icc_conv

/-- Grinstead–Snell Examples 2.4, 2.14, 7.3, 7.9 (PR-089), law statement. The sum of two independent uniform `[0,1]` variables has the triangular density. -/
@[kb "grinsteadsnell2006" "Example 7.3, p. 300"]
theorem gs_example_7_3_c : type_of% @UndergradKB.Probability.map_add_uniform :=
  @UndergradKB.Probability.map_add_uniform

/-- Grinstead–Snell Example 7.8 (PR-203). (a) For the 60 rolls of Table 7.1 (frequencies 15, 8, 7, 5, 7, 18) the statistic `V = ∑ (o_i - 10)²/10` equals `136/10 = 13.6`. (b) For a fair die rolled `n ≥ 1` times (uniform measure on `Fin n → Fin 6`, expectation as the average over the `6^n` equally likely outcomes), the expected value of `V = ∑ (o_i - n/6)²/(n/6)` is exactly `5`. -/
@[kb "grinsteadsnell2006" "Example 7.8, p. 305"]
theorem gs_example_7_8 : type_of% @UndergradKB.Probability.chi_squared_die_test :=
  @UndergradKB.Probability.chi_squared_die_test

/-! ## Wave 6 course layer (this library) -/

/-- Grinstead–Snell Example 7.2 (PR-169), the tail. Regarding a hand of `13` cards as `13` independent trials with the one-card distribution (the product of `13` copies of the uniform measure on `Fin 52`), the point count `C = ∑ⱼ (point count of card j)` satisfies `P(C ≥ 13) = 5782330171546220363776 / 52^13`, which lies in `(.2844, .2846)` (book: `.2845`). -/
@[kb "grinsteadsnell2006" "Example 7.2, p. 295"]
theorem gs_example_7_2_c : type_of% @UndergradKB.Probability.bridge_hand_tail :=
  @UndergradKB.Probability.bridge_hand_tail

end UndergradKB.Probability.Course
