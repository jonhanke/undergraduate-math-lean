import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Density
import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesExpectation
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.ExamplesGeometric
import UndergradKB.Probability.Basic
import UndergradKB.Probability.Moments
import UndergradKB.Probability.Transforms

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

/-! ### Continuous counterparts, and results proved in `UndergradKB.Probability` -/

/-- Grinstead–Snell Theorem 6.10 (PR-067). Linearity of expectation for continuous random variables
(the same statement as Theorem 6.2: Mathlib's expectation is one integral). -/
@[kb "grinsteadsnell2006" "Theorem 6.10, p. 277"]
theorem gs_theorem_6_10 : type_of% @gs_theorem_6_2 := @gs_theorem_6_2

/-- Grinstead–Snell Theorem 6.12 (PR-069). `E(XY) = E(X) E(Y)` for independent continuous variables
(same statement as Theorem 6.4). -/
@[kb "grinsteadsnell2006" "Theorem 6.12, p. 278"]
theorem gs_theorem_6_12 : type_of% @gs_theorem_6_4 := @gs_theorem_6_4

/-- Grinstead–Snell Definition 6.5 (PR-071). The variance of a continuous random variable is
`E((X - μ)²)` (same statement as Definition 6.3). -/
@[kb "grinsteadsnell2006" "Definition 6.5, p. 279"]
theorem gs_definition_6_5 : type_of% @gs_definition_6_3 := @gs_definition_6_3

/-- Grinstead–Snell Theorem 6.14 (PR-073). `V(cX) = c² V(X)` and `V(X + c) = V(X)` (same statement as
Theorem 6.7). -/
@[kb "grinsteadsnell2006" "Theorem 6.14, p. 280"]
theorem gs_theorem_6_14 : type_of% @gs_theorem_6_7 := @gs_theorem_6_7

/-- Grinstead–Snell Theorem 6.15 (PR-072). `V(X) = E(X²) - E(X)²` (same statement as Theorem 6.6). -/
@[kb "grinsteadsnell2006" "Theorem 6.15, p. 280"]
theorem gs_theorem_6_15 : type_of% @gs_theorem_6_6 := @gs_theorem_6_6

/-- Grinstead–Snell Theorem 6.16 (PR-074). Variances of independent continuous variables add (same
statement as Theorem 6.8). -/
@[kb "grinsteadsnell2006" "Theorem 6.16, p. 280"]
theorem gs_theorem_6_16 : type_of% @gs_theorem_6_8 := @gs_theorem_6_8

/-- Grinstead–Snell Definition 6.2 (PR-070). The conditional expectation `E(X | F)` given an event is
the expectation under the conditioned measure. -/
@[kb "grinsteadsnell2006" "Definition 6.2, p. 247"]
theorem gs_definition_6_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (F : Set Ω) :
    condExpEvent P X F = ∫ ω, X ω ∂(P[|F]) :=
  rfl

/-- Grinstead–Snell Theorem 6.5 (PR-070). For a partition `F j` of positive probabilities,
`E(X) = ∑ E(X | F j) P(F j)`. -/
@[kb "grinsteadsnell2006" "Theorem 6.5, p. 247"]
theorem gs_theorem_6_5 : type_of% @UndergradKB.Probability.integral_eq_sum_condExpEvent :=
  @UndergradKB.Probability.integral_eq_sum_condExpEvent

/-- Grinstead–Snell Theorem 6.9 (PR-075). For an independent trials process `S_n` has mean `n μ` and
variance `n σ²`. -/
@[kb "grinsteadsnell2006" "Theorem 6.9, p. 268"]
theorem gs_theorem_6_9 : type_of% @UndergradKB.Probability.sum_mean_variance :=
  @UndergradKB.Probability.sum_mean_variance

/-- Grinstead–Snell Corollary 6.1 (PR-075). The average `A_n = S_n/n` has mean `μ` and variance
`σ²/n`. -/
@[kb "grinsteadsnell2006" "Corollary 6.1, p. 283"]
theorem gs_corollary_6_1 : type_of% @UndergradKB.Probability.average_mean_variance :=
  @UndergradKB.Probability.average_mean_variance

/-- Grinstead–Snell Theorem 6.13 (PR-076). For a variable with density `f` the variance is
`∫ (x - μ)² f(x) dx`. -/
@[kb "grinsteadsnell2006" "Theorem 6.13, p. 280"]
theorem gs_theorem_6_13 : type_of% @UndergradKB.Probability.variance_eq_integral_pdf :=
  @UndergradKB.Probability.variance_eq_integral_pdf

/-- Grinstead–Snell Example 6.1 (PR-130). The expected number of heads in three fair tosses is `3/2`. -/
@[kb "grinsteadsnell2006" "Example 6.1, p. 234"]
theorem gs_example_6_1 : type_of% @UndergradKB.Probability.threeTosses_expected_heads :=
  @UndergradKB.Probability.threeTosses_expected_heads

/-- Grinstead–Snell Example 6.2 (PR-137). The expected number of tosses until the first head is `2`. -/
@[kb "grinsteadsnell2006" "Example 6.2, p. 234"]
theorem gs_example_6_2 : type_of% @UndergradKB.Probability.first_head_mean :=
  @UndergradKB.Probability.first_head_mean

/-- Grinstead–Snell Example 6.3 (PR-137). The St. Petersburg payment is not integrable (law form). -/
@[kb "grinsteadsnell2006" "Example 6.3, p. 235"]
theorem gs_example_6_3 : type_of% @UndergradKB.Probability.st_petersburg_not_integrable :=
  @UndergradKB.Probability.st_petersburg_not_integrable

/-- Grinstead–Snell Example 6.3 (PR-137). The St. Petersburg payment is not integrable (random-variable form). -/
@[kb "grinsteadsnell2006" "Example 6.3, p. 235"]
theorem gs_example_6_3_b : type_of% @UndergradKB.Probability.st_petersburg_payment :=
  @UndergradKB.Probability.st_petersburg_payment

/-- Grinstead–Snell Example 6.6 (PR-130). The expected number of runs in three fair tosses is `2`. -/
@[kb "grinsteadsnell2006" "Example 6.6, p. 237"]
theorem gs_example_6_6 : type_of% @UndergradKB.Probability.threeTosses_expected_runs :=
  @UndergradKB.Probability.threeTosses_expected_runs

/-- Grinstead–Snell Example 6.9 (PR-138). The expectation of a product for two independent fair tosses. -/
@[kb "grinsteadsnell2006" "Example 6.9, p. 242"]
theorem gs_example_6_9 : type_of% @UndergradKB.Probability.two_tosses_product :=
  @UndergradKB.Probability.two_tosses_product

/-- Grinstead–Snell Example 6.10 (PR-138). The expectation of a product of dependent variables `X` and `1 - X`. -/
@[kb "grinsteadsnell2006" "Example 6.10, p. 242"]
theorem gs_example_6_10 : type_of% @UndergradKB.Probability.one_toss_dependent_product :=
  @UndergradKB.Probability.one_toss_dependent_product

/-- Grinstead–Snell Example 6.12 (PR-139). The probability of winning at craps is `244/495`. -/
@[kb "grinsteadsnell2006" "Example 6.12, p. 243"]
theorem gs_example_6_12 : type_of% @UndergradKB.Probability.craps_win_probability :=
  @UndergradKB.Probability.craps_win_probability

/-- Grinstead–Snell Example 6.12 (PR-139). Stage two of craps: the point comes before a seven. -/
@[kb "grinsteadsnell2006" "Example 6.12, p. 243"]
theorem gs_example_6_12_b : type_of% @UndergradKB.Probability.craps_point_before_seven :=
  @UndergradKB.Probability.craps_point_before_seven

/-- Grinstead–Snell Example 6.12 (PR-139). Stage two of craps for the dice, for each point. -/
@[kb "grinsteadsnell2006" "Example 6.12, p. 243"]
theorem gs_example_6_12_c : type_of% @UndergradKB.Probability.craps_point_series :=
  @UndergradKB.Probability.craps_point_series

/-- Grinstead–Snell Example 6.13 (PR-140). The expected winnings at roulette on a Las Vegas wheel. -/
@[kb "grinsteadsnell2006" "Example 6.13, p. 245"]
theorem gs_example_6_13 : type_of% @UndergradKB.Probability.roulette_expected_winnings :=
  @UndergradKB.Probability.roulette_expected_winnings

/-- Grinstead–Snell Example 6.14 (PR-152). The mean of the geometric waiting time. -/
@[kb "grinsteadsnell2006" "Example 6.14, p. 248"]
theorem gs_example_6_14 : type_of% @UndergradKB.Probability.geometric_waiting_mean :=
  @UndergradKB.Probability.geometric_waiting_mean

/-- Grinstead–Snell Example 6.14 (PR-152). The expected number of rolls in a play of craps is `557/165`. -/
@[kb "grinsteadsnell2006" "Example 6.14, p. 248"]
theorem gs_example_6_14_b : type_of% @UndergradKB.Probability.craps_expected_rolls :=
  @UndergradKB.Probability.craps_expected_rolls

/-- Grinstead–Snell Example 6.14 (PR-152). The mean number of further rolls in the second stage of craps. -/
@[kb "grinsteadsnell2006" "Example 6.14, p. 248"]
theorem gs_example_6_14_c : type_of% @UndergradKB.Probability.craps_second_stage_mean :=
  @UndergradKB.Probability.craps_second_stage_mean

/-- Grinstead–Snell Example 6.17 (PR-141). The mean and variance of one roll of a die, on `Fin 6`. -/
@[kb "grinsteadsnell2006" "Example 6.17, p. 265"]
theorem gs_example_6_17 : type_of% @UndergradKB.Probability.die_mean_variance :=
  @UndergradKB.Probability.die_mean_variance

/-- Grinstead–Snell Example 6.17 (PR-141). The mean and variance of a variable with the law of a die roll. -/
@[kb "grinsteadsnell2006" "Example 6.17, p. 265"]
theorem gs_example_6_17_b : type_of% @UndergradKB.Probability.die_law_mean_variance :=
  @UndergradKB.Probability.die_law_mean_variance

/-- Grinstead–Snell Example 6.18 (PR-141). The variance of the average of independent die rolls. -/
@[kb "grinsteadsnell2006" "Example 6.18, p. 269"]
theorem gs_example_6_18 : type_of% @UndergradKB.Probability.die_average_variance :=
  @UndergradKB.Probability.die_average_variance

/-- Grinstead–Snell Example 6.21 (PR-154). The expected distance of a uniform point of the disk from the center is `2/3`. -/
@[kb "grinsteadsnell2006" "Example 6.21, p. 277"]
theorem gs_example_6_21 : type_of% @UndergradKB.Probability.integral_norm_uniform_disk :=
  @UndergradKB.Probability.integral_norm_uniform_disk

/-- Grinstead–Snell Example 6.21 (PR-154). The same expectation through the density `2x`. -/
@[kb "grinsteadsnell2006" "Example 6.21, p. 277"]
theorem gs_example_6_21_b : type_of% @UndergradKB.Probability.integral_mul_density_disk :=
  @UndergradKB.Probability.integral_mul_density_disk

/-- Grinstead–Snell Example 6.22 (PR-153). The expected meeting waiting time `E(Z) = 1/3`, through the density. -/
@[kb "grinsteadsnell2006" "Example 6.22, p. 277"]
theorem gs_example_6_22 : type_of% @UndergradKB.Probability.integral_mul_density_meeting :=
  @UndergradKB.Probability.integral_mul_density_meeting

/-- Grinstead–Snell Example 6.22 (PR-153). The same expectation computed directly on the unit square. -/
@[kb "grinsteadsnell2006" "Example 6.22, p. 277"]
theorem gs_example_6_22_b : type_of% @UndergradKB.Probability.integral_abs_sub_unitSquare :=
  @UndergradKB.Probability.integral_abs_sub_unitSquare

/-- Grinstead–Snell Example 6.23 (PR-155). Expectations of `X²` and `Y²` for a uniform point of the unit square. -/
@[kb "grinsteadsnell2006" "Example 6.23, p. 279"]
theorem gs_example_6_23 : type_of% @UndergradKB.Probability.unitSquare_sq_expectations :=
  @UndergradKB.Probability.unitSquare_sq_expectations

/-- Grinstead–Snell Example 6.24 (PR-155). Expectations of `Y` and `W = X + Y` for a uniform point of the unit square. -/
@[kb "grinsteadsnell2006" "Example 6.24, p. 279"]
theorem gs_example_6_24 : type_of% @UndergradKB.Probability.unitSquare_Y_W_expectations :=
  @UndergradKB.Probability.unitSquare_Y_W_expectations

end UndergradKB.Probability.Course
