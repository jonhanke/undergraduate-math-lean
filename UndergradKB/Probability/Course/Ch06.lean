import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Density
import Mathlib.Probability.HasLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesSchoolB
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesExpectation
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.ExamplesGeometric
import UndergradKB.Probability.Basic
import UndergradKB.Probability.Moments
import UndergradKB.Probability.Transforms
import UndergradKB.Probability.Combinatorial
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.DiscreteDistributions
import UndergradKB.Probability.ExamplesQueueStock
import UndergradKB.Probability.ExamplesSchoolD
import UndergradKB.Probability.LittleLaw
import UndergradKB.Probability.QueueContinuous
import UndergradKB.Probability.QueueConvergence
import UndergradKB.Probability.QueueEquilibrium
import UndergradKB.Probability.QueueForward
import UndergradKB.Probability.LittleLawAe
import UndergradKB.Probability.QueueArrivals
import UndergradKB.Probability.QueueForwardUnique
import UndergradKB.Probability.QueueStart
import UndergradKB.Probability.QueueStartTime
import UndergradKB.Probability.QueueUniformization

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

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 6.7 (PR-168). Flip a coin (`X = 1` for heads, `0` for tails) and roll a die (`Y` the face); the pair `(X, Y)` is uniform on the `12` outcomes of `Bool × Fin 6`. -/
@[kb "grinsteadsnell2006" "Example 6.7, p. 238"]
theorem gs_example_6_7 : type_of% @UndergradKB.Probability.coin_plus_die_expectation :=
  @UndergradKB.Probability.coin_plus_die_expectation


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell §6.3 covariance (PR-078). Independent random variables with finite second moments are uncorrelated: `ρ(X, Y) = 0`. -/
@[kb "grinsteadsnell2006" "§6.3 correlation, p. 289"]
theorem gs_section_6_3_correlation : type_of% @UndergradKB.Probability.IndepFun.correlation_eq_zero :=
  @UndergradKB.Probability.IndepFun.correlation_eq_zero

/-- Grinstead–Snell §6.3 correlation (PR-078). The correlation coefficient satisfies `|ρ(X, Y)| ≤ 1`. -/
@[kb "grinsteadsnell2006" "§6.3 correlation, p. 289"]
theorem gs_section_6_3_correlation_b : type_of% @UndergradKB.Probability.abs_correlation_le_one :=
  @UndergradKB.Probability.abs_correlation_le_one

/-- Grinstead–Snell Example 6.8 (PR-085). Summed over all permutations of `n ≥ 1` points, the number of fixed points is `n!`; hence the expected number of fixed points of a uniformly random permutation is `1`. -/
@[kb "grinsteadsnell2006" "Example 6.8, p. 240"]
theorem gs_example_6_8 : type_of% @UndergradKB.Probability.sum_fixedPoints_card :=
  @UndergradKB.Probability.sum_fixedPoints_card

/-- Grinstead–Snell Example 6.8 (PR-085), as an average: the mean number of fixed points over all `n!` permutations of `n ≥ 1` points equals `1`, i.e. the expected value under the uniform distribution on permutations. -/
@[kb "grinsteadsnell2006" "Example 6.8, p. 240"]
theorem gs_example_6_8_b : type_of% @UndergradKB.Probability.average_fixedPoints_card :=
  @UndergradKB.Probability.average_fixedPoints_card

/-- Grinstead–Snell Example 6.11 (PR-084). Summed over all permutations, the number of records is `∑_{i<n} n!/(i+1)`, i.e. position `i` is a record for `n!/(i+1)` permutations. -/
@[kb "grinsteadsnell2006" "Example 6.11, p. 242"]
theorem gs_example_6_11 : type_of% @UndergradKB.Probability.sum_records_card :=
  @UndergradKB.Probability.sum_records_card

/-- Grinstead–Snell Example 6.11 (PR-084). The expected number of records of a uniformly random permutation of `n` values is `1 + 1/2 + ... + 1/n`. -/
@[kb "grinsteadsnell2006" "Example 6.11, p. 242"]
theorem gs_example_6_11_b : type_of% @UndergradKB.Probability.average_records_card :=
  @UndergradKB.Probability.average_records_card

/-- Grinstead–Snell Example 6.26 (PR-081). An exponential law with rate `r > 0` has mean `1/r`. -/
@[kb "grinsteadsnell2006" "Example 6.26, p. 281"]
theorem gs_example_6_26 : type_of% @UndergradKB.Probability.integral_expMeasure :=
  @UndergradKB.Probability.integral_expMeasure

/-- Grinstead–Snell Example 6.26 (PR-081). An exponential law with rate `r > 0` has variance `1/r^2`. -/
@[kb "grinsteadsnell2006" "Example 6.26, p. 281"]
theorem gs_example_6_26_b : type_of% @UndergradKB.Probability.variance_expMeasure :=
  @UndergradKB.Probability.variance_expMeasure

/-- Grinstead–Snell Example 6.20 (PR-080). The uniform law on `[0,1]` has mean `1/2`. -/
@[kb "grinsteadsnell2006" "Example 6.20, p. 277"]
theorem gs_example_6_20 : type_of% @UndergradKB.Probability.integral_uniform_Icc :=
  @UndergradKB.Probability.integral_uniform_Icc

/-- Grinstead–Snell Example 6.25 (PR-080). The uniform law on `[0,1]` has variance `1/12`. -/
@[kb "grinsteadsnell2006" "Example 6.25, p. 280"]
theorem gs_example_6_25 : type_of% @UndergradKB.Probability.variance_uniform_Icc :=
  @UndergradKB.Probability.variance_uniform_Icc

/-- Grinstead–Snell Examples 6.20 and 6.25 (PR-080), random-variable form: a random variable uniform on `[0,1]` has mean `1/2`. -/
@[kb "grinsteadsnell2006" "Example 6.20, p. 277"]
theorem gs_example_6_20_b : type_of% @UndergradKB.Probability.integral_of_isUniform_Icc :=
  @UndergradKB.Probability.integral_of_isUniform_Icc

/-- Grinstead–Snell Examples 6.20 and 6.25 (PR-080), random-variable form: a random variable uniform on `[0,1]` has variance `1/12`. -/
@[kb "grinsteadsnell2006" "Example 6.25, p. 280"]
theorem gs_example_6_25_b : type_of% @UndergradKB.Probability.variance_of_isUniform_Icc :=
  @UndergradKB.Probability.variance_of_isUniform_Icc

/-- Grinstead–Snell Example 6.28 (PR-083). The standard Cauchy law has no expected value: `id` is not integrable, i.e. `∫ |x| / (π (1 + x^2))` diverges. -/
@[kb "grinsteadsnell2006" "Example 6.28, p. 282"]
theorem gs_example_6_28 : type_of% @UndergradKB.Probability.not_integrable_cauchyMeasure :=
  @UndergradKB.Probability.not_integrable_cauchyMeasure

/-- Grinstead–Snell §6.2, standardized random variable (PR-077). If `X` has finite variance `σ²` with `σ > 0` and mean `μ`, then `X* = (X - μ) / σ` has mean `0`. -/
@[kb "grinsteadsnell2006" "§6.2 standardized random variable, p. 272"]
theorem gs_section_6_2_standardized_random_variable : type_of% @UndergradKB.Probability.integral_standardize :=
  @UndergradKB.Probability.integral_standardize

/-- Grinstead–Snell §6.2, standardized random variable (PR-077). If `X` has finite variance `σ²` with `σ > 0`, then `X* = (X - μ) / σ` has variance `1`. -/
@[kb "grinsteadsnell2006" "§6.2 standardized random variable, p. 272"]
theorem gs_section_6_2_standardized_random_variable_b : type_of% @UndergradKB.Probability.variance_standardize :=
  @UndergradKB.Probability.variance_standardize

/-- Grinstead–Snell Example 6.4 (PR-079), law form: the mean of the number of trials up to the first success is `1/p`. -/
@[kb "grinsteadsnell2006" "Example 6.4, p. 236"]
theorem gs_example_6_4 : type_of% @UndergradKB.Probability.trialsLaw_mean :=
  @UndergradKB.Probability.trialsLaw_mean

/-- Grinstead–Snell Example 6.19 (PR-079), law form: the variance of the number of trials up to the first success is `q / p²`, where `q = 1 - p`. -/
@[kb "grinsteadsnell2006" "Example 6.19, p. 270"]
theorem gs_example_6_19 : type_of% @UndergradKB.Probability.trialsLaw_variance_integral :=
  @UndergradKB.Probability.trialsLaw_variance_integral

/-- Grinstead–Snell Example 6.4 (PR-079), random variable form: if `X` counts the trials up to and including the first success (law `trialsLaw p`), then `E(X) = 1/p`. -/
@[kb "grinsteadsnell2006" "Example 6.4, p. 236"]
theorem gs_example_6_4_b : type_of% @UndergradKB.Probability.geometric_expectation :=
  @UndergradKB.Probability.geometric_expectation

/-- Grinstead–Snell Example 6.19 (PR-079), random variable form: with `X` as above, `V(X) = q / p²`. -/
@[kb "grinsteadsnell2006" "Example 6.19, p. 270"]
theorem gs_example_6_19_b : type_of% @UndergradKB.Probability.geometric_variance :=
  @UndergradKB.Probability.geometric_variance

/-- Grinstead–Snell Example 6.15 (PR-086). In the fair heads-or-tails game, the steps `X i` are independent, each `+1` or `-1` with probability `1/2`; the fortune `S_n` has mean `0` and variance `n`. -/
@[kb "grinsteadsnell2006" "Example 6.15, p. 249"]
theorem gs_example_6_15 : type_of% @UndergradKB.Probability.fair_game_mean_variance :=
  @UndergradKB.Probability.fair_game_mean_variance

/-- Grinstead–Snell Example 6.29 (PR-209), the means: exponential interarrival and service times with rates `λ, μ > 0` have means `1/λ` and `1/μ`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29 : type_of% @UndergradKB.Probability.queue_exponential_means :=
  @UndergradKB.Probability.queue_exponential_means

/-- Grinstead–Snell Example 6.29 (PR-209), the equilibrium queue length. For arrival rate `λ`, service rate `μ` with traffic intensity `ρ = λ/μ < 1`, the law `s_j = (1-ρ)ρ^j` is a probability law with mean `ρ/(1-ρ)` which satisfies the detailed balance equations `λ s_j = μ s_{j+1}` and the global balance equations of the birth-death chain (`λ s_0 = μ s_1` and `(λ+μ) s_{j+1} = λ s_j + μ s_{j+2}`). -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_b : type_of% @UndergradKB.Probability.queue_geometric_equilibrium :=
  @UndergradKB.Probability.queue_geometric_equilibrium

/-- Grinstead–Snell Example 6.29 (PR-209), Little's law consequence. With `ρ = λ/μ < 1`, the geometric law has mean `N = ρ/(1-ρ)`; if Little's law `N = λ T` holds (the book does not prove it, and here it is the hypothesis `hL` on the numbers `N`, `T`), then `T = 1/(μ - λ)`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_c : type_of% @UndergradKB.Probability.queue_little_waiting_time :=
  @UndergradKB.Probability.queue_little_waiting_time

/-- Grinstead–Snell Example 6.16 (PR-208), expected winnings. On the fair `±1` walk (uniform measure on `Fin n → Bool`) Mr. Ace's winnings (the sum over days of the holding indicator, which depends only on earlier moves, times the move) have expectation exactly `0`, for every number `n` of days. -/
@[kb "grinsteadsnell2006" "Example 6.16, p. 249"]
theorem gs_example_6_16 : type_of% @UndergradKB.Probability.ace_expected_winnings :=
  @UndergradKB.Probability.ace_expected_winnings

/-- Grinstead–Snell Example 6.16 (PR-208), ahead after 20 days. Exactly `639771` of the `2^20` equally likely 20-day paths leave Mr. Ace with positive winnings, so he is ahead with probability `639771/2^20 = .61013…`, the book's "about .610"; yet the expectation is `0` (`ace_expected_winnings`). -/
@[kb "grinsteadsnell2006" "Example 6.16, p. 249"]
theorem gs_example_6_16_b : type_of% @UndergradKB.Probability.ace_ahead_after_20_days :=
  @UndergradKB.Probability.ace_ahead_after_20_days

/-- Grinstead–Snell Example 6.5 (PR-202). The average of the twelve heights `69, 69, 66, 68, 71, 65, 67, 66, 66, 67, 70, 72` is exactly `816/12 = 68`, and this is the expected value of the height `X` of a player chosen uniformly at random. Erratum: the book prints `67.9`; the correct value is `68` (the sum is `816`). -/
@[kb "grinsteadsnell2006" "Example 6.5, p. 236"]
theorem gs_example_6_5 : type_of% @UndergradKB.Probability.team_heights_expectation :=
  @UndergradKB.Probability.team_heights_expectation

/-! ## wave 7 course layer (this library) -/

/-- Grinstead–Snell Example 6.29 (PR-209), Little's law `N = λT` along a sample path. Customer `i` arrives at time `a i` (nondecreasing, `a 0 ≥ 0`) and stays `w i ≥ 0` in the system; `N(t)` is the number in the system at time `t`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_d : type_of% @UndergradKB.Probability.little_law_sample_path :=
  @UndergradKB.Probability.little_law_sample_path

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium in continuous time. Let the arrival rate be `λ > 0` and the service rate `μ > λ`, `ρ = λ/μ`. Started from an empty queue, the law at time `t` of the queue length (`queueLawTime`, by uniformization) converges to the geometric law: for every `k`, `P(queue length at time t = k) → (1-ρ)ρ^k` as `t → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_e : type_of% @UndergradKB.Probability.queue_time_law_tendsto_geometric :=
  @UndergradKB.Probability.queue_time_law_tendsto_geometric

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium. Let the arrival rate be `λ > 0` and the service rate `μ > λ`, `ρ = λ/μ`. Started from an empty queue, the law of the jump chain of the queue (`queueLaw`, the laws of `queueJump` by `queueLaw_step`) converges to the geometric law: for every queue length `k`, `P(X_n = k) → (1-ρ)ρ^k` as `n → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_f : type_of% @UndergradKB.Probability.queue_law_tendsto_geometric :=
  @UndergradKB.Probability.queue_law_tendsto_geometric

/-- Grinstead–Snell Example 6.29 (PR-209), uniqueness of the equilibrium law. Let the arrival rate be `λ > 0` and the service rate `μ > 0`. If a probability law `s` on the queue lengths `0, 1, 2, …` solves the global balance equations of the queue, `λ s_0 = μ s_1` and `(λ+μ) s_{j+1} = λ s_j + μ s_{j+2}`, then `λ < μ` and `s_j = (1-ρ)ρ^j` with `ρ = λ/μ`: the geometric law of the book is the only equili... -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_g : type_of% @UndergradKB.Probability.queue_balance_unique :=
  @UndergradKB.Probability.queue_balance_unique

/-- Grinstead–Snell Example 6.29 (PR-209), the equilibrium of the jump chain. For arrival rate `λ > 0` and service rate `μ > 0`, a probability law `s` on `ℕ` is stationary for the jump chain `queueJump` of the queue (`∑_i s_i P(i,k) = s_k` for every `k`) if and only if `λ < μ` and `s` is the geometric law `(1-ρ)ρ^j`, `ρ = λ/μ`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_h : type_of% @UndergradKB.Probability.queue_jump_stationary_iff :=
  @UndergradKB.Probability.queue_jump_stationary_iff

/-- Grinstead–Snell Example 6.29 (PR-209), the forward equations. For arrival rate `λ > 0` and service rate `μ > 0`, the law `p_t` of the queue length at time `t` (`queueLawTime`, by uniformization, started from an empty queue) solves the Kolmogorov forward equations of the queue: `p_0(k) = [k = 0]`, `p_t'(0) = -λ p_t(0) + μ p_t(1)` and `p_t'(k+1) = λ p_t(k) - (λ+μ) p_t(k+1) + μ p_t(k+2)` for every re... -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_i : type_of% @UndergradKB.Probability.queue_forward_equations :=
  @UndergradKB.Probability.queue_forward_equations

/-! ## wave 8 course layer (this library) -/

/-- Grinstead–Snell Example 6.29 (PR-209), Little's law almost surely. Let the interarrival times `X_0, X_1, …` be independent exponential variables with rate `λ > 0` (customer `n` arrives at `a_n = X_0 + ⋯ + X_n`), and let customer `i` stay `w_i ≥ 0` in the system. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_j : type_of% @UndergradKB.Probability.little_law_ae :=
  @UndergradKB.Probability.little_law_ae

/-- Grinstead–Snell Example 6.29 (PR-209), arrivals see the equilibrium. Let `λ > 0` and `μ > λ`, `ρ = λ/μ`. Drive the jump chain of the queue by independent variables `Z 0` (the initial queue length, with the geometric law `(1-ρ)ρ^k`) and `Z (n+1)` (the coin of ring `n`: an arrival, value `1`, with probability `λ/(λ+μ)`). -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_k : type_of% @UndergradKB.Probability.queue_arrivals_see_equilibrium :=
  @UndergradKB.Probability.queue_arrivals_see_equilibrium

/-- Grinstead–Snell Example 6.29 (PR-209), arrivals see the equilibrium in the limit. As in `queue_arrivals_see_equilibrium`, but the queue starts with `j` customers (`Z 0 = j` almost surely): the conditional probability that the customer arriving at ring `n` finds `k` customers tends to `(1-ρ)ρ^k` as `n → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_l : type_of% @UndergradKB.Probability.queue_arrivals_see_equilibrium_limit :=
  @UndergradKB.Probability.queue_arrivals_see_equilibrium_limit

/-- Grinstead–Snell Example 6.29 (PR-209), the law of the queue is determined by its forward equations. For arrival rate `λ > 0` and service rate `μ > 0`, let `p_t(k)` be bounded on `t ≥ 0` (for instance, each `p_t` a probability law), solve the Kolmogorov forward equations of the queue on `t ≥ 0`, and start with `j` customers (`p_0(k) = [k = j]`). -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_m : type_of% @UndergradKB.Probability.queue_forward_determines_law :=
  @UndergradKB.Probability.queue_forward_determines_law

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium from any start. Let the arrival rate be `λ > 0` and the service rate `μ > λ`, `ρ = λ/μ`. Started with `j` customers, the law of the jump chain of the queue (`queueLawFrom j`, the laws of `queueJump` by `queueLawFrom_step`) converges to the geometric law: for every queue length `k`, `P(X_n = k) → (1-ρ)ρ^k` as `n → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_n : type_of% @UndergradKB.Probability.queue_law_from_tendsto_geometric :=
  @UndergradKB.Probability.queue_law_from_tendsto_geometric

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium from any initial law. Let `λ > 0`, `μ > λ`, `ρ = λ/μ`, and let the initial queue length have law `π` (a probability law on `ℕ`). Then the law of the jump chain of the queue after `n` steps converges to the geometric law: `P(X_n = k) → (1-ρ)ρ^k`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_o : type_of% @UndergradKB.Probability.queue_law_mix_tendsto_geometric :=
  @UndergradKB.Probability.queue_law_mix_tendsto_geometric

/-- Grinstead–Snell Example 6.29 (PR-209), the forward equations from any start. For arrival rate `λ > 0` and service rate `μ > 0`, the law `p_t` of the queue length at time `t` started with `j` customers (`queueLawTimeFrom j`, by uniformization) solves the Kolmogorov forward equations of the queue: `p_0(k) = [k = j]`, `p_t'(0) = -λ p_t(0) + μ p_t(1)` and `p_t'(k+1) = λ p_t(k) - (λ+μ) p_t(k+1) + μ p_t... -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_p : type_of% @UndergradKB.Probability.queue_forward_equations_from :=
  @UndergradKB.Probability.queue_forward_equations_from

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium in continuous time from any start. Let `λ > 0`, `μ > λ`, `ρ = λ/μ`. Started with `j` customers, the law at time `t` of the queue length (`queueLawTimeFrom j`) converges to the geometric law: `P(queue length at time t = k) → (1-ρ)ρ^k` as `t → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_q : type_of% @UndergradKB.Probability.queue_time_law_from_tendsto_geometric :=
  @UndergradKB.Probability.queue_time_law_from_tendsto_geometric

/-- Grinstead–Snell Example 6.29 (PR-209), the queue in continuous time by uniformization. Let `λ, μ > 0`. Let the clock gaps `X_0, X_1, …` be independent exponential variables with rate `λ + μ`, let `Y_0, Y_1, …` be the queue lengths of the jump chain started with `j` customers (`P(Y_n = k) = queueLawFrom j n k`, the laws of `queueJump` by `queueLawFrom_step`), and let the clock be independent of the... -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem gs_example_6_29_r : type_of% @UndergradKB.Probability.queue_uniformization_law :=
  @UndergradKB.Probability.queue_uniformization_law

end UndergradKB.Probability.Course
