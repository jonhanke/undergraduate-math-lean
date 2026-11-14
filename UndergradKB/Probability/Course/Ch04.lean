import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.Beta
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesSchoolC
import UndergradKB.Probability.ExamplesSchoolB
import UndergradKB.Probability.ExamplesParadoxes
import UndergradKB.Probability.ExamplesChebyshev
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.ExamplesContinuous
import UndergradKB.Probability.ExamplesLimits
import UndergradKB.Probability.JointLaws
import UndergradKB.Probability.GeneratingFunctions
import UndergradKB.Probability.IndepDensity
import UndergradKB.Probability.Basic
import UndergradKB.Probability.ContinuousDistributions
import UndergradKB.Probability.ExamplesSchoolD

/-!
# Course layer, Chapter 4 (Grinstead–Snell, Conditional Probability)

Thin wrappers stating the book's results of Chapter 4 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory

/-- Grinstead–Snell §4.1 conditional probability (PR-036). For an event `E` of positive
probability, `P(F | E) = P(E ∩ F) / P(E)`, and `P(· | E)` is again a probability measure. -/
@[kb "grinsteadsnell2006" "§4.1 conditional probability, p. 143"]
theorem gs_section_4_1_conditional_probability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Set Ω} (hE : MeasurableSet E) (hpos : P E ≠ 0) (F : Set Ω) :
    P[F | E] = (P E)⁻¹ * P (E ∩ F) ∧ IsProbabilityMeasure P[|E] :=
  ⟨cond_apply hE P F, cond_isProbabilityMeasure hpos⟩

/-- Grinstead–Snell §4.1 product rule (PR-037). `P(E ∩ F) = P(F | E) P(E)`, and conditioning
successively on `E` and then `F` is conditioning on `E ∩ F`. -/
@[kb "grinsteadsnell2006" "§4.1 product rule, p. 143"]
theorem gs_section_4_1_product_rule {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    P (E ∩ F) = P[F | E] * P E ∧ P[|E][|F] = P[|E ∩ F] :=
  ⟨(cond_mul_eq_inter hE F P).symm, cond_cond_eq_cond_inter hE hF P⟩

/-- Grinstead–Snell Theorem 4.1 (PR-040). Two events are independent exactly when the probability
of their intersection is the product of their probabilities. -/
@[kb "grinsteadsnell2006" "Theorem 4.1, p. 148"]
theorem gs_theorem_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IndepSet E F P ↔ P (E ∩ F) = P E * P F :=
  indepSet_iff_measure_inter_eq_mul hE hF P

/-- Grinstead–Snell Definition 4.2 (PR-041). Events `A i` are mutually independent when every
finite subfamily has intersection probability equal to the product. -/
@[kb "grinsteadsnell2006" "Definition 4.2, p. 149"]
theorem gs_definition_4_2 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    iIndepSet A P ↔ ∀ s : Finset ι, P (⋂ i ∈ s, A i) = ∏ i ∈ s, P (A i) :=
  iIndepSet_iff_meas_biInter hA

/-- Grinstead–Snell Definition 4.4 (PR-043). Random variables are mutually independent when the
probability that each lies in a measurable set is multiplicative over every finite subfamily. -/
@[kb "grinsteadsnell2006" "Definition 4.4, p. 151"]
theorem gs_definition_4_4 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) :
    iIndepFun X P ↔ ∀ (S : Finset ι) (B : ι → Set ℝ), (∀ i ∈ S, MeasurableSet (B i)) →
      P (⋂ i ∈ S, X i ⁻¹' B i) = ∏ i ∈ S, P (X i ⁻¹' B i) :=
  iIndepFun_iff_measure_inter_preimage_eq_mul

/-- Grinstead–Snell Definition 4.5 (PR-044). In an independent trials process (independent,
identically distributed variables) joint probabilities multiply with the common distribution. -/
@[kb "grinsteadsnell2006" "Definition 4.5, p. 152"]
theorem gs_definition_4_5 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (i₀ : ι) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X i₀) P P) (S : Finset ι) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    P (⋂ i ∈ S, X i ⁻¹' B i) = ∏ i ∈ S, P (X i₀ ⁻¹' B i) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind S hB]
  exact Finset.prod_congr rfl fun i hi => (hid i).measure_mem_eq (hB i hi)

/-- Grinstead–Snell Theorem 4.3 (PR-048). Continuous functions applied separately to independent
random variables give independent random variables (two-variable and family forms). -/
@[kb "grinsteadsnell2006" "Theorem 4.3, p. 175"]
theorem gs_theorem_4_3 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (g : ι → ℝ → ℝ) (hg : ∀ i, Continuous (g i))
    (h : iIndepFun X P) :
    iIndepFun (fun i => g i ∘ X i) P ∧
      ∀ (Y Z : Ω → ℝ) (φ ψ : ℝ → ℝ), IndepFun Y Z P → Continuous φ → Continuous ψ →
        IndepFun (φ ∘ Y) (ψ ∘ Z) P :=
  ⟨h.comp g fun i => (hg i).measurable, fun _ _ _ _ hYZ hφ hψ =>
    hYZ.comp hφ.measurable hψ.measurable⟩

/-- Grinstead–Snell Definition 4.1 (PR-040). For an event `F` of positive probability, `E` and `F` are
independent exactly when `P(E | F) = P(E)`. -/
@[kb "grinsteadsnell2006" "Definition 4.1, p. 147"]
theorem gs_definition_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F) (hF0 : P F ≠ 0) :
    IndepSet E F P ↔ P[E | F] = P E := by
  rw [indepSet_iff_measure_inter_eq_mul hE hF P, cond_apply hF P E, Set.inter_comm]
  constructor
  · intro h
    rw [h, mul_comm (P E), ← mul_assoc, ENNReal.inv_mul_cancel hF0 (measure_ne_top P F), one_mul]
  · intro h
    rw [← h, mul_comm ((P F)⁻¹), mul_assoc, ENNReal.inv_mul_cancel hF0 (measure_ne_top P F),
      mul_one]

/-- Grinstead–Snell Definition 4.3 (PR-042). The joint random variable `(X_1, …, X_n)` has the joint
law, and the laws of the `X_i` are its marginals. -/
@[kb "grinsteadsnell2006" "Definition 4.3, p. 150"]
theorem gs_definition_4_3 : type_of% @UndergradKB.Probability.joint_and_marginal_laws :=
  @UndergradKB.Probability.joint_and_marginal_laws

/-- Grinstead–Snell Definition 4.6 (PR-045). The joint cumulative distribution function determines the
joint law. -/
@[kb "grinsteadsnell2006" "Definition 4.6, p. 173"]
theorem gs_definition_4_6 : type_of% @UndergradKB.Probability.jointLaw_eq_of_jointCdf_eq :=
  @UndergradKB.Probability.jointLaw_eq_of_jointCdf_eq

/-- Grinstead–Snell Definition 4.7 (PR-046). Continuous random variables are independent iff the joint
cdf is the product of the individual cdfs. -/
@[kb "grinsteadsnell2006" "Definition 4.7, p. 173"]
theorem gs_definition_4_7 : type_of% @UndergradKB.Probability.indepFun_iff_cdf_mul :=
  @UndergradKB.Probability.indepFun_iff_cdf_mul

/-- Grinstead–Snell Theorem 4.2 (PR-047). Continuous random variables are independent iff the joint
density is the product of the marginal densities (two-variable form; the `n`-variable form is
`UndergradKB.Probability.iIndepFun_iff_joint_density`). -/
@[kb "grinsteadsnell2006" "Theorem 4.2, p. 173"]
theorem gs_theorem_4_2 : type_of% @UndergradKB.Probability.indepFun_iff_joint_density :=
  @UndergradKB.Probability.indepFun_iff_joint_density

/-- Grinstead–Snell §4.3 beta density (PR-049). For `a, b > 0` the beta law has density
`x^(a-1) (1-x)^(b-1) / B(a,b)` on `(0,1)` and is a probability measure. -/
@[kb "grinsteadsnell2006" "§4.3 beta density, p. 176"]
theorem gs_section_4_3_beta_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (betaMeasure a b) ∧
      betaMeasure a b = volume.withDensity (betaPDF a b) ∧
      ∀ x : ℝ, betaPDFReal a b x =
        if 0 < x ∧ x < 1 then (1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) else 0 :=
  ⟨isProbabilityMeasureBeta ha hb, rfl, fun _ => rfl⟩

/-- Grinstead–Snell Theorem 4.2 (PR-047), `n` variables: `X_1, ..., X_n` with densities are mutually
independent iff the joint density is a.e. the product of the marginal densities. -/
@[kb "grinsteadsnell2006" "Theorem 4.2, p. 173"]
theorem gs_theorem_4_2_n : type_of% @UndergradKB.Probability.iIndepFun_iff_joint_density :=
  @UndergradKB.Probability.iIndepFun_iff_joint_density

/-- Grinstead–Snell Example 4.3 (PR-148). Conditional probabilities in the election once `A` drops out. -/
@[kb "grinsteadsnell2006" "Example 4.3, p. 142"]
theorem gs_example_4_3 : type_of% @UndergradKB.Probability.election_given_A_drops :=
  @UndergradKB.Probability.election_given_A_drops

/-- Grinstead–Snell Example 4.4 (PR-147). The conditional probability of a six given that a die roll exceeds four. -/
@[kb "grinsteadsnell2006" "Example 4.4, p. 143"]
theorem gs_example_4_4 : type_of% @UndergradKB.Probability.die_six_given_exceeds_four :=
  @UndergradKB.Probability.die_six_given_exceeds_four

/-- Grinstead–Snell Example 4.5 (PR-149). The two-urns problem. -/
@[kb "grinsteadsnell2006" "Example 4.5, p. 143"]
theorem gs_example_4_5 : type_of% @UndergradKB.Probability.two_urns :=
  @UndergradKB.Probability.two_urns

/-- Grinstead–Snell Example 4.6 (PR-133). Monty Hall: staying wins with probability `1/3`, switching with `2/3`. -/
@[kb "grinsteadsnell2006" "Example 4.6, p. 144"]
theorem gs_example_4_6 : type_of% @UndergradKB.Probability.monty_stay_switch :=
  @UndergradKB.Probability.monty_stay_switch

/-- Grinstead–Snell Example 4.6 (PR-133). Monty Hall, Craig's question about the conditional probability. -/
@[kb "grinsteadsnell2006" "Example 4.6, p. 144"]
theorem gs_example_4_6_b : type_of% @UndergradKB.Probability.monty_conditional :=
  @UndergradKB.Probability.monty_conditional

/-- Grinstead–Snell Example 4.17 (PR-134). The false-positive test via Bayes' formula. -/
@[kb "grinsteadsnell2006" "Example 4.17, p. 155"]
theorem gs_example_4_17 : type_of% @UndergradKB.Probability.falsePositive :=
  @UndergradKB.Probability.falsePositive

/-- Grinstead–Snell Example 4.22 (PR-135). The coordinates of a uniform point of the square have independent squares. -/
@[kb "grinsteadsnell2006" "Example 4.22, p. 174"]
theorem gs_example_4_22 : type_of% @UndergradKB.Probability.unitSquare_sq_indep :=
  @UndergradKB.Probability.unitSquare_sq_indep

/-- Grinstead–Snell Example 4.22 (PR-135). The squared coordinate and the other events of the example are not independent. -/
@[kb "grinsteadsnell2006" "Example 4.22, p. 174"]
theorem gs_example_4_22_b : type_of% @UndergradKB.Probability.unitSquare_not_indep :=
  @UndergradKB.Probability.unitSquare_not_indep

/-- Grinstead–Snell Example 4.23 (PR-159). The beta posterior for a beta prior and Bernoulli data. -/
@[kb "grinsteadsnell2006" "Example 4.23, p. 176"]
theorem gs_example_4_23 : type_of% @UndergradKB.Probability.beta_posterior :=
  @UndergradKB.Probability.beta_posterior

/-- Grinstead–Snell Example 4.25 (PR-136). Two children: given at least one boy, the other is a boy with probability `1/3`. -/
@[kb "grinsteadsnell2006" "Example 4.25, p. 183"]
theorem gs_example_4_25 : type_of% @UndergradKB.Probability.twoChildren_atLeastOneBoy :=
  @UndergradKB.Probability.twoChildren_atLeastOneBoy

/-- Grinstead–Snell Example 4.26 (PR-136). Two children: given that the companion is a boy, the other is a boy with probability `1/2`. -/
@[kb "grinsteadsnell2006" "Example 4.26, p. 184"]
theorem gs_example_4_26 : type_of% @UndergradKB.Probability.twoChildren_companionBoy :=
  @UndergradKB.Probability.twoChildren_companionBoy

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 4.2 (PR-191). In a finite population (uniform measure) let `E` be the women who reach 60 (`89835` of them) and `F ⊆ E` those who reach 80 (`57062` of them); then a woman... -/
@[kb "grinsteadsnell2006" "Example 4.2, p. 141"]
theorem gs_example_4_2 : type_of% @UndergradKB.Probability.life_table_conditional :=
  @UndergradKB.Probability.life_table_conditional

/-- Grinstead–Snell Example 4.7 (PR-165). Two tosses of a coin with `P(H) = p`, with the product weights `p^2, pq, qp, q^2` on `HH, HT, TH, TT` (`q = 1 - p`): the events "heads on the first toss"... -/
@[kb "grinsteadsnell2006" "Example 4.7, p. 148"]
theorem gs_example_4_7 : type_of% @UndergradKB.Probability.two_tosses_heads_first_tails_second :=
  @UndergradKB.Probability.two_tosses_heads_first_tails_second

/-- Grinstead–Snell Example 4.8 (PR-165). For the fair coin, the events "the first toss is a head" and "the two outcomes are the same" are independent: `P(B | A) = (1/4)/(1/2) = 1/2 = P(B)`. -/
@[kb "grinsteadsnell2006" "Example 4.8, p. 148"]
theorem gs_example_4_8 : type_of% @UndergradKB.Probability.two_tosses_first_head_same_indep :=
  @UndergradKB.Probability.two_tosses_first_head_same_indep

/-- Grinstead–Snell Example 4.9 (PR-165). For the fair coin, "heads on the first toss" (probability `1/2`) and "two heads" (probability `1/4`) are not independent: the intersection has probability... -/
@[kb "grinsteadsnell2006" "Example 4.9, p. 149"]
theorem gs_example_4_9 : type_of% @UndergradKB.Probability.two_tosses_first_head_two_heads_not_indep :=
  @UndergradKB.Probability.two_tosses_first_head_two_heads_not_indep

/-- Grinstead–Snell Example 4.10 (PR-166). Three independent tosses of a fair coin: each of the eight ordered triples has probability `1/8`, and each toss `Xᵢ` has the distribution `m(H) = m(T) = 1/2`. -/
@[kb "grinsteadsnell2006" "Example 4.10, p. 149"]
theorem gs_example_4_10 : type_of% @UndergradKB.Probability.three_fair_tosses :=
  @UndergradKB.Probability.three_fair_tosses

/-- Grinstead–Snell Example 4.11 (PR-166). For three fair tosses, `Ȳ = (Y₁, Y₂, Y₃)` takes exactly eight distinct values, each with probability `1/8` (it is a bijective relabelling of the outcome `X̄... -/
@[kb "grinsteadsnell2006" "Example 4.11, p. 150"]
theorem gs_example_4_11 : type_of% @UndergradKB.Probability.heads_partial_law :=
  @UndergradKB.Probability.heads_partial_law

/-- Grinstead–Snell Example 4.12 (PR-166). In an independent trials process (the product measure of `n` copies of a distribution `μ` on a finite set), the probability of an outcome `(a₁, ..., aₙ)` is... -/
@[kb "grinsteadsnell2006" "Example 4.12, p. 150"]
theorem gs_example_4_12 : type_of% @UndergradKB.Probability.trials_product_independent :=
  @UndergradKB.Probability.trials_product_independent

/-- Grinstead–Snell Example 4.13 (PR-192). A person is drawn uniformly from a group of 60 with cell counts `(C,S) = (0,0): 40, (0,1): 10, (1,0): 7, (1,1): 3`. -/
@[kb "grinsteadsnell2006" "Example 4.13, p. 151"]
theorem gs_example_4_13 : type_of% @UndergradKB.Probability.smoking_cancer :=
  @UndergradKB.Probability.smoking_cancer

/-- Grinstead–Snell Example 4.14 (PR-166). Three rolls of a fair die form an independent trials process (the product of three uniform measures on the six faces): each of the `216` outcomes has... -/
@[kb "grinsteadsnell2006" "Example 4.14, p. 152"]
theorem gs_example_4_14 : type_of% @UndergradKB.Probability.three_die_rolls :=
  @UndergradKB.Probability.three_die_rolls

/-- Grinstead–Snell Example 4.15 (PR-166). In a Bernoulli trials process with success probability `p` (the product measure of `n` copies of the coin) an outcome with `k` successes has probability... -/
@[kb "grinsteadsnell2006" "Example 4.15, p. 153"]
theorem gs_example_4_15 : type_of% @UndergradKB.Probability.bernoulli_trials_process :=
  @UndergradKB.Probability.bernoulli_trials_process

/-- Grinstead–Snell Example 4.16 (PR-167). With Table 4.3 (row totals `3215, 2125, 4660`, column totals `3016, 4001, 1964, 1019`, grand total `10000`), Bayes' formula gives the posterior probability... -/
@[kb "grinsteadsnell2006" "Example 4.16, p. 154"]
theorem gs_example_4_16 : type_of% @UndergradKB.Probability.diagnosis_two_tests :=
  @UndergradKB.Probability.diagnosis_two_tests

/-- Grinstead–Snell Example 4.18 (PR-174). For a (measurable) spinner `X` uniform on `[0,1]`, given that it stops in `[0, 1/2]`, the probability that it lies in `[1/6, 1/3]` is `1/3`. -/
@[kb "grinsteadsnell2006" "Example 4.18, p. 170"]
theorem gs_example_4_18 : type_of% @UndergradKB.Probability.spinner_conditional :=
  @UndergradKB.Probability.spinner_conditional

/-- Grinstead–Snell Example 4.19 (PR-174). For a dart `X` uniform on the unit disk, given that it lands in the upper half `y ≥ 0`, the probability that its distance from the centre is less than `1/2`... -/
@[kb "grinsteadsnell2006" "Example 4.19, p. 171"]
theorem gs_example_4_19 : type_of% @UndergradKB.Probability.dart_conditional_upper_half :=
  @UndergradKB.Probability.dart_conditional_upper_half

/-- Grinstead–Snell Example 4.21 (PR-174). For a dart `X` uniform on the unit disk, the events "upper half" (`y ≥ 0`) and "right half" (`x ≥ 0`) are independent, each of probability `1/2`, and the... -/
@[kb "grinsteadsnell2006" "Example 4.21, p. 172"]
theorem gs_example_4_21 : type_of% @UndergradKB.Probability.dart_halves_independent :=
  @UndergradKB.Probability.dart_halves_independent

/-- Grinstead–Snell Example 4.27 (PR-170). Two puppies with independent, equally likely sexes (uniform measure on `Bool × Bool`, `true` for male): given that at least one is male, the probability... -/
@[kb "grinsteadsnell2006" "Example 4.27, p. 184"]
theorem gs_example_4_27 : type_of% @UndergradKB.Probability.beagles_bothMale :=
  @UndergradKB.Probability.beagles_bothMale

/-- Grinstead–Snell Example 4.28 (PR-171). In Finn's version the coin decides which of the `$5`, `$10` envelopes Ali gets; Baba gets the other. -/
@[kb "grinsteadsnell2006" "Example 4.28, p. 186"]
theorem gs_example_4_28 : type_of% @UndergradKB.Probability.finn_keep_eq_switch :=
  @UndergradKB.Probability.finn_keep_eq_switch

/-- Grinstead–Snell Example 4.29 (PR-172). `p_x` is a probability distribution on the positive integers (it sums to `1`). -/
@[kb "grinsteadsnell2006" "Example 4.29, p. 187"]
theorem gs_example_4_29 : type_of% @UndergradKB.Probability.brams_hasSum :=
  @UndergradKB.Probability.brams_hasSum

/-- Grinstead–Snell Example 4.29 (PR-172). Part 2 (the book's criterion (4.6)). -/
@[kb "grinsteadsnell2006" "Example 4.29, p. 187"]
theorem gs_example_4_29_b : type_of% @UndergradKB.Probability.switchExp_gt_iff :=
  @UndergradKB.Probability.switchExp_gt_iff

/-- Grinstead–Snell Example 4.29 (PR-172). For `x = 2^k` with `k ≥ 2` (both `x/2` and `x` are possible values of the smaller amount), `p_{x/2}/(p_{x/2}+p_x) = 3/5`, so switching pays on average:... -/
@[kb "grinsteadsnell2006" "Example 4.29, p. 187"]
theorem gs_example_4_29_c : type_of% @UndergradKB.Probability.brams_switch_pays :=
  @UndergradKB.Probability.brams_switch_pays

/-- Grinstead–Snell Example 4.30 (PR-173). Fix distinct positive integers `x`, `y` in the two envelopes. -/
@[kb "grinsteadsnell2006" "Example 4.30, p. 188"]
theorem gs_example_4_30 : type_of% @UndergradKB.Probability.guessProb_eq_gt :=
  @UndergradKB.Probability.guessProb_eq_gt


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell §4.1 total probability (PR-038), in `ℝ≥0∞`. For a finite measurable partition `E i` of the sample space, `P F = ∑ P(F | E i) P(E i)`. -/
@[kb "grinsteadsnell2006" "§4.1 total probability, p. 154"]
theorem gs_section_4_1_total_probability : type_of% @UndergradKB.Probability.measure_eq_sum_cond_mul :=
  @UndergradKB.Probability.measure_eq_sum_cond_mul

/-- Grinstead–Snell §4.1 total probability (PR-038). For a finite measurable partition `E i` with `P (E i) > 0`, `P F = ∑ P(F | E i) P(E i)` (real-valued; the positivity is not needed). -/
@[kb "grinsteadsnell2006" "§4.1 total probability, p. 154"]
theorem gs_section_4_1_total_probability_b : type_of% @UndergradKB.Probability.real_eq_sum_cond_mul :=
  @UndergradKB.Probability.real_eq_sum_cond_mul

/-- Grinstead–Snell §4.1 Bayes' formula (PR-039). For a finite measurable partition `H j` with `P (H j) > 0` and an event `E` with `P E > 0`, `P(H i | E) = P(E | H i) P(H i) / ∑ j, P(E | H j) P(H j)`. -/
@[kb "grinsteadsnell2006" "§4.1 Bayes' formula, p. 154"]
theorem gs_section_4_1_bayes_formula : type_of% @UndergradKB.Probability.real_cond_eq_bayes :=
  @UndergradKB.Probability.real_cond_eq_bayes

/-- Grinstead–Snell Example 4.20 (PR-018). The exponential waiting time is memoryless: `P(T > r + s | T > r) = P(T > s)` for the exponential law of rate `lam > 0`. -/
@[kb "grinsteadsnell2006" "Example 4.20, p. 171"]
theorem gs_example_4_20 : type_of% @UndergradKB.Probability.expMeasure_memoryless :=
  @UndergradKB.Probability.expMeasure_memoryless

/-- Grinstead–Snell Example 4.24 (PR-198). For a machine whose success probability `x` has the uniform prior (the beta`(1,1)` density) and has produced `w` wins and `l` losses (likelihood `C(w+l, w) x^w (1-x)^l`), the posterior density is the beta`(w+1, l+1)` density, and the posterior probability of a win on the next play, `∫ x · (posterior density)`, is `(w+1)/(w+l+2)`. -/
@[kb "grinsteadsnell2006" "Example 4.24, p. 178"]
theorem gs_example_4_24 : type_of% @UndergradKB.Probability.bandit_posterior :=
  @UndergradKB.Probability.bandit_posterior

end UndergradKB.Probability.Course
