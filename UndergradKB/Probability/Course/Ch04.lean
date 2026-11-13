import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.Beta
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.ExamplesContinuous
import UndergradKB.Probability.ExamplesLimits
import UndergradKB.Probability.JointLaws
import UndergradKB.Probability.GeneratingFunctions
import UndergradKB.Probability.IndepDensity

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

end UndergradKB.Probability.Course
