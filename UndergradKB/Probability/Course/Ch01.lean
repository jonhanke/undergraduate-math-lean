import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Uniform
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.Basic
import UndergradKB.Probability.DiscreteDistributions

/-!
# Course layer, Chapter 1 (Grinstead–Snell, Discrete Probability Distributions)

Thin wrappers stating the book's results of Chapter 1 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory

/-- Grinstead–Snell Definition 1.1 (PR-001). A random variable is a measurable function on a
probability space; its distribution (the pushforward of the probability measure) is again a
probability measure. -/
@[kb "grinsteadsnell2006" "Definition 1.1, p. 26"]
theorem gs_definition_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) : IsProbabilityMeasure (P.map X) :=
  ⟨by rw [Measure.map_apply hX MeasurableSet.univ]; simp⟩

/-- Grinstead–Snell Definition 1.2 (PR-002). On a finite sample space a distribution function `m`
(a `PMF`) has total weight 1, and the probability of an event is the sum of `m` over it. -/
@[kb "grinsteadsnell2006" "Definition 1.2, p. 27"]
theorem gs_definition_1_2 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (m : PMF Ω) (E : Finset Ω) :
    (∑ ω, m ω = 1) ∧ m.toMeasure (E : Set Ω) = ∑ ω ∈ E, m ω := by
  refine ⟨?_, PMF.toMeasure_apply_finset m E⟩
  have h := m.tsum_coe
  rwa [tsum_fintype] at h

/-- Grinstead–Snell Theorem 1.1 (PR-003). A probability measure is monotone, bounded by 1, and the
complement of an event has probability one minus that of the event. -/
@[kb "grinsteadsnell2006" "Theorem 1.1, p. 30"]
theorem gs_theorem_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    P Set.univ = 1 ∧ (∀ {A B : Set Ω}, A ⊆ B → P A ≤ P B) ∧ (∀ A : Set Ω, P A ≤ 1) ∧
      ∀ {A : Set Ω}, MeasurableSet A → P Aᶜ = 1 - P A :=
  ⟨measure_univ, fun h => measure_mono h, fun _ => prob_le_one, fun hA => prob_compl_eq_one_sub hA⟩

/-- Grinstead–Snell Theorem 1.2 (PR-004). Additivity of probability over a finite family of
pairwise disjoint events. -/
@[kb "grinsteadsnell2006" "Theorem 1.2, p. 31"]
theorem gs_theorem_1_2 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Finset ι) (E : ι → Set Ω) (hd : (s : Set ι).PairwiseDisjoint E)
    (hm : ∀ i ∈ s, MeasurableSet (E i)) :
    P (⋃ i ∈ s, E i) = ∑ i ∈ s, P (E i) :=
  measure_biUnion_finset hd hm

/-- Grinstead–Snell Theorem 1.4 (PR-006). Probability of a union of two events. -/
@[kb "grinsteadsnell2006" "Theorem 1.4, p. 32"]
theorem gs_theorem_1_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A B : Set Ω} (hB : MeasurableSet B) :
    P (A ∪ B) + P (A ∩ B) = P A + P B :=
  measure_union_add_inter A hB

/-- Grinstead–Snell Definition 1.3 (PR-007). The uniform distribution on an `n`-element sample
space gives each outcome probability `1 / n`. -/
@[kb "grinsteadsnell2006" "Definition 1.3, p. 33"]
theorem gs_definition_1_3 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (ω : Ω) :
    Measure.uniformOfFinset (Finset.univ : Finset Ω) {ω} = (Fintype.card Ω : ENNReal)⁻¹ := by
  simp

/-- Grinstead–Snell Theorem 1.3 (PR-005). If the events `A i` partition the sample space then
`P(E) = ∑ P(E ∩ A i)`. -/
@[kb "grinsteadsnell2006" "Theorem 1.3, p. 31"]
theorem gs_theorem_1_3 : type_of% @UndergradKB.Probability.measure_eq_sum_inter_partition :=
  @UndergradKB.Probability.measure_eq_sum_inter_partition

/-- Grinstead–Snell Corollary 1.1 (PR-005). `P(A) = P(A ∩ B) + P(A ∩ Bᶜ)`. -/
@[kb "grinsteadsnell2006" "Corollary 1.1, p. 32"]
theorem gs_corollary_1_1 : type_of% @UndergradKB.Probability.measure_eq_inter_add_inter_compl :=
  @UndergradKB.Probability.measure_eq_inter_add_inter_compl

/-- Grinstead–Snell Definition 1.4 (PR-008). Odds `r : s` in favour of an event of probability `p`
(`r/s = p/(1-p)`) recover `p = r/(r+s)`. -/
@[kb "grinsteadsnell2006" "Definition 1.4, p. 36"]
theorem gs_definition_1_4 : type_of% @UndergradKB.Probability.prob_eq_of_odds :=
  @UndergradKB.Probability.prob_eq_of_odds

/-- Grinstead–Snell Example 1.9 (PR-148). The election with `A`, `B` equally likely and `C` half as likely has a determined distribution. -/
@[kb "grinsteadsnell2006" "Example 1.9, p. 28"]
theorem gs_example_1_9 : type_of% @UndergradKB.Probability.election_distribution :=
  @UndergradKB.Probability.election_distribution

/-- Grinstead–Snell Example 1.10 (PR-130). Probabilities of events for three tosses of a fair coin. -/
@[kb "grinsteadsnell2006" "Example 1.10, p. 32"]
theorem gs_example_1_10 : type_of% @UndergradKB.Probability.threeTosses_prob :=
  @UndergradKB.Probability.threeTosses_prob

/-- Grinstead–Snell Example 1.11 (PR-131). Probabilities of events for a pair of dice. -/
@[kb "grinsteadsnell2006" "Example 1.11, p. 34"]
theorem gs_example_1_11 : type_of% @UndergradKB.Probability.twoDice_prob :=
  @UndergradKB.Probability.twoDice_prob

end UndergradKB.Probability.Course
