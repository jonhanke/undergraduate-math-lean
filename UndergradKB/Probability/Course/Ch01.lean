import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Uniform
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesSchoolC
import UndergradKB.Probability.ExamplesSchoolB
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.Basic
import UndergradKB.Probability.DiscreteDistributions
import UndergradKB.Probability.ExamplesQueueStock
import UndergradKB.Probability.ExamplesSchoolD

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

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 1.6 (PR-187). For one roll of a fair die (faces `i + 1`, `i : Fin 6`, uniform measure) every face has weight `1/6`, and the event that the outcome is even has probability... -/
@[kb "grinsteadsnell2006" "Example 1.6, p. 26"]
theorem gs_example_1_6 : type_of% @UndergradKB.Probability.die_even_half :=
  @UndergradKB.Probability.die_even_half

/-- Grinstead–Snell Example 1.7 (PR-188). Two tosses of a fair coin recorded in order are the uniform measure on `Bool × Bool` (weight `1/4` each); at least one head has probability `3/4`, heads on... -/
@[kb "grinsteadsnell2006" "Example 1.7, p. 27"]
theorem gs_example_1_7 : type_of% @UndergradKB.Probability.two_tosses_law :=
  @UndergradKB.Probability.two_tosses_law

/-- Grinstead–Snell Example 1.8 (PR-187). For one roll of a fair die (faces `i + 1`, `i : Fin 6`, uniform measure) every face has weight `1/6`, and the event that the outcome is even has probability... -/
@[kb "grinsteadsnell2006" "Example 1.8, p. 28"]
theorem gs_example_1_8 : type_of% @UndergradKB.Probability.die_even_half :=
  @UndergradKB.Probability.die_even_half

/-- Grinstead–Snell Example 1.12 (PR-163). If candidate `C` wins with probability `1/5` then the odds in favour of `C` are `1 : 4` (that is `(1/5)/(4/5) = 1/4`, and conversely odds `1 : 4` give... -/
@[kb "grinsteadsnell2006" "Example 1.12, p. 36"]
theorem gs_example_1_12 : type_of% @UndergradKB.Probability.election_odds_fair :=
  @UndergradKB.Probability.election_odds_fair


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell Example 1.13 (PR-009). A fair coin is tossed until the first head: the first head occurs at toss `n ≥ 1` with probability `2⁻ⁿ`. -/
@[kb "grinsteadsnell2006" "Example 1.13, p. 37"]
theorem gs_example_1_13 : type_of% @UndergradKB.Probability.firstHead_real_singleton :=
  @UndergradKB.Probability.firstHead_real_singleton

/-- Grinstead–Snell Example 1.13 (PR-009): the masses `2⁻ⁿ`, `n ≥ 1`, sum to `1`. -/
@[kb "grinsteadsnell2006" "Example 1.13, p. 37"]
theorem gs_example_1_13_b : type_of% @UndergradKB.Probability.firstHead_hasSum :=
  @UndergradKB.Probability.firstHead_hasSum

/-- Grinstead–Snell Example 1.4 (PR-207), final winnings. In `2n` fair tosses (`n = 20` for the book's 40 tosses) Peter's final winnings `2k - 2n` have probability `C(2n,k)/2^{2n}`; this is largest for winnings `0` (`k = n`) and smallest for the extreme winnings `±2n` (`k = 0` and `k = 2n`, which have equal probability `1/2^{2n}`). -/
@[kb "grinsteadsnell2006" "Example 1.4, p. 13"]
theorem gs_example_1_4 : type_of% @UndergradKB.Probability.heads_tails_final_winnings :=
  @UndergradKB.Probability.heads_tails_final_winnings

/-- Grinstead–Snell Example 1.4 (PR-207), times in the lead. In `2n` fair tosses (`n = 20` for the book's 40 tosses) Peter is in the lead exactly `2k` times with probability `u_{2k} u_{2n-2k}` (the repo's Theorem 12.4, `leadCount_prob`); this is largest for `k = 0` and `k = n` (which have equal probability `u_{2n}`) and, when `n` is even, smallest for `k = n/2`. -/
@[kb "grinsteadsnell2006" "Example 1.4, p. 13"]
theorem gs_example_1_4_b : type_of% @UndergradKB.Probability.heads_tails_lead_times :=
  @UndergradKB.Probability.heads_tails_lead_times

/-- Grinstead–Snell Example 1.3 (PR-193), first game. `n` independent rolls of one die are the uniform measure on `Fin n → Fin 6` (face `5` is the six). The probability of at least one six in `n` rolls is `1 - (5/6)^n`; for `n = 4` it is `1 - (5/6)^4 = 671/1296`, which exceeds `1/2` and rounds to the book's `.518` (it lies in `[.5175, .5185)`). -/
@[kb "grinsteadsnell2006" "Example 1.3, p. 12"]
theorem gs_example_1_3 : type_of% @UndergradKB.Probability.demere_one_die :=
  @UndergradKB.Probability.demere_one_die

/-- Grinstead–Snell Example 1.3 (PR-193), second game. `n` independent rolls of a pair of dice are the uniform measure on `Fin n → Fin 6 × Fin 6` (the pair `(5, 5)` is a double six). -/
@[kb "grinsteadsnell2006" "Example 1.3, p. 12"]
theorem gs_example_1_3_b : type_of% @UndergradKB.Probability.demere_two_dice :=
  @UndergradKB.Probability.demere_two_dice

/-- Grinstead–Snell Example 1.5 (PR-194), the four horses. For `x` uniform on `[0,1)` the intervals `[0,.3)`, `[.3,.7)`, `[.7,.9)`, `[.9,1)` have probabilities `.3, .4, .2, .1`. -/
@[kb "grinsteadsnell2006" "Example 1.5, p. 14"]
theorem gs_example_1_5 : type_of% @UndergradKB.Probability.horse_race_intervals :=
  @UndergradKB.Probability.horse_race_intervals

/-- Grinstead–Snell Example 1.5 (PR-194), general form. For nonnegative weights `w : Fin k → ℝ` with sum `1`, the interval `[∑_{j<i} wⱼ, ∑_{j≤i} wⱼ)` of `[0,1)` has uniform probability `wᵢ` (so these intervals realize any given win probabilities). -/
@[kb "grinsteadsnell2006" "Example 1.5, p. 14"]
theorem gs_example_1_5_b : type_of% @UndergradKB.Probability.horse_race_general :=
  @UndergradKB.Probability.horse_race_general

end UndergradKB.Probability.Course
