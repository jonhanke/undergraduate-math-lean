import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import UndergradKB.Common.Attr

/-!
# Course layer, chapter 3 (OpenStax *Introductory Statistics 2e*): probability rules
-/

namespace UndergradKB.Statistics.Course.C3

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {A B : Set Ω}

open scoped Classical in
/-- OpenStax Introductory Statistics 2e §3.1 (ST-019). With equally likely outcomes (the uniform
law on a finite sample space `s`), the probability of an event `t` is the number of outcomes in
`t` divided by the number of outcomes. -/
@[kb "openstaxintrostats2e" "§3.1, p. 179"]
theorem equally_likely_probability [MeasurableSingletonClass Ω] (s : Finset Ω) (t : Set Ω) :
    Measure.uniformOfFinset s t = ((s.filter (· ∈ t)).card : ENNReal) / s.card :=
  Measure.uniformOfFinset_apply t

/-- OpenStax Introductory Statistics 2e §3.1 (ST-020). Probabilities lie in `[0, 1]`; the sample
space has probability 1 and the empty event probability 0. -/
@[kb "openstaxintrostats2e" "§3.1, p. 179"]
theorem probability_bounds [IsProbabilityMeasure P] (A : Set Ω) :
    P A ≤ 1 ∧ P Set.univ = 1 ∧ P ∅ = 0 :=
  ⟨prob_le_one, measure_univ, measure_empty⟩

/-- OpenStax Introductory Statistics 2e §3.1 (ST-021). Complement rule: `P(A') = 1 - P(A)`. -/
@[kb "openstaxintrostats2e" "§3.1, p. 179"]
theorem complement_rule [IsProbabilityMeasure P] (hA : MeasurableSet A) :
    P Aᶜ = 1 - P A :=
  prob_compl_eq_one_sub hA

/-- OpenStax Introductory Statistics 2e §3.3 (ST-022). Addition rule:
`P(A or B) = P(A) + P(B) - P(A and B)`, stated without subtraction. -/
@[kb "openstaxintrostats2e" "§3.3, p. 190"]
theorem addition_rule (hB : MeasurableSet B) :
    P (A ∪ B) + P (A ∩ B) = P A + P B :=
  measure_union_add_inter A hB

/-- OpenStax Introductory Statistics 2e §3.2 (ST-023). Mutually exclusive events cannot occur
together, and the probability of either is the sum of the probabilities. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem mutually_exclusive_rule (hd : Disjoint A B) (hB : MeasurableSet B) :
    P (A ∩ B) = 0 ∧ P (A ∪ B) = P A + P B := by
  rw [hd.inter_eq]
  exact ⟨measure_empty, measure_union hd hB⟩

/-- OpenStax Introductory Statistics 2e §3.3 (ST-024). Conditional probability:
`P(A | B) = P(A and B) / P(B)` (as `P(B)⁻¹ · P(B ∩ A)`, `P(B) > 0` makes it a quotient). -/
@[kb "openstaxintrostats2e" "§3.3, p. 190"]
theorem conditional_probability_def (hB : MeasurableSet B) (A : Set Ω) :
    P[A | B] = (P B)⁻¹ * P (B ∩ A) :=
  cond_apply hB P A

/-- OpenStax Introductory Statistics 2e §3.3 (ST-025). Multiplication rule:
`P(A and B) = P(A | B) P(B)`. -/
@[kb "openstaxintrostats2e" "§3.3, p. 190"]
theorem multiplication_rule [IsFiniteMeasure P] (hB : MeasurableSet B) (A : Set Ω) :
    P (B ∩ A) = P[A | B] * P B :=
  (cond_mul_eq_inter hB A P).symm

/-- OpenStax Introductory Statistics 2e §3.2 (ST-026). Events are independent exactly when
`P(A and B) = P(A) P(B)`. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem independent_iff_product [IsProbabilityMeasure P] (hA : MeasurableSet A)
    (hB : MeasurableSet B) : IndepSet A B P ↔ P (A ∩ B) = P A * P B :=
  indepSet_iff_measure_inter_eq_mul hA hB P

/-- OpenStax Introductory Statistics 2e §3.2 (ST-026). If `A` and `B` are independent and
`P(B) > 0` then `P(A | B) = P(A)`. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem conditional_eq_of_independent [IsProbabilityMeasure P] (hA : MeasurableSet A)
    (hB : MeasurableSet B) (h : IndepSet A B P) (h0 : P B ≠ 0) : P[A | B] = P A := by
  rw [cond_apply hB, Set.inter_comm, (indepSet_iff_measure_inter_eq_mul hA hB P).1 h,
    mul_comm, mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top P B), mul_one]

/-- OpenStax Introductory Statistics 2e §3.5 (ST-031). Two-branch tree: the probability of `B`
is the sum over the two paths through `A` and `A'`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem total_probability_two_branches [IsFiniteMeasure P] (hA : MeasurableSet A) (B : Set Ω) :
    P B = P[B | A] * P A + P[B | Aᶜ] * P Aᶜ := by
  rw [cond_mul_eq_inter hA B P, cond_mul_eq_inter hA.compl B P, Set.inter_comm A B,
    Set.inter_comm Aᶜ B, ← Set.sdiff_eq]
  exact (measure_inter_add_sdiff B hA).symm

/-- OpenStax Introductory Statistics 2e §3.5 (ST-032). Reversing a conditional probability:
`P(A | B) = P(B | A) P(A) / P(B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem reverse_conditional [IsFiniteMeasure P] (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P[A | B] = (P B)⁻¹ * P[B | A] * P A :=
  cond_eq_inv_mul_cond_mul hB hA P

/-- OpenStax Introductory Statistics 2e §3.5 (ST-033). Venn diagram identity:
`P(A and B') = P(A) - P(A and B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem prob_inter_compl [IsFiniteMeasure P] (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P (A ∩ Bᶜ) = P A - P (A ∩ B) := by
  have e : A ∩ Bᶜ = A \ (A ∩ B) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]; tauto
  rw [e]
  exact measure_diff Set.inter_subset_left (hA.inter hB).nullMeasurableSet (measure_ne_top P _)

end UndergradKB.Statistics.Course.C3
