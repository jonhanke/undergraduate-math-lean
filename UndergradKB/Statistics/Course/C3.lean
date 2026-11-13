import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Uniform
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Rules
import UndergradKB.Statistics.Remarks

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

/-- OpenStax Introductory Statistics 2e §3.1 (ST-019). If every outcome of a finite sample space is
equally likely, the probability of an event is the number of outcomes in the event divided by the
number of outcomes in the sample space. -/
@[kb "openstaxintrostats2e" "§3.1, p. 179"]
theorem equally_likely_outcomes_probability [Fintype Ω] [MeasurableSingletonClass Ω]
    [IsProbabilityMeasure P] (h : ∀ x y : Ω, P {x} = P {y}) (A : Set Ω) :
    P.real A = (A.ncard : ℝ) / (Fintype.card Ω : ℝ) :=
  UndergradKB.Statistics.equally_likely_prob_real P h A

/-- OpenStax Introductory Statistics 2e §3.5 (ST-031). Tree diagram, total probability: if the
first-level branches `A i` (`i ∈ s`) are pairwise disjoint, measurable and cover the sample space,
then `P(B)` is the sum over the branches of `P(A i) · P(B | A i)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem tree_diagram_total_probability [IsProbabilityMeasure P] {ι : Type*} (s : Finset ι)
    (A : ι → Set Ω) (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hdisj : Set.PairwiseDisjoint (↑s : Set ι) A) (hcover : ⋃ i ∈ s, A i = Set.univ)
    (B : Set Ω) (hB : MeasurableSet B) :
    P B = ∑ i ∈ s, P (A i) * P[B | A i] :=
  UndergradKB.Statistics.total_probability P s A hmeas hdisj hcover B hB

/-- OpenStax Introductory Statistics 2e §3.5 (ST-031). Tree diagram, path probability: the
probability of the path `A`, then `B`, then `C` is `P(A) · P(B | A) · P(C | A and B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem tree_diagram_path_probability [IsProbabilityMeasure P] (hA : MeasurableSet A)
    (hB : MeasurableSet B) (C : Set Ω) :
    P (A ∩ B ∩ C) = P A * P[B | A] * P[C | A ∩ B] :=
  UndergradKB.Statistics.tree_path_three P hA hB C

/-- OpenStax Introductory Statistics 2e §3.5 (ST-033). Venn diagram: the probability of neither
`A` nor `B` is `1 - P(A) - P(B) + P(A and B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem venn_diagram_neither [IsProbabilityMeasure P] (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    P.real (Aᶜ ∩ Bᶜ) = 1 - P.real A - P.real B + P.real (A ∩ B) :=
  UndergradKB.Statistics.venn_neither P hA hB

section Sampling

variable {N : ℕ}

/-- OpenStax Introductory Statistics 2e §3.2 (ST-029). Sampling with replacement: drawing twice from
`N` equally likely items, the first draw and the second draw are independent. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem with_replacement_draws_independent [NeZero N] :
    IndepFun (Prod.fst : Fin N × Fin N → Fin N) Prod.snd
      (uniformOn (Set.univ : Set (Fin N × Fin N))) :=
  UndergradKB.Statistics.withReplacement_indep

/-- OpenStax Introductory Statistics 2e §3.2 (ST-029). Sampling with replacement: the first draw
lands in a set `A` of items with probability `|A| / N`. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem with_replacement_first_draw_probability [NeZero N] (A : Finset (Fin N)) :
    (uniformOn (Set.univ : Set (Fin N × Fin N))).real {p | p.1 ∈ A} = (A.card : ℝ) / N :=
  UndergradKB.Statistics.withReplacement_first_prob A

/-- OpenStax Introductory Statistics 2e §3.2 (ST-029). Sampling without replacement: drawing two
distinct items from `N` (ordered pairs of distinct items equally likely), the probability that both
draws land in `A` is `|A| (|A| - 1) / (N (N - 1))`. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem without_replacement_both_draws_probability (A : Finset (Fin N)) :
    (uniformOn (((Finset.univ : Finset (Fin N)).offDiag : Finset (Fin N × Fin N)) :
        Set (Fin N × Fin N))).real ({p | p.1 ∈ A} ∩ {p | p.2 ∈ A}) =
      (A.card : ℝ) * (A.card - 1) / (N * (N - 1)) :=
  UndergradKB.Statistics.withoutReplacement_both_prob A

/-- OpenStax Introductory Statistics 2e §3.2 (ST-029). Sampling without replacement: the two draws
are not independent. For a set `A` with `0 < |A| < N`, the probability that both draws are in `A`
differs from the product of the single-draw probabilities. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem without_replacement_draws_not_independent (hN : 2 ≤ N) (A : Finset (Fin N))
    (h0 : 0 < A.card) (hlt : A.card < N) :
    (uniformOn (((Finset.univ : Finset (Fin N)).offDiag : Finset (Fin N × Fin N)) :
        Set (Fin N × Fin N))).real ({p | p.1 ∈ A} ∩ {p | p.2 ∈ A}) ≠
      (uniformOn (((Finset.univ : Finset (Fin N)).offDiag : Finset (Fin N × Fin N)) :
        Set (Fin N × Fin N))).real {p | p.1 ∈ A} *
        (uniformOn (((Finset.univ : Finset (Fin N)).offDiag : Finset (Fin N × Fin N)) :
          Set (Fin N × Fin N))).real {p | p.2 ∈ A} :=
  UndergradKB.Statistics.withoutReplacement_not_indep hN A h0 hlt

end Sampling

section Contingency

variable {α ρ γ : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [DecidableEq ρ] [DecidableEq γ]

/-- OpenStax Introductory Statistics 2e §3.4 (ST-030). In a contingency table (individuals labelled
by a row `r` and a column `c`), the probability that a randomly chosen individual lies in row `i`
is the row total divided by the grand total. -/
@[kb "openstaxintrostats2e" "§3.4, p. 194"]
theorem contingency_row_probability (r : α → ρ) (i : ρ) :
    (uniformOn (Set.univ : Set α)).real {ω | r ω = i} =
      ((Finset.univ.filter fun ω => r ω = i).card : ℝ) / Fintype.card α :=
  UndergradKB.Statistics.contingency_row_prob r i

/-- OpenStax Introductory Statistics 2e §3.4 (ST-030). The probability of being in row `i` and
column `j` is the cell count divided by the grand total. -/
@[kb "openstaxintrostats2e" "§3.4, p. 194"]
theorem contingency_cell_probability (r : α → ρ) (c : α → γ) (i : ρ) (j : γ) :
    (uniformOn (Set.univ : Set α)).real {ω | r ω = i ∧ c ω = j} =
      ((Finset.univ.filter fun ω => r ω = i ∧ c ω = j).card : ℝ) / Fintype.card α :=
  UndergradKB.Statistics.contingency_cell_prob r c i j

/-- OpenStax Introductory Statistics 2e §3.4 (ST-030). The conditional probability of column `j`
given row `i` is the cell count divided by the row total, when the row total is positive. -/
@[kb "openstaxintrostats2e" "§3.4, p. 194"]
theorem contingency_conditional_probability (r : α → ρ) (c : α → γ) (i : ρ) (j : γ)
    (hrow : 0 < (Finset.univ.filter fun ω => r ω = i).card) :
    (cond (uniformOn (Set.univ : Set α)) {ω | r ω = i} {ω | c ω = j}).toReal =
      ((Finset.univ.filter fun ω => r ω = i ∧ c ω = j).card : ℝ) /
        (Finset.univ.filter fun ω => r ω = i).card :=
  UndergradKB.Statistics.contingency_cond_prob r c i j hrow

end Contingency

end UndergradKB.Statistics.Course.C3
