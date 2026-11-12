import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalProbability
import UndergradKB.Common

/-! # Course layer: Levin, Chapter 3 (counting)
Rows of the checklist section "Counting" that are `in Mathlib` and stated only by Levin. -/

namespace UndergradKB.Foundations.Course

open Finset

/-- FO-218. A set with `n` elements has `2^n` subsets. -/
@[kb "levin2025" "Ex 3.2.13, p. 233"]
theorem levin_ex_3_2_13_card_powerset {α : Type*} (A : Finset α) :
    A.powerset.card = 2 ^ A.card :=
  Finset.card_powerset A

/-- FO-220. A bijection between two finite sets shows they have the same number of elements. -/
@[kb "levin2025" "Remark 3.1.7, p. 220"]
theorem levin_rem_3_1_7_card_bijection {α β : Type*} (A : Finset α) (B : Finset β) (e : α ≃ β)
    (h : ∀ a, a ∈ A ↔ e a ∈ B) : A.card = B.card :=
  Finset.card_equiv e h

/-- FO-235. Row sum: `C(n,0) + C(n,1) + ... + C(n,n) = 2^n`. -/
@[kb "levin2025" "Ex 3.6.6, p. 281"]
theorem levin_ex_3_6_6_row_sum (n : ℕ) : ∑ k ∈ range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-- FO-241. Inclusion-exclusion for any finite family of sets: the size of the union is the
alternating sum of sizes of the intersections of nonempty subfamilies. -/
@[kb "levin2025" "Text §3.3.3, p. 244"]
theorem levin_s3_3_3_inclusion_exclusion {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (S : ι → Finset α) :
    ((s.biUnion S).card : ℤ) =
      ∑ t : s.powerset.filter (·.Nonempty),
        (-1 : ℤ) ^ (t.1.card + 1) * (t.1.inf' (Finset.mem_filter.1 t.2).2 S).card :=
  Finset.inclusion_exclusion_card_biUnion s S

/-- FO-251. Derangements: permutations without fixed points. There are 2 of `{1,2,3}` and 9 of `{1,2,3,4}`. -/
@[kb "levin2025" "Text §3.8.3, p. 315"]
theorem levin_s3_8_3_derangements :
    Fintype.card (derangements (Fin 3)) = 2 ∧ Fintype.card (derangements (Fin 4)) = 9 := by
  rw [card_derangements_eq_numDerangements, card_derangements_eq_numDerangements]
  simp [numDerangements]

/-- FO-254. In a finite uniform sample space `s`, the probability of an event `t` is
`|s ∩ t| / |s|`. -/
@[kb "levin2025" "Def 3.7.4, p. 296"]
theorem levin_def_3_7_4_uniform_probability {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [DecidableEq Ω] (s t : Finset Ω) :
    ProbabilityTheory.uniformOn (s : Set Ω) (t : Set Ω) = ((s ∩ t).card : ENNReal) / s.card :=
  ProbabilityTheory.uniformOn_apply_finset

/-- FO-255. Complement rule: `P(Eᶜ) = 1 - P(E)` for a probability measure. -/
@[kb "levin2025" "Thm 3.7.7, p. 298"]
theorem levin_thm_3_7_7_complement {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) :
    μ Eᶜ = 1 - μ E :=
  MeasureTheory.prob_compl_eq_one_sub hE

/-- FO-256. Union rule: additivity for disjoint events. -/
@[kb "levin2025" "Thm 3.7.10, p. 300"]
theorem levin_thm_3_7_10_union_disjoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A B : Set Ω) (h : Disjoint A B) (hB : MeasurableSet B) :
    μ (A ∪ B) = μ A + μ B :=
  MeasureTheory.measure_union h hB

/-- FO-256 (general). `P(A ∪ B) + P(A ∩ B) = P(A) + P(B)`. -/
@[kb "levin2025" "Thm 3.7.10, p. 300"]
theorem levin_thm_3_7_10_union_add_inter {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A B : Set Ω) (hB : MeasurableSet B) :
    μ (A ∪ B) + μ (A ∩ B) = μ A + μ B :=
  MeasureTheory.measure_union_add_inter A hB

/-- FO-257. Two events are independent exactly when `P(A ∩ B) = P(A) P(B)`. -/
@[kb "levin2025" "Def 3.7.13, p. 301"]
theorem levin_def_3_7_13_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ProbabilityTheory.IndepSet A B μ ↔ μ (A ∩ B) = μ A * μ B :=
  ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hA hB μ

/-- FO-258. Conditional probability: `P(A | B) = P(B ∩ A) / P(B)`. -/
@[kb "levin2025" "Def 3.7.15, p. 303"]
theorem levin_def_3_7_15_conditional {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A B : Set Ω) (hB : MeasurableSet B) :
    ProbabilityTheory.cond μ B A = (μ B)⁻¹ * μ (B ∩ A) :=
  ProbabilityTheory.cond_apply hB μ A

end UndergradKB.Foundations.Course
