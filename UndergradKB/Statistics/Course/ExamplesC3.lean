import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Rules
import UndergradKB.Statistics.Remarks

/-!
# Worked examples, chapter 3 (OpenStax *Introductory Statistics 2e*): probability topics

Equally likely outcomes are modelled by `ProbabilityTheory.uniformOn Set.univ` on a finite type;
contingency tables by the probability mass function with weights equal to the cell counts. All
probabilities are stated as real numbers (`ENNReal.toReal`) equal to exact rationals.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Statistics.Course.ExamplesC3

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]

private lemma coe_filter_univ (p : Ω → Prop) [DecidablePred p] :
    ((Finset.univ.filter p : Finset Ω) : Set Ω) = {ω | p ω} := by
  ext; simp

private lemma uniform_real (s : Finset Ω) :
    (uniformOn (Set.univ : Set Ω) (s : Set Ω)).toReal = (#s : ℝ) / Fintype.card Ω := by
  classical
  have h := uniformOn_apply_finset (Ω := Ω) (s := Finset.univ) (t := s)
  rw [Finset.coe_univ] at h
  rw [h, Finset.univ_inter, Finset.card_univ, ENNReal.toReal_div]
  simp

omit [MeasurableSingletonClass Ω] [Fintype Ω] in
private lemma cond_real (μ : Measure Ω) {s t : Set Ω} (hs : MeasurableSet s) :
    (μ[t | s]).toReal = (μ (s ∩ t)).toReal / (μ s).toReal := by
  rw [cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- Equally likely outcomes: the probability of an event is the number of favourable outcomes over
the number of outcomes. -/
private lemma prob_card (p : Ω → Prop) [DecidablePred p] (k N : ℕ) (hN : Fintype.card Ω = N)
    (hk : #(Finset.univ.filter p) = k) :
    (uniformOn (Set.univ : Set Ω) {ω | p ω}).toReal = (k : ℝ) / N := by
  have := uniform_real (Finset.univ.filter p)
  rw [coe_filter_univ] at this
  rw [this, hk, hN]

/-- Conditional probability for equally likely outcomes. -/
private lemma cprob_card (p q : Ω → Prop) [DecidablePred p] [DecidablePred q] (a b : ℕ)
    (ha : #(Finset.univ.filter (fun ω => p ω ∧ q ω)) = a) (hb : #(Finset.univ.filter p) = b) :
    ((uniformOn (Set.univ : Set Ω))[{ω | q ω} | {ω | p ω}]).toReal = (a : ℝ) / b := by
  have hs : MeasurableSet {ω | p ω} := (Set.toFinite _).measurableSet
  rw [cond_real _ hs]
  have h1 := uniform_real (Finset.univ.filter (fun ω => p ω ∧ q ω))
  have h2 := uniform_real (Finset.univ.filter p)
  rw [coe_filter_univ] at h1 h2
  have : {ω | p ω} ∩ {ω | q ω} = {ω | p ω ∧ q ω} := rfl
  rw [this, h1, h2, ha, hb]
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · rw [← ha, ← hb]; simp
  · have : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
    rw [div_div_div_cancel_right₀ this]

/-- A probability mass function with weights `n ω / D`. -/
private noncomputable def natPMF (n : Ω → ℕ) (D : ℕ) (h : ∑ ω, n ω = D) (h0 : D ≠ 0) : PMF Ω :=
  PMF.ofFintype (fun ω => (n ω : ℝ≥0∞) / D) (by
    rw [← ENNReal.sum_div, ← Nat.cast_sum, h, ENNReal.div_self] <;> simp [h0])

private lemma natPMF_real (n : Ω → ℕ) (D : ℕ) (h : ∑ ω, n ω = D) (h0 : D ≠ 0) (A : Finset Ω) :
    ((natPMF n D h h0).toMeasure (A : Set Ω)).toReal = (∑ ω ∈ A, (n ω : ℝ)) / D := by
  classical
  rw [PMF.toMeasure_apply_fintype]
  simp only [natPMF, PMF.ofFintype_apply, Set.indicator_apply, Finset.mem_coe]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ A)]
  have h1 : (Finset.univ.filter (· ∈ A)) = A := by ext; simp
  have h2 : ∑ x ∈ Finset.univ.filter (¬ · ∈ A), (if x ∈ A then (n x : ℝ≥0∞) / D else 0) = 0 :=
    Finset.sum_eq_zero (by intro x hx; simp at hx; simp [hx])
  rw [h2, h1, add_zero, Finset.sum_congr rfl (g := fun x => (n x : ℝ≥0∞) / D)
    (by intro x hx; simp [hx]), ← ENNReal.sum_div, ENNReal.toReal_div, ← Nat.cast_sum]
  simp [ENNReal.toReal_sum, ENNReal.toReal_natCast]

/-- Probability of an event under cell-count weights. -/
private lemma wprob_card (n : Ω → ℕ) (D : ℕ) (h : ∑ ω, n ω = D) (h0 : D ≠ 0) (p : Ω → Prop)
    [DecidablePred p] (k : ℕ) (hk : ∑ ω ∈ Finset.univ.filter p, n ω = k) :
    ((natPMF n D h h0).toMeasure {ω | p ω}).toReal = (k : ℝ) / D := by
  have := natPMF_real n D h h0 (Finset.univ.filter p)
  rw [coe_filter_univ] at this
  rw [this, ← hk]
  push_cast
  rfl

/-- Conditional probability under cell-count weights. -/
private lemma wcprob_card (n : Ω → ℕ) (D : ℕ) (h : ∑ ω, n ω = D) (h0 : D ≠ 0) (p q : Ω → Prop)
    [DecidablePred p] [DecidablePred q] (a b : ℕ)
    (ha : ∑ ω ∈ Finset.univ.filter (fun ω => p ω ∧ q ω), n ω = a)
    (hb : ∑ ω ∈ Finset.univ.filter p, n ω = b) :
    (((natPMF n D h h0).toMeasure)[{ω | q ω} | {ω | p ω}]).toReal = (a : ℝ) / b := by
  have hs : MeasurableSet {ω | p ω} := (Set.toFinite _).measurableSet
  rw [cond_real _ hs]
  have h1 := wprob_card n D h h0 (fun ω => p ω ∧ q ω) a ha
  have h2 := wprob_card n D h h0 p b hb
  have : {ω | p ω} ∩ {ω | q ω} = {ω | p ω ∧ q ω} := rfl
  rw [this, h1, h2]
  have : (D : ℝ) ≠ 0 := by exact_mod_cast h0
  rw [div_div_div_cancel_right₀ this]

/-- The probability measure of a contingency table: each cell has probability its count over the
total. -/
private noncomputable def tableMeasure (n : Ω → ℕ) (h0 : ∑ ω, n ω ≠ 0) : Measure Ω :=
  (natPMF n (∑ ω, n ω) rfl h0).toMeasure

private lemma tprob (n : Ω → ℕ) (h0 : ∑ ω, n ω ≠ 0) (p : Ω → Prop) [DecidablePred p] (k D : ℕ)
    (hD : ∑ ω, n ω = D) (hk : ∑ ω ∈ Finset.univ.filter p, n ω = k) :
    (tableMeasure n h0 {ω | p ω}).toReal = (k : ℝ) / D := by
  rw [tableMeasure, wprob_card n _ rfl h0 p k hk, hD]

private lemma tcprob (n : Ω → ℕ) (h0 : ∑ ω, n ω ≠ 0) (p q : Ω → Prop) [DecidablePred p]
    [DecidablePred q] (a b : ℕ) (ha : ∑ ω ∈ Finset.univ.filter (fun ω => p ω ∧ q ω), n ω = a)
    (hb : ∑ ω ∈ Finset.univ.filter p, n ω = b) :
    ((tableMeasure n h0)[{ω | q ω} | {ω | p ω}]).toReal = (a : ℝ) / b :=
  wcprob_card n _ rfl h0 p q a b ha hb

end Helpers

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {A B : Set Ω}

private lemma cond_toReal (hB : MeasurableSet B) :
    (P[A | B]).toReal = P.real (B ∩ A) / P.real B := by
  rw [cond_apply hB, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [measureReal_def]
  ring

private lemma indep_real (hA : MeasurableSet A) (hB : MeasurableSet B) (hi : IndepSet A B P) :
    P.real (A ∩ B) = P.real A * P.real B := by
  have := (indepSet_iff_measure_inter_eq_mul hA hB P).1 hi
  simp only [measureReal_def, this, ENNReal.toReal_mul]

private lemma indep_of_real (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : P.real (A ∩ B) = P.real A * P.real B) : IndepSet A B P := by
  refine (indepSet_iff_measure_inter_eq_mul hA hB P).2 ?_
  simp only [measureReal_def, ← ENNReal.toReal_mul] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P (A ∩ B))
    (ENNReal.mul_ne_top (measure_ne_top P A) (measure_ne_top P B))).1 h

end Abstract

/-- OpenStax Introductory Statistics 2e Example 3.1. Choose one of the whole numbers 1 to 19 at
random; with `A` the even numbers and `B` the numbers above 13: `P(A) = 9/19`, `P(B) = 6/19`,
`P(A and B) = 3/19`, `P(A or B) = 12/19`, `P(A') = 10/19`, `P(A | B) = 1/2`, `P(B | A) = 1/3`
(so the two conditional probabilities differ). -/
@[kb "openstaxintrostats2e" "Example 3.1, p. 181"]
theorem example_3_1_numbers_one_to_nineteen :
    let P : Measure (Fin 19) := uniformOn Set.univ
    let A : Set (Fin 19) := {i | ((i : ℕ) + 1) % 2 = 0}
    let B : Set (Fin 19) := {i | 13 < (i : ℕ) + 1}
    (P A).toReal = 9 / 19 ∧ (P B).toReal = 6 / 19 ∧ (P (A ∩ B)).toReal = 3 / 19 ∧
      (P (A ∪ B)).toReal = 12 / 19 ∧ (P Aᶜ).toReal = 10 / 19 ∧
      (P[A | B]).toReal = 1 / 2 ∧ (P[B | A]).toReal = 1 / 3 := by
  intro P A B
  have hc : Fintype.card (Fin 19) = 19 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (prob_card (fun i : Fin 19 => ((i : ℕ) + 1) % 2 = 0) 9 19 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 19 => 13 < (i : ℕ) + 1) 6 19 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 19 => ((i : ℕ) + 1) % 2 = 0 ∧ 13 < (i : ℕ) + 1) 3 19 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 19 => ((i : ℕ) + 1) % 2 = 0 ∨ 13 < (i : ℕ) + 1) 12 19 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 19 => ¬ (((i : ℕ) + 1) % 2 = 0)) 10 19 hc (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 19 => 13 < (i : ℕ) + 1) (fun i => ((i : ℕ) + 1) % 2 = 0) 3 6
      (by decide) (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 19 => ((i : ℕ) + 1) % 2 = 0) (fun i => 13 < (i : ℕ) + 1) 3 9
      (by decide) (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.2. One roll of a fair die (the face is `i + 1`
for `i : Fin 6`): `P(two) = 1/6`, `P(even) = 1/2`, `P(less than 4) = 1/2`, `P(even') = 1/2`,
`P(A | B) = P(B | A) = 1/3`, `P(A and B) = 1/6`, `P(A or B) = 5/6`, `P(A or B') = 2/3`,
`P(prime) = 1/2` and `P(seven) = 0`, where `A` is "even" and `B` is "less than four". -/
@[kb "openstaxintrostats2e" "Example 3.2, p. 182"]
theorem example_3_2_one_die :
    let P : Measure (Fin 6) := uniformOn Set.univ
    let A : Set (Fin 6) := {i | ((i : ℕ) + 1) % 2 = 0}
    let B : Set (Fin 6) := {i | (i : ℕ) + 1 < 4}
    (P {i | (i : ℕ) + 1 = 2}).toReal = 1 / 6 ∧ (P A).toReal = 1 / 2 ∧ (P B).toReal = 1 / 2 ∧
      (P Aᶜ).toReal = 1 / 2 ∧ (P[A | B]).toReal = 1 / 3 ∧ (P[B | A]).toReal = 1 / 3 ∧
      (P (A ∩ B)).toReal = 1 / 6 ∧ (P (A ∪ B)).toReal = 5 / 6 ∧ (P (A ∪ Bᶜ)).toReal = 2 / 3 ∧
      (P {i | Nat.Prime ((i : ℕ) + 1)}).toReal = 1 / 2 ∧ (P {i | (i : ℕ) + 1 = 7}).toReal = 0 := by
  intro P A B
  have hc : Fintype.card (Fin 6) = 6 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (prob_card (fun i : Fin 6 => (i : ℕ) + 1 = 2) 1 6 hc (by decide)).trans ?_; norm_num
  · refine (prob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 0) 3 6 hc (by decide)).trans ?_; norm_num
  · refine (prob_card (fun i : Fin 6 => (i : ℕ) + 1 < 4) 3 6 hc (by decide)).trans ?_; norm_num
  · exact (prob_card (fun i : Fin 6 => ¬ (((i : ℕ) + 1) % 2 = 0)) 3 6 hc (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 6 => (i : ℕ) + 1 < 4) (fun i => ((i : ℕ) + 1) % 2 = 0) 1 3
      (by decide) (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 0) (fun i => (i : ℕ) + 1 < 4) 1 3
      (by decide) (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 0 ∧ (i : ℕ) + 1 < 4) 1 6 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 0 ∨ (i : ℕ) + 1 < 4) 5 6 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 0 ∨ ¬ ((i : ℕ) + 1 < 4)) 4 6 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 6 => Nat.Prime ((i : ℕ) + 1)) 3 6 hc (by decide)).trans (by norm_num)
  · refine (prob_card (fun i : Fin 6 => (i : ℕ) + 1 = 7) 0 6 hc (by decide)).trans ?_; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.6. Two fair coins (`0` is heads, `1` is tails,
outcomes `Fin 2 × Fin 2`): at most one tail has probability 3/4, all tails 1/4, the events "all
tails" and "all heads" are mutually exclusive, a head on the first coin has probability 1/2 and at
least one tail 3/4. -/
@[kb "openstaxintrostats2e" "Example 3.6, p. 186"]
theorem example_3_6_two_coins :
    let P : Measure (Fin 2 × Fin 2) := uniformOn Set.univ
    (P {ω | (ω.1 : ℕ) + ω.2 ≤ 1}).toReal = 3 / 4 ∧ (P {ω | ω = (1, 1)}).toReal = 1 / 4 ∧
      (P ({ω | ω = (1, 1)} ∩ {ω | ω = (0, 0)})).toReal = 0 ∧
      (P {ω | (ω.1 : ℕ) = 0}).toReal = 1 / 2 ∧ (P {ω | 1 ≤ (ω.1 : ℕ) + ω.2}).toReal = 3 / 4 := by
  intro P
  have hc : Fintype.card (Fin 2 × Fin 2) = 4 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) + ω.2 ≤ 1) 3 4 hc (by decide)).trans (by norm_num)
  · refine (prob_card (fun ω : Fin 2 × Fin 2 => ω = (1, 1)) 1 4 hc (by decide)).trans ?_; norm_num
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => ω = (1, 1) ∧ ω = (0, 0)) 0 4 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 2 4 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => 1 ≤ (ω.1 : ℕ) + ω.2) 3 4 hc (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.7. Two fair coins: "at most one tail" `F` has
probability 3/4, "two faces the same" `G` has probability 1/2, "head on the first flip" `H` has
probability 1/2; `F` and `G` share the outcome HH so `P(F and G) = 1/4 ≠ 0` (not mutually
exclusive), while "all tails" and `H` cannot occur together (`P = 0`, mutually exclusive). -/
@[kb "openstaxintrostats2e" "Example 3.7, p. 187"]
theorem example_3_7_two_coins_mutually_exclusive :
    let P : Measure (Fin 2 × Fin 2) := uniformOn Set.univ
    (P {ω | (ω.1 : ℕ) + ω.2 ≤ 1}).toReal = 3 / 4 ∧ (P {ω | ω.1 = ω.2}).toReal = 1 / 2 ∧
      (P {ω | (ω.1 : ℕ) = 0}).toReal = 1 / 2 ∧
      (P {ω | (ω.1 : ℕ) + ω.2 ≤ 1 ∧ ω.1 = ω.2}).toReal = 1 / 4 ∧
      (P {ω | ω = (1, 1) ∧ (ω.1 : ℕ) = 0}).toReal = 0 := by
  intro P
  have hc : Fintype.card (Fin 2 × Fin 2) = 4 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) + ω.2 ≤ 1) 3 4 hc (by decide)).trans (by norm_num)
  · refine (prob_card (fun ω : Fin 2 × Fin 2 => ω.1 = ω.2) 2 4 hc (by decide)).trans ?_; norm_num
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 2 4 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) + ω.2 ≤ 1 ∧ ω.1 = ω.2) 1 4 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => ω = (1, 1) ∧ (ω.1 : ℕ) = 0) 0 4 hc
      (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.8. One roll of a fair die with `A` = odd faces,
`C` = odd faces larger than two, `D` = even faces smaller than five, `E` = faces below five:
`P(A) = 1/2`, `P(C and D) = 0` (mutually exclusive), `P(C and E) = 1/6 ≠ 0` (not mutually
exclusive) and `P(C | A) = 2/3`. -/
@[kb "openstaxintrostats2e" "Example 3.8, p. 187"]
theorem example_3_8_die_mutually_exclusive :
    let P : Measure (Fin 6) := uniformOn Set.univ
    let A : Set (Fin 6) := {i | ((i : ℕ) + 1) % 2 = 1}
    let C : Set (Fin 6) := {i | ((i : ℕ) + 1) % 2 = 1 ∧ 2 < (i : ℕ) + 1}
    (P A).toReal = 1 / 2 ∧
      (P (C ∩ {i | ((i : ℕ) + 1) % 2 = 0 ∧ (i : ℕ) + 1 < 5})).toReal = 0 ∧
      (P (C ∩ {i | (i : ℕ) + 1 < 5})).toReal = 1 / 6 ∧ (P[C | A]).toReal = 2 / 3 := by
  intro P A C
  have hc : Fintype.card (Fin 6) = 6 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 1) 3 6 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 6 => (((i : ℕ) + 1) % 2 = 1 ∧ 2 < (i : ℕ) + 1) ∧
      (((i : ℕ) + 1) % 2 = 0 ∧ (i : ℕ) + 1 < 5)) 0 6 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 6 => (((i : ℕ) + 1) % 2 = 1 ∧ 2 < (i : ℕ) + 1) ∧
      (i : ℕ) + 1 < 5) 1 6 hc (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 1)
      (fun i => ((i : ℕ) + 1) % 2 = 1 ∧ 2 < (i : ℕ) + 1) 2 3 (by decide) (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.11. A box holds red cards 1-3 and blue cards 1-5
(eight cards, one drawn at random; card `i` is red with number `i + 1` when `i < 3`, blue with
number `i - 2` otherwise). `P(red) = 3/8`, `P(blue) = 5/8`, `P(red and blue) = 0`,
`P(even) = 3/8`, `P(even | blue) = 2/5`, `P(blue | even) = 2/3`; with `G` = a card numbered above
3 and `H` = a blue card numbered 1 to 4, `P(G) = 1/4 = P(G | H)`. -/
@[kb "openstaxintrostats2e" "Example 3.11, p. 189"]
theorem example_3_11_cards_in_a_box :
    let P : Measure (Fin 8) := uniformOn Set.univ
    (P {i | (i : ℕ) < 3}).toReal = 3 / 8 ∧ (P {i | 3 ≤ (i : ℕ)}).toReal = 5 / 8 ∧
      (P {i | (i : ℕ) < 3 ∧ 3 ≤ (i : ℕ)}).toReal = 0 ∧
      (P {i | (if (i : ℕ) < 3 then (i : ℕ) + 1 else (i : ℕ) - 2) % 2 = 0}).toReal = 3 / 8 ∧
      (P[{i | (if (i : ℕ) < 3 then (i : ℕ) + 1 else (i : ℕ) - 2) % 2 = 0} |
        {i | 3 ≤ (i : ℕ)}]).toReal = 2 / 5 ∧
      (P[{i | 3 ≤ (i : ℕ)} |
        {i | (if (i : ℕ) < 3 then (i : ℕ) + 1 else (i : ℕ) - 2) % 2 = 0}]).toReal = 2 / 3 ∧
      (P {i | 3 ≤ (i : ℕ) ∧ 3 < (i : ℕ) - 2}).toReal = 1 / 4 ∧
      (P[{i | 3 ≤ (i : ℕ) ∧ 3 < (i : ℕ) - 2} | {i | 3 ≤ (i : ℕ) ∧ (i : ℕ) - 2 ≤ 4}]).toReal =
        1 / 4 := by
  intro P
  have hc : Fintype.card (Fin 8) = 8 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (prob_card (fun i : Fin 8 => (i : ℕ) < 3) 3 8 hc (by decide)).trans ?_; norm_num
  · refine (prob_card (fun i : Fin 8 => 3 ≤ (i : ℕ)) 5 8 hc (by decide)).trans ?_; norm_num
  · exact (prob_card (fun i : Fin 8 => (i : ℕ) < 3 ∧ 3 ≤ (i : ℕ)) 0 8 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 8 => (if (i : ℕ) < 3 then (i : ℕ) + 1 else (i : ℕ) - 2) % 2 = 0)
      3 8 hc (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 8 => 3 ≤ (i : ℕ))
      (fun i => (if (i : ℕ) < 3 then (i : ℕ) + 1 else (i : ℕ) - 2) % 2 = 0) 2 5 (by decide)
      (by decide)).trans (by norm_num)
  · exact (cprob_card
      (fun i : Fin 8 => (if (i : ℕ) < 3 then (i : ℕ) + 1 else (i : ℕ) - 2) % 2 = 0)
      (fun i => 3 ≤ (i : ℕ)) 2 3 (by decide) (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 8 => 3 ≤ (i : ℕ) ∧ 3 < (i : ℕ) - 2) 2 8 hc (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 8 => 3 ≤ (i : ℕ) ∧ (i : ℕ) - 2 ≤ 4)
      (fun i => 3 ≤ (i : ℕ) ∧ 3 < (i : ℕ) - 2) 1 4 (by decide) (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.13. Toss a fair coin and then a fair die (12
equally likely outcomes `(coin, face)`, coin `0` = heads, face `j + 1`): `A` = heads then an even
face has probability 1/4, `B` = heads then a three has probability 1/12, `A` and `B` are mutually
exclusive, and `P(A and B) = 0 ≠ P(A)P(B) = 1/48`, so they are dependent. -/
@[kb "openstaxintrostats2e" "Example 3.13, p. 190"]
theorem example_3_13_coin_then_die :
    let P : Measure (Fin 2 × Fin 6) := uniformOn Set.univ
    let A : Set (Fin 2 × Fin 6) := {ω | (ω.1 : ℕ) = 0 ∧ ((ω.2 : ℕ) + 1) % 2 = 0}
    let B : Set (Fin 2 × Fin 6) := {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) + 1 = 3}
    (P A).toReal = 1 / 4 ∧ (P B).toReal = 1 / 12 ∧ (P (A ∩ B)).toReal = 0 ∧
      (P (A ∩ B)).toReal ≠ (P A).toReal * (P B).toReal := by
  intro P A B
  have hc : Fintype.card (Fin 2 × Fin 6) = 12 := by simp
  have h1 : (P A).toReal = 1 / 4 := by
    exact (prob_card (fun ω : Fin 2 × Fin 6 => (ω.1 : ℕ) = 0 ∧ ((ω.2 : ℕ) + 1) % 2 = 0) 3 12 hc
      (by decide)).trans (by norm_num)
  have h2 : (P B).toReal = 1 / 12 := by
    exact (prob_card (fun ω : Fin 2 × Fin 6 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) + 1 = 3) 1 12 hc
      (by decide)).trans (by norm_num)
  have h3 : (P (A ∩ B)).toReal = 0 := by
    exact (prob_card (fun ω : Fin 2 × Fin 6 => ((ω.1 : ℕ) = 0 ∧ ((ω.2 : ℕ) + 1) % 2 = 0) ∧
      ((ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) + 1 = 3)) 0 12 hc (by decide)).trans (by norm_num)
  refine ⟨h1, h2, h3, ?_⟩
  rw [h1, h2, h3]; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.24 (urn, with replacement). An urn holds 3 red
and 8 blue balls and two are drawn with replacement (121 equally likely ordered pairs, ball `i` is
red when `i < 3`): `P(RR) = 9/121`, `P(RB or BR) = 48/121`, `P(R then B) = 24/121`,
`P(R on 2nd | B on 1st) = 3/11`, `P(BB) = 64/121`, `P(B on 2nd | R on 1st) = 8/11`. -/
@[kb "openstaxintrostats2e" "Example 3.24, p. 201"]
theorem example_3_24_urn_with_replacement :
    let P : Measure (Fin 11 × Fin 11) := uniformOn Set.univ
    (P {ω | (ω.1 : ℕ) < 3 ∧ (ω.2 : ℕ) < 3}).toReal = 9 / 121 ∧
      (P {ω | ((ω.1 : ℕ) < 3 ∧ 3 ≤ (ω.2 : ℕ)) ∨ (3 ≤ (ω.1 : ℕ) ∧ (ω.2 : ℕ) < 3)}).toReal =
        48 / 121 ∧
      (P {ω | (ω.1 : ℕ) < 3 ∧ 3 ≤ (ω.2 : ℕ)}).toReal = 24 / 121 ∧
      (P[{ω | (ω.2 : ℕ) < 3} | {ω | 3 ≤ (ω.1 : ℕ)}]).toReal = 3 / 11 ∧
      (P {ω | 3 ≤ (ω.1 : ℕ) ∧ 3 ≤ (ω.2 : ℕ)}).toReal = 64 / 121 ∧
      (P[{ω | 3 ≤ (ω.2 : ℕ)} | {ω | (ω.1 : ℕ) < 3}]).toReal = 8 / 11 := by
  intro P
  have hc : Fintype.card (Fin 11 × Fin 11) = 121 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun ω : Fin 11 × Fin 11 => (ω.1 : ℕ) < 3 ∧ (ω.2 : ℕ) < 3) 9 121 hc
      (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 11 × Fin 11 =>
      ((ω.1 : ℕ) < 3 ∧ 3 ≤ (ω.2 : ℕ)) ∨ (3 ≤ (ω.1 : ℕ) ∧ (ω.2 : ℕ) < 3)) 48 121 hc
      (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 11 × Fin 11 => (ω.1 : ℕ) < 3 ∧ 3 ≤ (ω.2 : ℕ)) 24 121 hc
      (by decide +kernel)).trans (by norm_num)
  · exact (cprob_card (fun ω : Fin 11 × Fin 11 => 3 ≤ (ω.1 : ℕ)) (fun ω => (ω.2 : ℕ) < 3) 24 88
      (by decide +kernel) (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 11 × Fin 11 => 3 ≤ (ω.1 : ℕ) ∧ 3 ≤ (ω.2 : ℕ)) 64 121 hc
      (by decide +kernel)).trans (by norm_num)
  · exact (cprob_card (fun ω : Fin 11 × Fin 11 => (ω.1 : ℕ) < 3) (fun ω => 3 ≤ (ω.2 : ℕ)) 24 33
      (by decide +kernel) (by decide +kernel)).trans (by norm_num)

/-- Ordered draws of two distinct items from `n` without replacement, all `n (n - 1)` equally
likely. -/
abbrev TwoWithoutReplacement (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- OpenStax Introductory Statistics 2e Example 3.25 (urn, without replacement). Three red and
eight blue balls, two drawn without replacement (110 equally likely ordered pairs of distinct
balls, ball `i` red when `i < 3`): `P(RR) = 3/55`, `P(RB or BR) = 24/55`,
`P(R on 2nd | B on 1st) = 3/10`, `P(R then B) = 12/55`, `P(BB) = 28/55`,
`P(B on 2nd | R on 1st) = 4/5`. -/
@[kb "openstaxintrostats2e" "Example 3.25, p. 202"]
theorem example_3_25_urn_without_replacement :
    let P : Measure (TwoWithoutReplacement 11) := uniformOn Set.univ
    (P {ω | (ω.1.1 : ℕ) < 3 ∧ (ω.1.2 : ℕ) < 3}).toReal = 3 / 55 ∧
      (P {ω | ((ω.1.1 : ℕ) < 3 ∧ 3 ≤ (ω.1.2 : ℕ)) ∨ (3 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 3)}).toReal =
        24 / 55 ∧
      (P[{ω | (ω.1.2 : ℕ) < 3} | {ω | 3 ≤ (ω.1.1 : ℕ)}]).toReal = 3 / 10 ∧
      (P {ω | (ω.1.1 : ℕ) < 3 ∧ 3 ≤ (ω.1.2 : ℕ)}).toReal = 12 / 55 ∧
      (P {ω | 3 ≤ (ω.1.1 : ℕ) ∧ 3 ≤ (ω.1.2 : ℕ)}).toReal = 28 / 55 ∧
      (P[{ω | 3 ≤ (ω.1.2 : ℕ)} | {ω | (ω.1.1 : ℕ) < 3}]).toReal = 4 / 5 := by
  intro P
  have hc : Fintype.card (TwoWithoutReplacement 11) = 110 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun ω : TwoWithoutReplacement 11 => (ω.1.1 : ℕ) < 3 ∧ (ω.1.2 : ℕ) < 3) 6 110
      hc (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : TwoWithoutReplacement 11 =>
      ((ω.1.1 : ℕ) < 3 ∧ 3 ≤ (ω.1.2 : ℕ)) ∨ (3 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 3)) 48 110 hc
      (by decide +kernel)).trans (by norm_num)
  · exact (cprob_card (fun ω : TwoWithoutReplacement 11 => 3 ≤ (ω.1.1 : ℕ))
      (fun ω => (ω.1.2 : ℕ) < 3) 24 80 (by decide +kernel) (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : TwoWithoutReplacement 11 => (ω.1.1 : ℕ) < 3 ∧ 3 ≤ (ω.1.2 : ℕ)) 24
      110 hc (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : TwoWithoutReplacement 11 => 3 ≤ (ω.1.1 : ℕ) ∧ 3 ≤ (ω.1.2 : ℕ)) 56
      110 hc (by decide +kernel)).trans (by norm_num)
  · exact (cprob_card (fun ω : TwoWithoutReplacement 11 => (ω.1.1 : ℕ) < 3)
      (fun ω => 3 ≤ (ω.1.2 : ℕ)) 24 30 (by decide +kernel) (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.26. Four tabby and five black kittens, two
chosen without replacement (72 equally likely ordered pairs, kitten `i` is tabby when `i < 4`):
both tabby has probability 1/6, one of each colour 5/9, a tabby second given a black first 1/2, and
two of the same colour 4/9. -/
@[kb "openstaxintrostats2e" "Example 3.26, p. 204"]
theorem example_3_26_kittens :
    let P : Measure (TwoWithoutReplacement 9) := uniformOn Set.univ
    (P {ω | (ω.1.1 : ℕ) < 4 ∧ (ω.1.2 : ℕ) < 4}).toReal = 1 / 6 ∧
      (P {ω | ((ω.1.1 : ℕ) < 4 ∧ 4 ≤ (ω.1.2 : ℕ)) ∨ (4 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 4)}).toReal =
        5 / 9 ∧
      (P[{ω | (ω.1.2 : ℕ) < 4} | {ω | 4 ≤ (ω.1.1 : ℕ)}]).toReal = 1 / 2 ∧
      (P {ω | ((ω.1.1 : ℕ) < 4 ∧ (ω.1.2 : ℕ) < 4) ∨ (4 ≤ (ω.1.1 : ℕ) ∧ 4 ≤ (ω.1.2 : ℕ))}).toReal =
        4 / 9 := by
  intro P
  have hc : Fintype.card (TwoWithoutReplacement 9) = 72 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun ω : TwoWithoutReplacement 9 => (ω.1.1 : ℕ) < 4 ∧ (ω.1.2 : ℕ) < 4) 12 72
      hc (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : TwoWithoutReplacement 9 =>
      ((ω.1.1 : ℕ) < 4 ∧ 4 ≤ (ω.1.2 : ℕ)) ∨ (4 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 4)) 40 72 hc
      (by decide +kernel)).trans (by norm_num)
  · exact (cprob_card (fun ω : TwoWithoutReplacement 9 => 4 ≤ (ω.1.1 : ℕ))
      (fun ω => (ω.1.2 : ℕ) < 4) 20 40 (by decide +kernel) (by decide +kernel)).trans (by norm_num)
  · exact (prob_card (fun ω : TwoWithoutReplacement 9 =>
      ((ω.1.1 : ℕ) < 4 ∧ (ω.1.2 : ℕ) < 4) ∨ (4 ≤ (ω.1.1 : ℕ) ∧ 4 ≤ (ω.1.2 : ℕ))) 32 72 hc
      (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.27. One of the outcomes 1 to 12 is chosen at
random, `A = {1, ..., 6}` and `B = {6, 7, 8, 9}`: `P(A) = 1/2`, `P(B) = 1/3`,
`P(A and B) = 1/12` and `P(A or B) = 3/4`. -/
@[kb "openstaxintrostats2e" "Example 3.27, p. 205"]
theorem example_3_27_venn_of_twelve_outcomes :
    let P : Measure (Fin 12) := uniformOn Set.univ
    let A : Set (Fin 12) := {i | (i : ℕ) + 1 ≤ 6}
    let B : Set (Fin 12) := {i | 6 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ 9}
    (P A).toReal = 1 / 2 ∧ (P B).toReal = 1 / 3 ∧ (P (A ∩ B)).toReal = 1 / 12 ∧
      (P (A ∪ B)).toReal = 3 / 4 := by
  intro P A B
  have hc : Fintype.card (Fin 12) = 12 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (prob_card (fun i : Fin 12 => (i : ℕ) + 1 ≤ 6) 6 12 hc (by decide)).trans ?_; norm_num
  · exact (prob_card (fun i : Fin 12 => 6 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ 9) 4 12 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 12 => (i : ℕ) + 1 ≤ 6 ∧ (6 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ 9)) 1 12
      hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 12 => (i : ℕ) + 1 ≤ 6 ∨ (6 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ 9)) 9 12
      hc (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Example 3.28. Two fair coins (`1` is tails), `A` = tails on
the first coin, `B` = tails on the second: `P(A and B) = 1/4`, `P(A or B) = 3/4`, and the outcome HH
lies in neither (`P(neither) = 1/4`). -/
@[kb "openstaxintrostats2e" "Example 3.28, p. 206"]
theorem example_3_28_two_coins_venn :
    let P : Measure (Fin 2 × Fin 2) := uniformOn Set.univ
    let A : Set (Fin 2 × Fin 2) := {ω | (ω.1 : ℕ) = 1}
    let B : Set (Fin 2 × Fin 2) := {ω | (ω.2 : ℕ) = 1}
    (P (A ∩ B)).toReal = 1 / 4 ∧ (P (A ∪ B)).toReal = 3 / 4 ∧ (P (A ∪ B)ᶜ).toReal = 1 / 4 := by
  intro P A B
  have hc : Fintype.card (Fin 2 × Fin 2) = 4 := by simp
  refine ⟨?_, ?_, ?_⟩
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1) 1 4 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1 ∨ (ω.2 : ℕ) = 1) 3 4 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => ¬ ((ω.1 : ℕ) = 1 ∨ (ω.2 : ℕ) = 1)) 1 4 hc
      (by decide)).trans (by norm_num)

/-- Cell counts of the sex-by-handedness table of Example 3.3: rows males, females; columns
right-handed, left-handed. -/
def handednessCounts : Fin 2 × Fin 2 → ℕ := fun ω => ![![43, 9], ![44, 4]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Example 3.3. In a sample of 100 people (43 right-handed
males, 9 left-handed males, 44 right-handed females, 4 left-handed females), with `M`, `F`
(male, female) and `R`, `L` (right-, left-handed): `P(M) = 0.52`, `P(F) = 0.48`, `P(R) = 0.87`,
`P(L) = 0.13`, `P(M and R) = 0.43`, `P(F and L) = 0.04`, `P(M or F) = 1`, `P(M or R) = 0.96`,
`P(F or L) = 0.57`, `P(M') = 0.48`, `P(R | M) = 43/52`, `P(F | L) = 4/13`, `P(L | F) = 1/12`. -/
@[kb "openstaxintrostats2e" "Example 3.3, p. 183"]
theorem example_3_3_handedness_table :
    let P : Measure (Fin 2 × Fin 2) := tableMeasure handednessCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0}).toReal = 0.52 ∧ (P {ω | (ω.1 : ℕ) = 1}).toReal = 0.48 ∧
      (P {ω | (ω.2 : ℕ) = 0}).toReal = 0.87 ∧ (P {ω | (ω.2 : ℕ) = 1}).toReal = 0.13 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal = 0.43 ∧
      (P {ω | (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1}).toReal = 0.04 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∨ (ω.1 : ℕ) = 1}).toReal = 1 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 0}).toReal = 0.96 ∧
      (P {ω | (ω.1 : ℕ) = 1 ∨ (ω.2 : ℕ) = 1}).toReal = 0.57 ∧
      (P {ω | ¬ ((ω.1 : ℕ) = 0)}).toReal = 0.48 ∧
      (P[{ω | (ω.2 : ℕ) = 0} | {ω | (ω.1 : ℕ) = 0}]).toReal = 43 / 52 ∧
      (P[{ω | (ω.1 : ℕ) = 1} | {ω | (ω.2 : ℕ) = 1}]).toReal = 4 / 13 ∧
      (P[{ω | (ω.2 : ℕ) = 1} | {ω | (ω.1 : ℕ) = 1}]).toReal = 1 / 12 := by
  intro P
  have hD : ∑ ω, handednessCounts ω = 100 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 52 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1) 48 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 0) 87 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 1) 13 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 43 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1) 4 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∨ (ω.1 : ℕ) = 1) 100 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 0) 96 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1 ∨ (ω.2 : ℕ) = 1) 57 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => ¬ ((ω.1 : ℕ) = 0)) 48 100 hD (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) (fun ω => (ω.2 : ℕ) = 0) 43 52
      (by decide) (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 1) (fun ω => (ω.1 : ℕ) = 1) 4 13
      (by decide) (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1) (fun ω => (ω.2 : ℕ) = 1) 4 48
      (by decide) (by decide)).trans (by norm_num)

/-- Cell counts of the swim-team table of Example 3.16: rows advanced, intermediate, novice;
columns practises four times a week, does not. -/
def swimTeamCounts : Fin 3 × Fin 2 → ℕ := fun ω => ![![40, 35], ![30, 17], ![10, 18]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Example 3.16. A swim team of 150 has 75 advanced, 47
intermediate and 28 novice swimmers, of whom 40, 30 and 10 respectively practise four times a
week. A member chosen at random is novice with probability 14/75, practises four times a week with
probability 8/15, is advanced and practises four times a week with probability 4/15, cannot be both
advanced and intermediate, and "novice" and "four times a week" are not independent:
`P(novice and 4x) = 1/15 ≠ P(novice) P(4x) = 112/1125`. -/
@[kb "openstaxintrostats2e" "Example 3.16, p. 193"]
theorem example_3_16_swim_team :
    let P : Measure (Fin 3 × Fin 2) := tableMeasure swimTeamCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 2}).toReal = 14 / 75 ∧ (P {ω | (ω.2 : ℕ) = 0}).toReal = 8 / 15 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal = 4 / 15 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.1 : ℕ) = 1}).toReal = 0 ∧
      (P {ω | (ω.1 : ℕ) = 2 ∧ (ω.2 : ℕ) = 0}).toReal = 1 / 15 ∧
      (P {ω | (ω.1 : ℕ) = 2 ∧ (ω.2 : ℕ) = 0}).toReal ≠
        (P {ω | (ω.1 : ℕ) = 2}).toReal * (P {ω | (ω.2 : ℕ) = 0}).toReal := by
  intro P
  have hD : ∑ ω, swimTeamCounts ω = 150 := by decide
  have h1 : (P {ω | (ω.1 : ℕ) = 2}).toReal = 14 / 75 := by
    exact (tprob _ _ (fun ω : Fin 3 × Fin 2 => (ω.1 : ℕ) = 2) 28 150 hD (by decide)).trans (by norm_num)
  have h2 : (P {ω | (ω.2 : ℕ) = 0}).toReal = 8 / 15 := by
    exact (tprob _ _ (fun ω : Fin 3 × Fin 2 => (ω.2 : ℕ) = 0) 80 150 hD (by decide)).trans (by norm_num)
  have h3 : (P {ω | (ω.1 : ℕ) = 2 ∧ (ω.2 : ℕ) = 0}).toReal = 1 / 15 := by
    exact (tprob _ _ (fun ω : Fin 3 × Fin 2 => (ω.1 : ℕ) = 2 ∧ (ω.2 : ℕ) = 0) 10 150 hD
      (by decide)).trans (by norm_num)
  refine ⟨h1, h2, ?_, ?_, h3, ?_⟩
  · exact (tprob _ _ (fun ω : Fin 3 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 40 150 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 3 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.1 : ℕ) = 1) 0 150 hD
      (by decide)).trans (by norm_num)
  · rw [h1, h2, h3]; norm_num

/-- Cell counts of the cell-phone table of Example 3.20: rows uses a cell phone, does not; columns
speeding violation, none. -/
def speedingCounts : Fin 2 × Fin 2 → ℕ := fun ω => ![![25, 280], ![45, 405]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Example 3.20. Among 755 drivers (25 phone users with a
violation, 280 phone users without, 45 non-users with, 405 non-users without): `P(phone user) =
61/151`, `P(no violation) = 137/151`, `P(no violation and phone user) = 56/151`,
`P(phone user or no violation) = 142/151`, `P(phone user | violation) = 5/14` and
`P(no violation | not a phone user) = 9/10`. -/
@[kb "openstaxintrostats2e" "Example 3.20, p. 195"]
theorem example_3_20_cell_phone_speeding_table :
    let P : Measure (Fin 2 × Fin 2) := tableMeasure speedingCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0}).toReal = 61 / 151 ∧ (P {ω | (ω.2 : ℕ) = 1}).toReal = 137 / 151 ∧
      (P {ω | (ω.2 : ℕ) = 1 ∧ (ω.1 : ℕ) = 0}).toReal = 56 / 151 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 1}).toReal = 142 / 151 ∧
      (P[{ω | (ω.1 : ℕ) = 0} | {ω | (ω.2 : ℕ) = 0}]).toReal = 5 / 14 ∧
      (P[{ω | (ω.2 : ℕ) = 1} | {ω | (ω.1 : ℕ) = 1}]).toReal = 9 / 10 := by
  intro P
  have hD : ∑ ω, speedingCounts ω = 755 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 305 755 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 1) 685 755 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 1 ∧ (ω.1 : ℕ) = 0) 280 755 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 1) 710 755 hD
      (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 0) (fun ω => (ω.1 : ℕ) = 0) 25 70
      (by decide) (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1) (fun ω => (ω.2 : ℕ) = 1) 405 450
      (by decide) (by decide)).trans (by norm_num)

/-- Cell counts of the completed hiking table of Example 3.21: rows women, men; columns
coastline, lakes and streams, mountain peaks. -/
def hikingCounts : Fin 2 × Fin 3 → ℕ := fun ω => ![![18, 16, 11], ![16, 25, 14]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Example 3.21. Among 100 hikers (women 18, 16, 11 and men 16,
25, 14 for coastline, lakes and streams, peaks): `P(woman and coastline) = 0.18` but
`P(woman) P(coastline) = 0.45 · 0.34 = 0.153`, so these events are not independent;
`P(man | lakes and streams) = 25/41`; `P(woman) = 0.45`, `P(peaks) = 0.25`,
`P(woman and peaks) = 0.11` and `P(woman or peaks) = 0.59`. -/
@[kb "openstaxintrostats2e" "Example 3.21, p. 197"]
theorem example_3_21_hiking_table :
    let P : Measure (Fin 2 × Fin 3) := tableMeasure hikingCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal = 0.18 ∧
      (P {ω | (ω.1 : ℕ) = 0}).toReal * (P {ω | (ω.2 : ℕ) = 0}).toReal = 0.153 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal ≠
        (P {ω | (ω.1 : ℕ) = 0}).toReal * (P {ω | (ω.2 : ℕ) = 0}).toReal ∧
      (P[{ω | (ω.1 : ℕ) = 1} | {ω | (ω.2 : ℕ) = 1}]).toReal = 25 / 41 ∧
      (P {ω | (ω.1 : ℕ) = 0}).toReal = 0.45 ∧ (P {ω | (ω.2 : ℕ) = 2}).toReal = 0.25 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 2}).toReal = 0.11 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 2}).toReal = 0.59 := by
  intro P
  have hD : ∑ ω, hikingCounts ω = 100 := by decide
  have h1 : (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal = 0.18 := by
    exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 18 100 hD
      (by decide)).trans (by norm_num)
  have h2 : (P {ω | (ω.1 : ℕ) = 0}).toReal = 0.45 := by
    exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 0) 45 100 hD (by decide)).trans (by norm_num)
  have h3 : (P {ω | (ω.2 : ℕ) = 0}).toReal = 0.34 := by
    exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.2 : ℕ) = 0) 34 100 hD (by decide)).trans (by norm_num)
  refine ⟨h1, by rw [h2, h3]; norm_num, by rw [h1, h2, h3]; norm_num, ?_, h2, ?_, ?_, ?_⟩
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.2 : ℕ) = 1) (fun ω => (ω.1 : ℕ) = 1) 25 41
      (by decide) (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.2 : ℕ) = 2) 25 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 2) 11 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 2) 59 100 hD
      (by decide)).trans (by norm_num)

/-- Crime rates of Example 3.23, in tenths per 100 000 inhabitants: rows years 1 to 4; columns
robbery, burglary, vandalism, vehicle. -/
def crimeCounts : Fin 4 × Fin 4 → ℕ := fun ω =>
  ![![1457, 7321, 297, 3147], ![1331, 7177, 291, 2592], ![1193, 7010, 277, 2391],
    ![1137, 7022, 268, 2296]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Example 3.23. Treating the crime-index table (total 4520.7
per 100 000, weights in tenths) as a probability table: `P(year 2 and robbery) = 1331/45207`
(about 0.0294), `P(year 3 and burglary) = 7010/45207` (about 0.1551),
`P(year 3 or burglary) = 32391/45207` (about 0.7165), `P(year 4 | vandalism) = 268/1133` (about
0.2365) and `P(vehicle | year 1) = 3147/12222` (about 0.2575). -/
@[kb "openstaxintrostats2e" "Example 3.23, p. 200"]
theorem example_3_23_crime_rates_table :
    let P : Measure (Fin 4 × Fin 4) := tableMeasure crimeCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 0}).toReal = 1331 / 45207 ∧
      (P {ω | (ω.1 : ℕ) = 2 ∧ (ω.2 : ℕ) = 1}).toReal = 7010 / 45207 ∧
      (P {ω | (ω.1 : ℕ) = 2 ∨ (ω.2 : ℕ) = 1}).toReal = 32391 / 45207 ∧
      (P[{ω | (ω.1 : ℕ) = 3} | {ω | (ω.2 : ℕ) = 2}]).toReal = 268 / 1133 ∧
      (P[{ω | (ω.2 : ℕ) = 3} | {ω | (ω.1 : ℕ) = 0}]).toReal = 3147 / 12222 := by
  intro P
  have hD : ∑ ω, crimeCounts ω = 45207 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact tprob _ _ (fun ω : Fin 4 × Fin 4 => (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 0) 1331 45207 hD
      (by decide)
  · exact tprob _ _ (fun ω : Fin 4 × Fin 4 => (ω.1 : ℕ) = 2 ∧ (ω.2 : ℕ) = 1) 7010 45207 hD
      (by decide)
  · exact tprob _ _ (fun ω : Fin 4 × Fin 4 => (ω.1 : ℕ) = 2 ∨ (ω.2 : ℕ) = 1) 32391 45207 hD
      (by decide)
  · exact tcprob _ _ (fun ω : Fin 4 × Fin 4 => (ω.2 : ℕ) = 2) (fun ω => (ω.1 : ℕ) = 3) 268 1133
      (by decide) (by decide)
  · exact tcprob _ _ (fun ω : Fin 4 × Fin 4 => (ω.1 : ℕ) = 0) (fun ω => (ω.2 : ℕ) = 3) 3147 12222
      (by decide) (by decide)

/-- OpenStax Introductory Statistics 2e Example 3.9. Math and science classes: from `P(G) = 0.6`,
`P(H) = 0.5` and `P(G and H) = 0.3` one gets `P(G | H) = 0.6 = P(G)`, and `G`, `H` are
independent. -/
@[kb "openstaxintrostats2e" "Example 3.9, p. 188"]
theorem example_3_9_math_and_science_independent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G H : Set Ω} (hG : MeasurableSet G) (hH : MeasurableSet H)
    (pG : P.real G = 0.6) (pH : P.real H = 0.5) (pGH : P.real (G ∩ H) = 0.3) :
    (P[G | H]).toReal = 0.6 ∧ IndepSet G H P := by
  refine ⟨?_, indep_of_real hG hH (by rw [pG, pH, pGH]; norm_num)⟩
  rw [cond_toReal hH, Set.inter_comm, pGH, pH]; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.10. English and speech classes with `P(C) = 0.75`,
`P(D) = 0.3` and `P(C and D) = 0.225`: `C` and `D` are independent, not mutually exclusive
(`P(C and D) ≠ 0`), and `P(D | C) = 0.3`. -/
@[kb "openstaxintrostats2e" "Example 3.10, p. 189"]
theorem example_3_10_english_and_speech {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C D : Set Ω} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (pC : P.real C = 0.75) (pD : P.real D = 0.3) (pCD : P.real (C ∩ D) = 0.225) :
    IndepSet C D P ∧ P.real (C ∩ D) ≠ 0 ∧ (P[D | C]).toReal = 0.3 := by
  refine ⟨indep_of_real hC hD (by rw [pC, pD, pCD]; norm_num), by rw [pCD]; norm_num, ?_⟩
  rw [cond_toReal hC, pCD, pC]; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.12. Being a woman (`W`, probability 0.6) and
having long hair (`L`, probability 0.5), with `P(W and L) = 0.45`, are not independent because
`0.45 ≠ 0.6 · 0.5 = 0.30`; equivalently `P(L | W) = 0.75 ≠ P(L)`. -/
@[kb "openstaxintrostats2e" "Example 3.12, p. 190"]
theorem example_3_12_women_and_long_hair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W L : Set Ω} (hW : MeasurableSet W) (hL : MeasurableSet L)
    (pW : P.real W = 0.6) (pL : P.real L = 0.5) (pWL : P.real (W ∩ L) = 0.45) :
    ¬ IndepSet W L P ∧ (P[L | W]).toReal = 0.75 := by
  refine ⟨fun hi => ?_, ?_⟩
  · have := indep_real hW hL hi
    rw [pW, pL, pWL] at this; norm_num at this
  · rw [cond_toReal hW, pWL, pW]; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.15. Carlos scores with probability 0.65 on each of
two attempts and makes the second given the first with probability 0.9: both goals have probability
0.585, at least one has probability 0.715, and the attempts are neither independent
(`0.585 ≠ 0.65²`) nor mutually exclusive. -/
@[kb "openstaxintrostats2e" "Example 3.15, p. 192"]
theorem example_3_15_carlos_goals {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (pA : P.real A = 0.65) (pB : P.real B = 0.65) (pBA : (P[B | A]).toReal = 0.9) :
    P.real (A ∩ B) = 0.585 ∧ P.real (A ∪ B) = 0.715 ∧ ¬ IndepSet A B P ∧ P.real (A ∩ B) ≠ 0 := by
  have h1 : P.real (A ∩ B) = 0.585 := by
    rw [cond_toReal hA, pA] at pBA
    have : P.real (A ∩ B) = 0.9 * 0.65 := by
      field_simp at pBA; linarith
    rw [this]; norm_num
  have h2 := measureReal_union_add_inter (μ := P) (s := A) (t := B) hB
  refine ⟨h1, by rw [h1, pA, pB] at h2; linarith, fun hi => ?_, by rw [h1]; norm_num⟩
  have := indep_real hA hB hi
  rw [pA, pB, h1] at this; norm_num at this

/-- OpenStax Introductory Statistics 2e Example 3.17. Felicity takes a math class with probability
0.2, a speech class with probability 0.65, and math given speech with probability 0.25: math and
speech together have probability 0.1625, math or speech 0.6875, and the two are neither independent
nor mutually exclusive. -/
@[kb "openstaxintrostats2e" "Example 3.17, p. 194"]
theorem example_3_17_math_and_speech {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {M S : Set Ω} (hM : MeasurableSet M) (hS : MeasurableSet S)
    (pM : P.real M = 0.2) (pS : P.real S = 0.65) (pMS : (P[M | S]).toReal = 0.25) :
    P.real (M ∩ S) = 0.1625 ∧ P.real (M ∪ S) = 0.6875 ∧ ¬ IndepSet M S P ∧
      P.real (M ∩ S) ≠ 0 := by
  have h1 : P.real (M ∩ S) = 0.1625 := by
    rw [cond_toReal hS, pS] at pMS
    rw [Set.inter_comm] at pMS
    have : P.real (M ∩ S) = 0.25 * 0.65 := by
      field_simp at pMS; linarith
    rw [this]; norm_num
  have h2 := measureReal_union_add_inter (μ := P) (s := M) (t := S) hS
  refine ⟨h1, by rw [h1, pM, pS] at h2; linarith, fun hi => ?_, by rw [h1]; norm_num⟩
  have := indep_real hM hS hi
  rw [pM, pS, h1] at this; norm_num at this

/-- OpenStax Introductory Statistics 2e Examples 3.18 and 3.19. A woman develops breast cancer (`B`)
with probability 0.143, tests negative (`N`) with probability 0.85, and a woman with cancer tests
negative with probability 0.02. Then `P(B and N) = 0.00286`, `P(B or N) = 0.99014`, the events are
not independent, `P(B and positive) = 0.14014`, `P(B') = 0.857` and `P(positive) = 0.15`. -/
@[kb "openstaxintrostats2e" "Example 3.18, p. 194"]
theorem example_3_18_breast_cancer_test {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B N : Set Ω} (hB : MeasurableSet B) (hN : MeasurableSet N)
    (pB : P.real B = 0.143) (pN : P.real N = 0.85) (pNB : (P[N | B]).toReal = 0.02) :
    P.real (B ∩ N) = 0.00286 ∧ P.real (B ∪ N) = 0.99014 ∧ ¬ IndepSet B N P ∧
      P.real (B ∩ Nᶜ) = 0.14014 ∧ P.real Bᶜ = 0.857 ∧ P.real Nᶜ = 0.15 := by
  have h1 : P.real (B ∩ N) = 0.00286 := by
    rw [cond_toReal hB, pB] at pNB
    have : P.real (B ∩ N) = 0.02 * 0.143 := by
      field_simp at pNB; linarith
    rw [this]; norm_num
  have h2 := measureReal_union_add_inter (μ := P) (s := B) (t := N) hN
  have h3 := measureReal_inter_add_sdiff (μ := P) (s := B) (t := N) hN
  have h4 := probReal_add_probReal_compl (μ := P) hB
  have h5 := probReal_add_probReal_compl (μ := P) hN
  refine ⟨h1, by rw [h1, pB, pN] at h2; linarith, fun hi => ?_, ?_, by linarith, by linarith⟩
  · have := indep_real hB hN hi
    rw [pB, pN, h1] at this; norm_num at this
  · rw [Set.sdiff_eq] at h3
    linarith

/-- OpenStax Introductory Statistics 2e Example 3.29. Forty percent of students belong to a club
(`C`), 50% work part time (`PT`) and 5% do both: the chance of belonging to a club given part-time
work is 0.1, and the chance of either is 0.85. -/
@[kb "openstaxintrostats2e" "Example 3.29, p. 206"]
theorem example_3_29_club_and_part_time_work {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C T : Set Ω} (hT : MeasurableSet T)
    (pC : P.real C = 0.40) (pT : P.real T = 0.50) (pCT : P.real (C ∩ T) = 0.05) :
    (P[C | T]).toReal = 0.1 ∧ P.real (C ∪ T) = 0.85 := by
  refine ⟨?_, ?_⟩
  · rw [cond_toReal hT, Set.inter_comm, pCT, pT]; norm_num
  · have h2 := measureReal_union_add_inter (μ := P) (s := C) (t := T) hT
    rw [pC, pT, pCT] at h2; linarith

end UndergradKB.Statistics.Course.ExamplesC3
