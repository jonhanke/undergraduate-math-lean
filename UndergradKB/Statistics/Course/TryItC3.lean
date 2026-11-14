import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Prime.Defs
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Rules
import UndergradKB.Statistics.Course.ExamplesC3

/-!
# "Try It" exercises, chapter 3 (OpenStax *Introductory Statistics 2e*): probability topics

Equally likely outcomes are modelled by `ProbabilityTheory.uniformOn Set.univ` on a finite type;
contingency tables by the probability mass function with weights equal to the cell counts; exercises
that only give probabilities are stated for an arbitrary probability measure. All probabilities are
real numbers equal to exact rationals.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Statistics.Course.TryItC3

open UndergradKB.Statistics.Course.ExamplesC3 (TwoWithoutReplacement)

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

/-- Equally likely outcomes: favourable over total. -/
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

private lemma wprob_card (n : Ω → ℕ) (D : ℕ) (h : ∑ ω, n ω = D) (h0 : D ≠ 0) (p : Ω → Prop)
    [DecidablePred p] (k : ℕ) (hk : ∑ ω ∈ Finset.univ.filter p, n ω = k) :
    ((natPMF n D h h0).toMeasure {ω | p ω}).toReal = (k : ℝ) / D := by
  have := natPMF_real n D h h0 (Finset.univ.filter p)
  rw [coe_filter_univ] at this
  rw [this, ← hk]
  push_cast
  rfl

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

/-- The probability measure of a contingency table. -/
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

/-- Probability of the difference `A \ B` in terms of the intersection. -/
private lemma real_inter_compl (hB : MeasurableSet B) :
    P.real (A ∩ Bᶜ) = P.real A - P.real (A ∩ B) := by
  have h3 := measureReal_inter_add_sdiff (μ := P) (s := A) (t := B) hB
  rw [Set.sdiff_eq] at h3
  linarith

end Abstract

/-! ### Sections 3.1 to 3.2 -/

/-- OpenStax Introductory Statistics 2e Try It 3.1. Ordered pairs `(i + 1, j + 1)` with first entry
1 to 3 and second 1 to 4 (12 equally likely outcomes); `A` = the sum is even, `B` = the first
number is prime. `P(A) = 1/2`, `P(B) = 2/3`, `P(A and B) = 1/3`, `P(A or B) = 5/6`, `P(B') = 1/3`,
`P(A) + P(A') = 1`, `P(A | B) = 1/2` and `P(B | A) = 2/3` (the two conditional probabilities
differ). -/
@[kb "openstaxintrostats2e" "Try It 3.1, p. 182"]
theorem tryit_3_1_pairs_sum_even_first_prime :
    let P : Measure (Fin 3 × Fin 4) := uniformOn Set.univ
    let A : Set (Fin 3 × Fin 4) := {ω | ((ω.1 : ℕ) + 1 + ((ω.2 : ℕ) + 1)) % 2 = 0}
    let B : Set (Fin 3 × Fin 4) := {ω | Nat.Prime ((ω.1 : ℕ) + 1)}
    (P A).toReal = 1 / 2 ∧ (P B).toReal = 2 / 3 ∧ (P (A ∩ B)).toReal = 1 / 3 ∧
      (P (A ∪ B)).toReal = 5 / 6 ∧ (P Bᶜ).toReal = 1 / 3 ∧
      (P A).toReal + (P Aᶜ).toReal = 1 ∧
      (P[A | B]).toReal = 1 / 2 ∧ (P[B | A]).toReal = 2 / 3 ∧
      (P[A | B]).toReal ≠ (P[B | A]).toReal := by
  intro P A B
  have hc : Fintype.card (Fin 3 × Fin 4) = 12 := by simp
  have h1 : (P A).toReal = 1 / 2 :=
    (prob_card (fun ω : Fin 3 × Fin 4 => ((ω.1 : ℕ) + 1 + ((ω.2 : ℕ) + 1)) % 2 = 0) 6 12 hc
      (by decide)).trans (by norm_num)
  have h2 : (P Aᶜ).toReal = 1 / 2 :=
    (prob_card (fun ω : Fin 3 × Fin 4 => ¬ (((ω.1 : ℕ) + 1 + ((ω.2 : ℕ) + 1)) % 2 = 0)) 6 12 hc
      (by decide)).trans (by norm_num)
  have h3 : (P[A | B]).toReal = 1 / 2 :=
    (cprob_card (fun ω : Fin 3 × Fin 4 => Nat.Prime ((ω.1 : ℕ) + 1))
      (fun ω => ((ω.1 : ℕ) + 1 + ((ω.2 : ℕ) + 1)) % 2 = 0) 4 8 (by decide) (by decide)).trans
      (by norm_num)
  have h4 : (P[B | A]).toReal = 2 / 3 :=
    (cprob_card (fun ω : Fin 3 × Fin 4 => ((ω.1 : ℕ) + 1 + ((ω.2 : ℕ) + 1)) % 2 = 0)
      (fun ω => Nat.Prime ((ω.1 : ℕ) + 1)) 4 6 (by decide) (by decide)).trans (by norm_num)
  refine ⟨h1, ?_, ?_, ?_, ?_, by rw [h1, h2]; norm_num, h3, h4, by rw [h3, h4]; norm_num⟩
  · exact (prob_card (fun ω : Fin 3 × Fin 4 => Nat.Prime ((ω.1 : ℕ) + 1)) 8 12 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 3 × Fin 4 => ((ω.1 : ℕ) + 1 + ((ω.2 : ℕ) + 1)) % 2 = 0 ∧
      Nat.Prime ((ω.1 : ℕ) + 1)) 4 12 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 3 × Fin 4 => ((ω.1 : ℕ) + 1 + ((ω.2 : ℕ) + 1)) % 2 = 0 ∨
      Nat.Prime ((ω.1 : ℕ) + 1)) 10 12 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 3 × Fin 4 => ¬ Nat.Prime ((ω.1 : ℕ) + 1)) 4 12 hc
      (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.2. A number from 1 to 10 chosen at random
(outcome `i + 1`, `i : Fin 10`): `P(F) = P(outcome is 5) = 1/10`, `P(A) = P(more than 6) = 2/5`,
`P(B) = P(odd) = 1/2`, `P(B') = 1/2`, `P(A | B) = 2/5`, `P(B | A) = 1/2`, `P(A or B) = 7/10`,
`P(A' or B) = 4/5` and `P(composite) = 1/2`. -/
@[kb "openstaxintrostats2e" "Try It 3.2, p. 183"]
theorem tryit_3_2_number_one_to_ten :
    let P : Measure (Fin 10) := uniformOn Set.univ
    let A : Set (Fin 10) := {i | 6 < (i : ℕ) + 1}
    let B : Set (Fin 10) := {i | ((i : ℕ) + 1) % 2 = 1}
    (P {i | (i : ℕ) + 1 = 5}).toReal = 1 / 10 ∧ (P A).toReal = 2 / 5 ∧ (P B).toReal = 1 / 2 ∧
      (P Bᶜ).toReal = 1 / 2 ∧ (P[A | B]).toReal = 2 / 5 ∧ (P[B | A]).toReal = 1 / 2 ∧
      (P (A ∪ B)).toReal = 7 / 10 ∧ (P (Aᶜ ∪ B)).toReal = 4 / 5 ∧
      (P {i | 1 < (i : ℕ) + 1 ∧ ¬ Nat.Prime ((i : ℕ) + 1)}).toReal = 1 / 2 := by
  intro P A B
  have hc : Fintype.card (Fin 10) = 10 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun i : Fin 10 => (i : ℕ) + 1 = 5) 1 10 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 10 => 6 < (i : ℕ) + 1) 4 10 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 10 => ((i : ℕ) + 1) % 2 = 1) 5 10 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 10 => ¬ (((i : ℕ) + 1) % 2 = 1)) 5 10 hc (by decide)).trans
      (by norm_num)
  · exact (cprob_card (fun i : Fin 10 => ((i : ℕ) + 1) % 2 = 1) (fun i => 6 < (i : ℕ) + 1) 2 5
      (by decide) (by decide)).trans (by norm_num)
  · exact (cprob_card (fun i : Fin 10 => 6 < (i : ℕ) + 1) (fun i => ((i : ℕ) + 1) % 2 = 1) 2 4
      (by decide) (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 10 => 6 < (i : ℕ) + 1 ∨ ((i : ℕ) + 1) % 2 = 1) 7 10 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 10 => ¬ (6 < (i : ℕ) + 1) ∨ ((i : ℕ) + 1) % 2 = 1) 8 10 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 10 => 1 < (i : ℕ) + 1 ∧ ¬ Nat.Prime ((i : ℕ) + 1)) 5 10 hc
      (by decide)).trans (by norm_num)

/-- Cell counts of the tea-or-coffee table of Try It 3.3: rows men, women; columns tea, coffee. -/
def teaCoffeeCounts : Fin 2 × Fin 2 → ℕ := fun ω => ![![22, 26], ![16, 36]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Try It 3.3. A sample of 100 people (men: 22 tea, 26 coffee;
women: 16 tea, 36 coffee), `M`, `W` men and women, `T`, `C` tea and coffee: `P(M) = 12/25`,
`P(W) = 13/25`, `P(T) = 19/50`, `P(C) = 31/50`, `P(M and T) = 11/50`, `P(W and C) = 9/25`,
`P(M or W) = 1`, `P(M or T) = 16/25`, `P(W or C) = 39/50`, `P(M') = 13/25`, `P(T | M) = 11/24`,
`P(W | C) = 18/31` and `P(C | W) = 9/13`. -/
@[kb "openstaxintrostats2e" "Try It 3.3, p. 184"]
theorem tryit_3_3_tea_coffee_table :
    let P : Measure (Fin 2 × Fin 2) := tableMeasure teaCoffeeCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0}).toReal = 12 / 25 ∧ (P {ω | (ω.1 : ℕ) = 1}).toReal = 13 / 25 ∧
      (P {ω | (ω.2 : ℕ) = 0}).toReal = 19 / 50 ∧ (P {ω | (ω.2 : ℕ) = 1}).toReal = 31 / 50 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal = 11 / 50 ∧
      (P {ω | (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1}).toReal = 9 / 25 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∨ (ω.1 : ℕ) = 1}).toReal = 1 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 0}).toReal = 16 / 25 ∧
      (P {ω | (ω.1 : ℕ) = 1 ∨ (ω.2 : ℕ) = 1}).toReal = 39 / 50 ∧
      (P {ω | ¬ ((ω.1 : ℕ) = 0)}).toReal = 13 / 25 ∧
      (P[{ω | (ω.2 : ℕ) = 0} | {ω | (ω.1 : ℕ) = 0}]).toReal = 11 / 24 ∧
      (P[{ω | (ω.1 : ℕ) = 1} | {ω | (ω.2 : ℕ) = 1}]).toReal = 18 / 31 ∧
      (P[{ω | (ω.2 : ℕ) = 1} | {ω | (ω.1 : ℕ) = 1}]).toReal = 9 / 13 := by
  intro P
  have hD : ∑ ω, teaCoffeeCounts ω = 100 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 48 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1) 52 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 0) 38 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 1) 62 100 hD (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 22 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1) 36 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∨ (ω.1 : ℕ) = 1) 100 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 0) 64 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1 ∨ (ω.2 : ℕ) = 1) 78 100 hD
      (by decide)).trans (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => ¬ ((ω.1 : ℕ) = 0)) 52 100 hD (by decide)).trans
      (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) (fun ω => (ω.2 : ℕ) = 0) 22 48
      (by decide) (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 1) (fun ω => (ω.1 : ℕ) = 1) 36 62
      (by decide) (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 1) (fun ω => (ω.2 : ℕ) = 1) 36 52
      (by decide) (by decide)).trans (by norm_num)

/-- A card of the 52-card deck as (suit, rank): suit 0 spades, 1 hearts, 2 diamonds, 3 clubs; rank
0 the ace (the card "1"), ranks 1 to 9 the numbers 2 to 10, then 10 jack, 11 queen, 12 king. -/
abbrev Card := Fin 4 × Fin 13

/-- OpenStax Introductory Statistics 2e Try It 3.4. A sample of three cards that repeats a card
(queen of spades twice) cannot have been drawn without replacement, so it was drawn with
replacement; a sample of three distinct cards (queen of spades, king of hearts, jack of spades)
can come from either scheme (without replacement the list has no repeated entry, with replacement
every list of cards of the deck is possible). -/
@[kb "openstaxintrostats2e" "Try It 3.4, p. 185"]
theorem tryit_3_4_cards_with_or_without_replacement :
    let a : List Card := [(0, 11), (1, 12), (0, 11)]
    let b : List Card := [(0, 11), (1, 12), (0, 10)]
    ¬ a.Nodup ∧ b.Nodup ∧ (∀ c ∈ b, c ∈ (Finset.univ : Finset Card)) := by
  intro a b
  refine ⟨by decide, by decide, fun c _ => Finset.mem_univ c⟩

/-- OpenStax Introductory Statistics 2e Try It 3.5. Four cards sampled from the deck: an outcome
is possible without replacement exactly when no card is repeated, and with replacement whenever
every card is in the deck. (a) QS, 1D, 1C, QD: possible both ways; (b) KH, 7D, 6D, KH: only with
replacement; (c) QS, 7D, 6D, KS: possible both ways. -/
@[kb "openstaxintrostats2e" "Try It 3.5, p. 186"]
theorem tryit_3_5_possible_four_card_samples :
    let a : List Card := [(0, 11), (2, 0), (3, 0), (2, 11)]
    let b : List Card := [(1, 12), (2, 6), (2, 5), (1, 12)]
    let c : List Card := [(0, 11), (2, 6), (2, 5), (0, 12)]
    (a.Nodup ∧ ¬ b.Nodup ∧ c.Nodup) ∧
      ((∀ x ∈ a, x ∈ (Finset.univ : Finset Card)) ∧ (∀ x ∈ b, x ∈ (Finset.univ : Finset Card)) ∧
        ∀ x ∈ c, x ∈ (Finset.univ : Finset Card)) := by
  intro a b c
  exact ⟨⟨by decide, by decide, by decide⟩, fun x _ => Finset.mem_univ x,
    fun x _ => Finset.mem_univ x, fun x _ => Finset.mem_univ x⟩

/-- OpenStax Introductory Statistics 2e Try It 3.6. Two cards drawn with replacement from a 52-card
deck (26 black cards, ordered pairs of cards, card `i` black when `i < 26`): the probability of at
least one black card is 3/4. -/
@[kb "openstaxintrostats2e" "Try It 3.6, p. 186"]
theorem tryit_3_6_two_cards_at_least_one_black :
    let P : Measure (Fin 52 × Fin 52) := uniformOn Set.univ
    (P {ω | (ω.1 : ℕ) < 26 ∨ (ω.2 : ℕ) < 26}).toReal = 3 / 4 := by
  intro P
  have hc : Fintype.card (Fin 52 × Fin 52) = 2704 := by simp
  exact (prob_card (fun ω : Fin 52 × Fin 52 => (ω.1 : ℕ) < 26 ∨ (ω.2 : ℕ) < 26) 2028 2704 hc
    (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.7. A box has a white ball (`0`) and a red ball
(`1`), two draws with replacement: `F` = white twice has probability 1/4, `G` = two different
colours 1/2, `H` = white first 1/2. `F` and `G` are mutually exclusive (`P(F and G) = 0`), but `G`
and `H` are not (`P(G and H) = 1/4 ≠ 0`). -/
@[kb "openstaxintrostats2e" "Try It 3.7, p. 187"]
theorem tryit_3_7_white_and_red_ball :
    let P : Measure (Fin 2 × Fin 2) := uniformOn Set.univ
    let F : Set (Fin 2 × Fin 2) := {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}
    let G : Set (Fin 2 × Fin 2) := {ω | ω.1 ≠ ω.2}
    let H : Set (Fin 2 × Fin 2) := {ω | (ω.1 : ℕ) = 0}
    (P F).toReal = 1 / 4 ∧ (P G).toReal = 1 / 2 ∧ (P H).toReal = 1 / 2 ∧
      (P (F ∩ G)).toReal = 0 ∧ (P (G ∩ H)).toReal = 1 / 4 ∧ (P (G ∩ H)).toReal ≠ 0 := by
  intro P F G H
  have hc : Fintype.card (Fin 2 × Fin 2) = 4 := by simp
  have h5 : (P (G ∩ H)).toReal = 1 / 4 :=
    (prob_card (fun ω : Fin 2 × Fin 2 => ω.1 ≠ ω.2 ∧ (ω.1 : ℕ) = 0) 1 4 hc (by decide)).trans
      (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, h5, by rw [h5]; norm_num⟩
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 1 4 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => ω.1 ≠ ω.2) 2 4 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 2 4 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun ω : Fin 2 × Fin 2 => ((ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) ∧ ω.1 ≠ ω.2) 0 4 hc
      (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.8. Learning Spanish (`A`, probability 0.4) and
German (`B`, probability 0.2) with `P(A and B) = 0.08`: since `0.08 = 0.4 · 0.2` the events are
independent, and `P(A | B) = 0.4 = P(A)`. -/
@[kb "openstaxintrostats2e" "Try It 3.8, p. 188"]
theorem tryit_3_8_spanish_and_german_independent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (pA : P.real A = 0.4) (pB : P.real B = 0.2) (pAB : P.real (A ∩ B) = 0.08) :
    IndepSet A B P ∧ (P[A | B]).toReal = 0.4 := by
  refine ⟨indep_of_real hA hB (by rw [pA, pB, pAB]; norm_num), ?_⟩
  rw [cond_toReal hB, Set.inter_comm, pAB, pB]; norm_num

/-- OpenStax Introductory Statistics 2e Try It 3.9. A bag with red marbles numbered 1 to 6 and
green marbles numbered 1 to 4 (ten marbles, marble `i` is red with number `i + 1` when `i < 6` and
green with number `i - 5` otherwise); `G` = green, `O` = odd number: `P(G and O) = 1/5`. -/
@[kb "openstaxintrostats2e" "Try It 3.9, p. 188"]
theorem tryit_3_9_green_and_odd_marble :
    let P : Measure (Fin 10) := uniformOn Set.univ
    (P {i | 6 ≤ (i : ℕ) ∧ (if (i : ℕ) < 6 then (i : ℕ) + 1 else (i : ℕ) - 5) % 2 = 1}).toReal =
      1 / 5 := by
  intro P
  have hc : Fintype.card (Fin 10) = 10 := by simp
  exact (prob_card (fun i : Fin 10 => 6 ≤ (i : ℕ) ∧
    (if (i : ℕ) < 6 then (i : ℕ) + 1 else (i : ℕ) - 5) % 2 = 1) 2 10 hc (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.10. A library visitor takes a book (`B`) with
probability 0.40 and a DVD (`D`) with probability 0.30, both with probability 0.20: `P(B | D) = 2/3`,
`P(D | B) = 1/2`, the events are not independent (`0.2 ≠ 0.4 · 0.3`) and not mutually exclusive
(`P(B and D) ≠ 0`). -/
@[kb "openstaxintrostats2e" "Try It 3.10, p. 189"]
theorem tryit_3_10_book_and_dvd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B D : Set Ω} (hB : MeasurableSet B) (hD : MeasurableSet D)
    (pB : P.real B = 0.40) (pD : P.real D = 0.30) (pBD : P.real (B ∩ D) = 0.20) :
    (P[B | D]).toReal = 2 / 3 ∧ (P[D | B]).toReal = 1 / 2 ∧ ¬ IndepSet B D P ∧
      P.real (B ∩ D) ≠ 0 := by
  refine ⟨?_, ?_, fun hi => ?_, by rw [pBD]; norm_num⟩
  · rw [cond_toReal hD, Set.inter_comm, pBD, pD]; norm_num
  · rw [cond_toReal hB, pBD, pB]; norm_num
  · have := indep_real hB hD hi
    rw [pB, pD, pBD] at this; norm_num at this

/-- OpenStax Introductory Statistics 2e Try It 3.11. In an arena 70% of fans root for the home team
(so the away team `A` has probability 0.3), 25% wear blue (`B`), and 20% root for the away team and
wear blue. Then `P(B | A) = 2/3`, and the events are not independent (`0.2 ≠ 0.3 · 0.25`) and not
mutually exclusive (`P(A and B) ≠ 0`). -/
@[kb "openstaxintrostats2e" "Try It 3.11, p. 189"]
theorem tryit_3_11_away_fans_and_blue {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (pAc : P.real Aᶜ = 0.70) (pB : P.real B = 0.25) (pAB : P.real (A ∩ B) = 0.20) :
    P.real A = 0.3 ∧ (P[B | A]).toReal = 2 / 3 ∧ ¬ IndepSet A B P ∧ P.real (A ∩ B) ≠ 0 := by
  have h4 := probReal_add_probReal_compl (μ := P) hA
  have pA : P.real A = 0.3 := by rw [pAc] at h4; linarith
  refine ⟨pA, ?_, fun hi => ?_, by rw [pAB]; norm_num⟩
  · rw [cond_toReal hA, pAB, pA]; norm_num
  · have := indep_real hA hB hi
    rw [pA, pB, pAB] at this; norm_num at this

/-! ### Section 3.3 -/

/-- OpenStax Introductory Statistics 2e Try It 3.12. Mark takes the Interstate (`I`, probability
0.44) or Fifth Street (`F`, probability 0.56), never both (`P(I and F) = 0`): `P(I or F) = 1`. -/
@[kb "openstaxintrostats2e" "Try It 3.12, p. 190"]
theorem tryit_3_12_interstate_or_fifth_street {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {I F : Set Ω} (hF : MeasurableSet F)
    (pI : P.real I = 0.44) (pF : P.real F = 0.56) (pIF : P.real (I ∩ F) = 0) :
    P.real (I ∪ F) = 1 := by
  have h2 := measureReal_union_add_inter (μ := P) (s := I) (t := F) hF
  rw [pI, pF, pIF] at h2; linarith

/-- OpenStax Introductory Statistics 2e Try It 3.13. A box has a white (`0`) and a red (`1`) ball,
two draws with replacement; `T` = white twice, `F` = white first, `S` = white second:
`P(T) = 1/4`, `P(T | F) = 1/2`; `T` and `F` are not independent (`P(T and F) = 1/4 ≠ 1/8`);
`F` and `S` are not mutually exclusive (`P(F and S) = 1/4 ≠ 0`) but are independent
(`P(F and S) = P(F) P(S)`). -/
@[kb "openstaxintrostats2e" "Try It 3.13, p. 191"]
theorem tryit_3_13_white_ball_twice :
    let P : Measure (Fin 2 × Fin 2) := uniformOn Set.univ
    let T : Set (Fin 2 × Fin 2) := {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}
    let F : Set (Fin 2 × Fin 2) := {ω | (ω.1 : ℕ) = 0}
    let S : Set (Fin 2 × Fin 2) := {ω | (ω.2 : ℕ) = 0}
    (P T).toReal = 1 / 4 ∧ (P[T | F]).toReal = 1 / 2 ∧
      (P (T ∩ F)).toReal ≠ (P T).toReal * (P F).toReal ∧
      (P (F ∩ S)).toReal ≠ 0 ∧ (P (F ∩ S)).toReal = (P F).toReal * (P S).toReal := by
  intro P T F S
  have hc : Fintype.card (Fin 2 × Fin 2) = 4 := by simp
  have hT : (P T).toReal = 1 / 4 :=
    (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 1 4 hc (by decide)).trans
      (by norm_num)
  have hF : (P F).toReal = 1 / 2 :=
    (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 2 4 hc (by decide)).trans (by norm_num)
  have hS : (P S).toReal = 1 / 2 :=
    (prob_card (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 0) 2 4 hc (by decide)).trans (by norm_num)
  have hTF : (P (T ∩ F)).toReal = 1 / 4 :=
    (prob_card (fun ω : Fin 2 × Fin 2 => ((ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) ∧ (ω.1 : ℕ) = 0) 1 4 hc
      (by decide)).trans (by norm_num)
  have hFS : (P (F ∩ S)).toReal = 1 / 4 :=
    (prob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 1 4 hc (by decide)).trans
      (by norm_num)
  refine ⟨hT, ?_, by rw [hTF, hT, hF]; norm_num, by rw [hFS]; norm_num,
    by rw [hFS, hF, hS]; norm_num⟩
  exact (cprob_card (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0)
    (fun ω => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 1 2 (by decide) (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.14. Anna buys at most one of two cars `A`, `B`
(so the events are disjoint) with `P(A) = 0.25` and `P(B) = 0.65`: `P(A and B) = 0` and
`P(A or B) = 0.9`. -/
@[kb "openstaxintrostats2e" "Try It 3.14, p. 192"]
theorem tryit_3_14_anna_buys_one_car {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Set Ω} (hB : MeasurableSet B)
    (pA : P.real A = 0.25) (pB : P.real B = 0.65) (hAB : Disjoint A B) :
    P.real (A ∩ B) = 0 ∧ P.real (A ∪ B) = 0.9 := by
  have h0 : P.real (A ∩ B) = 0 := by
    rw [Set.disjoint_iff_inter_eq_empty.1 hAB]; simp
  have h2 := measureReal_union_add_inter (μ := P) (s := A) (t := B) hB
  rw [pA, pB, h0] at h2
  exact ⟨h0, by norm_num at h2 ⊢; linarith⟩

/-- OpenStax Introductory Statistics 2e Try It 3.15. Helen makes a free throw with probability 0.75
and the second given the first with probability 0.85: she makes both with probability
`0.85 · 0.75 = 0.6375`. -/
@[kb "openstaxintrostats2e" "Try It 3.15, p. 193"]
theorem tryit_3_15_helen_free_throws {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C D : Set Ω} (hC : MeasurableSet C)
    (pC : P.real C = 0.75) (pDC : (P[D | C]).toReal = 0.85) :
    P.real (C ∩ D) = 0.6375 := by
  rw [cond_toReal hC, pC] at pDC
  have : P.real (C ∩ D) = 0.85 * 0.75 := by
    field_simp at pDC; linarith
  rw [this]; norm_num

/-- Cell counts of the seniors table of Try Its 3.16 and 3.18: rows college, work, gap year;
columns plays sports, does not. -/
def seniorsCounts : Fin 3 × Fin 2 → ℕ := fun ω => ![![50, 90], ![30, 10], ![5, 15]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Try It 3.16. Of 200 seniors 140 go to college, 40 to work
and the remaining 20 take a gap year (sports players: 50, 30, 5): a senior takes a gap year with
probability 1/10. -/
@[kb "openstaxintrostats2e" "Try It 3.16, p. 193"]
theorem tryit_3_16_seniors_gap_year :
    let P : Measure (Fin 3 × Fin 2) := tableMeasure seniorsCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 2}).toReal = 1 / 10 := by
  intro P
  have hD : ∑ ω, seniorsCounts ω = 200 := by decide
  exact (tprob _ _ (fun ω : Fin 3 × Fin 2 => (ω.1 : ℕ) = 2) 20 200 hD (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.17. `P(B) = 0.40`, `P(D) = 0.30`,
`P(D | B) = 0.5`: `P(B and D) = 0.2` and `P(B or D) = 0.5`. -/
@[kb "openstaxintrostats2e" "Try It 3.17, p. 194"]
theorem tryit_3_17_book_and_dvd_given {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B D : Set Ω} (hB : MeasurableSet B) (hD : MeasurableSet D)
    (pB : P.real B = 0.40) (pD : P.real D = 0.30) (pDB : (P[D | B]).toReal = 0.5) :
    P.real (B ∩ D) = 0.2 ∧ P.real (B ∪ D) = 0.5 := by
  have h1 : P.real (B ∩ D) = 0.2 := by
    rw [cond_toReal hB, pB] at pDB
    have : P.real (B ∩ D) = 0.5 * 0.40 := by
      field_simp at pDB; linarith
    rw [this]; norm_num
  have h2 := measureReal_union_add_inter (μ := P) (s := B) (t := D) hD
  exact ⟨h1, by rw [h1, pB, pD] at h2; linarith⟩

/-- OpenStax Introductory Statistics 2e Try It 3.18. In the seniors table of Try It 3.16 a senior
goes to college and plays sports with probability 1/4. -/
@[kb "openstaxintrostats2e" "Try It 3.18, p. 195"]
theorem tryit_3_18_seniors_college_and_sports :
    let P : Measure (Fin 3 × Fin 2) := tableMeasure seniorsCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal = 1 / 4 := by
  intro P
  have hD : ∑ ω, seniorsCounts ω = 200 := by decide
  exact (tprob _ _ (fun ω : Fin 3 × Fin 2 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 50 200 hD
    (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.19. `P(B) = 0.40`, `P(D) = 0.30`,
`P(D | B) = 0.5`: `P(B') = 0.6`, `P(D and B) = 0.2`, `P(B | D) = 2/3`, `P(D and B') = 0.1` and
`P(D | B') = 1/6`. -/
@[kb "openstaxintrostats2e" "Try It 3.19, p. 195"]
theorem tryit_3_19_book_and_dvd_complement {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B D : Set Ω} (hB : MeasurableSet B) (hD : MeasurableSet D)
    (pB : P.real B = 0.40) (pD : P.real D = 0.30) (pDB : (P[D | B]).toReal = 0.5) :
    P.real Bᶜ = 0.6 ∧ P.real (D ∩ B) = 0.2 ∧ (P[B | D]).toReal = 2 / 3 ∧
      P.real (D ∩ Bᶜ) = 0.1 ∧ (P[D | Bᶜ]).toReal = 1 / 6 := by
  have h1 : P.real (B ∩ D) = 0.2 := by
    rw [cond_toReal hB, pB] at pDB
    have : P.real (B ∩ D) = 0.5 * 0.40 := by
      field_simp at pDB; linarith
    rw [this]; norm_num
  have h1' : P.real (D ∩ B) = 0.2 := by rw [Set.inter_comm]; exact h1
  have h4 := probReal_add_probReal_compl (μ := P) hB
  have pBc : P.real Bᶜ = 0.6 := by rw [pB] at h4; linarith
  have h5 : P.real (D ∩ Bᶜ) = 0.1 := by
    rw [real_inter_compl hB, h1', pD]; norm_num
  refine ⟨pBc, h1', ?_, h5, ?_⟩
  · rw [cond_toReal hD, h1', pD]; norm_num
  · rw [cond_toReal hB.compl, Set.inter_comm, h5, pBc]; norm_num

/-! ### Section 3.4 -/

/-- Cell counts of the stretching table of Try It 3.20: rows stretches, does not stretch; columns
injury in the last year, no injury. -/
def stretchingCounts : Fin 2 × Fin 2 → ℕ := fun ω => ![![55, 295], ![231, 219]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Try It 3.20. Among 800 athletes (stretch: 55 injured, 295
not; no stretching: 231 injured, 219 not), an athlete stretches with probability 7/16, and the
probability of stretching given no injury is 295/514. -/
@[kb "openstaxintrostats2e" "Try It 3.20, p. 196"]
theorem tryit_3_20_stretching_table :
    let P : Measure (Fin 2 × Fin 2) := tableMeasure stretchingCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0}).toReal = 7 / 16 ∧
      (P[{ω | (ω.1 : ℕ) = 0} | {ω | (ω.2 : ℕ) = 1}]).toReal = 295 / 514 := by
  intro P
  have hD : ∑ ω, stretchingCounts ω = 800 := by decide
  refine ⟨?_, ?_⟩
  · exact (tprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.1 : ℕ) = 0) 350 800 hD (by decide)).trans
      (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 2 × Fin 2 => (ω.2 : ℕ) = 1) (fun ω => (ω.1 : ℕ) = 0) 295 514
      (by decide) (by decide)).trans (by norm_num)

/-- Cell counts of the cyclists table of Try It 3.21: rows younger, older; columns lake path,
hilly path, wooded path. -/
def cyclistsCounts : Fin 2 × Fin 3 → ℕ := fun ω => ![![45, 38, 27], ![26, 52, 12]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Try It 3.21. Among 200 cyclists (younger 45, 38, 27; older
26, 52, 12 for the lake, hilly, wooded path), an older cyclist prefers the hilly path with
probability 26/45; "older" and "hilly path" are not independent, since
`P(O and H) = 13/50 ≠ P(O) P(H) = 9/20 · 9/20 = 81/400`. -/
@[kb "openstaxintrostats2e" "Try It 3.21, p. 198"]
theorem tryit_3_21_cyclists_table :
    let P : Measure (Fin 2 × Fin 3) := tableMeasure cyclistsCounts (by decide)
    (P[{ω | (ω.2 : ℕ) = 1} | {ω | (ω.1 : ℕ) = 1}]).toReal = 26 / 45 ∧
      (P {ω | (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1}).toReal = 13 / 50 ∧
      (P {ω | (ω.1 : ℕ) = 1}).toReal * (P {ω | (ω.2 : ℕ) = 1}).toReal = 81 / 400 ∧
      (P {ω | (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1}).toReal ≠
        (P {ω | (ω.1 : ℕ) = 1}).toReal * (P {ω | (ω.2 : ℕ) = 1}).toReal := by
  intro P
  have hD : ∑ ω, cyclistsCounts ω = 200 := by decide
  have h1 : (P {ω | (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1}).toReal = 13 / 50 :=
    (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 1) 52 200 hD
      (by decide)).trans (by norm_num)
  have h2 : (P {ω | (ω.1 : ℕ) = 1}).toReal = 9 / 20 :=
    (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 1) 90 200 hD (by decide)).trans (by norm_num)
  have h3 : (P {ω | (ω.2 : ℕ) = 1}).toReal = 9 / 20 :=
    (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.2 : ℕ) = 1) 90 200 hD (by decide)).trans (by norm_num)
  refine ⟨?_, h1, by rw [h2, h3]; norm_num, by rw [h1, h2, h3]; norm_num⟩
  exact (tcprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 1) (fun ω => (ω.2 : ℕ) = 1) 52 90
    (by decide) (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.22. Anna buys at most one of two cars `A`, `B`
(so the events are disjoint) with `P(A) = 0.25` and `P(B) = 0.65` (the book repeats Try It 3.14):
`P(A and B) = 0` and `P(A or B) = 0.9`. -/
@[kb "openstaxintrostats2e" "Try It 3.22, p. 199"]
theorem tryit_3_22_anna_buys_one_car_again {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Set Ω} (hB : MeasurableSet B)
    (pA : P.real A = 0.25) (pB : P.real B = 0.65) (hAB : Disjoint A B) :
    P.real (A ∩ B) = 0 ∧ P.real (A ∪ B) = 0.9 :=
  tryit_3_14_anna_buys_one_car hB pA pB hAB

/-- Cell counts of the weight-and-height table of Try It 3.23: rows overweight, typical weight,
underweight; columns tall, medium, short. -/
def weightHeightCounts : Fin 3 × Fin 3 → ℕ := fun ω =>
  ![![18, 28, 14], ![20, 51, 28], ![12, 25, 9]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Try It 3.23, parts (a) to (e). The row totals are 60, 99,
46, the column totals 50, 104, 51, the grand total 205; a person is tall with probability 10/41,
overweight and tall with probability 18/205, tall given overweight 3/10, and overweight given tall
9/25. -/
@[kb "openstaxintrostats2e" "Try It 3.23, p. 200"]
theorem tryit_3_23_weight_height_table :
    let P : Measure (Fin 3 × Fin 3) := tableMeasure weightHeightCounts (by decide)
    ((∑ j, weightHeightCounts (0, j)) = 60 ∧ (∑ j, weightHeightCounts (1, j)) = 99 ∧
      (∑ j, weightHeightCounts (2, j)) = 46 ∧ (∑ i, weightHeightCounts (i, 0)) = 50 ∧
      (∑ i, weightHeightCounts (i, 1)) = 104 ∧ (∑ i, weightHeightCounts (i, 2)) = 51 ∧
      (∑ ω, weightHeightCounts ω) = 205) ∧
    (P {ω | (ω.2 : ℕ) = 0}).toReal = 10 / 41 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0}).toReal = 18 / 205 ∧
      (P[{ω | (ω.2 : ℕ) = 0} | {ω | (ω.1 : ℕ) = 0}]).toReal = 3 / 10 ∧
      (P[{ω | (ω.1 : ℕ) = 0} | {ω | (ω.2 : ℕ) = 0}]).toReal = 9 / 25 := by
  intro P
  have hD : ∑ ω, weightHeightCounts ω = 205 := by decide
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, hD⟩, ?_, ?_, ?_, ?_⟩
  · exact (tprob _ _ (fun ω : Fin 3 × Fin 3 => (ω.2 : ℕ) = 0) 50 205 hD (by decide)).trans
      (by norm_num)
  · exact (tprob _ _ (fun ω : Fin 3 × Fin 3 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 0) 18 205 hD
      (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 3 × Fin 3 => (ω.1 : ℕ) = 0) (fun ω => (ω.2 : ℕ) = 0) 18 60
      (by decide) (by decide)).trans (by norm_num)
  · exact (tcprob _ _ (fun ω : Fin 3 × Fin 3 => (ω.2 : ℕ) = 0) (fun ω => (ω.1 : ℕ) = 0) 18 50
      (by decide) (by decide)).trans (by norm_num)

/-! ### Section 3.5 -/

/-- OpenStax Introductory Statistics 2e Try It 3.24. Two cards drawn with replacement from a deck
with 12 face cards and 40 other cards (ordered pairs of the 52 cards, card `i` a face card when
`i < 12`): `P(FF) = (12/52)^2 = 9/169`. -/
@[kb "openstaxintrostats2e" "Try It 3.24, p. 202"]
theorem tryit_3_24_two_face_cards_with_replacement :
    let P : Measure (Fin 52 × Fin 52) := uniformOn Set.univ
    (P {ω | (ω.1 : ℕ) < 12 ∧ (ω.2 : ℕ) < 12}).toReal = 9 / 169 := by
  intro P
  have hc : Fintype.card (Fin 52 × Fin 52) = 2704 := by simp
  exact (prob_card (fun ω : Fin 52 × Fin 52 => (ω.1 : ℕ) < 12 ∧ (ω.2 : ℕ) < 12) 144 2704 hc
    (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.25. Two cards drawn without replacement from a
deck with 12 face cards (`F`) and 40 other cards (`N`) (2652 equally likely ordered pairs of
distinct cards, card `i` a face card when `i < 12`): `P(FN or NF) = 80/221`, `P(N | F) = 40/51`,
`P(at most one face card) = 210/221` and `P(at least one face card) = 91/221`. -/
@[kb "openstaxintrostats2e" "Try It 3.25, p. 204"]
theorem tryit_3_25_face_cards_without_replacement :
    let P : Measure (TwoWithoutReplacement 52) := uniformOn Set.univ
    (P {ω | ((ω.1.1 : ℕ) < 12 ∧ 12 ≤ (ω.1.2 : ℕ)) ∨ (12 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 12)}).toReal
        = 80 / 221 ∧
      (P[{ω | 12 ≤ (ω.1.2 : ℕ)} | {ω | (ω.1.1 : ℕ) < 12}]).toReal = 40 / 51 ∧
      (P {ω | ¬ ((ω.1.1 : ℕ) < 12 ∧ (ω.1.2 : ℕ) < 12)}).toReal = 210 / 221 ∧
      (P {ω | (ω.1.1 : ℕ) < 12 ∨ (ω.1.2 : ℕ) < 12}).toReal = 91 / 221 := by
  intro P
  have hc : Fintype.card (TwoWithoutReplacement 52) = 2652 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (prob_card (fun ω : TwoWithoutReplacement 52 =>
      ((ω.1.1 : ℕ) < 12 ∧ 12 ≤ (ω.1.2 : ℕ)) ∨ (12 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 12)) 960 2652 hc
      (by decide +kernel)).trans (by norm_num)
  · exact (cprob_card (fun ω : TwoWithoutReplacement 52 => (ω.1.1 : ℕ) < 12)
      (fun ω => 12 ≤ (ω.1.2 : ℕ)) 480 612 (by decide +kernel) (by decide +kernel)).trans
      (by norm_num)
  · exact (prob_card (fun ω : TwoWithoutReplacement 52 =>
      ¬ ((ω.1.1 : ℕ) < 12 ∧ (ω.1.2 : ℕ) < 12)) 2520 2652 hc (by decide +kernel)).trans
      (by norm_num)
  · exact (prob_card (fun ω : TwoWithoutReplacement 52 =>
      (ω.1.1 : ℕ) < 12 ∨ (ω.1.2 : ℕ) < 12) 1092 2652 hc (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.26. Four red and three yellow balls, two drawn
without replacement (42 equally likely ordered pairs of distinct balls, ball `i` red when `i < 4`):
one ball of each colour with probability 4/7. -/
@[kb "openstaxintrostats2e" "Try It 3.26, p. 205"]
theorem tryit_3_26_red_and_yellow_balls :
    let P : Measure (TwoWithoutReplacement 7) := uniformOn Set.univ
    (P {ω | ((ω.1.1 : ℕ) < 4 ∧ 4 ≤ (ω.1.2 : ℕ)) ∨ (4 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 4)}).toReal =
      4 / 7 := by
  intro P
  have hc : Fintype.card (TwoWithoutReplacement 7) = 42 := by decide +kernel
  exact (prob_card (fun ω : TwoWithoutReplacement 7 =>
    ((ω.1.1 : ℕ) < 4 ∧ 4 ≤ (ω.1.2 : ℕ)) ∨ (4 ≤ (ω.1.1 : ℕ) ∧ (ω.1.2 : ℕ) < 4)) 24 42 hc
    (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.27. Eight equally likely colours (0 black, 1 white,
2 red, 3 orange, 4 yellow, 5 green, 6 blue, 7 purple), `C` = {green, blue, purple} and
`P` = {red, yellow, blue}: `C and P` is {blue} and `C or P` has five colours, with
`P(C) = P(P) = 3/8`, `P(C and P) = 1/8` and `P(C or P) = 5/8`. -/
@[kb "openstaxintrostats2e" "Try It 3.27, p. 206"]
theorem tryit_3_27_venn_of_eight_colours :
    let P : Measure (Fin 8) := uniformOn Set.univ
    let C : Set (Fin 8) := {i | (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7}
    let D : Set (Fin 8) := {i | (i : ℕ) = 2 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 6}
    C ∩ D = {i : Fin 8 | (i : ℕ) = 6} ∧ C ∪ D = {i : Fin 8 | (i : ℕ) = 2 ∨ (i : ℕ) = 4 ∨
      (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7} ∧
    (P C).toReal = 3 / 8 ∧ (P D).toReal = 3 / 8 ∧ (P (C ∩ D)).toReal = 1 / 8 ∧
      (P (C ∪ D)).toReal = 5 / 8 := by
  intro P C D
  have hc : Fintype.card (Fin 8) = 8 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i; simp only [C, D, Set.mem_inter_iff, Set.mem_setOf_eq]; omega
  · ext i; simp only [C, D, Set.mem_union, Set.mem_setOf_eq]; omega
  · exact (prob_card (fun i : Fin 8 => (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) 3 8 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 8 => (i : ℕ) = 2 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 6) 3 8 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 8 => ((i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) ∧
      ((i : ℕ) = 2 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 6)) 1 8 hc (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 8 => ((i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) ∨
      ((i : ℕ) = 2 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 6)) 5 8 hc (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.28. One roll of a fair die (face `i + 1`), `A` = a
prime number, `B` = an odd number: `A and B` = {3, 5}, `A or B` = {1, 2, 3, 5}, and
`P(A) = P(B) = 1/2`, `P(A and B) = 1/3`, `P(A or B) = 2/3`. -/
@[kb "openstaxintrostats2e" "Try It 3.28, p. 206"]
theorem tryit_3_28_die_prime_and_odd :
    let P : Measure (Fin 6) := uniformOn Set.univ
    let A : Set (Fin 6) := {i | Nat.Prime ((i : ℕ) + 1)}
    let B : Set (Fin 6) := {i | ((i : ℕ) + 1) % 2 = 1}
    A ∩ B = {i : Fin 6 | (i : ℕ) + 1 = 3 ∨ (i : ℕ) + 1 = 5} ∧
      A ∪ B = {i : Fin 6 | (i : ℕ) + 1 = 1 ∨ (i : ℕ) + 1 = 2 ∨ (i : ℕ) + 1 = 3 ∨ (i : ℕ) + 1 = 5} ∧
      (P A).toReal = 1 / 2 ∧ (P B).toReal = 1 / 2 ∧ (P (A ∩ B)).toReal = 1 / 3 ∧
      (P (A ∪ B)).toReal = 2 / 3 := by
  intro P A B
  have hc : Fintype.card (Fin 6) = 6 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    simp only [A, B, Set.mem_inter_iff, Set.mem_setOf_eq]
    have := i.2
    interval_cases (i : ℕ) <;> simp (config := {decide := true})
  · ext i
    simp only [A, B, Set.mem_union, Set.mem_setOf_eq]
    have := i.2
    interval_cases (i : ℕ) <;> simp (config := {decide := true})
  · exact (prob_card (fun i : Fin 6 => Nat.Prime ((i : ℕ) + 1)) 3 6 hc (by decide)).trans
      (by norm_num)
  · exact (prob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 1) 3 6 hc (by decide)).trans
      (by norm_num)
  · exact (prob_card (fun i : Fin 6 => Nat.Prime ((i : ℕ) + 1) ∧ ((i : ℕ) + 1) % 2 = 1) 2 6 hc
      (by decide)).trans (by norm_num)
  · exact (prob_card (fun i : Fin 6 => Nat.Prime ((i : ℕ) + 1) ∨ ((i : ℕ) + 1) % 2 = 1) 4 6 hc
      (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Try It 3.29. At a factory 50% of workers have a second job
(`W`), 25% have a working spouse (`S`), 5% both. The regions of the Venn diagram: `W` only 0.45,
both 0.05, `S` only 0.20, neither 0.30 (and `P(W or S) = 0.70`). -/
@[kb "openstaxintrostats2e" "Try It 3.29, p. 207"]
theorem tryit_3_29_second_job_and_working_spouse {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W S : Set Ω} (hW : MeasurableSet W) (hS : MeasurableSet S)
    (pW : P.real W = 0.50) (pS : P.real S = 0.25) (pWS : P.real (W ∩ S) = 0.05) :
    P.real (W ∩ Sᶜ) = 0.45 ∧ P.real (S ∩ Wᶜ) = 0.20 ∧ P.real (W ∪ S) = 0.70 ∧
      P.real (W ∪ S)ᶜ = 0.30 := by
  have h1 : P.real (W ∩ Sᶜ) = 0.45 := by
    rw [real_inter_compl hS, pW, pWS]; norm_num
  have h2 : P.real (S ∩ Wᶜ) = 0.20 := by
    rw [real_inter_compl hW, pS, Set.inter_comm, pWS]; norm_num
  have h3 : P.real (W ∪ S) = 0.70 := by
    have := measureReal_union_add_inter (μ := P) (s := W) (t := S) hS
    rw [pW, pS, pWS] at this; linarith
  refine ⟨h1, h2, h3, ?_⟩
  have := probReal_add_probReal_compl (μ := P) (hW.union hS)
  rw [h3] at this; linarith

/-- OpenStax Introductory Statistics 2e Try It 3.30. A bookstore customer buys a novel (`N`) with
probability 0.6, non-fiction (`F`) with probability 0.4, both with probability 0.2: the customer
buys a novel or a non-fiction book with probability 0.8 (Venn regions: novel only 0.4, both 0.2,
non-fiction only 0.2, neither 0.2). -/
@[kb "openstaxintrostats2e" "Try It 3.30, p. 208"]
theorem tryit_3_30_novel_or_nonfiction {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N F : Set Ω} (hN : MeasurableSet N) (hF : MeasurableSet F)
    (pN : P.real N = 0.6) (pF : P.real F = 0.4) (pNF : P.real (N ∩ F) = 0.2) :
    P.real (N ∪ F) = 0.8 ∧ P.real (N ∩ Fᶜ) = 0.4 ∧ P.real (F ∩ Nᶜ) = 0.2 ∧
      P.real (N ∪ F)ᶜ = 0.2 := by
  have h3 : P.real (N ∪ F) = 0.8 := by
    have := measureReal_union_add_inter (μ := P) (s := N) (t := F) hF
    rw [pN, pF, pNF] at this; linarith
  refine ⟨h3, ?_, ?_, ?_⟩
  · rw [real_inter_compl hF, pN, pNF]; norm_num
  · rw [real_inter_compl hN, pF, Set.inter_comm, pNF]; norm_num
  · have := probReal_add_probReal_compl (μ := P) (hN.union hF)
    rw [h3] at this; linarith

end UndergradKB.Statistics.Course.TryItC3
