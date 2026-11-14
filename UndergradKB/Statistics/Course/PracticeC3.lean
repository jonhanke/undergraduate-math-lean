import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Prime.Defs
import UndergradKB.Common.Attr

/-!
# Practice exercises, chapter 3 (OpenStax *Introductory Statistics 2e*): probability topics

Equally likely outcomes are modelled by `ProbabilityTheory.uniformOn Set.univ` on a finite type;
tables of counts by the probability mass function with weights equal to the counts; exercises that
only give probabilities are stated for an arbitrary probability measure. All probabilities are
real numbers equal to exact rationals.

Skipped as purely symbolic or verbal: 1, 24 to 36, 38, 39, 47, 49, 52 (symbols, words, sample
space), 22 and 23 (a colour wheel known only from a figure), 44 to 46 (values copied from the
statement).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Statistics.Course.PracticeC3

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

/-- The probability measure of a table of counts. -/
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

end Abstract

/-! ### Section 3.1: equally likely outcomes -/

/-- Party favors: 12 hats, 15 noisemakers, 10 finger traps, 5 bags of confetti (types 0 to 3). -/
def partyCounts : Fin 4 → ℕ := ![12, 15, 10, 5]

/-- OpenStax Introductory Statistics 2e Practice exercise 3.2. One of 42 party favors is drawn at
random; the probability of a hat is 12/42 = 2/7. -/
@[kb "openstaxintrostats2e" "Exercise 3.2, p. 214"]
theorem ex_3_2_party_hat :
    let P : Measure (Fin 4) := tableMeasure partyCounts (by decide)
    (P {i | (i : ℕ) = 0}).toReal = 2 / 7 := by
  intro P
  exact (tprob _ _ (fun i : Fin 4 => (i : ℕ) = 0) 12 42 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.3. Party favors as in 3.2: the
probability of a noisemaker is 15/42 = 5/14. -/
@[kb "openstaxintrostats2e" "Exercise 3.3, p. 214"]
theorem ex_3_3_party_noisemaker :
    let P : Measure (Fin 4) := tableMeasure partyCounts (by decide)
    (P {i | (i : ℕ) = 1}).toReal = 5 / 14 := by
  intro P
  exact (tprob _ _ (fun i : Fin 4 => (i : ℕ) = 1) 15 42 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.4. Party favors as in 3.2: the
probability of a finger trap is 10/42 = 5/21. -/
@[kb "openstaxintrostats2e" "Exercise 3.4, p. 214"]
theorem ex_3_4_party_finger_trap :
    let P : Measure (Fin 4) := tableMeasure partyCounts (by decide)
    (P {i | (i : ℕ) = 2}).toReal = 5 / 21 := by
  intro P
  exact (tprob _ _ (fun i : Fin 4 => (i : ℕ) = 2) 10 42 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.5. Party favors as in 3.2: the
probability of a bag of confetti is 5/42. -/
@[kb "openstaxintrostats2e" "Exercise 3.5, p. 214"]
theorem ex_3_5_party_confetti :
    let P : Measure (Fin 4) := tableMeasure partyCounts (by decide)
    (P {i | (i : ℕ) = 3}).toReal = 5 / 42 := by
  intro P
  exact (tprob _ _ (fun i : Fin 4 => (i : ℕ) = 3) 5 42 (by decide) (by decide)).trans
    (by norm_num)

/-- Jelly beans: 22 red, 38 yellow, 20 green, 28 purple, 26 blue (colours 0 to 4) and the rest of
the 150 orange (colour 5). -/
def jellyCounts : Fin 6 → ℕ := ![22, 38, 20, 28, 26, 150 - (22 + 38 + 20 + 28 + 26)]

/-- OpenStax Introductory Statistics 2e Practice exercise 3.6. A jar of 150 jelly beans: the
probability of blue is 26/150 = 13/75. -/
@[kb "openstaxintrostats2e" "Exercise 3.6, p. 214"]
theorem ex_3_6_jelly_blue :
    let P : Measure (Fin 6) := tableMeasure jellyCounts (by decide)
    (P {i | (i : ℕ) = 4}).toReal = 13 / 75 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 4) 26 150 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.7. Jelly beans as in 3.6: the
probability of green is 20/150 = 2/15. -/
@[kb "openstaxintrostats2e" "Exercise 3.7, p. 214"]
theorem ex_3_7_jelly_green :
    let P : Measure (Fin 6) := tableMeasure jellyCounts (by decide)
    (P {i | (i : ℕ) = 2}).toReal = 2 / 15 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 2) 20 150 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.8. Jelly beans as in 3.6: the
probability of purple is 28/150 = 14/75. -/
@[kb "openstaxintrostats2e" "Exercise 3.8, p. 214"]
theorem ex_3_8_jelly_purple :
    let P : Measure (Fin 6) := tableMeasure jellyCounts (by decide)
    (P {i | (i : ℕ) = 3}).toReal = 14 / 75 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 3) 28 150 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.9. Jelly beans as in 3.6: the
probability of red is 22/150 = 11/75. -/
@[kb "openstaxintrostats2e" "Exercise 3.9, p. 214"]
theorem ex_3_9_jelly_red :
    let P : Measure (Fin 6) := tableMeasure jellyCounts (by decide)
    (P {i | (i : ℕ) = 0}).toReal = 11 / 75 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 0) 22 150 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.10. Jelly beans as in 3.6: the
probability of yellow is 38/150 = 19/75. -/
@[kb "openstaxintrostats2e" "Exercise 3.10, p. 214"]
theorem ex_3_10_jelly_yellow :
    let P : Measure (Fin 6) := tableMeasure jellyCounts (by decide)
    (P {i | (i : ℕ) = 1}).toReal = 19 / 75 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 1) 38 150 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.11. Jelly beans as in 3.6: there are
150 - 134 = 16 orange ones, so the probability of orange is 16/150 = 8/75. -/
@[kb "openstaxintrostats2e" "Exercise 3.11, p. 214"]
theorem ex_3_11_jelly_orange :
    let P : Measure (Fin 6) := tableMeasure jellyCounts (by decide)
    (P {i | (i : ℕ) = 5}).toReal = 8 / 75 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 5) 16 150 (by decide) (by decide)).trans
    (by norm_num)

/-- Countries: North America 23, South America 12, Europe 47, Asia 44, Africa 54, Oceania 14
(regions 0 to 5 in this order). -/
def countryCounts : Fin 6 → ℕ := ![23, 12, 47, 44, 54, 14]

/-- OpenStax Introductory Statistics 2e Practice exercise 3.12. Of 194 countries, the probability
that a randomly chosen one is in Asia is 44/194 = 22/97. -/
@[kb "openstaxintrostats2e" "Exercise 3.12, p. 214"]
theorem ex_3_12_country_asia :
    let P : Measure (Fin 6) := tableMeasure countryCounts (by decide)
    (P {i | (i : ℕ) = 3}).toReal = 22 / 97 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 3) 44 194 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.13. Countries as in 3.12: Europe has
probability 47/194. -/
@[kb "openstaxintrostats2e" "Exercise 3.13, p. 214"]
theorem ex_3_13_country_europe :
    let P : Measure (Fin 6) := tableMeasure countryCounts (by decide)
    (P {i | (i : ℕ) = 2}).toReal = 47 / 194 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 2) 47 194 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.14. Countries as in 3.12: Africa has
probability 54/194 = 27/97. -/
@[kb "openstaxintrostats2e" "Exercise 3.14, p. 214"]
theorem ex_3_14_country_africa :
    let P : Measure (Fin 6) := tableMeasure countryCounts (by decide)
    (P {i | (i : ℕ) = 4}).toReal = 27 / 97 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 4) 54 194 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.15. Countries as in 3.12: North
America has probability 23/194. -/
@[kb "openstaxintrostats2e" "Exercise 3.15, p. 214"]
theorem ex_3_15_country_north_america :
    let P : Measure (Fin 6) := tableMeasure countryCounts (by decide)
    (P {i | (i : ℕ) = 0}).toReal = 23 / 194 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 0) 23 194 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.16. Countries as in 3.12: Oceania has
probability 14/194 = 7/97. -/
@[kb "openstaxintrostats2e" "Exercise 3.16, p. 214"]
theorem ex_3_16_country_oceania :
    let P : Measure (Fin 6) := tableMeasure countryCounts (by decide)
    (P {i | (i : ℕ) = 5}).toReal = 7 / 97 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 5) 14 194 (by decide) (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.17. Countries as in 3.12: South
America has probability 12/194 = 6/97. -/
@[kb "openstaxintrostats2e" "Exercise 3.17, p. 214"]
theorem ex_3_17_country_south_america :
    let P : Measure (Fin 6) := tableMeasure countryCounts (by decide)
    (P {i | (i : ℕ) = 1}).toReal = 6 / 97 := by
  intro P
  exact (tprob _ _ (fun i : Fin 6 => (i : ℕ) = 1) 12 194 (by decide) (by decide)).trans
    (by norm_num)

/-- A card of the 52-card deck as (suit, rank): suits 0 spades, 1 hearts, 2 diamonds, 3 clubs. -/
abbrev Card := Fin 4 × Fin 13

/-- OpenStax Introductory Statistics 2e Practice exercise 3.18. A card from a standard deck is red
(hearts or diamonds) with probability 26/52 = 1/2. -/
@[kb "openstaxintrostats2e" "Exercise 3.18, p. 214"]
theorem ex_3_18_red_card :
    let P : Measure Card := uniformOn Set.univ
    (P {c | (c.1 : ℕ) = 1 ∨ (c.1 : ℕ) = 2}).toReal = 1 / 2 := by
  intro P
  have hc : Fintype.card Card = 52 := by simp
  exact (prob_card (fun c : Card => (c.1 : ℕ) = 1 ∨ (c.1 : ℕ) = 2) 26 52 hc (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.19. A card from a standard deck is a
club with probability 13/52 = 1/4. -/
@[kb "openstaxintrostats2e" "Exercise 3.19, p. 214"]
theorem ex_3_19_club_card :
    let P : Measure Card := uniformOn Set.univ
    (P {c | (c.1 : ℕ) = 3}).toReal = 1 / 4 := by
  intro P
  have hc : Fintype.card Card = 52 := by simp
  exact (prob_card (fun c : Card => (c.1 : ℕ) = 3) 13 52 hc (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.20. A fair die (outcome `i + 1`) shows
an even number with probability 3/6 = 1/2. -/
@[kb "openstaxintrostats2e" "Exercise 3.20, p. 214"]
theorem ex_3_20_die_even :
    let P : Measure (Fin 6) := uniformOn Set.univ
    (P {i | ((i : ℕ) + 1) % 2 = 0}).toReal = 1 / 2 := by
  intro P
  have hc : Fintype.card (Fin 6) = 6 := by simp
  exact (prob_card (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 0) 3 6 hc (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.21. A fair die (outcome `i + 1`) shows
a prime number (2, 3 or 5) with probability 3/6 = 1/2. -/
@[kb "openstaxintrostats2e" "Exercise 3.21, p. 214"]
theorem ex_3_21_die_prime :
    let P : Measure (Fin 6) := uniformOn Set.univ
    (P {i | Nat.Prime ((i : ℕ) + 1)}).toReal = 1 / 2 := by
  intro P
  have hc : Fintype.card (Fin 6) = 6 := by simp
  exact (prob_card (fun i : Fin 6 => Nat.Prime ((i : ℕ) + 1)) 3 6 hc (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.37. An event and its complement have
probabilities adding to 1. -/
@[kb "openstaxintrostats2e" "Exercise 3.37, p. 215"]
theorem ex_3_37_event_and_complement {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) :
    P.real A + P.real Aᶜ = 1 :=
  probReal_add_probReal_compl hA

/-! ### Section 3.2 -/

/-- OpenStax Introductory Statistics 2e Practice exercise 3.40. If `E` and `F` cannot happen
together and `P(F) = 0.5`, the conditional probability `P(E | F)` is 0. -/
@[kb "openstaxintrostats2e" "Exercise 3.40, p. 216"]
theorem ex_3_40_mutually_exclusive_conditional {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E F : Set Ω} (hF : MeasurableSet F) (hEF : Disjoint E F)
    (pE : P.real E = 0.4) (pF : P.real F = 0.5) :
    (P[E | F]).toReal = 0 := by
  rw [cond_toReal hF, Set.disjoint_iff_inter_eq_empty.1 hEF.symm]
  simp

/-- OpenStax Introductory Statistics 2e Practice exercise 3.41. For independent events `J`, `K`
with `P(J | K) = 0.3` (and `P(K) > 0`), `P(J) = 0.3`. -/
@[kb "openstaxintrostats2e" "Exercise 3.41, p. 216"]
theorem ex_3_41_independent_conditional {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {J K : Set Ω} (hJ : MeasurableSet J) (hK : MeasurableSet K)
    (hi : IndepSet J K P) (hpos : 0 < P.real K) (h : (P[J | K]).toReal = 0.3) :
    P.real J = 0.3 := by
  rw [cond_toReal hK, Set.inter_comm, indep_real hJ hK hi] at h
  have : P.real K ≠ 0 := hpos.ne'
  field_simp at h
  linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 3.42. Mutually exclusive `U`, `V` with
`P(U) = 0.26`, `P(V) = 0.37`: `P(U and V) = 0`, `P(U | V) = 0` and `P(U or V) = 0.63`. -/
@[kb "openstaxintrostats2e" "Exercise 3.42, p. 216"]
theorem ex_3_42_mutually_exclusive_union {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U V : Set Ω} (hV : MeasurableSet V) (hUV : Disjoint U V)
    (pU : P.real U = 0.26) (pV : P.real V = 0.37) :
    P.real (U ∩ V) = 0 ∧ (P[U | V]).toReal = 0 ∧ P.real (U ∪ V) = 0.63 := by
  have h0 : P.real (U ∩ V) = 0 := by
    rw [Set.disjoint_iff_inter_eq_empty.1 hUV]; simp
  refine ⟨h0, ?_, ?_⟩
  · rw [cond_toReal hV, Set.inter_comm, h0]; simp
  · have h2 := measureReal_union_add_inter (μ := P) (s := U) (t := V) hV
    rw [pU, pV, h0] at h2
    norm_num at h2 ⊢; linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 3.43. Independent `Q`, `R` with
`P(Q) = 0.4` and `P(Q and R) = 0.1` give `P(R) = 0.25`. -/
@[kb "openstaxintrostats2e" "Exercise 3.43, p. 216"]
theorem ex_3_43_independent_probability {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Q R : Set Ω} (hQ : MeasurableSet Q) (hR : MeasurableSet R)
    (hi : IndepSet Q R P) (pQ : P.real Q = 0.4) (pQR : P.real (Q ∩ R) = 0.1) :
    P.real R = 0.25 := by
  have := indep_real hQ hR hi
  rw [pQ, pQR] at this
  linarith

/-! ### Section 3.3: the pizza and salad restaurant

The data of exercises 44 to 53 are `P(Z) = 0.87`, `P(S) = 0.32`, `P(S | Z) = 0.55`. They are in fact
inconsistent: `P(Z and S) = 0.4785` would exceed `P(S) = 0.32`. The arithmetic asked for is proved
below, and the inconsistency is recorded as `ex_3_48_pizza_data_inconsistent`. -/

/-- OpenStax Introductory Statistics 2e Practice exercise 3.48. From `P(Z) = 0.87` and
`P(S | Z) = 0.55`, the probability of ordering both is `0.87 * 0.55 = 0.4785`. -/
@[kb "openstaxintrostats2e" "Exercise 3.48, p. 216"]
theorem ex_3_48_pizza_and_salad {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z S : Set Ω} (hZ : MeasurableSet Z)
    (pZ : P.real Z = 0.87) (pSZ : (P[S | Z]).toReal = 0.55) :
    P.real (Z ∩ S) = 0.4785 := by
  rw [cond_toReal hZ, pZ] at pSZ
  have : P.real (Z ∩ S) = 0.55 * 0.87 := by
    field_simp at pSZ; linarith
  rw [this]; norm_num

/-- Possible erratum in the data of exercises 44 to 53: no probability measure has
`P(S) = 0.32` and `P(S | Z) = 0.55` with `P(Z) = 0.87`, since then `P(Z and S) = 0.4785 > P(S)`. -/
@[kb "openstaxintrostats2e" "Exercise 3.48, p. 216"]
theorem ex_3_48_pizza_data_inconsistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z S : Set Ω} (hZ : MeasurableSet Z)
    (pZ : P.real Z = 0.87) (pS : P.real S = 0.32) (pSZ : (P[S | Z]).toReal = 0.55) : False := by
  have h := ex_3_48_pizza_and_salad hZ pZ pSZ
  have h2 : P.real (Z ∩ S) ≤ P.real S := measureReal_mono Set.inter_subset_right
  rw [h, pS] at h2; norm_num at h2

/-- OpenStax Introductory Statistics 2e Practice exercise 3.50. Pizza and salad are not
independent: `P(S | Z) = 0.55` differs from `P(S) = 0.32`. -/
@[kb "openstaxintrostats2e" "Exercise 3.50, p. 216"]
theorem ex_3_50_pizza_salad_not_independent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z S : Set Ω}
    (pS : P.real S = 0.32) (pSZ : (P[S | Z]).toReal = 0.55) :
    (P[S | Z]).toReal ≠ P.real S := by
  rw [pS, pSZ]; norm_num

/-- OpenStax Introductory Statistics 2e Practice exercise 3.51. By the addition rule, the
probability of ordering pizza or salad is `0.87 + 0.32 - 0.4785 = 0.7115`. -/
@[kb "openstaxintrostats2e" "Exercise 3.51, p. 216"]
theorem ex_3_51_pizza_or_salad {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z S : Set Ω} (hZ : MeasurableSet Z) (hS : MeasurableSet S)
    (pZ : P.real Z = 0.87) (pS : P.real S = 0.32) (pSZ : (P[S | Z]).toReal = 0.55) :
    P.real (Z ∪ S) = 0.7115 := by
  have h1 := ex_3_48_pizza_and_salad hZ pZ pSZ
  have h2 := measureReal_union_add_inter (μ := P) (s := Z) (t := S) hS
  rw [pZ, pS, h1] at h2
  norm_num at h2 ⊢; linarith

/-- OpenStax Introductory Statistics 2e Practice exercise 3.53. Pizza and salad orders are not
mutually exclusive: `P(Z and S) = 0.4785 ≠ 0`. -/
@[kb "openstaxintrostats2e" "Exercise 3.53, p. 216"]
theorem ex_3_53_pizza_salad_not_exclusive {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z S : Set Ω} (hZ : MeasurableSet Z)
    (pZ : P.real Z = 0.87) (pSZ : (P[S | Z]).toReal = 0.55) :
    ¬ Disjoint Z S := by
  intro hd
  have h := ex_3_48_pizza_and_salad hZ pZ pSZ
  rw [Set.disjoint_iff_inter_eq_empty.1 hd] at h
  norm_num at h

/-! ### Section 3.4: musicians -/

/-- Cell counts of Table 3.16: rows woman, man; columns self-taught, studied in school, private
instruction. -/
def musicianCounts : Fin 2 × Fin 3 → ℕ := fun ω => ![![12, 38, 22], ![19, 24, 15]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Practice exercise 3.54. Of 130 musicians, 72 are women:
probability 72/130 = 36/65. -/
@[kb "openstaxintrostats2e" "Exercise 3.54, p. 217"]
theorem ex_3_54_musician_woman :
    let P : Measure (Fin 2 × Fin 3) := tableMeasure musicianCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0}).toReal = 36 / 65 := by
  intro P
  have hD : ∑ ω, musicianCounts ω = 130 := by decide
  exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 0) 72 130 hD (by decide)).trans
    (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.55. A musician is a man with private
instruction with probability 15/130 = 3/26 (about 0.12). -/
@[kb "openstaxintrostats2e" "Exercise 3.55, p. 217"]
theorem ex_3_55_musician_man_private :
    let P : Measure (Fin 2 × Fin 3) := tableMeasure musicianCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 2}).toReal = 3 / 26 := by
  intro P
  have hD : ∑ ω, musicianCounts ω = 130 := by decide
  exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 1 ∧ (ω.2 : ℕ) = 2) 15 130 hD
    (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.56. A musician is a woman or
self-taught with probability (72 + 31 - 12)/130 = 91/130 = 7/10. -/
@[kb "openstaxintrostats2e" "Exercise 3.56, p. 217"]
theorem ex_3_56_musician_woman_or_self_taught :
    let P : Measure (Fin 2 × Fin 3) := tableMeasure musicianCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 0}).toReal = 7 / 10 := by
  intro P
  have hD : ∑ ω, musicianCounts ω = 130 := by decide
  exact (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 0 ∨ (ω.2 : ℕ) = 0) 91 130 hD
    (by decide)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.57. "Woman" and "studied in school" are
not mutually exclusive: 38 of the 130 musicians are both, probability 19/65 ≠ 0. -/
@[kb "openstaxintrostats2e" "Exercise 3.57, p. 217"]
theorem ex_3_57_woman_and_school_not_exclusive :
    let P : Measure (Fin 2 × Fin 3) := tableMeasure musicianCounts (by decide)
    (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 1}).toReal = 19 / 65 ∧
      (P {ω | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 1}).toReal ≠ 0 := by
  intro P
  have hD : ∑ ω, musicianCounts ω = 130 := by decide
  have h : (P {ω : Fin 2 × Fin 3 | (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 1}).toReal = 19 / 65 :=
    (tprob _ _ (fun ω : Fin 2 × Fin 3 => (ω.1 : ℕ) = 0 ∧ (ω.2 : ℕ) = 1) 38 130 hD
      (by decide)).trans (by norm_num)
  exact ⟨h, by rw [h]; norm_num⟩

/-! ### Section 3.5 -/

/-- OpenStax Introductory Statistics 2e Practice exercise 3.58. The tree diagram of cancer (`C`,
probability 0.4567) and at least one false positive (`P`, probability 0.51): the complementary
branches have probabilities 0.5433 and 0.49. -/
@[kb "openstaxintrostats2e" "Exercise 3.58, p. 217"]
theorem ex_3_58_cancer_false_positive_tree {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C F : Set Ω} (hC : MeasurableSet C) (hF : MeasurableSet F)
    (pC : P.real C = 0.4567) (pF : P.real F = 0.51) :
    P.real Cᶜ = 0.5433 ∧ P.real Fᶜ = 0.49 := by
  have h1 := probReal_add_probReal_compl (μ := P) hC
  have h2 := probReal_add_probReal_compl (μ := P) hF
  rw [pC] at h1; rw [pF] at h2
  constructor <;> norm_num <;> linarith

/-! ### Bringing It Together: smoking level by ethnicity -/

/-- Table 3.17 counts: rows smoking level 1-10, 11-20, 21-30, 31+; columns Black, Native Hawaiian,
Hispanic/Latino, Japanese, White. -/
def smokeCounts : Fin 4 × Fin 5 → ℕ := fun ω =>
  ![![9886, 2745, 12831, 8378, 7650], ![6514, 3062, 4932, 10680, 9877],
    ![1671, 1419, 1406, 4715, 6062], ![759, 788, 800, 2305, 3970]] ω.1 ω.2

/-- OpenStax Introductory Statistics 2e Practice exercise 3.59. The completed totals of Table 3.17:
row totals 41490, 35065, 15273, 8622; column totals 18830, 8014, 19969, 26078, 27559; grand total
100450. -/
@[kb "openstaxintrostats2e" "Exercise 3.59, p. 217"]
theorem ex_3_59_smoking_table_totals :
    (∑ j : Fin 5, smokeCounts (0, j) = 41490 ∧ ∑ j : Fin 5, smokeCounts (1, j) = 35065 ∧
      ∑ j : Fin 5, smokeCounts (2, j) = 15273 ∧ ∑ j : Fin 5, smokeCounts (3, j) = 8622) ∧
    (∑ i : Fin 4, smokeCounts (i, 0) = 18830 ∧ ∑ i : Fin 4, smokeCounts (i, 1) = 8014 ∧
      ∑ i : Fin 4, smokeCounts (i, 2) = 19969 ∧ ∑ i : Fin 4, smokeCounts (i, 3) = 26078 ∧
      ∑ i : Fin 4, smokeCounts (i, 4) = 27559) ∧
    ∑ ω, smokeCounts ω = 100450 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> decide +kernel

/-- OpenStax Introductory Statistics 2e Practice exercise 3.60. A person from the study smoked 11
to 20 cigarettes a day with probability 35065/100450 = 7013/20090. -/
@[kb "openstaxintrostats2e" "Exercise 3.60, p. 217"]
theorem ex_3_60_smoke_11_to_20 :
    let P : Measure (Fin 4 × Fin 5) := tableMeasure smokeCounts (by decide +kernel)
    (P {ω | (ω.1 : ℕ) = 1}).toReal = 7013 / 20090 := by
  intro P
  have hD : ∑ ω, smokeCounts ω = 100450 := by decide +kernel
  exact (tprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.1 : ℕ) = 1) 35065 100450 hD
    (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.61. A person from the study is
Hispanic/Latino with probability 19969/100450. -/
@[kb "openstaxintrostats2e" "Exercise 3.61, p. 217"]
theorem ex_3_61_hispanic_latino :
    let P : Measure (Fin 4 × Fin 5) := tableMeasure smokeCounts (by decide +kernel)
    (P {ω | (ω.2 : ℕ) = 2}).toReal = 19969 / 100450 := by
  intro P
  have hD : ∑ ω, smokeCounts ω = 100450 := by decide +kernel
  exact tprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.2 : ℕ) = 2) 19969 100450 hD (by decide +kernel)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.62. A person is Japanese American and
smokes 21 to 30 cigarettes a day with probability 4715/100450 = 943/20090. -/
@[kb "openstaxintrostats2e" "Exercise 3.62, p. 217"]
theorem ex_3_62_japanese_and_21_to_30 :
    let P : Measure (Fin 4 × Fin 5) := tableMeasure smokeCounts (by decide +kernel)
    (P {ω | (ω.2 : ℕ) = 3 ∧ (ω.1 : ℕ) = 2}).toReal = 943 / 20090 := by
  intro P
  have hD : ∑ ω, smokeCounts ω = 100450 := by decide +kernel
  exact (tprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.2 : ℕ) = 3 ∧ (ω.1 : ℕ) = 2) 4715 100450 hD
    (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.63. A person is Japanese American or
smokes 21 to 30 cigarettes a day with probability (26078 + 15273 - 4715)/100450 = 36636/100450 =
18318/50225. -/
@[kb "openstaxintrostats2e" "Exercise 3.63, p. 217"]
theorem ex_3_63_japanese_or_21_to_30 :
    let P : Measure (Fin 4 × Fin 5) := tableMeasure smokeCounts (by decide +kernel)
    (P {ω | (ω.2 : ℕ) = 3 ∨ (ω.1 : ℕ) = 2}).toReal = 18318 / 50225 := by
  intro P
  have hD : ∑ ω, smokeCounts ω = 100450 := by decide +kernel
  exact (tprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.2 : ℕ) = 3 ∨ (ω.1 : ℕ) = 2) 36636 100450 hD
    (by decide +kernel)).trans (by norm_num)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.64. Given that a person smokes 21 to 30
cigarettes a day, the probability of being Japanese American is 4715/15273. -/
@[kb "openstaxintrostats2e" "Exercise 3.64, p. 217"]
theorem ex_3_64_japanese_given_21_to_30 :
    let P : Measure (Fin 4 × Fin 5) := tableMeasure smokeCounts (by decide +kernel)
    (P[{ω | (ω.2 : ℕ) = 3} | {ω | (ω.1 : ℕ) = 2}]).toReal = 4715 / 15273 := by
  intro P
  exact tcprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.1 : ℕ) = 2) (fun ω => (ω.2 : ℕ) = 3) 4715 15273
    (by decide +kernel) (by decide +kernel)

/-- OpenStax Introductory Statistics 2e Practice exercise 3.65. Smoking level and ethnicity are
dependent: for "Japanese American" and "21 to 30 a day", `P(both) = 4715/100450` while the product
of the two probabilities is `(26078/100450) (15273/100450)`, which is different, so the two events
are not independent. -/
@[kb "openstaxintrostats2e" "Exercise 3.65, p. 217"]
theorem ex_3_65_smoking_ethnicity_dependent :
    let P : Measure (Fin 4 × Fin 5) := tableMeasure smokeCounts (by decide +kernel)
    ¬ IndepSet {ω : Fin 4 × Fin 5 | (ω.2 : ℕ) = 3} {ω | (ω.1 : ℕ) = 2} P := by
  intro P hi
  have hD : ∑ ω, smokeCounts ω = 100450 := by decide +kernel
  have h1 : (P {ω : Fin 4 × Fin 5 | (ω.2 : ℕ) = 3 ∧ (ω.1 : ℕ) = 2}).toReal = 4715 / 100450 :=
    tprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.2 : ℕ) = 3 ∧ (ω.1 : ℕ) = 2) 4715 100450 hD
      (by decide +kernel)
  have h2 : (P {ω : Fin 4 × Fin 5 | (ω.2 : ℕ) = 3}).toReal = 26078 / 100450 :=
    tprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.2 : ℕ) = 3) 26078 100450 hD (by decide +kernel)
  have h3 : (P {ω : Fin 4 × Fin 5 | (ω.1 : ℕ) = 2}).toReal = 15273 / 100450 :=
    tprob _ _ (fun ω : Fin 4 × Fin 5 => (ω.1 : ℕ) = 2) 15273 100450 hD (by decide +kernel)
  have hm : ∀ s : Set (Fin 4 × Fin 5), MeasurableSet s := fun s => (Set.toFinite s).measurableSet
  haveI : IsProbabilityMeasure P :=
    show IsProbabilityMeasure (natPMF smokeCounts _ rfl (by decide +kernel)).toMeasure from
      inferInstance
  have := (indepSet_iff_measure_inter_eq_mul (hm _) (hm _) P).1 hi
  have h4 := congrArg ENNReal.toReal this
  rw [ENNReal.toReal_mul] at h4
  have e : {ω : Fin 4 × Fin 5 | (ω.2 : ℕ) = 3} ∩ {ω | (ω.1 : ℕ) = 2} =
      {ω | (ω.2 : ℕ) = 3 ∧ (ω.1 : ℕ) = 2} := rfl
  rw [e, h1, h2, h3] at h4
  norm_num at h4

end UndergradKB.Statistics.Course.PracticeC3
