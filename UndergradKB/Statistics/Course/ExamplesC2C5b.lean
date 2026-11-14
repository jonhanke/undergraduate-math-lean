import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Perm
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Discrete
import UndergradKB.Statistics.Continuous

/-!
# Worked examples, chapters 3 to 5 (OpenStax *Introductory Statistics 2e*): remaining examples

Examples that earlier files skipped: sampling with and without replacement, the addition and
conditional-probability rules with the book's numbers, binomial, geometric, hypergeometric and
Poisson probabilities computed from the mass functions (exact values or two-sided bounds around
the book's rounded values), and the uniform density of Chapter 5. Probabilities of events are
`P.real`; the named laws are Mathlib's `binomial`, `geometricMeasure`, `poissonMeasure`, and
`hypergeometricPMF` from the repository.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal unitInterval

namespace UndergradKB.Statistics.Course.ExamplesC2C5b

/-- A two-sided bound on `exp t` from the degree-9 Taylor bound at `x = t / k` (private helper). -/
private lemma exp_in {t x lo hi : ℝ} (k : ℕ) (hx : x * k = t) (hx1 : |x| ≤ 1) (h0 : 0 ≤ lo)
    (hl : lo ≤ (∑ m ∈ Finset.range 10, x ^ m / m.factorial) - |x| ^ 10 * (11 / (10 * 3628800)))
    (hh : (∑ m ∈ Finset.range 10, x ^ m / m.factorial) + |x| ^ 10 * (11 / (10 * 3628800)) ≤ hi) :
    lo ^ k ≤ Real.exp t ∧ Real.exp t ≤ hi ^ k := by
  have h := Real.exp_bound hx1 (n := 10) (by norm_num)
  have h' : |x| ^ 10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * (10 : ℕ))) =
      |x| ^ 10 * (11 / (10 * 3628800)) := by norm_num [Nat.factorial]
  rw [h', abs_le] at h
  have e : Real.exp t = Real.exp x ^ k := by rw [← Real.exp_nat_mul, ← hx]; ring_nf
  rw [e]
  exact ⟨pow_le_pow_left₀ h0 (by linarith [h.1]) k,
    pow_le_pow_left₀ (by linarith [h.1, Real.exp_pos x]) (by linarith [h.2]) k⟩

/-- Binomial coefficients as ratios of descending and ordinary factorials, which `norm_num`
evaluates quickly. -/
private lemma choose_real (n k : ℕ) :
    (Nat.choose n k : ℝ) = (n.descFactorial k : ℝ) / (k.factorial : ℝ) := by
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div (Nat.factorial_dvd_descFactorial n k)
    (by positivity)]

private lemma real_Iic (μ : Measure ℕ) [IsFiniteMeasure μ] (k : ℕ) :
    μ.real (Set.Iic k) = ∑ j ∈ range (k + 1), μ.real {j} := by
  have : (Set.Iic k : Set ℕ) = ↑(Finset.range (k + 1)) := by
    ext; simp
  rw [this, sum_measureReal_singleton]

private lemma cond_toReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : Set Ω} (hB : MeasurableSet B) :
    (P[A | B]).toReal = P.real (B ∩ A) / P.real B := by
  rw [cond_apply hB, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [measureReal_def]
  ring

section Chapter3

/-- A playing card: a suit (0 spades, 1 hearts, 2 diamonds, 3 clubs) and a rank (0 for the ace
(the book's "1"), 1 to 8 for 2 to 9, 9 for ten, 10 jack, 11 queen, 12 king). -/
private abbrev Card := Fin 4 × Fin 13

/-- OpenStax Introductory Statistics 2e Example 3.4. Picking three cards from a 52-card deck: with
replacement there are `52³` equally likely ordered picks, without replacement only
`52 · 51 · 50` (the picks are injective). The with-replacement pick (Q of spades, ten of clubs,
Q of spades) repeats a card, so it is not injective; the without-replacement pick (K of hearts,
three of diamonds, J of spades) is injective. -/
@[kb "openstaxintrostats2e" "Example 3.4, p. 185"]
theorem example_3_4_sampling_three_cards :
    Fintype.card (Fin 3 → Card) = 52 ^ 3 ∧ Fintype.card (Fin 3 ↪ Card) = 52 * 51 * 50 ∧
      ¬ Function.Injective (![(0, 11), (3, 9), (0, 11)] : Fin 3 → Card) ∧
      Function.Injective (![(1, 12), (2, 2), (0, 10)] : Fin 3 → Card) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · simp
  · rw [Fintype.card_embedding_eq]
    simp [Nat.descFactorial]

/-- OpenStax Introductory Statistics 2e Example 3.5. Four cards drawn from the deck: the draw
(Q of spades, ace of diamonds, ace of clubs, Q of diamonds) has four distinct cards, so it can come
from sampling without replacement, while (K of hearts, seven of diamonds, six of diamonds, K of
hearts) repeats the king of hearts, so it can only come from sampling with replacement. -/
@[kb "openstaxintrostats2e" "Example 3.5, p. 185"]
theorem example_3_5_which_sampling :
    Function.Injective (![(0, 11), (2, 0), (3, 0), (2, 11)] : Fin 4 → Card) ∧
      ¬ Function.Injective (![(1, 12), (2, 6), (2, 5), (1, 12)] : Fin 4 → Card) := by
  exact ⟨by decide, by decide⟩

/-- OpenStax Introductory Statistics 2e Example 3.14. Klaus goes to New Zealand (`A`, probability
0.6) or Alaska (`B`, probability 0.35) but can afford only one trip, so the events are disjoint:
`P(A or B) = 0.95` and the chance he takes neither is 0.05. -/
@[kb "openstaxintrostats2e" "Example 3.14, p. 191"]
theorem example_3_14_vacation_choice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B) (pA : P.real A = 0.6) (pB : P.real B = 0.35) :
    P.real (A ∪ B) = 0.95 ∧ P.real (A ∪ B)ᶜ = 0.05 := by
  have h := measureReal_union (μ := P) hd hB
  have h2 := probReal_compl_eq_one_sub (μ := P) (hA.union hB)
  rw [pA, pB] at h
  refine ⟨by rw [h]; norm_num, ?_⟩
  rw [h2, h]; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.19. With `P(B) = 0.143` for breast cancer, a woman
with cancer testing negative (`N`) with probability 0.02, and negative tests having probability
0.85, the positive-test probabilities are: `P(positive | B) = 0.98`, `P(B and positive) = 0.14014`
(the book's 0.1401), `P(B') = 0.857` and `P(positive) = 0.15`. -/
@[kb "openstaxintrostats2e" "Example 3.19, p. 195"]
theorem example_3_19_positive_test_probabilities {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B N : Set Ω} (hB : MeasurableSet B) (hN : MeasurableSet N)
    (pB : P.real B = 0.143) (pN : P.real N = 0.85) (pNB : (P[N | B]).toReal = 0.02) :
    (P[Nᶜ | B]).toReal = 0.98 ∧ P.real (B ∩ Nᶜ) = 0.14014 ∧ P.real Bᶜ = 0.857 ∧
      P.real Nᶜ = 0.15 := by
  have h1 : P.real (B ∩ N) = 0.00286 := by
    rw [cond_toReal hB, pB] at pNB
    have : P.real (B ∩ N) = 0.02 * 0.143 := by
      field_simp at pNB; linarith
    rw [this]; norm_num
  have h3 := measureReal_inter_add_sdiff (μ := P) (s := B) (t := N) hN
  have h4 := probReal_add_probReal_compl (μ := P) hB
  have h5 := probReal_add_probReal_compl (μ := P) hN
  have h6 : P.real (B ∩ Nᶜ) = 0.14014 := by
    rw [Set.sdiff_eq] at h3
    linarith
  refine ⟨?_, h6, by linarith, by linarith⟩
  rw [cond_toReal hB, h6, pB]; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.22. Muddy Mouse picks each of three doors with
probability 1/3 and is caught by the cat with probability 1/5, 1/4 and 1/2 behind the respective
doors.
The joint probabilities of being caught are `1/15, 1/12, 1/6`, of not being caught `4/15, 1/4, 1/6`;
the catch probability is `19/60`, the not-caught probability `41/60`, the table total is 1, and the
chance he used door one or two given that he was caught is `9/19`. -/
@[kb "openstaxintrostats2e" "Example 3.22, p. 198"]
theorem example_3_22_muddy_mouse_table :
    let c : Fin 3 → ℝ := ![1 / 5, 1 / 4, 1 / 2]
    let caught : Fin 3 → ℝ := fun i => 1 / 3 * c i
    let free : Fin 3 → ℝ := fun i => 1 / 3 * (1 - c i)
    caught 0 = 1 / 15 ∧ caught 1 = 1 / 12 ∧ caught 2 = 1 / 6 ∧
      free 0 = 4 / 15 ∧ free 1 = 1 / 4 ∧ free 2 = 1 / 6 ∧
      (∑ i, caught i) = 19 / 60 ∧ (∑ i, free i) = 41 / 60 ∧
      (∑ i, caught i) + (∑ i, free i) = 1 ∧
      (caught 0 + caught 1) / ∑ i, caught i = 9 / 19 := by
  intro c caught free
  have h1 : (∑ i, caught i) = 19 / 60 := by simp [caught, c, Fin.sum_univ_succ]; norm_num
  have h2 : (∑ i, free i) = 41 / 60 := by simp [free, c, Fin.sum_univ_succ]; norm_num
  refine ⟨by simp [caught, c]; norm_num, by simp [caught, c]; norm_num, by simp [caught, c]; norm_num,
    by simp [free, c]; norm_num, by simp [free, c]; norm_num, by simp [free, c]; norm_num,
    h1, h2, by rw [h1, h2]; norm_num, ?_⟩
  rw [h1]; simp [caught, c]; norm_num

/-- OpenStax Introductory Statistics 2e Example 3.30. Among African Americans, type O blood has
probability 0.51, the Rh-negative factor 0.075 (the midpoint of the book's 5-10% range) and both
0.04: the chance of type O or Rh-negative is `0.51 + 0.075 - 0.04 = 0.545`, and the chance of
neither is 0.455. -/
@[kb "openstaxintrostats2e" "Example 3.30, p. 207"]
theorem example_3_30_blood_type_venn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {O R : Set Ω} (hO : MeasurableSet O) (hR : MeasurableSet R)
    (pO : P.real O = 0.51) (pR : P.real R = 0.075) (pOR : P.real (O ∩ R) = 0.04) :
    P.real (O ∪ R) = 0.545 ∧ P.real (O ∪ R)ᶜ = 0.455 := by
  have h := measureReal_union_add_inter (μ := P) (s := O) (t := R) hR
  have h2 := probReal_compl_eq_one_sub (μ := P) (hO.union hR)
  rw [pO, pR, pOR] at h
  refine ⟨by linarith, ?_⟩
  rw [h2]; linarith

end Chapter3

section Chapter4

/-- OpenStax Introductory Statistics 2e Example 4.1. Of 50 sampled mothers, 2, 11, 23, 9, 4 and 1
are woken 0, 1, 2, 3, 4 and 5 times a week; the relative frequencies `count/50` lie in `[0, 1]`
and sum to 1, so they form a discrete probability distribution. -/
@[kb "openstaxintrostats2e" "Example 4.1, p. 240"]
theorem example_4_1_newborn_waking_distribution :
    let k : Fin 6 → ℝ := ![2, 11, 23, 9, 4, 1]
    let p : Fin 6 → ℝ := fun i => k i / 50
    (∑ i, k i) = 50 ∧ (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ (∑ i, p i) = 1 := by
  intro k p
  have h : (∑ i, k i) = 50 := by simp [k, Fin.sum_univ_succ]; norm_num
  refine ⟨h, fun i => ?_, ?_⟩
  · fin_cases i <;> simp [p, k] <;> norm_num
  · simp only [p, ← Finset.sum_div, h]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.9. Counting a withdrawal as a success, with
withdrawal probability 0.3 per term, the count of withdrawals among one student is
binomial `B(1, 0.3)`: success has probability 0.3 and failure 0.7. -/
@[kb "openstaxintrostats2e" "Example 4.9, p. 249"]
theorem example_4_9_withdrawal_success :
    let p : unitInterval := ⟨0.3, by norm_num⟩
    Bin(1, p).real {1} = 0.3 ∧ Bin(1, p).real {0} = 0.7 := by
  intro p
  constructor
  · rw [binomial_real_singleton]; simp [p]
  · rw [binomial_real_singleton]; simp [p]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.12. Each of 50 students does the homework on time
with probability 0.7, so `X ~ B(50, 0.7)`: the probability that at least 40 do, `P(X ≥ 40)`, lies
in `(0.0788, 0.0789)`. -/
@[kb "openstaxintrostats2e" "Example 4.12, p. 250"]
theorem example_4_12_at_least_forty_homework :
    let p : unitInterval := ⟨0.7, by norm_num⟩
    0.0788 < Bin(50, p).real (Set.Ici 40) ∧ Bin(50, p).real (Set.Ici 40) < 0.0789 := by
  intro p
  have e : (Set.Ici 40 : Set ℕ) = (Set.Iic 39)ᶜ := by
    ext n; simp only [Set.mem_Ici, Set.mem_compl_iff, Set.mem_Iic, not_le]; omega
  have hs : Bin(50, p).real (Set.Iic 39) = ∑ j ∈ range 40, (Nat.choose 50 j : ℝ) * (0.7 : ℝ) ^ j *
      (1 - 0.7) ^ (50 - j) := by
    rw [real_Iic]
    exact sum_congr rfl fun j _ => by rw [binomial_real_singleton]
  rw [e, probReal_compl_eq_one_sub measurableSet_Iic, hs]
  simp only [choose_real]
  set_option maxRecDepth 100000 in
  norm_num [Finset.sum_range_succ, Nat.descFactorial, Nat.factorial]

/-- OpenStax Introductory Statistics 2e Example 4.21 (first two parts). The chance that a person
has cancer is 0.015 and `X` is the number of people asked until the first says yes. Mathlib's
`geometricMeasure` counts failures before the first success, so asking exactly ten people is the
value 9 and exactly twenty the value 19: `P(X = 10) = 0.985⁹ · 0.015 ∈ (0.01309, 0.0131)` and
`P(X = 20) = 0.985¹⁹ · 0.015 ∈ (0.01125, 0.01126)`. -/
@[kb "openstaxintrostats2e" "Example 4.21, p. 259"]
theorem example_4_21_ask_until_cancer_probabilities :
    let p : unitInterval := ⟨0.015, by norm_num⟩
    (geometricMeasure p).real {9} = 0.985 ^ 9 * 0.015 ∧
      (0.01309 < (geometricMeasure p).real {9} ∧ (geometricMeasure p).real {9} < 0.0131) ∧
      (geometricMeasure p).real {19} = 0.985 ^ 19 * 0.015 ∧
      (0.01125 < (geometricMeasure p).real {19} ∧ (geometricMeasure p).real {19} < 0.01126) := by
  intro p
  have hp : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p] at this
  have h1 : (geometricMeasure p).real {9} = 0.985 ^ 9 * 0.015 := by
    rw [geometricMeasure_real_singleton hp]
    simp only [p]; norm_num
  have h2 : (geometricMeasure p).real {19} = 0.985 ^ 19 * 0.015 := by
    rw [geometricMeasure_real_singleton hp]
    simp only [p]; norm_num
  refine ⟨h1, ⟨by rw [h1]; norm_num, by rw [h1]; norm_num⟩, h2,
    ⟨by rw [h2]; norm_num, by rw [h2]; norm_num⟩⟩

/-- OpenStax Introductory Statistics 2e Example 4.21 (mean and standard deviation). For the
number of people asked until the first cancer report, with success probability 0.015, the mean is
`1/p = 200/3` (about 66.7), the variance is `(1 - p)/p²` and the standard deviation lies in
`(66.16, 66.17)`. -/
@[kb "openstaxintrostats2e" "Example 4.21, p. 259"]
theorem example_4_21_ask_until_cancer_mean_sd :
    let p : unitInterval := ⟨0.015, by norm_num⟩
    ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 200 / 3 ∧
      variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p) = 0.985 / 0.015 ^ 2 ∧
      (66.16 < Real.sqrt (variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p)) ∧
        Real.sqrt (variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p)) < 66.17) := by
  intro p
  have hp : p ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [p] at this
  have hv : variance (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure p) = 0.985 / 0.015 ^ 2 := by
    rw [UndergradKB.Statistics.variance_geometricMeasure_trials hp]
    simp only [p]; norm_num
  refine ⟨?_, hv, ?_, ?_⟩
  · rw [UndergradKB.Statistics.integral_geometricMeasure_trials hp]
    simp only [p]; norm_num
  · rw [hv, Real.lt_sqrt (by norm_num)]; norm_num
  · rw [hv, Real.sqrt_lt' (by norm_num)]; norm_num

/-- OpenStax Introductory Statistics 2e Example 4.22. A dish holds 100 jelly beans and 80 gumdrops
and 50 candies are drawn: the probability that exactly 35 are gumdrops is the hypergeometric value
`C(80,35) C(100,15) / C(180,50)`, which lies in `(0.0000143, 0.0000144)`. -/
@[kb "openstaxintrostats2e" "Example 4.22, p. 260"]
theorem example_4_22_gumdrops_in_sample :
    UndergradKB.Statistics.hypergeometricPMF 80 100 50 35 =
      (Nat.choose 80 35 : ℝ) * (Nat.choose 100 15 : ℝ) / (Nat.choose 180 50 : ℝ) ∧
      (0.0000143 < UndergradKB.Statistics.hypergeometricPMF 80 100 50 35 ∧
        UndergradKB.Statistics.hypergeometricPMF 80 100 50 35 < 0.0000144) := by
  have h : UndergradKB.Statistics.hypergeometricPMF 80 100 50 35 =
      (Nat.choose 80 35 : ℝ) * (Nat.choose 100 15 : ℝ) / (Nat.choose 180 50 : ℝ) := by
    rfl
  refine ⟨h, ?_⟩
  rw [h]
  simp only [choose_real]
  constructor <;> norm_num [Nat.descFactorial, Nat.factorial]

/-- OpenStax Introductory Statistics 2e Example 4.23. A shipment of 100 laptops has 10 defective and
12 are inspected: the probability of at most two defective ones is
`h(0) + h(1) + h(2)` for the hypergeometric law with 10 defective, 90 good and a sample of 12,
which lies in `(0.9018, 0.9019)`. -/
@[kb "openstaxintrostats2e" "Example 4.23, p. 260"]
theorem example_4_23_at_most_two_defective :
    0.9018 < UndergradKB.Statistics.hypergeometricPMF 10 90 12 0 +
      UndergradKB.Statistics.hypergeometricPMF 10 90 12 1 +
      UndergradKB.Statistics.hypergeometricPMF 10 90 12 2 ∧
    UndergradKB.Statistics.hypergeometricPMF 10 90 12 0 +
      UndergradKB.Statistics.hypergeometricPMF 10 90 12 1 +
      UndergradKB.Statistics.hypergeometricPMF 10 90 12 2 < 0.9019 := by
  simp only [UndergradKB.Statistics.hypergeometricPMF, choose_real]
  constructor <;> norm_num [Nat.descFactorial, Nat.factorial]

/-- OpenStax Introductory Statistics 2e Example 4.31 (exactly two). Text messages average 41.5 per
day, i.e. `λ = 41.5/24 = 83/48` (about 1.7292) per hour: the probability of exactly two in an hour
is `e^(-λ) λ²/2`, which lies in `(0.26525, 0.26535)` (the book's 0.2653). -/
@[kb "openstaxintrostats2e" "Example 4.31, p. 266"]
theorem example_4_31_two_messages_per_hour :
    (poissonMeasure (83 / 48)).real {2} = Real.exp (-(83 / 48)) * (83 / 48) ^ 2 / 2 ∧
      (0.26525 < (poissonMeasure (83 / 48)).real {2} ∧
        (poissonMeasure (83 / 48)).real {2} < 0.26535) := by
  have h : (poissonMeasure (83 / 48)).real {2} = Real.exp (-(83 / 48)) * (83 / 48) ^ 2 / 2 := by
    rw [poissonMeasure_real_singleton]
    simp [Nat.factorial]
  have hb := exp_in (t := -(83 / 48)) (x := -(83 / 96)) (lo := 0.421226) (hi := 0.421228) 2
    (by norm_num) (by rw [abs_neg]; norm_num) (by norm_num)
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
        norm_num [abs_of_neg])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
        norm_num [abs_of_neg])
  refine ⟨h, ?_, ?_⟩ <;> rw [h]
  · nlinarith [hb.1]
  · nlinarith [hb.2]

/-- OpenStax Introductory Statistics 2e Example 4.31 (more than two). With the same rate
`λ = 83/48`, `P(X > 2) = 1 - e^(-λ) (1 + λ + λ²/2)` lies in `(0.25049, 0.25051)` (the book's
0.2505, from `1 - 0.7495`). -/
@[kb "openstaxintrostats2e" "Example 4.31, p. 266"]
theorem example_4_31_more_than_two_messages :
    (poissonMeasure (83 / 48)).real (Set.Ioi 2) =
        1 - Real.exp (-(83 / 48)) * (1 + 83 / 48 + (83 / 48) ^ 2 / 2) ∧
      (0.25049 < (poissonMeasure (83 / 48)).real (Set.Ioi 2) ∧
        (poissonMeasure (83 / 48)).real (Set.Ioi 2) < 0.25051) := by
  have h : (poissonMeasure (83 / 48)).real (Set.Ioi 2) =
      1 - Real.exp (-(83 / 48)) * (1 + 83 / 48 + (83 / 48) ^ 2 / 2) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, real_Iic]
    simp [Finset.sum_range_succ, poissonMeasure_real_singleton, Nat.factorial]
    ring
  have hb := exp_in (t := -(83 / 48)) (x := -(83 / 96)) (lo := 0.421226) (hi := 0.421228) 2
    (by norm_num) (by rw [abs_neg]; norm_num) (by norm_num)
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
        norm_num [abs_of_neg])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
        norm_num [abs_of_neg])
  refine ⟨h, ?_, ?_⟩ <;> rw [h]
  · nlinarith [hb.2]
  · nlinarith [hb.1]

/-- OpenStax Introductory Statistics 2e Example 4.32. Low seismic activity has probability 0.0102 on
each of 200 days. The binomial probability of exactly ten such days is
`C(200,10) (0.0102)^10 (0.9898)^190`, in `(0.0000389, 0.0000391)` (the book's 0.000039); the Poisson
approximation with mean `200 · 0.0102 = 2.04` gives `e^(-2.04) 2.04^10 / 10!`, in
`(0.0000447, 0.0000448)` (the book's 0.000045); the two differ by less than `0.00001`. -/
@[kb "openstaxintrostats2e" "Example 4.32, p. 266"]
theorem example_4_32_binomial_versus_poisson :
    let p : unitInterval := ⟨0.0102, by norm_num⟩
    (0.0000389 < Bin(200, p).real {10} ∧ Bin(200, p).real {10} < 0.0000391) ∧
      (0.0000447 < (poissonMeasure 2.04).real {10} ∧ (poissonMeasure 2.04).real {10} < 0.0000448) ∧
      |Bin(200, p).real {10} - (poissonMeasure 2.04).real {10}| < 0.00001 := by
  intro p
  have hb : Bin(200, p).real {10} =
      (Nat.choose 200 10 : ℝ) * (0.0102 : ℝ) ^ 10 * (1 - 0.0102) ^ 190 := by
    rw [binomial_real_singleton]
  have hb2 : 0.0000389 < Bin(200, p).real {10} ∧ Bin(200, p).real {10} < 0.0000391 := by
    rw [hb, choose_real]
    constructor <;> norm_num [Nat.descFactorial, Nat.factorial]
  have hp : (poissonMeasure 2.04).real {10} = Real.exp (-2.04) * 2.04 ^ 10 / 3628800 := by
    rw [poissonMeasure_real_singleton]
    simp [Nat.factorial]
  have he := exp_in (t := -2.04) (x := -0.68) (lo := 0.506616) (hi := 0.506618) 3
    (by norm_num) (by rw [abs_neg]; norm_num) (by norm_num)
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
        norm_num [abs_of_neg])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
        norm_num [abs_of_neg])
  have hp2 : 0.0000447 < (poissonMeasure 2.04).real {10} ∧
      (poissonMeasure 2.04).real {10} < 0.0000448 := by
    rw [hp]
    constructor
    · nlinarith [he.1]
    · nlinarith [he.2]
  refine ⟨hb2, hp2, ?_⟩
  rw [abs_lt]
  constructor <;> linarith [hb2.1, hb2.2, hp2.1, hp2.2]

end Chapter4

section Chapter5

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

private lemma unif_real {a b : ℝ} (hX : pdf.IsUniform X (Set.Icc a b) P) (hab : a < b) {c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    P.real {ω | c < X ω ∧ X ω < d} = (d - c) / (b - a) := by
  rw [measureReal_def, UndergradKB.Statistics.uniform_prob_Ioo hX hab hac hcd hdb,
    ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

/-- OpenStax Introductory Statistics 2e Example 5.1. A variable `X` uniform on `[0, 20]` has the
constant density `1/20`, so interval probabilities are base times height: `P(0 < X < 2) = 0.1`,
`P(4 < X < 15) = 0.55`, `P(2.3 < X < 12.7) = 0.52`, and a single point has probability
`P(X = 15) = 0`. -/
@[kb "openstaxintrostats2e" "Example 5.1, p. 305"]
theorem example_5_1_uniform_zero_to_twenty (hX : pdf.IsUniform X (Set.Icc 0 20) P) :
    P.real {ω | 0 < X ω ∧ X ω < 2} = 0.1 ∧ P.real {ω | 4 < X ω ∧ X ω < 15} = 0.55 ∧
      P.real {ω | 2.3 < X ω ∧ X ω < 12.7} = 0.52 ∧ P.real {ω | X ω = 15} = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · rw [unif_real hX (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num
  · have h := HasLaw.measure_eq hX (p := fun y => y = 15) (measurableSet_singleton 15)
    rw [measureReal_def]
    have h0 : P {ω | X ω = 15} = 0 := by
      rw [h, cond_apply measurableSet_Icc]
      have : (volume : Measure ℝ) (Set.Icc 0 20 ∩ {x | x = 15}) = 0 :=
        measure_mono_null Set.inter_subset_right (by simp)
      rw [this]; simp
    rw [h0]; rfl

end Chapter5

end UndergradKB.Statistics.Course.ExamplesC2C5b
