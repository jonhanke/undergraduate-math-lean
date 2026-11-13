import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.HasLaw
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesExpectation

/-! # Probability: school-level worked examples (Grinstead–Snell, chapters 1, 3, 4, 5, 6, 7)

Bernoulli trials numbers (Examples 3.8, 3.9), conditioning on an event (Examples 4.1, 4.4, 1.9, 4.3,
4.5), the geometric waiting time of a queue (Example 5.1), the sum of two dice (Example 7.1) and the
expected length of a game of craps (Example 6.14). -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal unitInterval

namespace UndergradKB.Probability

/-! ## Examples 3.8 and 3.9: Bernoulli trials numbers (PR-146) -/

/-- The success probability `1/6` of a fair die, as an element of `[0,1]`. -/
noncomputable def sixthProb : unitInterval := ⟨1 / 6, by norm_num, by norm_num⟩

lemma sixthProb_coe : ((sixthProb : unitInterval) : ℝ) = 1 / 6 := rfl

/-- Grinstead–Snell Example 3.8 (PR-146). In six tosses of a fair coin the number of heads has the
binomial law `Bin(6, 1/2)`, and `b(6, 1/2, 3) = 5/16`: exactly three heads has probability `5/16`. -/
@[kb "grinsteadsnell2006" "Example 3.8, p. 106"]
theorem six_tosses_three_heads : (Bin(6, halfProb)).real {3} = 5 / 16 := by
  rw [binomial_real_singleton, halfProb_coe]
  norm_num [Nat.choose]

/-- Grinstead–Snell Example 3.9 (PR-146). In four rolls of a die the number of sixes has the
binomial law `Bin(4, 1/6)`, and `b(4, 1/6, 1) = 125/324`: exactly one six has probability `125/324`. -/
@[kb "grinsteadsnell2006" "Example 3.9, p. 106"]
theorem four_rolls_one_six : (Bin(4, sixthProb)).real {1} = 125 / 324 := by
  rw [binomial_real_singleton, sixthProb_coe]
  norm_num [Nat.choose]

/-! ## Examples 4.1 and 4.4: conditioning on a die roll (PR-147) -/

/-- Grinstead–Snell Example 4.1 and Example 4.4 (PR-147). For one roll of a fair die (faces
`i + 1`, `i : Fin 6`, uniform measure), given that the outcome exceeds 4, the roll is a 6 with
conditional probability `1/2` (and a 5 with probability `1/2`). -/
@[kb "grinsteadsnell2006" "Example 4.4, p. 143"]
theorem die_six_given_exceeds_four :
    (((uniformOn (Set.univ : Set (Fin 6)))[{i | (i : ℕ) + 1 = 6} | {i | 4 < (i : ℕ) + 1}]).toReal
      = 1 / 2) ∧
    (((uniformOn (Set.univ : Set (Fin 6)))[{i | (i : ℕ) + 1 = 5} | {i | 4 < (i : ℕ) + 1}]).toReal
      = 1 / 2) := by
  rw [uniform_cond_real, uniform_cond_real]
  have h1 : (Finset.univ.filter (fun i : Fin 6 => 4 < (i : ℕ) + 1 ∧ (i : ℕ) + 1 = 6)).card = 1 := by
    decide
  have h2 : (Finset.univ.filter (fun i : Fin 6 => 4 < (i : ℕ) + 1 ∧ (i : ℕ) + 1 = 5)).card = 1 := by
    decide
  have h3 : (Finset.univ.filter (fun i : Fin 6 => 4 < (i : ℕ) + 1)).card = 2 := by decide
  rw [h1, h2, h3]
  norm_num

/-! ## Examples 1.9 and 4.3: an election (PR-148) -/

/-- The distribution of Example 1.9 on `Fin 3` (`0 = A`, `1 = B`, `2 = C`): weights `2/5, 2/5, 1/5`. -/
noncomputable def electionPMF : PMF (Fin 3) :=
  natPMF (fun i => ![2, 2, 1] i) 5 (by simp [Fin.sum_univ_three]) (by norm_num)

/-- Grinstead–Snell Example 1.9 (PR-148). If `A` and `B` are equally likely to win and `C` has half
the chance of `A` (`m(A) = m(B) = 2 m(C)`), then `m` is the distribution `2/5, 2/5, 1/5`. -/
@[kb "grinsteadsnell2006" "Example 1.9, p. 28"]
theorem election_distribution (m : PMF (Fin 3)) (hAB : m 0 = m 1) (hAC : m 0 = 2 * m 2) :
    m = electionPMF := by
  have hsum : m 0 + m 1 + m 2 = 1 := by
    have := m.tsum_coe
    rwa [tsum_fintype, Fin.sum_univ_three] at this
  have h5 : 5 * m 2 = 1 := by
    have : m 0 + m 1 + m 2 = 5 * m 2 := by rw [← hAB, hAC]; ring
    rwa [this] at hsum
  have hC : m 2 = 5⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h5)
  have hdiv : ∀ n : ℝ≥0∞, n / 5 = n * 5⁻¹ := fun n => rfl
  ext i
  fin_cases i
  · simp [electionPMF, natPMF, hAC, hC, hdiv]
  · simp [electionPMF, natPMF, ← hAB, hAC, hC, hdiv]
  · simp [electionPMF, natPMF, hC, hdiv]

/-- Grinstead–Snell Example 4.3 (PR-148). In the election of Example 1.9, `P(A) = P(B) = 2/5` and
`P(C) = 1/5`; conditioned on "A does not win", `P(B) = 2/3` and `P(C) = 1/3`. -/
@[kb "grinsteadsnell2006" "Example 4.3, p. 142"]
theorem election_given_A_drops :
    (electionPMF.toMeasure {1}).toReal = 2 / 5 ∧ (electionPMF.toMeasure {2}).toReal = 1 / 5 ∧
    ((electionPMF.toMeasure)[({1} : Set (Fin 3)) | {0}ᶜ]).toReal = 2 / 3 ∧
    ((electionPMF.toMeasure)[({2} : Set (Fin 3)) | {0}ᶜ]).toReal = 1 / 3 := by
  have hs : MeasurableSet (({0} : Set (Fin 3))ᶜ) := MeasurableSet.of_discrete
  have hP : ∀ A : Finset (Fin 3), ((electionPMF.toMeasure (A : Set (Fin 3))).toReal) =
      (∑ ω ∈ A, ((![2, 2, 1] ω : ℕ) : ℝ)) / 5 := fun A => by
    unfold electionPMF
    simpa using natPMF_real (fun i => ![2, 2, 1] i) 5 (by simp [Fin.sum_univ_three])
      (by norm_num) A
  have e1 := hP {1}
  have e2 := hP {2}
  have e4 := hP ({0}ᶜ)
  simp only [Finset.coe_singleton, Finset.sum_singleton] at e1 e2
  have c : (({0}ᶜ : Finset (Fin 3)) : Set (Fin 3)) = ({0} : Set (Fin 3))ᶜ := by
    ext x; simp
  rw [c] at e4
  have cf : (({0}ᶜ : Finset (Fin 3))) = {1, 2} := by decide
  rw [cf] at e4
  have i1 : ({0} : Set (Fin 3))ᶜ ∩ {1} = {1} := by ext x; simp
  have i2 : ({0} : Set (Fin 3))ᶜ ∩ {2} = {2} := by ext x; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; simp
  · rw [e2]; simp
  · rw [cond_real _ hs, i1, e1, e4]
    simp
    norm_num
  · rw [cond_real _ hs, i2, e2, e4]
    simp
    norm_num

/-! ## Example 4.5: two urns (PR-149) -/

/-- The path measure of the two-urn tree, on `Fin 2 × Fin 2` (urn `0 = I`, `1 = II`; ball `0` black,
`1` white), in twentieths: urn I gives `1/2 · 2/5 = 4/20` black and `1/2 · 3/5 = 6/20` white, urn II
gives `1/2 · 1/2 = 5/20` each. -/
noncomputable def urnPMF : PMF (Fin 2 × Fin 2) :=
  natPMF (fun w => ![![4, 6], ![5, 5]] w.1 w.2) 20
    (by simp [Fintype.sum_prod_type, Fin.sum_univ_two]) (by norm_num)

lemma urnPMF_real (p : Fin 2 × Fin 2 → Prop) [DecidablePred p] :
    (urnPMF.toMeasure {w | p w}).toReal =
      (∑ w ∈ univ.filter p, ((![![4, 6], ![5, 5]] w.1 w.2 : ℕ) : ℝ)) / 20 := by
  have := natPMF_real (fun w : Fin 2 × Fin 2 => ![![4, 6], ![5, 5]] w.1 w.2) 20
    (by simp [Fintype.sum_prod_type, Fin.sum_univ_two]) (by norm_num) (univ.filter p)
  unfold urnPMF
  simpa using this

/-- Grinstead–Snell Example 4.5 (PR-149). Choose one of two urns at random (urn I: 2 black, 3 white;
urn II: 1 black, 1 white) and draw a ball from it: `P(black) = 9/20`, and, by Bayes, the probability
that urn I was chosen given a black ball is `P(I | B) = 4/9`. -/
@[kb "grinsteadsnell2006" "Example 4.5, p. 143"]
theorem two_urns :
    (urnPMF.toMeasure {w | w.2 = 0}).toReal = 9 / 20 ∧
    ((urnPMF.toMeasure)[{w | w.1 = 0} | {w | w.2 = 0}]).toReal = 4 / 9 := by
  have hs : MeasurableSet {w : Fin 2 × Fin 2 | w.2 = 0} := MeasurableSet.of_discrete
  have hB := urnPMF_real (fun w => w.2 = 0)
  have hIB := urnPMF_real (fun w => w.2 = 0 ∧ w.1 = 0)
  have hset : {w : Fin 2 × Fin 2 | w.2 = 0} ∩ {w | w.1 = 0} = {w | w.2 = 0 ∧ w.1 = 0} := rfl
  have e1 : (∑ w ∈ univ.filter (fun w : Fin 2 × Fin 2 => w.2 = 0),
      ((![![4, 6], ![5, 5]] w.1 w.2 : ℕ) : ℝ)) = 9 := by
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]; norm_num
  have e2 : (∑ w ∈ univ.filter (fun w : Fin 2 × Fin 2 => w.2 = 0 ∧ w.1 = 0),
      ((![![4, 6], ![5, 5]] w.1 w.2 : ℕ) : ℝ)) = 4 := by
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [e1] at hB
  rw [e2] at hIB
  refine ⟨hB, ?_⟩
  rw [cond_real _ hs, hset, hIB, hB]
  norm_num

/-! ## Example 5.1: a queue, geometric waiting time (PR-150) -/

/-- The waiting time `T ≥ 1` until the next arrival when an arrival occurs in each time unit with
probability `p`: `P(T = j) = q^(j-1) p`, i.e. Mathlib's geometric law of the number of failures,
shifted by one. -/
noncomputable def waitingLaw (p : unitInterval) : Measure ℕ := (geometricMeasure p).map Nat.succ

instance (p : unitInterval) : IsProbabilityMeasure (waitingLaw p) := by
  unfold waitingLaw; infer_instance

lemma waitingLaw_real (p : unitInterval) (s : Set ℕ) :
    (waitingLaw p).real s = (geometricMeasure p).real (Nat.succ ⁻¹' s) := by
  rw [waitingLaw, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]

lemma geometric_lt_real {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    (geometricMeasure p).real {n | n < k} = 1 - (1 - (p : ℝ)) ^ k := by
  have h := sum_measureReal_singleton (μ := geometricMeasure p) (Finset.range k)
  have hset : (↑(Finset.range k) : Set ℕ) = {n | n < k} := by ext; simp
  rw [hset] at h
  rw [← h]
  simp only [geometricMeasure_real_singleton hp]
  have hp' : (p : ℝ) ≠ 0 := fun h0 => hp (Subtype.ext h0)
  have := mul_neg_geom_sum (1 - (p : ℝ)) k
  rw [← Finset.sum_mul]
  have e : (1 - (1 - (p : ℝ))) = p := by ring
  rw [e] at this
  linarith [mul_comm (∑ i ∈ range k, (1 - (p : ℝ)) ^ i) (p : ℝ)]

/-- Grinstead–Snell Example 5.1 (PR-150). If an arrival occurs in each time unit with probability
`p > 0` (`q = 1 - p`) and `T` is the time until the next arrival, `P(T = j) = q^(j-1) p`, then
`P(T > k) = q^k`: no arrival in the first `k` time units. -/
@[kb "grinsteadsnell2006" "Example 5.1, p. 194"]
theorem queue_no_arrival {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    (waitingLaw p).real {j | k < j} = (1 - (p : ℝ)) ^ k := by
  rw [waitingLaw_real]
  have hc : Nat.succ ⁻¹' {j | k < j} = {n | n < k}ᶜ := by ext n; simp
  rw [hc, probReal_compl_eq_one_sub MeasurableSet.of_discrete, geometric_lt_real hp]
  ring

/-- Grinstead–Snell Example 5.1 (PR-150), random-variable form: if the arrival time `T` has the law
`waitingLaw p` under `P` then `P(T > k) = q^k`. -/
@[kb "grinsteadsnell2006" "Example 5.1, p. 194"]
theorem queue_no_arrival_rv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Ω → ℕ}
    {p : unitInterval} (hp : p ≠ 0) (hT : HasLaw T (waitingLaw p) P) (k : ℕ) :
    P.real {ω | k < T ω} = (1 - (p : ℝ)) ^ k := by
  rw [← queue_no_arrival hp k, ← hT.map_eq, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hT.aemeasurable MeasurableSet.of_discrete]
  rfl

/-- Grinstead–Snell Example 5.1 (PR-150), memoryless property. For `0 < p < 1`,
`P(T > r + s | T > r) = q^(r+s) / q^r = q^s`, independent of `r`. -/
@[kb "grinsteadsnell2006" "Example 5.1, p. 194"]
theorem queue_memoryless {p : unitInterval} (hp : p ≠ 0) (hp1 : p ≠ 1) (r s : ℕ) :
    (((waitingLaw p)[{j | r + s < j} | {j | r < j}]).toReal) = (1 - (p : ℝ)) ^ s := by
  have hs : MeasurableSet {j : ℕ | r < j} := MeasurableSet.of_discrete
  have hq : (1 - (p : ℝ)) ≠ 0 := by
    intro h0
    apply hp1
    have h1 : (p : ℝ) = 1 := by linarith
    exact Subtype.ext (by simpa using h1)
  have hsub : {j : ℕ | r < j} ∩ {j | r + s < j} = {j | r + s < j} := by
    ext j; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; omega
  rw [cond_real _ hs, hsub]
  have h1 := queue_no_arrival hp (r + s)
  have h2 := queue_no_arrival hp r
  rw [measureReal_def] at h1 h2
  rw [h1, h2, pow_add]
  field_simp

/-! ## Example 7.1: the sum of two dice (PR-151) -/

/-- Grinstead–Snell Example 7.1 (PR-151). For two rolls of a fair die (uniform measure on
`Fin 6 × Fin 6`, faces `i + 1` and `j + 1`) the sum `S₂` takes the value `k` with probability
`(6 - |k - 7|) / 36` for `k = 2, …, 12`, and every other value with probability `0`. -/
@[kb "grinsteadsnell2006" "Example 7.1, p. 294"]
theorem two_dice_sum_distribution :
    (∀ k : ℕ, 2 ≤ k → k ≤ 12 →
      (uniformOn (Set.univ : Set (Fin 6 × Fin 6))
        {w | (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = k}).toReal = (6 - |(k : ℝ) - 7|) / 36) ∧
    (∀ k : ℕ, (k < 2 ∨ 12 < k) →
      (uniformOn (Set.univ : Set (Fin 6 × Fin 6))
        {w | (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = k}).toReal = 0) := by
  refine ⟨fun k h2 h12 => ?_, fun k hk => ?_⟩
  · rw [uniform_real_pred]
    have counts : ∀ k ∈ Finset.Icc 2 12, (Finset.univ.filter (fun w : Fin 6 × Fin 6 =>
        (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = k)).card = 6 - ((k : ℤ) - 7).natAbs := by decide
    rw [counts k (Finset.mem_Icc.2 ⟨h2, h12⟩)]
    simp only [Fintype.card_prod, Fintype.card_fin]
    interval_cases k <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  · rw [uniform_real_pred]
    have : (Finset.univ.filter (fun w : Fin 6 × Fin 6 =>
        (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = k)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _
      have := w.1.isLt
      have := w.2.isLt
      omega
    rw [this]; simp

/-! ## Example 6.14: expected number of rolls in craps (PR-152) -/

/-- Grinstead–Snell Example 6.14 (PR-152), geometric mean (from Example 6.4). The number `S = N + 1` of trials
up to and including the first success, when each trial succeeds with probability `p > 0`, has mean
`E(S) = 1/p` (here `N` is Mathlib's geometric variable counting the failures). -/
@[kb "grinsteadsnell2006" "Example 6.14, p. 248"]
theorem geometric_waiting_mean {p : unitInterval} (hp : p ≠ 0) :
    ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = 1 / (p : ℝ) := by
  have hp' : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  have h1 : ‖1 - (p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith [p.2.2]
  rw [integral_geometricMeasure hp]
  simp only [smul_eq_mul]
  have hs1 := (hasSum_coe_mul_geometric_of_norm_lt_one h1).summable
  have hs2 := (hasSum_geometric_of_norm_lt_one h1).summable
  have : ∀ n : ℕ, (1 - (p : ℝ)) ^ n * p * ((n : ℝ) + 1)
      = p * (n * (1 - (p : ℝ)) ^ n) + p * (1 - (p : ℝ)) ^ n := by
    intro n; ring
  simp_rw [this]
  rw [Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one h1, tsum_geometric_of_norm_lt_one h1]
  have e : (1 - (1 - (p : ℝ))) = p := by ring
  rw [e]
  field_simp
  ring

/-- Expected number of rolls in one play of craps by the book's two-stage conditioning
`E(T) = ∑ⱼ E(T | X = j) P(X = j)`: `E(T | X = j) = 1` if the first roll `j` ends the play, and
`1 + 1 / (P(j) + P(7))` if `j` is a point (the second stage is a geometric waiting time with
parameter `P(j) + P(7)`). -/
def crapsExpectedRolls : ℚ :=
  ∑ j ∈ Finset.Icc 2 12, diceSumProb j *
    (if j ∈ crapsPoints then 1 + 1 / (diceSumProb j + diceSumProb 7) else 1)

/-- Grinstead–Snell Example 6.14 (PR-152). The expected number of rolls in a single play of craps is
`557/165`; the point-stage conditional means come from the geometric mean `1/p`
(`geometric_waiting_mean`) with `p = P(point) + P(7)`; see `craps_second_stage_mean`. -/
@[kb "grinsteadsnell2006" "Example 6.14, p. 248"]
theorem craps_expected_rolls : crapsExpectedRolls = 557 / 165 := by
  have h2 : diceSumProb 2 = 1 / 36 := by decide +kernel
  have h3 : diceSumProb 3 = 2 / 36 := by decide +kernel
  have h4 : diceSumProb 4 = 3 / 36 := by decide +kernel
  have h5 : diceSumProb 5 = 4 / 36 := by decide +kernel
  have h6 : diceSumProb 6 = 5 / 36 := by decide +kernel
  have h7 : diceSumProb 7 = 6 / 36 := by decide +kernel
  have h8 : diceSumProb 8 = 5 / 36 := by decide +kernel
  have h9 : diceSumProb 9 = 4 / 36 := by decide +kernel
  have h10 : diceSumProb 10 = 3 / 36 := by decide +kernel
  have h11 : diceSumProb 11 = 2 / 36 := by decide +kernel
  have h12 : diceSumProb 12 = 1 / 36 := by decide +kernel
  simp [crapsExpectedRolls, crapsPoints, Finset.sum_Icc_succ_top, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12]
  norm_num

/-- Grinstead–Snell Example 6.14 (PR-152), second stage. For each point `r`, the number of further
rolls until `r` or `7` shows (a geometric waiting time with parameter `p = P(r) + P(7)`) has mean
`1 / (P(r) + P(7))`. -/
@[kb "grinsteadsnell2006" "Example 6.14, p. 248"]
theorem craps_second_stage_mean (r : ℕ) (hr : r ∈ crapsPoints) (p : unitInterval)
    (hpr : (p : ℝ) = (diceSumProb r : ℝ) + (diceSumProb 7 : ℝ)) :
    ∫ n, ((n : ℝ) + 1) ∂geometricMeasure p = ((1 / (diceSumProb r + diceSumProb 7) : ℚ) : ℝ) := by
  have hpos : 0 < diceSumProb r := by
    simp only [crapsPoints, mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have h7 : (0 : ℚ) ≤ diceSumProb 7 := by decide +kernel
  have hne : p ≠ 0 := by
    intro h0
    have : (p : ℝ) = 0 := by rw [h0]; rfl
    rw [hpr] at this
    have : (0 : ℝ) < (diceSumProb r : ℝ) + (diceSumProb 7 : ℝ) := by
      have a : (0 : ℝ) < (diceSumProb r : ℝ) := by exact_mod_cast hpos
      have b : (0 : ℝ) ≤ (diceSumProb 7 : ℝ) := by exact_mod_cast h7
      linarith
    linarith
  rw [geometric_waiting_mean hne, hpr]
  push_cast
  rfl

end UndergradKB.Probability
