import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete

/-! # Probability: school-level worked examples, part C (Grinstead–Snell, chapters 1 to 4)

A die and its even faces (Examples 1.6, 1.8), two coin tosses (Examples 1.7, 3.14), the dart density
`2r` (Example 2.12), the binomial test of Example 3.11 (exact arithmetic), a life table
(Example 4.2) and smoking and cancer (Example 4.13). -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Probability

/-! ## Examples 1.6 and 1.8: one roll of a die (PR-187) -/

/-- Grinstead–Snell Example 1.6 and Example 1.8 (PR-187). For one roll of a fair die (faces
`i + 1`, `i : Fin 6`, uniform measure) every face has weight `1/6`, and the event that the outcome
is even has probability `1/2`. -/
@[kb "grinsteadsnell2006" "Example 1.8, p. 28"]
theorem die_even_half :
    (∀ i : Fin 6, (uniformOn (Set.univ : Set (Fin 6)) {i}).toReal = 1 / 6) ∧
    (uniformOn (Set.univ : Set (Fin 6)) {i | ((i : ℕ) + 1) % 2 = 0}).toReal = 1 / 2 := by
  refine ⟨fun i => ?_, ?_⟩
  · have := uniform_real ({i} : Finset (Fin 6))
    simpa using this
  · rw [uniform_real_pred]
    have : (Finset.univ.filter (fun i : Fin 6 => ((i : ℕ) + 1) % 2 = 0)).card = 3 := by decide
    rw [this]
    norm_num

/-! ## Examples 1.7 and 3.14: two tosses of a coin (PR-188) -/

/-- The number of heads in two tosses (`true` is heads). -/
def tossHeads (ω : Bool × Bool) : ℕ := (if ω.1 then 1 else 0) + (if ω.2 then 1 else 0)

/-- Grinstead–Snell Example 1.7 and Example 3.14 (PR-188). Two tosses of a fair coin recorded in
order are the uniform measure on `Bool × Bool` (weight `1/4` each); at least one head has
probability `3/4`, heads on the first toss has probability `1/2`, and the number of heads takes the
values `0, 1, 2` with probabilities `1/4, 1/2, 1/4`, which is not the uniform law `1/3` on
`{0, 1, 2}`. -/
@[kb "grinsteadsnell2006" "Example 3.14, p. 115"]
theorem two_tosses_law :
    (∀ ω : Bool × Bool, (uniformOn (Set.univ : Set (Bool × Bool)) {ω}).toReal = 1 / 4) ∧
    (uniformOn (Set.univ : Set (Bool × Bool)) {ω | ω.1 = true ∨ ω.2 = true}).toReal = 3 / 4 ∧
    (uniformOn (Set.univ : Set (Bool × Bool)) {ω | ω.1 = true}).toReal = 1 / 2 ∧
    (uniformOn (Set.univ : Set (Bool × Bool)) {ω | tossHeads ω = 0}).toReal = 1 / 4 ∧
    (uniformOn (Set.univ : Set (Bool × Bool)) {ω | tossHeads ω = 1}).toReal = 1 / 2 ∧
    (uniformOn (Set.univ : Set (Bool × Bool)) {ω | tossHeads ω = 2}).toReal = 1 / 4 ∧
    (uniformOn (Set.univ : Set (Bool × Bool)) {ω | tossHeads ω = 1}).toReal ≠ 1 / 3 := by
  have hc : Fintype.card (Bool × Bool) = 4 := by decide
  have key : ∀ (p : Bool × Bool → Prop) [DecidablePred p] (n : ℕ),
      (Finset.univ.filter p).card = n →
      (uniformOn (Set.univ : Set (Bool × Bool)) {ω | p ω}).toReal = n / 4 := by
    intro p _ n h
    rw [uniform_real_pred, h, hc]
    norm_num
  refine ⟨fun ω => ?_, key (fun ω => ω.1 = true ∨ ω.2 = true) 3 (by decide),
    (by rw [key (fun ω => ω.1 = true) 2 (by decide)]; norm_num), key (fun ω => tossHeads ω = 0) 1 (by decide),
    (by rw [key (fun ω => tossHeads ω = 1) 2 (by decide)]; norm_num), key (fun ω => tossHeads ω = 2) 1 (by decide), ?_⟩
  · have := uniform_real ({ω} : Finset (Bool × Bool))
    rw [hc] at this
    simpa using this
  · rw [key (fun ω => tossHeads ω = 1) 2 (by decide)]
    norm_num

/-! ## Example 2.12: the dart density `2r` (PR-189) -/

/-- The law of the distance `r` of the dart from the centre: density `2r` on `[0, 1]`. -/
noncomputable def dartRadiusLaw : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity (fun r => ENNReal.ofReal (2 * r))

/-- Grinstead–Snell Example 2.12 (PR-189). For the dart distance with density `2r` on `[0,1]`, the
probability that `a ≤ r ≤ b` is `b² - a²` whenever `0 ≤ a ≤ b ≤ 1` (in particular the total mass is
`1`). -/
@[kb "grinsteadsnell2006" "Example 2.12, p. 68"]
theorem dart_radius_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (dartRadiusLaw (Set.Icc a b)).toReal = b ^ 2 - a ^ 2 := by
  unfold dartRadiusLaw
  rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.2 (Set.Icc_subset_Icc ha hb)]
  have hint : IntegrableOn (fun r : ℝ => 2 * r) (Set.Icc a b) volume :=
    (continuous_const.mul continuous_id).continuousOn.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc a b)] (fun r : ℝ => 2 * r) :=
    ae_restrict_of_forall_mem measurableSet_Icc fun r hr => by
      have := hr.1
      show 0 ≤ 2 * r
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ENNReal.toReal_ofReal
    (integral_nonneg_of_ae hnn)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-! ## Example 3.11: the binomial test (PR-190) -/

/-- `α_m(p) = ∑_{m ≤ k ≤ 100} b(100, p, k)`: the probability of rejecting the null hypothesis when
at least `m` of `100` patients are cured and each is cured with probability `p`. -/
noncomputable def testAlpha (m : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc m 100, (Nat.choose 100 k : ℝ) * p ^ k * (1 - p) ^ (100 - k)

/-- Numerators of `testAlpha m (q/10) * 10^100`, with a kernel-cheap binomial coefficient. -/
def testNum (m q : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc m 100, (Nat.descFactorial 100 k / k.factorial) * q ^ k * (10 - q) ^ (100 - k)

lemma testAlpha_eq (m q : ℕ) (hq : q ≤ 10) :
    testAlpha m (q / 10) = testNum m q / 10 ^ 100 := by
  unfold testAlpha testNum
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ 100 := (Finset.mem_Icc.1 hk).2
  have h10 : (10 : ℝ) ^ 100 = 10 ^ k * 10 ^ (100 - k) := by rw [← pow_add]; congr 1; omega
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_sub hq, h10]
  push_cast
  rw [show (1 : ℝ) - q / 10 = (10 - q) / 10 by ring, div_pow, div_pow]
  field_simp

lemma testAlpha_anti {m n : ℕ} (h : m ≤ n) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    testAlpha n p ≤ testAlpha m p := by
  unfold testAlpha
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left h) fun k _ _ => ?_
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma testNum_69 : testNum 69 6 < 5 * 10 ^ 98 := by unfold testNum; decide +kernel
lemma testNum_68 : 5 * 10 ^ 98 ≤ testNum 68 6 := by unfold testNum; decide +kernel
lemma testNum_73 : 95 * 10 ^ 98 < testNum 73 8 := by unfold testNum; decide +kernel
lemma testNum_74 : testNum 74 8 ≤ 95 * 10 ^ 98 := by unfold testNum; decide +kernel

set_option maxRecDepth 100000 in
/-- Grinstead–Snell Example 3.11 (PR-190). For `n = 100` patients, the type 1 error `α_m(.6)`
(rejecting `p = .6` although it is true) is `< .05` exactly when `m ≥ 69`, and the type 2 error
`1 - α_m(.8)` is `< .05` (that is `α_m(.8) > .95`) exactly when `m ≤ 73`. So `69` is the smallest
critical value with type 1 error below `.05`, and `73` the largest with type 2 error below `.05`;
the book's numbers are right. -/
@[kb "grinsteadsnell2006" "Example 3.11, p. 109"]
theorem binomial_test_critical_values :
    testAlpha 69 (6 / 10) < 1 / 20 ∧ 1 / 20 ≤ testAlpha 68 (6 / 10) ∧
    1 - testAlpha 73 (8 / 10) < 1 / 20 ∧ 19 / 20 ≥ testAlpha 74 (8 / 10) ∧
    (∀ m, 69 ≤ m → testAlpha m (6 / 10) < 1 / 20) ∧
    (∀ m, m ≤ 68 → 1 / 20 ≤ testAlpha m (6 / 10)) ∧
    (∀ m, m ≤ 73 → 1 - testAlpha m (8 / 10) < 1 / 20) ∧
    (∀ m, 74 ≤ m → 19 / 20 ≥ testAlpha m (8 / 10)) := by
  have e6 := testAlpha_eq 69 6 (by norm_num)
  have e6' := testAlpha_eq 68 6 (by norm_num)
  have e8 := testAlpha_eq 73 8 (by norm_num)
  have e8' := testAlpha_eq 74 8 (by norm_num)
  have h10 : (0 : ℝ) < 10 ^ 100 := by positivity
  have a : testAlpha 69 (6 / 10) < 1 / 20 := by
    have h := testNum_69
    have : (testNum 69 6 : ℝ) < 5 * 10 ^ 98 := by exact_mod_cast h
    have e6 := e6
    push_cast at e6
    rw [e6, div_lt_iff₀ h10]
    linarith
  have b : 1 / 20 ≤ testAlpha 68 (6 / 10) := by
    have : (5 * 10 ^ 98 : ℝ) ≤ testNum 68 6 := by exact_mod_cast testNum_68
    have e6' := e6'
    push_cast at e6'
    rw [e6', le_div_iff₀ h10]
    linarith
  have c : 19 / 20 < testAlpha 73 (8 / 10) := by
    have : (95 * 10 ^ 98 : ℝ) < testNum 73 8 := by exact_mod_cast testNum_73
    have e8 := e8
    push_cast at e8
    rw [e8, lt_div_iff₀ h10]
    linarith
  have d : testAlpha 74 (8 / 10) ≤ 19 / 20 := by
    have : (testNum 74 8 : ℝ) ≤ 95 * 10 ^ 98 := by exact_mod_cast testNum_74
    have e8' := e8'
    push_cast at e8'
    rw [e8', div_le_iff₀ h10]
    linarith
  refine ⟨a, b, by linarith, d, fun m hm => ?_, fun m hm => ?_, fun m hm => ?_, fun m hm => ?_⟩
  · exact lt_of_le_of_lt (testAlpha_anti hm (by norm_num) (by norm_num)) a
  · exact le_trans b (testAlpha_anti hm (by norm_num) (by norm_num))
  · have := testAlpha_anti hm (p := 8 / 10) (by norm_num) (by norm_num)
    linarith
  · exact le_trans (testAlpha_anti hm (by norm_num) (by norm_num)) d

/-! ## Example 4.2: a life table (PR-191) -/

/-- Grinstead–Snell Example 4.2 (PR-191). In a finite population (uniform measure) let `E` be the
women who reach 60 (`89835` of them) and `F ⊆ E` those who reach 80 (`57062` of them); then a woman
of 60 reaches 80 with conditional probability `57062/89835`, which is within `.00005` of `.6352`. -/
@[kb "grinsteadsnell2006" "Example 4.2, p. 141"]
theorem life_table_conditional {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype Ω] (E F : Finset Ω) (hFE : F ⊆ E) (hE : E.card = 89835) (hF : F.card = 57062) :
    ((uniformOn (Set.univ : Set Ω))[(F : Set Ω) | (E : Set Ω)]).toReal = 57062 / 89835 ∧
    |((uniformOn (Set.univ : Set Ω))[(F : Set Ω) | (E : Set Ω)]).toReal - 6352 / 10000|
      < 5 / 100000 := by
  classical
  have h : ((uniformOn (Set.univ : Set Ω))[(F : Set Ω) | (E : Set Ω)]).toReal = 57062 / 89835 := by
    have := uniform_cond_real (Ω := Ω) (fun ω => ω ∈ E) (fun ω => ω ∈ F)
    have e1 : (Finset.univ.filter (fun ω => ω ∈ E ∧ ω ∈ F)) = F := by
      ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hFE h, h⟩⟩
    have e2 : (Finset.univ.filter (fun ω => ω ∈ E)) = E := by ext; simp
    rw [e1, e2, hE, hF] at this
    simpa using this
  refine ⟨h, ?_⟩
  rw [h, abs_lt]
  constructor <;> norm_num

/-! ## Example 4.13: smoking and cancer (PR-192) -/

/-- Cancer indicator on `Fin 60`: persons `0..39` are in cell `(C,S)=(0,0)`, `40..49` in `(0,1)`,
`50..56` in `(1,0)` and `57..59` in `(1,1)` (the counts `40, 10, 7, 3`). -/
def smokeC (i : Fin 60) : ℕ := if 50 ≤ (i : ℕ) then 1 else 0

/-- Smoking indicator on `Fin 60`, with the cells of `smokeC`. -/
def smokeS (i : Fin 60) : ℕ := if (40 ≤ (i : ℕ) ∧ (i : ℕ) < 50) ∨ 57 ≤ (i : ℕ) then 1 else 0

/-- Grinstead–Snell Example 4.13 (PR-192). A person is drawn uniformly from a group of 60 with cell
counts `(C,S) = (0,0): 40, (0,1): 10, (1,0): 7, (1,1): 3`. The joint law is `40/60, 10/60, 7/60,
3/60`, the marginals are `C ~ (50/60, 10/60)` and `S ~ (47/60, 13/60)`, `P(C=1,S=1) = 3/60` differs
from `P(C=1) P(S=1) = (10/60)(13/60)`, so `C` and `S` are not independent, and `P(C=1 | S=1) = 3/13`. -/
@[kb "grinsteadsnell2006" "Example 4.13, p. 151"]
theorem smoking_cancer :
    let P : Set (Fin 60) → ℝ := fun s => (uniformOn (Set.univ : Set (Fin 60)) s).toReal
    (P {i | smokeC i = 0 ∧ smokeS i = 0} = 40 / 60 ∧ P {i | smokeC i = 0 ∧ smokeS i = 1} = 10 / 60 ∧
      P {i | smokeC i = 1 ∧ smokeS i = 0} = 7 / 60 ∧ P {i | smokeC i = 1 ∧ smokeS i = 1} = 3 / 60) ∧
    (P {i | smokeC i = 0} = 50 / 60 ∧ P {i | smokeC i = 1} = 10 / 60) ∧
    (P {i | smokeS i = 0} = 47 / 60 ∧ P {i | smokeS i = 1} = 13 / 60) ∧
    P {i | smokeC i = 1 ∧ smokeS i = 1} ≠ P {i | smokeC i = 1} * P {i | smokeS i = 1} ∧
    ((uniformOn (Set.univ : Set (Fin 60)))[{i | smokeC i = 1} | {i | smokeS i = 1}]).toReal
      = 3 / 13 := by
  intro P
  have hc : Fintype.card (Fin 60) = 60 := by simp
  have key : ∀ (p : Fin 60 → Prop) [DecidablePred p] (n : ℕ),
      (Finset.univ.filter p).card = n → P {ω | p ω} = n / 60 := by
    intro p _ n h
    simp only [P]
    rw [uniform_real_pred, h, hc]
    simp
  have k1 := key (fun i => smokeC i = 0 ∧ smokeS i = 0) 40 (by decide)
  have k2 := key (fun i => smokeC i = 0 ∧ smokeS i = 1) 10 (by decide)
  have k3 := key (fun i => smokeC i = 1 ∧ smokeS i = 0) 7 (by decide)
  have k4 := key (fun i => smokeC i = 1 ∧ smokeS i = 1) 3 (by decide)
  have k5 := key (fun i => smokeC i = 0) 50 (by decide)
  have k6 := key (fun i => smokeC i = 1) 10 (by decide)
  have k7 := key (fun i => smokeS i = 0) 47 (by decide)
  have k8 := key (fun i => smokeS i = 1) 13 (by decide)
  push_cast at k1 k2 k3 k4 k5 k6 k7 k8
  refine ⟨⟨k1, k2, k3, k4⟩, ⟨k5, k6⟩, ⟨k7, k8⟩, ?_, ?_⟩
  · rw [k4, k6, k8]; norm_num
  · rw [uniform_cond_real (fun i => smokeS i = 1) (fun i => smokeC i = 1)]
    have e1 : (Finset.univ.filter (fun i : Fin 60 => smokeS i = 1 ∧ smokeC i = 1)).card = 3 := by
      decide
    have e2 : (Finset.univ.filter (fun i : Fin 60 => smokeS i = 1)).card = 13 := by decide
    rw [e1, e2]
    norm_num

end UndergradKB.Probability
