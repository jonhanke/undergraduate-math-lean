import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common.Attr

/-!
# Discrete worked examples (Grinstead–Snell, chapters 1, 3, 4, 6)

Coins, dice, Monty Hall, a false-positive medical test, the two children paradox (counting measures
`uniformOn univ` and a weighted `PMF`, with `ProbabilityTheory.cond`), and the poker counts.
Probabilities are stated through `ENNReal.toReal` so that the rational values can be checked by `norm_num`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Probability

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]

/-- `uniformOn univ` of a finset is its cardinality over the size of the sample space. -/
lemma uniform_real (s : Finset Ω) :
    (uniformOn (Set.univ : Set Ω) (s : Set Ω)).toReal = (#s : ℝ) / Fintype.card Ω := by
  classical
  have h := uniformOn_apply_finset (Ω := Ω) (s := Finset.univ) (t := s)
  rw [Finset.coe_univ] at h
  rw [h, Finset.univ_inter, Finset.card_univ, ENNReal.toReal_div]
  simp

/-- Same for an event given by a decidable predicate. -/
lemma uniform_real_pred (p : Ω → Prop) [DecidablePred p] :
    (uniformOn (Set.univ : Set Ω) {ω | p ω}).toReal =
      (#(Finset.univ.filter p) : ℝ) / Fintype.card Ω := by
  have := uniform_real (Finset.univ.filter p)
  simpa using this

omit [MeasurableSingletonClass Ω] [Fintype Ω] in
/-- Conditional probability for a finite measure, as a real quotient. -/
lemma cond_real (μ : Measure Ω) {s t : Set Ω} (hs : MeasurableSet s) :
    (μ[t | s]).toReal = (μ (s ∩ t)).toReal / (μ s).toReal := by
  rw [cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- Conditional probability for the uniform measure, events given by predicates. -/
lemma uniform_cond_real (p q : Ω → Prop) [DecidablePred p] [DecidablePred q] :
    ((uniformOn (Set.univ : Set Ω))[{ω | q ω} | {ω | p ω}]).toReal =
      (#(Finset.univ.filter (fun ω => p ω ∧ q ω)) : ℝ) / #(Finset.univ.filter p) := by
  have hs : MeasurableSet {ω | p ω} := (Set.toFinite _).measurableSet
  rw [cond_real _ hs]
  have h1 := uniform_real_pred (Ω := Ω) (fun ω => p ω ∧ q ω)
  have h2 := uniform_real_pred (Ω := Ω) p
  have : {ω | p ω} ∩ {ω | q ω} = {ω | p ω ∧ q ω} := rfl
  rw [this, h1, h2]
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · simp
  · have : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
    rw [div_div_div_cancel_right₀ this]

/-- Expectation under the uniform measure is the average. -/
lemma uniform_integral (f : Ω → ℝ) :
    ∫ ω, f ω ∂(uniformOn (Set.univ : Set Ω)) = (∑ ω, f ω) / Fintype.card Ω := by
  classical
  rw [integral_fintype _]
  simp only [measureReal_def]
  have : ∀ ω : Ω, (uniformOn (Set.univ : Set Ω) {ω}).toReal = 1 / Fintype.card Ω := by
    intro ω
    have := uniform_real ({ω} : Finset Ω)
    simpa using this
  simp only [this, smul_eq_mul]
  rw [← Finset.mul_sum]
  · ring
  · exact Integrable.of_finite

/-- A probability mass function with weights `n ω / D` (natural numerators summing to `D`). -/
noncomputable def natPMF (n : Ω → ℕ) (D : ℕ) (h : ∑ ω, n ω = D) (h0 : D ≠ 0) : PMF Ω :=
  PMF.ofFintype (fun ω => (n ω : ℝ≥0∞) / D) (by
    rw [← ENNReal.sum_div, ← Nat.cast_sum, h, ENNReal.div_self] <;> simp [h0])

lemma natPMF_real (n : Ω → ℕ) (D : ℕ) (h : ∑ ω, n ω = D) (h0 : D ≠ 0) (A : Finset Ω) :
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

end Helpers

/-! ### Three tosses of a fair coin (PR-130) -/

/-- Outcomes of three coin tosses; `true` is heads. -/
abbrev Tosses3 := Fin 3 → Bool

/-- Number of heads. -/
def heads3 (x : Tosses3) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- Number of runs: one more than the number of changes between consecutive tosses. -/
def runs3 (x : Tosses3) : ℕ :=
  1 + (if x 0 ≠ x 1 then 1 else 0) + (if x 1 ≠ x 2 then 1 else 0)

/-- Grinstead–Snell Example 1.10 (PR-130). Under the uniform distribution on the 8 outcomes of three
tosses each outcome has probability 1/8, no head (`TTT`) has probability 1/8, and so at least one head
(the complement, Property 5) has probability 7/8. The checklist row's "at least one head 7/8" is the
book's computation via the complement. -/
@[kb "grinsteadsnell2006" "Example 1.10, p. 32"]
theorem threeTosses_prob :
    (∀ x : Tosses3, (uniformOn (Set.univ : Set Tosses3) {x}).toReal = 1 / 8) ∧
    (uniformOn (Set.univ : Set Tosses3) {x | ∀ i, x i = false}).toReal = 1 / 8 ∧
    (uniformOn (Set.univ : Set Tosses3) {x | ∃ i, x i = true}).toReal = 7 / 8 := by
  have hc : Fintype.card Tosses3 = 8 := by simp
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have := uniform_real ({x} : Finset Tosses3)
    simpa [hc] using this
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun x : Tosses3 => ∀ i, x i = false)).card = 1 := by decide
    rw [this]; norm_num
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun x : Tosses3 => ∃ i, x i = true)).card = 7 := by decide
    rw [this]; norm_num

/-- Grinstead–Snell Example 6.1 (PR-130). The expected number of heads in three fair tosses is 3/2. -/
@[kb "grinsteadsnell2006" "Example 6.1, p. 234"]
theorem threeTosses_expected_heads :
    ∫ x, (heads3 x : ℝ) ∂(uniformOn (Set.univ : Set Tosses3)) = 3 / 2 := by
  rw [uniform_integral]
  have : ∑ x : Tosses3, (heads3 x : ℝ) = 12 := by
    have : ∑ x : Tosses3, heads3 x = 12 := by decide
    exact_mod_cast this
  rw [this]; simp; norm_num

/-- Grinstead–Snell Example 6.6 (PR-130). The expected number of runs in three fair tosses is 2 (the
book finds the distribution `m(1)=1/4, m(2)=1/2, m(3)=1/4`; we give the distribution and the mean). -/
@[kb "grinsteadsnell2006" "Example 6.6, p. 237"]
theorem threeTosses_expected_runs :
    (uniformOn (Set.univ : Set Tosses3) {x | runs3 x = 1}).toReal = 1 / 4 ∧
    (uniformOn (Set.univ : Set Tosses3) {x | runs3 x = 2}).toReal = 1 / 2 ∧
    (uniformOn (Set.univ : Set Tosses3) {x | runs3 x = 3}).toReal = 1 / 4 ∧
    ∫ x, (runs3 x : ℝ) ∂(uniformOn (Set.univ : Set Tosses3)) = 2 := by
  have hc : Fintype.card Tosses3 = 8 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun x : Tosses3 => runs3 x = 1)).card = 2 := by decide
    rw [this]; norm_num
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun x : Tosses3 => runs3 x = 2)).card = 4 := by decide
    rw [this]; norm_num
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun x : Tosses3 => runs3 x = 3)).card = 2 := by decide
    rw [this]; norm_num
  · rw [uniform_integral, hc]
    have : ∑ x : Tosses3, (runs3 x : ℝ) = 16 := by
      have : ∑ x : Tosses3, runs3 x = 16 := by decide
      exact_mod_cast this
    rw [this]; norm_num

/-! ### A pair of dice (PR-131) -/

/-- Outcomes of rolling two dice: `(i, j)` stands for faces `i+1`, `j+1`. -/
abbrev Dice2 := Fin 6 × Fin 6

/-- Grinstead–Snell Example 1.11 (PR-131). With the uniform distribution on the 36 ordered pairs, each
pair has probability 1/36, a sum of 7 has probability 1/6, a sum of 11 has probability 1/18, and neither
snake eyes nor boxcars has probability 17/18 (the book's three computations). -/
@[kb "grinsteadsnell2006" "Example 1.11, p. 34"]
theorem twoDice_prob :
    (∀ w : Dice2, (uniformOn (Set.univ : Set Dice2) {w}).toReal = 1 / 36) ∧
    (uniformOn (Set.univ : Set Dice2) {w | (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = 7}).toReal = 1 / 6 ∧
    (uniformOn (Set.univ : Set Dice2) {w | (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = 11}).toReal = 1 / 18 ∧
    (uniformOn (Set.univ : Set Dice2) {w | ¬ (w = (0, 0) ∨ w = (5, 5))}).toReal = 17 / 18 := by
  have hc : Fintype.card Dice2 = 36 := by simp
  refine ⟨fun w => ?_, ?_, ?_, ?_⟩
  · have := uniform_real ({w} : Finset Dice2)
    simpa [hc] using this
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun w : Dice2 => (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = 7)).card = 6 := by
      decide
    rw [this]; norm_num
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun w : Dice2 => (w.1 : ℕ) + 1 + ((w.2 : ℕ) + 1) = 11)).card = 2 := by
      decide
    rw [this]; norm_num
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun w : Dice2 => ¬ (w = (0, 0) ∨ w = (5, 5)))).card = 34 := by
      decide
    rw [this]; norm_num

/-! ### Monty Hall (PR-133) -/

/-- The Monty Hall model of the book: the car is behind door `c`, the contestant picks door `p`, and a
fair coin `b` is the host's choice when he has two goat doors to open. Doors are `0,1,2` (door `k+1`).
All `3 * 3 * 2 = 18` triples are equally likely: car `1/3`, pick `1/3`, coin `1/2`. -/
abbrev Monty := Fin 3 × Fin 3 × Bool

/-- The door opened by the host: the unique remaining door if the contestant missed the car (the three
doors sum to `0` modulo `3`), otherwise one of the other two according to the coin. -/
def montyOpen (w : Monty) : Fin 3 :=
  if w.1 = w.2.1 then (if w.2.2 then w.2.1 + 1 else w.2.1 + 2) else -(w.1 + w.2.1)

/-- Grinstead–Snell Example 4.6 (PR-133). In the book's model the host always opens a goat door that is
not the contestant's: the "stay" strategy wins with probability 1/3, the "switch" strategy with
probability 2/3. -/
@[kb "grinsteadsnell2006" "Example 4.6, p. 144"]
theorem monty_stay_switch :
    (∀ w : Monty, montyOpen w ≠ w.2.1 ∧ montyOpen w ≠ w.1) ∧
    (uniformOn (Set.univ : Set Monty) {w | w.1 = w.2.1}).toReal = 1 / 3 ∧
    (uniformOn (Set.univ : Set Monty) {w | w.1 ≠ w.2.1}).toReal = 2 / 3 := by
  have hc : Fintype.card Monty = 18 := by simp
  refine ⟨by decide, ?_, ?_⟩
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun w : Monty => w.1 = w.2.1)).card = 6 := by decide
    rw [this]; norm_num
  · rw [uniform_real_pred, hc]
    have : (Finset.univ.filter (fun w : Monty => w.1 ≠ w.2.1)).card = 12 := by decide
    rw [this]; norm_num

/-- Grinstead–Snell Example 4.6 (PR-133), Craig's question. Given that the contestant picked door 1 and
Monty opened door 3, switching (to door 2, where the car is) wins with conditional probability 2/3 and
staying wins with conditional probability 1/3. -/
@[kb "grinsteadsnell2006" "Example 4.6, p. 144"]
theorem monty_conditional :
    ((uniformOn (Set.univ : Set Monty))[{w | w.1 = 1} |
        {w | w.2.1 = 0 ∧ montyOpen w = 2}]).toReal = 2 / 3 ∧
    ((uniformOn (Set.univ : Set Monty))[{w | w.1 = 0} |
        {w | w.2.1 = 0 ∧ montyOpen w = 2}]).toReal = 1 / 3 := by
  constructor
  · rw [uniform_cond_real]
    have h1 : (Finset.univ.filter (fun w : Monty => (w.2.1 = 0 ∧ montyOpen w = 2) ∧ w.1 = 1)).card
        = 2 := by decide
    have h2 : (Finset.univ.filter (fun w : Monty => w.2.1 = 0 ∧ montyOpen w = 2)).card = 3 := by
      decide
    rw [h1, h2]; norm_num
  · rw [uniform_cond_real]
    have h1 : (Finset.univ.filter (fun w : Monty => (w.2.1 = 0 ∧ montyOpen w = 2) ∧ w.1 = 0)).card
        = 1 := by decide
    have h2 : (Finset.univ.filter (fun w : Monty => w.2.1 = 0 ∧ montyOpen w = 2)).card = 3 := by
      decide
    rw [h1, h2]; norm_num

/-! ### The false-positive test (PR-134) -/

/-- Weights, over `100000`, of (cancer?, positive?) in Example 4.17: prior `.001`, `P(+|cancer)=.99`,
`P(+|not cancer)=.05`. -/
def testWeight : Bool × Bool → ℕ
  | (true, true) => 99
  | (true, false) => 1
  | (false, true) => 4995
  | (false, false) => 94905

lemma testWeight_sum : ∑ w : Bool × Bool, testWeight w = 100000 := by decide

/-- The joint distribution of (cancer, test positive) from the book's data. -/
noncomputable def testPMF : PMF (Bool × Bool) :=
  natPMF testWeight 100000 testWeight_sum (by norm_num)

/-- Grinstead–Snell Example 4.17 (PR-134). The model reproduces the data (prior `.001`,
`P(+|cancer)=.99`, `P(+|not cancer)=.05`), and `P(cancer | +) = .00099/(.00099+.04995) = 99/5094`
(exactly `11/566`), which lies strictly between `.019` and `.02`. -/
@[kb "grinsteadsnell2006" "Example 4.17, p. 155"]
theorem falsePositive :
    (testPMF.toMeasure {w | w.1 = true}).toReal = 1 / 1000 ∧
    (testPMF.toMeasure[{w | w.2 = true} | {w | w.1 = true}]).toReal = 99 / 100 ∧
    (testPMF.toMeasure[{w | w.2 = true} | {w | w.1 = false}]).toReal = 1 / 20 ∧
    (testPMF.toMeasure[{w | w.1 = true} | {w | w.2 = true}]).toReal = 11 / 566 ∧
    (19 / 1000 : ℝ) < 11 / 566 ∧ (11 / 566 : ℝ) < 2 / 100 := by
  have key : ∀ (A : Finset (Bool × Bool)),
      (testPMF.toMeasure (A : Set (Bool × Bool))).toReal = (∑ w ∈ A, (testWeight w : ℝ)) / 100000 :=
    fun A => natPMF_real _ _ _ _ A
  have hm : ∀ s : Set (Bool × Bool), MeasurableSet s := fun s => (Set.toFinite s).measurableSet
  have e1 : {w : Bool × Bool | w.1 = true} = ((Finset.univ.filter (fun w : Bool × Bool => w.1 = true) :
      Finset (Bool × Bool)) : Set (Bool × Bool)) := by ext; simp
  have e2 : {w : Bool × Bool | w.1 = false} = ((Finset.univ.filter (fun w : Bool × Bool => w.1 = false) :
      Finset (Bool × Bool)) : Set (Bool × Bool)) := by ext; simp
  have e3 : {w : Bool × Bool | w.2 = true} = ((Finset.univ.filter (fun w : Bool × Bool => w.2 = true) :
      Finset (Bool × Bool)) : Set (Bool × Bool)) := by ext; simp
  have e12 : {w : Bool × Bool | w.1 = true} ∩ {w | w.2 = true} = (({(true, true)} : Finset (Bool × Bool)) :
      Set (Bool × Bool)) := by ext ⟨a, b⟩; cases a <;> cases b <;> simp
  have e21 : {w : Bool × Bool | w.1 = false} ∩ {w | w.2 = true} = (({(false, true)} : Finset (Bool × Bool)) :
      Set (Bool × Bool)) := by ext ⟨a, b⟩; cases a <;> cases b <;> simp
  have e31 : {w : Bool × Bool | w.2 = true} ∩ {w | w.1 = true} = (({(true, true)} : Finset (Bool × Bool)) :
      Set (Bool × Bool)) := by ext ⟨a, b⟩; cases a <;> cases b <;> simp
  have s1 : ∑ w ∈ Finset.univ.filter (fun w : Bool × Bool => w.1 = true), (testWeight w : ℝ) = 100 := by
    have : ∑ w ∈ Finset.univ.filter (fun w : Bool × Bool => w.1 = true), testWeight w = 100 := by
      decide
    exact_mod_cast this
  have s2 : ∑ w ∈ Finset.univ.filter (fun w : Bool × Bool => w.1 = false), (testWeight w : ℝ)
      = 99900 := by
    have : ∑ w ∈ Finset.univ.filter (fun w : Bool × Bool => w.1 = false), testWeight w = 99900 := by
      decide
    exact_mod_cast this
  have s3 : ∑ w ∈ Finset.univ.filter (fun w : Bool × Bool => w.2 = true), (testWeight w : ℝ)
      = 5094 := by
    have : ∑ w ∈ Finset.univ.filter (fun w : Bool × Bool => w.2 = true), testWeight w = 5094 := by
      decide
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · rw [e1, key, s1]; norm_num
  · rw [cond_real _ (hm _), e12, e1, key, key, s1]; simp [testWeight]; norm_num
  · rw [cond_real _ (hm _), e21, e2, key, key, s2]; simp [testWeight]; norm_num
  · rw [cond_real _ (hm _), e31, e3, key, key, s3]; simp [testWeight]; norm_num

/-! ### The two children paradox (PR-136) -/

/-- Two children, `true` for a boy: four equally likely families. -/
abbrev Family := Bool × Bool

/-- Grinstead–Snell Example 4.25 (PR-136). Given that at least one child is a boy, the probability that
both are boys is 1/3 (not 1/2). -/
@[kb "grinsteadsnell2006" "Example 4.25, p. 183"]
theorem twoChildren_atLeastOneBoy :
    ((uniformOn (Set.univ : Set Family))[{f | f.1 = true ∧ f.2 = true} |
        {f | f.1 = true ∨ f.2 = true}]).toReal = 1 / 3 := by
  rw [uniform_cond_real]
  have h1 : (Finset.univ.filter (fun f : Family => (f.1 = true ∨ f.2 = true) ∧ (f.1 = true ∧ f.2 = true))).card
      = 1 := by decide
  have h2 : (Finset.univ.filter (fun f : Family => f.1 = true ∨ f.2 = true)).card = 3 := by decide
  rw [h1, h2]; norm_num

/-- Mr. Smith's walk: the sexes of the two children and which child (`false` first, `true` second) he
walks with, each of the 8 combinations equally likely (a boy-girl family chooses either child with
probability 1/2). -/
abbrev SmithWalk := (Bool × Bool) × Bool

/-- Sex of the child walking with Mr. Smith. -/
def companion (w : SmithWalk) : Bool := if w.2 then w.1.2 else w.1.1

/-- Sex of the other child. -/
def otherChild (w : SmithWalk) : Bool := if w.2 then w.1.1 else w.1.2

/-- Grinstead–Snell Example 4.26 (PR-136). Given that the child walking with Mr. Smith is a boy, the
other child is a boy with probability 1/2. -/
@[kb "grinsteadsnell2006" "Example 4.26, p. 184"]
theorem twoChildren_companionBoy :
    ((uniformOn (Set.univ : Set SmithWalk))[{w | otherChild w = true} |
        {w | companion w = true}]).toReal = 1 / 2 := by
  rw [uniform_cond_real]
  have h1 : (Finset.univ.filter (fun w : SmithWalk => companion w = true ∧ otherChild w = true)).card
      = 2 := by decide
  have h2 : (Finset.univ.filter (fun w : SmithWalk => companion w = true)).card = 4 := by decide
  rw [h1, h2]; norm_num

/-! ### Poker hands (PR-132) -/

/-- A card is a value (13) and a suit (4). -/
abbrev PokerCard := Fin 13 × Fin 4

/-- The four cards of a given value. -/
def block (v : Fin 13) : Finset PokerCard := Finset.univ.filter (fun c => c.1 = v)

/-- The cards of a hand having a given value. -/
def ofValue (h : Finset PokerCard) (v : Fin 13) : Finset PokerCard := h.filter (fun c => c.1 = v)

/-- Poker hands: the 5-element subsets of the deck. -/
def hands : Finset (Finset PokerCard) := Finset.powersetCard 5 Finset.univ

/-- Hands with four cards of the same value. -/
def fourKind : Finset (Finset PokerCard) := hands.filter (fun h => ∃ v, (ofValue h v).card = 4)

/-- Hands with three cards of one value and two of another. -/
def fullHouse : Finset (Finset PokerCard) :=
  hands.filter (fun h => ∃ v w, v ≠ w ∧ (ofValue h v).card = 3 ∧ (ofValue h w).card = 2)

lemma block_card (v : Fin 13) : (block v).card = 4 := by
  revert v; unfold block; decide

lemma block_disjoint {v w : Fin 13} (h : v ≠ w) : Disjoint (block v) (block w) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [block, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  exact h (hx.symm.trans hx')

lemma ofValue_subset (h : Finset PokerCard) (v : Fin 13) : ofValue h v ⊆ block v := by
  intro x hx
  simp only [ofValue, block, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.2

lemma card_ofValue_eq_four_iff {h : Finset PokerCard} {v : Fin 13} :
    (ofValue h v).card = 4 ↔ block v ⊆ h := by
  constructor
  · intro hc
    have : ofValue h v = block v :=
      Finset.eq_of_subset_of_card_le (ofValue_subset h v) (by rw [hc, block_card])
    intro x hx
    rw [← this] at hx
    exact (Finset.mem_filter.1 hx).1
  · intro hb
    have : ofValue h v = block v := by
      ext x
      simp only [ofValue, block, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hx => hx.2, fun hx => ⟨hb (by simp [block, hx]), hx⟩⟩
    rw [this, block_card]

/-- Hands containing the block of value `v`: add one card outside the block. -/
def fourOf (v : Fin 13) : Finset (Finset PokerCard) :=
  (block v)ᶜ.image (fun c => insert c (block v))

lemma fourOf_card (v : Fin 13) : (fourOf v).card = 48 := by
  unfold fourOf
  rw [Finset.card_image_of_injOn, Finset.card_compl, block_card]
  · simp
  · intro c hc c' hc' he
    have hc : c ∉ block v := by simpa using hc
    have hc' : c' ∉ block v := by simpa using hc'
    have : c ∈ insert c' (block v) := by
      simp only at he
      rw [← he]; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.1 this with h | h
    · exact h
    · exact absurd h hc

lemma mem_fourOf {h : Finset PokerCard} {v : Fin 13} :
    h ∈ fourOf v ↔ h ∈ hands ∧ block v ⊆ h := by
  constructor
  · intro hh
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hh
    have hc : c ∉ block v := by simpa using hc
    refine ⟨?_, Finset.subset_insert _ _⟩
    simp [hands, Finset.mem_powersetCard, Finset.card_insert_of_notMem hc, block_card]
  · rintro ⟨hh, hb⟩
    have hcard : h.card = 5 := (Finset.mem_powersetCard.1 hh).2
    have h1 : (h \ block v).card = 1 := by
      have := Finset.card_sdiff_add_card_eq_card hb
      rw [block_card, hcard] at this
      omega
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 h1
    have hcm : c ∈ h \ block v := by rw [hc]; simp
    refine Finset.mem_image.2 ⟨c, by simpa using (Finset.mem_sdiff.1 hcm).2, ?_⟩
    ext x
    simp only [Finset.mem_insert]
    constructor
    · rintro (rfl | hx)
      · exact (Finset.mem_sdiff.1 hcm).1
      · exact hb hx
    · intro hx
      by_cases hxb : x ∈ block v
      · exact Or.inr hxb
      · left
        have : x ∈ h \ block v := Finset.mem_sdiff.2 ⟨hx, hxb⟩
        rw [hc] at this
        simpa using this

/-- Grinstead–Snell Example 3.6 (PR-132), four of a kind. There are `C(52,5) = 2598960` poker hands, and
`13 * 48 = 624` of them contain four cards of one value (13 values, then 48 choices of fifth card). The
count is proved by an explicit decomposition: the hands are the disjoint union over the 13 values `v` of
the 48 hands `block v ∪ {c}`. -/
@[kb "grinsteadsnell2006" "Example 3.6, p. 103"]
theorem poker_fourKind : hands.card = 2598960 ∧ fourKind.card = 624 := by
  refine ⟨by simp [hands, Finset.card_powersetCard]; decide +kernel, ?_⟩
  have hu : fourKind = Finset.univ.biUnion fourOf := by
    ext h
    simp only [fourKind, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
      mem_fourOf, card_ofValue_eq_four_iff]
    constructor
    · rintro ⟨h1, v, hv⟩; exact ⟨v, h1, hv⟩
    · rintro ⟨v, h1, hv⟩; exact ⟨h1, v, hv⟩
  rw [hu, Finset.card_biUnion]
  · simp [fourOf_card]
  · intro v _ w _ hvw
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro h hv hw
    obtain ⟨h5, hbv⟩ := mem_fourOf.1 hv
    obtain ⟨-, hbw⟩ := mem_fourOf.1 hw
    have h8 := Finset.card_le_card (Finset.union_subset hbv hbw)
    rw [Finset.card_union_of_disjoint (block_disjoint hvw), block_card, block_card,
      (Finset.mem_powersetCard.1 h5).2] at h8
    omega

/-- Full houses with triple of value `v` and pair of value `w`. -/
def fullOf (v w : Fin 13) : Finset (Finset PokerCard) :=
  (((block v).powersetCard 3) ×ˢ ((block w).powersetCard 2)).image (fun p => p.1 ∪ p.2)

lemma fullOf_card {v w : Fin 13} (hvw : v ≠ w) : (fullOf v w).card = 24 := by
  unfold fullOf
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_powersetCard,
    Finset.card_powersetCard, block_card, block_card]
  · decide
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powersetCard] at hab hab'
    simp only at he
    have hd1 : Disjoint a b :=
      Finset.disjoint_of_subset_left hab.1.1 (Finset.disjoint_of_subset_right hab.2.1 (block_disjoint hvw))
    have hd2 : Disjoint a' b' :=
      Finset.disjoint_of_subset_left hab'.1.1 (Finset.disjoint_of_subset_right hab'.2.1 (block_disjoint hvw))
    have ha : a = a' := by
      have e1 : (a ∪ b) ∩ block v = a := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxv⟩
          · exact hx
          · exact absurd hxv (Finset.disjoint_left.1 (block_disjoint hvw).symm (hab.2.1 hx))
        · intro hx; exact ⟨Or.inl hx, hab.1.1 hx⟩
      have e2 : (a' ∪ b') ∩ block v = a' := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxv⟩
          · exact hx
          · exact absurd hxv (Finset.disjoint_left.1 (block_disjoint hvw).symm (hab'.2.1 hx))
        · intro hx; exact ⟨Or.inl hx, hab'.1.1 hx⟩
      rw [← e1, ← e2, he]
    subst ha
    have hb : b = b' := by
      have := congrArg (fun t => t \ a) he
      simpa [Finset.union_sdiff_cancel_left hd1, Finset.union_sdiff_cancel_left hd2] using this
    rw [hb]

lemma ofValue_fullOf {v w : Fin 13} (hvw : v ≠ w) {h : Finset PokerCard} (hh : h ∈ fullOf v w)
    (u : Fin 13) :
    h ∈ hands ∧ (ofValue h u).card = if u = v then 3 else if u = w then 2 else 0 := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hh
  simp only [Finset.mem_product, Finset.mem_powersetCard] at hab
  have hd : Disjoint a b :=
    Finset.disjoint_of_subset_left hab.1.1 (Finset.disjoint_of_subset_right hab.2.1 (block_disjoint hvw))
  have hav : ∀ x ∈ a, x.1 = v := fun x hx => by simpa [block] using hab.1.1 hx
  have hbw : ∀ x ∈ b, x.1 = w := fun x hx => by simpa [block] using hab.2.1 hx
  refine ⟨?_, ?_⟩
  · simp [hands, Finset.mem_powersetCard, Finset.card_union_of_disjoint hd, hab.1.2, hab.2.2]
  · simp only [ofValue, Finset.filter_union]
    by_cases huv : u = v
    · subst huv
      have e1 : a.filter (fun c => c.1 = u) = a := Finset.filter_true_of_mem hav
      have e2 : b.filter (fun c => c.1 = u) = ∅ :=
        Finset.filter_false_of_mem (fun x hx h => hvw (h.symm.trans (hbw x hx)))
      simp [e1, e2, hab.1.2]
    · by_cases huw : u = w
      · subst huw
        have e1 : a.filter (fun c => c.1 = u) = ∅ :=
          Finset.filter_false_of_mem (fun x hx h => huv ((hav x hx).symm.trans h).symm)
        have e2 : b.filter (fun c => c.1 = u) = b := Finset.filter_true_of_mem hbw
        simp [e1, e2, hab.2.2, huv]
      · have e1 : a.filter (fun c => c.1 = u) = ∅ :=
          Finset.filter_false_of_mem (fun x hx h => huv ((hav x hx).symm.trans h).symm)
        have e2 : b.filter (fun c => c.1 = u) = ∅ :=
          Finset.filter_false_of_mem (fun x hx h => huw ((hbw x hx).symm.trans h).symm)
        simp [e1, e2, huv, huw]

/-- Grinstead–Snell Example 3.6 (PR-132), full house. There are `13 * C(4,3) * 12 * C(4,2) = 3744` full
houses. Proved as the disjoint union over the `13 * 12` ordered pairs of distinct values of the
`C(4,3) * C(4,2) = 24` hands made of three cards of the first value and two of the second. -/
@[kb "grinsteadsnell2006" "Example 3.6, p. 103"]
theorem poker_fullHouse : fullHouse.card = 3744 := by
  have hu : fullHouse = (Finset.univ : Finset (Fin 13)).offDiag.biUnion (fun p => fullOf p.1 p.2) := by
    ext h
    simp only [fullHouse, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_offDiag,
      Finset.mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨hh, v, w, hvw, h3, h2⟩
      refine ⟨v, w, hvw, ?_⟩
      have hd : Disjoint (ofValue h v) (ofValue h w) := by
        refine Finset.disjoint_of_subset_left (ofValue_subset h v)
          (Finset.disjoint_of_subset_right (ofValue_subset h w) (block_disjoint hvw))
      have hsub : ofValue h v ∪ ofValue h w ⊆ h := Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _)
      have hc : (ofValue h v ∪ ofValue h w).card = 5 := by
        rw [Finset.card_union_of_disjoint hd, h3, h2]
      have heq : ofValue h v ∪ ofValue h w = h :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hc, (Finset.mem_powersetCard.1 hh).2])
      refine Finset.mem_image.2 ⟨(ofValue h v, ofValue h w), ?_, heq⟩
      simp only [Finset.mem_product, Finset.mem_powersetCard]
      exact ⟨⟨ofValue_subset h v, h3⟩, ⟨ofValue_subset h w, h2⟩⟩
    · rintro ⟨v, w, hvw, hh⟩
      obtain ⟨h5, hc⟩ := ofValue_fullOf hvw hh v
      obtain ⟨-, hc'⟩ := ofValue_fullOf hvw hh w
      refine ⟨h5, v, w, hvw, ?_, ?_⟩
      · simpa using hc
      · simpa [hvw.symm] using hc'
  rw [hu, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 24)]
    · simp [Finset.offDiag_card]
    · intro p hp
      exact fullOf_card (Finset.mem_offDiag.1 hp).2.2
  · intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro h h1 h2
    have hp' := (Finset.mem_offDiag.1 hp).2.2
    have hq' := (Finset.mem_offDiag.1 hq).2.2
    have a1 := (ofValue_fullOf hp' h1 p.1).2
    have a2 := (ofValue_fullOf hq' h2 p.1).2
    have b1 := (ofValue_fullOf hp' h1 p.2).2
    have b2 := (ofValue_fullOf hq' h2 p.2).2
    apply hpq
    have c1 := a1.symm.trans a2
    have c2 := b1.symm.trans b2
    rw [if_pos rfl] at c1
    rw [if_neg hp'.symm, if_pos rfl] at c2
    refine Prod.ext ?_ ?_
    · by_contra hne
      rw [if_neg hne] at c1
      split_ifs at c1 <;> omega
    · by_contra hne
      rw [if_neg hne] at c2
      split_ifs at c2 <;> omega

end UndergradKB.Probability
