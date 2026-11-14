import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import UndergradKB.Common.Attr
import UndergradKB.Probability.DiscreteDistributions
import UndergradKB.Probability.ExamplesExpectation

/-! # Probability: more school-level worked examples (Grinstead–Snell, chapters 1, 3, 4, 6, 7)

Election odds (Example 1.12), basic counting (Examples 3.1, 3.2, 3.5), independence of events for
two tosses (Examples 4.7 to 4.9), independent trials processes (Examples 4.10 to 4.15), diagnosis
with two tests (Example 4.16), a coin plus a die (Example 6.7) and the bridge point count
(Example 7.2). -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal unitInterval

namespace UndergradKB.Probability

/-! ## Example 1.12: election odds (PR-163) -/

open Classical in
/-- Grinstead–Snell Example 1.12 (PR-163). If candidate `C` wins with probability `1/5` then the odds
in favour of `C` are `1 : 4` (that is `(1/5)/(4/5) = 1/4`, and conversely odds `1 : 4` give
probability `1/(1+4) = 1/5`), and the bet that pays `4` dollars if `C` wins and costs `1` dollar if `C`
loses has expected gain `0`, so it is fair. -/
@[kb "grinsteadsnell2006" "Example 1.12, p. 36"]
theorem election_odds_fair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {C : Set Ω} (hC : MeasurableSet C) (h : P.real C = 1 / 5) :
    P.real C / (1 - P.real C) = 1 / 4 ∧ P.real C = 1 / (1 + 4) ∧
      ∫ ω, (if ω ∈ C then (4 : ℝ) else -1) ∂P = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h]; norm_num
  · rw [h]; norm_num
  · have e : (fun ω => if ω ∈ C then (4 : ℝ) else -1) =
        fun ω => -1 + C.indicator (fun _ => (5 : ℝ)) ω := by
      ext ω; by_cases hω : ω ∈ C <;> simp [hω]; norm_num
    rw [e, integral_add (integrable_const _) ((integrable_const _).indicator hC),
      integral_indicator_const _ hC]
    simp [h]

/-! ## Examples 3.1, 3.2, 3.5: basic counting (PR-164) -/

/-- Grinstead–Snell Example 3.1 (PR-164). A menu is a choice of one of 2 appetizers, one of 3 main
courses and one of 2 desserts; there are `2 * 3 * 2 = 12` menus. -/
@[kb "grinsteadsnell2006" "Example 3.1, p. 83"]
theorem menus_count : Fintype.card (Fin 2 × Fin 3 × Fin 2) = 12 := by
  simp

/-- Grinstead–Snell Example 3.2 (PR-164). There are `26^3 = 17576` triples of initials, and in a group
of more than that many people (a finset `S`, with any assignment `f` of initials) there are two
distinct people with the same three initials: `f` is not injective on `S`. -/
@[kb "grinsteadsnell2006" "Example 3.2, p. 85"]
theorem initials_pigeonhole {α : Type*} (S : Finset α) (f : α → Fin 3 → Fin 26)
    (hS : 26 ^ 3 < S.card) :
    Fintype.card (Fin 3 → Fin 26) = 17576 ∧ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a = f b := by
  have hc : Fintype.card (Fin 3 → Fin 26) = 17576 := by simp
  refine ⟨hc, ?_⟩
  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := S)
    (t := (Finset.univ : Finset (Fin 3 → Fin 26)))
    (by rw [Finset.card_univ, hc]; omega) (f := f) (fun _ _ => Finset.mem_univ _)

/-- Grinstead–Snell Example 3.5 (PR-164). The three-element set `U = {a, b, c}` has `2^3 = 8`
subsets. -/
@[kb "grinsteadsnell2006" "Example 3.5, p. 101"]
theorem three_element_subsets : (({0, 1, 2} : Finset (Fin 3)).powerset).card = 8 := by
  decide

/-! ## Examples 4.7, 4.8, 4.9: independence of events for two tosses (PR-165) -/

/-- The coin with `P(H) = p`: `true` is heads. -/
noncomputable abbrev coin (p : unitInterval) : Measure Bool := Ber(true, false, p)

/-- Weight of one toss: `p` for heads (`true`), `1 - p` for tails. -/
def coinWt (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

lemma coin_real_singleton (p : unitInterval) (b : Bool) :
    (coin p).real {b} = coinWt p b := by
  cases b
  · rw [bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by simp) (by simp)]
    simp [coinWt]
  · rw [bernoulliMeasure_real_apply_of_mem_of_notMem p (by simp) (by simp) (by simp)]
    simp [coinWt]

/-- Two independent tosses of the coin with `P(H) = p` (the product measure on `Bool × Bool`). -/
noncomputable def twoTosses (p : unitInterval) : Measure (Bool × Bool) := (coin p).prod (coin p)

instance (p : unitInterval) : IsProbabilityMeasure (twoTosses p) := by
  unfold twoTosses; infer_instance

lemma twoTosses_real_singleton (p : unitInterval) (a b : Bool) :
    (twoTosses p).real {(a, b)} = coinWt p a * coinWt p b := by
  rw [measureReal_def, twoTosses, ← Set.singleton_prod_singleton, Measure.prod_prod,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, coin_real_singleton,
    coin_real_singleton]

lemma twoTosses_real_pred (p : unitInterval) (P : Bool × Bool → Prop) [DecidablePred P] :
    (twoTosses p).real {ω | P ω} =
      ∑ a : Bool, ∑ b : Bool, if P (a, b) then coinWt p a * coinWt p b else 0 := by
  have h : {ω | P ω} = ↑(Finset.univ.filter P) := by ext; simp
  rw [h, ← sum_measureReal_singleton, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [twoTosses_real_singleton]

lemma twoTosses_indep_iff (p : unitInterval) (P Q : Bool × Bool → Prop) [DecidablePred P]
    [DecidablePred Q] :
    IndepSet {ω | P ω} {ω | Q ω} (twoTosses p) ↔
      (twoTosses p).real {ω | P ω ∧ Q ω} =
        (twoTosses p).real {ω | P ω} * (twoTosses p).real {ω | Q ω} := by
  have hs : ∀ R : Bool × Bool → Prop, MeasurableSet {ω | R ω} := fun R =>
    (Set.toFinite _).measurableSet
  refine (indepSet_iff_measure_inter_eq_mul (hs P) (hs Q) (twoTosses p)).trans ?_
  rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul]
  have : {ω | P ω} ∩ {ω | Q ω} = {ω | P ω ∧ Q ω} := rfl
  rw [this, ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))]

/-- Grinstead–Snell Example 4.7 (PR-165). Two tosses of a coin with `P(H) = p`, with the product
weights `p^2, pq, qp, q^2` on `HH, HT, TH, TT` (`q = 1 - p`): the events "heads on the first toss" and
"tails on the second toss" are independent, `P(E ∩ F) = pq = P(E) P(F)`, for every `p`. -/
@[kb "grinsteadsnell2006" "Example 4.7, p. 148"]
theorem two_tosses_heads_first_tails_second (p : unitInterval) :
    (twoTosses p).real {ω | ω.1 = true} = p ∧ (twoTosses p).real {ω | ω.2 = false} = 1 - p ∧
      IndepSet {ω : Bool × Bool | ω.1 = true} {ω | ω.2 = false} (twoTosses p) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [twoTosses_real_pred]
    simp [coinWt]
    ring
  · rw [twoTosses_real_pred]
    simp [coinWt]
    ring
  · rw [twoTosses_indep_iff, twoTosses_real_pred, twoTosses_real_pred, twoTosses_real_pred]
    simp [coinWt]
    ring

/-- Grinstead–Snell Example 4.8 (PR-165). For the fair coin, the events "the first toss is a head"
and "the two outcomes are the same" are independent: `P(B | A) = (1/4)/(1/2) = 1/2 = P(B)`. -/
@[kb "grinsteadsnell2006" "Example 4.8, p. 148"]
theorem two_tosses_first_head_same_indep (h : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    IndepSet {ω : Bool × Bool | ω.1 = true} {ω | ω.1 = ω.2}
      (twoTosses ⟨1 / 2, h⟩) ∧
    (twoTosses ⟨1 / 2, h⟩).real {ω | ω.1 = true ∧ ω.1 = ω.2} = 1 / 4 ∧
    (twoTosses ⟨1 / 2, h⟩).real {ω | ω.1 = true} = 1 / 2 ∧
    (twoTosses ⟨1 / 2, h⟩).real {ω | ω.1 = ω.2} = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [twoTosses_indep_iff, twoTosses_real_pred, twoTosses_real_pred, twoTosses_real_pred]
    simp [coinWt]; norm_num
  · rw [twoTosses_real_pred]; simp [coinWt]; norm_num
  · rw [twoTosses_real_pred]; simp [coinWt]; norm_num
  · rw [twoTosses_real_pred]; simp [coinWt]; norm_num

/-- Grinstead–Snell Example 4.9 (PR-165). For the fair coin, "heads on the first toss" (probability
`1/2`) and "two heads" (probability `1/4`) are not independent: the intersection has probability `1/4`
but the product is `1/8`. -/
@[kb "grinsteadsnell2006" "Example 4.9, p. 149"]
theorem two_tosses_first_head_two_heads_not_indep (h : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    (twoTosses ⟨1 / 2, h⟩).real {ω | ω.1 = true} = 1 / 2 ∧
    (twoTosses ⟨1 / 2, h⟩).real {ω | ω.1 = true ∧ ω.2 = true} = 1 / 4 ∧
    ¬ IndepSet {ω : Bool × Bool | ω.1 = true} {ω | ω.1 = true ∧ ω.2 = true}
      (twoTosses ⟨1 / 2, h⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [twoTosses_real_pred]; simp [coinWt]; norm_num
  · rw [twoTosses_real_pred]; simp [coinWt]; norm_num
  · have e : {ω : Bool × Bool | ω.1 = true ∧ ω.1 = true ∧ ω.2 = true} =
        {ω | ω.1 = true ∧ ω.2 = true} := by ext; simp
    have := twoTosses_indep_iff ⟨1 / 2, h⟩ (fun ω => ω.1 = true) (fun ω => ω.1 = true ∧ ω.2 = true)
    rw [this, e]
    simp only [twoTosses_real_pred]
    simp [coinWt]
    norm_num

/-! ## Examples 4.10 to 4.15: independent trials processes (PR-166) -/

section Trials

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSingletonClass α] in
lemma pi_real_singleton (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (x : Fin n → α) :
    (Measure.pi fun _ : Fin n => μ).real {x} = ∏ i, μ.real {x i} := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  rfl

lemma pi_real_coord (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (i : Fin n) (a : α) :
    (Measure.pi fun _ : Fin n => μ).real {x | x i = a} = μ.real {a} := by
  have h := (measurePreserving_eval (fun _ : Fin n => μ) i).measure_preimage
    (measurableSet_singleton a).nullMeasurableSet
  rw [measureReal_def, measureReal_def]
  exact congrArg ENNReal.toReal h

/-- Grinstead–Snell Example 4.12 (PR-166). In an independent trials process (the product measure of
`n` copies of a distribution `μ` on a finite set), the probability of an outcome `(a₁, ..., aₙ)` is the
product of the probabilities `P(Xᵢ = aᵢ)` of its coordinates, and the coordinates `Xᵢ` are mutually
independent random variables. -/
@[kb "grinsteadsnell2006" "Example 4.12, p. 150"]
theorem trials_product_independent (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    (∀ a : Fin n → α, (Measure.pi fun _ : Fin n => μ).real {a} =
        ∏ i, (Measure.pi fun _ : Fin n => μ).real {x | x i = a i}) ∧
      iIndepFun (fun (i : Fin n) (x : Fin n → α) => x i) (Measure.pi fun _ : Fin n => μ) := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [pi_real_singleton]
    exact Finset.prod_congr rfl fun i _ => (pi_real_coord μ n i (a i)).symm
  · exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

end Trials

/-- The uniform probability measure on `Fin 3 → Bool`: three independent tosses of a fair coin
(`halfProb` is the probability `1/2` in the unit interval). -/
noncomputable abbrev threeFairTosses : Measure (Fin 3 → Bool) :=
  Measure.pi fun _ : Fin 3 => coin halfProb

lemma coinWt_half (b : Bool) : coinWt (halfProb : ℝ) b = 1 / 2 := by
  cases b <;> simp [coinWt, halfProb_coe]; norm_num

/-- Grinstead–Snell Example 4.10 (PR-166). Three independent tosses of a fair coin: each of the eight
ordered triples has probability `1/8`, and each toss `Xᵢ` has the distribution `m(H) = m(T) = 1/2`. -/
@[kb "grinsteadsnell2006" "Example 4.10, p. 149"]
theorem three_fair_tosses :
    (∀ x : Fin 3 → Bool, threeFairTosses.real {x} = 1 / 8) ∧
      ∀ (i : Fin 3) (b : Bool), threeFairTosses.real {x | x i = b} = 1 / 2 := by
  refine ⟨fun x => ?_, fun i b => ?_⟩
  · rw [pi_real_singleton]
    simp only [coin_real_singleton, coinWt_half, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  · rw [pi_real_coord, coin_real_singleton, coinWt_half]

/-- The joint random variable `Ȳ = (Y₁, Y₂, Y₃)` of Example 4.11, where `Yᵢ` is the number of heads in
the first `i` tosses. -/
def headsPartial (x : Fin 3 → Bool) : ℕ × ℕ × ℕ :=
  (((univ.filter fun j : Fin 3 => j.val < 1 ∧ x j = true)).card,
    ((univ.filter fun j : Fin 3 => j.val < 2 ∧ x j = true)).card,
    ((univ.filter fun j : Fin 3 => j.val < 3 ∧ x j = true)).card)

/-- Grinstead–Snell Example 4.11 (PR-166). For three fair tosses, `Ȳ = (Y₁, Y₂, Y₃)` takes exactly eight
distinct values, each with probability `1/8` (it is a bijective relabelling of the outcome
`X̄ = (X₁, X₂, X₃)`), while the outcome `(1, 0, 1)` has probability `0`. -/
@[kb "grinsteadsnell2006" "Example 4.11, p. 150"]
theorem heads_partial_law :
    (univ.image headsPartial).card = 8 ∧
      (∀ x, (threeFairTosses.map headsPartial).real {headsPartial x} = 1 / 8) ∧
      (threeFairTosses.map headsPartial).real {((1 : ℕ), (0 : ℕ), (1 : ℕ))} = 0 := by
  have hm : Measurable headsPartial := Measurable.of_discrete
  have hinj : Function.Injective headsPartial := by decide
  refine ⟨?_, fun x => ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]; simp
  · rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton _)]
    have : headsPartial ⁻¹' {headsPartial x} = {x} := by
      ext y; simp [hinj.eq_iff]
    rw [this, ← measureReal_def, (three_fair_tosses).1]
  · rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton _)]
    have : headsPartial ⁻¹' {((1 : ℕ), (0 : ℕ), (1 : ℕ))} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      revert y; decide
    simp [this]

/-- Grinstead–Snell Example 4.14 (PR-166). Three rolls of a fair die form an independent trials process
(the product of three uniform measures on the six faces): each of the `216` outcomes has probability
`1/6 * 1/6 * 1/6 = 1/216`, each roll has probability `1/6` for each face, and the rolls are mutually
independent. -/
@[kb "grinsteadsnell2006" "Example 4.14, p. 152"]
theorem three_die_rolls :
    (∀ x : Fin 3 → Fin 6, (Measure.pi fun _ : Fin 3 => fairMeasure (Fin 6)).real {x} = 1 / 216) ∧
    (∀ (i : Fin 3) (a : Fin 6),
      (Measure.pi fun _ : Fin 3 => fairMeasure (Fin 6)).real {x | x i = a} = 1 / 6) ∧
    iIndepFun (fun (i : Fin 3) (x : Fin 3 → Fin 6) => x i)
      (Measure.pi fun _ : Fin 3 => fairMeasure (Fin 6)) := by
  have hf : ∀ a : Fin 6, (fairMeasure (Fin 6)).real {a} = 1 / 6 := by
    intro a
    simp [fairMeasure, measureReal_def]
  refine ⟨fun x => ?_, fun i a => ?_, (trials_product_independent _ 3).2⟩
  · rw [pi_real_singleton]
    simp only [hf, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  · rw [pi_real_coord, hf]

/-- The number of successes (heads, `true`) in an outcome of `n` trials. -/
def successCount {n : ℕ} (x : Fin n → Bool) : ℕ := (univ.filter fun i => x i = true).card

lemma prod_coinWt {n : ℕ} (p : unitInterval) (x : Fin n → Bool) :
    ∏ i, coinWt p (x i) = (p : ℝ) ^ successCount x * (1 - p) ^ (n - successCount x) := by
  unfold coinWt successCount
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  simp only [Bool.not_eq_true] at *
  have h2 : (univ.filter fun i => ¬ x i = true).card = n - (univ.filter fun i => x i = true).card := by
    simp only [Bool.not_eq_true] at *
    omega
  simpa using h2

lemma card_successCount (n j : ℕ) :
    (univ.filter fun x : Fin n → Bool => successCount x = j).card = n.choose j := by
  have hp := Finset.card_powersetCard j (univ : Finset (Fin n))
  rw [Finset.card_univ, Fintype.card_fin] at hp
  rw [← hp]
  refine Finset.card_bij (fun x _ => univ.filter fun i => x i = true) ?_ ?_ ?_
  · intro x hx
    have hx' := (Finset.mem_filter.1 hx).2
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hx'⟩
  · intro x _ y _ hxy
    funext i
    have := congrArg (fun s => i ∈ s) hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hx : x i <;> cases hy : y i <;> simp_all
  · intro s hs
    refine ⟨fun i => decide (i ∈ s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simp only [Finset.mem_powersetCard] at hs
      simpa [successCount] using hs.2
    · ext i; simp

/-- Grinstead–Snell Example 4.15 (PR-166). In a Bernoulli trials process with success probability `p`
(the product measure of `n` copies of the coin) an outcome with `k` successes has probability
`p^k q^(n-k)`, the indicators `Xⱼ` of success on the `j`th trial are mutually independent with
`P(Xⱼ = 1) = p`, and the number of successes `Sₙ = X₁ + ... + Xₙ` has the binomial law `b(n, p, j)`
(`Bin(n, p)` of Mathlib). -/
@[kb "grinsteadsnell2006" "Example 4.15, p. 153"]
theorem bernoulli_trials_process (p : unitInterval) (n : ℕ) :
    (∀ x : Fin n → Bool, (Measure.pi fun _ : Fin n => coin p).real {x} =
        (p : ℝ) ^ successCount x * (1 - p) ^ (n - successCount x)) ∧
      iIndepFun (fun (i : Fin n) (x : Fin n → Bool) => x i) (Measure.pi fun _ : Fin n => coin p) ∧
      (∀ i : Fin n, (Measure.pi fun _ : Fin n => coin p).real {x | x i = true} = p) ∧
      ∀ j : ℕ, ((Measure.pi fun _ : Fin n => coin p).map successCount).real {j} =
        (Bin(n, p)).real {j} := by
  refine ⟨fun x => ?_, (trials_product_independent _ n).2, fun i => ?_, fun j => ?_⟩
  · rw [pi_real_singleton]
    simp only [coin_real_singleton]
    exact prod_coinWt p x
  · rw [pi_real_coord, coin_real_singleton]; simp [coinWt]
  · have hm : Measurable (successCount (n := n)) := Measurable.of_discrete
    rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton _), ← measureReal_def]
    have h : (successCount (n := n)) ⁻¹' {j} = ↑(univ.filter fun x : Fin n → Bool => successCount x = j) := by
      ext x; simp
    rw [h, ← sum_measureReal_singleton, binomial_real_singleton]
    have : ∀ x ∈ (univ.filter fun x : Fin n → Bool => successCount x = j),
        (Measure.pi fun _ : Fin n => coin p).real {x} =
          (p : ℝ) ^ j * (1 - p) ^ (n - j) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [pi_real_singleton]
      simp only [coin_real_singleton]
      rw [prod_coinWt, hx]
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_successCount, nsmul_eq_mul]
    ring

/-! ## Example 4.16: diagnosis with two tests (PR-167) -/

/-- Table 4.3 of the book: for 10,000 people with one of three diseases `d₁, d₂, d₃` (rows), the number
with each test pattern `++, +-, -+, --` (columns). -/
def diseaseTable : Fin 3 → Fin 4 → ℕ :=
  ![![2110, 301, 704, 100], ![396, 132, 1187, 410], ![510, 3568, 73, 509]]

/-- The number of people with disease `d` (the first column of Table 4.3). -/
def diseaseTotal (d : Fin 3) : ℕ := ∑ e, diseaseTable d e

/-- The number of people showing test pattern `e`. -/
def patternTotal (e : Fin 4) : ℕ := ∑ d, diseaseTable d e

/-- Prior probability of disease `d`, estimated from the table. -/
def diseasePrior (d : Fin 3) : ℚ := diseaseTotal d / 10000

/-- Probability of test pattern `e` given disease `d`, estimated from the table. -/
def patternLikelihood (d : Fin 3) (e : Fin 4) : ℚ := diseaseTable d e / diseaseTotal d

/-- Posterior probability of disease `d` given pattern `e` by Bayes' formula
`P(Hᵢ) P(E | Hᵢ) / ∑ₖ P(Hₖ) P(E | Hₖ)`. -/
def diseasePosterior (d : Fin 3) (e : Fin 4) : ℚ :=
  diseasePrior d * patternLikelihood d e / ∑ k, diseasePrior k * patternLikelihood k e

/-- The book's Table 4.4 (rows: patterns `++, +-, -+, --`; columns `d₁, d₂, d₃`), rounded to three
decimals. -/
def printedPosterior : Fin 4 → Fin 3 → ℚ :=
  ![![700 / 1000, 131 / 1000, 169 / 1000], ![75 / 1000, 33 / 1000, 892 / 1000],
    ![358 / 1000, 604 / 1000, 38 / 1000], ![98 / 1000, 403 / 1000, 499 / 1000]]

/-- Grinstead–Snell Example 4.16 (PR-167). With Table 4.3 (row totals `3215, 2125, 4660`, column totals
`3016, 4001, 1964, 1019`, grand total `10000`), Bayes' formula gives the posterior probability of
disease `d` given test pattern `e` as the table entry divided by the total of its pattern column,
`diseasePosterior d e = diseaseTable d e / patternTotal e`; for `++` the first disease has posterior
`2110/3016` (about `.700`). Every exact posterior is within `1/1000` of the book's three-decimal
Table 4.4 (the book's rounding of two entries, `.403` for `410/1019 = .4023...` and `.038` for
`73/1964 = .0372...`, is off in the last digit, so the bound is not `1/2000`). -/
@[kb "grinsteadsnell2006" "Example 4.16, p. 154"]
theorem diagnosis_two_tests :
    (∑ d, diseaseTotal d = 10000) ∧ diseaseTotal 0 = 3215 ∧ diseaseTotal 1 = 2125 ∧
      diseaseTotal 2 = 4660 ∧
      patternTotal 0 = 3016 ∧ patternTotal 1 = 4001 ∧ patternTotal 2 = 1964 ∧ patternTotal 3 = 1019 ∧
      (∀ d e, diseasePosterior d e = diseaseTable d e / patternTotal e) ∧
      diseasePosterior 0 0 = 2110 / 3016 ∧
      (∀ d e, |diseasePosterior d e - printedPosterior e d| < 1 / 1000) := by
  have hrow : ∀ d, diseaseTotal d ≠ 0 := by
    intro d; fin_cases d <;> simp [diseaseTotal, diseaseTable, Fin.sum_univ_succ]
  have hpost : ∀ d e, diseasePosterior d e = diseaseTable d e / patternTotal e := by
    intro d e
    have hd : ∀ k, diseasePrior k * patternLikelihood k e = (diseaseTable k e : ℚ) / 10000 := by
      intro k
      have := hrow k
      unfold diseasePrior patternLikelihood
      have h' : (diseaseTotal k : ℚ) ≠ 0 := by exact_mod_cast this
      field_simp
    unfold diseasePosterior
    simp only [hd, ← Finset.sum_div, patternTotal]
    rw [div_div_div_cancel_right₀ (by norm_num : (10000 : ℚ) ≠ 0)]
    push_cast
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpost, ?_, ?_⟩
  all_goals try (simp [diseaseTotal, patternTotal, diseaseTable, Fin.sum_univ_succ]; done)
  · rw [hpost]; simp [patternTotal, diseaseTable, Fin.sum_univ_succ]
  · intro d e
    rw [hpost]
    fin_cases d <;> fin_cases e <;>
      norm_num [patternTotal, diseaseTable, printedPosterior, Fin.sum_univ_succ, abs_lt]

/-! ## Example 6.7: a coin and a die (PR-168) -/

/-- Grinstead–Snell Example 6.7 (PR-168). Flip a coin (`X = 1` for heads, `0` for tails) and roll a die
(`Y` the face); the pair `(X, Y)` is uniform on the `12` outcomes of `Bool × Fin 6`. Then `E(X) = 1/2`,
`E(Y) = 7/2` and `E(X + Y) = 4`. -/
@[kb "grinsteadsnell2006" "Example 6.7, p. 238"]
theorem coin_plus_die_expectation :
    ∫ ω, headsCount ω.1 ∂fairMeasure (Bool × Fin 6) = 1 / 2 ∧
    ∫ ω, dieValue ω.2 ∂fairMeasure (Bool × Fin 6) = 7 / 2 ∧
    ∫ ω, (headsCount ω.1 + dieValue ω.2) ∂fairMeasure (Bool × Fin 6) = 4 := by
  simp only [integral_fairMeasure, Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Fintype.sum_bool, headsCount, dieValue, Finset.sum_add_distrib,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-! ## Example 7.2: the bridge point count (PR-169) -/

/-- The point value of the card with index `i` of a 52-card deck (rank `i % 13`, with `9, 10, 11, 12`
the jack, queen, king, ace): ace `4`, king `3`, queen `2`, jack `1`, others `0`. -/
def bridgeValue (i : Fin 52) : ℕ :=
  if i.val % 13 = 12 then 4 else if i.val % 13 = 11 then 3 else if i.val % 13 = 10 then 2
  else if i.val % 13 = 9 then 1 else 0

lemma fair_real_finset {n : ℕ} (A : Finset (Fin n)) (hn : 0 < n) :
    (fairMeasure (Fin n)).real (A : Set (Fin n)) = (A.card : ℝ) / n := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [← sum_measureReal_singleton]
  have : ∀ a : Fin n, (fairMeasure (Fin n)).real {a} = 1 / n := by
    intro a; simp [fairMeasure, measureReal_def]
  simp only [this, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Grinstead–Snell Example 7.2 (PR-169), one card. A card dealt at random from a full deck (uniform
on `Fin 52`) has point count with law `(36, 4, 4, 4, 4) / 52` on `0, ..., 4`, and mean `10/13`. -/
@[kb "grinsteadsnell2006" "Example 7.2, p. 295"]
theorem bridge_card_point_law :
    ((fairMeasure (Fin 52)).map bridgeValue).real {0} = 36 / 52 ∧
    ((fairMeasure (Fin 52)).map bridgeValue).real {1} = 4 / 52 ∧
    ((fairMeasure (Fin 52)).map bridgeValue).real {2} = 4 / 52 ∧
    ((fairMeasure (Fin 52)).map bridgeValue).real {3} = 4 / 52 ∧
    ((fairMeasure (Fin 52)).map bridgeValue).real {4} = 4 / 52 ∧
    ∫ i, (bridgeValue i : ℝ) ∂fairMeasure (Fin 52) = 10 / 13 := by
  have hm : Measurable bridgeValue := Measurable.of_discrete
  have hlaw : ∀ k : ℕ, ((fairMeasure (Fin 52)).map bridgeValue).real {k} =
      ((univ.filter fun i => bridgeValue i = k).card : ℝ) / 52 := by
    intro k
    rw [measureReal_def, Measure.map_apply hm (measurableSet_singleton _), ← measureReal_def]
    have h : bridgeValue ⁻¹' {k} = ↑(univ.filter fun i => bridgeValue i = k) := by
      ext i; simp
    rw [h, fair_real_finset _ (by norm_num)]
    norm_num
  have h0 : (univ.filter fun i => bridgeValue i = 0).card = 36 := by decide
  have h1 : (univ.filter fun i => bridgeValue i = 1).card = 4 := by decide
  have h2 : (univ.filter fun i => bridgeValue i = 2).card = 4 := by decide
  have h3 : (univ.filter fun i => bridgeValue i = 3).card = 4 := by decide
  have h4 : (univ.filter fun i => bridgeValue i = 4).card = 4 := by decide
  have hs : ∑ i, bridgeValue i = 40 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlaw, h0]; norm_num
  · rw [hlaw, h1]; norm_num
  · rw [hlaw, h2]; norm_num
  · rw [hlaw, h3]; norm_num
  · rw [hlaw, h4]; norm_num
  · rw [integral_fairMeasure]
    have : ∑ i, (bridgeValue i : ℝ) = 40 := by exact_mod_cast hs
    rw [this]; simp; norm_num

/-- Grinstead–Snell Example 7.2 (PR-169), the hand. Regarding a hand of `13` cards as `13` independent
trials with the one-card distribution (the product measure of `13` copies of the uniform measure on
`Fin 52`), the cards' point counts are mutually independent and the expected point count of the hand
`C = ∑ⱼ (point count of card j)` is `13 * (10/13) = 10`. The book's value `P(C ≥ 13) = .2845` is `bridge_hand_tail`. -/
@[kb "grinsteadsnell2006" "Example 7.2, p. 295"]
theorem bridge_hand_mean :
    iIndepFun (fun (j : Fin 13) (x : Fin 13 → Fin 52) => (bridgeValue (x j) : ℝ))
      (Measure.pi fun _ : Fin 13 => fairMeasure (Fin 52)) ∧
    ∫ x, ∑ j, (bridgeValue (x j) : ℝ) ∂(Measure.pi fun _ : Fin 13 => fairMeasure (Fin 52)) = 10 := by
  have hcard : ∫ i, (bridgeValue i : ℝ) ∂fairMeasure (Fin 52) = 10 / 13 :=
    bridge_card_point_law.2.2.2.2.2
  refine ⟨iIndepFun_pi (X := fun _ i => (bridgeValue i : ℝ))
    (fun _ => Measurable.of_discrete.aemeasurable), ?_⟩
  have hj : ∀ j : Fin 13, ∫ x, (bridgeValue (x j) : ℝ)
      ∂(Measure.pi fun _ : Fin 13 => fairMeasure (Fin 52)) = 10 / 13 := by
    intro j
    rw [← hcard, ← (measurePreserving_eval (fun _ : Fin 13 => fairMeasure (Fin 52)) j).map_eq,
      integral_map (measurable_pi_apply j).aemeasurable
        (Measurable.of_discrete.aestronglyMeasurable)]
    rw [(measurePreserving_eval (fun _ : Fin 13 => fairMeasure (Fin 52)) j).map_eq]
  rw [integral_finsetSum _ (fun j _ => Integrable.of_finite)]
  simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

end UndergradKB.Probability
