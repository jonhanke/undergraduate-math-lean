import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Combinatorics.Derangements.Exponential
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesSchool
import UndergradKB.Probability.Basic
import UndergradKB.Probability.Combinatorial
import UndergradKB.Probability.GeneratingFunctions
import UndergradKB.Probability.Shuffles

/-!
# Course layer, Chapter 3 (Grinstead–Snell, Combinatorics)

Thin wrappers stating the book's results of Chapter 3 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open Filter Topology MeasureTheory ProbabilityTheory
open scoped unitInterval

/-- Grinstead–Snell Definition 3.1 (PR-019). A permutation of a finite set is a bijection of the
set onto itself, and a `k`-permutation is an injective listing of `k` of its elements. -/
@[kb "grinsteadsnell2006" "Definition 3.1, p. 87"]
theorem gs_definition_3_1 {α : Type*} (e : Equiv.Perm α) (k : ℕ) (f : Fin k ↪ α) :
    Function.Bijective e ∧ Function.Injective f :=
  ⟨e.bijective, f.injective⟩

/-- Grinstead–Snell Theorem 3.1 (PR-020). A set of `n` elements has `n!` permutations. -/
@[kb "grinsteadsnell2006" "Theorem 3.1, p. 88"]
theorem gs_theorem_3_1 (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (Equiv.Perm α) = Nat.factorial (Fintype.card α) :=
  Fintype.card_perm

/-- Grinstead–Snell Theorem 3.2 (PR-020). The number of `k`-permutations of an `n`-element set is
`n (n-1) ... (n-k+1)`. -/
@[kb "grinsteadsnell2006" "Theorem 3.2, p. 88"]
theorem gs_theorem_3_2 (α : Type*) [Fintype α] (k : ℕ) :
    Fintype.card (Fin k ↪ α) = (Fintype.card α).descFactorial k := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin]

/-- Grinstead–Snell Definition 3.3 (PR-021). Sequences with eventually nonzero denominators are
asymptotically equal exactly when their ratio tends to one. -/
@[kb "grinsteadsnell2006" "Definition 3.3, p. 89"]
theorem gs_definition_3_3 (a b : ℕ → ℝ) (hb : ∀ᶠ n in atTop, b n ≠ 0) :
    Asymptotics.IsEquivalent atTop a b ↔ Tendsto (fun n => a n / b n) atTop (𝓝 1) :=
  Asymptotics.isEquivalent_iff_tendsto_one hb

/-- Grinstead–Snell Theorem 3.3 (PR-022). Stirling's formula: `n!` is asymptotically equal to
`√(2πn) (n/e)^n`. -/
@[kb "grinsteadsnell2006" "Theorem 3.3, p. 89"]
theorem gs_theorem_3_3 :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (Nat.factorial n : ℝ))
      (fun n : ℕ => Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n) := by
  simpa [mul_comm, mul_left_comm] using Stirling.factorial_isEquivalent_stirling

/-- Grinstead–Snell Theorem 3.4 (PR-025). Pascal's recursion for binomial coefficients. -/
@[kb "grinsteadsnell2006" "Theorem 3.4, p. 101"]
theorem gs_theorem_3_4 (n j : ℕ) :
    (n + 1).choose (j + 1) = n.choose j + n.choose (j + 1) :=
  Nat.choose_succ_succ' n j

/-- Grinstead–Snell Theorem 3.5 (PR-026). `C(n,j) = n!/(j!(n-j)!)` is the number of `j`-element
subsets of an `n`-element set, and it vanishes for `j > n`. -/
@[kb "grinsteadsnell2006" "Theorem 3.5, p. 102"]
theorem gs_theorem_3_5 {α : Type*} (s : Finset α) (j : ℕ) :
    (s.powersetCard j).card = s.card.choose j ∧
      (j ≤ s.card → s.card.choose j = s.card.factorial / (j.factorial * (s.card - j).factorial)) ∧
      (s.card < j → s.card.choose j = 0) :=
  ⟨Finset.card_powersetCard j s, Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_zero_of_lt⟩

/-- Grinstead–Snell Theorem 3.6 (PR-028). In `n` Bernoulli trials with success probability `p` the
probability of exactly `j` successes is `C(n,j) p^j q^(n-j)`. -/
@[kb "grinsteadsnell2006" "Theorem 3.6, p. 106"]
theorem gs_theorem_3_6 (n j : ℕ) (p : I) :
    (binomial n p).real {j} = (n.choose j) * (p : ℝ) ^ j * (1 - p : ℝ) ^ (n - j) :=
  binomial_real_singleton n j p

/-- Grinstead–Snell Definition 3.6 (PR-029). The binomial distribution is a probability measure,
the law of the number of successes among `n` Bernoulli trials. -/
@[kb "grinsteadsnell2006" "Definition 3.6, p. 107"]
theorem gs_definition_3_6 (n : ℕ) (p : I) :
    IsProbabilityMeasure (binomial n p) ∧
      binomial n p = (setBernoulli (Set.Iio n) p).map Set.ncard :=
  ⟨inferInstance, rfl⟩

/-- Grinstead–Snell Theorem 3.7 (PR-030). The binomial theorem. -/
@[kb "grinsteadsnell2006" "Theorem 3.7, p. 111"]
theorem gs_theorem_3_7 {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    (a + b) ^ n = ∑ j ∈ Finset.range (n + 1), a ^ j * b ^ (n - j) * (n.choose j) :=
  add_pow a b n

/-- Grinstead–Snell Corollary 3.1 (PR-030). Row sums of Pascal's triangle are `2^n` and the
alternating sums vanish for `n > 0`. -/
@[kb "grinsteadsnell2006" "Corollary 3.1, p. 111"]
theorem gs_corollary_3_1 (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), n.choose j) = 2 ^ n ∧
      (∑ j ∈ Finset.range (n + 1), ((-1) ^ j * n.choose j : ℤ)) = if n = 0 then 1 else 0 :=
  ⟨Nat.sum_range_choose n, Int.alternating_sum_range_choose⟩

/-- Grinstead–Snell Example 3.12 (PR-032). Hat-check problem: the number of fixed-point-free
permutations of `n` objects is the derangement number, and its proportion of all `n!`
permutations tends to `1/e`. -/
@[kb "grinsteadsnell2006" "Example 3.12, p. 113"]
theorem gs_example_3_12 (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (derangements α) = numDerangements (Fintype.card α) ∧
      Tendsto (fun n => (numDerangements n : ℝ) / n.factorial) atTop (𝓝 (Real.exp (-1))) :=
  ⟨card_derangements_eq_numDerangements α, numDerangements_tendsto_inv_e⟩

/-- Grinstead–Snell Definition 3.2 (PR-019). A `k`-permutation of a set is an injective listing of
`k` of its elements (an embedding `Fin k ↪ α`). -/
@[kb "grinsteadsnell2006" "Definition 3.2, p. 88"]
theorem gs_definition_3_2 {α : Type*} (k : ℕ) (f : Fin k ↪ α) : Function.Injective f :=
  f.injective

/-- Grinstead–Snell Definition 3.4 (PR-023). Position `i` is a record of the arrangement `σ` when its
value exceeds all values at earlier positions. -/
@[kb "grinsteadsnell2006" "Definition 3.4, p. 91"]
theorem gs_definition_3_4 {n : ℕ} (s : Equiv.Perm (Fin n)) (i : Fin n) :
    UndergradKB.Probability.IsRecord s i ↔ ∀ k : Fin n, k < i → s k < s i :=
  Iff.rfl

/-- Grinstead–Snell Definition 3.5 (PR-027). In a Bernoulli trials process the number of successes has
the binomial law. -/
@[kb "grinsteadsnell2006" "Definition 3.5, p. 104"]
theorem gs_definition_3_5 : type_of% @UndergradKB.Probability.hasLaw_sum_bernoulli :=
  @UndergradKB.Probability.hasLaw_sum_bernoulli

/-- Grinstead–Snell Theorem 3.8 (PR-031). Inclusion-exclusion for probabilities. -/
@[kb "grinsteadsnell2006" "Theorem 3.8, p. 112"]
theorem gs_theorem_3_8 : type_of% @UndergradKB.Probability.real_biUnion_eq_sum_inter :=
  @UndergradKB.Probability.real_biUnion_eq_sum_inter

/-- Grinstead–Snell Theorem 3.9 (PR-033). An `a`-shuffle followed by a `b`-shuffle corresponds to an
`ab`-shuffle. -/
@[kb "grinsteadsnell2006" "Theorem 3.9, p. 130"]
theorem gs_theorem_3_9 : type_of% @UndergradKB.Probability.exists_shuffle_pair_equiv :=
  @UndergradKB.Probability.exists_shuffle_pair_equiv

/-- Grinstead–Snell Theorem 3.10 (PR-033). Counting form: every ordering arises from equally many
pairs of an `a`-shuffle and a `b`-shuffle as from `ab`-shuffles. -/
@[kb "grinsteadsnell2006" "Theorem 3.10, p. 133"]
theorem gs_theorem_3_10 : type_of% @UndergradKB.Probability.card_shuffle_pairs_eq :=
  @UndergradKB.Probability.card_shuffle_pairs_eq

/-- Grinstead–Snell Theorem 3.11 (PR-034). An ordering with `r` rising sequences arises from
`C(n+a-r, n)` cut-interleaving pairs of an `a`-shuffle. -/
@[kb "grinsteadsnell2006" "Theorem 3.11, p. 134"]
theorem gs_theorem_3_11 : type_of% @UndergradKB.Probability.card_shuffles_eq_choose :=
  @UndergradKB.Probability.card_shuffles_eq_choose

/-- Grinstead–Snell Theorem 3.12 (PR-035). `a^n = ∑_r C(n+a-r, n) A(n,r)` with `A(n,r)` the Eulerian
numbers. -/
@[kb "grinsteadsnell2006" "Theorem 3.12, p. 135"]
theorem gs_theorem_3_12 : type_of% @UndergradKB.Probability.pow_eq_sum_choose_mul_eulerian :=
  @UndergradKB.Probability.pow_eq_sum_choose_mul_eulerian

/-- Grinstead–Snell Example 3.6 (PR-132). Poker hands: the number of hands and of four-of-a-kind hands. -/
@[kb "grinsteadsnell2006" "Example 3.6, p. 103"]
theorem gs_example_3_6 : type_of% @UndergradKB.Probability.poker_fourKind :=
  @UndergradKB.Probability.poker_fourKind

/-- Grinstead–Snell Example 3.6 (PR-132). Poker hands: the number of full houses. -/
@[kb "grinsteadsnell2006" "Example 3.6, p. 103"]
theorem gs_example_3_6_b : type_of% @UndergradKB.Probability.poker_fullHouse :=
  @UndergradKB.Probability.poker_fullHouse

/-- Grinstead–Snell Example 3.8 (PR-146). The number of heads in six fair tosses is three with probability `5/16`. -/
@[kb "grinsteadsnell2006" "Example 3.8, p. 106"]
theorem gs_example_3_8 : type_of% @UndergradKB.Probability.six_tosses_three_heads :=
  @UndergradKB.Probability.six_tosses_three_heads

/-- Grinstead–Snell Example 3.9 (PR-146). The number of sixes in four rolls of a die is one with probability `125/324`. -/
@[kb "grinsteadsnell2006" "Example 3.9, p. 106"]
theorem gs_example_3_9 : type_of% @UndergradKB.Probability.four_rolls_one_six :=
  @UndergradKB.Probability.four_rolls_one_six

end UndergradKB.Probability.Course
