import Mathlib.Probability.Kernel.Invariance
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesMarkov
import UndergradKB.Probability.ExamplesMarkovB
import UndergradKB.Probability.ExamplesMarkovC
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovLLN
import UndergradKB.Probability.MarkovPassage
import UndergradKB.Probability.MarkovClt

/-!
# Course layer, Chapter 11 (Grinstead–Snell, Markov Chains)

Thin wrappers citing the book's numbered results of Chapter 11 by number: Mathlib instances, and the
theorems proved in `UndergradKB.Probability.Markov*` (each wrapper has the statement of the proved theorem,
via `type_of%`; for definitions the wrapper unfolds the definition).
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory

/-- Grinstead–Snell §11.5 reversible chain (PR-122). A Markov chain with transition kernel `κ`
that satisfies detailed balance with respect to `π` (the kernel analogue of `w_i p_ij = w_j p_ji`)
leaves `π` invariant. -/
@[kb "grinsteadsnell2006" "§11.5 reversible chain, p. 471"]
theorem gs_section_11_5_reversible_chain {α : Type*} [MeasurableSpace α] (κ : Kernel α α)
    [IsMarkovKernel κ] (π : Measure α) (h : Kernel.IsReversible κ π) :
    Kernel.Invariant κ π :=
  h.invariant

/-- Grinstead–Snell Theorem 11.1 (PR-111). The `(i,j)` entry of `P^n` is the probability of moving from
`i` to `j` in `n` steps (total weight of the paths). -/
@[kb "grinsteadsnell2006" "Theorem 11.1, p. 415"]
theorem gs_theorem_11_1 : type_of% @UndergradKB.Probability.markov_nstep_prob :=
  @UndergradKB.Probability.markov_nstep_prob

/-- Grinstead–Snell Theorem 11.2 (PR-111). The distribution after `n` steps is `u P^n`. -/
@[kb "grinsteadsnell2006" "Theorem 11.2, p. 417"]
theorem gs_theorem_11_2 : type_of% @UndergradKB.Probability.markov_dist_after_n_steps :=
  @UndergradKB.Probability.markov_dist_after_n_steps

/-- Grinstead–Snell Theorem 11.2 (PR-111), probability-vector form: `u P^n` is again a probability vector. -/
@[kb "grinsteadsnell2006" "Theorem 11.2, p. 417"]
theorem gs_theorem_11_2_prob : type_of% @UndergradKB.Probability.markov_dist_after_n_steps_prob :=
  @UndergradKB.Probability.markov_dist_after_n_steps_prob

section Defs

open Matrix

set_option linter.unusedSectionVars false

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Grinstead–Snell Definition 11.1 (PR-112), absorbing state: `i` is absorbing when `p_ii = 1`. -/
@[kb "grinsteadsnell2006" "Definition 11.1, p. 424"]
theorem gs_definition_11_1 (P : Matrix S S ℝ) (i : S) : IsAbsorbingState P i ↔ P i i = 1 :=
  Iff.rfl

/-- Grinstead–Snell Definition 11.1 (PR-112), absorbing chain: at least one absorbing state, and an
absorbing state can be reached from every state. -/
@[kb "grinsteadsnell2006" "Definition 11.1, p. 424"]
theorem gs_definition_11_1_chain (P : Matrix S S ℝ) :
    IsAbsorbingChain P ↔
      (∃ a, IsAbsorbingState P a) ∧ ∀ i, ∃ n a, IsAbsorbingState P a ∧ 0 < (P ^ n) i a :=
  Iff.rfl

/-- Grinstead–Snell Definition 11.2 (PR-112). The transient states are the non-absorbing ones. -/
@[kb "grinsteadsnell2006" "Definition 11.2, p. 424"]
theorem gs_definition_11_2 (P : Matrix S S ℝ) (i : Transient P) : ¬ IsAbsorbingState P i.1 :=
  i.2

/-- Grinstead–Snell Definition 11.4 (PR-115). An ergodic chain: stochastic matrix, irreducible (every
state reachable from every state). -/
@[kb "grinsteadsnell2006" "Definition 11.4, p. 441"]
theorem gs_definition_11_4 (P : Matrix S S ℝ) :
    IsErgodicChain P ↔ P ∈ rowStochastic ℝ S ∧ P.IsIrreducible :=
  Iff.rfl

/-- Grinstead–Snell Definition 11.5 (PR-115). A regular chain: stochastic matrix with some positive power
having all entries positive. -/
@[kb "grinsteadsnell2006" "Definition 11.5, p. 441"]
theorem gs_definition_11_5 (P : Matrix S S ℝ) :
    IsRegularChain P ↔ P ∈ rowStochastic ℝ S ∧ ∃ N > 0, ∀ i j, 0 < (P ^ N) i j :=
  Iff.rfl

/-- Grinstead–Snell Definition 11.6 (PR-116), fixed row vector: `w P = w`. -/
@[kb "grinsteadsnell2006" "Definition 11.6, p. 443"]
theorem gs_definition_11_6 (P : Matrix S S ℝ) (w : S → ℝ) : IsFixedRow P w ↔ w ᵥ* P = w :=
  Iff.rfl

/-- Grinstead–Snell Definition 11.6 (PR-116), fixed column vector: `P x = x`. -/
@[kb "grinsteadsnell2006" "Definition 11.6, p. 443"]
theorem gs_definition_11_6_column (P : Matrix S S ℝ) (x : S → ℝ) : IsFixedColumn P x ↔ P *ᵥ x = x :=
  Iff.rfl

/-- Grinstead–Snell Definition 11.7 (PR-120). The mean first passage time is the sum of the tail
probabilities `P(T > n)` of the first passage time. -/
@[kb "grinsteadsnell2006" "Definition 11.7, p. 461"]
theorem gs_definition_11_7 (P : Matrix S S ℝ) (i j : S) :
    meanFirstPassage P i j = ∑' n, notYetHit P j n i :=
  rfl

/-- Grinstead–Snell Definition 11.8 (PR-120). The mean recurrence time: one step, then the mean first
passage time back to the starting state. -/
@[kb "grinsteadsnell2006" "Definition 11.8, p. 462"]
theorem gs_definition_11_8 (P : Matrix S S ℝ) (i : S) :
    meanRecurrence P i = 1 + ∑ k, P i k * meanFirstPassage P k i :=
  rfl

/-- Grinstead–Snell Proposition 11.1 (PR-120). For an ergodic chain with fixed probability vector `w`
and `W` the matrix with rows `w`, the matrix `I - P + W` is invertible. -/
@[kb "grinsteadsnell2006" "Proposition 11.1, p. 465"]
theorem gs_proposition_11_1 [Nonempty S] {P : Matrix S S ℝ} (h : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      IsUnit (1 - P + rowsMatrix w) :=
  let ⟨w, a, b, c, d, _⟩ := UndergradKB.Probability.meanFirstPassage_eq_fundamental h
  ⟨w, a, b, c, d⟩

end Defs

/-- Grinstead–Snell Theorem 11.3 (PR-113). In an absorbing chain absorption occurs with probability 1. -/
@[kb "grinsteadsnell2006" "Theorem 11.3, p. 425"]
theorem gs_theorem_11_3 : type_of% @UndergradKB.Probability.absorption_certain :=
  @UndergradKB.Probability.absorption_certain

/-- Grinstead–Snell Theorem 11.3 (PR-113), matrix form: `Q^n → 0`. -/
@[kb "grinsteadsnell2006" "Theorem 11.3, p. 425"]
theorem gs_theorem_11_3_pow : type_of% @UndergradKB.Probability.absorbQ_pow_tendsto_zero :=
  @UndergradKB.Probability.absorbQ_pow_tendsto_zero

/-- Grinstead–Snell Definition 11.3 (PR-114). The fundamental matrix `N = (I - Q)⁻¹ = I + Q + Q² + ⋯`. -/
@[kb "grinsteadsnell2006" "Definition 11.3, p. 427"]
theorem gs_definition_11_3 : type_of% @UndergradKB.Probability.fundamentalMatrix_spec :=
  @UndergradKB.Probability.fundamentalMatrix_spec

/-- Grinstead–Snell Theorem 11.4 (PR-114). `N i j` is the expected number of visits to `j` from `i`. -/
@[kb "grinsteadsnell2006" "Theorem 11.4, p. 426"]
theorem gs_theorem_11_4 : type_of% @UndergradKB.Probability.hasSum_visits :=
  @UndergradKB.Probability.hasSum_visits

/-- Grinstead–Snell Theorem 11.5 (PR-114). The expected time to absorption is `t = N c`. -/
@[kb "grinsteadsnell2006" "Theorem 11.5, p. 427"]
theorem gs_theorem_11_5 : type_of% @UndergradKB.Probability.hasSum_absorption_time :=
  @UndergradKB.Probability.hasSum_absorption_time

/-- Grinstead–Snell Theorem 11.6 (PR-114). The absorption probabilities are `B = N R`. -/
@[kb "grinsteadsnell2006" "Theorem 11.6, p. 428"]
theorem gs_theorem_11_6 : type_of% @UndergradKB.Probability.absorption_prob_tendsto :=
  @UndergradKB.Probability.absorption_prob_tendsto

/-- Grinstead–Snell Theorem 11.6 (PR-114), the absorption probabilities sum to one. -/
@[kb "grinsteadsnell2006" "Theorem 11.6, p. 428"]
theorem gs_theorem_11_6_sum : type_of% @UndergradKB.Probability.sum_absorption_prob :=
  @UndergradKB.Probability.sum_absorption_prob

/-- Grinstead–Snell Theorem 11.7 (PR-117). For a regular chain `P^n` converges to a matrix with equal
positive rows. -/
@[kb "grinsteadsnell2006" "Theorem 11.7, p. 442"]
theorem gs_theorem_11_7 : type_of% @UndergradKB.Probability.regular_pow_tendsto :=
  @UndergradKB.Probability.regular_pow_tendsto

/-- Grinstead–Snell Theorem 11.8 (PR-117). The limit row `w` is the unique fixed probability vector. -/
@[kb "grinsteadsnell2006" "Theorem 11.8, p. 443"]
theorem gs_theorem_11_8 : type_of% @UndergradKB.Probability.regular_fixed_vector :=
  @UndergradKB.Probability.regular_fixed_vector

/-- Grinstead–Snell Theorem 11.9 (PR-117). For a regular chain `u P^n → w`. -/
@[kb "grinsteadsnell2006" "Theorem 11.9, p. 444"]
theorem gs_theorem_11_9 : type_of% @UndergradKB.Probability.regular_distribution_tendsto :=
  @UndergradKB.Probability.regular_distribution_tendsto

/-- Grinstead–Snell Theorem 11.10 (PR-118). An ergodic chain has a unique positive fixed probability vector. -/
@[kb "grinsteadsnell2006" "Theorem 11.10, p. 446"]
theorem gs_theorem_11_10 : type_of% @UndergradKB.Probability.ergodic_fixed_vector :=
  @UndergradKB.Probability.ergodic_fixed_vector

/-- Grinstead–Snell Theorem 11.11 (PR-118). For an ergodic chain the Cesàro averages of `P^n` converge to `W`. -/
@[kb "grinsteadsnell2006" "Theorem 11.11, p. 446"]
theorem gs_theorem_11_11 : type_of% @UndergradKB.Probability.ergodic_cesaro_tendsto :=
  @UndergradKB.Probability.ergodic_cesaro_tendsto

/-- Grinstead–Snell Theorem 11.12 (PR-119). Law of large numbers for ergodic chains. -/
@[kb "grinsteadsnell2006" "Theorem 11.12, p. 447"]
theorem gs_theorem_11_12 : type_of% @UndergradKB.Probability.markov_lln :=
  @UndergradKB.Probability.markov_lln

/-- Grinstead–Snell Lemma 11.1 (PR-117). If all entries of `P` are at least `ε`, the oscillation of `P y`
is at most `1 - 2ε` times that of `y`. -/
@[kb "grinsteadsnell2006" "Lemma 11.1, p. 456"]
theorem gs_lemma_11_1 : type_of% @UndergradKB.Probability.osc_mulVec_le_of_entries_ge :=
  @UndergradKB.Probability.osc_mulVec_le_of_entries_ge

/-- Grinstead–Snell Theorem 11.13 (PR-117), fundamental limit theorem for regular chains: `P^n → W`.
(Proved as `regular_pow_tendsto`, the same statement as Theorem 11.7 here.) -/
@[kb "grinsteadsnell2006" "Theorem 11.13, p. 456"]
theorem gs_theorem_11_13 : type_of% @UndergradKB.Probability.regular_pow_tendsto :=
  @UndergradKB.Probability.regular_pow_tendsto

/-- Grinstead–Snell Theorem 11.14 (PR-117). For a regular chain and any initial probability vector `u`,
`u P^n → w`. -/
@[kb "grinsteadsnell2006" "Theorem 11.14, p. 458"]
theorem gs_theorem_11_14 : type_of% @UndergradKB.Probability.regular_distribution_tendsto :=
  @UndergradKB.Probability.regular_distribution_tendsto

/-- Grinstead–Snell Theorem 11.15 (PR-120). For an ergodic chain the mean recurrence time is `r_i = 1/w_i`. -/
@[kb "grinsteadsnell2006" "Theorem 11.15, p. 463"]
theorem gs_theorem_11_15 : type_of% @UndergradKB.Probability.meanRecurrence_eq_inv :=
  @UndergradKB.Probability.meanRecurrence_eq_inv

/-- Grinstead–Snell Corollary 11.1 (PR-120). For an ergodic chain the fixed probability vector has strictly
positive entries (stated with the rest of Theorem 11.10). -/
@[kb "grinsteadsnell2006" "Corollary 11.1, p. 464"]
theorem gs_corollary_11_1 : type_of% @UndergradKB.Probability.ergodic_fixed_vector :=
  @UndergradKB.Probability.ergodic_fixed_vector

/-- Grinstead–Snell Theorem 11.16 (PR-120). Mean first passage times from the fundamental matrix
`Z = (I - P + W)⁻¹`: `m_ij = (z_jj - z_ij)/w_j`. -/
@[kb "grinsteadsnell2006" "Theorem 11.16, p. 467"]
theorem gs_theorem_11_16 : type_of% @UndergradKB.Probability.meanFirstPassage_eq_fundamental :=
  @UndergradKB.Probability.meanFirstPassage_eq_fundamental

/-- Grinstead–Snell Theorem 11.17 (PR-121). Central limit theorem for ergodic chains: for `σ_j² > 0`,
`P(r < (S_j^(n) - n w_j)/√(n σ_j²) < s) → ∫_r^s φ` for every initial distribution. -/
@[kb "grinsteadsnell2006" "Theorem 11.17, p. 472"]
theorem gs_theorem_11_17 : type_of% @UndergradKB.Probability.markov_clt :=
  @UndergradKB.Probability.markov_clt

/-- Grinstead–Snell Example 11.1 (PR-143). The Land of Oz matrix is a transition matrix. -/
@[kb "grinsteadsnell2006" "Example 11.1, p. 414"]
theorem gs_example_11_1 : type_of% @UndergradKB.Probability.ozMatrix_mem :=
  @UndergradKB.Probability.ozMatrix_mem

/-- Grinstead–Snell Example 11.2 (PR-160). The two-step matrix of the Land of Oz chain. -/
@[kb "grinsteadsnell2006" "Example 11.2, p. 415"]
theorem gs_example_11_2 : type_of% @UndergradKB.Probability.ozMatrix_sq :=
  @UndergradKB.Probability.ozMatrix_sq

/-- Grinstead–Snell Example 11.2 (PR-160). The three-step matrix of the Land of Oz chain. -/
@[kb "grinsteadsnell2006" "Example 11.2, p. 415"]
theorem gs_example_11_2_b : type_of% @UndergradKB.Probability.ozMatrix_cube :=
  @UndergradKB.Probability.ozMatrix_cube

/-- Grinstead–Snell Example 11.3 (PR-160). The distribution after three steps from the uniform initial vector. -/
@[kb "grinsteadsnell2006" "Example 11.3, p. 417"]
theorem gs_example_11_3 : type_of% @UndergradKB.Probability.ozMatrix_u3 :=
  @UndergradKB.Probability.ozMatrix_u3

/-- Grinstead–Snell Example 11.8 (PR-145). The Ehrenfest matrix with four balls. -/
@[kb "grinsteadsnell2006" "Example 11.8, p. 418"]
theorem gs_example_11_8 : type_of% @UndergradKB.Probability.ehrenfest_four :=
  @UndergradKB.Probability.ehrenfest_four

/-- Grinstead–Snell Example 11.8 (PR-145). The Ehrenfest chain is a transition matrix. -/
@[kb "grinsteadsnell2006" "Example 11.8, p. 418"]
theorem gs_example_11_8_b : type_of% @UndergradKB.Probability.ehrenfest_mem :=
  @UndergradKB.Probability.ehrenfest_mem

/-- Grinstead–Snell Example 11.13 (PR-144). The drunkard's walk is an absorbing chain. -/
@[kb "grinsteadsnell2006" "Example 11.13, p. 424"]
theorem gs_example_11_13 : type_of% @UndergradKB.Probability.drunkP_isAbsorbingChain :=
  @UndergradKB.Probability.drunkP_isAbsorbingChain

/-- Grinstead–Snell Example 11.14 (PR-144). The fundamental matrix of the drunkard's walk. -/
@[kb "grinsteadsnell2006" "Example 11.14, p. 427"]
theorem gs_example_11_14 : type_of% @UndergradKB.Probability.drunk_fundamentalMatrix :=
  @UndergradKB.Probability.drunk_fundamentalMatrix

/-- Grinstead–Snell Example 11.14 (PR-144). The expected number of steps before absorption in the drunkard's walk. -/
@[kb "grinsteadsnell2006" "Example 11.14, p. 427"]
theorem gs_example_11_14_b : type_of% @UndergradKB.Probability.drunk_absorption_time :=
  @UndergradKB.Probability.drunk_absorption_time

/-- Grinstead–Snell Example 11.15 (PR-144). The absorption probabilities at `0` in the drunkard's walk. -/
@[kb "grinsteadsnell2006" "Example 11.15, p. 428"]
theorem gs_example_11_15 : type_of% @UndergradKB.Probability.drunk_absorption_zero :=
  @UndergradKB.Probability.drunk_absorption_zero

/-- Grinstead–Snell Example 11.15 (PR-144). The absorption probabilities at `4` in the drunkard's walk. -/
@[kb "grinsteadsnell2006" "Example 11.15, p. 428"]
theorem gs_example_11_15_b : type_of% @UndergradKB.Probability.drunk_absorption_four :=
  @UndergradKB.Probability.drunk_absorption_four

/-- Grinstead–Snell Example 11.16 (PR-145). The chain `[[0,1],[1,0]]` is ergodic but not regular. -/
@[kb "grinsteadsnell2006" "Example 11.16, p. 441"]
theorem gs_example_11_16 : type_of% @UndergradKB.Probability.flipChain_ergodic_not_regular :=
  @UndergradKB.Probability.flipChain_ergodic_not_regular

/-- Grinstead–Snell Example 11.17 (PR-145). The Ehrenfest chain is ergodic but not regular. -/
@[kb "grinsteadsnell2006" "Example 11.17, p. 441"]
theorem gs_example_11_17 : type_of% @UndergradKB.Probability.ehrenfest_ergodic_not_regular :=
  @UndergradKB.Probability.ehrenfest_ergodic_not_regular

/-- Grinstead–Snell Example 11.18 (PR-160). Every initial distribution of the Land of Oz chain converges. -/
@[kb "grinsteadsnell2006" "Example 11.18, p. 443"]
theorem gs_example_11_18 : type_of% @UndergradKB.Probability.ozMatrix_distribution_tendsto :=
  @UndergradKB.Probability.ozMatrix_distribution_tendsto

/-- Grinstead–Snell Example 11.19 (PR-143). The Land of Oz chain is regular. -/
@[kb "grinsteadsnell2006" "Example 11.19, p. 444"]
theorem gs_example_11_19 : type_of% @UndergradKB.Probability.ozMatrix_regular :=
  @UndergradKB.Probability.ozMatrix_regular

/-- Grinstead–Snell Example 11.19 (PR-143). The powers of the Land of Oz matrix converge to the limiting matrix. -/
@[kb "grinsteadsnell2006" "Example 11.19, p. 444"]
theorem gs_example_11_19_b : type_of% @UndergradKB.Probability.ozMatrix_pow_tendsto :=
  @UndergradKB.Probability.ozMatrix_pow_tendsto

/-- Grinstead–Snell Example 11.20 (PR-143). The fixed probability vector of the Land of Oz chain. -/
@[kb "grinsteadsnell2006" "Example 11.20, p. 444"]
theorem gs_example_11_20 : type_of% @UndergradKB.Probability.ozMatrix_fixed :=
  @UndergradKB.Probability.ozMatrix_fixed

/-- Grinstead–Snell Example 11.22 (PR-161). The maze matrix is a transition matrix. -/
@[kb "grinsteadsnell2006" "Example 11.22, p. 448"]
theorem gs_example_11_22 : type_of% @UndergradKB.Probability.mazeP_mem :=
  @UndergradKB.Probability.mazeP_mem

/-- Grinstead–Snell Example 11.22 (PR-161). The maze chain is ergodic. -/
@[kb "grinsteadsnell2006" "Example 11.22, p. 448"]
theorem gs_example_11_22_b : type_of% @UndergradKB.Probability.mazeP_ergodic :=
  @UndergradKB.Probability.mazeP_ergodic

/-- Grinstead–Snell Example 11.22 (PR-161). The fixed probability vector of the maze chain. -/
@[kb "grinsteadsnell2006" "Example 11.22, p. 448"]
theorem gs_example_11_22_c : type_of% @UndergradKB.Probability.mazeP_fixed :=
  @UndergradKB.Probability.mazeP_fixed

/-- Grinstead–Snell Example 11.23 (PR-145). The fixed probability vector of the Ehrenfest chain. -/
@[kb "grinsteadsnell2006" "Example 11.23, p. 449"]
theorem gs_example_11_23 : type_of% @UndergradKB.Probability.ehrenfest_fixed :=
  @UndergradKB.Probability.ehrenfest_fixed

/-- Grinstead–Snell Example 11.23 (PR-145). The fixed vector of the Ehrenfest chain with four balls. -/
@[kb "grinsteadsnell2006" "Example 11.23, p. 449"]
theorem gs_example_11_23_b : type_of% @UndergradKB.Probability.ehrenfest_four_fixed :=
  @UndergradKB.Probability.ehrenfest_four_fixed

/-- Grinstead–Snell Example 11.24 (PR-161). Expected steps to first reach the center in the maze chain. -/
@[kb "grinsteadsnell2006" "Example 11.24, p. 461"]
theorem gs_example_11_24 : type_of% @UndergradKB.Probability.mazeP_meanFirstPassage_center :=
  @UndergradKB.Probability.mazeP_meanFirstPassage_center

/-- Grinstead–Snell Example 11.25 (PR-161). The mean recurrence times of the maze chain. -/
@[kb "grinsteadsnell2006" "Example 11.25, p. 464"]
theorem gs_example_11_25 : type_of% @UndergradKB.Probability.mazeP_meanRecurrence :=
  @UndergradKB.Probability.mazeP_meanRecurrence

/-- Grinstead–Snell Example 11.27 (PR-143). The mean recurrence times of the Land of Oz chain. -/
@[kb "grinsteadsnell2006" "Example 11.27, p. 468"]
theorem gs_example_11_27 : type_of% @UndergradKB.Probability.ozMatrix_meanRecurrence :=
  @UndergradKB.Probability.ozMatrix_meanRecurrence

/-- Grinstead–Snell Example 11.27 (PR-143). The mean first passage matrix of the Land of Oz chain. -/
@[kb "grinsteadsnell2006" "Example 11.27, p. 468"]
theorem gs_example_11_27_b : type_of% @UndergradKB.Probability.ozMatrix_meanFirstPassage :=
  @UndergradKB.Probability.ozMatrix_meanFirstPassage

/-- Grinstead–Snell Example 11.28 (PR-162). The mean recurrence time in the Ehrenfest urn with `m` balls. -/
@[kb "grinsteadsnell2006" "Example 11.28, p. 469"]
theorem gs_example_11_28 : type_of% @UndergradKB.Probability.ehrenfest_meanRecurrence :=
  @UndergradKB.Probability.ehrenfest_meanRecurrence

/-- Grinstead–Snell Example 11.28 (PR-162). The mean recurrence time in the Ehrenfest urn with `2n` balls. -/
@[kb "grinsteadsnell2006" "Example 11.28, p. 469"]
theorem gs_example_11_28_b : type_of% @UndergradKB.Probability.ehrenfest_two_mul_meanRecurrence :=
  @UndergradKB.Probability.ehrenfest_two_mul_meanRecurrence

end UndergradKB.Probability.Course
