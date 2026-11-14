import Mathlib.Probability.Kernel.Invariance
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesMarkovD
import UndergradKB.Probability.ExamplesMarkov
import UndergradKB.Probability.ExamplesMarkovB
import UndergradKB.Probability.ExamplesMarkovC
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovLLN
import UndergradKB.Probability.MarkovPassage
import UndergradKB.Probability.MarkovClt
import UndergradKB.Probability.ExamplesSteppingStone
import UndergradKB.Probability.MarkovCltDegenerate
import UndergradKB.Probability.MarkovVariance

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

/-! ## Worked examples (wave 4) -/

/-- Grinstead–Snell Example 11.4 (PR-181). For `a + b ≠ 0` the powers of the two-state matrix are `P^n = (1/(a+b)) [[b, a], [b, a]] + ((1-a-b)^n/(a+b)) [[a, -a], [-b, b]]`. -/
@[kb "grinsteadsnell2006" "Example 11.4, p. 417"]
theorem gs_example_11_4 : type_of% @UndergradKB.Probability.twoStateP_pow :=
  @UndergradKB.Probability.twoStateP_pow

/-- Grinstead–Snell Example 11.4 (PR-181). For `0 ≤ a, b ≤ 1` and `0 < a + b < 2` the powers `P^n` of the two-state chain converge to the matrix both of whose rows are `(b, a)/(a+b)`, and this row is... -/
@[kb "grinsteadsnell2006" "Example 11.4, p. 417"]
theorem gs_example_11_4_b : type_of% @UndergradKB.Probability.twoStateP_pow_tendsto :=
  @UndergradKB.Probability.twoStateP_pow_tendsto

/-- Grinstead–Snell Example 11.5 (PR-182). For the horse race matrix with three equal rows `(1/2, 1/4, 1/4)` one has `P^n = P` for every `n ≥ 1`. -/
@[kb "grinsteadsnell2006" "Example 11.5, p. 417"]
theorem gs_example_11_5 : type_of% @UndergradKB.Probability.horseMatrix_pow :=
  @UndergradKB.Probability.horseMatrix_pow

/-- Grinstead–Snell Example 11.5 (PR-182). The horse race chain is regular (already `P^1` is positive), and its unique fixed probability vector is `(1/2, 1/4, 1/4)`. -/
@[kb "grinsteadsnell2006" "Example 11.5, p. 417"]
theorem gs_example_11_5_b : type_of% @UndergradKB.Probability.horseMatrix_regular_fixed :=
  @UndergradKB.Probability.horseMatrix_regular_fixed

/-- Grinstead–Snell Example 11.6 (PR-183). The Harvard–Yale–Dartmouth chain is regular (`P^2` is positive) and its unique fixed probability vector is `(5/9, 2/9, 2/9)`. -/
@[kb "grinsteadsnell2006" "Example 11.6, p. 418"]
theorem gs_example_11_6 : type_of% @UndergradKB.Probability.hydMatrix_regular_fixed :=
  @UndergradKB.Probability.hydMatrix_regular_fixed

/-- Grinstead–Snell Example 11.7 (PR-183). The modified chain is absorbing, with Harvard (state `0`) the only absorbing state. -/
@[kb "grinsteadsnell2006" "Example 11.7, p. 418"]
theorem gs_example_11_7 : type_of% @UndergradKB.Probability.hydAbsMatrix_absorbing :=
  @UndergradKB.Probability.hydAbsMatrix_absorbing

/-- Grinstead–Snell Example 11.7 (PR-183). With the repository's fundamental matrix `N = (I - Q)⁻¹`, where `Q = [[.4, .3], [.1, .7]]` on the transient states Yale, Dartmouth (`1, 2`), one has `N =... -/
@[kb "grinsteadsnell2006" "Example 11.7, p. 418"]
theorem gs_example_11_7_b : type_of% @UndergradKB.Probability.hydAbs_fundamental :=
  @UndergradKB.Probability.hydAbs_fundamental

/-- Grinstead–Snell Example 11.7 (PR-183). The expected number of generations before the family enters Harvard, `t = N c`, is `4` from Yale and `14/3` from Dartmouth. -/
@[kb "grinsteadsnell2006" "Example 11.7, p. 418"]
theorem gs_example_11_7_c : type_of% @UndergradKB.Probability.hydAbs_time :=
  @UndergradKB.Probability.hydAbs_time

/-- Grinstead–Snell Example 11.9 (PR-184). The gene chain mated with a hybrid is regular (`P^2` is positive); its unique fixed probability vector is `(1/4, 1/2, 1/4)`. -/
@[kb "grinsteadsnell2006" "Example 11.9, p. 419"]
theorem gs_example_11_9 : type_of% @UndergradKB.Probability.geneHybrid_regular_fixed :=
  @UndergradKB.Probability.geneHybrid_regular_fixed

/-- Grinstead–Snell Example 11.10 (PR-184). The gene chain mated with a dominant is absorbing (`GG` is the only absorbing state; `Gg` reaches it in one step and `gg` in two). -/
@[kb "grinsteadsnell2006" "Example 11.10, p. 419"]
theorem gs_example_11_10 : type_of% @UndergradKB.Probability.geneDomMatrix_absorbing :=
  @UndergradKB.Probability.geneDomMatrix_absorbing

/-- Grinstead–Snell Example 11.10 (PR-184). The fundamental matrix of the dominant-mating chain, with `Q = [[1/2, 0], [1, 0]]` on the transient states `Gg, gg`, is `N = [[2, 0], [2, 1]]`. -/
@[kb "grinsteadsnell2006" "Example 11.10, p. 419"]
theorem gs_example_11_10_b : type_of% @UndergradKB.Probability.geneDom_fundamental :=
  @UndergradKB.Probability.geneDom_fundamental

/-- Grinstead–Snell Example 11.10 (PR-184). The expected number of generations until a dominant offspring is reached is `2` from a hybrid `Gg` and `3` from a recessive `gg`. -/
@[kb "grinsteadsnell2006" "Example 11.10, p. 419"]
theorem gs_example_11_10_c : type_of% @UndergradKB.Probability.geneDom_time :=
  @UndergradKB.Probability.geneDom_time

/-- Grinstead–Snell Example 11.11 (PR-185). The inbreeding chain is absorbing: the states `(GG,GG)` and `(gg,gg)` (states `0` and `5`) are absorbing and every state reaches one of them. -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem gs_example_11_11 : type_of% @UndergradKB.Probability.inbreedMatrix_absorbing :=
  @UndergradKB.Probability.inbreedMatrix_absorbing

/-- Grinstead–Snell Example 11.11 (PR-185). The fundamental matrix of the inbreeding chain (transient states `(GG,Gg), (GG,gg), (Gg,Gg), (Gg,gg)`) is `N = [[8/3, 1/6, 4/3, 2/3], [4/3, 4/3, 8/3, 4/3],... -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem gs_example_11_11_b : type_of% @UndergradKB.Probability.inbreed_fundamental :=
  @UndergradKB.Probability.inbreed_fundamental

/-- Grinstead–Snell Example 11.11 (PR-185). The expected numbers of generations before one of the two absorbing states is reached are `t = N c = (29/6, 20/3, 17/3, 29/6)` from the four transient states. -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem gs_example_11_11_c : type_of% @UndergradKB.Probability.inbreed_time :=
  @UndergradKB.Probability.inbreed_time

/-- Grinstead–Snell Example 11.11 (PR-185). The probabilities of eventual absorption in `(GG,GG)` and `(gg,gg)` are `B = N R`, namely `(3/4, 1/4), (1/2, 1/2), (1/2, 1/2), (1/4, 3/4)` from the four... -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem gs_example_11_11_d : type_of% @UndergradKB.Probability.inbreed_absorption_prob :=
  @UndergradKB.Probability.inbreed_absorption_prob

/-- Grinstead–Snell Example 11.26 (PR-186). For the Land of Oz chain, `I - P + W` (with `W` the matrix all of whose rows are the fixed vector `(2/5, 1/5, 2/5)`) equals `[[9/10, -1/20, 3/20], [-1/10,... -/
@[kb "grinsteadsnell2006" "Example 11.26, p. 466"]
theorem gs_example_11_26 : type_of% @UndergradKB.Probability.ozMatrix_fundamentalZ :=
  @UndergradKB.Probability.ozMatrix_fundamentalZ

/-- Grinstead–Snell Example 11.26 (PR-186). The repository's `Z` of the ergodic Oz chain, built from the unique fixed probability vector given by `meanFirstPassage_eq_fundamental`, is the matrix... -/
@[kb "grinsteadsnell2006" "Example 11.26, p. 466"]
theorem gs_example_11_26_b : type_of% @UndergradKB.Probability.ozMatrix_meanFirstPassage_Z :=
  @UndergradKB.Probability.ozMatrix_meanFirstPassage_Z


/-! ## Wave 5 course layer (this library) -/

/-- Grinstead–Snell §11.2 harmonic function (PR-123): in an absorbing chain a function `f` on the states with `P f = f` (a harmonic function) is determined by its values on the absorbing states: `f i = ∑_a B i a f a` for every transient state `i`, with `B = N R` the absorption probabilities. -/
@[kb "grinsteadsnell2006" "§11.2 harmonic function, p. 436"]
theorem gs_section_11_2_harmonic_function : type_of% @UndergradKB.Probability.harmonic_eq_absorption :=
  @UndergradKB.Probability.harmonic_eq_absorption

/-- Grinstead–Snell §11.1 Markov chain and transition matrix (PR-110): the Markov property for the path weights. Extending a path by one step to the state `s` multiplies its probability by the transition probability from the present state to `s`; so given the whole past, the next state depends only on the present state. -/
@[kb "grinsteadsnell2006" "§11.1 Markov chain and transition matrix, p. 413"]
theorem gs_section_11_1_markov_chain_and_transition_matrix : type_of% @UndergradKB.Probability.pathProb_snoc :=
  @UndergradKB.Probability.pathProb_snoc

/-- Grinstead–Snell §11.1 (PR-110): the path weights of a Markov chain form a probability distribution on the paths of length `n` (they are nonnegative, `pathProb_nonneg`, and sum to one). -/
@[kb "grinsteadsnell2006" "§11.1 Markov chain and transition matrix, p. 413"]
theorem gs_section_11_1_markov_chain_and_transition_matrix_b : type_of% @UndergradKB.Probability.sum_pathProb :=
  @UndergradKB.Probability.sum_pathProb

/-- Grinstead–Snell Example 11.12 (PR-213): the stepping stone matrix is a transition matrix (row stochastic). -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem gs_example_11_12 : type_of% @UndergradKB.Probability.steppingStone_mem :=
  @UndergradKB.Probability.steppingStone_mem

/-- Grinstead–Snell Example 11.12 (PR-213): the absorbing states of the stepping stone chain are exactly the one-color colorings. -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem gs_example_11_12_b : type_of% @UndergradKB.Probability.steppingStone_absorbing_iff :=
  @UndergradKB.Probability.steppingStone_absorbing_iff

/-- Grinstead–Snell Example 11.12 (PR-213): the stepping stone chain is an absorbing chain (the absorbing states are the one-color colorings, and from every coloring a one-color coloring is reachable). -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem gs_example_11_12_c : type_of% @UndergradKB.Probability.steppingStone_isAbsorbingChain :=
  @UndergradKB.Probability.steppingStone_isAbsorbingChain

/-- Grinstead–Snell Example 11.12 (PR-213), the book's statement (Exercise 11.2.32): starting from the non-absorbing coloring `σ`, the probability that the chain is absorbed in the one-color coloring of color `c` (the entry of `B = N R` of the absorbing chain) equals the initial proportion `#{s : σ s = c} / n²` of sites of color `c`. -/
@[kb "grinsteadsnell2006" "Example 11.12, p. 420"]
theorem gs_example_11_12_d : type_of% @UndergradKB.Probability.steppingStone_absorption_prob :=
  @UndergradKB.Probability.steppingStone_absorption_prob

/-- Grinstead–Snell Example 11.21 (PR-214): in the Land of Oz, whatever the weather on the first day (any initial distribution `u`), the proportion of rainy, nice and snowy days among the first `n + 1` days converges in probability to the long-run proportions `2/5, 1/5, 2/5`; so the expected counts in a year of 525 days are `525 · (2/5, 1/5, 2/5) = (210, 105, 210)`. -/
@[kb "grinsteadsnell2006" "Example 11.21, p. 447"]
theorem gs_example_11_21 : type_of% @UndergradKB.Probability.oz_year_lln :=
  @UndergradKB.Probability.oz_year_lln

/-! ## Wave 6 course layer (this library) -/

/-- Grinstead–Snell Theorem 11.17 (PR-121), the degenerate case. Let `P` be an ergodic chain with fixed probability vector `w` and fundamental matrix `Z = (I - P + W)⁻¹`. -/
@[kb "grinsteadsnell2006" "Theorem 11.17, p. 472"]
theorem gs_theorem_11_17_b : type_of% @UndergradKB.Probability.markov_clt_degenerate :=
  @UndergradKB.Probability.markov_clt_degenerate

/-- Grinstead–Snell Theorem 11.17 (PR-121), the asymptotic variance (equation 11.10): for a regular chain with fixed probability vector `w`, fundamental matrix `Z = (I - P + W)⁻¹` and any initial probability vector `u`, the variance of the number `S_j^(n)` of visits to `j` among the times `0, …, n`, computed about `(n+1) w_j` and divided by `n + 1`, tends to `σ_j² = 2 w_j z_jj - w_j - w_j²`. -/
@[kb "grinsteadsnell2006" "Theorem 11.17, p. 472"]
theorem gs_theorem_11_17_c : type_of% @UndergradKB.Probability.markov_asymptotic_variance :=
  @UndergradKB.Probability.markov_asymptotic_variance

end UndergradKB.Probability.Course
