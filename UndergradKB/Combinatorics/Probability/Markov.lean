import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import UndergradKB.Common.Attr

/-!
# Finite Markov chains: transition matrices, regular and absorbing chains
(Keller–Trotter, Section 16.3)

A finite Markov chain on the states `n` is given by its transition matrix, a real matrix with
nonnegative entries and all row sums `1` (Mathlib's `Matrix.rowStochastic`).
-/

namespace UndergradKB.Combinatorics

open Matrix

namespace Markov

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- CO-251. `P` is the transition matrix of a finite Markov chain on the states `n`: entry
`P j k` is the (time independent) probability of moving from state `j` to state `k`; thus `P` is a
stochastic matrix (entries `≥ 0`, each row summing to `1`). Every stochastic matrix arises
this way. -/
@[kb "kellertrotter2017" "Definition (unnumbered) Markov chain, transition matrix, p. 344"]
def IsTransition (P : Matrix n n ℝ) : Prop := P ∈ Matrix.rowStochastic ℝ n

lemma IsTransition.nonneg {P : Matrix n n ℝ} (h : IsTransition P) (j k : n) : 0 ≤ P j k :=
  nonneg_of_mem_rowStochastic h

lemma IsTransition.sum_row {P : Matrix n n ℝ} (h : IsTransition P) (j : n) : ∑ k, P j k = 1 :=
  sum_row_of_mem_rowStochastic h j

/-- Powers of a transition matrix are transition matrices (the `m`-step transition
probabilities). -/
lemma IsTransition.pow {P : Matrix n n ℝ} (h : IsTransition P) (m : ℕ) : IsTransition (P ^ m) :=
  pow_mem h m

/-- CO-252. A transition matrix is regular if some power of it has only positive entries. -/
@[kb "kellertrotter2017" "Definition (unnumbered) regular transition matrix, p. 345"]
def IsRegular (P : Matrix n n ℝ) : Prop :=
  IsTransition P ∧ ∃ m : ℕ, ∀ j k, 0 < (P ^ m) j k

/-- CO-254. A state `i` is absorbing if the chain stays there forever: `p(i,i) = 1` and
`p(i,j) = 0` for `j ≠ i`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) absorbing state, p. 345"]
def IsAbsorbingState (P : Matrix n n ℝ) (i : n) : Prop :=
  P i i = 1 ∧ ∀ j, j ≠ i → P i j = 0

/-- CO-254. A Markov chain is absorbing if it has an absorbing state and from every
non-absorbing state some absorbing state can be reached (with positive probability after
some number of steps). -/
@[kb "kellertrotter2017" "Definition (unnumbered) absorbing chain, p. 345"]
def IsAbsorbingChain (P : Matrix n n ℝ) : Prop :=
  IsTransition P ∧ (∃ i, IsAbsorbingState P i) ∧
    ∀ j, ¬ IsAbsorbingState P j → ∃ i, IsAbsorbingState P i ∧ ∃ m : ℕ, 0 < (P ^ m) j i

/-- For a transition matrix, `p(i,i) = 1` already forces `p(i,j) = 0` for `j ≠ i`. -/
lemma IsTransition.absorbing_iff {P : Matrix n n ℝ} (h : IsTransition P) (i : n) :
    IsAbsorbingState P i ↔ P i i = 1 := by
  refine ⟨fun h' => h'.1, fun h1 => ⟨h1, fun j hj => ?_⟩⟩
  have hsum := h.sum_row i
  have hle : ∑ k ∈ ({i, j} : Finset n), P i k ≤ ∑ k, P i k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => h.nonneg i k)
  rw [Finset.sum_pair hj.symm, h1, hsum] at hle
  exact le_antisymm (by linarith) (h.nonneg i j)

/-- A matrix with all entries positive and all row sums `1` is a regular transition matrix. -/
lemma isRegular_of_pos {P : Matrix n n ℝ} (h : IsTransition P) (hpos : ∀ j k, 0 < P j k) :
    IsRegular P := ⟨h, 1, by simpa using hpos⟩

end Markov

end UndergradKB.Combinatorics
