import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-! # Finite Markov chains: transition matrices and n-step probabilities

Grinstead–Snell, chapter 11, §11.1. A finite Markov chain on the state space `S` is given by a transition matrix
`P : Matrix S S ℝ` in Mathlib's `Matrix.rowStochastic ℝ S` (nonnegative entries, rows summing to one) and an initial
distribution `u : S → ℝ` (a probability row vector). The probability of a path `x 0, x 1, …, x n` is
`u (x 0) * P (x 0) (x 1) * ⋯ * P (x (n-1)) (x n)` (`pathProb`); these weights form a probability distribution on
paths, the next step depends only on the present state (`pathProb_snoc`), and summing over the paths that end in `j`
gives the `j`-th entry of `u P^n` (Theorems 11.1 and 11.2). -/

namespace UndergradKB.Probability

open Matrix Finset

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The probability of the path `x 0, …, x n` of a Markov chain with initial distribution `u` and transition matrix
`P` (the book's tree measure on the first `n` steps of the chain). -/
noncomputable def pathProb (u : S → ℝ) (P : Matrix S S ℝ) (n : ℕ) (x : Fin (n + 1) → S) : ℝ :=
  u (x 0) * ∏ k : Fin n, P (x k.castSucc) (x k.succ)

omit [Fintype S] [DecidableEq S] in
/-- Grinstead–Snell §11.1 Markov chain and transition matrix (PR-110): the Markov property for the path weights.
Extending a path by one step to the state `s` multiplies its probability by the transition probability from the
present state to `s`; so given the whole past, the next state depends only on the present state. -/
@[kb "grinsteadsnell2006" "§11.1 Markov chain and transition matrix, p. 413"]
theorem pathProb_snoc (u : S → ℝ) (P : Matrix S S ℝ) (n : ℕ) (x : Fin (n + 1) → S) (s : S) :
    pathProb u P (n + 1) (Fin.snoc x s) = pathProb u P n x * P (x (Fin.last n)) s := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc x s : Fin (n + 2) → S) 0 = x 0 :=
    Fin.snoc_castSucc (α := fun _ => S) (p := x) (x := s) (i := 0)
  have h1 : ∀ i : Fin n, (Fin.snoc x s : Fin (n + 2) → S) i.castSucc.succ = x i.succ := by
    intro i
    rw [Fin.succ_castSucc]
    exact Fin.snoc_castSucc (α := fun _ => S) (p := x) (x := s) (i := i.succ)
  have h2 : (Fin.snoc x s : Fin (n + 2) → S) (Fin.last n).succ = s := by
    rw [Fin.succ_last]
    exact Fin.snoc_last (α := fun _ => S) (p := x) (x := s)
  simp only [h0, h1, h2, Fin.snoc_castSucc]
  ring

/-- Grinstead–Snell §11.1 (PR-110): the path weights of a Markov chain are nonnegative when the initial
distribution and the transition matrix are. -/
theorem pathProb_nonneg {u : S → ℝ} {P : Matrix S S ℝ} (hu : ∀ i, 0 ≤ u i) (hP : P ∈ rowStochastic ℝ S)
    (n : ℕ) (x : Fin (n + 1) → S) : 0 ≤ pathProb u P n x :=
  mul_nonneg (hu _) (prod_nonneg fun _ _ => nonneg_of_mem_rowStochastic hP)

/-- The sum of the path weights over the paths of length `n` ending in `j` is the `j`-th entry of `u P^n`
(general form, no hypothesis on `u` or `P`). -/
theorem sum_pathProb_last (u : S → ℝ) (P : Matrix S S ℝ) (n : ℕ) (j : S) :
    ∑ x : Fin (n + 1) → S with x (Fin.last n) = j, pathProb u P n x = (u ᵥ* P ^ n) j := by
  induction n generalizing j with
  | zero =>
    rw [sum_filter, pow_zero, vecMul_one]
    rw [← (Equiv.funUnique (Fin 1) S).symm.sum_comp]
    simp [pathProb, Fin.last]
  | succ n ih =>
    rw [sum_filter]
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => S)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.snocEquiv_apply, Fin.snoc_last, pathProb_snoc]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : Fin (n + 1) → S => x (Fin.last n))]
    have : ∀ k : S, ∑ x ∈ (univ : Finset (Fin (n + 1) → S)) with x (Fin.last n) = k,
        pathProb u P n x * P (x (Fin.last n)) j = (u ᵥ* P ^ n) k * P k j := by
      intro k
      rw [← ih k, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    simp only [this]
    rw [pow_succ, ← vecMul_vecMul]
    rfl

/-- Grinstead–Snell Theorem 11.2 (PR-111): the distribution of a Markov chain after `n` steps. With initial
distribution `u`, the probability that the chain is in state `j` after `n` steps (the total weight of the paths of
length `n` ending in `j`) is the `j`-th entry of the row vector `u P^n`. -/
@[kb "grinsteadsnell2006" "Theorem 11.2, p. 417"]
theorem markov_dist_after_n_steps (u : S → ℝ) (P : Matrix S S ℝ) (n : ℕ) (j : S) :
    ∑ x : Fin (n + 1) → S with x (Fin.last n) = j, pathProb u P n x = (u ᵥ* P ^ n) j :=
  sum_pathProb_last u P n j

/-- Grinstead–Snell Theorem 11.1 (PR-111): the `(i, j)` entry of `P^n` is the probability that a chain started in
state `i` is in state `j` after `n` steps (the total weight of the paths from `i` of length `n` ending in `j`). -/
@[kb "grinsteadsnell2006" "Theorem 11.1, p. 415"]
theorem markov_nstep_prob (P : Matrix S S ℝ) (n : ℕ) (i j : S) :
    ∑ x : Fin (n + 1) → S with x (Fin.last n) = j, pathProb (Pi.single i 1) P n x = (P ^ n) i j := by
  rw [sum_pathProb_last, single_vecMul, one_smul]
  rfl

/-- Grinstead–Snell §11.1 (PR-110): the path weights of a Markov chain form a probability distribution on the paths
of length `n` (they are nonnegative, `pathProb_nonneg`, and sum to one). -/
@[kb "grinsteadsnell2006" "§11.1 Markov chain and transition matrix, p. 413"]
theorem sum_pathProb {u : S → ℝ} {P : Matrix S S ℝ} (hu : ∑ i, u i = 1) (hP : P ∈ rowStochastic ℝ S) (n : ℕ) :
    ∑ x : Fin (n + 1) → S, pathProb u P n x = 1 := by
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : Fin (n + 1) → S => x (Fin.last n))]
  simp only [sum_pathProb_last]
  have hPn : P ^ n ∈ rowStochastic ℝ S := pow_mem hP n
  have := vecMul_dotProduct_one_eq_one_rowStochastic hPn (x := u) (by simpa [dotProduct] using hu)
  simpa [dotProduct] using this

/-- Grinstead–Snell Theorem 11.2 (PR-111): a power of a transition matrix is again a transition matrix, so the
distribution `u P^n` after `n` steps is a probability vector. -/
@[kb "grinsteadsnell2006" "Theorem 11.2, p. 417"]
theorem markov_dist_after_n_steps_prob {u : S → ℝ} {P : Matrix S S ℝ} (hu0 : ∀ i, 0 ≤ u i) (hu : ∑ i, u i = 1)
    (hP : P ∈ rowStochastic ℝ S) (n : ℕ) :
    (∀ j, 0 ≤ (u ᵥ* P ^ n) j) ∧ ∑ j, (u ᵥ* P ^ n) j = 1 := by
  have hPn : P ^ n ∈ rowStochastic ℝ S := pow_mem hP n
  refine ⟨fun j => ?_, ?_⟩
  · exact nonneg_vecMul_of_mem_rowStochastic hPn (fun i => hu0 i) j
  · have := vecMul_dotProduct_one_eq_one_rowStochastic hPn (x := u) (by simpa [dotProduct] using hu)
    simpa [dotProduct] using this

end UndergradKB.Probability
