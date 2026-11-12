/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Combinatorics.Order.Dilworth
import UndergradKB.Combinatorics.Graph.Brooks
import UndergradKB.Combinatorics.Graph.Cayley
import UndergradKB.Combinatorics.Graph.StableMatching
import UndergradKB.Combinatorics.Order.GaleRyser
import UndergradKB.Combinatorics.AeqB.GosperAlgorithm
import UndergradKB.Combinatorics.AeqB.Celine
import UndergradKB.Combinatorics.AeqB.HyperAlgorithm
import UndergradKB.Combinatorics.Graph.Euler
import UndergradKB.Combinatorics.Graph.Hamilton
import UndergradKB.Combinatorics.Probability.LocalLemma
import UndergradKB.Combinatorics.AeqB.GaussSum
import UndergradKB.Combinatorics.AeqB.DougallSum
import UndergradKB.Combinatorics.AeqB.DixonWellPoised

/-!
# Headline statements of undergraduate-math-lean 0.2.0: combinatorics (Keller–Trotter; A=B)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: Dilworth's chain covering theorem, Brooks's colouring theorem, Cayley's formula for labelled trees, the
existence of stable matchings and the correctness of the Gale–Shapley proposal algorithm, the Gale–Ryser theorem on
zero-one matrices, and, from the book on hypergeometric identities, Gosper's algorithm, Sister Celine's fundamental
theorem and the completeness of the candidate set of Petkovšek's algorithm Hyper; new in 0.2.0, Euler's theorem on
circuits, Dirac's theorem, the Lovász local lemma, and the summation theorems of Gauss, Dougall and Dixon for
hypergeometric series. To check what is claimed, read this
file. `Solution_Combinatorics.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator/Combinatorics.json`) checks that each proved statement is exactly the one here and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. The algorithm theorems (Gosper, Hyper, and the
proposal algorithm) are mathematical statements about decision and correctness, in which the outputs are chosen
classically; they are not executable programs.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `UndergradKB.Combinatorics.Order.width` (Keller–Trotter, p. 143): the width of a finite partially ordered set,
  the largest size of an antichain.
* `UndergradKB.Combinatorics.StableMatching.PrefProfile` (Keller–Trotter, Section 16.4): strict preferences of every
  male over the females and of every female over the males, given by injective rankings into the natural numbers
  (a larger rank is preferred).
* `UndergradKB.Combinatorics.StableMatching.IsStable` (Keller–Trotter, p. 345): a bijection between males and
  females is stable if no male and female both prefer each other to their partners.
* `UndergradKB.Combinatorics.StableMatching.run`, `IsProp` and `Step` (Keller–Trotter, pp. 345–346): the proposal
  algorithm, performing one rejection at a time (which rejection comes next is chosen classically); `IsProp P R m g`
  says that `g` is the best female for `m` among those who have not rejected him in the state `R`; `Step P R R'`
  says that `R'` arises from `R` by one rejection.
* `UndergradKB.Combinatorics.rowSum` and `colSum` (Keller–Trotter, p. 347): the number of ones in a row, respectively
  a column, of a zero-one matrix.
* `UndergradKB.Combinatorics.IsPartitionString` (Keller–Trotter, p. 347): a nonincreasing string of positive integers
  with a given sum.
* `UndergradKB.Combinatorics.conj` (Keller–Trotter, p. 348): the dual partition of a string, whose entry `k` is the
  number of entries larger than `k`.
* `UndergradKB.Combinatorics.Dominates` (Keller–Trotter, p. 347): the dominance order on strings, in which the
  partial sums of the dominating string are at least those of the other, up to its length.
* `UndergradKB.Combinatorics.AeqB.IsHypergeometric` (A=B, Definition 8.2.1): a sequence that is not eventually zero
  and satisfies, for large `n`, a first-order recurrence with nonzero polynomial coefficients.
* `UndergradKB.Combinatorics.AeqB.IsGosperSummable` (A=B, p. 84): a hypergeometric sequence `t` for which some
  hypergeometric sequence `z` has `z (n + 1) - z n = t n` for large `n`.
* `UndergradKB.Combinatorics.AeqB.GosperEq` (A=B, equation 5.2.6): the key equation
  `a(n) x(n + 1) - b(n - 1) x(n) = c(n)` of Gosper's algorithm.
* `UndergradKB.Combinatorics.AeqB.gosperOutput` (A=B, Step 4 of Gosper's algorithm): the output of the algorithm,
  an antidifference of `t` if one exists and the sequence of partial sums of `t` otherwise.
* `UndergradKB.Combinatorics.AeqB.ProperHypergeometricData`, with `eval` and `WellDefinedAt` (A=B, equation 4.4.1):
  the data (a polynomial, integer coefficient vectors of the factorials, and the base `x`) of a proper hypergeometric
  term, its value at integer points (with `1/m! = 0` for negative `m`), and the condition that no numerator
  factorial has a negative argument.
* `UndergradKB.Combinatorics.AeqB.Celine.iStar` and `jStar` (A=B, equation 4.4.3): the orders of the recurrence in
  Sister Celine's fundamental theorem.
* `UndergradKB.Combinatorics.AeqB.IsHyperCandidate` (A=B, Algorithm Hyper): a monic factor of the leading
  coefficient, a monic factor of the shifted last coefficient, a nonzero root of an auxiliary polynomial and a
  nonzero polynomial solution of an auxiliary recurrence.
* `UndergradKB.Combinatorics.Euler.IsEulerianGraph G` (Keller–Trotter, Section 5.3): there is a closed walk that
  uses every edge exactly once and passes through every vertex.
* `UndergradKB.Combinatorics.Probability.FinProbSpace Ω` (a finite probability space: nonnegative point weights
  `p` with sum 1), its `prob s = ∑ ω ∈ s, p ω`; `noneOf E S` is the event that no `E j` with `j ∈ S` occurs;
  `LLLIndep μ E N` (Keller–Trotter, Section 16.5): each `E i` is independent of every event `noneOf E S` with
  `i ∉ S` and `S` disjoint from the neighbourhood `N i`.
* `UndergradKB.Combinatorics.AeqB.pFqTerm a b x k` (A=B, Section 3.5): the `k`-th term
  `∏ (aᵢ)ₖ xᵏ / (∏ (bⱼ)ₖ k!)` of the hypergeometric series `pFq`, with `(y)ₖ` the rising factorial.
* `UndergradKB.Combinatorics.AeqB.dpoch x k`: the rising factorial `x (x + 1) ⋯ (x + k - 1)` of a real number;
  `NoNegInt x`: `x` is not `0, -1, -2, …`; `DougallHyp a b c d n`: eleven such conditions on expressions in the
  parameters (and `n + a ≠ 0`), which keep every denominator of the identity and of its proof nonzero.
-/

open Polynomial Filter

namespace UndergradKB.Headlines.Combinatorics

/-- **Dilworth's theorem** (Keller–Trotter, Theorem 6.17): a finite partially ordered set of width `w` is the union
of `w` chains, and no partition into fewer chains exists. Related: neither Mathlib nor Tau Ceti has Dilworth's
theorem or chain covers. -/
theorem dilworth {α : Type*} [PartialOrder α] [Fintype α] :
    (∃ f : α → Fin (UndergradKB.Combinatorics.Order.width α), ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) ∧
    ∀ (n : ℕ) (g : α → Fin n), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) →
      UndergradKB.Combinatorics.Order.width α ≤ n := by
  sorry

/-- **Brooks's theorem** (Keller–Trotter, Exercise 5.9.43): a connected finite graph all of whose degrees are at
most `k`, with `k ≥ 3`, which is not complete, can be coloured with `k` colours. Related: neither Mathlib nor Tau
Ceti has it. -/
theorem brooks {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 3 ≤ k) (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k) (hG : G ≠ ⊤) : G.Colorable k := by
  sorry

/-- **Cayley's formula** (Keller–Trotter, Theorem 5.39): the number of labelled trees on `n ≥ 1` vertices is
`n ^ (n - 2)`. Related: neither Mathlib nor Tau Ceti counts trees (the Cayley files of Mathlib are about Cayley
graphs of groups). -/
theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  sorry

/-- **The Stable Matching Theorem** (Keller–Trotter, Section 16.4, p. 345): for any strict preferences of `n`
males and `n` females there is a stable perfect matching. Related: neither Mathlib nor Tau Ceti has stable
matchings. -/
theorem stable_matching_exists {M F : Type*} {P : UndergradKB.Combinatorics.StableMatching.PrefProfile M F}
    [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, UndergradKB.Combinatorics.StableMatching.IsStable P σ := by
  sorry

/-- **Correctness of the Gale–Shapley proposal algorithm** (Keller–Trotter, Section 16.4, p. 346): started from the
empty rejection state, the proposal algorithm halts, and its final state determines a stable perfect matching
whose partners are the final proposals. The algorithm is modelled as a function whose choice of the next rejection
is made classically, so this is a statement of correctness, not an executable program. Related: neither Mathlib
nor Tau Ceti has the algorithm. -/
theorem gale_shapley_correct {M F : Type*} {P : UndergradKB.Combinatorics.StableMatching.PrefProfile M F}
    [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, UndergradKB.Combinatorics.StableMatching.IsStable P σ ∧
      (∀ m, UndergradKB.Combinatorics.StableMatching.IsProp P
        (UndergradKB.Combinatorics.StableMatching.run P fun _ => ∅) m (σ m)) ∧
      ¬ ∃ R', UndergradKB.Combinatorics.StableMatching.Step P
        (UndergradKB.Combinatorics.StableMatching.run P fun _ => ∅) R' := by
  sorry

/-- **The Gale–Ryser theorem** (Keller–Trotter, Theorem 16.12): for partitions `R` and `C` of `t`, a zero-one
matrix with row sum string `R` and column sum string `C` exists if and only if the dual partition of `R` dominates
`C`. Related: neither Mathlib nor Tau Ceti has it. -/
theorem gale_ryser {m n t : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ)
    (hR : UndergradKB.Combinatorics.IsPartitionString R t)
    (hC : UndergradKB.Combinatorics.IsPartitionString C t) :
    (∃ M : Fin m → Fin n → Bool, (∀ i, UndergradKB.Combinatorics.rowSum M i = R i) ∧
      ∀ j, UndergradKB.Combinatorics.colSum M j = C j) ↔
      UndergradKB.Combinatorics.Dominates (UndergradKB.Combinatorics.conj R) C := by
  sorry

/-- **Gosper's algorithm** (A=B, Chapter 5, the outline on p. 87): for a hypergeometric sequence `t` there are
polynomials `a`, `b`, `c` (with `b` and `c` monic and the coprimality conditions of the book) such that `t (n + 1)`
and `t n` are in the ratio `a c(n + 1) / (b c)` for large `n`, `t` is Gosper-summable if and only if the key equation
has a polynomial solution, in which case the output of the algorithm is a hypergeometric antidifference of `t`, and
otherwise the output is the sequence of partial sums of `t`. This is a decision and correctness theorem (the output is
chosen classically), not an executable program. Related: the only Gosper in Mathlib is a private trick for Catalan
numbers; Tau Ceti has none. -/
theorem gosper_algorithm {K : Type*} [Field K] [CharZero K] {t : ℕ → K}
    (ht : UndergradKB.Combinatorics.AeqB.IsHypergeometric t) :
    ∃ a b c : K[X], a ≠ 0 ∧ b.Monic ∧ c.Monic ∧
      (∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) ∧ IsCoprime a c ∧
      IsCoprime b (c.comp (X + 1)) ∧
      (∀ᶠ n : ℕ in atTop,
        (b * c).eval (n : K) * t (n + 1) = (a * c.comp (X + 1)).eval (n : K) * t n) ∧
      (UndergradKB.Combinatorics.AeqB.IsGosperSummable t ↔
        ∃ x, UndergradKB.Combinatorics.AeqB.GosperEq a b c x) ∧
      (UndergradKB.Combinatorics.AeqB.IsGosperSummable t →
        UndergradKB.Combinatorics.AeqB.IsHypergeometric
          (UndergradKB.Combinatorics.AeqB.gosperOutput t a b c) ∧
        ∀ᶠ n : ℕ in atTop,
          UndergradKB.Combinatorics.AeqB.gosperOutput t a b c (n + 1) -
            UndergradKB.Combinatorics.AeqB.gosperOutput t a b c n = t n) ∧
      (¬ UndergradKB.Combinatorics.AeqB.IsGosperSummable t →
        UndergradKB.Combinatorics.AeqB.gosperOutput t a b c = fun n => ∑ k ∈ Finset.range n, t k) := by
  sorry

/-- **Sister Celine's fundamental theorem** (A=B, Theorem 4.4.1): a proper hypergeometric term `F(n, k)` (with
`x ≠ 0`) satisfies a nontrivial recurrence in `n` and `k` with polynomial coefficients in `n` that are not all zero,
at every point where `F(n, k) ≠ 0` and all the values of `F` in the recurrence are well defined; moreover the orders
of the recurrence can be taken to be the explicit bounds of equation 4.4.3. Related: neither Mathlib nor Tau Ceti
has it. -/
theorem sister_celine {K : Type*} [Field K] [CharZero K]
    (D : UndergradKB.Combinatorics.AeqB.ProperHypergeometricData K) (hx : D.x ≠ 0) :
    ∃ a : Fin (UndergradKB.Combinatorics.AeqB.Celine.iStar D + 1) ×
        Fin (UndergradKB.Combinatorics.AeqB.Celine.jStar D + 1) → K[X], a ≠ 0 ∧
      ∀ n k : ℤ, D.eval n k ≠ 0 →
        (∀ i ≤ UndergradKB.Combinatorics.AeqB.Celine.iStar D, ∀ j ≤ UndergradKB.Combinatorics.AeqB.Celine.jStar D,
          D.WellDefinedAt (n - j) (k - i)) →
        ∑ p : Fin (UndergradKB.Combinatorics.AeqB.Celine.iStar D + 1) ×
            Fin (UndergradKB.Combinatorics.AeqB.Celine.jStar D + 1), (a p).eval (n : K) *
          D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 := by
  sorry

/-- **Completeness of Petkovšek's algorithm Hyper** (A=B, Theorem 8.4.1 and Algorithm Hyper, p. 162): a recurrence
`∑_{i ≤ d} p_i(n) y(n + i) = 0` for large `n`, with `d ≥ 1` and `p_0`, `p_d` nonzero, has a hypergeometric solution
if and only if some candidate of the algorithm works. Related: neither Mathlib nor Tau Ceti has it. This is a
decision and correctness theorem, not an executable program. -/
theorem hyper_complete {K : Type*} [Field K] [CharZero K] (p : ℕ → K[X]) (d : ℕ) (hd : 0 < d) (hp0 : p 0 ≠ 0)
    (hpd : p d ≠ 0) :
    (∃ y : ℕ → K, UndergradKB.Combinatorics.AeqB.IsHypergeometric y ∧
        ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0) ↔
      ∃ a b z c, UndergradKB.Combinatorics.AeqB.IsHyperCandidate p d a b z c := by
  sorry

/-- **Euler's theorem** (Keller–Trotter Theorem 5.13; new in 0.2.0): a finite graph has a closed walk using every
edge exactly once and visiting every vertex if and only if it is connected and every vertex has even degree.
Related: Mathlib proves only that the degrees of a graph with an Eulerian walk are even (the existence is a TODO
there); Tau Ceti has neither direction. -/
theorem euler_circuit_iff {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] :
    UndergradKB.Combinatorics.Euler.IsEulerianGraph G ↔ G.Connected ∧ ∀ v, Even (G.degree v) := by
  sorry

/-- **Dirac's theorem** (Keller–Trotter Theorem 5.18; new in 0.2.0): a graph on `n ≥ 3` vertices in which every
vertex has degree at least `n / 2` has a Hamiltonian cycle. Related: Mathlib defines Hamiltonian graphs but has no
degree condition; Tau Ceti's "Dirac" theorem is about cycles through prescribed vertices, a different result. -/
theorem dirac {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hn3 : 3 ≤ Fintype.card V)
    (hdeg : ∀ v, ⌈(Fintype.card V : ℚ) / 2⌉₊ ≤ G.degree v) : G.IsHamiltonian := by
  sorry

open UndergradKB.Combinatorics.Probability in
/-- **The Lovász local lemma** (Keller–Trotter Lemma 16.14; new in 0.2.0): in a finite probability space, if each
event `E i` is independent of the events outside its neighbourhood `N i` and `P(E i) ≤ x i ∏_{j ∈ N i} (1 - x j)`
with `0 < x i < 1`, then for every finite set `S` of indices the probability that no `E j`, `j ∈ S`, occurs is at
least `∏_{j ∈ S} (1 - x j)`. Related: neither Mathlib nor Tau Ceti has it. -/
theorem lovasz_local_lemma {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [DecidableEq ι]
    {μ : FinProbSpace Ω} {E : ι → Finset Ω} {N : ι → Finset ι} {x : ι → ℝ}
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.prob (E i) ≤ x i * ∏ j ∈ N i, (1 - x j)) (hind : LLLIndep μ E N) (S : Finset ι) :
    ∏ j ∈ S, (1 - x j) ≤ μ.prob (noneOf E S) := by
  sorry

open UndergradKB.Combinatorics.AeqB in
/-- **Gauss's summation of `₂F₁` at 1** (A=B, identity (I) of the list of Section 3.5, p. 53; new in 0.2.0): for
`c - a - b > 0` (and `c` not a nonpositive integer) the series `₂F₁(a, b; c; 1)` converges, with sum
`Γ(c) Γ(c - a - b) / (Γ(c - a) Γ(c - b))`. Related: Mathlib and Tau Ceti have the hypergeometric series, its radius
of convergence and analyticity, but not its value at 1. -/
theorem gauss_hypergeometric_sum (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c ≠ -(k : ℝ)) :
    Summable (fun k => pFqTerm ![a, b] ![c] (1 : ℝ) k) ∧
    ∑' k, pFqTerm ![a, b] ![c] (1 : ℝ) k =
      Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b)) := by
  sorry

open UndergradKB.Combinatorics.AeqB Finset in
/-- **Dougall's theorem** (A=B, identity (VI) of Section 3.5, p. 54; new in 0.2.0): the terminating, balanced
(`1 + 2a = b + c + d + e - n`), very well poised `₇F₆` series has the closed form below, for parameters avoiding the
poles (`DougallHyp`). Related: neither Mathlib nor Tau Ceti has it. -/
theorem dougall_sum (A B C D E : ℝ) (n : ℕ) (hE : 1 + 2 * A = B + C + D + E - n)
    (h : ∀ m ≤ n, DougallHyp (1 + 2 * A - B - C - D) (1 + A - C - D) (1 + A - B - D) A m) :
    ∑ k ∈ range (n + 1),
        dpoch A k * dpoch (1 + A / 2) k * dpoch B k * dpoch C k * dpoch D k * dpoch E k *
          dpoch (-(n : ℝ)) k /
        ((k.factorial : ℝ) * dpoch (A / 2) k * dpoch (1 + A - B) k * dpoch (1 + A - C) k *
          dpoch (1 + A - D) k * dpoch (1 + A - E) k * dpoch (1 + A + n) k)
      = dpoch (1 + A) n * dpoch (1 + A - B - C) n * dpoch (1 + A - B - D) n *
          dpoch (1 + A - C - D) n /
        (dpoch (1 + A - B) n * dpoch (1 + A - C) n * dpoch (1 + A - D) n *
          dpoch (1 + A - B - C - D) n) := by
  sorry

open UndergradKB.Combinatorics.AeqB Finset in
/-- **Dixon's theorem** (A=B, p. 55; new in 0.2.0): the terminating well-poised series
`₃F₂(-2n, b, c; 1 - b - 2n, 1 - c - 2n; 1)` equals `(2n)! (b)ₙ (c)ₙ (b + c)₂ₙ / (n! (b)₂ₙ (c)₂ₙ (b + c)ₙ)`, for
`b`, `c`, `b + c` avoiding the poles. Related: neither Mathlib nor Tau Ceti has it. -/
theorem dixon_sum (b c : ℝ) (n : ℕ)
    (hb : ∀ j : ℕ, j < 2 * n → b + j ≠ 0) (hc : ∀ j : ℕ, j < 2 * n → c + j ≠ 0)
    (hs : ∀ j : ℕ, j < 2 * n → b + c + j ≠ 0) :
    ∑ k ∈ range (2 * n + 1),
        dpoch (-(2 * (n : ℝ))) k * dpoch b k * dpoch c k /
          (dpoch (1 - b - 2 * n) k * dpoch (1 - c - 2 * n) k * (k.factorial : ℝ)) =
      dpoch 1 (2 * n) * dpoch b n * dpoch c n * dpoch (b + c) (2 * n) /
        (dpoch 1 n * dpoch b (2 * n) * dpoch c (2 * n) * dpoch (b + c) n) := by
  sorry

end UndergradKB.Headlines.Combinatorics
