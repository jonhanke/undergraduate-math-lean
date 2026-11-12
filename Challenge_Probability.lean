/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.PolyaRecurrence
import UndergradKB.Probability.PolyaThree
import UndergradKB.Probability.ArcSine
import UndergradKB.Probability.Shuffles
import UndergradKB.Probability.LocalLimitLattice

/-!
# Headline statements of undergraduate-math-lean 0.2.0: probability (Grinstead–Snell)

The main results of this topic that Mathlib and Tau Ceti lack, with every proof a deliberate `sorry`: the
convergence theorems for regular and ergodic finite Markov chains; the theory of absorbing chains (absorption is
certain; the fundamental matrix gives the absorption times and probabilities); Pólya's theorem on the recurrence of
the simple random walk in dimension 2 and its transience in dimension 3; the arc sine law for the time in the lead;
the composition law and the counting formula for riffle shuffles; and the local limit theorem for integer-valued
sums. To check what is claimed, read this file. `Solution_Probability.lean` proves the same statements from the
library, and `lake comparator` (configured by `comparator/Probability.json`) checks that each proved statement is
exactly the one here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib (`rowStochastic`, `Matrix.IsIrreducible`, `iIndepFun`, `IdentDistrib`, `MemLp`, `variance`), the
statements use these definitions of the library (namespace `UndergradKB.Probability`); a reader checking a statement
should check these too:

* Markov chains are given by their transition matrix `P : Matrix S S ℝ` on a finite state set `S`.
  `IsRegularChain P`: `P` is row-stochastic and some power `P ^ N` (`N > 0`) has all entries positive.
  `IsErgodicChain P`: `P` is row-stochastic and irreducible (every state can reach every state).
  `IsFixedRow P w`: `w ᵥ* P = w`. `cesaroAvg P n i j = (∑ k < n, (P ^ k) i j) / n`.
* `IsAbsorbingState P i`: `P i i = 1`. `IsAbsorbingChain P`: there is an absorbing state, and from every state some
  absorbing state is reached with positive probability in some number of steps. `Transient P`, `Absorbing P`: the
  subtypes of non-absorbing and absorbing states. `absorbQ P`, `absorbR P`: the transient-to-transient and
  transient-to-absorbing blocks of `P`. `fundamentalMatrix P = (1 - absorbQ P)⁻¹`.
* Random walks are modelled by their finite paths, all equally likely. `Polya.simpleStep d` sends `(i, b)` to `±eᵢ`
  (the `2d` unit steps of `ℤ^d`); for a step map `st : S → G`, `Polya.u st N` is the proportion of the `|S|^N` paths
  of `N` steps that end at `0`, and `Polya.f st N` the proportion of paths of `N` steps whose first return to `0` is
  at time `N` (`N > 0`).
* `walkPos ω k` is the position after `k` steps of the `±1` walk with steps `ω : Fin N → Bool`; `leadCount ω` is the
  number of steps `k ≤ N` at which the walk is in the lead (`walkPos ω k > 0`, or `= 0` with `walkPos ω (k-1) > 0`).
* A riffle shuffle of a deck of `n` cards with `a` packets is recorded by its packet labels `g : Fin n → Fin a`
  (`a ^ n` shuffles, equally likely); `shuffleOrdering g = (Tuple.sort g).symm` is the resulting order of the deck;
  `risingSequences σ` is the number of rising sequences of the order `σ`.
-/

namespace UndergradKB.Headlines.Probability

open Matrix Finset Filter Topology MeasureTheory ProbabilityTheory UndergradKB.Probability
open scoped Real

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Convergence of regular Markov chains** (Grinstead–Snell Theorems 11.7, 11.8): if some power of the
transition matrix has only positive entries, the `n`-step transition probabilities converge to a probability vector
with positive entries that does not depend on the starting state. Related: Tau Ceti has the Perron–Frobenius
eigenvectors of primitive matrices and coupling bounds for recurrent chains, but no convergence of the powers;
Mathlib has none. -/
theorem regular_pow_tendsto [Nonempty S] {P : Matrix S S ℝ} (h : IsRegularChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧
      ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 (w j)) := by
  sorry

/-- **The ergodic theorem for finite Markov chains** (Grinstead–Snell Theorems 11.10, 11.11): an irreducible chain
has a fixed probability vector with positive entries, and the averages of the first `n` powers of the transition
matrix converge to it. Related: as above; Tau Ceti has almost-sure occupation frequencies, not this matrix
statement. -/
theorem ergodic_cesaro_tendsto [Nonempty S] {P : Matrix S S ℝ} (h : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ i j, Tendsto (fun n => cesaroAvg P n i j) atTop (𝓝 (w j)) := by
  sorry

/-- **Absorption is certain** (Grinstead–Snell Theorem 11.3): in an absorbing chain, the probability of being in an
absorbing state after `n` steps tends to 1. Related: neither Mathlib nor Tau Ceti has absorbing chains (Tau Ceti has
a two-state example). -/
theorem absorption_certain {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i : S) :
    Tendsto (fun n => ∑ a : Absorbing P, (P ^ n) i a) atTop (𝓝 1) := by
  sorry

/-- **Expected time to absorption** (Grinstead–Snell Theorem 11.5): from a transient state `i`, the expected number
of steps before absorption, `∑ₖ P(not yet absorbed after k steps)`, is the `i`-th entry of `N 1`, where
`N = (I - Q)⁻¹` is the fundamental matrix. Related: as above. -/
theorem hasSum_absorption_time {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P)
    (i : Transient P) :
    HasSum (fun k => ∑ j : Transient P, (P ^ k) i j) ((fundamentalMatrix P *ᵥ fun _ => 1) i) := by
  sorry

/-- **Absorption probabilities** (Grinstead–Snell Theorem 11.6): from a transient state `i`, the probability of
being absorbed in the absorbing state `a` is the entry `(N R) i a`. Related: as above. -/
theorem absorption_prob_tendsto {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P)
    (i : Transient P) (a : Absorbing P) :
    Tendsto (fun n => (P ^ n) i a) atTop (𝓝 ((fundamentalMatrix P * absorbR P) i a)) := by
  sorry

/-- **Pólya's theorem in dimension 2** (Grinstead–Snell Example 12.2): the simple random walk on `ℤ²` returns to
the origin with probability 1 (the probabilities of first return at time `N` sum to 1). Related: Tau Ceti proves
recurrence of the walk on `ℤ` only; Mathlib has no random walks. -/
theorem polya_two : HasSum (Polya.f (Polya.simpleStep 2)) 1 := by
  sorry

/-- **Pólya's theorem in dimension 3** (Grinstead–Snell Example 12.3): the simple random walk on `ℤ³` returns to
the origin with probability `1 - 1/u < 1`, where `u = ∑ₙ P(at the origin at time n)` is finite. Related: as
above. -/
theorem polya_three :
    HasSum (Polya.f (Polya.simpleStep 3)) (1 - (∑' N, Polya.u (Polya.simpleStep 3) N)⁻¹) ∧
      ∑' N, Polya.f (Polya.simpleStep 3) N < 1 := by
  sorry

/-- **The arc sine law for the time in the lead** (Grinstead–Snell Theorem 12.4): in `2m` tosses of a fair coin,
the probability that the time in the lead is at most `α · 2m` tends to `(2/π) arcsin √α`. Related: Tau Ceti has
the arc sine distribution, but no random walk statement; Mathlib has neither. -/
theorem arcsine_law_lead (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Filter.Tendsto (fun m : ℕ => ∑ k ∈ range (⌊α * m⌋₊ + 1),
        ((univ.filter fun ω : Fin (2 * m) → Bool => leadCount ω = 2 * k).card : ℝ) / 2 ^ (2 * m))
      Filter.atTop (nhds ((2 / Real.pi) * Real.arcsin (Real.sqrt α))) := by
  sorry

/-- **An `a`-shuffle followed by a `b`-shuffle is an `ab`-shuffle** (Grinstead–Snell Theorem 3.10): there is a
bijection between pairs of an `a`-shuffle and a `b`-shuffle and the `ab`-shuffles under which the resulting orders
of the deck agree. Related: neither Mathlib nor Tau Ceti has card shuffling. -/
theorem riffle_shuffle_composition (n a b : ℕ) :
    ∃ e : ((Fin n → Fin a) × (Fin n → Fin b)) ≃ (Fin n → Fin (a * b)),
      ∀ p, shuffleOrdering (e p) = shuffleOrdering p.1 * shuffleOrdering p.2 := by
  sorry

/-- **The number of riffle shuffles giving an order** (Grinstead–Snell Theorem 3.11): an order of `n` cards with
`r` rising sequences arises from exactly `C(n + a - r, n)` of the `a ^ n` `a`-shuffles. Related: as above. -/
theorem card_riffle_shuffles (n a : ℕ) (σ : Equiv.Perm (Fin n)) :
    #{g : Fin n → Fin a | shuffleOrdering g = σ} = (n + a - risingSequences σ).choose n := by
  sorry

/-- **The local limit theorem** (Grinstead–Snell Theorem 9.3): for independent identically distributed
integer-valued random variables with finite variance `σ² > 0`, mean `μ` and span 1, the probability that the sum of
the first `n` equals `j` is `φ((j - nμ)/(σ√n)) / (σ√n)` up to an error `o(1/√n)` uniform in `j`, where `φ` is the
standard normal density. Related: Mathlib proves the central limit theorem (convergence in distribution), not the
local form; Tau Ceti has no local limit theorem. -/
theorem local_limit_theorem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℤ} (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (fun ω => (X 0 ω : ℝ)) 2 P) {μ σ : ℝ} (hσ : 0 < σ)
    (hμ : ∫ ω, (X 0 ω : ℝ) ∂P = μ) (hv : Var[fun ω => (X 0 ω : ℝ); P] = σ ^ 2)
    (hgcd : ∀ m : ℤ, (∀ i j : ℤ, 0 < P.real {ω | X 0 ω = i} → 0 < P.real {ω | X 0 ω = j} →
      m ∣ i - j) → m ∣ 1) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n → ∀ j : ℤ,
      |σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j} -
        Real.exp (-(((j - n * μ) / (σ * √(n : ℝ))) ^ 2) / 2) / √(2 * π)| ≤ ε n := by
  sorry

end UndergradKB.Headlines.Probability
