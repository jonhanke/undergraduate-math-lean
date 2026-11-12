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
# Proofs of the combinatorics headline statements

Proves the statements of `Challenge_Combinatorics.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Combinatorics.lean`.
-/

open Polynomial Filter

namespace UndergradKB.Headlines.Combinatorics

theorem dilworth {α : Type*} [PartialOrder α] [Fintype α] :
    (∃ f : α → Fin (UndergradKB.Combinatorics.Order.width α), ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) ∧
    ∀ (n : ℕ) (g : α → Fin n), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) →
      UndergradKB.Combinatorics.Order.width α ≤ n :=
  UndergradKB.Combinatorics.Order.dilworth

theorem brooks {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 3 ≤ k) (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k) (hG : G ≠ ⊤) : G.Colorable k :=
  UndergradKB.Combinatorics.brooks hk hconn hdeg hG

theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) :=
  UndergradKB.Combinatorics.Prufer.cayley n hn

theorem stable_matching_exists {M F : Type*} {P : UndergradKB.Combinatorics.StableMatching.PrefProfile M F}
    [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, UndergradKB.Combinatorics.StableMatching.IsStable P σ :=
  UndergradKB.Combinatorics.StableMatching.exists_stable hcard

theorem gale_shapley_correct {M F : Type*} {P : UndergradKB.Combinatorics.StableMatching.PrefProfile M F}
    [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, UndergradKB.Combinatorics.StableMatching.IsStable P σ ∧
      (∀ m, UndergradKB.Combinatorics.StableMatching.IsProp P
        (UndergradKB.Combinatorics.StableMatching.run P fun _ => ∅) m (σ m)) ∧
      ¬ ∃ R', UndergradKB.Combinatorics.StableMatching.Step P
        (UndergradKB.Combinatorics.StableMatching.run P fun _ => ∅) R' :=
  UndergradKB.Combinatorics.StableMatching.run_correct hcard

theorem gale_ryser {m n t : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ)
    (hR : UndergradKB.Combinatorics.IsPartitionString R t)
    (hC : UndergradKB.Combinatorics.IsPartitionString C t) :
    (∃ M : Fin m → Fin n → Bool, (∀ i, UndergradKB.Combinatorics.rowSum M i = R i) ∧
      ∀ j, UndergradKB.Combinatorics.colSum M j = C j) ↔
      UndergradKB.Combinatorics.Dominates (UndergradKB.Combinatorics.conj R) C :=
  UndergradKB.Combinatorics.gale_ryser R C hR hC

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
        UndergradKB.Combinatorics.AeqB.gosperOutput t a b c = fun n => ∑ k ∈ Finset.range n, t k) :=
  UndergradKB.Combinatorics.AeqB.gosper_algorithm ht

theorem sister_celine {K : Type*} [Field K] [CharZero K]
    (D : UndergradKB.Combinatorics.AeqB.ProperHypergeometricData K) (hx : D.x ≠ 0) :
    ∃ a : Fin (UndergradKB.Combinatorics.AeqB.Celine.iStar D + 1) ×
        Fin (UndergradKB.Combinatorics.AeqB.Celine.jStar D + 1) → K[X], a ≠ 0 ∧
      ∀ n k : ℤ, D.eval n k ≠ 0 →
        (∀ i ≤ UndergradKB.Combinatorics.AeqB.Celine.iStar D, ∀ j ≤ UndergradKB.Combinatorics.AeqB.Celine.jStar D,
          D.WellDefinedAt (n - j) (k - i)) →
        ∑ p : Fin (UndergradKB.Combinatorics.AeqB.Celine.iStar D + 1) ×
            Fin (UndergradKB.Combinatorics.AeqB.Celine.jStar D + 1), (a p).eval (n : K) *
          D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 :=
  UndergradKB.Combinatorics.AeqB.Celine.fundamental_theorem D hx

theorem hyper_complete {K : Type*} [Field K] [CharZero K] (p : ℕ → K[X]) (d : ℕ) (hd : 0 < d) (hp0 : p 0 ≠ 0)
    (hpd : p d ≠ 0) :
    (∃ y : ℕ → K, UndergradKB.Combinatorics.AeqB.IsHypergeometric y ∧
        ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0) ↔
      ∃ a b z c, UndergradKB.Combinatorics.AeqB.IsHyperCandidate p d a b z c :=
  UndergradKB.Combinatorics.AeqB.hyper_exists_iff p d hd hp0 hpd

theorem euler_circuit_iff {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] :
    UndergradKB.Combinatorics.Euler.IsEulerianGraph G ↔ G.Connected ∧ ∀ v, Even (G.degree v) :=
  UndergradKB.Combinatorics.Euler.isEulerianGraph_iff

theorem dirac {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hn3 : 3 ≤ Fintype.card V)
    (hdeg : ∀ v, ⌈(Fintype.card V : ℚ) / 2⌉₊ ≤ G.degree v) : G.IsHamiltonian :=
  UndergradKB.Combinatorics.Hamilton.dirac hn3 hdeg

open UndergradKB.Combinatorics.Probability in
theorem lovasz_local_lemma {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [DecidableEq ι]
    {μ : FinProbSpace Ω} {E : ι → Finset Ω} {N : ι → Finset ι} {x : ι → ℝ}
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.prob (E i) ≤ x i * ∏ j ∈ N i, (1 - x j)) (hind : LLLIndep μ E N) (S : Finset ι) :
    ∏ j ∈ S, (1 - x j) ≤ μ.prob (noneOf E S) :=
  UndergradKB.Combinatorics.Probability.lovasz_local_lemma hx0 hx1 hP hind S

open UndergradKB.Combinatorics.AeqB in
theorem gauss_hypergeometric_sum (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c ≠ -(k : ℝ)) :
    Summable (fun k => pFqTerm ![a, b] ![c] (1 : ℝ) k) ∧
    ∑' k, pFqTerm ![a, b] ![c] (1 : ℝ) k =
      Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b)) :=
  UndergradKB.Combinatorics.AeqB.gauss_two_one_gamma a b c hs hc

open UndergradKB.Combinatorics.AeqB Finset in
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
          dpoch (1 + A - B - C - D) n) :=
  UndergradKB.Combinatorics.AeqB.dougall_sum A B C D E n hE h

open UndergradKB.Combinatorics.AeqB Finset in
theorem dixon_sum (b c : ℝ) (n : ℕ)
    (hb : ∀ j : ℕ, j < 2 * n → b + j ≠ 0) (hc : ∀ j : ℕ, j < 2 * n → c + j ≠ 0)
    (hs : ∀ j : ℕ, j < 2 * n → b + c + j ≠ 0) :
    ∑ k ∈ range (2 * n + 1),
        dpoch (-(2 * (n : ℝ))) k * dpoch b k * dpoch c k /
          (dpoch (1 - b - 2 * n) k * dpoch (1 - c - 2 * n) k * (k.factorial : ℝ)) =
      dpoch 1 (2 * n) * dpoch b n * dpoch c n * dpoch (b + c) (2 * n) /
        (dpoch 1 n * dpoch b (2 * n) * dpoch c (2 * n) * dpoch (b + c) n) :=
  UndergradKB.Combinatorics.AeqB.dixon_well_poised b c n hb hc hs

end UndergradKB.Headlines.Combinatorics
