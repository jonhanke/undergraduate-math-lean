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

/-!
# Proofs of the combinatorics headline statements of undergraduate-math-lean 0.1.0

Each theorem here proves, from the library, the statement of the theorem of the same name in
`Challenge_Combinatorics.lean`; `lake comparator` checks that each statement here is exactly the one in
`Challenge_Combinatorics.lean`.
-/

open Polynomial Filter

namespace UndergradKB.Headlines.Combinatorics

theorem dilworth {α : Type*} [PartialOrder α] [Fintype α] :
    (∃ f : α → Fin (UndergradKB.Combinatorics.Order.width α), ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) ∧
    ∀ (n : ℕ) (g : α → Fin n), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) →
      UndergradKB.Combinatorics.Order.width α ≤ n := by
  exact UndergradKB.Combinatorics.Order.dilworth

theorem brooks {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 3 ≤ k) (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ k) (hG : G ≠ ⊤) : G.Colorable k := by
  exact UndergradKB.Combinatorics.brooks hk hconn hdeg hG

theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {T : SimpleGraph (Fin n) // T.IsTree} = n ^ (n - 2) := by
  exact UndergradKB.Combinatorics.Prufer.cayley n hn

theorem stable_matching_exists {M F : Type*} {P : UndergradKB.Combinatorics.StableMatching.PrefProfile M F}
    [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, UndergradKB.Combinatorics.StableMatching.IsStable P σ := by
  exact UndergradKB.Combinatorics.StableMatching.exists_stable hcard

theorem gale_shapley_correct {M F : Type*} {P : UndergradKB.Combinatorics.StableMatching.PrefProfile M F}
    [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, UndergradKB.Combinatorics.StableMatching.IsStable P σ ∧
      (∀ m, UndergradKB.Combinatorics.StableMatching.IsProp P
        (UndergradKB.Combinatorics.StableMatching.run P fun _ => ∅) m (σ m)) ∧
      ¬ ∃ R', UndergradKB.Combinatorics.StableMatching.Step P
        (UndergradKB.Combinatorics.StableMatching.run P fun _ => ∅) R' := by
  exact UndergradKB.Combinatorics.StableMatching.run_correct hcard

theorem gale_ryser {m n t : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ)
    (hR : UndergradKB.Combinatorics.IsPartitionString R t)
    (hC : UndergradKB.Combinatorics.IsPartitionString C t) :
    (∃ M : Fin m → Fin n → Bool, (∀ i, UndergradKB.Combinatorics.rowSum M i = R i) ∧
      ∀ j, UndergradKB.Combinatorics.colSum M j = C j) ↔
      UndergradKB.Combinatorics.Dominates (UndergradKB.Combinatorics.conj R) C := by
  exact UndergradKB.Combinatorics.gale_ryser R C hR hC

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
  exact UndergradKB.Combinatorics.AeqB.gosper_algorithm ht

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
  exact UndergradKB.Combinatorics.AeqB.Celine.fundamental_theorem D hx

theorem hyper_complete {K : Type*} [Field K] [CharZero K] (p : ℕ → K[X]) (d : ℕ) (hd : 0 < d) (hp0 : p 0 ≠ 0)
    (hpd : p d ≠ 0) :
    (∃ y : ℕ → K, UndergradKB.Combinatorics.AeqB.IsHypergeometric y ∧
        ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0) ↔
      ∃ a b z c, UndergradKB.Combinatorics.AeqB.IsHyperCandidate p d a b z c := by
  exact UndergradKB.Combinatorics.AeqB.hyper_exists_iff p d hd hp0 hpd

end UndergradKB.Headlines.Combinatorics
