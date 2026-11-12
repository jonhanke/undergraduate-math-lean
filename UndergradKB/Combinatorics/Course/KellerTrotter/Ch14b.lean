import UndergradKB.Combinatorics.Flow.MaxFlowMinCut
import UndergradKB.Combinatorics.Flow.Matching
import UndergradKB.Combinatorics.Flow.Integrality
import UndergradKB.Combinatorics.Order.FlowChains
import UndergradKB.Combinatorics.Order.FlowAntichain
import UndergradKB.Combinatorics.Polya.CycleIndex
import UndergradKB.Combinatorics.Polya.Graphs
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 14: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch14b

open UndergradKB.Combinatorics.Flow

/-- CO-300. Integrality theorem: if all capacities are integers, some maximum flow is
integer-valued on every edge. -/
@[kb "kellertrotter2017" "Theorem 14.1, p. 303"]
theorem thm_14_1_integrality {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : ∀ x y : V, ∃ n : ℕ, N.cap x y = n) :
    ∃ φ : V → V → ℝ, N.IsFlow φ ∧ (∀ x y : V, ∃ n : ℕ, φ x y = n) ∧
      ∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value φ :=
  Network.exists_integral_maxFlow N hcap

/-- CO-302. A maximum bipartite matching is a maximum integral flow in the unit-capacity network
`S → V₁ → V₂ → T`: matchings give integral flows of the same value and conversely, so the maximum
matching size equals the maximum flow value. -/
@[kb "kellertrotter2017" "text (matchings as flows), p. 305"]
theorem text_p305_matching_as_flow {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (r : A → B → Prop) :
    ∃ (M : Finset (A × B)) (φ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ),
      IsMatching r M ∧ (matchingNetwork r).IsFlow φ ∧ (M.card : ℝ) = (matchingNetwork r).value φ ∧
        (∀ ψ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ,
          (matchingNetwork r).IsFlow ψ → (matchingNetwork r).value ψ ≤ (matchingNetwork r).value φ) ∧
          ∀ M' : Finset (A × B), IsMatching r M' → M'.card ≤ M.card :=
  maxMatching_eq_maxFlow r

/-- CO-303. Matching algorithm: build the unit network from a bipartite graph and run the
labelling algorithm; the resulting flow gives a maximum matching, and the sink is unlabelled. -/
@[kb "kellertrotter2017" "text (matching by labelling), p. 305"]
theorem text_p305_matching_by_labelling {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (r : A → B → Prop) :
    ∃ (M : Finset (A × B)) (φ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ),
      IsMatching r M ∧ (matchingNetwork r).IsFlow φ ∧
        (matchingNetwork r).sink ∉ (matchingNetwork r).labelled φ ∧
          (M.card : ℝ) = (matchingNetwork r).value φ ∧
            ∀ M' : Finset (A × B), IsMatching r M' → M'.card ≤ M.card :=
  matching_by_labelling r

/-- CO-305. The chain-partition network of a poset has a source joined to each `xᵢ'`, each `xⱼ''`
joined to the sink, and an edge `xᵢ' → xⱼ''` exactly when `xᵢ < xⱼ`; all capacities are `1`. -/
@[kb "kellertrotter2017" "text (chain partition network), p. 308"]
theorem text_p308_chain_network {α : Type*} [PartialOrder α] :
    (∀ u v : Option (Option (α ⊕ α)), (Order.chainNetwork α).adj u v ↔
      (u = none ∧ ∃ x : α, v = some (some (Sum.inl x))) ∨
        (∃ x y : α, x < y ∧ u = some (some (Sum.inl x)) ∧ v = some (some (Sum.inr y))) ∨
          (∃ y : α, u = some (some (Sum.inr y))) ∧ v = some none) ∧
    ∀ u v : Option (Option (α ⊕ α)), (Order.chainNetwork α).adj u v →
      (Order.chainNetwork α).cap u v = 1 :=
  ⟨Order.chainNetwork_adj_iff, Order.chainNetwork_cap⟩

/-- CO-306. Chains and a maximum antichain from a maximum flow: for a finite poset there is an
integral maximum flow of some value `v` in the chain network, a partition into `|P| - v` chains read
off from the flow edges, and an antichain of size `|P| - v` read off from the final labelling; so
the width is `|P| - v`. -/
@[kb "kellertrotter2017" "text (chains and antichain from flow), p. 308"]
theorem text_p308_chains_and_antichain {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α] :
    ∃ (φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ) (v : ℕ),
      (Order.chainNetwork α).IsFlow φ ∧ (∀ x y, ∃ n : ℕ, φ x y = n) ∧
        (Order.chainNetwork α).value φ = v ∧
          (∀ ψ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ,
            (Order.chainNetwork α).IsFlow ψ → (Order.chainNetwork α).value ψ ≤ v) ∧
            (∃ g : α → Fin (Fintype.card α - v),
              ∀ i : Fin (Fintype.card α - v), IsChain (fun x1 x2 : α => x1 ≤ x2) (g ⁻¹' {i})) ∧
              IsAntichain (fun x1 x2 : α => x1 ≤ x2) (Order.labelAntichain φ : Set α) ∧
                (Order.labelAntichain φ).card = Fintype.card α - v ∧
                  Order.width α = Fintype.card α - v :=
  Order.exists_maxFlow_chains_and_antichain

/-- CO-307. From an integral flow in the chain network, the chains formed by the flow edges
partition the poset into `|P| - v` chains, and (when the sink is unlabelled) the first
labelled-prime/unlabelled-double-prime element of each chain forms an antichain of the same size. -/
@[kb "kellertrotter2017" "text (chains and antichain of equal size), p. 310"]
theorem text_p310_chain_partition_antichain {α : Type*} [PartialOrder α] [Fintype α]
    [DecidableEq α]
    {φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ}
    (hφ : (Order.chainNetwork α).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n) :
    (∀ {v : ℕ}, (Order.chainNetwork α).value φ = v →
        ∃ g : α → Fin (Fintype.card α - v),
          ∀ i : Fin (Fintype.card α - v), IsChain (fun x1 x2 : α => x1 ≤ x2) (g ⁻¹' {i})) ∧
      IsAntichain (fun x1 x2 : α => x1 ≤ x2) (Order.labelAntichain φ : Set α) ∧
      ((Order.chainNetwork α).sink ∉ (Order.chainNetwork α).labelled φ →
        ((Order.labelAntichain φ).card : ℝ) =
          (Fintype.card α : ℝ) - (Order.chainNetwork α).value φ) :=
  ⟨fun hv => Order.chain_partition_of_flow hφ hint hv, Order.labelAntichain_isAntichain hφ hint,
    fun hs => Order.card_labelAntichain hφ hint hs⟩

/-- CO-314. Cycle notation: the cycle type of a permutation counts its cycles of each length. In
the book's convention fixed points count as cycles of length one, so the cycle lengths are the
cycle type together with one `1` per fixed point. -/
@[kb "kellertrotter2017" "text (cycle notation), p. 319"]
theorem text_p319_cycle_notation {S : Type*} [Fintype S] [DecidableEq S] (σ : Equiv.Perm S) :
    (∀ i : ℕ, 2 ≤ i → Polya.numCyclesOfLength σ i = Multiset.count i σ.cycleType) ∧
      Polya.numCyclesOfLength σ 1 = (Finset.univ.filter fun x : S => σ x = x).card ∧
      Polya.cycleLengths σ =
        σ.cycleType + Multiset.replicate (Finset.univ.filter fun x : S => σ x = x).card 1 :=
  ⟨fun _ hi => Polya.numCyclesOfLength_eq_count_cycleType σ hi, Polya.numCyclesOfLength_one σ,
    Polya.cycleLengths_eq_cycleType_add σ⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch14b
