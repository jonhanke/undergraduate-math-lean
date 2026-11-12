import UndergradKB.Combinatorics.Flow.Network
import UndergradKB.Combinatorics.Flow.MaxFlowMinCut
import UndergradKB.Combinatorics.Flow.Integrality
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 13: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch13b

open UndergradKB.Combinatorics.Flow

/-- CO-291. Weak duality: the value of any flow is at most the capacity of any cut. -/
@[kb "kellertrotter2017" "Theorem 13.4, p. 286"]
theorem thm_13_4_weak_duality {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    {φ : V → V → ℝ} (hφ : N.IsFlow φ) {L : Finset V} (hL : N.IsCut L) :
    N.value φ ≤ N.capacity L :=
  Network.value_le_capacity hφ hL

/-- CO-293. Raising the flow by `δ` along the forward edges and lowering it along the backward
edges of an augmenting path (with `δ` at most every spare amount on the path) gives a flow whose
value is `v + δ`. -/
@[kb "kellertrotter2017" "Proposition 13.7, p. 289"]
theorem prop_13_7_augment {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    {φ : V → V → ℝ} (hφ : N.IsFlow φ) (p : Network.AugPath (N := N) φ N.source N.sink) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hle : ∀ i : Fin p.len, δ ≤ Network.residualCap (N := N) φ (p.vert i.castSucc) (p.vert i.succ)) :
    (N.IsFlow fun x y => φ x y + Network.pathChange p δ x y) ∧
      (N.value fun x y => φ x y + Network.pathChange p δ x y) = N.value φ + δ :=
  Network.augment hφ p hδ hle

/-- CO-296. Max Flow-Min Cut: there is a flow and a cut whose value and capacity coincide, the
flow is maximum and the cut is minimum. -/
@[kb "kellertrotter2017" "Theorem 13.10, p. 292"]
theorem thm_13_10_max_flow_min_cut {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) :
    ∃ (φ : V → V → ℝ) (L : Finset V), N.IsFlow φ ∧ N.IsCut L ∧ N.value φ = N.capacity L ∧
      (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ∧
        ∀ M : Finset V, N.IsCut M → N.capacity L ≤ N.capacity M :=
  Network.maxFlow_minCut N

/-- CO-295. The Ford–Fulkerson labelling algorithm: for a flow `φ`, if the sink is labelled there
is a flow of larger value; if not, the labelled set is a cut of capacity equal to the value of `φ`,
so `φ` is a maximum flow and the cut a minimum cut. For integer capacities the process reaches an
integral maximum flow. -/
@[kb "kellertrotter2017" "Algorithm 13.11, p. 292"]
theorem alg_13_11_labelling {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) :
    (∀ φ : V → V → ℝ, N.IsFlow φ →
      (N.sink ∈ N.labelled φ → ∃ ψ : V → V → ℝ, N.IsFlow ψ ∧ N.value φ < N.value ψ) ∧
        (N.sink ∉ N.labelled φ →
          N.IsCut (N.labelled φ) ∧ N.value φ = N.capacity (N.labelled φ) ∧
            (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ∧
              ∀ M : Finset V, N.IsCut M → N.capacity (N.labelled φ) ≤ N.capacity M)) ∧
    ((∀ x y : V, ∃ n : ℕ, N.cap x y = n) →
      ∃ φ : V → V → ℝ, N.IsFlow φ ∧ (∀ x y : V, ∃ n : ℕ, φ x y = n) ∧ N.sink ∉ N.labelled φ ∧
        N.IsCut (N.labelled φ) ∧ N.value φ = N.capacity (N.labelled φ) ∧
          (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ∧
            ∀ M : Finset V, N.IsCut M → N.capacity (N.labelled φ) ≤ N.capacity M) :=
  ⟨fun _ hφ => Network.labelling_correct hφ, Network.fordFulkerson_integral⟩

/-- CO-297. If the labelling reaches the sink, backtracking gives an augmenting path, hence a flow
of strictly larger value. -/
@[kb "kellertrotter2017" "text (sink labelled), p. 293"]
theorem text_p293_sink_labelled {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    {φ : V → V → ℝ} (hφ : N.IsFlow φ) (hs : N.sink ∈ N.labelled φ) :
    ∃ ψ : V → V → ℝ, N.IsFlow ψ ∧ N.value φ < N.value ψ :=
  Network.exists_larger_of_sink_labelled hφ hs

/-- CO-298. If the labelling stops with the sink unlabelled, the labelled set is a cut whose
capacity equals the current flow value. -/
@[kb "kellertrotter2017" "text (sink unlabelled), p. 293"]
theorem text_p293_sink_unlabelled {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    {φ : V → V → ℝ} (hφ : N.IsFlow φ) (hs : N.sink ∉ N.labelled φ) :
    N.IsCut (N.labelled φ) ∧ N.capacity (N.labelled φ) = N.value φ :=
  ⟨Network.labelled_isCut hs, Network.capacity_labelled_eq_value hφ hs⟩

/-- CO-299 (partial). With integer capacities the Ford–Fulkerson algorithm ends with an integral
maximum flow (the general statement about linear programs with rational data is not formalized). -/
@[kb "kellertrotter2017" "text (rational linear programs and flows), p. 297"]
theorem text_p297_integral_max_flow {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    (hcap : ∀ x y : V, ∃ n : ℕ, N.cap x y = n) :
    ∃ φ : V → V → ℝ, N.IsFlow φ ∧ (∀ x y : V, ∃ n : ℕ, φ x y = n) ∧ N.sink ∉ N.labelled φ ∧
      N.IsCut (N.labelled φ) ∧ N.value φ = N.capacity (N.labelled φ) ∧
        (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ∧
          ∀ M : Finset V, N.IsCut M → N.capacity (N.labelled φ) ≤ N.capacity M :=
  Network.fordFulkerson_integral hcap

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch13b
