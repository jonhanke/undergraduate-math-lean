import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import UndergradKB.Combinatorics.Graph.Subdivision
import UndergradKB.Combinatorics.Graph.EulerSplice
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 5: course wrappers of results proved in this library (wave 4)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch05c

universe u

open UndergradKB.Combinatorics

/-- CO-267. The splicing procedure from the proof of Theorem 5.13 is correct: whatever circuit it
returns is an Euler circuit, and on a connected edge list with all degrees even it never fails. -/
@[kb "kellertrotter2017" "text (proof of Theorem 5.13), p. 101"]
theorem thm_5_13_euler_splice_procedure :
    (∀ (es : List (ℕ × ℕ)) (w : List ℕ), Euler.eulerCircuit es = some w →
      Euler.IsEulerCircuit es w) ∧
    (∀ es : List (ℕ × ℕ), (∀ x, Even (Euler.deg es x)) → Euler.EdgeListConnected es →
      Euler.eulerCircuit es ≠ none) :=
  ⟨fun _ _ h => Euler.isEulerCircuit_sound (Euler.eulerCircuit_sound h),
    fun _ hev hconn => Euler.eulerCircuit_complete hev hconn⟩

/-- CO-117. Elementary subdivision of an edge `uv` (a new vertex, `uv` replaced by a path of length
two) adds one vertex and one edge and preserves connectedness; homeomorphism of graphs (having a
common subdivision, up to isomorphism) is reflexive and symmetric. -/
@[kb "kellertrotter2017" "Definition (elementary subdivision, homeomorphic graphs), p. 116"]
theorem def_p116_elementary_subdivision_homeomorphic {V : Type u} :
    (∀ [Fintype V] (_G : SimpleGraph V) (_u _v : V), Fintype.card (Option V) = Fintype.card V + 1) ∧
    (∀ [Finite V] (G : SimpleGraph V) (u v : V), G.Adj u v →
      (Graph.elemSubdiv G u v).edgeSet.ncard = G.edgeSet.ncard + 1) ∧
    (∀ (G : SimpleGraph V), G.Connected → ∀ u v : V, G.Adj u v →
      (Graph.elemSubdiv G u v).Connected) ∧
    (∀ _G : SimpleGraph V, Graph.Homeomorphic _G _G) ∧
    (∀ {W : Type u} {G : SimpleGraph V} {H : SimpleGraph W},
      Graph.Homeomorphic G H → Graph.Homeomorphic H G) :=
  ⟨fun G u v => Graph.card_elemSubdiv G u v,
    fun G u v h => Graph.ncard_edgeSet_elemSubdiv G u v h,
    fun _ hG u v h => Graph.Connected.elemSubdiv hG u v h,
    fun G => Graph.Homeomorphic.refl G,
    fun h => Graph.Homeomorphic.symm h⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch05c
