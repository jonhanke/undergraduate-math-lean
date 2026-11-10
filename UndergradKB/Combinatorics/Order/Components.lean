import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import UndergradKB.Combinatorics.Order.Basic

/-!
# Components of a poset

Source: Keller--Trotter, *Applied Combinatorics* (2017), Section 6.1 (p. 144).
A subposet `(Y, P(Y))` is a component when it is connected (its comparability graph is connected)
and no strictly larger subposet is connected. We show that the components are exactly the vertex
sets of the connected components of the comparability graph, so they partition the ground set, and
that a loose point (one-point component) is both minimal and maximal.
-/

namespace UndergradKB.Combinatorics.Order

variable {α : Type*} [PartialOrder α]

/-- The comparability graph of the subposet on `Y` is the induced subgraph of the comparability
graph on `Y`. -/
theorem comparabilityGraph_subtype (Y : Set α) :
    comparabilityGraph Y = (comparabilityGraph α).induce Y := by
  ext x y
  simp [comparabilityGraph_adj, Comparable, Subtype.ext_iff]

/-- CO-153. A subposet `(Y, P(Y))` is a component of `P` if it is connected and no subset strictly
containing `Y` induces a connected subposet. -/
@[kb "kellertrotter2017" "Definition (unnumbered) component, p. 144"]
def IsComponent (Y : Set α) : Prop :=
  IsConnectedPoset Y ∧ ∀ Z : Set α, Y ⊆ Z → IsConnectedPoset Z → Z = Y

/-- CO-153. The components of a poset are exactly the vertex sets of the connected components of
its comparability graph. -/
@[kb "kellertrotter2017" "Definition (unnumbered) component, p. 144"]
theorem isComponent_iff (Y : Set α) :
    IsComponent Y ↔ ∃ C : (comparabilityGraph α).ConnectedComponent, C.supp = Y := by
  rw [← SimpleGraph.ConnectedComponent.maximal_connected_induce_iff]
  simp only [IsComponent, IsConnectedPoset, comparabilityGraph_subtype, Maximal]
  constructor
  · rintro ⟨h, hmax⟩
    exact ⟨h, fun Z hZ hYZ => (hmax Z hYZ hZ).le⟩
  · rintro ⟨h, hmax⟩
    exact ⟨h, fun Z hYZ hZ => le_antisymm (hmax hZ hYZ) hYZ⟩

/-- CO-153. Every point lies in exactly one component. -/
@[kb "kellertrotter2017" "Definition (unnumbered) component, p. 144"]
theorem existsUnique_component (x : α) : ∃! Y : Set α, IsComponent Y ∧ x ∈ Y := by
  refine ⟨((comparabilityGraph α).connectedComponentMk x).supp,
    ⟨(isComponent_iff _).2 ⟨_, rfl⟩, rfl⟩, ?_⟩
  rintro Y ⟨hY, hx⟩
  obtain ⟨C, rfl⟩ := (isComponent_iff Y).1 hY
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx
  rw [hx]

/-- CO-153. A loose point (a one-point component) is both a minimal and a maximal element. -/
@[kb "kellertrotter2017" "Definition (unnumbered) component, p. 144"]
theorem isMin_isMax_of_isComponent_singleton {x : α} (h : IsComponent ({x} : Set α)) :
    IsMin x ∧ IsMax x := by
  obtain ⟨C, hC⟩ := (isComponent_iff _).1 h
  have hx : x ∈ C.supp := hC ▸ rfl
  have key : ∀ y, Comparable x y → False := by
    intro y hxy
    have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hx (comparabilityGraph_adj.2 hxy)
    rw [hC] at hy
    exact hxy.1 hy.symm
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · by_contra hne
    exact key y ⟨fun e => hne (e ▸ le_rfl), Or.inr hy⟩
  · by_contra hne
    exact key y ⟨fun e => hne (e ▸ le_rfl), Or.inl hy⟩

end UndergradKB.Combinatorics.Order
