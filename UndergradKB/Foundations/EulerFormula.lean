import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import UndergradKB.Foundations.Planarity

/-!
# Foundations: Euler's formula from the two face facts of Levin's proof

Mathlib has no plane embeddings and no Jordan curve theorem, so the number of faces of a drawing
cannot be defined here. Wave 1 recorded Euler's formula itself as a hypothesis (`PlaneDrawing`).
This file proves Euler's formula, following Levin's argument (Section 2.3.2, pdf p. 151: remove edges
from a connected planar graph and watch `v - e + f`), from the two topological facts that argument
uses, recorded as the named input `FaceData G`:

* erasing edges of a drawing of `G` gives a drawing of every spanning subgraph `H ≤ G`, with some
  number `faces H` of faces;
* a drawing of a tree has exactly one face;
* erasing an edge that lies on a cycle of a connected drawn graph merges the two faces on either
  side of it into one, so the number of faces drops by exactly one.

The second and third items are where the topology lives: the complement of a drawn tree is
connected, and the two sides of an edge on a drawn cycle lie in different faces (the Jordan curve
theorem for the cycle). They are inputs here, not theorems; Euler's formula is then derived by
Levin's induction on the number of edges. `PlaneFaceData` adds the face-length count `g f ≤ 2 e`
used for `K₅` and `K_{3,3}`, and produces the wave 1 `PlaneDrawing`, so the non-planarity theorems
now rest on these more primitive inputs instead of on Euler's formula.

Also Theorem 2.3.7 (pdf p. 156) in the form "the counts `v, e, f, p, q` of a regular polyhedron are
those of the five Platonic solids", from Euler's formula and the two edge counts.
-/

namespace UndergradKB.Foundations

open SimpleGraph

variable {V : Type*}

/-- The face facts of a drawing of `G` in the plane that Levin's proof of Euler's formula uses, as
hypotheses (a named input, not a definition of planarity): a face count for the drawing of each
spanning subgraph obtained by erasing edges, equal to `1` for trees, and dropping by exactly `1`
when an edge lying on a cycle is erased. -/
structure FaceData (G : SimpleGraph V) where
  /-- The number of faces of the drawing of the spanning subgraph `H ≤ G` (obtained from the drawing
  of `G` by erasing the edges not in `H`). -/
  faces : SimpleGraph V → ℕ
  /-- A drawn tree has exactly one face (its complement in the plane is connected). -/
  tree_faces : ∀ T ≤ G, T.IsTree → faces T = 1
  /-- Erasing an edge `e` that lies on a cycle of a connected drawn graph `H` merges the two
  faces on its two sides (they are different faces by the Jordan curve theorem for the cycle). -/
  cycle_edge_faces : ∀ H ≤ G, H.Connected → ∀ (u : V) (c : H.Walk u u), c.IsCycle →
    ∀ e ∈ c.edges, faces H = faces (H.deleteEdges {e}) + 1

/-- Levin's induction: every connected spanning subgraph `H` of the drawn graph satisfies
`v - e + f = 2`. -/
theorem FaceData.euler_of_le [Finite V] {G : SimpleGraph V} (D : FaceData G) :
    ∀ (n : ℕ) (H : SimpleGraph V), H ≤ G → H.Connected → H.edgeSet.ncard = n →
      (Nat.card V : ℤ) - n + D.faces H = 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hH hc hn
    by_cases hac : H.IsAcyclic
    · have ht : H.IsTree := ⟨hc, hac⟩
      have h1 := ht.ncard_edgeSet_add_one
      rw [D.tree_faces H hH ht, ← hn]
      have h2 : (H.edgeSet.ncard : ℤ) + 1 = Nat.card V := by exact_mod_cast h1
      push_cast
      linarith
    · obtain ⟨u, c, hcyc⟩ := not_isAcyclic_iff_exists_isCycle.1 hac
      obtain ⟨e, he⟩ := c.edges.exists_mem_of_ne_nil (by simp [hcyc.not_nil])
      have hbr : ¬ H.IsBridge e := fun hb => hb.notMem_edges_of_isCycle hcyc he
      have hc' := hc.preconnected.connected_deleteEdges_of_not_isBridge hbr
      have heH : e ∈ H.edgeSet := c.edges_subset_edgeSet he
      have hcard : (H.deleteEdges {e}).edgeSet.ncard + 1 = n := by
        rw [edgeSet_deleteEdges, ← hn]
        exact Set.ncard_sdiff_singleton_add_one heH
      have := ih _ (by omega) (H.deleteEdges {e}) ((deleteEdges_le _).trans hH) hc' rfl
      rw [D.cycle_edge_faces H hH hc u c hcyc e he, ← hcard]
      push_cast at this ⊢
      linarith

/-- FO-338 (conditional on the named input `FaceData`). **Euler's formula**: a connected graph
drawn in the plane with `v` vertices, `e` edges and `f` faces has `v - e + f = 2`. -/
@[kb "levin2025" "Euler's Formula for Planar Graphs §2.3.2, p. 151"]
theorem FaceData.euler [Finite V] {G : SimpleGraph V} (D : FaceData G) (hG : G.Connected) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + D.faces G = 2 :=
  D.euler_of_le _ G le_rfl hG rfl

/-- The face facts of `FaceData` together with the face-length count of Levin's proofs of
Theorems 2.3.3 and 2.3.4 (each face is bounded by at least `g` edges when every cycle has length at
least `g`, and each edge borders at most two faces, so `g f ≤ 2 e`), for a connected drawn graph. -/
structure PlaneFaceData (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    extends FaceData G where
  /-- The drawn graph is connected. -/
  connected : G.Connected
  /-- The face-length count `g f ≤ 2 e`. -/
  face_bound : ∀ g : ℕ, (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
    ¬ G.IsAcyclic → g * faces G ≤ 2 * G.edgeFinset.card

/-- The wave 1 drawing data, now with Euler's formula proved from the face facts. -/
noncomputable def PlaneFaceData.toPlaneDrawing {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (D : PlaneFaceData G) : PlaneDrawing G where
  faces := D.faces G
  connected := D.connected
  euler := by
    have h := D.toFaceData.euler D.connected
    rw [Nat.card_eq_fintype_card, ← coe_edgeFinset, Set.ncard_coe_finset] at h
    exact h
  face_bound := D.face_bound

/-- FO-339 (conditional on the named input `PlaneFaceData`). `K₅` is not planar. -/
@[kb "levin2025" "Thm 2.3.3, p. 153"]
theorem not_planeFaceData_K5 (D : PlaneFaceData (⊤ : SimpleGraph (Fin 5))) : False :=
  not_planeDrawing_K5 D.toPlaneDrawing

/-- FO-340 (conditional on the named input `PlaneFaceData`). `K_{3,3}` is not planar. -/
@[kb "levin2025" "Thm 2.3.4, p. 154"]
theorem not_planeFaceData_K33 (D : PlaneFaceData (completeBipartiteGraph (Fin 3) (Fin 3))) :
    False :=
  not_planeDrawing_K33 D.toPlaneDrawing

/-- FO-342 (conditional on the named input `PlaneFaceData`). A drawn graph with a cycle, all of
whose cycles have length at least `g`, has `(g - 2) e ≤ g (v - 2)`. -/
@[kb "levin2025" "Text §2.3, p. 154"]
theorem PlaneFaceData.girth_edge_bound {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (D : PlaneFaceData G) (g : ℕ) (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length)
    (hcyc : ¬ G.IsAcyclic) :
    ((g : ℤ) - 2) * G.edgeFinset.card ≤ g * ((Fintype.card V : ℤ) - 2) :=
  D.toPlaneDrawing.girth_edge_bound g hg hcyc

/-- FO-344 (counting core of Theorem 2.3.7). If `v - e + f = 2` (Euler's formula for the graph of
a convex polyhedron), every face has `p ≥ 3` edges (`p f = 2 e`) and every vertex has degree `q ≥ 3`
(`q v = 2 e`), then `(p, q; v, e, f)` is that of the tetrahedron, octahedron, cube, icosahedron or
dodecahedron. -/
@[kb "levin2025" "Thm 2.3.7, p. 156"]
theorem levin_thm_2_3_7_platonic_counts (v e f p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (heuler : (v : ℤ) - e + f = 2) (hf : p * f = 2 * e) (hv : q * v = 2 * e) :
    (p = 3 ∧ q = 3 ∧ v = 4 ∧ e = 6 ∧ f = 4) ∨ (p = 3 ∧ q = 4 ∧ v = 6 ∧ e = 12 ∧ f = 8) ∨
      (p = 4 ∧ q = 3 ∧ v = 8 ∧ e = 12 ∧ f = 6) ∨ (p = 3 ∧ q = 5 ∧ v = 12 ∧ e = 30 ∧ f = 20) ∨
      (p = 5 ∧ q = 3 ∧ v = 20 ∧ e = 30 ∧ f = 12) := by
  have hf' : (p : ℤ) * f = 2 * e := by exact_mod_cast hf
  have hv' : (q : ℤ) * v = 2 * e := by exact_mod_cast hv
  have key : (e : ℤ) * (2 * p + 2 * q - p * q) = 2 * p * q := by
    linear_combination (↑p * ↑q : ℤ) * heuler - (q : ℤ) * hf' - (p : ℤ) * hv'
  have hpq : p * q < 2 * p + 2 * q := by
    have hp0 : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
    have hq0 : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
    have he : (0 : ℤ) ≤ e := by positivity
    have : (0 : ℤ) < 2 * p + 2 * q - p * q := by
      by_contra h
      push Not at h
      have : (e : ℤ) * (2 * p + 2 * q - p * q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he h
      nlinarith
    have : (p : ℤ) * q < 2 * p + 2 * q := by linarith
    exact_mod_cast this
  have hp5 : p ≤ 5 := by nlinarith
  have hq5 : q ≤ 5 := by nlinarith
  interval_cases p <;> interval_cases q <;> omega

end UndergradKB.Foundations
