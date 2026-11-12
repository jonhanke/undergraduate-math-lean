import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UndergradKB.Common

/-!
# Foundations: planar graphs, conditional on drawing data

Mathlib has no plane embeddings and no Jordan curve theorem, so planarity cannot be defined
topologically here. Instead `PlaneDrawing G` is a structure recording exactly the two facts that
Levin's proofs extract from a drawing of a finite connected graph `G` in the plane: Euler's
formula `v - e + f = 2` for the number `f` of faces, and the face-length count (every face is
bounded by at least `g` edges, each edge borders two faces, so `g f ≤ 2 e`, where `g` is any lower
bound for the lengths of cycles of `G`). Every theorem below is therefore **conditional on the
drawing data**; none of them says a graph is planar in the topological sense.
-/

namespace UndergradKB.Foundations

open SimpleGraph

variable {V : Type*}

/-- Data of a plane drawing of a finite connected graph `G`, as hypotheses: a number of faces
satisfying Euler's formula, and the face-length bound `g f ≤ 2 e` for any lower bound `g` on cycle
lengths (when `G` has a cycle). This is a structure of assumptions about a drawing, not a
topological definition of planarity. -/
structure PlaneDrawing (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] where
  /-- The number of faces of the drawing. -/
  faces : ℕ
  /-- The drawn graph is connected. -/
  connected : G.Connected
  /-- Euler's formula `v - e + f = 2`, in the integers. -/
  euler : (Fintype.card V : ℤ) - G.edgeFinset.card + faces = 2
  /-- If every cycle has length at least `g` (and a cycle exists), each face is bounded by at
  least `g` edges and each edge lies on at most two faces, so `g f ≤ 2 e`. -/
  face_bound : ∀ g : ℕ, (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
    ¬ G.IsAcyclic → g * faces ≤ 2 * G.edgeFinset.card

/-- FO-342 (conditional on the drawing data). If every cycle has length at least `g` and the
graph has a cycle, then `(g - 2) e ≤ g (v - 2)`. -/
@[kb "levin2025" "Text §2.3, p. 154"]
theorem PlaneDrawing.girth_edge_bound {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (D : PlaneDrawing G) (g : ℕ) (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length)
    (hcyc : ¬ G.IsAcyclic) :
    ((g : ℤ) - 2) * G.edgeFinset.card ≤ g * ((Fintype.card V : ℤ) - 2) := by
  have h1 := D.face_bound g hg hcyc
  have h2 := D.euler
  have h1' : (g : ℤ) * D.faces ≤ 2 * G.edgeFinset.card := by exact_mod_cast h1
  have hf : (D.faces : ℤ) = 2 - Fintype.card V + G.edgeFinset.card := by linarith
  rw [hf] at h1'
  nlinarith

/-- FO-342 (conditional on the drawing data). The same bound in the form
`e ≤ g (v - 2) / (g - 2)`, for `g ≥ 3`. -/
@[kb "levin2025" "Text §2.3, p. 154"]
theorem PlaneDrawing.girth_edge_bound_div {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (D : PlaneDrawing G) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) (hcyc : ¬ G.IsAcyclic) :
    (G.edgeFinset.card : ℚ) ≤ g * ((Fintype.card V : ℚ) - 2) / (g - 2) := by
  have h := D.girth_edge_bound g hg hcyc
  have hq : ((g : ℚ) - 2) * G.edgeFinset.card ≤ g * ((Fintype.card V : ℚ) - 2) := by
    exact_mod_cast h
  have hpos : (0 : ℚ) < (g : ℚ) - 2 := by
    have : (3 : ℚ) ≤ g := by exact_mod_cast hg3
    linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- FO-339 support (conditional on the drawing data). A drawn graph on `v ≥ 3` vertices has at
most `3 v - 6` edges. -/
@[kb "levin2025" "Thm 2.3.3, p. 153"]
theorem PlaneDrawing.edges_le_three_mul_sub_six {G : SimpleGraph V} [Fintype V]
    [DecidableRel G.Adj] (D : PlaneDrawing G) (hv : 3 ≤ Fintype.card V) :
    (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6 := by
  by_cases hcyc : G.IsAcyclic
  · have ht : G.IsTree := ⟨D.connected, hcyc⟩
    have := ht.card_edgeFinset
    have h2 : (G.edgeFinset.card : ℤ) + 1 = Fintype.card V := by exact_mod_cast this
    have : (3 : ℤ) ≤ Fintype.card V := by exact_mod_cast hv
    linarith
  · have h := D.girth_edge_bound 3 (fun v c hc => hc.three_le_length) hcyc
    push_cast at h
    linarith

/-- FO-339 (conditional on the drawing data). The complete graph on five vertices admits no
plane drawing: `e = 10 > 9 = 3 v - 6`. -/
@[kb "levin2025" "Thm 2.3.3, p. 153"]
theorem not_planeDrawing_K5 (D : PlaneDrawing (⊤ : SimpleGraph (Fin 5))) : False := by
  have h := D.edges_le_three_mul_sub_six (by simp)
  have hc : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp [Nat.choose]
  rw [hc] at h
  simp at h

/-- In a graph with a 2-colouring, a walk has even length iff its endpoints get the same colour. -/
theorem walk_even_iff_color {G : SimpleGraph V} (c : G.Coloring Bool) :
    ∀ {u v : V} (p : G.Walk u v), (c u = c v ↔ Even p.length)
  | _, _, .nil => by simp
  | u, v, .cons (v := w) h p => by
    have ih := walk_even_iff_color c p
    have hne := c.valid h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    revert hne
    generalize c u = a
    generalize c w = b
    generalize c v = d
    cases a <;> cases b <;> cases d <;> simp

/-- Every cycle in a 2-colourable graph has length at least `4`. -/
theorem cycle_length_ge_four_of_colorable_two {G : SimpleGraph V} (c : G.Coloring Bool)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : 4 ≤ p.length := by
  have h3 := hp.three_le_length
  have he := (walk_even_iff_color c p).1 rfl
  obtain ⟨k, hk⟩ := he
  omega

instance : DecidableRel (completeBipartiteGraph (Fin 3) (Fin 3)).Adj := fun a b => by
  rw [completeBipartiteGraph_adj]
  infer_instance

/-- FO-340 (conditional on the drawing data). `K_{3,3}` admits no plane drawing: it has girth `4`
(it is bipartite), so a drawing would force `e ≤ 2 v - 4 = 8`, but `e = 9`. -/
@[kb "levin2025" "Thm 2.3.4, p. 154"]
theorem not_planeDrawing_K33 (D : PlaneDrawing (completeBipartiteGraph (Fin 3) (Fin 3))) :
    False := by
  have hcard : (completeBipartiteGraph (Fin 3) (Fin 3)).edgeFinset.card = 9 := by
    decide
  have hv : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by simp
  have hcyc : ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).IsAcyclic := by
    intro hac
    have ht : (completeBipartiteGraph (Fin 3) (Fin 3)).IsTree := ⟨D.connected, hac⟩
    have := ht.card_edgeFinset
    rw [hcard, hv] at this
    omega
  have h := D.girth_edge_bound 4
    (fun v p hp => cycle_length_ge_four_of_colorable_two
      (SimpleGraph.CompleteBipartiteGraph.bicoloring (Fin 3) (Fin 3)) p hp) hcyc
  rw [hcard, hv] at h
  norm_num at h

end UndergradKB.Foundations
