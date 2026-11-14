import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 2, worked examples (wave 4, figures)

Graphs read from the page images. A graph is given on `Fin n` from a list of edges.
-/

namespace UndergradKB.Foundations.Course

open SimpleGraph

/-- The simple graph on `Fin n` whose edges are the listed pairs (in either order, loops ignored). -/
def levinListGraph {n : ℕ} (L : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ ((a, b) ∈ L ∨ (b, a) ∈ L)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance levinListGraph_decidable {n : ℕ} (L : List (Fin n × Fin n)) :
    DecidableRel (levinListGraph L).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ L ∨ (b, a) ∈ L)))

private lemma levin_connected_of_parent {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (par : Fin (n + 1) → Fin (n + 1)) (hlt : ∀ v, v ≠ 0 → par v < v)
    (hadj : ∀ v, v ≠ 0 → G.Adj v (par v)) : G.Connected := by
  have h : ∀ k : ℕ, ∀ v : Fin (n + 1), v.val = k → G.Reachable v 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv
      by_cases h0 : v = 0
      · subst h0; exact Reachable.refl _
      · exact (hadj v h0).reachable.trans
          (ih (par v).val (by have := hlt v h0; rw [← hv]; exact this) (par v) rfl)
  exact (connected_iff _).2 ⟨fun u v => (h _ u rfl).trans (h _ v rfl).symm, ⟨0⟩⟩

private lemma levin_isTree_of_parent {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (par : Fin (n + 1) → Fin (n + 1)) (hlt : ∀ v, v ≠ 0 → par v < v)
    (hadj : ∀ v, v ≠ 0 → G.Adj v (par v)) (hcard : Nat.card G.edgeSet = n) : G.IsTree :=
  isTree_iff_connected_and_card.2 ⟨levin_connected_of_parent G par hlt hadj, by
    rw [hcard, Nat.card_eq_fintype_card (α := Fin (n + 1)), Fintype.card_fin]⟩

/-! ### Example 2.1.8: subgraphs and induced subgraphs (vertices `a..f` are `0..5`) -/

/-- `(V₂, G₂)` is a subgraph of `(V₁, G₁)`: vertices and edges are contained. -/
def LevinSubgraphOn (V₂ : Finset (Fin 6)) (G₂ : SimpleGraph (Fin 6)) (V₁ : Finset (Fin 6))
    (G₁ : SimpleGraph (Fin 6)) : Prop :=
  V₂ ⊆ V₁ ∧ ∀ x y, G₂.Adj x y → G₁.Adj x y

/-- `(V₂, G₂)` is an induced subgraph of `(V₁, G₁)`: additionally every edge of `G₁` between vertices of
`V₂` is an edge of `G₂`. -/
def LevinInducedOn (V₂ : Finset (Fin 6)) (G₂ : SimpleGraph (Fin 6)) (V₁ : Finset (Fin 6))
    (G₁ : SimpleGraph (Fin 6)) : Prop :=
  LevinSubgraphOn V₂ G₂ V₁ G₁ ∧ ∀ x ∈ V₂, ∀ y ∈ V₂, G₁.Adj x y → G₂.Adj x y

instance (V₂ : Finset (Fin 6)) (G₂ : SimpleGraph (Fin 6)) (V₁ : Finset (Fin 6))
    (G₁ : SimpleGraph (Fin 6)) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    Decidable (LevinSubgraphOn V₂ G₂ V₁ G₁) := by unfold LevinSubgraphOn; infer_instance

instance (V₂ : Finset (Fin 6)) (G₂ : SimpleGraph (Fin 6)) (V₁ : Finset (Fin 6))
    (G₁ : SimpleGraph (Fin 6)) [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    Decidable (LevinInducedOn V₂ G₂ V₁ G₁) := by unfold LevinInducedOn; infer_instance

/-- Graph `G₁` of Example 2.1.8 (three nested triangles; `a b c d e f = 0 1 2 3 4 5`). -/
abbrev levinG218_1 : SimpleGraph (Fin 6) :=
  levinListGraph [(0, 3), (3, 5), (5, 4), (4, 2), (0, 1), (1, 2), (3, 1), (4, 1), (3, 4)]

/-- Graph `G₂` of Example 2.1.8 on `{a,b,c,d}`. -/
abbrev levinG218_2 : SimpleGraph (Fin 6) := levinListGraph [(0, 3), (3, 1), (0, 1), (1, 2)]

/-- Graph `G₃` of Example 2.1.8 on `{a,b,c,d,f}`. -/
abbrev levinG218_3 : SimpleGraph (Fin 6) := levinListGraph [(0, 3), (3, 5), (3, 1), (1, 2)]

/-- Graph `G₄` of Example 2.1.8 on `{a,b,c,d,f}`. -/
abbrev levinG218_4 : SimpleGraph (Fin 6) :=
  levinListGraph [(0, 3), (3, 5), (3, 1), (0, 1), (1, 2), (5, 2)]

/-- Levin Example 2.1.8: `G₂` and `G₃` are subgraphs of `G₁`, but only `G₂` is induced (in `G₃` the edge `ab`
of `G₁` is missing although `a, b` are vertices); `G₄` is not a subgraph of `G₁` since `cf` is not an edge
of `G₁`. -/
@[kb "levin2025" "Example 2.1.8, p. 127"]
theorem levin_ex_2_1_8_subgraphs :
    LevinInducedOn {0, 1, 2, 3} levinG218_2 Finset.univ levinG218_1 ∧
    LevinSubgraphOn {0, 1, 2, 3, 5} levinG218_3 Finset.univ levinG218_1 ∧
    ¬ LevinInducedOn {0, 1, 2, 3, 5} levinG218_3 Finset.univ levinG218_1 ∧
    ¬ LevinSubgraphOn {0, 1, 2, 3, 5} levinG218_4 Finset.univ levinG218_1 := by
  unfold LevinInducedOn LevinSubgraphOn levinG218_1 levinG218_2 levinG218_3 levinG218_4
  decide

/-! ### Example 2.2.9: two spanning trees (center `0`, then `TL TR BL BR L R = 1 2 3 4 5 6`) -/

/-- The graph of Example 2.2.9. -/
abbrev levinG229 : SimpleGraph (Fin 7) :=
  levinListGraph [(5, 1), (5, 3), (1, 2), (1, 3), (1, 0), (2, 0), (2, 6), (2, 4), (3, 0), (3, 4),
    (0, 4), (6, 4)]

/-- First spanning tree: the center joined to the four middle vertices, plus the two outer vertices. -/
abbrev levinG229T1 : SimpleGraph (Fin 7) :=
  levinListGraph [(1, 0), (2, 0), (3, 0), (4, 0), (5, 1), (6, 2)]

/-- Second spanning tree. -/
abbrev levinG229T2 : SimpleGraph (Fin 7) :=
  levinListGraph [(1, 0), (2, 1), (3, 1), (4, 2), (5, 3), (6, 4)]

/-- Levin Example 2.2.9: the graph has two different spanning trees (subgraphs on all seven vertices that
are trees). The two trees are our own choice; the book's drawn trees are not reproduced. -/
@[kb "levin2025" "Example 2.2.9, p. 142"]
theorem levin_ex_2_2_9_two_spanning_trees :
    levinG229T1 ≤ levinG229 ∧ levinG229T2 ≤ levinG229 ∧ levinG229T1.IsTree ∧ levinG229T2.IsTree ∧
    levinG229T1 ≠ levinG229T2 := by
  have hle1 : levinG229T1 ≤ levinG229 := by
    intro a b; unfold levinG229T1 levinG229; revert a b; decide
  have hle2 : levinG229T2 ≤ levinG229 := by
    intro a b; unfold levinG229T2 levinG229; revert a b; decide
  refine ⟨hle1, hle2, ?_, ?_, fun h => ?_⟩
  · refine levin_isTree_of_parent _ ![0, 0, 0, 0, 0, 1, 2] ?_ ?_ ?_
    · decide
    · decide
    · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      decide
  · refine levin_isTree_of_parent _ ![0, 0, 1, 1, 2, 3, 4] ?_ ?_ ?_
    · decide
    · decide
    · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      decide
  · have := congrArg (fun G : SimpleGraph (Fin 7) => G.Adj 2 0) h
    revert this; unfold levinG229T1 levinG229T2; decide

/-! ### Example 2.2.10: a rooted tree (`e c a b d g f h i = 0 1 2 3 4 5 6 7 8`) -/

/-- The tree of Example 2.2.10 with edges `ac, ce, be, de, eg, ef, fh, fi`. -/
abbrev levinTree2210 : SimpleGraph (Fin 9) :=
  levinListGraph [(2, 1), (1, 0), (3, 0), (4, 0), (0, 5), (0, 6), (6, 7), (6, 8)]

/-- Levin Example 2.2.10: the figure is a tree; with root `f` the children of `f` are `e, h, i`, `a` is a
descendant of `f` through `f, e, c, a`, and `g` is a grandchild of `f`; `g` and `d` are siblings with parent
`e` and are not adjacent; with root `a` the lone child of `a` is `c`, whose only other neighbor is `e`, and
`f` hangs below `e`. -/
@[kb "levin2025" "Example 2.2.10, p. 144"]
theorem levin_ex_2_2_10_rooted_tree :
    levinTree2210.IsTree ∧
    (Finset.univ.filter (fun v => levinTree2210.Adj 6 v) = {0, 7, 8}) ∧
    (levinTree2210.Adj 6 0 ∧ levinTree2210.Adj 0 1 ∧ levinTree2210.Adj 1 2) ∧
    (levinTree2210.Adj 6 0 ∧ levinTree2210.Adj 0 5) ∧
    (levinTree2210.Adj 0 5 ∧ levinTree2210.Adj 0 4 ∧ (5 : Fin 9) ≠ 4 ∧ ¬ levinTree2210.Adj 5 4) ∧
    (Finset.univ.filter (fun v => levinTree2210.Adj 2 v) = {1}) ∧
    (Finset.univ.filter (fun v => levinTree2210.Adj 1 v) = {0, 2}) ∧
    levinTree2210.Adj 0 6 := by
  refine ⟨?_, ?_⟩
  · refine levin_isTree_of_parent _ ![0, 0, 1, 0, 0, 0, 0, 6, 6] ?_ ?_ ?_
    · decide
    · decide
    · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      decide
  · unfold levinTree2210; decide

/-! ### Example 2.4.2: Hamilton paths (a path is an ordering of all vertices with consecutive ones adjacent)

Left graph: the Petersen graph (outer cycle `0..4`, inner vertices `5..9` with spokes `i -- i+5` and
inner edges `5+i -- 5+(i+2)`). Right graph: the complete graph on `0..4` with a pendant vertex `5+i`
attached to each `i`. -/

/-- The left graph of Example 2.4.2 (Petersen graph). -/
abbrev levinPetersen : SimpleGraph (Fin 10) :=
  levinListGraph [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

/-- The right graph of Example 2.4.2: `K₅` with a pendant vertex at every vertex. -/
abbrev levinK5Pendants : SimpleGraph (Fin 10) :=
  levinListGraph [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]

/-- Levin Example 2.4.2: the left graph has a Hamilton path (an ordering of all ten vertices with consecutive
vertices adjacent), the right graph has none: its five pendant vertices could only be placed at the two ends. -/
@[kb "levin2025" "Example 2.4.2, p. 165"]
theorem levin_ex_2_4_2_hamilton_paths :
    (∃ f : Fin 10 → Fin 10, Function.Bijective f ∧
      ∀ i : Fin 9, levinPetersen.Adj (f i.castSucc) (f i.succ)) ∧
    ¬ ∃ f : Fin 10 → Fin 10, Function.Bijective f ∧
      ∀ i : Fin 9, levinK5Pendants.Adj (f i.castSucc) (f i.succ) := by
  refine ⟨⟨![0, 1, 2, 3, 4, 9, 7, 5, 8, 6], ?_, ?_⟩, ?_⟩
  · decide
  · unfold levinPetersen; decide
  · rintro ⟨f, hb, hadj⟩
    have hleaf : ∀ v w x : Fin 10, 5 ≤ v.val → levinK5Pendants.Adj w v → levinK5Pendants.Adj v x →
        w = x := by
      unfold levinK5Pendants; decide
    have hend : ∀ i : Fin 10, 5 ≤ (f i).val → i = 0 ∨ i = 9 := by
      intro i hi
      by_contra hne
      push Not at hne
      have hi1 : 1 ≤ i.val := by
        rcases Nat.eq_zero_or_pos i.val with h | h
        · exact absurd (Fin.ext h) hne.1
        · exact h
      have hi2 : i.val ≤ 8 := by
        have : i.val ≠ 9 := fun h => hne.2 (Fin.ext h)
        omega
      let j : Fin 9 := ⟨i.val - 1, by omega⟩
      let k : Fin 9 := ⟨i.val, by omega⟩
      have h1 := hadj j
      have h2 := hadj k
      have e1 : j.succ = i := Fin.ext (by simp only [j, Fin.val_succ]; omega)
      have e2 : k.castSucc = i := Fin.ext (by simp [k])
      rw [e1] at h1
      rw [e2] at h2
      have := hb.injective (hleaf _ _ _ hi h1 h2)
      have h3 := congrArg Fin.val this
      simp [j, k] at h3
    let S : Finset (Fin 10) := Finset.univ.filter (fun i => 5 ≤ (f i).val)
    have hS : S ⊆ {0, 9} := by
      intro i hi
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simpa using hend i hi
    have himg : S.image f = Finset.univ.filter (fun v : Fin 10 => 5 ≤ v.val) := by
      ext v
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hv
        obtain ⟨i, rfl⟩ := hb.surjective v
        exact ⟨i, hv, rfl⟩
    have hc1 : (S.image f).card = S.card := Finset.card_image_of_injective _ hb.injective
    have hc2 : (Finset.univ.filter (fun v : Fin 10 => 5 ≤ v.val)).card = 5 := by decide
    rw [himg] at hc1
    have hc3 : S.card ≤ ({0, 9} : Finset (Fin 10)).card := Finset.card_le_card hS
    have hc4 : ({0, 9} : Finset (Fin 10)).card = 2 := by decide
    omega

/-! ### Example 2.5.5: radio stations KQEA..KQEJ are `0..9` -/

/-- The interference graph of Example 2.5.5 (read from the table). -/
abbrev levinRadioGraph : SimpleGraph (Fin 10) :=
  levinListGraph [(0, 2), (0, 5), (0, 6), (0, 9), (1, 2), (1, 3), (2, 5), (2, 6), (2, 9), (3, 4),
    (3, 5), (3, 7), (4, 8), (5, 6), (5, 9), (6, 9), (7, 8), (8, 9)]

/-- Levin Example 2.5.5: the interference graph is 5-colorable (explicit coloring of the stations by five
frequencies) but not 4-colorable, because `KQEA, KQEC, KQEF, KQEG, KQEJ` are pairwise adjacent (a `K₅`);
hence its chromatic number is 5. -/
@[kb "levin2025" "Example 2.5.5, p. 175"]
theorem levin_ex_2_5_5_radio_frequencies :
    levinRadioGraph.Colorable 5 ∧ ¬ levinRadioGraph.Colorable 4 ∧
    levinRadioGraph.chromaticNumber = 5 := by
  have hcol : levinRadioGraph.Colorable 5 := by
    refine ⟨Coloring.mk ![0, 0, 1, 1, 0, 2, 3, 0, 1, 4] ?_⟩
    intro a b
    revert a b
    unfold levinRadioGraph
    decide
  have hcl : levinRadioGraph.IsClique (({0, 2, 5, 6, 9} : Finset (Fin 10)) : Set (Fin 10)) := by
    rw [isClique_iff]
    have : ∀ x ∈ ({0, 2, 5, 6, 9} : Finset (Fin 10)), ∀ y ∈ ({0, 2, 5, 6, 9} : Finset (Fin 10)),
        x ≠ y → levinRadioGraph.Adj x y := by
      unfold levinRadioGraph; decide
    intro x hx y hy hxy
    exact this x hx y hy hxy
  have h4 : ¬ levinRadioGraph.Colorable 4 := fun h => by
    have := hcl.card_le_of_colorable h
    revert this; decide
  refine ⟨hcol, h4, ?_⟩
  apply le_antisymm hcol.chromaticNumber_le
  have := hcl.card_le_chromaticNumber
  simpa using this

end UndergradKB.Foundations.Course
