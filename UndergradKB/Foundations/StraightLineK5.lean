import Mathlib.Data.Fintype.Basic
import UndergradKB.Foundations.StraightLine

/-!
# Foundations: `K₅` has no straight-line plane drawing

Levin, Theorem 2.3.3 (pdf p. 153): `K₅` is not planar. Levin's proof uses Euler's formula and the
face-length count; both need the topology of plane drawings by curves, which Mathlib lacks
(`PlaneFaceData` in `EulerFormula.lean` records them as inputs). Here the statement is proved
unconditionally for drawings with straight edges (`StraightLineDrawing`), by a different argument:

* in a straight-line drawing of `K₅` no three vertices are collinear (`orient_ne_zero`), since
  every pair of vertices is an edge;
* for each four of the five vertices, the four-point identity `orient_four` restricts the signs of
  the four orientations, and the absence of crossings excludes three more sign patterns
  (`cross12_false`, `cross13_false`, `cross14_false`);
* no assignment of signs to the ten triples satisfies all these constraints (`k5_signs`, checked
  by `decide` over the `2^10` sign patterns). Geometrically: some four of the vertices are in
  convex position, and the diagonals of that quadrilateral cross.

Restriction: straight edges instead of curves (Fáry's theorem, not in Mathlib, says that every
planar simple graph has a straight-line drawing).
-/

namespace UndergradKB.Foundations

/-- The sign constraints on four vertices `i, j, k, l` of a straight-line drawing of a complete
graph: the four-point identity and the three excluded crossings. -/
theorem StraightLineDrawing.top_four {V : Type*} (D : StraightLineDrawing (⊤ : SimpleGraph V))
    (i j k l : V) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) :
    quadOk (decide (0 < orient (D.pos j) (D.pos k) (D.pos l)))
        (decide (0 < orient (D.pos i) (D.pos k) (D.pos l)))
        (decide (0 < orient (D.pos i) (D.pos j) (D.pos l)))
        (decide (0 < orient (D.pos i) (D.pos j) (D.pos k))) = true ∧
      (decide (0 < orient (D.pos i) (D.pos j) (D.pos k)) !=
          decide (0 < orient (D.pos i) (D.pos j) (D.pos l)) &&
        decide (0 < orient (D.pos i) (D.pos k) (D.pos l)) !=
          decide (0 < orient (D.pos j) (D.pos k) (D.pos l))) = false ∧
      (decide (0 < orient (D.pos i) (D.pos j) (D.pos k)) ==
          decide (0 < orient (D.pos i) (D.pos k) (D.pos l)) &&
        decide (0 < orient (D.pos i) (D.pos j) (D.pos l)) ==
          decide (0 < orient (D.pos j) (D.pos k) (D.pos l))) = false ∧
      (decide (0 < orient (D.pos i) (D.pos j) (D.pos l)) !=
          decide (0 < orient (D.pos i) (D.pos k) (D.pos l)) &&
        decide (0 < orient (D.pos i) (D.pos j) (D.pos k)) !=
          decide (0 < orient (D.pos j) (D.pos k) (D.pos l))) = false := by
  have a := fun {x y : V} (h : x ≠ y) => (SimpleGraph.top_adj x y).2 h
  have h1 := D.orient_ne_zero (a hij) (a hjk) (a hik)
  have h2 := D.orient_ne_zero (a hij) (a hjl) (a hil)
  have h3 := D.orient_ne_zero (a hik) (a hkl) (a hil)
  have h4 := D.orient_ne_zero (a hjk) (a hkl) (a hjl)
  refine ⟨quadOk_four _ _ _ _, cross12_false h1 h2 h3 h4 ?_, cross13_false h1 h2 h3 h4 ?_,
    cross14_false h1 h2 h3 h4 ?_⟩
  · exact D.disjoint i j k l (a hij) (a hkl) hik hil hjk hjl
  · exact D.disjoint i k j l (a hik) (a hjl) hij hil hjk.symm hkl
  · exact D.disjoint i l j k (a hil) (a hjk) hij hik hjl.symm hkl.symm

set_option synthInstance.maxSize 4096 in
/-- No assignment of signs to the ten triples of five points satisfies the constraints of
`StraightLineDrawing.top_four` for all five quadruples. Variable `bijk` is the sign of the
orientation of the triple `i j k`. -/
theorem k5_signs : ∀ b012 b013 b014 b023 b024 b034 b123 b124 b134 b234 : Bool,
    quadOk b123 b023 b013 b012 = true →
    (b012 != b013 && b023 != b123) = false →
    (b012 == b023 && b013 == b123) = false →
    (b013 != b023 && b012 != b123) = false →
    quadOk b124 b024 b014 b012 = true →
    (b012 != b014 && b024 != b124) = false →
    (b012 == b024 && b014 == b124) = false →
    (b014 != b024 && b012 != b124) = false →
    quadOk b134 b034 b014 b013 = true →
    (b013 != b014 && b034 != b134) = false →
    (b013 == b034 && b014 == b134) = false →
    (b014 != b034 && b013 != b134) = false →
    quadOk b234 b034 b024 b023 = true →
    (b023 != b024 && b034 != b234) = false →
    (b023 == b034 && b024 == b234) = false →
    (b024 != b034 && b023 != b234) = false →
    quadOk b234 b134 b124 b123 = true →
    (b123 != b124 && b134 != b234) = false →
    (b123 == b134 && b124 == b234) = false →
    (b124 != b134 && b123 != b234) = false →
    False := by decide

/-- FO-339 (straight-line drawings). **`K₅` is not planar**: the complete graph on five vertices
has no drawing in the plane with straight edges and no crossings. -/
@[kb "levin2025" "Thm 2.3.3, p. 153"]
theorem not_straightLineDrawing_K5 (D : StraightLineDrawing (⊤ : SimpleGraph (Fin 5))) :
    False := by
  obtain ⟨a1, a2, a3, a4⟩ := D.top_four 0 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨b1, b2, b3, b4⟩ := D.top_four 0 1 2 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨c1, c2, c3, c4⟩ := D.top_four 0 1 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨d1, d2, d3, d4⟩ := D.top_four 0 2 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨e1, e2, e3, e4⟩ := D.top_four 1 2 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  exact k5_signs _ _ _ _ _ _ _ _ _ _ a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4
    e1 e2 e3 e4

end UndergradKB.Foundations
