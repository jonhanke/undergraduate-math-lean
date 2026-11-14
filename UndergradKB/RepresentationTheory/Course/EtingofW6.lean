import UndergradKB.RepresentationTheory.IcosahedronProblem
import UndergradKB.Common.Attr

/-! # Course names, wave 6: Problem 3.21 for the geometric icosahedron

Course-facing names for the regular icosahedron in `ℝ³` (vertices the cyclic permutations of `(0, ±1, ±φ)`), its
rotation group `Icosahedron.rotGroup`, the isomorphism with `A5`, and the three decompositions of Problem 3.21.
-/

namespace UndergradKB.RepresentationTheory.Course

/-- Etingof et al., Problem 3.21 (recalled fact): the rotation group of the regular icosahedron is isomorphic to
`A5`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_rotation_group := Icosahedron.rotGroup_iso_A5

/-- Etingof et al., Problem 3.21 (recalled fact): the rotation group is transitive on the `12` vertices. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_transitive_vertices := Icosahedron.transitive_vert

/-- Etingof et al., Problem 3.21 (recalled fact): the rotation group is transitive on the `30` edges. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_transitive_edges := Icosahedron.transitive_edge

/-- Etingof et al., Problem 3.21 (recalled fact): the rotation group is transitive on the `20` faces. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_transitive_faces := Icosahedron.transitive_face

/-- Etingof et al., Problem 3.21, geometric form: functions on the vertices of the regular icosahedron decompose
as `1 ⊕ 5 ⊕ 3 ⊕ 3'` under its rotation group. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_geometric_vertices := Icosahedron.etingof_3_21_vertices

/-- Etingof et al., Problem 3.21, geometric form: functions on the faces decompose as `1 ⊕ 2 · 4 ⊕ 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_geometric_faces := Icosahedron.etingof_3_21_faces

/-- Etingof et al., Problem 3.21, geometric form: functions on the edges decompose as
`1 ⊕ 2 · 4 ⊕ 3 · 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_geometric_edges := Icosahedron.etingof_3_21_edges

end UndergradKB.RepresentationTheory.Course
