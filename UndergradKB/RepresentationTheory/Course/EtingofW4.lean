import UndergradKB.RepresentationTheory.Basic
import UndergradKB.RepresentationTheory.PathAlgebra
import UndergradKB.RepresentationTheory.AlgebrasMisc
import UndergradKB.RepresentationTheory.AlgebrasChapter2
import UndergradKB.RepresentationTheory.CharactersChapter4
import UndergradKB.RepresentationTheory.CharactersMore
import UndergradKB.RepresentationTheory.AlgebraicIntegers
import UndergradKB.RepresentationTheory.Roots
import UndergradKB.RepresentationTheory.Categories
import UndergradKB.RepresentationTheory.CategoriesMore
import UndergradKB.RepresentationTheory.DehnInvariant
import UndergradKB.RepresentationTheory.DehnPolyhedra
import UndergradKB.RepresentationTheory.DehnSolids
import UndergradKB.RepresentationTheory.DehnCubeTetrahedron
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: definitions and problems formalized in wave 4

Course names for the book items whose supporting theorems were proved in this library in wave 4, tagged with the
source key `etingof2011` and the locator of the item.  Each is the repository theorem under the book's numbering
(an alias: same statement).
-/

namespace UndergradKB.RepresentationTheory.Course

open UndergradKB.RepresentationTheory

/-- Etingof et al., Definition 1.15: an irreducible representation is indecomposable. -/
@[kb "etingof2011" "Definition 1.15, p. 8"]
alias etingof_1_15_a := IsIndecomposable.of_isIrreducible

/-- Etingof et al., Definition 1.15: when the group order is invertible in the field, indecomposable
representations are irreducible. -/
@[kb "etingof2011" "Definition 1.15, p. 8"]
alias etingof_1_15_b := IsIndecomposable.isIrreducible

/-- Etingof et al., Definition 1.31: the product of two path elements in the path algebra is the concatenated path
when it exists, and zero otherwise. -/
@[kb "etingof2011" "Definition 1.31, p. 13"]
alias etingof_1_31_a := pathElem_mul

/-- Etingof et al., Definition 1.31: the identity of the path algebra is the sum of the trivial paths at the
vertices. -/
@[kb "etingof2011" "Definition 1.31, p. 13"]
alias etingof_1_31_b := pathElem_one

/-- Etingof et al., Definition 2.7: the action on the dual representation is `(a f)(v) = f(a' v)`, via the
antipode-twisted action. -/
@[kb "etingof2011" "Definition 2.7, p. 24"]
alias etingof_2_7 := dualRep_apply

/-- Etingof et al., Definition 2.9: an element lies in the radical iff it kills every simple module. -/
@[kb "etingof2011" "Definition 2.9, p. 26"]
alias etingof_2_9_a := mem_algebraRadical_iff

/-- Etingof et al., Definition 2.9: the radical of an algebra is its Jacobson radical. -/
@[kb "etingof2011" "Definition 2.9, p. 26"]
alias etingof_2_9_b := algebraRadical_eq_jacobson

/-- Etingof et al., Definition 4.3: the Frobenius-Schur indicator of an irreducible representation of real type
equals `1`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
alias etingof_4_3_a := fsIndicator_character_eq_one_of_isRealType

/-- Etingof et al., Definition 4.3: the Frobenius-Schur indicator of an irreducible representation of
quaternionic type equals `-1`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
alias etingof_4_3_b := fsIndicator_character_eq_neg_one_of_isQuaternionicType

/-- Etingof et al., Definition 4.3: the Frobenius-Schur indicator of an irreducible representation of complex
type equals `0`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
alias etingof_4_3_c := fsIndicator_character_eq_zero_of_isComplexType

/-- Etingof et al., Definition 4.6: the group determinant is a homogeneous polynomial of degree `|G|`. -/
@[kb "etingof2011" "Definition 4.6, p. 48"]
alias etingof_4_6 := groupDeterminant_isHomogeneous

/-- Etingof et al., Definition 4.10: a complex number is an algebraic integer iff it is an eigenvalue of an
integer matrix. -/
@[kb "etingof2011" "Definition 4.10, p. 49"]
alias etingof_4_10_a := isIntegral_int_iff_exists_matrix_hasEigenvalue

/-- Etingof et al., Definition 4.10: a complex number is algebraic iff it is an eigenvalue of a rational matrix. -/
@[kb "etingof2011" "Definition 4.10, p. 49"]
alias etingof_4_10_b := isAlgebraic_rat_iff_exists_matrix_hasEigenvalue

/-- Etingof et al., Definition 5.11: the Cartan matrix of the path graph on `n` vertices is the Cartan matrix
`A_n`. -/
@[kb "etingof2011" "Definition 5.11, p. 87"]
alias etingof_5_11 := Roots.cartanMatrix_pathGraph

/-- Etingof et al., Definition 5.13: for a positive definite form there are only finitely many roots. -/
@[kb "etingof2011" "Definition 5.13, p. 87"]
alias etingof_5_13 := Roots.roots_finite

/-- Etingof et al., Definition 5.15: each simple root is a root. -/
@[kb "etingof2011" "Definition 5.15, p. 87"]
alias etingof_5_15 := Roots.isRoot_simpleRoot

/-- Etingof et al., Definition 5.17: for a positive definite graph every root is positive or negative. -/
@[kb "etingof2011" "Definition 5.17, p. 88"]
alias etingof_5_17 := Roots.isRoot_pos_or_neg

/-- Etingof et al., Definition 5.20: the reflection in a root `α` sends `v` to `v - (v, α) α`. -/
@[kb "etingof2011" "Definition 5.20, p. 89"]
alias etingof_5_20 := Roots.reflect_apply

/-- Etingof et al., Definition 6.14: every small abelian category embeds fully faithfully and exactly in a module
category. -/
@[kb "etingof2011" "Definition 6.14, p. 103"]
alias etingof_6_14_a := abelian_embedding_modules

/-- Etingof et al., Definition 6.14: the embedding into a module category can be taken additive and exact. -/
@[kb "etingof2011" "Definition 6.14, p. 103"]
alias etingof_6_14_b := abelian_embedding_modules_exact

/-- Etingof et al., Definition 6.20: a functor is exact iff it preserves finite limits and finite colimits. -/
@[kb "etingof2011" "Definition 6.20, p. 104"]
alias etingof_6_20_a := isExactFunctor_iff

/-- Etingof et al., Definition 6.20: a functor is exact iff it is both left and right exact. -/
@[kb "etingof2011" "Definition 6.20, p. 104"]
alias etingof_6_20_b := isExactFunctor_iff_left_right

/-- Etingof et al., Problem 1.51: cutting a bounded polyhedron by a plane splits its Dehn invariant additively
(when the cutting plane contains no edge of the polyhedron). -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_b := polyDehn_cut

/-- Etingof et al., Problem 1.51: the Dehn invariant is unchanged by an isometry of space. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_c := polyDehn_move

/-- Etingof et al., Problem 1.51: scissors-congruent polyhedra have equal total Dehn invariant. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_d := totalDehn_eq_of_scissorsCongruent

/-- Etingof et al., Problem 1.51: the cell of the face list of a cube of side `a` is the box `[0,a]^3`. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_e := cell_cubeFaces

/-- Etingof et al., Problem 1.51: the Dehn invariant of a cube is zero. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_f := polyDehn_cube

/-- Etingof et al., Problem 1.51: the Dehn invariant of the regular tetrahedron is nonzero. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_g := polyDehn_tetrahedron_ne_zero

/-- Etingof et al., Problem 1.51: the dihedral angle of the regular tetrahedron, `arccos(1/3)`, is an irrational
multiple of `π`. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_h := arccos_one_third_div_pi_irrational

/-- Etingof et al., Problem 1.51: a cube and a regular tetrahedron are not scissors congruent. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_i := not_scissorsCongruent_cube_tetrahedron

end UndergradKB.RepresentationTheory.Course
