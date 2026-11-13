import UndergradKB.RepresentationTheory.ProblemsAlgebrasLie
import UndergradKB.RepresentationTheory.ProblemsGroups
import UndergradKB.RepresentationTheory.ProblemsMisc
import UndergradKB.RepresentationTheory.ProblemsFiniteGroups
import UndergradKB.RepresentationTheory.DehnMoves
import UndergradKB.RepresentationTheory.ProblemsGL
import UndergradKB.RepresentationTheory.ProblemsGL2
import UndergradKB.RepresentationTheory.ProblemsQuiversSym
import UndergradKB.RepresentationTheory.ProblemsQuiversSym2
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: problems formalized in wave 3

Course names for the book problems proved in this library in wave 3, tagged with the source key `etingof2011` and the
locator of the problem.  Each is the repository theorem under the book's numbering (an alias: same statement).
-/

namespace UndergradKB.RepresentationTheory.Course

open UndergradKB.RepresentationTheory

/-- Etingof et al., Problem 1.24: `k[x_1, …, x_n] / I` is indecomposable when `I` contains all homogeneous
polynomials of large degree. -/
@[kb "etingof2011" "Problem 1.24, p. 11"]
alias etingof_1_24 := quotient_mvPolynomial_indecomposable

/-- Etingof et al., Problem 1.26 (a): the Weyl algebra in characteristic zero has no nonzero finite-dimensional
representations. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
alias etingof_1_26_a := weyl_no_finite_rep

/-- Etingof et al., Problem 1.27 (b): a nonzero finite-dimensional representation of the q-Weyl algebra forces `q`
to be a root of unity. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
alias etingof_1_27_b := qweyl_finite_rep

/-- Etingof et al., Problem 1.27 (b), converse: for `q` a root of unity there is a finite-dimensional
representation. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
alias etingof_1_27_b' := qweyl_exists_finite_rep

/-- Etingof et al., Problem 1.51 (a), algebraic part: the Dehn invariant is unchanged by the local moves of a cut. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
alias etingof_1_51_a := dehnInvariant_eq_of_dehnMove

/-- Etingof et al., Problem 1.54: `Hom_g(V ⊗ W, U) ≅ Hom_g(V, U ⊗ W^*)`. -/
@[kb "etingof2011" "Problem 1.54, p. 20"]
alias etingof_1_54 := lieTensorHomEquiv

/-- Etingof et al., Problem 1.57 (characteristic zero): irreducible representations of the two-dimensional
non-abelian Lie algebra are one-dimensional with `Y` acting by zero. -/
@[kb "etingof2011" "Problem 1.57, p. 22"]
alias etingof_1_57 := aff1_irrep_dim_one

/-- Etingof et al., Problem 3.4: irreducible representations of a `p`-group in characteristic `p` are trivial. -/
@[kb "etingof2011" "Problem 3.4, p. 34"]
alias etingof_3_4 := irreducible_pgroup_trivial

/-- Etingof et al., Problem 3.17 (a), `N` odd: the irreducible characters of the dihedral group. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
alias etingof_3_17 := irrChars_dihedral_odd

/-- Etingof et al., Problem 3.17 (a), `N` even: the irreducible characters of the dihedral group. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
alias etingof_3_17' := irrChars_dihedral_even

/-- Etingof et al., Problem 3.18: the representation `R_z` of the Heisenberg group is irreducible iff `z ≠ 1`. -/
@[kb "etingof2011" "Problem 3.18, p. 43"]
alias etingof_3_18 := Heis.isIrreducible_heisRep_iff

/-- Etingof et al., Problem 3.18: the irreducible characters of the Heisenberg group over `F_p`. -/
@[kb "etingof2011" "Problem 3.18, p. 43"]
alias etingof_3_18' := Heis.irrChars_heis

/-- Etingof et al., Problem 3.20: a graph with non-commuting automorphisms has an adjacency matrix with a repeated
eigenvalue. -/
@[kb "etingof2011" "Problem 3.20, p. 43"]
alias etingof_3_20 := adjMatrix_charpoly_roots_not_nodup

/-- Etingof et al., Problem 3.22: the irreducible characters of the group of maps `x ↦ a x + b` over `F_q`. -/
@[kb "etingof2011" "Problem 3.22, p. 44"]
alias etingof_3_22 := AffGrp.irrChars_affine

/-- Etingof et al., Problem 3.26: every irreducible representation embeds in a tensor power of a faithful one. -/
@[kb "etingof2011" "Problem 3.26, p. 45"]
alias etingof_3_26 := exists_injective_intertwining_tensorPower

/-- Etingof et al., Problem 4.31: induction in stages. -/
@[kb "etingof2011" "Problem 4.31, p. 55"]
alias etingof_4_31 := indStages

/-- Etingof et al., Problem 4.39: the sum of the dimensions of the irreducible representations of `S_n` is the number
of involutions (elements with `g² = 1`). -/
@[kb "etingof2011" "Problem 4.39, p. 59"]
alias etingof_4_39 := sum_dim_irreps_perm

/-- Etingof et al., Problem 5.1: an injective `k`-algebra map `k[x_1..x_n] → k(y_1..y_m)` forces `n ≤ m`. -/
@[kb "etingof2011" "Problem 5.1, p. 78"]
alias etingof_5_1 := mvPolynomial_embedding_le

/-- Etingof et al., Problem 5.1: `k(x_1..x_n) ≅ k(y_1..y_m)` over `k` forces `m = n`. -/
@[kb "etingof2011" "Problem 5.1, p. 78"]
alias etingof_5_1' := fractionRing_mvPolynomial_equiv_card_eq

/-- Etingof et al., Problem 5.40 (a): the eight given vectors form a basis of the lattice `L`. -/
@[kb "etingof2011" "Problem 5.40, p. 97"]
alias etingof_5_40_a := e8Simple_isBasis

/-- Etingof et al., Problem 1.33: the path algebra is generated by the trivial paths and the arrows subject exactly to
the idempotent and source/target relations (universal property). -/
@[kb "etingof2011" "Problem 1.33, p. 13"]
alias etingof_1_33 := exists_unique_pathAlgebra_lift

/-- Etingof et al., Problem 1.33: the trivial paths and the arrows satisfy these relations. -/
@[kb "etingof2011" "Problem 1.33, p. 13"]
alias etingof_1_33' := pathRelations_pathAlgebra

/-- Etingof et al., Problem 2.23: for a finite quiver without oriented cycles the irreducible representations are the
simple representations `S_i`. -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
alias etingof_2_23 := QRep.isIrreducible_iff_exists_isSimpleAt

/-- Etingof et al., Problem 2.23: `dim Ext¹(S_i, S_j)` is the number of arrows `i → j`. -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
alias etingof_2_23' := QRep.finrank_qExt_simpleRep

/-- Etingof et al., Problem 3.17 (b): the character of `V ⊗ V` for the rotation representation of the dihedral group
is `1 + sgn + θ_2`. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
alias etingof_3_17_b := character_tprod_dihRep_one

/-- Etingof et al., Problem 3.19: the symmetric powers `S^n V` of `V = ℂ^N` are irreducible under `GL_N(ℂ)`. -/
@[kb "etingof2011" "Problem 3.19, p. 43"]
alias etingof_3_19_sym := isIrreducible_symRep

/-- Etingof et al., Problem 3.19: the exterior powers `Λ^m V` (`m ≤ N`) are irreducible under `GL_N(ℂ)`. -/
@[kb "etingof2011" "Problem 3.19, p. 43"]
alias etingof_3_19_ext := isIrreducible_extPowRep

/-- Etingof et al., Problem 3.25: the characters of the `p`-dimensional irreducible representations of the
Heisenberg group. -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
alias etingof_3_25 := Heis.repChar_psi_apply

/-- Etingof et al., Problem 3.25: the character of the tensor product of two `p`-dimensional irreducibles. -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
alias etingof_3_25' := Heis.character_tprod_rep_psi

/-- Etingof et al., Problem 4.68 (a): `ℂ[S_n] b_T a_T` is isomorphic to the Specht module `ℂ[S_n] a_T b_T`. -/
@[kb "etingof2011" "Problem 4.68, p. 68"]
alias etingof_4_68_a := span_colSum_mul_rowSum_linearEquiv

/-- Etingof et al., Problem 4.68 (b): `V_λ ⊗ sign ≅ V_{λ*}`. -/
@[kb "etingof2011" "Problem 4.68, p. 68"]
alias etingof_4_68_b := exists_linearEquiv_sign_twist

end UndergradKB.RepresentationTheory.Course
