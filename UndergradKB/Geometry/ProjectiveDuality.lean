import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import UndergradKB.Common.Attr

/-! # Duality in the projective plane (Petrunin, chapter 15G)

The book builds the projective plane by its space model (Section 15C, Observation 15.1): fixing a point `O`
of the Euclidean space `ℝ³` (the origin), the points of the projective plane correspond to the lines through
`O` (the set `Φ`) and its lines to the planes through `O` (the set `Ψ`), with incidence `P ∈ ℓ` corresponding
to containment of the line in the plane. We work directly in this model: points are 1-dimensional and lines
2-dimensional subspaces of `EuclideanSpace ℝ (Fin 3)`.

A *duality* (Petrunin, p. 127) is a bijection `P ↔ p` between points and lines with `P ∈ ℓ ⟺ p ∋ L` for every
point `P` and line `ℓ` (`L` the point corresponding to `ℓ`). Theorem 15.12: the projective plane admits one,
namely the orthogonal complement. -/

namespace UndergradKB.Geometry

open Module

/-- The Euclidean space `ℝ³` of the space model. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- Points of the projective plane in the space model: lines thru the origin of `ℝ³`. -/
def ProjPoint : Type := {W : Submodule ℝ Space3 // finrank ℝ W = 1}

/-- Lines of the projective plane in the space model: planes thru the origin of `ℝ³`. -/
def ProjLine : Type := {W : Submodule ℝ Space3 // finrank ℝ W = 2}

/-- Incidence: the point `P` lies on the line `ℓ` (the line of `P` is contained in the plane of `ℓ`). -/
def ProjPoint.LiesOn (P : ProjPoint) (ℓ : ProjLine) : Prop := P.1 ≤ ℓ.1

theorem finrank_orthogonal_space3 (W : Submodule ℝ Space3) : finrank ℝ Wᗮ = 3 - finrank ℝ W := by
  have h := W.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace, Fintype.card_fin] at h
  omega

/-- The duality of the projective plane: a point (line thru `O`) goes to the perpendicular plane, a line
(plane thru `O`) to the perpendicular line. -/
noncomputable def projDuality : ProjPoint ≃ ProjLine where
  toFun P := ⟨P.1ᗮ, by rw [finrank_orthogonal_space3, P.2]⟩
  invFun ℓ := ⟨ℓ.1ᗮ, by rw [finrank_orthogonal_space3, ℓ.2]⟩
  left_inv P := Subtype.ext (Submodule.orthogonal_orthogonal P.1)
  right_inv ℓ := Subtype.ext (Submodule.orthogonal_orthogonal ℓ.1)

/-- **The projective plane admits a duality** (Petrunin, Theorem 15.12): the bijection `projDuality` between
points and lines satisfies `P ∈ ℓ ⟺ p ∋ L`, where `p` is the line of `P` and `L` the point of `ℓ`. -/
@[kb "petrunin2025" "Theorem 15.12, p. 128"]
theorem projDuality_liesOn_iff (P : ProjPoint) (ℓ : ProjLine) :
    P.LiesOn ℓ ↔ (projDuality.symm ℓ).LiesOn (projDuality P) := by
  change P.1 ≤ ℓ.1 ↔ ℓ.1ᗮ ≤ P.1ᗮ
  exact Submodule.orthogonal_le_orthogonal_iff.symm

/-- Through two distinct points of the projective plane passes exactly one line (space model: two distinct
lines thru `O` span exactly one plane thru `O`). -/
theorem existsUnique_line_through {P Q : ProjPoint} (hPQ : P ≠ Q) :
    ∃! ℓ : ProjLine, P.LiesOn ℓ ∧ Q.LiesOn ℓ := by
  have hne : P.1 ≠ Q.1 := fun h => hPQ (Subtype.ext h)
  have hinf : P.1 ⊓ Q.1 = ⊥ := by
    -- two distinct 1-dimensional subspaces meet in `0`
    by_contra h
    have hle : finrank ℝ ↥(P.1 ⊓ Q.1) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : P.1 ⊓ Q.1 ≤ P.1)
      rwa [P.2] at this
    have hpos : finrank ℝ ↥(P.1 ⊓ Q.1) ≠ 0 := fun h0 => h (Submodule.finrank_eq_zero.mp h0)
    have h1 : finrank ℝ ↥(P.1 ⊓ Q.1) = 1 := by omega
    have eP : P.1 ⊓ Q.1 = P.1 := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, P.2])
    have eQ : P.1 ⊓ Q.1 = Q.1 := Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, Q.2])
    exact hne (eP.symm.trans eQ)
  have hsup : finrank ℝ ↥(P.1 ⊔ Q.1) = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq P.1 Q.1
    rw [hinf, finrank_bot, P.2, Q.2] at this
    omega
  refine ⟨⟨P.1 ⊔ Q.1, hsup⟩, ⟨le_sup_left, le_sup_right⟩, ?_⟩
  rintro ℓ ⟨hP, hQ⟩
  apply Subtype.ext
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le hP hQ) (by rw [hsup, ℓ.2])).symm

/-- Any two distinct lines of the projective plane meet in exactly one point (the dual statement, deduced
from `existsUnique_line_through` by the duality: in the projective plane there are no parallel lines). -/
@[kb "petrunin2025" "Section 15D, p. 123"]
theorem existsUnique_point_on {ℓ m : ProjLine} (hℓm : ℓ ≠ m) :
    ∃! P : ProjPoint, P.LiesOn ℓ ∧ P.LiesOn m := by
  have hne : projDuality.symm ℓ ≠ projDuality.symm m := fun h => hℓm (projDuality.symm.injective h)
  obtain ⟨n, ⟨h1, h2⟩, huniq⟩ := existsUnique_line_through hne
  refine ⟨projDuality.symm n, ⟨?_, ?_⟩, ?_⟩
  · rw [projDuality_liesOn_iff, Equiv.apply_symm_apply]; exact h1
  · rw [projDuality_liesOn_iff, Equiv.apply_symm_apply]; exact h2
  · intro P ⟨hP1, hP2⟩
    rw [projDuality_liesOn_iff] at hP1 hP2
    have := huniq (projDuality P) ⟨hP1, hP2⟩
    rw [← this, Equiv.symm_apply_apply]

end UndergradKB.Geometry
