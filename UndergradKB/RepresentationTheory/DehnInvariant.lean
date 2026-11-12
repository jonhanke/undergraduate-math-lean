import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import UndergradKB.Common.Attr

/-! # The Dehn invariant of the cube and the regular tetrahedron (Etingof et al., Problem 1.51)

The Dehn invariant of a polyhedron with edges of lengths `l_i` and dihedral angles `θ_i` is the element
`Σ l_i ⊗ (θ_i / π)` of `ℝ ⊗_ℚ (ℝ/ℚ)`. Here the polyhedron is recorded only by its list of edges (length and
dihedral angle); the additivity under cutting, which needs a theory of polyhedra, is not formalized.

We compute: the cube has Dehn invariant zero (all dihedral angles are `π/2`), while the regular tetrahedron with
edge `a ≠ 0` has nonzero Dehn invariant, because its dihedral angle `arccos (1/3)` is not a rational multiple of
`π` (by Niven's theorem in Mathlib). Hence the two invariants differ.
-/

namespace UndergradKB.RepresentationTheory

open Real TensorProduct

/-- The `ℚ`-subspace `ℚ ⊆ ℝ`. -/
noncomputable def ratSubspace : Submodule ℚ ℝ := Submodule.span ℚ {1}

/-- The target `ℝ ⊗_ℚ (ℝ/ℚ)` of the Dehn invariant. -/
abbrev DehnSpace : Type := ℝ ⊗[ℚ] (ℝ ⧸ ratSubspace)

/-- Dehn invariant of a polyhedron given by its edges, each with a length and a dihedral angle. -/
noncomputable def dehnInvariant (edges : List (ℝ × ℝ)) : DehnSpace :=
  (edges.map fun e => e.1 ⊗ₜ[ℚ] (ratSubspace.mkQ (e.2 / π))).sum

/-- The edges of a cube of side `a`: twelve edges, all with dihedral angle `π/2`. -/
noncomputable def cubeEdges (a : ℝ) : List (ℝ × ℝ) := List.replicate 12 (a, π / 2)

/-- The edges of a regular tetrahedron of side `a`: six edges, with dihedral angle `arccos (1/3)`. -/
noncomputable def tetrahedronEdges (a : ℝ) : List (ℝ × ℝ) := List.replicate 6 (a, arccos (1 / 3))

lemma mkQ_rat (q : ℚ) : ratSubspace.mkQ ((q : ℝ)) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have : (q : ℝ) = q • (1 : ℝ) := by simp [Rat.smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/-- The Dehn invariant of a cube is zero. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem dehnInvariant_cube (a : ℝ) : dehnInvariant (cubeEdges a) = 0 := by
  have h : ratSubspace.mkQ (π / 2 / π) = 0 := by
    rw [show π / 2 / π = ((1 / 2 : ℚ) : ℝ) by field_simp [pi_ne_zero]; push_cast; ring]
    exact mkQ_rat _
  simp only [dehnInvariant, cubeEdges, List.map_replicate, h, tmul_zero, List.sum_replicate, smul_zero]

/-- The dihedral angle `arccos (1/3)` of the regular tetrahedron is not a rational multiple of `π`. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem arccos_one_third_div_pi_irrational : Irrational (arccos (1 / 3) / π) := by
  rintro ⟨r, hr⟩
  have hθ : arccos (1 / 3) = r * π := by
    rw [hr]; field_simp [pi_ne_zero]
  have hc : cos (arccos (1 / 3)) = 1 / 3 := cos_arccos (by norm_num) (by norm_num)
  have := niven (θ := arccos (1 / 3)) ⟨r, hθ⟩ ⟨1 / 3, by rw [hc]; norm_num⟩
  rw [hc] at this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with h | h | h | h | h <;> norm_num at h

lemma mkQ_ne_zero_of_irrational {x : ℝ} (hx : Irrational x) : ratSubspace.mkQ x ≠ 0 := by
  rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
  intro h
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.1 h
  exact hx ⟨q, by rw [← hq]; simp [Rat.smul_def]⟩

/-- The Dehn invariant of a regular tetrahedron with nonzero side is nonzero, so it differs from that of any
cube: the two cannot be cut into pairwise congruent pieces (granting the additivity of the invariant). -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem dehnInvariant_tetrahedron_ne_zero {a : ℝ} (ha : a ≠ 0) : dehnInvariant (tetrahedronEdges a) ≠ 0 := by
  simp only [dehnInvariant, tetrahedronEdges, List.map_replicate, List.sum_replicate]
  intro h
  have h6 : ((6 : ℕ) • a) ⊗ₜ[ℚ] ratSubspace.mkQ (arccos (1 / 3) / π) = 0 := by
    rw [← TensorProduct.smul_tmul']; exact h
  have h6a : (6 : ℕ) • a ≠ 0 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, ne_eq, mul_eq_zero, not_or]; exact ⟨by norm_num, ha⟩
  obtain ⟨φ, hφ⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℚ _).1 h6a)
  have := congrArg (fun t => TensorProduct.lid ℚ _ (TensorProduct.map φ LinearMap.id t)) h6
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, LinearMap.id_apply, map_zero] at this
  exact mkQ_ne_zero_of_irrational arccos_one_third_div_pi_irrational ((smul_eq_zero.1 this).resolve_left hφ)

/-- The cube and the regular tetrahedron (any nonzero sides) have different Dehn invariants. -/
@[kb "etingof2011" "Problem 1.51, p. 19"]
theorem dehnInvariant_cube_ne_tetrahedron (a b : ℝ) (hb : b ≠ 0) :
    dehnInvariant (cubeEdges a) ≠ dehnInvariant (tetrahedronEdges b) := by
  rw [dehnInvariant_cube]
  exact (dehnInvariant_tetrahedron_ne_zero hb).symm

end UndergradKB.RepresentationTheory
