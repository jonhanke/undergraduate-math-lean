import UndergradKB.Topology.KroneckerWave2b
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import UndergradKB.Common.Attr

/-!
# Wave 2: compact Lie groups (Morris, Appendix 5.0, Definition A5.0.11)

A compact Lie group is a topological group topologically isomorphic to a closed subgroup of an orthogonal
group `O(n)`. Basic facts: `O(n)` is compact, so such a group is compact; closed subgroups, the circle and
finite groups are compact Lie groups.
-/

open Set Topology
open scoped Matrix

universe u

namespace UndergradKB.Topology

/-- Bridging definition for Morris, Definition A5.0.11 (TP-485): `G` is a compact Lie group if it is
topologically isomorphic to a closed subgroup of `O(n)` for some `n`; equivalently (see
`isCompactLieGroup_iff_exists_closedSubgroup`) there is a continuous homomorphism into `O(n)` which is a
closed embedding. -/
def IsCompactLieGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (n : ℕ) (f : G →* Matrix.orthogonalGroup (Fin n) ℝ), IsClosedEmbedding f

/-- Morris, Topology Without Tears, Definition A5.0.11 (TP-485): the two formulations of the definition
agree. -/
@[kb "morris2024" "Definition A5.0.11, p. 497"]
theorem isCompactLieGroup_iff_exists_closedSubgroup (G : Type*) [Group G] [TopologicalSpace G] :
    IsCompactLieGroup G ↔ ∃ (n : ℕ) (H : Subgroup (Matrix.orthogonalGroup (Fin n) ℝ)),
      IsClosed (H : Set (Matrix.orthogonalGroup (Fin n) ℝ)) ∧ Nonempty (G ≃ₜ* H) := by
  constructor
  · rintro ⟨n, f, hf⟩
    refine ⟨n, f.range, ?_, ⟨?_⟩⟩
    · exact hf.isClosed_range
    · let hh : G ≃ₜ f.range := hf.toIsEmbedding.toHomeomorph
      exact { toFun := hh
              invFun := hh.symm
              left_inv := hh.left_inv
              right_inv := hh.right_inv
              map_mul' := fun x y => Subtype.ext (map_mul f x y)
              continuous_toFun := hh.continuous
              continuous_invFun := hh.symm.continuous }
  · rintro ⟨n, H, hH, ⟨e⟩⟩
    refine ⟨n, H.subtype.comp e.toMulEquiv.toMonoidHom, ?_⟩
    exact (hH.isClosedEmbedding_subtypeVal).comp e.toHomeomorph.isClosedEmbedding

/-- A closed subgroup of a compact Lie group is a compact Lie group. -/
theorem IsCompactLieGroup.closedSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    (h : IsCompactLieGroup G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsCompactLieGroup H := by
  obtain ⟨n, f, hf⟩ := h
  exact ⟨n, f.comp H.subtype, hf.comp (hH.isClosedEmbedding_subtypeVal)⟩

/-- `O(n)` is compact. -/
theorem isCompact_orthogonalGroup (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) := by
  refine isCompact_univ_iff.1 ?_
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  let S : Set (Matrix (Fin n) (Fin n) ℝ) := Set.pi univ fun _ => Set.pi univ fun _ => Icc (-1) 1
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hcl : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A * Aᵀ = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have himg : Subtype.val '' (Set.univ : Set (Matrix.orthogonalGroup (Fin n) ℝ)) =
      {A : Matrix (Fin n) (Fin n) ℝ | A * Aᵀ = 1} := by
    ext A
    constructor
    · rintro ⟨B, -, rfl⟩; exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 B.2
    · intro hA; exact ⟨⟨A, (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).2 hA⟩, trivial, rfl⟩
  rw [himg]
  refine (hS.inter_right hcl).of_isClosed_subset hcl ?_
  intro A hA
  refine ⟨fun i _ j _ => ?_, hA⟩
  have h1 : (A * Aᵀ) i i = 1 := by rw [hA]; simp
  have h2 : (A * Aᵀ) i i = ∑ k, A i k ^ 2 := by simp [Matrix.mul_apply, sq]
  have h3 : A i j ^ 2 ≤ 1 := by
    rw [h2] at h1
    calc A i j ^ 2 ≤ ∑ k, A i k ^ 2 :=
          Finset.single_le_sum (f := fun k => A i k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ = 1 := h1
  constructor <;> nlinarith [sq_nonneg (A i j + 1), sq_nonneg (A i j - 1)]

/-- A compact Lie group is compact (it is a closed subgroup of the compact group `O(n)`). -/
theorem IsCompactLieGroup.compactSpace {G : Type*} [Group G] [TopologicalSpace G]
    (h : IsCompactLieGroup G) : CompactSpace G := by
  obtain ⟨n, f, hf⟩ := h
  haveI := isCompact_orthogonalGroup n
  exact hf.compactSpace

/-- The circle group is a compact Lie group (it is `SO(2) ⊆ O(2)`). -/
theorem isCompactLieGroup_circle : IsCompactLieGroup Circle := by
  let i : Matrix.specialOrthogonalGroup (Fin 2) ℝ →* Matrix.orthogonalGroup (Fin 2) ℝ :=
    { toFun := fun x => ⟨x.1, (Matrix.mem_specialOrthogonalGroup_iff.1 x.2).1⟩
      map_one' := rfl
      map_mul' := fun x y => rfl }
  have hi : Continuous i := Continuous.subtype_mk continuous_subtype_val _
  have hc : Continuous (i.comp circleToSO2) := hi.comp continuous_circleToSO2
  have hinj : Function.Injective (i.comp circleToSO2) := by
    intro z w h
    apply circleToSO2_injective
    exact Subtype.ext (congrArg (fun x : Matrix.orthogonalGroup (Fin 2) ℝ => x.1) h)
  exact ⟨2, i.comp circleToSO2, hc.isClosedEmbedding hinj⟩

theorem permMatrix_injective {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : σ.permMatrix ℝ = τ.permMatrix ℝ) : σ = τ := by
  refine Equiv.ext fun i => ?_
  have := congrFun (congrFun h i) (σ i)
  by_contra hne
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply] at this
  exact hne (by simpa using this.symm)

/-- A finite group with the discrete topology is a compact Lie group (via its permutation
representation on itself). -/
theorem isCompactLieGroup_of_finite (G : Type*) [Group G] [Finite G] [TopologicalSpace G]
    [DiscreteTopology G] : IsCompactLieGroup G := by
  classical
  let n := Nat.card G
  let e : G ≃ Fin n := Finite.equivFin G
  let P : G →* Equiv.Perm (Fin n) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G G)
  let M : G →* Matrix (Fin n) (Fin n) ℝ := (Matrix.permMatrixHom : Equiv.Perm (Fin n) →* Matrix (Fin n) (Fin n) ℝ).comp P
  have hperm : ∀ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ * (σ.permMatrix ℝ)ᵀ = 1 := by
    intro σ
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  have hM : ∀ g, M g ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    intro g
    rw [Matrix.mem_orthogonalGroup_iff]
    exact hperm (P g)⁻¹
  let f : G →* Matrix.orthogonalGroup (Fin n) ℝ :=
    { toFun := fun g => ⟨M g, hM g⟩
      map_one' := Subtype.ext (map_one M)
      map_mul' := fun a b => Subtype.ext (map_mul M a b) }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : M a = M b := congrArg (fun x : Matrix.orthogonalGroup (Fin n) ℝ => x.1) hab
    have h2 : (P a)⁻¹ = (P b)⁻¹ := by
      have h1' : ((P a)⁻¹).permMatrix ℝ = ((P b)⁻¹).permMatrix ℝ := h1
      exact permMatrix_injective h1'
    have h3 : (MulAction.toPermHom G G) a = (MulAction.toPermHom G G) b :=
      (Equiv.permCongrHom e).injective (inv_injective h2)
    have h4 := congrArg (fun σ : Equiv.Perm G => σ 1) h3
    simpa using h4
  have hcont : Continuous f := continuous_of_discreteTopology
  haveI : CompactSpace G := Finite.compactSpace
  exact ⟨n, f, hcont.isClosedEmbedding hinj⟩

/-- Block-diagonal embedding `O(n) × O(m) → O(n + m)`. -/
noncomputable def blockDiagOrthogonal (n m : ℕ) :
    (Matrix.orthogonalGroup (Fin n) ℝ × Matrix.orthogonalGroup (Fin m) ℝ) →*
      Matrix.orthogonalGroup (Fin (n + m)) ℝ where
  toFun p := ⟨(Matrix.fromBlocks p.1.1 0 0 p.2.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm, by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    have h1 := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 p.1.2
    have h2 := (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 p.2.2
    simp [h1, h2, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]⟩
  map_one' := by
    apply Subtype.ext
    simp [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  map_mul' p q := by
    apply Subtype.ext
    show (Matrix.fromBlocks (p.1.1 * q.1.1) 0 0 (p.2.1 * q.2.1)).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm =
      (Matrix.fromBlocks p.1.1 0 0 p.2.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      (Matrix.fromBlocks q.1.1 0 0 q.2.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem continuous_blockDiagOrthogonal (n m : ℕ) : Continuous (blockDiagOrthogonal n m) := by
  refine Continuous.subtype_mk ?_ _
  refine Continuous.matrix_submatrix ?_ _ _
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const ?_
  · exact continuous_subtype_val.comp continuous_fst
  · exact continuous_subtype_val.comp continuous_snd

theorem injective_blockDiagOrthogonal (n m : ℕ) : Function.Injective (blockDiagOrthogonal n m) := by
  intro p q h
  have h1 := congrArg (fun x : Matrix.orthogonalGroup (Fin (n + m)) ℝ => x.1) h
  simp only [blockDiagOrthogonal, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  have h2 : Matrix.fromBlocks p.1.1 0 0 p.2.1 = Matrix.fromBlocks q.1.1 0 0 q.2.1 := by
    ext i j
    have := congrFun (congrFun h1 (finSumFinEquiv i)) (finSumFinEquiv j)
    simpa using this
  obtain ⟨hA, -, -, hB⟩ := Matrix.fromBlocks_inj.1 h2
  exact Prod.ext (Subtype.ext hA) (Subtype.ext hB)

/-- Finite products of compact Lie groups are compact Lie groups (block-diagonal embedding
`O(n) × O(m) ⊆ O(n + m)`). -/
theorem IsCompactLieGroup.prod {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] (hG : IsCompactLieGroup G) (hH : IsCompactLieGroup H) :
    IsCompactLieGroup (G × H) := by
  obtain ⟨n, f, hf⟩ := hG
  obtain ⟨m, g, hg⟩ := hH
  haveI := isCompact_orthogonalGroup n
  haveI := isCompact_orthogonalGroup m
  have hb : IsClosedEmbedding (blockDiagOrthogonal n m) :=
    (continuous_blockDiagOrthogonal n m).isClosedEmbedding (injective_blockDiagOrthogonal n m)
  exact ⟨n + m, (blockDiagOrthogonal n m).comp (f.prodMap g), hb.comp (hf.prodMap hg)⟩

end UndergradKB.Topology
