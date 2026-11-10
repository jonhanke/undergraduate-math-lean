import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.UnitaryGroup
import UndergradKB.Common.Attr

/-! # Adjoint rules, isometries, unitary operators and matrices (Axler 7.5, 7.49, 7.53, 7.57)

`𝕜` is `ℝ` or `ℂ` (any `RCLike` field); all spaces are finite-dimensional inner product spaces.
Mathlib's inner product is conjugate-linear in the first slot (Axler: second).  Columns of a matrix are
identified with vectors of `EuclideanSpace 𝕜 (Fin m)`.
-/

open scoped InnerProductSpace ComplexConjugate Matrix
open Module

namespace UndergradKB.LinearAlgebra

section Adjoint

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- Axler 7.5: the adjoint is additive, conjugate-homogeneous, involutive, reverses products, fixes the
identity, and the adjoint of an invertible map is invertible with inverse the adjoint of the inverse. -/
@[kb "axler2024" "7.5, p. 248"]
theorem axler_7_5 :
    (∀ S T : E →ₗ[𝕜] F, LinearMap.adjoint (S + T) = LinearMap.adjoint S + LinearMap.adjoint T) ∧
    (∀ (c : 𝕜) (T : E →ₗ[𝕜] F), LinearMap.adjoint (c • T) = conj c • LinearMap.adjoint T) ∧
    (∀ T : E →ₗ[𝕜] F, LinearMap.adjoint (LinearMap.adjoint T) = T) ∧
    (∀ (T : E →ₗ[𝕜] F) (S : F →ₗ[𝕜] G),
      LinearMap.adjoint (S ∘ₗ T) = LinearMap.adjoint T ∘ₗ LinearMap.adjoint S) ∧
    LinearMap.adjoint (LinearMap.id : E →ₗ[𝕜] E) = LinearMap.id ∧
    (∀ (T : E →ₗ[𝕜] F) (S : F →ₗ[𝕜] E), S ∘ₗ T = LinearMap.id → T ∘ₗ S = LinearMap.id →
      LinearMap.adjoint S ∘ₗ LinearMap.adjoint T = LinearMap.id ∧
      LinearMap.adjoint T ∘ₗ LinearMap.adjoint S = LinearMap.id) := by
  refine ⟨fun S T => map_add _ S T, fun c T => map_smulₛₗ _ c T, LinearMap.adjoint_adjoint,
    fun T S => LinearMap.adjoint_comp S T, LinearMap.adjoint_id, fun T S h1 h2 => ?_⟩
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.adjoint_comp, h2, LinearMap.adjoint_id]
  · rw [← LinearMap.adjoint_comp, h1, LinearMap.adjoint_id]

end Adjoint

section Isometry

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

lemma adjoint_comp_self_eq_id_iff (S : E →ₗ[𝕜] F) :
    LinearMap.adjoint S ∘ₗ S = LinearMap.id ↔ ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜 := by
  constructor
  · intro h u v
    rw [← LinearMap.adjoint_inner_left]
    have := LinearMap.congr_fun h u
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this]
  · intro h
    ext u
    refine ext_inner_left 𝕜 fun w => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [LinearMap.adjoint_inner_right, h]

lemma norm_map_iff_adjoint_comp_self (S : E →ₗ[𝕜] F) :
    (∀ v, ‖S v‖ = ‖v‖) ↔ LinearMap.adjoint S ∘ₗ S = LinearMap.id :=
  (LinearMap.norm_map_iff_inner_map_map S).trans (adjoint_comp_self_eq_id_iff S).symm

/-- The columns of a matrix, viewed as vectors of Euclidean space, are orthonormal iff `Mᴴ * M = 1`. -/
lemma orthonormal_cols_iff {m n : ℕ} (M : Matrix (Fin m) (Fin n) 𝕜) :
    Orthonormal 𝕜 (fun k : Fin n => (WithLp.toLp 2 (fun j => M j k) : EuclideanSpace 𝕜 (Fin m))) ↔
      Mᴴ * M = 1 := by
  have key : ∀ k r, ⟪(WithLp.toLp 2 (fun j => M j k) : EuclideanSpace 𝕜 (Fin m)),
      WithLp.toLp 2 (fun j => M j r)⟫_𝕜 = (Mᴴ * M) k r := by
    intro k r
    simp [EuclideanSpace.inner_toLp_toLp, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      mul_comm]
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    ext k r
    rw [← key, h k r, Matrix.one_apply]
  · intro h k r
    rw [key, h, Matrix.one_apply]

/-- The rows of a square matrix, viewed as vectors of Euclidean space, are orthonormal iff `M * Mᴴ = 1`. -/
lemma orthonormal_rows_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) :
    Orthonormal 𝕜 (fun i : Fin n => (WithLp.toLp 2 (M i) : EuclideanSpace 𝕜 (Fin n))) ↔
      M * Mᴴ = 1 := by
  have key : ∀ i k, ⟪(WithLp.toLp 2 (M i) : EuclideanSpace 𝕜 (Fin n)), WithLp.toLp 2 (M k)⟫_𝕜 =
      (M * Mᴴ) k i := by
    intro i k
    simp [EuclideanSpace.inner_toLp_toLp, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      mul_comm]
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    ext k i
    rw [← key, h i k, Matrix.one_apply]
    simp [eq_comm]
  · intro h i k
    rw [key, h, Matrix.one_apply]
    simp [eq_comm]

/-- Axler 7.49: characterizations of isometries `S : V → W` with respect to orthonormal bases `e` of `V`
and `f` of `W`: `S` preserves norms; `S* S = I`; `S` preserves inner products; `S e_i` is orthonormal;
the columns of the matrix of `S` are orthonormal in `𝕜^m`. -/
@[kb "axler2024" "7.49, p. 277"]
theorem axler_7_49 {n m : ℕ} (S : E →ₗ[𝕜] F) (e : OrthonormalBasis (Fin n) 𝕜 E)
    (f : OrthonormalBasis (Fin m) 𝕜 F) : List.TFAE [
      ∀ v, ‖S v‖ = ‖v‖,
      LinearMap.adjoint S ∘ₗ S = LinearMap.id,
      ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜,
      Orthonormal 𝕜 (fun i => S (e i)),
      Orthonormal 𝕜 (fun k : Fin n =>
        (WithLp.toLp 2 (fun j => LinearMap.toMatrix e.toBasis f.toBasis S j k) :
          EuclideanSpace 𝕜 (Fin m)))] := by
  tfae_have 1 ↔ 2 := norm_map_iff_adjoint_comp_self S
  tfae_have 2 ↔ 3 := adjoint_comp_self_eq_id_iff S
  tfae_have 3 → 4 := by
    intro h
    rw [orthonormal_iff_ite]
    intro i j
    rw [h, orthonormal_iff_ite.1 e.orthonormal]
  tfae_have 4 → 1 := by
    intro h v
    exact (S.isometryOfOrthonormal (v := e.toBasis) (by simpa using e.orthonormal)
      (by exact h)).norm_map v
  tfae_have 4 ↔ 5 := by
    have hcol : (fun k : Fin n => (WithLp.toLp 2 (fun j => LinearMap.toMatrix e.toBasis f.toBasis S j k) :
        EuclideanSpace 𝕜 (Fin m))) = f.repr.toLinearIsometry ∘ (fun i => S (e i)) := by
      funext k
      ext j
      simp [LinearMap.toMatrix_apply]
    rw [hcol, LinearIsometry.orthonormal_comp_iff]
  tfae_finish

end Isometry

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- An orthonormal family with as many members as the dimension is an orthonormal basis. -/
lemma exists_onb_of_orthonormal {ι : Type*} [Fintype ι] (g : ι → E) (hon : Orthonormal 𝕜 g)
    (h : Fintype.card ι = finrank 𝕜 E) : ∃ b : OrthonormalBasis ι 𝕜 E, ∀ i, b i = g i :=
  ⟨OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank' h).ge,
    fun i => by simp⟩

lemma isUnit_of_mul_eq_one_both {M : Type*} [Monoid M] {a b : M} (h1 : a * b = 1) (h2 : b * a = 1) :
    IsUnit a :=
  ⟨⟨a, b, h1, h2⟩, rfl⟩

/-- Axler 7.53: characterizations of unitary operators `S` on `V`, for an orthonormal basis `e`:
unitary (an invertible isometry); `S* S = S S* = I`; invertible with inverse `S*`; `S e_i` is an
orthonormal basis; the rows of the matrix of `S` form an orthonormal basis of `𝕜^n`; `S*` is unitary. -/
@[kb "axler2024" "7.53, p. 279"]
theorem axler_7_53 {n : ℕ} (S : E →ₗ[𝕜] E) (e : OrthonormalBasis (Fin n) 𝕜 E) : List.TFAE [
    IsUnit S ∧ ∀ v, ‖S v‖ = ‖v‖,
    LinearMap.adjoint S * S = 1 ∧ S * LinearMap.adjoint S = 1,
    ∃ T : E →ₗ[𝕜] E, T * S = 1 ∧ S * T = 1 ∧ T = LinearMap.adjoint S,
    ∃ g : OrthonormalBasis (Fin n) 𝕜 E, ∀ i, g i = S (e i),
    ∃ r : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)), ∀ i,
      r i = WithLp.toLp 2 (LinearMap.toMatrix e.toBasis e.toBasis S i),
    IsUnit (LinearMap.adjoint S) ∧ ∀ v, ‖LinearMap.adjoint S v‖ = ‖v‖] := by
  have hcard : Fintype.card (Fin n) = finrank 𝕜 E := by
    simpa using (finrank_eq_card_basis e.toBasis).symm
  -- matrix form of `S * S* = 1`
  have hmat : S * LinearMap.adjoint S = 1 ↔
      LinearMap.toMatrix e.toBasis e.toBasis S * (LinearMap.toMatrix e.toBasis e.toBasis S)ᴴ = 1 := by
    rw [← LinearMap.toMatrix_adjoint e e S, ← LinearMap.toMatrix_mul,
      ← LinearMap.toMatrix_one e.toBasis]
    exact ((LinearMap.toMatrix e.toBasis e.toBasis).injective.eq_iff).symm
  have iso_iff : ∀ A : E →ₗ[𝕜] E, (∀ v, ‖A v‖ = ‖v‖) ↔ LinearMap.adjoint A * A = 1 := fun A =>
    norm_map_iff_adjoint_comp_self A
  tfae_have 1 → 2 := by
    rintro ⟨-, hn⟩
    have h1 := (iso_iff S).1 hn
    exact ⟨h1, mul_eq_one_comm.1 h1⟩
  tfae_have 2 → 3 := fun h => ⟨LinearMap.adjoint S, h.1, h.2, rfl⟩
  tfae_have 3 → 4 := by
    rintro ⟨T, h1, -, rfl⟩
    have hon : Orthonormal 𝕜 (fun i => S (e i)) :=
      ((axler_7_49 S e e).out 1 4).1 ((iso_iff S).2 h1)
    obtain ⟨g, hg⟩ := exists_onb_of_orthonormal _ hon hcard
    exact ⟨g, hg⟩
  tfae_have 4 → 5 := by
    rintro ⟨g, hg⟩
    have hon : Orthonormal 𝕜 (fun i => S (e i)) := by
      have : (fun i => S (e i)) = g := funext fun i => (hg i).symm
      rw [this]; exact g.orthonormal
    have h1 := (iso_iff S).1 (((axler_7_49 S e e).out 4 1).1 hon)
    have h2 := (hmat.1 (mul_eq_one_comm.1 h1))
    have hrow := (orthonormal_rows_iff _).2 h2
    exact exists_onb_of_orthonormal _ hrow (by simp)
  tfae_have 5 → 6 := by
    rintro ⟨r, hr⟩
    have hon : Orthonormal 𝕜 (fun i : Fin n => (WithLp.toLp 2
        (LinearMap.toMatrix e.toBasis e.toBasis S i) : EuclideanSpace 𝕜 (Fin n))) := by
      have : (fun i : Fin n => (WithLp.toLp 2
          (LinearMap.toMatrix e.toBasis e.toBasis S i) : EuclideanSpace 𝕜 (Fin n))) = r :=
        funext fun i => (hr i).symm
      rw [this]; exact r.orthonormal
    have h2 : S * LinearMap.adjoint S = 1 := hmat.2 ((orthonormal_rows_iff _).1 hon)
    refine ⟨isUnit_of_mul_eq_one_both (mul_eq_one_comm.1 h2) h2, ?_⟩
    rw [iso_iff, LinearMap.adjoint_adjoint]
    exact h2
  tfae_have 6 → 1 := by
    rintro ⟨-, hn⟩
    rw [iso_iff, LinearMap.adjoint_adjoint] at hn
    have h1 : LinearMap.adjoint S * S = 1 := mul_eq_one_comm.1 hn
    exact ⟨isUnit_of_mul_eq_one_both hn h1, (iso_iff S).2 h1⟩
  tfae_finish

end Unitary

section UnitaryMatrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Axler 7.57: for a square matrix `Q`: columns orthonormal (Axler's definition of unitary matrix);
rows orthonormal; `Q` preserves the Euclidean norm; `Q* Q = Q Q* = I`; `Q` lies in Mathlib's unitary
group; the conjugate transpose has orthonormal columns (is unitary). -/
@[kb "axler2024" "7.57, p. 281"]
theorem axler_7_57 {n : ℕ} (Q : Matrix (Fin n) (Fin n) 𝕜) : List.TFAE [
    Orthonormal 𝕜 (fun k : Fin n => (WithLp.toLp 2 (fun j => Q j k) : EuclideanSpace 𝕜 (Fin n))),
    Orthonormal 𝕜 (fun i : Fin n => (WithLp.toLp 2 (Q i) : EuclideanSpace 𝕜 (Fin n))),
    ∀ v : EuclideanSpace 𝕜 (Fin n), ‖(WithLp.toLp 2 (Q.mulVec v.ofLp) : EuclideanSpace 𝕜 (Fin n))‖ = ‖v‖,
    Qᴴ * Q = 1 ∧ Q * Qᴴ = 1,
    Q ∈ Matrix.unitaryGroup (Fin n) 𝕜,
    Orthonormal 𝕜 (fun k : Fin n => (WithLp.toLp 2 (fun j => Qᴴ j k) : EuclideanSpace 𝕜 (Fin n)))] := by
  tfae_have 1 ↔ 4 := by
    rw [orthonormal_cols_iff]
    exact ⟨fun h => ⟨h, mul_eq_one_comm.1 h⟩, fun h => h.1⟩
  tfae_have 2 ↔ 4 := by
    rw [orthonormal_rows_iff]
    exact ⟨fun h => ⟨mul_eq_one_comm.1 h, h⟩, fun h => h.2⟩
  tfae_have 5 ↔ 2 := by
    rw [Matrix.mem_unitaryGroup_iff, orthonormal_rows_iff]
    rfl
  tfae_have 6 ↔ 2 := by
    rw [orthonormal_cols_iff, Matrix.conjTranspose_conjTranspose, orthonormal_rows_iff]
  tfae_have 3 ↔ 1 := by
    have h := (axler_7_49 (Matrix.toEuclideanLin Q) (EuclideanSpace.basisFun (Fin n) 𝕜)
      (EuclideanSpace.basisFun (Fin n) 𝕜)).out 1 5
    have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis
        (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis (Matrix.toEuclideanLin Q) = Q := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
    rw [hM] at h
    rw [← h]
    exact forall_congr' fun v => by rfl
  tfae_finish

end UnitaryMatrix

section OrthogonalBasis

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Hefferon's definition of an orthogonal basis: a basis whose vectors are mutually orthogonal
(Mathlib has only the normalized notion `OrthonormalBasis`). -/
@[kb "hefferon2020" "Three.VI.2.5, p. 291"]
def IsOrthogonalBasis {ι : Type*} (b : Basis ι 𝕜 E) : Prop :=
  Pairwise fun i j => ⟪b i, b j⟫_𝕜 = 0

/-- Normalizing the vectors of an orthogonal basis gives an orthonormal basis. -/
theorem IsOrthogonalBasis.exists_orthonormalBasis {ι : Type*} [Fintype ι] {b : Basis ι 𝕜 E}
    (hb : IsOrthogonalBasis b) :
    ∃ c : OrthonormalBasis ι 𝕜 E, ∀ i, c i = ((‖b i‖ : 𝕜)⁻¹) • b i := by
  classical
  have hon : Orthonormal 𝕜 (fun i => ((‖b i‖ : 𝕜)⁻¹) • b i) := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      have : b i ≠ 0 := b.ne_zero i
      have hn : ‖((‖b i‖ : 𝕜)⁻¹) • b i‖ = 1 := norm_smul_inv_norm this
      rw [inner_self_eq_norm_sq_to_K, hn]
      simp
    · simp [inner_smul_left, inner_smul_right, hb hij, hij]
  exact exists_onb_of_orthonormal _ hon (by simpa using (finrank_eq_card_basis b).symm)

end OrthogonalBasis

end UndergradKB.LinearAlgebra
