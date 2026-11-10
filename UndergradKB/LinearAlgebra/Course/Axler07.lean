import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Normed.Module.FiniteDimension
import UndergradKB.Common.Attr

/-! # Axler, Chapter 7: operators on inner product spaces

Course-layer wrappers (thin theorems in the book's terms) for the rows of the linear-algebra checklist
classified `in Mathlib` that fall in Axler chapter 7. -/

open scoped InnerProductSpace ComplexOrder
open Module Matrix

namespace UndergradKB.LinearAlgebra.Course

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

/-! ## 7A Adjoints and self-adjoint operators -/

/-- Axler 7.1: the adjoint `T*` is characterised by `⟪T v, w⟫ = ⟪v, T* w⟫`. -/
@[kb "axler2024" "7.1, p. 246"]
theorem axler_7_1 [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) (v : E) (w : F) :
    ⟪T v, w⟫_𝕜 = ⟪v, LinearMap.adjoint T w⟫_𝕜 :=
  (LinearMap.adjoint_inner_right T v w).symm

/-- Axler 7.4: the adjoint of a linear map is linear. -/
@[kb "axler2024" "7.4, p. 247"]
theorem axler_7_4 [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) (w₁ w₂ : F) (c : 𝕜) :
    LinearMap.adjoint T (w₁ + w₂) = LinearMap.adjoint T w₁ + LinearMap.adjoint T w₂ ∧
      LinearMap.adjoint T (c • w₁) = c • LinearMap.adjoint T w₁ :=
  ⟨map_add _ _ _, map_smul _ _ _⟩

/-- Axler 7.6: null space and range of `T*` against those of `T`. -/
@[kb "axler2024" "7.6, p. 249"]
theorem axler_7_6 [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) :
    LinearMap.ker (LinearMap.adjoint T) = (LinearMap.range T)ᗮ ∧
    LinearMap.range (LinearMap.adjoint T) = (LinearMap.ker T)ᗮ ∧
    LinearMap.ker T = (LinearMap.range (LinearMap.adjoint T))ᗮ ∧
    LinearMap.range T = (LinearMap.ker (LinearMap.adjoint T))ᗮ := by
  refine ⟨(LinearMap.orthogonal_range T).symm, (LinearMap.orthogonal_ker T).symm, ?_, ?_⟩
  · simpa using (LinearMap.orthogonal_range (LinearMap.adjoint T)).symm
  · simpa using (LinearMap.orthogonal_ker (LinearMap.adjoint T)).symm

/-- Axler 7.7: the conjugate transpose has entries `star (A k j)` at position `(j, k)`. -/
@[kb "axler2024" "7.7, p. 249"]
theorem axler_7_7 {m n : Type*} (A : Matrix m n 𝕜) (j : n) (k : m) :
    A.conjTranspose j k = star (A k j) :=
  Matrix.conjTranspose_apply A k j

/-- Axler 7.9: in orthonormal bases the matrix of `T*` is the conjugate transpose of that of `T`. -/
@[kb "axler2024" "7.9, p. 250"]
theorem axler_7_9 {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (e : OrthonormalBasis n 𝕜 E) (f : OrthonormalBasis m 𝕜 F) (T : E →ₗ[𝕜] F) :
    LinearMap.toMatrix f.toBasis e.toBasis (LinearMap.adjoint T) =
      (LinearMap.toMatrix e.toBasis f.toBasis T).conjTranspose :=
  LinearMap.toMatrix_adjoint e f T

/-- Axler 7.10: `T` is self-adjoint (`T = T*`) iff `⟪T v, w⟫ = ⟪v, T w⟫` for all `v, w`. -/
@[kb "axler2024" "7.10, p. 251"]
theorem axler_7_10 [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    LinearMap.adjoint T = T ↔ ∀ v w, ⟪T v, w⟫_𝕜 = ⟪v, T w⟫_𝕜 := by
  rw [show (LinearMap.adjoint T = T) ↔ IsSelfAdjoint T from
    ⟨fun h => by rw [IsSelfAdjoint, LinearMap.star_eq_adjoint, h],
     fun h => by rwa [IsSelfAdjoint, LinearMap.star_eq_adjoint] at h⟩,
    ← LinearMap.isSymmetric_iff_isSelfAdjoint]
  rfl

/-- Axler 7.12: every eigenvalue of a self-adjoint operator is real. -/
@[kb "axler2024" "7.12, p. 251"]
theorem axler_7_12 [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) (hT : LinearMap.adjoint T = T) (μ : 𝕜)
    (hμ : Module.End.HasEigenvalue T μ) : ∃ r : ℝ, (r : 𝕜) = μ := by
  have hs : T.IsSymmetric := (axler_7_10 T).1 hT
  exact ⟨RCLike.re μ, RCLike.conj_eq_iff_re.mp (hs.conj_eigenvalue_eq_self hμ) |>.symm ▸ rfl⟩

/-- Axler 7.13: on a complex inner product space, `⟪T v, v⟫ = 0` for all `v` forces `T = 0`. -/
@[kb "axler2024" "7.13, p. 252"]
theorem axler_7_13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : V →ₗ[ℂ] V)
    (h : ∀ v, ⟪T v, v⟫_ℂ = 0) : T = 0 :=
  (inner_map_self_eq_zero T).1 h

/-- Axler 7.14: on a complex space, `T` is self-adjoint iff `⟪T v, v⟫` is real for every `v`. -/
@[kb "axler2024" "7.14, p. 252"]
theorem axler_7_14 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) : LinearMap.adjoint T = T ↔ ∀ v, (⟪T v, v⟫_ℂ).im = 0 := by
  rw [axler_7_10]
  rw [show (∀ v w, ⟪T v, w⟫_ℂ = ⟪v, T w⟫_ℂ) ↔ T.IsSymmetric from Iff.rfl,
    LinearMap.isSymmetric_iff_inner_map_self_real]
  refine forall_congr' fun v => ?_
  exact Complex.conj_eq_iff_im

/-- Axler 7.16: a self-adjoint operator with `⟪T v, v⟫ = 0` for all `v` is zero (real or complex). -/
@[kb "axler2024" "7.16, p. 253"]
theorem axler_7_16 [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) (hT : LinearMap.adjoint T = T)
    (h : ∀ v, ⟪T v, v⟫_𝕜 = 0) : T = 0 :=
  (LinearMap.IsSymmetric.inner_map_self_eq_zero (T := T) ((axler_7_10 T).1 hT)).1 h

/-! ## 7B Spectral theorem prerequisites: normal operators -/

/-- Axler 7.18: an operator is normal iff it commutes with its adjoint. -/
@[kb "axler2024" "7.18, p. 253"]
theorem axler_7_18 [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    IsStarNormal T ↔ T * LinearMap.adjoint T = LinearMap.adjoint T * T := by
  rw [isStarNormal_iff, LinearMap.star_eq_adjoint, Commute, SemiconjBy]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Axler 7.20: `T` is normal iff `‖T v‖ = ‖T* v‖` for every `v`. -/
@[kb "axler2024" "7.20, p. 254"]
theorem axler_7_20 [CompleteSpace E] (T : E →L[𝕜] E) :
    IsStarNormal T ↔ ∀ v, ‖T v‖ = ‖ContinuousLinearMap.adjoint T v‖ :=
  ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint

/-- Axler 7.23: over `ℂ`, `T` is normal iff `T = A + i B` with `A, B` commuting self-adjoint. -/
@[kb "axler2024" "7.23, p. 256"]
theorem axler_7_23 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (T : V →L[ℂ] V) :
    IsStarNormal T ↔ ∃ A B : V →L[ℂ] V, IsSelfAdjoint A ∧ IsSelfAdjoint B ∧ Commute A B ∧
      T = A + Complex.I • B := by
  constructor
  · intro h
    refine ⟨realPart T, imaginaryPart T, (realPart T).2, (imaginaryPart T).2,
      isStarNormal_iff_commute_realPart_imaginaryPart.1 h, (realPart_add_I_smul_imaginaryPart T).symm⟩
  · rintro ⟨A, B, hA, hB, hAB, rfl⟩
    rw [isStarNormal_iff]
    have h1 : star (A + Complex.I • B) = A - Complex.I • B := by
      rw [star_add, star_smul, hA.star_eq, hB.star_eq, Complex.star_def, Complex.conj_I, neg_smul,
        sub_eq_add_neg]
    rw [h1]
    have h2 : Commute A (A + Complex.I • B) := (Commute.refl A).add_right (hAB.smul_right _)
    have h3 : Commute (Complex.I • B) (A + Complex.I • B) :=
      (hAB.symm.smul_left _).add_right (((Commute.refl B).smul_left _).smul_right _)
    exact h2.sub_left h3

/-! ## 7C Positive operators -/

/-- Axler 7.34: an operator is positive iff it is self-adjoint and `⟪T v, v⟫ ≥ 0` for all `v`. -/
@[kb "axler2024" "7.34, p. 269"]
theorem axler_7_34 [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    T.IsPositive ↔ LinearMap.adjoint T = T ∧ ∀ v, 0 ≤ ⟪T v, v⟫_𝕜 := by
  rw [LinearMap.isPositive_iff, axler_7_10]
  rfl

/-- Axler 7.36: `R` is a square root of `T` when `R ^ 2 = T`; `T` has one iff it is a square. -/
@[kb "axler2024" "7.36, p. 269"]
theorem axler_7_36 (T : Module.End 𝕜 E) : (∃ R : Module.End 𝕜 E, R ^ 2 = T) ↔ IsSquare T := by
  simp only [sq, IsSquare, eq_comm]

/-! ## 7D Isometries and unitary operators -/

/-- Axler 7.44 and 7.49: norm-preserving is the same as inner-product-preserving. -/
@[kb "axler2024" "7.44, p. 276"]
theorem axler_7_44 (S : E →ₗ[𝕜] F) :
    (∀ v, ‖S v‖ = ‖v‖) ↔ ∀ v w, ⟪S v, S w⟫_𝕜 = ⟪v, w⟫_𝕜 :=
  LinearMap.norm_map_iff_inner_map_map S

/-- Axler 7.45: a linear map taking an orthonormal basis to an orthonormal list is an isometry. -/
@[kb "axler2024" "7.45, p. 276"]
theorem axler_7_45 {ι : Type*} (b : Basis ι 𝕜 E) (hb : Orthonormal 𝕜 b) (S : E →ₗ[𝕜] F)
    (hS : Orthonormal 𝕜 (S ∘ b)) (v : E) : ‖S v‖ = ‖v‖ := by
  have := (S.isometryOfOrthonormal hb hS).norm_map v
  simpa using this

/-- Axler 7.51: an operator is unitary (an invertible isometry) iff it is a member of the unitary group. -/
@[kb "axler2024" "7.51, p. 278"]
theorem axler_7_51 [CompleteSpace E] (S : E →L[𝕜] E) :
    S ∈ unitary (E →L[𝕜] E) ↔ ∃ U : E ≃ₗᵢ[𝕜] E, (U : E →L[𝕜] E) = S := by
  constructor
  · intro h
    exact ⟨Unitary.linearIsometryEquiv ⟨S, h⟩, rfl⟩
  · rintro ⟨U, rfl⟩
    exact (Unitary.linearIsometryEquiv.symm U).2

/-- Axler 7.54: every eigenvalue of a unitary operator has absolute value 1. -/
@[kb "axler2024" "7.54, p. 280"]
theorem axler_7_54 [CompleteSpace E] (S : E →L[𝕜] E) (h : S ∈ unitary (E →L[𝕜] E)) (μ : 𝕜)
    (hμ : Module.End.HasEigenvalue (S : E →ₗ[𝕜] E) μ) : ‖μ‖ = 1 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hn := (Unitary.linearIsometryEquiv ⟨S, h⟩).norm_map v
  have hSv : S v = μ • v := by simpa using Module.End.mem_eigenspace_iff.mp hv.1
  have hS : (Unitary.linearIsometryEquiv ⟨S, h⟩) v = S v := rfl
  rw [hS, hSv, norm_smul] at hn
  have : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  nlinarith [norm_nonneg μ]

/-- Axler 7.56: a square matrix is unitary iff its columns are orthonormal in `𝕜ⁿ`. -/
@[kb "axler2024" "7.56, p. 281"]
theorem axler_7_56 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) :
    A ∈ Matrix.unitaryGroup n 𝕜 ↔
      Orthonormal 𝕜 (fun j => (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 n)) := by
  rw [Matrix.mem_unitaryGroup_iff', orthonormal_iff_ite]
  constructor
  · intro h j k
    have := congrFun (congrFun h j) k
    simpa [Matrix.mul_apply, PiLp.inner_apply, mul_comm, Matrix.one_apply] using this
  · intro h
    ext j k
    have := h j k
    simpa [Matrix.mul_apply, PiLp.inner_apply, mul_comm, Matrix.one_apply] using this

/-- Axler 7.62: positive definiteness of a matrix `B`: `B* = B` and `x* B x > 0` for `x ≠ 0`. -/
@[kb "axler2024" "7.62, p. 284"]
theorem axler_7_62 {n : Type*} [Fintype n] (B : Matrix n n 𝕜) :
    B.PosDef ↔ B.IsHermitian ∧ ∀ ⦃x : n → 𝕜⦄, x ≠ 0 → 0 < star x ⬝ᵥ (B *ᵥ x) :=
  Matrix.posDef_iff_dotProduct_mulVec

/-! ## 7E Singular value decomposition -/

/-- Axler 7.64: `T* T` is positive with the same null space as `T`, range equal to range `T*`
(`= (null T)ᗮ`), and the same rank as `T`. -/
@[kb "axler2024" "7.64, p. 288"]
theorem axler_7_64 [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) :
    (LinearMap.adjoint T ∘ₗ T).IsPositive ∧
    LinearMap.ker (LinearMap.adjoint T ∘ₗ T) = LinearMap.ker T ∧
    LinearMap.range (LinearMap.adjoint T ∘ₗ T) = LinearMap.range (LinearMap.adjoint T) ∧
    LinearMap.range (LinearMap.adjoint T ∘ₗ T) = (LinearMap.ker T)ᗮ ∧
    finrank 𝕜 (LinearMap.range (LinearMap.adjoint T ∘ₗ T)) = finrank 𝕜 (LinearMap.range T) := by
  have h2 := LinearMap.range_adjoint_comp_self T
  have h3 : LinearMap.range (LinearMap.adjoint T) = (LinearMap.ker T)ᗮ := (LinearMap.orthogonal_ker T).symm
  exact ⟨LinearMap.isPositive_adjoint_comp_self T, LinearMap.ker_adjoint_comp_self T, h2, h2.trans h3,
    by rw [h2]; exact LinearMap.finrank_range_adjoint T⟩

/-- Axler 7.65: the singular values of `T` are the nonnegative square roots of the eigenvalues of
`T* T`, listed in decreasing order. -/
@[kb "axler2024" "7.65, p. 289"]
theorem axler_7_65 [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 E = n) :
    (∀ i : Fin n, T.singularValues i ^ 2 =
      (LinearMap.isSymmetric_adjoint_comp_self T).eigenvalues hn i) ∧
    (∀ i, 0 ≤ T.singularValues i) ∧ Antitone T.singularValues :=
  ⟨LinearMap.sq_singularValues_fin T hn, LinearMap.singularValues_nonneg T,
    LinearMap.singularValues_antitone T⟩

/-- Axler 7.68: injectivity, rank and surjectivity in terms of singular values. -/
@[kb "axler2024" "7.68, p. 290"]
theorem axler_7_68 [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) :
    (Function.Injective T ↔ ∀ i < finrank 𝕜 E, 0 < T.singularValues i) ∧
    T.singularValues.support.card = finrank 𝕜 (LinearMap.range T) ∧
    (Function.Surjective T ↔ T.singularValues.support.card = finrank 𝕜 F) := by
  refine ⟨LinearMap.injective_iff_forall_lt_finrank_singularValues_pos T,
    LinearMap.card_support_singularValues T, ?_⟩
  rw [LinearMap.card_support_singularValues, ← LinearMap.range_eq_top]
  exact ⟨fun h => by rw [h]; exact finrank_top 𝕜 F, Submodule.eq_top_of_finrank_eq⟩

/-! ## 7F Consequences of the SVD: the operator norm -/

/-- Axler 7.86: the norm of `T` is the maximum of `‖T v‖` over the closed unit ball. -/
@[kb "axler2024" "7.86, p. 298"]
theorem axler_7_86 [FiniteDimensional 𝕜 E] (T : E →L[𝕜] F) :
    IsGreatest ((fun v => ‖T v‖) '' Metric.closedBall 0 1) ‖T‖ := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  have hc : IsCompact ((fun v => ‖T v‖) '' Metric.closedBall (0 : E) 1) :=
    (isCompact_closedBall (0 : E) 1).image (by fun_prop)
  have hne : ((fun v => ‖T v‖) '' Metric.closedBall (0 : E) 1).Nonempty := ⟨_, 0, by simp, rfl⟩
  have := ContinuousLinearMap.sSup_unitClosedBall_eq_norm T
  rw [← this]
  exact ⟨hc.sSup_mem hne, fun _ hy => le_csSup hc.bddAbove hy⟩

/-- Axler 7.87: the operator norm is nonnegative, vanishes only on `0`, is homogeneous and satisfies
the triangle inequality. -/
@[kb "axler2024" "7.87, p. 299"]
theorem axler_7_87 (S T : E →L[𝕜] F) (c : 𝕜) :
    0 ≤ ‖T‖ ∧ (‖T‖ = 0 ↔ T = 0) ∧ ‖c • T‖ = ‖c‖ * ‖T‖ ∧ ‖S + T‖ ≤ ‖S‖ + ‖T‖ :=
  ⟨norm_nonneg T, ContinuousLinearMap.opNorm_zero_iff T, norm_smul c T,
    ContinuousLinearMap.opNorm_add_le S T⟩

/-- Axler 7.91: the adjoint has the same norm as `T`. -/
@[kb "axler2024" "7.91, p. 301"]
theorem axler_7_91 [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    ‖ContinuousLinearMap.adjoint T‖ = ‖T‖ :=
  LinearIsometryEquiv.norm_map _ T

/-- Axler 7.95: the open unit ball is the set of vectors of norm less than 1. -/
@[kb "axler2024" "7.95, p. 305"]
theorem axler_7_95 : Metric.ball (0 : E) 1 = {v | ‖v‖ < 1} := by
  ext v
  simp

end UndergradKB.LinearAlgebra.Course
