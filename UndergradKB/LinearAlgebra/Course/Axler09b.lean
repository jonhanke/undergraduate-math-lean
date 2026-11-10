import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import UndergradKB.Common.Attr

/-! # Axler, Chapter 9 (part b): determinants, tensor products

Course-layer wrappers for the `in Mathlib` rows of Axler 9C (determinants), 9D (the characteristic
polynomial, volume) and 9E (tensor products).  Rows shared with Hefferon carry both tags.  Inner products
follow Mathlib's convention (conjugate-linear in the first slot). -/

open Module Matrix
open scoped TensorProduct

namespace UndergradKB.LinearAlgebra.Course

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-! ## 9C Determinants -/

/-- Axler 9.40, 9.41: for an operator `T` and any alternating `n`-linear form `α`, the form
`α_T (v) = α (T v₁, ..., T v_n)` equals `det T • α`, and `det T` is the only scalar that works. -/
@[kb "axler2024" "9.40, p. 372", kb "axler2024" "9.41, p. 372"]
theorem axler_9_41 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V) (T : V →ₗ[K] V) :
    (∀ (α : V [⋀^ι]→ₗ[K] K) (v : ι → V), α (T ∘ v) = LinearMap.det T * α v) ∧
    ∀ c : K, (∀ (α : V [⋀^ι]→ₗ[K] K) (v : ι → V), α (T ∘ v) = c * α v) → c = LinearMap.det T := by
  refine ⟨fun α v => ?_, fun c hc => ?_⟩
  · have h := AlternatingMap.eq_smul_basis_det e α
    have h1 : ∀ w : ι → V, α w = α e * e.det w := fun w => by
      conv_lhs => rw [h]
      simp
    rw [h1 (T ∘ v), h1 v, Basis.det_comp]
    ring
  · have := hc e.det e
    rw [Basis.det_comp, Basis.det_self] at this
    simpa using this.symm

/-- Axler 9.42: `det I = 1`, `det (c T) = c ^ n det T`, and `det T` is the product of the eigenvalues
when `T` has an eigenbasis. -/
@[kb "axler2024" "9.42, p. 372"]
theorem axler_9_42 [FiniteDimensional K V] (T : V →ₗ[K] V) (c : K) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : Basis ι K V) (l : ι → K) (hl : ∀ i, T (e i) = l i • e i) :
    LinearMap.det (LinearMap.id : V →ₗ[K] V) = 1 ∧
    LinearMap.det (c • T) = c ^ finrank K V * LinearMap.det T ∧
    LinearMap.det T = ∏ i, l i := by
  refine ⟨LinearMap.det_id, LinearMap.det_smul c T, ?_⟩
  rw [← LinearMap.det_toMatrix e T]
  have : LinearMap.toMatrix e e T = Matrix.diagonal l := by
    ext i j
    rw [LinearMap.toMatrix_apply, hl j]
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Finsupp.single_apply, eq_comm, h]
  rw [this, Matrix.det_diagonal]

/-- Axler 9.43: the determinant of a square matrix is the determinant of the corresponding operator on
`Kⁿ`. -/
@[kb "axler2024" "9.43, p. 373"]
theorem axler_9_43 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    A.det = LinearMap.det (Matrix.toLin' A) :=
  (LinearMap.det_toLin' A).symm

/-- Axler 9.45 (and Hefferon Four.I.3.3): the map taking `(v₁, ..., v_n)` to the determinant of the matrix
with these columns is an alternating `n`-linear form on `Kⁿ`. -/
@[kb "axler2024" "9.45, p. 373", kb "hefferon2020" "Four.I.3.3, p. 348"]
theorem axler_9_45 (n : ℕ) :
    ∃ α : (Fin n → K) [⋀^Fin n]→ₗ[K] K, ∀ v : Fin n → Fin n → K,
      α v = (Matrix.of fun i k => v k i).det :=
  ⟨Matrix.detRowAlternating, fun v => by
    rw [← Matrix.det_transpose]
    rfl⟩

/-- Axler 9.46 (and Hefferon Four.I.3.12): the Leibniz formula for the determinant. -/
@[kb "axler2024" "9.46, p. 374", kb "hefferon2020" "Four.I.3.12, p. 352"]
theorem axler_9_46 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    A.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : K) * ∏ k, A (σ k) k :=
  Matrix.det_apply' A

/-- Axler 9.48: the determinant of an upper-triangular matrix is the product of its diagonal entries. -/
@[kb "axler2024" "9.48, p. 374"]
theorem axler_9_48 {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (h : ∀ i j, j < i → A i j = 0) :
    A.det = ∏ i, A i i :=
  Matrix.det_of_isUpperTriangular h

/-- Axler 9.49 (and Hefferon Four.II.1.5): the determinant is multiplicative, for operators and matrices. -/
@[kb "axler2024" "9.49, p. 375", kb "hefferon2020" "Four.II.1.5, p. 368"]
theorem axler_9_49 {n : Type*} [Fintype n] [DecidableEq n] (S T : V →ₗ[K] V) (A B : Matrix n n K) :
    LinearMap.det (S * T) = LinearMap.det S * LinearMap.det T ∧ (A * B).det = A.det * B.det :=
  ⟨LinearMap.det_comp S T, Matrix.det_mul A B⟩

/-- Axler 9.50 (and Hefferon Four.II.1.7): an operator is invertible iff its determinant is nonzero, and
then `det T⁻¹ = 1 / det T`. -/
@[kb "axler2024" "9.50, p. 375", kb "hefferon2020" "Four.II.1.7, p. 369"]
theorem axler_9_50 [FiniteDimensional K V] (T : V →ₗ[K] V) :
    IsUnit T ↔ LinearMap.det T ≠ 0 := by
  rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- Axler 9.50 (inverse part): `det (T⁻¹) = 1 / det T` for an invertible operator. -/
@[kb "axler2024" "9.50, p. 375", kb "hefferon2020" "Four.II.1.7, p. 369"]
theorem axler_9_50_inv (e : V ≃ₗ[K] V) :
    LinearMap.det (e.symm : V →ₗ[K] V) = 1 / LinearMap.det (e : V →ₗ[K] V) := by
  have h : LinearMap.det (e.symm : V →ₗ[K] V) * LinearMap.det (e : V →ₗ[K] V) = 1 := by
    rw [← LinearMap.det_comp]
    simp
  exact eq_one_div_of_mul_eq_one_left h

/-- Axler 9.51 (and Hefferon Five.II.3.7): `μ` is an eigenvalue of `T` iff `det (μ I - T) = 0`. -/
@[kb "axler2024" "9.51, p. 376", kb "hefferon2020" "Five.II.3.7, p. 425"]
theorem axler_9_51 [FiniteDimensional K V] (T : Module.End K V) (μ : K) :
    T.HasEigenvalue μ ↔ LinearMap.det (μ • (1 : Module.End K V) - T) = 0 := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot, LinearMap.eval_charpoly]
  simp [Algebra.algebraMap_eq_smul_one]

/-- Axler 9.52: the determinant is a similarity invariant: `det (S⁻¹ T S) = det T`. -/
@[kb "axler2024" "9.52, p. 376"]
theorem axler_9_52 {W : Type*} [AddCommGroup W] [Module K W] (S : W ≃ₗ[K] V) (T : V →ₗ[K] V) :
    LinearMap.det ((S.symm : V →ₗ[K] W) ∘ₗ T ∘ₗ (S : W →ₗ[K] V)) = LinearMap.det T := by
  simpa using LinearMap.det_conj T S.symm

/-- Axler 9.53: the determinant of an operator is the determinant of its matrix in any basis. -/
@[kb "axler2024" "9.53, p. 377"]
theorem axler_9_53 {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι K V) (T : V →ₗ[K] V) :
    LinearMap.det T = (LinearMap.toMatrix e e T).det :=
  (LinearMap.det_toMatrix e T).symm

/-- Axler 9.55: over `ℂ` (any algebraically closed field), `det T` is the product of the eigenvalues
counted with multiplicity, the multiplicity of `μ` being `dim G(μ, T)`. -/
@[kb "axler2024" "9.55, p. 377"]
theorem axler_9_55 [DecidableEq K] [IsAlgClosed K] [FiniteDimensional K V] (T : Module.End K V) :
    LinearMap.det T = (LinearMap.charpoly T).roots.prod ∧
      ∀ μ : K, (LinearMap.charpoly T).roots.count μ = finrank K (T.maxGenEigenspace μ) := by
  refine ⟨Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _), fun μ => ?_⟩
  rw [LinearMap.finrank_maxGenEigenspace_eq, Polynomial.count_roots]

/-- Axler 9.57 (and Hefferon Four.I.2.4, Four.I.3.16): row and column operations.  Equal rows (columns)
give determinant `0`; swapping two rows negates; scaling a row scales; adding a multiple of another row
(column) preserves the determinant. -/
@[kb "axler2024" "9.57, p. 378", kb "hefferon2020" "Four.I.2.4, p. 342",
  kb "hefferon2020" "Four.I.3.16, p. 353"]
theorem axler_9_57 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) (i j : n) (hij : i ≠ j)
    (c : K) :
    (A i = A j → A.det = 0) ∧ ((∀ k, A k i = A k j) → A.det = 0) ∧
    (A.submatrix (Equiv.swap i j) id).det = - A.det ∧
    (A.updateRow i (c • A i)).det = c * A.det ∧
    (A.updateCol i (c • fun k => A k i)).det = c * A.det ∧
    (A.updateRow i (A i + c • A j)).det = A.det ∧
    (A.updateCol i (fun k => A k i + c • A k j)).det = A.det := by
  refine ⟨Matrix.det_zero_of_row_eq hij, Matrix.det_zero_of_column_eq hij, ?_, ?_, ?_,
    Matrix.det_updateRow_add_smul_self A hij c, Matrix.det_updateCol_add_smul_self A hij c⟩
  · rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]
    simp
  · rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  · rw [Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]

/-! ## 9D Characteristic polynomial, volume -/

/-- Axler 9.60: `|det T| = sqrt (det (T* T))`, which also equals the product of the singular values of `T`
(over `ℝ` or `ℂ`). -/
@[kb "axler2024" "9.60, p. 380"]
theorem axler_9_60 {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    ‖LinearMap.det T‖ = Real.sqrt (RCLike.re (LinearMap.det (LinearMap.adjoint T ∘ₗ T))) ∧
    ‖LinearMap.det T‖ = ∏ i ∈ Finset.range (finrank 𝕜 E), T.singularValues i := by
  refine ⟨?_, by rw [← LinearMap.normDet_eq_norm_det, LinearMap.normDet_eq_prod_singularValues]⟩
  have h := LinearMap.normDet_sq T
  rw [← LinearMap.normDet_eq_norm_det, ← h]
  simp [Real.sqrt_sq (LinearMap.normDet_nonneg T)]

/-- Axler 9.61: for `T` on `ℝⁿ` and any set `Ω`, `volume (T Ω) = |det T| volume Ω`. -/
@[kb "axler2024" "9.61, p. 381"]
theorem axler_9_61 (n : ℕ) (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    MeasureTheory.volume (T '' Ω) = ENNReal.ofReal |LinearMap.det T| * MeasureTheory.volume Ω :=
  MeasureTheory.Measure.addHaar_image_linearMap _ T Ω

/-- Axler 9.64 (and Hefferon Five.IV.1.9), Cayley-Hamilton: `q (T) = 0` for the characteristic polynomial. -/
@[kb "axler2024" "9.64, p. 382", kb "hefferon2020" "Five.IV.1.9, p. 453"]
theorem axler_9_64 [FiniteDimensional K V] (T : Module.End K V) {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n K) :
    Polynomial.aeval T (LinearMap.charpoly T) = 0 ∧ Polynomial.aeval A A.charpoly = 0 :=
  ⟨LinearMap.aeval_self_charpoly T, Matrix.aeval_self_charpoly A⟩

/-- Axler 9.65: the characteristic polynomial is monic of degree `n`, with `z^(n-1)` coefficient `- tr T`
and constant term `(-1)^n det T`. -/
@[kb "axler2024" "9.65, p. 382"]
theorem axler_9_65 [FiniteDimensional K V] [Nontrivial V] (T : Module.End K V) :
    (LinearMap.charpoly T).Monic ∧ (LinearMap.charpoly T).natDegree = finrank K V ∧
    (LinearMap.charpoly T).coeff (finrank K V - 1) = - LinearMap.trace K V T ∧
    (LinearMap.charpoly T).coeff 0 = (-1) ^ finrank K V * LinearMap.det T := by
  refine ⟨LinearMap.charpoly_monic T, LinearMap.charpoly_natDegree T, ?_, ?_⟩
  · let b := Module.finBasis K V
    have hn : Nonempty (Fin (finrank K V)) := ⟨⟨0, finrank_pos⟩⟩
    have := Matrix.trace_eq_neg_charpoly_coeff (LinearMap.toMatrix b b T)
    rw [LinearMap.charpoly_toMatrix, ← LinearMap.trace_eq_matrix_trace K b, Fintype.card_fin] at this
    rw [this]
    ring
  · have := LinearMap.det_eq_sign_charpoly_coeff T
    rw [this, ← mul_assoc, ← mul_pow]
    simp

/-- Axler 9.67: the Vandermonde determinant. -/
@[kb "axler2024" "9.67, p. 384"]
theorem axler_9_67 {n : ℕ} (b : Fin n → K) :
    (Matrix.vandermonde b).det = ∏ k, ∏ j ∈ Finset.Iio k, (b k - b j) := by
  rw [Matrix.det_vandermonde]
  refine Finset.prod_comm' ?_
  intro x y
  simp [Finset.mem_Ioi, Finset.mem_Iio]

/-! ## 9E Tensor products -/

/-- Axler 9.68: a bilinear functional on `V × W` is a map linear in each variable; they are the elements
of `V →ₗ[K] W →ₗ[K] K`.  Axler 9.77: the same for maps into any space `U`. -/
@[kb "axler2024" "9.68, p. 388", kb "axler2024" "9.77, p. 392"]
theorem axler_9_68 {W U : Type*} [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (β : V → W → U)
    (h1 : ∀ v₁ v₂ w, β (v₁ + v₂) w = β v₁ w + β v₂ w) (h2 : ∀ (c : K) v w, β (c • v) w = c • β v w)
    (h3 : ∀ v w₁ w₂, β v (w₁ + w₂) = β v w₁ + β v w₂) (h4 : ∀ (c : K) v w, β v (c • w) = c • β v w) :
    ∃ B : V →ₗ[K] W →ₗ[K] U, ∀ v w, B v w = β v w :=
  ⟨LinearMap.mk₂ K β h1 h2 h3 h4, fun _ _ => rfl⟩

/-- Axler 9.72: `dim (V ⊗ W) = dim V * dim W`. -/
@[kb "axler2024" "9.72, p. 390"]
theorem axler_9_72 {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    [FiniteDimensional K W] : finrank K (V ⊗[K] W) = finrank K V * finrank K W :=
  Module.finrank_tensorProduct

/-- Axler 9.73: the map `(v, w) ↦ v ⊗ w` is bilinear. -/
@[kb "axler2024" "9.73, p. 390"]
theorem axler_9_73 {W : Type*} [AddCommGroup W] [Module K W] (v v₁ v₂ : V) (w w₁ w₂ : W) (c : K) :
    (v₁ + v₂) ⊗ₜ[K] w = v₁ ⊗ₜ[K] w + v₂ ⊗ₜ[K] w ∧
    v ⊗ₜ[K] (w₁ + w₂) = v ⊗ₜ[K] w₁ + v ⊗ₜ[K] w₂ ∧
    (c • v) ⊗ₜ[K] w = c • (v ⊗ₜ[K] w) ∧ v ⊗ₜ[K] (c • w) = c • (v ⊗ₜ[K] w) :=
  ⟨TensorProduct.add_tmul _ _ _, TensorProduct.tmul_add _ _ _, TensorProduct.smul_tmul' _ _ _,
    TensorProduct.tmul_smul _ _ _⟩

/-- Axler 9.74: if `e` and `f` are bases of `V` and `W`, then the `e_j ⊗ f_k` form a basis of `V ⊗ W`. -/
@[kb "axler2024" "9.74, p. 391"]
theorem axler_9_74 {W : Type*} [AddCommGroup W] [Module K W] {ι κ : Type*} (e : Basis ι K V)
    (f : Basis κ K W) :
    ∃ b : Basis (ι × κ) K (V ⊗[K] W), ∀ j k, b (j, k) = e j ⊗ₜ[K] f k :=
  ⟨e.tensorProduct f, fun j k => Basis.tensorProduct_apply e f j k⟩

/-- Axler 9.79: universal property of the tensor product: every bilinear map `V × W → U` factors
uniquely as `L (v ⊗ w)` for a linear map `L : V ⊗ W → U`. -/
@[kb "axler2024" "9.79, p. 393"]
theorem axler_9_79 {W U : Type*} [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (B : V →ₗ[K] W →ₗ[K] U) :
    ∃! L : V ⊗[K] W →ₗ[K] U, ∀ v w, L (v ⊗ₜ[K] w) = B v w := by
  refine ⟨TensorProduct.lift B, fun v w => TensorProduct.lift.tmul v w, fun L hL => ?_⟩
  apply TensorProduct.ext'
  intro v w
  rw [hL, TensorProduct.lift.tmul]

/-- Axler 9.80, 9.81, 9.82: the tensor product of inner product spaces carries an inner product with
`⟪v ⊗ w, v' ⊗ w'⟫ = ⟪v, v'⟫ ⟪w, w'⟫`. -/
@[kb "axler2024" "9.80, p. 394", kb "axler2024" "9.81, p. 395",
  kb "axler2024" "9.82, p. 395"]
theorem axler_9_80 {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (v v' : E) (w w' : F) :
    inner 𝕜 (v ⊗ₜ[𝕜] w) (v' ⊗ₜ[𝕜] w') = inner 𝕜 v v' * inner 𝕜 w w' :=
  TensorProduct.inner_tmul 𝕜 v v' w w'

/-- Axler 9.83: if `e` and `f` are orthonormal bases, then the `e_j ⊗ f_k` form an orthonormal basis. -/
@[kb "axler2024" "9.83, p. 395"]
theorem axler_9_83 {𝕜 : Type*} [RCLike 𝕜] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι 𝕜 E) (f : OrthonormalBasis κ 𝕜 F) :
    ∃ b : OrthonormalBasis (ι × κ) 𝕜 (E ⊗[𝕜] F), ∀ j k, b (j, k) = e j ⊗ₜ[𝕜] f k :=
  ⟨e.tensorProduct f, fun j k => by simp⟩

/-- Axler 9.85, 9.91: an `m`-linear map `V₁ × ... × V_m → U` (`U = K` for a functional) is linear in each
slot when the other slots are held fixed. -/
@[kb "axler2024" "9.85, p. 396", kb "axler2024" "9.91, p. 397"]
theorem axler_9_91 {ι : Type*} [DecidableEq ι] {W : ι → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module K (W i)] {U : Type*} [AddCommGroup U] [Module K U] (f : MultilinearMap K W U)
    (v : ∀ i, W i) (i : ι) (x y : W i) (c : K) :
    f (Function.update v i (x + y)) = f (Function.update v i x) + f (Function.update v i y) ∧
      f (Function.update v i (c • x)) = c • f (Function.update v i x) :=
  ⟨f.map_update_add v i x y, f.map_update_smul v i c x⟩

/-- Axler 9.90: products `e¹_{j₁} ⊗ ... ⊗ e^m_{j_m}` of basis vectors form a basis of the `m`-fold tensor
product. -/
@[kb "axler2024" "9.90, p. 397"]
theorem axler_9_90 {ι : Type*} [Finite ι] {W : ι → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module K (W i)] {κ : ι → Type*} (e : ∀ i, Basis (κ i) K (W i)) :
    ∃ b : Basis (∀ i, κ i) K (PiTensorProduct K W), ∀ p : ∀ i, κ i, b p = ⨂ₜ[K] i, e i (p i) :=
  ⟨Basis.piTensorProduct e, fun p => Basis.piTensorProduct_apply e p⟩

/-- Axler 9.92: universal property of the `m`-fold tensor product. -/
@[kb "axler2024" "9.92, p. 398"]
theorem axler_9_92 {ι : Type*} {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {U : Type*} [AddCommGroup U] [Module K U] (f : MultilinearMap K W U) :
    ∃! L : PiTensorProduct K W →ₗ[K] U, ∀ v : ∀ i, W i, L (PiTensorProduct.tprod K v) = f v :=
  ⟨PiTensorProduct.lift f, fun v => PiTensorProduct.lift.tprod v,
    fun _ hL => PiTensorProduct.lift.unique hL⟩

end UndergradKB.LinearAlgebra.Course
