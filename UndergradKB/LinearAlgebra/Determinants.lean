import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr

/-! # Determinants (Axler, chapter 9B-9D; Hefferon, chapters Four and Five.II)

Rows LA-528, 534, 537, 543, 544, 555, 557, 558, 575, 576, 581, 582, 584.
-/

open Module
open scoped ComplexOrder InnerProductSpace Matrix

namespace UndergradKB.LinearAlgebra

/-! ### Alternating forms -/

section Alternating

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If `m > dim V`, every alternating `m`-linear form on `V` is zero. -/
@[kb "axler2024" "9.29, p. 365"]
theorem axler_9_29 {m : ℕ} (hm : finrank K V < m) (f : V [⋀^Fin m]→ₗ[K] K) : f = 0 := by
  ext v
  have h : ¬ LinearIndependent K v := fun hv => by
    have := hv.fintype_card_le_finrank
    simp at this
    omega
  simpa using f.map_linearDependent v h

/-- The space of alternating `(dim V)`-linear forms on `V` has dimension `1`. -/
@[kb "axler2024" "9.37, p. 369"]
theorem axler_9_37 : finrank K (V [⋀^Fin (finrank K V)]→ₗ[K] K) = 1 := by
  let b := Module.finBasis K V
  have hne : b.det ≠ 0 := fun h => by
    have := b.det_self
    rw [h] at this
    simp at this
  rw [finrank_eq_one_iff_of_ne_zero' b.det hne]
  intro w
  exact ⟨w b, (w.eq_smul_basis_det b).symm⟩

end Alternating

/-! ### Hadamard's inequality -/

section Hadamard

variable {𝕜 : Type*} [RCLike 𝕜]

theorem hadamard_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ j, ‖(WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n))‖ := by
  set f : Fin n → EuclideanSpace 𝕜 (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j) with hf
  have h : finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n) := by simp
  set e := InnerProductSpace.gramSchmidtOrthonormalBasis h f with he
  set s := EuclideanSpace.basisFun (Fin n) 𝕜 with hs
  have h1 : A.det = s.toBasis.det f := by
    rw [Module.Basis.det_apply]
    congr 1
  have h2 : s.toBasis.det f = s.toBasis.det (e.toBasis : Fin n → _) * e.toBasis.det f := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  rw [OrthonormalBasis.coe_toBasis] at h2
  rw [h1, h2, norm_mul, s.det_to_matrix_orthonormalBasis e, one_mul, he,
    InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  calc ‖⟪InnerProductSpace.gramSchmidtOrthonormalBasis h f j, f j⟫_𝕜‖
      ≤ ‖InnerProductSpace.gramSchmidtOrthonormalBasis h f j‖ * ‖f j‖ := norm_inner_le_norm _ _
    _ = ‖f j‖ := by rw [(InnerProductSpace.gramSchmidtOrthonormalBasis h f).orthonormal.1 j, one_mul]

/-- Hadamard's inequality: the absolute value of the determinant of a real or complex square matrix is
at most the product of the Euclidean norms of its columns. -/
@[kb "axler2024" "9.66, p. 383"]
theorem axler_9_66 {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
  refine (hadamard_aux A).trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_))
  simp [EuclideanSpace.norm_eq]

end Hadamard

/-! ### Determinants of transposes, duals, adjoints -/

section Transpose

/-- `det Aᵗ = det A`. -/
@[kb "axler2024" "9.56, p. 378"]
theorem axler_9_56_transpose {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) : Aᵀ.det = A.det :=
  Matrix.det_transpose A

/-- The determinant of the dual (transpose) of an operator equals the determinant of the operator. -/
@[kb "axler2024" "9.56, p. 378"]
theorem axler_9_56_dual {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : V →ₗ[K] V) : LinearMap.det T.dualMap = LinearMap.det T :=
  LinearMap.det_dualMap T

/-- The determinant of the adjoint of an operator is the complex conjugate of its determinant. -/
@[kb "axler2024" "9.56, p. 378"]
theorem axler_9_56_adjoint {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    LinearMap.det (LinearMap.adjoint T) = star (LinearMap.det T) := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis T,
    LinearMap.toMatrix_adjoint b b T, Matrix.det_conjTranspose]

/-- A real square matrix has the same determinant as its transpose. -/
@[kb "hefferon2020" "Four.I.3.15, p. 353"]
theorem hefferon_Four_I_3_15 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Aᵀ.det = A.det :=
  Matrix.det_transpose A

/-- A real square matrix has the same determinant as its transpose (permutation-inverse proof). -/
@[kb "hefferon2020" "Four.I.4.10, p. 362"]
theorem hefferon_Four_I_4_10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Aᵀ.det = A.det :=
  Matrix.det_transpose A

end Transpose

/-! ### Unitary and positive operators -/

section Operators

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A unitary operator (here: a norm-preserving operator) has a determinant of absolute value `1`. -/
@[kb "axler2024" "9.58, p. 380"]
theorem axler_9_58 (T : E →ₗ[𝕜] E) (hT : ∀ v, ‖T v‖ = ‖v‖) : ‖LinearMap.det T‖ = 1 := by
  have hi : ∀ x y, ⟪T x, T y⟫_𝕜 = ⟪x, y⟫_𝕜 := (LinearMap.norm_map_iff_inner_map_map T).1 hT
  have hadj : LinearMap.adjoint T * T = 1 := by
    ext x
    refine ext_inner_left 𝕜 fun y => ?_
    simp only [mul_apply_eq_comp, one_apply_eq_self]
    rw [LinearMap.adjoint_inner_right, hi]
  have h1 : star (LinearMap.det T) * LinearMap.det T = 1 := by
    rw [← axler_9_56_adjoint, ← map_mul, hadj, map_one]
  have h2 : ((‖LinearMap.det T‖ : ℝ) : 𝕜) ^ 2 = 1 := by
    rw [← RCLike.conj_mul]
    simpa using h1
  have h3 : ‖LinearMap.det T‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg (LinearMap.det T)]

/-- A positive operator has a nonnegative determinant. -/
@[kb "axler2024" "9.59, p. 380"]
theorem axler_9_59 (T : E →ₗ[𝕜] E) (hT : T.IsPositive) : 0 ≤ LinearMap.det T := by
  rw [hT.isSymmetric.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_nonneg fun i _ => by
    exact_mod_cast hT.nonneg_eigenvalues rfl i

end Operators

/-! ### Cofactor expansion -/

section Cofactor

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The `(i, j)` minor of a square matrix: delete row `i` and column `j`. -/
def minorMatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) R :=
  A.submatrix i.succAbove j.succAbove

/-- The `(i, j)` cofactor: `(-1)^(i+j)` times the determinant of the `(i, j)` minor. -/
def cofactor (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) : R :=
  (-1) ^ (i + j : ℕ) * (minorMatrix A i j).det

/-- The cofactors are the entries of the adjugate (transposed). -/
@[kb "hefferon2020" "Four.III.1.2, p. 374"]
theorem hefferon_Four_III_1_2 (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin (n + 1)) :
    cofactor A i j = A.adjugate j i := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, cofactor, minorMatrix, add_comm]

/-- Laplace expansion along any row `i`, and along any column `j`, in terms of cofactors. -/
@[kb "hefferon2020" "Four.III.1.5, p. 375"]
theorem hefferon_Four_III_1_5 (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (∀ i, A.det = ∑ j, A i j * cofactor A i j) ∧ (∀ j, A.det = ∑ i, A i j * cofactor A i j) := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · rw [Matrix.det_succ_row A i]
    exact Finset.sum_congr rfl fun j _ => by simp [cofactor, minorMatrix]; ring
  · rw [Matrix.det_succ_column A j]
    exact Finset.sum_congr rfl fun i _ => by simp [cofactor, minorMatrix]; ring

end Cofactor

/-! ### Characteristic polynomials -/

section Charpoly

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The characteristic polynomial of `T` evaluated at `z` is `det (z I - T)`. -/
@[kb "axler2024" "9.62, p. 381"]
theorem axler_9_62 (T : V →ₗ[K] V) (z : K) :
    T.charpoly.eval z = LinearMap.det (z • (1 : V →ₗ[K] V) - T) := by
  rw [LinearMap.eval_charpoly, Algebra.algebraMap_eq_smul_one]

/-- Over an algebraically closed field the characteristic polynomial is
`∏ (z - λ)^(dim G(λ, T))` over the eigenvalues `λ` (`s` is the set of eigenvalues). -/
@[kb "axler2024" "9.63, p. 381"]
theorem axler_9_63 [IsAlgClosed K] (T : V →ₗ[K] V) (s : Finset K)
    (hs : ∀ μ, μ ∈ s ↔ Module.End.HasEigenvalue T μ) :
    T.charpoly = ∏ μ ∈ s, (Polynomial.X - Polynomial.C μ) ^ finrank K (Module.End.maxGenEigenspace T μ) := by
  classical
  have hmonic := LinearMap.charpoly_monic T
  have hroots : T.charpoly.roots.card = T.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have h1 := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hroots
  have h2 : s = T.charpoly.roots.toFinset := by
    ext μ
    rw [hs, Multiset.mem_toFinset, Polynomial.mem_roots hmonic.ne_zero,
      Module.End.hasEigenvalue_iff_isRoot_charpoly]
  rw [← h1, Finset.prod_multiset_map_count, h2]
  exact Finset.prod_congr rfl fun μ _ => by
    rw [LinearMap.finrank_maxGenEigenspace_eq, Polynomial.count_roots]

/-- Hefferon's convention for matrices: `det (A - x I) = (-1)^n * charpoly_A(x)` where the
characteristic polynomial is `det (x I - A)`. -/
@[kb "hefferon2020" "Five.II.3.9, p. 426"]
theorem hefferon_Five_II_3_9 {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (x : R) :
    (A - Matrix.scalar ι x).det = (-1) ^ Fintype.card ι * A.charpoly.eval x := by
  rw [Matrix.eval_charpoly, ← Matrix.det_neg, neg_sub]

end Charpoly

/-! ### Similar matrices -/

section Similar

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasEigenvector_conj (A P Q : Matrix ι ι K) (hQP : Q * P = 1) (μ : K) (v : ι → K)
    (h : Module.End.HasEigenvector (Matrix.toLin' A) μ v) :
    Module.End.HasEigenvector (Matrix.toLin' (P * A * Q)) μ (P *ᵥ v) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  rw [Matrix.toLin'_apply] at h1 ⊢
  refine ⟨?_, fun h0 => h2 ?_⟩
  · rw [Matrix.mulVec_mulVec, mul_assoc (P * A) Q P, hQP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul]
  · have : Q *ᵥ (P *ᵥ v) = 0 := by rw [h0, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec] at this

/-- Similar matrices `A` and `P A Q` (with `Q = P⁻¹`) have the same eigenvalues, and an eigenvector `v`
of `A` is carried to the eigenvector `P v` of `P A Q`. -/
@[kb "hefferon2020" "Five.II.3.6, p. 423"]
theorem hefferon_Five_II_3_6 (A P Q : Matrix ι ι K) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (∀ μ, Module.End.HasEigenvalue (Matrix.toLin' A) μ ↔
        Module.End.HasEigenvalue (Matrix.toLin' (P * A * Q)) μ) ∧
      ∀ μ v, Module.End.HasEigenvector (Matrix.toLin' A) μ v →
        Module.End.HasEigenvector (Matrix.toLin' (P * A * Q)) μ (P *ᵥ v) := by
  refine ⟨fun μ => ⟨fun h => ?_, fun h => ?_⟩, fun μ v => hasEigenvector_conj A P Q hQP μ v⟩
  · obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_conj A P Q hQP μ v hv)
  · obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have := hasEigenvector_conj (P * A * Q) Q P hPQ μ v hv
    rw [show Q * (P * A * Q) * P = A by
      rw [show Q * (P * A * Q) * P = (Q * P) * A * (Q * P) by simp only [mul_assoc], hQP, one_mul,
        mul_one]] at this
    exact Module.End.hasEigenvalue_of_hasEigenvector this

end Similar

/-! ### Hefferon's determinant functions -/

section DetFunction

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hefferon's definition of a determinant function (Definition Four.I.2.1) on square matrices,
conditions (1)-(4): adding a multiple of one row to another row, swapping two rows, scaling a row by any
scalar `k`, and the value `1` on the identity. -/
structure IsDetFunction (d : Matrix ι ι K → K) : Prop where
  add_smul_row : ∀ (M : Matrix ι ι K) (i j : ι), i ≠ j → ∀ k : K,
    d (M.updateRow j (k • M i + M j)) = d M
  swap_rows : ∀ (M : Matrix ι ι K) (i j : ι), i ≠ j → d (M.submatrix (Equiv.swap i j) id) = -d M
  smul_row : ∀ (M : Matrix ι ι K) (i : ι) (k : K), d (M.updateRow i (k • M i)) = k * d M
  map_one : d 1 = 1

/-- `Matrix.det` satisfies Hefferon's four determinant conditions. -/
@[kb "hefferon2020" "Four.I.2.1, p. 342"]
theorem hefferon_Four_I_2_1 : IsDetFunction (Matrix.det : Matrix ι ι K → K) where
  add_smul_row M i j h k := by
    rw [add_comm]
    exact Matrix.det_updateRow_add_smul_self M h.symm k
  swap_rows M i j h := by
    rw [Matrix.det_permute, Equiv.Perm.sign_swap h]
    simp
  smul_row M i k := by
    rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  map_one := Matrix.det_one

namespace IsDetFunction

variable {d : Matrix ι ι K → K} (hd : IsDetFunction d)
include hd

omit [Fintype ι] in
theorem zero_row (M : Matrix ι ι K) (i : ι) (h : M i = 0) : d M = 0 := by
  have := hd.smul_row M i 0
  have e : M.updateRow i ((0 : K) • M i) = M := by
    rw [zero_smul, ← h, Matrix.updateRow_eq_self]
  rw [e] at this
  simpa using this

theorem eq_zero_of_dependent (M : Matrix ι ι K) (i : ι) (c : ι → K)
    (h : M i + ∑ j ∈ Finset.univ.erase i, c j • M j = 0) : d M = 0 := by
  have key : ∀ s : Finset ι, i ∉ s →
      d (M.updateRow i (M i + ∑ j ∈ s, c j • M j)) = d M := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hi
      have hai : a ≠ i := fun e => hi (e ▸ Finset.mem_insert_self a s)
      have his : i ∉ s := fun e => hi (Finset.mem_insert_of_mem e)
      have step := hd.add_smul_row (M.updateRow i (M i + ∑ j ∈ s, c j • M j)) a i hai (c a)
      rw [Matrix.updateRow_ne hai, Matrix.updateRow_self, Matrix.updateRow_idem] at step
      rw [← ih his, ← step, Finset.sum_insert ha]
      congr 2
      abel
  have := key (Finset.univ.erase i) (by simp)
  rw [h] at this
  rw [← this]
  exact hd.zero_row _ i (by simp)

theorem eq_zero_of_det_eq_zero (M : Matrix ι ι K) (hM : M.det = 0) : d M = 0 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  refine hd.eq_zero_of_dependent M i (fun j => v j / v i) ?_
  funext k
  have hk : ∑ j, v j * M j k = 0 := by
    simpa [Matrix.vecMul, dotProduct] using congrFun hv k
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hk
  have hvi : v i ≠ 0 := hi
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  have : M i k + ∑ j ∈ Finset.univ.erase i, v j / v i * M j k =
      (v i)⁻¹ * (v i * M i k + ∑ j ∈ Finset.univ.erase i, v j * M j k) := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hvi, one_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hk, mul_zero]

theorem diagonal_mul (D : ι → K) (N : Matrix ι ι K) :
    d (Matrix.diagonal D * N) = (∏ i, D i) * d N := by
  have key : ∀ s : Finset ι,
      d (Matrix.of fun i j => if i ∈ s then D i * N i j else N i j) = (∏ i ∈ s, D i) * d N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (Matrix.of fun i j => if i ∈ (∅ : Finset ι) then D i * N i j else N i j) = N := by
        ext i j; simp
      rw [this]; simp
    | insert a s ha ih =>
      have e : (Matrix.of fun i j => if i ∈ insert a s then D i * N i j else N i j) =
          (Matrix.of fun i j => if i ∈ s then D i * N i j else N i j).updateRow a
            (D a • (Matrix.of fun i j => if i ∈ s then D i * N i j else N i j) a) := by
        ext i j
        by_cases hia : i = a
        · subst hia; simp [ha]
        · simp [hia, Matrix.updateRow_ne]
      rw [e, hd.smul_row, ih, Finset.prod_insert ha]
      ring
  have h := key Finset.univ
  have e : Matrix.diagonal D * N = Matrix.of fun i j => if i ∈ Finset.univ then D i * N i j
      else N i j := by
    ext i j; simp [Matrix.diagonal_mul]
  rw [e, h]

theorem transvection_mul (t : Matrix.TransvectionStruct ι K) (N : Matrix ι ι K) :
    d (t.toMatrix * N) = d N := by
  have e : t.toMatrix * N = N.updateRow t.i (t.c • N t.j + N t.i) := by
    ext a b
    by_cases ha : a = t.i
    · subst ha
      simp [Matrix.TransvectionStruct.toMatrix, Matrix.transvection_mul_apply_same, add_comm]
    · simp [Matrix.TransvectionStruct.toMatrix, ha, Matrix.updateRow_ne]
  rw [e]
  exact hd.add_smul_row N t.j t.i t.hij.symm t.c

/-- Any function satisfying the four determinant conditions is the determinant. -/
theorem eq_det : d = Matrix.det := by
  funext M
  by_cases hM : M.det = 0
  · rw [hM]; exact hd.eq_zero_of_det_eq_zero M hM
  · have := Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun A : Matrix ι ι K => ∀ N, d (A * N) = A.det * d N) M hM
      (fun D _ N => by rw [hd.diagonal_mul, Matrix.det_diagonal])
      (fun t N => by rw [hd.transvection_mul, Matrix.TransvectionStruct.det, one_mul])
      (fun A B _ _ hA hB N => by rw [Matrix.det_mul, mul_assoc, hA, hB, mul_assoc]) 1
    simpa [hd.map_one] using this

end IsDetFunction

/-- There is at most one determinant function on `n × n` matrices (and it is `Matrix.det`). -/
@[kb "hefferon2020" "Four.I.2.7, p. 344"]
theorem hefferon_Four_I_2_7 {d₁ d₂ : Matrix ι ι K → K} (h₁ : IsDetFunction d₁)
    (h₂ : IsDetFunction d₂) : d₁ = d₂ := by
  rw [h₁.eq_det, h₂.eq_det]

end DetFunction

/-! ### Inversions and the sign of a permutation -/

section Inversions

variable {n : ℕ}

/-- The number of inversions of a permutation of `{0, …, n-1}`: pairs `i < j` with `σ j < σ i`. -/
def inversions (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

theorem sign_eq_signAux (σ : Equiv.Perm (Fin n)) : Equiv.Perm.sign σ = Equiv.Perm.signAux σ := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · simp
  · intro f x y hxy ih
    rw [map_mul, Equiv.Perm.sign_swap hxy, ih, Equiv.Perm.signAux_mul,
      Equiv.Perm.signAux_swap hxy]

theorem signAux_eq_pow (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.signAux σ = (-1 : ℤˣ) ^ inversions σ := by
  unfold Equiv.Perm.signAux
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  unfold inversions
  refine Finset.card_bij (fun a _ => (a.2, a.1)) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Equiv.Perm.mem_finPairsLT] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨ha.1, lt_of_le_of_ne ha.2 fun e => ?_⟩
    have := σ.injective e
    exact absurd this (ne_of_gt ha.1)
  · rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨⟨b.2, b.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Equiv.Perm.mem_finPairsLT]
    exact ⟨hb.1, hb.2.le⟩

/-- The determinant of a permutation matrix is `(-1)^(number of inversions)`. -/
theorem det_permMatrix_eq_pow_inversions (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix ℤ).det = (-1) ^ inversions σ := by
  rw [Matrix.det_permutation, sign_eq_signAux, signAux_eq_pow]
  simp

/-- Swap rows `p.1` and `p.2` of a matrix. -/
def swapRows (M : Matrix (Fin n) (Fin n) ℤ) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  M.submatrix (Equiv.swap p.1 p.2) id

theorem det_foldl_swapRows (l : List (Fin n × Fin n)) (hl : ∀ p ∈ l, p.1 ≠ p.2)
    (M : Matrix (Fin n) (Fin n) ℤ) :
    (l.foldl swapRows M).det = (-1) ^ l.length * M.det := by
  induction l generalizing M with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)), swapRows,
      Matrix.det_permute, Equiv.Perm.sign_swap (hl p (List.mem_cons_self))]
    simp [pow_succ]

/-- If a permutation matrix is brought to the identity by a sequence `l` of row swaps, then the number
of swaps and the number of inversions of the permutation have the same parity. -/
@[kb "hefferon2020" "Four.I.4.5, p. 359"]
theorem hefferon_Four_I_4_5 (σ : Equiv.Perm (Fin n)) (l : List (Fin n × Fin n))
    (hl : ∀ p ∈ l, p.1 ≠ p.2) (h : l.foldl swapRows (σ.permMatrix ℤ) = 1) :
    Even l.length ↔ Even (inversions σ) := by
  have h1 := det_foldl_swapRows l hl (σ.permMatrix ℤ)
  rw [h, Matrix.det_one, det_permMatrix_eq_pow_inversions, ← pow_add] at h1
  have h2 : Even (l.length + inversions σ) :=
    (neg_one_pow_eq_one_iff_even (by norm_num)).1 h1.symm
  exact Nat.even_add.1 h2

end Inversions

end UndergradKB.LinearAlgebra
