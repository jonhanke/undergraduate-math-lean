import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr

/-! # Axler, Chapter 8: operators on complex vector spaces

Course-layer wrappers for the `in Mathlib` rows of Axler chapter 8 (generalized eigenvectors, nilpotent
operators, characteristic polynomial, trace).  Statements are over a general field `K` when the Mathlib
result is that general. Inner products follow the Mathlib convention (conjugate-linear in the first slot),
so Axler's `⟨T e, e⟩` appears as `⟪e, T e⟫`. -/

open scoped InnerProductSpace
open Module

namespace UndergradKB.LinearAlgebra.Course

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-! ## 8A Generalized eigenvectors and nilpotent operators -/

/-- Axler 8.1: the null spaces of `T^0, T^1, T^2, ...` form an increasing chain. -/
@[kb "axler2024" "8.1, p. 316"]
theorem axler_8_1 (T : End K V) : Monotone fun k : ℕ => LinearMap.ker (T ^ k) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [pow_succ']
  exact LinearMap.ker_le_ker_comp (T ^ k) T

/-- Axler 8.2: if `null T^m = null T^(m+1)` then `null T^(m+k) = null T^m` for all `k`. -/
@[kb "axler2024" "8.2, p. 316"]
theorem axler_8_2 (T : End K V) (m : ℕ) (h : LinearMap.ker (T ^ m) = LinearMap.ker (T ^ (m + 1)))
    (k : ℕ) : LinearMap.ker (T ^ (m + k)) = LinearMap.ker (T ^ m) :=
  (Module.End.ker_pow_constant h k).symm

/-- Axler 8.3: on a finite-dimensional space the null spaces stop growing at `k = dim V`. -/
@[kb "axler2024" "8.3, p. 317"]
theorem axler_8_3 [FiniteDimensional K V] (T : End K V) (k : ℕ) :
    LinearMap.ker (T ^ (finrank K V + k)) = LinearMap.ker (T ^ finrank K V) :=
  Module.End.ker_pow_eq_ker_pow_finrank_of_le (Nat.le_add_right _ _)

/-- Axler 8.8: `v` is a generalized eigenvector of `T` for `μ` iff `v ≠ 0` and some power of `T - μ I`
kills it. -/
@[kb "axler2024" "8.8, p. 318"]
theorem axler_8_8 (T : End K V) (μ : K) (v : V) :
    (∃ k, T.HasGenEigenvector μ k v) ↔ v ≠ 0 ∧ ∃ k : ℕ, ((T - μ • 1) ^ k) v = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [Module.End.hasGenEigenvector_iff, Module.End.genEigenspace_nat] at hk
    exact ⟨hk.2, k, hk.1⟩
  · rintro ⟨hv, k, hk⟩
    refine ⟨k, ?_⟩
    rw [Module.End.hasGenEigenvector_iff, Module.End.genEigenspace_nat]
    exact ⟨hk, hv⟩

/-- Axler 8.11: generalized eigenspaces of distinct scalars meet only in `0`. -/
@[kb "axler2024" "8.11, p. 320"]
theorem axler_8_11 (T : End K V) {μ₁ μ₂ : K} (h : μ₁ ≠ μ₂) (v : V)
    (h₁ : v ∈ T.maxGenEigenspace μ₁) (h₂ : v ∈ T.maxGenEigenspace μ₂) : v = 0 := by
  have := Module.End.disjoint_genEigenspace T h ⊤ ⊤
  exact (Submodule.disjoint_def.mp this) v h₁ h₂

/-- Axler 8.12: nonzero generalized eigenvectors for distinct eigenvalues are linearly independent. -/
@[kb "axler2024" "8.12, p. 321"]
theorem axler_8_12 (T : End K V) {ι : Type*} (μ : ι → K) (hμ : Function.Injective μ) (v : ι → V)
    (hv : ∀ i, v i ∈ T.maxGenEigenspace (μ i)) (hv0 : ∀ i, v i ≠ 0) : LinearIndependent K v :=
  iSupIndep.linearIndependent (fun i => T.maxGenEigenspace (μ i))
    ((Module.End.independent_maxGenEigenspace T).comp hμ) hv hv0

/-- Axler 8.14 (also Hefferon Five.III.2.7): an operator is nilpotent when some power of it is zero. -/
@[kb "axler2024" "8.14, p. 321", kb "hefferon2020" "Five.III.2.7, p. 440"]
theorem axler_8_14 (T : End K V) : IsNilpotent T ↔ ∃ k : ℕ, T ^ k = 0 := Iff.rfl

/-! ## 8B Generalized eigenspace decomposition -/

/-- Axler 8.19: `G(μ, T)` consists of the vectors killed by some power of `T - μ I`, and contains the
eigenspace. -/
@[kb "axler2024" "8.19, p. 326", kb "axler2024" "8.19a, p. 326"]
theorem axler_8_19 (T : End K V) (μ : K) :
    (∀ v, v ∈ T.maxGenEigenspace μ ↔ ∃ k : ℕ, ((T - μ • 1) ^ k) v = 0) ∧
      T.eigenspace μ ≤ T.maxGenEigenspace μ :=
  ⟨fun v => Module.End.mem_maxGenEigenspace T μ v, Module.End.eigenspace_le_maxGenEigenspace⟩

/-- Axler 8.8a and 8.20: `G(μ, T) = null (T - μ I)^(dim V)`. -/
@[kb "axler2024" "8.8a, p. 319", kb "axler2024" "8.20, p. 326"]
theorem axler_8_20 [FiniteDimensional K V] (T : End K V) (μ : K) :
    T.maxGenEigenspace μ = LinearMap.ker ((T - μ • 1) ^ finrank K V) := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat]

/-- Axler 8.35: a block diagonal matrix has the blocks on the diagonal (entries `A i`) and zeros
elsewhere. -/
@[kb "axler2024" "8.35, p. 332"]
theorem axler_8_35 {o : Type*} [DecidableEq o] {m' : o → Type*} (A : (i : o) → Matrix (m' i) (m' i) K)
    (i : o) (a b : m' i) (j : o) (hij : i ≠ j) (c : m' j) :
    Matrix.blockDiagonal' A ⟨i, a⟩ ⟨i, b⟩ = A i a b ∧ Matrix.blockDiagonal' A ⟨i, a⟩ ⟨j, c⟩ = 0 :=
  ⟨Matrix.blockDiagonal'_apply_eq A i a b, Matrix.blockDiagonal'_apply_ne A a c hij⟩

/-! ## 8C Characteristic polynomial and Cayley-Hamilton -/

/-- Axler 8.28: the characteristic polynomial has degree `dim V`, and its roots are exactly the
eigenvalues. -/
@[kb "axler2024" "8.28, p. 330"]
theorem axler_8_28 [FiniteDimensional K V] (T : End K V) :
    (LinearMap.charpoly T).natDegree = finrank K V ∧ (LinearMap.charpoly T).Monic ∧
      ∀ μ : K, T.HasEigenvalue μ ↔ (LinearMap.charpoly T).IsRoot μ :=
  ⟨LinearMap.charpoly_natDegree T, LinearMap.charpoly_monic T,
    Module.End.hasEigenvalue_iff_isRoot_charpoly T⟩

/-- Axler 8.29 (Cayley-Hamilton): `q(T) = 0` for the characteristic polynomial `q` of `T`. -/
@[kb "axler2024" "8.29, p. 330"]
theorem axler_8_29 [FiniteDimensional K V] (T : End K V) :
    Polynomial.aeval T (LinearMap.charpoly T) = 0 :=
  LinearMap.aeval_self_charpoly T

/-- Axler 8.30: the characteristic polynomial is a polynomial multiple of the minimal polynomial. -/
@[kb "axler2024" "8.30, p. 330"]
theorem axler_8_30 [FiniteDimensional K V] (T : End K V) :
    ∃ r : Polynomial K, LinearMap.charpoly T = minpoly K T * r :=
  LinearMap.minpoly_dvd_charpoly T

/-! ## 8D Trace -/

/-- Axler 8.47: the trace of a square matrix is the sum of its diagonal entries. -/
@[kb "axler2024" "8.47, p. 344"]
theorem axler_8_47 {n : Type*} [Fintype n] (A : Matrix n n K) : A.trace = ∑ i, A i i := rfl

/-- Axler 8.49: `tr (A B) = tr (B A)` for `A` of size `m × n` and `B` of size `n × m`. -/
@[kb "axler2024" "8.49, p. 344"]
theorem axler_8_49 {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) (B : Matrix n m K) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

/-- Axler 8.50: the trace of the matrix of an operator does not depend on the basis. -/
@[kb "axler2024" "8.50, p. 345"]
theorem axler_8_50 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (c : Basis κ K V) (T : End K V) :
    (LinearMap.toMatrix b b T).trace = (LinearMap.toMatrix c c T).trace := by
  rw [← LinearMap.trace_eq_matrix_trace K b, ← LinearMap.trace_eq_matrix_trace K c]

/-- Axler 8.51: the trace of an operator is the trace of its matrix in any basis. -/
@[kb "axler2024" "8.51, p. 345"]
theorem axler_8_51 {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (T : End K V) :
    LinearMap.trace K V T = (LinearMap.toMatrix b b T).trace :=
  LinearMap.trace_eq_matrix_trace K b T

/-- Axler 8.52: over `ℂ` (any algebraically closed field), `tr T` is the sum of the eigenvalues counted with
multiplicity, the multiplicity of `μ` being `dim G(μ, T)`. -/
@[kb "axler2024" "8.52, p. 346"]
theorem axler_8_52 [DecidableEq K] [IsAlgClosed K] [FiniteDimensional K V] (T : End K V) :
    LinearMap.trace K V T = (LinearMap.charpoly T).roots.sum ∧
      ∀ μ : K, (LinearMap.charpoly T).roots.count μ = finrank K (T.maxGenEigenspace μ) := by
  refine ⟨Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _), fun μ => ?_⟩
  rw [LinearMap.finrank_maxGenEigenspace_eq, Polynomial.count_roots]

/-- Axler 8.55: on an inner product space `tr T = ∑ ⟨T e_k, e_k⟩` over an orthonormal basis (written
`⟪e_k, T e_k⟫` in Mathlib's convention). -/
@[kb "axler2024" "8.55, p. 347"]
theorem axler_8_55 {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 E) (T : E →ₗ[𝕜] E) :
    LinearMap.trace 𝕜 E T = ∑ k, ⟪e k, T (e k)⟫_𝕜 :=
  LinearMap.trace_eq_sum_inner T e

/-- Axler 8.56: the trace is a linear functional on operators and `tr (S T) = tr (T S)`. -/
@[kb "axler2024" "8.56, p. 347"]
theorem axler_8_56 (S T : End K V) (c : K) :
    LinearMap.trace K V (S + T) = LinearMap.trace K V S + LinearMap.trace K V T ∧
    LinearMap.trace K V (c • T) = c * LinearMap.trace K V T ∧
    LinearMap.trace K V (S * T) = LinearMap.trace K V (T * S) :=
  ⟨map_add _ _ _, by simp, LinearMap.trace_mul_comm K S T⟩

end UndergradKB.LinearAlgebra.Course
