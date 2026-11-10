import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.AlgebraMap
import UndergradKB.Common.Attr

/-!
# Axler, Chapter 5 (Eigenvalues and eigenvectors): course layer

Thin theorems stated in the book's terms, proved by Mathlib.
-/

namespace UndergradKB.LinearAlgebra.Course

open Polynomial Module End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ## 5A Invariant subspaces -/

/-- Axler 5.2 (and Hefferon Five.IV.2.10): `U` is invariant under `T` iff `T` maps `U` into `U`. -/
@[kb "axler2024" "5.2, p. 151", kb "hefferon2020" "Five.IV.2.10, p. 466"]
theorem axler_5_2 (T : End K V) (U : Submodule K V) :
    U ∈ Module.End.invtSubmodule T ↔ ∀ u ∈ U, T u ∈ U := by
  rw [Module.End.mem_invtSubmodule]
  exact Iff.rfl

/-- Axler 5.5 (and Hefferon Five.II.3.1): `λ` is an eigenvalue iff `T v = λ v` for some `v ≠ 0`. -/
@[kb "axler2024" "5.5, p. 152", kb "hefferon2020" "Five.II.3.1, p. 422"]
theorem axler_5_5 (T : End K V) (l : K) :
    T.HasEigenvalue l ↔ ∃ v : V, v ≠ 0 ∧ T v = l • v := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  simp only [Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨v, h1, h2⟩; exact ⟨v, h2, h1⟩
  · rintro ⟨v, h1, h2⟩; exact ⟨v, h2, h1⟩

/-- Axler 5.7: for finite-dimensional `V`, `λ` is an eigenvalue iff `T - λ I` is not injective,
iff not surjective, iff not invertible. -/
@[kb "axler2024" "5.7, p. 153"]
theorem axler_5_7 [FiniteDimensional K V] (T : End K V) (l : K) :
    List.TFAE [T.HasEigenvalue l, ¬ Function.Injective (T - algebraMap K (End K V) l),
      ¬ Function.Surjective (T - algebraMap K (End K V) l),
      ¬ IsUnit (T - algebraMap K (End K V) l)] := by
  have hker : (T - algebraMap K (End K V) l).ker = T.eigenspace l := by
    exact (Module.End.eigenspace_def).symm
  have h1 : T.HasEigenvalue l ↔ ¬ Function.Injective (T - algebraMap K (End K V) l) := by
    rw [Module.End.hasEigenvalue_iff, ← hker, ← LinearMap.ker_eq_bot]
  have h2 := LinearMap.injective_iff_surjective (f := T - algebraMap K (End K V) l)
  have h3 := LinearMap.isUnit_iff_ker_eq_bot (T - algebraMap K (End K V) l)
  rw [LinearMap.ker_eq_bot] at h3
  tfae_have 1 ↔ 2 := h1
  tfae_have 2 ↔ 3 := not_congr h2
  tfae_have 2 ↔ 4 := not_congr h3.symm
  tfae_finish

/-- Axler 5.8: an eigenvector for `λ` is a nonzero `v` with `T v = λ v`
(equivalently a nonzero element of `null (T - λ I)`). -/
@[kb "axler2024" "5.8, p. 153"]
theorem axler_5_8 (T : End K V) (l : K) (v : V) :
    T.HasEigenvector l v ↔ v ≠ 0 ∧ T v = l • v ∧
      v ∈ LinearMap.ker (T - algebraMap K (End K V) l) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  tauto

/-- Axler 5.11 (and Hefferon Five.II.3.18): eigenvectors for distinct eigenvalues are linearly
independent. -/
@[kb "axler2024" "5.11, p. 154", kb "hefferon2020" "Five.II.3.18, p. 429"]
theorem axler_5_11 {ι : Type*} (T : End K V) (μ : ι → K) (hμ : Function.Injective μ) (v : ι → V)
    (h : ∀ i, T.HasEigenvector (μ i) (v i)) : LinearIndependent K v :=
  T.eigenvectors_linearIndependent' μ hμ v h

/-- Axler 5.13: powers of an operator, `T^0 = I` and `T^(m+1) = T T^m`. -/
@[kb "axler2024" "5.13, p. 155", kb "hefferon2020" "Five.III.1.pow, p. 424"]
theorem axler_5_13 (T : End K V) (m : ℕ) :
    T ^ 0 = LinearMap.id ∧ T ^ (m + 1) = T * T ^ m := by
  exact ⟨pow_zero T, pow_succ' T m⟩

/-- Axler 5.14 (and Hefferon Five.IV.1.1): `p(T) = a₀ I + a₁ T + ⋯ + aₘ Tᵐ`. -/
@[kb "axler2024" "5.14, p. 155", kb "hefferon2020" "Five.IV.1.1, p. 450"]
theorem axler_5_14 (T : End K V) (p : K[X]) :
    aeval T p = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • T ^ i :=
  aeval_eq_sum_range T

/-- Axler 5.16: the product of polynomials is computed pointwise. -/
@[kb "axler2024" "5.16, p. 156"]
theorem axler_5_16 (p q : K[X]) (z : K) : (p * q).eval z = p.eval z * q.eval z :=
  eval_mul

/-- Axler 5.17 (and Hefferon Five.IV.1.7): `(pq)(T) = p(T) q(T)`, so `p(T)` and `q(T)` commute. -/
@[kb "axler2024" "5.17, p. 156", kb "hefferon2020" "Five.IV.1.7, p. 452"]
theorem axler_5_17 (T : End K V) (p q : K[X]) :
    aeval T (p * q) = aeval T p * aeval T q ∧ Commute (aeval T p) (aeval T q) :=
  ⟨(aeval T).map_mul p q, (Commute.all p q).map (aeval T)⟩

/-! ## 5B Eigenvectors and upper-triangular matrices -/

/-- Axler 5.19 (and Hefferon Five.II.3.10): every operator on a nonzero finite-dimensional complex
vector space has an eigenvalue. -/
@[kb "axler2024" "5.19, p. 161", kb "hefferon2020" "Five.II.3.10, p. 426"]
theorem axler_5_19 {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (T : End ℂ W) : ∃ l : ℂ, T.HasEigenvalue l :=
  Module.End.exists_eigenvalue T

/-- Axler 5.24 (and Hefferon Five.IV.1.4): the minimal polynomial of an operator on a
finite-dimensional space is monic, kills `T`, and has least degree among monic polynomials killing
`T`. -/
@[kb "axler2024" "5.24, p. 163", kb "hefferon2020" "Five.IV.1.4, p. 451"]
theorem axler_5_24 [FiniteDimensional K V] (T : End K V) :
    (minpoly K T).Monic ∧ aeval T (minpoly K T) = 0 ∧
      ∀ q : K[X], q.Monic → aeval T q = 0 → (minpoly K T).natDegree ≤ q.natDegree := by
  have hi : IsIntegral K T := Algebra.IsIntegral.isIntegral T
  refine ⟨minpoly.monic hi, minpoly.aeval K T, fun q hq h => ?_⟩
  exact natDegree_le_natDegree (minpoly.min K T hq h)

/-- Axler 5.29 (and Hefferon Five.IV.1.10): `q(T) = 0` iff `q` is a polynomial multiple of the
minimal polynomial. -/
@[kb "axler2024" "5.29, p. 166", kb "hefferon2020" "Five.IV.1.10, p. 455"]
theorem axler_5_29 [FiniteDimensional K V] (T : End K V) (q : K[X]) :
    aeval T q = 0 ↔ ∃ s : K[X], q = minpoly K T * s := by
  rw [← minpoly.dvd_iff (A := K) (x := T)]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, hs⟩, fun ⟨s, hs⟩ => ⟨s, hs⟩⟩

/-- Axler 5.32: `T` is not invertible iff the constant term of its minimal polynomial is `0`. -/
@[kb "axler2024" "5.32, p. 167"]
theorem axler_5_32 [FiniteDimensional K V] (T : End K V) :
    ¬ IsUnit T ↔ (minpoly K T).coeff 0 = 0 := by
  have h := LinearMap.hasEigenvalue_zero_tfae T
  have h14 : T.HasEigenvalue 0 ↔ ⊥ < LinearMap.ker T := h.out 1 5
  have h12 : T.HasEigenvalue 0 ↔ (minpoly K T).IsRoot 0 := h.out 1 2
  have h0 : ¬ IsUnit T ↔ ⊥ < LinearMap.ker T := by
    rw [LinearMap.isUnit_iff_ker_eq_bot, bot_lt_iff_ne_bot]
  rw [h0, ← h14, h12, Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero]

/-- Axler 5.35: the matrix of an operator with respect to a basis, column by column:
`T v_k = ∑ⱼ M(T)ⱼₖ v_j`. -/
@[kb "axler2024" "5.35, p. 172"]
theorem axler_5_35 {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) (T : End K V)
    (k : n) : T (b k) = ∑ j, LinearMap.toMatrix b b T j k • b j := by
  conv_lhs => rw [← b.sum_repr (T (b k))]
  simp [LinearMap.toMatrix_apply]

omit [Field K] in
/-- Axler 5.37: the diagonal of a square matrix consists of the entries `A i i`. -/
@[kb "axler2024" "5.37, p. 173"]
theorem axler_5_37 {n : Type*} (A : Matrix n n K) (i : n) : A.diag i = A i i := rfl

/-- Axler 5.38: a square matrix is upper triangular when all entries below the diagonal vanish. -/
@[kb "axler2024" "5.38, p. 173"]
theorem axler_5_38 (n : ℕ) (A : Matrix (Fin n) (Fin n) K) :
    A.IsUpperTriangular ↔ ∀ i j : Fin n, j < i → A i j = 0 := by
  constructor
  · intro h i j hij; exact h hij
  · intro h i j hij; exact h i j hij

/-- Axler 5.48: a diagonal matrix has zero entries off the diagonal. -/
@[kb "axler2024" "5.48, p. 181"]
theorem axler_5_48 {n : Type*} (A : Matrix n n K) : A.IsDiag ↔ ∀ i j, i ≠ j → A i j = 0 :=
  Iff.rfl

/-! ## 5C Eigenspaces and diagonal matrices -/

/-- Axler 5.52 (and Hefferon Five.II.3.12, 3.13): the eigenspace `E(λ, T)` is `null (T - λ I)`,
i.e. the eigenvectors for `λ` together with `0`. -/
@[kb "axler2024" "5.52, p. 182", kb "hefferon2020" "Five.II.3.12, p. 427"]
theorem axler_5_52 (T : End K V) (l : K) (v : V) :
    v ∈ T.eigenspace l ↔ T v = l • v ∧ v ∈ LinearMap.ker (T - algebraMap K (End K V) l) := by
  rw [Module.End.mem_eigenspace_iff]
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  tauto

/-! ## 5E Commuting operators -/

/-- Axler 5.71: two operators commute when `S T = T S`. -/
@[kb "axler2024" "5.71, p. 193"]
theorem axler_5_71 (S T : End K V) : Commute S T ↔ S * T = T * S := Iff.rfl

/-- Axler 5.74: operators commute iff their matrices with respect to a common basis commute. -/
@[kb "axler2024" "5.74, p. 194"]
theorem axler_5_74 {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V)
    (S T : End K V) :
    Commute S T ↔ Commute (LinearMap.toMatrix b b S) (LinearMap.toMatrix b b T) := by
  constructor
  · intro h
    exact h.map (LinearMap.toMatrixAlgEquiv b)
  · intro h
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_mul, map_mul]
    exact h.eq

/-- Axler 5.75: if `S` and `T` commute then every eigenspace of `S` is invariant under `T`. -/
@[kb "axler2024" "5.75, p. 194"]
theorem axler_5_75 (S T : End K V) (h : Commute S T) (l : K) :
    ∀ v ∈ S.eigenspace l, T v ∈ S.eigenspace l := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have : S (T v) = T (S v) := by
    have := LinearMap.congr_fun h.eq v
    simpa using this
  rw [this, hv, map_smul]

end UndergradKB.LinearAlgebra.Course
