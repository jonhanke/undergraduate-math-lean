import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Dual
import UndergradKB.Common.Attr

/-! # Bilinear forms and quadratic forms (Axler, section 9A)

Rows LA-516, 517, 520, 522, 523, 524.  Bilinear forms are Mathlib's `LinearMap.BilinForm K V`.
Over a general field `K` we assume `Invertible (2 : K)` where the book uses `ℝ` or `ℂ` and divides by `2`.
A *quadratic form* in the book's sense (Axler 9.18) is a function `q : V → K` of the form
`q v = β v v` for some bilinear form `β`; this is the bridging definition `IsQuadraticForm`
(Mathlib's `QuadraticForm` is the same notion once `2` is invertible, but with a different definition).
-/

open Module
open LinearMap (BilinForm)
open scoped RealInnerProductSpace

namespace UndergradKB.LinearAlgebra

/-! ### Symmetric bilinear forms are diagonalizable -/

section Diagonalizable

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Equivalent conditions for a bilinear form to be symmetric: symmetric matrix in every basis,
in some basis, or diagonal matrix in some basis. -/
@[kb "axler2024" "9.12, p. 355"]
theorem axler_9_12 [Invertible (2 : K)] (B : BilinForm K V) :
    List.TFAE [B.IsSymm,
      ∀ b : Basis (Fin (finrank K V)) K V, (LinearMap.BilinForm.toMatrix b B).IsSymm,
      ∃ b : Basis (Fin (finrank K V)) K V, (LinearMap.BilinForm.toMatrix b B).IsSymm,
      ∃ b : Basis (Fin (finrank K V)) K V, (LinearMap.BilinForm.toMatrix b B).IsDiag] := by
  tfae_have 1 → 2 := fun h b => (LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm b).2 h
  tfae_have 2 → 3 := fun h => ⟨Module.finBasis K V, h _⟩
  tfae_have 3 → 1 := fun ⟨b, h⟩ => (LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm b).1 h
  tfae_have 1 → 4 := by
    intro h
    obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
      (LinearMap.BilinForm.isSymm_iff.1 h)
    refine ⟨v, fun i j hij => ?_⟩
    show (LinearMap.BilinForm.toMatrix v) B i j = 0
    rw [LinearMap.BilinForm.toMatrix_apply]
    exact hv hij
  tfae_have 4 → 3 := fun ⟨b, h⟩ => ⟨b, h.isSymm⟩
  tfae_finish

end Diagonalizable

/-! ### Orthonormal diagonalization over a real inner product space -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A symmetric bilinear form on a finite-dimensional real inner product space is diagonal in an
orthonormal basis (the form is represented by a self-adjoint operator, then the spectral theorem). -/
theorem exists_orthonormal_basis_orthogonal {B : BilinForm ℝ E} (hB : B.IsSymm) :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E, ∀ i j, i ≠ j → B (b i) (b j) = 0 := by
  let T : E →ₗ[ℝ] E :=
    { toFun := fun x => (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (B x))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  have hT : ∀ x y, ⟪T x, y⟫ = B x y := fun x y => by
    simp [T, InnerProductSpace.toDual_symm_apply]
  have hsymm : T.IsSymmetric := fun x y => by
    rw [hT, real_inner_comm, hT, hB.eq]
  refine ⟨hsymm.eigenvectorBasis rfl, fun i j hij => ?_⟩
  rw [← hT, hsymm.apply_eigenvectorBasis, inner_smul_left]
  have := (hsymm.eigenvectorBasis rfl).orthonormal.2 hij
  simp [this]

/-- Real symmetric bilinear forms have a diagonal matrix in some orthonormal basis. -/
@[kb "axler2024" "9.13, p. 357"]
theorem axler_9_13 {B : BilinForm ℝ E} (hB : B.IsSymm) :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E,
      (LinearMap.BilinForm.toMatrix b.toBasis B).IsDiag := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis_orthogonal hB
  exact ⟨b, fun i j hij => by simpa using hb i j hij⟩

end Real

/-! ### Symmetric plus alternating forms -/

section SymAlt

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

/-- The subspace of symmetric bilinear forms (Axler's `V_sym^(2)`). -/
def symmForms : Submodule K (BilinForm K V) where
  carrier := {B | B.IsSymm}
  add_mem' := fun ha hb => LinearMap.BilinForm.IsSymm.add ha hb
  zero_mem' := LinearMap.BilinForm.isSymm_zero
  smul_mem' := fun c _ hB => LinearMap.BilinForm.IsSymm.smul c hB

/-- The subspace of alternating bilinear forms (Axler's `V_alt^(2)`). -/
def altForms : Submodule K (BilinForm K V) where
  carrier := {B | B.IsAlt}
  add_mem' := fun ha hb => LinearMap.BilinForm.IsAlt.add ha hb
  zero_mem' := LinearMap.BilinForm.isAlt_zero
  smul_mem' := fun c _ hB => LinearMap.BilinForm.IsAlt.smul c hB

/-- Bilinear forms are the direct sum of the symmetric and the alternating ones
(complementary subspaces) when `2` is invertible. -/
@[kb "axler2024" "9.17, p. 358"]
theorem axler_9_17 [Invertible (2 : K)] : IsCompl (symmForms K V) (altForms K V) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  constructor
  · rw [Submodule.disjoint_def]
    intro B hs ha
    ext x y
    have e1 : B x y = B y x := (hs : B.IsSymm).eq x y
    have e2 : -B x y = B y x := (ha : B.IsAlt).neg_eq x y
    have : (2 : K) * B x y = 0 := by rw [two_mul]; nth_rewrite 2 [e1]; rw [← e2]; ring
    simpa [h2] using this
  · rw [codisjoint_iff, eq_top_iff]
    intro B _
    have hsum : B = (⅟2 : K) • (B + LinearMap.flip B) + (⅟2 : K) • (B - LinearMap.flip B) := by
      ext x y
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
        LinearMap.flip_apply, smul_eq_mul]
      have : (⅟2 : K) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
      linear_combination (-(B x y)) * this
    rw [hsum]
    have h1 : (⅟2 : K) • (B + LinearMap.flip B) ∈ symmForms K V :=
      LinearMap.BilinForm.IsSymm.smul _ ⟨fun x y => by simp [add_comm]⟩
    have h2 : (⅟2 : K) • (B - LinearMap.flip B) ∈ altForms K V :=
      LinearMap.BilinForm.IsAlt.smul _ (fun x => by simp)
    exact Submodule.add_mem_sup h1 h2

end SymAlt

/-! ### Quadratic forms -/

section Quadratic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Axler's notion of a quadratic form on `V` (9.18): a function of the form `v ↦ β v v` for some
bilinear form `β`. -/
def IsQuadraticForm (q : V → K) : Prop := ∃ β : BilinForm K V, ∀ v, q v = β v v

/-- A function on `Kⁿ` is a quadratic form iff it is a homogeneous quadratic polynomial
`∑ⱼ ∑ₖ Aⱼₖ xⱼ xₖ`. -/
@[kb "axler2024" "9.20, p. 359"]
theorem axler_9_20 {n : Type*} [Fintype n] [DecidableEq n] (q : (n → K) → K) :
    IsQuadraticForm q ↔ ∃ A : Matrix n n K, ∀ x, q x = ∑ j, ∑ k, A j k * x j * x k := by
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨LinearMap.BilinForm.toMatrix' β, fun x => ?_⟩
    have h1 : β x x = Matrix.toBilin' (LinearMap.BilinForm.toMatrix' β) x x := by
      rw [Matrix.toBilin'_toMatrix']
    rw [hβ, h1, Matrix.toBilin'_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rintro ⟨A, hA⟩
    refine ⟨Matrix.toBilin' A, fun x => ?_⟩
    rw [hA, Matrix.toBilin'_apply]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- A quadratic form comes from a symmetric bilinear form (replace `β` by `(β + βᵀ)/2`). -/
theorem symm_of_isQuadraticForm [Invertible (2 : K)] {q : V → K} (hq : IsQuadraticForm q) :
    ∃ ρ : BilinForm K V, ρ.IsSymm ∧ ∀ v, q v = ρ v v := by
  obtain ⟨β, hβ⟩ := hq
  have hhalf : (⅟2 : K) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  refine ⟨(⅟2 : K) • (β + LinearMap.flip β), ⟨fun x y => by simp [add_comm]⟩, fun v => ?_⟩
  simp only [hβ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul]
  linear_combination (-(β v v)) * hhalf

/-- Characterization of quadratic forms: (a) `q` is quadratic; (b) `q` comes from a unique symmetric
bilinear form; (c) `q` is homogeneous of degree 2 and its polarization is a symmetric bilinear form;
(d) the same with only `q (2 v) = 4 q v`. -/
@[kb "axler2024" "9.21, p. 360"]
theorem axler_9_21 [Invertible (2 : K)] (q : V → K) :
    List.TFAE [IsQuadraticForm q,
      ∃! ρ : BilinForm K V, ρ.IsSymm ∧ ∀ v, q v = ρ v v,
      (∀ (c : K) v, q (c • v) = c ^ 2 * q v) ∧
        ∃ ρ : BilinForm K V, ρ.IsSymm ∧ ∀ u w, ρ u w = q (u + w) - q u - q w,
      (∀ v, q ((2 : K) • v) = 4 * q v) ∧
        ∃ ρ : BilinForm K V, ρ.IsSymm ∧ ∀ u w, ρ u w = q (u + w) - q u - q w] := by
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  have hhalf : (⅟2 : K) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  tfae_have 1 → 2 := by
    rintro ⟨β, hβ⟩
    refine ⟨(⅟2 : K) • (β + LinearMap.flip β), ⟨⟨fun x y => by simp [add_comm]⟩, fun v => ?_⟩, ?_⟩
    · simp only [hβ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul]
      linear_combination (-(β v v)) * hhalf
    · rintro ρ' ⟨hρ', hq⟩
      refine LinearMap.BilinForm.ext_of_isSymm hρ' ⟨fun x y => by simp [add_comm]⟩ fun v => ?_
      simp only [← hq, hβ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply,
        smul_eq_mul]
      linear_combination (-(β v v)) * hhalf
  tfae_have 2 → 3 := by
    rintro ⟨ρ, ⟨hs, hq⟩, -⟩
    refine ⟨fun c v => by simp [hq, mul_assoc, pow_two], (2 : K) • ρ, hs.smul _, fun u w => ?_⟩
    simp only [hq, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hs.eq w u]
    ring
  tfae_have 3 → 4 := by
    rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, h2⟩
    rw [h1]
    norm_num
  tfae_have 4 → 1 := by
    rintro ⟨h1, ρ, hs, hρ⟩
    refine ⟨(⅟2 : K) • ρ, fun v => ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul, hρ]
    have := h1 v
    rw [← two_smul K v, this]
    have e : (2 : K) * ⅟2 = 1 := mul_invOf_self 2
    linear_combination (-(q v)) * e
  tfae_finish

end Quadratic

/-! ### Quadratic forms on real inner product spaces -/

section RealQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every quadratic form on a finite-dimensional real inner product space is
`∑ λₖ xₖ²` in the coordinates of some orthonormal basis. -/
@[kb "axler2024" "9.23, p. 361"]
theorem axler_9_23 (q : E → ℝ) (hq : IsQuadraticForm q) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) (l : Fin (finrank ℝ E) → ℝ),
      ∀ x : Fin (finrank ℝ E) → ℝ, q (∑ k, x k • b k) = ∑ k, l k * x k ^ 2 := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨ρ, hs, hρ⟩ := symm_of_isQuadraticForm hq
  obtain ⟨b, hb⟩ := exists_orthonormal_basis_orthogonal hs
  refine ⟨b, fun k => ρ (b k) (b k), fun x => ?_⟩
  rw [hρ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hj
    rw [hb j i hj]
    ring
  · simp

end RealQuadratic

end UndergradKB.LinearAlgebra
