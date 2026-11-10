import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import UndergradKB.Common.Attr

/-!
# Axler, Chapter 3E to 3F (isomorphisms, products, quotients, duality): book-named wrappers
-/

namespace UndergradKB.LinearAlgebra.Course

open UndergradKB Module Submodule

variable {K : Type*} [Field K] {U V W X : Type*}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
  [Module K U] [Module K V] [Module K W] [Module K X]

/-! ## 3D (continued) Isomorphisms -/

/-- Axler 3.69: two spaces are isomorphic iff there is an invertible linear map between them. -/
@[kb "axler2024" "3.69, p. 104", kb "hefferon2020" "Three.I.1.3, p. 185"]
theorem axler_3_69 : Nonempty (V ≃ₗ[K] W) ↔ ∃ T : V →ₗ[K] W, Function.Bijective T :=
  ⟨fun ⟨e⟩ => ⟨e.toLinearMap, e.bijective⟩, fun ⟨T, h⟩ => ⟨LinearEquiv.ofBijective T h⟩⟩

/-- Axler 3.70: finite-dimensional spaces are isomorphic iff they have the same dimension. -/
@[kb "axler2024" "3.70, p. 104", kb "hefferon2020" "Three.I.2.3, p. 195",
  kb "hefferon2020" "Three.I.2.4, p. 195"]
theorem axler_3_70 [FiniteDimensional K V] [FiniteDimensional K W] :
    Nonempty (V ≃ₗ[K] W) ↔ finrank K V = finrank K W :=
  FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq

/-- Axler 3.71: after fixing bases, `𝓜` is an isomorphism from `𝓛(V, W)` onto the matrices. -/
@[kb "axler2024" "3.71, p. 105", kb "hefferon2020" "Three.III.2.2, p. 234"]
theorem axler_3_71 {n m : ℕ} (v : Basis (Fin n) K V) (w : Basis (Fin m) K W) :
    ∃ e : (V →ₗ[K] W) ≃ₗ[K] Matrix (Fin m) (Fin n) K, ∀ T, e T = LinearMap.toMatrix v w T :=
  ⟨LinearMap.toMatrix v w, fun _ => rfl⟩

/-- Axler 3.72: `dim 𝓛(V, W) = (dim V)(dim W)`. -/
@[kb "axler2024" "3.72, p. 105"]
theorem axler_3_72 [FiniteDimensional K V] [FiniteDimensional K W] :
    finrank K (V →ₗ[K] W) = finrank K V * finrank K W := by
  simp [Module.finrank_linearMap]

/-- Axler 3.73: the matrix of a vector is the column of its coordinates, and the vector is recovered
from it. -/
@[kb "axler2024" "3.73, p. 106", kb "hefferon2020" "Two.III.1.13, p. 134"]
theorem axler_3_73 {n : ℕ} (b : Basis (Fin n) K V) (v : V) (k : Fin n) :
    b.equivFun v k = b.repr v k ∧ v = ∑ j, b.equivFun v j • b j :=
  ⟨rfl, (b.sum_equivFun v).symm⟩

/-- Axler 3.75: column `k` of `𝓜(T)` is `𝓜(T vₖ)`. -/
@[kb "axler2024" "3.75, p. 107"]
theorem axler_3_75 {n m : ℕ} (v : Basis (Fin n) K V) (w : Basis (Fin m) K W) (T : V →ₗ[K] W)
    (k : Fin n) : (fun j => LinearMap.toMatrix v w T j k) = w.equivFun (T (v k)) := by
  funext j
  simp [LinearMap.toMatrix_apply]

/-- Axler 3.76: `𝓜(T v) = 𝓜(T) 𝓜(v)`. -/
@[kb "axler2024" "3.76, p. 107", kb "hefferon2020" "Three.III.1.5, p. 225"]
theorem axler_3_76 {n m : ℕ} (v : Basis (Fin n) K V) (w : Basis (Fin m) K W) (T : V →ₗ[K] W)
    (x : V) : (LinearMap.toMatrix v w T).mulVec (v.equivFun x) = w.equivFun (T x) :=
  LinearMap.toMatrix_mulVec_repr v w T x

/-- Axler 3.78: `dim range T` equals the column rank of `𝓜(T)`. -/
@[kb "axler2024" "3.78, p. 108", kb "hefferon2020" "Three.III.2.4, p. 235"]
theorem axler_3_78 {n m : ℕ} (v : Basis (Fin n) K V) (w : Basis (Fin m) K W) (T : V →ₗ[K] W) :
    finrank K (LinearMap.range T) = (LinearMap.toMatrix v w T).rank := by
  rw [Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix v w T) w v, Matrix.toLin_toMatrix]

/-- Axler 3.79: the identity matrix has `1` on the diagonal and `0` elsewhere, and is the matrix of
the identity operator in every basis. -/
@[kb "axler2024" "3.79, p. 108", kb "hefferon2020" "Three.IV.3.9, p. 257",
  kb "hefferon2020" "Three.IV.3.11, p. 258"]
theorem axler_3_79 {n : ℕ} (v : Basis (Fin n) K V) :
    (∀ j k : Fin n, (1 : Matrix (Fin n) (Fin n) K) j k = if j = k then 1 else 0) ∧
    LinearMap.toMatrix v v LinearMap.id = 1 :=
  ⟨fun _ _ => Matrix.one_apply, LinearMap.toMatrix_id v⟩

/-- Axler 3.80: a square matrix is invertible if it has a two-sided inverse; `(A⁻¹)⁻¹ = A` and
`(A C)⁻¹ = C⁻¹ A⁻¹`. -/
@[kb "axler2024" "3.80, p. 109", kb "hefferon2020" "Three.IV.4.1, p. 265",
  kb "hefferon2020" "Three.IV.4.4, p. 266"]
theorem axler_3_80 {n : ℕ} (A C : Matrix (Fin n) (Fin n) K) :
    (IsUnit A ↔ ∃ B : Matrix (Fin n) (Fin n) K, A * B = 1 ∧ B * A = 1) ∧
    (IsUnit A → A⁻¹⁻¹ = A) ∧ (A * C)⁻¹ = C⁻¹ * A⁻¹ :=
  ⟨isUnit_iff_exists, fun h => Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp h),
    Matrix.mul_inv_rev A C⟩

/-- Axler 3.81: the matrix of a composite is the product of the matrices. -/
@[kb "axler2024" "3.81, p. 109"]
theorem axler_3_81 {n m p : ℕ} (u : Basis (Fin n) K U) (v : Basis (Fin m) K V)
    (w : Basis (Fin p) K W) (S : V →ₗ[K] W) (T : U →ₗ[K] V) :
    LinearMap.toMatrix u w (S ∘ₗ T) = LinearMap.toMatrix v w S * LinearMap.toMatrix u v T :=
  LinearMap.toMatrix_comp u v w S T

/-- Axler 3.82: the matrices of the identity between two bases are invertible, each the inverse of
the other. -/
@[kb "axler2024" "3.82, p. 110"]
theorem axler_3_82 {n : ℕ} (u u' : Basis (Fin n) K V) :
    LinearMap.toMatrix u u' LinearMap.id * LinearMap.toMatrix u' u LinearMap.id = 1 ∧
    LinearMap.toMatrix u' u LinearMap.id * LinearMap.toMatrix u u' LinearMap.id = 1 := by
  rw [LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.toMatrix_id_eq_basis_toMatrix]
  exact ⟨u'.toMatrix_mul_toMatrix_flip u, u.toMatrix_mul_toMatrix_flip u'⟩

/-- Axler 3.84 (change of basis): `A = C⁻¹ B C`, with `C` the matrix of the identity from the new
basis to the old one. -/
@[kb "axler2024" "3.84, p. 111", kb "hefferon2020" "Three.V.2.1, p. 277",
  kb "hefferon2020" "Five.II.intro, p. 412"]
theorem axler_3_84 {n : ℕ} (u u' : Basis (Fin n) K V) (T : V →ₗ[K] V) :
    LinearMap.toMatrix u' u' T =
      (u.toMatrix u')⁻¹ * LinearMap.toMatrix u u T * u.toMatrix u' := by
  rw [Matrix.inv_eq_right_inv (u.toMatrix_mul_toMatrix_flip u')]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix u' u u' u T).symm

/-! ## 3E Products and quotients -/

/-- Axler 3.87 and 3.89: products of vector spaces are vector spaces with componentwise
operations. -/
@[kb "axler2024" "3.87, p. 114", kb "axler2024" "3.89, p. 114"]
theorem axler_3_87 {m : ℕ} {E : Fin m → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)] :
    Nonempty (Module K (V × W)) ∧ Nonempty (Module K (∀ i, E i)) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- Axler 3.92: the dimension of a finite product is the sum of the dimensions. -/
@[kb "axler2024" "3.92, p. 115"]
theorem axler_3_92 {m : ℕ} {E : Fin m → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] :
    finrank K (∀ i, E i) = ∑ i, finrank K (E i) :=
  Module.finrank_pi_fintype K

/-- Axler 3.99: the quotient `V/U` consists of the translates `v + U`; `v + U = w + U` iff
`v - w ∈ U`. -/
@[kb "axler2024" "3.99, p. 117"]
theorem axler_3_99 (U : Submodule K V) (v w : V) :
    (Submodule.Quotient.mk v : V ⧸ U) = Submodule.Quotient.mk w ↔ v - w ∈ U :=
  Submodule.Quotient.eq U

/-- Axler 3.102 and 3.103: the operations on `V/U` are well defined: they act on representatives. -/
@[kb "axler2024" "3.102, p. 118", kb "axler2024" "3.103, p. 119"]
theorem axler_3_102 (U : Submodule K V) (v w : V) (c : K) :
    ((Submodule.Quotient.mk v : V ⧸ U) + Submodule.Quotient.mk w = Submodule.Quotient.mk (v + w)) ∧
    (c • (Submodule.Quotient.mk v : V ⧸ U) = Submodule.Quotient.mk (c • v)) :=
  ⟨rfl, rfl⟩

/-- Axler 3.104: the quotient map `π : V → V/U`, `v ↦ v + U`, is linear. -/
@[kb "axler2024" "3.104, p. 119"]
theorem axler_3_104 (U : Submodule K V) :
    ∃ π : V →ₗ[K] V ⧸ U, ∀ v, π v = Submodule.Quotient.mk v :=
  ⟨U.mkQ, fun _ => rfl⟩

/-- Axler 3.105: `dim V/U = dim V - dim U`. -/
@[kb "axler2024" "3.105, p. 120"]
theorem axler_3_105 [FiniteDimensional K V] (U : Submodule K V) :
    finrank K (V ⧸ U) = finrank K V - finrank K U := by
  have := Submodule.finrank_quotient_add_finrank U
  omega

/-- Axler 3.106 and 3.107: the induced map `T̃ : V / null T → W` is well defined and injective,
`T̃ ∘ π = T`, its range is `range T`, and `V / null T ≅ range T`. -/
@[kb "axler2024" "3.106, p. 120", kb "axler2024" "3.107, p. 120"]
theorem axler_3_106 (T : V →ₗ[K] W) :
    ∃ Tt : (V ⧸ LinearMap.ker T) →ₗ[K] W,
      (∀ v, Tt (Submodule.Quotient.mk v) = T v) ∧ Function.Injective Tt ∧
      Tt ∘ₗ (LinearMap.ker T).mkQ = T ∧ LinearMap.range Tt = LinearMap.range T ∧
      Nonempty ((V ⧸ LinearMap.ker T) ≃ₗ[K] LinearMap.range T) :=
  ⟨(LinearMap.ker T).liftQ T le_rfl, fun _ => rfl,
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl),
    Submodule.liftQ_mkQ _ _ _, Submodule.range_liftQ _ _ _, ⟨T.quotKerEquivRange⟩⟩

/-! ## 3F Duality -/

/-- Axler 3.108 and 3.110: a linear functional is a linear map `V → F`; the dual space is the
space of all of them. -/
@[kb "axler2024" "3.108, p. 123", kb "axler2024" "3.110, p. 123"]
theorem axler_3_108 : Module.Dual K V = (V →ₗ[K] K) := rfl

/-- Axler 3.111: `dim V' = dim V`. -/
@[kb "axler2024" "3.111, p. 123"]
theorem axler_3_111 [FiniteDimensional K V] : finrank K (Module.Dual K V) = finrank K V :=
  Subspace.dual_finrank_eq

/-- Axler 3.112: the dual basis `φ₁,…,φₙ` of a basis `v₁,…,vₙ` satisfies `φⱼ(vₖ) = δⱼₖ`. -/
@[kb "axler2024" "3.112, p. 124"]
theorem axler_3_112 {n : ℕ} (b : Basis (Fin n) K V) (j k : Fin n) :
    b.dualBasis j (b k) = if j = k then 1 else 0 := by
  rw [Basis.dualBasis_apply_self]
  simp [eq_comm]

/-- Axler 3.114: `v = φ₁(v) v₁ + ⋯ + φₙ(v) vₙ`. -/
@[kb "axler2024" "3.114, p. 124"]
theorem axler_3_114 {n : ℕ} (b : Basis (Fin n) K V) (v : V) :
    ∑ j, b.dualBasis j v • b j = v := by
  simp [Basis.dualBasis_apply]

/-- Axler 3.116: the dual basis is a basis of the dual space. -/
@[kb "axler2024" "3.116, p. 125"]
theorem axler_3_116 {n : ℕ} (b : Basis (Fin n) K V) :
    LinearIndependent K b.dualBasis ∧ span K (Set.range b.dualBasis) = ⊤ :=
  ⟨b.dualBasis.linearIndependent, b.dualBasis.span_eq⟩

/-- Axler 3.118: the dual map sends `φ` to `φ ∘ T`. -/
@[kb "axler2024" "3.118, p. 125"]
theorem axler_3_118 (T : V →ₗ[K] W) (φ : Module.Dual K W) : T.dualMap φ = φ ∘ₗ T := rfl

/-- Axler 3.120: the dual map is linear in `T` and reverses products. -/
@[kb "axler2024" "3.120, p. 126"]
theorem axler_3_120 (S T : V →ₗ[K] W) (c : K) (R : W →ₗ[K] X) :
    (S + T).dualMap = S.dualMap + T.dualMap ∧ (c • T).dualMap = c • T.dualMap ∧
    (R ∘ₗ T).dualMap = T.dualMap ∘ₗ R.dualMap := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp

/-- Axler 3.121: the annihilator `U⁰` is the set of functionals vanishing on `U`. -/
@[kb "axler2024" "3.121, p. 127"]
theorem axler_3_121 (U : Submodule K V) (φ : Module.Dual K V) :
    φ ∈ U.dualAnnihilator ↔ ∀ x ∈ U, φ x = 0 :=
  Submodule.mem_dualAnnihilator φ

/-- Axler 3.124: the annihilator is a subspace of `V'`. -/
@[kb "axler2024" "3.124, p. 128"]
theorem axler_3_124 (U : Submodule K V) :
    ∃ A : Submodule K (Module.Dual K V), (A : Set (Module.Dual K V)) = {φ | ∀ x ∈ U, φ x = 0} :=
  ⟨U.dualAnnihilator, by ext φ; simp [Submodule.mem_dualAnnihilator]⟩

/-- Axler 3.125: `dim U⁰ = dim V - dim U`. -/
@[kb "axler2024" "3.125, p. 128"]
theorem axler_3_125 [FiniteDimensional K V] (U : Subspace K V) :
    finrank K U.dualAnnihilator = finrank K V - finrank K U := by
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega

/-- Axler 3.127: `U⁰ = {0}` iff `U = V`, and `U⁰ = V'` iff `U = {0}`. -/
@[kb "axler2024" "3.127, p. 129"]
theorem axler_3_127 (U : Submodule K V) :
    (U.dualAnnihilator = ⊥ ↔ U = ⊤) ∧ (U.dualAnnihilator = ⊤ ↔ U = ⊥) :=
  ⟨Submodule.dualAnnihilator_eq_bot_iff, Submodule.dualAnnihilator_eq_top_iff⟩

/-- Axler 3.129: `T` is surjective iff `T'` is injective. -/
@[kb "axler2024" "3.129, p. 130"]
theorem axler_3_129 (T : V →ₗ[K] W) : Function.Surjective T ↔ Function.Injective T.dualMap :=
  LinearMap.dualMap_injective_iff.symm

/-- Axler 3.130: `dim range T' = dim range T` and `range T' = (null T)⁰`. -/
@[kb "axler2024" "3.130, p. 130"]
theorem axler_3_130 (T : V →ₗ[K] W) :
    finrank K (LinearMap.range T.dualMap) = finrank K (LinearMap.range T) ∧
    LinearMap.range T.dualMap = (LinearMap.ker T).dualAnnihilator :=
  ⟨LinearMap.finrank_range_dualMap_eq_finrank_range T, LinearMap.range_dualMap_eq_dualAnnihilator_ker T⟩

/-- Axler 3.131: `T` is injective iff `T'` is surjective. -/
@[kb "axler2024" "3.131, p. 131"]
theorem axler_3_131 (T : V →ₗ[K] W) : Function.Injective T ↔ Function.Surjective T.dualMap :=
  LinearMap.dualMap_surjective_iff.symm

/-- Axler 3.132: with respect to dual bases, `𝓜(T') = 𝓜(T)ᵗ`. -/
@[kb "axler2024" "3.132, p. 131"]
theorem axler_3_132 {n m : ℕ} (v : Basis (Fin n) K V) (w : Basis (Fin m) K W) (T : V →ₗ[K] W) :
    LinearMap.toMatrix w.dualBasis v.dualBasis T.dualMap = (LinearMap.toMatrix v w T).transpose :=
  LinearMap.toMatrix_transpose T

/-- Axler 3.133: the column rank of a matrix equals its row rank. -/
@[kb "axler2024" "3.133, p. 132"]
theorem axler_3_133 {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    finrank K (span K (Set.range A.col)) = finrank K (span K (Set.range A.row)) := by
  rw [← Matrix.rank_eq_finrank_span_cols, ← Matrix.rank_eq_finrank_span_row]

end UndergradKB.LinearAlgebra.Course
