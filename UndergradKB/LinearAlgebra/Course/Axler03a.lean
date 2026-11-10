import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Basis.VectorSpace
import UndergradKB.Common.Attr

/-!
# Axler, Chapter 3A to 3D (linear maps, matrices, invertibility): book-named wrappers
-/

namespace UndergradKB.LinearAlgebra.Course

open UndergradKB Module Submodule

variable {K : Type*} [Field K] {U V W X : Type*}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
  [Module K U] [Module K V] [Module K W] [Module K X]

/-! ## 3A The vector space of linear maps -/

/-- Axler 3.1: a function is a linear map iff it is additive and homogeneous. -/
@[kb "axler2024" "3.1, p. 70", kb "hefferon2020" "Three.II.1.1, p. 201"]
theorem axler_3_1 (T : V → W) :
    IsLinearMap K T ↔ (∀ u v, T (u + v) = T u + T v) ∧ (∀ (c : K) v, T (c • v) = c • T v) :=
  ⟨fun h => ⟨h.map_add, h.map_smul⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Axler 3.3: the zero map, the identity, and differentiation of polynomials are linear maps. -/
@[kb "axler2024" "3.3, p. 70", kb "hefferon2020" "Three.II.1.4, p. 202",
  kb "hefferon2020" "Three.II.1.15, p. 205"]
theorem axler_3_3 :
    (∀ v : V, (0 : V →ₗ[K] W) v = 0) ∧ (∀ v : V, (LinearMap.id : V →ₗ[K] V) v = v) ∧
    (∀ p q : Polynomial K, Polynomial.derivative (p + q) =
        Polynomial.derivative p + Polynomial.derivative q) ∧
    (∀ (c : K) (p : Polynomial K), Polynomial.derivative (c • p) = c • Polynomial.derivative p) :=
  ⟨fun _ => rfl, fun _ => rfl, fun p q => map_add _ p q, fun c p => map_smul _ c p⟩

/-- Axler 3.4 (linear map lemma): for a basis `v₁,…,vₙ` of `V` and any `w₁,…,wₙ` in `W` there is
exactly one linear map `T` with `T vₖ = wₖ`. -/
@[kb "axler2024" "3.4, p. 72", kb "hefferon2020" "Three.II.1.9, p. 203",
  kb "hefferon2020" "Three.II.1.10, p. 204"]
theorem axler_3_4 {n : ℕ} (b : Basis (Fin n) K V) (w : Fin n → W) :
    ∃! T : V →ₗ[K] W, ∀ k, T (b k) = w k :=
  ⟨b.constr K w, b.constr_basis K w, fun _ hT => b.ext fun i => (hT i).trans (b.constr_basis K w i).symm⟩

/-- Axler 3.5: the sum and scalar multiple of linear maps are defined pointwise. -/
@[kb "axler2024" "3.5, p. 73"]
theorem axler_3_5 (S T : V →ₗ[K] W) (c : K) (v : V) :
    (S + T) v = S v + T v ∧ (c • T) v = c • T v :=
  ⟨rfl, rfl⟩

/-- Axler 3.6: `𝓛(V, W)` is a vector space under the pointwise operations. -/
@[kb "axler2024" "3.6, p. 73", kb "hefferon2020" "Three.II.1.17, p. 205"]
theorem axler_3_6 : Nonempty (Module K (V →ₗ[K] W)) := ⟨inferInstance⟩

/-- Axler 3.7: the product `S T` of linear maps is the composition. -/
@[kb "axler2024" "3.7, p. 73", kb "hefferon2020" "Three.IV.2.1, p. 246"]
theorem axler_3_7 (T : U →ₗ[K] V) (S : V →ₗ[K] W) (u : U) (A B : Module.End K V) (v : V) :
    (S ∘ₗ T) u = S (T u) ∧ (A * B) v = A (B v) :=
  ⟨rfl, rfl⟩

/-- Axler 3.8: associativity, identity and distributivity of products of linear maps. -/
@[kb "axler2024" "3.8, p. 74"]
theorem axler_3_8 :
    (∀ (T₁ : U →ₗ[K] V) (T₂ : V →ₗ[K] W) (T₃ : W →ₗ[K] X),
        (T₃ ∘ₗ T₂) ∘ₗ T₁ = T₃ ∘ₗ (T₂ ∘ₗ T₁)) ∧
    (∀ T : V →ₗ[K] W, T ∘ₗ LinearMap.id = T ∧ LinearMap.id ∘ₗ T = T) ∧
    (∀ (S₁ S₂ : V →ₗ[K] W) (T : U →ₗ[K] V), (S₁ + S₂) ∘ₗ T = S₁ ∘ₗ T + S₂ ∘ₗ T) ∧
    (∀ (S : W →ₗ[K] X) (T₁ T₂ : V →ₗ[K] W), S ∘ₗ (T₁ + T₂) = S ∘ₗ T₁ + S ∘ₗ T₂) :=
  ⟨fun _ _ _ => LinearMap.comp_assoc _ _ _, fun T => ⟨LinearMap.comp_id T, LinearMap.id_comp T⟩,
    fun _ _ _ => LinearMap.add_comp _ _ _, fun _ _ _ => LinearMap.comp_add _ _ _⟩

/-- Axler 3.10: a linear map takes `0` to `0`. -/
@[kb "axler2024" "3.10, p. 74", kb "hefferon2020" "Three.I.1.10, p. 189",
  kb "hefferon2020" "Three.II.1.6, p. 203"]
theorem axler_3_10 (T : V →ₗ[K] W) : T 0 = 0 := map_zero T

/-- Axler Exercise 3A.13: a linear map on a subspace extends to a linear map on the whole space. -/
@[kb "axler2024" "Ex3A.13, p. 76"]
theorem axler_ex3A_13 (U : Submodule K V) (S : U →ₗ[K] W) :
    ∃ T : V →ₗ[K] W, ∀ u : U, T u = S u := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend S
  exact ⟨g, fun u => LinearMap.congr_fun hg u⟩

/-! ## 3B Null spaces and ranges -/

/-- Axler 3.11: the null space of `T` is `{v : T v = 0}`. -/
@[kb "axler2024" "3.11, p. 77"]
theorem axler_3_11 (T : V →ₗ[K] W) (v : V) : v ∈ LinearMap.ker T ↔ T v = 0 :=
  LinearMap.mem_ker

/-- Axler 3.13: the null space is a subspace (more generally the inverse image of a subspace). -/
@[kb "axler2024" "3.13, p. 77", kb "hefferon2020" "Three.II.2.10, p. 214"]
theorem axler_3_13 (T : V →ₗ[K] W) :
    (∃ N : Submodule K V, (N : Set V) = {v | T v = 0}) ∧
    ∀ P : Submodule K W, ∃ N : Submodule K V, (N : Set V) = T ⁻¹' P :=
  ⟨⟨LinearMap.ker T, by ext; simp⟩, fun P => ⟨P.comap T, rfl⟩⟩

/-- Axler 3.14: injective means equal images force equal inputs. -/
@[kb "axler2024" "3.14, p. 78"]
theorem axler_3_14 (T : V →ₗ[K] W) : Function.Injective T ↔ ∀ u v, T u = T v → u = v :=
  Iff.rfl

/-- Axler 3.15: a linear map is injective iff its null space is `{0}`. -/
@[kb "axler2024" "3.15, p. 78"]
theorem axler_3_15 (T : V →ₗ[K] W) : Function.Injective T ↔ LinearMap.ker T = ⊥ :=
  LinearMap.ker_eq_bot.symm

/-- Axler 3.16: the range of `T` is `{T v : v ∈ V}`. -/
@[kb "axler2024" "3.16, p. 79"]
theorem axler_3_16 (T : V →ₗ[K] W) (w : W) : w ∈ LinearMap.range T ↔ ∃ v, T v = w :=
  LinearMap.mem_range

/-- Axler 3.18: the range is a subspace (more generally the image of a subspace). -/
@[kb "axler2024" "3.18, p. 79", kb "hefferon2020" "Three.II.2.1, p. 210"]
theorem axler_3_18 (T : V →ₗ[K] W) :
    (∃ R : Submodule K W, (R : Set W) = Set.range T) ∧
    ∀ P : Submodule K V, ∃ R : Submodule K W, (R : Set W) = T '' P :=
  ⟨⟨LinearMap.range T, LinearMap.coe_range T⟩, fun P => ⟨P.map T, rfl⟩⟩

/-- Axler 3.19: a linear map is surjective iff its range is the whole codomain. -/
@[kb "axler2024" "3.19, p. 80"]
theorem axler_3_19 (T : V →ₗ[K] W) : Function.Surjective T ↔ LinearMap.range T = ⊤ :=
  LinearMap.range_eq_top.symm

/-- Axler 3.21 (fundamental theorem of linear maps): `dim V = dim null T + dim range T`. -/
@[kb "axler2024" "3.21, p. 80", kb "hefferon2020" "Two.III.3.13, p. 150",
  kb "hefferon2020" "Three.II.2.14, p. 215"]
theorem axler_3_21 [FiniteDimensional K V] (T : V →ₗ[K] W) :
    finrank K V = finrank K (LinearMap.ker T) + finrank K (LinearMap.range T) :=
  (LinearMap.finrank_range_add_finrank_ker T).symm.trans (add_comm _ _)

/-- Axler 3.22: a linear map to a lower-dimensional space is not injective. -/
@[kb "axler2024" "3.22, p. 81"]
theorem axler_3_22 [FiniteDimensional K V] [FiniteDimensional K W] (h : finrank K W < finrank K V)
    (T : V →ₗ[K] W) : ¬ Function.Injective T :=
  fun hT => absurd (LinearMap.finrank_le_finrank_of_injective hT) (not_le.mpr h)

/-- Axler 3.24: a linear map to a higher-dimensional space is not surjective. -/
@[kb "axler2024" "3.24, p. 82"]
theorem axler_3_24 [FiniteDimensional K V] [FiniteDimensional K W] (h : finrank K V < finrank K W)
    (T : V →ₗ[K] W) : ¬ Function.Surjective T :=
  fun hT => absurd (LinearMap.finrank_le_finrank_of_surjective hT) (not_le.mpr h)

/-! ## 3C Matrices -/

/-- Axler 3.29: an `m`-by-`n` matrix over `F` is determined by its entries `A j k`. -/
@[kb "axler2024" "3.29, p. 87", kb "hefferon2020" "One.I.2.6, p. 25"]
theorem axler_3_29 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K) (h : ∀ j k, A j k = B j k) :
    A = B :=
  Matrix.ext h

/-- Axler 3.31: column `k` of the matrix of `T` holds the coordinates of `T vₖ`. -/
@[kb "axler2024" "3.31, p. 87", kb "hefferon2020" "Three.III.1.2, p. 224"]
theorem axler_3_31 {n m : ℕ} (v : Basis (Fin n) K V) (w : Basis (Fin m) K W) (T : V →ₗ[K] W)
    (j : Fin m) (k : Fin n) : LinearMap.toMatrix v w T j k = w.repr (T (v k)) j :=
  LinearMap.toMatrix_apply v w T j k

/-- Axler Exercise 3A.3: every linear map `Fⁿ → Fᵐ` is given by a matrix. -/
@[kb "axler2024" "Ex3A.3, p. 75", kb "hefferon2020" "Three.III.2.u1, p. 235"]
theorem axler_ex3A_3 {n m : ℕ} (T : (Fin n → K) →ₗ[K] (Fin m → K)) :
    ∃ A : Matrix (Fin m) (Fin n) K, ∀ x, T x = A.mulVec x :=
  ⟨LinearMap.toMatrix' T, fun x => by
    simp⟩

/-- Axler 3.34 and 3.36: matrix addition and scalar multiplication are entrywise. -/
@[kb "axler2024" "3.34, p. 89", kb "axler2024" "3.36, p. 89",
  kb "hefferon2020" "Two.I.1.9, p. 99", kb "hefferon2020" "Three.IV.1.3, p. 243"]
theorem axler_3_34 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) K) (c : K) (j : Fin m) (k : Fin n) :
    (A + B) j k = A j k + B j k ∧ (c • A) j k = c * A j k :=
  ⟨rfl, rfl⟩

/-- Axler 3.35 and 3.38: the matrix of a sum or scalar multiple of linear maps is the sum or scalar
multiple of the matrices. -/
@[kb "axler2024" "3.35, p. 89", kb "axler2024" "3.38, p. 90",
  kb "hefferon2020" "Three.IV.1.4, p. 244"]
theorem axler_3_35 {n m : ℕ} (v : Basis (Fin n) K V) (w : Basis (Fin m) K W) (S T : V →ₗ[K] W)
    (c : K) :
    LinearMap.toMatrix v w (S + T) = LinearMap.toMatrix v w S + LinearMap.toMatrix v w T ∧
    LinearMap.toMatrix v w (c • T) = c • LinearMap.toMatrix v w T :=
  ⟨map_add _ S T, map_smul _ c T⟩

/-- Axler 3.40: the space of `m`-by-`n` matrices has dimension `m n`. -/
@[kb "axler2024" "3.40, p. 90"]
theorem axler_3_40 (m n : ℕ) : finrank K (Matrix (Fin m) (Fin n) K) = m * n := by
  simp [Module.finrank_matrix]

/-- Axler 3.41: the entries of a matrix product. -/
@[kb "axler2024" "3.41, p. 91", kb "hefferon2020" "Three.IV.2.3, p. 247"]
theorem axler_3_41 {m n p : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (j : Fin m) (k : Fin p) : (A * B) j k = ∑ r, A j r * B r k :=
  Matrix.mul_apply

/-- Axler 3.43: the matrix of a composite is the product of the matrices. -/
@[kb "axler2024" "3.43, p. 92", kb "hefferon2020" "Three.IV.2.7, p. 248"]
theorem axler_3_43 {n m p : ℕ} (u : Basis (Fin n) K U) (v : Basis (Fin m) K V)
    (w : Basis (Fin p) K W) (S : V →ₗ[K] W) (T : U →ₗ[K] V) :
    LinearMap.toMatrix u w (S ∘ₗ T) = LinearMap.toMatrix v w S * LinearMap.toMatrix u v T :=
  LinearMap.toMatrix_comp u v w S T

/-- Axler 3.46 and 3.47: the `(j,k)` entry of `A B` is row `j` of `A` times column `k` of `B`. -/
@[kb "axler2024" "3.46, p. 93", kb "axler2024" "3.47, p. 93"]
theorem axler_3_46 {m n p : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (j : Fin m) (k : Fin p) :
    (A * B) j k = dotProduct (fun r => A j r) (fun r => B r k) :=
  Matrix.mul_apply'

/-- Axler 3.48: column `k` of `A B` is `A` times column `k` of `B`. -/
@[kb "axler2024" "3.48, p. 93", kb "hefferon2020" "Three.IV.3.7, p. 256"]
theorem axler_3_48 {m n p : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (k : Fin p) : (fun j => (A * B) j k) = A.mulVec (fun r => B r k) := by
  funext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Axler 3.50: a matrix times a column vector is a linear combination of the columns. -/
@[kb "axler2024" "3.50, p. 94", kb "hefferon2020" "Three.III.1.u1, p. 229"]
theorem axler_3_50 {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (c : Fin n → K) :
    A.mulVec c = ∑ k, c k • (fun j => A j k) := by
  funext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- Axler Exercises 3C.8 and 3C.9: row `j` of `A B` is (row `j` of `A`) times `B`, and a row vector
times `B` is a linear combination of the rows of `B`. -/
@[kb "axler2024" "Ex3C.8, p. 98", kb "axler2024" "Ex3C.9, p. 98"]
theorem axler_ex3C_8 {m n p : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin p) K)
    (j : Fin m) (c : Fin n → K) :
    (fun k => (A * B) j k) = Matrix.vecMul (fun r => A j r) B ∧
    Matrix.vecMul c B = ∑ r, c r • (fun k => B r k) := by
  constructor
  · funext k
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · funext k
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

/-- Axler 3.52: column rank is the dimension of the span of the columns, row rank that of the rows. -/
@[kb "axler2024" "3.52, p. 95", kb "hefferon2020" "Two.III.3.1, p. 146",
  kb "hefferon2020" "Two.III.3.6, p. 147"]
theorem axler_3_52 {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    A.rank = finrank K (span K (Set.range A.col)) ∧
    A.rank = finrank K (span K (Set.range A.row)) :=
  ⟨Matrix.rank_eq_finrank_span_cols A, Matrix.rank_eq_finrank_span_row A⟩

/-- Axler 3.54: the transpose has entries `(Aᵗ)ₖ,ⱼ = Aⱼ,ₖ`. -/
@[kb "axler2024" "3.54, p. 95", kb "hefferon2020" "Two.III.3.8, p. 148"]
theorem axler_3_54 {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (j : Fin m) (k : Fin n) :
    A.transpose k j = A j k :=
  rfl

/-- Axler 3.57: column rank equals row rank. -/
@[kb "axler2024" "3.57, p. 96", kb "hefferon2020" "Two.III.3.11, p. 150"]
theorem axler_3_57 {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    finrank K (span K (Set.range A.col)) = finrank K (span K (Set.range A.row)) := by
  rw [← Matrix.rank_eq_finrank_span_cols, ← Matrix.rank_eq_finrank_span_row]

/-- Axler 3.58: the rank of a matrix is its column rank. -/
@[kb "axler2024" "3.58, p. 97", kb "hefferon2020" "Two.III.3.12, p. 150"]
theorem axler_3_58 {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    A.rank = finrank K (span K (Set.range A.col)) :=
  Matrix.rank_eq_finrank_span_cols A

/-! ## 3D Invertibility and isomorphisms -/

/-- Axler 3.59: a linear map is invertible (has a two-sided linear inverse) iff it is a linear
equivalence. -/
@[kb "axler2024" "3.59, p. 100"]
theorem axler_3_59 (T : V →ₗ[K] W) :
    (∃ S : W →ₗ[K] V, S ∘ₗ T = LinearMap.id ∧ T ∘ₗ S = LinearMap.id) ↔
      ∃ e : V ≃ₗ[K] W, e.toLinearMap = T := by
  constructor
  · rintro ⟨S, h1, h2⟩
    exact ⟨LinearEquiv.ofLinearMap T S h2 h1, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e.symm.toLinearMap, by ext; simp, by ext; simp⟩

/-- Axler 3.63: a linear map is invertible iff it is injective and surjective. -/
@[kb "axler2024" "3.63, p. 101"]
theorem axler_3_63 (T : V →ₗ[K] W) :
    (∃ S : W →ₗ[K] V, S ∘ₗ T = LinearMap.id ∧ T ∘ₗ S = LinearMap.id) ↔ Function.Bijective T := by
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := (axler_3_59 T).mp h
    exact e.bijective
  · intro h
    exact (axler_3_59 T).mpr ⟨LinearEquiv.ofBijective T h, rfl⟩

/-- Axler 3.65: for finite-dimensional spaces of equal dimension, a linear map is invertible iff
it is injective iff it is surjective. -/
@[kb "axler2024" "3.65, p. 102"]
theorem axler_3_65 [FiniteDimensional K V] [FiniteDimensional K W]
    (h : finrank K V = finrank K W) (T : V →ₗ[K] W) :
    ((∃ S : W →ₗ[K] V, S ∘ₗ T = LinearMap.id ∧ T ∘ₗ S = LinearMap.id) ↔ Function.Injective T) ∧
    (Function.Injective T ↔ Function.Surjective T) := by
  have hs := LinearMap.injective_iff_surjective_of_finrank_eq_finrank h (f := T)
  refine ⟨?_, hs⟩
  rw [axler_3_63]
  exact ⟨fun hb => hb.1, fun hi => ⟨hi, hs.mp hi⟩⟩

/-- Axler Exercise 3D.11: for operators `S`, `T` on a finite-dimensional space, `S T` is invertible
iff both `S` and `T` are. -/
@[kb "axler2024" "3D.11, p. 112"]
theorem axler_ex3D_11 [FiniteDimensional K V] (S T : Module.End K V) :
    IsUnit (S * T) ↔ IsUnit S ∧ IsUnit T :=
  IsUnit.mul_iff

end UndergradKB.LinearAlgebra.Course
