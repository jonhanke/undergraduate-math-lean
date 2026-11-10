import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 12 (part 1): orthogonal matrices

Determinant of an orthogonal matrix, the equivalent descriptions of orthogonal matrices
(Theorem 12.1.8) and the shape of the elements of `O(2)` (Example 12.1.10). Isometries, the
Euclidean group, lattices and the crystallographic restriction are in `MatrixGroups2`. -/

namespace UndergradKB.AbstractAlgebra

open Matrix

/-- AA-176. An orthogonal real matrix has determinant `1` or `-1`. -/
@[kb "judson2026" "Definition 12.1.3, p. 163"]
theorem det_orthogonal_eq_one_or_neg_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) : A.det = 1 ∨ A.det = -1 := by
  have h := (Matrix.mem_orthogonalGroup_iff' _ _).mp hA
  have h2 : A.det * A.det = 1 := by
    have := congrArg Matrix.det h
    simpa [Matrix.det_mul] using this
  exact mul_self_eq_one_iff.mp h2

/-- `toEuclideanLin A` acts on coordinates as `A *ᵥ`. -/
lemma toEuclideanLin_apply_ofLp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin A x = WithLp.toLp 2 (A *ᵥ x.ofLp) := rfl

lemma inner_euclid_eq {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = y.ofLp ⬝ᵥ x.ofLp := by
  simp [EuclideanSpace.inner_eq_star_dotProduct]

lemma dot_mulVec_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ ((Aᵀ * A) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm]

/-- The columns of `A` are orthonormal (for the dot product) iff `Aᵀ * A = 1`. -/
lemma cols_orthonormal_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ i j, Aᵀ i ⬝ᵥ Aᵀ j = if i = j then 1 else 0) ↔ Aᵀ * A = 1 := by
  constructor
  · intro h
    ext i j
    have := h i j
    simpa [Matrix.mul_apply, dotProduct, Matrix.one_apply] using this
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_apply, dotProduct, Matrix.one_apply, @eq_comm _ j i] using this

/-- AA-177. Theorem 12.1.8: for a real square matrix `A`, the following are equivalent: the
columns are orthonormal; `A⁻¹ = Aᵀ`; `A` preserves the dot product; `A` preserves (Euclidean)
distances; `A` preserves (Euclidean) lengths. -/
@[kb "judson2026" "Theorem 12.1.8, p. 163"]
theorem orthogonal_tfae {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    List.TFAE
      [ ∀ i j, Aᵀ i ⬝ᵥ Aᵀ j = if i = j then 1 else 0,
        IsUnit A.det ∧ A⁻¹ = Aᵀ,
        ∀ x y : Fin n → ℝ, (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y,
        ∀ x y : EuclideanSpace ℝ (Fin n),
          dist (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) = dist x y,
        ∀ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin A x‖ = ‖x‖ ] := by
  have key := cols_orthonormal_iff A
  tfae_have 1 → 2 := by
    intro h
    have h1 := key.mp h
    have hd : A.det * A.det = 1 := by
      have := congrArg Matrix.det h1
      simpa [Matrix.det_mul] using this
    have hu : IsUnit A.det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      rw [h0] at hd
      simp at hd
    exact ⟨hu, Matrix.inv_eq_left_inv h1 |>.symm ▸ rfl⟩
  tfae_have 2 → 3 := by
    rintro ⟨hu, hi⟩ x y
    have : Aᵀ * A = 1 := by
      rw [← hi]; exact Matrix.nonsing_inv_mul _ hu
    rw [dot_mulVec_mulVec, this]; simp
  tfae_have 3 → 1 := by
    intro h i j
    have := h (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, Pi.single_apply, dotProduct, @eq_comm _ j i] using this
  have bridge : (∀ x y : Fin n → ℝ, (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y) ↔
      ∀ x y : EuclideanSpace ℝ (Fin n),
        inner ℝ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) = inner ℝ x y := by
    constructor
    · intro h x y
      simpa [toEuclideanLin_apply_ofLp, inner_euclid_eq] using h y.ofLp x.ofLp
    · intro h x y
      have := h (WithLp.toLp 2 y) (WithLp.toLp 2 x)
      simpa [toEuclideanLin_apply_ofLp, inner_euclid_eq] using this
  tfae_have 3 → 5 := by
    intro h
    exact (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin A)).mpr (bridge.mp h)
  tfae_have 5 → 4 := by
    intro h x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, h]
  tfae_have 4 → 5 := by
    intro h x
    have := h x 0
    simpa using this
  tfae_have 5 → 3 := by
    intro h
    exact bridge.mpr ((LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin A)).mp h)
  tfae_finish

/-- A matrix whose action on `EuclideanSpace` preserves norms is orthogonal. -/
lemma mem_orthogonalGroup_of_norm_map {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin A x‖ = ‖x‖) :
    A ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  have h1 := ((orthogonal_tfae A).out 5 1).mp h
  exact (Matrix.mem_orthogonalGroup_iff' _ _).mpr ((cols_orthonormal_iff A).mp h1)

/-- An orthogonal matrix preserves Euclidean distances. -/
lemma dist_toEuclideanLin_of_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    dist (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) = dist x y := by
  have h1 := (cols_orthonormal_iff A).mpr ((Matrix.mem_orthogonalGroup_iff' _ _).mp hA)
  have h4 := ((orthogonal_tfae A).out 1 4).mp h1
  exact h4 x y

/-- AA-178. Example 12.1.10: every element of `O(2)` is a rotation matrix or a reflection matrix
for some angle `θ`. -/
@[kb "judson2026" "Example 12.1.10, p. 165"]
theorem orthogonal_two_rotation_or_reflection (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin 2) ℝ) :
    ∃ θ : ℝ, A = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] ∨
      A = !![Real.cos θ, Real.sin θ; Real.sin θ, -Real.cos θ] := by
  have h1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hA
  have hdet := det_orthogonal_eq_one_or_neg_one hA
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hn : ‖(⟨A 0 0, A 1 0⟩ : ℂ)‖ = 1 := by
    have : ‖(⟨A 0 0, A 1 0⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; nlinarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff _).mp hn
  have hc : Real.cos θ = A 0 0 := by
    have := congrArg Complex.re hθ
    simpa using this
  have hs : Real.sin θ = A 1 0 := by
    have := congrArg Complex.im hθ
    simpa using this
  rw [Matrix.det_fin_two] at hdet
  refine ⟨θ, ?_⟩
  rcases hdet with h | h
  · left
    have hb : A 0 1 = -A 1 0 := by linear_combination (-A 0 1) * e00 + A 0 0 * e01 - A 1 0 * h
    have hd : A 1 1 = A 0 0 := by linear_combination (-A 1 1) * e00 + A 1 0 * e01 + A 0 0 * h
    rw [hc, hs]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hd]
  · right
    have hb : A 0 1 = A 1 0 := by linear_combination (-A 0 1) * e00 + A 0 0 * e01 - A 1 0 * h
    have hd : A 1 1 = -A 0 0 := by linear_combination (-A 1 1) * e00 + A 1 0 * e01 + A 0 0 * h
    rw [hc, hs]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hd]

end UndergradKB.AbstractAlgebra
