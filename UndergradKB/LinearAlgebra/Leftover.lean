import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import UndergradKB.Common.Attr

/-! # Leftover rows: elementary row operations and inner-product examples -/

namespace UndergradKB.LinearAlgebra

open Matrix

section RowOps

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [DecidableEq m]

/-- Swapping rows `i` and `j` of `A` is left multiplication by the swap matrix. -/
@[kb "hefferon2020" "One.I.1.6, p. 15"]
theorem hefferon_One_I_1_6_swap (i j : m) (A : Matrix m n R) :
    Matrix.swap R i j * A = A.submatrix (Equiv.swap i j) id := by
  ext a b
  by_cases ha : a = i
  · subst ha; simp
  by_cases hb : a = j
  · subst hb; simp
  simp [Matrix.swap_mul_of_ne ha hb, Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Multiplying row `i` of `A` by `c` is left multiplication by the diagonal matrix `rowScale`. -/
@[kb "hefferon2020" "One.I.1.6, p. 15"]
theorem hefferon_One_I_1_6_scale (i : m) (c : R) (A : Matrix m n R) :
    Matrix.rowScale i c * A = A.updateRow i (c • A i) := by
  rw [Matrix.rowScale_mul]; rfl

/-- Adding `c` times row `j` to row `i` of `A` is left multiplication by a transvection. -/
@[kb "hefferon2020" "One.I.1.6, p. 15"]
theorem hefferon_One_I_1_6_add (i j : m) (c : R) (A : Matrix m n R) :
    Matrix.transvection i j c * A = A.updateRow i (A i + c • A j) := by
  ext a b
  by_cases ha : a = i
  · subst ha; simp
  · simp [Matrix.transvection_mul_apply_of_ne _ _ _ _ ha, ha]

end RowOps

section Inner

/-- The weighted form `∑ cᵢ xᵢ yᵢ` with all `cᵢ > 0` satisfies the inner-product axioms
(symmetry, additivity and homogeneity in the first slot, positivity and definiteness). -/
@[kb "axler2024" "6.3, p. 202"]
theorem axler_6_3_weighted {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ x y : Fin n → ℝ, ∑ i, c i * x i * y i = ∑ i, c i * y i * x i) ∧
    (∀ x x' y : Fin n → ℝ, ∑ i, c i * (x + x') i * y i
      = ∑ i, c i * x i * y i + ∑ i, c i * x' i * y i) ∧
    (∀ (a : ℝ) (x y : Fin n → ℝ), ∑ i, c i * (a • x) i * y i = a * ∑ i, c i * x i * y i) ∧
    (∀ x : Fin n → ℝ, 0 ≤ ∑ i, c i * x i * x i) ∧
    (∀ x : Fin n → ℝ, ∑ i, c i * x i * x i = 0 ↔ x = 0) := by
  have hnn : ∀ (x : Fin n → ℝ) (i : Fin n), 0 ≤ c i * x i * x i := fun x i => by
    have := mul_nonneg (hc i).le (mul_self_nonneg (x i))
    linarith
  refine ⟨fun x y => ?_, fun x x' y => ?_, fun a x y => ?_, fun x => ?_, fun x => ?_⟩
  · exact Finset.sum_congr rfl fun i _ => by ring
  · rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  · exact Finset.sum_nonneg fun i _ => hnn x i
  · constructor
    · intro h
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn x i)).1 h
      ext i
      have h1 := this i (Finset.mem_univ i)
      have h2 : c i * (x i * x i) = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h (hc i).ne'
      · simpa using h
    · rintro rfl; simp

/-- The Euclidean inner product on `F^n` (`F = ℝ` or `ℂ`) is the usual sum of coordinate products
(conjugating the first factor). -/
@[kb "axler2024" "6.3, p. 202"]
theorem axler_6_3_euclidean {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 x y = ∑ i, (starRingEnd 𝕜) (x i) * y i := by
  simp [PiLp.inner_apply, mul_comm]

end Inner

section OrthDecomp

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For `v ≠ 0`, every `u` is a multiple of `v` plus a vector orthogonal to `v`
(here `⟪v, u⟫` is the book's `⟨u, v⟩`). -/
@[kb "axler2024" "6.13, p. 206"]
theorem axler_6_13 {v : E} (hv : v ≠ 0) (u : E) :
    ∃ w : E, inner 𝕜 v w = 0 ∧
      u = (inner 𝕜 v u / ((‖v‖ : 𝕜) ^ 2)) • v + w := by
  refine ⟨u - (inner 𝕜 v u / ((‖v‖ : 𝕜) ^ 2)) • v, ?_, by abel⟩
  have hn : ((‖v‖ : 𝕜)) ^ 2 ≠ 0 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    exact pow_ne_zero _ (by exact_mod_cast this)
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, div_mul_cancel₀ _ hn]
  exact sub_self _

end OrthDecomp

section CS

/-- Cauchy-Schwarz for real finite sequences. -/
@[kb "axler2024" "6.16, p. 207"]
theorem axler_6_16 {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * ∑ i, y i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq _ x y

end CS

section Orthonormal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For an orthonormal family, the squared norm of a linear combination is the sum of the
squared absolute values of the coefficients. -/
@[kb "axler2024" "6.24, p. 216"]
theorem axler_6_24 {ι : Type*} {e : ι → E} (he : Orthonormal 𝕜 e) (a : ι → 𝕜) (s : Finset ι) :
    ‖∑ i ∈ s, a i • e i‖ ^ 2 = ∑ i ∈ s, ‖a i‖ ^ 2 := by
  have h := he.inner_sum a a s
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [RCLike.conj_mul] at h
  exact_mod_cast h

end Orthonormal

end UndergradKB.LinearAlgebra
