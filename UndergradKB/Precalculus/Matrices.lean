import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.BigOperators.Field
import UndergradKB.Common.Attr

/-!
# Matrices (Precalculus, Chapter 8.3-8.5)

Scalar multiplication, invertible matrices, minors, cofactors, and Cramer's rule for real
square matrices.
-/

open Matrix

namespace UndergradKB.Precalculus

/-! ### Scalar multiplication -/

/-- Laws of scalar multiplication of real matrices: associativity, `1A = A`, `-A = (-1)A`, both
distributive laws, and `kA = 0` exactly when `k = 0` or `A = 0` (PC-143). -/
@[kb "stitzzeager2013" "Theorem 8.4, p. 593"]
theorem matrix_smul_laws {m n : ℕ} (k r : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    (k * r) • A = k • (r • A) ∧ (1 : ℝ) • A = A ∧ -A = (-1 : ℝ) • A ∧
    k • (A + B) = k • A + k • B ∧ (k + r) • A = k • A + r • A ∧
    (k • A = 0 ↔ k = 0 ∨ A = 0) :=
  ⟨mul_smul k r A, one_smul ℝ A, (neg_one_smul ℝ A).symm, smul_add k A B, add_smul k r A,
    smul_eq_zero⟩

/-! ### Invertible matrices -/

/-- An `n × n` real matrix is invertible when some matrix is a two-sided inverse of it. -/
def IsInvertibleMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) ℝ, B * A = 1 ∧ A * B = 1

/-- The book's notion of invertible agrees with `IsUnit` and with a nonzero determinant, and any
two-sided inverse is Mathlib's `A⁻¹` (PC-147). -/
@[kb "stitzzeager2013" "Definition 8.11, p. 614"]
theorem isInvertibleMatrix_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (IsInvertibleMatrix A ↔ IsUnit A) ∧ (IsInvertibleMatrix A ↔ A.det ≠ 0) ∧
    (∀ B : Matrix (Fin n) (Fin n) ℝ, B * A = 1 → A * B = 1 → B = A⁻¹) := by
  have h1 : IsInvertibleMatrix A ↔ IsUnit A := by
    rw [isUnit_iff_exists]
    constructor
    · rintro ⟨B, hBA, hAB⟩
      exact ⟨B, hAB, hBA⟩
    · rintro ⟨B, hAB, hBA⟩
      exact ⟨B, hBA, hAB⟩
  refine ⟨h1, ?_, fun B _ hAB => (Matrix.inv_eq_right_inv hAB).symm⟩
  rw [h1, isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- An `n × n` matrix is invertible iff, for every `n × r` matrix `B`, the equation `A X = B` has
exactly one solution `X`; here also the version for column vectors (PC-149). -/
@[kb "stitzzeager2013" "Theorem 8.6, p. 614"]
theorem invertible_iff_unique_solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (IsInvertibleMatrix A ↔ ∀ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℝ), ∃! X : Matrix (Fin n) (Fin r) ℝ, A * X = B) ∧
    (IsInvertibleMatrix A ↔ ∀ b : Fin n → ℝ, ∃! x, A *ᵥ x = b) := by
  constructor
  · constructor
    · rintro ⟨Q, hQA, hAQ⟩ r B
      refine ⟨Q * B, ?_, fun X hX => ?_⟩
      · show A * (Q * B) = B
        rw [← Matrix.mul_assoc, hAQ, Matrix.one_mul]
      · rw [← hX, ← Matrix.mul_assoc, hQA, Matrix.one_mul]
    · intro h
      obtain ⟨X, hX, _⟩ := h n 1
      refine ⟨X, ?_, hX⟩
      exact mul_eq_one_comm.1 hX
  · constructor
    · rintro ⟨Q, hQA, hAQ⟩ b
      refine ⟨Q *ᵥ b, ?_, fun x hx => ?_⟩
      · show A *ᵥ (Q *ᵥ b) = b
        rw [mulVec_mulVec, hAQ, one_mulVec]
      · rw [← hx, mulVec_mulVec, hQA, one_mulVec]
    · intro h
      have hinj : Function.Injective A.mulVec := by
        intro x y hxy
        obtain ⟨z, _, hz⟩ := h (A *ᵥ y)
        exact (hz x hxy).trans (hz y rfl).symm
      have hU : IsUnit A := Matrix.mulVec_injective_iff_isUnit.1 hinj
      exact (isInvertibleMatrix_iff A).1.2 hU

/-! ### Minors and cofactors -/

/-- The matrix `A_{ij}` obtained from an `(n+1) × (n+1)` matrix by deleting row `i` and
column `j`. -/
def deleteRowCol {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix i.succAbove j.succAbove

/-- Entries of `A_{ij}`: row `r` and column `c` come from `A`, skipping the deleted row `i` and
column `j`; no kept row is `i` and every other row is kept (PC-150). -/
@[kb "stitzzeager2013" "Definition 8.12, p. 626"]
theorem deleteRowCol_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    (∀ r c, deleteRowCol A i j r c =
      A (if r.castSucc < i then r.castSucc else r.succ)
        (if c.castSucc < j then c.castSucc else c.succ)) ∧
    (∀ r, i.succAbove r ≠ i) ∧ (∀ i', i' ≠ i → ∃ r, i.succAbove r = i') ∧
    (∀ c, j.succAbove c ≠ j) ∧ (∀ j', j' ≠ j → ∃ c, j.succAbove c = j') :=
  ⟨fun _ _ => rfl, fun r => Fin.succAbove_ne i r, fun _ h => Fin.exists_succAbove_eq h,
    fun c => Fin.succAbove_ne j c, fun _ h => Fin.exists_succAbove_eq h⟩

/-- The minor `M_{ij} = det A_{ij}`. -/
def minor' {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) : ℝ :=
  (deleteRowCol A i j).det

/-- The cofactor `C_{ij} = (-1)^(i+j) M_{ij}`. -/
def cofactor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) : ℝ :=
  (-1) ^ ((i : ℕ) + (j : ℕ)) * minor' A i j

/-- Cofactor expansion of the determinant along any row or any column, and the adjugate is the
transposed cofactor matrix (PC-153). -/
@[kb "stitzzeager2013" "Definition 8.14, p. 628"]
theorem det_eq_sum_cofactor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (∀ i, A.det = ∑ j, A i j * cofactor A i j) ∧
    (∀ j, A.det = ∑ i, A i j * cofactor A i j) ∧
    (∀ i j, A.adjugate i j = cofactor A j i) := by
  refine ⟨fun i => ?_, fun j => ?_, fun i j => ?_⟩
  · rw [det_succ_row A i]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cofactor, minor', deleteRowCol]
    ring
  · rw [det_succ_column A j]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cofactor, minor', deleteRowCol]
    ring
  · rw [adjugate_fin_succ_eq_det_submatrix]
    simp only [cofactor, minor', deleteRowCol]

/-! ### Cramer's rule -/

/-- Cramer's rule: if `det A ≠ 0`, the system `A x = b` is consistent and independent, and the
solution is `x_j = det(A_j) / det A`, where `A_j` is `A` with column `j` replaced by `b`
(PC-160). -/
@[kb "stitzzeager2013" "Theorem 8.8, p. 631"]
theorem cramers_rule {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (h : A.det ≠ 0) :
    (∃! x, A *ᵥ x = b) ∧
    ∀ x, A *ᵥ x = b ↔ ∀ j, x j = (A.updateCol j b).det / A.det := by
  have hU : IsUnit A := (isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hU
  set x0 : Fin n → ℝ := fun j => (A.updateCol j b).det / A.det with hx0
  have hsol : A *ᵥ x0 = b := by
    have hx0' : x0 = (A.det)⁻¹ • cramer A b := by
      funext j
      simp [hx0, cramer_apply, div_eq_inv_mul]
    rw [hx0', mulVec_smul, mulVec_cramer, smul_smul, inv_mul_cancel₀ h, one_smul]
  have hiff : ∀ x, A *ᵥ x = b ↔ x = x0 := fun x =>
    ⟨fun hx => hinj (hx.trans hsol.symm), fun hx => hx ▸ hsol⟩
  refine ⟨⟨x0, hsol, fun x hx => (hiff x).1 hx⟩, fun x => ?_⟩
  rw [hiff, funext_iff]

/-! ### Partial fractions -/

open Polynomial

private lemma pf_term_degree_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → ℝ[X]}
    (hg : ∀ i ∈ s, (g i).Monic) (e : ι → ℕ) {i : ι} (hi : i ∈ s) (j : Fin (e i)) (r : ℝ[X])
    (hr : r.degree < (g i).degree) :
    (r * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ e k).degree < (∏ k ∈ s, g k ^ e k).degree := by
  have hP : (∏ k ∈ s.erase i, g k ^ e k).Monic :=
    monic_prod_of_monic _ _ fun k hk => (hg k (Finset.mem_of_mem_erase hk)).pow _
  have hgi : (g i ^ e i).Monic := (hg i hi).pow _
  have hD : ∏ k ∈ s, g k ^ e k = g i ^ e i * ∏ k ∈ s.erase i, g k ^ e k :=
    (Finset.mul_prod_erase s (fun k => g k ^ e k) hi).symm
  have hDmon : (∏ k ∈ s, g k ^ e k).Monic := hD ▸ hgi.mul hP
  have hD0 : ∏ k ∈ s, g k ^ e k ≠ 0 := hDmon.ne_zero
  by_cases hr0 : r = 0
  · rw [hr0]
    simp only [zero_mul, degree_zero]
    exact bot_lt_iff_ne_bot.2 (fun h => hD0 (degree_eq_bot.1 h))
  · have hrn : r.natDegree < (g i).natDegree := natDegree_lt_natDegree hr0 hr
    have hterm : r * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ e k ≠ 0 :=
      mul_ne_zero (mul_ne_zero hr0 ((hg i hi).pow _).ne_zero) hP.ne_zero
    rw [degree_eq_natDegree hterm, degree_eq_natDegree hD0]
    norm_cast
    have h1 : (r * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ e k).natDegree =
        r.natDegree + j.1 * (g i).natDegree + (∏ k ∈ s.erase i, g k ^ e k).natDegree := by
      rw [natDegree_mul (mul_ne_zero hr0 ((hg i hi).pow _).ne_zero) hP.ne_zero,
        natDegree_mul hr0 ((hg i hi).pow _).ne_zero, natDegree_pow]
    have h2 : (∏ k ∈ s, g k ^ e k).natDegree =
        e i * (g i).natDegree + (∏ k ∈ s.erase i, g k ^ e k).natDegree := by
      rw [hD, natDegree_mul hgi.ne_zero hP.ne_zero, natDegree_pow]
    rw [h1, h2]
    have hj : j.1 + 1 ≤ e i := j.2
    nlinarith

private lemma pf_poly_identity {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → ℝ[X]}
    (hg : ∀ i ∈ s, (g i).Monic) (hgg : Set.Pairwise (↑s) fun i j => IsCoprime (g i) (g j))
    (e : ι → ℕ) (N : ℝ[X]) (hN : N.degree < (∏ k ∈ s, g k ^ e k).degree) :
    ∃ r : (i : ι) → Fin (e i) → ℝ[X], (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      N = ∑ i ∈ s, ∑ j, r i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ e k := by
  obtain ⟨q, r, hr, hf⟩ := eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow N hg hgg e
  refine ⟨r, hr, ?_⟩
  set D := ∏ k ∈ s, g k ^ e k with hDdef
  have hDmon : D.Monic := monic_prod_of_monic _ _ fun k hk => (hg k hk).pow _
  have hbot : (⊥ : WithBot ℕ) < D.degree :=
    bot_lt_iff_ne_bot.2 (fun h => hDmon.ne_zero (degree_eq_bot.1 h))
  set T := ∑ i ∈ s, ∑ j, r i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ e k with hTdef
  have hT : T.degree < D.degree := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff hbot).2 fun i hi => ?_)
    refine lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff hbot).2 fun j _ => ?_)
    exact pf_term_degree_lt hg e hi j _ (hr i hi j)
  have hq : q = 0 := by
    by_contra hq0
    have hqD : q * D = N - T := by rw [hf]; ring
    have hqD0 : q * D ≠ 0 := mul_ne_zero hq0 hDmon.ne_zero
    have h1 : D.degree ≤ (q * D).degree := degree_le_of_dvd (dvd_mul_left D q) hqD0
    have h2 : (N - T).degree < D.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hN hT)
    rw [hqD] at h1
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  rw [hf, hq]
  simp

/-- Partial fractions over the reals: a proper rational function `N / D`, where `D` is a product
of powers `g_i ^ e_i` of pairwise coprime monic factors, is a sum of terms
`r_{ij} / g_i ^ (j+1)` with `deg r_{ij} < deg g_i` (so constants over linear factors and at most
linear numerators over quadratic factors), computed in the field of rational functions
(PC-164). -/
@[kb "stitzzeager2013" "Theorem 8.10, p. 642"]
theorem partial_fractions_proper {ι : Type*} [DecidableEq ι] {s : Finset ι} {g : ι → ℝ[X]}
    (hg : ∀ i ∈ s, (g i).Monic) (hgg : Set.Pairwise (↑s) fun i j => IsCoprime (g i) (g j))
    (e : ι → ℕ) (N : ℝ[X]) (hN : N.degree < (∏ k ∈ s, g k ^ e k).degree) :
    ∃ r : (i : ι) → Fin (e i) → ℝ[X], (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      algebraMap ℝ[X] (RatFunc ℝ) N / algebraMap ℝ[X] (RatFunc ℝ) (∏ k ∈ s, g k ^ e k) =
        ∑ i ∈ s, ∑ j : Fin (e i),
          algebraMap ℝ[X] (RatFunc ℝ) (r i j) / (algebraMap ℝ[X] (RatFunc ℝ) (g i)) ^ (j.1 + 1) := by
  obtain ⟨r, hr, hNeq⟩ := pf_poly_identity hg hgg e N hN
  have hinj := RatFunc.algebraMap_injective ℝ
  refine ⟨fun i j => r i j.rev, fun i hi j => hr i hi _, ?_⟩
  have hgne : ∀ i ∈ s, algebraMap ℝ[X] (RatFunc ℝ) (g i) ≠ 0 := fun i hi h =>
    (hg i hi).ne_zero (hinj (by rw [h, map_zero]))
  have hPne : ∀ i ∈ s, algebraMap ℝ[X] (RatFunc ℝ) (∏ k ∈ s.erase i, g k ^ e k) ≠ 0 :=
    fun i hi h => (monic_prod_of_monic _ _ fun k hk =>
      (hg k (Finset.mem_of_mem_erase hk)).pow (e k)).ne_zero (hinj (by rw [h, map_zero]))
  rw [hNeq, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_sum, Finset.sum_div, ← Equiv.sum_comp Fin.revPerm]
  refine Fintype.sum_congr _ _ fun j => ?_
  obtain ⟨t, ht⟩ : ∃ t, e i = j.1 + 1 + t := ⟨e i - (j.1 + 1), by have := j.2; omega⟩
  have hD : algebraMap ℝ[X] (RatFunc ℝ) (∏ k ∈ s, g k ^ e k) =
      algebraMap ℝ[X] (RatFunc ℝ) (g i) ^ (j.1 + 1 + t) *
        algebraMap ℝ[X] (RatFunc ℝ) (∏ k ∈ s.erase i, g k ^ e k) := by
    rw [← Finset.mul_prod_erase s (fun k => g k ^ e k) hi, map_mul, map_pow]
    exact congrArg (fun n : ℕ => algebraMap ℝ[X] (RatFunc ℝ) (g i) ^ n * algebraMap ℝ[X] (RatFunc ℝ) (∏ k ∈ s.erase i, g k ^ e k)) ht
  have hrev : (j.rev : ℕ) = t := by
    rw [Fin.val_rev]
    omega
  simp only [Fin.revPerm_apply]
  rw [hD, map_mul, map_mul, map_pow, hrev]
  have h1 := hgne i hi
  have h2 := hPne i hi
  field_simp
  ring

/-- Shape of the numerators in Theorem 8.10: over a linear factor the numerator is a constant,
over a quadratic factor it has the form `B x + C`. -/
theorem partial_fraction_numerator_shape (g r : ℝ[X]) (hr : r.degree < g.degree) :
    (g.natDegree = 1 → ∃ A : ℝ, r = C A) ∧
    (g.natDegree = 2 → ∃ B C' : ℝ, r = C B * X + C C') := by
  by_cases hr0 : r = 0
  · exact ⟨fun _ => ⟨0, by simp [hr0]⟩, fun _ => ⟨0, 0, by simp [hr0]⟩⟩
  · have hlt : r.natDegree < g.natDegree := natDegree_lt_natDegree hr0 hr
    refine ⟨fun h => ⟨r.coeff 0, eq_C_of_natDegree_eq_zero (by omega)⟩, fun h => ?_⟩
    exact ⟨r.coeff 1, r.coeff 0, eq_X_add_C_of_natDegree_le_one (by omega)⟩

end UndergradKB.Precalculus
