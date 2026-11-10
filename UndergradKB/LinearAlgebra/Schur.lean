import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr

/-! # Upper-triangular matrices in orthonormal bases: Schur (Axler 6.37, 6.38)

`𝕜` is `ℝ` or `ℂ` (an `RCLike` field).  Mathlib's inner product is conjugate-linear in the first slot.
The matrix of `T` in an orthonormal basis `u` has entry `⟪u i, T (u j)⟫` at `(i, j)`; it is upper triangular
when this vanishes for `j < i`.
-/

open scoped InnerProductSpace ComplexOrder Matrix
open Module

namespace UndergradKB.LinearAlgebra

universe u

section Compression

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ`, for a unit vector `v`, as a linear map. -/
noncomputable def perpProj (v : E) (hv : ‖v‖ = 1) : E →ₗ[𝕜] (𝕜 ∙ v)ᗮ :=
  LinearMap.codRestrict (𝕜 ∙ v)ᗮ (LinearMap.id - (innerₛₗ 𝕜 v).smulRight v) (by
    intro y
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv])

/-- The compression of `T` to `(𝕜 ∙ v)ᗮ`: apply `T`, then project orthogonally to `v`. -/
noncomputable def compress (T : E →ₗ[𝕜] E) (v : E) (hv : ‖v‖ = 1) :
    (𝕜 ∙ v)ᗮ →ₗ[𝕜] (𝕜 ∙ v)ᗮ :=
  perpProj v hv ∘ₗ T ∘ₗ (𝕜 ∙ v)ᗮ.subtype

lemma coe_compress (T : E →ₗ[𝕜] E) (v : E) (hv : ‖v‖ = 1) (w : (𝕜 ∙ v)ᗮ) :
    (compress T v hv w : E) = T w - ⟪v, T w⟫_𝕜 • v := by
  simp [compress, perpProj]

lemma compress_pow (T : E →ₗ[𝕜] E) (v : E) (hv : ‖v‖ = 1) {μ : 𝕜} (hTv : T v = μ • v) (k : ℕ)
    (w : (𝕜 ∙ v)ᗮ) : ∃ c : 𝕜, ((compress T v hv ^ k) w : E) = (T ^ k) w + c • v := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * μ - ⟪v, T ((T ^ k) w + c • v)⟫_𝕜, ?_⟩
    rw [pow_succ', mul_apply_eq_comp, coe_compress, hc, pow_succ', mul_apply_eq_comp,
      map_add, map_smul, hTv, smul_smul]
    module

lemma aeval_compress (T : E →ₗ[𝕜] E) (v : E) (hv : ‖v‖ = 1) {μ : 𝕜} (hTv : T v = μ • v)
    (p : Polynomial 𝕜) (w : (𝕜 ∙ v)ᗮ) :
    ∃ c : 𝕜, (Polynomial.aeval (compress T v hv) p w : E) = Polynomial.aeval T p w + c • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨c₁, h₁⟩ := hp
    obtain ⟨c₂, h₂⟩ := hq
    refine ⟨c₁ + c₂, ?_⟩
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, h₁, h₂, add_smul]
    abel
  | monomial n a =>
    obtain ⟨c, hc⟩ := compress_pow T v hv hTv n w
    refine ⟨a * c, ?_⟩
    simp [Polynomial.aeval_monomial, hc, smul_add, smul_smul]

lemma minpoly_compress_dvd (T : E →ₗ[𝕜] E) (v : E) (hv : ‖v‖ = 1) {μ : 𝕜} (hTv : T v = μ • v) :
    minpoly 𝕜 (compress T v hv) ∣ minpoly 𝕜 T := by
  refine minpoly.dvd 𝕜 _ ?_
  ext w
  obtain ⟨c, hc⟩ := aeval_compress T v hv hTv (minpoly 𝕜 T) w
  rw [minpoly.aeval] at hc
  set x := (Polynomial.aeval (compress T v hv) (minpoly 𝕜 T)) w with hx
  have h2 : ⟪v, (x : E)⟫_𝕜 = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 x.2
  have h1 : (x : E) = c • v := by simpa using hc
  rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K, hv] at h2
  have hc0 : c = 0 := by simpa using h2
  rw [h1, hc0]
  simp

end Compression

section Triangularization

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Induction on the dimension: an operator with split minimal polynomial has an orthonormal basis `u`
with `⟪u i, T (u j)⟫ = 0` for `j < i`. -/
theorem exists_orthonormalBasis_upperTriangular_aux :
    ∀ (n : ℕ) (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
      (T : E →ₗ[𝕜] E), finrank 𝕜 E = n → (minpoly 𝕜 T).Splits →
      ∃ u : OrthonormalBasis (Fin n) 𝕜 E, ∀ i j : Fin n, j < i → ⟪u i, T (u j)⟫_𝕜 = 0 := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ T hn _
    exact ⟨(stdOrthonormalBasis 𝕜 E).reindex (finCongr hn), fun i => i.elim0⟩
  | succ n ih =>
    intro E _ _ _ T hn hspl
    have : Nontrivial E := Module.finrank_pos_iff.1 (by rw [hn]; exact Nat.succ_pos n)
    have hdeg : (minpoly 𝕜 T).degree ≠ 0 := (minpoly.degree_pos (LinearMap.isIntegral T)).ne'
    obtain ⟨μ, hμ⟩ := hspl.exists_eval_eq_zero hdeg
    have hev : Module.End.HasEigenvalue T μ := Module.End.hasEigenvalue_of_isRoot hμ
    obtain ⟨v₀, hv₀⟩ := hev.exists_hasEigenvector
    have hv₀' : T v₀ = μ • v₀ := Module.End.mem_eigenspace_iff.1 hv₀.1
    set v : E := (‖v₀‖⁻¹ : 𝕜) • v₀ with hvdef
    have hv : ‖v‖ = 1 := norm_smul_inv_norm hv₀.2
    have hv0 : v ≠ 0 := by
      intro h; rw [h] at hv; simp at hv
    have hTv : T v = μ • v := by
      rw [hvdef, map_smul, hv₀', smul_comm]
    have : Fact (finrank 𝕜 E = n + 1) := ⟨hn⟩
    have hW : finrank 𝕜 (𝕜 ∙ v)ᗮ = n := Submodule.finrank_orthogonal_span_singleton hv0
    obtain ⟨u', hu'⟩ := ih (𝕜 ∙ v)ᗮ (compress T v hv) hW
      (hspl.of_dvd (minpoly.ne_zero (LinearMap.isIntegral T)) (minpoly_compress_dvd T v hv hTv))
    have hperp : ∀ i, ⟪v, ((u' i : (𝕜 ∙ v)ᗮ) : E)⟫_𝕜 = 0 := fun i =>
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (u' i).2
    have hperp' : ∀ i, ⟪((u' i : (𝕜 ∙ v)ᗮ) : E), v⟫_𝕜 = 0 := fun i => by
      rw [← inner_conj_symm, hperp i, map_zero]
    have hon : Orthonormal 𝕜 (Fin.cons v (fun i => ((u' i : (𝕜 ∙ v)ᗮ) : E)) : Fin (n + 1) → E) := by
      rw [orthonormal_iff_ite]
      intro i j
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp [inner_self_eq_norm_sq_to_K, hv]
        | succ j' => simp [hperp j', (Fin.succ_ne_zero j').symm]
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [hperp' i', (Fin.succ_ne_zero i')]
        | succ j' =>
          have := orthonormal_iff_ite.1 u'.orthonormal i' j'
          simpa [Submodule.coe_inner] using this
    have hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range
        (Fin.cons v (fun i => ((u' i : (𝕜 ∙ v)ᗮ) : E)) : Fin (n + 1) → E)) :=
      (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [hn])).ge
    refine ⟨OrthonormalBasis.mk hon hsp, ?_⟩
    intro i j hij
    simp only [OrthonormalBasis.coe_mk]
    induction i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ i' =>
      induction j using Fin.cases with
      | zero => simp [hTv, inner_smul_right, hperp' i']
      | succ j' =>
        have hlt : j' < i' := Fin.succ_lt_succ_iff.1 hij
        have h1 := hu' i' j' hlt
        have e : T (u' j' : E) = ((compress T v hv (u' j') : (𝕜 ∙ v)ᗮ) : E) +
            ⟪v, T (u' j' : E)⟫_𝕜 • v := by
          rw [coe_compress]; abel
        simp only [Fin.cons_succ]
        rw [e, inner_add_right, inner_smul_right, hperp' i', mul_zero, add_zero]
        simpa [Submodule.coe_inner] using h1

/-- The `(i, j)` entry of the matrix of `T` in an orthonormal basis `u` is `⟪u i, T (u j)⟫`. -/
lemma toMatrix_orthonormalBasis_apply {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ} (u : OrthonormalBasis (Fin n) 𝕜 E) (T : E →ₗ[𝕜] E)
    (i j : Fin n) : LinearMap.toMatrix u.toBasis u.toBasis T i j = ⟪u i, T (u j)⟫_𝕜 := by
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  simp

/-- Axler 6.37: an operator has an upper-triangular matrix in some orthonormal basis iff its minimal
polynomial splits into linear factors. -/
@[kb "axler2024" "6.37, p. 221"]
theorem axler_6_37 {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    (∃ u : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      (LinearMap.toMatrix u.toBasis u.toBasis T).IsUpperTriangular) ↔ (minpoly 𝕜 T).Splits := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 := Matrix.charpoly_of_isUpperTriangular _ hu
    rw [LinearMap.charpoly_toMatrix] at h1
    have h2 : T.charpoly.Splits := by
      rw [h1]
      exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
    exact h2.of_dvd T.charpoly_monic.ne_zero (LinearMap.minpoly_dvd_charpoly T)
  · intro hs
    obtain ⟨u, hu⟩ := exists_orthonormalBasis_upperTriangular_aux (finrank 𝕜 E) E T rfl hs
    refine ⟨u, fun i j hij => ?_⟩
    rw [toMatrix_orthonormalBasis_apply]
    exact hu i j hij

/-- Axler 6.38 (Schur): every operator on a finite-dimensional complex inner product space has an
upper-triangular matrix in some orthonormal basis. -/
@[kb "axler2024" "6.38, p. 222"]
theorem axler_6_38 {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    ∃ u : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      (LinearMap.toMatrix u.toBasis u.toBasis T).IsUpperTriangular :=
  (axler_6_37 T).2 (IsAlgClosed.splits _)

end Triangularization

section QR

open InnerProductSpace Finset Submodule

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

lemma inner_eq_zero_of_mem_span' {s : Set E} {z : E} (hz : ∀ t ∈ s, ⟪t, z⟫_𝕜 = 0) {w : E}
    (hw : w ∈ Submodule.span 𝕜 s) : ⟪w, z⟫_𝕜 = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hz x hx
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- Uniqueness of Gram-Schmidt: an orthonormal family `q` such that `f j` is a combination of `q i`,
`i ≤ j`, with positive coefficient at `q j`, is `gramSchmidtNormed f`. -/
theorem gramSchmidtNormed_unique {n : ℕ} (f : Fin n → E) (q : Fin n → E) (hq : Orthonormal 𝕜 q)
    (c : Fin n → Fin n → 𝕜) (hc_tri : ∀ i j, j < i → c i j = 0)
    (hc_pos : ∀ j, ∃ r : ℝ, 0 < r ∧ c j j = r) (hfc : ∀ j, f j = ∑ i, c i j • q i) :
    gramSchmidtNormed 𝕜 f = q := by
  funext j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    set gs := gramSchmidt 𝕜 f with hgs
    set S := Submodule.span 𝕜 (gs '' Set.Iio j) with hSdef
    have hS' : Submodule.span 𝕜 (q '' Set.Iio j) = S := by
      have : gramSchmidtNormed 𝕜 f '' Set.Iio j = q '' Set.Iio j :=
        Set.image_congr (fun i hi => ih i hi)
      rw [hSdef, ← this, span_gramSchmidtNormed]
    have hsplit : f j = c j j • q j + ∑ i ∈ Finset.Iio j, c i j • q i := by
      rw [hfc j, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic j))
        (fun i _ hi => by rw [hc_tri i j (not_le.1 (by simpa using hi)), zero_smul]),
        ← Finset.Iio_insert, Finset.sum_insert (by simp)]
    have hw : ∑ i ∈ Finset.Iio j, c i j • q i ∈ S := by
      rw [← hS']
      exact Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)
    have hdef : f j - gs j ∈ S := by
      have h3 : f j - gs j = ∑ i ∈ Finset.Iio j, (𝕜 ∙ gs i).starProjection (f j) := by
        rw [hgs, gramSchmidt_def 𝕜 f j, sub_sub_cancel]
      rw [h3]
      refine Submodule.sum_mem _ fun i hi => ?_
      have hsub : (𝕜 ∙ gs i) ≤ S := Submodule.span_mono
        (Set.singleton_subset_iff.2 (Set.mem_image_of_mem gs (Finset.mem_Iio.1 hi)))
      exact hsub (Submodule.starProjection_apply_mem _ _)
    have hy : f j - c j j • q j ∈ S := by
      rw [hsplit, add_sub_cancel_left]; exact hw
    have hmem : gs j - c j j • q j ∈ S := by
      have := S.sub_mem hy hdef
      convert this using 1
      abel
    have horth : ∀ s ∈ S, ⟪s, gs j - c j j • q j⟫_𝕜 = 0 := by
      intro s hs
      rw [inner_sub_right, inner_smul_right]
      have h1 : ⟪s, gs j⟫_𝕜 = 0 :=
        inner_eq_zero_of_mem_span' (s := gs '' Set.Iio j) (z := gs j) (by
          rintro _ ⟨i, hi, rfl⟩
          exact gramSchmidt_orthogonal 𝕜 f (ne_of_lt (Set.mem_Iio.1 hi))) hs
      have h2 : ⟪s, q j⟫_𝕜 = 0 :=
        inner_eq_zero_of_mem_span' (s := q '' Set.Iio j) (z := q j) (by
          rintro _ ⟨i, hi, rfl⟩
          exact hq.2 (ne_of_lt (Set.mem_Iio.1 hi))) (hS' ▸ hs)
      rw [h1, h2, mul_zero, sub_zero]
    have hgy : gs j = c j j • q j := sub_eq_zero.1 (inner_self_eq_zero.1 (horth _ hmem))
    obtain ⟨r, hr, hcr⟩ := hc_pos j
    have hne : ((r : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hr.ne'
    have hnorm : ‖gs j‖ = r := by
      rw [hgy, hcr, norm_smul, hq.1 j, mul_one, RCLike.norm_ofReal, abs_of_pos hr]
    simp only [gramSchmidtNormed, ← hgs, hnorm]
    rw [hgy, hcr, smul_smul, inv_mul_cancel₀ hne, one_smul]

end QR

section QRTheorem

open InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

lemma qr_orthonormal_cols_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) :
    Orthonormal 𝕜 (fun k : Fin n => (WithLp.toLp 2 (fun j => M j k) : EuclideanSpace 𝕜 (Fin n))) ↔
      Mᴴ * M = 1 := by
  have key : ∀ k r, ⟪(WithLp.toLp 2 (fun j => M j k) : EuclideanSpace 𝕜 (Fin n)),
      WithLp.toLp 2 (fun j => M j r)⟫_𝕜 = (Mᴴ * M) k r := by
    intro k r
    simp [EuclideanSpace.inner_toLp_toLp, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
      mul_comm]
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    ext k r
    rw [← key, h k r, Matrix.one_apply]
  · intro h k r
    rw [key, h, Matrix.one_apply]

lemma inner_gramSchmidt_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}
    (f : Fin n → E) (j : Fin n) :
    ⟪gramSchmidt 𝕜 f j, f j⟫_𝕜 = ((‖gramSchmidt 𝕜 f j‖ : ℝ) : 𝕜) ^ 2 := by
  have h := gramSchmidt_def'' 𝕜 f j
  calc ⟪gramSchmidt 𝕜 f j, f j⟫_𝕜
      = ⟪gramSchmidt 𝕜 f j, gramSchmidt 𝕜 f j + ∑ i ∈ Finset.Iio j,
          (⟪gramSchmidt 𝕜 f i, f j⟫_𝕜 / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i⟫_𝕜 := by
        rw [← h]
    _ = _ := by
        rw [inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero, inner_self_eq_norm_sq_to_K]
        intro i hi
        rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 f (ne_of_gt (Finset.mem_Iio.1 hi)), mul_zero]

/-- Axler 7.58 (QR factorization): a square matrix with linearly independent columns factors uniquely
as `Q R` with `Q` unitary and `R` upper triangular with positive diagonal. -/
@[kb "axler2024" "7.58, p. 282"]
theorem axler_7_58 {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
    (hA : LinearIndependent 𝕜
      (fun j : Fin n => (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n)))) :
    ∃! p : Matrix (Fin n) (Fin n) 𝕜 × Matrix (Fin n) (Fin n) 𝕜,
      p.1 ∈ Matrix.unitaryGroup (Fin n) 𝕜 ∧ p.2.IsUpperTriangular ∧ (∀ i, 0 < p.2 i i) ∧
        A = p.1 * p.2 := by
  set f : Fin n → EuclideanSpace 𝕜 (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j) with hf
  have hq : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := gramSchmidtNormed_orthonormal hA
  set q := gramSchmidtNormed 𝕜 f with hqdef
  let Q : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i j => (q j).ofLp i
  let R : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i j => ⟪q i, f j⟫_𝕜
  have hQ : Qᴴ * Q = 1 := (qr_orthonormal_cols_iff Q).1 hq
  have hcard : Fintype.card (Fin n) = finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) := by simp
  let b := OrthonormalBasis.mk hq (hq.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge
  have hexp : ∀ j, f j = ∑ i, R i j • q i := fun j => by
    have := b.sum_repr' (f j)
    simpa [b, R] using this.symm
  have hRtri : ∀ i j, j < i → R i j = 0 := by
    intro i j hij
    simp [R, q, gramSchmidtNormed, inner_smul_left, gramSchmidt_inv_triangular 𝕜 f hij]
  have hRpos : ∀ j, ∃ r : ℝ, 0 < r ∧ R j j = r := by
    intro j
    refine ⟨‖gramSchmidt 𝕜 f j‖, norm_pos_iff.2 (gramSchmidt_ne_zero j hA), ?_⟩
    have hne : (‖gramSchmidt 𝕜 f j‖ : 𝕜) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.2 (gramSchmidt_ne_zero j hA)).ne'
    simp only [R, q, gramSchmidtNormed, Matrix.of_apply, inner_smul_left, inner_gramSchmidt_self]
    simp only [map_inv₀, RCLike.conj_ofReal]
    field_simp
  have hAQR : A = Q * R := by
    ext i j
    have := congrArg (fun x : EuclideanSpace 𝕜 (Fin n) => x.ofLp i) (hexp j)
    simp only [hf, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [Matrix.mul_apply, Q]
    rw [show A i j = _ from this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  refine ⟨(Q, R), ⟨?_, fun i j hij => hRtri i j hij, fun i => ?_, hAQR⟩, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    exact hQ
  · obtain ⟨r, hr, h⟩ := hRpos i
    change 0 < R i i
    rw [h]; exact_mod_cast hr
  · rintro ⟨Q', R'⟩ ⟨hQ', htri, hpos, hAeq⟩
    dsimp only at hQ' htri hpos hAeq
    have hQ'1 : Q'ᴴ * Q' = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ'
    have hq' := (qr_orthonormal_cols_iff Q').2 hQ'1
    have hfc : ∀ j, f j = ∑ i, R' i j • (WithLp.toLp 2 (fun l => Q' l i) :
        EuclideanSpace 𝕜 (Fin n)) := by
      intro j
      ext l
      have := congrFun (congrFun hAeq l) j
      simp only [Matrix.mul_apply] at this
      simp [hf, this, mul_comm]
    have hpos' : ∀ j, ∃ r : ℝ, 0 < r ∧ R' j j = r := by
      intro j
      have h := RCLike.pos_iff.1 (hpos j)
      exact ⟨RCLike.re (R' j j), h.1, (RCLike.conj_eq_iff_re.1 (RCLike.conj_eq_iff_im.2 h.2)).symm⟩
    have hqq := gramSchmidtNormed_unique f _ hq' R' (fun i j hij => htri hij) hpos' hfc
    have hQQ : Q' = Q := by
      ext i j
      have := congrFun hqq j
      have h2 := congrArg (fun x : EuclideanSpace 𝕜 (Fin n) => x.ofLp i) this
      simpa [Q, q] using h2.symm
    subst hQQ
    have hAR : A = Q * R := hAQR
    have : R' = R := by
      have h1 : Q * R' = Q * R := hAeq.symm.trans hAR
      calc R' = (Qᴴ * Q) * R' := by rw [hQ'1, Matrix.one_mul]
        _ = Qᴴ * (Q * R') := by rw [Matrix.mul_assoc]
        _ = Qᴴ * (Q * R) := by rw [h1]
        _ = (Qᴴ * Q) * R := by rw [Matrix.mul_assoc]
        _ = R := by rw [hQ'1, Matrix.one_mul]
    rw [this]

end QRTheorem

section Cholesky

open scoped MatrixOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Axler 7.63 (Cholesky factorization): a positive definite matrix `B` equals `Rᴴ R` for a unique
upper-triangular `R` with positive diagonal. -/
@[kb "axler2024" "7.63, p. 285"]
theorem axler_7_63 {n : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.PosDef) :
    ∃! R : Matrix (Fin n) (Fin n) 𝕜, R.IsUpperTriangular ∧ (∀ i, 0 < R i i) ∧ B = Rᴴ * R := by
  have hnn : (0 : Matrix (Fin n) (Fin n) 𝕜) ≤ B := Matrix.nonneg_iff_posSemidef.2 hB.posSemidef
  set A : Matrix (Fin n) (Fin n) 𝕜 := CFC.sqrt B with hAdef
  have hAh : Aᴴ = A := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg B)).isHermitian
  have hBA : B = Aᴴ * A := by
    rw [hAh, ← sq, hAdef, CFC.sq_sqrt B hnn]
  have hAcols : LinearIndependent 𝕜
      (fun j : Fin n => (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n))) := by
    rw [Fintype.linearIndependent_iff]
    intro x hx
    have hAx : A *ᵥ x = 0 := by
      ext i
      have := congrArg (fun y : EuclideanSpace 𝕜 (Fin n) => y.ofLp i) hx
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    by_contra h
    have hx0 : x ≠ 0 := fun h0 => h (fun i => by simp [h0])
    have h1 := hB.dotProduct_mulVec_pos hx0
    rw [hBA, ← Matrix.mulVec_mulVec, hAx] at h1
    simp at h1
  obtain ⟨⟨Q, R⟩, ⟨hQ, hRtri, hRpos, hAQR⟩, huniq⟩ := axler_7_58 A hAcols
  have hQ1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  refine ⟨R, ⟨hRtri, hRpos, ?_⟩, ?_⟩
  · dsimp only at hAQR
    rw [hBA, hAQR, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ1,
      Matrix.one_mul]
  · rintro S ⟨hStri, hSpos, hBS⟩
    have hdet : S.det ≠ 0 :=
      (hStri.det_ne_zero_iff).2 fun i => (hSpos i).ne'
    have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    have hSS' : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    have hAA : Aᴴ * A = Sᴴ * S := hBA.symm.trans hBS
    have h1 : (S⁻¹)ᴴ * Sᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hSS, Matrix.conjTranspose_one]
    have hX : (A * S⁻¹) ∈ Matrix.unitaryGroup (Fin n) 𝕜 := by
      rw [Matrix.mem_unitaryGroup_iff']
      show (A * S⁻¹)ᴴ * (A * S⁻¹) = 1
      calc (A * S⁻¹)ᴴ * (A * S⁻¹) = (S⁻¹)ᴴ * (Aᴴ * A) * S⁻¹ := by
            rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = (S⁻¹)ᴴ * Sᴴ * (S * S⁻¹) := by rw [hAA]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, hSS, Matrix.mul_one]
    have hAXS : A = (A * S⁻¹) * S := by rw [Matrix.mul_assoc, hSS', Matrix.mul_one]
    have := huniq (A * S⁻¹, S) ⟨hX, hStri, hSpos, hAXS⟩
    exact congrArg Prod.snd this

end Cholesky

end UndergradKB.LinearAlgebra
