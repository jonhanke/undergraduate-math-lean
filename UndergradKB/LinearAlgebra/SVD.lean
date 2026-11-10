import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr
import UndergradKB.LinearAlgebra.Pseudoinverse

/-! # Singular value decomposition (Axler, sections 7E and 7F)

Rows LA-433 to LA-438, LA-441, LA-443.  Mathlib already defines the singular values
(`LinearMap.singularValues`, zero-indexed, finitely supported, in decreasing order); we use them.
Axler's `s₁ ≥ ... ≥ s_m` is `T.singularValues 0, ..., T.singularValues (m-1)`.
Mathlib's inner product is conjugate-linear in the first slot, so Axler's `⟨v, e⟩` is `⟪e, v⟫`.
-/

set_option linter.unusedSectionVars false

open Module InnerProductSpace
open scoped InnerProductSpace

namespace UndergradKB.LinearAlgebra

/-! ### Diagonal rectangular matrices (7.74) -/

/-- Axler's notion of an `M`-by-`N` diagonal matrix: all entries outside the positions `(k, k)`
vanish. -/
def IsRectDiagonal {M N : ℕ} {F : Type*} [Zero F] (A : Matrix (Fin M) (Fin N) F) : Prop :=
  ∀ (i : Fin M) (j : Fin N), (i : ℕ) ≠ j → A i j = 0

/-- On square matrices, Axler's diagonal matrices are Mathlib's `Matrix.IsDiag`. -/
@[kb "axler2024" "7.74, p. 292"]
theorem axler_7_74 {n : ℕ} {F : Type*} [Zero F] (A : Matrix (Fin n) (Fin n) F) :
    IsRectDiagonal A ↔ A.IsDiag := by
  constructor
  · intro h i j hij
    exact h i j (fun e => hij (Fin.ext e))
  · intro h i j hij
    exact h (fun e => hij (congrArg Fin.val e))

namespace SVD

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
  (T : V →ₗ[𝕜] W)

/-- An orthonormal eigenbasis of `T* T`. -/
noncomputable def eb [FiniteDimensional 𝕜 W] : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

variable [FiniteDimensional 𝕜 W]

lemma adj_apply_eb (i : Fin (finrank 𝕜 V)) :
    LinearMap.adjoint T (T (eb T i)) = ((T.singularValues i : 𝕜) ^ 2) • eb T i := by
  have := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [eb, this, ← T.sq_singularValues_fin rfl i]
  simp

lemma inner_eb_eb (i j : Fin (finrank 𝕜 V)) :
    ⟪eb T i, eb T j⟫_𝕜 = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (eb T).orthonormal i j

lemma inner_T_eb (i j : Fin (finrank 𝕜 V)) :
    ⟪T (eb T i), T (eb T j)⟫_𝕜 = if i = j then ((T.singularValues i : 𝕜) ^ 2) else 0 := by
  rw [← LinearMap.adjoint_inner_left, adj_apply_eb, inner_smul_left, inner_eb_eb]
  split_ifs <;> simp

lemma norm_sq_T_eb (i : Fin (finrank 𝕜 V)) : ‖T (eb T i)‖ ^ 2 = T.singularValues i ^ 2 := by
  have h := inner_T_eb T i i
  simp only [↓reduceIte, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

lemma T_eb_eq_zero {i : Fin (finrank 𝕜 V)} (h : T.singularValues i = 0) : T (eb T i) = 0 := by
  have := norm_sq_T_eb T i
  rw [h] at this
  simpa using this

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- Pythagoras for a map sending an orthonormal basis to a pairwise orthogonal family. -/
lemma norm_sq_apply_of_orth {ι : Type*} [Fintype ι] [DecidableEq ι] (T' : V →ₗ[𝕜] W)
    (b : OrthonormalBasis ι 𝕜 V) (h : ∀ i j, i ≠ j → ⟪T' (b i), T' (b j)⟫_𝕜 = 0) (v : V) :
    ‖T' v‖ ^ 2 = ∑ i, ‖⟪b i, v⟫_𝕜‖ ^ 2 * ‖T' (b i)‖ ^ 2 := by
  have hv : T' v = ∑ i, ⟪b i, v⟫_𝕜 • T' (b i) := by
    conv_lhs => rw [← b.sum_repr' v]
    simp [map_sum]
  have : ((‖T' v‖ ^ 2 : ℝ) : 𝕜) = ((∑ i, ‖⟪b i, v⟫_𝕜‖ ^ 2 * ‖T' (b i)‖ ^ 2 : ℝ) : 𝕜) := by
    rw [show ((‖T' v‖ ^ 2 : ℝ) : 𝕜) = ⟪T' v, T' v⟫_𝕜 by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; ring]
    conv_lhs => rw [hv]
    rw [sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [inner_self_eq_norm_sq_to_K, ← mul_assoc, RCLike.mul_conj]
    · intro j _ hj
      rw [h i j (Ne.symm hj)]; simp
    · simp
  exact_mod_cast this


lemma norm_sq_T (v : V) :
    ‖T v‖ ^ 2 = ∑ i, ‖⟪eb T i, v⟫_𝕜‖ ^ 2 * T.singularValues i ^ 2 := by
  rw [norm_sq_apply_of_orth T (eb T)]
  · simp only [norm_sq_T_eb]
  · intro i j hij
    rw [inner_T_eb]; simp [hij]

lemma norm_le_singularValues_zero (v : V) : ‖T v‖ ≤ T.singularValues 0 * ‖v‖ := by
  have h0 : 0 ≤ T.singularValues 0 := T.singularValues_nonneg 0
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [norm_sq_T, mul_pow, ← (eb T).sum_sq_norm_inner_right v, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : T.singularValues i ≤ T.singularValues 0 := T.singularValues_antitone (Nat.zero_le _)
  have h2 := T.singularValues_nonneg i
  have : T.singularValues i ^ 2 ≤ T.singularValues 0 ^ 2 := by gcongr
  nlinarith [sq_nonneg ‖⟪eb T i, v⟫_𝕜‖]

lemma exists_norm_eq_singularValues_zero :
    ∃ v : V, ‖v‖ ≤ 1 ∧ ‖T v‖ = T.singularValues 0 := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 V) with h | h
  · refine ⟨0, by simp, ?_⟩
    rw [T.singularValues_of_finrank_le h.le]; simp
  · refine ⟨eb T ⟨0, h⟩, by simp, ?_⟩
    have := norm_sq_T_eb T ⟨0, h⟩
    exact (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg _)).mp this

/-- A linear map between finite-dimensional inner product spaces is an isometry exactly when all
of its singular values (those indexed below the dimension of the domain) equal `1`. -/
@[kb "axler2024" "7.69, p. 290"]
theorem axler_7_69 :
    (∀ v : V, ‖T v‖ = ‖v‖) ↔ ∀ i < finrank 𝕜 V, T.singularValues i = 1 := by
  constructor
  · intro h i hi
    have h1 := norm_sq_T_eb T ⟨i, hi⟩
    rw [h, OrthonormalBasis.norm_eq_one, one_pow] at h1
    have h2 := T.singularValues_nonneg i
    have : T.singularValues i ^ 2 = 1 ^ 2 := by rw [← h1]; simp
    exact (sq_eq_sq₀ h2 zero_le_one).mp this
  · intro h v
    have h1 : ‖T v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sq_T, ← (eb T).sum_sq_norm_inner_right v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h i i.2]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

/-- For every `v`, `‖T v‖ ≤ s₁ ‖v‖` where `s₁` is the largest singular value. -/
@[kb "axler2024" "7.82, p. 298"]
theorem axler_7_82 (v : V) : ‖T v‖ ≤ T.singularValues 0 * ‖v‖ :=
  norm_le_singularValues_zero T v

/-- The maximum of `‖T v‖` over the closed unit ball exists and equals the largest singular value. -/
@[kb "axler2024" "7.85, p. 298"]
theorem axler_7_85 :
    IsGreatest {x : ℝ | ∃ v : V, ‖v‖ ≤ 1 ∧ x = ‖T v‖} (T.singularValues 0) := by
  constructor
  · obtain ⟨v, hv, h⟩ := exists_norm_eq_singularValues_zero T
    exact ⟨v, hv, h.symm⟩
  · rintro x ⟨v, hv, rfl⟩
    calc ‖T v‖ ≤ T.singularValues 0 * ‖v‖ := norm_le_singularValues_zero T v
      _ ≤ T.singularValues 0 * 1 := by
        gcongr
        exact T.singularValues_nonneg 0
      _ = _ := mul_one _

/-- Three descriptions of the norm of a linear map: it is the largest singular value, the maximum
of `‖T v‖` over unit vectors (when the domain is nontrivial), and the least `c ≥ 0` with
`‖T v‖ ≤ c ‖v‖` for all `v`. -/
@[kb "axler2024" "7.88, p. 300"]
theorem axler_7_88 :
    ‖LinearMap.toContinuousLinearMap T‖ = T.singularValues 0 ∧
    (Nontrivial V → IsGreatest {x : ℝ | ∃ v : V, ‖v‖ = 1 ∧ x = ‖T v‖} (T.singularValues 0)) ∧
    IsLeast {c : ℝ | 0 ≤ c ∧ ∀ v : V, ‖T v‖ ≤ c * ‖v‖} (T.singularValues 0) := by
  have hle : ∀ v : V, ‖T v‖ ≤ T.singularValues 0 * ‖v‖ := norm_le_singularValues_zero T
  have hnorm : ‖LinearMap.toContinuousLinearMap T‖ = T.singularValues 0 := by
    apply le_antisymm
    · exact ContinuousLinearMap.opNorm_le_bound _ (T.singularValues_nonneg 0) hle
    · obtain ⟨v, hv, h⟩ := exists_norm_eq_singularValues_zero T
      have := (LinearMap.toContinuousLinearMap T).le_opNorm v
      simp only [LinearMap.coe_toContinuousLinearMap'] at this
      rw [← h]
      calc ‖T v‖ ≤ ‖LinearMap.toContinuousLinearMap T‖ * ‖v‖ := this
        _ ≤ ‖LinearMap.toContinuousLinearMap T‖ * 1 := by gcongr
        _ = _ := mul_one _
  refine ⟨hnorm, ?_, ?_⟩
  · intro hnt
    have hpos : 0 < finrank 𝕜 V := Module.finrank_pos
    constructor
    · refine ⟨eb T ⟨0, hpos⟩, by simp, ?_⟩
      have := norm_sq_T_eb T ⟨0, hpos⟩
      exact ((sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg _)).mp this).symm
    · rintro x ⟨v, hv, rfl⟩
      simpa [hv] using hle v
  · refine ⟨⟨T.singularValues_nonneg 0, hle⟩, ?_⟩
    rintro c ⟨hc, hcv⟩
    rw [← hnorm]
    exact ContinuousLinearMap.opNorm_le_bound _ hc hcv


/-! ### The singular value decomposition (7.70) -/

omit [FiniteDimensional 𝕜 W] in
lemma rank_le : finrank 𝕜 T.range ≤ finrank 𝕜 V := T.finrank_range_le

/-- The right singular vectors `e_k`, `k < dim range T`. -/
noncomputable def eK (k : Fin (finrank 𝕜 T.range)) : V :=
  eb T (Fin.castLE (rank_le T) k)

/-- The left singular vectors `f_k = T e_k / s_k`, `k < dim range T`. -/
noncomputable def fK (k : Fin (finrank 𝕜 T.range)) : W :=
  ((T.singularValues (Fin.castLE (rank_le T) k))⁻¹ : 𝕜) • T (eb T (Fin.castLE (rank_le T) k))

lemma sv_pos (k : Fin (finrank 𝕜 T.range)) :
    0 < T.singularValues (Fin.castLE (rank_le T) k) := by
  rw [T.singularValues_pos_iff_lt_finrank_range]
  simp

lemma orthonormal_eK : Orthonormal 𝕜 (eK T) :=
  (eb T).orthonormal.comp _ (Fin.castLE_injective _)

lemma T_eK (k : Fin (finrank 𝕜 T.range)) :
    T (eK T k) = (T.singularValues (Fin.castLE (rank_le T) k) : 𝕜) • fK T k := by
  have := (sv_pos T k).ne'
  simp only [eK, fK, smul_smul]
  rw [mul_inv_cancel₀ (by exact_mod_cast this), one_smul]

lemma orthonormal_fK : Orthonormal 𝕜 (fK T) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hi : (T.singularValues (Fin.castLE (rank_le T) i) : 𝕜) ≠ 0 := by
    exact_mod_cast (sv_pos T i).ne'
  have hj : (T.singularValues (Fin.castLE (rank_le T) j) : 𝕜) ≠ 0 := by
    exact_mod_cast (sv_pos T j).ne'
  simp only [fK]
  rw [inner_smul_left, inner_smul_right, inner_T_eb]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [map_inv₀, RCLike.conj_ofReal]
    field_simp
  · have : Fin.castLE (rank_le T) i ≠ Fin.castLE (rank_le T) j := fun h =>
      hij (Fin.castLE_injective _ h)
    simp [hij, this]

lemma T_eq_sum (v : V) :
    T v = ∑ k : Fin (finrank 𝕜 T.range),
      (T.singularValues (k : ℕ) : 𝕜) • ⟪eK T k, v⟫_𝕜 • fK T k := by
  set g : Fin (finrank 𝕜 V) → W := fun i => ⟪eb T i, v⟫_𝕜 • T (eb T i) with hg
  have h1 : T v = ∑ i, g i := by
    conv_lhs => rw [← (eb T).sum_repr' v]
    simp [map_sum, hg]
  have h2 : ∑ i, g i = ∑ k : Fin (finrank 𝕜 T.range), g (Fin.castLE (rank_le T) k) := by
    refine Eq.trans ?_ (Finset.sum_map Finset.univ (Fin.castLEEmb (rank_le T)) g)
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have hr : finrank 𝕜 T.range ≤ i := by
      by_contra hlt
      exact hi (Finset.mem_map.mpr ⟨⟨i, not_le.mp hlt⟩, Finset.mem_univ _, rfl⟩)
    have : T.singularValues i = 0 := (T.singularValues_eq_zero_iff_le_finrank_range).mpr hr
    simp [hg, T_eb_eq_zero T this]
  rw [h1, h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := T_eK T k
  simp only [hg, eK] at this ⊢
  rw [this, smul_smul, smul_smul, mul_comm]
  rfl

/-- Singular value decomposition: if `s₁ ≥ ... ≥ s_m` are the positive singular values of `T`
(`m = dim range T`), there are orthonormal lists `e` in `V` and `f` in `W` of length `m` with
`T v = ∑ s_k ⟨v, e_k⟩ f_k`.  In Mathlib's convention `⟨v, e_k⟩` is `⟪e_k, v⟫`. -/
@[kb "axler2024" "7.70, p. 291"]
theorem axler_7_70 :
    ∃ (e : Fin (finrank 𝕜 T.range) → V) (f : Fin (finrank 𝕜 T.range) → W),
      Orthonormal 𝕜 e ∧ Orthonormal 𝕜 f ∧
      ∀ v : V, T v = ∑ k : Fin (finrank 𝕜 T.range),
        (T.singularValues (k : ℕ) : 𝕜) • ⟪e k, v⟫_𝕜 • f k :=
  ⟨eK T, fK T, orthonormal_eK T, orthonormal_fK T, T_eq_sum T⟩


/-! ### Matrix version (7.80) -/

open Matrix in
lemma finrank_range_toEuclideanLin {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [DecidableEq m] (A : Matrix m n 𝕜) :
    finrank 𝕜 (LinearMap.range (Matrix.toEuclideanLin A)) = A.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun m 𝕜).toBasis
    (EuclideanSpace.basisFun n 𝕜).toBasis]
  rfl

open Matrix in
/-- Matrix form of the singular value decomposition: a matrix of rank `m` factors as `B D C*`,
where `B` and `C` have orthonormal columns (`B* B = 1`, `C* C = 1`) and `D` is an `m × m` diagonal
matrix with positive real diagonal entries (here the positive singular values). -/
@[kb "axler2024" "7.80, p. 295"]
theorem axler_7_80 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq m]
    (A : Matrix m n 𝕜) :
    ∃ (B : Matrix m (Fin A.rank) 𝕜) (d : Fin A.rank → ℝ) (C : Matrix n (Fin A.rank) 𝕜),
      Bᴴ * B = 1 ∧ Cᴴ * C = 1 ∧ (∀ k, 0 < d k) ∧
      A = B * Matrix.diagonal (fun k => (d k : 𝕜)) * Cᴴ := by
  set T := Matrix.toEuclideanLin A with hT
  have hr := finrank_range_toEuclideanLin A
  -- transport the decomposition along `hr`
  suffices H : ∀ r : ℕ, finrank 𝕜 T.range = r →
      ∃ (B : Matrix m (Fin r) 𝕜) (d : Fin r → ℝ) (C : Matrix n (Fin r) 𝕜),
        Bᴴ * B = 1 ∧ Cᴴ * C = 1 ∧ (∀ k, 0 < d k) ∧
        A = B * Matrix.diagonal (fun k => (d k : 𝕜)) * Cᴴ from H _ hr
  intro r hr'
  subst hr'
  refine ⟨Matrix.of fun i k => (fK T k) i, fun k => T.singularValues (k : ℕ),
    Matrix.of fun j k => (eK T k) j, ?_, ?_, fun k => (sv_pos T k), ?_⟩
  · ext k l
    have := orthonormal_iff_ite.mp (orthonormal_fK T) k l
    simp only [PiLp.inner_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.conjTranspose_apply, mul_comm]
  · ext k l
    have := orthonormal_iff_ite.mp (orthonormal_eK T) k l
    simp only [PiLp.inner_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.conjTranspose_apply, mul_comm]
  · ext i j
    have h := congrArg (fun w => w i) (T_eq_sum T (EuclideanSpace.single j (1 : 𝕜)))
    have hA : T (EuclideanSpace.single j (1 : 𝕜)) i = A i j := by
      simp [hT, Matrix.mulVec, dotProduct, Pi.single_apply]
    simp only [hA] at h
    rw [h]
    simp [Matrix.mul_apply, Matrix.diagonal_apply, EuclideanSpace.inner_single_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.real_smul_eq_coe_mul]; ring


/-! ### Adjoint and pseudoinverse (7.75) -/

-- The pseudoinverse `pinv` (Axler 6.68) is the one of `UndergradKB.LinearAlgebra.Pseudoinverse`.

lemma pinv_eq_of {w : W} {v : V} (hv : v ∈ (LinearMap.ker T)ᗮ)
    (h : T v = (LinearMap.range T).starProjection w) : pinv T w = v := by
  have : (restrictPerpEquiv T).symm ((LinearMap.range T).orthogonalProjectionOnto w) = ⟨v, hv⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [show (((restrictPerpEquiv T) ⟨v, hv⟩ : LinearMap.range T) : W) = T v from rfl, h]
    rfl
  simp [pinv, this]

section SVDformulas

variable {m : ℕ} (s : Fin m → ℝ) (hs : ∀ k, 0 < s k) (e : Fin m → V) (f : Fin m → W)
  (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
  (hT : ∀ v, T v = ∑ k, (s k : 𝕜) • ⟪e k, v⟫_𝕜 • f k)

include he hT in
lemma T_e (k : Fin m) : T (e k) = (s k : 𝕜) • f k := by
  rw [hT, Finset.sum_eq_single k]
  · have := orthonormal_iff_ite.mp he k k
    simp only [this, ↓reduceIte, one_smul]
  · intro j _ hj
    have := orthonormal_iff_ite.mp he j k
    simp [this, hj]
  · simp

include hf in
lemma inner_f_T (hT : ∀ v, T v = ∑ k, (s k : 𝕜) • ⟪e k, v⟫_𝕜 • f k) (v : V) (k : Fin m) :
    ⟪f k, T v⟫_𝕜 = (s k : 𝕜) * ⟪e k, v⟫_𝕜 := by
  rw [hT v]
  have := hf.inner_right_fintype (fun j => (s j : 𝕜) * ⟪e j, v⟫_𝕜) k
  simpa [smul_smul] using this

include he hf hs hT in
/-- Singular value decomposition of the adjoint and of the pseudoinverse: from a decomposition
`T v = ∑ s_k ⟨v, e_k⟩ f_k` with positive `s_k` and orthonormal `e`, `f`, one gets
`T* w = ∑ s_k ⟨w, f_k⟩ e_k` and `T† w = ∑ (⟨w, f_k⟩ / s_k) e_k`. -/
@[kb "axler2024" "7.75, p. 293"]
theorem axler_7_75 (w : W) :
    LinearMap.adjoint T w = ∑ k, (s k : 𝕜) • ⟪f k, w⟫_𝕜 • e k ∧
    pinv T w = ∑ k, ((s k : 𝕜)⁻¹) • ⟪f k, w⟫_𝕜 • e k := by
  have hs' : ∀ k, (s k : 𝕜) ≠ 0 := fun k => by exact_mod_cast (hs k).ne'
  constructor
  · apply ext_inner_left 𝕜
    intro v
    rw [LinearMap.adjoint_inner_right, hT v, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    rw [← inner_conj_symm (e k) v, starRingEnd_self_apply]
    ring
  · set v : V := ∑ k, ((s k : 𝕜)⁻¹) • ⟪f k, w⟫_𝕜 • e k with hv
    have hinner : ∀ j, ⟪e j, v⟫_𝕜 = ((s j : 𝕜)⁻¹) * ⟪f j, w⟫_𝕜 := by
      intro j
      have := he.inner_right_fintype (fun k => ((s k : 𝕜)⁻¹) * ⟪f k, w⟫_𝕜) j
      simpa [hv, smul_smul] using this
    have hTv : T v = ∑ k, ⟪f k, w⟫_𝕜 • f k := by
      rw [hT v]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hinner k, smul_smul, ← mul_assoc, mul_inv_cancel₀ (hs' k), one_mul]
    refine pinv_eq_of T ?_ ?_
    · -- v is orthogonal to the kernel
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hu0 : T u = 0 := hu
      have : ∀ k, ⟪e k, u⟫_𝕜 = 0 := by
        intro k
        have h1 := inner_f_T T s e f hf hT u k
        rw [hu0, inner_zero_right] at h1
        exact (mul_eq_zero.mp h1.symm).resolve_left (hs' k)
      rw [hv, inner_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk : ⟪u, e k⟫_𝕜 = 0 := by rw [← inner_conj_symm, this k, map_zero]
      rw [inner_smul_right, inner_smul_right, hk]
      simp
    · symm
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · rw [hTv]
        refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
        have : f k = T ((s k : 𝕜)⁻¹ • e k) := by
          rw [map_smul, T_e T s e f he hT k, smul_smul, inv_mul_cancel₀ (hs' k), one_smul]
        rw [this]; exact LinearMap.mem_range_self _ _
      · rintro y ⟨z, rfl⟩
        have h0 : ∀ j, ⟪w - T v, f j⟫_𝕜 = 0 := by
          intro j
          rw [hTv, inner_sub_left, hf.inner_left_fintype (fun k => ⟪f k, w⟫_𝕜) j,
            inner_conj_symm, sub_self]
        rw [hT z, inner_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [inner_smul_right, inner_smul_right, h0 j]; simp

end SVDformulas


/-! ### Best low-rank approximation (7.92) -/

/-- Pythagoras for a combination of an orthonormal family. -/
lemma norm_sq_sum_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {ι : Type*} (g : ι → E) (hg : Orthonormal 𝕜 g) (J : Finset ι) (c : ι → 𝕜) :
    ‖∑ j ∈ J, c j • g j‖ ^ 2 = ∑ j ∈ J, ‖c j‖ ^ 2 := by
  have : ((‖∑ j ∈ J, c j • g j‖ ^ 2 : ℝ) : 𝕜) = ((∑ j ∈ J, ‖c j‖ ^ 2 : ℝ) : 𝕜) := by
    rw [show ((‖∑ j ∈ J, c j • g j‖ ^ 2 : ℝ) : 𝕜) = ⟪∑ j ∈ J, c j • g j, ∑ j ∈ J, c j • g j⟫_𝕜 by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; ring]
    rw [sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_smul_left, hg.inner_right_sum c hi, RCLike.conj_mul]
  exact_mod_cast this

/-- The truncated sum `∑_{j ∈ J} s_j ⟨·, e_j⟩ f_j` as a linear map. -/
noncomputable def trunc (𝕜 : Type*) [RCLike 𝕜] {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] {m : ℕ}
    (s : Fin m → ℝ) (e : Fin m → V) (f : Fin m → W) (J : Finset (Fin m)) : V →ₗ[𝕜] W :=
  ∑ j ∈ J, (s j : 𝕜) • (innerₛₗ 𝕜 (e j)).smulRight (f j)

lemma trunc_apply {m : ℕ} (s : Fin m → ℝ) (e : Fin m → V) (f : Fin m → W)
    (J : Finset (Fin m)) (v : V) :
    trunc 𝕜 s e f J v = ∑ j ∈ J, (s j : 𝕜) • ⟪e j, v⟫_𝕜 • f j := by
  simp [trunc, LinearMap.sum_apply]

section EY

variable {m : ℕ} (s : Fin m → ℝ) (e : Fin m → V) (f : Fin m → W)
  (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
  (hT : ∀ v, T v = ∑ k, (s k : 𝕜) • ⟪e k, v⟫_𝕜 • f k)
  (hpos : ∀ k, 0 < s k) (hanti : Antitone s)

include he hf hT hpos hanti in
lemma EY_lower (k : ℕ) (hk : k < m) (S : V →ₗ[𝕜] W) (hS : finrank 𝕜 S.range ≤ k) :
    s ⟨k, hk⟩ ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ := by
  let ι : Fin (k + 1) → Fin m := fun i => ⟨i, lt_of_lt_of_le i.2 hk⟩
  have hι : Function.Injective ι := fun a b h => Fin.ext (by simpa [ι] using congrArg Fin.val h)
  let comb : (Fin (k + 1) → 𝕜) →ₗ[𝕜] V := Fintype.linearCombination 𝕜 (fun i => e (ι i))
  let Φ : (Fin (k + 1) → 𝕜) →ₗ[𝕜] S.range := S.rangeRestrict ∘ₗ comb
  have hlt : finrank 𝕜 S.range < finrank 𝕜 (Fin (k + 1) → 𝕜) := by
    simpa using Nat.lt_succ_of_le hS
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt hlt)
  set u : V := ∑ i, a i • e (ι i) with hu
  have hSu : S u = 0 := by
    have : Φ a = 0 := ha
    have h2 := congrArg Subtype.val this
    simpa [Φ, comb, Fintype.linearCombination_apply, hu] using h2
  have hnorm_u : ‖u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 :=
    norm_sq_sum_orthonormal (fun i => e (ι i)) (he.comp _ hι) Finset.univ a
  have hTu : T u = ∑ i, (a i * (s (ι i) : 𝕜)) • f (ι i) := by
    rw [hu, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, T_e T s e f he hT (ι i), smul_smul]
  have hnorm_Tu : ‖T u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 * s (ι i) ^ 2 := by
    rw [hTu, norm_sq_sum_orthonormal (fun i => f (ι i)) (hf.comp _ hι) Finset.univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul]; simp [mul_pow, abs_of_pos (hpos _)]
  have hpos_u : 0 < ‖u‖ ^ 2 := by
    rw [hnorm_u]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (funext h)
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖a i‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  have hge : s ⟨k, hk⟩ ^ 2 * ‖u‖ ^ 2 ≤ ‖T u‖ ^ 2 := by
    rw [hnorm_u, hnorm_Tu, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : s ⟨k, hk⟩ ≤ s (ι i) := hanti (by
      show (i : ℕ) ≤ k
      exact Nat.lt_succ_iff.mp i.2)
    have h2 : s ⟨k, hk⟩ ^ 2 ≤ s (ι i) ^ 2 := by
      have := hpos ⟨k, hk⟩
      gcongr
    nlinarith [sq_nonneg ‖a i‖]
  have hu0 : 0 < ‖u‖ := by
    rcases (norm_nonneg u).lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos_u; simp at hpos_u
  have hle : ‖(T - S) u‖ ≤ ‖LinearMap.toContinuousLinearMap (T - S)‖ * ‖u‖ :=
    (LinearMap.toContinuousLinearMap (T - S)).le_opNorm u
  simp only [LinearMap.sub_apply, hSu, sub_zero] at hle
  have : (s ⟨k, hk⟩ * ‖u‖) ^ 2 ≤ (‖LinearMap.toContinuousLinearMap (T - S)‖ * ‖u‖) ^ 2 := by
    calc (s ⟨k, hk⟩ * ‖u‖) ^ 2 = s ⟨k, hk⟩ ^ 2 * ‖u‖ ^ 2 := by ring
      _ ≤ ‖T u‖ ^ 2 := hge
      _ ≤ _ := by gcongr
  have := le_of_sq_le_sq this (by positivity)
  exact le_of_mul_le_mul_right this hu0


include hT in
lemma EY_tail (k : ℕ) (v : V) :
    (T - trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)) v =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
        (s j : 𝕜) • ⟪e j, v⟫_𝕜 • f j := by
  rw [LinearMap.sub_apply, hT v, trunc_apply,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin m => (j : ℕ) < k)]
  abel

include he hf hT hpos hanti in
lemma EY_upper (k : ℕ) (hk : k < m) (v : V) :
    ‖(T - trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)) v‖ ≤ s ⟨k, hk⟩ * ‖v‖ := by
  have hsk : 0 ≤ s ⟨k, hk⟩ := (hpos _).le
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [EY_tail T s e f hT k v]
  simp only [smul_smul]
  rw [norm_sq_sum_orthonormal f hf]
  calc ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k), ‖(s j : 𝕜) * ⟪e j, v⟫_𝕜‖ ^ 2
      ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
          s ⟨k, hk⟩ ^ 2 * ‖⟪e j, v⟫_𝕜‖ ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : ¬ (j : ℕ) < k := (Finset.mem_filter.mp hj).2
        have h1 : s j ≤ s ⟨k, hk⟩ := hanti (by show k ≤ (j : ℕ); omega)
        have h2 : s j ^ 2 ≤ s ⟨k, hk⟩ ^ 2 := by
          have := (hpos j).le
          gcongr
        rw [norm_mul, mul_pow]
        simp only [RCLike.norm_ofReal, sq_abs]
        gcongr
    _ = s ⟨k, hk⟩ ^ 2 * ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
          ‖⟪e j, v⟫_𝕜‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ s ⟨k, hk⟩ ^ 2 * ‖v‖ ^ 2 := by
        gcongr
        exact he.sum_inner_products_le v
    _ = _ := by ring

lemma trunc_e (k : ℕ) (j : Fin m) (hj : (j : ℕ) < k) (he : Orthonormal 𝕜 e) :
    trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) (e j) =
      (s j : 𝕜) • f j := by
  rw [trunc_apply, Finset.sum_eq_single j]
  · have := orthonormal_iff_ite.mp he j j
    simp only [this, ↓reduceIte, one_smul]
  · intro i _ hij
    have := orthonormal_iff_ite.mp he i j
    simp [this, hij]
  · intro h; exact absurd (by simpa using hj) h

include he hf hT hpos hanti in
lemma EY_upper_eq (k : ℕ) (hk : k < m) :
    ‖LinearMap.toContinuousLinearMap
        (T - trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k))‖ = s ⟨k, hk⟩ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (hpos _).le (EY_upper T s e f he hf hT hpos hanti k hk)
  · have h := (LinearMap.toContinuousLinearMap
        (T - trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k))).le_opNorm (e ⟨k, hk⟩)
    have hk' : (T - trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)) (e ⟨k, hk⟩) =
        (s ⟨k, hk⟩ : 𝕜) • f ⟨k, hk⟩ := by
      rw [LinearMap.sub_apply, T_e T s e f he hT, trunc_apply, Finset.sum_eq_zero, sub_zero]
      intro i hi
      have hik : i ≠ ⟨k, hk⟩ := fun h => by
        have := (Finset.mem_filter.mp hi).2
        rw [h] at this; exact lt_irrefl _ this
      have := orthonormal_iff_ite.mp he i ⟨k, hk⟩
      simp [this, hik]
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    rw [hk', norm_smul, hf.norm_eq_one, he.norm_eq_one, mul_one, mul_one, RCLike.norm_ofReal,
      abs_of_pos (hpos _)] at h
    exact h

include he hf hT hpos in
lemma EY_rank (k : ℕ) (hk : k ≤ m) :
    finrank 𝕜 (trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)).range = k := by
  let ι : Fin k → Fin m := fun i => ⟨i, lt_of_lt_of_le i.2 hk⟩
  have hι : Function.Injective ι := fun a b h => Fin.ext (by simpa [ι] using congrArg Fin.val h)
  have hli : LinearIndependent 𝕜 (fun i => f (ι i)) := (hf.comp _ hι).linearIndependent
  have hr : (trunc 𝕜 s e f (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)).range =
      Submodule.span 𝕜 (Set.range fun i => f (ι i)) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [trunc_apply]
      refine Submodule.sum_mem _ fun j hj => ?_
      have hj' : (j : ℕ) < k := (Finset.mem_filter.mp hj).2
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨j, hj'⟩, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨((s (ι i) : 𝕜)⁻¹) • e (ι i), ?_⟩
      have hne : (s (ι i) : 𝕜) ≠ 0 := by exact_mod_cast (hpos _).ne'
      rw [map_smul, trunc_e s e f k (ι i) i.2 he, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hr, finrank_span_eq_card hli]
  simp

end EY


lemma sv_antitone_fin : Antitone (fun j : Fin (finrank 𝕜 T.range) => T.singularValues (j : ℕ)) :=
  fun _ _ h => T.singularValues_antitone h

lemma sv_pos_fin (j : Fin (finrank 𝕜 T.range)) : 0 < T.singularValues (j : ℕ) := by
  rw [T.singularValues_pos_iff_lt_finrank_range]; exact j.2

/-- Best approximation by maps of small rank (Eckart-Young).  For `k < m` (zero-indexed, so the
bound is the `(k+1)`-st singular value), no linear map of rank at most `k` is closer to `T` in the
operator norm than `s_{k+1}`; and for any singular value decomposition of `T`, truncating it after
`k` terms (`SVD.trunc`) gives a map of rank `k` at exactly that distance. -/
@[kb "axler2024" "7.92, p. 302"]
theorem axler_7_92 (k : ℕ) (hk : k < finrank 𝕜 T.range) :
    IsLeast {x : ℝ | ∃ S : V →ₗ[𝕜] W, finrank 𝕜 S.range ≤ k ∧
        x = ‖LinearMap.toContinuousLinearMap (T - S)‖} (T.singularValues k) ∧
    ∀ (e : Fin (finrank 𝕜 T.range) → V) (f : Fin (finrank 𝕜 T.range) → W),
      Orthonormal 𝕜 e → Orthonormal 𝕜 f →
      (∀ v, T v = ∑ j : Fin (finrank 𝕜 T.range),
        (T.singularValues (j : ℕ) : 𝕜) • ⟪e j, v⟫_𝕜 • f j) →
      finrank 𝕜 (trunc 𝕜 (fun j => T.singularValues (j : ℕ)) e f
        (Finset.univ.filter fun j : Fin (finrank 𝕜 T.range) => (j : ℕ) < k)).range = k ∧
      ‖LinearMap.toContinuousLinearMap (T - trunc 𝕜 (fun j => T.singularValues (j : ℕ)) e f
        (Finset.univ.filter fun j : Fin (finrank 𝕜 T.range) => (j : ℕ) < k))‖ =
        T.singularValues k := by
  have hdata : ∀ (e : Fin (finrank 𝕜 T.range) → V) (f : Fin (finrank 𝕜 T.range) → W),
      Orthonormal 𝕜 e → Orthonormal 𝕜 f →
      (∀ v, T v = ∑ j : Fin (finrank 𝕜 T.range),
        (T.singularValues (j : ℕ) : 𝕜) • ⟪e j, v⟫_𝕜 • f j) →
      finrank 𝕜 (trunc 𝕜 (fun j => T.singularValues (j : ℕ)) e f
        (Finset.univ.filter fun j : Fin (finrank 𝕜 T.range) => (j : ℕ) < k)).range = k ∧
      ‖LinearMap.toContinuousLinearMap (T - trunc 𝕜 (fun j => T.singularValues (j : ℕ)) e f
        (Finset.univ.filter fun j : Fin (finrank 𝕜 T.range) => (j : ℕ) < k))‖ =
        T.singularValues k := by
    intro e f he hf hT
    exact ⟨EY_rank T _ e f he hf hT (sv_pos_fin T) k hk.le,
      EY_upper_eq T _ e f he hf hT (sv_pos_fin T) (sv_antitone_fin T) k hk⟩
  refine ⟨⟨?_, ?_⟩, hdata⟩
  · obtain ⟨h1, h2⟩ := hdata (eK T) (fK T) (orthonormal_eK T) (orthonormal_fK T) (T_eq_sum T)
    exact ⟨_, h1.le, h2.symm⟩
  · rintro x ⟨S, hS, rfl⟩
    exact EY_lower T _ (eK T) (fK T) (orthonormal_eK T) (orthonormal_fK T) (T_eq_sum T)
      (sv_pos_fin T) (sv_antitone_fin T) k hk S hS

end SVD
end UndergradKB.LinearAlgebra
