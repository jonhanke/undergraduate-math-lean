import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr

/-! # Normal operators and the spectral theorems (Axler, chapter 7)

Conventions: `𝕜` is `ℝ` or `ℂ` (any `RCLike` field), `E` a finite-dimensional inner product space over it.
Mathlib's inner product is conjugate-linear in the *first* slot (Axler's is in the second).
An operator is *normal* when `IsStarNormal T` holds in the star algebra `E →ₗ[𝕜] E`, i.e. `T` commutes with
`LinearMap.adjoint T`.
-/

open scoped ComplexConjugate InnerProductSpace
open Module End

namespace UndergradKB.LinearAlgebra

section Normal

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

lemma adjoint_mul_self_eq {T : E →ₗ[𝕜] E} (hT : IsStarNormal T) :
    LinearMap.adjoint T * T = T * LinearMap.adjoint T := by
  have := hT.star_comm_self.eq
  rwa [LinearMap.star_eq_adjoint] at this

lemma norm_eq_norm_adjoint_of_normal {T : E →ₗ[𝕜] E} (hT : IsStarNormal T) (v : E) :
    ‖T v‖ = ‖LinearMap.adjoint T v‖ := by
  have h := adjoint_mul_self_eq hT
  have h1 : ((‖T v‖ : ℝ) : 𝕜) ^ 2 = ((‖LinearMap.adjoint T v‖ : ℝ) : 𝕜) ^ 2 := by
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K]
    calc ⟪T v, T v⟫_𝕜 = ⟪LinearMap.adjoint T (T v), v⟫_𝕜 := (LinearMap.adjoint_inner_left _ _ _).symm
      _ = ⟪T (LinearMap.adjoint T v), v⟫_𝕜 := by
          have := congrArg (fun S => S v) h
          simp only [mul_apply_eq_comp] at this
          rw [this]
      _ = ⟪LinearMap.adjoint T v, LinearMap.adjoint T v⟫_𝕜 := (LinearMap.adjoint_inner_right _ _ _).symm
  have h2 : ‖T v‖ ^ 2 = ‖LinearMap.adjoint T v‖ ^ 2 := by exact_mod_cast h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

lemma isStarNormal_sub_smul_one {T : E →ₗ[𝕜] E} (hT : IsStarNormal T) (μ : 𝕜) :
    IsStarNormal (T - μ • (1 : E →ₗ[𝕜] E)) := by
  refine ⟨?_⟩
  rw [star_sub, star_smul, star_one]
  have h := hT.star_comm_self
  have hs : Commute (star μ • (1 : E →ₗ[𝕜] E)) (μ • (1 : E →ₗ[𝕜] E)) :=
    ((Commute.one_left _).smul_left _).smul_right _
  exact (h.sub_right ((Commute.one_right _).smul_right μ)).sub_left
    (((Commute.one_left _).smul_left (star μ)).sub_right hs)


lemma normal_eigen_iff {T : E →ₗ[𝕜] E} (hT : IsStarNormal T) (μ : 𝕜) (v : E) :
    T v = μ • v ↔ LinearMap.adjoint T v = conj μ • v := by
  have hA := isStarNormal_sub_smul_one hT μ
  have h := norm_eq_norm_adjoint_of_normal hA v
  have e1 : LinearMap.adjoint (T - μ • (1 : E →ₗ[𝕜] E)) =
      LinearMap.adjoint T - (conj μ) • (1 : E →ₗ[𝕜] E) := by
    rw [← LinearMap.star_eq_adjoint, star_sub, star_smul, star_one, LinearMap.star_eq_adjoint]; rfl
  rw [e1] at h
  have h1 : T v = μ • v ↔ ‖(T - μ • (1 : E →ₗ[𝕜] E)) v‖ = 0 := by
    simp [sub_eq_zero]
  have h2 : LinearMap.adjoint T v = conj μ • v ↔
      ‖(LinearMap.adjoint T - (conj μ) • (1 : E →ₗ[𝕜] E)) v‖ = 0 := by
    simp [sub_eq_zero]
  rw [h1, h2, h]

/-- Axler 7.21(a)-(e): for a normal operator, the kernels of `T` and `T*` agree, the ranges agree,
the space is the direct sum of kernel and range, `T - μ I` is again normal, and `T v = μ v` iff
`T* v = conj μ v`. -/
@[kb "axler2024" "7.21, p. 255"]
theorem axler_7_21 {T : E →ₗ[𝕜] E} (hT : IsStarNormal T) :
    LinearMap.ker T = LinearMap.ker (LinearMap.adjoint T) ∧
    LinearMap.range T = LinearMap.range (LinearMap.adjoint T) ∧
    IsCompl (LinearMap.ker T) (LinearMap.range T) ∧
    (∀ μ : 𝕜, IsStarNormal (T - μ • (1 : E →ₗ[𝕜] E))) ∧
    (∀ (μ : 𝕜) (v : E), T v = μ • v ↔ LinearMap.adjoint T v = conj μ • v) := by
  have hk : LinearMap.ker T = LinearMap.ker (LinearMap.adjoint T) := by
    ext v
    simp only [LinearMap.mem_ker, ← norm_eq_zero (E := E) (a := T v),
      ← norm_eq_zero (E := E) (a := LinearMap.adjoint T v), norm_eq_norm_adjoint_of_normal hT v]
  refine ⟨hk, ?_, ?_, isStarNormal_sub_smul_one hT, normal_eigen_iff hT⟩
  · calc LinearMap.range T = (LinearMap.range T)ᗮᗮ := (Submodule.orthogonal_orthogonal _).symm
      _ = (LinearMap.ker (LinearMap.adjoint T))ᗮ := by rw [LinearMap.orthogonal_range]
      _ = (LinearMap.ker T)ᗮ := by rw [hk]
      _ = LinearMap.range (LinearMap.adjoint T) := LinearMap.orthogonal_ker T
  · have : (LinearMap.range T)ᗮ = LinearMap.ker T := by
      rw [LinearMap.orthogonal_range, hk]
    have h := Submodule.isCompl_orthogonal (K := LinearMap.range T)
    rw [this] at h
    exact h.symm

/-- Axler 7.22: for a normal operator, eigenvectors for distinct eigenvalues are orthogonal. -/
@[kb "axler2024" "7.22, p. 256"]
theorem axler_7_22 {T : E →ₗ[𝕜] E} (hT : IsStarNormal T) {α β : 𝕜} {v w : E}
    (hv : T v = α • v) (hw : T w = β • w) (hαβ : α ≠ β) : ⟪v, w⟫_𝕜 = 0 := by
  have hw' := (normal_eigen_iff hT β w).1 hw
  have h1 : ⟪T v, w⟫_𝕜 = ⟪v, LinearMap.adjoint T w⟫_𝕜 := (LinearMap.adjoint_inner_right _ _ _).symm
  rw [hv, hw', inner_smul_left, inner_smul_right] at h1
  have : (conj α - conj β) * ⟪v, w⟫_𝕜 = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd ((starRingEnd 𝕜).injective (sub_eq_zero.1 h)) hαβ
  · exact h

/-- If `T* T = 1` then `T` preserves norms. -/
lemma norm_map_eq_of_adjoint_mul_self {T : E →ₗ[𝕜] E} (h : LinearMap.adjoint T * T = 1) (v : E) :
    ‖T v‖ = ‖v‖ := by
  have h1 : ((‖T v‖ : ℝ) : 𝕜) ^ 2 = ((‖v‖ : ℝ) : 𝕜) ^ 2 := by
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K,
      ← LinearMap.adjoint_inner_left]
    have := congrArg (fun A => A v) h
    simp only [mul_apply_eq_comp, Module.End.one_apply] at this
    rw [this]
  have h2 : ‖T v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- A self-adjoint operator is normal. (Helper.) -/
lemma isStarNormal_of_isSymmetric {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : IsStarNormal T :=
  ((LinearMap.isSymmetric_iff_isSelfAdjoint T).1 hT).isStarNormal

end Normal


/-! ### Operators diagonal in an orthonormal basis -/

section Diagonal

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The matrix of `T` in an orthonormal basis is diagonal iff the basis vectors are eigenvectors. -/
lemma toMatrix_eq_diagonal_iff {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) (T : E →ₗ[𝕜] E)
    (d : Fin n → 𝕜) :
    LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.diagonal d ↔ ∀ i, T (b i) = d i • b i := by
  constructor
  · intro h i
    have := Matrix.toLin_self b.toBasis b.toBasis (LinearMap.toMatrix b.toBasis b.toBasis T) i
    rw [Matrix.toLin_toMatrix, h] at this
    simpa [Matrix.diagonal_apply] using this
  · intro h
    ext i j
    simp [LinearMap.toMatrix_apply, h, Matrix.diagonal_apply, Finsupp.single_apply]
    grind

/-- If an orthonormal basis consists of eigenvectors of `T`, then it consists of eigenvectors of `T*`
with conjugate eigenvalues. -/
lemma adjoint_apply_of_eigenbasis {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) {T : E →ₗ[𝕜] E}
    {d : Fin n → 𝕜} (h : ∀ i, T (b i) = d i • b i) (i : Fin n) :
    LinearMap.adjoint T (b i) = conj (d i) • b i := by
  refine InnerProductSpace.ext_inner_right_basis b.toBasis fun j => ?_
  rw [LinearMap.adjoint_inner_left]
  simp only [OrthonormalBasis.coe_toBasis, h, inner_smul_right, inner_smul_left, RCLike.conj_conj]
  rw [b.inner_eq_ite]
  by_cases hij : i = j <;> simp [hij, eq_comm]

/-- An operator with an orthonormal eigenbasis is normal. -/
lemma isStarNormal_of_eigenbasis {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) {T : E →ₗ[𝕜] E}
    {d : Fin n → 𝕜} (h : ∀ i, T (b i) = d i • b i) : IsStarNormal T := by
  refine ⟨?_⟩
  rw [LinearMap.star_eq_adjoint]
  show LinearMap.adjoint T * T = T * LinearMap.adjoint T
  refine b.toBasis.ext fun i => ?_
  simp [h, adjoint_apply_of_eigenbasis b h, smul_smul, mul_comm]

/-- An operator with an orthonormal eigenbasis with real eigenvalues is self-adjoint. -/
lemma isSymmetric_of_eigenbasis {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) {T : E →ₗ[𝕜] E}
    {d : Fin n → ℝ} (h : ∀ i, T (b i) = (d i : 𝕜) • b i) : T.IsSymmetric := by
  have hadj : LinearMap.adjoint T = T := by
    refine b.toBasis.ext fun i => ?_
    simp [adjoint_apply_of_eigenbasis b h, h]
  exact (LinearMap.isSymmetric_iff_isSelfAdjoint T).2 (LinearMap.isSelfAdjoint_iff'.2 hadj)

end Diagonal

section SelfAdjoint

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Axler 7.26: if `T` is self-adjoint and `b² < 4c` (real `b`, `c`) then `T² + bT + cI` is invertible. -/
@[kb "axler2024" "7.26, p. 261"]
theorem axler_7_26 {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {b c : ℝ} (h : b ^ 2 < 4 * c) :
    IsUnit (T * T + (b : 𝕜) • T + (c : 𝕜) • (1 : E →ₗ[𝕜] E)) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  by_contra hv0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have h1 : ⟪(T * T + (b : 𝕜) • T + (c : 𝕜) • (1 : E →ₗ[𝕜] E)) v, v⟫_𝕜 = 0 := by rw [hv]; simp
  simp only [LinearMap.add_apply, LinearMap.smul_apply, mul_apply_eq_comp, Module.End.one_apply,
    inner_add_left, inner_smul_left, RCLike.conj_ofReal] at h1
  rw [hT (T v) v] at h1
  have h2 := congrArg RCLike.re h1
  simp only [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq, map_zero] at h2
  have h3 : |RCLike.re ⟪T v, v⟫_𝕜| ≤ ‖T v‖ * ‖v‖ :=
    (RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h4 : -(|b| * (‖T v‖ * ‖v‖)) ≤ b * RCLike.re ⟪T v, v⟫_𝕜 := by
    have := abs_mul b (RCLike.re ⟪T v, v⟫_𝕜)
    have h5 : |b| * |RCLike.re ⟪T v, v⟫_𝕜| ≤ |b| * (‖T v‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    have := neg_abs_le (b * RCLike.re ⟪T v, v⟫_𝕜)
    linarith
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith [sq_nonneg (‖T v‖ - |b| * ‖v‖ / 2), mul_pos hvpos hvpos]

/-- Axler 7.29 (real spectral theorem), over `ℝ` or `ℂ`: `T` is self-adjoint iff its matrix in some
orthonormal basis is diagonal with *real* diagonal entries (for `𝕜 = ℝ` this is exactly the book's statement). -/
@[kb "axler2024" "7.29, p. 263"]
theorem axler_7_29 (T : E →ₗ[𝕜] E) :
    T.IsSymmetric ↔ ∃ (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (d : Fin (finrank 𝕜 E) → ℝ),
      LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.diagonal (fun i => (d i : 𝕜)) := by
  constructor
  · intro hT
    exact ⟨hT.eigenvectorBasis rfl, hT.eigenvalues rfl, hT.toMatrix_eigenvectorBasis rfl⟩
  · rintro ⟨b, d, hd⟩
    exact isSymmetric_of_eigenbasis b ((toMatrix_eq_diagonal_iff b T _).1 hd)

end SelfAdjoint

section ComplexSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {T : E →ₗ[ℂ] E}

lemma normal_invariant_orthogonal_eigenspace (hT : IsStarNormal T) (μ : ℂ) (v : E)
    (hv : v ∈ (eigenspace T μ)ᗮ) : T v ∈ (eigenspace T μ)ᗮ := by
  intro w hw
  have hw' : T w = μ • w := by rwa [mem_eigenspace_iff] at hw
  have := (normal_eigen_iff hT μ w).1 hw'
  rw [← LinearMap.adjoint_inner_left, this, inner_smul_left]
  have := hv w hw
  simp [this]

lemma normal_orthogonalFamily (hT : IsStarNormal T) :
    OrthogonalFamily ℂ (fun μ : ℂ => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  rw [mem_eigenspace_iff] at hv hw
  exact axler_7_22 hT hv hw hμν

lemma normal_orthogonal_iSup_eigenspaces (hT : IsStarNormal T) :
    (⨆ μ, eigenspace T μ)ᗮ = ⊥ := by
  have hinv : ∀ ⦃v : E⦄, v ∈ (⨆ μ, eigenspace T μ)ᗮ → T v ∈ (⨆ μ, eigenspace T μ)ᗮ := by
    intro v hv
    rw [← Submodule.iInf_orthogonal] at hv ⊢
    exact T.iInf_invariant (normal_invariant_orthogonal_eigenspace hT) v hv
  by_contra hne
  haveI : Nontrivial (⨆ μ, eigenspace T μ)ᗮ := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T.restrict hinv)
  refine hμ (eigenspace_restrict_eq_bot hinv ?_)
  have H₂ : eigenspace T μ ⟂ (⨆ μ, eigenspace T μ)ᗮ :=
    (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact H₂.disjoint

/-- Existence half of the complex spectral theorem: a normal operator has an orthonormal basis of
eigenvectors. -/
lemma exists_orthonormalBasis_eigen_of_normal (hT : IsStarNormal T) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (d : Fin (finrank ℂ E) → ℂ),
      ∀ i, T (b i) = d i • b i := by
  have hfam : OrthogonalFamily ℂ (fun μ : Eigenvalues T => eigenspace T μ)
      fun μ => (eigenspace T μ).subtypeₗᵢ :=
    (normal_orthogonalFamily hT).comp Subtype.coe_injective
  have hbot : (⨆ μ : Eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
    show (⨆ μ : { μ // eigenspace T μ ≠ ⊥ }, eigenspace T μ)ᗮ = ⊥ by
      rw [iSup_ne_bot_subtype, normal_orthogonal_iSup_eigenspaces hT]
  have hint : DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ :=
    hfam.isInternal_iff.mpr hbot
  refine ⟨hint.subordinateOrthonormalBasis rfl hfam,
    fun i => (hint.subordinateOrthonormalBasisIndex rfl i hfam).val, fun i => ?_⟩
  exact mem_eigenspace_iff.1 (hint.subordinateOrthonormalBasis_subordinate rfl i hfam)

/-- Axler 7.31 (complex spectral theorem): `T` is normal iff its matrix in some orthonormal basis is
diagonal (equivalently, `E` has an orthonormal basis of eigenvectors of `T`). -/
@[kb "axler2024" "7.31, p. 264"]
theorem axler_7_31 (T : E →ₗ[ℂ] E) :
    IsStarNormal T ↔ ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (d : Fin (finrank ℂ E) → ℂ),
      LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.diagonal d := by
  constructor
  · intro hT
    obtain ⟨b, d, h⟩ := exists_orthonormalBasis_eigen_of_normal hT
    exact ⟨b, d, (toMatrix_eq_diagonal_iff b T d).2 h⟩
  · rintro ⟨b, d, hd⟩
    exact isStarNormal_of_eigenbasis b ((toMatrix_eq_diagonal_iff b T d).1 hd)

/-- Axler 7.31, eigenbasis form: `T` is normal iff `E` has an orthonormal basis of eigenvectors of `T`. -/
@[kb "axler2024" "7.31, p. 264"]
theorem axler_7_31_eigenbasis (T : E →ₗ[ℂ] E) :
    IsStarNormal T ↔ ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (d : Fin (finrank ℂ E) → ℂ),
      ∀ i, T (b i) = d i • b i :=
  ⟨exists_orthonormalBasis_eigen_of_normal, fun ⟨b, _, h⟩ => isStarNormal_of_eigenbasis b h⟩

/-- Axler 7.55: over `ℂ`, `S` is unitary iff `E` has an orthonormal basis of eigenvectors of `S` whose
eigenvalues all have absolute value `1`. -/
@[kb "axler2024" "7.55, p. 280"]
theorem axler_7_55 (S : E →ₗ[ℂ] E) :
    S ∈ unitary (E →ₗ[ℂ] E) ↔
      ∃ (b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) (d : Fin (finrank ℂ E) → ℂ),
        (∀ i, S (b i) = d i • b i) ∧ ∀ i, ‖d i‖ = 1 := by
  constructor
  · intro hS
    rw [Unitary.mem_iff] at hS
    have hN : IsStarNormal S := ⟨by rw [Commute, SemiconjBy, hS.1, hS.2]⟩
    obtain ⟨b, d, h⟩ := exists_orthonormalBasis_eigen_of_normal hN
    refine ⟨b, d, h, fun i => ?_⟩
    have h1 : ‖S (b i)‖ = ‖b i‖ :=
      norm_map_eq_of_adjoint_mul_self (by simpa [LinearMap.star_eq_adjoint] using hS.1) _
    rw [h i, norm_smul] at h1
    simpa using h1
  · rintro ⟨b, d, h, hd⟩
    rw [Unitary.mem_iff]
    have hadj := adjoint_apply_of_eigenbasis b h
    have key : ∀ i, conj (d i) * d i = 1 := by
      intro i
      rw [RCLike.conj_mul]
      simp [hd i]
    have key' : ∀ i, d i * conj (d i) = 1 := fun i => by rw [mul_comm]; exact key i
    constructor
    · refine b.toBasis.ext fun i => ?_
      simp [LinearMap.star_eq_adjoint, h, hadj, smul_smul, key, key']
    · refine b.toBasis.ext fun i => ?_
      simp [LinearMap.star_eq_adjoint, h, hadj, smul_smul, key, key']

end ComplexSpectral

section MinpolySelfAdjoint

open Polynomial

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Axler 7.27: the minimal polynomial of a self-adjoint operator is a product of linear factors
`X - r` with `r` real. -/
@[kb "axler2024" "7.27, p. 262"]
theorem axler_7_27 {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    ∃ s : Multiset ℝ, minpoly 𝕜 T = (s.map fun r : ℝ => X - C (r : 𝕜)).prod := by
  have hdvd : minpoly 𝕜 T ∣ T.charpoly := LinearMap.minpoly_dvd_charpoly T
  have hspl : (minpoly 𝕜 T).Splits :=
    hT.splits_charpoly.of_dvd (T.charpoly_monic.ne_zero) hdvd
  have hmon : (minpoly 𝕜 T).Monic := minpoly.monic (LinearMap.isIntegral T)
  have hroots : ∀ a ∈ (minpoly 𝕜 T).roots, ((RCLike.re a : ℝ) : 𝕜) = a := by
    intro a ha
    have hr : (minpoly 𝕜 T).IsRoot a := (mem_roots hmon.ne_zero).1 ha
    have hr' : T.charpoly.IsRoot a :=
      dvd_iff_isRoot.1 ((dvd_iff_isRoot.2 hr).trans hdvd)
    have ha' : a ∈ T.charpoly.roots := (mem_roots T.charpoly_monic.ne_zero).2 hr'
    rw [hT.roots_charpoly_eq_eigenvalues rfl] at ha'
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha'
    simp
  refine ⟨(minpoly 𝕜 T).roots.map RCLike.re, ?_⟩
  rw [Multiset.map_map]
  conv_lhs => rw [hspl.eq_prod_roots_of_monic hmon]
  congr 1
  refine Multiset.map_congr rfl fun a ha => ?_
  simp [hroots a ha]

end MinpolySelfAdjoint

section Positive

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- An operator acting on an orthonormal basis by prescribed scalars exists. -/
lemma exists_op_of_eigenbasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (f : ι → 𝕜) :
    ∃ R : E →ₗ[𝕜] E, ∀ i, R (b i) = f i • b i :=
  ⟨b.toBasis.constr 𝕜 (fun i => f i • b i), fun i => Basis.constr_basis b.toBasis 𝕜 (fun i => f i • b i) i⟩

/-- An operator with an orthonormal eigenbasis with nonnegative real eigenvalues is positive. -/
lemma isPositive_of_eigenbasis {n : ℕ} (b : OrthonormalBasis (Fin n) 𝕜 E) {T : E →ₗ[𝕜] E}
    {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) (h : ∀ i, T (b i) = (d i : 𝕜) • b i) : T.IsPositive := by
  rw [← LinearMap.posSemidef_toMatrix_iff b,
    (toMatrix_eq_diagonal_iff b T (fun i => (d i : 𝕜))).2 h, Matrix.posSemidef_diagonal_iff]
  intro i
  simpa using hd i

/-- Axler 7.38: six equivalent descriptions of a positive operator: positive; self-adjoint with
nonnegative eigenvalues; diagonal with nonnegative entries in some orthonormal basis; has a positive
square root; has a self-adjoint square root; of the form `R* R`. -/
@[kb "axler2024" "7.38, p. 270"]
theorem axler_7_38 (T : E →ₗ[𝕜] E) : List.TFAE [
    T.IsPositive,
    T.IsSymmetric ∧ ∀ μ : ℝ, Module.End.HasEigenvalue T (μ : 𝕜) → 0 ≤ μ,
    ∃ (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (d : Fin (finrank 𝕜 E) → ℝ),
      (∀ i, 0 ≤ d i) ∧ LinearMap.toMatrix b.toBasis b.toBasis T = Matrix.diagonal (fun i => (d i : 𝕜)),
    ∃ R : E →ₗ[𝕜] E, R.IsPositive ∧ R * R = T,
    ∃ R : E →ₗ[𝕜] E, R.IsSymmetric ∧ R * R = T,
    ∃ R : E →ₗ[𝕜] E, LinearMap.adjoint R * R = T] := by
  tfae_have 1 → 2 := fun hT =>
    ⟨hT.isSymmetric, fun μ hμ => eigenvalue_nonneg_of_nonneg hμ hT.re_inner_nonneg_right⟩
  tfae_have 2 → 3 := by
    rintro ⟨hs, hnn⟩
    exact ⟨hs.eigenvectorBasis rfl, hs.eigenvalues rfl,
      fun i => hnn _ (hs.hasEigenvalue_eigenvalues rfl i), hs.toMatrix_eigenvectorBasis rfl⟩
  tfae_have 3 → 4 := by
    rintro ⟨b, d, hd, hm⟩
    have h := (toMatrix_eq_diagonal_iff b T _).1 hm
    obtain ⟨R, hR⟩ := exists_op_of_eigenbasis b (fun i => ((Real.sqrt (d i) : ℝ) : 𝕜))
    refine ⟨R, isPositive_of_eigenbasis b (fun i => Real.sqrt_nonneg _) hR, ?_⟩
    refine b.toBasis.ext fun i => ?_
    simp only [OrthonormalBasis.coe_toBasis, mul_apply_eq_comp, hR, map_smul, h, smul_smul]
    congr 1
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hd i)]
  tfae_have 4 → 5 := fun ⟨R, hR, h⟩ => ⟨R, hR.isSymmetric, h⟩
  tfae_have 5 → 6 := fun ⟨R, hR, h⟩ => ⟨R, by rw [hR.adjoint_eq]; exact h⟩
  tfae_have 6 → 1 := by
    rintro ⟨R, rfl⟩
    exact LinearMap.isPositive_adjoint_comp_self R
  tfae_finish

/-- A positive operator, applied to a vector `v` with `T (T v) = s² v`, `s ≥ 0`, acts as `s`. -/
lemma isPositive_apply_of_sq_eigen {S : E →ₗ[𝕜] E} (hS : S.IsPositive) {s : ℝ} (hs : 0 ≤ s) {v : E}
    (hv : S (S v) = ((s : 𝕜) * s) • v) : S v = (s : 𝕜) • v := by
  rcases hs.eq_or_lt with rfl | hpos
  · have : ⟪S v, S v⟫_𝕜 = 0 := by
      rw [← hS.isSymmetric (S v) v, hv]; simp
    simpa using inner_self_eq_zero.1 this
  · have hinj : ∀ u, S u + (s : 𝕜) • u = 0 → u = 0 := by
      intro u hu
      have h1 : S u = -((s : 𝕜) • u) := eq_neg_of_add_eq_zero_left hu
      have h2 := hS.re_inner_nonneg_left u
      rw [h1, inner_neg_left, inner_smul_left, RCLike.conj_ofReal] at h2
      simp only [map_neg, inner_self_eq_norm_sq_to_K] at h2
      have h3 : RCLike.re ((s : 𝕜) * ((‖u‖ : 𝕜) ^ 2)) = s * ‖u‖ ^ 2 := by
        rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
      rw [h3] at h2
      have : ‖u‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖u‖]
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg u])
    refine sub_eq_zero.1 (hinj _ ?_)
    simp only [map_sub, map_smul, hv, smul_sub, smul_smul]
    abel

/-- Axler 7.39/7.40: a positive operator has exactly one positive square root. -/
@[kb "axler2024" "7.39, p. 271"]
theorem axler_7_39 {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    ∃! R : E →ₗ[𝕜] E, R.IsPositive ∧ R * R = T := by
  obtain ⟨R, hR, hRR⟩ := ((axler_7_38 T).out 1 4).1 hT
  refine ⟨R, ⟨hR, hRR⟩, ?_⟩
  rintro S ⟨hS, hSS⟩
  have hsym := hR.isSymmetric
  refine b_ext hsym hR hRR hS hSS
where
  b_ext {T R S : E →ₗ[𝕜] E} (hsym : R.IsSymmetric) (hR : R.IsPositive) (hRR : R * R = T)
      (hS : S.IsPositive) (hSS : S * S = T) : S = R := by
    refine (hsym.eigenvectorBasis rfl).toBasis.ext fun i => ?_
    have hRb : R (hsym.eigenvectorBasis rfl i) =
        (hsym.eigenvalues rfl i : 𝕜) • hsym.eigenvectorBasis rfl i := hsym.apply_eigenvectorBasis rfl i
    have he : 0 ≤ hsym.eigenvalues rfl i := hR.nonneg_eigenvalues rfl i
    have h2 : S (S (hsym.eigenvectorBasis rfl i)) =
        ((hsym.eigenvalues rfl i : 𝕜) * hsym.eigenvalues rfl i) • hsym.eigenvectorBasis rfl i := by
      have h3 : (S * S) (hsym.eigenvectorBasis rfl i) = (R * R) (hsym.eigenvectorBasis rfl i) := by
        rw [hSS, hRR]
      simpa only [mul_apply_eq_comp, hRb, map_smul, smul_smul] using h3
    simpa [hRb] using isPositive_apply_of_sq_eigen hS he h2

/-- The positive square root `√T` of a positive operator (Axler 7.39). -/
noncomputable def posSqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : E →ₗ[𝕜] E :=
  Classical.choose (axler_7_39 hT).exists

lemma posSqrt_isPositive {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : (posSqrt hT).IsPositive :=
  (Classical.choose_spec (axler_7_39 hT).exists).1

lemma posSqrt_mul_self {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : posSqrt hT * posSqrt hT = T :=
  (Classical.choose_spec (axler_7_39 hT).exists).2

/-- Axler 7.43: if `T` is positive and `⟪T v, v⟫ = 0` then `T v = 0`. -/
@[kb "axler2024" "7.43, p. 272"]
theorem axler_7_43 {T : E →ₗ[𝕜] E} (hT : T.IsPositive) {v : E} (hv : ⟪T v, v⟫_𝕜 = 0) : T v = 0 := by
  have hR := posSqrt_isPositive hT
  have hRR := posSqrt_mul_self hT
  have h1 : ⟪posSqrt hT v, posSqrt hT v⟫_𝕜 = 0 := by
    rw [← hR.isSymmetric (posSqrt hT v) v, ← mul_apply_eq_comp, hRR, hv]
  have h2 : posSqrt hT v = 0 := inner_self_eq_zero.1 h1
  rw [← hRR, mul_apply_eq_comp, h2, map_zero]

/-- Axler 7.61: a self-adjoint operator is positive and invertible iff `⟪T v, v⟫ > 0` for all `v ≠ 0`
(here `>` refers to the real part, which is all of `⟪T v, v⟫` for a self-adjoint `T`). -/
@[kb "axler2024" "7.61, p. 284"]
theorem axler_7_61 {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    (T.IsPositive ∧ IsUnit T) ↔ ∀ v : E, v ≠ 0 → 0 < RCLike.re ⟪T v, v⟫_𝕜 := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · rintro ⟨hpos, hinj⟩ v hv0
    refine lt_of_le_of_ne (hpos.re_inner_nonneg_left v) fun h0 => hv0 (hinj v ?_)
    have hc : (starRingEnd 𝕜) ⟪T v, v⟫_𝕜 = ⟪T v, v⟫_𝕜 := by
      rw [hT v v, inner_conj_symm, ← hT v v]
    have : ((RCLike.re ⟪T v, v⟫_𝕜 : ℝ) : 𝕜) = ⟪T v, v⟫_𝕜 := RCLike.conj_eq_iff_re.1 hc
    refine axler_7_43 hpos ?_
    rw [← this, ← h0]; simp
  · intro h
    refine ⟨⟨hT, fun v => ?_⟩, fun v hv => ?_⟩
    · by_cases hv : v = 0
      · simp [hv]
      · exact (h v hv).le
    · by_contra hv0
      have := h v hv0
      simp [hv] at this

end Positive

section ComplexTable

open scoped ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {T : E →ₗ[ℂ] E}

lemma hasEigenvalue_of_eigenbasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) {d : Fin n → ℂ}
    (h : ∀ i, T (b i) = d i • b i) (i : Fin n) : HasEigenvalue T (d i) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    ⟨mem_eigenspace_iff.2 (h i), by simpa using b.toBasis.ne_zero i⟩

lemma norm_apply_le_of_eigenbasis {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) {d : Fin n → ℂ}
    (h : ∀ i, T (b i) = d i • b i) {r : ℝ} (hr0 : 0 ≤ r) (hr : ∀ i, ‖d i‖ ≤ r) (x : E) :
    ‖T x‖ ≤ r * ‖x‖ := by
  have hinner : ∀ i, ⟪b i, T x⟫_ℂ = d i * ⟪b i, x⟫_ℂ := by
    intro i
    rw [← LinearMap.adjoint_inner_left, adjoint_apply_of_eigenbasis b h i, inner_smul_left,
      Complex.conj_conj]
  have h1 : ‖T x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_norm_inner_right (T x), ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hinner i, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hr i) 2) (by positivity)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg _))).1 h1

lemma eq_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (RCLike.ofReal z.re : ℂ) :=
  Complex.ext (by simp) (by simp [hz])

/-- The table of Axler (end of section 7F), for a normal operator `T` on a complex inner product
space: invertible iff all eigenvalues are nonzero; self-adjoint iff all eigenvalues are real;
positive iff all eigenvalues are `≥ 0`; unitary iff all eigenvalues have absolute value `1`;
operator norm `< 1` iff all eigenvalues have absolute value `< 1`. -/
@[kb "axler2024" "table, p. 311"]
theorem axler_normal_eigenvalue_table (hT : IsStarNormal T) :
    (IsUnit T ↔ ∀ μ : ℂ, HasEigenvalue T μ → μ ≠ 0) ∧
    (IsSelfAdjoint T ↔ ∀ μ : ℂ, HasEigenvalue T μ → μ.im = 0) ∧
    (T.IsPositive ↔ ∀ μ : ℂ, HasEigenvalue T μ → (0 : ℂ) ≤ μ) ∧
    (T ∈ unitary (E →ₗ[ℂ] E) ↔ ∀ μ : ℂ, HasEigenvalue T μ → ‖μ‖ = 1) ∧
    (‖LinearMap.toContinuousLinearMap T‖ < 1 ↔ ∀ μ : ℂ, HasEigenvalue T μ → ‖μ‖ < 1) := by
  obtain ⟨b, d, h⟩ := exists_orthonormalBasis_eigen_of_normal hT
  have hd := hasEigenvalue_of_eigenbasis b h
  have heig : ∀ μ, HasEigenvalue T μ → ∃ v : E, v ≠ 0 ∧ T v = μ • v := fun μ hμ => by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    exact ⟨v, hv.2, mem_eigenspace_iff.1 hv.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.isUnit_iff_ker_eq_bot]
    constructor
    · intro hk μ hμ hμ0
      rw [hμ0, Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero] at hμ
      exact hμ hk
    · intro H
      by_contra hk
      refine H 0 ?_ rfl
      rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero]
      exact hk
  · rw [← LinearMap.isSymmetric_iff_isSelfAdjoint]
    constructor
    · intro hs μ hμ
      exact Complex.conj_eq_iff_im.1 (hs.conj_eigenvalue_eq_self hμ)
    · intro H
      exact isSymmetric_of_eigenbasis b (d := fun i => (d i).re) (fun i => by
        rw [h i, ← eq_ofReal_re_of_im_eq_zero (H _ (hd i))])
  · constructor
    · intro hp μ hμ
      have him := Complex.conj_eq_iff_im.1 (hp.isSymmetric.conj_eigenvalue_eq_self hμ)
      have hre := eq_ofReal_re_of_im_eq_zero him
      have := eigenvalue_nonneg_of_nonneg (T := T) (μ := μ.re) (by rwa [← hre])
        hp.re_inner_nonneg_right
      exact Complex.nonneg_iff.2 ⟨this, him.symm⟩
    · intro H
      have hre : ∀ i, 0 ≤ (d i).re ∧ (d i).im = 0 := fun i => by
        have := Complex.nonneg_iff.1 (H _ (hd i))
        exact ⟨this.1, this.2.symm⟩
      exact isPositive_of_eigenbasis b (d := fun i => (d i).re) (fun i => (hre i).1)
        (fun i => by rw [h i, ← eq_ofReal_re_of_im_eq_zero (hre i).2])
  · constructor
    · intro hU μ hμ
      obtain ⟨v, hv0, hv⟩ := heig μ hμ
      rw [Unitary.mem_iff] at hU
      have := norm_map_eq_of_adjoint_mul_self (by simpa [LinearMap.star_eq_adjoint] using hU.1) v
      rw [hv, norm_smul] at this
      exact (mul_eq_right₀ (norm_ne_zero_iff.2 hv0)).1 this
    · intro H
      exact (axler_7_55 T).2 ⟨b, d, h, fun i => H _ (hd i)⟩
  · constructor
    · intro hn μ hμ
      obtain ⟨v, hv0, hv⟩ := heig μ hμ
      have h1 : ‖T v‖ ≤ ‖LinearMap.toContinuousLinearMap T‖ * ‖v‖ :=
        (LinearMap.toContinuousLinearMap T).le_opNorm v
      rw [hv, norm_smul] at h1
      have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv0
      exact ((mul_le_mul_iff_left₀ hv').1 h1).trans_lt hn
    · intro H
      obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ i, ‖d i‖ ≤ r := by
        rcases isEmpty_or_nonempty (Fin (finrank ℂ E)) with hn | hn
        · exact ⟨0, le_rfl, one_pos, fun i => (hn.false i).elim⟩
        · obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ‖d i‖)
          exact ⟨‖d i0‖, norm_nonneg _, H _ (hd i0), hi0⟩
      exact lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ hr0
        (fun x => norm_apply_le_of_eigenbasis b h hr0 hr x)) hr1

end ComplexTable

end UndergradKB.LinearAlgebra
