import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import UndergradKB.Common.Attr
import UndergradKB.LinearAlgebra.Spectral

/-! # Polar decomposition (Axler, section 7F)

Row LA-444.  Mathlib has no square root of a positive operator on `V →ₗ[𝕜] V`; for `𝕜 = ℂ` the
continuous functional calculus provides `CFC.sqrt` on `V →L[ℂ] V`, and we identify our square root
with it.  Over a general `RCLike` field the square root is characterised as the positive operator
whose square is `T* T`.
-/

set_option linter.unusedSectionVars false

open Module InnerProductSpace
open scoped InnerProductSpace

namespace UndergradKB.LinearAlgebra
namespace Polar

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  (T : V →ₗ[𝕜] V)

/-- An orthonormal eigenbasis of `T* T`. -/
noncomputable def eb : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

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

/-- The positive square root of `T* T`, defined by `R (e_i) = s_i e_i` on an eigenbasis. -/
noncomputable def sqrtAdjComp : V →ₗ[𝕜] V :=
  (eb T).toBasis.constr 𝕜 (fun i => (T.singularValues i : 𝕜) • eb T i)

lemma sqrt_apply_eb (i : Fin (finrank 𝕜 V)) :
    sqrtAdjComp T (eb T i) = (T.singularValues i : 𝕜) • eb T i := by
  have := (eb T).toBasis.constr_basis 𝕜 (fun i => (T.singularValues i : 𝕜) • eb T i) i
  simpa [sqrtAdjComp] using this

lemma sqrt_apply (v : V) :
    sqrtAdjComp T v = ∑ i : Fin (finrank 𝕜 V), (T.singularValues i : 𝕜) • ⟪eb T i, v⟫_𝕜 • eb T i := by
  conv_lhs => rw [← (eb T).sum_repr' v]
  simp only [map_sum, map_smul, sqrt_apply_eb, smul_comm _ (⟪_, v⟫_𝕜)]

lemma sqrt_symm (x y : V) : ⟪sqrtAdjComp T x, y⟫_𝕜 = ⟪x, sqrtAdjComp T y⟫_𝕜 := by
  rw [sqrt_apply, sqrt_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_ofReal, map_mul]
  rw [← inner_conj_symm (eb T i) x, starRingEnd_self_apply]
  ring

lemma sqrt_inner_self (x : V) :
    ⟪sqrtAdjComp T x, x⟫_𝕜 = ((∑ i : Fin (finrank 𝕜 V), T.singularValues i * ‖⟪eb T i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [sqrt_apply, sum_inner]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, RCLike.conj_ofReal, map_mul]
  rw [← mul_assoc, ← RCLike.conj_mul]
  ring

lemma isPositive_sqrt : (sqrtAdjComp T).IsPositive := by
  refine ⟨fun x y => sqrt_symm T x y, fun x => ?_⟩
  rw [sqrt_inner_self, RCLike.ofReal_re]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (T.singularValues_nonneg _) (by positivity)

lemma sqrt_comp_sqrt : sqrtAdjComp T ∘ₗ sqrtAdjComp T = LinearMap.adjoint T ∘ₗ T := by
  refine (eb T).toBasis.ext fun i => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.coe_comp, Function.comp_apply,
    sqrt_apply_eb, map_smul, adj_apply_eb, smul_smul]
  congr 1
  ring

lemma norm_sqrt (v : V) : ‖sqrtAdjComp T v‖ = ‖T v‖ := by
  have h : ‖sqrtAdjComp T v‖ ^ 2 = ‖T v‖ ^ 2 := by
    have : ((‖sqrtAdjComp T v‖ ^ 2 : ℝ) : 𝕜) = ((‖T v‖ ^ 2 : ℝ) : 𝕜) := by
      rw [show ((‖sqrtAdjComp T v‖ ^ 2 : ℝ) : 𝕜) = ⟪sqrtAdjComp T v, sqrtAdjComp T v⟫_𝕜 by
        rw [inner_self_eq_norm_sq_to_K]; push_cast; ring,
        show ((‖T v‖ ^ 2 : ℝ) : 𝕜) = ⟪T v, T v⟫_𝕜 by
        rw [inner_self_eq_norm_sq_to_K]; push_cast; ring,
        sqrt_symm, ← LinearMap.comp_apply (sqrtAdjComp T), sqrt_comp_sqrt,
        LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    exact_mod_cast this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- There is an isometric automorphism `S` with `S ∘ sqrt(T* T) = T`. -/
lemma exists_isometry :
    ∃ S : V ≃ₗᵢ[𝕜] V, S.toLinearEquiv.toLinearMap ∘ₗ sqrtAdjComp T = T := by
  classical
  let b := eb T
  let sv : Fin (finrank 𝕜 V) → ℝ := fun i => T.singularValues i
  let vfam : Fin (finrank 𝕜 V) → V := fun i => ((sv i : 𝕜)⁻¹) • T (b i)
  let P : Set (Fin (finrank 𝕜 V)) := {i | 0 < sv i}
  have hv : Orthonormal 𝕜 (P.domRestrict vfam) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : (sv i : 𝕜) ≠ 0 := by exact_mod_cast (show 0 < sv i from hi).ne'
    have hj' : (sv j : 𝕜) ≠ 0 := by exact_mod_cast (show 0 < sv j from hj).ne'
    simp only [Set.domRestrict_apply, vfam]
    rw [inner_smul_left, inner_smul_right, inner_T_eb]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Subtype.mk.injEq]
      rw [map_inv₀, RCLike.conj_ofReal]
      field_simp
      simp [sv]
    · simp [hij]
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) hv
  refine ⟨b.equiv f (Equiv.refl _), ?_⟩
  refine b.toBasis.ext fun i => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  have hb : b.equiv f (Equiv.refl _) (b i) = f i := by simp
  rw [show sqrtAdjComp T (b i) = (sv i : 𝕜) • b i from sqrt_apply_eb T i, map_smul, hb]
  rcases (T.singularValues_nonneg i).lt_or_eq with hpos | hzero
  · rw [hf i hpos]
    simp only [vfam, smul_smul]
    rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_smul]
  · have h0 : T.singularValues i = 0 := hzero.symm
    rw [T_eb_eq_zero T h0]
    simp [sv, h0]


/-- Polar decomposition.  Every operator `T` on a finite-dimensional inner product space is a
unitary (isometric automorphism) `S` composed with a positive operator `R` whose square is `T* T`,
that is, with the positive square root of `T* T`. -/
@[kb "axler2024" "7.93, p. 304"]
theorem axler_7_93 :
    ∃ (R : V →ₗ[𝕜] V) (S : V ≃ₗᵢ[𝕜] V), R.IsPositive ∧
      R ∘ₗ R = LinearMap.adjoint T ∘ₗ T ∧ T = S.toLinearEquiv.toLinearMap ∘ₗ R := by
  obtain ⟨S, hS⟩ := exists_isometry T
  exact ⟨sqrtAdjComp T, S, isPositive_sqrt T, sqrt_comp_sqrt T, hS.symm⟩

/-- Axler 7.93 in the book's form: `T = S √(T* T)` for a unitary `S`, where `√(T* T)` is the unique positive
square root of the positive operator `T* T` (`posSqrt`, Axler 7.39, from `UndergradKB.LinearAlgebra.Spectral`). -/
@[kb "axler2024" "7.93, p. 304"]
theorem axler_7_93_posSqrt (h : (LinearMap.adjoint T ∘ₗ T).IsPositive) :
    ∃ S : V ≃ₗᵢ[𝕜] V, T = S.toLinearEquiv.toLinearMap ∘ₗ posSqrt h := by
  obtain ⟨R, S, hR, hRR, hT⟩ := axler_7_93 T
  have huniq := (axler_7_39 h).unique ⟨posSqrt_isPositive h, posSqrt_mul_self h⟩
    ⟨hR, (by simpa [Module.End.mul_eq_comp] using hRR : R * R = LinearMap.adjoint T ∘ₗ T)⟩
  exact ⟨S, by rw [huniq]; exact hT⟩

end Polar

/-- Polar decomposition over `ℂ`, with the square root taken as `CFC.sqrt` in the C*-algebra of
bounded operators: every operator `T` is `S * sqrt (T* * T)` for some unitary `S`. -/
@[kb "axler2024" "7.93, p. 304"]
theorem axler_7_93_complex {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (T : V →L[ℂ] V) :
    ∃ S : V ≃ₗᵢ[ℂ] V,
      T = (S.toContinuousLinearEquiv : V →L[ℂ] V) *
        CFC.sqrt (ContinuousLinearMap.adjoint T * T) := by
  obtain ⟨R, S, hRpos, hRR, hTS⟩ := Polar.axler_7_93 (T : V →ₗ[ℂ] V)
  refine ⟨S, ?_⟩
  have hnn : 0 ≤ LinearMap.toContinuousLinearMap R :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      ((LinearMap.isPositive_toContinuousLinearMap_iff R).mpr hRpos)
  have hsq : LinearMap.toContinuousLinearMap R * LinearMap.toContinuousLinearMap R =
      ContinuousLinearMap.adjoint T * T := by
    ext v
    have := congrArg (fun L => L v) hRR
    simpa [LinearMap.adjoint_eq_toCLM_adjoint, LinearMap.toContinuousLinearMap] using this
  rw [CFC.sqrt_unique hsq hnn]
  ext v
  have := congrArg (fun L => L v) hTS
  simpa using this

end UndergradKB.LinearAlgebra
