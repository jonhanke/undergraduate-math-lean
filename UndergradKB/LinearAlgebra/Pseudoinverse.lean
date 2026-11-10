import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import UndergradKB.Common.Attr

/-! # The pseudoinverse and least squares (Axler 6.67-6.70, Hefferon Three.VI.3.8)

`𝕜` is `ℝ` or `ℂ` (any `RCLike` field); `V`, `W` are finite-dimensional inner product spaces over it.
-/

open scoped InnerProductSpace Matrix ComplexConjugate
open Module

namespace UndergradKB.LinearAlgebra

section Pseudoinverse

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- `T` restricted to `(null T)ᗮ`, with codomain `range T`. -/
noncomputable def restrictPerp (T : V →ₗ[𝕜] W) : (LinearMap.ker T)ᗮ →ₗ[𝕜] LinearMap.range T :=
  LinearMap.codRestrict (LinearMap.range T) (T ∘ₗ (LinearMap.ker T)ᗮ.subtype) (fun x => ⟨x, rfl⟩)

@[simp] lemma coe_restrictPerp (T : V →ₗ[𝕜] W) (x : (LinearMap.ker T)ᗮ) :
    ((restrictPerp T x : LinearMap.range T) : W) = T x := rfl

/-- Applying `T` to the component of `v` in `(null T)ᗮ` gives `T v`. -/
lemma map_starProjection_ker_orthogonal (T : V →ₗ[𝕜] W) (v : V) :
    T ((LinearMap.ker T)ᗮ.starProjection v) = T v := by
  have h := Submodule.sub_starProjection_mem_orthogonal (K := (LinearMap.ker T)ᗮ) v
  rw [Submodule.orthogonal_orthogonal] at h
  have := LinearMap.mem_ker.1 h
  rwa [map_sub, sub_eq_zero, eq_comm] at this

/-- Axler 6.67: `T` restricted to `(null T)ᗮ` is a bijection onto `range T`. -/
@[kb "axler2024" "6.67, p. 238"]
theorem axler_6_67 (T : V →ₗ[𝕜] W) : Function.Bijective (restrictPerp T) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (x : V) ∈ LinearMap.ker T := by
      have := congrArg Subtype.val hx
      simpa using this
    exact Subtype.ext (Submodule.disjoint_def.1 (Submodule.isCompl_orthogonal (K := LinearMap.ker T)).disjoint
      _ h1 (by simpa using x.2) |>.trans rfl)
  · rintro ⟨y, v, rfl⟩
    refine ⟨⟨(LinearMap.ker T)ᗮ.starProjection v, Submodule.starProjection_apply_mem _ _⟩, ?_⟩
    exact Subtype.ext (by simpa using map_starProjection_ker_orthogonal T v)

/-- Set-theoretic form of Axler 6.67. -/
theorem axler_6_67_bijOn (T : V →ₗ[𝕜] W) :
    Set.BijOn T ((LinearMap.ker T)ᗮ : Set V) (LinearMap.range T) := by
  refine ⟨fun x _ => ⟨x, rfl⟩, ?_, ?_⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val ((axler_6_67 T).1 (Subtype.ext hxy : restrictPerp T ⟨x, hx⟩ = restrictPerp T ⟨y, hy⟩))
  · rintro y ⟨v, rfl⟩
    exact ⟨_, Submodule.starProjection_apply_mem _ _, map_starProjection_ker_orthogonal T v⟩

/-- `T` restricted to `(null T)ᗮ` as a linear equivalence onto `range T`. -/
noncomputable def restrictPerpEquiv (T : V →ₗ[𝕜] W) : (LinearMap.ker T)ᗮ ≃ₗ[𝕜] LinearMap.range T :=
  LinearEquiv.ofBijective (restrictPerp T) (axler_6_67 T)

/-- The pseudoinverse `T†` of `T : V → W` (Axler 6.68): first project `w` orthogonally onto `range T`,
then apply the inverse of `T` restricted to `(null T)ᗮ`.  Bridging definition (Mathlib has no
Moore-Penrose pseudoinverse for linear maps). -/
noncomputable def pinv (T : V →ₗ[𝕜] W) : W →ₗ[𝕜] V :=
  (LinearMap.ker T)ᗮ.subtype ∘ₗ (restrictPerpEquiv T).symm.toLinearMap ∘ₗ
    (LinearMap.range T).orthogonalProjectionOnto.toLinearMap

/-- Axler 6.68: the defining formula `T† w = (T|_{(null T)ᗮ})⁻¹ (P_{range T} w)`. -/
@[kb "axler2024" "6.68, p. 239"]
theorem axler_6_68 (T : V →ₗ[𝕜] W) (w : W) :
    pinv T w = (((restrictPerpEquiv T).symm ((LinearMap.range T).orthogonalProjectionOnto w) :
      (LinearMap.ker T)ᗮ) : V) := rfl

lemma pinv_mem_orthogonal (T : V →ₗ[𝕜] W) (w : W) : pinv T w ∈ (LinearMap.ker T)ᗮ :=
  ((restrictPerpEquiv T).symm ((LinearMap.range T).orthogonalProjectionOnto w)).2

lemma map_pinv (T : V →ₗ[𝕜] W) (w : W) : T (pinv T w) = (LinearMap.range T).starProjection w := by
  have h := (restrictPerpEquiv T).apply_symm_apply ((LinearMap.range T).orthogonalProjectionOnto w)
  have h2 := congrArg Subtype.val h
  rw [Submodule.starProjection_apply]
  exact h2

lemma pinv_map (T : V →ₗ[𝕜] W) (v : V) :
    pinv T (T v) = (LinearMap.ker T)ᗮ.starProjection v := by
  have hP : (LinearMap.range T).orthogonalProjectionOnto (T v) = ⟨T v, v, rfl⟩ := by
    apply Subtype.ext
    simpa using Submodule.starProjection_eq_self_iff.2 (⟨v, rfl⟩ : T v ∈ LinearMap.range T)
  rw [axler_6_68, hP]
  have : (restrictPerpEquiv T) ⟨(LinearMap.ker T)ᗮ.starProjection v, Submodule.starProjection_apply_mem _ _⟩
      = ⟨T v, v, rfl⟩ :=
    Subtype.ext (by simpa [restrictPerpEquiv] using map_starProjection_ker_orthogonal T v)
  rw [← this]
  simp

/-- Axler 6.69: if `T` is invertible then `T† = T⁻¹`; `T T† = P_{range T}`; `T† T = P_{(null T)ᗮ}`. -/
@[kb "axler2024" "6.69, p. 239"]
theorem axler_6_69 (T : V →ₗ[𝕜] W) :
    (∀ hT : Function.Bijective T, pinv T = (LinearEquiv.ofBijective T hT).symm.toLinearMap) ∧
    (∀ w, T (pinv T w) = (LinearMap.range T).starProjection w) ∧
    (∀ v, pinv T (T v) = (LinearMap.ker T)ᗮ.starProjection v) := by
  refine ⟨fun hT => ?_, map_pinv T, pinv_map T⟩
  ext w
  obtain ⟨v, rfl⟩ := hT.2 w
  have hk : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.2 hT.1
  have h2 : (LinearEquiv.ofBijective T hT).symm (T v) = v := (LinearEquiv.symm_apply_eq _).2 rfl
  show pinv T (T v) = (LinearEquiv.ofBijective T hT).symm (T v)
  rw [h2, pinv_map, hk]
  exact Submodule.starProjection_eq_self_iff.2 (by simp)

/-- Axler 6.70: `x = T† b` minimizes `‖T x - b‖`; among all minimizers it has the least norm, and it is
the only minimizer of that norm. -/
@[kb "axler2024" "6.70, p. 240"]
theorem axler_6_70 (T : V →ₗ[𝕜] W) (b : W) :
    (∀ x, ‖T (pinv T b) - b‖ ≤ ‖T x - b‖) ∧
    (∀ x, ‖T x - b‖ = ‖T (pinv T b) - b‖ →
      ‖pinv T b‖ ≤ ‖x‖ ∧ (‖x‖ = ‖pinv T b‖ → x = pinv T b)) := by
  set p := (LinearMap.range T).starProjection b with hp
  have hTy : T (pinv T b) = p := map_pinv T b
  have key : ∀ x, ‖T x - b‖ ^ 2 = ‖p - b‖ ^ 2 + ‖T x - p‖ ^ 2 := by
    intro x
    have h1 : T x - p ∈ LinearMap.range T :=
      Submodule.sub_mem _ ⟨x, rfl⟩ (Submodule.starProjection_apply_mem _ _)
    have h2 : b - p ∈ (LinearMap.range T)ᗮ := Submodule.sub_starProjection_mem_orthogonal b
    have h3 : ⟪T x - p, p - b⟫_𝕜 = 0 := by
      rw [← neg_sub b p, inner_neg_right, Submodule.inner_right_of_mem_orthogonal h1 h2, neg_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h3
    rw [show T x - p + (p - b) = T x - b by abel, add_comm] at this
    simp only [sq]
    linarith
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [hTy]
    have := key x
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    nlinarith [sq_nonneg ‖T x - p‖]
  · rw [hTy] at hx
    have h0 : ‖T x - p‖ ^ 2 = 0 := by
      have := key x
      rw [hx] at this
      nlinarith
    have hTx : T x = p := sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h0))
    have hker : x - pinv T b ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker, map_sub, hTy, hTx, sub_self]
    have horth : ⟪x - pinv T b, pinv T b⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal hker (pinv_mem_orthogonal T b)
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [sub_add_cancel] at hpy
    refine ⟨?_, fun hn => ?_⟩
    · refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
      nlinarith [sq_nonneg ‖x - pinv T b‖]
    · have : ‖x - pinv T b‖ ^ 2 = 0 := by rw [hn] at hpy; nlinarith
      exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this))

end Pseudoinverse

section LeastSquaresMatrix

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- If the columns of a tall matrix are linearly independent then `Aᴴ A` is invertible. -/
lemma isUnit_conjTranspose_mul_self {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜)
    (hA : LinearIndependent 𝕜
      (fun j : Fin k => (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n)))) :
    IsUnit (Aᴴ * A) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have hinj : Function.Injective (Matrix.mulVecLin (Aᴴ * A)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : (Aᴴ * A) *ᵥ x = 0 := by simpa using hx
    have h0 : star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = 0 := by
      calc star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) := by
            rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
              ← Matrix.dotProduct_mulVec]
        _ = 0 := by rw [hx']; simp
    have hAx : A *ᵥ x = 0 := dotProduct_star_self_eq_zero.1 h0
    funext i
    refine Fintype.linearIndependent_iff.1 hA x ?_ i
    ext j
    have := congrFun hAx j
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact hinj

/-- Hefferon Three.VI.3.8: if the columns of `A` form a basis of the subspace `M` (here `M` is their span
and they are independent), orthogonal projection into `M` is `v ↦ A (Aᴴ A)⁻¹ Aᴴ v` (over `ℝ`,
`Aᴴ = Aᵀ`, the book's statement). -/
@[kb "hefferon2020" "Three.VI.3.8, p. 300"]
theorem hefferon_Three_VI_3_8 {n k : ℕ} (A : Matrix (Fin n) (Fin k) 𝕜)
    (hA : LinearIndependent 𝕜
      (fun j : Fin k => (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n))))
    (v : EuclideanSpace 𝕜 (Fin n)) :
    (Submodule.span 𝕜 (Set.range fun j : Fin k =>
        (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n)))).starProjection v =
      WithLp.toLp 2 ((A * (Aᴴ * A)⁻¹ * Aᴴ) *ᵥ v.ofLp) := by
  have hG := isUnit_conjTranspose_mul_self A hA
  have hdet : IsUnit (Aᴴ * A).det := (Matrix.isUnit_iff_isUnit_det _).1 hG
  have hGG : (Aᴴ * A) * (Aᴴ * A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hAP : Aᴴ * (A * (Aᴴ * A)⁻¹ * Aᴴ) = Aᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · have hmem : ∀ c : Fin k → 𝕜, (WithLp.toLp 2 (A *ᵥ c) : EuclideanSpace 𝕜 (Fin n)) ∈
        Submodule.span 𝕜 (Set.range fun j : Fin k =>
          (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n))) := by
      intro c
      have : (WithLp.toLp 2 (A *ᵥ c) : EuclideanSpace 𝕜 (Fin n)) =
          ∑ j, c j • (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n)) := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h2 : (A * (Aᴴ * A)⁻¹ * Aᴴ) *ᵥ v.ofLp = A *ᵥ (((Aᴴ * A)⁻¹ * Aᴴ) *ᵥ v.ofLp) := by
      rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    rw [h2]
    exact hmem _
  · intro w hw
    set u : EuclideanSpace 𝕜 (Fin n) :=
      v - WithLp.toLp 2 ((A * (Aᴴ * A)⁻¹ * Aᴴ) *ᵥ v.ofLp) with hu
    have hu0 : Aᴴ *ᵥ u.ofLp = 0 := by
      have : u.ofLp = v.ofLp - (A * (Aᴴ * A)⁻¹ * Aᴴ) *ᵥ v.ofLp := by simp [hu]
      rw [this, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hAP, sub_self]
    have hker : Submodule.span 𝕜 (Set.range fun j : Fin k =>
          (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n))) ≤
        LinearMap.ker (innerₛₗ 𝕜 u) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h : ⟪u, (WithLp.toLp 2 (fun i => A i j) : EuclideanSpace 𝕜 (Fin n))⟫_𝕜 =
          star ((Aᴴ *ᵥ u.ofLp) j) := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, mul_comm]
      simp [h, hu0]
    exact hker hw

end LeastSquaresMatrix

end UndergradKB.LinearAlgebra
