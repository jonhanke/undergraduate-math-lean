import UndergradKB.RepresentationTheory.CharactersMore
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import UndergradKB.Common.Attr

/-! # Problem 4.1: real-linear endomorphisms of an irreducible complex representation (Etingof et al.)

For an irreducible finite-dimensional complex representation `ρ` of a finite group `G`, let `E` be the algebra of
`ℝ`-linear `G`-equivariant endomorphisms of `V` (`realEnd ρ`).  The proofs go through an antilinear equivariant
map `J` attached to an invariant bilinear form `B` by `B v w = H (J v) w`, where `H` is an invariant positive
definite Hermitian form.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open Representation Module Quaternion
open scoped ComplexConjugate

namespace RealType

section Basic

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- Multiplication by `i`, as a real-linear endomorphism. -/
noncomputable def Im : Module.End ℝ V := (Complex.I • LinearMap.id : V →ₗ[ℂ] V).restrictScalars ℝ

theorem Im_apply (v : V) : (Im : Module.End ℝ V) v = Complex.I • v := rfl

theorem Im_mul_Im : (Im : Module.End ℝ V) * Im = -1 := by
  refine LinearMap.ext fun v => ?_
  simp [mul_apply_eq_comp, Im_apply, smul_smul]

theorem smul_re_im (c : ℂ) (v : V) : c • v = c.re • v + c.im • (Complex.I • v) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul]
  simp [Complex.coe_smul]

/-- A real-linear map commuting with `i` is complex linear. -/
noncomputable def toC (T : Module.End ℝ V) (h : T * Im = Im * T) : V →ₗ[ℂ] V where
  toFun := T
  map_add' := T.map_add
  map_smul' c v := by
    have hT : ∀ v, T (Complex.I • v) = Complex.I • T v := fun v => by
      have := congrArg (fun S : Module.End ℝ V => S v) h
      simpa [mul_apply_eq_comp, Im_apply] using this
    simp only [RingHom.id_apply]
    rw [smul_re_im c v, map_add, map_smul, map_smul, hT, ← smul_re_im c (T v)]

@[simp] theorem toC_apply (T : Module.End ℝ V) (h : T * Im = Im * T) (v : V) : toC T h v = T v := rfl

theorem anti_of_anticomm (T : Module.End ℝ V) (h : T * Im = -(Im * T)) (c : ℂ) (v : V) :
    T (c • v) = conj c • T v := by
  have hT : T (Complex.I • v) = -(Complex.I • T v) := by
    have := congrArg (fun S : Module.End ℝ V => S v) h
    simpa [mul_apply_eq_comp, Im_apply] using this
  rw [smul_re_im c v, map_add, map_smul, map_smul, hT, smul_re_im (conj c) (T v)]
  simp [Complex.conj_re, Complex.conj_im, smul_neg, neg_smul]

variable (ρ : Representation ℂ G V)

/-- The algebra of real-linear `G`-equivariant endomorphisms of `V`. -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
noncomputable def realEnd : Subalgebra ℝ (Module.End ℝ V) :=
  Subalgebra.centralizer ℝ (Set.range fun g => (ρ g).restrictScalars ℝ)

variable {ρ}

theorem mem_realEnd {T : Module.End ℝ V} : T ∈ realEnd ρ ↔ ∀ g v, T (ρ g v) = ρ g (T v) := by
  rw [realEnd, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h g v
    have := h _ ⟨g, rfl⟩
    exact (congrArg (fun S : Module.End ℝ V => S v) this).symm
  · rintro h _ ⟨g, rfl⟩
    refine LinearMap.ext fun v => ?_
    exact (h g v).symm

variable (ρ)

theorem Im_mem : (Im : Module.End ℝ V) ∈ realEnd ρ := by
  rw [mem_realEnd]
  intro g v
  simp [Im_apply]

variable {ρ}

/-- The `ℂ`-linear part of `T`. -/
noncomputable def Tp (T : Module.End ℝ V) : Module.End ℝ V := (2 : ℝ)⁻¹ • (T - Im * T * Im)

/-- The antilinear part of `T`. -/
noncomputable def Tm (T : Module.End ℝ V) : Module.End ℝ V := (2 : ℝ)⁻¹ • (T + Im * T * Im)

theorem Tp_add_Tm (T : Module.End ℝ V) : Tp T + Tm T = T := by
  unfold Tp Tm
  module

theorem Tp_comm (T : Module.End ℝ V) : Tp T * Im = Im * Tp T := by
  have h1 : Im * T * Im * Im = -(Im * T) := by
    rw [mul_assoc, Im_mul_Im, mul_neg, mul_one]
  have h2 : Im * (Im * T * Im) = -(T * Im) := by
    rw [← mul_assoc, ← mul_assoc, Im_mul_Im, neg_mul, one_mul, neg_mul]
  unfold Tp
  rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, h1, h2]
  congr 1
  abel

theorem Tm_anticomm (T : Module.End ℝ V) : Tm T * Im = -(Im * Tm T) := by
  have h1 : Im * T * Im * Im = -(Im * T) := by
    rw [mul_assoc, Im_mul_Im, mul_neg, mul_one]
  have h2 : Im * (Im * T * Im) = -(T * Im) := by
    rw [← mul_assoc, ← mul_assoc, Im_mul_Im, neg_mul, one_mul, neg_mul]
  unfold Tm
  rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, h1, h2, ← smul_neg]
  congr 1
  abel

theorem Tp_mem (T : Module.End ℝ V) (hT : T ∈ realEnd ρ) : Tp T ∈ realEnd ρ := by
  have := (realEnd ρ).sub_mem hT ((realEnd ρ).mul_mem ((realEnd ρ).mul_mem (Im_mem ρ) hT) (Im_mem ρ))
  exact (realEnd ρ).smul_mem this _

theorem Tm_mem (T : Module.End ℝ V) (hT : T ∈ realEnd ρ) : Tm T ∈ realEnd ρ := by
  have := (realEnd ρ).add_mem hT ((realEnd ρ).mul_mem ((realEnd ρ).mul_mem (Im_mem ρ) hT) (Im_mem ρ))
  exact (realEnd ρ).smul_mem this _

end Basic

section Schur

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [IsIrreducible ρ]

/-- An equivariant real-linear map commuting with `i` is of the form `a + b i`. -/
theorem exists_ab_of_comm (S : Module.End ℝ V) (hS : S ∈ realEnd ρ) (hc : S * Im = Im * S) :
    ∃ a b : ℝ, S = a • 1 + b • Im := by
  have hcomm : ∀ g, toC S hc ∘ₗ ρ g = ρ g ∘ₗ toC S hc := by
    intro g
    refine LinearMap.ext fun v => ?_
    exact (mem_realEnd.mp hS) g v
  obtain ⟨c, hc'⟩ := exists_eq_smul_id_of_commute (toC S hc) hcomm
  refine ⟨c.re, c.im, LinearMap.ext fun v => ?_⟩
  have := congrArg (fun φ : V →ₗ[ℂ] V => φ v) hc'
  simp only [toC_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
  simp [Im_apply, this, smul_re_im c v]

end Schur

section Anti

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- An antilinear `G`-equivariant map, as a real-linear map. -/
structure IsAnti (ρ : Representation ℂ G V) (J : Module.End ℝ V) : Prop where
  anti : ∀ (c : ℂ) v, J (c • v) = conj c • J v
  comm : ∀ g v, J (ρ g v) = ρ g (J v)

theorem IsAnti.mem {J : Module.End ℝ V} (hJ : IsAnti ρ J) : J ∈ realEnd ρ := mem_realEnd.mpr hJ.comm

theorem IsAnti.anticomm {J : Module.End ℝ V} (hJ : IsAnti ρ J) : J * Im = -(Im * J) := by
  refine LinearMap.ext fun v => ?_
  simp [mul_apply_eq_comp, Im_apply, hJ.anti]

theorem isAnti_of {J : Module.End ℝ V} (hm : J ∈ realEnd ρ) (h : J * Im = -(Im * J)) : IsAnti ρ J :=
  ⟨anti_of_anticomm J h, mem_realEnd.mp hm⟩

theorem IsAnti.smul_real {J : Module.End ℝ V} (hJ : IsAnti ρ J) (r : ℝ) : IsAnti ρ (r • J) := by
  refine ⟨fun c v => ?_, fun g v => ?_⟩
  · simp [hJ.anti, smul_comm r]
  · simp [hJ.comm]

variable [FiniteDimensional ℂ V] [IsIrreducible ρ]

/-- A nonzero antilinear equivariant map on an irreducible representation is bijective. -/
theorem IsAnti.bijective_or_zero {J : Module.End ℝ V} (hJ : IsAnti ρ J) :
    J = 0 ∨ Function.Bijective J := by
  let K : Submodule ℂ V :=
    { carrier := {v | J v = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c v hv => by
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [hJ.anti, hv, smul_zero] }
  let S : Subrepresentation ρ :=
    ⟨K, fun g v hv => by
      show J (ρ g v) = 0
      rw [hJ.comm]
      have : J v = 0 := hv
      rw [this, map_zero]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · right
    have hinj : Function.Injective J := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hvS : v ∈ S := hv
      rw [h] at hvS
      exact (Submodule.mem_bot ℂ).mp hvS
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  · left
    refine LinearMap.ext fun v => ?_
    have hvS : v ∈ S := by rw [h]; trivial
    exact hvS

end Anti

section Hermitian

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

theorem nontrivial_of_irreducible (ρ : Representation ℂ G V) [IsIrreducible ρ] : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  exact bot_ne_top this

/-- The bilinear form `(v, w) ↦ H (J v) w` attached to an antilinear map `J`. -/
noncomputable def bilJ (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (J : Module.End ℝ V)
    (hJ : ∀ (c : ℂ) v, J (c • v) = conj c • J v) : LinearMap.BilinForm ℂ V :=
  LinearMap.mk₂ ℂ (fun v w => H (J v) w)
    (fun v₁ v₂ w => by simp [map_add])
    (fun c v w => by simp [hJ])
    (fun v w₁ w₂ => by simp)
    (fun c v w => by simp)

theorem bilJ_apply (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (J : Module.End ℝ V) (hJ : ∀ (c : ℂ) v, J (c • v) = conj c • J v)
    (v w : V) : bilJ H J hJ v w = H (J v) w := rfl

theorem bilJ_nondeg (hH : IsPosDefHermitian H) {J : Module.End ℝ V} (hJ : IsAnti ρ J)
    (hb : Function.Bijective J) : (bilJ H J hJ.anti).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have : J x = 0 := hH.eq_zero fun w => hx w
    exact hb.1 (this.trans (map_zero J).symm)
  · by_contra hne
    obtain ⟨x, rfl⟩ := hb.2 y
    have h0 := hy x
    have := (hH.pos (J x) hne).2
    rw [bilJ_apply] at h0
    rw [h0] at this
    simp at this

theorem bilJ_invariant (hHi : IsInvariantForm ρ H) {J : Module.End ℝ V} (hJ : IsAnti ρ J) :
    IsInvariantBilinForm ρ (bilJ H J hJ.anti) := by
  intro g v w
  rw [bilJ_apply, bilJ_apply, hJ.comm]
  exact hHi g _ _

/-- A representation carrying a nonzero antilinear equivariant map is not of complex type. -/
theorem not_isComplexType_of_anti [IsIrreducible ρ] (hH : IsPosDefHermitian H) (hHi : IsInvariantForm ρ H)
    {J : Module.End ℝ V} (hJ : IsAnti ρ J) (hne : J ≠ 0) : ¬ IsComplexType ρ := by
  have hb := hJ.bijective_or_zero.resolve_left hne
  exact fun hc => hc (nonempty_equiv_dual_of_invariantForm (bilJ_nondeg hH hJ hb) (bilJ_invariant hHi hJ))

/-- The antilinear map `J` with `H (J v) w = B v w` (Riesz representation). -/
noncomputable def rieszFun (hH : IsPosDefHermitian H) (B : LinearMap.BilinForm ℂ V) (v : V) : V :=
  Classical.choose (hH.exists_repr (B v))

theorem rieszFun_spec (hH : IsPosDefHermitian H) (B : LinearMap.BilinForm ℂ V) (v w : V) :
    H (rieszFun hH B v) w = B v w := Classical.choose_spec (hH.exists_repr (B v)) w

theorem rieszFun_add (hH : IsPosDefHermitian H) (B : LinearMap.BilinForm ℂ V) (v₁ v₂ : V) :
    rieszFun hH B (v₁ + v₂) = rieszFun hH B v₁ + rieszFun hH B v₂ := by
  apply hH.ext; intro w
  rw [rieszFun_spec, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, rieszFun_spec,
    rieszFun_spec]

theorem rieszFun_smul (hH : IsPosDefHermitian H) (B : LinearMap.BilinForm ℂ V) (c : ℂ) (v : V) :
    rieszFun hH B (c • v) = conj c • rieszFun hH B v := by
  apply hH.ext; intro w
  rw [rieszFun_spec, map_smul, LinearMap.smul_apply, map_smulₛₗ, LinearMap.smul_apply, rieszFun_spec,
    Complex.conj_conj]

/-- The Riesz map as a real-linear endomorphism. -/
noncomputable def rieszMap (hH : IsPosDefHermitian H) (B : LinearMap.BilinForm ℂ V) : Module.End ℝ V where
  toFun := rieszFun hH B
  map_add' := rieszFun_add hH B
  map_smul' r v := by
    have e : r • v = (r : ℂ) • v := (Complex.coe_smul r v).symm
    rw [RingHom.id_apply, e, rieszFun_smul, Complex.conj_ofReal, Complex.coe_smul]

theorem rieszMap_apply (hH : IsPosDefHermitian H) (B : LinearMap.BilinForm ℂ V) (v : V) :
    rieszMap hH B v = rieszFun hH B v := rfl

theorem rieszMap_isAnti (hH : IsPosDefHermitian H) (hHi : IsInvariantForm ρ H) {B : LinearMap.BilinForm ℂ V}
    (hB : IsInvariantBilinForm ρ B) : IsAnti ρ (rieszMap hH B) := by
  refine ⟨fun c v => rieszFun_smul hH B c v, fun g v => ?_⟩
  rw [rieszMap_apply, rieszMap_apply]
  apply hH.ext; intro w
  calc H (rieszFun hH B (ρ g v)) w = B (ρ g v) w := rieszFun_spec hH B _ _
    _ = B (ρ g v) (ρ g (ρ g⁻¹ w)) := by rw [rep_apply_inv_apply]
    _ = B v (ρ g⁻¹ w) := hB g v _
    _ = H (rieszFun hH B v) (ρ g⁻¹ w) := (rieszFun_spec hH B _ _).symm
    _ = H (ρ g (rieszFun hH B v)) (ρ g (ρ g⁻¹ w)) := (hHi g _ _).symm
    _ = H (ρ g (rieszFun hH B v)) w := by rw [rep_apply_inv_apply]

theorem bilJ_rieszMap (hH : IsPosDefHermitian H) (hHi : IsInvariantForm ρ H) {B : LinearMap.BilinForm ℂ V}
    (hB : IsInvariantBilinForm ρ B) (v w : V) :
    bilJ H (rieszMap hH B) (rieszMap_isAnti hH hHi hB).anti v w = B v w := by
  rw [bilJ_apply, rieszMap_apply, rieszFun_spec]

theorem rieszMap_ne_zero [Nontrivial V] (hH : IsPosDefHermitian H) {B : LinearMap.BilinForm ℂ V}
    (hB : B.Nondegenerate) : rieszMap hH B ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply hB.1 v
  intro w
  rw [← rieszFun_spec hH B v w]
  have : rieszFun hH B v = 0 := by
    have := congrArg (fun J : Module.End ℝ V => J v) h0
    simpa [rieszMap_apply] using this
  rw [this, map_zero, LinearMap.zero_apply]

end Hermitian

section Normalize

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [IsIrreducible ρ] {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

/-- An antilinear equivariant bijection is an isometry of `H` up to a positive constant. -/
theorem exists_isom_const (hH : IsPosDefHermitian H) (hHi : IsInvariantForm ρ H) {J : Module.End ℝ V}
    (hJ : IsAnti ρ J) (hb : Function.Bijective J) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y, H (J x) (J y) = (c : ℂ) * H y x := by
  let K : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => H (J y) (J x))
      (fun x₁ x₂ y => by simp [map_add])
      (fun c x y => by simp [hJ.anti])
      (fun x y₁ y₂ => by simp [map_add])
      (fun c x y => by simp [hJ.anti])
  have hKapp : ∀ x y, K x y = H (J y) (J x) := fun _ _ => rfl
  have hK : IsPosDefHermitian K := by
    refine ⟨fun v w => ?_, fun v hv => ?_⟩
    · rw [hKapp, hKapp]; exact hH.conj_symm _ _
    · have hne : J v ≠ 0 := fun h => hv (hb.1 (h.trans (map_zero J).symm))
      rw [hKapp]; exact hH.pos _ hne
  have hKi : IsInvariantForm ρ K := by
    intro g v w
    rw [hKapp, hKapp, hJ.comm, hJ.comm]
    exact hHi g _ _
  obtain ⟨c, hc, hprop⟩ := posDef_forms_proportional (ρ := ρ) hH hK hHi hKi
  exact ⟨c, hc, fun x y => by rw [← hKapp]; exact hprop y x⟩

/-- The square of an antilinear equivariant bijection is a nonzero real scalar. -/
theorem exists_sq {J : Module.End ℝ V} (hJ : IsAnti ρ J) (hb : Function.Bijective J) :
    ∃ μ : ℝ, μ ≠ 0 ∧ ∀ v, J (J v) = (μ : ℂ) • v := by
  haveI := nontrivial_of_irreducible ρ
  have hm : J * J ∈ realEnd ρ := (realEnd ρ).mul_mem hJ.mem hJ.mem
  have hc : (J * J) * Im = Im * (J * J) := by
    rw [mul_assoc, hJ.anticomm, mul_neg, ← mul_assoc, hJ.anticomm, neg_mul, neg_neg, mul_assoc]
  obtain ⟨a, b, hab⟩ := exists_ab_of_comm (J * J) hm hc
  have h2 : ∀ v, J (J v) = a • v + b • (Complex.I • v) := fun v => by
    have := congrArg (fun S : Module.End ℝ V => S v) hab
    simpa [mul_apply_eq_comp, Im_apply] using this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hw : J v ≠ 0 := fun h => hv (hb.1 (h.trans (map_zero J).symm))
  have hx : Complex.I • J v ≠ 0 := fun h => hw ((smul_eq_zero.mp h).resolve_left Complex.I_ne_zero)
  have hb0 : b = 0 := by
    have e1 := h2 (J v)
    have e2 : J (J (J v)) = a • J v + b • (-(Complex.I • J v)) := by
      rw [h2 v, map_add, map_smul, map_smul, hJ.anti]
      simp
    rw [e1] at e2
    have e3 : b • (Complex.I • J v) = -(b • (Complex.I • J v)) := by
      have := add_left_cancel e2
      rwa [smul_neg] at this
    have e4 : (2 : ℝ) • (b • (Complex.I • J v)) = 0 := by
      rw [two_smul]; nth_rewrite 1 [e3]; exact neg_add_cancel _
    have e5 := (smul_eq_zero.mp e4).resolve_left two_ne_zero
    exact (smul_eq_zero.mp e5).resolve_right hx
  refine ⟨a, ?_, fun v => ?_⟩
  · intro ha
    have : J (J v) = 0 := by rw [h2, ha, hb0]; simp
    exact hw (hb.1 (this.trans (map_zero J).symm))
  · rw [h2, hb0]; simp [Complex.coe_smul]

/-- The symmetry relation between `H (J w) v` and `H (J v) w`. -/
theorem H_J_symm {J : Module.End ℝ V} (hJ : IsAnti ρ J) {c μ : ℝ}
    (hc : ∀ x y, H (J x) (J y) = (c : ℂ) * H y x) (hμ0 : μ ≠ 0) (hμ : ∀ v, J (J v) = (μ : ℂ) • v)
    (v w : V) : H (J w) v = ((c / μ : ℝ) : ℂ) * H (J v) w := by
  have hv : J (((μ⁻¹ : ℝ) : ℂ) • J v) = v := by
    rw [hJ.anti, Complex.conj_ofReal, hμ, smul_smul]
    have : ((μ⁻¹ : ℝ) : ℂ) * (μ : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hμ0]; simp
    rw [this, one_smul]
  calc H (J w) v = H (J w) (J (((μ⁻¹ : ℝ) : ℂ) • J v)) := by rw [hv]
    _ = (c : ℂ) * H (((μ⁻¹ : ℝ) : ℂ) • J v) w := hc _ _
    _ = ((c / μ : ℝ) : ℂ) * H (J v) w := by
      rw [map_smulₛₗ, LinearMap.smul_apply, Complex.conj_ofReal, smul_eq_mul]
      push_cast
      ring

/-- Normalization of an antilinear equivariant bijection: a positive real multiple of `J` squares to `±1`
and satisfies the corresponding (skew-)symmetry with respect to `H`. -/
theorem exists_normalized (hH : IsPosDefHermitian H) (hHi : IsInvariantForm ρ H) {J : Module.End ℝ V}
    (hJ : IsAnti ρ J) (hb : Function.Bijective J) :
    ∃ (r μ ε : ℝ), 0 < r ∧ μ ≠ 0 ∧ (∀ v, J (J v) = (μ : ℂ) • v) ∧ ε = r ^ 2 * μ ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ v w, H ((r • J) w) v = (ε : ℂ) * H ((r • J) v) w := by
  obtain ⟨c, hc0, hc⟩ := exists_isom_const hH hHi hJ hb
  obtain ⟨μ, hμ0, hμ⟩ := exists_sq hJ hb
  have hsymm := H_J_symm hJ hc hμ0 hμ
  set s : ℝ := c / μ with hs
  have hs2 : s ^ 2 = 1 := by
    haveI := nontrivial_of_irreducible ρ
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have hJu : J u ≠ 0 := fun h => hu (hb.1 (h.trans (map_zero J).symm))
    have hpos := (hH.pos (J u) hJu).2
    have e1 := hsymm (J u) u
    have e2 := hsymm u (J u)
    have hne : H (J u) (J u) ≠ 0 := by
      intro h; rw [h] at hpos; simp at hpos
    rw [e2] at e1
    have : (((s ^ 2 : ℝ)) : ℂ) = 1 := by
      have h3 : H (J u) (J u) * ((s : ℂ) ^ 2 - 1) = 0 := by linear_combination -e1
      have := (mul_eq_zero.mp h3).resolve_left hne
      push_cast
      linear_combination this
    exact_mod_cast this
  have hs' : s = 1 ∨ s = -1 := by
    have : (s - 1) * (s + 1) = 0 := by linear_combination hs2
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  refine ⟨(Real.sqrt c)⁻¹, μ, s, by positivity, hμ0, hμ, ?_, hs', fun v w => ?_⟩
  · have : ((Real.sqrt c)⁻¹) ^ 2 = c⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hc0.le]
    have h : c ^ 2 = μ ^ 2 := by
      have h' := hs2
      rw [hs, div_pow, div_eq_one_iff_eq (pow_ne_zero 2 hμ0)] at h'
      exact h'
    rw [this, hs]
    field_simp
    linear_combination h
  · simp only [LinearMap.smul_apply]
    rw [← Complex.coe_smul ((Real.sqrt c)⁻¹) (J w), ← Complex.coe_smul ((Real.sqrt c)⁻¹) (J v),
      map_smulₛₗ, map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, Complex.conj_ofReal, hsymm v w]
    simp only [smul_eq_mul]
    ring

theorem bijective_of_sq {J : Module.End ℝ V} {σ : ℝ} (hσ : σ ≠ 0) (hsq : ∀ v, J (J v) = σ • v) :
    Function.Bijective J := by
  have hinj : Function.Injective J := by
    intro a b hab
    have : σ • a = σ • b := by rw [← hsq a, ← hsq b, hab]
    exact smul_right_injective V hσ this
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

end Normalize

section Types

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [IsIrreducible ρ]

/-- From an invariant nondegenerate form with symmetry sign `σ = ±1`, an antilinear equivariant map squaring
to `σ`. -/
theorem exists_anti_sq_of_form {B : LinearMap.BilinForm ℂ V} (hB : B.Nondegenerate)
    (hBi : IsInvariantBilinForm ρ B) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsym : ∀ v w, B w v = (σ : ℂ) * B v w) :
    ∃ J : Module.End ℝ V, IsAnti ρ J ∧ ∀ v, J (J v) = σ • v := by
  haveI := nontrivial_of_irreducible ρ
  obtain ⟨H, hH, hHi⟩ := exists_invariantPosDefHermitian ρ
  set J := rieszMap hH B with hJdef
  have hJ : IsAnti ρ J := rieszMap_isAnti hH hHi hBi
  have hJne : J ≠ 0 := rieszMap_ne_zero hH hB
  have hb := hJ.bijective_or_zero.resolve_left hJne
  obtain ⟨r, μ, ε, hr, hμ0, hμ, hε, hε1, hrel⟩ := exists_normalized hH hHi hJ hb
  -- the relation `B w v = ε B v w`
  have hBJ : ∀ v w, H (J v) w = B v w := fun v w => rieszFun_spec hH B v w
  have hrel' : ∀ v w, B w v = (ε : ℂ) * B v w := by
    intro v w
    have h1 := hrel v w
    simp only [LinearMap.smul_apply] at h1
    rw [← Complex.coe_smul r (J w), ← Complex.coe_smul r (J v), map_smulₛₗ, map_smulₛₗ,
      LinearMap.smul_apply, LinearMap.smul_apply, Complex.conj_ofReal, hBJ, hBJ] at h1
    simp only [smul_eq_mul] at h1
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    apply mul_left_cancel₀ hr0
    linear_combination h1
  -- `ε = σ` because `B ≠ 0`
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (hB.1 v hcon)
  have hεσ : ε = σ := by
    have h1 := hsym v w
    have h2 := hrel' v w
    have : ((σ : ℂ) - ε) * B v w = 0 := by linear_combination h2 - h1
    have := (mul_eq_zero.mp this).resolve_right hw
    exact_mod_cast (sub_eq_zero.mp this).symm
  refine ⟨r • J, hJ.smul_real r, fun v => ?_⟩
  have hsq : (r • J) ((r • J) v) = (r ^ 2 * μ) • v := by
    simp only [LinearMap.smul_apply, map_smul]
    have : J (J v) = μ • v := by rw [hμ, Complex.coe_smul]
    rw [this, smul_smul, smul_smul]
    congr 1; ring
  rw [hsq, ← hε, hεσ]

/-- An antilinear equivariant map squaring to `σ = ±1` gives an invariant nondegenerate form of symmetry
sign `σ`. -/
theorem form_of_anti_sq {J : Module.End ℝ V} (hJ : IsAnti ρ J) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsq : ∀ v, J (J v) = σ • v) :
    ∃ B : LinearMap.BilinForm ℂ V, B.Nondegenerate ∧ IsInvariantBilinForm ρ B ∧
      ∀ v w, B w v = (σ : ℂ) * B v w := by
  haveI := nontrivial_of_irreducible ρ
  obtain ⟨H, hH, hHi⟩ := exists_invariantPosDefHermitian ρ
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> simp [h]
  have hb := bijective_of_sq hσ0 hsq
  obtain ⟨r, μ, ε, hr, hμ0, hμ, hε, hε1, hrel⟩ := exists_normalized hH hHi hJ hb
  have hμσ : μ = σ := by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 := hμ u
    rw [Complex.coe_smul, hsq u] at h1
    exact (smul_left_injective ℝ hu h1).symm
  have hεσ : ε = σ := by
    rw [hε, hμσ]
    rcases hσ with h | h <;> rcases hε1 with h' | h' <;> subst h <;> nlinarith [sq_pos_of_pos hr]
  have hsq' : ∀ v, (r • J) ((r • J) v) = ε • v := by
    intro v
    simp only [LinearMap.smul_apply, map_smul]
    have : J (J v) = μ • v := by rw [hμ, Complex.coe_smul]
    rw [this, smul_smul, smul_smul, hε]
    congr 1; ring
  have hJ' := hJ.smul_real r
  have hb' := bijective_of_sq (σ := ε) (by rcases hε1 with h | h <;> simp [h]) hsq'
  refine ⟨bilJ H (r • J) hJ'.anti, bilJ_nondeg hH hJ' hb', bilJ_invariant hHi hJ', fun v w => ?_⟩
  rw [bilJ_apply, bilJ_apply, hrel v w, hεσ]

/-- If `ρ` is of complex type, every antilinear equivariant map vanishes. -/
theorem eq_zero_of_isComplexType (hc : IsComplexType ρ) {J : Module.End ℝ V} (hJ : IsAnti ρ J) : J = 0 := by
  obtain ⟨H, hH, hHi⟩ := exists_invariantPosDefHermitian ρ
  by_contra hne
  exact not_isComplexType_of_anti hH hHi hJ hne hc

theorem exists_anti_sq_of_isRealType (h : IsRealType ρ) :
    ∃ J : Module.End ℝ V, IsAnti ρ J ∧ ∀ v, J (J v) = (1 : ℝ) • v := by
  obtain ⟨B, hB, hs, hi⟩ := h
  exact exists_anti_sq_of_form hB hi (Or.inl rfl) (fun v w => by simp [hs v w])

theorem exists_anti_sq_of_isQuaternionicType (h : IsQuaternionicType ρ) :
    ∃ J : Module.End ℝ V, IsAnti ρ J ∧ ∀ v, J (J v) = (-1 : ℝ) • v := by
  obtain ⟨B, hB, hs, hi⟩ := h
  exact exists_anti_sq_of_form hB hi (Or.inr rfl) (fun v w => by simp [hs v w])

theorem isRealType_of_anti_sq {J : Module.End ℝ V} (hJ : IsAnti ρ J) (hsq : ∀ v, J (J v) = (1 : ℝ) • v) :
    IsRealType ρ := by
  obtain ⟨B, hB, hi, hs⟩ := form_of_anti_sq hJ (Or.inl rfl) hsq
  exact ⟨B, hB, fun v w => by simpa using hs w v, hi⟩

theorem isQuaternionicType_of_anti_sq {J : Module.End ℝ V} (hJ : IsAnti ρ J)
    (hsq : ∀ v, J (J v) = (-1 : ℝ) • v) : IsQuaternionicType ρ := by
  obtain ⟨B, hB, hi, hs⟩ := form_of_anti_sq hJ (Or.inr rfl) hsq
  exact ⟨B, hB, fun v w => by simpa using hs w v, hi⟩

end Types

section Structure

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [IsIrreducible ρ]

/-- If `J` is antilinear equivariant with `J² = σ = ±1`, every element of `realEnd ρ` is `a + b i + c J + d iJ`. -/
theorem exists_decomp {J : Module.End ℝ V} (hJ : IsAnti ρ J) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsq : J * J = σ • 1) (T : Module.End ℝ V) (hT : T ∈ realEnd ρ) :
    ∃ a b c d : ℝ, T = a • 1 + b • Im + c • J + d • (Im * J) := by
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> simp [h]
  obtain ⟨a, b, hab⟩ := exists_ab_of_comm (Tp T) (Tp_mem T hT) (Tp_comm T)
  have hm : J * Tm T ∈ realEnd ρ := (realEnd ρ).mul_mem hJ.mem (Tm_mem T hT)
  have hc : (J * Tm T) * Im = Im * (J * Tm T) := by
    rw [mul_assoc, Tm_anticomm, mul_neg, ← mul_assoc, hJ.anticomm, neg_mul, neg_neg, mul_assoc]
  obtain ⟨a', b', hab'⟩ := exists_ab_of_comm (J * Tm T) hm hc
  have h1 : σ • Tm T = a' • J - b' • (Im * J) := by
    have : J * (J * Tm T) = σ • Tm T := by rw [← mul_assoc, hsq, smul_mul_assoc, one_mul]
    rw [← this, hab', mul_add, mul_smul_comm, mul_smul_comm, mul_one, hJ.anticomm]
    simp [sub_eq_add_neg]
  have h2 : Tm T = (σ * a') • J + (-(σ * b')) • (Im * J) := by
    have : Tm T = σ • (σ • Tm T) := by rw [smul_smul, hσσ, one_smul]
    rw [this, h1, smul_sub, smul_smul, smul_smul]
    simp [sub_eq_add_neg]
  refine ⟨a, b, σ * a', -(σ * b'), ?_⟩
  rw [← Tp_add_Tm T, hab, h2]
  abel

/-- The quaternionic basis of `realEnd ρ` attached to `J`. -/
noncomputable def endBasis {J : Module.End ℝ V} (hJ : IsAnti ρ J) (c₃ : ℝ) (hsq : J * J = c₃ • 1) :
    QuaternionAlgebra.Basis (realEnd ρ) (-1) 0 c₃ where
  i := ⟨Im, Im_mem ρ⟩
  j := ⟨J, hJ.mem⟩
  k := ⟨Im * J, (realEnd ρ).mul_mem (Im_mem ρ) hJ.mem⟩
  i_mul_i := Subtype.ext (by simp [Im_mul_Im])
  j_mul_j := Subtype.ext (by simpa using hsq)
  i_mul_j := rfl
  j_mul_i := Subtype.ext (by simp [hJ.anticomm])

theorem endBasis_surjective {J : Module.End ℝ V} (hJ : IsAnti ρ J) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsq : J * J = σ • 1) : Function.Surjective (QuaternionAlgebra.Basis.liftHom (endBasis hJ σ hsq)) := by
  rintro ⟨T, hT⟩
  obtain ⟨a, b, c, d, h⟩ := exists_decomp hJ hσ hsq T hT
  refine ⟨⟨a, b, c, d⟩, Subtype.ext ?_⟩
  simp [QuaternionAlgebra.Basis.lift, endBasis, h, Algebra.algebraMap_eq_smul_one]

/-- **Problem 4.1(a), quaternionic case**: if `ρ` carries an antilinear equivariant `J` with `J² = -1`, then the
algebra of real-linear equivariant endomorphisms is isomorphic to the quaternions. -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
noncomputable def realEndEquivQuaternion {J : Module.End ℝ V} (hJ : IsAnti ρ J)
    (hsq : J * J = (-1 : ℝ) • 1) : ℍ[ℝ] ≃ₐ[ℝ] realEnd ρ := by
  haveI := nontrivial_of_irreducible ρ
  exact AlgEquiv.ofBijective (QuaternionAlgebra.Basis.liftHom (endBasis hJ (-1) hsq))
    ⟨(QuaternionAlgebra.Basis.liftHom (endBasis hJ (-1) hsq)).toRingHom.injective,
      endBasis_surjective hJ (Or.inr rfl) hsq⟩

/-- **Problem 4.1(a), complex case**: if every antilinear equivariant map vanishes, the algebra of real-linear
equivariant endomorphisms is `ℂ`. -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
noncomputable def realEndEquivComplex (hno : ∀ J : Module.End ℝ V, IsAnti ρ J → J = 0) :
    ℂ ≃ₐ[ℝ] realEnd ρ := by
  haveI := nontrivial_of_irreducible ρ
  have hI : (⟨Im, Im_mem ρ⟩ : realEnd ρ) * ⟨Im, Im_mem ρ⟩ = -1 := Subtype.ext (by simp [Im_mul_Im])
  refine AlgEquiv.ofBijective (Complex.liftAux (⟨Im, Im_mem ρ⟩ : realEnd ρ) hI)
    ⟨(Complex.liftAux (⟨Im, Im_mem ρ⟩ : realEnd ρ) hI).toRingHom.injective, ?_⟩
  rintro ⟨T, hT⟩
  have hTm : Tm T = 0 := hno _ (isAnti_of (Tm_mem T hT) (Tm_anticomm T))
  obtain ⟨a, b, hab⟩ := exists_ab_of_comm (Tp T) (Tp_mem T hT) (Tp_comm T)
  have hTT : T = a • 1 + b • Im := by
    have := Tp_add_Tm T
    rw [hTm, add_zero, hab] at this
    exact this.symm
  refine ⟨⟨a, b⟩, Subtype.ext ?_⟩
  simp [Complex.liftAux_apply, hTT, Algebra.algebraMap_eq_smul_one]

/-- The split quaternion basis of `2 × 2` real matrices. -/
noncomputable def matBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) (-1 : ℝ) 0 1 where
  i := !![0, -1; 1, 0]
  j := !![1, 0; 0, -1]
  k := !![0, 1; 1, 0]
  i_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  i_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The split quaternion algebra `ℍ[ℝ, -1, 0, 1]` is `M₂(ℝ)`. -/
noncomputable def splitQuatEquivMat : ℍ[ℝ, -1, 0, 1] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  AlgEquiv.ofBijective (QuaternionAlgebra.Basis.liftHom matBasis) (by
    constructor
    · intro p q h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
      have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) h
      have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
      simp [QuaternionAlgebra.Basis.lift, matBasis, Algebra.algebraMap_eq_smul_one] at h00 h01 h10 h11
      ext
      · linarith
      · linarith
      · linarith
      · linarith
    · intro M
      refine ⟨⟨(M 0 0 + M 1 1) / 2, (M 1 0 - M 0 1) / 2, (M 0 0 - M 1 1) / 2, (M 0 1 + M 1 0) / 2⟩, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [QuaternionAlgebra.Basis.lift, matBasis, Algebra.algebraMap_eq_smul_one] <;> ring)

/-- **Problem 4.1(a), real case**: if `ρ` carries an antilinear equivariant `J` with `J² = 1`, then the
algebra of real-linear equivariant endomorphisms is isomorphic to `M₂(ℝ)`. -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
noncomputable def realEndEquivMatrix {J : Module.End ℝ V} (hJ : IsAnti ρ J)
    (hsq : J * J = (1 : ℝ) • 1) : realEnd ρ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := by
  haveI := nontrivial_of_irreducible ρ
  let φ := QuaternionAlgebra.Basis.liftHom (endBasis hJ 1 hsq)
  let ψ : Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] realEnd ρ := φ.comp splitQuatEquivMat.symm.toAlgHom
  have hψ : Function.Bijective ψ := by
    refine ⟨ψ.toRingHom.injective, ?_⟩
    intro T
    obtain ⟨q, hq⟩ := endBasis_surjective hJ (Or.inl rfl) hsq T
    refine ⟨splitQuatEquivMat q, ?_⟩
    show φ (splitQuatEquivMat.symm (splitQuatEquivMat q)) = T
    rw [AlgEquiv.symm_apply_apply]
    exact hq
  exact (AlgEquiv.ofBijective ψ hψ).symm

end Structure

section Headline

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [IsIrreducible ρ]

theorem mul_self_eq_of_sq {J : Module.End ℝ V} {σ : ℝ} (hsq : ∀ v, J (J v) = σ • v) : J * J = σ • 1 :=
  LinearMap.ext fun v => by simp [mul_apply_eq_comp, hsq v]

/-- **Etingof et al., Problem 4.1(a)**: for an irreducible finite-dimensional complex representation of a finite
group, the algebra of real-linear `G`-equivariant endomorphisms of `V` is isomorphic to `ℂ` (complex type),
`M₂(ℝ)` (real type), or `ℍ` (quaternionic type). -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
theorem realEnd_algEquiv_of_isComplexType (hc : IsComplexType ρ) : Nonempty (ℂ ≃ₐ[ℝ] realEnd ρ) :=
  ⟨realEndEquivComplex fun _ hJ => eq_zero_of_isComplexType hc hJ⟩

@[kb "etingof2011" "Problem 4.1, p. 47"]
theorem realEnd_algEquiv_of_isRealType (h : IsRealType ρ) :
    Nonempty (realEnd ρ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨J, hJ, hsq⟩ := exists_anti_sq_of_isRealType h
  exact ⟨realEndEquivMatrix hJ (mul_self_eq_of_sq hsq)⟩

@[kb "etingof2011" "Problem 4.1, p. 47"]
theorem realEnd_algEquiv_of_isQuaternionicType (h : IsQuaternionicType ρ) :
    Nonempty (ℍ[ℝ] ≃ₐ[ℝ] realEnd ρ) := by
  obtain ⟨J, hJ, hsq⟩ := exists_anti_sq_of_isQuaternionicType h
  exact ⟨realEndEquivQuaternion hJ (mul_self_eq_of_sq hsq)⟩

end Headline

section RealForm

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [IsIrreducible ρ]

/-- **Etingof et al., Problem 4.1(b), forward direction**: a representation of real type is the complexification
of a real representation: there is a `G`-invariant real subspace `W` with `V = W ⊕ iW`. -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
theorem exists_realForm_of_isRealType (h : IsRealType ρ) :
    ∃ W : Submodule ℝ V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) ∧ IsCompl W (W.map Im) := by
  obtain ⟨J, hJ, hsq⟩ := exists_anti_sq_of_isRealType h
  have hJJ : ∀ v, J (J v) = v := fun v => by simpa using hsq v
  have hJI : ∀ u, J (Complex.I • u) = -(Complex.I • J u) := fun u => by
    rw [hJ.anti]; simp [Complex.conj_I, neg_smul]
  let W : Submodule ℝ V :=
    { carrier := {v | J v = v}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := fun r v hv => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_smul, hv] }
  refine ⟨W, fun g w hw => ?_, ?_⟩
  · show J (ρ g w) = ρ g w
    have : J w = w := hw
    rw [hJ.comm, this]
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro x hx ⟨u, hu, rfl⟩
      have hu' : J u = u := hu
      have hx' : J (Im u) = Im u := hx
      rw [Im_apply] at hx' ⊢
      rw [hJI, hu'] at hx'
      have : Complex.I • u = 0 := by
        have h2 : (2 : ℝ) • (Complex.I • u) = 0 := by
          rw [two_smul]; nth_rewrite 1 [← hx']; exact neg_add_cancel _
        exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
      exact this
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      refine Submodule.mem_sup.mpr ⟨(1 / 2 : ℝ) • (v + J v), ?_, Im ((1 / 2 : ℝ) • (-(Complex.I • (v - J v)))),
        ⟨_, ?_, rfl⟩, ?_⟩
      · show J ((1 / 2 : ℝ) • (v + J v)) = (1 / 2 : ℝ) • (v + J v)
        rw [map_smul, map_add, hJJ, add_comm]
      · show J ((1 / 2 : ℝ) • (-(Complex.I • (v - J v)))) = (1 / 2 : ℝ) • (-(Complex.I • (v - J v)))
        rw [map_smul, map_neg, hJI, map_sub, hJJ]
        have : J v - v = -(v - J v) := by abel
        simp only [this, smul_neg, neg_neg]
      · have key : Complex.I • ((1 / 2 : ℝ) • (-(Complex.I • (v - J v)))) = (1 / 2 : ℝ) • (v - J v) := by
          rw [smul_comm Complex.I (1 / 2 : ℝ), smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul,
            neg_neg]
        rw [Im_apply, key, ← smul_add]
        rw [show (v + J v) + (v - J v) = (2 : ℝ) • v by rw [two_smul]; abel, smul_smul]
        norm_num

/-- The real-linear map `(a, b) ↦ a + i b` from `W × W` to `V`. -/
noncomputable def phiW (W : Submodule ℝ V) : (W × W) →ₗ[ℝ] V := W.subtype.coprod (Im ∘ₗ W.subtype)

theorem phiW_apply (W : Submodule ℝ V) (p : W × W) :
    phiW W p = (p.1 : V) + Complex.I • (p.2 : V) := rfl

theorem phiW_bijective {W : Submodule ℝ V} (hc : IsCompl W (W.map Im)) : Function.Bijective (phiW W) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    rw [phiW_apply] at hab
    have h1 : (a : V) = -(Complex.I • (b : V)) := eq_neg_of_add_eq_zero_left hab
    have h2 : (a : V) ∈ W.map Im := by
      refine ⟨-(b : V), W.neg_mem b.2, ?_⟩
      rw [Im_apply, h1, smul_neg]
    have h3 : (a : V) = 0 := (Submodule.disjoint_def.mp hc.disjoint) _ a.2 h2
    rw [h3, zero_add] at hab
    have h4 : (b : V) = 0 := (smul_eq_zero.mp hab).resolve_left Complex.I_ne_zero
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  · intro v
    have : v ∈ W ⊔ W.map Im := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, c, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.mp this
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

/-- **Etingof et al., Problem 4.1(b), converse**: if `V` is the complexification of a real subrepresentation
(`G`-invariant real subspace `W` with `V = W ⊕ iW`), then `ρ` is of real type. -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
theorem isRealType_of_realForm {W : Submodule ℝ V} (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hc : IsCompl W (W.map Im)) : IsRealType ρ := by
  have hb := phiW_bijective hc
  let e : (W × W) ≃ₗ[ℝ] V := LinearEquiv.ofBijective (phiW W) hb
  let δ : (W × W) →ₗ[ℝ] (W × W) := LinearMap.prodMap LinearMap.id (-LinearMap.id)
  let J : Module.End ℝ V := e.toLinearMap ∘ₗ δ ∘ₗ e.symm.toLinearMap
  have key : ∀ a b : V, a ∈ W → b ∈ W → J (a + Complex.I • b) = a - Complex.I • b := by
    intro a b ha hb'
    have h0 : e (⟨a, ha⟩, ⟨b, hb'⟩) = a + Complex.I • b := rfl
    show e (δ (e.symm (a + Complex.I • b))) = _
    rw [← h0, LinearEquiv.symm_apply_apply]
    simp [δ, e, phiW_apply, sub_eq_add_neg, smul_neg]
  have hsurj : ∀ v : V, ∃ a b : V, a ∈ W ∧ b ∈ W ∧ v = a + Complex.I • b := fun v => by
    obtain ⟨p, rfl⟩ := hb.2 v
    exact ⟨p.1, p.2, p.1.2, p.2.2, rfl⟩
  have hcomm : ∀ g v, J (ρ g v) = ρ g (J v) := by
    intro g v
    obtain ⟨a, b, ha, hb', rfl⟩ := hsurj v
    rw [map_add, map_smul, key _ _ (hW g a ha) (hW g b hb'), key a b ha hb', map_sub, map_smul]
  have hanti : J * Im = -(Im * J) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, b, ha, hb', rfl⟩ := hsurj v
    have e1 : Im (a + Complex.I • b) = -b + Complex.I • a := by
      rw [Im_apply, smul_add, smul_smul, Complex.I_mul_I, neg_smul, one_smul, add_comm]
    simp only [mul_apply_eq_comp, Function.comp_apply, LinearMap.neg_apply]
    rw [e1, key (-b) a (W.neg_mem hb') ha, key a b ha hb', Im_apply, smul_sub, smul_smul,
      Complex.I_mul_I, neg_smul, one_smul]
    abel
  have hJ : IsAnti ρ J := isAnti_of (mem_realEnd.mpr hcomm) hanti
  refine isRealType_of_anti_sq hJ fun v => ?_
  obtain ⟨a, b, ha, hb', rfl⟩ := hsurj v
  have e2 : a - Complex.I • b = a + Complex.I • (-b) := by rw [smul_neg, sub_eq_add_neg]
  rw [key a b ha hb', e2, key a (-b) ha (W.neg_mem hb'), smul_neg, sub_neg_eq_add, one_smul]

/-- **Etingof et al., Problem 4.1(b)**: an irreducible complex representation of a finite group is of real type
if and only if it is the complexification of a real representation, i.e. there is a `G`-invariant real subspace
`W ⊆ V` with `V = W ⊕ iW`. -/
@[kb "etingof2011" "Problem 4.1, p. 47"]
theorem isRealType_iff_exists_realForm :
    IsRealType ρ ↔ ∃ W : Submodule ℝ V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) ∧ IsCompl W (W.map Im) :=
  ⟨exists_realForm_of_isRealType, fun ⟨_, hW, hc⟩ => isRealType_of_realForm hW hc⟩

end RealForm

end RealType

end UndergradKB.RepresentationTheory
