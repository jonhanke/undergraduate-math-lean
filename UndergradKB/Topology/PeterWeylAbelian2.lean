import UndergradKB.Topology.PeterWeylAbelian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import UndergradKB.Common.Attr

/-!
# Characters of a compact abelian group separate points (TP-581, main argument)

Continuation of `PeterWeylAbelian.lean`: the bump kernel, the nonzero compact self-adjoint operator on
the orthogonal complement of the `g`-invariant functions, its finite-dimensional eigenspace, the
common eigenvector of the translations, and the character it defines.
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate Pointwise

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

namespace PeterWeyl

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

theorem exists_bump {g : K} (hg : g ≠ 1) : ∃ φr : C(K, ℝ), (∀ y, 0 ≤ φr y) ∧ φr 1 = 1 ∧
    (∀ y, φr y⁻¹ = φr y) ∧ ∀ y, φr y ≠ 0 → φr (g * y⁻¹) ≠ 0 → False := by
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset (U := {g}ᶜ)
    (isOpen_compl_singleton.mem_nhds (Ne.symm hg))
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl
    isClosed_singleton (Set.disjoint_singleton_right.2 (fun h => h hV1))
  have hsupp : ∀ y, f y ≠ 0 → y ∈ V := fun y hy => by_contra fun h => hy (hf0 h)
  have hf1' : f 1 = 1 := hf1 (Set.mem_singleton 1)
  refine ⟨⟨fun y => f y * f y⁻¹, by fun_prop⟩, fun y => mul_nonneg (hf01 y).1 (hf01 _).1, ?_, ?_, ?_⟩
  · simp [hf1']
  · intro y; simp [mul_comm]
  · intro y hy hgy
    simp only [ContinuousMap.coe_mk] at hy hgy
    have h1 : y ∈ V := hsupp y (left_ne_zero_of_mul hy)
    have h2 : g * y⁻¹ ∈ V := hsupp _ (left_ne_zero_of_mul hgy)
    have : g ∈ V * V := ⟨g * y⁻¹, h2, y, h1, by simp⟩
    exact hVV this (Set.mem_singleton g)

/-- A complex number of modulus one as an element of the circle. -/
def toCircle (z : ℂ) (hz : ‖z‖ = 1) : Circle := ⟨z, mem_sphere_zero_iff_norm.2 hz⟩

@[simp] theorem coe_toCircle (z : ℂ) (hz : ‖z‖ = 1) : (toCircle z hz : ℂ) = z := rfl

variable [MeasurableSpace K] [BorelSpace K]

theorem exists_char_ne_one_of_measure (μ : Measure K) [μ.IsHaarMeasure] {g : K} (hg : g ≠ 1) :
    ∃ χ : PontryaginDual K, χ g ≠ 1 := by
  classical
  obtain ⟨φr, hφ0, hφ1, hφinv, hφsupp⟩ := exists_bump hg
  let φ : C(K, ℂ) := ⟨fun y => (φr y : ℂ), Complex.continuous_ofReal.comp φr.continuous⟩
  let T := kernelOp μ φ
  let Tadj := ContinuousLinearMap.adjoint T
  let A : L2 μ →L[ℂ] L2 μ := T ∘L Tadj
  let u : L2 μ := ContinuousMap.toLp 2 μ ℂ φ
  let F₁ : C(K, ℂ) := kernelOpC μ φ u
  have hF₁ : ∀ x, F₁ x = ∫ y, (φr y : ℂ) * conj (φr (x * y⁻¹) : ℂ) ∂μ := by
    intro x
    show ⟪kerL μ φ x, u⟫_ℂ = _
    rw [kerL, ContinuousMap.inner_toLp]
    rfl
  have hF₁g : F₁ g = 0 := by
    rw [hF₁]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    by_cases h1 : φr y = 0
    · simp [h1]
    by_cases h2 : φr (g * y⁻¹) = 0
    · simp [h2]
    exact (hφsupp y h1 h2).elim
  have hF₁1 : F₁ 1 ≠ 0 := by
    rw [hF₁]
    have : (fun y => (φr y : ℂ) * conj (φr (1 * y⁻¹) : ℂ)) = fun y => ((φr y ^ 2 : ℝ) : ℂ) := by
      funext y; simp [hφinv, sq]
    rw [this, integral_complex_ofReal]
    have hpos : 0 < ∫ y, φr y ^ 2 ∂μ :=
      (φr.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_ne_zero
        (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
        (fun y => sq_nonneg _) (x := 1) (by simp [hφ1])
    exact_mod_cast hpos.ne'
  let w : L2 μ := T u
  have hw : w = ContinuousMap.toLp 2 μ ℂ F₁ := rfl
  have hgw : transl μ g w ≠ w := by
    rw [hw, transl_toLp]
    intro h
    have := congrArg (fun F : C(K, ℂ) => F 1) (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ h)
    simp only [ContinuousMap.comp_apply, mulLeftC, ContinuousMap.coe_mk, mul_one] at this
    exact hF₁1 (this ▸ hF₁g)
  set W := invariants μ g
  let h : L2 μ := transl μ g w - w
  have hhW : h ∈ Wᗮ := transl_sub_mem_orthogonal μ g w
  have hinner : ⟪h, w⟫_ℂ ≠ 0 := by
    intro h0
    apply hgw
    have hn : ‖transl μ g w‖ = ‖w‖ := (transl μ g).norm_map w
    have h1 : ⟪transl μ g w, w⟫_ℂ = ⟪w, w⟫_ℂ := by
      have h0' : ⟪transl μ g w - w, w⟫_ℂ = 0 := h0
      rwa [inner_sub_left, sub_eq_zero] at h0'
    have hre : RCLike.re ⟪transl μ g w, w⟫_ℂ = ‖w‖ ^ 2 := by
      rw [h1, inner_self_eq_norm_sq]
    have : ‖transl μ g w - w‖ ^ 2 = 0 := by
      rw [@norm_sub_sq ℂ, hn, hre]; ring
    exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this))
  have hTadjh : Tadj h ≠ 0 := by
    intro h0
    apply hinner
    have := ContinuousLinearMap.adjoint_inner_left T u h
    rw [h0, inner_zero_left] at this
    exact this.symm
  have hAh : A h ≠ 0 := by
    intro h0
    apply hTadjh
    have : ⟪A h, h⟫_ℂ = ⟪Tadj h, Tadj h⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right T (Tadj h) h).symm
    rw [h0, inner_zero_left] at this
    exact inner_self_eq_zero.1 this.symm
  have hAsym : (A : L2 μ →ₗ[ℂ] L2 μ).IsSymmetric := by
    intro x y
    show ⟪T (Tadj x), y⟫_ℂ = ⟪x, T (Tadj y)⟫_ℂ
    rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  have hAtransl : ∀ a f, A (transl μ a f) = transl μ a (A f) := by
    intro a f
    show T (Tadj (transl μ a f)) = _
    rw [adjoint_kernelOp_transl, kernelOp_transl]
    rfl
  have hAW : ∀ x ∈ Wᗮ, A x ∈ Wᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hs : ⟪A v, x⟫_ℂ = ⟪v, A x⟫_ℂ := hAsym v x
    rw [← hs]
    refine Submodule.inner_right_of_mem_orthogonal ?_ hx
    rw [mem_invariants, ← hAtransl, (mem_invariants μ).1 hv]
  have hAcomp : IsCompactOperator A := (isCompactOperator_kernelOp μ φ).comp_clm Tadj
  let S : Wᗮ →L[ℂ] Wᗮ := A.restrict hAW
  have hScomp : IsCompactOperator S := hAcomp.restrict' (f := (A : L2 μ →ₗ[ℂ] L2 μ)) hAW
  have hSsym : (S : Wᗮ →ₗ[ℂ] Wᗮ).IsSymmetric := hAsym.restrict_invariant hAW
  have hS0 : S ≠ 0 := by
    intro h0
    apply hAh
    have := congrArg (fun L : Wᗮ →L[ℂ] Wᗮ => ((L ⟨h, hhW⟩ : Wᗮ) : L2 μ)) h0
    simpa [S] using this
  obtain ⟨lam, hlam, hlam0⟩ :
      ∃ lam, Module.End.HasEigenvalue (S : Module.End ℂ Wᗮ) lam ∧ lam ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hS0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hScomp hSsym).1 hno)
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  let E := Module.End.eigenspace (A : Module.End ℂ (L2 μ)) lam
  let P : Submodule ℂ (L2 μ) := E ⊓ Wᗮ
  have hEfin : FiniteDimensional ℂ E :=
    ContinuousLinearMap.finite_dimensional_eigenspace hAcomp lam hlam0
  have hPfin : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le inf_le_left
  have hmemP : ∀ x, x ∈ P ↔ A x = lam • x ∧ x ∈ Wᗮ := by
    intro x; rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]; rfl
  have hvP : (v : L2 μ) ∈ P := by
    refine (hmemP _).2 ⟨?_, v.2⟩
    have := congrArg Subtype.val hv.apply_eq_smul
    simpa [S] using this
  have hv0 : (v : L2 μ) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
  have hPne : P ≠ ⊥ := fun hb => hv0 (by rw [hb] at hvP; simpa using hvP)
  have hPinv : ∀ a, ∀ x ∈ P, (transl μ a).toLinearMap x ∈ P := by
    intro a x hx
    obtain ⟨h1, h2⟩ := (hmemP x).1 hx
    refine (hmemP _).2 ⟨?_, transl_mem_orthogonal μ g a h2⟩
    simp only [LinearIsometry.coe_toLinearMap]
    rw [hAtransl, h1, map_smul]
  obtain ⟨f, hfP, hf0, hfc⟩ := exists_common_eigenvector (fun a => (transl μ a).toLinearMap)
    (fun a b => LinearMap.ext fun x => transl_comm μ a b x) P hPfin hPne hPinv
  obtain ⟨hfA, hfW⟩ := (hmemP f).1 hfP
  let F₀ : C(K, ℂ) := kernelOpC μ φ (lam⁻¹ • Tadj f)
  have hfF : f = ContinuousMap.toLp 2 μ ℂ F₀ := by
    show f = T (lam⁻¹ • Tadj f)
    rw [map_smul]
    have : T (Tadj f) = lam • f := hfA
    rw [this, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have hF₀rel : ∀ a, ∃ c : ℂ, ∀ x, F₀ (a * x) = c * F₀ x := by
    intro a
    obtain ⟨c, hc⟩ := hfc a
    refine ⟨c, fun x => ?_⟩
    have h1 : ContinuousMap.toLp 2 μ ℂ (F₀.comp (mulLeftC a)) =
        ContinuousMap.toLp 2 μ ℂ (c • F₀) := by
      rw [← transl_toLp, ← hfF, map_smul, ← hfF]; exact hc
    have := congrArg (fun F : C(K, ℂ) => F x)
      (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ h1)
    simpa [mulLeftC] using this
  have hF₀ne : F₀ ≠ 0 := by
    intro h0; apply hf0; rw [hfF, h0, map_zero]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, F₀ x₀ ≠ 0 := by
    by_contra hno; push Not at hno; exact hF₀ne (ContinuousMap.ext hno)
  let χf : K → ℂ := fun a => F₀ (a * x₀) / F₀ x₀
  have hχrel : ∀ a x, F₀ (a * x) = χf a * F₀ x := by
    intro a x
    obtain ⟨c, hc⟩ := hF₀rel a
    have : c = χf a := by
      simp only [χf]; rw [hc x₀, mul_div_assoc, div_self hx₀, mul_one]
    rw [hc x, this]
  have htransl : ∀ a, transl μ a f = χf a • f := by
    intro a
    rw [hfF, transl_toLp, ← map_smul]
    congr 1
    ext x
    simp [mulLeftC, hχrel]
  have hnorm : ∀ a, ‖χf a‖ = 1 := by
    intro a
    have h1 : ‖transl μ a f‖ = ‖f‖ := (transl μ a).norm_map f
    rw [htransl, norm_smul] at h1
    have hfpos : 0 < ‖f‖ := norm_pos_iff.2 hf0
    exact mul_right_cancel₀ hfpos.ne' (h1.trans (one_mul _).symm)
  have hmul : ∀ a b, χf (a * b) = χf a * χf b := by
    intro a b
    have h1 := hχrel (a * b) x₀
    have h2 : F₀ (a * b * x₀) = χf a * (χf b * F₀ x₀) := by rw [mul_assoc, hχrel, hχrel]
    have := h1.symm.trans h2
    rw [← mul_assoc] at this
    exact mul_right_cancel₀ hx₀ this
  have hcont : Continuous χf :=
    (F₀.continuous.comp (continuous_id.mul continuous_const)).div_const _
  let χ : PontryaginDual K :=
    { toFun := fun a => toCircle (χf a) (hnorm a)
      map_one' := Circle.ext (by simp [χf, div_self hx₀])
      map_mul' := fun a b => Circle.ext (by simp [hmul])
      continuous_toFun := continuous_induced_rng.2 hcont }
  refine ⟨χ, fun h1 => ?_⟩
  have hχg : χf g = 1 := congrArg Subtype.val h1
  have hfWin : f ∈ W := by rw [mem_invariants, htransl, hχg, one_smul]
  exact hf0 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hfWin hfW))

end PeterWeyl

end UndergradKB.Topology
