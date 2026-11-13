import UndergradKB.Topology.PeterWeylGeneral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-!
# Peter-Weyl theorem for compact groups (Morris, Theorem A5.10.1; TP-580)

For a compact Hausdorff group `K` and `g ≠ 1`, with the operator `T` of `PeterWeylGeneral.lean`
built from a symmetric bump `φ` supported in a neighbourhood `V` of `1` with `g ∉ V V`: the compact
self-adjoint operator `A = T T*` commutes with all left translations and does not vanish on the
orthogonal complement of the `g`-invariant functions, so it has an eigenvalue `λ ≠ 0` with an
eigenvector `v` there. The eigenspace `E` of `λ` is finite dimensional (compactness), invariant under
all translations, consists of continuous functions, and `g` moves `v ∈ E`. Translation on `E` is a
continuous unitary representation in which `g` acts nontrivially. (The abelian case, wave 2, went on
to a common eigenvector; here the finite-dimensional representation itself is the answer.)
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate Pointwise

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

namespace PeterWeylGeneral

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K]

/-- A symmetric bump at `1` whose support `S` satisfies `g ∉ S S`. -/
theorem exists_bump {g : K} (hg : g ≠ 1) : ∃ φr : C(K, ℝ), (∀ y, 0 ≤ φr y) ∧ φr 1 = 1 ∧
    (∀ y, φr y⁻¹ = φr y) ∧ ∀ y, φr y ≠ 0 → φr (y⁻¹ * g) ≠ 0 → False := by
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
    have h2 : y⁻¹ * g ∈ V := hsupp _ (left_ne_zero_of_mul hgy)
    have : g ∈ V * V := ⟨y, h1, y⁻¹ * g, h2, by simp⟩
    exact hVV this (Set.mem_singleton g)

variable [MeasurableSpace K] [BorelSpace K]

/-- The core of the Peter-Weyl theorem: a finite-dimensional subspace of `L²(K)` invariant under all
translations, consisting of continuous functions, on which `g` acts nontrivially. -/
theorem exists_invariant_subspace (μ : Measure K) [μ.IsHaarMeasure] {g : K} (hg : g ≠ 1) :
    ∃ E : Submodule ℂ (L2 μ), FiniteDimensional ℂ E ∧ (∀ a, ∀ x ∈ E, transl μ a x ∈ E) ∧
      (∀ x ∈ E, ∃ F : C(K, ℂ), x = ContinuousMap.toLp 2 μ ℂ F) ∧
      ∃ x ∈ E, transl μ g x ≠ x := by
  classical
  obtain ⟨φr, hφ0, hφ1, hφinv, hφsupp⟩ := exists_bump hg
  let φ : C(K, ℂ) := ⟨fun y => (φr y : ℂ), Complex.continuous_ofReal.comp φr.continuous⟩
  let T := kernelOp μ φ
  let Tadj := ContinuousLinearMap.adjoint T
  let A : L2 μ →L[ℂ] L2 μ := T ∘L Tadj
  let u : L2 μ := ContinuousMap.toLp 2 μ ℂ φ
  let F₁ : C(K, ℂ) := kernelOpC μ φ u
  have hF₁ : ∀ x, F₁ x = ∫ y, (φr y : ℂ) * conj (φr (y⁻¹ * x) : ℂ) ∂μ := by
    intro x
    show ⟪kerL μ φ x, u⟫_ℂ = _
    rw [kerL, ContinuousMap.inner_toLp]
    rfl
  have hF₁g : F₁ g = 0 := by
    rw [hF₁]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    by_cases h1 : φr y = 0
    · simp [h1]
    by_cases h2 : φr (y⁻¹ * g) = 0
    · simp [h2]
    exact (hφsupp y h1 h2).elim
  have hF₁1 : F₁ 1 ≠ 0 := by
    rw [hF₁]
    have : (fun y => (φr y : ℂ) * conj (φr (y⁻¹ * 1) : ℂ)) = fun y => ((φr y ^ 2 : ℝ) : ℂ) := by
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
  have hEfin : FiniteDimensional ℂ E :=
    ContinuousLinearMap.finite_dimensional_eigenspace hAcomp lam hlam0
  have hmemE : ∀ x, x ∈ E ↔ A x = lam • x := fun x => Module.End.mem_eigenspace_iff
  have hvE : (v : L2 μ) ∈ E := by
    refine (hmemE _).2 ?_
    have := congrArg Subtype.val hv.apply_eq_smul
    simpa [S] using this
  have hv0 : (v : L2 μ) ≠ 0 := fun h0 => hv.2 (Subtype.ext h0)
  refine ⟨E, hEfin, ?_, ?_, v, hvE, ?_⟩
  · intro a x hx
    refine (hmemE _).2 ?_
    rw [hAtransl, (hmemE x).1 hx, map_smul]
  · intro x hx
    refine ⟨kernelOpC μ φ (lam⁻¹ • Tadj x), ?_⟩
    show x = T (lam⁻¹ • Tadj x)
    rw [map_smul]
    have : T (Tadj x) = lam • x := (hmemE x).1 hx
    rw [this, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  · intro hgv
    have hvW : (v : L2 μ) ∈ W := hgv
    exact hv0 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hvW v.2))

section Rep

variable (μ : Measure K) [μ.IsHaarMeasure] (E : Submodule ℂ (L2 μ))
  (hE : ∀ a, ∀ x ∈ E, transl μ a x ∈ E)

/-- Translation `f ↦ f (a⁻¹ ·)` on an invariant subspace, as a linear isometry equivalence. -/
noncomputable def translOn (a : K) : E ≃ₗᵢ[ℂ] E :=
  { toFun := fun x => ⟨transl μ a⁻¹ x, hE _ _ x.2⟩
    invFun := fun x => ⟨transl μ a x, hE _ _ x.2⟩
    map_add' := fun x y => Subtype.ext (map_add (transl μ a⁻¹) (x : L2 μ) y)
    map_smul' := fun c x => Subtype.ext (map_smul (transl μ a⁻¹) c (x : L2 μ))
    left_inv := fun x => Subtype.ext (transl_inv_transl μ a x)
    right_inv := fun x => Subtype.ext (by
      have := transl_inv_transl μ a⁻¹ (x : L2 μ)
      rwa [inv_inv] at this)
    norm_map' := fun x => (transl μ a⁻¹).norm_map (x : L2 μ) }

theorem translOn_apply (a : K) (x : E) : (translOn μ E hE a x : L2 μ) = transl μ a⁻¹ x := rfl

/-- The translation representation on an invariant subspace. -/
noncomputable def translRep : K →* (E ≃ₗᵢ[ℂ] E) where
  toFun := translOn μ E hE
  map_one' := LinearIsometryEquiv.ext fun x => Subtype.ext (by
    rw [translOn_apply, inv_one, transl_one]
    rfl)
  map_mul' a b := LinearIsometryEquiv.ext fun x => Subtype.ext (by
    rw [translOn_apply, mul_inv_rev, transl_mul]
    rfl)

/-- The translation representation is continuous (strongly, hence in norm since `E` is finite
dimensional) when `E` consists of continuous functions. -/
theorem continuous_translRep [FiniteDimensional ℂ E]
    (hc : ∀ x ∈ E, ∃ F : C(K, ℂ), x = ContinuousMap.toLp 2 μ ℂ F) :
    Continuous fun a => ((Unitary.linearIsometryEquiv.symm (translRep μ E hE a) :
      unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
  rw [continuous_clm_apply]
  intro y
  obtain ⟨F, hF⟩ := hc y y.2
  have hcurry : Continuous fun a : K => F.comp (mulLeftC a⁻¹) := by
    have : (fun a : K => F.comp (mulLeftC a⁻¹)) = ContinuousMap.curry (F.comp
        ⟨fun p : K × K => p.1⁻¹ * p.2, (continuous_inv.comp continuous_fst).mul continuous_snd⟩) := by
      ext a z
      rfl
    rw [this]
    exact (ContinuousMap.curry _).continuous
  have h2 : Continuous fun a : K => ContinuousMap.toLp 2 μ ℂ (F.comp (mulLeftC a⁻¹)) :=
    (ContinuousMap.toLp 2 μ ℂ).continuous.comp hcurry
  refine Continuous.subtype_mk (h2.congr fun a => ?_) _
  show ContinuousMap.toLp 2 μ ℂ (F.comp (mulLeftC a⁻¹)) = transl μ a⁻¹ (y : L2 μ)
  rw [hF, transl_toLp]

end Rep

end PeterWeylGeneral

open PeterWeylGeneral

universe u

/-- Peter-Weyl, operator form: for `g ≠ 1` in a compact Hausdorff group there is a continuous
unitary representation on a finite-dimensional complex Hilbert space in which `g` acts
nontrivially. -/
theorem exists_unitaryRep_ne_one {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] {g : K} (hg : g ≠ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
      FiniteDimensional ℂ H ∧ ∃ π : K →* unitary (H →L[ℂ] H), Continuous π ∧ π g ≠ 1 := by
  borelize K
  obtain ⟨E, hEfin, hE, hc, x, hxE, hgx⟩ := exists_invariant_subspace (Measure.haar : Measure K) hg
  let π : K →* unitary (E →L[ℂ] E) :=
    (Unitary.linearIsometryEquiv.symm : (E ≃ₗᵢ[ℂ] E) ≃* unitary (E →L[ℂ] E)).toMonoidHom.comp
      (translRep _ E hE)
  refine ⟨E, inferInstance, inferInstance, inferInstance, hEfin, π, ?_, ?_⟩
  · exact continuous_induced_rng.2 (continuous_translRep _ E hE hc)
  · intro h1
    apply hgx
    have h2 : translRep _ E hE g = 1 := by
      have := congrArg (fun u => Unitary.linearIsometryEquiv u) h1
      simpa [π] using this
    have h3 : transl _ g⁻¹ x = x := by
      have := congrArg (fun e : E ≃ₗᵢ[ℂ] E => ((e ⟨x, hxE⟩ : E) : L2 (Measure.haar : Measure K))) h2
      exact this
    calc transl _ g x = transl _ g (transl _ g⁻¹ x) := by rw [h3]
      _ = x := transl_inv_transl _ g x

/-- Morris, Topology Without Tears, Theorem A5.10.1 (TP-580), Peter-Weyl theorem. Let `K` be a
compact Hausdorff group. For each `g ≠ e` in `K` there is a continuous homomorphism `π` of `K` into
the unitary group `U(n)` (unitary `n × n` complex matrices), for some `n`, with `π g ≠ e`. -/
@[kb "morris2024" "Theorem A5.10.1, p. 572"]
theorem exists_unitaryMatrixRep_ne_one {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] {g : K} (hg : g ≠ 1) :
    ∃ (n : ℕ) (π : K →* Matrix.unitaryGroup (Fin n) ℂ), Continuous π ∧ π g ≠ 1 := by
  obtain ⟨H, _, _, _, hfin, π, hπc, hπg⟩ := exists_unitaryRep_ne_one hg
  let b := stdOrthonormalBasis ℂ H
  let Ψ : (H →ₗ[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := LinearMap.adjoint_toContinuousLinearMap }
  let Φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] Matrix (Fin (Module.finrank ℂ H)) (Fin (Module.finrank ℂ H)) ℂ :=
    Ψ.symm.trans (LinearMap.toMatrixOrthonormal b)
  have hΦc : Continuous Φ :=
    LinearMap.continuous_of_finiteDimensional Φ.toAlgEquiv.toLinearEquiv.toLinearMap
  let πM : K →* Matrix.unitaryGroup (Fin (Module.finrank ℂ H)) ℂ :=
    { toFun := fun a => ⟨Φ (π a), Unitary.map_mem Φ (π a).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  refine ⟨Module.finrank ℂ H, πM, ?_, ?_⟩
  · exact continuous_induced_rng.2 (hΦc.comp (continuous_subtype_val.comp hπc))
  · intro h1
    apply hπg
    have h2 : Φ (π g) = Φ 1 := by
      have := congrArg Subtype.val h1
      rw [map_one]
      exact this
    exact Subtype.ext (Φ.injective h2)

/-- Morris, Topology Without Tears, Theorem A5.10.1 (TP-580), separation form: the continuous
unitary matrix representations of a compact Hausdorff group separate its points. -/
@[kb "morris2024" "Theorem A5.10.1, p. 572"]
theorem unitaryMatrixReps_separate_points {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] {x y : K} (hxy : x ≠ y) :
    ∃ (n : ℕ) (π : K →* Matrix.unitaryGroup (Fin n) ℂ), Continuous π ∧ π x ≠ π y := by
  obtain ⟨n, π, hc, h⟩ := exists_unitaryMatrixRep_ne_one (g := x⁻¹ * y)
    (fun h => hxy (inv_mul_eq_one.1 h))
  refine ⟨n, π, hc, fun h' => h ?_⟩
  rw [map_mul, map_inv, h', inv_mul_cancel]

end UndergradKB.Topology
