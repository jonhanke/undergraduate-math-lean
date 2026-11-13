import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr

/-!
# Characters of a compact abelian group separate points (Peter-Weyl, abelian case)

Morris, *Topology Without Tears*, Corollary A5.10.2 (TP-581): a compact Hausdorff abelian group has
enough continuous characters to separate points.  The proof is the classical spectral one.  On
`L²(K)` for a Haar measure, a continuous kernel `φ` gives the operator `T f (x) = ⟪φ(x ·⁻¹), f⟫`,
whose values are continuous functions; by Arzelà-Ascoli it is compact, and it commutes with the
translations.  The compact self-adjoint operator `A = T T*` has, on the orthogonal complement of the
functions invariant under a given `g ≠ 1`, a nonzero eigenvalue with a finite-dimensional
eigenspace (spectral theorem for compact self-adjoint operators, in Mathlib); the commuting
translations have a common eigenvector there, which is a continuous function `F` with
`F (a x) = χ a * F x` for a continuous character `χ`, and `χ g ≠ 1`.
-/

open MeasureTheory Filter Topology Set

set_option linter.unusedSectionVars false
open scoped InnerProductSpace ComplexConjugate

namespace UndergradKB.Topology

namespace PeterWeyl

/-- Common eigenvector of a commuting family of linear maps preserving a nonzero finite-dimensional
subspace (over `ℂ`). -/
theorem exists_common_eigenvector {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : ι → V →ₗ[ℂ] V)
    (hc : ∀ i j, L i ∘ₗ L j = L j ∘ₗ L i) :
    ∀ (P : Submodule ℂ V), FiniteDimensional ℂ P → P ≠ ⊥ → (∀ i, ∀ x ∈ P, L i x ∈ P) →
      ∃ v ∈ P, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, L i v = c • v := by
  intro P
  induction h : Module.finrank ℂ P using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  intro hfin hP hinv
  by_cases hsc : ∀ i, ∃ c : ℂ, ∀ x ∈ P, L i x = c • x
  · obtain ⟨v, hvP, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact ⟨v, hvP, hv, fun i => (hsc i).imp fun c hc => hc v hvP⟩
  · push Not at hsc
    obtain ⟨i, hi⟩ := hsc
    let Li : Module.End ℂ P := (L i).restrict (hinv i)
    have : Nontrivial P := Submodule.nontrivial_iff_ne_bot.2 hP
    obtain ⟨c, hcev⟩ := Module.End.exists_eigenvalue Li
    obtain ⟨w, hw⟩ := hcev.exists_hasEigenvector
    let P' : Submodule ℂ V := P ⊓ LinearMap.ker (L i - c • LinearMap.id)
    have hP'le : P' ≤ P := inf_le_left
    have hker : ∀ y, y ∈ P' ↔ y ∈ P ∧ L i y = c • y := by
      intro y
      rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
    have hwP' : (w : V) ∈ P' := by
      refine (hker _).2 ⟨w.2, ?_⟩
      have := congrArg Subtype.val hw.apply_eq_smul
      simpa [Li] using this
    have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
    have hP'ne : P' ≠ ⊥ := fun hb => hw0 (by rw [hb] at hwP'; simpa using hwP')
    have hlt : P' < P := by
      refine lt_of_le_of_ne hP'le fun heq => ?_
      obtain ⟨x, hxP, hx⟩ := hi c
      have hx' : x ∈ P' := heq ▸ hxP
      exact hx ((hker x).1 hx').2
    have hfin' : FiniteDimensional ℂ P' := Submodule.finiteDimensional_of_le hP'le
    have hrank : Module.finrank ℂ P' < n := h ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hinv' : ∀ j, ∀ x ∈ P', L j x ∈ P' := by
      intro j x hx
      obtain ⟨hx1, hx2⟩ := (hker x).1 hx
      refine (hker _).2 ⟨hinv j x hx1, ?_⟩
      have := congrArg (fun f => f x) (hc i j)
      simp only [LinearMap.comp_apply] at this
      rw [this, hx2, map_smul]
    obtain ⟨v, hv, hv0, hvc⟩ := ih _ hrank P' rfl hfin' hP'ne hinv'
    exact ⟨v, hP'le hv, hv0, hvc⟩

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]

/-- The Hilbert space `L²(K, μ)`. -/
noncomputable abbrev L2 := Lp ℂ 2 μ

/-- Left translation `f ↦ f (a * ·)` on `L²`. -/
noncomputable def transl (a : K) : L2 μ →ₗᵢ[ℂ] L2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => a * x) (measurePreserving_mul_left μ a)

theorem transl_apply_ae (a : K) (f : L2 μ) : transl μ a f =ᵐ[μ] fun x => f (a * x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem transl_mul (a b : K) (f : L2 μ) : transl μ (a * b) f = transl μ b (transl μ a f) := by
  apply Lp.ext
  have h1 := transl_apply_ae μ (a * b) f
  have h2 := transl_apply_ae μ b (transl μ a f)
  have h3 : (fun x => (transl μ a f) (b * x)) =ᵐ[μ] fun x => f (a * (b * x)) :=
    (measurePreserving_mul_left μ b).quasiMeasurePreserving.ae_eq_comp (transl_apply_ae μ a f)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3, mul_assoc]

theorem transl_one (f : L2 μ) : transl μ 1 f = f := by
  apply Lp.ext
  filter_upwards [transl_apply_ae μ 1 f] with x hx
  rw [hx, one_mul]

theorem transl_comm (a b : K) (f : L2 μ) :
    transl μ a (transl μ b f) = transl μ b (transl μ a f) := by
  rw [← transl_mul, ← transl_mul, mul_comm]

theorem transl_inv_transl (a : K) (f : L2 μ) : transl μ a (transl μ a⁻¹ f) = f := by
  rw [← transl_mul, inv_mul_cancel, transl_one]

theorem inner_transl (a : K) (f h : L2 μ) :
    ⟪transl μ a f, h⟫_ℂ = ⟪f, transl μ a⁻¹ h⟫_ℂ := by
  conv_lhs => rw [← transl_inv_transl μ a h]
  exact (transl μ a).inner_map_map f _

theorem inner_transl' (a : K) (f h : L2 μ) :
    ⟪f, transl μ a h⟫_ℂ = ⟪transl μ a⁻¹ f, h⟫_ℂ := by
  rw [← inner_conj_symm, inner_transl, inner_conj_symm]

/-- Left multiplication by `a` as a continuous map. -/
def mulLeftC (a : K) : C(K, K) := ⟨fun x => a * x, continuous_const.mul continuous_id⟩

theorem transl_toLp (a : K) (F : C(K, ℂ)) :
    transl μ a (ContinuousMap.toLp 2 μ ℂ F) = ContinuousMap.toLp 2 μ ℂ (F.comp (mulLeftC a)) := by
  apply Lp.ext
  have h1 := transl_apply_ae μ a (ContinuousMap.toLp 2 μ ℂ F)
  have h2 : (fun x => (ContinuousMap.toLp 2 μ ℂ F) (a * x)) =ᵐ[μ] fun x => F (a * x) :=
    (measurePreserving_mul_left μ a).quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp μ F)
  have h3 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (F.comp (mulLeftC a))
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  rfl

section Kernel

variable (φ : C(K, ℂ))

/-- The kernel function `y ↦ φ (x * y⁻¹)`. -/
noncomputable def kerFun (x : K) : C(K, ℂ) := φ.comp ⟨fun y => x * y⁻¹, continuous_const.mul continuous_inv⟩

theorem kerFun_apply (x y : K) : kerFun φ x y = φ (x * y⁻¹) := rfl

theorem continuous_kerFun : Continuous (kerFun φ) := by
  have : kerFun φ = ContinuousMap.curry (φ.comp ⟨fun p : K × K => p.1 * p.2⁻¹,
      continuous_fst.mul (continuous_inv.comp continuous_snd)⟩) := by
    ext x y; rfl
  rw [this]
  exact (ContinuousMap.curry _).continuous

/-- The kernel function as an element of `L²`. -/
noncomputable def kerL (x : K) : L2 μ := ContinuousMap.toLp 2 μ ℂ (kerFun φ x)

theorem continuous_kerL : Continuous (kerL μ φ) :=
  (ContinuousMap.toLp 2 μ ℂ).continuous.comp (continuous_kerFun φ)

theorem exists_bound_kerL : ∃ C, 0 ≤ C ∧ ∀ x, ‖kerL μ φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_kerL μ φ)).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ ⟨x, rfl⟩).trans (le_max_left _ _)⟩

/-- The integral operator with kernel `φ`, with values in continuous functions. -/
noncomputable def kernelOpC : L2 μ →L[ℂ] C(K, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun x => ⟪kerL μ φ x, f⟫_ℂ, (continuous_kerL μ φ).inner continuous_const⟩
      map_add' := fun f g => by ext x; simp [inner_add_right]
      map_smul' := fun c f => by ext x; simp [inner_smul_right] }
    (Classical.choose (exists_bound_kerL μ φ)) (by
      intro f
      obtain ⟨hC0, hC⟩ := Classical.choose_spec (exists_bound_kerL μ φ)
      refine (ContinuousMap.norm_le _ (mul_nonneg hC0 (norm_nonneg f))).2 fun x => ?_
      calc ‖⟪kerL μ φ x, f⟫_ℂ‖ ≤ ‖kerL μ φ x‖ * ‖f‖ := norm_inner_le_norm _ _
        _ ≤ _ := by gcongr; exact hC x)

theorem kernelOpC_apply (f : L2 μ) (x : K) : kernelOpC μ φ f x = ⟪kerL μ φ x, f⟫_ℂ := rfl

theorem isCompactOperator_kernelOpC : IsCompactOperator (kernelOpC μ φ) := by
  apply (isCompactOperator_iff_isCompact_closure_image_ball
    (kernelOpC μ φ : L2 μ →ₗ[ℂ] C(K, ℂ)) one_pos).2
  obtain ⟨C, hC0, hC⟩ := exists_bound_kerL μ φ
  set A := (kernelOpC μ φ : L2 μ →ₗ[ℂ] C(K, ℂ)) '' Metric.ball 0 1
  let e := ContinuousMap.isometryEquivBoundedOfCompact K ℂ
  suffices hK : IsCompact (closure (e '' A)) by
    refine (hK.image e.symm.continuous).of_isClosed_subset isClosed_closure ?_
    intro F hF
    exact ⟨e F, image_closure_subset_closure_image e.continuous ⟨F, hF, rfl⟩, e.symm_apply_apply F⟩
  refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 C) (isCompact_closedBall 0 C)
    _ ?_ ?_
  · rintro _ x ⟨F, ⟨f, hf, rfl⟩, rfl⟩
    rw [mem_closedBall_zero_iff]
    change ‖⟪kerL μ φ x, f⟫_ℂ‖ ≤ C
    calc ‖⟪kerL μ φ x, f⟫_ℂ‖ ≤ ‖kerL μ φ x‖ * ‖f‖ := norm_inner_le_norm _ _
      _ ≤ C * 1 := by
        gcongr
        · exact hC x
        · exact (mem_ball_zero_iff.1 hf).le
      _ = C := mul_one C
  · intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 ((continuous_kerL μ φ).continuousAt (x := x₀)) ε hε]
      with x hx
    rintro ⟨_, F, ⟨f, hf, rfl⟩, rfl⟩
    change dist (⟪kerL μ φ x₀, f⟫_ℂ) (⟪kerL μ φ x, f⟫_ℂ) < ε
    rw [dist_eq_norm, ← inner_sub_left]
    calc ‖⟪kerL μ φ x₀ - kerL μ φ x, f⟫_ℂ‖ ≤ ‖kerL μ φ x₀ - kerL μ φ x‖ * ‖f‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖kerL μ φ x₀ - kerL μ φ x‖ * 1 := by gcongr; exact (mem_ball_zero_iff.1 hf).le
      _ < ε := by rw [mul_one, ← dist_eq_norm, dist_comm]; exact hx

theorem kerFun_comp_mulLeft (a x : K) :
    (kerFun φ x).comp (mulLeftC a⁻¹) = kerFun φ (a * x) := by
  ext y
  simp only [ContinuousMap.comp_apply, kerFun_apply, mulLeftC, ContinuousMap.coe_mk]
  congr 1
  rw [mul_inv_rev, inv_inv, mul_comm y⁻¹ a, ← mul_assoc, mul_comm x a]

theorem kernelOpC_transl (a : K) (f : L2 μ) :
    kernelOpC μ φ (transl μ a f) = (kernelOpC μ φ f).comp (mulLeftC a) := by
  ext x
  rw [kernelOpC_apply, inner_transl', kerL, transl_toLp, kerFun_comp_mulLeft]
  rfl

/-- The integral operator with kernel `φ` on `L²`. -/
noncomputable def kernelOp : L2 μ →L[ℂ] L2 μ := (ContinuousMap.toLp 2 μ ℂ).comp (kernelOpC μ φ)

theorem isCompactOperator_kernelOp : IsCompactOperator (kernelOp μ φ) :=
  (isCompactOperator_kernelOpC μ φ).clm_comp (ContinuousMap.toLp 2 μ ℂ)

theorem kernelOp_transl (a : K) (f : L2 μ) :
    kernelOp μ φ (transl μ a f) = transl μ a (kernelOp μ φ f) := by
  simp only [kernelOp, ContinuousLinearMap.comp_apply, kernelOpC_transl, transl_toLp]

/-- Translation as a continuous linear map. -/
noncomputable def translC (a : K) : L2 μ →L[ℂ] L2 μ := (transl μ a).toContinuousLinearMap

theorem translC_apply (a : K) (f : L2 μ) : translC μ a f = transl μ a f := rfl

theorem adjoint_translC (a : K) : ContinuousLinearMap.adjoint (translC μ a) = translC μ a⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [translC_apply, translC_apply, inner_transl']

theorem adjoint_kernelOp_transl (a : K) (f : L2 μ) :
    ContinuousLinearMap.adjoint (kernelOp μ φ) (transl μ a f) =
      transl μ a (ContinuousLinearMap.adjoint (kernelOp μ φ) f) := by
  have hc : kernelOp μ φ ∘L translC μ a⁻¹ = translC μ a⁻¹ ∘L kernelOp μ φ := by
    ext1 f; exact kernelOp_transl μ φ a⁻¹ f
  have := congrArg ContinuousLinearMap.adjoint hc
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_translC,
    inv_inv] at this
  exact (congrArg (fun L : L2 μ →L[ℂ] L2 μ => L f) this).symm

end Kernel

section Main

/-- The functions invariant under translation by `g`. -/
def invariants (g : K) : Submodule ℂ (L2 μ) where
  carrier := {f | transl μ g f = f}
  add_mem' := by intro f h hf hh; simp only [Set.mem_ofPred_eq, map_add] at *; rw [hf, hh]
  zero_mem' := by simp
  smul_mem' := by intro c f hf; simp only [Set.mem_ofPred_eq, map_smul] at *; rw [hf]

theorem mem_invariants {g : K} {f : L2 μ} : f ∈ invariants μ g ↔ transl μ g f = f := Iff.rfl

theorem transl_sub_mem_orthogonal (g : K) (x : L2 μ) :
    transl μ g x - x ∈ (invariants μ g)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [inner_sub_right, inner_transl']
  have : transl μ g⁻¹ u = u := by
    conv_lhs => rw [← (mem_invariants μ).1 hu]
    rw [← transl_mul, mul_inv_cancel, transl_one]
  rw [this, sub_self]

theorem transl_mem_orthogonal (g a : K) {x : L2 μ} (hx : x ∈ (invariants μ g)ᗮ) :
    transl μ a x ∈ (invariants μ g)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [inner_transl']
  refine Submodule.inner_right_of_mem_orthogonal ?_ hx
  rw [mem_invariants, transl_comm, (mem_invariants μ).1 hu]

end Main

end PeterWeyl

end UndergradKB.Topology
