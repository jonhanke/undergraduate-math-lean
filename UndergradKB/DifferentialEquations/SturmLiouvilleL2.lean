import UndergradKB.DifferentialEquations.SturmLiouvilleGreen
import UndergradKB.DifferentialEquations.KernelOperator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The Green operator of a regular Sturm-Liouville problem on `L²(r dx)`

For a regular Sturm-Liouville problem (`RegularSL`), `λ = -1` is not an eigenvalue (eigenvalues are `≥ 0`, Theorem
5.1.1, "moreover" part, proved in wave 2), so the Green's function `G = S.green (-1)` exists
(`SturmLiouvilleGreen.lean`).  On the Hilbert space `L²([a, b], r(x) dx)` the Green operator
`(T f)(x) = ∫_a^b G(x, t) f(t) r(t) dt` is compact and symmetric (`KernelOperator.lean`).  Here:

* an eigenfunction `y` of the problem with eigenvalue `λ` gives an eigenvector of `T` with eigenvalue
  `-1/(1 + λ)` (`hasEigenvalue_greenOp`);
* conversely an eigenvector of `T` with eigenvalue `μ ≠ 0` gives an eigenfunction with eigenvalue `-1 - μ⁻¹`
  (`isEigenvalue_of_hasEigenvalue`);
* the class of every `C²` function satisfying the boundary conditions lies in the range of `T`
  (`mem_range_greenOp`).

These are the inputs of the spectral theorem for the problem (`SturmLiouvilleSpectrum.lean`). -/

namespace UndergradKB.DifferentialEquations

open MeasureTheory Set Filter KernelOp
open scoped RealInnerProductSpace NNReal ENNReal

namespace RegularSL

variable (S : RegularSL)

/-- The weight `r`, extended by clamping (continuous on `ℝ`). -/
noncomputable def rr (t : ℝ) : ℝ := S.r (S.clampI t)

lemma continuous_rr : Continuous S.rr :=
  S.r_cont.comp_continuous S.continuous_clampI S.clampI_mem

lemma rr_of_mem {t : ℝ} (ht : t ∈ Icc S.a S.b) : S.rr t = S.r t := by
  simp [rr, S.clampI_of_mem ht]

/-- The weighted measure `r(x) dx` on `[a, b]`. -/
noncomputable def wμ : Measure ℝ :=
  (volume.restrict (Icc S.a S.b)).withDensity fun t => ((S.rr t).toNNReal : ℝ≥0∞)

instance : IsFiniteMeasure S.wμ := by
  have hi : Integrable S.rr (volume.restrict (Icc S.a S.b)) :=
    S.continuous_rr.continuousOn.integrableOn_Icc
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

lemma ae_mem : ∀ᵐ t ∂S.wμ, t ∈ Icc S.a S.b :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

/-- Integrals against `r(x) dx`. -/
lemma integral_wμ (F : ℝ → ℝ) : ∫ t, F t ∂S.wμ = ∫ t in S.a..S.b, S.r t * F t := by
  have hm : Measurable fun t => (S.rr t).toNNReal :=
    (continuous_real_toNNReal.comp S.continuous_rr).measurable
  rw [wμ, integral_withDensity_eq_integral_smul hm, intervalIntegral.integral_of_le S.hab.le,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (S.r_pos t ht).le, S.rr_of_mem ht]

/-- A continuous function is in `L²(r dx)`. -/
lemma memLp_of_continuous {y : ℝ → ℝ} (hy : Continuous y) : MemLp y 2 S.wμ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := y) (s := Icc S.a S.b) hy.continuousOn
  refine MemLp.of_bound hy.aestronglyMeasurable C ?_
  filter_upwards [S.ae_mem] with t ht
  exact hC t ht

/-- The class of a continuous function in `L²(r dx)`. -/
noncomputable def toL2 (y : ℝ → ℝ) (hy : Continuous y) : Lp ℝ 2 S.wμ :=
  (S.memLp_of_continuous hy).toLp y

lemma toL2_ae {y : ℝ → ℝ} (hy : Continuous y) : S.toL2 y hy =ᵐ[S.wμ] y := MemLp.coeFn_toLp _

lemma inner_toL2 {y z : ℝ → ℝ} (hy : Continuous y) (hz : Continuous z) :
    ⟪S.toL2 y hy, S.toL2 z hz⟫ = ∫ t in S.a..S.b, S.r t * (y t * z t) := by
  rw [MeasureTheory.L2.inner_def, ← S.integral_wμ]
  refine integral_congr_ae ?_
  filter_upwards [S.toL2_ae hy, S.toL2_ae hz] with t h1 h2
  rw [h1, h2]
  simp [mul_comm]

lemma toL2_ne_zero {y : ℝ → ℝ} (hy : Continuous y) {t₀ : ℝ} (ht : t₀ ∈ Icc S.a S.b) (h : y t₀ ≠ 0) :
    S.toL2 y hy ≠ 0 := by
  intro h0
  have h1 := S.inner_toL2 hy hy
  rw [h0, inner_zero_left] at h1
  have h2 := S.integral_r_sq_pos hy ht h
  have e : (fun t => S.r t * y t ^ 2) = fun t => S.r t * (y t * y t) := by funext t; ring
  rw [e, ← h1] at h2
  exact lt_irrefl _ h2

/-! ### The Green operator at `λ = -1` -/

lemma not_isEigenvalue_neg_one : ¬ S.IsEigenvalue (-1) := by
  rintro ⟨y, hy⟩
  have := S.eigenvalue_nonneg hy
  norm_num at this

lemma green_clamp (l x t : ℝ) : S.green l (S.clampI x) (S.clampI t) = S.green l x t := by
  simp only [green, S.clampI_of_mem (S.clampI_mem x), S.clampI_of_mem (S.clampI_mem t)]

lemma green_bdd (l : ℝ) : ∃ M, ∀ x t, |S.green l x t| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (S.continuous_green l).continuousOn (s := Icc S.a S.b ×ˢ Icc S.a S.b)
  refine ⟨C, fun x t => ?_⟩
  rw [← S.green_clamp]
  exact hC (S.clampI x, S.clampI t) ⟨S.clampI_mem x, S.clampI_mem t⟩

/-- The Green's function at `λ = -1` as a bounded continuous kernel. -/
noncomputable def gK : KernelOp.Kernel where
  K := S.green (-1)
  M := Classical.choose (S.green_bdd (-1))
  cont := S.continuous_green (-1)
  bound := Classical.choose_spec (S.green_bdd (-1))

/-- **The Green operator** `(T f)(x) = ∫_a^b G(x, t) f(t) r(t) dt` on `L²(r dx)`, for `λ = -1`. -/
noncomputable def greenOp : Lp ℝ 2 S.wμ →L[ℝ] Lp ℝ 2 S.wμ := S.gK.op S.wμ S.ae_mem

theorem isCompactOperator_greenOp : IsCompactOperator S.greenOp :=
  S.gK.isCompactOperator_op S.hab S.ae_mem

theorem isSymmetric_greenOp : (S.greenOp : Lp ℝ 2 S.wμ →ₗ[ℝ] Lp ℝ 2 S.wμ).IsSymmetric :=
  S.gK.isSymmetric_op S.ae_mem fun x t => S.green_symm (-1) x t

lemma greenOp_toL2_ae {y : ℝ → ℝ} (hy : Continuous y) :
    S.greenOp (S.toL2 y hy) =ᵐ[S.wμ] fun x => ∫ t in S.a..S.b, S.r t * (S.green (-1) x t * y t) := by
  filter_upwards [S.gK.op_apply_ae S.ae_mem (S.toL2 y hy)] with x hx
  rw [greenOp, hx]
  have : ∫ t, S.gK.K x t * (S.toL2 y hy) t ∂S.wμ = ∫ t, S.green (-1) x t * y t ∂S.wμ := by
    refine integral_congr_ae ?_
    filter_upwards [S.toL2_ae hy] with t ht
    rw [ht]; rfl
  rw [this, S.integral_wμ]

/-! ### Eigenfunctions of the problem and eigenvectors of the Green operator -/

/-- An eigenfunction `y` with eigenvalue `λ` satisfies `T y = -1/(1 + λ) y` in `L²(r dx)`. -/
theorem greenOp_eigenfunction {l : ℝ} {y : ℝ → ℝ} (h : S.IsEigenfunction l y) :
    S.greenOp (S.toL2 y h.1.1.continuous) = (-1 / (1 + l)) • S.toL2 y h.1.1.continuous := by
  have hl0 := S.eigenvalue_nonneg h
  have h1l : 1 + l ≠ 0 := by linarith
  have hyc : Continuous y := h.1.1.continuous
  set f : ℝ → ℝ := fun t => -(1 + l) * S.r t * y t with hf
  have hfc : ContinuousOn f (Icc S.a S.b) :=
    (continuousOn_const.mul S.r_cont).mul hyc.continuousOn
  obtain ⟨z, hz, hzG⟩ := S.green_solution S.not_isEigenvalue_neg_one hfc
  have hy : S.IsSolution (-1) f y := by
    obtain ⟨hC, hE, hA, hB⟩ := h.1
    refine ⟨hC, fun t ht => ?_, hA, hB⟩
    have := hE t ht
    simp only [hf, Pi.zero_apply] at this ⊢
    linear_combination this
  have hyz := S.solution_unique_of_not_eigenvalue S.not_isEigenvalue_neg_one hy hz
  apply Lp.ext
  filter_upwards [S.greenOp_toL2_ae hyc, Lp.coeFn_smul (-1 / (1 + l)) (S.toL2 y hyc), S.toL2_ae hyc,
    S.ae_mem] with x h1 h2 h3 hx
  rw [h1, h2, Pi.smul_apply, h3, hyz x hx, hzG x hx, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hf]
  field_simp

/-- An eigenvalue `λ` of the problem gives the eigenvalue `-1/(1 + λ)` of the Green operator. -/
theorem hasEigenvalue_greenOp {l : ℝ} (h : S.IsEigenvalue l) :
    Module.End.HasEigenvalue (S.greenOp : Module.End ℝ (Lp ℝ 2 S.wμ)) (-1 / (1 + l)) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨t₀, ht₀, hne⟩ := hy.2
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := S.toL2 y hy.1.1.continuous) ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe]
    exact S.greenOp_eigenfunction hy
  · exact S.toL2_ne_zero hy.1.1.continuous ht₀ hne

/-- An eigenvector `F` of the Green operator with eigenvalue `μ ≠ 0` is (the class of) `μ⁻¹ z` for an
eigenfunction `z` of the problem with eigenvalue `-1 - μ⁻¹`. -/
theorem exists_eigenfunction_of_eigvec {μ : ℝ} (hμ : μ ≠ 0) {F : Lp ℝ 2 S.wμ}
    (hTF : S.greenOp F = μ • F) (hF0 : F ≠ 0) :
    ∃ z, S.IsEigenfunction (-1 - μ⁻¹) z ∧ ∀ᵐ x ∂S.wμ, F x = μ⁻¹ * z x := by
  set y₀ : ℝ → ℝ := fun x => ⟪S.gK.sec S.wμ x, F⟫ with hy0
  have hy0c : Continuous y₀ := (S.gK.continuous_sec S.ae_mem).inner continuous_const
  have hFae : ∀ᵐ x ∂S.wμ, F x = μ⁻¹ * y₀ x := by
    filter_upwards [S.gK.op_apply_ae' S.ae_mem F, Lp.coeFn_smul μ F] with x h1 h2
    have e : y₀ x = μ * F x := by
      rw [hy0]
      simp only
      rw [← h1]
      change (S.greenOp F) x = _
      rw [hTF, h2, Pi.smul_apply, smul_eq_mul]
    rw [e]
    field_simp
  have hy0int : ∀ x, y₀ x = ∫ t in S.a..S.b, S.green (-1) x t * (μ⁻¹ * S.r t * y₀ t) := by
    intro x
    have e1 : y₀ x = ∫ t, S.gK.K x t * F t ∂S.wμ := S.gK.inner_sec x F
    have e2 : ∫ t, S.gK.K x t * F t ∂S.wμ = ∫ t, S.green (-1) x t * (μ⁻¹ * y₀ t) ∂S.wμ := by
      refine integral_congr_ae ?_
      filter_upwards [hFae] with t ht
      rw [ht]; rfl
    rw [e1, e2, S.integral_wμ]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  set hh : ℝ → ℝ := fun t => μ⁻¹ * S.r t * y₀ t with hhdef
  have hhc : ContinuousOn hh (Icc S.a S.b) :=
    (continuousOn_const.mul S.r_cont).mul hy0c.continuousOn
  obtain ⟨z, hz, hzG⟩ := S.green_solution S.not_isEigenvalue_neg_one hhc
  have hzy : ∀ x ∈ Icc S.a S.b, z x = y₀ x := fun x hx => by rw [hzG x hx, hy0int x]
  refine ⟨z, ⟨⟨hz.1, fun t ht => ?_, hz.2.2.1, hz.2.2.2⟩, ?_⟩, ?_⟩
  · have e := hz.2.1 t ht
    simp only [hhdef, ← hzy t ht] at e
    simp only [Pi.zero_apply]
    linear_combination e
  · by_contra hall
    push Not at hall
    apply hF0
    apply Lp.ext
    filter_upwards [hFae, S.ae_mem, Lp.coeFn_zero ℝ 2 S.wμ] with x h1 hx h0
    rw [h1, h0, ← hzy x hx, hall x hx]
    simp
  · filter_upwards [hFae, S.ae_mem] with x h1 hx
    rw [h1, hzy x hx]

/-- An eigenvalue `μ ≠ 0` of the Green operator gives the eigenvalue `-1 - μ⁻¹` of the problem. -/
theorem isEigenvalue_of_hasEigenvalue {μ : ℝ} (hμ : μ ≠ 0)
    (h : Module.End.HasEigenvalue (S.greenOp : Module.End ℝ (Lp ℝ 2 S.wμ)) μ) :
    S.IsEigenvalue (-1 - μ⁻¹) := by
  obtain ⟨F, hF1, hF0⟩ := h.exists_hasEigenvector
  have hTF : S.greenOp F = μ • F := by
    rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hF1
    exact hF1
  obtain ⟨z, hz, -⟩ := S.exists_eigenfunction_of_eigvec hμ hTF hF0
  exact ⟨z, hz⟩

/-! ### The range of the Green operator -/

lemma continuousOn_lhs {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y) :
    ContinuousOn (fun t => deriv (fun s => S.p s * deriv y s) t - S.q t * y t + (-1) * S.r t * y t)
      (Icc S.a S.b) := by
  have hd : (fun t => deriv (fun s => S.p s * deriv y s) t)
      = fun t => deriv S.p t * deriv y t + S.p t * deriv (deriv y) t :=
    funext fun t => (S.hasDerivAt_pd hy t).deriv
  have c1 : Continuous (deriv S.p) := S.p_C1.continuous_deriv le_rfl
  have c2 : Continuous (deriv y) := (cd2 hy).2.continuous
  have c3 : Continuous (deriv (deriv y)) := (cd2 hy).2.continuous_deriv le_rfl
  have c4 : Continuous S.p := S.p_C1.continuous
  have hc : Continuous fun t => deriv (fun s => S.p s * deriv y s) t := by
    rw [hd]; fun_prop
  exact (hc.continuousOn.sub (S.q_cont.mul hy.continuous.continuousOn)).add
    ((continuousOn_const.mul S.r_cont).mul hy.continuous.continuousOn)

/-- **Every `C²` function with the boundary conditions is in the range of the Green operator.** -/
theorem toL2_mem_range {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y)
    (hA : S.α₁ * y S.a - S.α₂ * deriv y S.a = 0) (hB : S.β₁ * y S.b + S.β₂ * deriv y S.b = 0) :
    S.toL2 y hy.continuous ∈ LinearMap.range (S.greenOp : Lp ℝ 2 S.wμ →ₗ[ℝ] Lp ℝ 2 S.wμ) := by
  set E : ℝ → ℝ :=
    fun t => deriv (fun s => S.p s * deriv y s) t - S.q t * y t + (-1) * S.r t * y t with hE
  have hEc : ContinuousOn E (Icc S.a S.b) := S.continuousOn_lhs hy
  have hrr : ∀ t, S.rr t ≠ 0 := fun t => (S.r_pos _ (S.clampI_mem t)).ne'
  set φ : ℝ → ℝ := fun t => E (S.clampI t) / S.rr t with hφ
  have hφc : Continuous φ :=
    (hEc.comp_continuous S.continuous_clampI S.clampI_mem).div S.continuous_rr hrr
  obtain ⟨z, hz, hzG⟩ := S.green_solution S.not_isEigenvalue_neg_one hEc
  have hyS : S.IsSolution (-1) E y := ⟨hy, fun t _ => rfl, hA, hB⟩
  have hyz := S.solution_unique_of_not_eigenvalue S.not_isEigenvalue_neg_one hyS hz
  refine ⟨S.toL2 φ hφc, ?_⟩
  apply Lp.ext
  filter_upwards [S.greenOp_toL2_ae hφc, S.toL2_ae hy.continuous, S.ae_mem] with x h1 h2 hx
  rw [ContinuousLinearMap.coe_coe, h1, h2, hyz x hx, hzG x hx]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le S.hab.le] at ht
  have hr := (S.r_pos t ht).ne'
  simp only [hφ, S.clampI_of_mem ht, S.rr_of_mem ht]
  field_simp

end RegularSL

end UndergradKB.DifferentialEquations
