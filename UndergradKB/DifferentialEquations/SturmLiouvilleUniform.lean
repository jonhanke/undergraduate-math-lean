import UndergradKB.DifferentialEquations.SturmLiouvilleExpansion

/-! # Uniform convergence of eigenfunction series for `C²` functions with the boundary conditions

Lebl, Theorem 5.1.4 states that the eigenfunction series of a regular Sturm-Liouville problem converges to `f`
"as for Fourier series".  Here: for `f` of class `C²` satisfying the two boundary conditions, the series
`∑ cₙ yₙ` (`cₙ = ⟨f, yₙ⟩`, `yₙ` orthonormal) converges to `f` **uniformly on `[a, b]`**
(`eigenfunction_expansion_uniform`).

Proof: `f = T φ` pointwise on `[a, b]` with `T` the Green operator and `φ` continuous (`toL2_mem_range`), i.e.
`f(x) = ⟪kₓ, φ⟫` with `kₓ = G(x, ·)` in `L²(r dx)`; an eigenfunction satisfies `yₙ(x) = μₙ⁻¹ ⟪kₓ, yₙ⟫` with
`μₙ = -1/(1 + λₙ)`, and `cₙ = ⟨T φ, yₙ⟩ = μₙ ⟨φ, yₙ⟩`.  So `cₙ yₙ(x) = ⟨φ, yₙ⟩ ⟪kₓ, yₙ⟫` and
`f(x) - ∑_{n<N} cₙ yₙ(x) = ⟪kₓ, φ - ∑_{n<N} ⟨φ, yₙ⟩ yₙ⟫`, bounded by `‖kₓ‖ ‖φ - ∑_{n<N} ⟨φ, yₙ⟩ yₙ‖`, where `‖kₓ‖`
is bounded uniformly in `x` and the second factor tends to `0` (the `L²` expansion of `φ`). -/

namespace UndergradKB.DifferentialEquations

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace RegularSL

variable (S : RegularSL)

lemma inner_sec_toL2 {y : ℝ → ℝ} (hy : Continuous y) (x : ℝ) :
    ⟪S.gK.sec S.wμ x, S.toL2 y hy⟫ = ∫ t in S.a..S.b, S.r t * (S.green (-1) x t * y t) := by
  rw [S.gK.inner_sec, ← S.integral_wμ]
  refine integral_congr_ae ?_
  filter_upwards [S.toL2_ae hy] with t ht
  rw [ht]; rfl

/-- Pointwise form of `greenOp_eigenfunction`: `y(x) = -(1 + λ) ⟪kₓ, y⟫` on `[a, b]`. -/
lemma eigenfunction_pointwise {l : ℝ} {y : ℝ → ℝ} (h : S.IsEigenfunction l y) :
    ∀ x ∈ Icc S.a S.b, y x = -(1 + l) * ⟪S.gK.sec S.wμ x, S.toL2 y h.1.1.continuous⟫ := by
  intro x hx
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
  rw [S.solution_unique_of_not_eigenvalue S.not_isEigenvalue_neg_one hy hz x hx, hzG x hx,
    S.inner_sec_toL2, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hf]
  ring

/-- Pointwise form of `toL2_mem_range`: a `C²` function with the boundary conditions is `T φ` on `[a, b]`. -/
lemma exists_greenOp_pointwise {y : ℝ → ℝ} (hy : ContDiff ℝ 2 y)
    (hA : S.α₁ * y S.a - S.α₂ * deriv y S.a = 0) (hB : S.β₁ * y S.b + S.β₂ * deriv y S.b = 0) :
    ∃ φ : ℝ → ℝ, ∃ hφ : Continuous φ, S.greenOp (S.toL2 φ hφ) = S.toL2 y hy.continuous ∧
      ∀ x ∈ Icc S.a S.b, y x = ⟪S.gK.sec S.wμ x, S.toL2 φ hφ⟫ := by
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
  have hpt : ∀ x ∈ Icc S.a S.b, y x = ⟪S.gK.sec S.wμ x, S.toL2 φ hφc⟫ := by
    intro x hx
    rw [S.inner_sec_toL2, hyz x hx, hzG x hx]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le S.hab.le] at ht
    have hr := (S.r_pos t ht).ne'
    simp only [hφ, S.clampI_of_mem ht, S.rr_of_mem ht]
    field_simp
  refine ⟨φ, hφc, ?_, hpt⟩
  apply Lp.ext
  filter_upwards [S.gK.op_apply_ae' S.ae_mem (S.toL2 φ hφc), S.toL2_ae hy.continuous, S.ae_mem]
    with x h1 h2 hx
  rw [greenOp, h1, h2, hpt x hx]

/-- **Eigenfunction expansion (Lebl, Theorem 5.1.4): uniform convergence for `C²` functions with the boundary
conditions, mean-square convergence for continuous functions.**  For a regular Sturm-Liouville problem there are
eigenvalues `λ₀ < λ₁ < ⋯` (all of them) with eigenfunctions `yₙ` orthonormal for the weight `r`, such that, with
`cₙ = ⟨f, yₙ⟩ = ∫_a^b f yₙ r`:
* if `f` is `C²` and satisfies both boundary conditions, `∑ cₙ yₙ` converges to `f` uniformly on `[a, b]`;
* if `f` is continuous on `[a, b]`, `∫_a^b r (f - ∑_{n<N} cₙ yₙ)² → 0`. -/
@[kb "lebldiffyqs2026" "Theorem 5.1.4, p. 279"]
theorem eigenfunction_expansion_uniform :
    ∃ ev : ℕ → ℝ, ∃ y : ℕ → ℝ → ℝ, StrictMono ev ∧ (∀ l, S.IsEigenvalue l ↔ ∃ n, ev n = l) ∧
      (∀ n, S.IsEigenfunction (ev n) (y n)) ∧
      (∀ m n, S.wInner (y m) (y n) = if m = n then 1 else 0) ∧
      (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → S.α₁ * f S.a - S.α₂ * deriv f S.a = 0 →
        S.β₁ * f S.b + S.β₂ * deriv f S.b = 0 →
        TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, S.wInner f (y n) * y n x) f atTop
          (Icc S.a S.b)) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc S.a S.b) →
        Tendsto (fun N => ∫ t in S.a..S.b,
          S.r t * (f t - ∑ n ∈ Finset.range N, S.wInner f (y n) * y n t) ^ 2) atTop (𝓝 0) := by
  obtain ⟨ev, y, hy, hmono, hiff, hon, hsum⟩ := S.eigenfunction_expansion_L2
  refine ⟨ev, y, hmono, hiff, hy, hon, fun f hf hA hB => ?_, fun f hf => S.mean_square_of_hasSum hy hsum hf⟩
  set e : ℕ → Lp ℝ 2 S.wμ := fun n => S.toL2 (y n) (hy n).1.1.continuous with he
  obtain ⟨φ, hφ, hTφ, hpt⟩ := S.exists_greenOp_pointwise hf hA hB
  set Φ := S.toL2 φ hφ
  have hl : ∀ n, 1 + ev n ≠ 0 := fun n => by
    have := S.eigenvalue_nonneg (hy n); linarith
  -- the coefficients
  have hcoef : ∀ n, S.wInner f (y n) = (-1 / (1 + ev n)) * ⟪Φ, e n⟫ := by
    intro n
    have h1 : S.wInner f (y n) = ⟪S.toL2 f hf.continuous, e n⟫ := (S.inner_toL2_eq_wInner _ _).symm
    have hsym := S.isSymmetric_greenOp Φ (e n)
    simp only [ContinuousLinearMap.coe_coe] at hsym
    rw [h1, ← hTφ, hsym, he]
    simp only
    rw [S.greenOp_eigenfunction (hy n), real_inner_smul_right]
  -- each term of the series at `x`
  have hterm : ∀ x ∈ Icc S.a S.b, ∀ n,
      S.wInner f (y n) * y n x = ⟪S.gK.sec S.wμ x, ⟪e n, Φ⟫ • e n⟫ := by
    intro x hx n
    rw [hcoef n, S.eigenfunction_pointwise (hy n) x hx, real_inner_smul_right, real_inner_comm (e n) Φ]
    have := hl n
    field_simp
    rfl
  -- the uniform bound
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set C := KernelOp.cν S.wμ * S.gK.M with hC
  have hC0 : 0 ≤ C := mul_nonneg KernelOp.cν_nonneg S.gK.M_nonneg
  have hT := (hsum Φ).tendsto_sum_nat
  rw [tendsto_iff_norm_sub_tendsto_zero] at hT
  have hev := (Metric.tendsto_nhds.1 hT) (ε / (C + 1)) (by positivity)
  filter_upwards [hev] with N hN x hx
  have hN' : ‖∑ n ∈ Finset.range N, ⟪e n, Φ⟫ • e n - Φ‖ < ε / (C + 1) := by
    simpa [dist_zero_right] using hN
  rw [Real.dist_eq]
  have hsumx : ∑ n ∈ Finset.range N, S.wInner f (y n) * y n x
      = ⟪S.gK.sec S.wμ x, ∑ n ∈ Finset.range N, ⟪e n, Φ⟫ • e n⟫ := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun n _ => hterm x hx n
  rw [hsumx, hpt x hx, ← inner_sub_right]
  calc |⟪S.gK.sec S.wμ x, Φ - ∑ n ∈ Finset.range N, ⟪e n, Φ⟫ • e n⟫|
      ≤ ‖S.gK.sec S.wμ x‖ * ‖Φ - ∑ n ∈ Finset.range N, ⟪e n, Φ⟫ • e n‖ := abs_real_inner_le_norm _ _
    _ ≤ C * (ε / (C + 1)) := by
        refine mul_le_mul (S.gK.norm_sec_le x) ?_ (norm_nonneg _) hC0
        rw [norm_sub_rev]; exact hN'.le
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

end RegularSL

end UndergradKB.DifferentialEquations
