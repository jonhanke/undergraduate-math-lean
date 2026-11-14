import UndergradKB.DifferentialEquations.SturmLiouvilleSpectrum
import UndergradKB.DifferentialEquations.SturmLiouvilleKernel
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Eigenfunction expansions for regular Sturm-Liouville problems (Lebl Theorem 5.1.4, in mean square)

Lebl, Theorem 5.1.4: the eigenfunctions `yₙ` of a regular Sturm-Liouville problem are orthogonal for the weight `r`,
and a function `f` on `[a, b]` has the expansion `f = ∑ cₙ yₙ` with `cₙ = ⟨f, yₙ⟩ / ⟨yₙ, yₙ⟩`; the book states
pointwise convergence for piecewise smooth continuous `f` ("as for Fourier series").

Here: the normalized eigenfunctions form a Hilbert basis of `L²([a, b], r dx)` (`eigenfunction_expansion_L2`), so
for every `f` continuous on `[a, b]` the partial sums converge to `f` in mean square:
`∫_a^b r (f - ∑_{n<N} cₙ yₙ)² → 0` (`eigenfunction_expansion_mean_square`).  Proof: an `L²` function orthogonal to
every eigenfunction is orthogonal to every eigenspace of the compact symmetric Green operator `T` (the eigenspaces
for `μ ≠ 0` are spanned by eigenfunctions, `exists_eigenfunction_of_eigvec` and `eigenfunction_unique`; the kernel
of `T` is zero, `greenOp_eq_zero_iff`), hence zero by the spectral theorem.  Pointwise convergence is not
formalized. -/

namespace UndergradKB.DifferentialEquations

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace RegularSL

variable (S : RegularSL)

/-- A nonzero multiple of an eigenfunction is an eigenfunction. -/
lemma isEigenfunction_const_mul {l c : ℝ} {y : ℝ → ℝ} (h : S.IsEigenfunction l y) (hc : c ≠ 0) :
    S.IsEigenfunction l (fun t => c * y t) := by
  obtain ⟨⟨hC, hE, hA, hB⟩, t₀, ht₀, hne⟩ := h
  have hd : Differentiable ℝ y := hC.differentiable (by norm_num)
  have hD : deriv (fun t => c * y t) = fun t => c * deriv y t :=
    funext fun t => deriv_const_mul c (hd t)
  have hD2 : ∀ t, deriv (fun t => S.p t * deriv (fun t => c * y t) t) t
      = c * deriv (fun t => S.p t * deriv y t) t := by
    intro t
    rw [hD]
    have : (fun t => S.p t * (c * deriv y t)) = fun t => c * (S.p t * deriv y t) := by
      funext t; ring
    rw [this, deriv_const_mul]
    exact (S.hasDerivAt_pd hC t).differentiableAt
  refine ⟨⟨contDiff_const.mul hC, fun t ht => ?_, ?_, ?_⟩, t₀, ht₀, mul_ne_zero hc hne⟩
  · rw [hD2]
    have := hE t ht
    simp only [Pi.zero_apply] at this ⊢
    linear_combination c * this
  · rw [hD]; linear_combination c * hA
  · rw [hD]; linear_combination c * hB

lemma wInner_self_pos {l : ℝ} {y : ℝ → ℝ} (h : S.IsEigenfunction l y) : 0 < S.wInner y y := by
  obtain ⟨t₀, ht₀, hne⟩ := h.2
  have := S.integral_r_sq_pos h.1.1.continuous ht₀ hne
  unfold wInner
  convert this using 1
  exact intervalIntegral.integral_congr fun t _ => by ring

/-- Every eigenvalue has an eigenfunction with `⟨y, y⟩ = 1`. -/
lemma exists_normalized_eigenfunction {l : ℝ} (h : S.IsEigenvalue l) :
    ∃ y, S.IsEigenfunction l y ∧ S.wInner y y = 1 := by
  obtain ⟨y, hy⟩ := h
  have hpos := S.wInner_self_pos hy
  set c := (Real.sqrt (S.wInner y y))⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hpos).ne'
  refine ⟨fun t => c * y t, S.isEigenfunction_const_mul hy hc0, ?_⟩
  have e : S.wInner (fun t => c * y t) (fun t => c * y t) = c ^ 2 * S.wInner y y := by
    unfold wInner
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [e, hc, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- **Orthonormal eigenfunctions.**  The eigenvalues `λ₀ < λ₁ < ⋯ → ∞` with eigenfunctions `yₙ` normalized
by `⟨yₙ, yₙ⟩ = 1`; they are orthonormal for the weight `r`. -/
theorem exists_orthonormal_eigenfunctions :
    ∃ ev : ℕ → ℝ, ∃ y : ℕ → ℝ → ℝ, StrictMono ev ∧ Tendsto ev atTop atTop ∧
      (∀ l, S.IsEigenvalue l ↔ ∃ n, ev n = l) ∧ (∀ n, S.IsEigenfunction (ev n) (y n)) ∧
      ∀ m n, S.wInner (y m) (y n) = if m = n then 1 else 0 := by
  obtain ⟨ev, hmono, htend, hiff, -, -⟩ := S.sturm_liouville_eigenvalues
  have hex : ∀ n, ∃ y, S.IsEigenfunction (ev n) y ∧ S.wInner y y = 1 := fun n =>
    S.exists_normalized_eigenfunction ((hiff (ev n)).2 ⟨n, rfl⟩)
  choose y hy hy1 using hex
  refine ⟨ev, y, hmono, htend, hiff, hy, fun m n => ?_⟩
  split_ifs with hmn
  · subst hmn; exact hy1 m
  · exact S.orthogonality (hy m) (hy n) (fun h => hmn (hmono.injective h))

lemma inner_toL2_eq_wInner {y z : ℝ → ℝ} (hy : Continuous y) (hz : Continuous z) :
    ⟪S.toL2 y hy, S.toL2 z hz⟫ = S.wInner y z := by
  rw [S.inner_toL2]
  exact intervalIntegral.integral_congr fun t _ => by ring

/-- The `L²` classes of the eigenfunctions are complete: only `0` is orthogonal to all of them. -/
theorem orthogonal_eigenfunctions_eq_bot {ev : ℕ → ℝ} {y : ℕ → ℝ → ℝ}
    (hiff : ∀ l, S.IsEigenvalue l ↔ ∃ n, ev n = l) (hy : ∀ n, S.IsEigenfunction (ev n) (y n)) :
    (Submodule.span ℝ (Set.range fun n => S.toL2 (y n) (hy n).1.1.continuous))ᗮ = ⊥ := by
  set T := S.greenOp
  rw [Submodule.eq_bot_iff]
  intro F hF
  have hFe : ∀ n, ⟪S.toL2 (y n) (hy n).1.1.continuous, F⟫ = 0 := fun n =>
    (Submodule.mem_orthogonal _ F).1 hF _ (Submodule.subset_span ⟨n, rfl⟩)
  -- `F` is orthogonal to every eigenspace of `T`
  have hle : (⨆ μ, Module.End.eigenspace (T : Module.End ℝ (Lp ℝ 2 S.wμ)) μ)
      ≤ (Submodule.span ℝ {F})ᗮ := by
    refine iSup_le fun μ v hv => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    have hTv : T v = μ • v := by
      rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hv
      exact hv
    by_cases hv0 : v = 0
    · rw [hv0, inner_zero_left]
    by_cases hμ : μ = 0
    · exfalso
      apply hv0
      rw [hμ, zero_smul] at hTv
      exact S.greenOp_eq_zero_iff.1 hTv
    obtain ⟨z, hz, hvz⟩ := S.exists_eigenfunction_of_eigvec hμ hTv hv0
    obtain ⟨n, hn⟩ := (hiff _).1 ⟨z, hz⟩
    have hz' : S.IsEigenfunction (ev n) z := by rw [hn]; exact hz
    obtain ⟨c, hc⟩ := S.eigenfunction_unique (hy n) hz'.1
    have hveq : v = (μ⁻¹ * c) • S.toL2 (y n) (hy n).1.1.continuous := by
      apply Lp.ext
      filter_upwards [hvz, S.ae_mem, Lp.coeFn_smul (μ⁻¹ * c) (S.toL2 (y n) (hy n).1.1.continuous),
        S.toL2_ae (hy n).1.1.continuous] with x h1 hx h2 h3
      rw [h1, h2, Pi.smul_apply, h3, hc x hx, smul_eq_mul]
      ring
    rw [hveq, real_inner_smul_left, hFe n, mul_zero]
  have hspec := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    S.isCompactOperator_greenOp S.isSymmetric_greenOp
  have hmem : F ∈ (⨆ μ, Module.End.eigenspace (T : Module.End ℝ (Lp ℝ 2 S.wμ)) μ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hu)
    rw [real_inner_comm]
    exact this
  rw [hspec] at hmem
  exact hmem

/-- **Eigenfunction expansion in `L²(r dx)` (Lebl, Theorem 5.1.4, in the `L²` sense).**  There are eigenvalues
`λ₀ < λ₁ < ⋯` (all of them) with eigenfunctions `yₙ`, orthonormal for the weight `r`, such that every
`F ∈ L²([a, b], r dx)` is the sum of its eigenfunction series `∑ ⟨yₙ, F⟩ yₙ`, converging in `L²`. -/
theorem eigenfunction_expansion_L2 :
    ∃ ev : ℕ → ℝ, ∃ y : ℕ → ℝ → ℝ, ∃ hy : ∀ n, S.IsEigenfunction (ev n) (y n),
      StrictMono ev ∧ (∀ l, S.IsEigenvalue l ↔ ∃ n, ev n = l) ∧
      (∀ m n, S.wInner (y m) (y n) = if m = n then 1 else 0) ∧
      ∀ F : Lp ℝ 2 S.wμ, HasSum (fun n => ⟪S.toL2 (y n) (hy n).1.1.continuous, F⟫ •
        S.toL2 (y n) (hy n).1.1.continuous) F := by
  obtain ⟨ev, y, hmono, -, hiff, hy, hon⟩ := S.exists_orthonormal_eigenfunctions
  refine ⟨ev, y, hy, hmono, hiff, hon, fun F => ?_⟩
  set e : ℕ → Lp ℝ 2 S.wμ := fun n => S.toL2 (y n) (hy n).1.1.continuous with he
  have horth : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro m n
    rw [he]
    simp only
    rw [S.inner_toL2_eq_wInner, hon]
  have hsp := S.orthogonal_eigenfunctions_eq_bot hiff hy
  let b := HilbertBasis.mkOfOrthogonalEqBot horth hsp
  have hb : ⇑b = e := HilbertBasis.coe_mkOfOrthogonalEqBot horth hsp
  have := b.hasSum_repr F
  simp only [HilbertBasis.repr_apply_apply, hb] at this
  exact this

/-- Mean-square convergence from the `L²` expansion. -/
theorem mean_square_of_hasSum {ev : ℕ → ℝ} {y : ℕ → ℝ → ℝ} (hy : ∀ n, S.IsEigenfunction (ev n) (y n))
    (hsum : ∀ F : Lp ℝ 2 S.wμ, HasSum (fun n => ⟪S.toL2 (y n) (hy n).1.1.continuous, F⟫ •
        S.toL2 (y n) (hy n).1.1.continuous) F)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc S.a S.b)) :
    Tendsto (fun N => ∫ t in S.a..S.b,
      S.r t * (f t - ∑ n ∈ Finset.range N, S.wInner f (y n) * y n t) ^ 2) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun t => f (S.clampI t) with hg
  have hgc : Continuous g := hf.comp_continuous S.continuous_clampI S.clampI_mem
  have hgf : ∀ t ∈ Icc S.a S.b, g t = f t := fun t ht => by simp [hg, S.clampI_of_mem ht]
  set F := S.toL2 g hgc
  set e : ℕ → Lp ℝ 2 S.wμ := fun n => S.toL2 (y n) (hy n).1.1.continuous with he
  have hc : ∀ n, ⟪e n, F⟫ = S.wInner f (y n) := fun n => by
    rw [he]; simp only
    rw [S.inner_toL2_eq_wInner, S.wInner_comm]
    exact intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le S.hab.le] at ht; rw [hgf t ht]
  have hT := (hsum F).tendsto_sum_nat
  rw [tendsto_iff_norm_sub_tendsto_zero] at hT
  have hT2 := hT.pow 2
  rw [zero_pow two_ne_zero] at hT2
  refine hT2.congr fun N => ?_
  -- the squared norm is the weighted integral
  set D := F - ∑ n ∈ Finset.range N, ⟪e n, F⟫ • e n with hD
  have hae : ⇑D =ᵐ[S.wμ] fun x => g x - ∑ n ∈ Finset.range N, S.wInner f (y n) * y n x := by
    have h4 : ∀ᵐ x ∂S.wμ, ∀ n, e n x = y n x :=
      ae_all_iff.2 fun n => S.toL2_ae (hy n).1.1.continuous
    have h5 : ∀ᵐ x ∂S.wμ, ∀ n, (⟪e n, F⟫ • e n) x = ⟪e n, F⟫ • e n x :=
      ae_all_iff.2 fun n => Lp.coeFn_smul _ _
    filter_upwards [Lp.coeFn_sub F (∑ n ∈ Finset.range N, ⟪e n, F⟫ • e n),
      KernelOp.coeFn_finset_sum (Finset.range N) (fun n => ⟪e n, F⟫ • e n), S.toL2_ae hgc, h4, h5]
      with x h1 h2 h3 h4 h5
    rw [hD, h1, Pi.sub_apply, h2, h3]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [h5 n, h4 n, hc n, smul_eq_mul]
  rw [norm_sub_rev, ← hD, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  calc ∫ x, ⟪D x, D x⟫ ∂S.wμ
      = ∫ x, (g x - ∑ n ∈ Finset.range N, S.wInner f (y n) * y n x) ^ 2 ∂S.wμ := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with x hx
        rw [hx]
        simp [sq]
    _ = ∫ t in S.a..S.b, S.r t * (g t - ∑ n ∈ Finset.range N, S.wInner f (y n) * y n t) ^ 2 :=
        S.integral_wμ _
    _ = _ := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le S.hab.le] at ht
        simp only [hgf t ht]


/-- **Eigenfunction expansion, mean-square convergence (Lebl, Theorem 5.1.4).**  For the orthonormal
eigenfunctions `yₙ` (eigenvalues `λ₀ < λ₁ < ⋯`, all of them) and every `f` continuous on `[a, b]`, with
`cₙ = ⟨f, yₙ⟩ = ∫_a^b f yₙ r`, the partial sums of `∑ cₙ yₙ` converge to `f` in mean square:
`∫_a^b r (f - ∑_{n<N} cₙ yₙ)² → 0`.  (The book states pointwise convergence for piecewise smooth continuous
`f`; that mode of convergence is not formalized.) -/
@[kb "lebldiffyqs2026" "Theorem 5.1.4, p. 279"]
theorem eigenfunction_expansion_mean_square :
    ∃ ev : ℕ → ℝ, ∃ y : ℕ → ℝ → ℝ, StrictMono ev ∧ (∀ l, S.IsEigenvalue l ↔ ∃ n, ev n = l) ∧
      (∀ n, S.IsEigenfunction (ev n) (y n)) ∧
      (∀ m n, S.wInner (y m) (y n) = if m = n then 1 else 0) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Icc S.a S.b) →
        Tendsto (fun N => ∫ t in S.a..S.b,
          S.r t * (f t - ∑ n ∈ Finset.range N, S.wInner f (y n) * y n t) ^ 2) atTop (𝓝 0) := by
  obtain ⟨ev, y, hy, hmono, hiff, hon, hsum⟩ := S.eigenfunction_expansion_L2
  exact ⟨ev, y, hmono, hiff, hy, hon, fun f hf => S.mean_square_of_hasSum hy hsum hf⟩

end RegularSL

end UndergradKB.DifferentialEquations
