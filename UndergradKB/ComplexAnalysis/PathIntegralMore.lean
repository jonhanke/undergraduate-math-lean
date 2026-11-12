import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.ComplexAnalysis.PathIntegral

/-!
# Simple connectivity, limits and power series along paths (rows CX-076, CX-108, CX-116)

* Open discs and the slit plane are simply connected, `ℂ \ {0}` is not (the latter via the
  non-existence of a primitive of `1/z`, `not_exists_antiderivative_inv`).
* Uniform convergence on the trace of a `C^1` path passes to path integrals.
* A power series may be integrated term by term along a `C^1` path inside its disc of convergence.
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace UndergradKB.ComplexAnalysis

/-! ### CX-076 -/

/-- Beck Example 5.2.3 (CX-076). Open discs are simply connected. -/
@[kb "beck2025" "Example 5.2.3, p. 94"]
theorem isSimplyConnected_ball (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (Metric.ball c r) := by
  have := (convex_ball c r).contractibleSpace ⟨c, Metric.mem_ball_self hr⟩
  show SimplyConnectedSpace (Metric.ball c r)
  infer_instance

/-- Beck Example 5.2.3 (CX-076). The slit plane is simply connected. -/
@[kb "beck2025" "Example 5.2.3, p. 94"]
theorem isSimplyConnected_slitPlane : IsSimplyConnected Complex.slitPlane := by
  have := Complex.starConvex_one_slitPlane.contractibleSpace
    ⟨1, Complex.one_mem_slitPlane⟩
  show SimplyConnectedSpace Complex.slitPlane
  infer_instance

/-- Beck Example 5.2.3 (CX-076). `ℂ \ {0}` is not simply connected: otherwise a continuous
logarithm would exist and be an antiderivative of `1/z`. -/
@[kb "beck2025" "Example 5.2.3, p. 94"]
theorem not_isSimplyConnected_compl_zero : ¬ IsSimplyConnected ({0}ᶜ : Set ℂ) := by
  intro h
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp (g := id) h
    isOpen_compl_singleton continuousOn_id (by simp)
  refine not_exists_antiderivative_inv ⟨L, fun z hz => ?_⟩
  have hz' : z ∈ ({0}ᶜ : Set ℂ) := hz
  have hnhds : ({0}ᶜ : Set ℂ) ∈ 𝓝 z := isOpen_compl_singleton.mem_nhds hz'
  have hcont : ContinuousAt L z := hLc.continuousAt hnhds
  have ev : ∀ᶠ y in 𝓝 z, Complex.exp (L y) = y := by
    filter_upwards [hnhds] with y hy
    exact hL hy
  have hexp : Complex.exp (L z) = z := hL hz'
  have := HasDerivAt.of_local_left_inverse hcont (Complex.hasDerivAt_exp (L z))
    (Complex.exp_ne_zero _) ev
  rwa [hexp] at this

/-! ### CX-108 -/

lemma pathIntegral_sub {f g : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b)
    (hg : IntervalIntegrable (fun t => g (γ t) * deriv γ t) volume a b) :
    pathIntegral (fun z => f z - g z) γ a b = pathIntegral f γ a b - pathIntegral g γ a b := by
  unfold pathIntegral
  simp only [sub_mul]
  exact integral_sub hf hg

/-- Beck Proposition 7.3.6 (CX-108). If `F n → f` uniformly on the trace of a `C^1` path and each
`F n` is continuous there, the path integrals converge. -/
@[kb "beck2025" "Proposition 7.3.6, p. 119"]
theorem tendsto_pathIntegral_of_tendstoUniformlyOn {ι : Type*} {p : Filter ι} [p.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsC1On γ a b) (hab : a ≤ b)
    (hF : ∀ᶠ n in p, ContinuousOn (F n) (γ '' uIcc a b))
    (hu : TendstoUniformlyOn F f p (γ '' uIcc a b)) :
    Tendsto (fun n => pathIntegral (F n) γ a b) p (𝓝 (pathIntegral f γ a b)) := by
  have hfc : ContinuousOn f (γ '' uIcc a b) := hu.continuousOn hF.frequently
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hL : 0 ≤ pathLength γ a b :=
    integral_nonneg hab (fun _ _ => norm_nonneg _)
  have hδ : 0 < ε / (pathLength γ a b + 1) := by positivity
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.1 hu _ hδ] with n hn hn2
  have hle := norm_pathIntegral_le (f := fun z => F n z - f z) (M := ε / (pathLength γ a b + 1))
    hγ (hn.sub hfc) hab (fun t ht => by
      have := hn2 (γ t) (mem_image_of_mem γ (Icc_subset_uIcc ht))
      rw [dist_comm, dist_eq_norm] at this
      exact this.le)
  rw [dist_eq_norm, ← pathIntegral_sub (intervalIntegrable_integrand hγ hn)
    (intervalIntegrable_integrand hγ hfc)]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-! ### CX-116 -/

lemma pathIntegral_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hF : ∀ i ∈ s, IntervalIntegrable (fun t => F i (γ t) * deriv γ t) volume a b) :
    pathIntegral (fun z => ∑ i ∈ s, F i z) γ a b = ∑ i ∈ s, pathIntegral (F i) γ a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pathIntegral]
  | insert i s hi ih =>
    have h1 := hF i (Finset.mem_insert_self i s)
    have h2 : IntervalIntegrable (fun t => (∑ j ∈ s, F j (γ t)) * deriv γ t) volume a b := by
      have := IntervalIntegrable.sum s (f := fun j t => F j (γ t) * deriv γ t)
        (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have e : (fun t => (∑ j ∈ s, F j (γ t)) * deriv γ t)
          = ∑ i ∈ s, fun t => F i (γ t) * deriv γ t := by
        ext t; simp [Finset.sum_apply, Finset.sum_mul]
      rw [e]; exact this
    have h3 := pathIntegral_add (f := F i) (g := fun z => ∑ j ∈ s, F j z) (γ := γ) h1 h2
    simp only [Finset.sum_insert hi]
    rw [h3, ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))]

/-- Beck Corollary 7.4.10 (CX-116). A power series `∑ c k * (z - z₀)^k` with `∑ ‖c k‖ r^k < ∞`
can be integrated term by term along a `C^1` path staying in `closedBall z₀ r`. -/
@[kb "beck2025" "Corollary 7.4.10, p. 124"]
theorem hasSum_pathIntegral_powerSeries {c : ℕ → ℂ} {z₀ : ℂ} {r : ℝ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsC1On γ a b) (hab : a ≤ b) (hr : Summable fun k => ‖c k‖ * r ^ k)
    (hin : ∀ t ∈ uIcc a b, ‖γ t - z₀‖ ≤ r) :
    HasSum (fun k => c k * pathIntegral (fun z => (z - z₀) ^ k) γ a b)
      (pathIntegral (fun z => ∑' k, c k * (z - z₀) ^ k) γ a b) := by
  have hS : ∀ z ∈ γ '' uIcc a b, ‖z - z₀‖ ≤ r := by
    rintro _ ⟨t, ht, rfl⟩
    exact hin t ht
  have hbound : ∀ k (z : ℂ), z ∈ γ '' uIcc a b → ‖c k * (z - z₀) ^ k‖ ≤ ‖c k‖ * r ^ k := by
    intro k z hz
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hS z hz) k) (norm_nonneg _)
  have hcont : ∀ k, ContinuousOn (fun z : ℂ => (z - z₀) ^ k) (γ '' uIcc a b) :=
    fun k => (by fun_prop : Continuous fun z : ℂ => (z - z₀) ^ k).continuousOn
  have hu := tendstoUniformlyOn_tsum_nat (f := fun k (z : ℂ) => c k * (z - z₀) ^ k) hr hbound
  have hconv := tendsto_pathIntegral_of_tendstoUniformlyOn (p := atTop) hγ hab
    (Eventually.of_forall fun N =>
      (by fun_prop :
        Continuous fun z : ℂ => ∑ k ∈ Finset.range N, c k * (z - z₀) ^ k).continuousOn) hu
  have hpart : ∀ N, pathIntegral (fun z => ∑ k ∈ Finset.range N, c k * (z - z₀) ^ k) γ a b
      = ∑ k ∈ Finset.range N, c k * pathIntegral (fun z => (z - z₀) ^ k) γ a b := by
    intro N
    rw [pathIntegral_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => pathIntegral_const_mul (c k)
    · intro k _
      have := intervalIntegrable_integrand hγ
        (((hcont k).const_smul (c k)) :
          ContinuousOn (fun z : ℂ => c k * (z - z₀) ^ k) (γ '' uIcc a b))
      exact this
  have hsum : Summable fun k => c k * pathIntegral (fun z => (z - z₀) ^ k) γ a b := by
    refine Summable.of_norm_bounded (hr.mul_right (pathLength γ a b)) (fun k => ?_)
    rw [norm_mul]
    have := norm_pathIntegral_le (f := fun z => (z - z₀) ^ k) (M := r ^ k) hγ (hcont k) hab
      (fun t ht => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hin t (Icc_subset_uIcc ht)) k)
    calc ‖c k‖ * ‖pathIntegral (fun z => (z - z₀) ^ k) γ a b‖
        ≤ ‖c k‖ * (r ^ k * pathLength γ a b) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖c k‖ * r ^ k * pathLength γ a b := by ring
  rw [hsum.hasSum_iff_tendsto_nat]
  simpa only [hpart] using hconv

end UndergradKB.ComplexAnalysis
