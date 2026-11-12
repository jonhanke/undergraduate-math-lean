import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import UndergradKB.Common.Attr

/-! # Isolated singularities: Riemann and Casorati-Weierstrass (rows CX-136, CX-138)

We use the classification of an isolated singularity `z₀` of a function `f : ℂ → ℂ` that is
holomorphic on a punctured disc: removable (it agrees with a holomorphic function on the whole
disc), a pole (`‖f z‖ → ∞` as `z → z₀`), essential (neither).  Mathlib's `MeromorphicAt` is a
related but different notion and is not used here.

Contents: the limit characterisation of removable singularities (Beck Proposition 9.1.6(a)), the
characterisation of poles (9.1.6(b)), and the Casorati-Weierstrass theorem (9.1.9). -/

namespace UndergradKB.ComplexAnalysis

open Metric Set Filter Topology Function

/-- Beck Definition 9.1.1(a) (CX-136). `f` has a removable singularity at `z₀`: on some disc
around `z₀` it agrees, away from `z₀`, with a function holomorphic on the whole disc. -/
@[kb "beck2025" "Definition 9.1.1, p. 138"]
def HasRemovableSingularity (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ R > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₀ R) ∧ EqOn f g (ball z₀ R \ {z₀})

/-- Beck Definition 9.1.1(b) (CX-136). `f` has a pole at `z₀`: `‖f z‖ → ∞` as `z → z₀`. -/
@[kb "beck2025" "Definition 9.1.1, p. 138"]
def HasPole (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  Tendsto (fun z => ‖f z‖) (𝓝[≠] z₀) atTop

/-- Beck Definition 9.1.1(c) (CX-136). An essential singularity is neither removable nor a pole. -/
@[kb "beck2025" "Definition 9.1.1, p. 138"]
def HasEssentialSingularity (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ¬ HasRemovableSingularity f z₀ ∧ ¬ HasPole f z₀

theorem tendsto_inv_norm_sub_atTop (z₀ : ℂ) :
    Tendsto (fun z : ℂ => ‖z - z₀‖⁻¹) (𝓝[≠] z₀) atTop := by
  have h0 : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝 z₀) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝 z₀) (𝓝 ‖z₀ - z₀‖) :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).tendsto z₀
    simpa using this
  have h : Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝[≠] z₀) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz => norm_pos_iff.2 (sub_ne_zero.2 hz)⟩
  exact tendsto_inv_nhdsGT_zero.comp h

/-- Beck Proposition 9.1.6(a) (CX-136). Let `f` be holomorphic on the punctured disc of radius
`R` around `z₀`.  Then `z₀` is a removable singularity iff `(z - z₀) f(z) → 0` as `z → z₀`. -/
@[kb "beck2025" "Proposition 9.1.6, p. 149"]
theorem removable_iff_tendsto_mul_sub {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R \ {z₀})) :
    HasRemovableSingularity f z₀ ↔ Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 0) := by
  classical
  constructor
  · rintro ⟨r, hr, g, hg, hfg⟩
    have hgc : ContinuousAt g z₀ := (hg.differentiableAt (ball_mem_nhds z₀ hr)).continuousAt
    have h1 : Tendsto (fun z => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
      have : Tendsto (fun z => (z - z₀) * g z) (𝓝 z₀) (𝓝 ((z₀ - z₀) * g z₀)) :=
        (continuousAt_id.sub continuousAt_const).mul hgc
      simpa using this.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hr)] with z hz hzb
    rw [hfg ⟨hzb, hz⟩]
  · intro h
    have hs : ball z₀ R ∈ 𝓝 z₀ := ball_mem_nhds z₀ hR
    have hd : DifferentiableOn ℂ (update f z₀ 0) (ball z₀ R \ {z₀}) :=
      hf.congr (fun z hz => update_of_ne hz.2 _ _)
    have ho : (fun z => update f z₀ 0 z - update f z₀ 0 z₀) =o[𝓝[≠] z₀] fun z => (z - z₀)⁻¹ := by
      simp only [update_self, sub_zero]
      refine (Asymptotics.isLittleO_iff_tendsto' (𝕜 := ℂ) ?_).2 ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz h0
        exfalso
        exact hz (sub_eq_zero.1 (inv_eq_zero.1 h0))
      · refine h.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [update_of_ne hz, div_inv_eq_mul, mul_comm]
    have := Complex.differentiableOn_update_limUnder_of_isLittleO hs hd ho
    refine ⟨R, hR, _, this, fun z hz => ?_⟩
    rw [update_of_ne hz.2, update_of_ne hz.2]

/-- A pole is not a removable singularity. -/
theorem HasPole.not_removable {f : ℂ → ℂ} {z₀ : ℂ} (hp : HasPole f z₀) :
    ¬ HasRemovableSingularity f z₀ := by
  rintro ⟨r, hr, g, hg, hfg⟩
  have hgc : ContinuousAt g z₀ := (hg.differentiableAt (ball_mem_nhds z₀ hr)).continuousAt
  have h2 : Tendsto (fun z => ‖f z‖) (𝓝[≠] z₀) (𝓝 ‖g z₀‖) := by
    refine (hgc.norm.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hr)] with z hz hzb
    rw [hfg ⟨hzb, hz⟩]
  exact not_tendsto_nhds_of_tendsto_atTop hp _ h2

/-- If `(z - z₀)^(n+1) f(z) → 0` then `z₀` is a removable singularity or a pole. -/
theorem removable_or_pole_of_tendsto_pow {z₀ : ℂ} (n : ℕ) :
    ∀ {f : ℂ → ℂ} {R : ℝ}, 0 < R → DifferentiableOn ℂ f (ball z₀ R \ {z₀}) →
    Tendsto (fun z => (z - z₀) ^ (n + 1) * f z) (𝓝[≠] z₀) (𝓝 0) →
    HasRemovableSingularity f z₀ ∨ HasPole f z₀ := by
  induction n with
  | zero =>
    intro f R hR hf h
    left
    exact (removable_iff_tendsto_mul_sub hR hf).2 (by simpa using h)
  | succ n ih =>
    intro f R hR hf h
    set h' : ℂ → ℂ := fun z => (z - z₀) * f z with hh'
    have hd' : DifferentiableOn ℂ h' (ball z₀ R \ {z₀}) :=
      (differentiableOn_id.sub_const z₀).mul hf
    have ht : Tendsto (fun z => (z - z₀) ^ (n + 1) * h' z) (𝓝[≠] z₀) (𝓝 0) := by
      refine h.congr (fun z => ?_)
      simp only [hh']
      ring
    rcases ih hR hd' ht with ⟨r, hr, g, hg, hfg⟩ | hp
    · by_cases hg0 : g z₀ = 0
      · left
        refine ⟨r, hr, dslope g z₀, (Complex.differentiableOn_dslope (ball_mem_nhds z₀ hr)).2 hg,
          fun z hz => ?_⟩
        have hne : z - z₀ ≠ 0 := sub_ne_zero.2 hz.2
        have e : h' z = g z := hfg hz
        rw [dslope_of_ne _ hz.2, slope_def_field, ← e, hg0]
        simp only [hh', sub_zero]
        field_simp
      · right
        have hgc : ContinuousAt g z₀ := (hg.differentiableAt (ball_mem_nhds z₀ hr)).continuousAt
        refine (Filter.Tendsto.pos_mul_atTop (norm_pos_iff.2 hg0)
          (hgc.norm.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_inv_norm_sub_atTop z₀)).congr' ?_
        filter_upwards [self_mem_nhdsWithin,
          eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hr)] with z hz hzb
        have e : h' z = g z := hfg ⟨hzb, hz⟩
        have hne : ‖z - z₀‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hz)
        rw [← e]
        simp only [hh', norm_mul]
        field_simp
    · right
      refine tendsto_atTop_mono' _ ?_ hp
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ one_pos)] with z hz hzb
      have : ‖z - z₀‖ ≤ 1 := by
        have := hzb
        rw [dist_eq_norm] at this
        exact this.le
      simp only [hh', norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) this

/-- Beck Proposition 9.1.6(b) (CX-136). Let `f` be holomorphic on the punctured disc of radius `R`
around `z₀`.  Then `z₀` is a pole iff it is not removable and `(z - z₀)^(n+1) f(z) → 0` for some
positive integer `n`. -/
@[kb "beck2025" "Proposition 9.1.6, p. 149"]
theorem hasPole_iff {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R \ {z₀})) :
    HasPole f z₀ ↔ ¬ HasRemovableSingularity f z₀ ∧
      ∃ n : ℕ, 0 < n ∧ Tendsto (fun z => (z - z₀) ^ (n + 1) * f z) (𝓝[≠] z₀) (𝓝 0) := by
  classical
  constructor
  · intro hp
    refine ⟨hp.not_removable, ?_⟩
    have hp1 : ∀ᶠ z in 𝓝[≠] z₀, 1 ≤ ‖f z‖ := hp.eventually_ge_atTop 1
    set q : ℂ → ℂ := update (fun z => (f z)⁻¹) z₀ 0 with hq
    have hqa : AnalyticAt ℂ q z₀ := by
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hR),
          self_mem_nhdsWithin, hp1] with z hzb hz hz1
        have hfz : f z ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hz1
          linarith
        have hopen : ball z₀ R \ {z₀} ∈ 𝓝 z := by
          have : IsOpen (ball z₀ R \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
          exact this.mem_nhds ⟨hzb, hz⟩
        have hfd : DifferentiableAt ℂ f z := hf.differentiableAt hopen
        have : DifferentiableAt ℂ (fun z => (f z)⁻¹) z := hfd.inv hfz
        refine this.congr_of_eventuallyEq ?_
        filter_upwards [(isOpen_ne (x := z₀)).mem_nhds (show z ≠ z₀ from hz)] with y hy
        exact update_of_ne hy _ _
      · rw [hq, continuousAt_update_same]
        refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
        simpa [Function.comp_def, norm_inv] using tendsto_inv_atTop_zero.comp hp
    have hnz : ¬ ∀ᶠ z in 𝓝 z₀, q z = 0 := by
      intro hz
      obtain ⟨z, h1, h2, h3⟩ :=
        ((hz.filter_mono nhdsWithin_le_nhds).and (hp1.and self_mem_nhdsWithin)).exists
      have hz2 : z ≠ z₀ := h3
      rw [hq, update_of_ne hz2] at h1
      have : f z = 0 := by simpa using h1
      rw [this, norm_zero] at h2
      linarith
    obtain ⟨n, g, hg, hg0, hev⟩ := (hqa.exists_eventuallyEq_pow_smul_ne_zero_iff).2 hnz
    have hn : 0 < n := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      have h := hev.self_of_nhds
      simp [hq] at h
      exact hg0 h.symm
    refine ⟨n, hn, ?_⟩
    have hlim : Tendsto (fun z => (z - z₀) / g z) (𝓝 z₀) (𝓝 0) := by
      have : ContinuousAt (fun z => (z - z₀) / g z) z₀ :=
        (continuousAt_id.sub continuousAt_const).div hg.continuousAt hg0
      simpa using this.tendsto
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds, hp1,
      (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds] with z hz hz2 hz1 hgz
    have hfz : f z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz1
      linarith
    have hne : z - z₀ ≠ 0 := sub_ne_zero.2 hz
    rw [hq, update_of_ne hz, smul_eq_mul] at hz2
    have hf' : f z = ((z - z₀) ^ n * g z)⁻¹ := by
      rw [← hz2]; simp
    rw [hf']
    field_simp
    ring
  · rintro ⟨hnr, n, -, ht⟩
    exact (removable_or_pole_of_tendsto_pow n hR hf ht).resolve_left hnr

/-- Beck Theorem 9.1.9 (CX-138), Casorati-Weierstrass.  Let `f` be holomorphic on the punctured
disc of radius `R` around an essential singularity `z₀`.  Then for every `w`, `ε > 0` and `r > 0`
there is `z` with `0 < ‖z - z₀‖ < r` and `‖f z - w‖ < ε`. -/
@[kb "beck2025" "Theorem 9.1.9, p. 152"]
theorem casorati_weierstrass {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R \ {z₀})) (hess : HasEssentialSingularity f z₀)
    (w : ℂ) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ z : ℂ, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r ∧ ‖f z - w‖ < ε := by
  by_contra hcon
  push Not at hcon
  set ρ : ℝ := min r R with hρ
  have hρ0 : 0 < ρ := lt_min hr hR
  have hmem : ∀ z ∈ ball z₀ ρ \ {z₀}, z ∈ ball z₀ R ∧ 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r := by
    intro z hz
    have h1 : ‖z - z₀‖ < ρ := by
      have := mem_ball.1 hz.1
      rwa [dist_eq_norm] at this
    exact ⟨ball_subset_ball (min_le_right _ _) hz.1,
      norm_pos_iff.2 (sub_ne_zero.2 hz.2), lt_of_lt_of_le h1 (min_le_left _ _)⟩
  have hfw : ∀ z ∈ ball z₀ ρ \ {z₀}, ε ≤ ‖f z - w‖ := fun z hz =>
    hcon z (hmem z hz).2.1 (hmem z hz).2.2
  have hne : ∀ z ∈ ball z₀ ρ \ {z₀}, f z - w ≠ 0 := by
    intro z hz h0
    have := hfw z hz
    rw [h0, norm_zero] at this
    linarith
  set g : ℂ → ℂ := fun z => (f z - w)⁻¹ with hg
  have hgd : DifferentiableOn ℂ g (ball z₀ ρ \ {z₀}) :=
    ((hf.mono fun z hz => ⟨(hmem z hz).1, hz.2⟩).sub_const w).inv hne
  have hgb : ∀ z ∈ ball z₀ ρ \ {z₀}, ‖g z‖ ≤ ε⁻¹ := by
    intro z hz
    simp only [hg, norm_inv]
    exact inv_anti₀ hε (hfw z hz)
  have hglim : Tendsto (fun z => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (a := fun z => ‖z - z₀‖ * ε⁻¹) ?_
    · filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hρ0)] with z hz hzb
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hgb z ⟨hzb, hz⟩) (norm_nonneg _)
    · have : Tendsto (fun z : ℂ => ‖z - z₀‖ * ε⁻¹) (𝓝 z₀) (𝓝 (‖z₀ - z₀‖ * ε⁻¹)) :=
        ((continuous_norm.comp (continuous_id.sub continuous_const)).mul
          continuous_const).tendsto z₀
      simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨r', hr', gt, hgt, hgg⟩ := (removable_iff_tendsto_mul_sub hρ0 hgd).2 hglim
  have hgta : AnalyticAt ℂ gt z₀ := hgt.analyticAt (ball_mem_nhds z₀ hr')
  have hnz : ¬ ∀ᶠ z in 𝓝 z₀, gt z = 0 := by
    intro hz
    have hev' : ∀ᶠ z in 𝓝[≠] z₀, gt z = 0 ∧ z ∈ ball z₀ ρ ∧ z ∈ ball z₀ r' ∧ z ≠ z₀ := by
      filter_upwards [hz.filter_mono nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hρ0),
        eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hr'),
        self_mem_nhdsWithin] with z h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    obtain ⟨z, h1, h2, h3, hz'⟩ := hev'.exists
    have e : g z = gt z := hgg ⟨h3, hz'⟩
    rw [h1] at e
    exact inv_ne_zero (hne z ⟨h2, hz'⟩) e
  obtain ⟨n, k, hk, hk0, hev⟩ := (hgta.exists_eventuallyEq_pow_smul_ne_zero_iff).2 hnz
  have hlim : Tendsto (fun z => (z - z₀) / k z) (𝓝 z₀) (𝓝 0) := by
    have : ContinuousAt (fun z => (z - z₀) / k z) z₀ :=
      (continuousAt_id.sub continuousAt_const).div hk.continuousAt hk0
    simpa using this.tendsto
  have hpow : Tendsto (fun z => (z - z₀) ^ (n + 1) * (f z - w)) (𝓝[≠] z₀) (𝓝 0) := by
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds,
      (hk.continuousAt.eventually_ne hk0).filter_mono nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hρ0),
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds z₀ hr')]
      with z hz hz2 hkz hzb hzb'
    have hne' : z - z₀ ≠ 0 := sub_ne_zero.2 hz
    have e : g z = gt z := hgg ⟨hzb', hz⟩
    rw [smul_eq_mul] at hz2
    have hf' : f z - w = ((z - z₀) ^ n * k z)⁻¹ := by
      rw [← hz2, ← e]
      simp [hg]
    rw [hf']
    field_simp
    ring
  have hf1 : DifferentiableOn ℂ (fun z => f z - w) (ball z₀ R \ {z₀}) := hf.sub_const w
  rcases removable_or_pole_of_tendsto_pow n hR hf1 hpow with ⟨R'', hR'', gg, hgd', hfg⟩ | hp
  · refine hess.1 ⟨R'', hR'', fun z => gg z + w, hgd'.add_const w, fun z hz => ?_⟩
    have h2 : f z - w = gg z := hfg hz
    linear_combination h2
  · refine hess.2 ?_
    have h1 : Tendsto (fun z => ‖f z - w‖ + -‖w‖) (𝓝[≠] z₀) atTop :=
      tendsto_atTop_add_const_right _ _ hp
    refine tendsto_atTop_mono' _ (Eventually.of_forall fun z => ?_) h1
    have := norm_sub_le (f z) w
    simp only
    linarith

end UndergradKB.ComplexAnalysis
