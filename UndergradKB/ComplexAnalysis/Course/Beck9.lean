import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 9 (Isolated Singularities and the Residue Theorem): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`).
Beck's Definition 9.3.1 (meromorphic function) is a pure definition and is not restated. -/

namespace UndergradKB.ComplexAnalysis.Course.Beck9
open Filter Topology Metric Set

/-- Beck Corollary 9.1.7 (CX-137), the factorisation implies a pole. If `f` is holomorphic in the
punctured disk about `z₀` and `f z = g z / (z - z₀)^m` there, with `m ≥ 1`, `g` holomorphic in the
disk and `g z₀ ≠ 0`, then `|f z| → ∞` as `z → z₀`. -/
@[kb "beck2025" "Corollary 9.1.7, p. 151"]
theorem pole_of_factorization (f g : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m)
    (hg : DifferentiableOn ℂ g (ball z₀ R)) (hg0 : g z₀ ≠ 0)
    (hfg : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z = g z / (z - z₀) ^ m) :
    Tendsto (fun z => ‖f z‖) (𝓝[≠] z₀) atTop := by
  have hgc : ContinuousAt g z₀ := (hg.differentiableAt (ball_mem_nhds z₀ hR)).continuousAt
  have h1 : Tendsto (fun z => ‖g z‖) (𝓝[≠] z₀) (𝓝 ‖g z₀‖) :=
    hgc.norm.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℂ => (z - z₀) ^ m) (𝓝[≠] z₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => (z - z₀) ^ m) (𝓝 z₀) (𝓝 ((z₀ - z₀) ^ m)) :=
        ((continuous_id.sub continuous_const).pow m).tendsto z₀
      rw [sub_self, zero_pow hm.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact pow_ne_zero _ (sub_ne_zero.2 hz)
  have h3 := tendsto_norm_inv_nhdsNE_zero_atTop.comp h2
  have h4 := Filter.Tendsto.pos_mul_atTop (norm_pos_iff.2 hg0) h1 h3
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hR)] with z hz hzb
  simp [hfg z hzb hz, div_eq_mul_inv]

/-- Beck Corollary 9.1.7 (CX-137), a pole has a factorisation. If `f` is holomorphic in the
punctured disk about `z₀` and `|f z| → ∞` as `z → z₀`, then there are `m ≥ 1` and `g` holomorphic
in the disk with `g z₀ ≠ 0` and `f z = g z / (z - z₀)^m` in the punctured disk. -/
@[kb "beck2025" "Corollary 9.1.7, p. 151"]
theorem factorization_of_pole (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R \ {z₀}))
    (hpole : Tendsto (fun z => ‖f z‖) (𝓝[≠] z₀) atTop) :
    ∃ m : ℕ, 0 < m ∧ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₀ R) ∧ g z₀ ≠ 0 ∧
      ∀ z ∈ ball z₀ R, z ≠ z₀ → f z = g z / (z - z₀) ^ m := by
  classical
  have hPopen : IsOpen (ball z₀ R \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
  have hPev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ ball z₀ R \ {z₀} := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hR), self_mem_nhdsWithin]
      with z hz hzc
    exact ⟨hz, hzc⟩
  have hbig : ∀ᶠ z in 𝓝[≠] z₀, 1 < ‖f z‖ := hpole.eventually_gt_atTop 1
  have hfne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := hbig.mono fun z hz h0 => by
    rw [h0, norm_zero] at hz; linarith
  set H : ℂ → ℂ := Function.update (fun z => (f z)⁻¹) z₀ 0 with hHdef
  have hHne : ∀ z, z ≠ z₀ → H z = (f z)⁻¹ := fun z hz => by simp [hHdef, hz]
  have hH0 : H z₀ = 0 := by simp [hHdef]
  have hHd : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ H z := by
    filter_upwards [hPev, hfne] with z hz hfz
    have h1 : DifferentiableAt ℂ (fun w => (f w)⁻¹) z :=
      (hf.differentiableAt (hPopen.mem_nhds hz)).inv hfz
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz.2] with w hw using hHne w hw
  have hHc : ContinuousAt H z₀ := by
    rw [← continuousWithinAt_compl_self]
    have h1 : Tendsto (fun z => (f z)⁻¹) (𝓝[≠] z₀) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_inv_atTop_zero.comp hpole).congr fun z => ?_
      simp [norm_inv]
    show Tendsto H (𝓝[≠] z₀) (𝓝 (H z₀))
    rw [hH0]
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using (hHne z hz).symm
  have hA : AnalyticAt ℂ H z₀ :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hHd hHc
  have hnetop : analyticOrderAt H z₀ ≠ ⊤ := by
    intro htop
    have h1 := analyticOrderAt_eq_top.1 htop
    have h2 : ∀ᶠ z in 𝓝[≠] z₀, H z = 0 := eventually_nhdsWithin_of_eventually_nhds h1
    obtain ⟨z, hz1, hz2, hz3⟩ := (h2.and (hfne.and self_mem_nhdsWithin)).exists
    rw [hHne z hz3] at hz1
    exact hz2 (inv_eq_zero.1 hz1)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hnetop
  obtain ⟨k, hkA, hk0, hev⟩ := (hA.analyticOrderAt_eq_natCast (n := m)).1 hm.symm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      have := hev.self_of_nhds
      rw [h0, hH0] at this
      simp at this
      exact hk0 this.symm
    · exact h0
  set g : ℂ → ℂ := Function.update (fun z => f z * (z - z₀) ^ m) z₀ (k z₀)⁻¹ with hgdef
  have hgne : ∀ z, z ≠ z₀ → g z = f z * (z - z₀) ^ m := fun z hz => by simp [hgdef, hz]
  have hg0 : g z₀ = (k z₀)⁻¹ := by simp [hgdef]
  have hkc : ∀ᶠ w in 𝓝 z₀, k w ≠ 0 := hkA.continuousAt.eventually_ne hk0
  have hgz : g =ᶠ[𝓝 z₀] fun w => (k w)⁻¹ := by
    filter_upwards [hev, hkc, eventually_nhdsWithin_iff.1 (hPev.and hfne)] with w hw hkw hwP
    by_cases hwz : w = z₀
    · subst hwz; simp [hg0]
    · obtain ⟨_, hfw⟩ := hwP hwz
      rw [hgne w hwz]
      rw [hHne w hwz] at hw
      have hp : (w - z₀) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwz)
      simp only [smul_eq_mul] at hw
      have hk' : k w = (f w)⁻¹ * ((w - z₀) ^ m)⁻¹ := by
        rw [hw]; field_simp
      rw [hk']
      field_simp
  refine ⟨m, hmpos, g, ?_, by rw [hg0]; exact inv_ne_zero hk0, ?_⟩
  · intro z hz
    by_cases hzc : z = z₀
    · subst hzc
      exact ((hkA.differentiableAt.inv hk0).congr_of_eventuallyEq hgz).differentiableWithinAt
    · have hzP : z ∈ ball z₀ R \ {z₀} := ⟨hz, hzc⟩
      have hfz := hf.differentiableAt (hPopen.mem_nhds hzP)
      have h1 : DifferentiableAt ℂ (fun w => f w * (w - z₀) ^ m) z := hfz.mul (by fun_prop)
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_ne.mem_nhds hzc] with w hw using hgne w hw
  · intro z _ hzc
    rw [hgne z hzc]
    have hp : (z - z₀) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzc)
    field_simp

/-- Beck Definition 9.1.8 (CX-137). The order `m` of a pole is determined by the factorisation
`f = g / (z - z₀)^m`: it is the negative of Mathlib's `meromorphicOrderAt`. -/
@[kb "beck2025" "Definition 9.1.8, p. 151"]
theorem pole_order_eq_neg_meromorphicOrderAt (f g : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R) (m : ℕ)
    (hg : DifferentiableOn ℂ g (ball z₀ R)) (hg0 : g z₀ ≠ 0)
    (hfg : ∀ z ∈ ball z₀ R, z ≠ z₀ → f z = g z / (z - z₀) ^ m) :
    meromorphicOrderAt f z₀ = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
  have hga : AnalyticAt ℂ g z₀ := hg.analyticOnNhd isOpen_ball z₀ (mem_ball_self hR)
  have hmero : MeromorphicAt f z₀ := by
    have : MeromorphicAt (fun z => (z - z₀) ^ (-(m : ℤ)) • g z) z₀ :=
      ((MeromorphicAt.id z₀).sub (MeromorphicAt.const _ z₀)).zpow (-(m : ℤ)) |>.smul hga.meromorphicAt
    refine this.congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hR), self_mem_nhdsWithin]
      with z hzb hz
    rw [hfg z hzb hz]
    simp [zpow_neg, div_eq_mul_inv, mul_comm]
  rw [meromorphicOrderAt_eq_int_iff hmero]
  refine ⟨g, hga, hg0, ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hR), self_mem_nhdsWithin]
    with z hzb hz
  rw [hfg z hzb hz]
  simp [zpow_neg, div_eq_mul_inv, mul_comm]

/-- Beck Definition 9.3.1 (CX-143). f is meromorphic on U iff near each point z of U, some power
(w - z)^n times f is analytic at z (so f is holomorphic except at poles). -/
@[kb "beck2025" "Definition 9.3.1, p. 158"]
theorem meromorphicOn_iff_mul_pow_analytic (f : ℂ → ℂ) (U : Set ℂ) :
    MeromorphicOn f U ↔ ∀ z ∈ U, ∃ n : ℕ, AnalyticAt ℂ (fun w => (w - z) ^ n * f w) z :=
  Iff.rfl

end UndergradKB.ComplexAnalysis.Course.Beck9
