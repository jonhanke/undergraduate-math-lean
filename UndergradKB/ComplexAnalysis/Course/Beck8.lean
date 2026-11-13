import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 8 (Taylor and Laurent Series): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`).

A power series `∑ c_k (z - z₀)^k` is given by its coefficient sequence `c : ℕ → ℂ`; its radius of
convergence is the radius of `FormalMultilinearSeries.ofScalars ℂ c`, and its disk of convergence is
`Metric.eball z₀ R`. -/

namespace UndergradKB.ComplexAnalysis.Course.Beck8
open Filter Topology Metric Set
open scoped Nat NNReal ENNReal

/-- The radius of convergence of `∑ c_k (z - z₀)^k`. -/
noncomputable abbrev rad (c : ℕ → ℂ) : ℝ≥0∞ := (FormalMultilinearSeries.ofScalars ℂ c).radius

/-- The sum function `z ↦ ∑ c_k (z - z₀)^k` of a power series. -/
noncomputable def psum (c : ℕ → ℂ) (z₀ : ℂ) (z : ℂ) : ℂ := ∑' k, c k * (z - z₀) ^ k

lemma psum_eq (c : ℕ → ℂ) (z₀ : ℂ) :
    psum c z₀ = fun z => (FormalMultilinearSeries.ofScalars ℂ c).sum (z - z₀) := by
  funext z
  unfold psum
  show _ = ∑' n, (FormalMultilinearSeries.ofScalars ℂ c n) fun _ => z - z₀
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

lemma hasFPS (c : ℕ → ℂ) (z₀ : ℂ) (hR : 0 < rad c) :
    HasFPowerSeriesOnBall (psum c z₀) (FormalMultilinearSeries.ofScalars ℂ c) z₀ (rad c) := by
  rw [psum_eq]
  have := ((FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall hR).comp_sub z₀
  rwa [zero_add] at this

lemma radius_ge_of_summable (c : ℕ → ℂ) (z₀ : ℂ) (r : ℝ≥0∞)
    (h : ∀ z : ℂ, edist z z₀ < r → Summable (fun k => c k * (z - z₀) ^ k)) : r ≤ rad c := by
  refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ => ?_
  have hs := h (z₀ + ρ) (by simpa [edist_dist, dist_eq_norm] using hρ)
  have h0 := hs.tendsto_atTop_zero.norm
  rw [norm_zero] at h0
  refine (FormalMultilinearSeries.ofScalars ℂ c).le_radius_of_tendsto (l := 0) ?_
  refine h0.congr fun n => ?_
  simp

/-- Beck Theorem 8.1.1 (CX-118). A power series with positive radius of convergence `R` is
holomorphic in the disk `D[z₀, R]`. -/
@[kb "beck2025" "Theorem 8.1.1, p. 130"]
theorem power_series_holomorphic (c : ℕ → ℂ) (z₀ : ℂ) (hR : 0 < rad c) :
    DifferentiableOn ℂ (psum c z₀) (eball z₀ (rad c)) :=
  (hasFPS c z₀ hR).differentiableOn

lemma hasSum_deriv_terms (c : ℕ → ℂ) (z₀ z : ℂ) (_hR : 0 < rad c) (hz : edist z z₀ < rad c) :
    HasSum (fun i : ℕ => (i : ℂ) * c i * (z - z₀) ^ (i - 1)) (deriv (psum c z₀) z) := by
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show (‖z - z₀‖₊ : ℝ≥0∞) < rad c by rw [edist_eq_enorm_sub] at hz; exact hz)
  have hs : Summable (fun k => ‖c k‖ * (r : ℝ) ^ k) := by
    have := (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow hr2
    simpa [FormalMultilinearSeries.ofScalars_norm] using this
  have hzU : z ∈ ball z₀ (r : ℝ) := by
    rw [mem_ball_iff_norm]
    exact_mod_cast hr1
  have key := Complex.hasSum_deriv_of_summable_norm (F := fun (k : ℕ) (w : ℂ) => c k * (w - z₀) ^ k)
    (U := ball z₀ (r : ℝ)) hs (fun i => by fun_prop) isOpen_ball
    (fun i w hw => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_iff_norm.1 hw).le i)
        (norm_nonneg _)) hzU
  have hd : ∀ i : ℕ, deriv (fun w : ℂ => c i * (w - z₀) ^ i) z = (i : ℂ) * c i * (z - z₀) ^ (i - 1) := by
    intro i
    have := (((hasDerivAt_id z).sub_const z₀).pow i).const_mul (c i)
    have h2 : HasDerivAt (fun w : ℂ => c i * (w - z₀) ^ i)
        (c i * ((i : ℂ) * (z - z₀) ^ (i - 1) * 1)) z := by simpa using this
    rw [h2.deriv]
    ring
  simp only [hd] at key
  exact key

/-- Beck Theorem 8.1.2 (CX-118). A power series with positive radius of convergence `R` can be
differentiated term by term in `D[z₀, R]`; the differentiated series has radius of convergence at
least `R` (Mathlib-shaped: the book's equality of radii needs the other inequality, which we do
not restate). -/
@[kb "beck2025" "Theorem 8.1.2, p. 131"]
theorem power_series_derivative (c : ℕ → ℂ) (z₀ : ℂ) (hR : 0 < rad c) :
    (∀ z ∈ eball z₀ (rad c),
      HasDerivAt (psum c z₀) (∑' k : ℕ, (k : ℂ) * c k * (z - z₀) ^ (k - 1)) z) ∧
    rad c ≤ rad (fun k => ((k : ℂ) + 1) * c (k + 1)) := by
  constructor
  · intro z hz
    have hz' : edist z z₀ < rad c := hz
    have hdiff : DifferentiableAt ℂ (psum c z₀) z :=
      (power_series_holomorphic c z₀ hR).differentiableAt (isOpen_eball.mem_nhds hz)
    rw [(hasSum_deriv_terms c z₀ z hR hz').tsum_eq]
    exact hdiff.hasDerivAt
  · refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ => ?_
    have hs := hasSum_deriv_terms c z₀ (z₀ + ρ) hR (by simpa [edist_dist, dist_eq_norm] using hρ)
    have h1 := (summable_nat_add_iff 1).2 hs.summable
    have h2 := h1.tendsto_atTop_zero.norm
    rw [norm_zero] at h2
    refine (FormalMultilinearSeries.ofScalars ℂ (fun k : ℕ => ((k : ℂ) + 1) * c (k + 1))).le_radius_of_tendsto (l := 0) ?_
    refine h2.congr fun n => ?_
    simp

/-- Beck Example 8.1.3 (CX-118). `∑ z^k / k! = exp z` for every `z`. -/
@[kb "beck2025" "Example 8.1.3, p. 131"]
theorem exp_power_series (z : ℂ) : HasSum (fun k : ℕ => z ^ k / (k ! : ℂ)) (Complex.exp z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp z
  rwa [← Complex.exp_eq_exp_ℂ] at h

/-- Beck Example 8.1.4 (CX-119). Power series of sine and cosine, from the exponential series. -/
@[kb "beck2025" "Example 8.1.4, p. 132"]
theorem sin_cos_power_series (z : ℂ) :
    HasSum (fun j : ℕ => (-1) ^ j * z ^ (2 * j + 1) / ((2 * j + 1)! : ℂ)) (Complex.sin z) ∧
    HasSum (fun j : ℕ => (-1) ^ j * z ^ (2 * j) / ((2 * j)! : ℂ)) (Complex.cos z) :=
  ⟨Complex.hasSum_sin z, Complex.hasSum_cos z⟩

/-- Beck Corollary 8.1.5 (CX-120). The coefficients of a power series with positive radius are
`c_k = f^(k)(z₀) / k!`. -/
@[kb "beck2025" "Corollary 8.1.5, p. 132"]
theorem power_series_coefficients (c : ℕ → ℂ) (z₀ : ℂ) (hR : 0 < rad c) (k : ℕ) :
    c k = iteratedDeriv k (psum c z₀) z₀ / (k ! : ℂ) := by
  have h := (hasFPS c z₀ hR).factorial_smul 1 k
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [← h]
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    nsmul_eq_mul]
  have : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
  field_simp

lemma hasFPSAt_of_hasSum (e : ℕ → ℂ) (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (F : ℂ → ℂ)
    (he : ∀ z ∈ ball z₀ r, HasSum (fun k => e k * (z - z₀) ^ k) (F z)) :
    HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ e) z₀ := by
  have hle : ENNReal.ofReal r ≤ rad e := by
    refine radius_ge_of_summable e z₀ _ fun z hz => (he z ?_).summable
    exact mem_ball.2 (edist_lt_ofReal.1 hz)
  refine ⟨ENNReal.ofReal r, ⟨hle, by simpa using hr, ?_⟩⟩
  intro y hy
  have hy' : y ∈ ball (0 : ℂ) r := mem_ball.2 (edist_lt_ofReal.1 (mem_eball.1 hy))
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
    he (z₀ + y) (by simpa using hy')

/-- Beck Corollary 8.1.6 (CX-120). Two power series centered at `z₀` that sum to the same function
on a disk about `z₀` have the same coefficients. -/
@[kb "beck2025" "Corollary 8.1.6, p. 132"]
theorem power_series_unique (c d : ℕ → ℂ) (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (F : ℂ → ℂ)
    (hc : ∀ z ∈ ball z₀ r, HasSum (fun k => c k * (z - z₀) ^ k) (F z))
    (hd : ∀ z ∈ ball z₀ r, HasSum (fun k => d k * (z - z₀) ^ k) (F z)) : c = d := by
  have := (hasFPSAt_of_hasSum c z₀ r hr F hc).eq_formalMultilinearSeries
    (hasFPSAt_of_hasSum d z₀ r hr F hd)
  exact (FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ) this

/-- Beck Theorem 8.1.8 (CX-122). Taylor's theorem: a function holomorphic in the disk `D[z₀, R]`
equals its Taylor series there (so the radius of convergence is at least `R`), and the
coefficients are given by Cauchy's integrals over any circle `C[z₀, r]`, `0 < r < R`. -/
@[kb "beck2025" "Theorem 8.1.8, p. 133"]
theorem taylor_theorem (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hf : DifferentiableOn ℂ f (ball z₀ R)) :
    (∀ z ∈ ball z₀ R,
      HasSum (fun k : ℕ => (iteratedDeriv k f z₀ / (k ! : ℂ)) * (z - z₀) ^ k) (f z)) ∧
    (∀ r : ℝ, 0 < r → r < R → ∀ k : ℕ, iteratedDeriv k f z₀ / (k ! : ℂ) =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(z₀, r), f w / (w - z₀) ^ (k + 1)) := by
  refine ⟨fun z hz => ?_, fun r hr0 hrR k => ?_⟩
  · have := Complex.hasSum_taylorSeries_on_ball hf hz
    convert this using 1
    funext k
    simp only [smul_eq_mul]
    ring
  · lift r to ℝ≥0 using hr0.le
    have hd : DifferentiableOn ℂ f (closedBall z₀ r) := hf.mono (closedBall_subset_ball hrR)
    have hp := hd.hasFPowerSeriesOnBall (NNReal.coe_pos.1 hr0)
    have h := hp.factorial_smul 1 k
    rw [cauchyPowerSeries_apply, ← iteratedDeriv_eq_iteratedFDeriv] at h
    have e : (fun w : ℂ => (1 / (w - z₀)) ^ k • (w - z₀)⁻¹ • f w) =
        fun w => f w / (w - z₀) ^ (k + 1) := by
      funext w
      simp only [smul_eq_mul, div_eq_mul_inv, pow_succ, mul_inv]
      ring
    have e2 : (∮ w in C(z₀, r), (1 / (w - z₀)) ^ k • (w - z₀)⁻¹ • f w) =
        ∮ w in C(z₀, r), f w / (w - z₀) ^ (k + 1) := by
      rw [e]
    rw [e2] at h
    rw [← h]
    have : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    simp only [nsmul_eq_mul, smul_eq_mul]
    field_simp

/-- Beck Corollary 8.1.10 (CX-123). A function holomorphic on an open set `G` is represented by its
Taylor series at `z₀ ∈ G` in every point closer to `z₀` than the distance of `z₀` to `∂G`. -/
@[kb "beck2025" "Corollary 8.1.10, p. 134"]
theorem taylor_radius_at_least_distance_to_boundary (G : Set ℂ) (hG : IsOpen G) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f G) (z₀ : ℂ) (hz₀ : z₀ ∈ G) :
    ∀ z : ℂ, edist z z₀ < infEDist z₀ (frontier G) →
      HasSum (fun k : ℕ => (iteratedDeriv k f z₀ / (k ! : ℂ)) * (z - z₀) ^ k) (f z) := by
  intro z hz
  set d := infEDist z₀ (frontier G) with hd
  have hsub : eball z₀ d ⊆ G := by
    intro y hy
    have hdpos : 0 < d := lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ _) (mem_eball.1 hy)
    have hconn : IsPreconnected (eball z₀ d) := isPreconnected_eball
    have hz0 : z₀ ∈ eball z₀ d := by simpa [mem_eball] using hdpos
    have hdisj : Disjoint G (closure G)ᶜ := disjoint_compl_right.mono_left subset_closure
    have hcov : eball z₀ d ⊆ G ∪ (closure G)ᶜ := by
      intro y hy
      by_contra hcon
      simp only [mem_union, not_or] at hcon
      have hfr : y ∈ frontier G := by
        rw [frontier, hG.interior_eq]
        exact ⟨by simpa using hcon.2, hcon.1⟩
      have := infEDist_le_edist_of_mem (x := z₀) hfr
      rw [edist_comm] at this
      exact absurd (mem_eball.1 hy) (not_lt.2 this)
    exact hconn.subset_left_of_subset_union hG isClosed_closure.isOpen_compl hdisj hcov
      ⟨z₀, hz0, hz₀⟩ hy
  have hdiff : DifferentiableOn ℂ f (eball z₀ d) := hf.mono hsub
  have := Complex.hasSum_taylorSeries_on_eball hdiff (mem_eball.2 hz)
  convert this using 1
  funext k
  simp only [smul_eq_mul]
  ring

/-- Beck Example 8.1.11 (CX-123). The function `1 / (z² + 1)` has the power series
`∑ (-1)^k z^(2k)` at `0`, converging for `|z| < 1`. -/
@[kb "beck2025" "Example 8.1.11, p. 134"]
theorem inv_sq_add_one_series (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (-1) ^ k * z ^ (2 * k)) (1 / (z ^ 2 + 1)) := by
  have h : ‖-z ^ 2‖ < 1 := by
    rw [norm_neg, norm_pow]
    nlinarith [norm_nonneg z]
  have := hasSum_geometric_of_norm_lt_one h
  convert this using 1
  · funext k
    rw [neg_pow (z ^ 2), pow_mul]
  · rw [one_div, sub_neg_eq_add, add_comm]

/-- Beck Definition 8.1.14 and Theorem 8.1.15 (CX-124). On an open set, a function is analytic
(near every point it is the sum of a power series in a disk) iff it is holomorphic. -/
@[kb "beck2025" "Theorem 8.1.15, p. 135"]
theorem analytic_iff_holomorphic (G : Set ℂ) (hG : IsOpen G) (f : ℂ → ℂ) :
    (∀ z₀ ∈ G, ∃ R > 0, ∃ c : ℕ → ℂ,
      ∀ z ∈ ball z₀ R, HasSum (fun k => c k * (z - z₀) ^ k) (f z)) ↔ DifferentiableOn ℂ f G := by
  constructor
  · intro h z₀ hz₀
    obtain ⟨R, hR, c, hc⟩ := h z₀ hz₀
    exact (hasFPSAt_of_hasSum c z₀ R hR f hc).analyticAt.differentiableAt.differentiableWithinAt
  · intro hf z₀ hz₀
    obtain ⟨R, hR, hRG⟩ := Metric.isOpen_iff.1 hG z₀ hz₀
    refine ⟨R, hR, fun k => iteratedDeriv k f z₀ / (k ! : ℂ), fun z hz => ?_⟩
    exact (taylor_theorem f z₀ R (hf.mono hRG)).1 z hz

/-- Beck Theorem 8.2.1 (CX-125). Classification of zeros: for `f` holomorphic on a region `G` with
`f a = 0`, either `f` vanishes on a disk about `a`, or `f = (z - a)^m g` on `G` with `m ≥ 1`,
`g` holomorphic on `G`, `g a ≠ 0`, and `a` is an isolated zero. -/
@[kb "beck2025" "Theorem 8.2.1, p. 135"]
theorem classification_of_zeros (G : Set ℂ) (hG : IsOpen G) (_hC : IsConnected G) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f G) (a : ℂ) (ha : a ∈ G) (hfa : f a = 0) :
    (∃ r > 0, ∀ z ∈ ball a r, f z = 0) ∨
    (∃ m : ℕ, 0 < m ∧ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g G ∧ g a ≠ 0 ∧
      (∀ z ∈ G, f z = (z - a) ^ m * g z) ∧ ∃ r > 0, ∀ z ∈ ball a r, z ≠ a → f z ≠ 0) := by
  have hA : AnalyticAt ℂ f a := (hf.analyticOnNhd hG) a ha
  by_cases htop : analyticOrderAt f a = ⊤
  · left
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.1 (analyticOrderAt_eq_top.1 htop)
    exact ⟨r, hr, h⟩
  · right
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 htop
    obtain ⟨g', hg'a, hg'0, hev⟩ := (hA.analyticOrderAt_eq_natCast (n := m)).1 hm.symm
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        have := hev.self_of_nhds
        rw [h0, hfa] at this
        simp at this
        exact hg'0 this.symm
      · exact h0
    let g : ℂ → ℂ := fun z => if z = a then g' a else f z / (z - a) ^ m
    have hga : g =ᶠ[𝓝 a] g' := by
      filter_upwards [hev] with z hz
      by_cases hza : z = a
      · simp [g, hza]
      · simp only [g, hza, ite_false]
        rw [hz]
        have : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hza)
        simp only [smul_eq_mul]
        field_simp
    have hgdiff : DifferentiableOn ℂ g G := by
      intro z hz
      by_cases hza : z = a
      · subst hza
        exact (hg'a.differentiableAt.congr_of_eventuallyEq hga).differentiableWithinAt
      · have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (hG.mem_nhds hz)
        have hev2 : g =ᶠ[𝓝 z] fun w => f w / (w - a) ^ m := by
          filter_upwards [isOpen_ne.mem_nhds hza] with w hw
          simp [g, hw]
        have hne : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hza)
        refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.congr_of_eventuallyEq ?_ hev2)
        exact hfz.div (by fun_prop) hne
    have hfg : ∀ z ∈ G, f z = (z - a) ^ m * g z := by
      intro z hz
      by_cases hza : z = a
      · subst hza
        simp [hfa, hmpos.ne']
      · have : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hza)
        simp only [g, hza, ite_false]
        field_simp
    have hga0 : g a ≠ 0 := by simpa [g] using hg'0
    refine ⟨m, hmpos, g, hgdiff, hga0, hfg, ?_⟩
    have hgc : ContinuousAt g a := (hgdiff.differentiableAt (hG.mem_nhds ha)).continuousAt
    have hev3 : ∀ᶠ z in 𝓝 a, g z ≠ 0 ∧ z ∈ G :=
      (hgc.eventually_ne hga0).and (hG.mem_nhds ha)
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.1 hev3
    refine ⟨r, hr, fun z hz hza => ?_⟩
    obtain ⟨h1, h2⟩ := h z hz
    rw [hfg z h2]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hza)) h1

/-- Beck Theorem 8.2.2 (CX-126). Identity theorem: a function holomorphic on a region `G` that
vanishes on a sequence of distinct points converging to a point of `G` is zero on `G`. -/
@[kb "beck2025" "Theorem 8.2.2, p. 136"]
theorem identity_theorem (G : Set ℂ) (hG : IsOpen G) (hC : IsConnected G) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f G) (a : ℕ → ℂ) (hinj : Function.Injective a) (_hmem : ∀ n, a n ∈ G)
    (w : ℂ) (hw : w ∈ G) (hlim : Tendsto a atTop (𝓝 w)) (hz : ∀ n, f (a n) = 0) :
    ∀ z ∈ G, f z = 0 := by
  have hne : ∀ᶠ n in atTop, a n ≠ w := by
    by_cases h : ∃ n₀, a n₀ = w
    · obtain ⟨n₀, hn₀⟩ := h
      filter_upwards [eventually_ne_atTop n₀] with n hn h2
      exact hn (hinj (h2.trans hn₀.symm))
    · simp only [not_exists] at h
      exact Eventually.of_forall h
  have hlim' : Tendsto a atTop (𝓝[≠] w) := tendsto_nhdsWithin_iff.2 ⟨hlim, hne⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] w, f z = 0 := hlim'.frequently (Eventually.of_forall hz).frequently
  exact fun z hzG => (hf.analyticOnNhd hG).eqOn_zero_of_preconnected_of_frequently_eq_zero
    hC.isPreconnected hw hfreq hzG

/-- Beck Corollary 8.2.3 (CX-126). Two functions holomorphic on a region `G` that agree on a
sequence `a_k ≠ w` converging to `w ∈ G` agree on `G`. -/
@[kb "beck2025" "Corollary 8.2.3, p. 136"]
theorem identity_theorem_two_functions (G : Set ℂ) (hG : IsOpen G) (hC : IsConnected G)
    (f g : ℂ → ℂ) (hf : DifferentiableOn ℂ f G) (hg : DifferentiableOn ℂ g G) (a : ℕ → ℂ)
    (w : ℂ) (hw : w ∈ G) (hlim : Tendsto a atTop (𝓝 w)) (hne : ∀ k, a k ≠ w)
    (heq : ∀ k, f (a k) = g (a k)) : ∀ z ∈ G, f z = g z := by
  have hlim' : Tendsto a atTop (𝓝[≠] w) := tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] w, f z = g z := hlim'.frequently (Eventually.of_forall heq).frequently
  exact fun z hzG => (hf.analyticOnNhd hG).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hG) hC.isPreconnected hw hfreq hzG

/-- Beck Theorem 8.2.4 (CX-127). Maximum-modulus theorem: a nonconstant holomorphic function on a
region has no weak relative maximum of `|f|`. -/
@[kb "beck2025" "Theorem 8.2.4, p. 137"]
theorem maximum_modulus (G : Set ℂ) (hG : IsOpen G) (hC : IsConnected G) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f G) (hnc : ¬ ∃ c : ℂ, ∀ z ∈ G, f z = c) :
    ¬ ∃ w ∈ G, ∃ r > 0, closedBall w r ⊆ G ∧ ∀ z ∈ closedBall w r, ‖f z‖ ≤ ‖f w‖ := by
  rintro ⟨w, hw, r, hr, hsub, hmax⟩
  have hd : ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ f z :=
    Filter.mem_of_superset (hG.mem_nhds hw) fun z hz => hf.differentiableAt (hG.mem_nhds hz)
  have hloc : IsLocalMax (norm ∘ f) w :=
    Filter.mem_of_superset (closedBall_mem_nhds w hr) fun z hz => hmax z hz
  have hev := Complex.eventually_eq_of_isLocalMax_norm hd hloc
  have hall := (hf.analyticOnNhd hG).eqOn_of_preconnected_of_eventuallyEq
    (g := fun _ => f w) (fun z _ => analyticAt_const) hC.isPreconnected hw hev
  exact hnc ⟨f w, hall⟩

/-- Beck Corollary 8.2.5 (CX-128). If `f` is holomorphic in a bounded (nonempty) region `G` and
continuous on its closure, then `sup_{z ∈ G} |f z|` is attained as a maximum over the boundary. -/
@[kb "beck2025" "Corollary 8.2.5, p. 137"]
theorem sup_on_boundary (G : Set ℂ) (hb : Bornology.IsBounded G) (hne : G.Nonempty) (f : ℂ → ℂ)
    (hd : DiffContOnCl ℂ f G) :
    ∃ z₀ ∈ frontier G, (∀ z ∈ frontier G, ‖f z‖ ≤ ‖f z₀‖) ∧
      sSup ((fun z => ‖f z‖) '' G) = ‖f z₀‖ := by
  obtain ⟨z₀, hz₀, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hb hne hd
  refine ⟨z₀, hz₀, fun z hz => hmax (frontier_subset_closure hz), ?_⟩
  have hup : ∀ y ∈ (fun z => ‖f z‖) '' G, y ≤ ‖f z₀‖ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hmax (subset_closure hz)
  apply le_antisymm
  · exact csSup_le (hne.image _) hup
  · have hcl : z₀ ∈ closure G := frontier_subset_closure hz₀
    obtain ⟨s, hsG, hs⟩ := mem_closure_iff_seq_limit.1 hcl
    have hcont : Tendsto (fun n => ‖f (s n)‖) atTop (𝓝 ‖f z₀‖) :=
      ((hd.continuousOn.norm).continuousWithinAt hcl).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hs, Eventually.of_forall fun n => subset_closure (hsG n)⟩)
    refine le_of_tendsto' hcont fun n => ?_
    exact le_csSup ⟨‖f z₀‖, hup⟩ ⟨s n, hsG n, rfl⟩

/-- Beck, Weierstraß convergence theorem, §8.4 (CX-159; Exercises 8.4.7 and 8.4.8). If holomorphic
functions `f_n` converge uniformly on an open set `G` to `f`, then `f` is holomorphic and all the
derivatives `f_n^(k)` converge to `f^(k)` at every point of `G`. -/
@[kb "beck2025" "Weierstrass convergence theorem §8.4, p. 142"]
theorem weierstrass_convergence (G : Set ℂ) (hG : IsOpen G) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) G) (hu : TendstoUniformlyOn F f atTop G) :
    DifferentiableOn ℂ f G ∧
      ∀ k : ℕ, ∀ z ∈ G, Tendsto (fun n => iteratedDeriv k (F n) z) atTop (𝓝 (iteratedDeriv k f z)) := by
  have key : ∀ k : ℕ, ∀ (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ), (∀ n, DifferentiableOn ℂ (F n) G) →
      TendstoLocallyUniformlyOn F f atTop G →
      TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n)) (iteratedDeriv k f) atTop G := by
    intro k
    induction k with
    | zero => intro F f _ h; simpa using h
    | succ k ih =>
      intro F f hF' h
      have h1 := h.deriv (Eventually.of_forall hF') hG
      have h2 := ih (fun n => deriv (F n)) (deriv f)
        (fun n => (hF' n).deriv hG) h1
      simpa [iteratedDeriv_succ'] using h2
  have hl := hu.tendstoLocallyUniformlyOn
  refine ⟨hl.differentiableOn (Eventually.of_forall hF) hG, fun k z hz => ?_⟩
  exact (key k F f hF hl).tendsto_at hz

/-- Beck Definition 8.1.9 (CX-123). For an open proper region G and z0 in G, the distance from z0
to the boundary is positive and the disc of that radius about z0 lies in G. -/
@[kb "beck2025" "Definition 8.1.9, p. 134"]
theorem disc_of_distance_to_boundary (G : Set ℂ) (hG : IsOpen G) (z₀ : ℂ) (hz : z₀ ∈ G)
    (hne : Gᶜ.Nonempty) :
    0 < Metric.infDist z₀ Gᶜ ∧ Metric.ball z₀ (Metric.infDist z₀ Gᶜ) ⊆ G := by
  refine ⟨?_, fun z hzb => ?_⟩
  · exact (hG.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa using hz)
  · by_contra hzG
    have := Metric.infDist_le_dist_of_mem (x := z₀) (show z ∈ Gᶜ from hzG)
    rw [Metric.mem_ball] at hzb
    rw [dist_comm] at hzb
    linarith

/-- Beck Definition 8.1.14 (CX-124). f is analytic at z0 iff it has a power series expansion on
some disc of positive radius about z0. -/
@[kb "beck2025" "Definition 8.1.14, p. 135"]
theorem analyticAt_iff_power_series_on_disc (f : ℂ → ℂ) (z₀ : ℂ) :
    AnalyticAt ℂ f z₀ ↔
      ∃ (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ENNReal),
        0 < r ∧ HasFPowerSeriesOnBall f p z₀ r :=
  ⟨fun ⟨_, _, h⟩ => ⟨_, _, h.r_pos, h⟩, fun ⟨_, _, _, h⟩ => ⟨_, _, h⟩⟩

/-- Beck Multiplicity of a zero, §8.2 (CX-125). An analytic f has a zero of multiplicity m at a iff
near a, f = (z - a)^m g with g analytic and g(a) nonzero. -/
@[kb "beck2025" "Multiplicity of a zero §8.2, p. 135"]
theorem zero_multiplicity_iff (f : ℂ → ℂ) (a : ℂ) (hf : AnalyticAt ℂ f a) (m : ℕ) :
    analyticOrderAt f a = (m : ℕ∞) ↔
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧ ∀ᶠ z in 𝓝 a, f z = (z - a) ^ m • g z :=
  hf.analyticOrderAt_eq_natCast

end UndergradKB.ComplexAnalysis.Course.Beck8
