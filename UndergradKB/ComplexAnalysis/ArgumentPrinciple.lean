import UndergradKB.ComplexAnalysis.ResidueTheorem
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The argument principle and Rouché's theorem for a circle

Beck et al., *A First Course in Complex Analysis*, Section 9.3 (checklist rows CX-144, CX-145), for the path a circle.

* `residue_logDeriv`: at a point where the meromorphic function `f` has order `n` (a zero of multiplicity `n > 0`,
  a pole of order `-n`, or neither when `n = 0`), the residue of `f'/f` is `n`.
* `argument_principle_circle` (Theorem 9.3.2): if `f` is holomorphic and nonzero on the closed disc except at finitely
  many points of the open disc, where it is meromorphic, then `(2πi)⁻¹ ∮ f'/f` is the sum of the orders of `f` at those
  points: the number of zeros minus the number of poles, counted with multiplicity.
* `zeros_count_circle`: for `f` holomorphic on (a neighbourhood of) the closed disc and nonzero on the circle,
  `(2πi)⁻¹ ∮ f'/f` is the number of zeros inside, counted with multiplicity.
* `rouche_circle` (Theorem 9.3.3): if `|g| < |f|` on the circle, `f + g` and `f` have the same number of zeros
  inside, counted with multiplicity. The proof uses that `(f+g)/f` takes values in the disc `|w - 1| < 1` on the
  circle, so `log ((f+g)/f)` is a primitive of `(f+g)'/(f+g) - f'/f` there.
-/

open Complex Metric Set Filter Topology Real

namespace UndergradKB.ComplexAnalysis

/-- At a point where the meromorphic function `f` has order `n`, the residue of the logarithmic derivative `f'/f`
is `n` (Beck, proof of Theorem 9.3.2). -/
theorem residue_logDeriv {f : ℂ → ℂ} {s : ℂ} {n : ℤ} (hf : MeromorphicAt f s)
    (hn : meromorphicOrderAt f s = n) : residue (fun z => deriv f z / f z) s = n := by
  obtain ⟨g, hga, hg0, hev⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  have H : ∀ᶠ z in 𝓝 s, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ (z ≠ s → f z = (z - s) ^ n * g z) := by
    refine hga.eventually_analyticAt.and ((hga.continuousAt.eventually_ne hg0).and ?_)
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with z hz hzs
    simpa only [smul_eq_mul] using hz hzs
  obtain ⟨ε, hε, hεH⟩ := Metric.eventually_nhds_iff_ball.1 H
  set ψ : ℂ → ℂ := fun y => n + (y - s) * deriv g y / g y
  have hψ : DifferentiableOn ℂ ψ (ball s ε) := by
    intro y hy
    obtain ⟨hgy, hgy0, -⟩ := hεH y hy
    refine (DifferentiableAt.add (differentiableAt_const _) ?_).differentiableWithinAt
    exact ((differentiableAt_id.sub_const s).mul hgy.deriv.differentiableAt).div
      hgy.differentiableAt hgy0
  have heq : ∀ z ∈ ball s ε \ {s}, deriv f z / f z = ψ z / (z - s) ^ (0 + 1) := by
    intro z ⟨hz, hzs⟩
    have hzs' : z - s ≠ 0 := sub_ne_zero.2 hzs
    obtain ⟨hgz, hgz0, -⟩ := hεH z hz
    have hopen : IsOpen (ball s ε \ {s}) := isOpen_ball.sdiff isClosed_singleton
    have hloc : f =ᶠ[𝓝 z] fun y => (y - s) ^ n * g y :=
      eventually_of_mem (hopen.mem_nhds ⟨hz, hzs⟩) fun y ⟨hy, hys⟩ => (hεH y hy).2.2 hys
    have hd : HasDerivAt (fun y => (y - s) ^ n * g y)
        ((n * (z - s) ^ (n - 1)) * g z + (z - s) ^ n * deriv g z) z := by
      have h1 : HasDerivAt (fun y => (y - s) ^ n) (n * (z - s) ^ (n - 1)) z := by
        have := (hasDerivAt_zpow n (z - s) (Or.inl hzs')).comp z ((hasDerivAt_id z).sub_const s)
        convert this using 1
        · rfl
        · rw [mul_one]
      exact h1.mul hgz.differentiableAt.hasDerivAt
    rw [hloc.deriv_eq, hd.deriv, (hεH z hz).2.2 hzs]
    simp only [ψ, zero_add, pow_one]
    rw [zpow_sub_one₀ hzs']
    have : (z - s) ^ n ≠ 0 := zpow_ne_zero n hzs'
    field_simp
  rw [residue_of_eq_div_pow hε hψ 0 heq]
  simp [ψ]

/-- Beck Theorem 9.3.2 (CX-144), **the argument principle**, for the path a circle: let `f` be holomorphic and
nonzero at every point of the closed disc `|z - c| ≤ R` outside a finite set `S` of points of the open disc, and
meromorphic (not identically zero) at the points of `S`. Then `(2πi)⁻¹ ∮_{|z-c|=R} f'/f` is the sum over `S` of the
orders of `f`, that is, the number of zeros of `f` inside the circle minus the number of its poles, both counted
with multiplicity. -/
@[kb "beck2025" "Theorem 9.3.2, p. 158"]
theorem argument_principle_circle {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} (hR : 0 < R)
    (hS : ∀ s ∈ S, s ∈ ball c R) (hf : ∀ z ∈ closedBall c R \ (S : Set ℂ), AnalyticAt ℂ f z)
    (hf0 : ∀ z ∈ closedBall c R \ (S : Set ℂ), f z ≠ 0) (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hord : ∀ s ∈ S, meromorphicOrderAt f s ≠ ⊤) :
    (2 * π * I)⁻¹ * (∮ z in C(c, R), deriv f z / f z) =
      ∑ s ∈ S, ((meromorphicOrderAt f s).untop₀ : ℂ) := by
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (closedBall c R \ (S : Set ℂ)) :=
    fun z hz => ((hf z hz).deriv.differentiableAt.div (hf z hz).differentiableAt
      (hf0 z hz)).differentiableWithinAt
  rw [residue_theorem_circle hR hS hd, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  refine Finset.sum_congr rfl fun s hs => residue_logDeriv (hmero s hs) ?_
  exact (WithTop.coe_untop₀_of_ne_top (hord s hs)).symm

/-- A function holomorphic at every point of a closed disc and nonzero on its boundary circle has finitely many
zeros in the disc, each of finite order. -/
theorem finite_zeros_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall c R, AnalyticAt ℂ f z) (hf0 : ∀ z ∈ sphere c R, f z ≠ 0) :
    {z | z ∈ closedBall c R ∧ f z = 0}.Finite ∧ ∀ z ∈ closedBall c R, analyticOrderAt f z ≠ ⊤ := by
  have hord : ∀ z ∈ closedBall c R, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    have h0 : f =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.1 htop
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (U := closedBall c R) hf (convex_closedBall c R).isPreconnected hz h0
    have hmem : c + R ∈ sphere c R := by
      rw [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR]
    exact hf0 _ hmem (hall (sphere_subset_closedBall hmem))
  refine ⟨?_, hord⟩
  have hcl : IsClosed {z | z ∈ closedBall c R ∧ f z = 0} := by
    have hcont : ContinuousOn f (closedBall c R) := fun z hz =>
      (hf z hz).continuousAt.continuousWithinAt
    exact hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  refine (isCompact_closedBall c R |>.of_isClosed_subset hcl fun z hz => hz.1).finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  rcases (hf z hz.1).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (analyticOrderAt_eq_top.2 h) (hord z hz.1)
  · rw [← disjoint_iff, disjoint_principal_right]
    filter_upwards [h] with w hw hw' using hw hw'.2

/-- The number of zeros, counted with multiplicity, of `f` in the open disc `|z - c| < R`. -/
noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℕ :=
  ∑ᶠ z ∈ ball c R, analyticOrderNatAt f z

/-- The argument principle for a function holomorphic on a closed disc and nonzero on its boundary circle:
`(2πi)⁻¹ ∮ f'/f` is the number of zeros inside, counted with multiplicity (Beck Theorem 9.3.2 without poles). -/
@[kb "beck2025" "Theorem 9.3.2, p. 158"]
theorem argument_principle_zeroCount {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall c R, AnalyticAt ℂ f z) (hf0 : ∀ z ∈ sphere c R, f z ≠ 0) :
    (2 * π * I)⁻¹ * (∮ z in C(c, R), deriv f z / f z) = zeroCount f c R := by
  obtain ⟨hfin, hord⟩ := finite_zeros_closedBall hR hf hf0
  set S := hfin.toFinset
  have hmemS : ∀ z, z ∈ S ↔ z ∈ closedBall c R ∧ f z = 0 := fun z => hfin.mem_toFinset
  have hSball : ∀ s ∈ S, s ∈ ball c R := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := (hmemS s).1 hs
    rw [mem_ball, ← Ne.le_iff_lt]
    · exact mem_closedBall.1 hs1
    · intro h; exact hf0 s (mem_sphere.2 h) hs2
  rw [argument_principle_circle hR hSball (fun z hz => hf z hz.1)
    (fun z hz h0 => hz.2 ((hmemS z).2 ⟨hz.1, h0⟩)) (fun s hs => (hf s ((hmemS s).1 hs).1).meromorphicAt)
    (fun s hs => by
      rw [(hf s ((hmemS s).1 hs).1).meromorphicOrderAt_eq]
      intro h
      exact hord s ((hmemS s).1 hs).1 (by simpa using h))]
  have hsupp : ball c R ∩ Function.support (fun z => analyticOrderNatAt f z) =
      ↑S ∩ Function.support (fun z => analyticOrderNatAt f z) := by
    ext z
    simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hne⟩
      refine ⟨(hmemS z).2 ⟨ball_subset_closedBall hz, ?_⟩, hne⟩
      by_contra h0
      exact hne (by simp [analyticOrderNatAt, (hf z (ball_subset_closedBall hz)).analyticOrderAt_eq_zero.2 h0])
    · rintro ⟨hz, hne⟩
      exact ⟨hSball z hz, hne⟩
  unfold zeroCount
  rw [finsum_mem_eq_sum_of_inter_support_eq _ hsupp, Nat.cast_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs1 := ((hmemS s).1 hs).1
  rw [(hf s hs1).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt (hord s hs1)]
  simp

/-- Beck Theorem 9.3.3 (CX-145), **Rouché's theorem**, for the path a circle: if `f` and `g` are holomorphic on the
closed disc `|z - c| ≤ R` and `|g| < |f|` on the circle `|z - c| = R`, then `f + g` and `f` have the same number of
zeros inside the circle, counted with multiplicity. -/
@[kb "beck2025" "Theorem 9.3.3, p. 159"]
theorem rouche_circle {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall c R, AnalyticAt ℂ f z) (hg : ∀ z ∈ closedBall c R, AnalyticAt ℂ g z)
    (hlt : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    zeroCount (fun z => f z + g z) c R = zeroCount f c R := by
  have hf0 : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz h => by
    have := hlt z hz; rw [h, norm_zero] at this; exact absurd this (not_lt.2 (norm_nonneg _))
  have hfg : ∀ z ∈ closedBall c R, AnalyticAt ℂ (fun z => f z + g z) z := fun z hz =>
    (hf z hz).add (hg z hz)
  have hfg0 : ∀ z ∈ sphere c R, f z + g z ≠ 0 := fun z hz h => by
    have := hlt z hz
    rw [add_eq_zero_iff_eq_neg.1 h, norm_neg] at this; exact lt_irrefl _ this
  have key : (∮ z in C(c, R), deriv (fun z => f z + g z) z / (f z + g z)) =
      ∮ z in C(c, R), deriv f z / f z := by
    have hint : ∀ F : ℂ → ℂ, (∀ z ∈ closedBall c R, AnalyticAt ℂ F z) → (∀ z ∈ sphere c R, F z ≠ 0) →
        CircleIntegrable (fun z => deriv F z / F z) c R := fun F hF hF0 =>
      ContinuousOn.circleIntegrable hR.le fun z hz =>
        ((hF z (sphere_subset_closedBall hz)).deriv.continuousAt.div
          (hF z (sphere_subset_closedBall hz)).continuousAt (hF0 z hz)).continuousWithinAt
    rw [← sub_eq_zero, ← circleIntegral.integral_sub (hint _ hfg hfg0) (hint _ hf hf0)]
    refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt'
      (f := fun z => log ((f z + g z) / f z)) fun z hz => ?_
    rw [abs_of_pos hR] at hz
    have hzb := sphere_subset_closedBall hz
    have hfz := hf0 z hz
    have hfgz := hfg0 z hz
    have hh : HasDerivAt (fun z => (f z + g z) / f z)
        ((deriv (fun z => f z + g z) z * f z - (f z + g z) * deriv f z) / f z ^ 2) z :=
      (hfg z hzb).differentiableAt.hasDerivAt.div (hf z hzb).differentiableAt.hasDerivAt hfz
    have hslit : (f z + g z) / f z ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left
      have h1 : (f z + g z) / f z = 1 + g z / f z := by field_simp
      have h2 : ‖g z / f z‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.2 hfz)]; exact hlt z hz
      rw [h1, add_re, one_re]
      linarith [neg_abs_le (g z / f z).re, abs_re_le_norm (g z / f z)]
    refine (hh.clog hslit).hasDerivWithinAt.congr_deriv ?_
    field_simp
  have e1 := argument_principle_zeroCount hR hfg hfg0
  have e2 := argument_principle_zeroCount hR hf hf0
  rw [key, e2] at e1
  exact_mod_cast e1.symm

end UndergradKB.ComplexAnalysis
