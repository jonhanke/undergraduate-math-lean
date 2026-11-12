import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness
import UndergradKB.Common.Attr

/-! # Maximum principle for harmonic functions (rows CX-087, CX-089, CX-129)

For a real harmonic function `u : ℂ → ℝ` we prove: it has no strong relative extremum, a weak
relative extremum at a point of a region forces `u` to be constant on the region, and on a bounded
region a harmonic function that is continuous on the closure is controlled by its boundary values
(zero boundary values give zero; uniqueness for the Dirichlet problem).

The key step: on a disc where `u ≤ u z₀`, write `u = Re F` with `F` holomorphic (Mathlib's
harmonic conjugate on a ball) and apply the maximum modulus principle to `exp ∘ F`, whose modulus
is `exp ∘ u`.  Passing from the disc to the region uses real analyticity of harmonic functions
and the identity theorem. -/

namespace UndergradKB.ComplexAnalysis

open Metric Set InnerProductSpace

/-- Beck Definition 6.2.2 (CX-087). `u` has a strong relative maximum at `z₀`: it is strictly
smaller than `u z₀` at all other points of some disc around `z₀`. -/
@[kb "beck2025" "Definition 6.2.2, p. 106"]
def HasStrongRelMax (u : ℂ → ℝ) (z₀ : ℂ) : Prop :=
  ∃ r > 0, ∀ z, z ≠ z₀ → dist z z₀ < r → u z < u z₀

/-- Beck Definition 6.2.2 (CX-087). `u` has a strong relative minimum at `z₀`. -/
@[kb "beck2025" "Definition 6.2.2, p. 106"]
def HasStrongRelMin (u : ℂ → ℝ) (z₀ : ℂ) : Prop :=
  ∃ r > 0, ∀ z, z ≠ z₀ → dist z z₀ < r → u z₀ < u z

/-- On a disc where a harmonic function is bounded above by its central value, it is constant. -/
theorem harmonic_const_of_le_center {u : ℂ → ℝ} {z₀ : ℂ} {r : ℝ}
    (hu : HarmonicOnNhd u (ball z₀ r)) (hmax : ∀ z ∈ ball z₀ r, u z ≤ u z₀) :
    ∀ z ∈ ball z₀ r, u z = u z₀ := by
  intro z hz
  have hr : z₀ ∈ ball z₀ r := by
    have : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.1 hz)
    simpa using this
  obtain ⟨F, hF, hFu⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hu
  have hd : DifferentiableOn ℂ (fun w => Complex.exp (F w)) (ball z₀ r) := fun w hw =>
    (((hF w hw).differentiableAt).cexp).differentiableWithinAt
  have hm : IsMaxOn (norm ∘ fun w => Complex.exp (F w)) (ball z₀ r) z₀ := by
    intro w hw
    simp only [mem_ofPred_eq, Function.comp, Complex.norm_exp]
    have e1 : (F w).re = u w := hFu hw
    have e2 : (F z₀).re = u z₀ := hFu hr
    rw [e1, e2]
    exact Real.exp_le_exp.2 (hmax w hw)
  have := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z₀ r).isPreconnected
    isOpen_ball hd hr hm hz
  have h2 := congrArg norm this
  simp only [Function.const_apply, Complex.norm_exp] at h2
  have e1 : (F z).re = u z := hFu hz
  have e2 : (F z₀).re = u z₀ := hFu hr
  rw [e1, e2] at h2
  exact Real.exp_injective h2

/-- Weak relative maximum on a region forces constancy: the general form (hypotheses on a
possibly non-connected open set, conclusion on the connected open set `G`). -/
theorem harmonic_const_of_weak_max {G : Set ℂ} {u : ℂ → ℝ} {z₀ : ℂ}
    (hGo : IsOpen G) (hGc : IsConnected G) (hu : HarmonicOnNhd u G) (hz₀ : z₀ ∈ G)
    (hmax : ∃ r > 0, ∀ z, dist z z₀ < r → u z ≤ u z₀) :
    ∀ z ∈ G, u z = u z₀ := by
  obtain ⟨r, hr, hr'⟩ := hmax
  obtain ⟨ρ, hρ, hρG⟩ := Metric.isOpen_iff.1 hGo z₀ hz₀
  set s := min r ρ with hs
  have hs0 : 0 < s := lt_min hr hρ
  have hball : ball z₀ s ⊆ G := fun z hz => hρG (ball_subset_ball (min_le_right _ _) hz)
  have hloc := harmonic_const_of_le_center (hu.mono hball)
    (fun z hz => hr' z (ball_subset_ball (min_le_left _ _) hz))
  have han : AnalyticOnNhd ℝ u G := fun z hz => HarmonicAt.analyticAt (hu z hz)
  have han2 : AnalyticOnNhd ℝ (fun _ : ℂ => u z₀) G := fun z _ => analyticAt_const
  have hev : u =ᶠ[nhds z₀] fun _ => u z₀ :=
    Filter.eventually_of_mem (ball_mem_nhds z₀ hs0) hloc
  exact fun z hz => han.eqOn_of_preconnected_of_eventuallyEq han2 hGc.isPreconnected hz₀ hev hz

/-- Beck Theorem 6.2.3 (CX-087). A harmonic function has no strong relative maximum:
if `u` is harmonic on an open set `G` and `z₀ ∈ G`, then `u` does not have a strong relative
maximum at `z₀`. -/
@[kb "beck2025" "Theorem 6.2.3, p. 106"]
theorem not_hasStrongRelMax {G : Set ℂ} {u : ℂ → ℝ} {z₀ : ℂ}
    (hGo : IsOpen G) (hu : HarmonicOnNhd u G) (hz₀ : z₀ ∈ G) : ¬ HasStrongRelMax u z₀ := by
  rintro ⟨r, hr, h⟩
  obtain ⟨ρ, hρ, hρG⟩ := Metric.isOpen_iff.1 hGo z₀ hz₀
  set s := min r ρ with hs
  have hs0 : 0 < s := lt_min hr hρ
  have hball : ball z₀ s ⊆ G := fun z hz => hρG (ball_subset_ball (min_le_right _ _) hz)
  have hloc := harmonic_const_of_le_center (hu.mono hball) (fun z hz => by
    by_cases hzz : z = z₀
    · rw [hzz]
    · exact (h z hzz (lt_of_lt_of_le (mem_ball.1 hz) (min_le_left _ _))).le)
  have hp : z₀ + ((s / 2 : ℝ) : ℂ) ∈ ball z₀ s := by
    rw [mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    linarith
  have hne : z₀ + ((s / 2 : ℝ) : ℂ) ≠ z₀ := by
    intro h0
    have : ((s / 2 : ℝ) : ℂ) = 0 := by simpa using h0
    have : s / 2 = 0 := by exact_mod_cast this
    linarith
  have := h _ hne (lt_of_lt_of_le (mem_ball.1 hp) (min_le_left _ _))
  rw [hloc _ hp] at this
  exact lt_irrefl _ this

/-- Beck Theorem 6.2.3 (CX-087). A harmonic function has no strong relative minimum. -/
@[kb "beck2025" "Theorem 6.2.3, p. 106"]
theorem not_hasStrongRelMin {G : Set ℂ} {u : ℂ → ℝ} {z₀ : ℂ}
    (hGo : IsOpen G) (hu : HarmonicOnNhd u G) (hz₀ : z₀ ∈ G) : ¬ HasStrongRelMin u z₀ := by
  rintro ⟨r, hr, h⟩
  refine not_hasStrongRelMax hGo hu.neg hz₀ ⟨r, hr, fun z hz hd => ?_⟩
  simpa using h z hz hd

/-- Beck Corollary 8.2.7 (CX-129). If `u` is harmonic on a region `G` and has a weak relative
maximum at a point `z₀ ∈ G` (that is, `u z ≤ u z₀` on a disc around `z₀`), then `u` is constant
on `G`. -/
@[kb "beck2025" "Corollary 8.2.7, p. 137"]
theorem harmonic_const_of_weakRelMax {G : Set ℂ} {u : ℂ → ℝ} {z₀ : ℂ}
    (hGo : IsOpen G) (hGc : IsConnected G) (hu : HarmonicOnNhd u G) (hz₀ : z₀ ∈ G)
    (hmax : ∃ r > 0, ∀ z, dist z z₀ < r → u z ≤ u z₀) :
    ∀ z ∈ G, u z = u z₀ :=
  harmonic_const_of_weak_max hGo hGc hu hz₀ hmax

/-- Beck Corollary 8.2.7 (CX-129), minimum version: a weak relative minimum at a point of a
region forces `u` to be constant. -/
@[kb "beck2025" "Corollary 8.2.7, p. 137"]
theorem harmonic_const_of_weakRelMin {G : Set ℂ} {u : ℂ → ℝ} {z₀ : ℂ}
    (hGo : IsOpen G) (hGc : IsConnected G) (hu : HarmonicOnNhd u G) (hz₀ : z₀ ∈ G)
    (hmin : ∃ r > 0, ∀ z, dist z z₀ < r → u z₀ ≤ u z) :
    ∀ z ∈ G, u z = u z₀ := by
  obtain ⟨r, hr, h⟩ := hmin
  have := harmonic_const_of_weak_max hGo hGc hu.neg hz₀ ⟨r, hr, fun z hz => by
    simpa using h z hz⟩
  intro z hz
  have := this z hz
  simp only [Pi.neg_apply] at this
  linarith

/-- One-sided boundary estimate: if `G` is a bounded region, `u` is harmonic on `G`, continuous
on the closure, and `u ≤ C` on the boundary, then `u ≤ C` on `G`. -/
theorem harmonic_le_of_frontier_le {G : Set ℂ} {u : ℂ → ℝ} {C : ℝ}
    (hGo : IsOpen G) (hGc : IsConnected G) (hGb : Bornology.IsBounded G)
    (hu : HarmonicOnNhd u G) (hcont : ContinuousOn u (closure G))
    (hb : ∀ z ∈ frontier G, u z ≤ C) : ∀ z ∈ G, u z ≤ C := by
  intro z1 hz1
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨w, hwcl, hw⟩ := hGb.isCompact_closure.exists_isMaxOn
    ⟨z1, subset_closure hz1⟩ hcont
  have hwG : w ∈ G := by
    rcases (closure_eq_self_union_frontier G ▸ hwcl : w ∈ G ∪ frontier G) with h | h
    · exact h
    · have := hw (subset_closure hz1)
      have := hb w h
      simp only [mem_ofPred_eq] at *
      linarith
  have hmaxG : ∃ r > 0, ∀ z, dist z w < r → u z ≤ u w := by
    obtain ⟨ρ, hρ, hρG⟩ := Metric.isOpen_iff.1 hGo w hwG
    exact ⟨ρ, hρ, fun z hz => hw (subset_closure (hρG hz))⟩
  have hconst := harmonic_const_of_weak_max hGo hGc hu hwG hmaxG
  have hfr : (frontier G).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨hGc.nonempty, fun h => ?_⟩
    rw [h] at hGb
    exact NormedSpace.unbounded_univ ℂ ℂ hGb
  obtain ⟨p, hp⟩ := hfr
  have hEq : EqOn u (fun _ => u w) (closure G) :=
    Set.EqOn.of_subset_closure hconst hcont continuousOn_const subset_closure subset_rfl
  have h1 := hEq (frontier_subset_closure hp)
  have h2 := hb p hp
  have h3 := hconst z1 hz1
  simp only at h1
  linarith

/-- Beck Corollary 6.2.5 (CX-089). Let `G` be a bounded region, `u` harmonic on `G` and
continuous on the closure of `G`, with `u = 0` on the boundary of `G`.  Then `u = 0` on `G`. -/
@[kb "beck2025" "Corollary 6.2.5, p. 107"]
theorem harmonic_eq_zero_of_frontier_zero {G : Set ℂ} {u : ℂ → ℝ}
    (hGo : IsOpen G) (hGc : IsConnected G) (hGb : Bornology.IsBounded G)
    (hu : HarmonicOnNhd u G) (hcont : ContinuousOn u (closure G))
    (hb : ∀ z ∈ frontier G, u z = 0) : ∀ z ∈ G, u z = 0 := by
  intro z hz
  have h1 := harmonic_le_of_frontier_le hGo hGc hGb hu hcont (C := 0)
    (fun p hp => (hb p hp).le) z hz
  have h2 := harmonic_le_of_frontier_le hGo hGc hGb hu.neg hcont.neg (C := 0)
    (fun p hp => by simp [hb p hp]) z hz
  simp only [Pi.neg_apply] at h2
  linarith

/-- Beck Corollary 6.2.6 (CX-089). Uniqueness for the Dirichlet problem: two functions that are
harmonic on a bounded region, continuous on its closure, and agree on the boundary, agree on the
region. -/
@[kb "beck2025" "Corollary 6.2.6, p. 107"]
theorem harmonic_dirichlet_unique {G : Set ℂ} {u v : ℂ → ℝ}
    (hGo : IsOpen G) (hGc : IsConnected G) (hGb : Bornology.IsBounded G)
    (hu : HarmonicOnNhd u G) (hv : HarmonicOnNhd v G)
    (hucont : ContinuousOn u (closure G)) (hvcont : ContinuousOn v (closure G))
    (hb : ∀ z ∈ frontier G, u z = v z) : ∀ z ∈ G, u z = v z := by
  intro z hz
  have := harmonic_eq_zero_of_frontier_zero hGo hGc hGb (hu.sub hv) (hucont.sub hvcont)
    (fun p hp => by simp [hb p hp]) z hz
  simp only [Pi.sub_apply] at this
  linarith

end UndergradKB.ComplexAnalysis
