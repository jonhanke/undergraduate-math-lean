import UndergradKB.ComplexAnalysis.StarJordan
import UndergradKB.ComplexAnalysis.StarExamples
import UndergradKB.ComplexAnalysis.ResidueGeneral

/-!
# Consequences of the Jordan curve theorem for star-shaped paths

With `IsStarPath.isPositivelyOrientedSimpleClosed_star` (no convexity), Cauchy's integral formula
4.4.5 and the residue theorem 9.2.2 hold for every piecewise smooth star-shaped path whose closed
inside lies in the domain; in particular for every polar path `c + ρ(t) e^{2π i t}` with a positive
`C¹` radius `ρ` of period `1` (`polarPath`), convex or not.
-/

open Set Metric Complex Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

namespace IsStarPath

variable {γ : ℝ → ℂ} {c : ℂ} {φ : ℝ → ℝ}

/-- A star-shaped path is contractible to its centre in any set containing its closed inside
(radial homotopy towards the centre). -/
theorem contractible_star (h : IsStarPath γ c φ) {G : Set ℂ} (hG : inner γ c ∪ pathImage γ ⊆ G) :
    IsGHomotopic G γ (fun _ => c) := by
  refine ⟨fun t s => c + ((1 - s : ℝ) : ℂ) * (γ t - c), ?_, fun t ht s hs => hG ?_, ?_, ?_, ?_⟩
  · refine continuousOn_const.add (ContinuousOn.mul ?_ ?_)
    · exact continuous_ofReal.comp_continuousOn (continuousOn_const.sub continuousOn_snd)
    · exact (h.cont.comp continuousOn_fst
        (fun q (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hq.1)).sub continuousOn_const
  · rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · right
      exact ⟨t, ht, by rw [← hs0]; push_cast; ring⟩
    · left
      exact h.ray_mem_inner ht ⟨by linarith [hs.2], by linarith⟩
  · intro t _; push_cast; ring
  · intro t _; push_cast; ring
  · intro s _; simp only [h.closed]

open Classical in
/-- **The residue theorem for star-shaped paths** (Beck Theorem 9.2.2, with no topological
assumption): if `f` is holomorphic on the open set `G` except at the finitely many points of `S`,
the path `γ` is piecewise smooth and star-shaped about `c`, its closed inside lies in `G`, and it
avoids `S`, then `∫_γ f = 2π i ∑_{s ∈ S inside γ} Res_s f`. -/
@[kb "beck2025" "Theorem 9.2.2, p. 154"]
theorem residue_theorem_star (h : IsStarPath γ c φ) (hs : IsPiecewiseSmooth γ 0 1)
    {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hKG : inner γ c ∪ pathImage γ ⊆ G) {S : Finset ℂ}
    (hf : DifferentiableOn ℂ f (G \ S)) (hγS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ S) :
    pathIntegral f γ 0 1 = 2 * π * I * ∑ s ∈ S.filter (· ∈ inner γ c), residue f s := by
  rw [UndergradKB.ComplexAnalysis.residue_theorem hG hf
    (h.isPositivelyOrientedSimpleClosed_star hs) hγS (h.contractible_star hKG)]
  congr 2
  ext s
  simp [Finset.mem_filter, h.insideOf_eq_inner]

/-- **Cauchy's integral formula for star-shaped paths** (Beck Theorem 4.4.5, with no topological
assumption). -/
@[kb "beck2025" "Theorem 4.4.5, p. 83"]
theorem cauchy_integral_formula_star (h : IsStarPath γ c φ) (hs : IsPiecewiseSmooth γ 0 1)
    {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hKG : inner γ c ∪ pathImage γ ⊆ G)
    (hf : DifferentiableOn ℂ f G) {w : ℂ} (hw : w ∈ inner γ c) :
    f w = (2 * π * I)⁻¹ * pathIntegral (fun z => f z / (z - w)) γ 0 1 :=
  (h.isPositivelyOrientedSimpleClosed_star hs).cauchy_integral_formula hG hf
    (h.contractible_star hKG) (by rw [h.insideOf_eq_inner]; exact hw)

end IsStarPath

/-! ### Polar paths -/

section Polar

variable {c : ℂ} {ρ : ℝ → ℝ}

lemma isPiecewiseSmooth_polarPath (hρ : ContDiff ℝ 1 ρ) : IsPiecewiseSmooth (polarPath c ρ) 0 1 := by
  have hc : ContDiff ℝ 1 (polarPath c ρ) := by
    unfold polarPath
    have h1 : ContDiff ℝ 1 (fun t => ((ρ t : ℝ) : ℂ)) := ofRealCLM.contDiff.comp hρ
    have h2 : ContDiff ℝ 1 (fun t : ℝ => exp (((2 * π * t : ℝ) : ℂ) * I)) :=
      Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
        contDiff_const)
    exact contDiff_const.add (h1.mul h2)
  exact IsC1On.isPiecewiseSmooth ⟨fun t _ => (hc.differentiable (by norm_num)).differentiableAt,
    (hc.continuous_deriv le_rfl).continuousOn⟩ zero_le_one

/-- **Polar paths are positively oriented simple closed paths.** For a positive `C¹` radius
`ρ` with `ρ 0 = ρ 1`, the polar path `c + ρ(t) e^{2π i t}` satisfies Definition 4.4.4 with both
assumed fields proved, whether or not the region it bounds is convex. -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem isPositivelyOrientedSimpleClosed_polarPath (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ t, 0 < ρ t)
    (h01 : ρ 0 = ρ 1) : IsPositivelyOrientedSimpleClosed (polarPath c ρ) :=
  (isStarPath_polarPath hρ.continuous.continuousOn (fun t _ => hpos t) h01).isPositivelyOrientedSimpleClosed_star
    (isPiecewiseSmooth_polarPath hρ)

/-- **The Jordan curve theorem for polar paths**: the inside of `c + ρ(t) e^{2π i t}` is the set of
points `c + s ρ(t) e^{2π i t}` with `0 ≤ s < 1`. -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem insideOf_polarPath (hρ : ContinuousOn ρ (Icc 0 1)) (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ρ t)
    (h01 : ρ 0 = ρ 1) :
    insideOf (polarPath c ρ) = (fun p : ℝ × ℝ => c + p.1 * (polarPath c ρ p.2 - c)) ''
      (Ico 0 1 ×ˢ Icc 0 1) := by
  have h := isStarPath_polarPath (c := c) hρ hpos h01
  rw [h.insideOf_eq_inner]
  ext z
  constructor
  · intro hz
    by_cases hzc : z = c
    · exact ⟨(0, 0), ⟨⟨le_rfl, one_pos⟩, IsStarPath.zero_mem⟩, by simp [hzc]⟩
    obtain ⟨t, ht, r, hr, hzr, -, hn⟩ := h.exists_ray_radius hzc
    refine ⟨(r, t), ⟨⟨hr.le, ?_⟩, ht⟩, hzr.symm⟩
    have h1 : r * IsStarPath.radius (polarPath c ρ) c z < IsStarPath.radius (polarPath c ρ) c z :=
      hn ▸ hz
    have := h.radius_pos z
    nlinarith
  · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    exact h.ray_mem_inner ht hs

/-- For every polar path, `∫ dz / (z - c) = 2π i` (Cauchy's formula with `f = 1`). -/
@[kb "beck2025" "Theorem 4.4.5, p. 83"]
theorem pathIntegral_inv_sub_polarPath (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ t, 0 < ρ t)
    (h01 : ρ 0 = ρ 1) : pathIntegral (fun z => 1 / (z - c)) (polarPath c ρ) 0 1 = 2 * π * I := by
  have h := isStarPath_polarPath (c := c) hρ.continuous.continuousOn (fun t _ => hpos t) h01
  have e := h.cauchy_integral_formula_star (isPiecewiseSmooth_polarPath hρ) isOpen_univ
    (subset_univ _) (f := fun _ => (1 : ℂ)) (differentiableOn_const 1) h.center_mem_inner
  have hπ : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  rw [eq_inv_mul_iff_mul_eq₀ hπ, mul_one] at e
  exact e.symm

/-- A non-convex example: the five-petal flower `c + (2 + cos 10πt) e^{2π i t}` is a positively
oriented simple closed path (Definition 4.4.4, both assumed fields proved). -/
theorem isPositivelyOrientedSimpleClosed_flower :
    IsPositivelyOrientedSimpleClosed (polarPath c (fun t => 2 + Real.cos (10 * π * t))) := by
  refine isPositivelyOrientedSimpleClosed_polarPath (by fun_prop) (fun t => ?_) ?_
  · linarith [Real.neg_one_le_cos (10 * π * t)]
  · simp only [mul_zero, Real.cos_zero, mul_one]
    rw [show 10 * π = (5 : ℕ) * (2 * π) by push_cast; ring, Real.cos_nat_mul_two_pi]

end Polar

end UndergradKB.ComplexAnalysis
