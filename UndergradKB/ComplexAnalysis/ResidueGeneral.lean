import UndergradKB.ComplexAnalysis.CauchyFormula
import UndergradKB.ComplexAnalysis.ResidueTheorem
import UndergradKB.ComplexAnalysis.PathIntegralMore

/-!
# The residue theorem for positively oriented simple closed paths (row CX-141)

Beck et al., Theorem 9.2.2: if `f` is holomorphic on the open set `G` except at finitely many
isolated singularities `S`, and `γ` is a positively oriented simple closed piecewise smooth path
avoiding `S` with `γ ∼_G 0`, then `∫_γ f = 2 π i ∑ Res_{z = s} f`, the sum over the singularities
inside `γ`. (The book allows any set of isolated singularities in `G`; here `S` is finite.)

Proof, following the book with the topology it assumes (`IsPositivelyOrientedSimpleClosed`):
subtract the principal parts `P s` at the singularities `s` inside `γ` (from `ResidueTheorem.lean`);
the difference extends holomorphically to `G` minus the singularities outside `γ`, a set in which `γ`
is still contractible (Proposition 4.4.6), so its integral vanishes (Corollary 4.3.8); the integral of
each principal part over `γ` equals its integral over a small circle about `s` (the annulus homotopy
and Cauchy's theorem 4.3.4), which is `2 π i Res_{z = s} f`.
-/

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

namespace UndergradKB.ComplexAnalysis

lemma pathIntegral_congr_on {f g : ℂ → ℂ} {γ : ℝ → ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) = g (γ t)) :
    pathIntegral f γ 0 1 = pathIntegral g γ 0 1 := by
  unfold pathIntegral
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  simp only [h t ht]

set_option maxHeartbeats 1600000 in
open Classical in
/-- Beck Theorem 9.2.2 (CX-141), **the residue theorem**: `f` holomorphic on the open set `G`
except at the finite set `S`, `γ` a positively oriented simple closed piecewise smooth path in `G`
avoiding `S` and `G`-contractible. Then `∫_γ f = 2 π i ∑_{s ∈ S inside γ} Res_{z=s} f`. -/
@[kb "beck2025" "Theorem 9.2.2, p. 154"]
theorem residue_theorem {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) {S : Finset ℂ}
    (hf : DifferentiableOn ℂ f (G \ S)) {γ : ℝ → ℂ} (hγ : IsPositivelyOrientedSimpleClosed γ)
    (hγS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ S) {c : ℂ} (hc : IsGHomotopic G γ (fun _ => c)) :
    pathIntegral f γ 0 1 =
      2 * π * I * ∑ s ∈ S.filter (· ∈ insideOf γ), residue f s := by
  set T := S.filter (· ∈ insideOf γ) with hTdef
  have hTS : ∀ s ∈ T, s ∈ S := fun s hs => (Finset.mem_filter.1 hs).1
  have hTin : ∀ s ∈ T, s ∈ insideOf γ := fun s hs => (Finset.mem_filter.1 hs).2
  have hinG := hγ.inside_subset_of_contractible hG hc
  have himgG : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G := hc.mem_left
  -- the region without the singularities outside `γ`
  set G' : Set ℂ := G \ ((S : Set ℂ) \ insideOf γ) with hG'def
  have hG'o : IsOpen G' := hG.sdiff (S.finite_toSet.subset diff_subset).isClosed
  have hinG' : insideOf γ ⊆ G' := fun z hz => ⟨hinG hz, fun h => h.2 hz⟩
  have himgG' : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G' := fun t ht => ⟨himgG t ht, fun h => hγS t ht h.1⟩
  obtain ⟨c', hc'⟩ := (hγ.contractible_iff_inside_subset hG'o himgG').2 hinG'
  -- a common radius `δ` around the singularities inside
  have hopenIn := hγ.isOpen_inside
  obtain ⟨δ, hδ, hδin, hδS⟩ : ∃ δ > 0, (∀ s ∈ T, closedBall s δ ⊆ insideOf γ) ∧
      (∀ s ∈ T, ∀ t ∈ S, t ≠ s → δ < ‖t - s‖) := by
    have h1 : ∀ s ∈ T, ∀ᶠ δ in 𝓝[>] (0 : ℝ), closedBall s δ ⊆ insideOf γ := fun s hs => by
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopenIn s (hTin s hs)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hε)] with δ hδ
      exact (closedBall_subset_ball hδ).trans hball
    have h2 : ∀ s ∈ T, ∀ t ∈ S, ∀ᶠ δ in 𝓝[>] (0 : ℝ), t ≠ s → δ < ‖t - s‖ := by
      intro s _ t _
      by_cases hts : t = s
      · exact Eventually.of_forall fun _ h => absurd hts h
      · exact (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds
          (norm_pos_iff.2 (sub_ne_zero.2 hts)))).mono fun _ h _ => h
    have H := (((Filter.eventually_all_finset T).2 h1).and ((Filter.eventually_all_finset T).2
      fun s hs => (Filter.eventually_all_finset S).2 (h2 s hs))).and
      (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))
    obtain ⟨δ, ⟨hA, hB⟩, hpos⟩ := H.exists
    exact ⟨δ, hpos, hA, fun s hs t ht => hB s hs t ht⟩
  have hfs : ∀ s ∈ T, DifferentiableOn ℂ f (ball s δ \ {s}) := by
    intro s hs
    refine hf.mono fun z ⟨hz1, hz2⟩ => ⟨hinG (hδin s hs (ball_subset_closedBall hz1)),
      fun hzS => ?_⟩
    have := hδS s hs z hzS hz2
    rw [mem_ball_iff_norm] at hz1; linarith
  have hnotS : ∀ s ∈ T, ∀ w ∈ ball s δ, w ≠ s → w ∉ S := by
    intro s hs w hw hws hwS
    have := hδS s hs w hwS hws
    rw [mem_ball_iff_norm] at hw; linarith
  have hδ2 : 0 < δ / 2 := half_pos hδ
  set P : ℂ → ℂ → ℂ := fun s => principalPart f s δ with hP
  set O : ℂ → ℂ → ℂ := fun s w => (2 * π * I)⁻¹ * ∮ z in C(s, δ / 2), (z - w)⁻¹ * f z with hO
  set F : ℂ → ℂ := fun w => f w - ∑ s ∈ T, P s w with hF
  set Gf : ℂ → ℂ := fun w => if w ∈ T then O w w - ∑ t ∈ T.erase w, P t w else F w with hGf
  have hPd : ∀ s ∈ T, ∀ w, w ≠ s → DifferentiableAt ℂ (P s) w := fun s hs w hw =>
    differentiableAt_principalPart (hfs s hs) hδ hw
  have hOd : ∀ s ∈ T, ∀ w ∈ ball s (δ / 2), DifferentiableAt ℂ (O s) w := by
    intro s hs w hw
    refine (differentiableAt_cauchyIntegral hδ2 ?_ ?_).const_mul _
    · exact (hfs s hs).continuousOn.mono (sphere_subset_punctured hδ2 (half_lt_self hδ))
    · exact (mem_ball_iff_norm.1 hw).ne
  have hA : ∀ s ∈ T, ∀ w ∈ ball s (δ / 2), Gf w = O s w - ∑ t ∈ T.erase s, P t w := by
    intro s hs w hw
    by_cases hws : w = s
    · subst hws; simp only [hGf, hs, ite_true]
    · have hwS : w ∉ T := fun h =>
        hnotS s hs w (ball_subset_ball (half_le_self hδ.le) hw) hws (hTS w h)
      simp only [hGf, hwS, ite_false, hF]
      rw [← Finset.add_sum_erase T _ hs,
        eq_add_principalPart (hfs s hs) (half_lt_self hδ) (norm_pos_iff.2 (sub_ne_zero.2 hws))
          (mem_ball_iff_norm.1 hw)]
      simp only [hO, hP]; ring
  have hopen : IsOpen ((T : Set ℂ)ᶜ) := T.finite_toSet.isClosed.isOpen_compl
  have hGF : ∀ w, w ∉ T → Gf =ᶠ[𝓝 w] F := fun w hw =>
    eventually_of_mem (hopen.mem_nhds hw) fun v hv => by
      have hv' : v ∉ T := hv
      simp only [hGf, hv', ite_false]
  have hSo : IsOpen (G \ (S : Set ℂ)) := hG.sdiff S.finite_toSet.isClosed
  have hB : ∀ w ∈ G', DifferentiableAt ℂ Gf w := by
    intro w hw
    by_cases hwT : w ∈ T
    · have hev : Gf =ᶠ[𝓝 w] fun v => O w v - ∑ t ∈ T.erase w, P t v :=
        eventually_of_mem (ball_mem_nhds w hδ2) fun v hv => hA w hwT v hv
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      refine (hOd w hwT w (mem_ball_self hδ2)).sub (DifferentiableAt.fun_sum fun t ht => ?_)
      exact hPd t (Finset.mem_of_mem_erase ht) w (Finset.ne_of_mem_erase ht).symm
    · have hwS : w ∉ S := by
        intro hwS
        refine hwT (Finset.mem_filter.2 ⟨hwS, ?_⟩)
        by_contra hni
        exact hw.2 ⟨hwS, hni⟩
      refine DifferentiableAt.congr_of_eventuallyEq ?_ (hGF w hwT)
      refine DifferentiableAt.sub ?_ (DifferentiableAt.fun_sum fun s hs => hPd s hs w
        fun h => hwT (h ▸ hs))
      exact hf.differentiableAt (hSo.mem_nhds ⟨hw.1, hwS⟩)
  have hzero : pathIntegral Gf γ 0 1 = 0 :=
    pathIntegral_eq_zero_of_contractible hG'o (fun w hw => (hB w hw).differentiableWithinAt)
      hγ.smooth hc'
  have hγT : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ T := fun t ht h => hγS t ht (hTS _ h)
  have hGFγ : pathIntegral Gf γ 0 1 = pathIntegral F γ 0 1 :=
    pathIntegral_congr_on fun t ht => by simp only [hGf, hγT t ht, ite_false]
  -- integrability along `γ`
  have hfint : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume 0 1 :=
    hγ.smooth.intervalIntegrable_integrand zero_le_one
      (hf.continuousOn.mono (by rintro _ ⟨t, ht, rfl⟩; exact ⟨himgG t ht, hγS t ht⟩))
  have hPc : ∀ s ∈ T, ContinuousOn (P s) (γ '' Icc 0 1) := by
    rintro s hs _ ⟨t, ht, rfl⟩
    exact (hPd s hs (γ t) fun h => hγT t ht (h ▸ hs)).continuousAt.continuousWithinAt
  have hPint : ∀ s ∈ T, IntervalIntegrable (fun t => P s (γ t) * deriv γ t) volume 0 1 :=
    fun s hs => hγ.smooth.intervalIntegrable_integrand zero_le_one (hPc s hs)
  have hsumint : IntervalIntegrable (fun t => (∑ s ∈ T, P s (γ t)) * deriv γ t) volume 0 1 :=
    hγ.smooth.intervalIntegrable_integrand zero_le_one (f := fun z => ∑ s ∈ T, P s z)
      (by
        rintro _ ⟨t, ht, rfl⟩
        exact (DifferentiableAt.fun_sum fun s hs => hPd s hs (γ t) fun h => hγT t ht (h ▸ hs))
          |>.continuousAt.continuousWithinAt)
  -- each principal part contributes `2 π i Res`
  have hPres : ∀ s ∈ T, pathIntegral (P s) γ 0 1 = 2 * π * I * residue f s := by
    intro s hs
    have h34 : (0 : ℝ) < 3 * δ / 4 := by positivity
    have hsub : closedBall s (3 * δ / 4) ⊆ insideOf γ :=
      (closedBall_subset_closedBall (by linarith)).trans (hδin s hs)
    have hhom := (hγ.annulus s (3 * δ / 4) h34 hsub).mono (show
      (insideOf γ ∪ pathImage γ) \ ball s (3 * δ / 4) ⊆ {s}ᶜ by
        rintro z ⟨-, hz⟩ rfl; exact hz (mem_ball_self h34))
    have hPd' : DifferentiableOn ℂ (P s) {s}ᶜ := fun w hw =>
      (hPd s hs w hw).differentiableWithinAt
    rw [cauchy_theorem_homotopy isOpen_compl_singleton hPd' hγ.smooth
      (isPiecewiseSmooth_circlePath s _) hhom, pathIntegral_circlePath]
    refine circleIntegral_principalPart (hfs s hs) hδ2 (half_lt_self hδ) h34.le ?_ ?_
    · intro w hw
      rw [mem_sphere_iff_norm] at hw
      linarith
    · exact closedBall_subset_ball (by linarith)
  rw [hGFγ] at hzero
  simp only [hF] at hzero
  rw [pathIntegral_sub hfint hsumint, pathIntegral_finset_sum T hPint,
    Finset.sum_congr rfl hPres, ← Finset.mul_sum, sub_eq_zero] at hzero
  exact hzero

end UndergradKB.ComplexAnalysis
