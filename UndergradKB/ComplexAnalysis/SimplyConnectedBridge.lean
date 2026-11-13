import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import UndergradKB.ComplexAnalysis.PathIntegralMore
import UndergradKB.ComplexAnalysis.SimplyConnected

/-!
# Mathlib's `IsSimplyConnected` and Beck's simply connected regions (rows CX-076, CX-077)

An open set that is simply connected in Mathlib's sense is a simply connected region in Beck's
sense (`IsSimplyConnectedRegion`); hence discs and the slit plane are simply connected regions,
and holomorphic functions on them have antiderivatives.
-/

open Set Filter Topology

namespace UndergradKB.ComplexAnalysis

/-- An open set that is simply connected in Mathlib's sense is a simply connected region in the
sense of Beck Definition 5.2.2. -/
theorem IsSimplyConnected.isSimplyConnectedRegion {G : Set ℂ} (hGo : IsOpen G)
    (hG : IsSimplyConnected G) : IsSimplyConnectedRegion G := by
  obtain ⟨hpc, hloop⟩ := isSimplyConnected_iff_exists_homotopy_refl_forall_mem.1 hG
  refine ⟨hGo, hpc.isConnected, fun γ hγ hγG h01 => ⟨γ 0, ?_⟩⟩
  have hcont : Continuous (fun t : unitInterval => γ t) :=
    hγ.comp_continuous continuous_subtype_val (fun t => t.2)
  let p : Path (γ 0) (γ 0) :=
    { toFun := fun t => γ t
      continuous_toFun := hcont
      source' := by simp
      target' := by simpa using h01.symm }
  obtain ⟨F, hF⟩ := hloop (γ 0) p (fun t => hγG t t.2)
  have h0 : Set.projIcc (0:ℝ) 1 zero_le_one 0 = 0 := by
    apply Subtype.ext; simp [Set.projIcc]
  have h1 : Set.projIcc (0:ℝ) 1 zero_le_one 1 = 1 := by
    apply Subtype.ext; simp [Set.projIcc]
  refine ⟨fun t s => F (Set.projIcc 0 1 zero_le_one s, Set.projIcc 0 1 zero_le_one t),
    ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun q : ℝ × ℝ => F (Set.projIcc (0:ℝ) 1 zero_le_one q.2,
        Set.projIcc (0:ℝ) 1 zero_le_one q.1)) :=
      F.continuous.comp ((continuous_projIcc.comp continuous_snd).prodMk
        (continuous_projIcc.comp continuous_fst))
    exact hc.continuousOn
  · intro t _ s _
    exact hF _
  · intro t ht
    have h2 : (Set.projIcc (0:ℝ) 1 zero_le_one t : unitInterval) = ⟨t, ht⟩ :=
      Set.projIcc_of_mem _ ht
    simp only [h0, h2]
    have := F.apply_zero ⟨t, ht⟩
    simp [p]
  · intro t ht
    simp only [h1]
    exact F.apply_one _
  · intro s hs
    simp only [h0, h1]
    have a := F.source (Set.projIcc (0:ℝ) 1 zero_le_one s)
    have b := F.target (Set.projIcc (0:ℝ) 1 zero_le_one s)
    rw [a, b]

/-- Beck Example 5.2.3 (CX-076). Open discs are simply connected regions. -/
@[kb "beck2025" "Example 5.2.3, p. 94"]
theorem isSimplyConnectedRegion_ball (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnectedRegion (Metric.ball c r) :=
  IsSimplyConnected.isSimplyConnectedRegion Metric.isOpen_ball (isSimplyConnected_ball c hr)

/-- Beck Example 5.2.3 (CX-076). The slit plane is a simply connected region. -/
@[kb "beck2025" "Example 5.2.3, p. 94"]
theorem isSimplyConnectedRegion_slitPlane : IsSimplyConnectedRegion Complex.slitPlane :=
  IsSimplyConnected.isSimplyConnectedRegion Complex.isOpen_slitPlane isSimplyConnected_slitPlane

/-- Beck Corollary 5.2.4 (CX-077) for Mathlib's `IsSimplyConnected`: every holomorphic function on
an open simply connected set has an antiderivative there. -/
@[kb "beck2025" "Corollary 5.2.4, p. 94"]
theorem exists_antiderivative_of_isSimplyConnected {f : ℂ → ℂ} {G : Set ℂ} (hGo : IsOpen G)
    (hG : IsSimplyConnected G) (hf : DifferentiableOn ℂ f G) :
    ∃ F : ℂ → ℂ, ∀ z ∈ G, HasDerivAt F (f z) z :=
  exists_antiderivative_of_simplyConnected (IsSimplyConnected.isSimplyConnectedRegion hGo hG) hf

end UndergradKB.ComplexAnalysis
