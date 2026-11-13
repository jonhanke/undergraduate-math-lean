import UndergradKB.ComplexAnalysis.HomotopyGeneral
import UndergradKB.ComplexAnalysis.Primitive

/-!
# Simply connected regions and antiderivatives (rows CX-076, CX-077)

Beck et al., Definition 5.2.2: a region `G` is simply connected if every closed path in `G` is
`G`-contractible. With Cauchy's theorem for continuous homotopies (`cauchy_theorem_homotopy`) this
gives Corollary 5.2.4 (every holomorphic function on a simply connected region has an
antiderivative) and Corollary 5.2.5 (path independence), following the book: closed polygonal
paths are contractible, so their integrals vanish, and Theorem 4.2.9
(`exists_antiderivative_of_closed_integrals`) produces the antiderivative.
-/

open Set Metric

namespace UndergradKB.ComplexAnalysis

/-- Beck Definition 5.2.2 (CX-076). A region `G` (open and connected) is simply connected if every
closed path `γ` in `G` (continuous on `[0, 1]`, `γ 0 = γ 1`) is `G`-homotopic to a constant
path. -/
@[kb "beck2025" "Definition 5.2.2, p. 94"]
def IsSimplyConnectedRegion (G : Set ℂ) : Prop :=
  IsOpen G ∧ IsConnected G ∧ ∀ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) →
    (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G) → γ 0 = γ 1 → ∃ c : ℂ, IsGHomotopic G γ (fun _ => c)

variable {f : ℂ → ℂ} {G : Set ℂ}

/-- A polygonal path made of horizontal and vertical segments is realised by a piecewise smooth
path on `[0, 1]` with the same integral. -/
theorem HVPathIntegral.exists_path (hf : ContinuousOn f G) {a b I : ℂ}
    (h : HVPathIntegral G f a b I) :
    ∃ γ : ℝ → ℂ, IsPiecewiseSmooth γ 0 1 ∧ γ 0 = a ∧ γ 1 = b ∧ (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G) ∧
      pathIntegral f γ 0 1 = I := by
  induction h with
  | refl ha =>
    exact ⟨fun _ => a, isPiecewiseSmooth_const a 0 1, rfl, rfl, fun _ _ => ha,
      pathIntegral_const_path a 0 1⟩
  | @step b c I _ _ hseg ih =>
    obtain ⟨γ, hγ, h0, h1, hG, hI⟩ := ih
    have hs : IsPiecewiseSmooth (segPath b c) 0 1 :=
      (isC1On_segPath b c 0 1).isPiecewiseSmooth zero_le_one
    have hsG : ∀ t ∈ Icc (0 : ℝ) 1, segPath b c t ∈ G := fun t ht => hseg (segPath_mem ht)
    have hj : γ 1 = segPath b c 0 := by rw [h1, segPath_zero]
    refine ⟨pathConcat γ (segPath b c), hγ.pathConcat hs hj, by simp [h0], by simp [segPath_one],
      fun t ht => ?_, ?_⟩
    · rcases pathConcat_mem (γ₁ := γ) (γ₂ := segPath b c) ht with ⟨u, hu, e⟩ | ⟨u, hu, e⟩
      · rw [← e]; exact hG u hu
      · rw [← e]; exact hsG u hu
    · rw [pathIntegral_pathConcat hγ hs hj
        (hf.mono (by rintro _ ⟨u, hu, rfl⟩; exact hG u hu))
        (hf.mono (by rintro _ ⟨u, hu, rfl⟩; exact hsG u hu)), hI]
      rfl

/-- Beck Corollary 5.2.4 (CX-077): every holomorphic function on a simply connected region has an
antiderivative there. -/
@[kb "beck2025" "Corollary 5.2.4, p. 94"]
theorem exists_antiderivative_of_simplyConnected (hG : IsSimplyConnectedRegion G)
    (hf : DifferentiableOn ℂ f G) :
    ∃ F : ℂ → ℂ, ∀ z ∈ G, HasDerivAt F (f z) z := by
  obtain ⟨hGo, hGc, hsc⟩ := hG
  refine exists_antiderivative_of_closed_integrals hGo hGc.isPreconnected hf.continuousOn
    (fun a I hI => ?_)
  obtain ⟨γ, hγ, h0, h1, hγG, rfl⟩ := hI.exists_path hf.continuousOn
  obtain ⟨c, hc⟩ := hsc γ hγ.continuousOn hγG (h0.trans h1.symm)
  exact pathIntegral_eq_zero_of_contractible hGo hf hγ hc

/-- Beck Corollary 5.2.5 (CX-077): if `f` is holomorphic on a simply connected region `G`, the
integral of `f` along a piecewise smooth path in `G` depends only on the endpoints of the path. -/
@[kb "beck2025" "Corollary 5.2.5, p. 94"]
theorem pathIntegral_eq_of_simplyConnected (hG : IsSimplyConnectedRegion G)
    (hf : DifferentiableOn ℂ f G) {γ γ' : ℝ → ℂ} {a b a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    (hγ : IsPiecewiseSmooth γ a b) (hsub : ∀ t ∈ Icc a b, γ t ∈ G)
    (hγ' : IsPiecewiseSmooth γ' a' b') (hsub' : ∀ t ∈ Icc a' b', γ' t ∈ G)
    (hstart : γ a = γ' a') (hend : γ b = γ' b') :
    pathIntegral f γ a b = pathIntegral f γ' a' b' := by
  obtain ⟨F, hF⟩ := exists_antiderivative_of_simplyConnected hG hf
  rw [pathIntegral_eq_sub_of_isPiecewiseSmooth hγ hab hsub hF hf.continuousOn,
    pathIntegral_eq_sub_of_isPiecewiseSmooth hγ' hab' hsub' hF hf.continuousOn, hstart, hend]

/-- Beck Corollary 4.3.8 (CX-068) on a simply connected region: the integral of a holomorphic
function along any piecewise smooth closed path in a simply connected region is zero. -/
@[kb "beck2025" "Corollary 4.3.8, p. 80"]
theorem pathIntegral_eq_zero_of_simplyConnected (hG : IsSimplyConnectedRegion G)
    (hf : DifferentiableOn ℂ f G) {γ : ℝ → ℂ} (hγ : IsPiecewiseSmooth γ 0 1)
    (hsub : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G) (hclosed : γ 0 = γ 1) :
    pathIntegral f γ 0 1 = 0 := by
  obtain ⟨c, hc⟩ := hG.2.2 γ hγ.continuousOn hsub hclosed
  exact pathIntegral_eq_zero_of_contractible hG.1 hf hγ hc

end UndergradKB.ComplexAnalysis
