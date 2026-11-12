import UndergradKB.ComplexAnalysis.PathIntegral
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Cauchy's theorem along arbitrary closed paths in a disc or in the plane

Beck et al., *A First Course in Complex Analysis*, Corollaries 4.3.8, 4.3.10, 5.2.4, 5.2.5 (checklist rows CX-068,
CX-077) for the regions where Mathlib provides primitives (discs and the whole plane, `DifferentiableOn.isExactOn_ball`,
`Differentiable.isExactOn_univ`): the integral of a holomorphic function along any closed `C¹` path in the region is
zero, and integrals along paths with the same endpoints agree. The general simply connected region needs the homotopy
form of Cauchy's theorem, which is not in Mathlib.
-/

open Complex Metric Set

namespace UndergradKB.ComplexAnalysis

variable {f : ℂ → ℂ} {γ γ' : ℝ → ℂ} {a b a' b' : ℝ}

/-- Beck Corollary 4.3.10 (CX-068): the integral of an entire function along any closed `C¹` path is zero. -/
@[kb "beck2025" "Corollary 4.3.10, p. 81"]
theorem pathIntegral_eq_zero_of_entire (hf : Differentiable ℂ f) (hγ : IsC1On γ a b)
    (hclosed : γ a = γ b) : pathIntegral f γ a b = 0 := by
  obtain ⟨F, hF⟩ := hf.isExactOn_univ
  exact pathIntegral_eq_zero_of_closed hγ (fun t _ => mem_univ (γ t)) hF hf.continuous.continuousOn
    hclosed

/-- Beck Corollary 4.3.8 (CX-068), for a disc: the integral of a function holomorphic on an open disc along any
closed `C¹` path in the disc is zero (every closed path in a disc is contractible there). -/
@[kb "beck2025" "Corollary 4.3.8, p. 80"]
theorem pathIntegral_eq_zero_of_ball {c : ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (ball c r))
    (hγ : IsC1On γ a b) (hsub : ∀ t ∈ uIcc a b, γ t ∈ ball c r) (hclosed : γ a = γ b) :
    pathIntegral f γ a b = 0 := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  exact pathIntegral_eq_zero_of_closed hγ hsub hF hf.continuousOn hclosed

/-- Beck Corollary 5.2.4 (CX-077), for a disc: a function holomorphic on an open disc has an antiderivative there
(Mathlib's `DifferentiableOn.isExactOn_ball`). -/
@[kb "beck2025" "Corollary 5.2.4, p. 94"]
theorem exists_antiderivative_ball {c : ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (ball c r)) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball c r, HasDerivAt F (f z) z :=
  hf.isExactOn_ball

/-- Beck Corollary 5.2.5 (CX-077), for a disc: integrals of a function holomorphic on an open disc along two `C¹`
paths in the disc with the same endpoints agree. -/
@[kb "beck2025" "Corollary 5.2.5, p. 94"]
theorem pathIntegral_eq_of_ball {c : ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (ball c r))
    (hγ : IsC1On γ a b) (hsub : ∀ t ∈ uIcc a b, γ t ∈ ball c r)
    (hγ' : IsC1On γ' a' b') (hsub' : ∀ t ∈ uIcc a' b', γ' t ∈ ball c r)
    (hstart : γ a = γ' a') (hend : γ b = γ' b') :
    pathIntegral f γ a b = pathIntegral f γ' a' b' := by
  obtain ⟨F, hF⟩ := hf.isExactOn_ball
  rw [pathIntegral_eq_sub hγ hsub hF hf.continuousOn, pathIntegral_eq_sub hγ' hsub' hF hf.continuousOn,
    hstart, hend]

/-- Beck Corollary 5.2.5 (CX-077), for the plane: integrals of an entire function along two `C¹` paths with the
same endpoints agree. -/
@[kb "beck2025" "Corollary 5.2.5, p. 94"]
theorem pathIntegral_eq_of_entire (hf : Differentiable ℂ f)
    (hγ : IsC1On γ a b) (hγ' : IsC1On γ' a' b') (hstart : γ a = γ' a') (hend : γ b = γ' b') :
    pathIntegral f γ a b = pathIntegral f γ' a' b' := by
  obtain ⟨F, hF⟩ := hf.isExactOn_univ
  rw [pathIntegral_eq_sub hγ (fun t _ => mem_univ (γ t)) hF hf.continuous.continuousOn,
    pathIntegral_eq_sub hγ' (fun t _ => mem_univ (γ' t)) hF hf.continuous.continuousOn, hstart, hend]

end UndergradKB.ComplexAnalysis
