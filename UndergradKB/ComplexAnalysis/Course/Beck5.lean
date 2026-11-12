import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 5 (Consequences of Cauchy's Theorem): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`). -/

namespace UndergradKB.ComplexAnalysis.Course.Beck5
open Complex Polynomial Metric
open scoped ContDiff

/-- Beck Corollary 5.1.6 (CX-074). A function differentiable on a region (open and connected set)
is infinitely differentiable there, also as a function of the real variables `x`, `y`. -/
@[kb "beck2025" "Corollary 5.1.6, p. 93"]
theorem differentiable_implies_smooth (G : Set ℂ) (hG : IsOpen G) (_hC : IsConnected G)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f G) :
    ContDiffOn ℂ ∞ f G ∧ ContDiffOn ℝ ∞ f G :=
  ⟨hf.contDiffOn hG, (hf.contDiffOn hG).restrict_scalars ℝ⟩

/-- Beck Theorem 5.3.2 (CX-004). Fundamental theorem of algebra: every nonconstant polynomial has a
root in `ℂ`. -/
@[kb "beck2025" "Theorem 5.3.2, p. 95"]
theorem fundamental_theorem_of_algebra (p : ℂ[X]) (hp : 0 < p.degree) : ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root hp

/-- Beck Corollary 5.3.4 (CX-080). Liouville's theorem: a bounded entire function is constant. -/
@[kb "beck2025" "Corollary 5.3.4, p. 96"]
theorem liouville (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hb : ∃ M : ℝ, ∀ z, ‖f z‖ ≤ M) :
    ∃ c : ℂ, ∀ z, f z = c := by
  obtain ⟨M, hM⟩ := hb
  refine hf.exists_const_forall_eq_of_bounded ?_
  rw [isBounded_iff_forall_norm_le]
  exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM z⟩

end UndergradKB.ComplexAnalysis.Course.Beck5
