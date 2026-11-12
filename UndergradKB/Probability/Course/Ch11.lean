import Mathlib.Probability.Kernel.Invariance
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 11 (Grinstead–Snell, Markov Chains)

Thin wrappers stating the book's results of Chapter 11 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory

/-- Grinstead–Snell §11.5 reversible chain (PR-122). A Markov chain with transition kernel `κ`
that satisfies detailed balance with respect to `π` (the kernel analogue of `w_i p_ij = w_j p_ji`)
leaves `π` invariant. -/
@[kb "grinsteadsnell2006" "§11.5 reversible chain, p. 471"]
theorem gs_section_11_5_reversible_chain {α : Type*} [MeasurableSpace α] (κ : Kernel α α)
    [IsMarkovKernel κ] (π : Measure α) (h : Kernel.IsReversible κ π) :
    Kernel.Invariant κ π :=
  h.invariant

end UndergradKB.Probability.Course
