/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.RealAnalysis.RiemannLebesgue

/-!
# Proofs of the real analysis headline statements

Proves the statements of `Challenge_RealAnalysis.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_RealAnalysis.lean`.
-/

namespace UndergradKB.Headlines.RealAnalysis

open MeasureTheory UndergradKB.RealAnalysis

theorem riemann_integral_eq_lebesgue {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : RiemannIntegrableOn f a b) :
    IntervalIntegrable f volume a b ∧ riemannIntegral f a b hf = ∫ x in a..b, f x :=
  ⟨hf.intervalIntegrable hab, riemannIntegral_eq_intervalIntegral hab hf⟩

end UndergradKB.Headlines.RealAnalysis
