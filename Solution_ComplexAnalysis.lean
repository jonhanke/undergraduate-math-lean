/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.ComplexAnalysis.Singularities
import UndergradKB.ComplexAnalysis.Dedekind

/-!
# Proofs of the complex analysis headline statements

Proves the statements of `Challenge_ComplexAnalysis.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_ComplexAnalysis.lean`.
-/

namespace UndergradKB.Headlines.ComplexAnalysis

open Metric Set Filter Topology Finset Real UndergradKB.ComplexAnalysis

theorem casorati_weierstrass {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R \ {z₀})) (hess : HasEssentialSingularity f z₀)
    (w : ℂ) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ z : ℂ, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < r ∧ ‖f z - w‖ < ε :=
  UndergradKB.ComplexAnalysis.casorati_weierstrass hR hf hess w hε hr

theorem dedekind_sum_reciprocity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    dedekindSumCot a b + dedekindSumCot b a
      = -1 / 4 + ((a : ℝ) / b + 1 / ((a : ℝ) * b) + (b : ℝ) / a) / 12 :=
  UndergradKB.ComplexAnalysis.dedekindSumCot_reciprocity ha hb hab

end UndergradKB.Headlines.ComplexAnalysis
