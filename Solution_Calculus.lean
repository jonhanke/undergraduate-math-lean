/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Calculus.RiemannRearrangement
import UndergradKB.Calculus.Simpson

/-!
# Proofs of the calculus headline statements

Proves the statements of `Challenge_Calculus.lean` from the library. `lake comparator` checks that each statement
here is exactly the one in `Challenge_Calculus.lean`.
-/

namespace UndergradKB.Headlines.Calculus

open Set Finset intervalIntegral MeasureTheory Filter Topology

theorem riemann_rearrangement {a : ℕ → ℝ} {S : ℝ}
    (hS : Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S))
    (habs : ¬ Summable (fun n => |a n|)) (L : ℝ) :
    ∃ σ : ℕ ≃ ℕ, Tendsto (fun n => ∑ i ∈ range n, a (σ i)) atTop (𝓝 L) :=
  UndergradKB.Calculus.riemann_rearrangement hS habs L

theorem simpson_error_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) {a b M : ℝ} (hab : a ≤ b) {n : ℕ}
    (hn : Even n) (hpos : 0 < n) (hM : ∀ x ∈ Icc a b, |iteratedDeriv 4 f x| ≤ M) :
    |UndergradKB.Calculus.simpson f a b n - ∫ x in a..b, f x| ≤ M * (b - a) ^ 5 / (180 * n ^ 4) :=
  UndergradKB.Calculus.simpson_error_le hf hab hn hpos hM

end UndergradKB.Headlines.Calculus
