import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import UndergradKB.Common.Attr

/-!
# Lebl, Notes on Diffy Qs, Chapter 8 (nonlinear systems): course layer

Thin wrapper around Mathlib stating the notion of a simply connected region.
-/

namespace UndergradKB.DifferentialEquations.Course.Ch8

/-- Lebl §8.4 Simply connected region (DE-234). A region `U ⊆ ℝ²` is simply connected iff it is
path connected and any two paths with the same endpoints in it are homotopic (it has no holes). -/
@[kb "lebldiffyqs2026" "§8.4 Simply connected region, p. 375"]
theorem lebl_simply_connected_iff (U : Set (ℝ × ℝ)) :
    SimplyConnectedSpace U ↔
      PathConnectedSpace U ∧ ∀ {x y : U} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ :=
  simply_connected_iff_paths_homotopic'

end UndergradKB.DifferentialEquations.Course.Ch8
