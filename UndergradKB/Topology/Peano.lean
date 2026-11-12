import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.UnitInterval
import UndergradKB.Common.Attr

/-! # Peano's space-filling curve (Morris, Theorem 9.5.9)

For each `n` there is a continuous map of `[0, 1]` onto the `n`-cube `Iⁿ`. The book's proof: the Cantor space maps
continuously onto `Iⁿ` (Hausdorff-Alexandroff, Mathlib's `exists_nat_bool_continuous_surjective_of_compact`); the
Cantor set is a closed subset of `[0, 1]` homeomorphic to the Cantor space; extend over the omitted intervals. The
book extends linearly on each omitted interval; here the extension is the Tietze extension theorem for the cube
(Mathlib's `TietzeExtension` instances for `unitInterval` and finite products), which gives the same conclusion. -/

open Set Topology

namespace UndergradKB.Topology

/-- A continuous map from the Cantor set (a closed subset of `ℝ` inside `[0, 1]`) onto a nonempty compact metric
space whose points can be extended (a Tietze space) extends to a continuous map of `[0, 1]` onto that space. -/
theorem exists_continuous_surjective_unitInterval_of_tietze (Y : Type) [Nonempty Y] [MetricSpace Y]
    [CompactSpace Y] [TietzeExtension.{0} Y] :
    ∃ f : unitInterval → Y, Continuous f ∧ Function.Surjective f := by
  obtain ⟨g, hg, hgs⟩ := exists_nat_bool_continuous_surjective_of_compact Y
  let φ : C(cantorSet, Y) := ⟨g ∘ cantorSetHomeomorphNatToBool, hg.comp (Homeomorph.continuous _)⟩
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq isClosed_cantorSet φ
  refine ⟨fun t ↦ G t, G.continuous.comp continuous_subtype_val, fun y ↦ ?_⟩
  obtain ⟨b, rfl⟩ := hgs y
  let c := cantorSetHomeomorphNatToBool.symm b
  refine ⟨⟨c, cantorSet_subset_unitInterval c.2⟩, ?_⟩
  have := congrArg (fun F : C(cantorSet, Y) ↦ F c) hG
  simpa [φ, c] using this

/-- Morris, Topology Without Tears, Theorem 9.5.9 (TP-233), Peano's theorem. For each positive integer `n` there
is a continuous map of `[0, 1]` onto the `n`-cube `Iⁿ = [0, 1]ⁿ`. -/
@[kb "morris2024" "Theorem 9.5.9, p. 252"]
theorem peano_exists_continuous_surjective_cube (n : ℕ) (_hn : 0 < n) :
    ∃ ψ : unitInterval → (Fin n → unitInterval), Continuous ψ ∧ Function.Surjective ψ :=
  exists_continuous_surjective_unitInterval_of_tietze _

/-- The same argument maps `[0, 1]` continuously onto the Hilbert cube `I^ℕ` (a companion of Morris,
Theorem 9.5.9, TP-233). -/
@[kb "morris2024" "Theorem 9.5.9, p. 252"]
theorem exists_continuous_surjective_hilbertCube :
    ∃ ψ : unitInterval → (ℕ → unitInterval), Continuous ψ ∧ Function.Surjective ψ := by
  let _ : MetricSpace (ℕ → unitInterval) := TopologicalSpace.metrizableSpaceMetric _
  exact exists_continuous_surjective_unitInterval_of_tietze _

end UndergradKB.Topology
