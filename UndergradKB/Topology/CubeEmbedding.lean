import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.ProperSpace
import UndergradKB.Common.Attr

/-!
# Embedding into cubes

Cubes are the powers `ι → unitInterval` (written `I^ι`).  Every metric space embeds in the cube
`I^X`, every Tychonoff space in a cube (via the evaluation of all continuous maps to `I`), and the
subspaces of cubes are exactly the Tychonoff spaces.  Compact Hausdorff spaces are Tychonoff, and a
compact space is metrizable iff it is Hausdorff and second countable.
-/

open Topology Set Filter unitInterval

namespace UndergradKB.Topology

universe u

/-! ### Metric spaces -/

/-- The map `x ↦ (a ↦ min (d(x,a), 1))` of a metric space into the cube `I^X`. -/
def metricCubeMap (X : Type u) [MetricSpace X] : X → (X → I) :=
  fun x a => ⟨min (dist x a) 1, le_min dist_nonneg zero_le_one, min_le_right _ _⟩

theorem continuous_metricCubeMap (X : Type u) [MetricSpace X] :
    Continuous (metricCubeMap X) :=
  continuous_pi fun _ =>
    Continuous.subtype_mk ((continuous_id.dist continuous_const).min continuous_const) _

/-- Morris, Topology Without Tears, Proposition 10.3.7 (TP-278). Every metric space is
homeomorphic to a subspace of the cube `I^X`: the map `metricCubeMap` is an embedding. -/
@[kb "morris2024" "Proposition 10.3.7, p. 275"]
theorem isEmbedding_metricCubeMap (X : Type u) [MetricSpace X] :
    IsEmbedding (metricCubeMap X) := by
  have hind : IsInducing (metricCubeMap X) := by
    rw [isInducing_iff_nhds]
    intro x
    refine le_antisymm
      (map_le_iff_le_comap.mp (continuous_metricCubeMap X).continuousAt) ?_
    rw [le_nhds_iff]
    intro U hxU hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
    rw [mem_comap]
    refine ⟨{p : X → I | (p x : ℝ) < min ε 1}, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact isOpen_lt (continuous_subtype_val.comp (continuous_apply x)) continuous_const
      · simp [metricCubeMap, hε]
    · intro y hy
      apply hball
      have h : min (dist y x) 1 < min ε 1 := hy
      rcases min_lt_iff.mp h with h1 | h1
      · exact Metric.mem_ball.mpr (lt_of_lt_of_le h1 (min_le_left _ _))
      · exact absurd (min_le_right ε 1) (not_le.mpr h1)
  refine ⟨hind, ?_⟩
  intro x y h
  have h1 := congrArg Subtype.val (congrFun h x)
  simp only [metricCubeMap, dist_self] at h1
  by_contra hne
  have hpos : 0 < dist y x := dist_pos.mpr (Ne.symm hne)
  have : (0 : ℝ) < min (dist y x) 1 := lt_min hpos one_pos
  rw [dist_comm] at this
  have h2 : min (0 : ℝ) 1 = 0 := min_eq_left zero_le_one
  simp [dist_comm] at h1
  rw [← h1] at this
  simp at this

/-! ### Tychonoff spaces -/

/-- The evaluation map of `X` into the cube indexed by all continuous maps `X → I`. -/
def cubeEval (X : Type u) [TopologicalSpace X] : X → ({f : X → I // Continuous f} → I) :=
  fun x f => f.1 x

theorem continuous_cubeEval (X : Type u) [TopologicalSpace X] : Continuous (cubeEval X) :=
  continuous_pi fun f => f.2

/-- The Embedding Lemma for Tychonoff spaces: the evaluation map into the cube indexed by the
continuous maps `X → I` is an embedding. -/
theorem isEmbedding_cubeEval (X : Type u) [TopologicalSpace X] [T35Space X] :
    IsEmbedding (cubeEval X) := by
  have hind : IsInducing (cubeEval X) := by
    rw [isInducing_iff_nhds]
    intro x
    refine le_antisymm
      (map_le_iff_le_comap.mp (continuous_cubeEval X).continuousAt) ?_
    rw [le_nhds_iff]
    intro U hxU hU
    obtain ⟨g, hg, hgx, hgU⟩ := CompletelyRegularSpace.completely_regular_isOpen x U hU hxU
    rw [mem_comap]
    refine ⟨{p | p ⟨g, hg⟩ ≠ 1}, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact isOpen_compl_singleton.preimage (continuous_apply (⟨g, hg⟩ :
          {f : X → I // Continuous f}))
      · show g x ≠ 1
        rw [hgx]
        exact zero_ne_one
    · intro y hy
      by_contra hyU
      exact hy (hgU hyU)
  refine ⟨hind, ?_⟩
  intro x y h
  by_contra hne
  obtain ⟨f, hf, hfxy⟩ := separatesPoints_continuous_of_t35Space_Icc hne
  exact hfxy (congrFun h ⟨f, hf⟩)

/-- Morris, Topology Without Tears, Proposition 10.3.17 (TP-285). Every Tychonoff space is
homeomorphic to a subspace of a cube `I^ι`. -/
@[kb "morris2024" "Proposition 10.3.17, p. 278"]
theorem exists_isEmbedding_cube_of_t35 (X : Type u) [TopologicalSpace X] [T35Space X] :
    ∃ (ι : Type u) (e : X → (ι → I)), IsEmbedding e :=
  ⟨_, cubeEval X, isEmbedding_cubeEval X⟩

/-- Morris, Topology Without Tears, Proposition 10.3.18 (TP-286). A space embeds in a cube
if and only if it is a Tychonoff space. -/
@[kb "morris2024" "Proposition 10.3.18, p. 278"]
theorem exists_isEmbedding_cube_iff_t35 (X : Type u) [TopologicalSpace X] :
    (∃ (ι : Type u) (e : X → (ι → I)), IsEmbedding e) ↔ T35Space X := by
  constructor
  · rintro ⟨ι, e, he⟩
    exact he.t35Space
  · intro h
    exact exists_isEmbedding_cube_of_t35 X

/-! ### Compact Hausdorff spaces -/

/-- Morris, Topology Without Tears, Corollary 10.3.25 (TP-292). Every compact Hausdorff space
embeds in a cube. -/
@[kb "morris2024" "Corollary 10.3.25, p. 280"]
theorem exists_isEmbedding_cube_of_compact_t2 (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : ∃ (ι : Type u) (e : X → (ι → I)), IsEmbedding e :=
  exists_isEmbedding_cube_of_t35 X

/-- Morris, Topology Without Tears, Corollary 10.3.32 (TP-298). A compact space is metrizable
if and only if it is Hausdorff and second countable. -/
@[kb "morris2024" "Corollary 10.3.32, p. 285"]
theorem compact_metrizableSpace_iff (X : Type u) [TopologicalSpace X] [CompactSpace X] :
    TopologicalSpace.MetrizableSpace X ↔ T2Space X ∧ SecondCountableTopology X := by
  constructor
  · intro h
    let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨h2, hs⟩
    infer_instance

end UndergradKB.Topology
