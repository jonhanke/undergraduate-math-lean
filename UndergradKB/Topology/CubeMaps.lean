import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Separation.CompletelyRegular
import UndergradKB.Common.Attr

/-!
# Maps between cubes induced by continuous maps

Morris, *Topology Without Tears*, Lemma 10.4.3: the evaluation embedding of a space `X` into the
cube `I^{C(X,I)}` is natural in `X`.
-/

open Set Topology unitInterval

namespace UndergradKB.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The evaluation map `x ↦ (f x)_{f ∈ C(X,I)}` of `X` into the cube `I^{C(X,I)}`. -/
def tychonoffEval (X : Type*) [TopologicalSpace X] : X → (C(X, unitInterval) → unitInterval) :=
  fun x f => f x

/-- The map of cubes `I^{C(X,I)} → I^{C(Y,I)}`, `(t_f)_f ↦ (t_{g ∘ φ})_g`, induced by a map
`φ : X → Y`. -/
def cubeMap (φ : C(X, Y)) : (C(X, unitInterval) → unitInterval) → (C(Y, unitInterval) → unitInterval) :=
  fun t g => t (g.comp φ)

/-- Morris, Topology Without Tears, Lemma 10.4.3 (TP-316).  The induced map of cubes is continuous. -/
@[kb "morris2024" "Lemma 10.4.3, p. 328"]
theorem continuous_cubeMap (φ : C(X, Y)) : Continuous (cubeMap φ) :=
  continuous_pi fun g => continuous_apply (g.comp φ)

/-- Morris, Topology Without Tears, Lemma 10.4.3 (TP-316).  The induced map of cubes commutes with
the evaluation maps: `Φ ∘ e_X = e_Y ∘ φ`. -/
@[kb "morris2024" "Lemma 10.4.3, p. 328"]
theorem cubeMap_comp_tychonoffEval (φ : C(X, Y)) : cubeMap φ ∘ tychonoffEval X = tychonoffEval Y ∘ φ := rfl

/-- Morris, Topology Without Tears, Lemma 10.4.3 (TP-316).  The induced map of cubes sends the image
of `e_X` into the image of `e_Y`. -/
@[kb "morris2024" "Lemma 10.4.3, p. 328"]
theorem cubeMap_image_range_subset (φ : C(X, Y)) :
    cubeMap φ '' range (tychonoffEval X) ⊆ range (tychonoffEval Y) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨φ x, rfl⟩

/-- Morris, Topology Without Tears, Lemma 10.4.3 (TP-316).  The evaluation map is continuous. -/
@[kb "morris2024" "Lemma 10.4.3, p. 328"]
theorem continuous_tychonoffEval : Continuous (tychonoffEval X) :=
  continuous_pi fun f => f.continuous

/-- Morris, Topology Without Tears, Lemma 10.4.3 (TP-316).  For a Tychonoff (completely regular
T1) space the evaluation map into the cube is an embedding. -/
@[kb "morris2024" "Lemma 10.4.3, p. 328"]
theorem isEmbedding_tychonoffEval [T35Space X] : IsEmbedding (tychonoffEval X) := by
  refine ⟨?_, fun x y h => ?_⟩
  · rw [isInducing_iff_nhds]
    intro x
    refine le_antisymm (Filter.tendsto_iff_comap.mp continuous_tychonoffEval.continuousAt) ?_
    intro U hU
    obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.mp hU
    obtain ⟨f, hfc, hfx, hf1⟩ := CompletelyRegularSpace.completely_regular_isOpen x U' hU'o hxU'
    rw [Filter.mem_comap]
    refine ⟨(fun t : C(X, unitInterval) → unitInterval => t ⟨f, hfc⟩) ⁻¹' Iio 1, ?_, ?_⟩
    · refine (isOpen_Iio.preimage (continuous_apply _)).mem_nhds ?_
      show f x < 1
      rw [hfx]
      exact zero_lt_one
    · intro y hy
      apply hU'U
      by_contra hn
      have h1 : f y = 1 := hf1 hn
      have h2 : f y < 1 := hy
      exact absurd h1 h2.ne
  · by_contra hne
    obtain ⟨f, hfc, hf⟩ := separatesPoints_continuous_of_t35Space_Icc hne
    exact hf (congrFun h ⟨f, hfc⟩)

end UndergradKB.Topology
