import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-! # Course layer, Morris: exercises of Chapters 6 and 7 (wave 4, part f)

Thin theorems for standard facts that Morris, *Topology Without Tears*, sets as exercises in Chapter 6
(metric spaces: convergence, sequential closure, completeness, separability) and Chapter 7
(compactness: closed subsets, continuous bijections, separation of compact sets).
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace

section Chapter6

variable {X : Type*}

/-- Morris, Topology Without Tears, Exercises 6.1 #5. For a fixed point `a` of a metric space, the map
`x ↦ d(a, x)` into `ℝ` is continuous. -/
@[kb "morris2024" "Exercises 6.1 #5, p. 136"]
theorem morris_exercise_6_1_5 [PseudoMetricSpace X] (a : X) : Continuous fun x => dist a x :=
  continuous_const.dist continuous_id

/-- Morris, Topology Without Tears, Exercises 6.2 #2. A sequence in a metric space has at most one
limit. -/
@[kb "morris2024" "Exercises 6.2 #2, p. 146"]
theorem morris_exercise_6_2_2 [MetricSpace X] {u : ℕ → X} {x y : X} (hx : Tendsto u atTop (𝓝 x))
    (hy : Tendsto u atTop (𝓝 y)) : x = y :=
  tendsto_nhds_unique hx hy

/-- Morris, Topology Without Tears, Exercises 6.2 #3(i). In a metric space, `xₙ → x` iff every open
set containing `x` contains `xₙ` for all large `n`. -/
@[kb "morris2024" "Exercises 6.2 #3(i), p. 146"]
theorem morris_exercise_6_2_3_i [TopologicalSpace X] (u : ℕ → X) (x : X) :
    Tendsto u atTop (𝓝 x) ↔ ∀ U : Set X, IsOpen U → x ∈ U → ∃ n₀, ∀ n ≥ n₀, u n ∈ U := by
  rw [tendsto_atTop']
  constructor
  · intro h U hU hx
    obtain ⟨a, ha⟩ := h U (hU.mem_nhds hx)
    exact ⟨a, fun n hn => ha n hn⟩
  · intro h U hU
    obtain ⟨a, ha⟩ := h (interior U) isOpen_interior (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨a, fun n hn => interior_subset (ha n hn)⟩

/-- Morris, Topology Without Tears, Exercises 6.2 #5. In a topological space, a sequence may converge
to two different points: in an indiscrete two-point space, a constant sequence converges to both
points. -/
@[kb "morris2024" "Exercises 6.2 #5, p. 146"]
theorem morris_exercise_6_2_5 :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (u : ℕ → Z) (x y : Z),
      Tendsto u atTop (𝓝 x) ∧ Tendsto u atTop (𝓝 y) ∧ x ≠ y := by
  refine ⟨Bool, ⊤, fun _ => true, true, false, ?_, ?_, by decide⟩
  · rw [nhds_top]; exact tendsto_top
  · rw [nhds_top]; exact tendsto_top

/-- Morris, Topology Without Tears, Exercises 6.2 #6(i). If `xₙ → x` in a metric space, the set
consisting of `x` and all the `xₙ` is closed. -/
@[kb "morris2024" "Exercises 6.2 #6(i), p. 146"]
theorem morris_exercise_6_2_6_i [MetricSpace X] {u : ℕ → X} {x : X} (h : Tendsto u atTop (𝓝 x)) :
    IsClosed (insert x (range u)) :=
  h.isCompact_insert_range.isClosed

/-- Morris, Topology Without Tears, Exercises 6.2 #8. If `xₙ → x` and `yₙ → y` then `(xₙ, yₙ) → (x, y)`
in the product metric. -/
@[kb "morris2024" "Exercises 6.2 #8, p. 146"]
theorem morris_exercise_6_2_8 {Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {u : ℕ → X}
    {v : ℕ → Y} {x : X} {y : Y} (hu : Tendsto u atTop (𝓝 x)) (hv : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun n => (u n, v n)) atTop (𝓝 (x, y)) :=
  hu.prodMk_nhds hv

/-- Morris, Topology Without Tears, Exercises 6.2 #9(i). In a metric space, the closure of a non-empty
set `S` is the set of points at distance zero from `S`. -/
@[kb "morris2024" "Exercises 6.2 #9(i), p. 147"]
theorem morris_exercise_6_2_9_i [PseudoMetricSpace X] {S : Set X} (hS : S.Nonempty) :
    closure S = {x | Metric.infDist x S = 0} := by
  ext x
  exact Metric.mem_closure_iff_infDist_zero hS

/-- Morris, Topology Without Tears, Exercises 6.2 #9(ii). The distance to a fixed set is a continuous
function on a metric space. -/
@[kb "morris2024" "Exercises 6.2 #9(ii), p. 147"]
theorem morris_exercise_6_2_9_ii [PseudoMetricSpace X] (S : Set X) : Continuous fun x => Metric.infDist x S :=
  Metric.continuous_infDist_pt S

/-- Morris, Topology Without Tears, Exercises 6.2 #11(i). In a metric space every sequentially closed
set is closed. -/
@[kb "morris2024" "Exercises 6.2 #11(i), p. 147"]
theorem morris_exercise_6_2_11_i [PseudoMetricSpace X] {S : Set X} (h : IsSeqClosed S) : IsClosed S :=
  h.isClosed

/-- Morris, Topology Without Tears, Exercises 6.2 #11(vi). Every first countable space is a
Frechet-Urysohn space, and every Frechet-Urysohn space is a sequential space. -/
@[kb "morris2024" "Exercises 6.2 #11(vi), p. 147"]
theorem morris_exercise_6_2_11_vi [TopologicalSpace X] :
    (FirstCountableTopology X → FrechetUrysohnSpace X) ∧
      (FrechetUrysohnSpace X → SequentialSpace X) :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-- Morris, Topology Without Tears, Exercises 6.2 #11(vii). Every subspace of a Frechet-Urysohn space
is a Frechet-Urysohn space. -/
@[kb "morris2024" "Exercises 6.2 #11(vii), p. 147"]
theorem morris_exercise_6_2_11_vii [TopologicalSpace X] [FrechetUrysohnSpace X] (S : Set X) :
    FrechetUrysohnSpace S :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 6.2 #11(vii)*. On a sequential space (in particular a
metrizable space), a sequentially continuous map into any space is continuous. -/
@[kb "morris2024" "Exercises 6.2 #11(vii)*, p. 147"]
theorem morris_exercise_6_2_11_vii_star {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SequentialSpace X] {f : X → Y} (hf : SeqContinuous f) : Continuous f :=
  continuous_iff_seqContinuous.2 hf

/-- Morris, Topology Without Tears, Exercises 6.3 #2. A subsequence of a Cauchy sequence is a Cauchy
sequence. -/
@[kb "morris2024" "Exercises 6.3 #2, p. 160"]
theorem morris_exercise_6_3_2 [PseudoMetricSpace X] {u : ℕ → X} (hu : CauchySeq u) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : CauchySeq (u ∘ φ) :=
  hu.comp_tendsto hφ.tendsto_atTop

/-- Morris, Topology Without Tears, Exercises 6.3 #4. Euclidean `m`-space is a complete metric
space. -/
@[kb "morris2024" "Exercises 6.3 #4, p. 160"]
theorem morris_exercise_6_3_4 (m : ℕ) : CompleteSpace (EuclideanSpace ℝ (Fin m)) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 6.3 #5(a). A closed subset of a complete metric space is
complete. -/
@[kb "morris2024" "Exercises 6.3 #5(a), p. 160"]
theorem morris_exercise_6_3_5_a [PseudoMetricSpace X] [CompleteSpace X] {S : Set X} (hS : IsClosed S) :
    IsComplete S :=
  hS.isComplete

/-- Morris, Topology Without Tears, Exercises 6.3 #5(b). A complete subset of a metric space is
closed. -/
@[kb "morris2024" "Exercises 6.3 #5(b), p. 160"]
theorem morris_exercise_6_3_5_b [MetricSpace X] {S : Set X} (hS : IsComplete S) : IsClosed S :=
  hS.isClosed

/-- Morris, Topology Without Tears, Exercises 6.3 #6. Euclidean `n`-space is a Polish space. -/
@[kb "morris2024" "Exercises 6.3 #6, p. 160"]
theorem morris_exercise_6_3_6 (n : ℕ) : PolishSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 6.3 #7. The intervals `[a, b]` and `(a, b)` are Polish
spaces, being a closed and an open subspace of `ℝ`. -/
@[kb "morris2024" "Exercises 6.3 #7, p. 161"]
theorem morris_exercise_6_3_7 (a b : ℝ) : PolishSpace (Icc a b) ∧ PolishSpace (Ioo a b) :=
  ⟨isClosed_Icc.polishSpace, isOpen_Ioo.polishSpace⟩

/-- Morris, Topology Without Tears, Exercises 6.3 #13(ii). The set of points of a convergent sequence
is bounded. -/
@[kb "morris2024" "Exercises 6.3 #13(ii), p. 161"]
theorem morris_exercise_6_3_13_ii [PseudoMetricSpace X] {u : ℕ → X} {x : X} (h : Tendsto u atTop (𝓝 x)) :
    Bornology.IsBounded (range u) :=
  Metric.isBounded_range_of_tendsto u h

/-- Morris, Topology Without Tears, Exercises 6.3 #13(iii). The set of points of a Cauchy sequence is
bounded. -/
@[kb "morris2024" "Exercises 6.3 #13(iii), p. 161"]
theorem morris_exercise_6_3_13_iii [PseudoMetricSpace X] {u : ℕ → X} (h : CauchySeq u) :
    Bornology.IsBounded (range u) :=
  h.isBounded_range

/-- Morris, Topology Without Tears, Exercises 6.3 #14. A metric space is separable iff its topology
satisfies the second axiom of countability. -/
@[kb "morris2024" "Exercises 6.3 #14, p. 161"]
theorem morris_exercise_6_3_14 [PseudoMetricSpace X] : SeparableSpace X ↔ SecondCountableTopology X :=
  ⟨fun _ => UniformSpace.secondCountable_of_separable X, fun _ => inferInstance⟩

/-- Morris, Topology Without Tears, Exercises 6.3 #15. Every subspace of a separable metric space is
separable. -/
@[kb "morris2024" "Exercises 6.3 #15, p. 162"]
theorem morris_exercise_6_3_15 [PseudoMetricSpace X] [SeparableSpace X] (Y : Set X) : SeparableSpace Y :=
  have := UniformSpace.secondCountable_of_separable X
  inferInstance

end Chapter6

section Chapter7

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Morris, Topology Without Tears, Exercises 7.1 #1. In an indiscrete space every subset is
compact. -/
@[kb "morris2024" "Exercises 7.1 #1, p. 180"]
theorem morris_exercise_7_1_1 (h : ∀ U : Set X, IsOpen U → U = ∅ ∨ U = univ) (S : Set X) : IsCompact S := by
  refine isCompact_of_finite_subcover fun {ι} U hU hcov => ?_
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨∅, by simp⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hx)
    rcases h _ (hU i) with h0 | h0
    · rw [h0] at hi; exact absurd hi (notMem_empty x)
    · refine ⟨{i}, fun y _ => ?_⟩
      simp [h0]

/-- Morris, Topology Without Tears, Exercises 7.1 #3(i),(ii). The intervals `(0, 1)` and `[0, 1)` are
not compact subsets of `ℝ`. -/
@[kb "morris2024" "Exercises 7.1 #3(i), p. 180"]
theorem morris_exercise_7_1_3_i : ¬ IsCompact (Ioo (0 : ℝ) 1) ∧ ¬ IsCompact (Ico (0 : ℝ) 1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := isClosed_Ioo_iff.1 h.isClosed
    norm_num at this
  · have := isClosed_Ico_iff.1 h.isClosed
    norm_num at this

/-- Morris, Topology Without Tears, Exercises 7.1 #3(v). The plane `ℝ²` is not compact. -/
@[kb "morris2024" "Exercises 7.1 #3(v), p. 180"]
theorem morris_exercise_7_1_3_v : NoncompactSpace (ℝ × ℝ) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 7.1 #6. The set `{0} ∪ {1/n : n ≥ 1}` is a compact
subset of `ℝ`. -/
@[kb "morris2024" "Exercises 7.1 #6, p. 180"]
theorem morris_exercise_7_1_6 : IsCompact (insert (0 : ℝ) (range fun n : ℕ => 1 / ((n : ℝ) + 1))) :=
  (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).isCompact_insert_range

/-- Morris, Topology Without Tears, Exercises 7.2 #3. In a compact space, if a family of closed sets
has empty intersection, some finite subfamily has empty intersection. -/
@[kb "morris2024" "Exercises 7.2 #3, p. 186"]
theorem morris_exercise_7_2_3 [CompactSpace X] {I : Type*} (F : I → Set X) (hF : ∀ i, IsClosed (F i))
    (h : ⋂ i, F i = ∅) : ∃ u : Finset I, ⋂ i ∈ u, F i = ∅ := by
  obtain ⟨u, hu⟩ := isCompact_univ.elim_finite_subfamily_closed F hF
    (by rw [h]; exact disjoint_empty _)
  exact ⟨u, by simpa using hu⟩

/-- Morris, Topology Without Tears, Exercises 7.2 #5(b). A continuous map from a compact space to a
Hausdorff space is a closed map. -/
@[kb "morris2024" "Exercises 7.2 #5(b), p. 187"]
theorem morris_exercise_7_2_5_b [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f) :
    IsClosedMap f :=
  hf.isClosedMap

/-- Morris, Topology Without Tears, Exercises 7.2 #6. A continuous bijection from a compact space to a
Hausdorff space is a homeomorphism. -/
@[kb "morris2024" "Exercises 7.2 #6, p. 187"]
theorem morris_exercise_7_2_6 [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f)
    (hb : Function.Bijective f) : IsHomeomorph f :=
  (isHomeomorph_iff_continuous_bijective).2 ⟨hf, hb⟩

/-- Morris, Topology Without Tears, Exercises 7.2 #7. An intersection of a non-empty family of closed
compact subsets of a space is compact. -/
@[kb "morris2024" "Exercises 7.2 #7, p. 187"]
theorem morris_exercise_7_2_7 {J : Type*} [Nonempty J] {C : J → Set X} (hC : ∀ j, IsCompact (C j))
    (hcl : ∀ j, IsClosed (C j)) : IsCompact (⋂ j, C j) := by
  obtain ⟨j⟩ := ‹Nonempty J›
  exact (hC j).of_isClosed_subset (isClosed_iInter hcl) (iInter_subset C j)

/-- Morris, Topology Without Tears, Exercises 7.2 #10. Every compact Hausdorff space is normal. -/
@[kb "morris2024" "Exercises 7.2 #10, p. 188"]
theorem morris_exercise_7_2_10 [CompactSpace X] [T2Space X] : NormalSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 7.2 #11. Disjoint compact subsets of a Hausdorff space
have disjoint open neighbourhoods. -/
@[kb "morris2024" "Exercises 7.2 #11, p. 188"]
theorem morris_exercise_7_2_11 [T2Space X] {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) : ∃ G H : Set X, IsOpen G ∧ IsOpen H ∧ A ⊆ G ∧ B ⊆ H ∧ Disjoint G H := by
  obtain ⟨G, H, hG, hH, hAG, hBH, hGH⟩ := SeparatedNhds.of_isCompact_isCompact hA hB hAB
  exact ⟨G, H, hG, hH, hAG, hBH, hGH⟩

end Chapter7

end UndergradKB.Topology.Course
