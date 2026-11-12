import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.UnitInterval
import UndergradKB.Common.Attr

/-!
# Countable products: Cantor space, Hilbert cube, Urysohn embedding, Cantor surjections

Morris, *Topology Without Tears*, Chapter 9 (sections 9.3 to 9.5).  The Cantor space is `ℕ → Bool`
(Mathlib's convention), the Hilbert cube is `ℕ → unitInterval`.
-/

open Set Topology TopologicalSpace unitInterval

namespace UndergradKB.Topology

/-! ### TP-209: the Cantor space and its powers -/

/-- Morris, Topology Without Tears, Proposition 9.3.3 (TP-209).  The Cantor space is homeomorphic
to each of its positive finite powers. -/
@[kb "morris2024" "Proposition 9.3.3, p. 230"]
theorem cantorSpace_homeo_fin_pow (n : ℕ) (hn : n ≠ 0) :
    Nonempty ((ℕ → Bool) ≃ₜ (Fin n → ℕ → Bool)) := by
  have : NeZero n := ⟨hn⟩
  let e : Fin n × ℕ ≃ ℕ := (Equiv.prodComm _ _).trans (Nat.divModEquiv n).symm
  exact ⟨((Homeomorph.piCongrLeft (Y := fun _ : ℕ => Bool) e).symm).trans Homeomorph.piCurry⟩

/-- Morris, Topology Without Tears, Proposition 9.3.3 (TP-209).  The Cantor space is homeomorphic
to its countable power. -/
@[kb "morris2024" "Proposition 9.3.3, p. 230"]
theorem cantorSpace_homeo_nat_pow : Nonempty ((ℕ → Bool) ≃ₜ (ℕ → ℕ → Bool)) :=
  ⟨cantorSpaceHomeomorphNatToCantorSpace⟩

/-- Morris, Topology Without Tears, Proposition 9.3.3 (TP-209).  If every `G i` (`i < n`, `n ≥ 1`)
is homeomorphic to the Cantor space, so is the finite product. -/
@[kb "morris2024" "Proposition 9.3.3, p. 230"]
theorem cantorSpace_homeo_pi_fin {n : ℕ} (hn : n ≠ 0) (G : Fin n → Type*)
    [∀ i, TopologicalSpace (G i)] (h : ∀ i, Nonempty (G i ≃ₜ (ℕ → Bool))) :
    Nonempty ((ℕ → Bool) ≃ₜ (∀ i, G i)) := by
  obtain ⟨e⟩ := cantorSpace_homeo_fin_pow n hn
  exact ⟨e.trans (Homeomorph.piCongrRight fun i => (h i).some.symm)⟩

/-- Morris, Topology Without Tears, Proposition 9.3.3 (TP-209).  If every `G i` (`i : ℕ`) is
homeomorphic to the Cantor space, so is the countable product. -/
@[kb "morris2024" "Proposition 9.3.3, p. 230"]
theorem cantorSpace_homeo_pi_nat (G : ℕ → Type*)
    [∀ i, TopologicalSpace (G i)] (h : ∀ i, Nonempty (G i ≃ₜ (ℕ → Bool))) :
    Nonempty ((ℕ → Bool) ≃ₜ (∀ i, G i)) :=
  ⟨cantorSpaceHomeomorphNatToCantorSpace.trans
    (Homeomorph.piCongrRight fun i => (h i).some.symm)⟩

/-! ### TP-211: Hilbert cube and n-cube -/

/-- Morris, Topology Without Tears, Definition 9.3.7 (TP-211).  The Hilbert cube `I^∞`, the
countable product of copies of `[0,1]`. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
abbrev HilbertCube : Type := ℕ → unitInterval

/-- Morris, Topology Without Tears, Definition 9.3.7 (TP-211).  The `n`-cube `I^n`, the `n`-fold
product of copies of `[0,1]`. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
abbrev NCube (n : ℕ) : Type := Fin n → unitInterval

/-- Morris, Topology Without Tears, Definition 9.3.7 (TP-211).  A countable product of spaces each
homeomorphic to `[0,1]` is homeomorphic to the Hilbert cube. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
theorem nonempty_homeo_hilbertCube (Y : ℕ → Type*) [∀ i, TopologicalSpace (Y i)]
    (h : ∀ i, Nonempty (Y i ≃ₜ unitInterval)) : Nonempty ((∀ i, Y i) ≃ₜ HilbertCube) :=
  ⟨Homeomorph.piCongrRight fun i => (h i).some⟩

/-- Morris, Topology Without Tears, Definition 9.3.7 (TP-211).  A finite product of spaces each
homeomorphic to `[0,1]` is homeomorphic to the `n`-cube. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
theorem nonempty_homeo_nCube {n : ℕ} (Y : Fin n → Type*) [∀ i, TopologicalSpace (Y i)]
    (h : ∀ i, Nonempty (Y i ≃ₜ unitInterval)) : Nonempty ((∀ i, Y i) ≃ₜ NCube n) :=
  ⟨Homeomorph.piCongrRight fun i => (h i).some⟩

/-- Morris, Topology Without Tears, Theorem 9.3.8 (TP-211).  The Hilbert cube is compact. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
theorem compactSpace_hilbertCube : CompactSpace HilbertCube := inferInstance

/-- Morris, Topology Without Tears, Definition 9.3.7 (TP-211).  The `n`-cube is compact. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
theorem compactSpace_nCube (n : ℕ) : CompactSpace (NCube n) := inferInstance

/-- Morris, Topology Without Tears, Definition 9.3.7 (TP-211).  The Hilbert cube is metrizable. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
theorem metrizableSpace_hilbertCube : MetrizableSpace HilbertCube := inferInstance

/-- Morris, Topology Without Tears, Definition 9.3.7 (TP-211).  The `n`-cube is metrizable. -/
@[kb "morris2024" "Definition 9.3.7, p. 231"]
theorem metrizableSpace_nCube (n : ℕ) : MetrizableSpace (NCube n) := inferInstance

/-! ### TP-220: the Embedding Lemma, countable families -/

section Embedding

variable {X : Type*} [TopologicalSpace X]

private theorem isEmbedding_eval_aux {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i))
    (hpt : ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y)
    (hcl : ∀ x (A : Set X), IsClosed A → x ∉ A → ∃ i, f i x ∉ closure (f i '' A)) :
    IsEmbedding (fun x i => f i x) := by
  refine ⟨?_, fun x y hxy => ?_⟩
  · rw [isInducing_iff_nhds]
    intro x
    refine le_antisymm (Filter.tendsto_iff_comap.mp (continuous_pi hf).continuousAt) ?_
    intro U hU
    obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.mp hU
    obtain ⟨i, hi⟩ := hcl x U'ᶜ hU'o.isClosed_compl (fun h => h hxU')
    rw [Filter.mem_comap]
    refine ⟨(fun z : ∀ i, Y i => z i) ⁻¹' (closure (f i '' U'ᶜ))ᶜ, ?_, ?_⟩
    · exact ((continuous_apply i).isOpen_preimage _ isClosed_closure.isOpen_compl).mem_nhds hi
    · intro t ht
      apply hU'U
      by_contra hn
      exact ht (subset_closure ⟨t, hn, rfl⟩)
  · by_contra hne
    obtain ⟨i, hi⟩ := hpt x y hne
    exact hi (congrFun hxy i)

variable {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)]

/-- Morris, Topology Without Tears, Lemma 9.4.7 (TP-220).  The Embedding Lemma for a countable
family: continuous maps `f i : X → Y i` that separate points and separate points from closed sets
give an embedding `x ↦ (f i x)_i` of `X` into the product. -/
@[kb "morris2024" "Lemma 9.4.7, p. 239"]
theorem isEmbedding_eval_nat (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i))
    (hpt : ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y)
    (hcl : ∀ x (A : Set X), IsClosed A → x ∉ A → ∃ i, f i x ∉ closure (f i '' A)) :
    IsEmbedding (fun x i => f i x) :=
  isEmbedding_eval_aux f hf hpt hcl

/-- Morris, Topology Without Tears, Corollary 9.4.10 (TP-220).  For a T1 domain, separating points
from closed sets already gives the embedding (separating points is superfluous). -/
@[kb "morris2024" "Corollary 9.4.10, p. 240"]
theorem isEmbedding_eval_nat_of_t1 [T1Space X] (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i))
    (hcl : ∀ x (A : Set X), IsClosed A → x ∉ A → ∃ i, f i x ∉ closure (f i '' A)) :
    IsEmbedding (fun x i => f i x) := by
  refine isEmbedding_eval_aux f hf (fun x y hxy => ?_) hcl
  obtain ⟨i, hi⟩ := hcl x {y} isClosed_singleton (fun h => hxy h)
  exact ⟨i, fun h => hi (by rw [h]; exact subset_closure ⟨y, rfl, rfl⟩)⟩

end Embedding

/-! ### TP-223: compact metrizable spaces in the Hilbert cube -/

/-- Morris, Topology Without Tears, Corollary 9.4.12 (TP-223).  Every compact metrizable space is
homeomorphic to a closed subspace of the Hilbert cube: there is a closed embedding into it. -/
@[kb "morris2024" "Corollary 9.4.12, p. 241"]
theorem exists_isClosedEmbedding_hilbertCube (X : Type*) [TopologicalSpace X] [MetrizableSpace X]
    [CompactSpace X] : ∃ F : X → HilbertCube, IsClosedEmbedding F := by
  let _ : MetricSpace X := metrizableSpaceMetric X
  have : SeparableSpace X := SecondCountableTopology.to_separableSpace
  obtain ⟨F, hF⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  exact ⟨F, hF.continuous.isClosedEmbedding hF.injective⟩

/-! ### TP-228: separable metrizable spaces as images of subspaces of the Cantor space -/

/-- Morris, Topology Without Tears, Proposition 9.5.2 (TP-228).  Every separable metrizable space is
a continuous image of a subspace `Z` of the Cantor space `ℕ → Bool`, and `Z` can be chosen closed
when the space is compact. -/
@[kb "morris2024" "Proposition 9.5.2, p. 249"]
theorem exists_subspace_cantorSpace_continuous_surjective (X : Type*) [TopologicalSpace X]
    [MetrizableSpace X] [SeparableSpace X] :
    ∃ (Z : Set (ℕ → Bool)) (g : Z → X), Continuous g ∧ Function.Surjective g ∧
      (CompactSpace X → IsClosed Z) := by
  let _ : MetricSpace X := metrizableSpaceMetric X
  obtain ⟨F, hF⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  refine ⟨cantorToHilbert ⁻¹' range F,
    hF.toHomeomorph.symm ∘ (range F).restrictPreimage cantorToHilbert, ?_, ?_, ?_⟩
  · exact hF.toHomeomorph.symm.continuous.comp (Continuous.restrictPreimage cantorToHilbert_continuous)
  · exact hF.toHomeomorph.symm.surjective.comp
      (Set.restrictPreimage_surjective _ cantorToHilbert_surjective)
  · intro _
    exact (isCompact_range hF.continuous).isClosed.preimage cantorToHilbert_continuous

/-! ### TP-231, TP-232: continuous images of compact metric spaces -/

/-- A continuous surjection from a compact second countable space onto a Hausdorff space has a
second countable codomain. -/
theorem secondCountableTopology_of_continuous_surjective {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hs : Function.Surjective f) : SecondCountableTopology Y := by
  have hcl : IsClosedMap f := hf.isClosedMap
  let 𝒰 : Set (Set X) := (fun t : Set (Set X) => ⋃₀ t) '' {t | t.Finite ∧ t ⊆ countableBasis X}
  have h𝒰 : 𝒰.Countable := (Set.countable_ofPred_finite_subset (countable_countableBasis X)).image _
  let 𝒱 : Set (Set Y) := (fun U => (f '' Uᶜ)ᶜ) '' 𝒰
  have h𝒱 : 𝒱.Countable := h𝒰.image _
  have hB : IsTopologicalBasis 𝒱 := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨U, ⟨t, ⟨htf, htB⟩, rfl⟩, rfl⟩
      refine (hcl _ ?_).isOpen_compl
      exact (isOpen_sUnion fun s hs => isOpen_of_mem_countableBasis (htB hs)).isClosed_compl
    · intro y W hyW hWo
      have hK : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf).isCompact
      have hsub : f ⁻¹' {y} ⊆ ⋃ s ∈ {s | s ∈ countableBasis X ∧ s ⊆ f ⁻¹' W}, id s := by
        intro x hx
        have hxW : x ∈ f ⁻¹' W := by
          have : f x = y := hx
          simpa [this] using hyW
        obtain ⟨s, hsB, hxs, hsW⟩ :=
          (isBasis_countableBasis X).exists_subset_of_mem_open hxW (hWo.preimage hf)
        exact mem_iUnion₂.mpr ⟨s, ⟨hsB, hsW⟩, hxs⟩
      obtain ⟨b', hb'sub, hb'fin, hcov⟩ := hK.elim_finite_subcover_image
        (b := {s | s ∈ countableBasis X ∧ s ⊆ f ⁻¹' W}) (c := id)
        (fun s hs' => isOpen_of_mem_countableBasis hs'.1) hsub
      refine ⟨(f '' (⋃₀ b')ᶜ)ᶜ, ⟨⋃₀ b', ⟨b', ⟨hb'fin, fun s hs => (hb'sub hs).1⟩, rfl⟩, rfl⟩,
        ?_, ?_⟩
      · rintro ⟨x, hx, hxy⟩
        apply hx
        obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (hcov (show x ∈ f ⁻¹' {y} from hxy))
        exact ⟨s, hs, hxs⟩
      · intro y' hy'
        obtain ⟨x, rfl⟩ := hs y'
        have hx : x ∈ ⋃₀ b' := by
          by_contra hn
          exact hy' ⟨x, hn, rfl⟩
        obtain ⟨s, hs, hxs⟩ := hx
        exact (hb'sub hs).2 hxs
  exact hB.secondCountableTopology h𝒱

/-- A continuous surjection from a compact second countable space onto a Hausdorff space has a
compact metrizable codomain. -/
theorem compactSpace_metrizableSpace_of_continuous_surjective {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hs : Function.Surjective f) : CompactSpace Y ∧ MetrizableSpace Y := by
  have : CompactSpace Y := ⟨hs.range_eq ▸ isCompact_range hf⟩
  have :=secondCountableTopology_of_continuous_surjective hf hs
  exact ⟨inferInstance, inferInstance⟩

/-- Morris, Topology Without Tears, Proposition 9.5.6 (TP-231).  A continuous map of a compact
metric space onto a Hausdorff space has compact metrizable codomain. -/
@[kb "morris2024" "Proposition 9.5.6, p. 251"]
theorem compactSpace_metrizableSpace_of_metric_surjective {X Y : Type*} [MetricSpace X]
    [CompactSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hf : Continuous f)
    (hs : Function.Surjective f) : CompactSpace Y ∧ MetrizableSpace Y :=
  compactSpace_metrizableSpace_of_continuous_surjective hf hs

/-- Morris, Topology Without Tears, Corollary 9.5.7 (TP-232).  A (nonempty) Hausdorff space is a
continuous image of the Cantor space `ℕ → Bool` if and only if it is compact and metrizable.  (The
empty space is excluded, since the Cantor space is nonempty.) -/
@[kb "morris2024" "Corollary 9.5.7, p. 252"]
theorem exists_continuous_surjective_cantorSpace_iff (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [Nonempty Y] :
    (∃ f : (ℕ → Bool) → Y, Continuous f ∧ Function.Surjective f) ↔
      CompactSpace Y ∧ MetrizableSpace Y := by
  constructor
  · rintro ⟨f, hf, hs⟩
    exact compactSpace_metrizableSpace_of_continuous_surjective hf hs
  · rintro ⟨hc, hm⟩
    let _ : MetricSpace Y := metrizableSpaceMetric Y
    exact exists_nat_bool_continuous_surjective_of_compact Y

end UndergradKB.Topology
