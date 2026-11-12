import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ClusterPt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs
import UndergradKB.Common.Attr

/-!
# Nets (Morris, Appendix 6, Section 3)

Mathlib has no net type: a net is a function `φ : D → X` on a directed index type `D`
(`[Preorder D] [IsDirectedOrder D] [Nonempty D]`) and its limit is `Tendsto φ atTop (𝓝 a)`.
Here the book's notions (convergence, cluster point, ultranet, subnet) are given as small bridging
definitions stated exactly as in the book, and proved equivalent to the Mathlib filter formulations;
then the book's propositions are proved literally for nets.

Index types of the nets that the converse directions build live in the universe of `X`.
-/

open Filter Topology Set

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

universe u v w

namespace Net

variable {X : Type u} [TopologicalSpace X]

section Defs

variable {D : Type v} [Preorder D]

/-- Morris, Topology Without Tears, Definition A6.3.5 (TP-678). The net `φ` converges to `a` when for
each neighbourhood `U` of `a` the net is eventually in `U`. -/
def Converges (φ : D → X) (a : X) : Prop :=
  ∀ U ∈ 𝓝 a, ∃ β, ∀ α, β ≤ α → φ α ∈ U

/-- Morris, Topology Without Tears, Definition A6.3.25 (TP-689). A cluster point of a net: each
neighbourhood of `a` contains `φ α` for arbitrarily large `α`. -/
def ClusterPoint (φ : D → X) (a : X) : Prop :=
  ∀ U ∈ 𝓝 a, ∀ β, ∃ α, β ≤ α ∧ φ α ∈ U

/-- Morris, Topology Without Tears, Definition A6.3.16 (TP-684). An ultranet: for every subset `S`
the net is eventually in `S` or eventually in its complement. -/
def IsUltranet (φ : D → X) : Prop :=
  ∀ S : Set X, (∃ β, ∀ α, β ≤ α → φ α ∈ S) ∨ (∃ β, ∀ α, β ≤ α → φ α ∈ Sᶜ)

/-- Morris, Topology Without Tears, Definition A6.3.20 (TP-687). The net `ψ` is a subnet of `φ` when
`ψ = φ ∘ θ` for a non-decreasing cofinal map `θ` between the index sets. -/
def IsSubnet {D₁ : Type v} {D₂ : Type w} [Preorder D₁] [Preorder D₂] (ψ : D₂ → X) (φ : D₁ → X) :
    Prop :=
  ∃ θ : D₂ → D₁, Monotone θ ∧ (∀ α, ∃ β, α ≤ θ β) ∧ ψ = φ ∘ θ

end Defs

section Basic

variable {D : Type v} [Preorder D] [IsDirectedOrder D] [Nonempty D] {φ : D → X} {a : X}

/-- Morris, Topology Without Tears, Definition A6.3.4 (TP-678). Convergence of a net in the book's
sense is `Tendsto φ atTop (𝓝 a)`. -/
@[kb "morris2024" "Definition A6.3.4, p. 650"]
theorem converges_iff_tendsto : Converges φ a ↔ Tendsto φ atTop (𝓝 a) := by
  simp only [Converges, tendsto_def, mem_atTop_sets, mem_preimage]

/-- Morris, Topology Without Tears, Definition A6.3.14 (TP-678). The filter associated with a net is
`map φ atTop`; the net converges to `a` iff this filter is finer than the neighbourhood filter. -/
@[kb "morris2024" "Definition A6.3.14, p. 653"]
theorem converges_iff_map_le : Converges φ a ↔ map φ atTop ≤ 𝓝 a :=
  converges_iff_tendsto

/-- Morris, Topology Without Tears, Proposition A6.3.13 (TP-678). The tail sets of a net generate a
proper filter. -/
@[kb "morris2024" "Proposition A6.3.13, p. 653"]
theorem neBot_map_atTop : (map φ atTop).NeBot := inferInstance

/-- Morris, Topology Without Tears, Definition A6.3.25 (TP-689). A cluster point of a net is a cluster
point of its tail filter. -/
@[kb "morris2024" "Definition A6.3.25, p. 656"]
theorem clusterPoint_iff_mapClusterPt : ClusterPoint φ a ↔ MapClusterPt a atTop φ := by
  rw [mapClusterPt_iff_frequently]
  simp only [ClusterPoint, frequently_atTop]

/-- Morris, Topology Without Tears, Proposition A6.3.26 (TP-689). A limit of a net is a cluster
point. -/
theorem Converges.clusterPoint (h : Converges φ a) : ClusterPoint φ a := by
  refine fun U hU β => ?_
  obtain ⟨γ, hγ⟩ := h U hU
  obtain ⟨δ, hβδ, hγδ⟩ := exists_ge_ge β γ
  exact ⟨δ, hβδ, hγ δ hγδ⟩

/-- Morris, Topology Without Tears, Definition A6.3.16 and Proposition A6.3.17 (TP-684). A net is an
ultranet iff its associated filter is an ultrafilter. -/
@[kb "morris2024" "Proposition A6.3.17, p. 654"]
theorem isUltranet_iff : IsUltranet φ ↔ ∃ U : Ultrafilter X, (U : Filter X) = map φ atTop := by
  have key : ∀ s : Set X, s ∈ map φ atTop ↔ ∃ β, ∀ α, β ≤ α → φ α ∈ s := fun s => by
    simp [mem_map, mem_atTop_sets]
  constructor
  · intro h
    refine ⟨Ultrafilter.ofComplNotMemIff (map φ atTop) (fun s => ?_), rfl⟩
    refine ⟨fun hs => ?_, fun hs hc => ?_⟩
    · rcases h s with h1 | h2
      · exact (key s).2 h1
      · exact absurd ((key _).2 h2) hs
    · exact (Filter.empty_notMem (map φ atTop)) (by simpa using inter_mem hs hc)
  · rintro ⟨U, hU⟩ S
    by_cases hS : S ∈ (U : Filter X)
    · left
      rw [hU] at hS
      exact (key S).1 hS
    · right
      have : Sᶜ ∈ (U : Filter X) := Ultrafilter.compl_mem_iff_notMem.2 hS
      rw [hU] at this
      exact (key _).1 this

end Basic

/-! ### The net associated with a filter -/

section FilterNet

variable (F : Filter X)

/-- Morris, Topology Without Tears, Definition A6.3.14(ii) (TP-683). The directed set of pairs `(x, A)`
with `x ∈ A ∈ F`, ordered by reverse inclusion of the sets `A`. -/
structure FilterIndex (F : Filter X) where
  /-- the point -/
  pt : X
  /-- the set of the filter -/
  set : Set X
  /-- the set belongs to the filter -/
  set_mem : set ∈ F
  /-- the point lies in the set -/
  pt_mem : pt ∈ set

instance : Preorder (FilterIndex F) where
  le a b := b.set ⊆ a.set
  le_refl _ := Subset.rfl
  le_trans _ _ _ hab hbc := hbc.trans hab

/-- Morris, Topology Without Tears, Definition A6.3.14(ii) (TP-683). The net associated with a filter:
`(x, A) ↦ x`. -/
def filterNet : FilterIndex F → X := FilterIndex.pt

variable [F.NeBot]

instance : Nonempty (FilterIndex F) := by
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (univ_mem : (univ : Set X) ∈ F)
  exact ⟨⟨x, univ, univ_mem, hx⟩⟩

instance : IsDirectedOrder (FilterIndex F) :=
  ⟨fun a b => by
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (inter_mem a.set_mem b.set_mem)
    exact ⟨⟨x, a.set ∩ b.set, inter_mem a.set_mem b.set_mem, hx⟩, inter_subset_left,
      inter_subset_right⟩⟩

/-- Morris, Topology Without Tears, Proposition A6.3.15 (TP-683). The filter associated with the net
associated with a filter `F` is `F` itself. -/
@[kb "morris2024" "Proposition A6.3.15, p. 653"]
theorem map_filterNet_atTop : map (filterNet F) atTop = F := by
  ext s
  rw [mem_map, mem_atTop_sets]
  constructor
  · rintro ⟨β, hβ⟩
    refine mem_of_superset β.set_mem (fun x hx => ?_)
    exact hβ ⟨x, β.set, β.set_mem, hx⟩ Subset.rfl
  · intro hs
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hs
    exact ⟨⟨x, s, hs, hx⟩, fun b hb => hb b.pt_mem⟩

/-- Morris, Topology Without Tears, Proposition A6.3.15 (TP-683). The net associated with `F`
converges to `a` iff `F` converges to `a`. -/
@[kb "morris2024" "Proposition A6.3.15, p. 653"]
theorem converges_filterNet_iff {a : X} : Converges (filterNet F) a ↔ F ≤ 𝓝 a := by
  rw [converges_iff_map_le, map_filterNet_atTop]

/-- Morris, Topology Without Tears, Proposition A6.3.17 (TP-684). The net associated with an
ultrafilter is an ultranet. -/
@[kb "morris2024" "Proposition A6.3.17, p. 654"]
theorem isUltranet_filterNet (U : Ultrafilter X) : IsUltranet (filterNet (U : Filter X)) :=
  isUltranet_iff.2 ⟨U, (map_filterNet_atTop _).symm⟩

end FilterNet

/-! ### Hausdorff spaces, closure, continuity -/

/-- In a Hausdorff space a net has at most one limit (any index universe). -/
theorem Converges.unique [T2Space X] {D : Type v} [Preorder D] [IsDirectedOrder D] [Nonempty D]
    {φ : D → X} {a b : X} (ha : Converges φ a) (hb : Converges φ b) : a = b := by
  rw [converges_iff_tendsto] at ha hb
  exact tendsto_nhds_unique ha hb

/-- Morris, Topology Without Tears, Proposition A6.3.6 (TP-680). A space is Hausdorff iff no net
converges to two distinct points. -/
@[kb "morris2024" "Proposition A6.3.6, p. 651"]
theorem t2Space_iff_net : T2Space X ↔
    ∀ (D : Type u) [Preorder D] [IsDirectedOrder D] [Nonempty D] (φ : D → X) (a b : X),
      Converges φ a → Converges φ b → a = b := by
  constructor
  · intro _ D _ _ _ φ a b ha hb
    exact ha.unique hb
  · intro h
    rw [t2_iff_nhds]
    intro x y hne
    exact h (FilterIndex (𝓝 x ⊓ 𝓝 y)) (filterNet _) x y
      ((converges_filterNet_iff _).2 inf_le_left) ((converges_filterNet_iff _).2 inf_le_right)

/-- Morris, Topology Without Tears, Proposition A6.3.10 (TP-681). A point lies in the closure of `S`
(the book's "limit point", meaning every neighbourhood meets `S`) iff some net in `S` converges to it. -/
@[kb "morris2024" "Proposition A6.3.10, p. 652"]
theorem mem_closure_iff_net {S : Set X} {a : X} : a ∈ closure S ↔
    ∃ (D : Type u) (_ : Preorder D) (_ : IsDirectedOrder D) (_ : Nonempty D) (φ : D → X),
      (∀ d, φ d ∈ S) ∧ Converges φ a := by
  constructor
  · intro h
    rw [mem_closure_iff_comap_neBot] at h
    set G : Filter S := comap ((↑) : S → X) (𝓝 a) with hG
    refine ⟨FilterIndex G, inferInstance, inferInstance, inferInstance,
      fun d => ((filterNet G d : S) : X), fun d => (filterNet G d).2, ?_⟩
    rw [converges_iff_tendsto]
    exact tendsto_comap.comp (by
      rw [Tendsto, map_filterNet_atTop])
  · rintro ⟨D, _, _, _, φ, hS, hc⟩
    rw [converges_iff_tendsto] at hc
    exact mem_closure_of_tendsto hc (Eventually.of_forall hS)

/-- Morris, Topology Without Tears, Corollary A6.3.11 (TP-681). A set is closed iff no net in it
converges to a point outside it. -/
@[kb "morris2024" "Corollary A6.3.11, p. 652"]
theorem isClosed_iff_net {S : Set X} : IsClosed S ↔
    ¬ ∃ (D : Type u) (_ : Preorder D) (_ : IsDirectedOrder D) (_ : Nonempty D) (φ : D → X),
      (∀ d, φ d ∈ S) ∧ ∃ a ∈ Sᶜ, Converges φ a := by
  constructor
  · rintro hS ⟨D, _, _, _, φ, hφ, a, ha, hc⟩
    rw [converges_iff_tendsto] at hc
    exact ha (hS.mem_of_tendsto hc (Eventually.of_forall hφ))
  · intro h
    refine isClosed_of_closure_subset (fun a ha => ?_)
    obtain ⟨D, i1, i2, i3, φ, hφ, hc⟩ := mem_closure_iff_net.1 ha
    by_contra hna
    exact h ⟨D, i1, i2, i3, φ, hφ, a, hna, hc⟩

/-- Morris, Topology Without Tears, Proposition A6.3.19 (TP-686). A map is continuous iff it sends
every net converging to `a` to a net converging to `f a`. -/
@[kb "morris2024" "Proposition A6.3.19, p. 654"]
theorem continuous_iff_net {Y : Type w} [TopologicalSpace Y] {f : X → Y} : Continuous f ↔
    ∀ (D : Type u) [Preorder D] [IsDirectedOrder D] [Nonempty D] (φ : D → X) (a : X),
      Converges φ a → Converges (f ∘ φ) (f a) := by
  constructor
  · intro hf D _ _ _ φ a h
    rw [converges_iff_tendsto] at h ⊢
    exact (hf.tendsto a).comp h
  · intro h
    rw [continuous_iff_continuousAt]
    intro a
    have h1 := h (FilterIndex (𝓝 a)) (filterNet _) a ((converges_filterNet_iff _).2 le_rfl)
    rw [converges_iff_tendsto] at h1
    have h2 : Tendsto f (map (filterNet (𝓝 a)) atTop) (𝓝 (f a)) := tendsto_map'_iff.2 h1
    rwa [map_filterNet_atTop] at h2

/-! ### Subnets -/

section Subnets

variable {D₁ : Type v} {D₂ : Type w} {D₃ : Type*} [Preorder D₁] [Preorder D₂] [Preorder D₃]

/-- Morris, Topology Without Tears, Definition A6.3.20 (TP-687). Every net is a subnet of itself. -/
@[kb "morris2024" "Definition A6.3.20, p. 655"]
theorem IsSubnet.refl (φ : D₁ → X) : IsSubnet φ φ :=
  ⟨id, monotone_id, fun α => ⟨α, le_rfl⟩, rfl⟩

/-- Morris, Topology Without Tears, Definition A6.3.20 (TP-687). A subnet of a subnet is a subnet. -/
@[kb "morris2024" "Definition A6.3.20, p. 655"]
theorem IsSubnet.trans {χ : D₃ → X} {ψ : D₂ → X} {φ : D₁ → X} (h₁ : IsSubnet χ ψ)
    (h₂ : IsSubnet ψ φ) : IsSubnet χ φ := by
  obtain ⟨θ, hθm, hθc, rfl⟩ := h₁
  obtain ⟨η, hηm, hηc, rfl⟩ := h₂
  refine ⟨η ∘ θ, hηm.comp hθm, fun α => ?_, rfl⟩
  obtain ⟨β₂, hβ₂⟩ := hηc α
  obtain ⟨β₃, hβ₃⟩ := hθc β₂
  exact ⟨β₃, hβ₂.trans (hηm hβ₃)⟩

/-- Morris, Topology Without Tears, Example A6.3.22 (TP-687). A subsequence of a sequence is a subnet. -/
@[kb "morris2024" "Example A6.3.22, p. 655"]
theorem isSubnet_comp_strictMono (φ : ℕ → X) {g : ℕ → ℕ} (hg : StrictMono g) :
    IsSubnet (φ ∘ g) φ :=
  ⟨g, hg.monotone, fun α => ⟨α, hg.id_le α⟩, rfl⟩

/-- Morris, Topology Without Tears, Definition A6.3.20 (TP-687). The index map of a subnet tends to
infinity, so that a subnet is eventually as far along the original net as one wishes. -/
@[kb "morris2024" "Definition A6.3.20, p. 655"]
theorem IsSubnet.exists_tendsto_atTop [IsDirectedOrder D₂] [Nonempty D₂] {ψ : D₂ → X}
    {φ : D₁ → X} (h : IsSubnet ψ φ) :
    ∃ θ : D₂ → D₁, Tendsto θ atTop atTop ∧ ψ = φ ∘ θ := by
  obtain ⟨θ, hm, hc, e⟩ := h
  refine ⟨θ, ?_, e⟩
  rw [tendsto_atTop]
  intro b
  obtain ⟨β, hβ⟩ := hc b
  exact eventually_atTop.2 ⟨β, fun x hx => hβ.trans (hm hx)⟩

/-- Morris, Topology Without Tears, Proposition A6.3.27 (TP-689). A cluster point of a subnet of a net
is a cluster point of the net. -/
@[kb "morris2024" "Proposition A6.3.27, p. 657"]
theorem IsSubnet.clusterPoint {ψ : D₂ → X} {φ : D₁ → X} (h : IsSubnet ψ φ) {a : X}
    (ha : ClusterPoint ψ a) : ClusterPoint φ a := by
  obtain ⟨θ, hm, hc, rfl⟩ := h
  refine fun U hU β => ?_
  obtain ⟨γ, hγ⟩ := hc β
  obtain ⟨δ, hδ, hv⟩ := ha U hU γ
  exact ⟨θ δ, hγ.trans (hm hδ), hv⟩

end Subnets

/-- The directed set of the proof of Proposition A6.3.28: pairs `(α, A)` of an index `α` and a set `A` of
the filter `G` with `φ α ∈ A`, ordered by `α₁ ≤ α₂` and `A₁ ⊇ A₂`. With `G = 𝓝 a` this is the
book's directed set; with `G` an ultrafilter it is the one used for ultranet subnets. -/
structure SubnetIndex {D : Type v} (φ : D → X) (G : Filter X) where
  /-- the index of the original net -/
  idx : D
  /-- the set of the filter -/
  set : Set X
  /-- membership in the filter -/
  set_mem : set ∈ G
  /-- the value lies in the set -/
  val_mem : φ idx ∈ set

section SubnetIndex

variable {D : Type v} [Preorder D] (φ : D → X) (G : Filter X)

instance : Preorder (SubnetIndex φ G) where
  le i j := i.idx ≤ j.idx ∧ j.set ⊆ i.set
  le_refl _ := ⟨le_rfl, Subset.rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- The hypothesis making `SubnetIndex φ G` directed: `φ` is frequently in every set of `G`. -/
def Frequent : Prop := ∀ S ∈ G, ∀ γ, ∃ α, γ ≤ α ∧ φ α ∈ S

variable {φ G}

theorem SubnetIndex.isDirected [IsDirectedOrder D] (h : Frequent φ G) :
    IsDirectedOrder (SubnetIndex φ G) :=
  ⟨fun i j => by
    obtain ⟨γ, hiγ, hjγ⟩ := exists_ge_ge i.idx j.idx
    obtain ⟨α, hα, hv⟩ := h (i.set ∩ j.set) (inter_mem i.set_mem j.set_mem) γ
    exact ⟨⟨α, i.set ∩ j.set, inter_mem i.set_mem j.set_mem, hv⟩, ⟨hiγ.trans hα, inter_subset_left⟩,
      ⟨hjγ.trans hα, inter_subset_right⟩⟩⟩

theorem SubnetIndex.nonempty [Nonempty D] : Nonempty (SubnetIndex φ G) := by
  obtain ⟨d⟩ := ‹Nonempty D›
  exact ⟨⟨d, univ, univ_mem, trivial⟩⟩

theorem SubnetIndex.isSubnet : IsSubnet (fun i : SubnetIndex φ G => φ i.idx) φ :=
  ⟨SubnetIndex.idx, fun _ _ h => h.1,
    fun α => ⟨⟨α, univ, univ_mem, trivial⟩, le_rfl⟩, rfl⟩

theorem SubnetIndex.tendsto [IsDirectedOrder D] [Nonempty D] (h : Frequent φ G) :
    Tendsto (fun i : SubnetIndex φ G => φ i.idx) atTop G := by
  have := SubnetIndex.isDirected h
  have := SubnetIndex.nonempty (φ := φ) (G := G)
  rw [tendsto_def]
  intro S hS
  rw [mem_atTop_sets]
  obtain ⟨d⟩ := ‹Nonempty D›
  obtain ⟨α, -, hv⟩ := h S hS d
  exact ⟨⟨α, S, hS, hv⟩, fun b hb => hb.2 b.val_mem⟩

end SubnetIndex

section SubnetProps

variable {D : Type v} [Preorder D] [IsDirectedOrder D] [Nonempty D] {φ : D → X}

/-- Morris, Topology Without Tears, Proposition A6.3.28 (TP-690). A point is a cluster point of a net iff
some subnet of the net converges to it. -/
@[kb "morris2024" "Proposition A6.3.28, p. 657"]
theorem clusterPoint_iff_exists_subnet {a : X} : ClusterPoint φ a ↔
    ∃ (D₂ : Type (max u v)) (_ : Preorder D₂) (_ : IsDirectedOrder D₂) (_ : Nonempty D₂)
      (ψ : D₂ → X), IsSubnet ψ φ ∧ Converges ψ a := by
  constructor
  · intro h
    have hF : Frequent φ (𝓝 a) := h
    have := SubnetIndex.isDirected hF
    have := SubnetIndex.nonempty (φ := φ) (G := 𝓝 a)
    exact ⟨SubnetIndex φ (𝓝 a), inferInstance, inferInstance, inferInstance, _,
      SubnetIndex.isSubnet, converges_iff_tendsto.2 (SubnetIndex.tendsto hF)⟩
  · rintro ⟨D₂, _, _, _, ψ, hsub, hconv⟩
    exact hsub.clusterPoint hconv.clusterPoint

/-- Morris, Topology Without Tears, Proposition A6.3.30 (TP-692). Every net has a subnet which is an
ultranet. -/
@[kb "morris2024" "Proposition A6.3.30, p. 658"]
theorem exists_ultranet_subnet (φ : D → X) :
    ∃ (D₂ : Type (max u v)) (_ : Preorder D₂) (_ : IsDirectedOrder D₂) (_ : Nonempty D₂)
      (ψ : D₂ → X), IsSubnet ψ φ ∧ IsUltranet ψ := by
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (map φ atTop)
  have hF : Frequent φ (U : Filter X) := by
    intro S hS γ
    have h1 : φ '' Ici γ ∈ map φ atTop :=
      mem_map.2 (mem_of_superset (Ici_mem_atTop γ) (subset_preimage_image _ _))
    obtain ⟨x, hxS, ⟨α, hα, rfl⟩⟩ := Filter.nonempty_of_mem (inter_mem hS (hU h1))
    exact ⟨α, hα, hxS⟩
  have := SubnetIndex.isDirected hF
  have := SubnetIndex.nonempty (φ := φ) (G := (U : Filter X))
  refine ⟨SubnetIndex φ (U : Filter X), inferInstance, inferInstance, inferInstance, _,
    SubnetIndex.isSubnet, isUltranet_iff.2 ⟨U, ?_⟩⟩
  exact (Ultrafilter.unique U (SubnetIndex.tendsto hF)).symm

end SubnetProps

/-! ### Compactness -/

/-- Morris, Topology Without Tears, Proposition A6.3.29 (TP-691). A space is compact iff every ultranet
in it converges. -/
@[kb "morris2024" "Proposition A6.3.29, p. 658"]
theorem compactSpace_iff_ultranet : CompactSpace X ↔
    ∀ (D : Type u) [Preorder D] [IsDirectedOrder D] [Nonempty D] (φ : D → X),
      IsUltranet φ → ∃ a, Converges φ a := by
  constructor
  · intro hX D _ _ _ φ hu
    obtain ⟨U, hU⟩ := isUltranet_iff.1 hu
    obtain ⟨a, -, ha⟩ := isCompact_iff_ultrafilter_le_nhds.1 (isCompact_univ (X := X)) U (by simp)
    exact ⟨a, converges_iff_map_le.2 (by rw [← hU]; exact ha)⟩
  · intro h
    refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun U _ => ?_⟩
    obtain ⟨a, ha⟩ := h (FilterIndex (U : Filter X)) (filterNet _) (isUltranet_filterNet U)
    exact ⟨a, mem_univ _, (converges_filterNet_iff _).1 ha⟩

/-- Morris, Topology Without Tears, Proposition A6.3.31 (TP-693). A space is compact iff every net has a
convergent subnet iff every net has a cluster point. -/
@[kb "morris2024" "Proposition A6.3.31, p. 658"]
theorem compactSpace_tfae : List.TFAE
    [CompactSpace X,
     ∀ (D : Type u) [Preorder D] [IsDirectedOrder D] [Nonempty D] (φ : D → X),
       ∃ (D₂ : Type u) (_ : Preorder D₂) (_ : IsDirectedOrder D₂) (_ : Nonempty D₂)
         (ψ : D₂ → X) (a : X), IsSubnet ψ φ ∧ Converges ψ a,
     ∀ (D : Type u) [Preorder D] [IsDirectedOrder D] [Nonempty D] (φ : D → X),
       ∃ a, ClusterPoint φ a] := by
  tfae_have 1 → 3 := by
    intro hX D _ _ _ φ
    obtain ⟨a, ha⟩ := exists_clusterPt_of_compactSpace (map φ atTop)
    exact ⟨a, clusterPoint_iff_mapClusterPt.2 ha⟩
  tfae_have 3 → 2 := by
    intro h D _ _ _ φ
    obtain ⟨a, ha⟩ := h D φ
    obtain ⟨D₂, i1, i2, i3, ψ, hs, hc⟩ := clusterPoint_iff_exists_subnet.1 ha
    exact ⟨D₂, i1, i2, i3, ψ, a, hs, hc⟩
  tfae_have 2 → 3 := by
    intro h D _ _ _ φ
    obtain ⟨D₂, _, _, _, ψ, a, hs, hc⟩ := h D φ
    exact ⟨a, hs.clusterPoint hc.clusterPoint⟩
  tfae_have 3 → 1 := by
    intro h
    refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun U _ => ?_⟩
    obtain ⟨a, ha⟩ := h (FilterIndex (U : Filter X)) (filterNet _)
    rw [clusterPoint_iff_mapClusterPt, MapClusterPt, map_filterNet_atTop] at ha
    exact ⟨a, mem_univ _, Ultrafilter.clusterPt_iff.1 ha⟩
  tfae_finish

end Net

end UndergradKB.Topology
