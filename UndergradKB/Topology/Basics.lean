import Mathlib.Topology.Bases
import Mathlib.Topology.Constructions
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Irrational
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.PNat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import UndergradKB.Common.Attr

/-!
# Topology Without Tears: basic open sets, bases, connectedness (batch B1)

Morris, *Topology Without Tears* (2024), reference key `morris2024`.
-/

namespace UndergradKB.Topology

open Set TopologicalSpace

/-! ### Chapter 1: an infinite intersection of open sets -/

/-- Morris, Topology Without Tears, Example 1.2.3 (TP-007). In the finite-closed topology on the
positive integers, the sets `{1} ∪ {m | n < m}` are open but their intersection `{1}` is not. -/
@[kb "morris2024" "Example 1.2.3, p. 34"]
theorem iInter_open_not_open :
    (∀ n : ℕ+, IsOpen (CofiniteTopology.of.symm ⁻¹' {m : ℕ+ | m = 1 ∨ n < m})) ∧
    (⋂ n : ℕ+, (CofiniteTopology.of.symm ⁻¹' {m : ℕ+ | m = 1 ∨ n < m} :
      Set (CofiniteTopology ℕ+))) = CofiniteTopology.of.symm ⁻¹' {1} ∧
    ¬ IsOpen (CofiniteTopology.of.symm ⁻¹' ({1} : Set ℕ+)) := by
  have key : ∀ S : Set ℕ+, IsOpen (CofiniteTopology.of.symm ⁻¹' S) ↔ (S.Nonempty → Sᶜ.Finite) := by
    intro S
    rw [CofiniteTopology.isOpen_iff]
    have hne : (CofiniteTopology.of.symm ⁻¹' S).Nonempty ↔ S.Nonempty := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨_, hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨CofiniteTopology.of x, by simpa using hx⟩
    have hfin : (CofiniteTopology.of.symm ⁻¹' S)ᶜ.Finite ↔ Sᶜ.Finite := by
      rw [← Set.preimage_compl]
      constructor
      · intro h
        have := h.image CofiniteTopology.of.symm
        rwa [Equiv.image_preimage] at this
      · intro h
        exact h.preimage (CofiniteTopology.of.symm.injective.injOn)
    rw [hne, hfin]
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [key]
    intro _
    refine ((Set.finite_Iic (n : ℕ)).preimage PNat.coe_injective.injOn).subset ?_
    intro m hm
    simp only [mem_compl_iff, mem_ofPred_eq, not_or, not_lt] at hm
    exact PNat.coe_le_coe _ _ |>.2 hm.2
  · ext m
    simp only [mem_iInter, mem_preimage, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      have := (h (CofiniteTopology.of.symm m)).resolve_left hne
      exact lt_irrefl _ this
    · intro h n
      exact Or.inl h
  · rw [key]
    intro h
    exact (Set.finite_singleton (1 : ℕ+)).infinite_compl (h ⟨1, rfl⟩)

/-! ### Chapter 2.1: the euclidean topology on the reals -/

/-- Morris, Topology Without Tears, Definition 2.1.1 and Remark 2.1.2 (i) (TP-019). A subset of the
reals is open iff around each of its points there is an open interval inside it. -/
@[kb "morris2024" "Definition 2.1.1, p. 51"]
theorem isOpen_real_iff_exists_Ioo (s : Set ℝ) :
    IsOpen s ↔ ∀ x ∈ s, ∃ a b : ℝ, x ∈ Ioo a b ∧ Ioo a b ⊆ s :=
  isOpen_iff_mem_nhds.trans (forall₂_congr fun _ _ => mem_nhds_iff_exists_Ioo_subset)

/-- Morris, Topology Without Tears, Remark 2.1.2 (v) (TP-021). A closed interval `[c, d]` with
`c < d` is not open in the reals. -/
@[kb "morris2024" "Remark 2.1.2, p. 53"]
theorem not_isOpen_Icc {c d : ℝ} (h : c < d) : ¬ IsOpen (Icc c d) := by
  intro ho
  have hc : IsClopen (Icc c d) := ⟨isClosed_Icc, ho⟩
  rcases isClopen_iff.1 hc with h0 | h1
  · exact (nonempty_Icc.2 h.le).ne_empty h0
  · have : d + 1 ∈ Icc c d := by rw [h1]; trivial
    linarith [this.2]

/-- Morris, Topology Without Tears, Remark 2.1.2 (x) (TP-024). The rationals are not open in the
reals. -/
@[kb "morris2024" "Remark 2.1.2, p. 54"]
theorem not_isOpen_range_ratCast : ¬ IsOpen (Set.range ((↑) : ℚ → ℝ)) := by
  intro ho
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 ho 0 ⟨0, by simp⟩
  obtain ⟨x, hx, hxb⟩ := dense_irrational.exists_mem_open Metric.isOpen_ball
    (Metric.nonempty_ball.2 hε)
  exact hx (hsub hxb)

/-- Morris, Topology Without Tears, Remark 2.1.2 (x) (TP-024). The rationals are not closed in the
reals. -/
@[kb "morris2024" "Remark 2.1.2, p. 54"]
theorem not_isClosed_range_ratCast : ¬ IsClosed (Set.range ((↑) : ℚ → ℝ)) := by
  intro hc
  have hd : closure (Set.range ((↑) : ℚ → ℝ)) = univ := Rat.denseRange_cast.closure_range
  rw [hc.closure_eq] at hd
  exact irrational_sqrt_two (by rw [hd]; trivial)

/-! ### Fσ and Gδ sets -/

/-- Bridging definition for Morris, Topology Without Tears, section 2.1 (p. 55): an `Fσ` set is a
countable union of closed sets (Mathlib has `IsGδ` but not its dual). -/
def IsFσ {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

/-- Morris, Topology Without Tears, section 2.1 (TP-026). The complement of an `Fσ` set is a `Gδ`
set. -/
@[kb "morris2024" "Definition (Fσ and Gδ sets), section 2.1, p. 55"]
theorem isGδ_compl_iff_isFσ {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsGδ sᶜ ↔ IsFσ s := by
  constructor
  · rintro ⟨T, ho, hc, hs⟩
    refine ⟨compl '' T, ?_, hc.image _, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (ho t ht).isClosed_compl
    · have := congrArg compl hs
      rw [compl_compl, compl_sInter] at this
      exact this
  · rintro ⟨T, hcl, hc, rfl⟩
    refine ⟨compl '' T, ?_, hc.image _, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (hcl t ht).isOpen_compl
    · rw [compl_sUnion]

/-- Morris, Topology Without Tears, section 2.1 (TP-026). The complement of a `Gδ` set is an `Fσ`
set. -/
@[kb "morris2024" "Definition (Fσ and Gδ sets), section 2.1, p. 55"]
theorem isFσ_compl_iff_isGδ {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsFσ sᶜ ↔ IsGδ s := by
  rw [← isGδ_compl_iff_isFσ, compl_compl]

/-! ### Basis for a topology -/

/-- Morris, Topology Without Tears, Proposition 2.2.8 (TP-030). A family `B` of subsets of `X` is a
basis for some topology on `X` iff it covers `X` and each intersection of two members is a union of
members. -/
@[kb "morris2024" "Proposition 2.2.8, p. 59"]
theorem exists_topology_isTopologicalBasis_iff {X : Type*} (B : Set (Set X)) :
    (∃ t : TopologicalSpace X, IsTopologicalBasis (t := t) B) ↔
      (⋃₀ B = univ ∧ ∀ B₁ ∈ B, ∀ B₂ ∈ B, ∃ C ⊆ B, B₁ ∩ B₂ = ⋃₀ C) := by
  constructor
  · rintro ⟨t, hb⟩
    refine ⟨hb.sUnion_eq, fun B₁ h₁ B₂ h₂ => ?_⟩
    exact hb.open_eq_sUnion ((hb.isOpen h₁).inter (hb.isOpen h₂))
  · rintro ⟨hcov, hint⟩
    refine ⟨generateFrom B, @IsTopologicalBasis.mk X (generateFrom B) B ?_ hcov rfl⟩
    intro B₁ h₁ B₂ h₂ x hx
    obtain ⟨C, hC, hEq⟩ := hint B₁ h₁ B₂ h₂
    have : x ∈ ⋃₀ C := hEq ▸ hx
    obtain ⟨c, hcC, hxc⟩ := this
    exact ⟨c, hC hcC, hxc, hEq ▸ subset_sUnion_of_mem hcC⟩

/-- A rectangle `(a, b) × (c, d)` in the plane `ℝ × ℝ` is a product of two open intervals. -/
@[kb "morris2024" "Example 2.2.9, p. 60"]
theorem isTopologicalBasis_open_rectangles :
    IsTopologicalBasis {s : Set (ℝ × ℝ) | ∃ a b c d : ℝ, s = Ioo a b ×ˢ Ioo c d} := by
  have hI : IsTopologicalBasis {s : Set ℝ | ∃ a b : ℝ, s = Ioo a b} :=
    isTopologicalBasis_of_isOpen_of_nhds
      (by rintro _ ⟨a, b, rfl⟩; exact isOpen_Ioo)
      (fun x u hx hu => by
        obtain ⟨l, m, hxm, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hu.mem_nhds hx)
        exact ⟨_, ⟨l, m, rfl⟩, hxm, hsub⟩)
  convert hI.prod hI using 1
  ext s
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨_, ⟨a, b, rfl⟩, _, ⟨c, d, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, b, rfl⟩, _, ⟨c, d, rfl⟩, rfl⟩
    exact ⟨a, b, c, d, rfl⟩

/-- Morris, Topology Without Tears, Example 2.2.9 and Remark 2.2.10 (TP-031). Open rectangles
form a basis of the topology of the plane `ℝ × ℝ`, and open boxes `∏ (aᵢ, bᵢ)` form a basis of the
topology of `ℝⁿ` (here for any finite index type `ι`, with the product topology, which is the
topology of the sup metric, equal to the euclidean one). -/
@[kb "morris2024" "Remark 2.2.10, p. 60"]
theorem isTopologicalBasis_open_boxes (ι : Type*) [Fintype ι] :
    IsTopologicalBasis {s : Set (ι → ℝ) | ∃ a b : ι → ℝ, s = Set.pi univ fun i => Ioo (a i) (b i)} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨a, b, rfl⟩
    exact isOpen_set_pi finite_univ fun i _ => isOpen_Ioo
  · intro x u hx hu
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hu x hx
    refine ⟨_, ⟨fun i => x i - ε, fun i => x i + ε, rfl⟩, ?_, ?_⟩
    · intro i _
      constructor <;> linarith
    · refine Subset.trans (fun y hy => ?_) hsub
      rw [ball_pi x hε]
      intro i _
      have := hy i (mem_univ i)
      show y i ∈ Metric.ball (x i) ε
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- Morris, Topology Without Tears, Proposition 2.3.4 (TP-034). Two bases `B`, `B'` for topologies
`t`, `t'` on `X` give the same topology iff each member of one contains, around each of its
points, a member of the other. -/
@[kb "morris2024" "Proposition 2.3.4, p. 65"]
theorem topology_eq_iff_refines {X : Type*} {t t' : TopologicalSpace X} {B B' : Set (Set X)}
    (hB : IsTopologicalBasis (t := t) B) (hB' : IsTopologicalBasis (t := t') B') :
    t = t' ↔ (∀ b ∈ B, ∀ x ∈ b, ∃ b' ∈ B', x ∈ b' ∧ b' ⊆ b) ∧
      (∀ b' ∈ B', ∀ x ∈ b', ∃ b ∈ B, x ∈ b ∧ b ⊆ b') := by
  constructor
  · rintro rfl
    exact ⟨fun b hb x hx => hB'.exists_subset_of_mem_open hx (hB.isOpen hb),
      fun b hb x hx => hB.exists_subset_of_mem_open hx (hB'.isOpen hb)⟩
  · rintro ⟨h1, h2⟩
    have key : ∀ {t t' : TopologicalSpace X} {B B' : Set (Set X)},
        IsTopologicalBasis (t := t) B → IsTopologicalBasis (t := t') B' →
        (∀ b ∈ B, ∀ x ∈ b, ∃ b' ∈ B', x ∈ b' ∧ b' ⊆ b) → t' ≤ t := by
      intro t t' B B' hB hB' h1 U hU
      have hU' := (IsTopologicalBasis.isOpen_iff (t := t) hB).1 hU
      refine (IsTopologicalBasis.isOpen_iff (t := t') hB').2 fun x hx => ?_
      obtain ⟨b, hb, hxb, hbU⟩ := hU' x hx
      obtain ⟨b', hb', hxb', hb'b⟩ := h1 b hb x hxb
      exact ⟨b', hb', hxb', hb'b.trans hbU⟩
    exact le_antisymm (key hB' hB h2) (key hB hB' h1)

/-- Bridging definition for Morris, Topology Without Tears, section 2.3 (p. 69): `S` is a subbasis
for the topology of `X` when the finite intersections of members of `S` form a basis. -/
def IsSubbasis {X : Type*} [TopologicalSpace X] (S : Set (Set X)) : Prop :=
  IsTopologicalBasis ((fun f : Set (Set X) => ⋂₀ f) '' {f | f.Finite ∧ f ⊆ S})

/-- Morris, Topology Without Tears, section 2.3 (TP-036). `S` is a subbasis for the topology iff the
topology is the one generated by `S`. -/
@[kb "morris2024" "Definition (subbasis), section 2.3, p. 69"]
theorem isSubbasis_iff {X : Type*} [t : TopologicalSpace X] (S : Set (Set X)) :
    IsSubbasis S ↔ t = generateFrom S := by
  constructor
  · intro h
    refine le_antisymm ?_ ?_
    · refine le_generateFrom_iff_subset_isOpen.2 ?_
      intro s hs
      exact h.isOpen ⟨{s}, ⟨finite_singleton s, singleton_subset_iff.2 hs⟩, sInter_singleton s⟩
    · refine le_trans ?_ h.eq_generateFrom.ge
      refine (le_generateFrom_iff_subset_isOpen (t := generateFrom S)).2 ?_
      rintro _ ⟨f, ⟨hf, hfS⟩, rfl⟩
      exact @Set.Finite.isOpen_sInter _ (generateFrom S) _ hf fun s hs => isOpen_generateFrom_of_mem (hfS hs)
  · intro h
    exact isTopologicalBasis_of_subbasis h

/-! ### Connectedness -/

/-- Morris, Topology Without Tears, Example 3.3.7 (TP-057). An indiscrete space is connected
(here also preconnected; connected when nonempty). -/
@[kb "morris2024" "Example 3.3.7, p. 86"]
theorem preconnectedSpace_of_indiscrete {X : Type*} [TopologicalSpace X] [IndiscreteTopology X] :
    PreconnectedSpace X := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  rcases (IndiscreteTopology.isOpen_iff s).1 hs.isOpen with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Morris, Topology Without Tears, Example 3.3.7 (TP-057). A nonempty indiscrete space is
connected. -/
@[kb "morris2024" "Example 3.3.7, p. 86"]
theorem connectedSpace_of_indiscrete {X : Type*} [TopologicalSpace X] [IndiscreteTopology X]
    [Nonempty X] : ConnectedSpace X :=
  { toPreconnectedSpace := preconnectedSpace_of_indiscrete, toNonempty := inferInstance }

/-- Morris, Topology Without Tears, Remark 3.3.9 (TP-058). A space is disconnected iff it is the
union of two disjoint nonempty open sets. -/
@[kb "morris2024" "Remark 3.3.9, p. 87"]
theorem not_preconnectedSpace_iff {X : Type*} [TopologicalSpace X] :
    ¬ PreconnectedSpace X ↔
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧ U ∪ V = univ := by
  rw [preconnectedSpace_iff_clopen]
  constructor
  · intro h
    push Not at h
    obtain ⟨s, hs, hne, hu⟩ := h
    refine ⟨s, sᶜ, hs.isOpen, hs.compl.isOpen, hne, ?_,
      disjoint_compl_right, union_compl_self s⟩
    exact nonempty_compl.2 hu
  · rintro ⟨U, V, hU, hV, hUn, hVn, hd, hUV⟩ h
    have hc : IsCompl U V := ⟨hd, codisjoint_iff.2 hUV⟩
    have hcl : IsClosed U := by
      rw [← isOpen_compl_iff, hc.compl_eq]
      exact hV
    rcases h U ⟨hcl, hU⟩ with h0 | h1
    · exact hUn.ne_empty h0
    · rw [h1] at hd
      exact hVn.ne_empty (by simpa using hd)

end UndergradKB.Topology
