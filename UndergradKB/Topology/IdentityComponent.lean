import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.TotallyDisconnected
import UndergradKB.Common.Attr

/-!
# The identity component of a topological group

Morris, *Topology Without Tears*, Appendix 5: the identity component `G₀` is a closed normal
subgroup and `G/G₀` is totally disconnected.  Mathlib provides `Subgroup.connectedComponentOfOne`.
-/

open Set Topology

namespace UndergradKB.Topology

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Morris, Topology Without Tears, Definition A5.0.24 (TP-497).  The identity component of a
topological group is (as a set) the connected component of `1`, a subgroup by Mathlib's
`Subgroup.connectedComponentOfOne`. -/
@[kb "morris2024" "Definition A5.0.24, p. 509"]
theorem coe_connectedComponentOfOne :
    (Subgroup.connectedComponentOfOne G : Set G) = connectedComponent (1 : G) := rfl

/-- Morris, Topology Without Tears, Proposition A5.2.15 (TP-497).  The identity component is a
closed subgroup. -/
@[kb "morris2024" "Proposition A5.2.15, p. 524"]
theorem isClosed_connectedComponentOfOne : IsClosed (Subgroup.connectedComponentOfOne G : Set G) :=
  isClosed_connectedComponent

/-- Morris, Topology Without Tears, Proposition A5.2.15 (TP-497).  The identity component is a
normal subgroup. -/
@[kb "morris2024" "Proposition A5.2.15, p. 524"]
theorem normal_connectedComponentOfOne : (Subgroup.connectedComponentOfOne G).Normal where
  conj_mem g hg x := by
    have hc : Continuous fun y : G => x * y * x⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    have h : x * g * x⁻¹ ∈ connectedComponent (x * 1 * x⁻¹) :=
      hc.image_connectedComponent_subset (1 : G) ⟨g, hg, rfl⟩
    rwa [mul_one, mul_inv_cancel] at h

/-- Morris, Topology Without Tears, Proposition A5.2.20 (TP-497).  The cosets of the identity
component are the connected components of `G`: each fibre of the quotient map is connected. -/
theorem isConnected_fiber_quotient_connectedComponentOfOne (y : G ⧸ Subgroup.connectedComponentOfOne G) :
    IsConnected ((QuotientGroup.mk : G → G ⧸ Subgroup.connectedComponentOfOne G) ⁻¹' {y}) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have : ((QuotientGroup.mk : G → G ⧸ Subgroup.connectedComponentOfOne G) ⁻¹'
      {(g : G ⧸ Subgroup.connectedComponentOfOne G)}) = connectedComponent g := by
    ext x
    rw [mem_preimage, mem_singleton_iff, QuotientGroup.eq]
    have h1 : x ∈ connectedComponent g ↔ g⁻¹ * x ∈ connectedComponent (1 : G) := by
      rw [← mul_one g, ← smul_connectedComponent, mem_smul_set_iff_inv_smul_mem]
      simp
    rw [h1, ← Subgroup.inv_mem_iff (Subgroup.connectedComponentOfOne G), mul_inv_rev, inv_inv]
    rfl
  rw [this]
  exact isConnected_connectedComponent

/-- Morris, Topology Without Tears, Proposition A5.0.25 and Proposition A5.2.20 (TP-497).  The
quotient `G / G₀` of a topological group by its identity component is totally disconnected. -/
@[kb "morris2024" "Proposition A5.2.20, p. 525"]
theorem totallyDisconnectedSpace_quotient_connectedComponentOfOne
    [(Subgroup.connectedComponentOfOne G).Normal] :
    TotallyDisconnectedSpace (G ⧸ Subgroup.connectedComponentOfOne G) := by
  have hq : IsQuotientMap (QuotientGroup.mk : G → G ⧸ Subgroup.connectedComponentOfOne G) :=
    QuotientGroup.isQuotientMap_mk _
  have hcomp := hq.isCoinducing.preimage_connectedComponent
    (isConnected_fiber_quotient_connectedComponentOfOne G) 1
  have himg := hq.isCoinducing.image_connectedComponent
    (isConnected_fiber_quotient_connectedComponentOfOne G) (1 : G)
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  have h1 : ((1 : G) : G ⧸ Subgroup.connectedComponentOfOne G) = 1 := rfl
  rw [← h1, ← himg]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (QuotientGroup.mk x : G ⧸ Subgroup.connectedComponentOfOne G) = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    exact this
  · rintro rfl
    exact ⟨1, mem_connectedComponent, rfl⟩

/-- Morris, Topology Without Tears, Proposition A5.0.25 (TP-497).  With the identity component
normal, the quotient group `G / G₀` is a topological group (Mathlib's quotient-group instance) and
is totally disconnected. -/
@[kb "morris2024" "Proposition A5.0.25, p. 509"]
theorem isTopologicalGroup_totallyDisconnected_quotient_connectedComponentOfOne
    [(Subgroup.connectedComponentOfOne G).Normal] :
    IsTopologicalGroup (G ⧸ Subgroup.connectedComponentOfOne G) ∧
      TotallyDisconnectedSpace (G ⧸ Subgroup.connectedComponentOfOne G) :=
  ⟨inferInstance, totallyDisconnectedSpace_quotient_connectedComponentOfOne G⟩

end UndergradKB.Topology
