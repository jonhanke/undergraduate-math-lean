import Mathlib.SetTheory.ZFC.Ordinal
import UndergradKB.Common.Attr

/-!
# Wave 2: von Neumann ordinals as in Morris (Appendix 1.4, Definition A1.4.8, Proposition A1.4.9)

An ordinal number is a set `α` which is the set of the ordinals `β < α`, well ordered by `⊆`; here `<` on
ordinals is `∈` (Remark A1.4.11). In Mathlib this is `ZFSet.IsOrdinal` (a transitive set of transitive
sets, equivalently a transitive set well ordered by `∈`). We prove the book's characterisations in these
terms.
-/

universe u

namespace UndergradKB.Topology

open ZFSet

/-- `α` is well ordered by `⊆`: any two elements are comparable under `⊆` and every nonempty subset has a
`⊆`-least element. -/
def WellOrderedBySubset (α : ZFSet.{u}) : Prop :=
  (∀ β ∈ α, ∀ γ ∈ α, β ⊆ γ ∨ γ ⊆ β) ∧
    ∀ s : ZFSet.{u}, s ⊆ α → s ≠ ∅ → ∃ β ∈ s, ∀ γ ∈ s, β ⊆ γ

/-- An ordinal is well ordered by `⊆`. -/
theorem _root_.ZFSet.IsOrdinal.wellOrderedBySubset {α : ZFSet.{u}} (h : α.IsOrdinal) : WellOrderedBySubset α := by
  refine ⟨fun β hβ γ hγ => ZFSet.IsOrdinal.subset_total (h.mem hβ) (h.mem hγ), ?_⟩
  intro s hs hne
  have hex : ∃ x, x ∈ s := by
    by_contra hc
    push Not at hc
    exact hne ((ZFSet.eq_empty s).2 hc)
  obtain ⟨x0, hx0⟩ := hex
  have hwo := h.isWellOrder
  obtain ⟨m, hm, hmin⟩ := hwo.wf.has_min {y : {z // z ∈ α} | y.1 ∈ s} ⟨⟨x0, hs hx0⟩, hx0⟩
  refine ⟨m.1, hm, fun γ hγ => ?_⟩
  have hmo : m.1.IsOrdinal := h.mem m.2
  have hγo : γ.IsOrdinal := h.mem (hs hγ)
  have hnot : ¬ γ ∈ m.1 := fun hmem => hmin ⟨γ, hs hγ⟩ hγ hmem
  exact (ZFSet.IsOrdinal.notMem_iff_subset hγo hmo |>.1 hnot)

/-- Morris, Topology Without Tears, Definition A1.4.8 (TP-420), in `ZFSet` terms. A set `α` is an
ordinal iff it is a set of ordinals, closed downwards (every ordinal below an element of `α` is in `α`; the
order `<` on ordinals is `∈`), and well ordered by `⊆`. -/
@[kb "morris2024" "Definition A1.4.8, p. 419"]
theorem isOrdinal_iff_downward_closed_wellOrderedBySubset (α : ZFSet.{u}) :
    α.IsOrdinal ↔ (∀ β ∈ α, β.IsOrdinal) ∧ (∀ β ∈ α, ∀ γ, γ.IsOrdinal → γ ∈ β → γ ∈ α) ∧
      WellOrderedBySubset α := by
  constructor
  · intro h
    exact ⟨fun β hβ => h.mem hβ, fun β hβ γ _ hγ => h.mem_trans hγ hβ, h.wellOrderedBySubset⟩
  · rintro ⟨h1, h2, -⟩
    refine ZFSet.isOrdinal_iff_forall_mem_isOrdinal.2 ⟨fun β hβ γ hγ => ?_, h1⟩
    exact h2 β hβ γ ((h1 β hβ).mem hγ) hγ

/-- Morris, Topology Without Tears, Proposition A1.4.9 (TP-420). A set `α` is an ordinal iff (i) it is
well ordered by `⊆`; (ii) `α ∉ α`; (iii) no element `β` of `α` is a member of itself; (iv) every element of
`α` is a subset of `α`; (v) elements of elements of `α` are elements of `α`. -/
@[kb "morris2024" "Proposition A1.4.9, p. 419"]
theorem isOrdinal_iff_morris_conditions (α : ZFSet.{u}) :
    α.IsOrdinal ↔ WellOrderedBySubset α ∧ α ∉ α ∧ (∀ β ∈ α, β ∉ β) ∧ (∀ β ∈ α, β ⊆ α) ∧
      (∀ β ∈ α, ∀ γ ∈ β, γ ∈ α) := by
  constructor
  · intro h
    exact ⟨h.wellOrderedBySubset, ZFSet.mem_irrefl α, fun β _ => ZFSet.mem_irrefl β,
      fun β hβ => h.subset_of_mem hβ, fun β hβ γ hγ => h.mem_trans hγ hβ⟩
  · rintro ⟨⟨htot, -⟩, -, hiii, hiv, hv⟩
    refine ZFSet.isOrdinal_iff_forall_mem_isTransitive.2 ⟨hiv, fun β hβ y hy x hx => ?_⟩
    have hyα : y ∈ α := hv β hβ y hy
    rcases htot β hβ y hyα with hβy | hyβ
    · exact absurd (hβy hy) (hiii y hyα)
    · exact hyβ hx

end UndergradKB.Topology
