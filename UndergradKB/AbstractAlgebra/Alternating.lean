import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import UndergradKB.Common.Attr

/-! # Judson–Beezer, section 10.2: simplicity of the alternating groups

Normal subgroups of `Aₙ` and 3-cycles. -/

namespace UndergradKB.AbstractAlgebra

open Equiv Equiv.Perm

/-- A 3-cycle is conjugated to its inverse by a transposition. -/
theorem exists_odd_conj_inv {α : Type*} [Fintype α] [DecidableEq α] {c : Perm α}
    (hc : IsThreeCycle c) : ∃ τ : Perm α, sign τ = -1 ∧ τ * c * τ⁻¹ = c⁻¹ := by
  obtain ⟨a, ha⟩ : ∃ a, a ∈ c.support := by
    by_contra h
    push Not at h
    apply hc.ne_one
    ext x
    simpa using h x
  have hsupp := hc.support_eq_iff_mem_support.mpr ha
  have hcard := hc.card_support
  have hceq := hc.eq_swap_mul_swap_iff_mem_support.mpr ha
  have hab : c a ≠ a := by simpa using ha
  have hbe : c (c a) ≠ c a := by
    have := (Equiv.Perm.apply_mem_support (f := c) (x := a)).mpr ha
    simpa using this
  have hae : c (c a) ≠ a := by
    intro h
    rw [hsupp, h] at hcard
    have e1 : ({a, c a, a} : Finset α) = {a, c a} := by
      ext x; simp; tauto
    rw [e1] at hcard
    have := Finset.card_le_two (a := a) (b := c a)
    omega
  generalize c (c a) = e at *
  generalize c a = b at *
  refine ⟨swap b e, by rw [sign_swap hbe.symm], ?_⟩
  have : c⁻¹ = swap b e * swap a b := by
    rw [hceq]; simp [mul_inv_rev]
  rw [this, hceq]
  simp [mul_assoc]

/-- AA-149. For `n ≥ 3`, a normal subgroup of `Aₙ` containing a 3-cycle is all of `Aₙ`.
(All 3-cycles of `Aₙ` are then in the subgroup, and they generate `Aₙ`.) -/
@[kb "judson2026" "Lemma 10.2.2, p. 146"]
theorem alternatingGroup_eq_top_of_threeCycle {n : ℕ} (_hn : 3 ≤ n)
    (N : Subgroup (alternatingGroup (Fin n))) [N.Normal]
    (h : ∃ g ∈ N, IsThreeCycle (g : Perm (Fin n))) : N = ⊤ := by
  obtain ⟨g, hgN, hg3⟩ := h
  obtain ⟨τ, hτ, hτc⟩ := exists_odd_conj_inv hg3
  have hginv : g⁻¹ ∈ N := N.inv_mem hgN
  have hall : ∀ d : alternatingGroup (Fin n), IsThreeCycle (d : Perm (Fin n)) → d ∈ N := by
    intro d hd
    obtain ⟨π, hπ⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hg3.cycleType.trans hd.cycleType.symm))
    rcases Int.units_eq_one_or (sign π) with h1 | h1
    · have hmem : π ∈ alternatingGroup (Fin n) := mem_alternatingGroup.mpr h1
      have := (inferInstance : N.Normal).conj_mem g hgN ⟨π, hmem⟩
      convert this using 1
      apply Subtype.ext
      simpa using hπ.symm
    · have hmem : π * τ ∈ alternatingGroup (Fin n) := by
        rw [mem_alternatingGroup, map_mul, h1, hτ]; decide
      have := (inferInstance : N.Normal).conj_mem g⁻¹ hginv ⟨π * τ, hmem⟩
      convert this using 1
      apply Subtype.ext
      have hc2 : τ * (g : Perm (Fin n))⁻¹ * τ⁻¹ = g := by
        calc τ * (g : Perm (Fin n))⁻¹ * τ⁻¹ = (τ * g * τ⁻¹)⁻¹ := by group
          _ = (g : Perm (Fin n))⁻¹⁻¹ := by rw [hτc]
          _ = g := inv_inv _
      have h4 := congrArg (fun x => π * x * π⁻¹) hc2
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev]
      rw [← hπ, ← h4]
      group
  rw [eq_top_iff, ← alternatingGroup.closure_isThreeCycles_eq_top, Subgroup.closure_le]
  exact hall

/-- AA-150. For `n ≥ 5`, every nontrivial normal subgroup of `Aₙ` contains a 3-cycle
(it is all of `Aₙ` by simplicity, and `Aₙ` has 3-cycles). -/
@[kb "judson2026" "Lemma 10.2.3, p. 146"]
theorem exists_threeCycle_of_normal_ne_bot {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (alternatingGroup (Fin n))) [N.Normal] (hN : N ≠ ⊥) :
    ∃ g ∈ N, IsThreeCycle (g : Perm (Fin n)) := by
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have htop : N = ⊤ :=
    (alternatingGroup.normal_subgroup_eq_bot_or_eq_top hcard).resolve_left hN
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have h3 : IsThreeCycle (swap a b * swap a c) :=
    isThreeCycle_swap_mul_swap_same (by simp [a, b, Fin.ext_iff]) (by simp [a, c, Fin.ext_iff])
      (by simp [b, c, Fin.ext_iff])
  exact ⟨⟨_, h3.mem_alternatingGroup⟩, by rw [htop]; trivial, h3⟩

end UndergradKB.AbstractAlgebra
