import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 15 (Pólya enumeration, Burnside): thin wrappers over Mathlib
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

/-- CO-313. The dihedral group of the regular `n`-gon has `2n` elements. -/
@[kb "kellertrotter2017" "text (dihedral group), p. 318"]
theorem text_p318_dihedral_card (n : ℕ) [NeZero n] :
    Fintype.card (DihedralGroup n) = 2 * n :=
  DihedralGroup.card

/-- CO-317. Burnside's lemma: the number of orbits of a finite group `G` acting on a finite set `X`
is the average, over `g ∈ G`, of the number of points fixed by `g`. -/
@[kb "kellertrotter2017" "Lemma 15.9, p. 322"]
theorem lem_15_9 (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Finite X] :
    (Nat.card (MulAction.orbitRel.Quotient G X) : ℚ) =
      (Nat.card G : ℚ)⁻¹ * ∑ g : G, (Nat.card (MulAction.fixedBy X g) : ℚ) := by
  classical
  have := Fintype.ofFinite X
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hG : (0 : ℚ) < Nat.card G := Nat.cast_pos.2 Nat.card_pos
  simp only [Nat.card_eq_fintype_card] at hG ⊢
  have h' : (∑ g : G, (Fintype.card (MulAction.fixedBy X g) : ℚ)) =
      (Fintype.card (MulAction.orbitRel.Quotient G X) : ℚ) * Fintype.card G := by
    exact_mod_cast h
  rw [h']
  field_simp


/-! ### Definitions of Chapter 15 in the book's terms -/

/-- CO-310. A group acting on a set induces the equivalence "lies in the same orbit"; the classes
are the nonequivalent objects. -/
@[kb "kellertrotter2017" "text (action equivalence), p. 317"]
theorem text_p317_orbit_equivalence (G X : Type*) [Group G] [MulAction G X] (x y : X) :
    MulAction.orbitRel G X x y ↔ ∃ g : G, g • y = x := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- CO-311. A permutation group is a set of bijections of `X` containing the identity and closed
under composition and inverses, i.e. a subgroup of `Equiv.Perm X`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) permutation group, p. 318"]
theorem def_p318_permutation_group (X : Type*) (H : Subgroup (Equiv.Perm X)) :
    1 ∈ H ∧ (∀ f ∈ H, ∀ g ∈ H, f * g ∈ H) ∧ ∀ f ∈ H, f⁻¹ ∈ H :=
  ⟨H.one_mem, fun _ hf _ hg => H.mul_mem hf hg, fun _ hf => H.inv_mem hf⟩

/-- CO-312. The symmetric group `S_n` of all permutations of `[n]` has `n!` elements. -/
@[kb "kellertrotter2017" "Definition (unnumbered) symmetric group, p. 318"]
theorem def_p318_symmetric_group (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- CO-315. `fix(π)` is the set of colorings fixed by `π`, and `stab(C)` the set of group
elements fixing the coloring `C`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) fix and stab, p. 321"]
theorem def_p321_fix_stab (G X : Type*) [Group G] [MulAction G X] (g : G) (x : X) :
    (x ∈ MulAction.fixedBy X g ↔ g • x = x) ∧ (g ∈ MulAction.stabilizer G x ↔ g • x = x) :=
  ⟨MulAction.mem_fixedBy, MulAction.mem_stabilizer_iff⟩

end UndergradKB.Combinatorics.Course.KellerTrotter
