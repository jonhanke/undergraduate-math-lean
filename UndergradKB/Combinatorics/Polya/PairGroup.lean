import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.PeriodicPts.Defs
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Polya.CycleIndex

/-!
# The pair group and counting graphs on four vertices (Keller--Trotter, Chapter 15.5.3)

The symmetric group `S_n` acts on the `2`-element subsets of `[n]` (Mathlib's action of
`Equiv.Perm α` on `Set.powersetCard α 2`); the image of `S_n` in the permutations of the pairs is
the pair group `S_n^(2)`.  A graph on `[n]` is a colouring of the pairs by "edge / non-edge"; its
isomorphism class is an orbit.  We compute the cycle index of `S_4^(2)` and the number of graphs
on four vertices.
-/

namespace UndergradKB.Combinatorics.Polya

open Finset MulAction

section General

open scoped Classical
variable {S : Type*} [Fintype S] (σ : Equiv.Perm S)

lemma mem_cycleLengths {k : ℕ} :
    k ∈ cycleLengths σ ↔
      ∃ q : orbitRel.Quotient (Subgroup.zpowers σ) S, Nat.card q.orbit = k := by
  simp [cycleLengths]

lemma one_le_of_mem_cycleLengths {k : ℕ} (hk : k ∈ cycleLengths σ) : 1 ≤ k := by
  obtain ⟨q, rfl⟩ := (mem_cycleLengths σ).1 hk
  have : Nonempty q.orbit := ⟨⟨q.out, orbitRel.Quotient.mem_orbit.2 (Quotient.out_eq' q)⟩⟩
  exact Nat.card_pos

lemma le_card_of_mem_cycleLengths {k : ℕ} (hk : k ∈ cycleLengths σ) : k ≤ Fintype.card S := by
  obtain ⟨q, rfl⟩ := (mem_cycleLengths σ).1 hk
  calc Nat.card q.orbit ≤ Nat.card S := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = Fintype.card S := Nat.card_eq_fintype_card

/-- The cycle monomial as a product over the possible cycle lengths `0, ..., |S|`. -/
lemma cycleMonomial_eq_prod_range :
    cycleMonomial σ = ∏ k ∈ range (Fintype.card S + 1),
      (MvPolynomial.X k : MvPolynomial ℕ ℚ) ^ numCyclesOfLength σ k := by
  rw [cycleMonomial_eq]
  apply Finset.prod_subset
  · intro k hk
    rw [Multiset.mem_toFinset] at hk
    exact mem_range.2 (Nat.lt_succ_of_le (le_card_of_mem_cycleLengths σ hk))
  · intro k _ hk
    rw [Multiset.mem_toFinset] at hk
    simp [numCyclesOfLength, Multiset.count_eq_zero.2 hk]

/-- Counting the points of `S` in cycles of length `k`. -/
lemma numCyclesOfLength_mul (k : ℕ) :
    numCyclesOfLength σ k * k
      = (univ.filter fun s : S => Function.minimalPeriod (fun x => σ x) s = k).card := by
  have hper : ∀ s : S, Function.minimalPeriod (fun x => σ x) s
      = Nat.card (orbitRel.Quotient.orbit
          (Quotient.mk'' s : orbitRel.Quotient (Subgroup.zpowers σ) S)) := by
    intro s
    let _ := Fintype.ofFinite (orbit (Subgroup.zpowers σ) s)
    have h1 := MulAction.minimalPeriod_eq_card σ s
    rw [orbitRel.Quotient.orbit_mk, Nat.card_eq_fintype_card]
    exact h1
  have hnum : numCyclesOfLength σ k
      = (univ.filter fun q : orbitRel.Quotient (Subgroup.zpowers σ) S =>
          Nat.card q.orbit = k).card := by
    rw [numCyclesOfLength, cycleLengths, Multiset.count_map]
    simp only [Finset.card, Finset.filter_val]
    congr 2
    ext q
    exact eq_comm
  have hset : (univ.filter fun s : S => Function.minimalPeriod (fun x => σ x) s = k)
      = univ.filter fun s : S => Nat.card (orbitRel.Quotient.orbit
          (Quotient.mk'' s : orbitRel.Quotient (Subgroup.zpowers σ) S)) = k :=
    Finset.filter_congr (fun s _ => by rw [hper s])
  rw [hnum, hset]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s : S => (Quotient.mk'' s : orbitRel.Quotient (Subgroup.zpowers σ) S))
    (t := univ.filter fun q : orbitRel.Quotient (Subgroup.zpowers σ) S => Nat.card q.orbit = k)]
  · rw [Finset.sum_congr rfl (g := fun _ => k), sum_const, smul_eq_mul]
    intro q hq
    rw [Finset.filter_filter]
    have : (univ.filter fun s : S =>
        Nat.card (orbitRel.Quotient.orbit
          (Quotient.mk'' s : orbitRel.Quotient (Subgroup.zpowers σ) S)) = k ∧
        (Quotient.mk'' s : orbitRel.Quotient (Subgroup.zpowers σ) S) = q)
        = univ.filter fun s : S => (Quotient.mk'' s : orbitRel.Quotient (Subgroup.zpowers σ) S) = q := by
      apply Finset.filter_congr
      intro s _
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [h]
        exact (mem_filter.1 hq).2
    rw [this, card_fiber]
    exact (mem_filter.1 hq).2
  · intro s hs
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hs).2⟩

end General

end UndergradKB.Combinatorics.Polya
