import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapters 3, 4 and 6: groups, cyclic groups, cosets

Results of the chapters on groups, cyclic subgroups and cosets that Mathlib does not state in the
book's form. -/

open scoped Pointwise

namespace UndergradKB.AbstractAlgebra

section Identity

variable {G : Type*} [Group G]

/-- AA-036. An element acting as a left identity on every element of a group is `1`. -/
@[kb "judson2026" "Proposition 3.2.10, p. 48"]
theorem identity_unique_left (e : G) (h : ∀ g : G, e * g = g) : e = 1 := by
  simpa using h 1

/-- AA-036. An element acting as a right identity on every element of a group is `1`. -/
theorem identity_unique_right (e : G) (h : ∀ g : G, g * e = g) : e = 1 := by
  simpa using h 1

/-- AA-036. Inverses are unique: two right inverses of `g` coincide. -/
theorem inverse_unique (g a b : G) (ha : g * a = 1) (hb : g * b = 1) : a = b := by
  rw [eq_inv_of_mul_eq_one_right ha, eq_inv_of_mul_eq_one_right hb]

/-- AA-036. The identity of a group is unique, in the book's form: any `e` that is a left identity
or a right identity for all elements is `1`, and inverses are unique. -/
@[kb "judson2026" "Proposition 3.2.10, p. 48"]
theorem identity_and_inverse_unique :
    (∀ e : G, (∀ g : G, e * g = g) → e = 1) ∧ (∀ e : G, (∀ g : G, g * e = g) → e = 1) ∧
      ∀ g a b : G, g * a = 1 → g * b = 1 → a = b :=
  ⟨identity_unique_left, identity_unique_right, inverse_unique⟩

end Identity

section SubgroupsOfZ

/-- AA-053. Every subgroup of `ℤ` is `nℤ` for a unique natural number `n`. -/
@[kb "judson2026" "Corollary 4.1.11, p. 61"]
theorem subgroups_of_int (H : AddSubgroup ℤ) :
    ∃! n : ℕ, H = AddSubgroup.zmultiples (n : ℤ) := by
  obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq H).mp H.isAddCyclic
  refine ⟨g.natAbs, ?_, ?_⟩
  · simp only
    rw [Int.zmultiples_natAbs]
    exact hg.symm
  · intro m hm
    rw [← hg, ← Int.zmultiples_natAbs] at hm
    have e1 : (m : ℤ) ∈ AddSubgroup.zmultiples ((g.natAbs : ℕ) : ℤ) := by
      rw [hm]; exact AddSubgroup.mem_zmultiples _
    have e2 : ((g.natAbs : ℕ) : ℤ) ∈ AddSubgroup.zmultiples (m : ℤ) := by
      rw [← hm]; exact AddSubgroup.mem_zmultiples _
    rw [Int.mem_zmultiples_iff] at e1 e2
    exact Nat.dvd_antisymm (by exact_mod_cast e2) (by exact_mod_cast e1)

end SubgroupsOfZ

section Generators

/-- AA-056. For `n > 0`, the residue class of `r` generates `ℤ/nℤ` iff `gcd(r, n) = 1`. -/
@[kb "judson2026" "Corollary 4.1.14, p. 61"]
theorem zmultiples_eq_top_iff_coprime (n : ℕ) [NeZero n] (r : ℕ) :
    AddSubgroup.zmultiples (r : ZMod n) = ⊤ ↔ Nat.Coprime r n := by
  rw [← AddSubgroup.card_eq_iff_eq_top, Nat.card_zmultiples, ZMod.addOrderOf_coe r (NeZero.ne n),
    Nat.card_zmod]
  have hg : 0 < n.gcd r := Nat.gcd_pos_of_pos_left _ (NeZero.pos n)
  have hd : n.gcd r ∣ n := Nat.gcd_dvd_left _ _
  constructor
  · intro h
    have : n.gcd r = 1 := by
      obtain ⟨k, hk⟩ := hd
      rw [Nat.div_eq_of_eq_mul_right hg hk] at h
      nlinarith [NeZero.pos n, hk]
    simpa [Nat.Coprime, Nat.gcd_comm] using this
  · intro h
    have : n.gcd r = 1 := by simpa [Nat.Coprime, Nat.gcd_comm] using h
    simp [this]

/-- AA-056. Same, for a residue `r : ZMod n` represented by `r.val`. -/
theorem zmultiples_eq_top_iff_coprime_val (n : ℕ) [NeZero n] (r : ZMod n) :
    AddSubgroup.zmultiples r = ⊤ ↔ Nat.Coprime r.val n := by
  rw [← zmultiples_eq_top_iff_coprime, ZMod.natCast_zmod_val]

end Generators

section Cosets

variable {G : Type*} [Group G]

/-- AA-079. Lemma 6.1.3: for a subgroup `H` and `g₁ g₂ : G`, the following are equivalent:
`g₁H = g₂H`, `Hg₁⁻¹ = Hg₂⁻¹`, `g₁H ⊆ g₂H`, `g₂ ∈ g₁H`, `g₁⁻¹g₂ ∈ H`. -/
@[kb "judson2026" "Lemma 6.1.3, p. 90"]
theorem coset_equivalences (H : Subgroup G) (g₁ g₂ : G) :
    List.TFAE
      [g₁ • (H : Set G) = g₂ • (H : Set G),
       MulOpposite.op g₁⁻¹ • (H : Set G) = MulOpposite.op g₂⁻¹ • (H : Set G),
       g₁ • (H : Set G) ⊆ g₂ • (H : Set G),
       g₂ ∈ g₁ • (H : Set G),
       g₁⁻¹ * g₂ ∈ H] := by
  have h5 : g₁⁻¹ * g₂ ∈ H ↔ g₂⁻¹ * g₁ ∈ H := by
    rw [← H.inv_mem_iff]; simp
  tfae_have 1 ↔ 5 := leftCoset_eq_iff H
  tfae_have 4 ↔ 5 := mem_leftCoset_iff g₁
  tfae_have 2 ↔ 5 := by
    rw [rightCoset_eq_iff]
    simpa using h5.symm
  tfae_have 1 → 3 := fun h => h.le
  tfae_have 3 → 5 := by
    intro h
    have : g₁ ∈ g₂ • (H : Set G) := h ⟨1, H.one_mem, by simp⟩
    rw [mem_leftCoset_iff] at this
    exact h5.mpr this
  tfae_finish

end Cosets

end UndergradKB.AbstractAlgebra
