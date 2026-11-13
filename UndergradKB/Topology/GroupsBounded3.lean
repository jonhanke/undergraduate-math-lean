import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Algebra.Group.Basic
import UndergradKB.Topology.GroupsBounded2
import UndergradKB.Topology.DualityCompact2
import UndergradKB.Common.Attr

/-!
# Compact abelian torsion groups: bounded exponent and the structure of the dual

Morris, *Topology Without Tears* (2024), Theorem A5.11.12 (`morris2024`).  First half of the proof: a compact
Hausdorff abelian torsion group has bounded exponent (Baire category theorem: the closed sets `{x | x^n = 1}`
cover the group, so one contains an open set, hence a neighbourhood of `1`, and finitely many translates of it
cover), so its dual has bounded exponent and, by Theorem A5.11.11 (`GroupsBounded2`), is a restricted direct sum
of finite cyclic groups.
-/

universe u

open Function Set Topology

namespace UndergradKB.Topology

/-- Morris, Topology Without Tears, Theorem A5.11.12 (TP-594), first step: a compact Hausdorff abelian torsion
group has bounded exponent (Baire category). -/
@[kb "morris2024" "Theorem A5.11.12, p. 580"]
theorem exists_pow_eq_one_of_compact_torsion {G : Type u} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (h : ∀ g : G, IsOfFinOrder g) :
    ∃ n : ℕ, 0 < n ∧ ∀ g : G, g ^ n = 1 := by
  classical
  let f : ℕ → Set G := fun n => {x | x ^ (n + 1) = 1}
  have hc : ∀ n, IsClosed (f n) := fun n => isClosed_eq (continuous_pow _) continuous_const
  have hU : ⋃ n, f n = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨k, hk, hx⟩ := (isOfFinOrder_iff_pow_eq_one.mp (h x))
    exact mem_iUnion.mpr ⟨k - 1, by show x ^ (k - 1 + 1) = 1; rwa [Nat.sub_add_cancel hk]⟩
  obtain ⟨m, y, hy⟩ := nonempty_interior_of_iUnion_of_closed hc hU
  have hyf : y ^ (m + 1) = 1 := interior_subset hy
  -- a neighbourhood `W` of `1` all of whose elements have `v ^ (m + 1) = 1`
  let W : Set G := (fun v => y * v) ⁻¹' interior (f m)
  have hWo : IsOpen W := isOpen_interior.preimage (continuous_const.mul continuous_id)
  have hW1 : (1 : G) ∈ W := by simpa [W] using hy
  have hWpow : ∀ v ∈ W, v ^ (m + 1) = 1 := by
    intro v hv
    have h1 : (y * v) ^ (m + 1) = 1 := interior_subset hv
    rw [mul_pow, hyf, one_mul] at h1
    exact h1
  -- finitely many translates of `W` cover `G`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : G => (fun v => g * v) '' W)
    (fun g => (isOpenMap_mul_left g) W hWo)
    (fun g _ => mem_iUnion.mpr ⟨g, ⟨1, hW1, mul_one g⟩⟩)
  refine ⟨(m + 1) * ∏ g ∈ t, orderOf g, ?_, ?_⟩
  · refine Nat.mul_pos (Nat.succ_pos m) (Finset.prod_pos fun g _ => ?_)
    exact (h g).orderOf_pos
  · intro x
    have hx := ht (mem_univ x)
    simp only [mem_iUnion] at hx
    obtain ⟨g, hg, w, hw, rfl⟩ := hx
    rw [mul_pow]
    have e1 : g ^ ((m + 1) * ∏ g ∈ t, orderOf g) = 1 := by
      rw [mul_comm, pow_mul]
      have : g ^ ∏ g ∈ t, orderOf g = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ hg)
      rw [this, one_pow]
    have e2 : w ^ ((m + 1) * ∏ g ∈ t, orderOf g) = 1 := by
      rw [pow_mul, hWpow w hw, one_pow]
    rw [e1, e2, one_mul]

/-- Morris, Topology Without Tears, Theorem A5.11.12 (TP-594), algebraic half: the dual of a compact Hausdorff
abelian torsion group is isomorphic to a restricted direct sum of finite cyclic groups. -/
@[kb "morris2024" "Theorem A5.11.12, p. 580"]
theorem exists_mulEquiv_directSum_dual_of_compact_torsion {G : Type u} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (h : ∀ g : G, IsOfFinOrder g) :
    ∃ (ι : Type u) (m : ι → ℕ), (∀ i, 0 < m i) ∧
      Nonempty (PontryaginDual G ≃* Multiplicative (DirectSum ι (fun i => ZMod (m i)))) := by
  obtain ⟨n, hn, hG⟩ := exists_pow_eq_one_of_compact_torsion h
  have hD : ∀ a : Additive (PontryaginDual G), n • a = 0 := by
    intro a
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ n = 1
    apply PontryaginDual.ext
    intro x
    rw [dual_pow_apply', ← map_pow, hG]
    exact map_one _
  obtain ⟨ι, m, hm, ⟨e⟩⟩ := exists_addEquiv_directSum_cyclic_of_exponent n hn hD
  exact ⟨ι, m, hm, ⟨(AddEquiv.toMultiplicative e).symm.symm⟩⟩

end UndergradKB.Topology
