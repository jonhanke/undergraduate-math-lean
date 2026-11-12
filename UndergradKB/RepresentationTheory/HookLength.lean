import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Algebra.BigOperators.Intervals
import UndergradKB.RepresentationTheory.FrobeniusTheorem
import UndergradKB.Common.Attr

/-!
# The hook length formula

For a Young diagram `μ` the hook length of a box `(i, j)` is the number of boxes to its right in the
same row, plus the number of boxes below it in the same column, plus one.  We show that the hook
lengths in row `i` are exactly the numbers `1, …, l_i` with the differences `l_i - l_k` (`k > i`)
removed, where `l_i = μ_i + N - 1 - i`.  Combined with the dimension formula
`finrank_specht_eq`, this gives the hook length formula `dim V_λ = n! / ∏ hooks`.
-/

namespace UndergradKB.RepresentationTheory

open Finset

/-- Hook length of the box `(i, j)` of a Young diagram: arm length plus leg length plus one,
written as `(μ_i - j) + (μ'_j - i) - 1`. -/
def hookLength (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) - 1

private lemma rowShift_lt (μ : YoungDiagram) (N : ℕ) (k k' : Fin N) (h : k < k') :
    μ.rowLen k' + rhoExp N k' < μ.rowLen k + rhoExp N k := by
  have := μ.rowLen_anti k k' (le_of_lt h)
  have h' : (k : ℕ) < k' := h
  have := k'.2
  simp only [rhoExp, Fin.val_rev]
  omega

private lemma hook_row (μ : YoungDiagram) (N : ℕ) (hN : μ.colLen 0 ≤ N) (i : Fin N) :
    (∏ j ∈ range (μ.rowLen i), hookLength μ (i, j)) *
      ∏ k ∈ Ioi i, ((μ.rowLen i + rhoExp N i) - (μ.rowLen k + rhoExp N k)) =
    (μ.rowLen i + rhoExp N i).factorial := by
  have hc : ∀ j, μ.colLen j ≤ N := fun j => (μ.colLen_anti 0 j (Nat.zero_le _)).trans hN
  have key : ∀ k j : ℕ, k < μ.colLen j ↔ j < μ.rowLen k := fun k j => by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  have hrho : ∀ k : Fin N, rhoExp N k = N - (k + 1) := fun k => by
    simp [rhoExp, Fin.val_rev]
  have hl := rowShift_lt μ N
  set H := (range (μ.rowLen i)).image (fun j => hookLength μ (i, j)) with hH
  set D := (Ioi i).image
    (fun k : Fin N => (μ.rowLen i + rhoExp N i) - (μ.rowLen k + rhoExp N k)) with hD
  have hHinj : Set.InjOn (fun j => hookLength μ (i, j)) (range (μ.rowLen i) : Set ℕ) := by
    intro j hj j' hj' hjj
    simp only [coe_range, Set.mem_Iio] at hj hj'
    simp only [hookLength] at hjj
    have k1 := (key i j).2 hj
    have k2 := (key i j').2 hj'
    rcases lt_trichotomy j j' with h | h | h
    · have := μ.colLen_anti j j' h.le
      omega
    · exact h
    · have := μ.colLen_anti j' j h.le
      omega
  have hDinj : Set.InjOn
      (fun k : Fin N => (μ.rowLen i + rhoExp N i) - (μ.rowLen k + rhoExp N k)) (Ioi i : Set (Fin N)) := by
    intro k hk k' hk' hkk
    simp only [coe_Ioi, Set.mem_Ioi] at hk hk'
    simp only at hkk
    rcases lt_trichotomy k k' with h | h | h
    · have := hl k k' h
      have := hl i k hk
      have := hl i k' hk'
      omega
    · exact h
    · have := hl k' k h
      have := hl i k hk
      have := hl i k' hk'
      omega
  have hdisj : Disjoint H D := by
    rw [Finset.disjoint_left]
    intro x hxH hxD
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hxH
    obtain ⟨k, hk, hkx⟩ := Finset.mem_image.1 hxD
    rw [mem_range] at hj
    rw [mem_Ioi] at hk
    simp only [hookLength] at hkx
    have h1 := (key i j).2 hj
    have h2 := key k j
    have h3 := hl i k hk
    have h4 := hc j
    have h5 : (i : ℕ) < k := hk
    have h6 := k.2
    rw [hrho, hrho] at hkx h3
    omega
  have hsub : H ∪ D ⊆ Icc 1 (μ.rowLen i + rhoExp N i) := by
    intro x hx
    rw [mem_union] at hx
    rw [mem_Icc]
    rcases hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      rw [mem_range] at hj
      have h1 := (key i j).2 hj
      have h4 := hc j
      simp only [hookLength]
      rw [hrho]
      have := i.2
      omega
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      rw [mem_Ioi] at hk
      have h3 := hl i k hk
      omega
  have hcard : (H ∪ D).card = μ.rowLen i + rhoExp N i := by
    rw [Finset.card_union_of_disjoint hdisj, hH, hD, card_image_of_injOn hHinj,
      card_image_of_injOn hDinj, card_range, Fin.card_Ioi, hrho]
    have := i.2
    omega
  have heq : H ∪ D = Icc 1 (μ.rowLen i + rhoExp N i) :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have hprod : ∏ x ∈ Icc 1 (μ.rowLen i + rhoExp N i), x = (μ.rowLen i + rhoExp N i).factorial := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    exact Finset.prod_Ico_id_eq_factorial _
  rw [← heq, prod_union hdisj, hH, hD, prod_image hHinj, prod_image hDinj] at hprod
  exact hprod

/-- The product of all hook lengths of a Young diagram, as a double product over rows. -/
private lemma prod_cells_hook (μ : YoungDiagram) (N : ℕ) (hN : μ.colLen 0 ≤ N) :
    ∏ c ∈ μ.cells, hookLength μ c =
      ∏ i : Fin N, ∏ j ∈ range (μ.rowLen i), hookLength μ (i, j) := by
  rw [Finset.prod_finset_product μ.cells (range N) (fun i => range (μ.rowLen i))]
  · exact (Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range (μ.rowLen i), hookLength μ (i, j)) N).symm
  · intro p
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, mem_range, mem_range]
    constructor
    · intro h
      refine ⟨?_, h⟩
      have : p.1 < μ.colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
        omega
      omega
    · exact fun h => h.2

/-- **Theorem 4.53 (hook length formula).**  The dimension of the irreducible representation
`V_λ` of `S_n` multiplied by the product of all hook lengths of `λ` equals `n!`. -/
@[kb "etingof2011" "Theorem 4.53, p. 64"]
theorem finrank_specht_mul_prod_hook {n : ℕ} (la : DiagramsOfSize n) :
    (Module.finrank ℂ (spechtIrrRep n la).V : ℂ) *
      ∏ c ∈ la.1.cells, (hookLength la.1 c : ℂ) = n.factorial := by
  set N := la.1.colLen 0 with hNdef
  have hN : la.1.colLen 0 ≤ N := le_rfl
  rw [finrank_specht_eq la hN]
  have hrow := fun i : Fin N => hook_row la.1 N hN i
  have hQ : (∏ i : Fin N, (((la.1.rowLen i + rhoExp N i).factorial : ℕ) : ℂ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  have hmain : (∏ c ∈ la.1.cells, (hookLength la.1 c : ℂ)) *
      (∏ i : Fin N, ∏ j ∈ Ioi i,
        ((((la.1.rowLen i + rhoExp N i : ℕ)) : ℂ) - ((la.1.rowLen j + rhoExp N j : ℕ) : ℂ))) =
      ∏ i : Fin N, (((la.1.rowLen i + rhoExp N i).factorial : ℕ) : ℂ) := by
    have hrc : ∀ i : Fin N, ((∏ j ∈ range (la.1.rowLen i), (hookLength la.1 (i, j) : ℂ)) *
        ∏ k ∈ Ioi i, ((((la.1.rowLen i + rhoExp N i : ℕ)) : ℂ) -
          ((la.1.rowLen k + rhoExp N k : ℕ) : ℂ))) =
        (((la.1.rowLen i + rhoExp N i).factorial : ℕ) : ℂ) := by
      intro i
      have h := congrArg (fun m : ℕ => (m : ℂ)) (hrow i)
      simp only [Nat.cast_mul, Nat.cast_prod] at h
      rw [← h]
      congr 1
      refine prod_congr rfl fun k hk => ?_
      have hlt := rowShift_lt la.1 N i k (mem_Ioi.1 hk)
      rw [Nat.cast_sub hlt.le]
    have hcells : ∏ c ∈ la.1.cells, (hookLength la.1 c : ℂ) =
        ∏ i : Fin N, ∏ j ∈ range (la.1.rowLen i), (hookLength la.1 (i, j) : ℂ) := by
      rw [← Nat.cast_prod, prod_cells_hook la.1 N hN, Nat.cast_prod]
      simp only [Nat.cast_prod]
    rw [hcells, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hrc i
  have hnat : (∏ i : Fin N, (((la.1.rowLen i + rhoExp N i).factorial : ℕ) : ℂ)) ≠ 0 := hQ
  rw [div_mul_eq_mul_div, div_eq_iff hnat, ← hmain]
  ring

end UndergradKB.RepresentationTheory
