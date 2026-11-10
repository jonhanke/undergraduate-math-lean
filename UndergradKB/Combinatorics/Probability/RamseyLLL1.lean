import UndergradKB.Combinatorics.Probability.ErdosGirth
import UndergradKB.Combinatorics.Probability.LocalLemma
import UndergradKB.Common.Attr

/-!
# R(3,n) ≥ c n² / ln² n via the Local Lemma, part 1 (Keller–Trotter, p. 352–353)

Independence of events depending on disjoint sets of coordinates under the product weights `wt p`
on subsets of a finite set (the random graph `G(N, p)` is a random subset of the potential edges).
-/

namespace UndergradKB.Combinatorics

open Finset

namespace RamseyLLL

open ErdosGirth

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The event `A` (a set of edge sets) depends only on the coordinates in `F`. -/
def DepOn (A : Finset (Finset E)) (F : Finset E) : Prop :=
  ∀ S S' : Finset E, S ∩ F = S' ∩ F → (S ∈ A ↔ S' ∈ A)

/-- Weight of the cylinder "`S ∩ F = T`". -/
noncomputable def cyl (p : ℝ) (F T : Finset E) : ℝ := p ^ T.card * (1 - p) ^ (F.card - T.card)

lemma sum_wt_inter (p : ℝ) (F T : Finset E) (hT : T ⊆ F) :
    ∑ S ∈ univ.filter (fun S : Finset E => S ∩ F = T), wt p S = cyl p F T := by
  have hfil : univ.filter (fun S : Finset E => S ∩ F = T) =
      univ.filter (fun S : Finset E => T ⊆ S ∧ Disjoint S (F \ T)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [← h]; exact Finset.inter_subset_left
      · rw [Finset.disjoint_left]
        intro x hxS hxd
        rw [Finset.mem_sdiff] at hxd
        apply hxd.2
        rw [← h]; exact Finset.mem_inter.mpr ⟨hxS, hxd.1⟩
    · rintro ⟨h1, h2⟩
      ext x
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hxS, hxF⟩
        by_contra hxT
        exact Finset.disjoint_left.mp h2 hxS (Finset.mem_sdiff.mpr ⟨hxF, hxT⟩)
      · intro hxT
        exact ⟨h1 hxT, hT hxT⟩
  rw [hfil, sum_wt_cond p T (F \ T) Finset.disjoint_sdiff, Finset.card_sdiff_of_subset hT]
  rfl

lemma sum_wt_inter2 (p : ℝ) (F G T T' : Finset E) (hT : T ⊆ F) (hT' : T' ⊆ G)
    (hFG : Disjoint F G) :
    ∑ S ∈ univ.filter (fun S : Finset E => S ∩ F = T ∧ S ∩ G = T'), wt p S =
      cyl p F T * cyl p G T' := by
  have hTT' : Disjoint T T' := hFG.mono hT hT'
  have hd1 : Disjoint (F \ T) (G \ T') := hFG.mono Finset.sdiff_subset Finset.sdiff_subset
  have hd : Disjoint (T ∪ T') ((F \ T) ∪ (G \ T')) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hx2 with h | h
    · exact (Finset.mem_sdiff.mp h).2 hx
    · exact Finset.disjoint_left.mp hFG (hT hx) (Finset.mem_sdiff.mp h).1
    · exact Finset.disjoint_left.mp hFG (Finset.mem_sdiff.mp h).1 (hT' hx)
    · exact (Finset.mem_sdiff.mp h).2 hx
  have hfil : univ.filter (fun S : Finset E => S ∩ F = T ∧ S ∩ G = T') =
      univ.filter (fun S : Finset E => T ∪ T' ⊆ S ∧ Disjoint S ((F \ T) ∪ (G \ T'))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Finset.union_subset ?_ ?_, ?_⟩
      · rw [← h1]; exact Finset.inter_subset_left
      · rw [← h2]; exact Finset.inter_subset_left
      · rw [Finset.disjoint_left]
        intro x hxS hx
        rcases Finset.mem_union.mp hx with hx | hx
        · apply (Finset.mem_sdiff.mp hx).2
          rw [← h1]; exact Finset.mem_inter.mpr ⟨hxS, (Finset.mem_sdiff.mp hx).1⟩
        · apply (Finset.mem_sdiff.mp hx).2
          rw [← h2]; exact Finset.mem_inter.mpr ⟨hxS, (Finset.mem_sdiff.mp hx).1⟩
    · rintro ⟨h1, h2⟩
      constructor
      · ext x
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hxS, hxF⟩
          by_contra hxT
          exact Finset.disjoint_left.mp h2 hxS
            (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxF, hxT⟩))
        · intro hxT
          exact ⟨h1 (Finset.mem_union_left _ hxT), hT hxT⟩
      · ext x
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hxS, hxG⟩
          by_contra hxT
          exact Finset.disjoint_left.mp h2 hxS
            (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxG, hxT⟩))
        · intro hxT
          exact ⟨h1 (Finset.mem_union_right _ hxT), hT' hxT⟩
  rw [hfil, sum_wt_cond p (T ∪ T') ((F \ T) ∪ (G \ T')) hd, Finset.card_union_of_disjoint hTT',
    Finset.card_union_of_disjoint hd1, Finset.card_sdiff_of_subset hT,
    Finset.card_sdiff_of_subset hT']
  unfold cyl
  ring

/-- Probability of an event depending on `F` only. -/
lemma sum_wt_depOn (p : ℝ) {A : Finset (Finset E)} {F : Finset E} (hA : DepOn A F) :
    ∑ S ∈ A, wt p S = ∑ T ∈ F.powerset, if T ∈ A then cyl p F T else 0 := by
  classical
  have h1 : ∑ S ∈ A, wt p S = ∑ S : Finset E, if S ∈ A then wt p S else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := fun S => S ∩ F) (t := F.powerset)
    (fun S _ => Finset.mem_powerset.mpr Finset.inter_subset_right)]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTF := Finset.mem_powerset.mp hT
  have hTT : T ∩ F = T := Finset.inter_eq_left.mpr hTF
  have hiff : ∀ S ∈ univ.filter (fun S : Finset E => S ∩ F = T), (S ∈ A ↔ T ∈ A) := by
    intro S hS
    have := (Finset.mem_filter.mp hS).2
    exact hA S T (by rw [this, hTT])
  by_cases hTA : T ∈ A
  · rw [if_pos hTA, ← sum_wt_inter p F T hTF]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [if_pos ((hiff S hS).mpr hTA)]
  · rw [if_neg hTA]
    refine Finset.sum_eq_zero fun S hS => ?_
    rw [if_neg (fun h => hTA ((hiff S hS).mp h))]

/-- Events depending on disjoint sets of coordinates are independent. -/
lemma sum_wt_inter_depOn (p : ℝ) {A B : Finset (Finset E)} {F G : Finset E} (hA : DepOn A F)
    (hB : DepOn B G) (hFG : Disjoint F G) :
    ∑ S ∈ A ∩ B, wt p S = (∑ S ∈ A, wt p S) * (∑ S ∈ B, wt p S) := by
  classical
  rw [sum_wt_depOn p hA, sum_wt_depOn p hB, Finset.sum_mul_sum]
  have h1 : ∑ S ∈ A ∩ B, wt p S = ∑ S : Finset E, if S ∈ A ∧ S ∈ B then wt p S else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext S; simp
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := fun S => (S ∩ F, S ∩ G))
    (t := F.powerset ×ˢ G.powerset) (fun S _ => Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩), Finset.sum_product]
  refine Finset.sum_congr rfl fun T hT => Finset.sum_congr rfl fun T' hT' => ?_
  have hTF := Finset.mem_powerset.mp hT
  have hTG := Finset.mem_powerset.mp hT'
  have hTT : T ∩ F = T := Finset.inter_eq_left.mpr hTF
  have hTT' : T' ∩ G = T' := Finset.inter_eq_left.mpr hTG
  have hfil : univ.filter (fun S : Finset E => (S ∩ F, S ∩ G) = (T, T')) =
      univ.filter (fun S : Finset E => S ∩ F = T ∧ S ∩ G = T') := by
    ext S; simp [Prod.ext_iff]
  rw [hfil]
  have hiff : ∀ S ∈ univ.filter (fun S : Finset E => S ∩ F = T ∧ S ∩ G = T'),
      (S ∈ A ∧ S ∈ B ↔ T ∈ A ∧ T' ∈ B) := by
    intro S hS
    have := (Finset.mem_filter.mp hS).2
    rw [hA S T (by rw [this.1, hTT]), hB S T' (by rw [this.2, hTT'])]
  by_cases hc : T ∈ A ∧ T' ∈ B
  · rw [if_pos hc.1, if_pos hc.2, ← sum_wt_inter2 p F G T T' hTF hTG hFG]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [if_pos ((hiff S hS).mpr hc)]
  · have : (if T ∈ A then cyl p F T else 0) * (if T' ∈ B then cyl p G T' else 0) = 0 := by
      by_cases h1 : T ∈ A
      · have h2 : T' ∉ B := fun h2 => hc ⟨h1, h2⟩
        simp [h2]
      · simp [h1]
    rw [this]
    refine Finset.sum_eq_zero fun S hS => ?_
    rw [if_neg (fun h => hc ((hiff S hS).mp h))]

end RamseyLLL

end UndergradKB.Combinatorics
