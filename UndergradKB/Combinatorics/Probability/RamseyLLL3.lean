import UndergradKB.Combinatorics.Probability.RamseyLLL2
import UndergradKB.Common.Attr

/-!
# R(3,n) ≥ c n² / ln² n via the Local Lemma, part 3

Counting the dependency neighbourhoods, the asymmetric Local Lemma inequalities, and the existence
of an edge set with no triangle and no independent `n`-set under explicit numerical hypotheses.
-/

namespace UndergradKB.Combinatorics

open Finset

namespace RamseyLLL

open ErdosGirth UndergradKB.Combinatorics.Probability

section Counting

variable {N n : ℕ}

lemma mem_DA_iff {u v : Fin N} (huv : u ≠ v) {j : Finset (Fin N)} :
    s(u, v) ∈ DA j ↔ u ∈ j ∧ v ∈ j := by
  unfold DA
  simp only [Finset.mem_image, Finset.mem_offDiag, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb, _⟩, h⟩
    have h : s(a, b) = s(u, v) := h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  · rintro ⟨hu, hv⟩
    exact ⟨u, v, ⟨hu, hv, huv⟩, rfl⟩

lemma exists_of_mem_DA {j : Finset (Fin N)} {e : Sym2 (Fin N)} (he : e ∈ DA j) :
    ∃ u v, u ≠ v ∧ e = s(u, v) ∧ u ∈ j ∧ v ∈ j := by
  unfold DA at he
  simp only [Finset.mem_image, Finset.mem_offDiag, Prod.exists] at he
  obtain ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩ := he
  exact ⟨a, b, hab, rfl, ha, hb⟩

/-- The number of `m`-sets containing two given vertices is at most `C(N, m - 2)`. -/
lemma card_contain (m : ℕ) {u v : Fin N} (huv : u ≠ v) (hm : 2 ≤ m) :
    ((univ : Finset (Finset (Fin N))).filter
      (fun j => j.card = m ∧ u ∈ j ∧ v ∈ j)).card ≤ N.choose (m - 2) := by
  classical
  have hmaps : ∀ j ∈ (univ : Finset (Finset (Fin N))).filter
      (fun j => j.card = m ∧ u ∈ j ∧ v ∈ j), j \ {u, v} ∈ (univ : Finset (Fin N)).powersetCard (m - 2) := by
    intro j hj
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.mp hj
    have hsub : ({u, v} : Finset (Fin N)) ⊆ j := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact h2
      · rw [Finset.mem_singleton.mp hx]; exact h3
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair huv, h1]
  have hinj : Set.InjOn (fun j : Finset (Fin N) => j \ {u, v})
      ((univ : Finset (Finset (Fin N))).filter (fun j => j.card = m ∧ u ∈ j ∧ v ∈ j) :
        Set (Finset (Fin N))) := by
    intro j hj j' hj' h
    have hj1 := Finset.mem_filter.mp hj
    have hj1' := Finset.mem_filter.mp hj'
    have hsub : ({u, v} : Finset (Fin N)) ⊆ j := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hj1.2.2.1
      · rw [Finset.mem_singleton.mp hx]; exact hj1.2.2.2
    have hsub' : ({u, v} : Finset (Fin N)) ⊆ j' := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hj1'.2.2.1
      · rw [Finset.mem_singleton.mp hx]; exact hj1'.2.2.2
    simp only at h
    rw [← Finset.sdiff_union_of_subset hsub, ← Finset.sdiff_union_of_subset hsub', h]
  calc _ ≤ ((univ : Finset (Fin N)).powersetCard (m - 2)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = N.choose (m - 2) := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The weights `x` on triples and `y` on the other sets. -/
noncomputable def wgt (n : ℕ) (x y : ℝ) (j : Finset (Fin N)) : ℝ :=
  if j.card = 3 then x else y

open Classical in
lemma sum_edge (hn : 4 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {u v : Fin N} (huv : u ≠ v) :
    ∑ j ∈ (univ : Finset (Finset (Fin N))).filter (fun j => good N n j ∧ s(u, v) ∈ DA j),
        wgt n x y j ≤ (N : ℝ) * x + (N.choose (n - 2) : ℝ) * y := by
  classical
  set F3 := (univ : Finset (Finset (Fin N))).filter (fun j => j.card = 3 ∧ u ∈ j ∧ v ∈ j) with hF3
  set Fn := (univ : Finset (Finset (Fin N))).filter (fun j => j.card = n ∧ u ∈ j ∧ v ∈ j) with hFn
  have hdisj : Disjoint F3 Fn := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have := (Finset.mem_filter.mp h1).2.1
    have := (Finset.mem_filter.mp h2).2.1
    omega
  have hsub : (univ : Finset (Finset (Fin N))).filter (fun j => good N n j ∧ s(u, v) ∈ DA j) ⊆
      F3 ∪ Fn := by
    intro j hj
    obtain ⟨-, hg, he⟩ := Finset.mem_filter.mp hj
    rw [mem_DA_iff huv] at he
    rcases hg with h3 | hn'
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3, he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn', he⟩)
  have hw : ∀ j : Finset (Fin N), 0 ≤ wgt n x y j := fun j => by unfold wgt; split_ifs <;> assumption
  calc _ ≤ ∑ j ∈ F3 ∪ Fn, wgt n x y j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    _ = ∑ j ∈ F3, wgt n x y j + ∑ j ∈ Fn, wgt n x y j := Finset.sum_union hdisj
    _ = F3.card * x + Fn.card * y := by
        congr 1
        · rw [Finset.sum_congr rfl (g := fun _ => x)]
          · simp
          · intro j hj
            unfold wgt; rw [if_pos (Finset.mem_filter.mp hj).2.1]
        · rw [Finset.sum_congr rfl (g := fun _ => y)]
          · simp
          · intro j hj
            have := (Finset.mem_filter.mp hj).2.1
            unfold wgt; rw [if_neg (by omega)]
    _ ≤ _ := by
        have h1 : (F3.card : ℝ) ≤ N := by
          have := card_contain (N := N) 3 huv (by norm_num)
          have e : N.choose (3 - 2) = N := by norm_num
          rw [e] at this
          exact_mod_cast this
        have h2 : (Fn.card : ℝ) ≤ N.choose (n - 2) := by
          exact_mod_cast card_contain (N := N) n huv (by omega)
        nlinarith

open Classical in
lemma sum_nbr (hn : 4 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {i : Finset (Fin N)}
    (hi : good N n i) :
    ∑ j ∈ nbr N n i, wgt n x y j ≤
      ((DA i).card : ℝ) * ((N : ℝ) * x + (N.choose (n - 2) : ℝ) * y) := by
  classical
  have hw : ∀ j : Finset (Fin N), 0 ≤ wgt n x y j := fun j => by unfold wgt; split_ifs <;> assumption
  have hQ : 0 ≤ (N : ℝ) * x + (N.choose (n - 2) : ℝ) * y := by positivity
  calc ∑ j ∈ nbr N n i, wgt n x y j
      ≤ ∑ j ∈ nbr N n i, ∑ e ∈ DA i, if e ∈ DA j then wgt n x y j else 0 := by
        refine Finset.sum_le_sum fun j hj => ?_
        obtain ⟨-, hg, hji, hd⟩ := Finset.mem_filter.mp hj
        obtain ⟨e, he1, he2⟩ := Finset.not_disjoint_iff.mp hd
        calc wgt n x y j = (if e ∈ DA j then wgt n x y j else 0) := by rw [if_pos he2]
          _ ≤ _ := Finset.single_le_sum (f := fun e => if e ∈ DA j then wgt n x y j else 0)
              (fun e _ => by split_ifs; exact hw j; exact le_rfl) he1
    _ = ∑ e ∈ DA i, ∑ j ∈ nbr N n i, if e ∈ DA j then wgt n x y j else 0 := Finset.sum_comm
    _ ≤ ∑ e ∈ DA i, ((N : ℝ) * x + (N.choose (n - 2) : ℝ) * y) := by
        refine Finset.sum_le_sum fun e he => ?_
        obtain ⟨u, v, huv, rfl, -, -⟩ := exists_of_mem_DA he
        calc ∑ j ∈ nbr N n i, (if s(u, v) ∈ DA j then wgt n x y j else 0)
            ≤ ∑ j ∈ (univ : Finset (Finset (Fin N))).filter (fun j => good N n j ∧ s(u, v) ∈ DA j),
                wgt n x y j := by
              rw [Finset.sum_filter]
              calc _ ≤ ∑ j ∈ nbr N n i, (if good N n j ∧ s(u, v) ∈ DA j then wgt n x y j else 0) := by
                    refine Finset.sum_le_sum fun j hj => ?_
                    have hg := (Finset.mem_filter.mp hj).2.1
                    by_cases hm : s(u, v) ∈ DA j
                    · rw [if_pos hm, if_pos ⟨hg, hm⟩]
                    · rw [if_neg hm]; split_ifs <;> first | exact hw j | exact le_rfl
                _ ≤ _ := by
                    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
                    intro j _ _
                    split_ifs
                    · exact hw j
                    · exact le_rfl
          _ ≤ _ := sum_edge hn hx hy huv
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Counting

end RamseyLLL

end UndergradKB.Combinatorics
