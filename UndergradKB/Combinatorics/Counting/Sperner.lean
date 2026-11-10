import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Basic
import UndergradKB.Common.Attr

/-!
# Extremal families in Sperner's theorem

Source: Keller--Trotter, *Applied Combinatorics* (2017), remark on p. 343.
Mathlib proves the bound `IsAntichain.sperner`; here we determine the extremal antichains.
-/

namespace UndergradKB.Combinatorics.Counting

open Finset
open scoped FinsetFamily

variable {α : Type*} [Fintype α] [DecidableEq α]

section Aux

theorem choose_lt_choose_succ_of_lt_half {n k : ℕ} (h : k + 1 ≤ n / 2) :
    n.choose k < n.choose (k + 1) := by
  have h1 : (n.choose k) * (k + 1) < (n.choose k) * (n - k) := by
    apply Nat.mul_lt_mul_of_pos_left (by omega)
    exact Nat.choose_pos (by omega)
  have h2 := Nat.choose_succ_right_eq n k
  rw [← h2] at h1
  exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)

theorem choose_lt_choose_half {n k : ℕ} (h : k < n / 2) : n.choose k < n.choose (n / 2) := by
  obtain ⟨d, hd⟩ : ∃ d, k + d + 1 = n / 2 := ⟨n / 2 - k - 1, by omega⟩
  clear h
  induction d generalizing k with
  | zero =>
    have := choose_lt_choose_succ_of_lt_half (n := n) (k := k) (by omega)
    simpa [← hd] using this
  | succ d ih =>
    have h1 := choose_lt_choose_succ_of_lt_half (n := n) (k := k) (by omega)
    have h2 := ih (k := k + 1) (by omega)
    exact h1.trans h2

/-- A size `k` with `C(n,k) = C(n, n/2)` is `n/2` or `(n+1)/2`. -/
theorem eq_half_of_choose_eq {n k : ℕ} (hk : k ≤ n) (h : n.choose k = n.choose (n / 2)) :
    k = n / 2 ∨ k = (n + 1) / 2 := by
  by_contra hne
  push Not at hne
  rcases lt_or_ge k (n / 2) with h1 | h1
  · exact absurd h (choose_lt_choose_half h1).ne
  · have h2 : n - k < n / 2 := by omega
    have := choose_lt_choose_half h2
    rw [Nat.choose_symm hk] at this
    exact absurd h this.ne

end Aux

section Main

variable {A : Finset (Finset α)}

omit [DecidableEq α] in
/-- Step 1: in an extremal antichain all members have size `n/2` or `(n+1)/2`. -/
theorem sperner_extremal_sizes (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α)))
    (hcard : #A = (Fintype.card α).choose (Fintype.card α / 2)) :
    ∀ s ∈ A, #s = Fintype.card α / 2 ∨ #s = (Fintype.card α + 1) / 2 := by
  intro s hs
  by_contra hne
  push Not at hne
  have hch : (Fintype.card α).choose #s ≠ (Fintype.card α).choose (Fintype.card α / 2) :=
    fun h => (eq_half_of_choose_eq (card_le_univ s) h).elim hne.1 hne.2
  have hlt : (Fintype.card α).choose #s < (Fintype.card α).choose (Fintype.card α / 2) :=
    lt_of_le_of_ne (Nat.choose_le_middle _ _) hch
  have hpos : (0 : ℚ) < (Fintype.card α).choose #s := by exact_mod_cast Nat.choose_pos (card_le_univ s)
  have hlym := lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ) hA
  have hltq : (((Fintype.card α).choose (Fintype.card α / 2) : ℚ))⁻¹
      < (((Fintype.card α).choose #s : ℚ))⁻¹ := by
    apply inv_strictAnti₀ hpos
    exact_mod_cast hlt
  have hsum : ∑ t ∈ A, (((Fintype.card α).choose (Fintype.card α / 2) : ℚ))⁻¹
      < ∑ t ∈ A, (((Fintype.card α).choose #t : ℚ))⁻¹ := by
    apply Finset.sum_lt_sum
    · intro t _
      have hp : (0 : ℚ) < (Fintype.card α).choose #t := by
        exact_mod_cast Nat.choose_pos (card_le_univ t)
      apply inv_anti₀ hp
      exact_mod_cast Nat.choose_le_middle _ _
    · exact ⟨s, hs, hltq⟩
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have hc : (0 : ℚ) < (Fintype.card α).choose (Fintype.card α / 2) :=
    by exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)
  rw [mul_inv_cancel₀ hc.ne'] at hsum
  exact lt_irrefl _ (lt_of_lt_of_le hsum hlym)

/-- The `(m+1)`-sets of a `(2m+1)`-set with `m+1` subsets of size `m` above each `m`-set. -/
theorem card_supersets {n m : ℕ} (hn : Fintype.card α = n) (x : Finset α) (hx : #x = m) :
    #((powersetCard (m + 1) (univ : Finset α)).filter (fun u => x ⊆ u)) = n - m := by
  have : (powersetCard (m + 1) (univ : Finset α)).filter (fun u => x ⊆ u)
      = xᶜ.image (fun a => insert a x) := by
    ext u
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_image, mem_compl]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a, ha, rfl⟩ := Finset.exists_eq_insert_iff.2 ⟨h2, by omega⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨?_, subset_insert _ _⟩
      rw [card_insert_of_notMem ha, hx]
  rw [this, card_image_of_injOn (insert_inj_on' _), card_compl, hn, hx]

/-- Odd case: if an extremal antichain on `2m+1` points contains an `(m+1)`-set then it is the
whole layer of `(m+1)`-sets. -/
theorem odd_case {m : ℕ} (hn : Fintype.card α = 2 * m + 1)
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α)))
    (hcard : #A = (Fintype.card α).choose (Fintype.card α / 2))
    (hsz : ∀ s ∈ A, #s = m ∨ #s = m + 1) {u0 : Finset α} (hu0 : u0 ∈ A) (hu0c : #u0 = m + 1) :
    A = powersetCard (m + 1) univ := by
  have hm : Fintype.card α / 2 = m := by omega
  rw [hm] at hcard
  obtain ⟨U, hU⟩ : ∃ U, U = A.filter (fun s => #s = m + 1) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = A.filter (fun s => #s = m) := ⟨_, rfl⟩
  have hmemU : ∀ s, s ∈ U ↔ s ∈ A ∧ #s = m + 1 := fun s => by rw [hU, mem_filter]
  have hmemL : ∀ s, s ∈ L ↔ s ∈ A ∧ #s = m := fun s => by rw [hL, mem_filter]
  have hUsz : ∀ s ∈ U, #s = m + 1 := fun s hs => ((hmemU s).1 hs).2
  have hLsz : ∀ s ∈ L, #s = m := fun s hs => ((hmemL s).1 hs).2
  have hUA : U ⊆ A := fun s hs => ((hmemU s).1 hs).1
  have hLA : L ⊆ A := fun s hs => ((hmemL s).1 hs).1
  have hAUL : A = U ∪ L := by
    ext s
    rw [mem_union, hmemU, hmemL]
    constructor
    · intro hs
      rcases hsz s hs with h | h
      · exact Or.inr ⟨hs, h⟩
      · exact Or.inl ⟨hs, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint U L := by
    rw [disjoint_left]
    intro s h1 h2
    have := hUsz s h1
    have := hLsz s h2
    omega
  have hsplit : #U + #L = #A := by rw [← card_union_of_disjoint hdisj, ← hAUL]
  have hUs : (U : Set (Finset α)).Sized (m + 1) := fun s hs => hUsz s (mem_coe.1 hs)
  have hshsz : ((∂ U : Finset (Finset α)) : Set (Finset α)).Sized m := by
    have := Set.Sized.shadow hUs
    simpa using this
  -- local LYM
  have hlocal : #U ≤ #(∂ U) := by
    have h := local_lubell_yamamoto_meshalkin_inequality_mul hUs
    have e : Fintype.card α - (m + 1) + 1 = m + 1 := by omega
    rw [e] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos m)
  have hdisj2 : Disjoint L (∂ U) := by
    rw [disjoint_left]
    intro t htL htS
    obtain ⟨s, hs, a, ha, rfl⟩ := mem_shadow_iff.1 htS
    have h1 := hUsz s hs
    refine hA (hLA htL) (hUA hs) (fun h => ?_) (erase_subset a s)
    have := hLsz _ htL
    rw [h] at this
    omega
  have hLS : L ∪ ∂ U ⊆ powersetCard m univ := by
    intro t ht
    rw [mem_powersetCard]
    refine ⟨subset_univ _, ?_⟩
    rcases mem_union.1 ht with h | h
    · exact hLsz t h
    · exact hshsz (mem_coe.2 h)
  have hle : #L + #(∂ U) ≤ (Fintype.card α).choose m := by
    rw [← card_union_of_disjoint hdisj2]
    calc #(L ∪ ∂ U) ≤ #(powersetCard m (univ : Finset α)) := card_le_card hLS
      _ = _ := by rw [card_powersetCard, card_univ]
  have hshU : #(∂ U) = #U := by omega
  -- the double count
  have hbelow : ∀ u ∈ U, #((∂ U).bipartiteBelow (fun x y => x ⊆ y) u) = m + 1 := by
    intro u hu
    have : (∂ U).bipartiteBelow (fun x y => x ⊆ y) u = powersetCard m u := by
      ext t
      rw [mem_bipartiteBelow, mem_powersetCard]
      constructor
      · rintro ⟨ht, hsub⟩
        exact ⟨hsub, hshsz (mem_coe.2 ht)⟩
      · rintro ⟨hsub, hc⟩
        refine ⟨mem_shadow_iff_exists_sdiff.2 ⟨u, hu, hsub, ?_⟩, hsub⟩
        rw [card_sdiff_of_subset hsub, hc, hUsz u hu]
        omega
    rw [this, card_powersetCard, hUsz u hu]
    simp
  have habove : ∀ x ∈ ∂ U, #(U.bipartiteAbove (fun x y => x ⊆ y) x)
      ≤ #((powersetCard (m + 1) (univ : Finset α)).filter (fun u => x ⊆ u)) := by
    intro x _
    apply card_le_card
    intro u hu
    rw [mem_bipartiteAbove] at hu
    rw [mem_filter, mem_powersetCard]
    exact ⟨⟨subset_univ _, hUsz u hu.1⟩, hu.2⟩
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun x y : Finset α => x ⊆ y) (s := ∂ U) (t := U)
  have hsumA : ∑ x ∈ ∂ U, #(U.bipartiteAbove (fun x y => x ⊆ y) x)
      = ∑ x ∈ ∂ U, #((powersetCard (m + 1) (univ : Finset α)).filter (fun u => x ⊆ u)) := by
    rw [hdc, Finset.sum_const_nat hbelow,
      Finset.sum_const_nat (m := m + 1) (fun x hx => by
        rw [card_supersets rfl x (hshsz (mem_coe.2 hx))]
        omega), hshU]
  have heq := (Finset.sum_eq_sum_iff_of_le habove).1 hsumA
  have hclosed : ∀ x ∈ ∂ U, ∀ b, b ∉ x → insert b x ∈ U := by
    intro x hx b hb
    have h1 := heq x hx
    have h2 : U.bipartiteAbove (fun x y => x ⊆ y) x
        = (powersetCard (m + 1) (univ : Finset α)).filter (fun u => x ⊆ u) := by
      apply eq_of_subset_of_card_le
      · intro u hu
        rw [mem_bipartiteAbove] at hu
        rw [mem_filter, mem_powersetCard]
        exact ⟨⟨subset_univ _, hUsz u hu.1⟩, hu.2⟩
      · exact h1.ge
    have : insert b x ∈ (powersetCard (m + 1) (univ : Finset α)).filter (fun u => x ⊆ u) := by
      rw [mem_filter, mem_powersetCard, card_insert_of_notMem hb, hshsz (mem_coe.2 hx)]
      exact ⟨⟨subset_univ _, rfl⟩, subset_insert _ _⟩
    rw [← h2, mem_bipartiteAbove] at this
    exact this.1
  have hconn : ∀ k, ∀ u ∈ U, ∀ v : Finset α, #v = m + 1 → #(v \ u) = k → v ∈ U := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hu v hv hk
      by_cases hsub : v ⊆ u
      · have : v = u := eq_of_subset_of_card_le hsub (by rw [hv, hUsz u hu])
        rw [this]; exact hu
      · obtain ⟨x, hxv, hxu⟩ := not_subset.1 hsub
        have hnot : ¬ u ⊆ v := fun h =>
          hsub (eq_of_subset_of_card_le h (by rw [hv, hUsz u hu])).symm.subset
        obtain ⟨y, hyu, hyv⟩ := not_subset.1 hnot
        have hmem : insert x (u.erase y) ∈ U :=
          hclosed _ (erase_mem_shadow hu hyu) x (fun h => hxu (mem_of_mem_erase h))
        have hlt : #(v \ insert x (u.erase y)) < k := by
          rw [← hk]
          calc #(v \ insert x (u.erase y)) ≤ #((v \ u).erase x) := card_le_card (by
                intro z hz
                simp only [mem_sdiff, mem_insert, mem_erase, not_or] at hz ⊢
                obtain ⟨hzv, hz1, hz2⟩ := hz
                exact ⟨hz1, hzv, fun hzu => hz2 ⟨fun hzy => hyv (hzy ▸ hzv), hzu⟩⟩)
            _ < #(v \ u) := card_erase_lt_of_mem (by simp [hxv, hxu])
        exact ih _ hlt (insert x (u.erase y)) hmem v hv rfl
  have hu0U : u0 ∈ U := (hmemU u0).2 ⟨hu0, hu0c⟩
  have hUfull : U = powersetCard (m + 1) univ := by
    ext v
    rw [mem_powersetCard]
    constructor
    · intro hv; exact ⟨subset_univ _, hUsz v hv⟩
    · rintro ⟨-, hv⟩
      exact hconn _ u0 hu0U v hv rfl
  have hUeqA : U = A := by
    apply eq_of_subset_of_card_le hUA
    rw [hcard, hUfull, card_powersetCard, card_univ, hn]
    exact (Nat.choose_symm_half m).ge
  rw [← hUeqA, hUfull]

/-- CO-329. Extremal families in Sperner's theorem: an antichain of subsets of an `n`-set with
as many members as the middle binomial coefficient consists of all `⌊n/2⌋`-subsets or of all
`⌈n/2⌉`-subsets. -/
@[kb "kellertrotter2017" "text, p. 343"]
theorem sperner_extremal (hA : IsAntichain (· ⊆ ·) (A : Set (Finset α)))
    (hcard : #A = (Fintype.card α).choose (Fintype.card α / 2)) :
    A = powersetCard (Fintype.card α / 2) univ ∨
      A = powersetCard ((Fintype.card α + 1) / 2) univ := by
  have hsz := sperner_extremal_sizes hA hcard
  by_cases h : ∀ s ∈ A, #s = Fintype.card α / 2
  · left
    apply eq_of_subset_of_card_le
    · intro s hs
      rw [mem_powersetCard]
      exact ⟨subset_univ _, h s hs⟩
    · rw [card_powersetCard, card_univ, hcard]
  · right
    push Not at h
    obtain ⟨s, hs, hne⟩ := h
    have hs2 := (hsz s hs).resolve_left hne
    have e : (Fintype.card α + 1) / 2 = Fintype.card α / 2 + 1 := by omega
    rw [e]
    exact odd_case (m := Fintype.card α / 2) (by omega) hA hcard
      (fun t ht => by have := hsz t ht; omega) hs (by omega)

omit [DecidableEq α] in
/-- CO-329 (converse). The two layers named in `sperner_extremal` are antichains of the extremal
size. -/
@[kb "kellertrotter2017" "text, p. 343"]
theorem powersetCard_middle_extremal {k : ℕ}
    (hk : k = Fintype.card α / 2 ∨ k = (Fintype.card α + 1) / 2) :
    IsAntichain (· ⊆ ·) ((powersetCard k (univ : Finset α) : Finset (Finset α)) : Set (Finset α))
      ∧ #(powersetCard k (univ : Finset α)) = (Fintype.card α).choose (Fintype.card α / 2) := by
  refine ⟨(Set.sized_powersetCard univ k).isAntichain, ?_⟩
  rw [card_powersetCard, card_univ]
  rcases hk with rfl | rfl
  · rfl
  · rw [← Nat.choose_symm (n := Fintype.card α) (k := (Fintype.card α + 1) / 2) (by omega)]
    congr 1
    omega

end Main

end UndergradKB.Combinatorics.Counting
