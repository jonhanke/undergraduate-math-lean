import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Minimal
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SetFamily.LYM
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.Basic

/-!
# Dilworth's chain covering theorem

Source: Keller--Trotter, *Applied Combinatorics* (2017), Section 6.3.
The core is `dilworth_aux`: a finset `s` of a poset in which every antichain has at most `k`
points is covered by `k` chains, proved by the book's induction (remove a two-point chain
`{y ≤ x}` with `y` minimal and `x` maximal; either the width drops, or a maximum antichain `A`
splits the set into the proper pieces `D[A]` and `U[A]` which are glued along `A`).
-/

namespace UndergradKB.Combinatorics.Order

open Classical

variable {α : Type*} [PartialOrder α]

/-- `s` is covered by `k` chains: a labelling by numbers below `k` whose fibers inside `s` are
chains. -/
def ChainCover (s : Finset α) (k : ℕ) : Prop :=
  ∃ f : α → ℕ, (∀ x ∈ s, f x < k) ∧ ∀ i, IsChain (· ≤ ·) ((s : Set α) ∩ f ⁻¹' {i})

omit [PartialOrder α] in
theorem surj_of_injOn {A : Finset α} {k : ℕ} {f : α → ℕ} (hf : ∀ a ∈ A, f a < k)
    (hi : Set.InjOn f (A : Set α)) (hc : A.card = k) : ∀ i < k, ∃ a ∈ A, f a = i := by
  have h1 : A.image f = Finset.range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi'
      exact Finset.mem_range.2 (hf a ha)
    · rw [Finset.card_image_of_injOn hi, Finset.card_range, hc]
  intro i hi'
  have : i ∈ A.image f := by rw [h1]; exact Finset.mem_range.2 hi'
  obtain ⟨a, ha, h⟩ := Finset.mem_image.1 this
  exact ⟨a, ha, h⟩

omit [PartialOrder α] in
theorem exists_relabel {A : Finset α} {k : ℕ} {fD fU : α → ℕ}
    (hD : ∀ a ∈ A, fD a < k) (hU : ∀ a ∈ A, fU a < k)
    (iD : Set.InjOn fD (A : Set α)) (iU : Set.InjOn fU (A : Set α)) (hc : A.card = k) :
    ∃ σ : ℕ → ℕ, (∀ i < k, σ i < k) ∧ (∀ i < k, ∀ j < k, σ i = σ j → i = j) ∧
      (∀ a ∈ A, σ (fU a) = fD a) := by
  have sU := surj_of_injOn hU iU hc
  let σ : ℕ → ℕ := fun i => if h : ∃ a ∈ A, fU a = i then fD (Classical.choose h) else 0
  have h3 : ∀ a ∈ A, σ (fU a) = fD a := by
    intro a ha
    have h : ∃ a' ∈ A, fU a' = fU a := ⟨a, ha, rfl⟩
    have hs := Classical.choose_spec h
    have : Classical.choose h = a := iU hs.1 ha hs.2
    simp only [σ, h, dite_true, this]
  refine ⟨σ, ?_, ?_, h3⟩
  · intro i hi
    obtain ⟨a, ha, rfl⟩ := sU i hi
    rw [h3 a ha]; exact hD a ha
  · intro i hi j hj hij
    obtain ⟨a, ha, rfl⟩ := sU i hi
    obtain ⟨b, hb, rfl⟩ := sU j hj
    rw [h3 a ha, h3 b hb] at hij
    rw [iD ha hb hij]

theorem injOn_of_chainCover_fibers {s : Finset α} {f : α → ℕ}
    (hch : ∀ i, IsChain (· ≤ ·) ((s : Set α) ∩ f ⁻¹' {i})) {A : Finset α} (hA : A ⊆ s)
    (hAc : IsAntichain (· ≤ ·) (A : Set α)) : Set.InjOn f (A : Set α) := by
  intro x hx y hy hxy
  by_contra hne
  rcases hch (f x) ⟨hA hx, rfl⟩ ⟨hA hy, hxy.symm⟩ hne with h | h
  · exact hAc hx hy hne h
  · exact hAc hy hx (Ne.symm hne) h

theorem le_of_same_label {D A : Finset α} {fD : α → ℕ}
    (hch : ∀ i, IsChain (· ≤ ·) ((D : Set α) ∩ fD ⁻¹' {i}))
    (hAc : IsAntichain (· ≤ ·) (A : Set α)) (hdown : ∀ x ∈ D, ∃ b ∈ A, x ≤ b)
    {a x : α} (ha : a ∈ A) (haD : a ∈ D) (hx : x ∈ D) (hl : fD x = fD a) : x ≤ a := by
  by_cases hxa : x = a
  · exact hxa.le
  rcases hch (fD a) ⟨hx, hl⟩ ⟨haD, rfl⟩ hxa with h | h
  · exact h
  · obtain ⟨b, hb, hxb⟩ := hdown x hx
    by_cases hab : a = b
    · exact hab ▸ hxb
    · exact absurd (h.trans hxb) (hAc ha hb hab)

theorem le_of_same_label' {U A : Finset α} {fU : α → ℕ}
    (hch : ∀ i, IsChain (· ≤ ·) ((U : Set α) ∩ fU ⁻¹' {i}))
    (hAc : IsAntichain (· ≤ ·) (A : Set α)) (hup : ∀ x ∈ U, ∃ b ∈ A, b ≤ x)
    {a x : α} (ha : a ∈ A) (haU : a ∈ U) (hx : x ∈ U) (hl : fU x = fU a) : a ≤ x := by
  by_cases hxa : x = a
  · exact hxa.ge
  rcases hch (fU a) ⟨hx, hl⟩ ⟨haU, rfl⟩ hxa with h | h
  · obtain ⟨b, hb, hbx⟩ := hup x hx
    by_cases hab : b = a
    · exact hab ▸ hbx
    · exact absurd (hbx.trans h) (hAc hb ha hab)
  · exact h

/-- The induction behind Dilworth's theorem (CO-156): if every antichain contained in `s` has at
most `k` points then `s` is covered by `k` chains. -/
theorem dilworth_aux [Finite α] : ∀ (n k : ℕ) (s : Finset α), s.card = n →
    (∀ A ⊆ s, IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ k) → ChainCover s k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k s hn hb
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, by simp, fun i => by simp⟩
  obtain ⟨x, hx⟩ := Finset.exists_maximal hne
  obtain ⟨y, hy⟩ := exists_minimal_of_wellFoundedLT (fun z => z ∈ s ∧ z ≤ x) ⟨x, hx.1, le_rfl⟩
  have hk : 1 ≤ k := by
    have := hb {x} (by simpa using hx.1) (by simp)
    simpa using this
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s', hs'⟩ : ∃ s' : Finset α, ∀ z, z ∈ s' ↔ z ≠ y ∧ z ≠ x ∧ z ∈ s :=
    ⟨(s.erase x).erase y, by intro z; simp [Finset.mem_erase]⟩
  have hs'sub : s' ⊆ s := fun z hz => ((hs' z).1 hz).2.2
  have hxs' : x ∉ s' := fun h => ((hs' x).1 h).2.1 rfl
  have hys' : y ∉ s' := fun h => ((hs' y).1 h).1 rfl
  have hlt : s'.card < n := by
    rw [← hn]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hs'sub).2 ⟨x, hx.1, hxs'⟩)
  by_cases hcase : ∀ A ⊆ s', IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ k
  · -- the width drops: one extra chain `{y, x}`
    obtain ⟨f', hf'b, hf'c⟩ := ih _ hlt k s' rfl hcase
    refine ⟨fun z => if z ∈ s' then f' z else k, ?_, ?_⟩
    · intro z hz
      by_cases h : z ∈ s'
      · simp only [h, ite_true]; have := hf'b z h; omega
      · simp only [h, ite_false]; omega
    · intro i
      by_cases hik : i = k
      · subst hik
        have hmem : ∀ z, z ∈ (s : Set α) ∩ (fun z => if z ∈ s' then f' z else i) ⁻¹' {i} →
            z = x ∨ z = y := by
          rintro z ⟨hzs, hzi⟩
          have e : (if z ∈ s' then f' z else i) = i := hzi
          by_cases h : z ∈ s'
          · simp only [h, ite_true] at e
            have := hf'b z h; omega
          · by_contra hc
            push Not at hc
            exact h ((hs' z).2 ⟨hc.2, hc.1, hzs⟩)
        have hyx : y ≤ x := hy.1.2
        intro z1 hz1 z2 hz2 hne
        rcases hmem z1 hz1 with rfl | rfl <;> rcases hmem z2 hz2 with rfl | rfl
        · exact absurd rfl hne
        · exact Or.inr hyx
        · exact Or.inl hyx
        · exact absurd rfl hne
      · refine (hf'c i).mono ?_
        rintro z ⟨hzs, hzi⟩
        have e : (if z ∈ s' then f' z else k) = i := hzi
        by_cases h : z ∈ s'
        · simp only [h, ite_true] at e
          exact ⟨Finset.mem_coe.2 h, e⟩
        · simp only [h, ite_false] at e
          exact absurd e.symm hik
  · -- a antichain `A` of size `k + 1` avoiding `x` and `y`: split along `A`
    push Not at hcase
    obtain ⟨A, hAs', hAc, hAcard⟩ := hcase
    have hAs : A ⊆ s := hAs'.trans hs'sub
    have hAcard' : A.card = k + 1 := le_antisymm (hb A hAs hAc) hAcard
    let D : Finset α := s.filter fun z => ∃ a ∈ A, z ≤ a
    let U : Finset α := s.filter fun z => ∃ a ∈ A, a ≤ z
    have hDm : ∀ z, z ∈ D ↔ z ∈ s ∧ ∃ a ∈ A, z ≤ a := fun z => Finset.mem_filter
    have hUm : ∀ z, z ∈ U ↔ z ∈ s ∧ ∃ a ∈ A, a ≤ z := fun z => Finset.mem_filter
    have hcover : ∀ z ∈ s, z ∈ D ∨ z ∈ U := by
      intro z hz
      by_contra hcon
      simp only [not_or, hDm, hUm, hz, true_and, not_exists, not_and] at hcon
      obtain ⟨hd, hu⟩ := hcon
      have hzA : z ∉ A := fun h => hd z h le_rfl
      have hanti : IsAntichain (· ≤ ·) ((insert z A : Finset α) : Set α) := by
        rw [Finset.coe_insert]
        exact isAntichain_insert.2 ⟨hAc, fun b hb hne => ⟨hd b hb, hu b hb⟩⟩
      have := hb (insert z A) (Finset.insert_subset hz hAs) hanti
      rw [Finset.card_insert_of_notMem hzA] at this
      omega
    have hxD : x ∉ D := by
      intro h
      obtain ⟨_, a, ha, hxa⟩ := (hDm x).1 h
      have : a = x := le_antisymm (hx.2 (hAs ha) hxa) hxa
      exact hxs' (this ▸ hAs' ha)
    have hyU : y ∉ U := by
      intro h
      obtain ⟨_, a, ha, hay⟩ := (hUm y).1 h
      have : y ≤ a := hy.2 ⟨hAs ha, hay.trans hy.1.2⟩ hay
      exact hys' ((le_antisymm hay this) ▸ hAs' ha)
    have hDlt : D.card < n := by
      rw [← hn]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
        ⟨x, hx.1, hxD⟩)
    have hUlt : U.card < n := by
      rw [← hn]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
        ⟨y, hy.1.1, hyU⟩)
    obtain ⟨fD, hfDb, hfDc⟩ := ih _ hDlt (k + 1) D rfl
      (fun B hB hBc => hb B (hB.trans (Finset.filter_subset _ _)) hBc)
    obtain ⟨fU, hfUb, hfUc⟩ := ih _ hUlt (k + 1) U rfl
      (fun B hB hBc => hb B (hB.trans (Finset.filter_subset _ _)) hBc)
    have hAD : A ⊆ D := fun a ha => (hDm a).2 ⟨hAs ha, a, ha, le_rfl⟩
    have hAU : A ⊆ U := fun a ha => (hUm a).2 ⟨hAs ha, a, ha, le_rfl⟩
    have iD := injOn_of_chainCover_fibers hfDc hAD hAc
    have iU := injOn_of_chainCover_fibers hfUc hAU hAc
    obtain ⟨σ, hσb, hσi, hσa⟩ := exists_relabel (fun a ha => hfDb a (hAD ha))
      (fun a ha => hfUb a (hAU ha)) iD iU hAcard'
    have sD := surj_of_injOn (fun a ha => hfDb a (hAD ha)) iD hAcard'
    have hdown : ∀ z ∈ D, ∃ b ∈ A, z ≤ b := fun z hz => ((hDm z).1 hz).2
    have hup : ∀ z ∈ U, ∃ b ∈ A, b ≤ z := fun z hz => ((hUm z).1 hz).2
    refine ⟨fun z => if z ∈ D then fD z else σ (fU z), ?_, ?_⟩
    · intro z hz
      by_cases h : z ∈ D
      · simp only [h, ite_true]; exact hfDb z h
      · simp only [h, ite_false]
        exact hσb _ (hfUb z ((hcover z hz).resolve_left h))
    · intro i
      by_cases hi : i < k + 1
      swap
      · intro z hz
        exfalso
        obtain ⟨hzs, hzi⟩ := hz
        have e : (if z ∈ D then fD z else σ (fU z)) = i := hzi
        by_cases h : z ∈ D
        · simp only [h, ite_true] at e; have := hfDb z h; omega
        · simp only [h, ite_false] at e
          have := hσb _ (hfUb z ((hcover z hzs).resolve_left h)); omega
      obtain ⟨a, haA, hfa⟩ := sD i hi
      have haD := hAD haA
      have haU := hAU haA
      have hσa' := hσa a haA
      have key : ∀ z, z ∈ (s : Set α) ∩ (fun z => if z ∈ D then fD z else σ (fU z)) ⁻¹' {i} →
          (z ∈ D ∧ fD z = fD a ∧ z ≤ a) ∨ (z ∉ D ∧ z ∈ U ∧ fU z = fU a ∧ a ≤ z) := by
        rintro z ⟨hzs, hzi⟩
        have e : (if z ∈ D then fD z else σ (fU z)) = i := hzi
        by_cases hzD : z ∈ D
        · simp only [hzD, ite_true] at e
          have hl : fD z = fD a := e.trans hfa.symm
          exact Or.inl ⟨hzD, hl, le_of_same_label hfDc hAc hdown haA haD hzD hl⟩
        · simp only [hzD, ite_false] at e
          have hzU : z ∈ U := (hcover z hzs).resolve_left hzD
          have hl : fU z = fU a :=
            hσi _ (hfUb z hzU) _ (hfUb a haU) (e.trans (hfa.symm.trans hσa'.symm))
          exact Or.inr ⟨hzD, hzU, hl, le_of_same_label' hfUc hAc hup haA haU hzU hl⟩
      intro z1 hz1 z2 hz2 hne
      rcases key z1 hz1 with ⟨d1, f1, l1⟩ | ⟨d1, u1, f1, g1⟩ <;>
        rcases key z2 hz2 with ⟨d2, f2, l2⟩ | ⟨d2, u2, f2, g2⟩
      · exact hfDc (fD a) ⟨Finset.mem_coe.2 d1, f1⟩ ⟨Finset.mem_coe.2 d2, f2⟩ hne
      · exact Or.inl (l1.trans g2)
      · exact Or.inr (l2.trans g1)
      · exact hfUc (fU a) ⟨Finset.mem_coe.2 u1, f1⟩ ⟨Finset.mem_coe.2 u2, f2⟩ hne

/-- A map from an antichain to the pieces of a chain partition is injective. -/
theorem injOn_of_chain_fibers {ι : Type*} {g : α → ι}
    (hg : ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) {s : Set α} (hs : IsAntichain (· ≤ ·) s) :
    Set.InjOn g s := by
  intro x hx y hy hxy
  by_contra hne
  rcases hg (g x) (show x ∈ g ⁻¹' {g x} from rfl) (show y ∈ g ⁻¹' {g x} from hxy.symm) hne
    with h | h
  · exact hs hx hy hne h
  · exact hs hy hx (Ne.symm hne) h

variable [Fintype α]

/-- CO-156. Dilworth's theorem, covering part: a finite poset of width `w` is partitioned into
`w` chains. -/
@[kb "kellertrotter2017" "Theorem 6.17, p. 146"]
theorem dilworth_exists_partition :
    ∃ f : α → Fin (width α), ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i}) := by
  obtain ⟨f, hb, hc⟩ := dilworth_aux _ (width α) Finset.univ rfl
    (fun A _ hA => card_le_width hA)
  refine ⟨fun x => ⟨f x, hb x (Finset.mem_univ x)⟩, fun i => (hc i.val).mono ?_⟩
  intro z hz
  exact ⟨Finset.mem_coe.2 (Finset.mem_univ z), congrArg Fin.val hz⟩

/-- CO-156. Dilworth's theorem, optimality part: no chain partition into fewer than `width`
chains. -/
@[kb "kellertrotter2017" "Theorem 6.17, p. 146"]
theorem width_le_card_of_chain_partition {ι : Type*} [Fintype ι] (g : α → ι)
    (hg : ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) : width α ≤ Fintype.card ι := by
  obtain ⟨s, hs, hcard⟩ := exists_antichain_card_eq_width (α := α)
  rw [← hcard]
  calc s.card ≤ (Finset.univ : Finset ι).card :=
        Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _)
          (injOn_of_chain_fibers hg hs)
    _ = Fintype.card ι := Finset.card_univ

/-- CO-156, book-shaped. **Dilworth's theorem**: a poset of width `w` is the union of `w`
chains, and no partition into fewer chains exists. -/
@[kb "kellertrotter2017" "Theorem 6.17, p. 146"]
theorem dilworth :
    (∃ f : α → Fin (width α), ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) ∧
    ∀ (n : ℕ) (g : α → Fin n), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) → width α ≤ n := by
  refine ⟨dilworth_exists_partition, fun n g hg => ?_⟩
  simpa using width_le_card_of_chain_partition g hg

/-- CO-166. The width of the subset lattice `2^t` (here `Finset β` with `t = |β|`) is
`C(t, ⌊t/2⌋)`: Sperner's theorem for `≤`, the middle layer for `≥`. -/
@[kb "kellertrotter2017" "Theorem 6.27, p. 151"]
theorem width_finset (β : Type*) [DecidableEq β] [Fintype β] :
    width (Finset β) = (Fintype.card β).choose (Fintype.card β / 2) := by
  apply le_antisymm
  · obtain ⟨s, hs, hcard⟩ := exists_antichain_card_eq_width (α := Finset β)
    rw [← hcard]
    exact IsAntichain.sperner hs
  · have h := card_le_width (α := Finset β)
      (s := Finset.powersetCard (Fintype.card β / 2) (Finset.univ : Finset β))
      (Set.Sized.isAntichain (Set.sized_powersetCard _ _))
    rwa [Finset.card_powersetCard, Finset.card_univ] at h

end UndergradKB.Combinatorics.Order
