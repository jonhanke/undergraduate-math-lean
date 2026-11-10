import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.Basic
import UndergradKB.Combinatorics.Order.FlowChains
import UndergradKB.Combinatorics.Flow.MaxFlowMinCut
import UndergradKB.Combinatorics.Flow.Matching

/-!
# Reading a maximum antichain off a maximum flow (Keller--Trotter, Section 14.3)

Let `φ` be a maximum flow in the chain-partition network and let `Λ` be the set of labelled
vertices at the end of the labelling algorithm (the vertices reachable from the source by residual
steps; the sink is not among them).  The antichain is
`A = {x | x' ∈ Λ and x'' ∉ Λ}`.

The book takes, on each chain of the chain partition built from the flow edges, the first element
`y` with `y'` labelled and `y''` unlabelled, and shows that these elements form an antichain with
one element per chain.  Here the antichain is described at the level of the whole poset (all `x`
with `x'` labelled and `x''` unlabelled); we prove that it is an antichain and has exactly
`|P| - value φ` elements, i.e. as many as the chain partition has chains.  Hence the antichain is
maximum and the chain partition minimum.
-/

namespace UndergradKB.Combinatorics.Order

open UndergradKB.Combinatorics.Flow
open UndergradKB.Combinatorics.Flow.MatchingNetwork (L R)

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

section Labelling

variable {φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ}

private lemma adj_LR {x y : α} : (chainNetwork α).adj (L x) (R y) ↔ x < y := by
  rw [chainNetwork_adj_iff]
  simp [L, R]

private lemma flow_h0 (hφ : (chainNetwork α).IsFlow φ) :
    ∀ x y, ¬ MatchingNetwork.adj (fun x y : α => x < y) x y → φ x y = 0 :=
  fun x y h => hφ.eq_zero_of_not_adj h

private lemma row_sum (hφ : (chainNetwork α).IsFlow φ) (x : α) :
    ∑ b, φ (L x) (R b) = φ none (L x) := by
  have h0 := flow_h0 hφ
  have := hφ.conserve (L x) (by simp [chainNetwork, matchingNetwork, L])
    (by simp [chainNetwork, matchingNetwork, L])
  rw [MatchingNetwork.netOut_L h0] at this
  linarith

private lemma phi_le_one (hφ : (chainNetwork α).IsFlow φ) (u w) : φ u w ≤ 1 := by
  refine (hφ.le_cap u w).trans ?_
  by_cases h : (chainNetwork α).adj u w
  · exact (chainNetwork_cap u w h).le
  · rw [(chainNetwork α).cap_of_not_adj u w h]; norm_num

private lemma phi_zero_or_one (hφ : (chainNetwork α).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n)
    (u w) : φ u w = 0 ∨ φ u w = 1 := by
  obtain ⟨n, hn⟩ := hint u w
  have h1 := phi_le_one hφ u w
  rw [hn] at h1 ⊢
  have : n ≤ 1 := by exact_mod_cast h1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with rfl | rfl <;> simp

private lemma labelled_step {u w : Option (Option (α ⊕ α))}
    (hu : u ∈ (chainNetwork α).labelled φ) (h : (chainNetwork α).Residual φ u w) :
    w ∈ (chainNetwork α).labelled φ :=
  Network.mem_labelled.2 ((Network.mem_labelled.1 hu).tail h)

private lemma source_labelled : (none : Option (Option (α ⊕ α))) ∈ (chainNetwork α).labelled φ :=
  Network.mem_labelled.2 Relation.ReflTransGen.refl

/-- If `x < y` and `x'` is labelled then `y''` is labelled (in a flow of the chain network with the
sink unlabelled, integral). -/
private lemma mid_labelled (hφ : (chainNetwork α).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n)
    {x y : α} (hxy : x < y) (hx : L x ∈ (chainNetwork α).labelled φ) :
    R y ∈ (chainNetwork α).labelled φ := by
  by_contra hy
  have hadj : (chainNetwork α).adj (L x) (R y) := adj_LR.2 hxy
  have h1 : φ (L x) (R y) = 1 := by
    rcases phi_zero_or_one hφ hint (L x) (R y) with h | h
    · exfalso; apply hy
      refine labelled_step hx (Or.inl ⟨hadj, ?_⟩)
      rw [h, chainNetwork_cap _ _ hadj]; norm_num
    · exact h
  have hrow := row_sum hφ x
  have hS := phi_le_one hφ none (L x)
  have hge : φ (L x) (R y) ≤ ∑ b, φ (L x) (R b) :=
    Finset.single_le_sum (f := fun b => φ (L x) (R b)) (fun b _ => hφ.nonneg _ _)
      (Finset.mem_univ y)
  have hx' := Network.mem_labelled.1 hx
  rcases Relation.ReflTransGen.cases_tail hx' with h | ⟨p, hp, hres⟩
  · exact absurd h (by simp [chainNetwork, matchingNetwork, L])
  · rcases (show _ ∨ _ from hres) with ⟨hpa, hlt⟩ | ⟨hpa, hpos⟩
    · rw [chainNetwork_adj_iff] at hpa
      rcases hpa with ⟨rfl, -⟩ | ⟨a, b, -, rfl, h⟩ | ⟨-, h⟩
      · rw [chainNetwork_cap _ _ ((chainNetwork_adj_iff _ _).2 (Or.inl ⟨rfl, x, rfl⟩))] at hlt
        linarith
      · simp [L, R] at h
      · simp [L] at h
    · rw [chainNetwork_adj_iff] at hpa
      rcases hpa with ⟨h, -⟩ | ⟨a, b, -, h1', rfl⟩ | ⟨⟨a, h⟩, -⟩
      · simp [L] at h
      · have hax : a = x := by simpa [L] using h1'.symm
        subst hax
        have h2 : φ (L a) (R b) = 1 := by
          rcases phi_zero_or_one hφ hint (L a) (R b) with h | h
          · rw [h] at hpos; exact absurd hpos (lt_irrefl _)
          · exact h
        have hby : b = y := MatchingNetwork.eq_of_sum_le_one (fun b => φ (L a) (R b))
          (fun b => hφ.nonneg _ _) (hrow.le.trans hS) b y h2 h1
        subst hby
        exact hy (Network.mem_labelled.2 hp)
      · simp [L] at h

/-- If `x''` is labelled then `x'` is labelled. -/
private lemma left_labelled (hφ : (chainNetwork α).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n)
    (ht : (chainNetwork α).sink ∉ (chainNetwork α).labelled φ) {x : α}
    (hx : R x ∈ (chainNetwork α).labelled φ) : L x ∈ (chainNetwork α).labelled φ := by
  by_contra hLx
  have hadjS : (chainNetwork α).adj none (L x) := (chainNetwork_adj_iff _ _).2 (Or.inl ⟨rfl, x, rfl⟩)
  have hS : φ none (L x) = 1 := by
    rcases phi_zero_or_one hφ hint none (L x) with h | h
    · exfalso; apply hLx
      refine labelled_step source_labelled (Or.inl ⟨hadjS, ?_⟩)
      rw [h, chainNetwork_cap _ _ hadjS]; norm_num
    · exact h
  have hrow := row_sum hφ x
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun b => φ (L x) (R b)) (by rw [hrow, hS]; norm_num)
  have hy1 : φ (L x) (R y) = 1 := by
    rcases phi_zero_or_one hφ hint (L x) (R y) with h | h
    · exact absurd h hy
    · exact h
  have hxy : x < y := by
    by_contra hn
    exact absurd (hφ.eq_zero_of_not_adj (fun h => hn (adj_LR.1 h))) (by rw [hy1]; norm_num)
  have hRy : R y ∉ (chainNetwork α).labelled φ := by
    intro h
    refine hLx (labelled_step h (Or.inr ⟨adj_LR.2 hxy, ?_⟩))
    rw [hy1]; norm_num
  have hx' := Network.mem_labelled.1 hx
  rcases Relation.ReflTransGen.cases_tail hx' with h | ⟨p, hp, hres⟩
  · exact absurd h (by simp [chainNetwork, matchingNetwork, R])
  · rcases (show _ ∨ _ from hres) with ⟨hpa, -⟩ | ⟨hpa, -⟩
    · rw [chainNetwork_adj_iff] at hpa
      rcases hpa with ⟨-, a, h⟩ | ⟨a, b, hab, rfl, h⟩ | ⟨-, h⟩
      · simp [R] at h
      · have : b = x := by simpa [R] using h.symm
        subst this
        exact hRy (mid_labelled hφ hint (hab.trans hxy) (Network.mem_labelled.2 hp))
      · simp [R] at h
    · rw [chainNetwork_adj_iff] at hpa
      rcases hpa with ⟨h, -⟩ | ⟨a, b, -, h, -⟩ | ⟨-, rfl⟩
      · simp [R] at h
      · simp [R, L] at h
      · exact ht (Network.mem_labelled.2 hp)

open Classical in
private lemma cap_eq (u w : Option (Option (α ⊕ α))) :
    (chainNetwork α).cap u w = if (chainNetwork α).adj u w then 1 else 0 := by
  by_cases h : (chainNetwork α).adj u w
  · simp [h, chainNetwork_cap u w h]
  · simp [h, (chainNetwork α).cap_of_not_adj u w h]

open Classical in
private lemma capacity_labelled_count (hφ : (chainNetwork α).IsFlow φ)
    (hint : ∀ x y, ∃ n : ℕ, φ x y = n)
    (ht : (chainNetwork α).sink ∉ (chainNetwork α).labelled φ) :
    (chainNetwork α).capacity ((chainNetwork α).labelled φ) =
      ((Finset.univ.filter fun x : α => L x ∉ (chainNetwork α).labelled φ).card : ℝ) +
        (Finset.univ.filter fun x : α => R x ∈ (chainNetwork α).labelled φ).card := by
  set Λ := (chainNetwork α).labelled φ with hΛ
  have e : (chainNetwork α).capacity Λ = ∑ u, ∑ w,
      if u ∈ Λ then (if w ∈ Λᶜ then (chainNetwork α).cap u w else 0) else 0 := by
    unfold Network.capacity
    rw [← Finset.univ_inter Λ, ← Finset.sum_ite_mem, Finset.univ_inter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs
    · rw [← Finset.univ_inter Λᶜ, ← Finset.sum_ite_mem, Finset.univ_inter]
    · simp_all
  have hmid : ∀ x y : α, L x ∈ Λ → x < y → R y ∈ Λ := fun x y h1 h2 => mid_labelled hφ hint h2 h1
  have hs : (none : Option (Option (α ⊕ α))) ∈ Λ := source_labelled
  have ht' : (some none : Option (Option (α ⊕ α))) ∉ Λ := ht
  obtain ⟨F, hF⟩ : ∃ F : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ, F = fun u w =>
      if u ∈ Λ then (if w ∈ Λᶜ then (chainNetwork α).cap u w else 0) else 0 := ⟨_, rfl⟩
  have e' : (chainNetwork α).capacity Λ = ∑ u, ∑ w, F u w := by rw [e, hF]
  rw [e']
  have F1 : ∀ x, F none (L x) = if L x ∉ Λ then 1 else 0 := by
    intro x
    have : (chainNetwork α).cap none (L x) = 1 :=
      chainNetwork_cap _ _ ((chainNetwork_adj_iff _ _).2 (Or.inl ⟨rfl, x, rfl⟩))
    simp [hF, hs, this]
  have F2 : ∀ x, F (R x) (some none) = if R x ∈ Λ then 1 else 0 := by
    intro x
    have : (chainNetwork α).cap (R x) (some none) = 1 :=
      chainNetwork_cap _ _ ((chainNetwork_adj_iff _ _).2 (Or.inr (Or.inr ⟨⟨x, rfl⟩, rfl⟩)))
    simp [hF, ht', this]
  have F3 : ∀ w, F (some none) w = 0 := by
    intro w; simp [hF, ht']
  have F4 : ∀ w, (∀ x, w ≠ L x) → F none w = 0 := by
    intro w hw
    have : (chainNetwork α).cap none w = 0 := by
      rw [cap_eq]
      have : ¬ (chainNetwork α).adj none w := by
        rw [chainNetwork_adj_iff]
        rintro (⟨-, x, h⟩ | ⟨x, y, -, h, -⟩ | ⟨⟨y, h⟩, -⟩)
        · exact hw x h
        · simp at h
        · simp at h
      simp [this]
    simp [hF, this]
  have F5 : ∀ x w, ¬ (∃ y, w = R y ∧ x < y) → F (L x) w = 0 := by
    intro x w h3
    have : (chainNetwork α).cap (L x) w = 0 := by
      rw [cap_eq]
      have : ¬ (chainNetwork α).adj (L x) w := by
        rw [chainNetwork_adj_iff]
        rintro (⟨h, -⟩ | ⟨a, b, hab, h, h'⟩ | ⟨⟨y, h⟩, -⟩)
        · simp [L] at h
        · have : a = x := by simpa [L] using h.symm
          subst this
          exact h3 ⟨b, h', hab⟩
        · simp [L, R] at h
      simp [this]
    simp [hF, this]
  have F6 : ∀ x y, F (L x) (R y) = 0 := by
    intro x y
    by_cases h1 : L x ∈ Λ
    · by_cases h2 : x < y
      · simp [hF, hmid x y h1 h2]
      · have : (chainNetwork α).cap (L x) (R y) = 0 := by
          rw [(chainNetwork α).cap_of_not_adj]
          exact fun h => h2 (adj_LR.1 h)
        simp [hF, this]
    · simp [hF, h1]
  have F7 : ∀ x w, w ≠ some none → F (R x) w = 0 := by
    intro x w h1
    have : (chainNetwork α).cap (R x) w = 0 := by
      rw [(chainNetwork α).cap_of_not_adj]
      rw [chainNetwork_adj_iff]
      rintro (⟨h, -⟩ | ⟨a, b, -, h, -⟩ | ⟨-, h⟩)
      · simp [R] at h
      · simp [R, L] at h
      · exact h1 h
    simp [hF, this]
  simp only [Fintype.sum_option, Fintype.sum_sum_type]
  have G1 : F none none = 0 := F4 _ (by simp [L])
  have G2 : F none (some none) = 0 := F4 _ (by simp [L])
  have G3 : ∀ y, F none (R y) = 0 := fun y => F4 _ (by simp [L, R])
  have G4 : ∀ x, F (L x) none = 0 := fun x => F5 x _ (by simp [R])
  have G5 : ∀ x, F (L x) (some none) = 0 := fun x => F5 x _ (by simp [R])
  have G6 : ∀ x y, F (L x) (L y) = 0 := fun x y => F5 x _ (by simp [R, L])
  have G7 : ∀ x, F (R x) none = 0 := fun x => F7 x _ (by simp)
  have G8 : ∀ x y, F (R x) (L y) = 0 := fun x y => F7 x _ (by simp [L])
  have G9 : ∀ x y, F (R x) (R y) = 0 := fun x y => F7 x _ (by simp [R])
  simp [F1, F2, F3, F6, G1, G2, G3, G4, G5, G6, G7, G8, G9]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : L x ∈ Λ <;> simp [h]

end Labelling

open Classical in
/-- CO-307. The antichain read off the labelling of a flow `φ` of the chain-partition network:
the points `x` whose left copy `x'` is labelled (reachable from the source by residual steps) while
the right copy `x''` is not. -/
@[kb "kellertrotter2017" "text (antichain from the final labelling), p. 311"]
noncomputable def labelAntichain
    (φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ) : Finset α :=
  Finset.univ.filter fun x =>
    L x ∈ (chainNetwork α).labelled φ ∧ R x ∉ (chainNetwork α).labelled φ

/-- CO-307. For an integral flow of the chain-partition network, the points with `x'` labelled and
`x''` unlabelled form an antichain: if `x < y` then the scan from `x'` labels `y''`. -/
@[kb "kellertrotter2017" "text (antichain from the final labelling), p. 311"]
theorem labelAntichain_isAntichain {φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ}
    (hφ : (chainNetwork α).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n) :
    IsAntichain (· ≤ ·) (labelAntichain φ : Set α) := by
  intro x hx y hy hne hle
  have hx' := (Finset.mem_filter.1 hx).2
  have hy' := (Finset.mem_filter.1 hy).2
  exact hy'.2 (mid_labelled hφ hint (lt_of_le_of_ne hle hne) hx'.1)

open Classical in
/-- CO-307. When the sink is unlabelled (i.e. `φ` is a maximum flow), the labelling antichain has
`|P| - value φ` elements, exactly the number of chains of the chain partition built from `φ`. -/
@[kb "kellertrotter2017" "text (antichain from the final labelling), p. 311"]
theorem card_labelAntichain {φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ}
    (hφ : (chainNetwork α).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n)
    (ht : (chainNetwork α).sink ∉ (chainNetwork α).labelled φ) :
    ((labelAntichain φ).card : ℝ) = Fintype.card α - (chainNetwork α).value φ := by
  set Λ := (chainNetwork α).labelled φ with hΛ
  have hcount := capacity_labelled_count hφ hint ht
  rw [Network.capacity_labelled_eq_value hφ ht] at hcount
  rw [hcount]
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
    (fun x : α => L x ∈ Λ)
  rw [Finset.card_univ] at h1
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun x : α => L x ∈ Λ) (fun x : α => R x ∈ Λ)
  have h3 : (Finset.univ.filter fun x : α => L x ∈ Λ).filter (fun x : α => R x ∈ Λ) =
      Finset.univ.filter fun x : α => R x ∈ Λ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    exact left_labelled hφ hint ht
  have h4 : (Finset.univ.filter fun x : α => L x ∈ Λ).filter (fun x : α => ¬ R x ∈ Λ) =
      labelAntichain φ := by
    ext x
    simp only [labelAntichain, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [h3, h4] at h2
  have h5 : (Finset.univ.filter fun x : α => ¬ L x ∈ Λ) = Finset.univ.filter fun x : α => L x ∉ Λ :=
    rfl
  rw [h5] at h1
  have : (labelAntichain φ).card + (Finset.univ.filter fun x : α => L x ∉ Λ).card +
      (Finset.univ.filter fun x : α => R x ∈ Λ).card - (Finset.univ.filter fun x : α => R x ∈ Λ).card
      + (Finset.univ.filter fun x : α => R x ∈ Λ).card = Fintype.card α := by omega
  have h6 : (labelAntichain φ).card + (Finset.univ.filter fun x : α => R x ∈ Λ).card +
      (Finset.univ.filter fun x : α => L x ∉ Λ).card = Fintype.card α := by omega
  have h7 : ((labelAntichain φ).card : ℝ) + (Finset.univ.filter fun x : α => R x ∈ Λ).card +
      (Finset.univ.filter fun x : α => L x ∉ Λ).card = Fintype.card α := by exact_mod_cast h6
  linarith

/-- CO-306/CO-307. **The chain-partition algorithm.** In the chain-partition network of a finite
poset take an integral maximum flow `φ` of value `v` (it exists).  Then the flow edges give a
partition of the poset into `|P| - v` chains, and the points with `x'` labelled, `x''` unlabelled
at the end of the labelling algorithm form an antichain with `|P| - v` elements.  Consequently the
antichain is a maximum antichain, the chain partition is a minimum chain partition, and
`width P = |P| - v` (Dilworth's theorem). -/
@[kb "kellertrotter2017" "text (chain partitioning algorithm), p. 311"]
theorem exists_maxFlow_chains_and_antichain :
    ∃ (φ : Option (Option (α ⊕ α)) → Option (Option (α ⊕ α)) → ℝ) (v : ℕ),
      (chainNetwork α).IsFlow φ ∧ (∀ x y, ∃ n : ℕ, φ x y = n) ∧
      (chainNetwork α).value φ = v ∧
      (∀ ψ, (chainNetwork α).IsFlow ψ → (chainNetwork α).value ψ ≤ v) ∧
      (∃ g : α → Fin (Fintype.card α - v), ∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) ∧
      IsAntichain (· ≤ ·) (labelAntichain φ : Set α) ∧
      (labelAntichain φ).card = Fintype.card α - v ∧ width α = Fintype.card α - v := by
  obtain ⟨φ, hφ, hint, hmax⟩ := (chainNetwork α).exists_integral_maxFlow (fun x y => by
    classical
    by_cases h : (chainNetwork α).adj x y
    · exact ⟨1, by simp [chainNetwork_cap x y h]⟩
    · exact ⟨0, by simp [(chainNetwork α).cap_of_not_adj x y h]⟩)
  obtain ⟨M, hM, hcard⟩ := exists_matching_of_flow (r := fun x y : α => x < y) hφ hint
  have hv : (chainNetwork α).value φ = (M.card : ℝ) := hcard.symm
  have ht := (Network.isMax_iff_sink_not_labelled hφ).1 hmax
  have hA := card_labelAntichain hφ hint ht
  rw [hv] at hA
  have hAn : (labelAntichain φ).card = Fintype.card α - M.card := by
    have hle : M.card ≤ Fintype.card α := card_matching_le M hM
    have : ((labelAntichain φ).card : ℝ) = ((Fintype.card α - M.card : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]; exact hA
    exact_mod_cast this
  obtain ⟨g, hg⟩ := chain_partition_of_matching hM
  have hanti := labelAntichain_isAntichain hφ hint
  have hw1 : Fintype.card α - M.card ≤ width α := hAn ▸ card_le_width hanti
  have hw2 : width α ≤ Fintype.card α - M.card := by
    simpa using width_le_card_of_chain_partition g hg
  refine ⟨φ, M.card, hφ, hint, hv, fun ψ hψ => ?_, ⟨g, hg⟩, hanti, hAn, le_antisymm hw2 hw1⟩
  rw [← hv]; exact hmax ψ hψ

end UndergradKB.Combinatorics.Order
