import Mathlib.Data.Fintype.BigOperators
import UndergradKB.Combinatorics.Flow.MaxFlowMinCut

/-!
# Bipartite matchings as flows (Keller–Trotter, Section 14.2)

For a bipartite graph with parts `A` and `B` (adjacency `r : A → B → Prop`) the book builds the network with a source
`S`, an edge `S → a` for every `a ∈ A`, an edge `a → b` whenever `a` and `b` are adjacent, an edge `b → T` for every
`b ∈ B` and a sink `T`, all capacities one. Integral flows of value `v` and matchings of size `v` correspond, so a
maximum matching is read off from an integral maximum flow (which exists by the integrality theorem).

Vertices: `Option (Option (A ⊕ B))`, with `none` the source, `some none` the sink, `some (some (inl a))` and
`some (some (inr b))` the two parts.
-/

namespace UndergradKB.Combinatorics.Flow

open Finset

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A matching in the bipartite graph `r`: a set of adjacent pairs, no two sharing an endpoint. -/
def IsMatching (r : A → B → Prop) (M : Finset (A × B)) : Prop :=
  (∀ p ∈ M, r p.1 p.2) ∧ (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧ (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q)

namespace MatchingNetwork

/-- The edges of the matching network. -/
def adj (r : A → B → Prop) : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → Prop
  | none, some (some (Sum.inl _)) => True
  | some (some (Sum.inl a)), some (some (Sum.inr b)) => r a b
  | some (some (Sum.inr _)), some none => True
  | _, _ => False

end MatchingNetwork

open MatchingNetwork Classical in
/-- CO-302. The matching network of a bipartite graph: source to every vertex of `A`, `a → b` for adjacent `a, b`, every
vertex of `B` to the sink, all capacities one. -/
@[kb "kellertrotter2017" "text (bipartite matching as a network flow), p. 305"]
noncomputable def matchingNetwork (r : A → B → Prop) : Network (Option (Option (A ⊕ B))) where
  adj := adj r
  oriented x y h := by
    rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;> simp_all [adj]
  source := none
  sink := some none
  source_ne_sink := by simp
  no_in_source x := by rcases x with _ | _ | _ | _ <;> simp [adj]
  no_out_sink y := by rcases y with _ | _ | _ | _ <;> simp [adj]
  cap x y := if adj r x y then 1 else 0
  cap_nonneg x y := by split_ifs <;> norm_num
  cap_of_not_adj x y h := by simp [h]

namespace MatchingNetwork

variable {r : A → B → Prop}

/-- The vertex of the network for `a ∈ A`. -/
abbrev L (a : A) : Option (Option (A ⊕ B)) := some (some (Sum.inl a))
/-- The vertex of the network for `b ∈ B`. -/
abbrev R (b : B) : Option (Option (A ⊕ B)) := some (some (Sum.inr b))

/-- The values of a flow on the non-edges of the matching network vanish. -/
lemma zeros {φ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ} (h0 : ∀ x y, ¬ adj r x y → φ x y = 0) :
    (∀ x, φ x none = 0) ∧ (∀ y, φ (some none) y = 0) ∧ (∀ a a', φ (L a) (L a') = 0) ∧
    (∀ b b', φ (R b) (R b') = 0) ∧ (∀ a b, φ (R b) (L a) = 0) ∧ (∀ a, φ (L a) (some none) = 0) ∧
    (∀ b, φ none (R b) = 0) ∧ φ none (some none) = 0 := by
  refine ⟨fun x => h0 _ _ ?_, fun y => h0 _ _ ?_, fun a a' => h0 _ _ ?_, fun b b' => h0 _ _ ?_,
    fun a b => h0 _ _ ?_, fun a => h0 _ _ ?_, fun b => h0 _ _ ?_, h0 _ _ ?_⟩ <;>
  first
  | (rcases x with _ | _ | _ | _ <;> simp [adj])
  | (rcases y with _ | _ | _ | _ <;> simp [adj])
  | simp [adj]

lemma netOut_L {φ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ}
    (h0 : ∀ x y, ¬ adj r x y → φ x y = 0) (a : A) :
    Network.netOut φ (L a) = ∑ b, φ (L a) (R b) - φ none (L a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := zeros h0
  simp [Network.netOut, Fintype.sum_option, Fintype.sum_sum_type, h1, h2, h3, h4, h5, h6, h7, h8]

lemma netOut_R {φ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ}
    (h0 : ∀ x y, ¬ adj r x y → φ x y = 0) (b : B) :
    Network.netOut φ (R b) = φ (R b) (some none) - ∑ a, φ (L a) (R b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := zeros h0
  simp [Network.netOut, Fintype.sum_option, Fintype.sum_sum_type, h1, h2, h3, h4, h5, h6, h7, h8]

lemma value_eq {φ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ}
    (h0 : ∀ x y, ¬ adj r x y → φ x y = 0) : (matchingNetwork r).value φ = ∑ a, φ none (L a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := zeros h0
  simp [Network.value, Network.netOut, matchingNetwork, Fintype.sum_option, Fintype.sum_sum_type, h1, h2, h3, h4,
    h5, h6, h7, h8]

open Classical in
/-- The flow of a matching: one unit along `S → a → b → T` for each matched pair `(a, b)`. -/
noncomputable def flowOf (M : Finset (A × B)) : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ
  | none, some (some (Sum.inl a)) => ∑ b, if (a, b) ∈ M then 1 else 0
  | some (some (Sum.inl a)), some (some (Sum.inr b)) => if (a, b) ∈ M then 1 else 0
  | some (some (Sum.inr b)), some none => ∑ a, if (a, b) ∈ M then 1 else 0
  | _, _ => 0

lemma sum_row_le_one {M : Finset (A × B)} (hM : IsMatching r M) (a : A) :
    (∑ b, if (a, b) ∈ M then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ b, (a, b) ∈ M
  · obtain ⟨b, hb⟩ := h
    rw [Finset.sum_eq_single b]
    · simp [hb]
    · intro b' _ hb'
      rw [ite_eq_right]
      intro hm
      exact hb' (congrArg Prod.snd (hM.2.1 _ hm _ hb rfl))
    · simp
  · push Not at h
    simp [h]

lemma sum_col_le_one {M : Finset (A × B)} (hM : IsMatching r M) (b : B) :
    (∑ a, if (a, b) ∈ M then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ a, (a, b) ∈ M
  · obtain ⟨a, ha⟩ := h
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro a' _ ha'
      rw [ite_eq_right]
      intro hm
      exact ha' (congrArg Prod.fst (hM.2.2 _ hm _ ha rfl))
    · simp
  · push Not at h
    simp [h]

lemma flowOf_int (M : Finset (A × B)) : ∀ x y, ∃ n : ℕ, flowOf M x y = n
  | none, none | none, some none | none, some (some (Sum.inr _)) => ⟨0, by simp [flowOf]⟩
  | none, some (some (Sum.inl a)) => ⟨∑ b, if (a, b) ∈ M then 1 else 0, by simp [flowOf]⟩
  | some none, none | some none, some none | some none, some (some _) => ⟨0, by simp [flowOf]⟩
  | some (some (Sum.inl _)), none | some (some (Sum.inl _)), some none
  | some (some (Sum.inl _)), some (some (Sum.inl _)) => ⟨0, by simp [flowOf]⟩
  | some (some (Sum.inl a)), some (some (Sum.inr b)) =>
    ⟨if (a, b) ∈ M then 1 else 0, by by_cases h : (a, b) ∈ M <;> simp [flowOf, h]⟩
  | some (some (Sum.inr _)), none | some (some (Sum.inr _)), some (some _) => ⟨0, by simp [flowOf]⟩
  | some (some (Sum.inr b)), some none => ⟨∑ a, if (a, b) ∈ M then 1 else 0, by simp [flowOf]⟩

/-- In a sum of nonnegative terms at most one, at most one term equals one. -/
lemma eq_of_sum_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hs : ∑ i, f i ≤ 1) (i j : ι) (hi : f i = 1) (hj : f j = 1) : i = j := by
  by_contra hij
  have : f i + f j ≤ ∑ k, f k := by
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hf k
  linarith

lemma flowOf_zero (M : Finset (A × B)) (hM : IsMatching r M) :
    ∀ x y, ¬ adj r x y → flowOf M x y = 0 := by
  intro x y h
  rcases x with _ | _ | a | b <;> rcases y with _ | _ | a' | b' <;> simp_all [adj, flowOf]
  intro hm
  exact h (hM.1 _ hm)

end MatchingNetwork

open MatchingNetwork

/-- CO-302 (one direction). A matching of size `k` gives an integral flow of value `k` in the matching network. -/
@[kb "kellertrotter2017" "text (bipartite matching as a network flow), p. 305"]
theorem exists_flow_of_matching {r : A → B → Prop} {M : Finset (A × B)} (hM : IsMatching r M) :
    ∃ φ, (matchingNetwork r).IsFlow φ ∧ (∀ x y, ∃ n : ℕ, φ x y = n) ∧ (matchingNetwork r).value φ = M.card := by
  classical
  have h0 := flowOf_zero M hM
  refine ⟨flowOf M, ⟨fun x y => ?_, fun x y => ?_, fun v hs ht => ?_⟩, fun x y => ?_, ?_⟩
  · rcases x with _ | _ | a | b <;> rcases y with _ | _ | a' | b' <;> simp only [flowOf, le_refl] <;>
      first | exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num | (split_ifs <;> norm_num)
  · by_cases hxy : adj r x y
    · have hc : (matchingNetwork r).cap x y = 1 := by simp [matchingNetwork, hxy]
      rw [hc]
      rcases x with _ | _ | a | b <;> rcases y with _ | _ | a' | b' <;> simp only [flowOf] <;>
        first | exact sum_row_le_one hM _ | exact sum_col_le_one hM _ | (split_ifs <;> norm_num) | norm_num
    · rw [h0 x y hxy]
      exact (matchingNetwork r).cap_nonneg x y
  · rcases v with _ | _ | a | b
    · exact absurd rfl hs
    · exact absurd rfl ht
    · rw [netOut_L h0]; exact sub_eq_zero.2 rfl
    · rw [netOut_R h0]; exact sub_eq_zero.2 rfl
  · exact flowOf_int M x y
  · rw [value_eq h0]
    simp only [flowOf]
    rw [← Fintype.sum_prod_type' (f := fun a b => if (a, b) ∈ M then (1 : ℝ) else 0)]
    simp

/-- CO-302 (other direction). An integral flow of value `v` in the matching network gives a matching of size `v`:
the edges `a → b` carrying flow. -/
@[kb "kellertrotter2017" "text (bipartite matching as a network flow), p. 305"]
theorem exists_matching_of_flow {r : A → B → Prop} {φ : Option (Option (A ⊕ B)) → Option (Option (A ⊕ B)) → ℝ}
    (hφ : (matchingNetwork r).IsFlow φ) (hint : ∀ x y, ∃ n : ℕ, φ x y = n) :
    ∃ M, IsMatching r M ∧ (M.card : ℝ) = (matchingNetwork r).value φ := by
  classical
  have h0 : ∀ x y, ¬ adj r x y → φ x y = 0 := fun x y h => hφ.eq_zero_of_not_adj h
  -- values on the middle edges are `0` or `1`
  have h01 : ∀ a b, φ (L a) (R b) = 0 ∨ φ (L a) (R b) = 1 := by
    intro a b
    obtain ⟨n, hn⟩ := hint (L a) (R b)
    have hle := hφ.le_cap (L a) (R b)
    have hc : (matchingNetwork r).cap (L a) (R b) ≤ 1 := by
      simp only [matchingNetwork]; split_ifs <;> norm_num
    rw [hn] at hle ⊢
    have : n ≤ 1 := by exact_mod_cast hle.trans hc
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with rfl | rfl <;> simp
  have hrow : ∀ a, ∑ b, φ (L a) (R b) = φ none (L a) := by
    intro a
    have := hφ.conserve (L a) (by simp [matchingNetwork]) (by simp [matchingNetwork])
    rw [netOut_L h0] at this
    linarith
  have hcol : ∀ b, ∑ a, φ (L a) (R b) = φ (R b) (some none) := by
    intro b
    have := hφ.conserve (R b) (by simp [matchingNetwork]) (by simp [matchingNetwork])
    rw [netOut_R h0] at this
    linarith
  have hcapS : ∀ a, φ none (L a) ≤ 1 := fun a => (hφ.le_cap _ _).trans (by
    simp only [matchingNetwork]; split_ifs <;> norm_num)
  have hcapT : ∀ b, φ (R b) (some none) ≤ 1 := fun b => (hφ.le_cap _ _).trans (by
    simp only [matchingNetwork]; split_ifs <;> norm_num)
  refine ⟨Finset.univ.filter fun p : A × B => φ (L p.1) (R p.2) = 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hr
    have := h0 (L p.1) (R p.2) (by simpa [adj] using hr)
    rw [this] at hp
    norm_num at hp
  · intro p hp q hq he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have := eq_of_sum_le_one (fun b => φ (L p.1) (R b)) (fun b => hφ.nonneg _ _) ((hrow p.1).le.trans (hcapS _)) p.2 q.2 hp
      (he ▸ hq)
    exact Prod.ext he this
  · intro p hp q hq he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have := eq_of_sum_le_one (fun a => φ (L a) (R p.2)) (fun a => hφ.nonneg _ _) ((hcol p.2).le.trans (hcapT _)) p.1 q.1 hp
      (he ▸ hq)
    exact Prod.ext this he
  · rw [value_eq h0, ← Finset.sum_congr rfl fun a _ => hrow a, ← Fintype.sum_prod_type']
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases h01 p.1 p.2 with h | h <;> simp [h]

/-- CO-302. **Maximum matchings are maximum flows.** In the matching network of a bipartite graph there is an integral
maximum flow, and the edges `a → b` carrying flow form a maximum matching, whose size is the maximum flow value. -/
@[kb "kellertrotter2017" "text (bipartite matching as a network flow), p. 305"]
theorem maxMatching_eq_maxFlow (r : A → B → Prop) :
    ∃ M φ, IsMatching r M ∧ (matchingNetwork r).IsFlow φ ∧ (M.card : ℝ) = (matchingNetwork r).value φ ∧
      (∀ ψ, (matchingNetwork r).IsFlow ψ → (matchingNetwork r).value ψ ≤ (matchingNetwork r).value φ) ∧
      ∀ M', IsMatching r M' → M'.card ≤ M.card := by
  classical
  obtain ⟨φ, hφ, hint, hmax⟩ := (matchingNetwork r).exists_integral_maxFlow (fun x y => by
    by_cases h : adj r x y
    · exact ⟨1, by simp [matchingNetwork, h]⟩
    · exact ⟨0, by simp [matchingNetwork, h]⟩)
  obtain ⟨M, hM, hcard⟩ := exists_matching_of_flow hφ hint
  refine ⟨M, φ, hM, hφ, hcard, hmax, fun M' hM' => ?_⟩
  obtain ⟨ψ, hψ, -, hv⟩ := exists_flow_of_matching hM'
  have := hmax ψ hψ
  rw [hv, ← hcard] at this
  exact_mod_cast this

end UndergradKB.Combinatorics.Flow
