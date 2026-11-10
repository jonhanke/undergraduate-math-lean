import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import UndergradKB.Combinatorics.Flow.Matching
import UndergradKB.Combinatorics.Order.Dominance
import UndergradKB.Common.Attr

/-!
# The Gale–Ryser theorem (Keller–Trotter, Section 16.5)

A zero-one matrix `M : ι → κ → Bool` has row sum string `rowSum M` and column sum string `colSum M`.  The question is
which pairs `(R, C)` of strings are realised.

**Proof method.**  This is *not* the book's proof (a chain of covers in the dominance order, Proposition 16.11 and the
construction on p. 349); instead we use the network-flow library of Chapters 13 and 14.  A zero-one matrix with
prescribed sums is an integral flow in the network `source → row i` (capacity `R i`), `row i → column j` (capacity `1`),
`column j → sink` (capacity `C j`) of value `∑ C`.  By max-flow min-cut and integrality, such a flow exists as soon as
every cut has capacity at least `∑ C`; minimising over the rows on the source side, this becomes the condition
`∑_{j ∈ K} C j ≤ ∑_i min (R i, |K|)` for every set `K` of columns.  For a nonincreasing `C` the worst `K` of a given
size is an initial segment, and `∑_i min (R i, s)` is the sum of the first `s` entries of the dual partition `Rᵈ`, which
gives the book's form "`Rᵈ` dominates `C`".

Main results:
* `exists_matrix_iff_min_condition`: matrices exist iff `∑ R = ∑ C` and `∑_{K} C ≤ ∑_i min (R i, |K|)` for all `K`;
* `dominates_conj_of_matrix` (CO-332, the obvious necessary condition);
* `gale_ryser` (CO-334, Theorem 16.12), and its partial-sum form `gale_ryser_partial_sums`.
-/

namespace UndergradKB.Combinatorics

open Finset UndergradKB.Combinatorics.Flow

/-- CO-331. The row sum string of a zero-one matrix: the number of ones in row `i`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) row sum string, p. 347"]
def rowSum {ι κ : Type*} [Fintype κ] (M : ι → κ → Bool) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => M i j = true).card

/-- CO-331. The column sum string of a zero-one matrix: the number of ones in column `j`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) column sum string, p. 347"]
def colSum {ι κ : Type*} [Fintype ι] (M : ι → κ → Bool) (j : κ) : ℕ :=
  (Finset.univ.filter fun i => M i j = true).card

namespace GaleRyser

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Capacities of the Gale–Ryser network. -/
noncomputable def capf (R : ι → ℕ) (C : κ → ℕ) :
    Option (Option (ι ⊕ κ)) → Option (Option (ι ⊕ κ)) → ℝ
  | none, some (some (Sum.inl i)) => R i
  | some (some (Sum.inl _)), some (some (Sum.inr _)) => 1
  | some (some (Sum.inr j)), some none => C j
  | _, _ => 0

open MatchingNetwork in
/-- The network. -/
noncomputable def net (R : ι → ℕ) (C : κ → ℕ) : Network (Option (Option (ι ⊕ κ))) where
  adj := MatchingNetwork.adj (fun (_ : ι) (_ : κ) => True)
  oriented x y h := by
    rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;> simp_all [MatchingNetwork.adj]
  source := none
  sink := some none
  source_ne_sink := by simp
  no_in_source x := by rcases x with _ | _ | _ | _ <;> simp [MatchingNetwork.adj]
  no_out_sink y := by rcases y with _ | _ | _ | _ <;> simp [MatchingNetwork.adj]
  cap := capf R C
  cap_nonneg x y := by
    rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;> simp [capf]
  cap_of_not_adj x y h := by
    rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;> simp_all [capf, MatchingNetwork.adj]

variable {R : ι → ℕ} {C : κ → ℕ}

lemma cap_int (x y) : ∃ n : ℕ, (net R C).cap x y = n := by
  rcases x with _ | _ | _ | _ <;> rcases y with _ | _ | _ | _ <;>
    first
    | (refine ⟨0, ?_⟩; simp [net, capf]; done)
    | (refine ⟨1, ?_⟩; simp [net, capf]; done)
    | (refine ⟨_, rfl⟩)

/-- Capacity of a cut, expanded. -/
lemma capacity_eq (L : Finset (Option (Option (ι ⊕ κ)))) (h1 : none ∈ L) (h2 : some none ∉ L) :
    (net R C).capacity L =
      (∑ i, if (some (some (Sum.inl i)) : Option (Option (ι ⊕ κ))) ∈ L then 0 else (R i : ℝ)) +
      (∑ i, ∑ j, if (some (some (Sum.inl i)) : Option (Option (ι ⊕ κ))) ∈ L then
          (if (some (some (Sum.inr j)) : Option (Option (ι ⊕ κ))) ∈ L then 0 else (1 : ℝ)) else 0) +
      (∑ j, if (some (some (Sum.inr j)) : Option (Option (ι ⊕ κ))) ∈ L then (C j : ℝ) else 0) := by
  have key : ∀ (s : Finset (Option (Option (ι ⊕ κ)))) (g : Option (Option (ι ⊕ κ)) → ℝ),
      ∑ x ∈ s, g x = ∑ x, if x ∈ s then g x else 0 := fun s g => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have key2 : ∀ f : Option (Option (ι ⊕ κ)) → Option (Option (ι ⊕ κ)) → ℝ,
      ∑ x ∈ L, ∑ y ∈ Lᶜ, f x y = ∑ x, ∑ y, if x ∈ L then (if y ∈ L then 0 else f x y) else 0 := by
    intro f
    rw [key L]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ L
    · simp only [hx, ite_true]
      rw [key Lᶜ]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp
    · simp [hx]
  unfold Network.capacity
  rw [key2]
  simp only [Fintype.sum_option, Fintype.sum_sum_type, net, capf, h1, h2, Finset.sum_add_distrib, ite_true, ite_false]
  simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero]
  ring

/-- The vertex of a row. -/
abbrev vr (i : ι) : Option (Option (ι ⊕ κ)) := some (some (Sum.inl i))
/-- The vertex of a column. -/
abbrev vc (j : κ) : Option (Option (ι ⊕ κ)) := some (some (Sum.inr j))

/-- Every cut has capacity at least `∑ C`, given the min condition. -/
lemma cut_ge (H : ∀ K : Finset κ, ∑ j ∈ K, C j ≤ ∑ i, min (R i) K.card)
    (S : Finset (Option (Option (ι ⊕ κ)))) (h1 : none ∈ S) (h2 : some none ∉ S) :
    (∑ j, (C j : ℝ)) ≤ (net R C).capacity S := by
  classical
  rw [capacity_eq S h1 h2]
  set K : Finset κ := Finset.univ.filter fun j => vc j ∉ S with hK
  have hcard : (K.card : ℝ) = ∑ j, if vc j ∈ S then 0 else (1 : ℝ) := by
    rw [hK, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : vc j ∈ S <;> simp [h]
  have hKsum : (∑ j ∈ K, (C j : ℝ)) = ∑ j, if vc j ∈ S then 0 else (C j : ℝ) := by
    rw [hK, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : vc j ∈ S <;> simp [h]
  have hH : (∑ j ∈ K, (C j : ℝ)) ≤ ∑ i, if vr i ∈ S then (K.card : ℝ) else R i := by
    have h3 : ∑ j ∈ K, C j ≤ ∑ i, if vr i ∈ S then K.card else R i :=
      (H K).trans (Finset.sum_le_sum fun i _ => by
        by_cases h : vr i ∈ S
        · simp [h]
        · simp [h])
    exact_mod_cast h3
  have hmid : (∑ i, ∑ j, if vr i ∈ S then (if vc j ∈ S then 0 else (1 : ℝ)) else 0) =
      ∑ i, if vr i ∈ S then (K.card : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : vr i ∈ S
    · simp [h, hcard]
    · simp [h]
  have hC : (∑ j, (C j : ℝ)) =
      (∑ j, if vc j ∈ S then (C j : ℝ) else 0) + ∑ j, if vc j ∈ S then 0 else (C j : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : vc j ∈ S <;> simp [h]
  have hmerge : (∑ i, if vr i ∈ S then 0 else (R i : ℝ)) +
      (∑ i, if vr i ∈ S then (K.card : ℝ) else 0) = ∑ i, if vr i ∈ S then (K.card : ℝ) else R i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : vr i ∈ S <;> simp [h]
  rw [hmid, hC]
  rw [hKsum] at hH
  linarith

lemma value_eq {φ : Option (Option (ι ⊕ κ)) → Option (Option (ι ⊕ κ)) → ℝ}
    (h0 : ∀ x y, ¬ MatchingNetwork.adj (fun (_ : ι) (_ : κ) => True) x y → φ x y = 0) :
    (net R C).value φ = ∑ i, φ none (vr i) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := MatchingNetwork.zeros h0
  simp [Network.value, Network.netOut, net, Fintype.sum_option, Fintype.sum_sum_type, h1, h2, h3, h4,
    h5, h6, h7, h8]

/-- Sufficiency: if the totals agree and every set of columns satisfies the min condition,
a 0-1 matrix with the given row and column sums exists. -/
theorem exists_matrix_of_min_condition (hsum : ∑ i, R i = ∑ j, C j)
    (H : ∀ K : Finset κ, ∑ j ∈ K, C j ≤ ∑ i, min (R i) K.card) :
    ∃ M : ι → κ → Bool, (∀ i, rowSum M i = R i) ∧ ∀ j, colSum M j = C j := by
  classical
  obtain ⟨φ, hφ, hint, hmax⟩ := (net R C).exists_integral_maxFlow cap_int
  obtain ⟨φ0, S, hφ0, hS, hval, -, -⟩ := (net R C).maxFlow_minCut
  have hge : (∑ j, (C j : ℝ)) ≤ (net R C).value φ :=
    calc (∑ j, (C j : ℝ)) ≤ (net R C).capacity S := cut_ge H S hS.source_mem hS.sink_not_mem
      _ = (net R C).value φ0 := hval.symm
      _ ≤ (net R C).value φ := hmax φ0 hφ0
  have h0 : ∀ x y, ¬ MatchingNetwork.adj (fun (_ : ι) (_ : κ) => True) x y → φ x y = 0 :=
    fun x y h => hφ.eq_zero_of_not_adj h
  have hrow : ∀ i, ∑ j, φ (vr i) (vc j) = φ none (vr i) := by
    intro i
    have := hφ.conserve (vr i) (by simp [net]) (by simp [net])
    rw [MatchingNetwork.netOut_L h0] at this
    linarith
  have hcol : ∀ j, ∑ i, φ (vr i) (vc j) = φ (vc j) (some none) := by
    intro j
    have := hφ.conserve (vc j) (by simp [net]) (by simp [net])
    rw [MatchingNetwork.netOut_R h0] at this
    linarith
  have hcapS : ∀ i, φ none (vr i) ≤ R i := fun i => by
    simpa [net, capf] using hφ.le_cap none (vr i)
  have hcapT : ∀ j, φ (vc j) (some none) ≤ C j := fun j => by
    simpa [net, capf] using hφ.le_cap (vc j) (some none)
  have h01 : ∀ i j, φ (vr i) (vc j) = 0 ∨ φ (vr i) (vc j) = 1 := by
    intro i j
    obtain ⟨n, hn⟩ := hint (vr i) (vc j)
    have hle := hφ.le_cap (vr i) (vc j)
    have hc : (net R C).cap (vr i) (vc j) = 1 := by simp [net, capf]
    rw [hn, hc] at hle
    have : n ≤ 1 := by exact_mod_cast hle
    rw [hn]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with rfl | rfl <;> simp
  have hsumR : (∑ i, (R i : ℝ)) = ∑ j, (C j : ℝ) := by exact_mod_cast hsum
  have hv : (net R C).value φ = ∑ i, φ none (vr i) := value_eq h0
  have hf : ∀ i, φ none (vr i) = R i := by
    have hsf : ∑ i, φ none (vr i) = ∑ i, (R i : ℝ) :=
      le_antisymm (Finset.sum_le_sum fun i _ => hcapS i) (by linarith)
    intro i
    exact (Finset.sum_eq_sum_iff_of_le fun i _ => hcapS i).1 hsf i (Finset.mem_univ i)
  have hg : ∀ j, φ (vc j) (some none) = C j := by
    have hsg : ∑ j, φ (vc j) (some none) = ∑ j, (C j : ℝ) := by
      simp_rw [← hcol]
      rw [Finset.sum_comm]
      simp_rw [hrow, hf]
      exact hsumR
    intro j
    exact (Finset.sum_eq_sum_iff_of_le fun j _ => hcapT j).1 hsg j (Finset.mem_univ j)
  refine ⟨fun i j => decide (φ (vr i) (vc j) = 1), fun i => ?_, fun j => ?_⟩
  · have : (rowSum (fun i j => decide (φ (vr i) (vc j) = 1)) i : ℝ) = R i := by
      rw [← hf i, ← hrow i, rowSum, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases h01 i j with h | h <;> simp [h]
    exact_mod_cast this
  · have : (colSum (fun i j => decide (φ (vr i) (vc j) = 1)) j : ℝ) = C j := by
      rw [← hg j, ← hcol j, colSum, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases h01 i j with h | h <;> simp [h]
    exact_mod_cast this

end GaleRyser

/-! ### Necessity and the general criterion -/

section Criterion

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma rowSum_eq_sum (M : ι → κ → Bool) (i : ι) : rowSum M i = ∑ j, if M i j = true then 1 else 0 := by
  rw [rowSum, Finset.card_filter]

lemma colSum_eq_sum (M : ι → κ → Bool) (j : κ) : colSum M j = ∑ i, if M i j = true then 1 else 0 := by
  rw [colSum, Finset.card_filter]

/-- The total number of ones counted by rows and by columns agree. -/
lemma sum_rowSum_eq_sum_colSum (M : ι → κ → Bool) : ∑ i, rowSum M i = ∑ j, colSum M j := by
  simp_rw [rowSum_eq_sum, colSum_eq_sum]
  exact Finset.sum_comm

/-- The ones of a matrix in the columns of `K` number at most `∑_i min (row sum, |K|)`. -/
lemma sum_colSum_le (M : ι → κ → Bool) (K : Finset κ) :
    ∑ j ∈ K, colSum M j ≤ ∑ i, min (rowSum M i) K.card := by
  simp_rw [colSum_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => le_min ?_ ?_
  · rw [rowSum_eq_sum]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ K)
  · calc ∑ j ∈ K, (if M i j = true then 1 else 0) ≤ ∑ j ∈ K, 1 :=
          Finset.sum_le_sum fun _ _ => by split_ifs <;> simp
      _ = K.card := by simp

/-- A matrix with the given row and column sums exists exactly when the totals agree and
`∑_{j ∈ K} C j ≤ ∑_i min (R i, |K|)` for every set `K` of columns (the max-flow min-cut form of the
Gale–Ryser criterion). -/
theorem exists_matrix_iff_min_condition (R : ι → ℕ) (C : κ → ℕ) :
    (∃ M : ι → κ → Bool, (∀ i, rowSum M i = R i) ∧ ∀ j, colSum M j = C j) ↔
      ∑ i, R i = ∑ j, C j ∧ ∀ K : Finset κ, ∑ j ∈ K, C j ≤ ∑ i, min (R i) K.card := by
  classical
  constructor
  · rintro ⟨M, hR, hC⟩
    refine ⟨?_, fun K => ?_⟩
    · simp_rw [← hR, ← hC]
      exact sum_rowSum_eq_sum_colSum M
    · simp_rw [← hR, ← hC]
      exact sum_colSum_le M K
  · rintro ⟨hsum, H⟩
    exact GaleRyser.exists_matrix_of_min_condition hsum H

end Criterion

/-! ### Strings indexed by `Fin` -/

section Fin

variable {m n : ℕ}

/-- The sum of the first `s` entries is the sum over the initial segment `{k < s}`. -/
lemma psum_eq_sum_filter (C : Fin n → ℕ) {s : ℕ} (hs : s ≤ n) :
    psum C s = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < s), C j := by
  rw [Finset.sum_filter]
  have h1 : ∀ j : Fin n, (if (j : ℕ) < s then C j else 0) = if (j : ℕ) < s then extZero C j else 0 := by
    intro j
    rw [extZero_lt]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < s then extZero C k else 0) n, ← Finset.sum_filter]
  unfold psum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- For a nonincreasing string, a set of `s` entries has sum at most the first `s` entries. -/
lemma sum_le_psum {C : Fin n → ℕ} (hC : Antitone C) (K : Finset (Fin n)) :
    ∑ j ∈ K, C j ≤ psum C K.card := by
  classical
  have hKn : K.card ≤ n := by simpa using Finset.card_le_univ K
  rw [psum_eq_sum_filter C hKn]
  set S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => (j : ℕ) < K.card) with hSdef
  have hS : S.card = K.card := by
    rw [hSdef, Fin.card_filter_val_lt]; exact min_eq_right hKn
  have hc : (K \ S).card = (S \ K).card := by
    have h1 := Finset.card_sdiff_add_card_inter K S
    have h2 := Finset.card_sdiff_add_card_inter S K
    rw [Finset.inter_comm] at h2
    omega
  set c : ℕ := if h : K.card < n then C ⟨K.card, h⟩ else 0 with hc_def
  have hx : ∀ x ∈ K \ S, C x ≤ c := by
    intro x hx
    have hxS : ¬ (x : ℕ) < K.card := by
      have := (Finset.mem_sdiff.1 hx).2
      simpa [hSdef] using this
    have h : K.card < n := lt_of_le_of_lt (not_lt.1 hxS) x.2
    rw [hc_def]
    simp only [h, ↓reduceDIte]
    exact hC (show (⟨K.card, h⟩ : Fin n) ≤ x from Fin.mk_le_of_le_val (not_lt.1 hxS))
  have hy : ∀ y ∈ S \ K, c ≤ C y := by
    intro y hy
    have hyS : (y : ℕ) < K.card := by
      have := (Finset.mem_sdiff.1 hy).1
      simpa [hSdef] using this
    by_cases h : K.card < n
    · rw [hc_def]
      simp only [h, ↓reduceDIte]
      exact hC (show y ≤ (⟨K.card, h⟩ : Fin n) from Fin.le_def.2 hyS.le)
    · rw [hc_def]
      simp only [h, ↓reduceDIte]
      exact Nat.zero_le _
  have e1 := Finset.sum_inter_add_sum_sdiff K S C
  have e2 := Finset.sum_inter_add_sum_sdiff S K C
  rw [Finset.inter_comm] at e2
  have l1 : ∑ x ∈ K \ S, C x ≤ (K \ S).card • c := Finset.sum_le_card_nsmul _ _ _ hx
  have l2 : (S \ K).card • c ≤ ∑ x ∈ S \ K, C x := Finset.card_nsmul_le_sum _ _ _ hy
  rw [hc] at l1
  omega

end Fin

/-- CO-332. The obvious necessary condition: if a zero-one matrix has row sums `R` and column sums `C`, then the dual
partition of `R` dominates `C`. (Moving all the ones of each row to the left turns the column sums into the dual
partition and can only raise partial sums; here the same inequality is derived from `sum_colSum_le`.) -/
@[kb "kellertrotter2017" "text (the obvious necessary condition), p. 348"]
theorem dominates_conj_of_matrix {m n : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ) (M : Fin m → Fin n → Bool)
    (hR : ∀ i, rowSum M i = R i) (hC : ∀ j, colSum M j = C j) : Dominates (conj R) C := by
  classical
  have hmin : ∀ s ≤ n, psum C s ≤ ∑ i, min (R i) s := by
    intro s hs
    have h := (exists_matrix_iff_min_condition R C).1 ⟨M, hR, hC⟩
    have := h.2 (Finset.univ.filter fun j : Fin n => (j : ℕ) < s)
    rw [← psum_eq_sum_filter C hs] at this
    have hcard : (Finset.univ.filter fun j : Fin n => (j : ℕ) < s).card = s := by
      rw [Fin.card_filter_val_lt]; exact min_eq_right hs
    rwa [hcard] at this
  have hRn : ∀ i, R i ≤ n := fun i => by
    rw [← hR i, rowSum]
    simpa using Finset.card_le_univ (Finset.univ.filter fun j : Fin n => M i j = true)
  have hN : Finset.univ.sup R ≤ n := Finset.sup_le fun i _ => hRn i
  refine ⟨hN, fun j hj => ?_⟩
  rw [psum_conj]
  exact hmin j (hj.trans hN)

/-- CO-334 (partial-sum form). **Gale–Ryser.** For strings `R`, `C` with equal sums and `C` nonincreasing, a zero-one
matrix with row sums `R` and column sums `C` exists iff for each `s ≤ n` the sum of the first `s` entries of `C` is at
most `∑_i min (R i, s)`, the sum of the first `s` entries of the dual partition `Rᵈ`. -/
theorem gale_ryser_partial_sums {m n : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ) (hC : Antitone C)
    (hsum : ∑ i, R i = ∑ j, C j) :
    (∃ M : Fin m → Fin n → Bool, (∀ i, rowSum M i = R i) ∧ ∀ j, colSum M j = C j) ↔
      ∀ s ≤ n, psum C s ≤ ∑ i, min (R i) s := by
  classical
  constructor
  · rintro ⟨M, hR, hC'⟩ s hs
    have h := (exists_matrix_iff_min_condition R C).1 ⟨M, hR, hC'⟩
    have := h.2 (Finset.univ.filter fun j : Fin n => (j : ℕ) < s)
    rw [← psum_eq_sum_filter C hs] at this
    have hcard : (Finset.univ.filter fun j : Fin n => (j : ℕ) < s).card = s := by
      rw [Fin.card_filter_val_lt]; exact min_eq_right hs
    rwa [hcard] at this
  · intro h
    refine (exists_matrix_iff_min_condition R C).2 ⟨hsum, fun K => ?_⟩
    have hKn : K.card ≤ n := by simpa using Finset.card_le_univ K
    exact (sum_le_psum hC K).trans (h _ hKn)

/-- CO-334. **The Gale–Ryser theorem** (Theorem 16.12). Let `R` and `C` be partitions of `t` (nonincreasing strings of
positive integers with sum `t`). A zero-one matrix with row sum string `R` and column sum string `C` exists iff the dual
partition `Rᵈ` dominates `C` in the poset `P(t)`.  (Proved via max-flow min-cut rather than the book's chain of
covers.) -/
@[kb "kellertrotter2017" "Theorem 16.12, p. 349"]
theorem gale_ryser {m n t : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ) (hR : IsPartitionString R t)
    (hC : IsPartitionString C t) :
    (∃ M : Fin m → Fin n → Bool, (∀ i, rowSum M i = R i) ∧ ∀ j, colSum M j = C j) ↔ Dominates (conj R) C := by
  constructor
  · rintro ⟨M, hR', hC'⟩
    exact dominates_conj_of_matrix R C M hR' hC'
  · rintro ⟨hN, hdom⟩
    refine (gale_ryser_partial_sums R C hC.antitone (hR.sum_eq.trans hC.sum_eq.symm)).2 fun s hs => ?_
    by_cases hsN : s ≤ Finset.univ.sup R
    · rw [← psum_conj]; exact hdom s hsN
    · have hle : ∀ i, R i ≤ s := fun i =>
        ((Finset.le_sup (f := R) (Finset.mem_univ i)).trans (not_le.1 hsN).le)
      have h1 : ∑ i, min (R i) s = t := by
        rw [← hR.sum_eq]
        exact Finset.sum_congr rfl fun i _ => min_eq_left (hle i)
      rw [h1, ← hC.sum_eq, ← psum_of_ge C (le_refl n)]
      unfold psum
      exact Finset.sum_le_sum_of_subset (Finset.range_mono hs)

end UndergradKB.Combinatorics
