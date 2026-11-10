import Mathlib.Data.Nat.Cast.Order.Field
import UndergradKB.Combinatorics.Flow.Matching
import UndergradKB.Common.Attr

/-!
# Ford–Fulkerson with integer capacities (Keller–Trotter, Algorithm 13.11, Theorem 14.1)

The labelled vertices of the labelling algorithm are the vertices reachable from the source by
residual steps (`Network.labelled`).  Here we prove the correctness of the whole algorithm run from
the zero flow with integer capacities: each round with the sink labelled augments an integral flow by
one unit along an augmenting path and yields an integral flow, the value is bounded by the capacity
of the cut `{source}`, so after finitely many rounds the sink is unlabelled; the final flow is an
integral maximum flow and the labelled set a minimum cut.
-/

namespace UndergradKB.Combinatorics.Flow

open Finset

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

/-- A function on ordered pairs is integer valued. -/
def IsIntegral (φ : V → V → ℝ) : Prop := ∀ x y, ∃ n : ℤ, φ x y = n

lemma one_le_residualCap (hcap : ∀ x y, ∃ n : ℤ, N.cap x y = n) {φ : V → V → ℝ}
    (hφ : IsIntegral φ) {x y : V} (h : N.Residual φ x y) : 1 ≤ N.residualCap φ x y := by
  classical
  unfold residualCap
  rcases h with ⟨hadj, hlt⟩ | ⟨hadj, hpos⟩
  · rw [ite_eq_left hadj]
    obtain ⟨a, ha⟩ := hcap x y
    obtain ⟨b, hb⟩ := hφ x y
    rw [ha, hb] at hlt ⊢
    have h1 : b < a := by exact_mod_cast hlt
    have h2 : b + 1 ≤ a := h1
    have h3 : ((b : ℝ) + 1) ≤ a := by exact_mod_cast h2
    linarith
  · rw [ite_eq_right (N.oriented _ _ hadj)]
    obtain ⟨b, hb⟩ := hφ y x
    rw [hb] at hpos ⊢
    have h1 : 0 < b := by exact_mod_cast hpos
    have h2 : (1 : ℤ) ≤ b := h1
    exact_mod_cast h2

lemma pathChange_integral {φ : V → V → ℝ} {a b : V} (p : N.AugPath φ a b) :
    IsIntegral (N.pathChange p 1) := by
  intro x y
  rcases N.pathChange_cases p 1 x y with h | ⟨i, -, -, -, h⟩ | ⟨i, -, -, -, h⟩
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩

/-- One round of the algorithm: with the sink labelled, an integral flow can be augmented by one
unit to another integral flow. -/
theorem exists_integral_augment (hcap : ∀ x y, ∃ n : ℤ, N.cap x y = n) {φ : V → V → ℝ}
    (hφ : N.IsFlow φ) (hint : IsIntegral φ) (ht : N.sink ∈ N.labelled φ) :
    ∃ ψ, N.IsFlow ψ ∧ IsIntegral ψ ∧ N.value ψ = N.value φ + 1 := by
  obtain ⟨p⟩ := exists_augPath (mem_labelled.1 ht)
  obtain ⟨hψ, hv⟩ := N.augment hφ p (δ := 1) zero_le_one
    (fun i => one_le_residualCap hcap hint (p.step i))
  refine ⟨_, hψ, fun x y => ?_, hv⟩
  obtain ⟨a, ha⟩ := hint x y
  obtain ⟨b, hb⟩ := pathChange_integral p x y
  exact ⟨a + b, by push_cast; rw [ha, hb]⟩

/-- Termination: starting from the zero flow with integer capacities, augmenting by units reaches
an integral flow for which the sink is unlabelled. -/
theorem exists_integral_flow_sink_unlabelled (hcap : ∀ x y, ∃ n : ℤ, N.cap x y = n) :
    ∃ φ, N.IsFlow φ ∧ IsIntegral φ ∧ N.sink ∉ N.labelled φ := by
  by_contra hno
  push Not at hno
  have key : ∀ k : ℕ, ∃ φ, N.IsFlow φ ∧ IsIntegral φ ∧ N.value φ = k := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, ⟨fun _ _ => le_rfl, fun x y => N.cap_nonneg x y,
        fun v _ _ => by simp [netOut]⟩, fun x y => ⟨0, by simp⟩, ?_⟩
      simp [value, netOut]
    | succ k ih =>
      obtain ⟨φ, h1, h2, h3⟩ := ih
      obtain ⟨ψ, g1, g2, g3⟩ := exists_integral_augment hcap h1 h2 (hno φ h1 h2)
      exact ⟨ψ, g1, g2, by rw [g3, h3]; push_cast; ring⟩
  have hL : N.IsCut ({N.source} : Finset V) :=
    ⟨by simp, by simpa using N.source_ne_sink.symm⟩
  obtain ⟨φ, h1, h2, h3⟩ := key (⌈N.capacity {N.source}⌉₊ + 1)
  have h4 := value_le_capacity h1 hL
  rw [h3] at h4
  push_cast at h4
  have h5 := Nat.le_ceil (N.capacity {N.source})
  linarith

lemma IsIntegral.toNat {φ : V → V → ℝ} (hφ : N.IsFlow φ) (hi : IsIntegral φ) :
    ∀ x y, ∃ n : ℕ, φ x y = n := by
  intro x y
  obtain ⟨z, hz⟩ := hi x y
  have h0 : 0 ≤ z := by
    have := hφ.nonneg x y
    rw [hz] at this
    exact_mod_cast this
  exact ⟨z.toNat, by rw [hz]; exact_mod_cast (Int.toNat_of_nonneg h0).symm⟩

/-- CO-295. Correctness of one stage of the Ford–Fulkerson labelling algorithm for any flow `φ`:
if the sink gets labelled the flow can be enlarged; if the labelling stops without reaching the sink,
`φ` is a maximum flow and the labelled set is a minimum cut of the same capacity. -/
@[kb "kellertrotter2017" "Algorithm 13.11, p. 292"]
theorem labelling_correct {φ : V → V → ℝ} (hφ : N.IsFlow φ) :
    (N.sink ∈ N.labelled φ → ∃ ψ, N.IsFlow ψ ∧ N.value φ < N.value ψ) ∧
    (N.sink ∉ N.labelled φ → N.IsCut (N.labelled φ) ∧ N.value φ = N.capacity (N.labelled φ) ∧
      (∀ ψ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ∧
      ∀ M, N.IsCut M → N.capacity (N.labelled φ) ≤ N.capacity M) := by
  refine ⟨fun h => exists_larger_of_sink_labelled hφ h, fun ht => ?_⟩
  have hv := capacity_labelled_eq_value hφ ht
  exact ⟨labelled_isCut ht, hv.symm, (isMax_iff_sink_not_labelled hφ).2 ht,
    fun M hM => hv ▸ value_le_capacity hφ hM⟩

/-- CO-295 and CO-299. The Ford–Fulkerson algorithm with integer capacities, started from the zero
flow and augmenting by one unit per round, terminates with an integral maximum flow and a minimum cut
(the labelled vertices) of equal capacity. -/
@[kb "kellertrotter2017" "Algorithm 13.11, p. 292; Theorem 14.1, p. 303"]
theorem fordFulkerson_integral (hcap : ∀ x y, ∃ n : ℕ, N.cap x y = n) :
    ∃ φ, N.IsFlow φ ∧ (∀ x y, ∃ n : ℕ, φ x y = n) ∧ N.sink ∉ N.labelled φ ∧
      N.IsCut (N.labelled φ) ∧ N.value φ = N.capacity (N.labelled φ) ∧
      (∀ ψ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ∧
      ∀ M, N.IsCut M → N.capacity (N.labelled φ) ≤ N.capacity M := by
  obtain ⟨φ, h1, h2, h3⟩ := exists_integral_flow_sink_unlabelled (N := N)
    (fun x y => by obtain ⟨n, hn⟩ := hcap x y; exact ⟨n, by simpa using hn⟩)
  obtain ⟨a, b, c, d⟩ := (labelling_correct h1).2 h3
  exact ⟨φ, h1, h2.toNat h1, h3, a, b, c, d⟩

end Network

open MatchingNetwork in
/-- CO-303. Maximum bipartite matching by the labelling algorithm: on the unit network of the
bipartite graph `r`, the Ford–Fulkerson algorithm ends with an integral flow whose sink is
unlabelled, and the pairs carrying flow form a maximum matching of size equal to the flow value. -/
@[kb "kellertrotter2017" "text, p. 305"]
theorem matching_by_labelling {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) :
    ∃ M φ, IsMatching r M ∧ (matchingNetwork r).IsFlow φ ∧
      (matchingNetwork r).sink ∉ (matchingNetwork r).labelled φ ∧
      (M.card : ℝ) = (matchingNetwork r).value φ ∧
      ∀ M', IsMatching r M' → M'.card ≤ M.card := by
  have hcap : ∀ x y, ∃ n : ℕ, (matchingNetwork r).cap x y = n := fun x y => by
    classical
    by_cases h : adj r x y
    · exact ⟨1, by simp [matchingNetwork, h]⟩
    · exact ⟨0, by simp [matchingNetwork, h]⟩
  obtain ⟨φ, hφ, hint, hs, -, -, hmax, -⟩ := Network.fordFulkerson_integral hcap
  obtain ⟨M, hM, hcard⟩ := exists_matching_of_flow hφ hint
  refine ⟨M, φ, hM, hφ, hs, hcard, fun M' hM' => ?_⟩
  obtain ⟨ψ, hψ, -, hv⟩ := exists_flow_of_matching hM'
  have := hmax ψ hψ
  rw [hv, ← hcard] at this
  exact_mod_cast this

end UndergradKB.Combinatorics.Flow
