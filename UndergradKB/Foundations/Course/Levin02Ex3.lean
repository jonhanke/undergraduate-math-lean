import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Basic
import UndergradKB.Common

/-!
# Course layer: Levin, Discrete Mathematics, Chapter 2, worked examples (wave 4)
-/

namespace UndergradKB.Foundations.Course

open SimpleGraph

/-! ### Section 2.1: equal versus isomorphic graphs (vertices `a b c d` are `0 1 2 3`) -/

/-- Edge set `{{a,b},{b,c}}` on `{a,b,c} = Fin 3`. -/
def levinG213a : SimpleGraph (Fin 3) := fromEdgeSet {s(0, 1), s(1, 2)}

/-- Edge set `{{a,c},{c,b}}` on `{a,b,c} = Fin 3`. -/
def levinG213b : SimpleGraph (Fin 3) := fromEdgeSet {s(0, 2), s(2, 1)}

/-- Levin Example 2.1.3: the graphs with edges `ab, bc` and `ac, cb` on `{a,b,c}` are not equal, although
`{b,c} = {c,b}`; the difference is that `{a,b} ≠ {a,c}`. -/
@[kb "levin2025" "Example 2.1.3, p. 123"]
theorem levin_ex_2_1_3_graphs_not_equal :
    (s(1, 2) : Sym2 (Fin 3)) = s(2, 1) ∧ (s(0, 1) : Sym2 (Fin 3)) ≠ s(0, 2) ∧
    levinG213a ≠ levinG213b := by
  refine ⟨Sym2.eq_swap, by decide, fun h => ?_⟩
  have := congrArg (fun G : SimpleGraph (Fin 3) => G.Adj 0 1) h
  simp [levinG213a, levinG213b, fromEdgeSet_adj] at this

/-- The triangle on the letters `a, b, c`. -/
def levinTriangleABC : SimpleGraph Char := fromEdgeSet {s('a', 'b'), s('a', 'c'), s('b', 'c')}

/-- The triangle on the letters `u, v, w`. -/
def levinTriangleUVW : SimpleGraph Char := fromEdgeSet {s('u', 'v'), s('u', 'w'), s('v', 'w')}

/-- Levin Example 2.1.4: the triangles on `{a,b,c}` and on `{u,v,w}` are not equal (different vertex sets),
yet renaming `a, b, c` to `u, v, w` is a bijection of vertex sets preserving adjacency both ways. -/
@[kb "levin2025" "Example 2.1.4, p. 124"]
theorem levin_ex_2_1_4_equal_vs_isomorphic :
    ({'a', 'b', 'c'} : Finset Char) ≠ {'u', 'v', 'w'} ∧
    ∃ f : Char → Char, Set.BijOn f ({'a', 'b', 'c'} : Finset Char) ({'u', 'v', 'w'} : Finset Char) ∧
      ∀ x ∈ ({'a', 'b', 'c'} : Finset Char), ∀ y ∈ ({'a', 'b', 'c'} : Finset Char),
        levinTriangleABC.Adj x y ↔ levinTriangleUVW.Adj (f x) (f y) := by
  refine ⟨by decide, fun c => if c = 'a' then 'u' else if c = 'b' then 'v' else 'w', ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    · intro x hx y hy e
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
    · intro y hy
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨'a', by simp⟩
      · exact ⟨'b', by simp⟩
      · exact ⟨'c', by simp⟩
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp [levinTriangleABC, levinTriangleUVW, fromEdgeSet_adj]

/-- Edges `ab, ac, ad, cd` on `{a,b,c,d} = Fin 4`. -/
def levinG216a : SimpleGraph (Fin 4) := fromEdgeSet {s(0, 1), s(0, 2), s(0, 3), s(2, 3)}

/-- Edges `ab, ac, bc, cd` on `{a,b,c,d} = Fin 4`. -/
def levinG216b : SimpleGraph (Fin 4) := fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(2, 3)}

/-- Levin Example 2.1.6: the two graphs are not equal (`ad` is an edge of the first only); the cyclic
shift `a→b→c→d→a` is a bijection that is not an isomorphism; but `a→c, b→d, c→b, d→a` is an isomorphism. -/
@[kb "levin2025" "Example 2.1.6, p. 125"]
theorem levin_ex_2_1_6_equal_or_isomorphic :
    levinG216a ≠ levinG216b ∧
    (¬ ∀ x y : Fin 4, levinG216a.Adj x y ↔ levinG216b.Adj (x + 1) (y + 1)) ∧
    Nonempty (levinG216a ≃g levinG216b) := by
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · have := congrArg (fun G : SimpleGraph (Fin 4) => G.Adj 0 3) h
    simp [levinG216a, levinG216b, fromEdgeSet_adj] at this
  · have := h 0 2
    simp [levinG216a, levinG216b, fromEdgeSet_adj] at this
  · let g : Fin 4 → Fin 4 := ![2, 3, 1, 0]
    let gi : Fin 4 → Fin 4 := ![3, 2, 0, 1]
    refine ⟨⟨g, gi, by decide, by decide⟩, ?_⟩
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [g, levinG216a, levinG216b, fromEdgeSet_adj, Equiv.coe_fn_mk]

/-! ### Section 2.6: the relation "is a multiple of" -/

/-- The relation `M` of Example 2.6.5: `(x, y) ∈ M` when `x` is a multiple of `y`, on `{1..6}`. -/
def levinMultipleOf : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 6 ×ˢ Finset.Icc 1 6).filter (fun p => p.2 ∣ p.1)

/-- Levin Example 2.6.5: the relation "is a multiple of" on `{1,...,6}` consists of exactly 14 listed pairs;
it contains the loops `(x,x)` and is not symmetric, so it is not (the edge relation of) a simple graph. -/
@[kb "levin2025" "Example 2.6.5, p. 187"]
theorem levin_ex_2_6_5_multiple_of_relation :
    levinMultipleOf = {(1, 1), (2, 1), (2, 2), (3, 1), (3, 3), (4, 1), (4, 2), (4, 4),
      (5, 1), (5, 5), (6, 1), (6, 2), (6, 3), (6, 6)} ∧
    (∀ x ∈ Finset.Icc 1 6, (x, x) ∈ levinMultipleOf) ∧
    (6, 2) ∈ levinMultipleOf ∧ (2, 6) ∉ levinMultipleOf := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Levin D057 (Example 2.6.5 notation): `(6, 2)` belongs to the "is a multiple of" relation on
`{1,...,6}` while `(6, 4)` does not. -/
@[kb "levin2025" "Example 2.6.5, p. 187"]
theorem levin_d057_multiple_of_membership :
    (6, 2) ∈ levinMultipleOf ∧ (6, 4) ∉ levinMultipleOf := by
  decide

/-! ### Section 2.7: Hall's theorem on card piles -/

private lemma levin_fiber_card {C D : Type} [Fintype C] [Fintype D] [DecidableEq D] (f : C → D)
    (hf : ∀ d, (Finset.univ.filter (fun x => f x = d)).card = 4) (T : Finset D) :
    (Finset.univ.filter (fun x => f x ∈ T)).card = 4 * T.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := T) (fun _ hx => by simpa using hx)]
  have : ∀ d ∈ T, ((Finset.univ.filter (fun x => f x ∈ T)).filter (fun x => f x = d)).card = 4 := by
    intro d hd
    rw [← hf d]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hd, h⟩
  rw [Finset.sum_congr rfl this]
  simp [mul_comm]

/-- Levin Example 2.7.3: 52 cards are dealt into 13 piles of 4 and have 13 values with 4 cards each (here
cards are `Fin 52`, `pile` and `val` give the pile and the value of a card). Then one card can be chosen
from every pile so that every value occurs exactly once: there is a card `c v` of each value `v` and the
piles of the chosen cards are all different (so every pile is used exactly once). -/
@[kb "levin2025" "Example 2.7.3, p. 203"]
theorem levin_ex_2_7_3_card_piles (pile val : Fin 52 → Fin 13)
    (hp : ∀ p, (Finset.univ.filter (fun x => pile x = p)).card = 4)
    (hv : ∀ v, (Finset.univ.filter (fun x => val x = v)).card = 4) :
    ∃ c : Fin 13 → Fin 52, (∀ v, val (c v) = v) ∧ Function.Bijective (fun v => pile (c v)) := by
  classical
  let t : Fin 13 → Finset (Fin 13) := fun v => (Finset.univ.filter (fun x => val x = v)).image pile
  have hall : ∀ s : Finset (Fin 13), s.card ≤ (s.biUnion t).card := by
    intro s
    have h1 := levin_fiber_card val hv s
    have h2 := levin_fiber_card pile hp (s.biUnion t)
    have hsub : Finset.univ.filter (fun x => val x ∈ s) ⊆
        Finset.univ.filter (fun x => pile x ∈ s.biUnion t) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact Finset.mem_biUnion.2 ⟨val x, hx, Finset.mem_image.2 ⟨x, by simp, rfl⟩⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨f, hfi, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hex : ∀ v, ∃ x, val x = v ∧ pile x = f v := by
    intro v
    have := hft v
    simp only [t, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at this
    obtain ⟨x, hx, hpx⟩ := this
    exact ⟨x, hx, hpx⟩
  choose c hc1 hc2 using hex
  refine ⟨c, hc1, ?_⟩
  have : (fun v => pile (c v)) = f := funext hc2
  rw [this]
  exact (Finite.injective_iff_bijective).1 hfi

end UndergradKB.Foundations.Course
