import Mathlib.Order.Sum.Order
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-!
# Interval orders and Fishburn's theorem

Source: Keller--Trotter, *Applied Combinatorics* (2017), Section 6.6.

The hard direction of Fishburn's theorem is proved by a short argument that differs from the
book's algorithm (Section 6.7): in a poset excluding `2 + 2` the strict down sets `D(x)` form a
chain under inclusion, and `a x = |D x|`, `b x = max {|D z| : ¬ x < z}` is an interval
representation.
-/

namespace UndergradKB.Combinatorics.Order

open Finset

variable {α : Type*} [PartialOrder α]

/-- CO-167. A poset is an interval order if every point gets a closed real interval `[a x, b x]`
such that `x < y` exactly when the interval of `x` lies entirely to the left of that of `y`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) interval order, p. 152"]
def IsIntervalOrder (α : Type*) [PartialOrder α] : Prop :=
  ∃ a b : α → ℝ, (∀ x, a x ≤ b x) ∧ ∀ x y, x < y ↔ b x < a y

/-- CO-149. `P` contains `Q` if `Q` embeds in `P` as a subposet (order embedding);
`P` excludes `Q` otherwise. -/
@[kb "kellertrotter2017" "Definition (unnumbered) contains/excludes, p. 143"]
def ContainsPoset (P Q : Type*) [PartialOrder P] [PartialOrder Q] : Prop := Nonempty (Q ↪o P)

/-- Four points `a < b`, `c < d` with no comparabilities between `{a, b}` and `{c, d}`:
a copy of `2 + 2`. -/
def TwoPlusTwo (a b c d : α) : Prop :=
  a < b ∧ c < d ∧ (¬ a ≤ c ∧ ¬ c ≤ a) ∧ (¬ a ≤ d ∧ ¬ d ≤ a) ∧ (¬ b ≤ c ∧ ¬ c ≤ b) ∧
    (¬ b ≤ d ∧ ¬ d ≤ b)

/-- CO-169. `2 + 2` is the disjoint sum of two 2-point chains; it embeds in `α` iff there are four
points forming `TwoPlusTwo`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) P + Q, 2 + 2, p. 152"]
theorem containsPoset_two_plus_two_iff :
    ContainsPoset α (Fin 2 ⊕ Fin 2) ↔ ∃ a b c d : α, TwoPlusTwo a b c d := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e (Sum.inl 0), e (Sum.inl 1), e (Sum.inr 0), e (Sum.inr 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact e.lt_iff_lt.2 (Sum.inl_lt_inl_iff.2 (by decide))
    · exact e.lt_iff_lt.2 (Sum.inr_lt_inr_iff.2 (by decide))
    all_goals
      exact ⟨fun h => Sum.not_inl_le_inr (e.le_iff_le.1 h),
        fun h => Sum.not_inr_le_inl (e.le_iff_le.1 h)⟩
  · rintro ⟨a, b, c, d, h1, h2, ⟨i1, i2⟩, ⟨i3, i4⟩, ⟨i5, i6⟩, ⟨i7, i8⟩⟩
    refine ⟨OrderEmbedding.ofMapLEIff (Sum.elim ![a, b] ![c, d]) ?_⟩
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [h1.le, h2.le, h1.not_ge, h2.not_ge, i1, i2, i3, i4, i5, i6, i7, i8]

/-- CO-170 (easy direction). An interval order excludes `2 + 2`. -/
theorem IsIntervalOrder.not_containsPoset {α : Type*} [PartialOrder α] (h : IsIntervalOrder α) :
    ¬ ContainsPoset α (Fin 2 ⊕ Fin 2) := by
  intro hc
  obtain ⟨p, q, r, s, h1, h2, -, ⟨i3, -⟩, ⟨-, i6⟩, -⟩ := containsPoset_two_plus_two_iff.1 hc
  obtain ⟨a, b, -, hab⟩ := h
  have e1 := (hab p q).1 h1
  have e2 := (hab r s).1 h2
  have e3 : ¬ b p < a s := fun h => i3 ((hab p s).2 h).le
  have e4 : ¬ b r < a q := fun h => i6 ((hab r q).2 h).le
  push Not at e3 e4
  linarith

variable [Fintype α]

omit [Fintype α] in
/-- In a poset excluding `2 + 2`, the strict down sets are totally ordered by inclusion. -/
theorem downSets_comparable (hne : ¬ ContainsPoset α (Fin 2 ⊕ Fin 2)) (x y : α) :
    ({z | z < x} : Set α) ⊆ {z | z < y} ∨ ({z | z < y} : Set α) ⊆ {z | z < x} := by
  by_contra hcon
  rw [not_or, Set.not_subset, Set.not_subset] at hcon
  obtain ⟨⟨z, hzx, hzy⟩, ⟨w, hwy, hwx⟩⟩ := hcon
  simp only [Set.mem_ofPred_eq] at hzx hzy hwx hwy
  apply hne
  rw [containsPoset_two_plus_two_iff]
  refine ⟨z, x, w, y, hzx, hwy, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact fun h => hzy (lt_of_le_of_lt h hwy)
  · exact fun h => hwx (lt_of_le_of_lt h hzx)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact hzy h
    · exact hwx (hwy.trans hzx)
  · exact fun h => hwx ((hwy.trans_le h).trans hzx)
  · exact fun h => hzy ((hzx.trans_le h).trans hwy)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact hwx h
    · exact hzy (hzx.trans hwy)
  · exact fun h => hzy (hzx.trans_le h)
  · exact fun h => hwx (hwy.trans_le h)

/-- CO-170. **Fishburn's theorem**: a finite poset is an interval order if and only if it
excludes `2 + 2`. -/
@[kb "kellertrotter2017" "Theorem 6.29, p. 153"]
theorem isIntervalOrder_iff_excludes_two_plus_two :
    IsIntervalOrder α ↔ ¬ ContainsPoset α (Fin 2 ⊕ Fin 2) := by
  classical
  refine ⟨IsIntervalOrder.not_containsPoset, fun hne => ?_⟩
  let D : α → Finset α := fun x => univ.filter (· < x)
  have hD : ∀ x z, z ∈ D x ↔ z < x := fun x z => by simp [D]
  have hch : ∀ x y, D x ⊆ D y ∨ D y ⊆ D x := by
    intro x y
    rcases downSets_comparable hne x y with h | h
    · exact Or.inl fun z hz => (hD _ _).2 (h ((hD _ _).1 hz))
    · exact Or.inr fun z hz => (hD _ _).2 (h ((hD _ _).1 hz))
  let r : α → ℕ := fun x => (univ.filter fun z => ¬ x < z).sup fun z => (D z).card
  have hr : ∀ x y, ¬ x < y → (D y).card ≤ r x := fun x y h =>
    Finset.le_sup (f := fun z => (D z).card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  refine ⟨fun x => ((D x).card : ℝ), fun x => (r x : ℝ), fun x => ?_, fun x y => ?_⟩
  · show ((D x).card : ℝ) ≤ (r x : ℝ)
    exact_mod_cast hr x x (lt_irrefl x)
  · rw [Nat.cast_lt]
    constructor
    · intro hxy
      have hpos : ⊥ < (D y).card :=
        Finset.card_pos.2 ⟨x, (hD _ _).2 hxy⟩
      refine (Finset.sup_lt_iff hpos).2 fun z hz => ?_
      have hz' : ¬ x < z := (Finset.mem_filter.1 hz).2
      have hsub : D z ⊆ D y := by
        rcases hch z y with h | h
        · exact h
        · exact absurd ((hD _ _).1 (h ((hD _ _).2 hxy))) hz'
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
        ⟨x, (hD _ _).2 hxy, fun hx => hz' ((hD _ _).1 hx)⟩)
    · intro h
      by_contra hxy
      exact absurd (hr x y hxy) (not_le_of_gt h)

end UndergradKB.Combinatorics.Order
