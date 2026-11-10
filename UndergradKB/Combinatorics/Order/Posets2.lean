import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Extension.Linear
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Lattice
import Mathlib.Order.Prod.Lex.Basic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.Basic
import UndergradKB.Combinatorics.Order.IntervalOrder

/-!
# More on finite posets (Keller--Trotter, Chapter 6)

* the level decomposition obtained by repeatedly removing the minimal points (CO-159);
* the four universal constructions of posets of Example 6.7 (CO-150);
* the dimension of a poset as the least number of linear orders with intersection `P` (CO-176);
* distinguishing representations of interval orders (CO-168).
-/

namespace UndergradKB.Combinatorics.Order

open Finset

variable {α : Type*} [PartialOrder α]

/-! ### Levels: repeatedly removing the minimal points (CO-159) -/

section Levels

open Classical

variable [Fintype α]

/-- The minimal points of a finite set `t` of the poset. -/
noncomputable def minPoints (t : Finset α) : Finset α :=
  t.filter fun x => ∀ y ∈ t, y ≤ x → y = x

/-- `remaining k` is what is left of the poset after the first `k` rounds of removing the minimal
points (the book's `P_k`). -/
noncomputable def remaining : ℕ → Finset α
  | 0 => univ
  | k + 1 => remaining k \ minPoints (remaining k)

/-- CO-159. The `k`-th level (zero-based): the minimal points of what remains after removing the
first `k` levels (the book's antichain `A_k`). -/
@[kb "kellertrotter2017" "text (algorithm after Theorem 6.18), p. 146"]
noncomputable def level (k : ℕ) : Finset α := minPoints (remaining k)

theorem remaining_succ (k : ℕ) :
    remaining (α := α) (k + 1) = remaining k \ level k := rfl

theorem exists_lt_pointHeight {x : α} (hx : 2 ≤ pointHeight x) :
    ∃ y, y < x ∧ pointHeight x ≤ pointHeight y + 1 := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup (chainsBelow x) ⟨∅, by simp⟩ Finset.card
  obtain ⟨hch, hle⟩ := mem_chainsBelow.1 hs
  have hcard' : pointHeight x = s.card := hcard
  have hne : (s.erase x).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.pred_card_le_card_erase (s := s) (a := x)
    omega
  obtain ⟨y, hy⟩ := Finset.exists_maximal hne
  have hyx : y ∈ s ∧ y ≠ x := by simpa [Finset.mem_erase, and_comm] using hy.1
  have hlt : y < x := lt_of_le_of_ne (hle y hyx.1) hyx.2
  refine ⟨y, hlt, ?_⟩
  have hmem : s.erase x ∈ chainsBelow y := by
    refine mem_chainsBelow.2 ⟨hch.mono (by simp), fun z hz => ?_⟩
    have hz' : z ∈ s ∧ z ≠ x := by simpa [Finset.mem_erase, and_comm] using hz
    by_cases hzy : z = y
    · exact hzy.le
    rcases hch hz'.1 hyx.1 hzy with h | h
    · exact h
    · exact hy.2 hz h
  have h1 : (s.erase x).card ≤ pointHeight y := Finset.le_sup (f := Finset.card) hmem
  have := Finset.pred_card_le_card_erase (s := s) (a := x)
  omega

theorem mem_remaining (k : ℕ) (x : α) : x ∈ remaining k ↔ k < pointHeight x := by
  induction k generalizing x with
  | zero => simpa [remaining] using pointHeight_pos x
  | succ k ih =>
    rw [remaining_succ, Finset.mem_sdiff, level, minPoints, Finset.mem_filter, ih]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hcon
      have h3 : pointHeight x = k + 1 := by omega
      apply h2
      refine ⟨h1, fun y hy hyx => ?_⟩
      by_contra hne
      have := pointHeight_lt_of_lt (lt_of_le_of_ne hyx hne)
      have := (ih y).1 hy
      omega
    · intro h
      refine ⟨by omega, fun ⟨_, hmin⟩ => ?_⟩
      obtain ⟨y, hyx, hy⟩ := exists_lt_pointHeight (x := x) (by omega)
      have := hmin y ((ih y).2 (by omega)) hyx.le
      exact hyx.ne this

/-- A point lies in level `k` exactly when its height (the longest chain ending at it) is `k+1`. -/
theorem mem_level (k : ℕ) (x : α) : x ∈ level k ↔ pointHeight x = k + 1 := by
  rw [level, minPoints, Finset.mem_filter, mem_remaining]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hcon
    obtain ⟨y, hyx, hy⟩ := exists_lt_pointHeight (x := x) (by omega)
    have := h2 y ((mem_remaining k y).2 (by omega)) hyx.le
    exact hyx.ne this
  · intro h
    refine ⟨by omega, fun y hy hyx => ?_⟩
    by_contra hne
    have := pointHeight_lt_of_lt (lt_of_le_of_ne hyx hne)
    have := (mem_remaining k y).1 hy
    omega

theorem exists_pointHeight_eq {m : ℕ} (hm : 1 ≤ m) (hmh : m ≤ height α) :
    ∃ x : α, pointHeight x = m := by
  have key : ∀ d, d + m = height α → ∃ x : α, pointHeight x = m := by
    intro d
    induction d generalizing m with
    | zero =>
      intro hd
      have hd' : m = height α := by omega
      obtain ⟨s, hs, hcard⟩ := exists_chain_card_eq_height (α := α)
      have hsne : s.Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨x, hx⟩ := Finset.exists_maximal hsne
      have hsub : s ∈ chainsBelow x := by
        refine mem_chainsBelow.2 ⟨hs, fun z hz => ?_⟩
        by_cases hzx : z = x
        · exact hzx.le
        rcases hs hz hx.1 hzx with h | h
        · exact h
        · exact hx.2 hz h
      have h1 : s.card ≤ pointHeight x := Finset.le_sup (f := Finset.card) hsub
      have h2 := pointHeight_le_height x
      exact ⟨x, by omega⟩
    | succ d ih =>
      intro hd
      obtain ⟨x, hx⟩ := ih (m := m + 1) (by omega) (by omega) (by omega)
      obtain ⟨y, hyx, hy⟩ := exists_lt_pointHeight (x := x) (by omega)
      have := pointHeight_lt_of_lt hyx
      exact ⟨y, by omega⟩
  exact key (height α - m) (by omega)

/-- CO-159. The algorithm of repeatedly removing the set of minimal points produces an antichain
partition of the poset into exactly `height(P)` antichains: every level is an antichain, every
point lies in exactly one level, and the `k`-th level is nonempty exactly when `k < height P`. -/
@[kb "kellertrotter2017" "text (algorithm after Theorem 6.18), p. 146"]
theorem levels_partition :
    (∀ k, IsAntichain (· ≤ ·) ((level k : Finset α) : Set α)) ∧
    (∀ x : α, ∃! k, x ∈ level k) ∧
    (∀ k, (level k : Finset α).Nonempty ↔ k < height α) := by
  refine ⟨fun k x hx y hy hne hxy => ?_, fun x => ?_, fun k => ?_⟩
  · have hx' := (mem_level k x).1 hx
    have hy' := (mem_level k y).1 hy
    have := pointHeight_lt_of_lt (lt_of_le_of_ne hxy hne)
    omega
  · refine ⟨pointHeight x - 1, (mem_level _ _).2 (by have := pointHeight_pos x; omega), fun k hk => ?_⟩
    have := (mem_level _ _).1 hk
    omega
  · constructor
    · rintro ⟨x, hx⟩
      have := (mem_level k x).1 hx
      have := pointHeight_le_height x
      omega
    · intro hk
      obtain ⟨x, hx⟩ := exists_pointHeight_eq (α := α) (m := k + 1) (by omega) (by omega)
      exact ⟨x, (mem_level k x).2 hx⟩

end Levels

/-! ### Every poset is a poset of sets, of integers, of real tuples (CO-150) -/

/-- The down-set `D[x] = {y : y ≤ x}` as a set. -/
def downClosure (x : α) : Set α := Set.Iic x

/-- CO-150 (1). Every poset is isomorphic to a family of sets ordered by inclusion:
`x ↦ D[x]` is an order embedding of `α` into `Set α`. -/
@[kb "kellertrotter2017" "Discussion 6.12, p. 143"]
def downSetEmbedding : α ↪o Set α :=
  OrderEmbedding.ofMapLEIff (fun x => Set.Iic x) fun _ _ => Set.Iic_subset_Iic

open Classical in
/-- CO-150 (1), finite version: a finite poset embeds in `Finset α` ordered by inclusion via
`x ↦ D[x]`. -/
@[kb "kellertrotter2017" "Discussion 6.12, p. 143"]
noncomputable def finsetDownSetEmbedding [Fintype α] : α ↪o Finset α :=
  OrderEmbedding.ofMapLEIff (fun x => Finset.univ.filter (· ≤ x)) fun x y => by
    constructor
    · intro h
      have : x ∈ Finset.univ.filter (· ≤ y) := h (by simp)
      simpa using this
    · intro h z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.trans h

/-- CO-150 (2). Every finite poset is isomorphic to a set of positive integers ordered by
divisibility: give each point its own prime and send `x` to the product of the primes of `D[x]`. -/
@[kb "kellertrotter2017" "Discussion 6.12, p. 143"]
theorem exists_divisibility_embedding [Fintype α] :
    ∃ f : α → ℕ, (∀ x, 0 < f x) ∧ ∀ x y, x ≤ y ↔ f x ∣ f y := by
  classical
  let e := Fintype.equivFin α
  let p : α → ℕ := fun x => Nat.nth Nat.Prime (e x)
  have hp : ∀ x, (p x).Prime := fun x => Nat.prime_nth_prime _
  have hpi : Function.Injective p :=
    (Nat.nth_injective Nat.infinite_setOfPred_prime).comp (fun a b h => e.injective (Fin.ext h))
  let D : α → Finset α := fun x => Finset.univ.filter (· ≤ x)
  have hD : ∀ x y, y ∈ D x ↔ y ≤ x := fun x y => by simp [D]
  refine ⟨fun x => ∏ y ∈ D x, p y, fun x => Finset.prod_pos fun y _ => (hp y).pos, fun x y => ?_⟩
  constructor
  · intro h
    exact Finset.prod_dvd_prod_of_subset _ _ _ fun z hz => (hD _ _).2 (((hD _ _).1 hz).trans h)
  · intro h
    have hx : p x ∣ ∏ z ∈ D y, p z := (Finset.dvd_prod_of_mem _ ((hD x x).2 le_rfl)).trans h
    obtain ⟨w, hw, hdvd⟩ := (hp x).prime.exists_mem_finset_dvd hx
    have : p x = p w := (Nat.prime_dvd_prime_iff_eq (hp x) (hp w)).1 hdvd
    rw [hpi this]
    exact (hD _ _).1 hw

/-- CO-150 (3). Every finite poset is isomorphic to a set of `t`-tuples of reals under the
coordinatewise order, with `t = |α|`: send `x` to the 0-1 indicator vector of `D[x]`. -/
@[kb "kellertrotter2017" "Discussion 6.12, p. 143"]
theorem exists_realTuple_embedding [Fintype α] :
    ∃ f : α → (Fin (Fintype.card α) → ℝ), ∀ x y, x ≤ y ↔ f x ≤ f y := by
  classical
  let e := Fintype.equivFin α
  refine ⟨fun x i => if e.symm i ≤ x then 1 else 0, fun x y => ⟨fun h i => ?_, fun h => ?_⟩⟩
  · by_cases hi : e.symm i ≤ x
    · simp [hi, hi.trans h]
    · simp only [hi, ite_false]
      split_ifs <;> norm_num
  · have := h (e x)
    simp only [Equiv.symm_apply_apply, le_refl, ite_true] at this
    by_contra hxy
    simp only [hxy, ite_false] at this
    norm_num at this

/-! ### Dimension (CO-176) -/

/-- A family of `t` linear orders (as relations) whose intersection is the partial order of `α`:
`x ≤ y` exactly when `x ≤ y` in every one of the linear orders. -/
def IsRealizer {t : ℕ} (r : Fin t → α → α → Prop) : Prop :=
  (∀ i, IsLinearOrder α (r i)) ∧ ∀ x y : α, x ≤ y ↔ ∀ i, r i x y

/-- CO-176. The dimension of a poset: the least `t` such that the poset is the intersection of
`t` linear orders on its ground set. -/
@[kb "kellertrotter2017" "Exercise 6.21, p. 163"]
noncomputable def dimension (α : Type*) [PartialOrder α] : ℕ :=
  sInf {t | ∃ r : Fin t → α → α → Prop, IsRealizer r}

/-- Szpilrajn with a prescribed non-relation: if `¬ x ≤ y` there is a linear order extending the
partial order in which `x` is not below `y`. -/
theorem exists_linearOrder_extension_not_le {x y : α} (h : ¬ x ≤ y) :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ (∀ a b : α, a ≤ b → s a b) ∧ ¬ s x y := by
  let r' : α → α → Prop := fun a b => a ≤ b ∨ (a ≤ y ∧ x ≤ b)
  have hpo : IsPartialOrder α r' :=
    { refl := fun a => Or.inl le_rfl
      trans := by
        rintro a b c (ab | ⟨ay, xb⟩) (bc | ⟨by', xc⟩)
        · exact Or.inl (ab.trans bc)
        · exact Or.inr ⟨ab.trans by', xc⟩
        · exact Or.inr ⟨ay, xb.trans bc⟩
        · exact Or.inr ⟨ay, xc⟩
      antisymm := by
        rintro a b (ab | ⟨ay, xb⟩) (ba | ⟨by', xa⟩)
        · exact le_antisymm ab ba
        · exact absurd (xa.trans (ab.trans by')) h
        · exact absurd (xb.trans (ba.trans ay)) h
        · exact absurd (xa.trans ay) h }
  obtain ⟨s, hs, hrs⟩ := extend_partialOrder r'
  refine ⟨s, hs, fun a b hab => hrs a b (Or.inl hab), fun hxy => ?_⟩
  have hyx : s y x := hrs y x (Or.inr ⟨le_rfl, le_rfl⟩)
  have : x = y := hs.toIsPartialOrder.antisymm _ _ hxy hyx
  exact h this.le

/-- CO-176. The dimension is well defined: every finite poset is the intersection of finitely many
linear orders (extensions of its order, one for each pair `x ≰ y` separating them). -/
@[kb "kellertrotter2017" "Exercise 6.21, p. 163"]
theorem exists_realizer [Finite α] : ∃ (t : ℕ) (r : Fin t → α → α → Prop), IsRealizer r := by
  classical
  let ι := Option {p : α × α // ¬ p.1 ≤ p.2}
  have hsep : ∀ p : {p : α × α // ¬ p.1 ≤ p.2}, ∃ s : α → α → Prop, IsLinearOrder α s ∧
      (∀ a b : α, a ≤ b → s a b) ∧ ¬ s p.1.1 p.1.2 := fun p =>
    exists_linearOrder_extension_not_le p.2
  choose S hS1 hS2 hS3 using hsep
  obtain ⟨s0, hs0, hs0'⟩ := extend_partialOrder ((· ≤ ·) : α → α → Prop)
  let R : ι → α → α → Prop := fun i => match i with
    | none => s0
    | some p => S p
  let e := (Finite.equivFin ι).symm
  refine ⟨Nat.card ι, fun i => R (e i), fun i => ?_, fun x y => ⟨fun hxy i => ?_, fun h => ?_⟩⟩
  · rcases h : e i with _ | p
    · simpa [R, h] using hs0
    · simpa [R, h] using hS1 p
  · rcases h : e i with _ | p
    · simpa [R, h] using hs0' x y hxy
    · simpa [R, h] using hS2 p x y hxy
  · by_contra hxy
    have := h ((Finite.equivFin ι) (some ⟨(x, y), hxy⟩))
    simp only [e, Equiv.symm_apply_apply, R] at this
    exact hS3 ⟨(x, y), hxy⟩ this

/-- CO-150 (4). Every finite poset is isomorphic to (indeed equal to) the intersection of finitely
many linear orders on its ground set (the fourth type of Example 6.7). -/
@[kb "kellertrotter2017" "Discussion 6.12, p. 143"]
theorem exists_linearOrder_intersection [Finite α] :
    ∃ (t : ℕ) (r : Fin t → α → α → Prop), IsRealizer r :=
  exists_realizer

/-- CO-176. The least number of linear orders is attained: a finite poset is the intersection of
exactly `dimension α` linear orders, and not of fewer. -/
@[kb "kellertrotter2017" "Exercise 6.21, p. 163"]
theorem dimension_spec [Finite α] :
    (∃ r : Fin (dimension α) → α → α → Prop, IsRealizer r) ∧
    ∀ (t : ℕ) (r : Fin t → α → α → Prop), IsRealizer r → dimension α ≤ t := by
  obtain ⟨t, r, hr⟩ := exists_realizer (α := α)
  exact ⟨Nat.sInf_mem (s := {t | ∃ r : Fin t → α → α → Prop, IsRealizer r}) ⟨t, r, hr⟩,
    fun t r hr => Nat.sInf_le ⟨r, hr⟩⟩

/-! ### Ranking an injective key -/

/-- A finite type with an injective key into a linear order is ranked by natural numbers
compatibly with the key. -/
theorem exists_rank {β γ : Type*} [Fintype β] [LinearOrder γ] (key : β → γ)
    (hk : Function.Injective key) : ∃ g : β → ℕ, ∀ u v, key u < key v ↔ g u < g v := by
  classical
  have hlt : ∀ u v, key u < key v →
      (univ.filter fun w => key w < key u).card < (univ.filter fun w => key w < key v).card := by
    intro u v h
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨u, by simp [h], by simp⟩
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.trans h
  refine ⟨fun u => (univ.filter fun w => key w < key u).card, fun u v => ⟨hlt u v, fun h => ?_⟩⟩
  by_contra hn
  push Not at hn
  rcases hn.lt_or_eq with hn | hn
  · exact absurd h (not_lt.2 (hlt v u hn).le)
  · have := hk hn
    subst this
    exact lt_irrefl _ h

/-! ### Distinguishing representations (CO-168) -/

/-- CO-168. Every finite interval order has a distinguishing representation: non-degenerate
intervals `[a x, b x]` (`a x < b x`) all of whose `2|α|` endpoints are distinct, with
`x < y ↔ b x < a y`. -/
@[kb "kellertrotter2017" "text (distinguishing representation), p. 152"]
theorem IsIntervalOrder.exists_distinguishing [Fintype α] (h : IsIntervalOrder α) :
    ∃ a b : α → ℝ, (∀ x, a x < b x) ∧ Function.Injective a ∧ Function.Injective b ∧
      (∀ x y, a x ≠ b y) ∧ ∀ x y, x < y ↔ b x < a y := by
  obtain ⟨a, b, hab, hrep⟩ := h
  let ι : α → ℕ := fun x => (Fintype.equivFin α x : ℕ)
  have hι : Function.Injective ι := fun x y hxy =>
    (Fintype.equivFin α).injective (Fin.ext hxy)
  let key : α ⊕ α → ℝ ×ₗ (Bool ×ₗ ℕ) := fun u => match u with
    | Sum.inl x => toLex (a x, toLex (false, ι x))
    | Sum.inr x => toLex (b x, toLex (true, ι x))
  have hk : Function.Injective key := by
    rintro (x | x) (y | y) hxy <;> simp [key] at hxy
    · rw [hι hxy.2]
    · rw [hι hxy.2]
  obtain ⟨g, hg⟩ := exists_rank key hk
  have ginj : ∀ u v, g u = g v → u = v := fun u v huv => by
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (hk h)) with h | h
    · exact absurd huv (ne_of_lt ((hg u v).1 h))
    · exact absurd huv (ne_of_gt ((hg v u).1 h))
  refine ⟨fun x => (g (Sum.inl x) : ℝ), fun x => (g (Sum.inr x) : ℝ), fun x => ?_, ?_, ?_, ?_,
    fun x y => ?_⟩
  · rw [Nat.cast_lt, ← hg]
    simp only [key, Prod.Lex.toLex_lt_toLex]
    rcases (hab x).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl (by simp)⟩
  · intro x y hxy
    have := ginj (Sum.inl x) (Sum.inl y) (Nat.cast_injective hxy)
    simpa using this
  · intro x y hxy
    have := ginj (Sum.inr x) (Sum.inr y) (Nat.cast_injective hxy)
    simpa using this
  · intro x y hxy
    have := ginj (Sum.inl x) (Sum.inr y) (Nat.cast_injective hxy)
    simp at this
  · rw [hrep x y, Nat.cast_lt, ← hg]
    simp only [key, Prod.Lex.toLex_lt_toLex]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | ⟨-, h⟩)
      · exact h
      · rcases h with h | ⟨h, -⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)

end UndergradKB.Combinatorics.Order
