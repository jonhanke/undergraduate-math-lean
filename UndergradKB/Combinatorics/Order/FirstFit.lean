import Mathlib.Order.Antichain
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Prod.Lex.Basic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.Basic
import UndergradKB.Combinatorics.Order.Dilworth
import UndergradKB.Combinatorics.Order.IntervalOrder
import UndergradKB.Combinatorics.Order.Posets2

/-!
# First Fit chain partitioning (Keller--Trotter, Section 6.7)

The points of a finite poset are processed in the order given by an injective position map
`σ : α → ℕ`; each point goes to the first chain (chains are numbered `0, 1, 2, ...`) in which it
is comparable to every point already placed there. The index of the chain of `x` is defined by
well-founded recursion on `σ x`.
-/

namespace UndergradKB.Combinatorics.Order

variable {α : Type*} [PartialOrder α]

/-- CO-174. **First Fit** on chains. Points are processed in the order of `σ`; the chain index of
`x` is the least `j` such that `x` is comparable to every earlier point already placed in
chain `j`. -/
@[kb "kellertrotter2017" "text (First Fit), p. 156"]
noncomputable def firstFit (σ : α → ℕ) (x : α) : ℕ :=
  sInf {j | ∀ y : α, ∀ _ : σ y < σ x, firstFit σ y = j → (x ≤ y ∨ y ≤ x)}
termination_by σ x
decreasing_by assumption

theorem firstFit_eq (σ : α → ℕ) (x : α) :
    firstFit σ x = sInf {j | ∀ y : α, ∀ _ : σ y < σ x, firstFit σ y = j → (x ≤ y ∨ y ≤ x)} := by
  rw [firstFit]

theorem firstFit_set_nonempty [Finite α] (σ : α → ℕ) (x : α) :
    {j | ∀ y : α, ∀ _ : σ y < σ x, firstFit σ y = j → (x ≤ y ∨ y ≤ x)}.Nonempty := by
  obtain ⟨B, hB⟩ := (Set.finite_range (firstFit σ)).bddAbove
  refine ⟨B + 1, fun y _ h => ?_⟩
  have := hB (Set.mem_range_self y)
  omega

/-- A point is comparable to every earlier point of its own chain. -/
theorem firstFit_comparable [Finite α] (σ : α → ℕ) {x y : α} (h : σ y < σ x)
    (hxy : firstFit σ y = firstFit σ x) : x ≤ y ∨ y ≤ x :=
  Nat.sInf_mem (firstFit_set_nonempty σ x) y h (hxy.trans (firstFit_eq σ x))

/-- First Fit is first: if `j` is smaller than the chain of `x`, then chain `j` already holds an
earlier point incomparable to `x`. -/
theorem firstFit_least [Finite α] (σ : α → ℕ) {x : α} {j : ℕ} (hj : j < firstFit σ x) :
    ∃ y, σ y < σ x ∧ firstFit σ y = j ∧ ¬ (x ≤ y ∨ y ≤ x) := by
  have := Nat.notMem_of_lt_sInf (firstFit_eq σ x ▸ hj)
  simp only [Set.mem_ofPred_eq, not_forall] at this
  obtain ⟨y, h1, h2, h3⟩ := this
  exact ⟨y, h1, h2, h3⟩

/-- CO-174. The output of First Fit is a chain partition: the points sent to one index form a
chain. -/
@[kb "kellertrotter2017" "text (First Fit), p. 156"]
theorem firstFit_isChain [Finite α] {σ : α → ℕ} (hσ : Function.Injective σ) (i : ℕ) :
    IsChain (· ≤ ·) (firstFit σ ⁻¹' {i}) := by
  intro x hx y hy hne
  have hx' : firstFit σ x = i := hx
  have hy' : firstFit σ y = i := hy
  rcases lt_or_gt_of_ne (fun h => hne (hσ h)) with h | h
  · exact (firstFit_comparable σ h (hx'.trans hy'.symm)).symm
  · exact firstFit_comparable σ h (hy'.trans hx'.symm)

/-- CO-174. First Fit on a finite poset yields a partition into `n` chains (`n` the number of
indices used), labelled by the First Fit index. -/
@[kb "kellertrotter2017" "text (First Fit), p. 156"]
theorem firstFit_chain_partition [Fintype α] {σ : α → ℕ} (hσ : Function.Injective σ) :
    ∃ (n : ℕ) (g : α → Fin n), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) ∧
      ∀ x, (g x : ℕ) = firstFit σ x := by
  classical
  refine ⟨Finset.univ.sup (firstFit σ) + 1,
    fun x => ⟨firstFit σ x, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ x))⟩, fun i => ?_,
    fun x => rfl⟩
  refine (firstFit_isChain hσ i).mono ?_
  intro z hz
  exact congrArg Fin.val hz

/-- If `x` is placed in chain `j`, then `x` together with the earlier points that block the chains
`0, ..., j-1` form an antichain of size `j + 1` when the poset is an interval order and the points
are processed by non-decreasing left endpoint. Hence the chain index of every point is below the
width. -/
theorem firstFit_lt_width [Fintype α] {σ : α → ℕ} (a b : α → ℝ)
    (hrep : ∀ x y, x < y ↔ b x < a y) (hσa : ∀ x y, σ x < σ y → a x ≤ a y) (x : α) :
    firstFit σ x < width α := by
  classical
  have hy : ∀ j, j < firstFit σ x → ∃ y, σ y < σ x ∧ firstFit σ y = j ∧ ¬ (x ≤ y ∨ y ≤ x) :=
    fun j hj => firstFit_least σ hj
  have : Nonempty α := ⟨x⟩
  choose! Y hY1 hY2 hY3 using hy
  set s : Finset α := insert x ((Finset.range (firstFit σ x)).image Y) with hs
  have hxn : x ∉ (Finset.range (firstFit σ x)).image Y := by
    intro h
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 h
    have := hY2 j (Finset.mem_range.1 hj)
    rw [hjx] at this
    have := Finset.mem_range.1 hj
    omega
  have hinj : Set.InjOn Y (Finset.range (firstFit σ x) : Set ℕ) := by
    intro j hj k hk hjk
    have h1 := hY2 j (Finset.mem_range.1 hj)
    have h2 := hY2 k (Finset.mem_range.1 hk)
    rw [← h1, ← h2, hjk]
  have hcard : s.card = firstFit σ x + 1 := by
    rw [hs, Finset.card_insert_of_notMem hxn, Finset.card_image_of_injOn hinj, Finset.card_range]
  -- every blocking point contains the left endpoint of `x`
  have hcont : ∀ j, j < firstFit σ x → a (Y j) ≤ a x ∧ a x ≤ b (Y j) := by
    intro j hj
    refine ⟨hσa _ _ (hY1 j hj), ?_⟩
    by_contra hcon
    push Not at hcon
    exact hY3 j hj (Or.inr (((hrep _ _).2 hcon).le))
  have hanti : IsAntichain (· ≤ ·) (s : Set α) := by
    have hinc : ∀ j, j < firstFit σ x → ¬ x ≤ Y j ∧ ¬ Y j ≤ x := fun j hj => by
      have := hY3 j hj
      tauto
    intro u hu v hv huv hle
    simp only [hs, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe, Finset.mem_range] at hu hv
    rcases hu with rfl | ⟨j, hj, rfl⟩ <;> rcases hv with rfl | ⟨k, hk, rfl⟩
    · exact huv rfl
    · exact (hinc k hk).1 hle
    · exact (hinc j hj).2 hle
    · have h1 := (hrep _ _).1 (lt_of_le_of_ne hle huv)
      have h2 := hcont j hj
      have h3 := hcont k hk
      linarith [h2.2, h3.1]
  have := card_le_width hanti
  omega

omit [PartialOrder α] in
/-- The order in which First Fit processes the points of an interval order: by left endpoint, ties
broken by an arbitrary enumeration. -/
theorem exists_leftEndpoint_order [Fintype α] (a : α → ℝ) :
    ∃ σ : α → ℕ, Function.Injective σ ∧ ∀ x y, σ x < σ y → a x ≤ a y := by
  let ι : α → ℕ := fun x => (Fintype.equivFin α x : ℕ)
  have hι : Function.Injective ι := fun x y hxy =>
    (Fintype.equivFin α).injective (Fin.ext hxy)
  let key : α → ℝ ×ₗ ℕ := fun x => toLex (a x, ι x)
  have hk : Function.Injective key := by
    intro x y hxy
    simp only [key, toLex_inj, Prod.mk.injEq] at hxy
    exact hι hxy.2
  obtain ⟨g, hg⟩ := exists_rank key hk
  refine ⟨g, fun x y hxy => ?_, fun x y hxy => ?_⟩
  · by_contra hne
    rcases lt_or_gt_of_ne (a := key x) (b := key y) (fun h => hne (hk h)) with h | h
    · exact absurd hxy (ne_of_lt ((hg x y).1 h))
    · exact absurd hxy (ne_of_gt ((hg y x).1 h))
  · have := (hg x y).2 hxy
    simp only [key, Prod.Lex.toLex_lt_toLex] at this
    rcases this with h | ⟨h, -⟩
    · exact h.le
    · exact h.le

/-- CO-173. **First Fit is optimal on interval orders.** For an interval order, processing the
points by non-decreasing left endpoint, First Fit partitions the poset into exactly `width(P)`
chains (the width equals the chromatic number of the interval graph of the incomparability
relation). -/
@[kb "kellertrotter2017" "text (interval orders and First Fit), p. 155"]
theorem IsIntervalOrder.firstFit_optimal [Fintype α] (h : IsIntervalOrder α) :
    ∃ σ : α → ℕ, Function.Injective σ ∧
      ∃ g : α → Fin (width α), (∀ i, IsChain (· ≤ ·) (g ⁻¹' {i})) ∧
        ∀ x, (g x : ℕ) = firstFit σ x := by
  obtain ⟨a, b, -, hrep⟩ := h
  obtain ⟨σ, hσ, hσa⟩ := exists_leftEndpoint_order a
  refine ⟨σ, hσ, fun x => ⟨firstFit σ x, firstFit_lt_width a b hrep hσa x⟩, fun i => ?_,
    fun x => rfl⟩
  refine (firstFit_isChain hσ i).mono ?_
  intro z hz
  exact congrArg Fin.val hz

end UndergradKB.Combinatorics.Order
