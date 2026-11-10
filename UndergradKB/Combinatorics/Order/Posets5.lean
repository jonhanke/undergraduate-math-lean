import Mathlib.Order.Interval.Finset.Nat
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.IntervalOrder
import UndergradKB.Combinatorics.Order.Posets4
import UndergradKB.Combinatorics.Order.FirstFit
import UndergradKB.Combinatorics.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Integer interval representations (Keller--Trotter, Theorem 6.30, part 4)

Source: Keller--Trotter, *Applied Combinatorics* (2017), p. 154.  A representation of an interval
order with integer endpoints in `[n]` needs `n ≥ d`, where `d` is the number of distinct down sets;
there is one with `n = d` (`downIndex`, `upIndex`), and it is the only one.
-/

namespace UndergradKB.Combinatorics.Order

open Finset
open scoped Classical

variable {α : Type*} [PartialOrder α]

/-- CO-172. An interval representation with integer endpoints in `[n] = {1, ..., n}`: point `x`
gets the interval `[a x, b x]`, and `x < y` exactly when the interval of `x` lies entirely to the
left of that of `y`. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
def IsIntRep (n : ℕ) (a b : α → ℕ) : Prop :=
  (∀ x, 1 ≤ a x ∧ a x ≤ b x ∧ b x ≤ n) ∧ ∀ x y, x < y ↔ b x < a y

variable [Fintype α]

/-- The down set cut off at the threshold `v`: `{y : b y < v}`. -/
noncomputable def dnCut (b : α → ℕ) (v : ℕ) : Finset α := univ.filter fun y => b y < v

/-- The up set cut off at the threshold `v`: `{z : v < a z}`. -/
noncomputable def upCut (a : α → ℕ) (v : ℕ) : Finset α := univ.filter fun z => v < a z

section Rep

variable {n : ℕ} {a b : α → ℕ}

lemma IsIntRep.dnFin_eq (h : IsIntRep n a b) (x : α) : dnFin x = dnCut b (a x) := by
  ext y; simp [dnCut, h.2 y x]

lemma IsIntRep.upFin_eq (h : IsIntRep n a b) (x : α) : upFin x = upCut a (b x) := by
  ext z; simp [upCut, h.2 x z]

lemma IsIntRep.image_a_sub (h : IsIntRep n a b) : univ.image a ⊆ Icc 1 n := by
  intro v hv
  obtain ⟨x, -, rfl⟩ := mem_image.1 hv
  have := h.1 x
  simp only [mem_Icc]; omega

lemma IsIntRep.image_b_sub (h : IsIntRep n a b) : univ.image b ⊆ Icc 1 n := by
  intro v hv
  obtain ⟨x, -, rfl⟩ := mem_image.1 hv
  have := h.1 x
  simp only [mem_Icc]; omega

lemma IsIntRep.dnFins_sub (h : IsIntRep n a b) :
    dnFins α ⊆ (univ.image a).image (dnCut b) := by
  intro s hs
  obtain ⟨x, -, rfl⟩ := mem_image.1 hs
  exact mem_image.2 ⟨a x, mem_image.2 ⟨x, mem_univ _, rfl⟩, (h.dnFin_eq x).symm⟩

/-- CO-172 (Theorem 6.30, part 4, lower bound). Any integer representation with endpoints in `[n]`
has `n ≥ d`, where `d` is the number of distinct down sets. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem IsIntRep.card_dnFins_le (h : IsIntRep n a b) : (dnFins α).card ≤ n :=
  calc (dnFins α).card ≤ ((univ.image a).image (dnCut b)).card := card_le_card h.dnFins_sub
    _ ≤ (univ.image a).card := card_image_le
    _ ≤ (Icc 1 n).card := card_le_card h.image_a_sub
    _ = n := by simp

lemma IsIntRep.image_a_eq (h : IsIntRep n a b) (hd : n = (dnFins α).card) :
    univ.image a = Icc 1 n ∧ Set.InjOn (dnCut b) (univ.image a : Set ℕ) := by
  have h1 : (dnFins α).card ≤ ((univ.image a).image (dnCut b)).card :=
    card_le_card h.dnFins_sub
  have h2 : ((univ.image a).image (dnCut b)).card ≤ (univ.image a).card := card_image_le
  have h3 : (univ.image a).card ≤ n :=
    (card_le_card h.image_a_sub).trans (by simp)
  have hA : (univ.image a).card = n := by omega
  have hf : ((univ.image a).image (dnCut b)).card = (univ.image a).card := by omega
  refine ⟨eq_of_subset_of_card_le h.image_a_sub (by simp [hA]), ?_⟩
  exact Finset.card_image_iff.1 hf

lemma IsIntRep.a_lt_iff (h : IsIntRep n a b) (hd : n = (dnFins α).card) (x y : α) :
    a x < a y ↔ dnFin x ⊂ dnFin y := by
  obtain ⟨hA, hinj⟩ := h.image_a_eq hd
  rw [h.dnFin_eq, h.dnFin_eq]
  constructor
  · intro hlt
    refine Finset.ssubset_iff_subset_ne.2 ⟨fun z hz => ?_, fun e => ?_⟩
    · simp only [dnCut, mem_filter, mem_univ, true_and] at hz ⊢
      omega
    · have := hinj (Finset.mem_coe.2 (mem_image.2 ⟨x, mem_univ _, rfl⟩))
        (Finset.mem_coe.2 (mem_image.2 ⟨y, mem_univ _, rfl⟩)) e
      omega
  · intro hss
    by_contra hle
    push Not at hle
    have hsub : dnCut b (a y) ⊆ dnCut b (a x) := fun z hz => by
      simp only [dnCut, mem_filter, mem_univ, true_and] at hz ⊢
      omega
    exact hss.ne (Finset.Subset.antisymm hss.subset hsub)

lemma IsIntRep.downIndex_eq (h : IsIntRep n a b) (hd : n = (dnFins α).card) (x : α) :
    downIndex x = a x := by
  obtain ⟨hA, hinj⟩ := h.image_a_eq hd
  have hx := h.1 x
  have hcard : ((dnFins α).filter (· ⊂ dnFin x)).card = ((Icc 1 n).filter (· < a x)).card := by
    symm
    refine Finset.card_bij (fun v _ => dnCut b v) ?_ ?_ ?_
    · intro v hv
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      rw [← hA] at hv1
      obtain ⟨w, -, rfl⟩ := mem_image.1 hv1
      rw [← h.dnFin_eq]
      exact mem_filter.2 ⟨mem_image.2 ⟨w, mem_univ _, rfl⟩, (h.a_lt_iff hd w x).1 hv2⟩
    · intro v hv w hw e
      rw [← hA] at *
      exact hinj (Finset.mem_coe.2 (by rw [hA]; exact (mem_filter.1 hv).1))
        (Finset.mem_coe.2 (by rw [hA]; exact (mem_filter.1 hw).1)) e
    · intro s hs
      obtain ⟨hs1, hs2⟩ := mem_filter.1 hs
      obtain ⟨w, -, rfl⟩ := mem_image.1 hs1
      refine ⟨a w, mem_filter.2 ⟨?_, (h.a_lt_iff hd w x).2 hs2⟩, (h.dnFin_eq w).symm⟩
      exact h.image_a_sub (mem_image.2 ⟨w, mem_univ _, rfl⟩)
  have hIco : (Icc 1 n).filter (· < a x) = Ico 1 (a x) := by
    ext v; simp only [mem_filter, mem_Icc, mem_Ico]; omega
  rw [downIndex, hcard, hIco, Nat.card_Ico]
  omega

lemma IsIntRep.upFin_sub_iff (h : IsIntRep n a b) (hd : n = (dnFins α).card) (x y : α) :
    upFin x ⊆ upFin y ↔ b y ≤ b x := by
  obtain ⟨hA, -⟩ := h.image_a_eq hd
  rw [h.upFin_eq, h.upFin_eq]
  constructor
  · intro hsub
    by_contra hlt
    push Not at hlt
    have hy := h.1 y
    have : b x + 1 ∈ univ.image a := by
      rw [hA]; simp only [mem_Icc]; have := h.1 x; omega
    obtain ⟨z, -, hz⟩ := mem_image.1 this
    have hz1 : z ∈ upCut a (b x) := by simp [upCut, hz]
    have hz2 := hsub hz1
    simp only [upCut, mem_filter, mem_univ, true_and] at hz2
    omega
  · intro hle z hz
    simp only [upCut, mem_filter, mem_univ, true_and] at hz ⊢
    omega

lemma IsIntRep.upFin_ssub_iff (h : IsIntRep n a b) (hd : n = (dnFins α).card) (x y : α) :
    upFin x ⊂ upFin y ↔ b y < b x := by
  rw [Finset.ssubset_def, h.upFin_sub_iff hd, h.upFin_sub_iff hd]
  omega

lemma IsIntRep.image_b_eq (h : IsIntRep n a b) (hne : ¬ ContainsPoset α (Fin 2 ⊕ Fin 2))
    (hd : n = (dnFins α).card) : univ.image b = Icc 1 n := by
  have hu : (upFins α).card = n := by rw [hd]; exact (card_dnFins_eq_card_upFins hne).symm
  have hsub : upFins α ⊆ (univ.image b).image (upCut a) := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := mem_image.1 hs
    exact mem_image.2 ⟨b x, mem_image.2 ⟨x, mem_univ _, rfl⟩, (h.upFin_eq x).symm⟩
  have h1 : n ≤ (univ.image b).card :=
    hu ▸ (card_le_card hsub).trans card_image_le
  exact eq_of_subset_of_card_le h.image_b_sub (by simp; omega)

lemma IsIntRep.upIndex_eq (h : IsIntRep n a b) (hne : ¬ ContainsPoset α (Fin 2 ⊕ Fin 2))
    (hd : n = (dnFins α).card) (x : α) : upIndex x = b x := by
  have hB := h.image_b_eq hne hd
  have hx := h.1 x
  have hcard : ((upFins α).filter (upFin x ⊂ ·)).card = ((Icc 1 n).filter (· < b x)).card := by
    symm
    refine Finset.card_bij (fun v _ => upCut a v) ?_ ?_ ?_
    · intro v hv
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      rw [← hB] at hv1
      obtain ⟨w, -, rfl⟩ := mem_image.1 hv1
      rw [← h.upFin_eq]
      exact mem_filter.2 ⟨mem_image.2 ⟨w, mem_univ _, rfl⟩, (h.upFin_ssub_iff hd x w).2 hv2⟩
    · intro v hv v' hv' e
      have hv1 := (mem_filter.1 hv).1
      have hv1' := (mem_filter.1 hv').1
      rw [← hB] at hv1 hv1'
      obtain ⟨w, -, rfl⟩ := mem_image.1 hv1
      obtain ⟨w', -, rfl⟩ := mem_image.1 hv1'
      rw [← h.upFin_eq, ← h.upFin_eq] at e
      have e1 := (h.upFin_sub_iff hd w w').1 e.subset
      have e2 := (h.upFin_sub_iff hd w' w).1 e.symm.subset
      omega
    · intro s hs
      obtain ⟨hs1, hs2⟩ := mem_filter.1 hs
      obtain ⟨w, -, rfl⟩ := mem_image.1 hs1
      refine ⟨b w, mem_filter.2 ⟨?_, (h.upFin_ssub_iff hd x w).1 hs2⟩, (h.upFin_eq w).symm⟩
      exact h.image_b_sub (mem_image.2 ⟨w, mem_univ _, rfl⟩)
  have hIco : (Icc 1 n).filter (· < b x) = Ico 1 (b x) := by
    ext v; simp only [mem_filter, mem_Icc, mem_Ico]; omega
  rw [upIndex, hcard, hIco, Nat.card_Ico]
  omega

end Rep

section Main

omit [Fintype α] in
/-- An integer interval representation makes the poset an interval order. -/
lemma IsIntRep.not_containsPoset {n : ℕ} {a b : α → ℕ} (h : IsIntRep n a b) :
    ¬ ContainsPoset α (Fin 2 ⊕ Fin 2) := by
  refine IsIntervalOrder.not_containsPoset ⟨fun x => (a x : ℝ), fun x => (b x : ℝ),
    fun x => by show (a x : ℝ) ≤ b x; exact_mod_cast (h.1 x).2.1, fun x y => ?_⟩
  rw [h.2 x y]
  exact (Nat.cast_lt (α := ℝ)).symm

/-- CO-172 (Theorem 6.30, part 4, existence). In a finite poset excluding `2 + 2`, the book's
intervals `[downIndex x, upIndex x]` form an integer representation with endpoints in `[d]`,
`d` the number of distinct down sets. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem isIntRep_downIndex_upIndex (hne : ¬ ContainsPoset α (Fin 2 ⊕ Fin 2)) :
    IsIntRep (dnFins α).card (downIndex (α := α)) (upIndex (α := α)) := by
  refine ⟨fun x => ⟨Nat.le_add_left _ _, downIndex_le_upIndex hne x, ?_⟩,
    lt_iff_upIndex_lt_downIndex hne⟩
  rw [card_dnFins_eq_card_upFins hne, upIndex]
  refine Nat.succ_le_of_lt (Finset.card_lt_card ?_)
  refine (Finset.filter_ssubset).2 ⟨upFin x, mem_image.2 ⟨x, mem_univ _, rfl⟩, ?_⟩
  simp

/-- CO-172 (Theorem 6.30, part 4, minimality). `d` is the least `n` for which an integer
representation with endpoints in `[n]` exists. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem dnFins_card_le_of_isIntRep {n : ℕ} {a b : α → ℕ} (h : IsIntRep n a b) :
    (dnFins α).card ≤ n := h.card_dnFins_le

/-- CO-172 (Theorem 6.30, part 4, uniqueness). Any integer representation with endpoints in
`[d]`, `d` the number of distinct down sets, is the book's: `a = downIndex`, `b = upIndex`. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem isIntRep_unique {a b : α → ℕ} (h : IsIntRep (dnFins α).card a b) :
    a = downIndex ∧ b = upIndex :=
  ⟨funext fun x => (h.downIndex_eq rfl x).symm,
    funext fun x => (h.upIndex_eq h.not_containsPoset rfl x).symm⟩

end Main

/-! ### CO-175: First Fit can be forced to use arbitrarily many antichains / chains -/

section FirstFitBad

/-- `sInf` of a set of naturals that contains `i` but no smaller number is `i`. -/
lemma sInf_eq_of_least {S : Set ℕ} {i : ℕ} (hi : i ∈ S) (hlt : ∀ j < i, j ∉ S) : sInf S = i :=
  le_antisymm (Nat.sInf_le hi) (by
    by_contra h
    push Not at h
    exact hlt _ h (Nat.sInf_mem ⟨i, hi⟩))

variable {β : Type*} [PartialOrder β]

/-- CO-175. **First Fit on antichains.** Points are processed in the order of `σ`; the antichain
index of `x` is the least `j` such that `x` is incomparable to every earlier point already placed
in antichain `j`. -/
@[kb "kellertrotter2017" "Example 6.32, p. 156"]
noncomputable def firstFitAnti (σ : β → ℕ) (x : β) : ℕ :=
  sInf {j | ∀ y : β, ∀ _ : σ y < σ x, firstFitAnti σ y = j → (¬ x ≤ y ∧ ¬ y ≤ x)}
termination_by σ x
decreasing_by assumption

theorem firstFitAnti_eq (σ : β → ℕ) (x : β) :
    firstFitAnti σ x = sInf {j | ∀ y : β, ∀ _ : σ y < σ x, firstFitAnti σ y = j →
      (¬ x ≤ y ∧ ¬ y ≤ x)} := by
  rw [firstFitAnti]

/-! #### Height 2, arbitrarily many antichains -/

/-- The points of the height-2 poset: `bot i = x_i` (bottom) and `top i = y_i` (top). -/
inductive TwoLevel (t : ℕ) : Type
  | bot (i : Fin t) : TwoLevel t
  | top (i : Fin t) : TwoLevel t

namespace TwoLevel

/-- The height-2 poset: `x_i < y_j` exactly when `i ≠ j`, and no other strict relations. -/
instance (t : ℕ) : PartialOrder (TwoLevel t) where
  le a b := a = b ∨ ∃ i j : Fin t, a = bot i ∧ b = top j ∧ i ≠ j
  le_refl a := Or.inl rfl
  le_trans a b c h1 h2 := by
    rcases h1 with rfl | ⟨i, j, rfl, rfl, hij⟩
    · exact h2
    · rcases h2 with h2 | ⟨i', j', h, -, -⟩
      · subst h2; exact Or.inr ⟨i, j, rfl, rfl, hij⟩
      · cases h
  le_antisymm a b h1 h2 := by
    rcases h1 with rfl | ⟨i, j, rfl, rfl, hij⟩
    · rfl
    · rcases h2 with h2 | ⟨i', j', h, -, -⟩
      · exact h2.symm
      · cases h

instance (t : ℕ) : Finite (TwoLevel t) :=
  Finite.of_injective (fun a : TwoLevel t => match a with | bot i => Sum.inl i | top i => Sum.inr i)
    (by intro a b h; cases a <;> cases b <;> simp_all)

lemma le_iff {t : ℕ} (a b : TwoLevel t) :
    a ≤ b ↔ a = b ∨ ∃ i j : Fin t, a = bot i ∧ b = top j ∧ i ≠ j := Iff.rfl

/-- The processing order `x_0, y_0, x_1, y_1, ...`. -/
def pos {t : ℕ} : TwoLevel t → ℕ
  | bot i => 2 * i
  | top i => 2 * i + 1

/-- The index `i` of `x_i` or `y_i`. -/
def idx {t : ℕ} : TwoLevel t → ℕ
  | bot i => i
  | top i => i

lemma pos_injective {t : ℕ} : Function.Injective (pos (t := t)) := by
  intro a b h
  cases a <;> cases b <;> simp only [pos] at h
  · exact congrArg bot (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg top (Fin.ext (by omega))

lemma bot_le_top {t : ℕ} {i j : Fin t} (h : i ≠ j) : (bot i : TwoLevel t) ≤ top j :=
  Or.inr ⟨i, j, rfl, rfl, h⟩

lemma not_bot_le_top_self {t : ℕ} (i : Fin t) : ¬ (bot i : TwoLevel t) ≤ top i := by
  rintro (h | ⟨i', j', h1, h2, h3⟩)
  · cases h
  · cases h1; cases h2; exact h3 rfl

lemma not_top_le_bot {t : ℕ} (i j : Fin t) : ¬ (top i : TwoLevel t) ≤ bot j := by
  rintro (h | ⟨i', j', h1, h2, h3⟩)
  · cases h
  · cases h1

end TwoLevel

/-- CO-175. The poset `TwoLevel t` has height 2: it has no chain `a < b < c`. -/
@[kb "kellertrotter2017" "Example 6.32, p. 156"]
theorem twoLevel_no_three_chain {t : ℕ} : ¬ ∃ a b c : TwoLevel t, a < b ∧ b < c := by
  rintro ⟨a, b, c, hab, hbc⟩
  have h1 := hab.le
  have h2 := hbc.le
  rw [TwoLevel.le_iff] at h1 h2
  rcases h1 with rfl | ⟨i, j, rfl, rfl, hij⟩
  · exact lt_irrefl _ hab
  · rcases h2 with rfl | ⟨i', j', h, -, -⟩
    · exact lt_irrefl _ hbc
    · cases h

/-- CO-175 (antichain half). On the height-2 poset `TwoLevel t`, First Fit on antichains, with the
points taken in the order `x_0, y_0, x_1, y_1, ...`, puts both `x_i` and `y_i` into antichain `i`;
so it uses `t` antichains although the height is 2. -/
@[kb "kellertrotter2017" "Example 6.32, p. 156"]
theorem firstFitAnti_twoLevel (t : ℕ) (a : TwoLevel t) :
    firstFitAnti (TwoLevel.pos (t := t)) a = a.idx := by
  have key : ∀ n : ℕ, ∀ a : TwoLevel t, a.pos = n → firstFitAnti (TwoLevel.pos (t := t)) a = a.idx := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha
      have ih' : ∀ y : TwoLevel t, y.pos < a.pos →
          firstFitAnti (TwoLevel.pos (t := t)) y = y.idx :=
        fun y hy => ih _ (ha ▸ hy) y rfl
      rw [firstFitAnti_eq]
      rcases a with i | i
      · apply sInf_eq_of_least
        · intro y hy hff
          rw [ih' y hy] at hff
          rcases y with m | m <;> simp only [TwoLevel.pos, TwoLevel.idx] at hy hff
          · omega
          · omega
        · intro j hj hmem
          simp only [TwoLevel.idx] at hj
          have hjt : j < t := by have := i.2; omega
          have := hmem (TwoLevel.top ⟨j, hjt⟩) (by simp only [TwoLevel.pos]; omega)
            (by rw [ih']
                · simp only [TwoLevel.idx]
                · simp only [TwoLevel.pos]; omega)
          exact this.1 (TwoLevel.bot_le_top
            (by intro h; have := congrArg Fin.val h; simp at this; omega))
      · apply sInf_eq_of_least
        · intro y hy hff
          rw [ih' y hy] at hff
          rcases y with m | m <;> simp only [TwoLevel.pos, TwoLevel.idx] at hy hff
          · have hm : m = i := Fin.ext (by omega)
            subst hm
            exact ⟨TwoLevel.not_top_le_bot _ _, TwoLevel.not_bot_le_top_self _⟩
          · omega
        · intro j hj hmem
          simp only [TwoLevel.idx] at hj
          have hjt : j < t := by have := i.2; omega
          have := hmem (TwoLevel.bot ⟨j, hjt⟩) (by simp only [TwoLevel.pos]; omega)
            (by rw [ih']
                · simp only [TwoLevel.idx]
                · simp only [TwoLevel.pos]; omega)
          exact this.2 (TwoLevel.bot_le_top
            (by intro h; have := congrArg Fin.val h; simp at this; omega))
  exact key _ a rfl

/-! #### Width 2, arbitrarily many chains -/

/-- The strict order of the width-2 construction between the point `(m, c)` and the point
`(l, j)`: levels two or more apart are comparable (lower below higher); between adjacent levels
`(m, c) < (m+1, j)` iff `j ≤ c`; inside a level the order is reversed: `(l, j) < (l, c)` iff
`c < j` (the point with the smaller second coordinate is higher). -/
def ffLt (m c l j : ℕ) : Prop := m + 1 < l ∨ (m + 1 = l ∧ j ≤ c) ∨ (m = l ∧ j < c)

/-- CO-175. The points `(ℓ, i)` with `0 ≤ i ≤ ℓ < t` of the width-2 construction. -/
def WidthTwo (t : ℕ) : Type := {p : ℕ × ℕ // p.2 ≤ p.1 ∧ p.1 < t}

namespace WidthTwo

variable {t : ℕ}

/-- `x ≤ y` in the width-2 construction. -/
def Le (x y : WidthTwo t) : Prop :=
  (x.1.1 = y.1.1 ∧ x.1.2 = y.1.2) ∨ ffLt x.1.1 x.1.2 y.1.1 y.1.2

instance (t : ℕ) : PartialOrder (WidthTwo t) where
  le := Le
  le_refl x := Or.inl ⟨rfl, rfl⟩
  le_trans x y z h1 h2 := by
    have h1 : Le x y := h1
    have h2 : Le y z := h2
    show Le x z
    unfold Le ffLt at *
    omega
  le_antisymm x y h1 h2 := by
    have h1 : Le x y := h1
    have h2 : Le y x := h2
    unfold Le ffLt at *
    exact Subtype.ext (Prod.ext (by omega) (by omega))

instance (t : ℕ) : Finite (WidthTwo t) :=
  Finite.of_injective
    (fun x : WidthTwo t => ((⟨x.1.1, x.2.2⟩ : Fin t), (⟨x.1.2, lt_of_le_of_lt x.2.1 x.2.2⟩ : Fin t)))
    (by
      intro x y h
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2))

lemma le_iff (x y : WidthTwo t) :
    x ≤ y ↔ (x.1.1 = y.1.1 ∧ x.1.2 = y.1.2) ∨ ffLt x.1.1 x.1.2 y.1.1 y.1.2 := Iff.rfl

/-- The processing order: level by level, and inside level `ℓ` first `(ℓ, ℓ)` and then
`(ℓ, 0), (ℓ, 1), ..., (ℓ, ℓ-1)`. -/
def pos (t : ℕ) (x : WidthTwo t) : ℕ :=
  (t + 1) * x.1.1 + (if x.1.2 = x.1.1 then 0 else x.1.2 + 1)

lemma pos_lt_of_level_lt {x y : WidthTwo t} (h : x.1.1 < y.1.1) : pos t x < pos t y := by
  have h1 : (t + 1) * (x.1.1 + 1) ≤ (t + 1) * y.1.1 := Nat.mul_le_mul_left _ h
  rw [Nat.mul_succ] at h1
  have hx := x.2
  unfold pos
  generalize (t + 1) * x.1.1 = A at *
  generalize (t + 1) * y.1.1 = B at *
  split_ifs <;> omega

lemma level_le_of_pos_lt {x y : WidthTwo t} (h : pos t x < pos t y) : x.1.1 ≤ y.1.1 := by
  by_contra hc
  push Not at hc
  exact absurd (pos_lt_of_level_lt hc) (not_lt.2 h.le)

lemma pos_injective : Function.Injective (pos t) := by
  intro x y h
  have hl : x.1.1 = y.1.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd h (pos_lt_of_level_lt hlt).ne
    · exact absurd h (pos_lt_of_level_lt hgt).ne.symm
  have hx := x.2
  have hy := y.2
  have hm : (t + 1) * x.1.1 = (t + 1) * y.1.1 := by rw [hl]
  unfold pos at h
  refine Subtype.ext (Prod.ext hl ?_)
  split_ifs at h <;> omega

end WidthTwo

/-- CO-175. The poset `WidthTwo t` has no three pairwise incomparable points. -/
@[kb "kellertrotter2017" "Example 6.32, p. 156"]
theorem widthTwo_no_three_antichain {t : ℕ} :
    ¬ ∃ x y z : WidthTwo t, (¬ x ≤ y ∧ ¬ y ≤ x) ∧ (¬ x ≤ z ∧ ¬ z ≤ x) ∧ (¬ y ≤ z ∧ ¬ z ≤ y) := by
  rintro ⟨x, y, z, ⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
  rw [WidthTwo.le_iff] at h1 h2 h3 h4 h5 h6
  unfold ffLt at *
  omega

/-- CO-175. The width of `WidthTwo t` is at most 2. -/
@[kb "kellertrotter2017" "Example 6.32, p. 156"]
theorem widthTwo_width_le {t : ℕ} [Fintype (WidthTwo t)] : width (WidthTwo t) ≤ 2 := by
  classical
  obtain ⟨s, hs, hc⟩ := exists_antichain_card_eq_width (α := WidthTwo t)
  by_contra h
  push Not at h
  rw [← hc] at h
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.1 h
  exact widthTwo_no_three_antichain ⟨a, b, c,
    ⟨hs ha hb hab, hs hb ha hab.symm⟩, ⟨hs ha hc' hac, hs hc' ha hac.symm⟩,
    ⟨hs hb hc' hbc, hs hc' hb hbc.symm⟩⟩

/-- CO-175 (chain half). On the width-2 poset `WidthTwo t`, First Fit on chains, with the points
taken in the order `WidthTwo.pos`, sends the point `(ℓ, i)` to chain `i`; so it uses `t` chains
(the point `(t-1, t-1)` lies in chain `t-1`) although the width is 2. -/
@[kb "kellertrotter2017" "Example 6.32, p. 156"]
theorem firstFit_widthTwo (t : ℕ) (x : WidthTwo t) :
    firstFit (WidthTwo.pos t) x = x.1.2 := by
  have key : ∀ n : ℕ, ∀ x : WidthTwo t, WidthTwo.pos t x = n →
      firstFit (WidthTwo.pos t) x = x.1.2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      have ih' : ∀ y : WidthTwo t, WidthTwo.pos t y < WidthTwo.pos t x →
          firstFit (WidthTwo.pos t) y = y.1.2 :=
        fun y hy => ih _ (hx ▸ hy) y rfl
      rw [firstFit_eq]
      apply sInf_eq_of_least
      · intro y hy hff
        rw [ih' y hy] at hff
        have hl := WidthTwo.level_le_of_pos_lt hy
        right
        rw [WidthTwo.le_iff]
        unfold ffLt
        omega
      · intro j hj hmem
        have hxx := x.2
        have hl1 : 1 ≤ x.1.1 := by omega
        let y : WidthTwo t := ⟨(x.1.1 - 1, j), by simp only; omega, by simp only; omega⟩
        have hyl : y.1.1 < x.1.1 := by show x.1.1 - 1 < x.1.1; omega
        have hyp := WidthTwo.pos_lt_of_level_lt hyl
        have := hmem y hyp (by rw [ih' y hyp])
        rw [WidthTwo.le_iff, WidthTwo.le_iff] at this
        have hy1 : y.1.1 = x.1.1 - 1 := rfl
        have hy2 : y.1.2 = j := rfl
        unfold ffLt at this
        omega
  exact key _ x rfl

end FirstFitBad

end UndergradKB.Combinatorics.Order
