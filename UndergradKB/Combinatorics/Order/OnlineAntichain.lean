import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import UndergradKB.Common.Attr

/-!
# On-line antichain partitioning: Szemerédi's lower bound (Keller–Trotter, Theorem 16.5)

* CO-178: for every `h` Builder has a strategy that builds a poset of height at most `h` while
  forcing Assigner to use at least `C(h+1, 2)` antichains, and at least `h` different antichains
  on the maximal elements.

**The game.**  Builder presents the points `0, 1, 2, …` one at a time; the point `i` is presented
together with its order relations to the points `< i`.  So after the `k`th round the position is a
partial order `r` on `{0, …, k-1}` (`IsPos k r`, a relation on `ℕ` supported on `{0,…,k-1}`).
An Assigner strategy `σ : Strategy` labels the point `i` (the antichain it is put into) knowing only
the relation `r` restricted to `{0, …, i}`: the label is `lab σ r i = σ i (restr (i+1) r)`.
The strategy is *valid* if comparable distinct points always receive different labels, i.e. the
classes are antichains.  A deterministic Assigner strategy is a function, so "Builder has a strategy
forcing …" is the statement that, for every valid `σ`, some play (a poset `r` on `{0,…,k-1}`) makes
`σ` use many labels.
-/

namespace UndergradKB.Combinatorics

open Finset

namespace OnlineAntichain

open Classical

/-- A binary relation on `ℕ`. -/
abbrev Rel := ℕ → ℕ → Prop

/-- `r` is a partial order on `{0, …, k-1}` (and relates nothing else). -/
structure IsPos (k : ℕ) (r : Rel) : Prop where
  supp : ∀ a b, r a b → a < k ∧ b < k
  refl : ∀ a, a < k → r a a
  trans : ∀ a b c, r a b → r b c → r a c
  antisymm : ∀ a b, r a b → r b a → a = b

/-- Restriction of a relation to `{0, …, n-1}`. -/
def restr (n : ℕ) (r : Rel) : Rel := fun a b => a < n ∧ b < n ∧ r a b

/-- An on-line Assigner strategy: the label of point `i` as a function of the relation seen so far
(the relation restricted to the points `≤ i`). -/
def Strategy := ℕ → Rel → ℕ

/-- The label (antichain index) given to point `i` when the play is `r`. -/
def lab (σ : Strategy) (r : Rel) (i : ℕ) : ℕ := σ i (restr (i + 1) r)

/-- The strategy is a legal Assigner strategy: comparable distinct points get distinct labels
(each label class is an antichain). -/
def Valid (σ : Strategy) : Prop :=
  ∀ k r, IsPos k r → ∀ a b, r a b → a ≠ b → lab σ r a ≠ lab σ r b

/-- Every chain in `r` (a set of points of `{0,…,k-1}`, pairwise comparable) has at most `h`
elements: the poset has height at most `h`. -/
def HeightLe (k : ℕ) (r : Rel) (h : ℕ) : Prop :=
  ∀ c : Finset ℕ, (∀ a ∈ c, a < k) → (∀ a ∈ c, ∀ b ∈ c, r a b ∨ r b a) → c.card ≤ h

/-- `a` is a maximal element of `r`. -/
def IsMax (r : Rel) (a : ℕ) : Prop := ∀ b, r a b → b = a

/-- The set of labels (antichains) used on the play `r` with `k` points. -/
noncomputable def labs (σ : Strategy) (k : ℕ) (r : Rel) : Finset ℕ := (range k).image (lab σ r)

/-- The set of labels used on the maximal elements. -/
noncomputable def maxLabs (σ : Strategy) (k : ℕ) (r : Rel) : Finset ℕ :=
  ((range k).filter (IsMax r)).image (lab σ r)

/-! ### Gluing a block of new points onto a position -/

/-- Put the block `s` (on `m` points) after the position `r` (on `k` points).  New points are below
every element of `U` and above every element of `D`; all other pairs (old, new) are incomparable. -/
def glue (k m : ℕ) (r s : Rel) (U D : Set ℕ) : Rel := fun a b =>
  r a b ∨ (k ≤ a ∧ k ≤ b ∧ s (a - k) (b - k)) ∨ (k ≤ a ∧ a < k + m ∧ b < k ∧ b ∈ U) ∨
    (a < k ∧ k ≤ b ∧ b < k + m ∧ a ∈ D)

section Glue

variable {k m : ℕ} {r s : Rel} {U D : Set ℕ}

lemma glue_old (a b : ℕ) (ha : a < k) (hb : b < k) : glue k m r s U D a b ↔ r a b := by
  unfold glue
  constructor
  · rintro (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩) <;> first | exact h | omega
  · exact Or.inl

lemma glue_new (hr : IsPos k r) (a b : ℕ) (ha : k ≤ a) (hb : k ≤ b) :
    glue k m r s U D a b ↔ s (a - k) (b - k) := by
  unfold glue
  constructor
  · rintro (h | ⟨_, _, h⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩)
    · have := (hr.supp a b h).1; omega
    · exact h
    · omega
    · omega
  · intro h; exact Or.inr (Or.inl ⟨ha, hb, h⟩)

lemma glue_new_old (hr : IsPos k r) (a b : ℕ) (ha : k ≤ a) (ha' : a < k + m) (hb : b < k) :
    glue k m r s U D a b ↔ b ∈ U := by
  unfold glue
  constructor
  · rintro (h | ⟨_, h, _⟩ | ⟨_, _, _, h⟩ | ⟨h, _⟩)
    · have := (hr.supp a b h).1; omega
    · omega
    · exact h
    · omega
  · intro h; exact Or.inr (Or.inr (Or.inl ⟨ha, ha', hb, h⟩))

lemma glue_old_new (hr : IsPos k r) (a b : ℕ) (ha : a < k) (hb : k ≤ b) (hb' : b < k + m) :
    glue k m r s U D a b ↔ a ∈ D := by
  unfold glue
  constructor
  · rintro (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, h⟩)
    · have := (hr.supp a b h).2; omega
    · omega
    · omega
    · exact h
  · intro h; exact Or.inr (Or.inr (Or.inr ⟨ha, hb, hb', h⟩))

lemma glue_supp (hr : IsPos k r) (hs : IsPos m s) {a b : ℕ} (h : glue k m r s U D a b) :
    a < k + m ∧ b < k + m := by
  unfold glue at h
  rcases h with h | ⟨h1, h2, h⟩ | ⟨h1, h2, h3, h⟩ | ⟨h1, h2, h3, h⟩
  · have := hr.supp a b h; omega
  · have := hs.supp _ _ h; omega
  · omega
  · omega

/-- Gluing produces a partial order, provided `U` is an up-set, `D` a down-set, `D` lies below
`U` and the two are disjoint. -/
lemma glue_isPos (hr : IsPos k r) (hs : IsPos m s)
    (hU : ∀ u ∈ U, u < k ∧ ∀ w, r u w → w ∈ U)
    (hD : ∀ d ∈ D, d < k ∧ ∀ e, r e d → e ∈ D)
    (hDU : ∀ d ∈ D, ∀ u ∈ U, r d u) (hdis : ∀ x ∈ D, x ∉ U) :
    IsPos (k + m) (glue k m r s U D) where
  supp := fun _ _ h => glue_supp hr hs h
  refl := by
    intro a ha
    by_cases hak : a < k
    · exact (glue_old a a hak hak).mpr (hr.refl a hak)
    · rw [glue_new hr a a (by omega) (by omega)]
      exact hs.refl _ (by omega)
  trans := by
    intro a b c hab hbc
    obtain ⟨ha', hb'⟩ := glue_supp hr hs hab
    obtain ⟨_, hc'⟩ := glue_supp hr hs hbc
    rcases lt_or_ge a k with ha | ha <;> rcases lt_or_ge b k with hb | hb <;>
      rcases lt_or_ge c k with hc | hc
    · exact (glue_old a c ha hc).mpr (hr.trans _ _ _ ((glue_old a b ha hb).mp hab)
        ((glue_old b c hb hc).mp hbc))
    · have hbD := (glue_old_new hr b c hb hc hc').mp hbc
      exact (glue_old_new hr a c ha hc hc').mpr ((hD b hbD).2 a ((glue_old a b ha hb).mp hab))
    · have haD := (glue_old_new hr a b ha hb hb').mp hab
      have hcU := (glue_new_old hr b c hb hb' hc).mp hbc
      exact (glue_old a c ha hc).mpr (hDU a haD c hcU)
    · exact (glue_old_new hr a c ha hc hc').mpr ((glue_old_new hr a b ha hb hb').mp hab)
    · have hbU := (glue_new_old hr a b ha ha' hb).mp hab
      have hr' := (glue_old b c hb hc).mp hbc
      exact (glue_new_old hr a c ha ha' hc).mpr ((hU b hbU).2 c hr')
    · have hbU := (glue_new_old hr a b ha ha' hb).mp hab
      have hbD := (glue_old_new hr b c hb hc hc').mp hbc
      exact absurd hbU (hdis b hbD)
    · exact (glue_new_old hr a c ha ha' hc).mpr ((glue_new_old hr b c hb hb' hc).mp hbc)
    · exact (glue_new hr a c ha hc).mpr (hs.trans _ _ _ ((glue_new hr a b ha hb).mp hab)
        ((glue_new hr b c hb hc).mp hbc))
  antisymm := by
    intro a b hab hba
    obtain ⟨ha', hb'⟩ := glue_supp hr hs hab
    rcases lt_or_ge a k with ha | ha <;> rcases lt_or_ge b k with hb | hb
    · exact hr.antisymm _ _ ((glue_old a b ha hb).mp hab) ((glue_old b a hb ha).mp hba)
    · have haD := (glue_old_new hr a b ha hb hb').mp hab
      have haU := (glue_new_old hr b a hb hb' ha).mp hba
      exact absurd haU (hdis a haD)
    · have hbD := (glue_old_new hr b a hb ha ha').mp hba
      have hbU := (glue_new_old hr a b ha ha' hb).mp hab
      exact absurd hbU (hdis b hbD)
    · have := hs.antisymm _ _ ((glue_new hr a b ha hb).mp hab) ((glue_new hr b a hb ha).mp hba)
      omega

/-- The strategy seen by the block `s` once the position `r` and the placement data `U, D` are
fixed (the block is played "relative to" the earlier play). -/
def derive (σ : Strategy) (k : ℕ) (r : Rel) (U D : Set ℕ) : Strategy :=
  fun i rel => σ (k + i) (restr (k + i + 1) (glue k (i + 1) r rel U D))

lemma restr_glue (i : ℕ) (hi : i < m) :
    restr (k + i + 1) (glue k (i + 1) r (restr (i + 1) s) U D) =
      restr (k + i + 1) (glue k m r s U D) := by
  funext a b
  apply propext
  unfold restr glue
  constructor
  · rintro ⟨ha, hb, h⟩
    refine ⟨ha, hb, ?_⟩
    rcases h with h | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2, h5⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, by omega, h3, h4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, by omega, h4⟩))
  · rintro ⟨ha, hb, h⟩
    refine ⟨ha, hb, ?_⟩
    rcases h with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, h2, by omega, by omega, h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, by omega, h3, h4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, by omega, h4⟩))

lemma lab_derive (σ : Strategy) {i : ℕ} (hi : i < m) :
    lab (derive σ k r U D) s i = lab σ (glue k m r s U D) (k + i) := by
  unfold lab derive
  rw [restr_glue i hi]

lemma lab_old (σ : Strategy) {a : ℕ} (ha : a < k) :
    lab σ (glue k m r s U D) a = lab σ r a := by
  unfold lab
  congr 1
  funext x y
  apply propext
  unfold restr
  constructor
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, (glue_old x y (by omega) (by omega)).mp h⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, (glue_old x y (by omega) (by omega)).mpr h⟩

lemma valid_derive {σ : Strategy} (hσ : Valid σ) (hr : IsPos k r)
    (hU : ∀ u ∈ U, u < k ∧ ∀ w, r u w → w ∈ U)
    (hD : ∀ d ∈ D, d < k ∧ ∀ e, r e d → e ∈ D)
    (hDU : ∀ d ∈ D, ∀ u ∈ U, r d u) (hdis : ∀ x ∈ D, x ∉ U) :
    Valid (derive σ k r U D) := by
  intro m' s hs a b hab hne
  have hg := glue_isPos hr hs hU hD hDU hdis
  have ha := (hs.supp a b hab).1
  have hb := (hs.supp a b hab).2
  rw [lab_derive σ ha, lab_derive σ hb]
  exact hσ _ _ hg (k + a) (k + b) ((glue_new hr _ _ (by omega) (by omega)).mpr
    (by simpa using hab)) (by omega)

/-! ### Heights of glued posets -/

lemma old_card (hr : IsPos k r) {a : ℕ} (hra : HeightLe k r a) (c : Finset ℕ)
    (hcomp : ∀ x ∈ c, ∀ y ∈ c, glue k m r s U D x y ∨ glue k m r s U D y x) :
    (c.filter (fun x => x < k)).card ≤ a := by
  refine hra _ (fun x hx => (mem_filter.mp hx).2) ?_
  intro x hx y hy
  have hx' := mem_filter.mp hx
  have hy' := mem_filter.mp hy
  rcases hcomp x hx'.1 y hy'.1 with h | h
  · exact Or.inl ((glue_old x y hx'.2 hy'.2).mp h)
  · exact Or.inr ((glue_old y x hy'.2 hx'.2).mp h)

lemma new_card (hr : IsPos k r) (hs : IsPos m s) {b : ℕ} (hsb : HeightLe m s b) (c : Finset ℕ)
    (hc : ∀ x ∈ c, x < k + m)
    (hcomp : ∀ x ∈ c, ∀ y ∈ c, glue k m r s U D x y ∨ glue k m r s U D y x) :
    (c.filter (fun x => ¬ x < k)).card ≤ b := by
  have hinj : Set.InjOn (fun x => x - k) (c.filter (fun x => ¬ x < k) : Set ℕ) := by
    intro x hx y hy hxy
    have := (mem_filter.mp hx).2
    have := (mem_filter.mp hy).2
    simp only at hxy
    omega
  rw [← Finset.card_image_of_injOn hinj]
  refine hsb _ ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    have := hc y (mem_filter.mp hy).1
    have := (mem_filter.mp hy).2
    omega
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
    have hx2 := mem_filter.mp hx'
    have hy2 := mem_filter.mp hy'
    rcases hcomp x' hx2.1 y' hy2.1 with h | h
    · exact Or.inl ((glue_new hr x' y' (by omega) (by omega)).mp h)
    · exact Or.inr ((glue_new hr y' x' (by omega) (by omega)).mp h)

lemma height_glue_add (hr : IsPos k r) (hs : IsPos m s) {a b : ℕ} (hra : HeightLe k r a)
    (hsb : HeightLe m s b) : HeightLe (k + m) (glue k m r s U D) (a + b) := by
  intro c hc hcomp
  have h1 := old_card (m := m) (s := s) (U := U) (D := D) hr hra c hcomp
  have h2 := new_card hr hs hsb c hc hcomp
  have h3 := Finset.card_filter_add_card_filter_not (s := c) (fun x => x < k)
  omega

lemma height_glue_max (hr : IsPos k r) (hs : IsPos m s) {a b : ℕ} (hra : HeightLe k r a)
    (hsb : HeightLe m s b) : HeightLe (k + m) (glue k m r s ∅ ∅) (max a b) := by
  intro c hc hcomp
  have h1 := old_card (m := m) (s := s) (U := ∅) (D := ∅) hr hra c hcomp
  have h2 := new_card hr hs hsb c hc hcomp
  have h3 := Finset.card_filter_add_card_filter_not (s := c) (fun x => x < k)
  by_cases hnew : (c.filter (fun x => ¬ x < k)).Nonempty
  · obtain ⟨p, hp⟩ := hnew
    have hp' := mem_filter.mp hp
    have hold : c.filter (fun x => x < k) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hxk
      rcases hcomp x hx p hp'.1 with h | h
      · rw [glue_old_new hr x p hxk (by omega) (hc p hp'.1)] at h; exact h
      · rw [glue_new_old hr p x (by omega) (hc p hp'.1) hxk] at h; exact h
    have e0 : (c.filter (fun x => x < k)).card = 0 := by rw [hold]; rfl
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hnew
    have e0 : (c.filter (fun x => ¬ x < k)).card = 0 := by rw [hnew]; rfl
    omega

lemma height_glue_U (hr : IsPos k r) (hs : IsPos m s) {a b : ℕ} (hra : HeightLe k r a)
    (hsb : HeightLe m s b) (hmax : ∀ u ∈ U, ∀ w, r u w → w = u) :
    HeightLe (k + m) (glue k m r s U ∅) (max a (b + 1)) := by
  intro c hc hcomp
  have h1 := old_card (m := m) (s := s) (U := U) (D := ∅) hr hra c hcomp
  have h2 := new_card hr hs hsb c hc hcomp
  have h3 := Finset.card_filter_add_card_filter_not (s := c) (fun x => x < k)
  by_cases hnew : (c.filter (fun x => ¬ x < k)).Nonempty
  · obtain ⟨p, hp⟩ := hnew
    have hp' := mem_filter.mp hp
    have hsub : ∀ x ∈ c.filter (fun x => x < k), x ∈ U := by
      intro x hx
      have hx' := mem_filter.mp hx
      rcases hcomp x hx'.1 p hp'.1 with h | h
      · rw [glue_old_new hr x p hx'.2 (by omega) (hc p hp'.1)] at h
        exact absurd h (by simp)
      · rwa [glue_new_old hr p x (by omega) (hc p hp'.1) hx'.2] at h
    have h4 : (c.filter (fun x => x < k)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' := mem_filter.mp hx
      have hy' := mem_filter.mp hy
      rcases hcomp x hx'.1 y hy'.1 with h | h
      · exact (hmax x (hsub x hx) y ((glue_old x y hx'.2 hy'.2).mp h)).symm
      · exact hmax y (hsub y hy) x ((glue_old y x hy'.2 hx'.2).mp h)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hnew
    have e0 : (c.filter (fun x => ¬ x < k)).card = 0 := by rw [hnew]; rfl
    omega

/-! ### Maximal elements and labels of glued positions -/

lemma isMax_glue_old (hr : IsPos k r) {a : ℕ} (ha : a < k) (hmax : IsMax r a) :
    IsMax (glue k m r s U ∅) a := by
  intro b h
  unfold glue at h
  rcases h with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, h⟩
  · exact hmax b h
  · omega
  · omega
  · exact absurd h (by simp)

lemma isMax_glue_new (hr : IsPos k r) {i : ℕ} (hmax : IsMax s i) :
    IsMax (glue k m r s ∅ D) (k + i) := by
  intro b h
  unfold glue at h
  rcases h with h | ⟨_, h2, h⟩ | ⟨_, _, _, h⟩ | ⟨h, _⟩
  · have := (hr.supp _ _ h).1; omega
  · have h' : s i (b - k) := by simpa using h
    have := hmax _ h'; omega
  · exact absurd h (by simp)
  · omega

lemma labs_old_subset (σ : Strategy) :
    labs σ k r ⊆ labs σ (k + m) (glue k m r s U D) := by
  intro l hl
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hl
  rw [mem_range] at ha
  exact mem_image.mpr ⟨a, mem_range.mpr (by omega), lab_old σ ha⟩

lemma labs_new_subset (σ : Strategy) :
    labs (derive σ k r U D) m s ⊆ labs σ (k + m) (glue k m r s U D) := by
  intro l hl
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hl
  rw [mem_range] at ha
  exact mem_image.mpr ⟨k + a, mem_range.mpr (by omega), (lab_derive σ ha).symm⟩

/-- Extending below a set `U` of maximal elements. -/
lemma extendU (σ : Strategy) (hσ : Valid σ) (hr : IsPos k r) (hs : IsPos m s) (UF : Finset ℕ)
    (hU : ∀ u ∈ UF, u < k ∧ IsMax r u) :
    IsPos (k + m) (glue k m r s (UF : Set ℕ) ∅) ∧
    (∀ a b, HeightLe k r a → HeightLe m s b →
      HeightLe (k + m) (glue k m r s (UF : Set ℕ) ∅) (max a (b + 1))) ∧
    (UF.image (lab σ r)).card + (labs (derive σ k r (UF : Set ℕ) ∅) m s).card ≤
      (labs σ (k + m) (glue k m r s (UF : Set ℕ) ∅)).card ∧
    UF.image (lab σ r) ⊆ maxLabs σ (k + m) (glue k m r s (UF : Set ℕ) ∅) := by
  have hU' : ∀ u ∈ (UF : Set ℕ), u < k ∧ ∀ w, r u w → w ∈ (UF : Set ℕ) := by
    intro u hu
    have := hU u hu
    exact ⟨this.1, fun w hw => by rw [this.2 w hw]; exact hu⟩
  have hg := glue_isPos (D := (∅ : Set ℕ)) hr hs hU' (by simp) (by simp) (by simp)
  refine ⟨hg, fun a b hra hsb => height_glue_U hr hs hra hsb (fun u hu w hw => (hU u hu).2 w hw),
    ?_, ?_⟩
  · rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (Finset.union_subset ?_ (labs_new_subset σ))
      intro l hl
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hl
      exact labs_old_subset σ (mem_image.mpr ⟨u, mem_range.mpr (hU u hu).1, rfl⟩)
    · rw [Finset.disjoint_left]
      intro l hl hl'
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hl
      obtain ⟨i, hi, hil⟩ := mem_image.mp hl'
      rw [mem_range] at hi
      rw [lab_derive σ hi, ← lab_old (m := m) (s := s) (U := (UF : Set ℕ)) (D := ∅) σ
        (hU u hu).1] at hil
      refine hσ _ _ hg (k + i) u ?_ (by have := (hU u hu).1; omega) hil
      exact (glue_new_old hr _ _ (by omega) (by omega) (hU u hu).1).mpr hu
  · intro l hl
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hl
    refine mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_range.mpr (by have := (hU u hu).1; omega),
      isMax_glue_old hr (hU u hu).1 (hU u hu).2⟩, lab_old σ (hU u hu).1⟩

end Glue

/-! ### Szemerédi's strategy -/

/-- The one-point poset. -/
def pt : Rel := fun a b => a = 0 ∧ b = 0

lemma isPos_pt : IsPos 1 pt where
  supp := by rintro a b ⟨rfl, rfl⟩; simp
  refl := by intro a ha; have : a = 0 := by omega
             exact ⟨this, this⟩
  trans := by rintro a b c ⟨h1, _⟩ ⟨_, h4⟩; exact ⟨h1, h4⟩
  antisymm := by rintro a b ⟨h1, h2⟩ _; omega

lemma heightLe_pt : HeightLe 1 pt 1 := by
  intro c hc _
  have : c ⊆ {0} := by
    intro x hx
    have := hc x hx
    simp; omega
  simpa using Finset.card_le_card this

lemma isMax_pt : IsMax pt 0 := by
  rintro b ⟨_, h⟩; exact h

lemma isPos_empty : IsPos 0 (fun _ _ => False) where
  supp := by simp
  refl := by intro a ha; omega
  trans := by simp
  antisymm := by simp

/-- **The inductive statement of Szemerédi's theorem.** -/
theorem szemeredi_step (h : ℕ) (ih : ∀ σ : Strategy, Valid σ → ∃ k r, IsPos k r ∧ HeightLe k r h ∧
      (h + 1).choose 2 ≤ (labs σ k r).card ∧ h ≤ (maxLabs σ k r).card)
    (σ : Strategy) (hσ : Valid σ) :
    ∃ k r, IsPos k r ∧ HeightLe k r (h + 1) ∧
      (h + 2).choose 2 ≤ (labs σ k r).card ∧ h + 1 ≤ (maxLabs σ k r).card := by
  have hch : (h + 2).choose 2 = (h + 1) + (h + 1).choose 2 := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  obtain ⟨k1, r1, hr1, hh1, hl1, hm1⟩ := ih σ hσ
  have hv2 := valid_derive (U := (∅ : Set ℕ)) (D := ∅) hσ hr1 (by simp) (by simp) (by simp)
    (by simp)
  obtain ⟨m2, s2, hs2, hh2, hl2, hm2⟩ := ih _ hv2
  have hR12 : IsPos (k1 + m2) (glue k1 m2 r1 s2 ∅ ∅) :=
    glue_isPos hr1 hs2 (by simp) (by simp) (by simp) (by simp)
  have hhR12 : HeightLe (k1 + m2) (glue k1 m2 r1 s2 ∅ ∅) h := by
    simpa using height_glue_max hr1 hs2 hh1 hh2
  -- maximal labels of both halves are maximal labels of the union
  have hA : maxLabs σ k1 r1 ⊆ maxLabs σ (k1 + m2) (glue k1 m2 r1 s2 ∅ ∅) := by
    intro l hl
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hl
    obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
    rw [mem_range] at ha1
    exact mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_range.mpr (by omega),
      isMax_glue_old hr1 ha1 ha2⟩, lab_old σ ha1⟩
  have hB : maxLabs (derive σ k1 r1 ∅ ∅) m2 s2 ⊆
      maxLabs σ (k1 + m2) (glue k1 m2 r1 s2 ∅ ∅) := by
    intro l hl
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hl
    obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
    rw [mem_range] at ha1
    exact mem_image.mpr ⟨k1 + a, mem_filter.mpr ⟨mem_range.mpr (by omega),
      isMax_glue_new hr1 ha2⟩, (lab_derive σ ha1).symm⟩
  by_cases hcase : h + 1 ≤ (maxLabs σ (k1 + m2) (glue k1 m2 r1 s2 ∅ ∅)).card
  · -- Case 1: many labels on the maximal elements; put a copy below all of them
    set R12 := glue k1 m2 r1 s2 ∅ ∅ with hR12def
    have hUF : ∀ u ∈ (range (k1 + m2)).filter (IsMax R12), u < k1 + m2 ∧ IsMax R12 u := by
      intro u hu
      obtain ⟨h1, h2⟩ := mem_filter.mp hu
      exact ⟨mem_range.mp h1, h2⟩
    have hv3 := valid_derive (D := (∅ : Set ℕ)) hσ hR12
      (U := (((range (k1 + m2)).filter (IsMax R12) : Finset ℕ) : Set ℕ))
      (fun u hu => by
        have := hUF u hu
        exact ⟨this.1, fun w hw => by rw [this.2 w hw]; exact hu⟩) (by simp) (by simp) (by simp)
    obtain ⟨m3, s3, hs3, hh3, hl3, hm3⟩ := ih _ hv3
    obtain ⟨hpos, hhgt, hlab, hmx⟩ := extendU σ hσ hR12 hs3 _ hUF
    refine ⟨k1 + m2 + m3, _, hpos, ?_, ?_, ?_⟩
    · have := hhgt h h hhR12 hh3
      rwa [max_eq_right (Nat.le_succ h)] at this
    · have e1 : ((range (k1 + m2)).filter (IsMax R12)).image (lab σ R12) =
          maxLabs σ (k1 + m2) R12 := rfl
      rw [e1] at hlab
      omega
    · refine le_trans hcase (Finset.card_le_card ?_)
      exact hmx
  · -- Case 2: the maximal labels coincide; add a point above the first copy
    push Not at hcase
    set R12 := glue k1 m2 r1 s2 ∅ ∅ with hR12def
    set A := maxLabs σ k1 r1 with hAdef
    set B := maxLabs (derive σ k1 r1 ∅ ∅) m2 s2 with hBdef
    have hAB : (A ∪ B).card ≤ h := by
      have := Finset.card_le_card (Finset.union_subset hA hB)
      omega
    have hAeq : A = A ∪ B :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have hBA : B ⊆ A := by rw [hAeq]; exact Finset.subset_union_right
    have hDdown : ∀ d ∈ (Set.Iio k1 : Set ℕ), d < k1 + m2 ∧ ∀ e, R12 e d → e ∈ (Set.Iio k1 : Set ℕ) := by
      intro d hd
      have hd' : d < k1 := hd
      refine ⟨by omega, fun e he => ?_⟩
      by_contra hne
      have hek : k1 ≤ e := by simpa using hne
      have := glue_supp hr1 hs2 he
      have h' := (glue_new_old hr1 e d hek this.1 hd').mp he
      exact h'
    have hR' : IsPos (k1 + m2 + 1) (glue (k1 + m2) 1 R12 pt ∅ (Set.Iio k1)) :=
      glue_isPos hR12 isPos_pt (by simp) hDdown (by simp) (by simp)
    have hhR' : HeightLe (k1 + m2 + 1) (glue (k1 + m2) 1 R12 pt ∅ (Set.Iio k1)) (h + 1) :=
      height_glue_add hR12 isPos_pt hhR12 heightLe_pt
    set R' := glue (k1 + m2) 1 R12 pt ∅ (Set.Iio k1) with hR'def
    -- the label of the new point differs from all labels in `A`
    have hlx : lab σ R' (k1 + m2) ∉ A := by
      intro hl
      obtain ⟨a, ha, hal⟩ := mem_image.mp hl
      obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
      rw [mem_range] at ha1
      have hadj : R' a (k1 + m2) :=
        (glue_old_new hR12 a (k1 + m2) (by omega) le_rfl (by omega)).mpr ha1
      have e : lab σ R' a = lab σ r1 a := (lab_old σ (by omega)).trans (lab_old σ ha1)
      exact hσ _ _ hR' a (k1 + m2) hadj (by omega) (e.trans hal)
    -- the new level of maximal elements
    set U3 : Finset ℕ := ((Finset.Ico k1 (k1 + m2)).filter (IsMax R12)) ∪ {k1 + m2} with hU3def
    have hU3 : ∀ u ∈ U3, u < k1 + m2 + 1 ∧ IsMax R' u := by
      intro u hu
      rcases mem_union.mp hu with hu | hu
      · obtain ⟨h1, h2⟩ := mem_filter.mp hu
        rw [Finset.mem_Ico] at h1
        refine ⟨by omega, fun b hb => ?_⟩
        rw [hR'def] at hb
        unfold glue at hb
        rcases hb with hb | ⟨hb, _⟩ | ⟨hb, _⟩ | ⟨_, _, _, hb⟩
        · exact h2 b hb
        · omega
        · omega
        · exact absurd hb (by simp; omega)
      · rw [mem_singleton] at hu
        subst hu
        exact ⟨by omega, isMax_glue_new (D := Set.Iio k1) hR12 (i := 0) isMax_pt⟩
    have hv3 := valid_derive (D := (∅ : Set ℕ)) hσ hR'
      (U := ((U3 : Finset ℕ) : Set ℕ))
      (fun u hu => by
        have := hU3 u hu
        exact ⟨this.1, fun w hw => by rw [this.2 w hw]; exact hu⟩) (by simp) (by simp) (by simp)
    obtain ⟨m3, s3, hs3, hh3, hl3, hm3⟩ := ih _ hv3
    obtain ⟨hpos, hhgt, hlab, hmx⟩ := extendU σ hσ hR' hs3 U3 hU3
    -- the labels on `U3` contain `B` and the label of the new point
    have hsubB : insert (lab σ R' (k1 + m2)) B ⊆ U3.image (lab σ R') := by
      intro l hl
      rcases mem_insert.mp hl with rfl | hl
      · exact mem_image.mpr ⟨k1 + m2, mem_union_right _ (mem_singleton_self _), rfl⟩
      · obtain ⟨a, ha, rfl⟩ := mem_image.mp hl
        obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
        rw [mem_range] at ha1
        refine mem_image.mpr ⟨k1 + a, mem_union_left _ (mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, isMax_glue_new hr1 ha2⟩), ?_⟩
        rw [lab_old σ (by omega : k1 + a < k1 + m2)]
        exact (lab_derive σ ha1).symm
    have hcardU : h + 1 ≤ (U3.image (lab σ R')).card := by
      have hnot : lab σ R' (k1 + m2) ∉ B := fun hb => hlx (hBA hb)
      have := Finset.card_le_card hsubB
      rw [Finset.card_insert_of_notMem hnot] at this
      have hB' : h ≤ B.card := by simpa [hBdef] using hm2
      omega
    refine ⟨k1 + m2 + 1 + m3, _, hpos, ?_, ?_, ?_⟩
    · have := hhgt (h + 1) h hhR' hh3
      rwa [max_eq_left (by omega)] at this
    · omega
    · exact le_trans hcardU (Finset.card_le_card hmx)

/-- The statement of Szemerédi's theorem, by induction on `h`. -/
theorem szemeredi_aux (h : ℕ) (σ : Strategy) (hσ : Valid σ) :
    ∃ k r, IsPos k r ∧ HeightLe k r h ∧ (h + 1).choose 2 ≤ (labs σ k r).card ∧
      h ≤ (maxLabs σ k r).card := by
  induction h generalizing σ with
  | zero =>
    exact ⟨0, fun _ _ => False, isPos_empty,
      fun c hc _ => by
        have : c = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by have := hc x hx; omega
        simp [this], by simp, by simp⟩
  | succ h ih => exact szemeredi_step h ih σ hσ

end OnlineAntichain

open OnlineAntichain in
/-- CO-178. **Szemerédi's on-line antichain theorem** (Theorem 16.5).  Builder presents the points
of a poset one at a time, each with its relations to the earlier points (a play is a partial order
`r` on `{0,…,k-1}`, the order of presentation being the numbering).  Against every legal on-line
Assigner strategy `σ` (one that always puts comparable points into different antichains), Builder
can build a poset of height at most `h` on which `σ` uses at least `C(h+1, 2)` different antichains,
and at least `h` different antichains on the set of maximal elements. -/
@[kb "kellertrotter2017" "Theorem 16.5, p. 341"]
theorem szemeredi_online_antichain (h : ℕ) (σ : Strategy) (hσ : Valid σ) :
    ∃ k r, IsPos k r ∧ HeightLe k r h ∧ (h + 1).choose 2 ≤ (labs σ k r).card ∧
      h ≤ (maxLabs σ k r).card :=
  szemeredi_aux h σ hσ

end UndergradKB.Combinatorics
