import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Lattice.Fold
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Order.IntervalOrder
import UndergradKB.Combinatorics.Order.Posets2

/-!
# Interval-order representation by down sets and up sets (Keller--Trotter, Section 6.7)

Source: Keller--Trotter, *Applied Combinatorics* (2017), pp. 153--154.  For a finite poset
excluding `2 + 2` the strict down sets `D(x)` form a chain, so do the strict up sets `U(x)`,
there are equally many of each, and numbering them gives the integer interval representation
`I(x) = [i, j]` with `D(x) = D_i`, `U(x) = U_j`.
-/

namespace UndergradKB.Combinatorics.Order

open Finset
open scoped Classical

variable {α : Type*} [PartialOrder α]

/-- The strict down set `D(x) = {y : y < x}`. -/
noncomputable def dnFin [Fintype α] (x : α) : Finset α := univ.filter (· < x)

/-- The strict up set `U(x) = {y : x < y}`. -/
noncomputable def upFin [Fintype α] (x : α) : Finset α := univ.filter (x < ·)

section
variable [Fintype α]

@[simp] lemma mem_dnFin {x z : α} : z ∈ dnFin x ↔ z < x := by simp [dnFin]
@[simp] lemma mem_upFin {x z : α} : z ∈ upFin x ↔ x < z := by simp [upFin]

/-- The family `𝔇` of distinct strict down sets. -/
noncomputable def dnFins (α : Type*) [PartialOrder α] [Fintype α] : Finset (Finset α) :=
  univ.image dnFin

/-- The family `𝔘` of distinct strict up sets. -/
noncomputable def upFins (α : Type*) [PartialOrder α] [Fintype α] : Finset (Finset α) :=
  univ.image upFin

/-! ### CO-171: the certificate half of the algorithm -/

/-- CO-171. If two down sets `D(x)`, `D(y)` are incomparable under inclusion, then choosing
`z ∈ D(x) \ D(y)` and `w ∈ D(y) \ D(x)` yields a copy `z < x`, `w < y` of `2 + 2`. -/
@[kb "kellertrotter2017" "text, p. 153"]
theorem two_plus_two_of_incomparable_dnFins {x y : α}
    (h1 : ¬ dnFin x ⊆ dnFin y) (h2 : ¬ dnFin y ⊆ dnFin x) :
    ∃ z w : α, z ∈ dnFin x ∧ z ∉ dnFin y ∧ w ∈ dnFin y ∧ w ∉ dnFin x ∧
      TwoPlusTwo z x w y := by
  obtain ⟨z, hzx, hzy⟩ := Finset.not_subset.1 h1
  obtain ⟨w, hwy, hwx⟩ := Finset.not_subset.1 h2
  rw [mem_dnFin] at hzx hwy
  rw [mem_dnFin] at hzy hwx
  refine ⟨z, w, by simpa using hzx, by simpa using hzy, by simpa using hwy, by simpa using hwx,
    hzx, hwy, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
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

/-- CO-171. The dichotomy of the algorithm: either the down sets form a chain under inclusion, or
the poset contains `2 + 2`. -/
@[kb "kellertrotter2017" "text, p. 153"]
theorem dnFins_chain_or_two_plus_two :
    (∀ x y : α, dnFin x ⊆ dnFin y ∨ dnFin y ⊆ dnFin x) ∨
      ContainsPoset α (Fin 2 ⊕ Fin 2) := by
  by_cases h : ∀ x y : α, dnFin x ⊆ dnFin y ∨ dnFin y ⊆ dnFin x
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨x, y, h1, h2⟩ := h
    obtain ⟨z, w, -, -, -, -, h⟩ := two_plus_two_of_incomparable_dnFins h1 h2
    exact containsPoset_two_plus_two_iff.2 ⟨z, x, w, y, h⟩

/-- CO-171/CO-172. In a poset excluding `2 + 2` the strict down sets form a chain under
inclusion. -/
@[kb "kellertrotter2017" "text, p. 153"]
theorem dnFin_chain (hne : ¬ ContainsPoset α (Fin 2 ⊕ Fin 2)) (x y : α) :
    dnFin x ⊆ dnFin y ∨ dnFin y ⊆ dnFin x := by
  rcases dnFins_chain_or_two_plus_two (α := α) with h | h
  · exact h x y
  · exact absurd h hne

/-- CO-171/CO-172. In a poset excluding `2 + 2` the strict up sets form a chain under inclusion
(dual of `dnFin_chain`). -/
@[kb "kellertrotter2017" "text, p. 153"]
theorem upFin_chain (hne : ¬ ContainsPoset α (Fin 2 ⊕ Fin 2)) (x y : α) :
    upFin x ⊆ upFin y ∨ upFin y ⊆ upFin x := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨z, hzx, hzy⟩ := Finset.not_subset.1 h1
  obtain ⟨w, hwy, hwx⟩ := Finset.not_subset.1 h2
  rw [mem_upFin] at hzx hwy hzy hwx
  apply hne
  rw [containsPoset_two_plus_two_iff]
  refine ⟨x, z, y, w, hzx, hwy, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact fun h => hwx (lt_of_le_of_lt h hwy)
  · exact fun h => hzy (lt_of_le_of_lt h hzx)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact hwx h
    · exact hzy (hwy.trans hzx)
  · exact fun h => hzy ((hwy.trans_le h).trans hzx)
  · exact fun h => hwx ((hzx.trans_le h).trans hwy)
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact hzy h
    · exact hwx (hzx.trans hwy)
  · exact fun h => hwx (hzx.trans_le h)
  · exact fun h => hzy (hwy.trans_le h)

/-! ### CO-172: Theorem 6.30 -/

lemma lt_dnFin_ssub' {x y : α} (h : x < y) : dnFin x ⊂ dnFin y :=
  (Finset.ssubset_iff_of_subset (fun _ hz => mem_dnFin.2 ((mem_dnFin.1 hz).trans h))).2
    ⟨x, mem_dnFin.2 h, fun hx => lt_irrefl _ (mem_dnFin.1 hx)⟩

variable (α) in
/-- The size `|D(x)|` of a strict down set. -/
noncomputable def dcard (x : α) : ℕ := (dnFin x).card

variable (α) in
/-- The set of values `|D(x)|`. -/
noncomputable def dvals : Finset ℕ := univ.image (dcard (α := α))

variable (α) in
/-- `thr p = {y : p < |D(y)|}`: the up set cut off at threshold `p`. -/
noncomputable def thr (p : ℕ) : Finset α := univ.filter fun y => p < dcard (α := α) y

variable (α) in
/-- The rank of `p` among the values `|D(x)|`: the number of such values below `p`. -/
noncomputable def rk (p : ℕ) : ℕ := ((dvals α).filter (· < p)).card

/-- The right end `max {|D(z)| : ¬ x < z}` of the canonical representation. -/
noncomputable def beta (x : α) : ℕ := (univ.filter fun z => ¬ x < z).sup (dcard α)

/-- CO-172. The index `i` of the down set `D(x) = D_i` when the distinct down sets are listed
increasingly `∅ = D_1 ⊂ D_2 ⊂ ⋯`: one plus the number of distinct down sets strictly inside
`D(x)`. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
noncomputable def downIndex (x : α) : ℕ := ((dnFins α).filter (· ⊂ dnFin x)).card + 1

/-- CO-172. The index `j` of the up set `U(x) = U_j` when the distinct up sets are listed
decreasingly `U_1 ⊃ U_2 ⊃ ⋯`: one plus the number of distinct up sets strictly containing
`U(x)`. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
noncomputable def upIndex (x : α) : ℕ := ((upFins α).filter (upFin x ⊂ ·)).card + 1

section Thm630

variable (hch : ∀ x y : α, dnFin x ⊆ dnFin y ∨ dnFin y ⊆ dnFin x)
include hch

lemma sub_of_dcard_le {x y : α} (h : dcard α x ≤ dcard α y) : dnFin x ⊆ dnFin y := by
  rcases hch x y with h1 | h1
  · exact h1
  · exact (Finset.eq_of_subset_of_card_le h1 h).symm.subset

lemma dnFin_eq_of_dcard_eq {x y : α} (h : dcard α x = dcard α y) : dnFin x = dnFin y :=
  Finset.Subset.antisymm (sub_of_dcard_le hch h.le) (sub_of_dcard_le hch h.ge)

lemma dnFin_ssub_iff {x y : α} : dnFin x ⊂ dnFin y ↔ dcard α x < dcard α y := by
  refine ⟨fun h => Finset.card_lt_card h, fun h => ?_⟩
  refine Finset.ssubset_iff_subset_ne.2 ⟨sub_of_dcard_le hch h.le, fun e => ?_⟩
  unfold dcard at h
  rw [e] at h
  exact lt_irrefl _ h

omit hch in
lemma beta_mem (x : α) : beta x ∈ dvals α := by
  obtain ⟨i, -, he⟩ := Finset.exists_mem_eq_sup (univ.filter fun z => ¬ x < z)
    ⟨x, by simp⟩ (dcard α)
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, he.symm⟩

omit hch in
lemma dcard_le_beta {x z : α} (h : ¬ x < z) : dcard α z ≤ beta x :=
  Finset.le_sup (f := dcard α) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

lemma upFin_eq_thr (x : α) : upFin x = thr α (beta x) := by
  ext y
  simp only [mem_upFin, thr, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hxy
    have hpos : ⊥ < dcard α y := Finset.card_pos.2 ⟨x, mem_dnFin.2 hxy⟩
    refine (Finset.sup_lt_iff hpos).2 fun z hz => ?_
    have hz' : ¬ x < z := (Finset.mem_filter.1 hz).2
    have hsub : dnFin z ⊆ dnFin y := by
      rcases hch z y with h | h
      · exact h
      · exact absurd (mem_dnFin.1 (h (mem_dnFin.2 hxy))) hz'
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
      ⟨x, mem_dnFin.2 hxy, fun hx => hz' (mem_dnFin.1 hx)⟩)
  · intro h
    by_contra hxy
    exact absurd (dcard_le_beta hxy) (not_le_of_gt h)

omit hch in
lemma thr_ssub_iff {p q : ℕ} (hq : q ∈ dvals α) :
    p < q ↔ thr α q ⊂ thr α p := by
  have hsub : q ≤ p → thr α p ⊆ thr α q := fun h y hy => by
    simp only [thr, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    omega
  constructor
  · intro h
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 hq
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨w, ?_, ?_⟩
    · intro y hy
      simp only [thr, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      omega
    · simp [thr, hw, h]
    · simp [thr, hw]
  · intro h
    by_contra hpq
    have h1 := hsub (not_lt.1 hpq)
    exact (Finset.ssubset_iff_subset_ne.1 h).2 (Finset.Subset.antisymm h.subset h1)

omit hch in
lemma thr_injOn : Set.InjOn (thr α) (dvals α : Set ℕ) := by
  intro p hp q hq h
  rcases lt_trichotomy p q with hlt | heq | hgt
  · have := (thr_ssub_iff (p := p) hq).1 hlt
    rw [h] at this
    exact absurd this (ssubset_irrefl _)
  · exact heq
  · have := (thr_ssub_iff (p := q) hp).1 hgt
    rw [h] at this
    exact absurd this (ssubset_irrefl _)

lemma exists_upFin_eq_thr {p : ℕ} (hp : p ∈ dvals α) : ∃ x : α, upFin x = thr α p := by
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hp
  by_cases hex : ∃ w, dcard α z < dcard α w
  · obtain ⟨w, hwS, hmin⟩ := (univ.filter fun w => dcard α z < dcard α w).exists_min_image
      (dcard α) (by obtain ⟨w, hw⟩ := hex; exact ⟨w, by simp [hw]⟩)
    have hwz : dcard α z < dcard α w := (Finset.mem_filter.1 hwS).2
    obtain ⟨x, hxw, hxz⟩ := Finset.exists_of_ssubset ((dnFin_ssub_iff hch).2 hwz)
    refine ⟨x, ?_⟩
    ext y
    simp only [mem_upFin, thr, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hxy
      by_contra hle
      exact hxz (sub_of_dcard_le hch (not_lt.1 hle) (mem_dnFin.2 hxy))
    · intro hy
      have hyS : y ∈ univ.filter fun w => dcard α z < dcard α w := by simp [hy]
      exact mem_dnFin.1 (sub_of_dcard_le hch (hmin y hyS) hxw)
  · push Not at hex
    obtain ⟨x, -, hxmax⟩ := (univ : Finset α).exists_max_image (dcard α) ⟨z, mem_univ _⟩
    refine ⟨x, ?_⟩
    ext y
    simp only [mem_upFin, thr, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hxy
      have h1 : dcard α x < dcard α y := Finset.card_lt_card (lt_dnFin_ssub' hxy)
      exact absurd (hxmax y (mem_univ _)) (not_le_of_gt h1)
    · intro hy
      exact absurd (hex y) (not_le_of_gt hy)

omit hch in
lemma rk_mono {p q : ℕ} (h : p ≤ q) : rk α p ≤ rk α q :=
  Finset.card_le_card fun y hy => by
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, lt_of_lt_of_le hy.2 h⟩

omit hch in
lemma rk_lt_iff {p q : ℕ} (hp : p ∈ dvals α) : p < q ↔ rk α p < rk α q := by
  constructor
  · intro h
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨p, ?_, ?_⟩)
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, hy.2.trans h⟩
    · simp [hp, h]
    · simp
  · intro h
    by_contra hpq
    exact absurd (rk_mono (not_lt.1 hpq)) (not_le_of_gt h)

lemma downIndex_eq (x : α) : downIndex x = rk α (dcard α x) + 1 := by
  unfold downIndex rk
  congr 1
  refine Finset.card_bij (fun s _ => s.card) ?_ ?_ ?_
  · intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 hs
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hs1
    exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨u, mem_univ _, rfl⟩, Finset.card_lt_card hs2⟩
  · intro s hs t ht h
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hs).1
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 ht).1
    exact dnFin_eq_of_dcard_eq hch h
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp1
    exact ⟨dnFin u, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨u, mem_univ _, rfl⟩,
      (dnFin_ssub_iff hch).2 hp2⟩, rfl⟩

lemma upFins_eq_image : upFins α = (dvals α).image (thr α) := by
  ext s
  simp only [upFins, dvals, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, -, hz⟩ := Finset.mem_image.1 (beta_mem x)
    exact ⟨beta x, ⟨z, hz⟩, (upFin_eq_thr hch x).symm⟩
  · rintro ⟨p, ⟨z, rfl⟩, rfl⟩
    exact exists_upFin_eq_thr hch (Finset.mem_image.2 ⟨z, mem_univ _, rfl⟩)

lemma upIndex_eq (x : α) : upIndex x = rk α (beta x) + 1 := by
  unfold upIndex rk
  congr 1
  symm
  refine Finset.card_bij (fun p _ => thr α p) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · rw [upFins_eq_image hch]
      exact Finset.mem_image.2 ⟨p, hp1, rfl⟩
    · rw [upFin_eq_thr hch x]
      exact (thr_ssub_iff (p := p) (beta_mem x)).1 hp2
  · intro p hp q hq h
    exact thr_injOn (Finset.mem_coe.2 (Finset.mem_filter.1 hp).1)
      (Finset.mem_coe.2 (Finset.mem_filter.1 hq).1) h
  · intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.1 hs
    rw [upFins_eq_image hch] at hs1
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs1
    rw [upFin_eq_thr hch x] at hs2
    exact ⟨p, Finset.mem_filter.2 ⟨hp, (thr_ssub_iff (p := p) (beta_mem x)).2 hs2⟩, rfl⟩

end Thm630

section Main

variable (hne : ¬ ContainsPoset α (Fin 2 ⊕ Fin 2))
include hne

/-- CO-172 (Theorem 6.30, part 1). In a finite poset excluding `2 + 2`, the number of distinct
down sets equals the number of distinct up sets. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem card_dnFins_eq_card_upFins : (dnFins α).card = (upFins α).card := by
  have hch := dnFin_chain hne
  rw [upFins_eq_image hch, Finset.card_image_of_injOn thr_injOn]
  have h : dvals α = (dnFins α).image Finset.card := by
    unfold dvals dnFins
    rw [Finset.image_image]
    rfl
  rw [h, Finset.card_image_of_injOn]
  intro s hs t ht hst
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hs)
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
  exact dnFin_eq_of_dcard_eq hch hst

/-- CO-172 (Theorem 6.30, part 2). The intervals `I(x) = [i, j]` are well formed: `i ≤ j`. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem downIndex_le_upIndex (x : α) : downIndex x ≤ upIndex x := by
  have hch := dnFin_chain hne
  rw [downIndex_eq hch, upIndex_eq hch]
  exact Nat.succ_le_succ (rk_mono (dcard_le_beta (lt_irrefl x)))

/-- CO-172 (Theorem 6.30, part 3). The intervals `I(x) = [i, j]`, `I(y) = [k, l]` represent the
order: `x < y` exactly when `j < k`. -/
@[kb "kellertrotter2017" "Theorem 6.30, p. 154"]
theorem lt_iff_upIndex_lt_downIndex (x y : α) : x < y ↔ upIndex x < downIndex y := by
  have hch := dnFin_chain hne
  rw [upIndex_eq hch, downIndex_eq hch, Nat.add_lt_add_iff_right, ← rk_lt_iff (beta_mem x)]
  have h := upFin_eq_thr hch x
  have h2 : y ∈ upFin x ↔ y ∈ thr α (beta x) := by rw [h]
  simpa [thr] using h2

end Main

end

/-! ### CO-138: standard ways to build posets (Example 6.7) -/

section StandardPosets

/-- CO-138 (1). A family `F` of sets is partially ordered by inclusion: the subtype `↥F` carries
Mathlib's order induced from `⊆`, and `A ≤ B` means `A ⊆ B`. -/
@[kb "kellertrotter2017" "Example 6.7, p. 141"]
theorem family_le_iff {β : Type*} (F : Set (Set β)) (A B : F) :
    A ≤ B ↔ (A : Set β) ⊆ B := Iff.rfl

/-- A positive integer, ordered by divisibility (a type synonym, so that the divisibility order
does not clash with the usual order on `ℕ`). -/
structure DvdPos where
  /-- The underlying natural number. -/
  val : ℕ
  /-- It is positive. -/
  pos : 0 < val

/-- CO-138 (2). Positive integers are partially ordered by divisibility: `m ≤ n` iff `m ∣ n`.
Any set `X` of positive integers inherits this order as the subtype `↥X`. -/
@[kb "kellertrotter2017" "Example 6.7, p. 141"]
instance : PartialOrder DvdPos where
  le m n := m.val ∣ n.val
  le_refl m := dvd_refl m.val
  le_trans _ _ _ h1 h2 := dvd_trans h1 h2
  le_antisymm m n h1 h2 := by
    have : m.val = n.val := Nat.dvd_antisymm h1 h2
    cases m; cases n; simp_all

/-- CO-138 (2). `m ≤ n` in `DvdPos` exactly when `n ≡ 0 (mod m)`. -/
@[kb "kellertrotter2017" "Example 6.7, p. 141"]
theorem dvdPos_le_iff (m n : DvdPos) : m ≤ n ↔ m.val ∣ n.val := Iff.rfl

/-- CO-138 (3). A set `X` of real `t`-tuples is partially ordered coordinatewise: the subtype `↥X`
of `Fin t → ℝ` (Mathlib's `Pi` order). -/
@[kb "kellertrotter2017" "Example 6.7, p. 141"]
theorem tuple_le_iff {t : ℕ} (X : Set (Fin t → ℝ)) (a b : X) :
    a ≤ b ↔ ∀ i, (a : Fin t → ℝ) i ≤ (b : Fin t → ℝ) i := Iff.rfl

/-- CO-138 (4). The intersection of linear orders `L_1, ..., L_k` (`k ≥ 1`) on the same set is a
partial order: `x ≤ y` iff `x ≤ y` in every `L_i`. -/
@[kb "kellertrotter2017" "Example 6.7, p. 141"]
theorem isPartialOrder_inter {β ι : Type*} [Nonempty ι] (r : ι → β → β → Prop)
    (h : ∀ i, IsLinearOrder β (r i)) : IsPartialOrder β (fun x y => ∀ i, r i x y) := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  exact
    { refl := fun x i => (h i).refl x
      trans := fun x y z hxy hyz i => (h i).trans x y z (hxy i) (hyz i)
      antisymm := fun x y hxy hyx => (h i0).antisymm x y (hxy i0) (hyx i0) }

/-- CO-138 (4), link with the dimension machinery: a realizer of a poset is a family of linear
orders whose intersection is the order of the poset. -/
theorem isRealizer_iff {t : ℕ} (r : Fin t → α → α → Prop) :
    IsRealizer r ↔ (∀ i, IsLinearOrder α (r i)) ∧ ∀ x y : α, x ≤ y ↔ ∀ i, r i x y := Iff.rfl

end StandardPosets

/-! ### CO-343: Dedekind cuts of the rationals -/

section Cuts

/-- CO-343. A Dedekind cut of `ℚ`: a nonempty proper subset that is closed downward and has no
largest element. -/
@[kb "kellertrotter2017" "Definition (unnumbered) Dedekind cut, p. 379"]
def IsCut (S : Set ℚ) : Prop :=
  S.Nonempty ∧ S ≠ Set.univ ∧ (∀ x ∈ S, ∀ y, y < x → y ∈ S) ∧ ∀ x ∈ S, ∃ y ∈ S, x < y

/-- CO-343. The rational cut of `q`: all rationals below `q`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) rational cut, p. 379"]
def rationalCut (q : ℚ) : Set ℚ := {p | p < q}

/-- CO-343. A rational cut is a cut. -/
@[kb "kellertrotter2017" "Definition (unnumbered) rational cut, p. 379"]
theorem isCut_rationalCut (q : ℚ) : IsCut (rationalCut q) := by
  refine ⟨⟨q - 1, by simp [rationalCut]⟩, fun h => ?_, fun x hx y hy => ?_, fun x hx => ?_⟩
  · have : q ∈ rationalCut q := by rw [h]; trivial
    exact lt_irrefl q this
  · exact lt_trans hy hx
  · refine ⟨(x + q) / 2, ?_, ?_⟩ <;> simp only [rationalCut, Set.mem_ofPred_eq] at hx ⊢ <;> linarith

/-- CO-343. `q ↦ q̄` is order preserving and reflects the order: `q̄ ⊆ r̄ ↔ q ≤ r`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) rational cut, p. 379"]
theorem rationalCut_subset_iff (q r : ℚ) : rationalCut q ⊆ rationalCut r ↔ q ≤ r := by
  constructor
  · intro h
    by_contra hqr
    push Not at hqr
    have : (q + r) / 2 ∈ rationalCut q := by
      simp only [rationalCut, Set.mem_ofPred_eq]; linarith
    have h2 := h this
    simp only [rationalCut, Set.mem_ofPred_eq] at h2
    linarith
  · intro h p hp
    simp only [rationalCut, Set.mem_ofPred_eq] at hp ⊢
    exact lt_of_lt_of_le hp h

/-- CO-343. The map `q ↦ q̄` is injective. -/
@[kb "kellertrotter2017" "Definition (unnumbered) rational cut, p. 379"]
theorem rationalCut_injective : Function.Injective rationalCut := fun q r h =>
  le_antisymm ((rationalCut_subset_iff q r).1 h.subset) ((rationalCut_subset_iff r q).1 h.symm.subset)

/-- The book's irrational cut `{p : p ≤ 0} ∪ {p : p² < 2}`. -/
def sqrtTwoCut : Set ℚ := {p | p ≤ 0 ∨ p ^ 2 < 2}

/-- CO-343. The set `{p ≤ 0} ∪ {p : p² < 2}` is a cut. -/
@[kb "kellertrotter2017" "Definition (unnumbered) Dedekind cut, p. 379"]
theorem isCut_sqrtTwoCut : IsCut sqrtTwoCut := by
  refine ⟨⟨0, Or.inl le_rfl⟩, fun h => ?_, fun x hx y hy => ?_, fun x hx => ?_⟩
  · have : (2 : ℚ) ∈ sqrtTwoCut := by rw [h]; trivial
    rcases this with h | h <;> norm_num at h
  · rcases hx with hx | hx
    · exact Or.inl (by linarith)
    · by_cases hy0 : y ≤ 0
      · exact Or.inl hy0
      · right
        push Not at hy0
        nlinarith
  · rcases hx with hx | hx
    · exact ⟨1, Or.inr (by norm_num), by linarith⟩
    · by_cases hx0 : x ≤ 0
      · exact ⟨1, Or.inr (by norm_num), by linarith⟩
      · push Not at hx0
        have hx2 : x < 2 := by nlinarith
        set δ : ℚ := (2 - x ^ 2) / (2 * x + 2) with hδ
        have hden : 0 < 2 * x + 2 := by linarith
        have hδpos : 0 < δ := div_pos (by linarith) hden
        have hδ1 : δ ≤ 1 := by
          rw [hδ, div_le_one hden]; nlinarith
        have hδeq : δ * (2 * x + 2) = 2 - x ^ 2 := by
          rw [hδ]; field_simp
        refine ⟨x + δ, Or.inr ?_, by linarith⟩
        nlinarith

/-- CO-343. The cut `{p ≤ 0} ∪ {p : p² < 2}` is not a rational cut (there is no rational square
root of `2`). -/
@[kb "kellertrotter2017" "Definition (unnumbered) rational cut, p. 379"]
theorem sqrtTwoCut_not_rational : ∀ q : ℚ, sqrtTwoCut ≠ rationalCut q := by
  intro q hq
  have hmem : ∀ p : ℚ, (p ≤ 0 ∨ p ^ 2 < 2) ↔ p < q := fun p => by
    have := Set.ext_iff.1 hq p
    simpa [sqrtTwoCut, rationalCut] using this
  have hq2 : q ^ 2 ≠ 2 := by
    intro h
    have : Irrational (Real.sqrt 2) := irrational_sqrt_two
    apply this
    refine ⟨|q|, ?_⟩
    have h' : ((|q| : ℚ) : ℝ) ^ 2 = 2 := by
      push_cast
      rw [sq_abs]; exact_mod_cast h
    have hnn : (0 : ℝ) ≤ ((|q| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg q
    rw [← h', Real.sqrt_sq hnn]
  by_cases hq0 : q ≤ 0
  · exact lt_irrefl q ((hmem q).1 (Or.inl hq0))
  push Not at hq0
  rcases lt_or_gt_of_ne hq2 with hlt | hgt
  · exact lt_irrefl q ((hmem q).1 (Or.inr hlt))
  · set r : ℚ := 2 / q with hr
    have hqr : q * r = 2 := by rw [hr]; field_simp
    have hrpos : 0 < r := div_pos (by norm_num) hq0
    have hrq : r < q := by nlinarith
    have hp : (q + r) / 2 < q := by linarith
    rcases (hmem _).2 hp with h | h
    · linarith
    · nlinarith [sq_nonneg (q - r)]

end Cuts

end UndergradKB.Combinatorics.Order
