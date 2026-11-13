import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Data.Finsupp.WellFounded
import UndergradKB.Common.Attr

/-!
# Ordinals, wave 2 (Morris, Topology Without Tears, Appendix 1, section A1.4)

* TP-421: two von Neumann ordinals that are order isomorphic (as sets well ordered by membership)
  are equal.
* TP-428: the book's definition of ordinal exponentiation `α ^ β` as a set of finitely supported
  functions `β → α` with a lexicographic order has the order type of `Ordinal.opow`.
-/

universe u

namespace UndergradKB.Topology

/-! ### TP-421 -/

private theorem fixed_of_relIso {x y : ZFSet.{u}} (hx : x.IsOrdinal) (hy : y.IsOrdinal)
    (f : Subrel (· ∈ ·) (· ∈ x) ≃r Subrel (· ∈ ·) (· ∈ y)) :
    ∀ z : ZFSet.{u}, ∀ hz : z ∈ x, (f ⟨z, hz⟩).1 = z := by
  intro z
  induction z using ZFSet.inductionOn with
  | _ z ih =>
  intro hz
  refine ZFSet.ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · have hfy : (f ⟨z, hz⟩).1 ∈ y := (f ⟨z, hz⟩).2
    have hwy : w ∈ y := hy.subset_of_mem hfy hw
    have h1 : f (f.symm ⟨w, hwy⟩) = ⟨w, hwy⟩ := f.apply_symm_apply _
    have h2 : (f.symm ⟨w, hwy⟩).1 ∈ z := by
      refine (f.map_rel_iff (a := f.symm ⟨w, hwy⟩) (b := ⟨z, hz⟩)).1 ?_
      show (f (f.symm ⟨w, hwy⟩)).1 ∈ (f ⟨z, hz⟩).1
      rw [h1]
      exact hw
    have h3 := ih _ h2 (f.symm ⟨w, hwy⟩).2
    have h4 : w = (f.symm ⟨w, hwy⟩).1 := by
      rw [← h3]
      exact (congrArg Subtype.val h1).symm
    rw [h4]
    exact h2
  · have hwx : w ∈ x := hx.subset_of_mem hz hw
    have h3 := ih w hw hwx
    have : (f ⟨w, hwx⟩).1 ∈ (f ⟨z, hz⟩).1 :=
      (f.map_rel_iff (a := ⟨w, hwx⟩) (b := ⟨z, hz⟩)).2 hw
    rw [h3] at this
    exact this

private theorem subset_of_relIso {x y : ZFSet.{u}} (hx : x.IsOrdinal) (hy : y.IsOrdinal)
    (f : Subrel (· ∈ ·) (· ∈ x) ≃r Subrel (· ∈ ·) (· ∈ y)) : x ⊆ y := by
  intro z hz
  have := fixed_of_relIso hx hy f z hz
  rw [← this]
  exact (f ⟨z, hz⟩).2

/-- Morris, Topology Without Tears, Proposition A1.4.12 (TP-421). Two (von Neumann) ordinals that are
order isomorphic, as sets well ordered by membership, are equal. -/
@[kb "morris2024" "Proposition A1.4.12, p. 420"]
theorem isOrdinal_eq_of_relIso {x y : ZFSet.{u}} (hx : x.IsOrdinal) (hy : y.IsOrdinal)
    (f : Subrel (· ∈ ·) (· ∈ x) ≃r Subrel (· ∈ ·) (· ∈ y)) : x = y :=
  ZFSet.ext fun w => ⟨fun h => subset_of_relIso hx hy f h, fun h => subset_of_relIso hy hx f.symm h⟩

/-! ### TP-428 -/

section Expo

open Ordinal

/-- The set `α ^ β` of Morris, Definition A1.4.25: functions from the set `β` (the ordinals below `β`)
to the set `α`, equal to `0` outside a finite set. They are encoded as finitely supported functions
`Ordinal →₀ Ordinal` whose support lies below `β` and whose values below `β` lie below `α`. -/
def FinsuppExpo (α β : Ordinal.{u}) : Type (u + 1) :=
  {f : Ordinal.{u} →₀ Ordinal.{u} // (∀ e < β, f e < α) ∧ ∀ e ∈ f.support, e < β}

/-- The lexicographic order of Definition A1.4.25, comparing two functions at the largest index where
they differ. (Comparing at the smallest such index, as the text literally says, does not give a
well order: see `not_wellFounded_smallest_index`.) -/
def colexLT (α β : Ordinal.{u}) (f g : FinsuppExpo α β) : Prop :=
  ∃ e, f.1 e < g.1 e ∧ ∀ e', e < e' → f.1 e' = g.1 e'

theorem finsupp_decomp (f : Ordinal.{u} →₀ Ordinal.{u}) (e : Ordinal.{u}) :
    f = f.filter (e < ·) + (Finsupp.single e (f e) + f.filter (· < e)) := by
  classical
  ext a
  simp only [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.single_apply]
  rcases lt_trichotomy a e with h | h | h
  · simp [h, h.ne', h.not_gt]
  · subst h
    simp
  · simp [h, h.ne, h.not_gt]

theorem eval_lt_of_colex {b : Ordinal.{u}} (hb : 1 < b) {f g : Ordinal.{u} →₀ Ordinal.{u}}
    (hf : ∀ e, f e < b) (hg : ∀ e, g e < b) (e : Ordinal.{u}) (h1 : f e < g e)
    (h2 : ∀ e', e < e' → f e' = g e') : CNF.eval b f < CNF.eval b g := by
  classical
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hH : f.filter (e < ·) = g.filter (e < ·) := by
    ext a
    simp only [Finsupp.filter_apply]
    split_ifs with h
    · exact h2 a h
    · rfl
  have key : ∀ k : Ordinal.{u} →₀ Ordinal.{u}, (∀ a, k a < b) →
      CNF.eval b k = CNF.eval b (k.filter (e < ·)) + (b ^ e * k e + CNF.eval b (k.filter (· < e))) := by
    intro k hk
    have hL : ∀ a ∈ (k.filter (· < e)).support, a < e := by
      intro a ha
      simp only [Finsupp.mem_support_iff, Finsupp.filter_apply] at ha
      by_contra hne
      exact ha (by simp [hne])
    conv_lhs => rw [finsupp_decomp k e]
    rw [CNF.eval_add, CNF.eval_single_add' b hL]
    intro e1 he1 e2 he2
    have he1' : e < e1 := by
      simp only [Finsupp.mem_support_iff, Finsupp.filter_apply] at he1
      by_contra hne
      exact he1 (by simp [hne])
    rcases Finset.mem_union.1 (Finsupp.support_add he2) with h | h
    · have := Finsupp.support_single_subset h
      rw [Finset.mem_singleton] at this
      exact this ▸ he1'.le
    · exact (hL e2 h).le.trans he1'.le
  have hLb : ∀ k : Ordinal.{u} →₀ Ordinal.{u}, (∀ a, k a < b) →
      CNF.eval b (k.filter (· < e)) < b ^ e := by
    intro k hk
    refine CNF.eval_lt (fun a => ?_) (fun a ha => ?_)
    · simp only [Finsupp.filter_apply]
      split_ifs
      · exact hk a
      · exact hb0
    · simp only [Finsupp.mem_support_iff, Finsupp.filter_apply] at ha
      by_contra hne
      exact ha (by simp [hne])
  rw [key f hf, key g hg, hH]
  refine (add_lt_add_iff_left _).2 ?_
  calc b ^ e * f e + CNF.eval b (f.filter (· < e))
      < b ^ e * f e + b ^ e := (add_lt_add_iff_left _).2 (hLb f hf)
    _ = b ^ e * (f e + 1) := (mul_add_one _ _).symm
    _ ≤ b ^ e * g e := by
        apply mul_le_mul_right
        exact Order.add_one_le_of_lt h1
    _ ≤ b ^ e * g e + CNF.eval b (g.filter (· < e)) := le_self_add

theorem colex_trichotomy {α β : Ordinal.{u}} (f g : FinsuppExpo α β) :
    f = g ∨ colexLT α β f g ∨ colexLT α β g f := by
  classical
  by_cases hfg : f = g
  · exact Or.inl hfg
  right
  have hne : f.1 ≠ g.1 := fun h => hfg (Subtype.ext h)
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hne
  let S : Finset Ordinal.{u} := (f.1.support ∪ g.1.support).filter (fun e => f.1 e ≠ g.1 e)
  have hS : S.Nonempty := ⟨a, by
    simp only [S, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff]
    refine ⟨?_, ha⟩
    by_contra h
    push Not at h
    exact ha (h.1.trans h.2.symm)⟩
  let e := S.max' hS
  have heS : e ∈ S := S.max'_mem hS
  have hne_e : f.1 e ≠ g.1 e := (Finset.mem_filter.1 heS).2
  have hgt : ∀ e', e < e' → f.1 e' = g.1 e' := by
    intro e' he'
    by_contra hne'
    have : e' ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff]
      refine ⟨?_, hne'⟩
      by_contra h
      push Not at h
      exact hne' (h.1.trans h.2.symm)
    exact absurd (S.le_max' e' this) (not_le.2 he')
  rcases lt_or_gt_of_ne hne_e with h | h
  · exact Or.inl ⟨e, h, hgt⟩
  · exact Or.inr ⟨e, h, fun e' he' => (hgt e' he').symm⟩

theorem coeff_mem_FinsuppExpo {α β o : Ordinal.{u}} (hα : 1 < α) (ho : o < α ^ β) :
    (∀ e < β, CNF.coeff α o e < α) ∧ ∀ e ∈ (CNF.coeff α o).support, e < β := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  refine ⟨fun e _ => ?_, fun e he => ?_⟩
  · by_cases h : e ∈ (CNF α o).map Prod.fst
    · obtain ⟨⟨e', c⟩, hp, rfl⟩ := List.mem_map.1 h
      rw [CNF.coeff_of_mem_CNF hp]
      exact CNF.snd_lt hα hp
    · rw [CNF.coeff_of_notMem_CNF h]
      exact hα0
  · rw [CNF.support_coeff, List.mem_toFinset] at he
    obtain ⟨⟨e', c⟩, hp, rfl⟩ := List.mem_map.1 he
    have ho0 : o ≠ 0 := by
      rintro rfl
      simp at hp
    exact (CNF.fst_le_log hp).trans_lt ((lt_opow_iff_log_lt hα ho0).1 ho)

/-- Morris, Topology Without Tears, Definition A1.4.25 (TP-428). For ordinals `α > 1`, the set of
finitely supported functions `β → α`, ordered lexicographically (largest differing index first), is
order isomorphic to the ordinals below Mathlib's `α ^ β`. -/
theorem exists_relIso_opow_of_one_lt {α β : Ordinal.{u}} (hα : 1 < α) :
    Nonempty (colexLT α β ≃r ((· < ·) : Set.Iio (α ^ β) → Set.Iio (α ^ β) → Prop)) := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hall : ∀ f : FinsuppExpo α β, ∀ e, f.1 e < α := by
    intro f e
    by_cases he : e < β
    · exact f.2.1 e he
    · have : e ∉ f.1.support := fun h => he (f.2.2 e h)
      rw [Finsupp.notMem_support_iff.1 this]
      exact hα0
  let ev : FinsuppExpo α β → Set.Iio (α ^ β) := fun f =>
    ⟨CNF.eval α f.1, CNF.eval_lt (hall f) f.2.2⟩
  have hinj : Function.Injective ev := by
    intro f g h
    apply Subtype.ext
    have h' : CNF.eval α f.1 = CNF.eval α g.1 := congrArg Subtype.val h
    rw [← CNF.coeff_eval hα (hall f), h', CNF.coeff_eval hα (hall g)]
  have hsurj : Function.Surjective ev := by
    rintro ⟨o, ho⟩
    obtain ⟨h1, h2⟩ := coeff_mem_FinsuppExpo hα ho
    refine ⟨⟨CNF.coeff α o, h1, h2⟩, Subtype.ext ?_⟩
    exact CNF.eval_coeff α o
  refine ⟨{ toEquiv := Equiv.ofBijective ev ⟨hinj, hsurj⟩, map_rel_iff' := ?_ }⟩
  intro f g
  show CNF.eval α f.1 < CNF.eval α g.1 ↔ colexLT α β f g
  constructor
  · intro h
    rcases colex_trichotomy f g with rfl | h' | h'
    · exact absurd h (lt_irrefl _)
    · exact h'
    · obtain ⟨e, he1, he2⟩ := h'
      exact absurd (eval_lt_of_colex hα (hall g) (hall f) e he1 he2) (not_lt.2 h.le)
  · rintro ⟨e, he1, he2⟩
    exact eval_lt_of_colex hα (hall f) (hall g) e he1 he2

theorem lt_one_eq_zero {o : Ordinal.{u}} (h : o < 1) : o = 0 := by
  by_contra hne
  exact absurd h (not_lt.2 (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hne)))

/-- The finitely supported functions into `{0}` (that is `α = 1`), or the empty family of indices
(`β = 0`), form a one-element set. -/
def uniqueFinsuppExpo {α β : Ordinal.{u}} (h0 : ∀ e < β, 0 < α) (h1 : ∀ e < β, α ≤ 1) :
    Unique (FinsuppExpo α β) where
  default := ⟨0, fun e he => by simpa using h0 e he, by simp⟩
  uniq f := by
    apply Subtype.ext
    ext e
    by_cases he : e < β
    · have : f.1 e < 1 := lt_of_lt_of_le (f.2.1 e he) (h1 e he)
      simpa using lt_one_eq_zero this
    · have : e ∉ f.1.support := fun h => he (f.2.2 e h)
      simpa using Finsupp.notMem_support_iff.1 this

instance (α β : Ordinal.{u}) : Std.Irrefl (colexLT α β) :=
  ⟨fun _ ⟨_, h, _⟩ => lt_irrefl _ h⟩

/-- Morris, Topology Without Tears, Definition A1.4.25 (TP-428). For all ordinals `α` and `β`, the set
of finitely supported functions `β → α`, ordered lexicographically at the largest index where two
functions differ, is order isomorphic to the ordinals below `α ^ β` (Mathlib's ordinal power); in
particular it is a well order of order type `α ^ β`. -/
@[kb "morris2024" "Definition A1.4.25, p. 423"]
theorem exists_relIso_opow (α β : Ordinal.{u}) :
    Nonempty (colexLT α β ≃r ((· < ·) : Set.Iio (α ^ β) → Set.Iio (α ^ β) → Prop)) := by
  rcases lt_trichotomy α 1 with h | h | h
  · obtain rfl : α = 0 := lt_one_eq_zero h
    by_cases hβ : β = 0
    · subst hβ
      rw [Ordinal.opow_zero]
      haveI : Unique (FinsuppExpo 0 0) :=
        uniqueFinsuppExpo (fun e he => (not_lt_zero he).elim)
          (fun e he => (not_lt_zero he).elim)
      haveI : Unique (Set.Iio (1 : Ordinal.{u})) :=
        { default := ⟨0, Set.mem_Iio.2 zero_lt_one⟩
          uniq := fun o => Subtype.ext (lt_one_eq_zero o.2) }
      exact ⟨RelIso.ofUniqueOfIrrefl _ _⟩
    · rw [Ordinal.zero_opow hβ]
      haveI : IsEmpty (FinsuppExpo 0 β) :=
        ⟨fun f => not_lt_zero (f.2.1 0 (pos_iff_ne_zero.2 hβ))⟩
      haveI : IsEmpty (Set.Iio (0 : Ordinal.{u})) := ⟨fun o => not_lt_zero (Set.mem_Iio.1 o.2)⟩
      exact ⟨RelIso.relIsoOfIsEmpty _ _⟩
  · subst h
    rw [Ordinal.one_opow]
    haveI : Unique (FinsuppExpo 1 β) :=
      uniqueFinsuppExpo (fun _ _ => zero_lt_one) (fun _ _ => le_rfl)
    haveI : Unique (Set.Iio (1 : Ordinal.{u})) :=
      { default := ⟨0, Set.mem_Iio.2 zero_lt_one⟩
        uniq := fun o => Subtype.ext (lt_one_eq_zero o.2) }
    exact ⟨RelIso.ofUniqueOfIrrefl _ _⟩
  · exact exists_relIso_opow_of_one_lt h

/-- Remark on Morris, Definition A1.4.25 (TP-428). If two functions are compared at the *smallest*
index where they differ (as the text of the definition literally says), the order is not a well
order already for `α = 2`, `β = ω`: the indicator functions of `{n}` form an infinite descending
chain. This is why `colexLT` compares at the largest differing index. -/
theorem not_wellFounded_smallest_index :
    ¬ WellFounded (fun f g : FinsuppExpo (2 : Ordinal.{u}) Ordinal.omega0.{u} =>
      ∃ e, f.1 e < g.1 e ∧ ∀ e' < e, f.1 e' = g.1 e') := by
  intro hwf
  have hs1 : ∀ n : ℕ, ∀ e < Ordinal.omega0.{u}, (Finsupp.single (n : Ordinal.{u}) (1 : Ordinal.{u})) e < 2 := by
    intro n e _
    rw [Finsupp.single_apply]
    split_ifs
    · exact one_lt_two
    · exact zero_lt_two
  have hs2 : ∀ n : ℕ, ∀ e ∈ (Finsupp.single (n : Ordinal.{u}) (1 : Ordinal.{u})).support, e < Ordinal.omega0.{u} := by
    intro n e he
    have := Finsupp.support_single_subset he
    rw [Finset.mem_singleton] at this
    rw [this]
    exact Ordinal.natCast_lt_omega0 n
  let s : ℕ → FinsuppExpo (2 : Ordinal.{u}) Ordinal.omega0.{u} := fun n =>
    ⟨Finsupp.single (n : Ordinal.{u}) (1 : Ordinal.{u}), hs1 n, hs2 n⟩
  have hdesc : ∀ n, ∃ e, (s (n + 1)).1 e < (s n).1 e ∧ ∀ e' < e, (s (n + 1)).1 e' = (s n).1 e' := by
    intro n
    refine ⟨(n : Ordinal), ?_, fun e he => ?_⟩
    · simp [s, Finsupp.single_apply]
    · have h1 : (n : Ordinal) ≠ e := he.ne'
      have h2 : (n : Ordinal) + 1 ≠ e := (he.trans (lt_add_one _)).ne'
      simp [s, Finsupp.single_apply, h1, h2]
  exact (wellFounded_iff_isEmpty_descending_chain.1 hwf).false ⟨s, hdesc⟩

end Expo

end UndergradKB.Topology
