import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.GabrielBasics
import UndergradKB.RepresentationTheory.ProblemsQuiversSym2

/-! # Problem 2.23: two-dimensional representations of a quiver (Etingof et al.)

For a finite quiver without oriented cycles, a representation with total dimension `2` is either
`S_i ⊕ S_i`, or `S_i ⊕ S_j` with `i ≠ j`, or has one-dimensional spaces at `i ≠ j`, a nonzero arrow map
`i → j`, no arrow `j → i`, and is indecomposable (a non-split extension of `S_i` by `S_j`); see
`twoDim_quiver_classification`.
-/

namespace UndergradKB.RepresentationTheory

section QuiverTwoDim

open scoped Classical

open _root_.Quiver

universe u v w w' a

/-- Combinatorial step: a function `Q → ℕ` with total `2` is `2` at one point or `1` at two points. -/
theorem dim_cases {Q : Type v} [Fintype Q] (f : Q → ℕ) (h : ∑ x, f x = 2) :
    (∃ i, f i = 2 ∧ ∀ x, x ≠ i → f x = 0) ∨
      (∃ i j, i ≠ j ∧ f i = 1 ∧ f j = 1 ∧ ∀ x, x ≠ i → x ≠ j → f x = 0) := by
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at h
  have hsplit := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  have hle : f i ≤ 2 := by
    rw [← h]; exact Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hrest : ∑ x ∈ Finset.univ.erase i, f x = 2 - f i := by omega
  rcases (by omega : f i = 1 ∨ f i = 2) with h1 | h2
  · right
    rw [h1] at hrest
    obtain ⟨j, hjm, hj⟩ : ∃ j ∈ Finset.univ.erase i, f j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [Finset.sum_eq_zero hcon] at hrest
      omega
    have hjle : f j ≤ 1 := by
      rw [show (1 : ℕ) = 2 - 1 from rfl, ← hrest]
      exact Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hjm
    have hj1 : f j = 1 := by omega
    have hsplit2 := Finset.add_sum_erase _ f hjm
    have hz : ∑ x ∈ (Finset.univ.erase i).erase j, f x = 0 := by omega
    refine ⟨i, j, (Finset.mem_erase.mp hjm).1.symm, h1, hj1, fun x hxi hxj => ?_⟩
    exact (Finset.sum_eq_zero_iff.mp hz) x
      (Finset.mem_erase.mpr ⟨hxj, Finset.mem_erase.mpr ⟨hxi, Finset.mem_univ _⟩⟩)
  · left
    rw [h2] at hrest
    refine ⟨i, h2, fun x hx => ?_⟩
    exact (Finset.sum_eq_zero_iff.mp (by simpa using hrest)) x
      (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩)

namespace QRep

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

theorem map_eq_zero_of_subsingleton {V : QRep.{u, v, w, a} k Q} {x y : Q} (e : x ⟶ y)
    (h : Subsingleton (V.obj x) ∨ Subsingleton (V.obj y)) : V.map e = 0 := by
  rcases h with h | h
  · refine LinearMap.ext fun v => ?_
    rw [Subsingleton.elim v 0]; simp
  · exact LinearMap.ext fun v => Subsingleton.elim _ _

theorem isomorphic_of_map_eq_zero {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q}
    [∀ x, Module.Finite k (V.obj x)] [∀ x, Module.Finite k (W.obj x)]
    (hV : ∀ {x y : Q} (e : x ⟶ y), V.map e = 0) (hW : ∀ {x y : Q} (e : x ⟶ y), W.map e = 0)
    (hd : ∀ x, Module.finrank k (V.obj x) = Module.finrank k (W.obj x)) : Isomorphic V W := by
  let E : ∀ x, V.obj x ≃ₗ[k] W.obj x := fun x => LinearEquiv.ofFinrankEq _ _ (hd x)
  refine ⟨⟨fun x => (E x).toLinearMap, fun {x y} e => ?_⟩,
    ⟨fun x => (E x).symm.toLinearMap, fun {x y} e => ?_⟩, ?_, ?_⟩
  · rw [hV e, hW e]; simp
  · rw [hV e, hW e]; simp
  · apply Hom.ext; intro x
    exact LinearMap.ext fun z => (E x).apply_symm_apply z
  · apply Hom.ext; intro x
    exact LinearMap.ext fun z => (E x).symm_apply_apply z

instance directSum_obj_finite {V W : QRep.{u, v, w, a} k Q} [∀ x, Module.Finite k (V.obj x)]
    [∀ x, Module.Finite k (W.obj x)] (x : Q) : Module.Finite k ((directSum V W).obj x) :=
  inferInstanceAs (Module.Finite k (V.obj x × W.obj x))

theorem finrank_directSum_obj {V W : QRep.{u, v, w, a} k Q} [∀ x, Module.Finite k (V.obj x)]
    [∀ x, Module.Finite k (W.obj x)] (x : Q) :
    Module.finrank k ((directSum V W).obj x) =
      Module.finrank k (V.obj x) + Module.finrank k (W.obj x) :=
  Module.finrank_prod (R := k) (M := V.obj x) (M' := W.obj x)

theorem directSum_simpleRep_map (i j : Q) {x y : Q} (e : x ⟶ y) :
    (directSum (simpleRep k i : QRep.{u, v, u, a} k Q)
      (simpleRep k j : QRep.{u, v, u, a} k Q)).map e = 0 :=
  LinearMap.ext fun v => Prod.ext rfl rfl

/-- In a one-dimensional space, complementary subspaces are `⊥, ⊤` in some order. -/
theorem one_dim_isCompl {M : Type*} [AddCommGroup M] [Module k M] (h : Module.finrank k M = 1)
    {S T : Submodule k M} (hST : IsCompl S T) : (S = ⊥ ∧ T = ⊤) ∨ (S = ⊤ ∧ T = ⊥) := by
  haveI : IsSimpleModule k M := isSimpleModule_iff_finrank_eq_one.2 h
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS <;>
    rcases IsSimpleOrder.eq_bot_or_eq_top T with hT | hT
  · have h := hST.sup_eq_top
    rw [hS, hT, sup_idem] at h
    exact absurd h bot_ne_top
  · exact Or.inl ⟨hS, hT⟩
  · exact Or.inr ⟨hS, hT⟩
  · have h := hST.inf_eq_bot
    rw [hS, hT, inf_idem] at h
    exact absurd h top_ne_bot

/-- A representation with one-dimensional spaces at `i`, `j`, zero spaces elsewhere and a nonzero map along an
arrow `i → j` is indecomposable. -/
theorem isIndecomposable_of_nonzero_arrow {V : QRep.{u, v, w, a} k Q} {i j : Q}
    (hi : Module.finrank k (V.obj i) = 1) (hj : Module.finrank k (V.obj j) = 1)
    (hrest : ∀ x, x ≠ i → x ≠ j → Subsingleton (V.obj x)) (e : i ⟶ j) (he : V.map e ≠ 0) :
    V.IsIndecomposable := by
  haveI : Nontrivial (V.obj i) := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hbot : ∀ S : Subrep V, S.carrier i = ⊥ → S.carrier j = ⊥ → S = ⊥ := by
    intro S h1 h2
    apply Subrep.ext
    intro x
    rw [Subrep.bot_carrier]
    by_cases hxi : x = i
    · subst hxi; exact h1
    by_cases hxj : x = j
    · subst hxj; exact h2
    haveI := hrest x hxi hxj
    exact Submodule.eq_bot_of_subsingleton
  have hne : ∃ v, V.map e v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he (LinearMap.ext fun v => hcon v)
  obtain ⟨v, hv⟩ := hne
  refine ⟨fun h => ?_, fun S T hST => ?_⟩
  · have := congrArg (fun T : Subrep V => T.carrier i) h
    simp only [Subrep.bot_carrier, Subrep.top_carrier] at this
    exact bot_ne_top this
  · have hv' : ∀ (R : Subrep V), R.carrier i = ⊤ → R.carrier j = ⊥ → False := by
      intro R h1 h2
      have := R.map_mem e (x := v) (by rw [h1]; trivial)
      rw [h2, Submodule.mem_bot] at this
      exact hv this
    rcases one_dim_isCompl hi (hST i) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases one_dim_isCompl hj (hST j) with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl (hbot S h1 h3)
    · exact (hv' T h2 h4).elim
    · exact (hv' S h1 h3).elim
    · exact Or.inr (hbot T h2 h4)

/-- **Etingof et al., Problem 2.23 (two-dimensional representations)**: let `Q` be a finite quiver without
oriented cycles and `V` a representation of `Q` with finite-dimensional spaces and total dimension `2`.  Then
either `V ≅ S_i ⊕ S_i`; or `V ≅ S_i ⊕ S_j` with `i ≠ j`; or there are vertices `i ≠ j` with `V_i`, `V_j`
one-dimensional, `V_x = 0` elsewhere, no arrow `j → i`, some arrow `i → j` with nonzero map, and `V` is
indecomposable (a non-split extension of `S_i` by `S_j`, whose class lies in `Ext¹(S_i, S_j)`, the space of
vectors indexed by the arrows `i → j`). -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
theorem twoDim_quiver_classification [Fintype Q] (hQ : NoOrientedCycles Q) (V : QRep.{u, v, w, a} k Q)
    [∀ x, Module.Finite k (V.obj x)] (hdim : ∑ x, Module.finrank k (V.obj x) = 2) :
    (∃ i, Isomorphic V (directSum (simpleRep k i : QRep.{u, v, u, a} k Q) (simpleRep k i))) ∨
      (∃ i j, i ≠ j ∧
        Isomorphic V (directSum (simpleRep k i : QRep.{u, v, u, a} k Q) (simpleRep k j))) ∨
      (∃ i j, i ≠ j ∧ V.IsIndecomposable ∧ Module.finrank k (V.obj i) = 1 ∧
        Module.finrank k (V.obj j) = 1 ∧ (∀ x, x ≠ i → x ≠ j → Subsingleton (V.obj x)) ∧
        IsEmpty (j ⟶ i) ∧ ∃ e : i ⟶ j, V.map e ≠ 0) := by
  have hloop : ∀ {x : Q} (e : x ⟶ x), False := fun {x} e => by
    have := hQ x (Path.cons Path.nil e)
    simp at this
  rcases dim_cases (fun x => Module.finrank k (V.obj x)) hdim with
    ⟨i, hi, hrest⟩ | ⟨i, j, hij, hi, hj, hrest⟩
  · left
    refine ⟨i, ?_⟩
    have hsub : ∀ x, x ≠ i → Subsingleton (V.obj x) := fun x hx =>
      Module.finrank_zero_iff.mp (hrest x hx)
    have hz : ∀ {x y : Q} (e : x ⟶ y), V.map e = 0 := by
      intro x y e
      by_cases hx : x = i
      · subst hx
        have hy : y ≠ x := by rintro rfl; exact hloop e
        exact map_eq_zero_of_subsingleton e (Or.inr (hsub y hy))
      · exact map_eq_zero_of_subsingleton e (Or.inl (hsub x hx))
    refine isomorphic_of_map_eq_zero hz (fun e => directSum_simpleRep_map i i e) ?_
    intro x
    rw [finrank_directSum_obj, finrank_simpleRep_obj]
    by_cases hx : x = i
    · subst hx; simpa using hi
    · simpa [hx] using hrest x hx
  · right
    have hi' : Module.finrank k (V.obj i) = 1 := hi
    have hj' : Module.finrank k (V.obj j) = 1 := hj
    by_cases hall : ∀ {x y : Q} (e : x ⟶ y), V.map e = 0
    · left
      refine ⟨i, j, hij, isomorphic_of_map_eq_zero hall (fun e => directSum_simpleRep_map i j e) ?_⟩
      intro x
      rw [finrank_directSum_obj, finrank_simpleRep_obj, finrank_simpleRep_obj]
      by_cases hxi : x = i
      · subst hxi; rw [if_pos rfl, if_neg hij]; exact hi'
      by_cases hxj : x = j
      · subst hxj; rw [if_neg hxi, if_pos rfl]; simpa using hj'
      rw [if_neg hxi, if_neg hxj]; exact hrest x hxi hxj
    · right
      push Not at hall
      obtain ⟨x, y, e, he⟩ := hall
      have hsupp : ∀ z, ¬ Subsingleton (V.obj z) → z = i ∨ z = j := by
        intro z hz
        by_contra hcon
        push Not at hcon
        exact hz (Module.finrank_zero_iff.mp (hrest z hcon.1 hcon.2))
      have hx : ¬ Subsingleton (V.obj x) := fun h => he (map_eq_zero_of_subsingleton e (Or.inl h))
      have hy : ¬ Subsingleton (V.obj y) := fun h => he (map_eq_zero_of_subsingleton e (Or.inr h))
      have hxy : x ≠ y := by rintro rfl; exact hloop e
      have key : ∀ (p q : Q), p ≠ q → Module.finrank k (V.obj p) = 1 → Module.finrank k (V.obj q) = 1 →
          (∀ z, z ≠ p → z ≠ q → Subsingleton (V.obj z)) → ∀ (e : p ⟶ q), V.map e ≠ 0 →
          ∃ i j, i ≠ j ∧ V.IsIndecomposable ∧ Module.finrank k (V.obj i) = 1 ∧
            Module.finrank k (V.obj j) = 1 ∧ (∀ x, x ≠ i → x ≠ j → Subsingleton (V.obj x)) ∧
            IsEmpty (j ⟶ i) ∧ ∃ e : i ⟶ j, V.map e ≠ 0 := by
        intro p q hpq hp hq hr e he
        refine ⟨p, q, hpq, isIndecomposable_of_nonzero_arrow hp hq hr e he, hp, hq, hr, ?_, e, he⟩
        refine ⟨fun e' => ?_⟩
        have := hQ p (Path.cons (Path.cons Path.nil e) e')
        simp at this
      rcases hsupp x hx with rfl | rfl <;> rcases hsupp y hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact key x y hij hi' hj' (fun z h1 h2 => Module.finrank_zero_iff.mp (hrest z h1 h2)) e he
      · exact key x y hij.symm hj' hi' (fun z h1 h2 => Module.finrank_zero_iff.mp (hrest z h2 h1)) e he
      · exact (hxy rfl).elim

end QRep

end QuiverTwoDim

end UndergradKB.RepresentationTheory
