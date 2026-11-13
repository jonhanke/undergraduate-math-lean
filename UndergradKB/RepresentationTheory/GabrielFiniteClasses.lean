import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Set.Finite.List
import UndergradKB.RepresentationTheory.GabrielConverseDefs
import UndergradKB.RepresentationTheory.GabrielBasics
import UndergradKB.Common.Attr

/-! # A quiver of finite type has finitely many orbits in each dimension (Etingof et al., Problem 5.4)

Part of the converse of Gabriel's theorem. If `Q` has only finitely many indecomposable representations up to
isomorphism, then for every dimension vector `d` the group `∏ GL(d_i)` has finitely many orbits on `Rep(d)`.

* `isomorphic_of_equiv`, `QRep.Isomorphic.exists_equiv`: isomorphisms as families of compatible linear equivalences.
* `MatRep.equiv_of_isomorphic`: isomorphic matrix representations lie in one orbit.
* `exists_matRep`: a finite-dimensional representation is isomorphic to a matrix representation.
* `sumList`: iterated direct sum; `exists_indecomposable_list`: every finite-dimensional representation is
  isomorphic to the sum of a list of finite-dimensional indecomposables.
* `IsFiniteType.exists_finite_orbits`: the headline statement.
-/

namespace UndergradKB.RepresentationTheory.Gabriel

open scoped Classical
open Roots QRep

noncomputable section

universe u a

variable {n : ℕ} [Q : Quiver.{a} (Fin n)] {k : Type u} [Field k]

/-! ### Isomorphisms as compatible families of linear equivalences -/

theorem isomorphic_of_equiv {V W : QRep.{u, 0, u, a} k (Fin n)} (e : ∀ i, V.obj i ≃ₗ[k] W.obj i)
    (h : ∀ {i j : Fin n} (a : i ⟶ j) (x : V.obj i), e j (V.map a x) = W.map a (e i x)) :
    V.Isomorphic W := by
  refine ⟨⟨fun i => (e i).toLinearMap, fun {i j} a => ?_⟩,
    ⟨fun i => (e i).symm.toLinearMap, fun {i j} a => ?_⟩, ?_, ?_⟩
  · ext x
    exact h a x
  · ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply (e j).injective
    rw [LinearEquiv.apply_symm_apply, h, LinearEquiv.apply_symm_apply]
  · apply Hom.ext
    intro i
    ext x
    simp
  · apply Hom.ext
    intro i
    ext x
    simp

theorem exists_equiv_of_isomorphic {V W : QRep.{u, 0, u, a} k (Fin n)} (h : V.Isomorphic W) :
    ∃ e : ∀ i, V.obj i ≃ₗ[k] W.obj i,
      ∀ {i j : Fin n} (a : i ⟶ j) (x : V.obj i), e j (V.map a x) = W.map a (e i x) := by
  obtain ⟨f, g, hfg, hgf⟩ := h
  have h1 : ∀ i, (f.app i).comp (g.app i) = LinearMap.id := fun i => by
    simpa using congrArg (fun h => Hom.app h i) hfg
  have h2 : ∀ i, (g.app i).comp (f.app i) = LinearMap.id := fun i => by
    simpa using congrArg (fun h => Hom.app h i) hgf
  refine ⟨fun i => LinearEquiv.ofLinearMap (f.app i) (g.app i) (h1 i) (h2 i), fun {i j} a x => ?_⟩
  exact LinearMap.congr_fun (f.comm a) x

/-! ### Matrix representations -/

/-- Isomorphic matrix representations lie in the same `∏ GL(d_i)`-orbit. -/
theorem MatRep.equiv_of_isomorphic {d : Fin n → ℕ} {x y : MatRep k d}
    (h : x.toQRep.Isomorphic y.toQRep) : MatRep.Equiv x y := by
  obtain ⟨f, g, hfg, hgf⟩ := h
  let F : ∀ i, (Fin (d i) → k) →ₗ[k] (Fin (d i) → k) := fun i => f.app i
  let G : ∀ i, (Fin (d i) → k) →ₗ[k] (Fin (d i) → k) := fun i => g.app i
  refine ⟨fun i => LinearMap.toMatrix' (F i), fun i => ?_, fun i j e => ?_⟩
  · have e1 : (F i).comp (G i) = LinearMap.id := congrArg (fun h => Hom.app h i) hfg
    have e2 : (G i).comp (F i) = LinearMap.id := congrArg (fun h => Hom.app h i) hgf
    refine ⟨⟨LinearMap.toMatrix' (F i), LinearMap.toMatrix' (G i), ?_, ?_⟩, rfl⟩
    · rw [← LinearMap.toMatrix'_comp, e1, LinearMap.toMatrix'_id]
    · rw [← LinearMap.toMatrix'_comp, e2, LinearMap.toMatrix'_id]
  · have hc : (F j).comp (Matrix.toLin' (x i j e)) = (Matrix.toLin' (y i j e)).comp (F i) := f.comm e
    have := congrArg LinearMap.toMatrix' hc
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at this
    exact this.symm

/-- Every finite-dimensional representation is isomorphic to a matrix representation of its dimension vector. -/
theorem exists_matRep (V : QRep.{u, 0, u, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] :
    ∃ x : MatRep k V.dimVec, V.Isomorphic x.toQRep := by
  let b : ∀ i, Module.Basis (Fin (V.dimVec i)) k (V.obj i) := fun i =>
    Module.finBasisOfFinrankEq k (V.obj i) rfl
  refine ⟨fun i j e => LinearMap.toMatrix (b i) (b j) (V.map e), ?_⟩
  apply isomorphic_of_equiv (fun i => (b i).equivFun)
  intro i j e x
  show (b j).equivFun (V.map e x) = Matrix.toLin' (LinearMap.toMatrix (b i) (b j) (V.map e)) ((b i).equivFun x)
  rw [Matrix.toLin'_apply]
  exact (LinearMap.toMatrix_mulVec_repr (b i) (b j) (V.map e) x).symm

/-! ### Iterated direct sums -/

variable (k) in
/-- The zero representation. -/
def zeroRep : QRep.{u, 0, u, a} k (Fin n) where
  obj _ := PUnit.{u + 1}
  map _ := 0

instance zeroRep_unique (i : Fin n) : Unique ((zeroRep k : QRep.{u, 0, u, a} k (Fin n)).obj i) :=
  inferInstanceAs (Unique PUnit.{u + 1})

/-- The iterated direct sum of a list of representations (the zero representation for the empty list). -/
def sumList : List (QRep.{u, 0, u, a} k (Fin n)) → QRep.{u, 0, u, a} k (Fin n)
  | [] => zeroRep k
  | V :: L => directSum V (sumList L)

theorem sumList_finite : ∀ (L : List (QRep.{u, 0, u, a} k (Fin n))),
    (∀ V ∈ L, ∀ j, Module.Finite k (V.obj j)) → ∀ j, Module.Finite k ((sumList L).obj j)
  | [], _, _ => by
    show Module.Finite k PUnit.{u + 1}
    infer_instance
  | V :: L, h, j => by
    show Module.Finite k (V.obj j × (sumList L).obj j)
    have := h V (by simp) j
    have := sumList_finite L (fun W hW => h W (by simp [hW])) j
    infer_instance

theorem finrank_sumList_cons (V : QRep.{u, 0, u, a} k (Fin n)) (L : List (QRep.{u, 0, u, a} k (Fin n)))
    [∀ j, Module.Finite k (V.obj j)] [∀ j, Module.Finite k ((sumList L).obj j)] (j : Fin n) :
    Module.finrank k ((sumList (V :: L)).obj j) =
      Module.finrank k (V.obj j) + Module.finrank k ((sumList L).obj j) := by
  show Module.finrank k (V.obj j × (sumList L).obj j) = _
  exact Module.finrank_prod

theorem directSum_congr {V V' W W' : QRep.{u, 0, u, a} k (Fin n)} (h1 : V.Isomorphic V')
    (h2 : W.Isomorphic W') : (directSum V W).Isomorphic (directSum V' W') := by
  obtain ⟨e1, he1⟩ := exists_equiv_of_isomorphic h1
  obtain ⟨e2, he2⟩ := exists_equiv_of_isomorphic h2
  apply isomorphic_of_equiv (fun i => LinearEquiv.prodCongr (e1 i) (e2 i))
  intro _ _ a x
  exact Prod.ext (he1 a x.1) (he2 a x.2)

theorem isomorphic_directSum_zero (V : QRep.{u, 0, u, a} k (Fin n)) :
    V.Isomorphic (directSum V (zeroRep k)) := by
  apply isomorphic_of_equiv (fun i => (LinearEquiv.prodUnique (R := k) (M := V.obj i)
    (M₂ := (zeroRep k : QRep.{u, 0, u, a} k (Fin n)).obj i)).symm)
  intro i j a x
  exact Prod.ext rfl (Subsingleton.elim (α := PUnit.{u + 1}) _ _)

theorem directSum_assoc (A B C : QRep.{u, 0, u, a} k (Fin n)) :
    (directSum (directSum A B) C).Isomorphic (directSum A (directSum B C)) := by
  apply isomorphic_of_equiv (fun i => LinearEquiv.prodAssoc k (A.obj i) (B.obj i) (C.obj i))
  intro i j a x
  rfl

theorem zero_directSum (A : QRep.{u, 0, u, a} k (Fin n)) :
    A.Isomorphic (directSum (zeroRep k) A) := by
  apply isomorphic_of_equiv (fun i => (LinearEquiv.prodUnique (R := k) (M := A.obj i)
    (M₂ := (zeroRep k : QRep.{u, 0, u, a} k (Fin n)).obj i)).symm.trans
    (LinearEquiv.prodComm k (A.obj i) ((zeroRep k : QRep.{u, 0, u, a} k (Fin n)).obj i)))
  intro i j a x
  exact Prod.ext (Subsingleton.elim (α := PUnit.{u + 1}) _ _) rfl

theorem sumList_append : ∀ (L₁ L₂ : List (QRep.{u, 0, u, a} k (Fin n))),
    (sumList (L₁ ++ L₂)).Isomorphic (directSum (sumList L₁) (sumList L₂))
  | [], L₂ => zero_directSum (sumList L₂)
  | V :: L₁, L₂ => by
    have ih := sumList_append L₁ L₂
    have h1 : (sumList (V :: (L₁ ++ L₂))).Isomorphic (directSum V (directSum (sumList L₁) (sumList L₂))) :=
      directSum_congr (Isomorphic.refl V) ih
    exact h1.trans (directSum_assoc V (sumList L₁) (sumList L₂)).symm

/-! ### Subrepresentations as representations -/

/-- A subrepresentation as a representation. -/
def subRep {V : QRep.{u, 0, u, a} k (Fin n)} (S : Subrep V) : QRep.{u, 0, u, a} k (Fin n) where
  obj i := ↥(S.carrier i)
  map e := (V.map e).restrict (fun _ hx => S.map_mem e hx)

theorem subRep_directSum_iso {V : QRep.{u, 0, u, a} k (Fin n)} (S T : Subrep V)
    (hST : ∀ i, IsCompl (S.carrier i) (T.carrier i)) :
    (directSum (subRep S) (subRep T)).Isomorphic V := by
  apply isomorphic_of_equiv (fun i => Submodule.prodEquivOfIsCompl _ _ (hST i))
  intro i j a x
  obtain ⟨s, t⟩ := x
  exact (map_add (V.map a) (↑(show S.carrier i from s) : V.obj i) ↑(show T.carrier i from t)).symm

/-! ### Decomposition into indecomposables -/

theorem finrank_sum_pos_of_indecomposable {V : QRep.{u, 0, u, a} k (Fin n)}
    [∀ j, Module.Finite k (V.obj j)] (hV : V.IsIndecomposable) :
    0 < ∑ i, Module.finrank k (V.obj i) := by
  by_contra hcon
  have hz : ∀ i, Module.finrank k (V.obj i) = 0 := by
    intro i
    have := Finset.sum_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hcon) i (Finset.mem_univ i)
    exact this
  apply hV.1
  apply Subrep.ext
  intro i
  have : Subsingleton (V.obj i) := Module.finrank_zero_iff.mp (hz i)
  exact Subsingleton.elim _ _

theorem exists_indecomposable_list : ∀ (N : ℕ) (V : QRep.{u, 0, u, a} k (Fin n)),
    (∀ j, Module.Finite k (V.obj j)) → ∑ i, Module.finrank k (V.obj i) = N →
    ∃ L : List (QRep.{u, 0, u, a} k (Fin n)),
      (∀ W ∈ L, (∀ j, Module.Finite k (W.obj j)) ∧ W.IsIndecomposable) ∧ V.Isomorphic (sumList L) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V hV hN
  by_cases hind : V.IsIndecomposable
  · refine ⟨[V], ?_, isomorphic_directSum_zero V⟩
    intro W hW
    rw [List.mem_singleton] at hW
    subst hW
    exact ⟨hV, hind⟩
  · by_cases hbt : (⊥ : Subrep V) = ⊤
    · refine ⟨[], by simp, ?_⟩
      have hs : ∀ i, Subsingleton (V.obj i) := by
        intro i
        refine ⟨fun x y => ?_⟩
        have hc := congrArg (fun S : Subrep V => S.carrier i) hbt
        simp only [Subrep.bot_carrier, Subrep.top_carrier] at hc
        have hx : x ∈ (⊥ : Submodule k (V.obj i)) := by rw [hc]; trivial
        have hy : y ∈ (⊥ : Submodule k (V.obj i)) := by rw [hc]; trivial
        rw [Submodule.mem_bot] at hx hy
        rw [hx, hy]
      apply isomorphic_of_equiv (fun i => LinearEquiv.ofSubsingleton (V.obj i)
        ((zeroRep k : QRep.{u, 0, u, a} k (Fin n)).obj i))
      intro i j a x
      exact Subsingleton.elim (α := PUnit.{u + 1}) _ _
    · have hex : ∃ S T : Subrep V, (∀ i, IsCompl (S.carrier i) (T.carrier i)) ∧ S ≠ ⊥ ∧ T ≠ ⊥ := by
        by_contra hcon
        apply hind
        refine ⟨hbt, fun S T hST => ?_⟩
        by_contra hh
        exact hcon ⟨S, T, hST, (not_or.mp hh).1, (not_or.mp hh).2⟩
      obtain ⟨S, T, hST, hS, hT⟩ := hex
      have hsum : ∀ i, Module.finrank k (S.carrier i) + Module.finrank k (T.carrier i) =
          Module.finrank k (V.obj i) := fun i => Submodule.finrank_add_eq_of_isCompl (hST i)
      have hpos : ∀ R : Subrep V, R ≠ ⊥ → 0 < ∑ i, Module.finrank k (R.carrier i) := by
        intro R hR
        by_contra hcon
        apply hR
        apply Subrep.ext
        intro i
        have h0 : Module.finrank k (R.carrier i) = 0 :=
          Finset.sum_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hcon) i (Finset.mem_univ i)
        exact Submodule.finrank_eq_zero.mp h0
      have hSpos := hpos S hS
      have hTpos := hpos T hT
      have hN' : ∑ i, Module.finrank k (S.carrier i) + ∑ i, Module.finrank k (T.carrier i) = N := by
        rw [← Finset.sum_add_distrib, ← hN]
        exact Finset.sum_congr rfl (fun i _ => hsum i)
      have : ∀ j, Module.Finite k ((subRep S).obj j) := fun j => by
        show Module.Finite k (S.carrier j)
        infer_instance
      have : ∀ j, Module.Finite k ((subRep T).obj j) := fun j => by
        show Module.Finite k (T.carrier j)
        infer_instance
      obtain ⟨L₁, hL₁, hi₁⟩ := ih (∑ i, Module.finrank k (S.carrier i)) (by omega) (subRep S) inferInstance rfl
      obtain ⟨L₂, hL₂, hi₂⟩ := ih (∑ i, Module.finrank k (T.carrier i)) (by omega) (subRep T) inferInstance rfl
      refine ⟨L₁ ++ L₂, ?_, ?_⟩
      · intro W hW
        rcases List.mem_append.mp hW with h | h
        · exact hL₁ W h
        · exact hL₂ W h
      · exact (subRep_directSum_iso S T hST).symm.trans
          ((directSum_congr hi₁ hi₂).trans (sumList_append L₁ L₂).symm)

theorem length_le_finrank_sum : ∀ (L : List (QRep.{u, 0, u, a} k (Fin n))),
    (∀ W ∈ L, (∀ j, Module.Finite k (W.obj j)) ∧ W.IsIndecomposable) →
    L.length ≤ ∑ i, Module.finrank k ((sumList L).obj i)
  | [], _ => by simp
  | V :: L, h => by
    have hV := h V (by simp)
    have := hV.1
    have hL : ∀ W ∈ L, (∀ j, Module.Finite k (W.obj j)) ∧ W.IsIndecomposable :=
      fun W hW => h W (by simp [hW])
    have := sumList_finite L (fun W hW => (hL W hW).1)
    have ih := length_le_finrank_sum L hL
    have hp := finrank_sum_pos_of_indecomposable hV.2
    have : ∑ i, Module.finrank k ((sumList (V :: L)).obj i) =
        ∑ i, Module.finrank k (V.obj i) + ∑ i, Module.finrank k ((sumList L).obj i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => finrank_sumList_cons V L i)
    rw [this, List.length_cons]
    omega

theorem exists_index_list {ι : Type} (W : ι → QRep.{u, 0, u, a} k (Fin n)) :
    ∀ (L : List (QRep.{u, 0, u, a} k (Fin n))), (∀ V ∈ L, ∃ m, V.Isomorphic (W m)) →
      ∃ l : List ι, l.length = L.length ∧ (sumList L).Isomorphic (sumList (l.map W))
  | [], _ => ⟨[], rfl, Isomorphic.refl _⟩
  | V :: L, h => by
    obtain ⟨m, hm⟩ := h V (by simp)
    obtain ⟨l, hl, hi⟩ := exists_index_list W L (fun X hX => h X (by simp [hX]))
    exact ⟨m :: l, by simp [hl], directSum_congr hm hi⟩

/-- **Etingof et al., Problem 5.4 (finiteness step).** If `Q` is of finite type, then for every dimension vector
`d` the group `∏ GL(d_i)` has finitely many orbits on the representations of dimension vector `d`. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
theorem IsFiniteType.exists_finite_orbits (h : IsFiniteType Q k) (d : Fin n → ℕ) :
    ∃ (m : ℕ) (xs : Fin m → MatRep k d), ∀ y : MatRep k d, ∃ t, MatRep.Equiv (xs t) y := by
  obtain ⟨ι, hι, W, hWf, hW⟩ := h
  let N := ∑ i, d i
  let T : Set (List ι) := {l | l.length ≤ N ∧ (sumList (l.map W)).dimVec = d}
  have hT : T.Finite := (List.finite_length_le ι N).subset (fun l hl => hl.1)
  have hfin : ∀ l : List ι, ∀ j, Module.Finite k ((sumList (l.map W)).obj j) := by
    intro l
    apply sumList_finite
    intro V hV
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hV
    exact hWf m
  have hex : ∀ l : T, ∃ x : MatRep k d, (sumList (l.1.map W)).Isomorphic x.toQRep := by
    rintro ⟨l, _, hd⟩
    have := hfin l
    have key : ∀ d' : Fin n → ℕ, (sumList (l.map W)).dimVec = d' →
        ∃ x : MatRep k d', (sumList (l.map W)).Isomorphic x.toQRep := by
      rintro d' rfl
      exact exists_matRep _
    exact key d hd
  choose c hc using hex
  have : Finite T := hT.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨m, fun t => c (e.symm t), ?_⟩
  intro y
  have hyf : ∀ j, Module.Finite k (y.toQRep.obj j) := fun j => by
    show Module.Finite k (Fin (d j) → k)
    infer_instance
  obtain ⟨L, hL, hiso⟩ := exists_indecomposable_list _ y.toQRep hyf rfl
  obtain ⟨l, hlen, hl⟩ := exists_index_list W L (fun V hV => hW V (hL V hV).1 (hL V hV).2)
  have hdim : y.toQRep.dimVec = d := by
    funext i
    exact Module.finrank_fin_fun k
  have hdimL : (sumList L).dimVec = d := by
    rw [← hdim]
    exact hiso.symm.dimVec_eq
  have hlT : l ∈ T := by
    refine ⟨?_, ?_⟩
    · rw [hlen]
      have := length_le_finrank_sum L hL
      have h2 : ∑ i, Module.finrank k ((sumList L).obj i) = N := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact congrFun hdimL i
      omega
    · rw [← hdimL]
      exact hl.dimVec_eq.symm
  refine ⟨e ⟨l, hlT⟩, ?_⟩
  show (c (e.symm (e ⟨l, hlT⟩))).Equiv y
  rw [Equiv.symm_apply_apply]
  apply MatRep.equiv_of_isomorphic
  exact ((hiso.trans (hl.trans (hc ⟨l, hlT⟩))).symm)

end

end UndergradKB.RepresentationTheory.Gabriel
