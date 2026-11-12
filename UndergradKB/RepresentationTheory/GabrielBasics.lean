import Mathlib.RingTheory.SimpleModule.Rank
import UndergradKB.RepresentationTheory.ReflectionFunctorsMore
import UndergradKB.RepresentationTheory.GabrielOrder
import UndergradKB.Common.Attr

/-! # Tools for Gabriel's theorem (Etingof et al., §5.8)

Bridging lemmas used in the proof of Theorem 5.34 and Corollaries 5.35-5.37 (`GabrielTheorem.lean`).

* Isomorphism of quiver representations is symmetric and transitive (`QRep.Isomorphic.symm`,
  `QRep.Isomorphic.trans`) and preserves indecomposability (`QRep.Isomorphic.isIndecomposable`).
* `normRep V`: a finite-dimensional representation is isomorphic to one whose spaces are `k^d`
  (`isomorphic_normRep`). This keeps the spaces in a fixed universe when reflection functors are iterated.
* `QRep.IsSimpleAt`: a representation is simple at `i` iff its dimension vector is the simple root `α_i`
  (`isSimpleAt_iff_dimZ`); such a representation is indecomposable (`isIndecomposable_of_isSimpleAt`), exists
  (`simpleRep`) and is unique up to isomorphism when there is no loop at `i` (`isomorphic_of_isSimpleAt`).
* `pullback φ X`: a representation of a quiver `Q₂` viewed as one of `Q₁` along a map of arrows; along the
  identification `toRR` of `Q` with `(Q_i)_i`, which is surjective on arrows, this turns `RevRevIso` into an
  isomorphism and preserves indecomposability.
* `IsOrientation G Q`: the quiver structure `Q` on `Fin n` is an orientation of the simple graph `G` (at most one
  arrow between two vertices, in one direction, exactly when they are adjacent). It is preserved by reversing the
  arrows at a vertex, and its arrow relation is then `Gabriel.flipAt`.
-/

namespace UndergradKB.RepresentationTheory

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

universe u v w w' w'' a

namespace QRep

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

/-! ### Isomorphisms -/

theorem Isomorphic.symm {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q} (h : Isomorphic V W) :
    Isomorphic W V := by
  obtain ⟨f, g, h1, h2⟩ := h
  exact ⟨g, f, h2, h1⟩

theorem Isomorphic.trans {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q} {X : QRep.{u, v, w'', a} k Q}
    (h : Isomorphic V W) (h' : Isomorphic W X) : Isomorphic V X := by
  obtain ⟨f, g, h1, h2⟩ := h
  obtain ⟨f', g', h1', h2'⟩ := h'
  refine ⟨f'.comp f, g.comp g', ?_, ?_⟩
  · apply Hom.ext; intro i
    have e1 := congrArg (fun h => Hom.app h i) h1
    have e1' := congrArg (fun h => Hom.app h i) h1'
    simp only [Hom.comp_app, Hom.id_app] at e1 e1' ⊢
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (g'.app i), e1, LinearMap.id_comp, e1']
  · apply Hom.ext; intro i
    have e2 := congrArg (fun h => Hom.app h i) h2
    have e2' := congrArg (fun h => Hom.app h i) h2'
    simp only [Hom.comp_app, Hom.id_app] at e2 e2' ⊢
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (f.app i), e2', LinearMap.id_comp, e2]

theorem Isomorphic.refl (V : QRep.{u, v, w, a} k Q) : Isomorphic V V :=
  ⟨Hom.id V, Hom.id V, Hom.ext fun _ => rfl, Hom.ext fun _ => rfl⟩

/-- The linear equivalence at a vertex given by an isomorphism. -/
def isoEquiv {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q} (f : Hom V W) (g : Hom W V)
    (h1 : f.comp g = Hom.id W) (h2 : g.comp f = Hom.id V) (i : Q) : V.obj i ≃ₗ[k] W.obj i :=
  LinearEquiv.ofLinear (f.app i) (g.app i) (by simpa using congrArg (fun h => Hom.app h i) h1)
    (by simpa using congrArg (fun h => Hom.app h i) h2)

/-- An isomorphism preserves indecomposability. -/
theorem Isomorphic.isIndecomposable {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q}
    (h : Isomorphic V W) (hV : V.IsIndecomposable) : W.IsIndecomposable := by
  obtain ⟨f, g, h1, h2⟩ := h
  let E := isoEquiv f g h1 h2
  have hE : ∀ i (z : V.obj i), E i z = f.app i z := fun _ _ => rfl
  -- pull a subrepresentation of `W` back to `V`
  let pb : Subrep W → Subrep V := fun S =>
    { carrier := fun i => (S.carrier i).comap (f.app i)
      map_mem := by
        intro i j e z hz
        rw [Submodule.mem_comap] at hz ⊢
        have := LinearMap.congr_fun (f.comm e) z
        simp only [LinearMap.comp_apply] at this
        rw [this]
        exact S.map_mem e hz }
  have hpb : ∀ S i, (pb S).carrier i = (Submodule.orderIsoMapComap (E i)).symm (S.carrier i) := by
    intro S i; rfl
  have hbot : ∀ S : Subrep W, pb S = ⊥ → S = ⊥ := by
    intro S hS
    apply Subrep.ext; intro i
    have := congrArg (fun T => Subrep.carrier T i) hS
    simp only [hpb, Subrep.bot_carrier] at this
    rw [Subrep.bot_carrier]
    have h' := congrArg (Submodule.orderIsoMapComap (E i)) this
    rw [OrderIso.apply_symm_apply] at h'
    rw [h']
    simp
  refine ⟨fun hW => hV.1 ?_, fun S T hST => ?_⟩
  · apply Subrep.ext; intro i
    have := congrArg (fun T => Subrep.carrier T i) hW
    simp only [Subrep.bot_carrier, Subrep.top_carrier] at this ⊢
    have h' := congrArg (Submodule.orderIsoMapComap (E i)).symm this
    simpa using h'
  · rcases hV.2 (pb S) (pb T) (fun i => by
      rw [hpb, hpb]
      exact (Submodule.orderIsoMapComap (E i)).symm.isCompl (hST i)) with h | h
    · exact Or.inl (hbot S h)
    · exact Or.inr (hbot T h)

/-! ### Normalising the spaces to `k^d` -/

/-- The chosen identification of the space at a vertex with `k^d`. -/
def normEquiv (V : QRep.{u, v, w, a} k Q) [∀ x, Module.Finite k (V.obj x)] (x : Q) :
    V.obj x ≃ₗ[k] (Fin (V.dimVec x) → k) :=
  (Module.finBasis k (V.obj x)).equivFun

/-- The representation with spaces `k^{d_x}` isomorphic to a finite-dimensional `V`. -/
def normRep (V : QRep.{u, v, w, a} k Q) [∀ x, Module.Finite k (V.obj x)] : QRep.{u, v, u, a} k Q where
  obj x := Fin (V.dimVec x) → k
  map e := (normEquiv V _).toLinearMap ∘ₗ V.map e ∘ₗ (normEquiv V _).symm.toLinearMap

instance normRep_finite (V : QRep.{u, v, w, a} k Q) [∀ x, Module.Finite k (V.obj x)] (x : Q) :
    Module.Finite k ((normRep V).obj x) :=
  inferInstanceAs (Module.Finite k (Fin (V.dimVec x) → k))

theorem isomorphic_normRep (V : QRep.{u, v, w, a} k Q) [∀ x, Module.Finite k (V.obj x)] :
    Isomorphic V (normRep V) := by
  refine ⟨⟨fun x => (normEquiv V x).toLinearMap, fun {x y} e => ?_⟩,
    ⟨fun x => (normEquiv V x).symm.toLinearMap, fun {x y} e => ?_⟩, ?_, ?_⟩
  · refine LinearMap.ext fun z => ?_
    show normEquiv V y (V.map e z) = normEquiv V y (V.map e ((normEquiv V x).symm (normEquiv V x z)))
    rw [LinearEquiv.symm_apply_apply]
  · refine LinearMap.ext fun z => ?_
    show (normEquiv V y).symm (normEquiv V y (V.map e ((normEquiv V x).symm z))) = V.map e ((normEquiv V x).symm z)
    rw [LinearEquiv.symm_apply_apply]
  · apply Hom.ext; intro x
    exact LinearMap.ext fun z => (normEquiv V x).apply_symm_apply z
  · apply Hom.ext; intro x
    exact LinearMap.ext fun z => (normEquiv V x).symm_apply_apply z

theorem dimVec_normRep (V : QRep.{u, v, w, a} k Q) [∀ x, Module.Finite k (V.obj x)] :
    (normRep V).dimVec = V.dimVec :=
  (isomorphic_normRep V).dimVec_eq.symm

/-! ### Simple representations -/

/-- The dimension vector as an integer vector. -/
def dimZ (V : QRep.{u, v, w, a} k Q) : Q → ℤ := fun x => (V.dimVec x : ℤ)

theorem Isomorphic.dimZ_eq {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q} (h : Isomorphic V W) :
    V.dimZ = W.dimZ := by
  funext x; simp [dimZ, h.dimVec_eq]

theorem finrank_eq_zero_iff_subsingleton {M : Type w} [AddCommGroup M] [Module k M] [Module.Finite k M] :
    Module.finrank k M = 0 ↔ Subsingleton M :=
  Module.finrank_zero_iff

theorem isSimpleAt_iff_dimVec (V : QRep.{u, v, w, a} k Q) [∀ x, Module.Finite k (V.obj x)] (i : Q) :
    V.IsSimpleAt i ↔ ∀ x, V.dimVec x = if x = i then 1 else 0 := by
  unfold IsSimpleAt dimVec
  constructor
  · rintro ⟨h1, h2⟩ x
    by_cases hx : x = i
    · subst hx
      rw [if_pos rfl]
      rw [← Module.finrank_eq_rank] at h2
      exact_mod_cast h2
    · rw [if_neg hx]
      haveI := h1 x hx
      exact Module.finrank_zero_of_subsingleton
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have := h j
      rw [if_neg hj] at this
      exact Module.finrank_zero_iff.1 this
    · have := h i
      rw [if_pos rfl] at this
      rw [← Module.finrank_eq_rank, this]
      simp

/-- A representation that is simple at a vertex is indecomposable. -/
theorem isIndecomposable_of_isSimpleAt {V : QRep.{u, v, w, a} k Q} {i : Q} (h : V.IsSimpleAt i) :
    V.IsIndecomposable := by
  obtain ⟨h1, h2⟩ := h
  haveI : Module.Finite k (V.obj i) := Module.rank_lt_aleph0_iff.1 (by rw [h2]; exact Cardinal.one_lt_aleph0)
  have hfr : Module.finrank k (V.obj i) = 1 := by
    rw [← Module.finrank_eq_rank] at h2; exact_mod_cast h2
  haveI : IsSimpleModule k (V.obj i) := isSimpleModule_iff_finrank_eq_one.2 hfr
  have hsub : ∀ S : Subrep V, S.carrier i = ⊥ → S = ⊥ := by
    intro S hS
    apply Subrep.ext; intro x
    rw [Subrep.bot_carrier]
    by_cases hx : x = i
    · subst hx; exact hS
    · haveI := h1 x hx
      exact Subsingleton.elim _ _
  refine ⟨fun h => ?_, fun S T hST => ?_⟩
  · have := congrArg (fun T => Subrep.carrier T i) h
    simp only [Subrep.bot_carrier, Subrep.top_carrier] at this
    have hs : Subsingleton (V.obj i) := ⟨fun p q => by
      have hp : p ∈ (⊥ : Submodule k (V.obj i)) := this ▸ Submodule.mem_top
      have hq : q ∈ (⊥ : Submodule k (V.obj i)) := this ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hp hq
      rw [hp, hq]⟩
    rw [Module.finrank_zero_of_subsingleton] at hfr
    exact absurd hfr (by norm_num)
  · rcases IsSimpleOrder.eq_bot_or_eq_top (S.carrier i) with hS | hS
    · exact Or.inl (hsub S hS)
    · right
      apply hsub
      have := (hST i).disjoint
      rw [hS] at this
      exact top_disjoint.1 this

theorem simple_comm {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q} {i : Q}
    (hloop : ∀ e : i ⟶ i, False) (hV : V.IsSimpleAt i) (hW : W.IsSimpleAt i) (F : ∀ x, V.obj x →ₗ[k] W.obj x)
    {x y : Q} (e : x ⟶ y) : (F y).comp (V.map e) = (W.map e).comp (F x) := by
  ext z
  by_cases hy : y = i
  · have hx : x ≠ i := by
      rintro rfl
      subst hy
      exact hloop e
    haveI := hV.1 x hx
    rw [Subsingleton.elim z 0]
    simp
  · haveI := hW.1 y hy
    exact Subsingleton.elim _ _

theorem IsSimpleAt.finite {V : QRep.{u, v, w, a} k Q} {i : Q} (hV : V.IsSimpleAt i) (x : Q) :
    Module.Finite k (V.obj x) := by
  by_cases hx : x = i
  · subst hx; exact Module.rank_lt_aleph0_iff.1 (by rw [hV.2]; exact Cardinal.one_lt_aleph0)
  · haveI := hV.1 x hx; infer_instance

/-- Two representations with the same dimension vector, simple at a vertex `i` without loops, are isomorphic. -/
theorem isomorphic_of_isSimpleAt {V : QRep.{u, v, w, a} k Q} {W : QRep.{u, v, w', a} k Q} {i : Q}
    (hloop : ∀ e : i ⟶ i, False) (hV : V.IsSimpleAt i) (hW : W.IsSimpleAt i) : Isomorphic V W := by
  haveI := hV.finite
  haveI := hW.finite
  have hd : ∀ x, Module.finrank k (V.obj x) = Module.finrank k (W.obj x) := by
    intro x
    have a := (isSimpleAt_iff_dimVec V i).1 hV x
    have b := (isSimpleAt_iff_dimVec W i).1 hW x
    unfold dimVec at a b
    rw [a, b]
  let E : ∀ x, V.obj x ≃ₗ[k] W.obj x := fun x => LinearEquiv.ofFinrankEq _ _ (hd x)
  refine ⟨⟨fun x => (E x).toLinearMap, fun {_ _} e => simple_comm hloop hV hW (fun x => (E x).toLinearMap) e⟩,
    ⟨fun x => (E x).symm.toLinearMap, simple_comm hloop hW hV (fun x => (E x).symm.toLinearMap)⟩, ?_, ?_⟩
  · apply Hom.ext; intro x
    exact LinearMap.ext fun z => (E x).apply_symm_apply z
  · apply Hom.ext; intro x
    exact LinearMap.ext fun z => (E x).symm_apply_apply z

/-- The simple representation at `i`: the line `k` at `i`, zero elsewhere, all maps zero. -/
def simpleRep (k : Type u) [Field k] (i : Q) : QRep.{u, v, u, a} k Q where
  obj x := Fin (if x = i then 1 else 0) → k
  map _ := 0

instance simpleRep_finite (i x : Q) : Module.Finite k ((simpleRep k i : QRep.{u, v, u, a} k Q).obj x) :=
  inferInstanceAs (Module.Finite k (Fin _ → k))

theorem simpleRep_isSimpleAt (i : Q) : (simpleRep k i : QRep.{u, v, u, a} k Q).IsSimpleAt i := by
  rw [isSimpleAt_iff_dimVec]
  intro x
  show Module.finrank k (Fin _ → k) = _
  rw [Module.finrank_fin_fun]

/-! ### Pulling back along a map of arrows -/

section Pullback

variable {Q' : Type v}

/-- A representation of `Q₂` viewed as a representation of `Q₁` along a map of arrows `φ`. -/
def pullback (Q₁ Q₂ : Quiver.{a} Q') (φ : ∀ x y : Q', @Quiver.Hom Q' Q₁ x y → @Quiver.Hom Q' Q₂ x y)
    (X : @QRep.{u, v, w, a} k Q' _ Q₂) : @QRep.{u, v, w, a} k Q' _ Q₁ :=
  @QRep.mk k Q' _ Q₁ (@QRep.obj k Q' _ Q₂ X) (fun x => @QRep.addCommGroup k Q' _ Q₂ X x)
    (fun x => @QRep.module k Q' _ Q₂ X x) (fun {x y} e => @QRep.map k Q' _ Q₂ X x y (φ x y e))

theorem pullback_isIndecomposable (Q₁ Q₂ : Quiver.{a} Q')
    (φ : ∀ x y : Q', @Quiver.Hom Q' Q₁ x y → @Quiver.Hom Q' Q₂ x y) (hφ : ∀ x y, Function.Surjective (φ x y))
    (X : @QRep.{u, v, w, a} k Q' _ Q₂) (hX : @QRep.IsIndecomposable k Q' _ Q₂ X) :
    @QRep.IsIndecomposable k Q' _ Q₁ (pullback Q₁ Q₂ φ X) := by
  let up : @Subrep k Q' _ Q₁ (pullback Q₁ Q₂ φ X) → @Subrep k Q' _ Q₂ X := fun S =>
    @Subrep.mk k Q' _ Q₂ X (@Subrep.carrier k Q' _ Q₁ _ S) (by
      intro x y b z hz
      obtain ⟨e, rfl⟩ := hφ x y b
      exact @Subrep.map_mem k Q' _ Q₁ _ S x y e z hz)
  refine ⟨fun h => hX.1 ?_, fun S T hST => ?_⟩
  · refine @Subrep.ext k Q' _ Q₂ X _ _ fun x => ?_
    exact congrArg (fun T => @Subrep.carrier k Q' _ Q₁ _ T x) h
  · rcases hX.2 (up S) (up T) hST with h | h
    · left
      refine @Subrep.ext k Q' _ Q₁ _ _ _ fun x => ?_
      exact congrArg (fun T => @Subrep.carrier k Q' _ Q₂ _ T x) h
    · right
      refine @Subrep.ext k Q' _ Q₁ _ _ _ fun x => ?_
      exact congrArg (fun T => @Subrep.carrier k Q' _ Q₂ _ T x) h

theorem pullback_isomorphic (Q₁ Q₂ : Quiver.{a} Q')
    (φ : ∀ x y : Q', @Quiver.Hom Q' Q₁ x y → @Quiver.Hom Q' Q₂ x y)
    {X : @QRep.{u, v, w, a} k Q' _ Q₂} {X' : @QRep.{u, v, w', a} k Q' _ Q₂}
    (h : @QRep.Isomorphic k Q' _ Q₂ X X') :
    @QRep.Isomorphic k Q' _ Q₁ (pullback Q₁ Q₂ φ X) (pullback Q₁ Q₂ φ X') := by
  obtain ⟨f, g, h1, h2⟩ := h
  refine ⟨@Hom.mk k Q' _ Q₁ _ _ (@Hom.app k Q' _ Q₂ _ _ f) (fun {x y} e => @Hom.comm k Q' _ Q₂ _ _ f x y (φ x y e)),
    @Hom.mk k Q' _ Q₁ _ _ (@Hom.app k Q' _ Q₂ _ _ g) (fun {x y} e => @Hom.comm k Q' _ Q₂ _ _ g x y (φ x y e)),
    ?_, ?_⟩
  · refine @Hom.ext k Q' _ Q₁ _ _ _ _ fun x => ?_
    exact congrArg (fun h => @Hom.app k Q' _ Q₂ _ _ h x) h1
  · refine @Hom.ext k Q' _ Q₁ _ _ _ _ fun x => ?_
    exact congrArg (fun h => @Hom.app k Q' _ Q₂ _ _ h x) h2

theorem pullback_dimVec (Q₁ Q₂ : Quiver.{a} Q')
    (φ : ∀ x y : Q', @Quiver.Hom Q' Q₁ x y → @Quiver.Hom Q' Q₂ x y) (X : @QRep.{u, v, w, a} k Q' _ Q₂) :
    @dimVec k Q' _ Q₁ (pullback Q₁ Q₂ φ X) = @dimVec k Q' _ Q₂ X := rfl

theorem pullback_finite (Q₁ Q₂ : Quiver.{a} Q')
    (φ : ∀ x y : Q', @Quiver.Hom Q' Q₁ x y → @Quiver.Hom Q' Q₂ x y) (X : @QRep.{u, v, w, a} k Q' _ Q₂)
    [h : ∀ x, Module.Finite k (@QRep.obj k Q' _ Q₂ X x)] (x : Q') :
    Module.Finite k (@QRep.obj k Q' _ Q₁ (pullback Q₁ Q₂ φ X) x) := h x

end Pullback

end QRep

/-! ### The identification of `(Q_i)_i` with `Q` -/

section RevRev

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

theorem toRR_surjective (i x y : Q) : Function.Surjective (fun e : x ⟶ y => toRR i e) := by
  intro b
  rcases b with ⟨⟨e, h⟩ | ⟨e, h⟩, h'⟩ | ⟨⟨e, h⟩ | ⟨e, h⟩, h'⟩
  · exact ⟨e, by simp [toRR_of_ne e h'.1 h'.2]⟩
  · exact absurd h (by rintro (h | h) <;> [exact h'.1 h; exact h'.2 h])
  · exact absurd h' (by rintro (h'' | h'') <;> [exact h.2 h''; exact h.1 h''])
  · by_cases hy : y = i
    · exact ⟨e, by show toRR i e = _; rw [toRR_of_eq_right e hy]⟩
    · have hx : x = i := h'.resolve_right hy
      exact ⟨e, by show toRR i e = _; rw [toRR_of_eq_left e hx]⟩

/-- `V` viewed through the identification `toRR` of the arrows of `Q` with those of `(Q_i)_i`. -/
abbrev rrPullback (i : Q) (X : @QRep.{u, v, w, a} k Q _ (revrev i)) : QRep.{u, v, w, a} k Q :=
  QRep.pullback _ (revrev i) (fun _ _ e => toRR i e) X

theorem RevRevIso.isomorphic {V : QRep.{u, v, w, a} k Q} {i : Q} {X : @QRep.{u, v, w', a} k Q _ (revrev i)}
    (h : RevRevIso V X) : QRep.Isomorphic V (rrPullback i X) := by
  obtain ⟨e, he⟩ := h
  refine ⟨⟨fun x => (e x).symm.toLinearMap, fun {x y} a => ?_⟩, ⟨fun x => (e x).toLinearMap, fun {x y} a => ?_⟩,
    ?_, ?_⟩
  · refine LinearMap.ext fun z => ?_
    show (e y).symm (V.map a z) = @QRep.map k Q _ (revrev i) X x y (toRR i a) ((e x).symm z)
    rw [LinearEquiv.symm_apply_eq, he a]
    simp
  · refine LinearMap.ext fun z => ?_
    exact he a z
  · apply QRep.Hom.ext; intro x
    exact LinearMap.ext fun z => (e x).symm_apply_apply z
  · apply QRep.Hom.ext; intro x
    exact LinearMap.ext fun z => (e x).apply_symm_apply z

end RevRev

/-! ### Orientations of a graph on `Fin n` -/

namespace Gabriel

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The arrow relation of a quiver structure: there is an arrow `x → y`. -/
def arr (Q : Quiver.{a} (Fin n)) (x y : Fin n) : Prop := Nonempty (@Quiver.Hom _ Q x y)

/-- The quiver structure `Q` on `Fin n` is an orientation of the graph `G`: there is at most one arrow
`x → y`, arrows join adjacent vertices, adjacent vertices are joined by an arrow, and never in both directions. -/
structure IsOrientation (Q : Quiver.{a} (Fin n)) : Prop where
  sub : ∀ x y, Subsingleton (@Quiver.Hom _ Q x y)
  adj : ∀ x y, arr Q x y → G.Adj x y
  adj' : ∀ x y, G.Adj x y → arr Q x y ∨ arr Q y x
  asymm : ∀ x y, arr Q x y → ¬ arr Q y x

theorem arr_reversedAt (Q : Quiver.{a} (Fin n)) (i : Fin n) :
    arr (@reversedAt _ Q i) = flipAt i (arr Q) := by
  funext x y
  apply propext
  unfold arr flipAt
  by_cases h : x = i ∨ y = i
  · rw [if_pos h]
    constructor
    · rintro ⟨⟨e, he⟩ | ⟨e, _⟩⟩
      · exact absurd h (by rintro (h' | h') <;> [exact he.1 h'; exact he.2 h'])
      · exact ⟨e⟩
    · rintro ⟨e⟩; exact ⟨PSum.inr ⟨e, h⟩⟩
  · rw [if_neg h]
    have h' : x ≠ i ∧ y ≠ i := ⟨fun hx => h (Or.inl hx), fun hy => h (Or.inr hy)⟩
    constructor
    · rintro ⟨⟨e, _⟩ | ⟨e, he⟩⟩
      · exact ⟨e⟩
      · exact absurd he h
    · rintro ⟨e⟩; exact ⟨PSum.inl ⟨e, h'⟩⟩

theorem IsOrientation.reversedAt {Q : Quiver.{a} (Fin n)} (hQ : IsOrientation G Q) (i : Fin n) :
    IsOrientation G (@reversedAt _ Q i) := by
  have hR := arr_reversedAt Q i
  have hflip : ∀ x y, flipAt i (arr Q) x y = arr Q x y ∨ flipAt i (arr Q) x y = arr Q y x := by
    intro x y; unfold flipAt; split_ifs <;> simp
  refine ⟨fun x y => ⟨fun b b' => ?_⟩, fun x y h => ?_, fun x y h => ?_, fun x y h h' => ?_⟩
  · haveI := hQ.sub x y
    haveI := hQ.sub y x
    rcases b with ⟨e, he⟩ | ⟨e, he⟩ <;> rcases b' with ⟨e', he'⟩ | ⟨e', he'⟩
    · exact congrArg PSum.inl (Subtype.ext (Subsingleton.elim e e'))
    · exact absurd he' (by rintro (h | h) <;> [exact he.1 h; exact he.2 h])
    · exact absurd he (by rintro (h | h) <;> [exact he'.1 h; exact he'.2 h])
    · exact congrArg PSum.inr (Subtype.ext (Subsingleton.elim e e'))
  · rw [hR] at h
    rcases hflip x y with e | e <;> rw [e] at h
    · exact hQ.adj x y h
    · exact (hQ.adj y x h).symm
  · rw [hR]
    unfold flipAt
    by_cases hc : x = i ∨ y = i
    · have hc' : y = i ∨ x = i := hc.symm
      rw [if_pos hc, if_pos hc']
      exact (hQ.adj' x y h).symm
    · have hc' : ¬ (y = i ∨ x = i) := fun h' => hc h'.symm
      rw [if_neg hc, if_neg hc']
      exact hQ.adj' x y h
  · rw [hR] at h h'
    unfold flipAt at h h'
    by_cases hc : x = i ∨ y = i
    · have hc' : y = i ∨ x = i := hc.symm
      rw [if_pos hc] at h
      rw [if_pos hc'] at h'
      exact hQ.asymm y x h h'
    · have hc' : ¬ (y = i ∨ x = i) := fun h' => hc h'.symm
      rw [if_neg hc] at h
      rw [if_neg hc'] at h'
      exact hQ.asymm x y h h'

/-- Finiteness of the arrow types of an orientation (noncomputable). -/
def IsOrientation.fintype {Q : Quiver.{a} (Fin n)} (hQ : IsOrientation G Q) (x y : Fin n) :
    Fintype (@Quiver.Hom _ Q x y) :=
  @Fintype.ofFinite _ (@Finite.of_subsingleton _ (hQ.sub x y))

theorem IsOrientation.card {Q : Quiver.{a} (Fin n)} (hQ : IsOrientation G Q)
    [inst : ∀ x y, Fintype (@Quiver.Hom _ Q x y)] (x y : Fin n) :
    Fintype.card (@Quiver.Hom _ Q x y) + Fintype.card (@Quiver.Hom _ Q y x) = if G.Adj x y then 1 else 0 := by
  have hc : ∀ x y, Fintype.card (@Quiver.Hom _ Q x y) = if arr Q x y then 1 else 0 := by
    intro x y
    haveI := hQ.sub x y
    by_cases h : arr Q x y
    · rw [if_pos h]
      exact Fintype.card_eq_one_iff_nonempty_unique.2 ⟨⟨⟨h.some⟩, fun b => Subsingleton.elim _ _⟩⟩
    · rw [if_neg h]
      exact Fintype.card_eq_zero_iff.2 (not_nonempty_iff.1 h)
  rw [hc, hc]
  by_cases hxy : G.Adj x y
  · rw [if_pos hxy]
    rcases hQ.adj' x y hxy with h | h
    · rw [if_pos h, if_neg (hQ.asymm x y h)]
    · rw [if_pos h, if_neg (hQ.asymm y x h)]
  · rw [if_neg hxy]
    have h1 : ¬ arr Q x y := fun h => hxy (hQ.adj x y h)
    have h2 : ¬ arr Q y x := fun h => hxy (hQ.adj y x h).symm
    rw [if_neg h1, if_neg h2]

theorem IsOrientation.isSink_iff {Q : Quiver.{a} (Fin n)} (i : Fin n) :
    @Quiver.IsSink _ Q i ↔ ∀ j, ¬ arr Q i j :=
  ⟨fun h j hj => (h j).false hj.some, fun h j => not_nonempty_iff.1 (h j)⟩

theorem IsOrientation.noLoop {Q : Quiver.{a} (Fin n)} (hQ : IsOrientation G Q) (i : Fin n)
    (e : @Quiver.Hom _ Q i i) : False :=
  hQ.asymm i i ⟨e⟩ ⟨e⟩

end Gabriel

end

end UndergradKB.RepresentationTheory
