import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Prod
import UndergradKB.Common.Attr

/-! # Representations of quivers (Etingof et al., §1.7, §1.8, §5.1, §5.3)

Mathlib has quivers but no quiver representations, so we define a small bridging structure `QRep k Q`:
a family of `k`-vector spaces indexed by the vertices of `Q`, with a linear map for every arrow.

* Definition 1.30: `QRep`.
* Definition 1.37: `QRep.Hom` (with `Hom.id`, `Hom.comp`) and `QRep.Isomorphic`.
* Definition 1.35: `QRep.Subrep`; Definition 1.36: `QRep.directSum`.
* Section 1.8: `QRep.IsIrreducible` and `QRep.IsIndecomposable`.
* Definition 5.22: `QRep.dimVec`. Definition 5.24: `Quiver.IsSink`, `Quiver.IsSource`.
* Example 5.7: on the quiver with one vertex and no arrows, indecomposable iff one-dimensional.
-/

namespace UndergradKB.RepresentationTheory

universe u v w a

/-- A representation of the quiver `Q` over the field `k`: a vector space at each vertex and a linear map for
each arrow. -/
@[kb "etingof2011" "Definition 1.30, p. 13"]
structure QRep (k : Type u) (Q : Type v) [Field k] [Quiver.{a} Q] where
  /-- The vector space at each vertex. -/
  obj : Q → Type w
  [addCommGroup : ∀ i, AddCommGroup (obj i)]
  [module : ∀ i, Module k (obj i)]
  /-- The linear map attached to each arrow. -/
  map : ∀ {i j : Q}, (i ⟶ j) → obj i →ₗ[k] obj j

attribute [instance] QRep.addCommGroup QRep.module

namespace QRep

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{a} Q]

/-- A homomorphism of quiver representations: linear maps at the vertices commuting with the arrow maps. -/
@[kb "etingof2011" "Definition 1.37, p. 14"]
structure Hom (V W : QRep k Q) where
  /-- The component at each vertex. -/
  app : ∀ i, V.obj i →ₗ[k] W.obj i
  comm : ∀ {i j : Q} (a : i ⟶ j), (app j).comp (V.map a) = (W.map a).comp (app i)

namespace Hom

variable {V W X : QRep k Q}

theorem ext {f g : Hom V W} (h : ∀ i, f.app i = g.app i) : f = g := by
  cases f; cases g
  congr
  exact funext h

/-- The identity homomorphism. -/
def id (V : QRep k Q) : Hom V V where
  app _ := LinearMap.id
  comm _ := rfl

/-- Composition of homomorphisms (`g` after `f`). -/
def comp (g : Hom W X) (f : Hom V W) : Hom V X where
  app i := (g.app i).comp (f.app i)
  comm a := LinearMap.ext fun x => by
    have h2 : f.app _ (V.map a x) = W.map a (f.app _ x) := LinearMap.congr_fun (f.comm a) x
    have h1 : g.app _ (W.map a (f.app _ x)) = X.map a (g.app _ (f.app _ x)) :=
      LinearMap.congr_fun (g.comm a) _
    simp only [LinearMap.comp_apply, h2, h1]

@[simp] theorem id_app (V : QRep k Q) (i : Q) : (id V).app i = LinearMap.id := rfl

@[simp] theorem comp_app (g : Hom W X) (f : Hom V W) (i : Q) : (g.comp f).app i = (g.app i).comp (f.app i) :=
  rfl

end Hom

/-- Two representations are isomorphic if there are mutually inverse homomorphisms between them. -/
@[kb "etingof2011" "Definition 1.37, p. 14"]
def Isomorphic (V W : QRep k Q) : Prop :=
  ∃ (f : Hom V W) (g : Hom W V), f.comp g = Hom.id W ∧ g.comp f = Hom.id V

theorem Isomorphic.dim_eq {V W : QRep k Q} (h : Isomorphic V W) (i : Q) :
    Module.finrank k (V.obj i) = Module.finrank k (W.obj i) := by
  obtain ⟨f, g, hfg, hgf⟩ := h
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinearMap (f.app i) (g.app i) ?_ ?_)
  · simpa using congrArg (fun h => Hom.app h i) hfg
  · simpa using congrArg (fun h => Hom.app h i) hgf

/-- The dimension vector of a representation: the dimension of the space at each vertex. -/
@[kb "etingof2011" "Definition 5.22, p. 89"]
noncomputable def dimVec (V : QRep k Q) : Q → ℕ := fun i => Module.finrank k (V.obj i)

theorem Isomorphic.dimVec_eq {V W : QRep k Q} (h : Isomorphic V W) : V.dimVec = W.dimVec :=
  funext h.dim_eq

/-- A subrepresentation: a subspace at each vertex, stable under all the arrow maps. -/
@[kb "etingof2011" "Definition 1.35, p. 14"]
structure Subrep (V : QRep k Q) where
  /-- The subspace at each vertex. -/
  carrier : ∀ i, Submodule k (V.obj i)
  map_mem : ∀ {i j : Q} (a : i ⟶ j) {x : V.obj i}, x ∈ carrier i → V.map a x ∈ carrier j

namespace Subrep

variable {V : QRep k Q}

theorem ext {S T : Subrep V} (h : ∀ i, S.carrier i = T.carrier i) : S = T := by
  cases S; cases T
  congr
  exact funext h

/-- The zero subrepresentation. -/
def bot : Subrep V where
  carrier _ := ⊥
  map_mem := by
    intro i j a x hx
    rw [Submodule.mem_bot] at hx ⊢
    simp [hx]

/-- The whole representation as a subrepresentation. -/
def top : Subrep V where
  carrier _ := ⊤
  map_mem := by
    intro i j a x _
    exact Submodule.mem_top

instance : Bot (Subrep V) := ⟨bot⟩
instance : Top (Subrep V) := ⟨top⟩

theorem bot_carrier (i : Q) : (⊥ : Subrep V).carrier i = ⊥ := rfl
theorem top_carrier (i : Q) : (⊤ : Subrep V).carrier i = ⊤ := rfl

end Subrep

/-- The direct sum of two representations, taken vertexwise. -/
@[kb "etingof2011" "Definition 1.36, p. 14"]
def directSum (V W : QRep k Q) : QRep k Q where
  obj i := V.obj i × W.obj i
  map a := LinearMap.prodMap (V.map a) (W.map a)

/-- A representation is irreducible if it has exactly two subrepresentations, namely `0` and itself
(in particular it is nonzero). -/
@[kb "etingof2011" "§1.8, p. 14"]
def IsIrreducible (V : QRep k Q) : Prop :=
  (⊥ : Subrep V) ≠ ⊤ ∧ ∀ S : Subrep V, S = ⊥ ∨ S = ⊤

/-- A representation is indecomposable if it is nonzero and admits no decomposition into two complementary
subrepresentations unless one of them is zero. -/
@[kb "etingof2011" "§1.8, p. 14"]
def IsIndecomposable (V : QRep k Q) : Prop :=
  (⊥ : Subrep V) ≠ ⊤ ∧
    ∀ S T : Subrep V, (∀ i, IsCompl (S.carrier i) (T.carrier i)) → S = ⊥ ∨ T = ⊥

theorem IsIrreducible.isIndecomposable {V : QRep k Q} (h : V.IsIrreducible) : V.IsIndecomposable := by
  refine ⟨h.1, fun S T hST => ?_⟩
  rcases h.2 S with hS | hS
  · exact Or.inl hS
  · right
    apply Subrep.ext
    intro i
    have := (hST i).disjoint
    rw [hS, Subrep.top_carrier] at this
    exact top_disjoint.mp this

end QRep

namespace Quiver

variable {Q : Type v} [Quiver.{a} Q]

/-- A vertex is a sink if no arrow leaves it (all adjacent arrows point into it). -/
@[kb "etingof2011" "Definition 5.24, p. 90"]
def IsSink (i : Q) : Prop := ∀ j : Q, IsEmpty (i ⟶ j)

/-- A vertex is a source if no arrow enters it (all adjacent arrows point out of it). -/
@[kb "etingof2011" "Definition 5.24, p. 90"]
def IsSource (i : Q) : Prop := ∀ j : Q, IsEmpty (j ⟶ i)

end Quiver

/-! ### Example 5.7: the quiver `A₁` -/

section A1

variable {k : Type u} [Field k]

theorem rank_one_isCompl {M : Type*} [AddCommGroup M] [Module k M]
    (h : ∃ v : M, v ≠ 0 ∧ ∀ w, ∃ r : k, r • v = w) {S T : Submodule k M} (hST : IsCompl S T) :
    S = ⊥ ∨ T = ⊥ := by
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  obtain ⟨v, hv0, hv⟩ := h
  have hS' : S = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨c, hc⟩ := hv s
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hs0 (by rw [← hc]; simp)
    have hvs : v = c⁻¹ • s := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    obtain ⟨d, hd⟩ := hv w
    rw [← hd, hvs]
    exact S.smul_mem _ (S.smul_mem _ hs)
  have := hST.disjoint
  rw [hS'] at this
  exact top_disjoint.mp this

/-- **Example 5.7.** On a quiver with a single vertex and no arrows (`A₁`), a representation is
indecomposable if and only if its space has dimension one. -/
@[kb "etingof2011" "Example 5.7, p. 81"]
theorem isIndecomposable_iff_rank_eq_one {Q : Type v} [Quiver.{a} Q] [Unique Q]
    [∀ i j : Q, IsEmpty (i ⟶ j)] (V : QRep k Q) :
    V.IsIndecomposable ↔ Module.rank k (V.obj default) = 1 := by
  have hall : ∀ i : Q, i = default := fun i => Subsingleton.elim _ _
  let mk : Submodule k (V.obj default) → QRep.Subrep V := fun p =>
    { carrier := fun i => by rw [hall i]; exact p
      map_mem := fun a => isEmptyElim a }
  have mk_default : ∀ p, (mk p).carrier default = p := fun p => rfl
  have key : ∀ S : QRep.Subrep V, S = ⊥ ↔ S.carrier default = ⊥ := by
    intro S
    constructor
    · rintro rfl; rfl
    · intro h
      apply QRep.Subrep.ext
      intro i
      rw [hall i]
      exact h
  rw [rank_eq_one_iff]
  constructor
  · rintro ⟨hne, hdec⟩
    have hnt : Nontrivial (V.obj default) := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      apply hne
      apply QRep.Subrep.ext
      intro i
      rw [hall i]
      exact Subsingleton.elim _ _
    obtain ⟨v, hv⟩ := exists_ne (0 : V.obj default)
    obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span k {v})
    have hcompl : ∀ i, IsCompl ((mk (Submodule.span k {v})).carrier i) ((mk q).carrier i) := by
      intro i
      rw [hall i]
      exact hq
    refine ⟨v, hv, fun w => ?_⟩
    rcases hdec _ _ hcompl with h | h
    · exfalso
      have := (key _).mp h
      rw [mk_default] at this
      exact hv (by simpa using (Submodule.span_eq_bot.mp this) v (by simp))
    · have h2 := (key _).mp h
      rw [mk_default] at h2
      have hq' : Submodule.span k {v} = ⊤ := by
        have := hq.sup_eq_top
        rwa [h2, sup_bot_eq] at this
      have hw : w ∈ Submodule.span k {v} := by rw [hq']; trivial
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
      exact ⟨r, hr⟩
  · intro h
    obtain ⟨v, hv0, _⟩ := id h
    refine ⟨fun hbt => ?_, fun S T hST => ?_⟩
    · have := congrArg (fun S : QRep.Subrep V => S.carrier default) hbt
      have hv : v ∈ (⊤ : Submodule k (V.obj default)) := trivial
      simp only [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier] at this
      rw [← this] at hv
      exact hv0 (by simpa using hv)
    · rcases rank_one_isCompl h (hST default) with h' | h'
      · exact Or.inl ((key S).mpr h')
      · exact Or.inr ((key T).mpr h')

end A1

end UndergradKB.RepresentationTheory
