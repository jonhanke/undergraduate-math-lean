import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Defs
import UndergradKB.Common.Attr

/-! # Extensions of modules and 1-cocycles (Etingof et al., Problem 2.21)

Let `A` be an algebra over a commutative ring `k`, and let `V`, `W` be `A`-modules, presented as algebra
homomorphisms `ρV : A → End_k V` and `ρW : A → End_k W`. A 1-cocycle is a `k`-linear map `c : A → Hom_k(W, V)`
with `c (a b) = ρV a ∘ c b + c a ∘ ρW b`; a coboundary is a map of the form `a ↦ ρV a ∘ f - f ∘ ρW a` with
`f : W → V` linear.

* every cocycle `c` makes `V × W` an `A`-module `extRep c` (upper triangular matrices) such that the inclusion of `V`
  and the projection onto `W` are module maps forming a short exact sequence;
* two cocycles give isomorphic extensions (an isomorphism compatible with the inclusion and projection) exactly
  when they differ by a coboundary;
* the space of cocycles modulo coboundaries, the group `Ext^1(W, V)` in the book's description, is defined as a
  quotient of additive groups (Mathlib could not form the `Submodule` quotient of this subtype).

Not formalized: the converse direction that every extension with underlying space `V ⊕ W` arises from a cocycle
(it follows from the same computation, with `c a w` the `V`-component of `a (0, w)`), and the identification with the
derived functor `Ext^1`.
-/

namespace UndergradKB.RepresentationTheory

namespace Extensions

variable {k A V W : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A 1-cocycle of `A` with coefficients in `Hom_k(W, V)`. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
def IsCocycle (ρV : A →ₐ[k] Module.End k V) (ρW : A →ₐ[k] Module.End k W) (c : A →ₗ[k] (W →ₗ[k] V)) : Prop :=
  ∀ a b : A, c (a * b) = ρV a ∘ₗ c b + c a ∘ₗ ρW b

/-- The coboundary of `f : W → V` is the map `a ↦ ρV a ∘ f - f ∘ ρW a`. -/
def coboundaryMap (ρV : A →ₐ[k] Module.End k V) (ρW : A →ₐ[k] Module.End k W) (f : W →ₗ[k] V) :
    A →ₗ[k] (W →ₗ[k] V) where
  toFun a := ρV a ∘ₗ f - f ∘ₗ ρW a
  map_add' a b := by
    simp only [map_add, LinearMap.add_comp, LinearMap.comp_add]
    abel
  map_smul' r a := by
    simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply, smul_sub]

/-- The coboundary map as a linear map in `f`. -/
def coboundaryLin (ρV : A →ₐ[k] Module.End k V) (ρW : A →ₐ[k] Module.End k W) :
    (W →ₗ[k] V) →ₗ[k] (A →ₗ[k] (W →ₗ[k] V)) where
  toFun := coboundaryMap ρV ρW
  map_add' f g := by
    ext a w
    simp [coboundaryMap]
    abel
  map_smul' r f := by
    ext a w
    simp [coboundaryMap, smul_sub]

/-- The submodule of 1-cocycles. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
def cocycles (ρV : A →ₐ[k] Module.End k V) (ρW : A →ₐ[k] Module.End k W) :
    Submodule k (A →ₗ[k] (W →ₗ[k] V)) where
  carrier := {c | IsCocycle ρV ρW c}
  add_mem' := by
    intro c d hc hd a b
    simp only [LinearMap.add_apply, hc a b, hd a b, LinearMap.comp_add, LinearMap.add_comp]
    abel
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro r c hc a b
    simp only [LinearMap.smul_apply, hc a b, smul_add, LinearMap.comp_smul, LinearMap.smul_comp]

/-- The submodule of coboundaries. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
def coboundaries (ρV : A →ₐ[k] Module.End k V) (ρW : A →ₐ[k] Module.End k W) :
    Submodule k (A →ₗ[k] (W →ₗ[k] V)) :=
  LinearMap.range (coboundaryLin ρV ρW)

/-- Every coboundary is a cocycle. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
theorem coboundaries_le_cocycles (ρV : A →ₐ[k] Module.End k V) (ρW : A →ₐ[k] Module.End k W) :
    coboundaries ρV ρW ≤ cocycles ρV ρW := by
  rintro _ ⟨f, rfl⟩ a b
  ext w
  simp [coboundaryLin, coboundaryMap]

/-- The space of cocycles modulo coboundaries, the book's description of `Ext^1(W, V)`. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
abbrev ExtOne (ρV : A →ₐ[k] Module.End k V) (ρW : A →ₐ[k] Module.End k W) : Type _ :=
  ↥(cocycles ρV ρW) ⧸
    AddSubgroup.comap (cocycles ρV ρW).subtype.toAddMonoidHom (coboundaries ρV ρW).toAddSubgroup

variable {ρV : A →ₐ[k] Module.End k V} {ρW : A →ₐ[k] Module.End k W} {c : A →ₗ[k] (W →ₗ[k] V)}

theorem IsCocycle.map_one (hc : IsCocycle ρV ρW c) : c 1 = 0 := by
  have h := hc 1 1
  have h2 : c 1 = c 1 + c 1 := by simpa [Module.End.one_eq_id] using h
  simpa using h2

/-- The `A`-action on `V × W` determined by a cocycle: `a (v, w) = (a v + c a w, a w)`. -/
noncomputable def extAction (hc : IsCocycle ρV ρW c) : A →ₐ[k] Module.End k (V × W) :=
  AlgHom.ofLinearMap
    { toFun := fun a => LinearMap.prod (ρV a ∘ₗ LinearMap.fst k V W + c a ∘ₗ LinearMap.snd k V W)
        (ρW a ∘ₗ LinearMap.snd k V W)
      map_add' := fun a b => by
        ext <;> simp
      map_smul' := fun r a => by
        ext <;> simp }
    (by
      ext <;> simp [hc.map_one])
    (by
      intro a b
      refine LinearMap.ext fun x => Prod.ext ?_ ?_
      · simp [hc a b]
        abel
      · simp)

@[simp] theorem extAction_apply (hc : IsCocycle ρV ρW c) (a : A) (x : V × W) :
    extAction hc a x = (ρV a x.1 + c a x.2, ρW a x.2) := by simp [extAction]

/-- The inclusion `V → V × W` is a module map for the extension action. -/
theorem extAction_inl (hc : IsCocycle ρV ρW c) (a : A) (v : V) :
    extAction hc a (v, 0) = (ρV a v, 0) := by
  simp

/-- The projection `V × W → W` is a module map for the extension action. -/
theorem extAction_snd (hc : IsCocycle ρV ρW c) (a : A) (x : V × W) :
    (extAction hc a x).2 = ρW a x.2 := by simp

/-- The sequence `0 → V → V × W → W → 0` is exact (injective inclusion, surjective projection, kernel of the
projection equal to the image of the inclusion); the maps are `A`-equivariant by `extAction_inl` and
`extAction_snd`. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
theorem extension_exact :
    Function.Injective (LinearMap.inl k V W) ∧ Function.Surjective (LinearMap.snd k V W) ∧
      Function.Exact (LinearMap.inl k V W) (LinearMap.snd k V W) := by
  refine ⟨LinearMap.inl_injective, LinearMap.snd_surjective, ?_⟩
  intro x
  constructor
  · intro h
    exact ⟨x.1, Prod.ext rfl (by simpa using h.symm)⟩
  · rintro ⟨v, rfl⟩
    rfl

/-- An isomorphism of the extensions defined by two cocycles: an `A`-equivariant linear isomorphism of `V × W`
compatible with the inclusion of `V` and the projection onto `W`. -/
def ExtIso (hc : IsCocycle ρV ρW c) {c' : A →ₗ[k] (W →ₗ[k] V)} (hc' : IsCocycle ρV ρW c') : Prop :=
  ∃ φ : (V × W) ≃ₗ[k] (V × W), (∀ a x, φ (extAction hc a x) = extAction hc' a (φ x)) ∧
    (∀ v, φ (v, 0) = (v, 0)) ∧ ∀ x, (φ x).2 = x.2

/-- Two cocycles define isomorphic extensions of `W` by `V` if and only if they differ by a coboundary. -/
@[kb "etingof2011" "Problem 2.21, p. 30"]
theorem extIso_iff {c' : A →ₗ[k] (W →ₗ[k] V)} (hc : IsCocycle ρV ρW c) (hc' : IsCocycle ρV ρW c') :
    ExtIso hc hc' ↔ c - c' ∈ coboundaries ρV ρW := by
  constructor
  · rintro ⟨φ, hφ, hι, hp⟩
    -- the `V`-component of `φ (0, w)`
    let f : W →ₗ[k] V := LinearMap.fst k V W ∘ₗ (φ : (V × W) →ₗ[k] V × W) ∘ₗ LinearMap.inr k V W
    have hφx : ∀ x : V × W, φ x = (x.1 + f x.2, x.2) := by
      intro x
      have hx : x = (x.1, 0) + (0, x.2) := by simp
      have h2 : (φ (0, x.2)).2 = x.2 := hp (0, x.2)
      conv_lhs => rw [hx, map_add, hι]
      refine Prod.ext ?_ ?_
      · simp [f]
      · simpa using h2
    refine ⟨f, ?_⟩
    ext a w
    have := hφ a (0, w)
    rw [hφx, hφx] at this
    have h1 := congrArg Prod.fst this
    simp [coboundaryLin, coboundaryMap] at h1 ⊢
    rw [sub_eq_sub_iff_add_eq_add]
    exact h1.symm
  · rintro ⟨f, hf⟩
    let φ : (V × W) ≃ₗ[k] (V × W) :=
      { toFun := fun x => (x.1 + f x.2, x.2)
        map_add' := fun x y => by
          ext <;> simp
          abel
        map_smul' := fun r x => by
          ext <;> simp [smul_add]
        invFun := fun x => (x.1 - f x.2, x.2)
        left_inv := fun x => by simp
        right_inv := fun x => by simp }
    refine ⟨φ, ?_, ?_, ?_⟩
    · intro a x
      have h := LinearMap.congr_fun (LinearMap.congr_fun hf a) x.2
      simp [coboundaryLin, coboundaryMap] at h
      simp only [φ, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, extAction_apply, map_add]
      refine Prod.ext ?_ rfl
      simp only
      rw [sub_eq_sub_iff_add_eq_add] at h
      rw [add_assoc (ρV a x.1) (ρV a (f x.2)), h]
      abel
    · intro v
      simp [φ]
    · intro x
      rfl

/-- Isomorphism of extensions is the equivalence relation "same class in `ExtOne`". -/
theorem extIso_iff_mk_eq {c' : A →ₗ[k] (W →ₗ[k] V)} (hc : IsCocycle ρV ρW c) (hc' : IsCocycle ρV ρW c') :
    ExtIso hc hc' ↔
      (QuotientAddGroup.mk (⟨c, hc⟩ : cocycles ρV ρW) : ExtOne ρV ρW) =
        QuotientAddGroup.mk (⟨c', hc'⟩ : cocycles ρV ρW) := by
  rw [extIso_iff hc hc', QuotientAddGroup.eq]
  rw [AddSubgroup.mem_comap, ← neg_mem_iff (G := A →ₗ[k] (W →ₗ[k] V)) (H := coboundaries ρV ρW)]
  simp [neg_add_eq_sub]

end Extensions

end UndergradKB.RepresentationTheory
