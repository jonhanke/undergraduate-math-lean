import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.SetTheory.Cardinal.Finite
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.Common.Attr

/-! # Irreducible representations of a product of groups (Etingof et al., Theorem 4.25)

Let `k` be an algebraically closed field and `G`, `H` finite groups whose orders are invertible in `k`.
The external tensor product of a representation `V` of `G` and a representation `W` of `H` is the representation
`(g, h) ↦ ρ(g) ⊗ σ(h)` of `G × H` on `V ⊗ W`.  We show:

* its character is `(g, h) ↦ χ_V(g) χ_W(h)`;
* it is irreducible when `V` and `W` are (this holds over any algebraically closed field, using the Jacobson
  density theorem: the images of `k[G]` and `k[H]` are the full endomorphism algebras);
* every irreducible representation of `G × H` is isomorphic to one of this form, by comparing the number of
  irreducible characters of `G × H` (the number of conjugacy classes) with the number of pairs.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Representation Module TensorProduct
open scoped MonoidAlgebra

/-! ### Irreducible representations span all endomorphisms -/

section Density

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A finite-dimensional irreducible representation over an algebraically closed field is
nontrivial as a vector space. -/
theorem nontrivial_of_isIrreducible {ρ : Representation k G V} [IsIrreducible ρ] : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    exact Subsingleton.elim _ _
  exact bot_ne_top this

/-- For a finite-dimensional irreducible representation `ρ` over an algebraically closed field, the operators
`ρ g` span the space of all linear endomorphisms (a consequence of Jacobson density). -/
theorem span_range_eq_top [IsAlgClosed k] [FiniteDimensional k V] (ρ : Representation k G V)
    [IsIrreducible ρ] : Submodule.span k (Set.range ρ) = ⊤ := by
  have hsurj : Function.Surjective ρ.asAlgebraHom := by
    intro f
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := ρ.asModule)
    let f' : Module.End (Module.End k[G] ρ.asModule) ρ.asModule :=
      { toFun := fun m ↦ ρ.asModuleEquiv.symm (f (ρ.asModuleEquiv m))
        map_add' := by intros; simp
        map_smul' := fun φ m ↦ by
          obtain ⟨c, rfl⟩ :=
            (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
              (A := k[G]) (V := ρ.asModule)).2 φ
          simp }
    obtain ⟨r, hr⟩ := jacobson_density f' s
    refine ⟨r, ?_⟩
    have : (ρ.asAlgebraHom r).comp ρ.asModuleEquiv.toLinearMap = f.comp ρ.asModuleEquiv.toLinearMap := by
      refine LinearMap.ext_on hs fun m hm ↦ ?_
      have h1 := hr m hm
      have h2 := congrArg ρ.asModuleEquiv h1
      simp only [f', LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] at h2
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h2, asModuleEquiv_map_smul]
    ext v
    simpa using (LinearMap.congr_fun this (ρ.asModuleEquiv.symm v))
  rw [eq_top_iff]
  intro f hf
  clear hf
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single g c =>
    rw [asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end Density

/-! ### The external tensor product -/

section External

variable {k G H V W : Type*} [Field k] [Group G] [Group H] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The external tensor product of a representation `ρ` of `G` on `V` and a representation `σ` of `H` on `W`:
the representation `(g, h) ↦ ρ(g) ⊗ σ(h)` of `G × H` on `V ⊗ W`. -/
noncomputable def extTprod (ρ : Representation k G V) (σ : Representation k H W) :
    Representation k (G × H) (V ⊗[k] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

theorem extTprod_apply (ρ : Representation k G V) (σ : Representation k H W) (g : G) (h : H) :
    extTprod ρ σ (g, h) = TensorProduct.map (ρ g) (σ h) := rfl

/-- **Etingof et al., Theorem 4.25** (character part): the character of the external tensor product is the
product `(g, h) ↦ χ_V(g) χ_W(h)` of the characters. -/
@[kb "etingof2011" "Theorem 4.25, p. 54"]
theorem extTprod_character [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k H W) (p : G × H) :
    (extTprod ρ σ).character p = ρ.character p.1 * σ.character p.2 :=
  congrFun (char_tensor (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))) p

/-- **Etingof et al., Theorem 4.25** (irreducibility part): the external tensor product of finite-dimensional
irreducible representations over an algebraically closed field is irreducible. -/
@[kb "etingof2011" "Theorem 4.25, p. 54"]
instance isIrreducible_extTprod [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k H W) [IsIrreducible ρ] [IsIrreducible σ] :
    IsIrreducible (extTprod ρ σ) := by
  have hV : Nontrivial V := nontrivial_of_isIrreducible (ρ := ρ)
  have hW : Nontrivial W := nontrivial_of_isIrreducible (ρ := σ)
  have hP : Nontrivial (V ⊗[k] W) := by
    refine (Module.finrank_pos_iff (R := k)).mp ?_
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have : Nontrivial (Subrepresentation (extTprod ρ σ)) := by
    refine ⟨⟨⊥, ⊤, fun h ↦ ?_⟩⟩
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule k (V ⊗[k] W)) this
  refine { eq_bot_or_eq_top := fun S ↦ ?_ }
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hS' : S.toSubmodule ≠ ⊥ := fun e ↦ hS (Subrepresentation.ext e)
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'
  -- operators `a ⊗ id` preserving `S`
  let T1 : Submodule k (Module.End k V) :=
    { carrier := {a | ∀ y ∈ S.toSubmodule, TensorProduct.map a (LinearMap.id : W →ₗ[k] W) y ∈ S.toSubmodule}
      add_mem' := fun {a b} ha hb y hy ↦ by
        rw [TensorProduct.map_add_left, LinearMap.add_apply]
        exact S.toSubmodule.add_mem (ha y hy) (hb y hy)
      zero_mem' := fun y hy ↦ by simp
      smul_mem' := fun c a ha y hy ↦ by
        rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
        exact S.toSubmodule.smul_mem c (ha y hy) }
  let T2 : Submodule k (Module.End k W) :=
    { carrier := {b | ∀ y ∈ S.toSubmodule, TensorProduct.map (LinearMap.id : V →ₗ[k] V) b y ∈ S.toSubmodule}
      add_mem' := fun {a b} ha hb y hy ↦ by
        rw [TensorProduct.map_add_right, LinearMap.add_apply]
        exact S.toSubmodule.add_mem (ha y hy) (hb y hy)
      zero_mem' := fun y hy ↦ by simp
      smul_mem' := fun c a ha y hy ↦ by
        rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
        exact S.toSubmodule.smul_mem c (ha y hy) }
  have h1 : T1 = ⊤ := by
    rw [eq_top_iff, ← span_range_eq_top ρ, Submodule.span_le]
    rintro _ ⟨g, rfl⟩ y hy
    have := S.apply_mem_toSubmodule (g, 1) hy
    rwa [extTprod_apply, map_one, Module.End.one_eq_id] at this
  have h2 : T2 = ⊤ := by
    rw [eq_top_iff, ← span_range_eq_top σ, Submodule.span_le]
    rintro _ ⟨h, rfl⟩ y hy
    have := S.apply_mem_toSubmodule (1, h) hy
    rwa [extTprod_apply, map_one, Module.End.one_eq_id] at this
  have h3 : ∀ (a : Module.End k V) (b : Module.End k W), ∀ y ∈ S.toSubmodule,
      TensorProduct.map a b y ∈ S.toSubmodule := by
    intro a b y hy
    have ha : a ∈ T1 := by rw [h1]; trivial
    have hb : b ∈ T2 := by rw [h2]; trivial
    have : TensorProduct.map a b =
        TensorProduct.map a (LinearMap.id : W →ₗ[k] W) ∘ₗ TensorProduct.map (LinearMap.id : V →ₗ[k] V) b := by
      ext v w
      simp
    rw [this, LinearMap.comp_apply]
    exact ha _ (hb y hy)
  let T3 : Submodule k (Module.End k (V ⊗[k] W)) :=
    { carrier := {F | ∀ y ∈ S.toSubmodule, F y ∈ S.toSubmodule}
      add_mem' := fun {a b} ha hb y hy ↦ by
        rw [LinearMap.add_apply]
        exact S.toSubmodule.add_mem (ha y hy) (hb y hy)
      zero_mem' := fun y hy ↦ by simp
      smul_mem' := fun c a ha y hy ↦ by
        rw [LinearMap.smul_apply]
        exact S.toSubmodule.smul_mem c (ha y hy) }
  have h4 : ∀ F, F ∈ T3 := by
    intro F
    obtain ⟨z, rfl⟩ := (homTensorHomEquiv k V W V W).surjective F
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [homTensorHomEquiv_apply, homTensorHomMap_apply]; exact h3 a b
    | add z z' hz hz' => rw [map_add]; exact T3.add_mem hz hz'
  apply Subrepresentation.ext
  refine Submodule.eq_top_iff'.mpr fun y ↦ ?_
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (V ⊗[k] W), φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff k x).mp h)
  have := h4 ((φ x)⁻¹ • LinearMap.smulRight φ y) x hxS
  simpa [hφ] using this

end External

/-! ### Every irreducible representation of a product is an external tensor product -/

section Classification

variable {k : Type u} {G H : Type v} [Field k] [Group G] [Group H] [Fintype G] [Fintype H] [IsAlgClosed k]
  [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)]

/-- The order of `G × H` is invertible in `k` when the orders of `G` and `H` are. -/
noncomputable instance instInvertibleNatCardProd : Invertible (Nat.card (G × H) : k) := by
  rw [Nat.card_prod, Nat.cast_mul]
  exact invertibleMul _ _

/-- The external tensor product of two bundled irreducible representations, as a bundled irreducible
representation of `G × H`. -/
noncomputable def IrrRep.extTprod (X : IrrRep k G) (Y : IrrRep k H) : IrrRep k (G × H) where
  V := X.V ⊗[k] Y.V
  ρ := UndergradKB.RepresentationTheory.extTprod X.ρ Y.ρ

omit [IsAlgClosed k] [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)] in
theorem pairing_prod (χ χ' : G → k) (ψ ψ' : H → k) :
    pairing (fun p : G × H ↦ χ p.1 * ψ p.2) (fun p : G × H ↦ χ' p.1 * ψ' p.2) =
      pairing χ χ' * pairing ψ ψ' := by
  have : ∑ g, ∑ h, (χ g * ψ h) * (χ' g⁻¹ * ψ' h⁻¹) =
      (∑ g, χ g * χ' g⁻¹) * ∑ h, ψ h * ψ' h⁻¹ := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun h _ ↦ by ring
  simp only [pairing_apply, Fintype.sum_prod_type, Nat.card_prod, Nat.cast_mul, mul_inv, Prod.fst_inv,
    Prod.snd_inv]
  rw [this]
  ring

omit [Fintype G] [Fintype H] in
/-- The conjugacy classes of a product of groups are the pairs of conjugacy classes. -/
theorem card_conjClasses_prod :
    Nat.card (ConjClasses (G × H)) = Nat.card (ConjClasses G) * Nat.card (ConjClasses H) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun C ↦ (ConjClasses.map (MonoidHom.fst G H) C, ConjClasses.map (MonoidHom.snd G H) C)) ⟨?_, ?_⟩)
  · intro C D h
    obtain ⟨⟨a, b⟩, rfl⟩ := ConjClasses.mk_surjective C
    obtain ⟨⟨a', b'⟩, rfl⟩ := ConjClasses.mk_surjective D
    change (ConjClasses.mk a, ConjClasses.mk b) = (ConjClasses.mk a', ConjClasses.mk b') at h
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (Prod.ext_iff.mp h).1)
    obtain ⟨d, hd⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp (Prod.ext_iff.mp h).2)
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨(c, d), Prod.ext hc hd⟩)
  · rintro ⟨C, D⟩
    obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
    obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective D
    exact ⟨ConjClasses.mk (a, b), rfl⟩

omit [Fintype G] [Fintype H] [Invertible (Nat.card G : k)] [Invertible (Nat.card H : k)] in
theorem prod_mem_irrChars {χ : G → k} {ψ : H → k} (hχ : χ ∈ irrChars k G) (hψ : ψ ∈ irrChars k H) :
    (fun p : G × H ↦ χ p.1 * ψ p.2) ∈ irrChars k (G × H) := by
  obtain ⟨X, rfl⟩ := hχ
  obtain ⟨Y, rfl⟩ := hψ
  exact ⟨X.extTprod Y, funext fun p ↦ extTprod_character X.ρ Y.ρ p⟩

/-- **Etingof et al., Theorem 4.25** (classification part): every irreducible representation of `G × H` is
isomorphic to the external tensor product `V ⊠ W` of irreducible representations `V` of `G` and `W` of `H`.
(That each such tensor product is irreducible is the instance `isIrreducible_extTprod`; the proof here counts
irreducible characters: the products `χ_V χ_W` are orthonormal, hence distinct, and there are as many of them as
conjugacy classes of `G × H`.) -/
@[kb "etingof2011" "Theorem 4.25, p. 54"]
theorem exists_equiv_extTprod (Z : IrrRep k (G × H)) :
    ∃ (X : IrrRep k G) (Y : IrrRep k H),
      Nonempty (Representation.Equiv Z.ρ (X.extTprod Y).ρ) := by
  classical
  let Φ : irrChars k G × irrChars k H → irrChars k (G × H) :=
    fun p ↦ ⟨_, prod_mem_irrChars p.1.2 p.2.2⟩
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have hval : (fun x : G × H ↦ (p.1 : G → k) x.1 * (p.2 : H → k) x.2) =
        fun x : G × H ↦ (q.1 : G → k) x.1 * (q.2 : H → k) x.2 := congrArg Subtype.val hpq
    have key : pairing (p.1 : G → k) q.1 * pairing (p.2 : H → k) q.2 = 1 := by
      have := pairing_irrChars (prod_mem_irrChars p.1.2 p.2.2) (prod_mem_irrChars p.1.2 p.2.2)
      rw [if_pos rfl] at this
      rw [← pairing_prod, ← hval]
      exact this
    have e1 : p.1 = q.1 := by
      by_contra hne
      have : pairing (p.1 : G → k) q.1 = 0 := by
        rw [pairing_irrChars p.1.2 q.1.2, if_neg (fun h ↦ hne (Subtype.ext h))]
      rw [this, zero_mul] at key
      exact zero_ne_one key
    have e2 : p.2 = q.2 := by
      by_contra hne
      have : pairing (p.2 : H → k) q.2 = 0 := by
        rw [pairing_irrChars p.2.2 q.2.2, if_neg (fun h ↦ hne (Subtype.ext h))]
      rw [this, mul_zero] at key
      exact zero_ne_one key
    exact Prod.ext e1 e2
  have hbij : Function.Bijective Φ := by
    refine hinj.bijective_of_nat_card_le (le_of_eq ?_)
    rw [Nat.card_prod, card_irrChars, card_irrChars, card_irrChars, card_conjClasses_prod]
  obtain ⟨p, hp⟩ := hbij.2 ⟨Z.ρ.character, Z, rfl⟩
  obtain ⟨X, hX⟩ := p.1.2
  obtain ⟨Y, hY⟩ := p.2.2
  refine ⟨X, Y, (nonempty_equiv_iff_character_eq _ _).mpr (funext fun x ↦ ?_)⟩
  have := congrFun (congrArg Subtype.val hp) x
  change (p.1 : G → k) x.1 * (p.2 : H → k) x.2 = Z.ρ.character x at this
  rw [← this, ← hX, ← hY]
  exact (extTprod_character X.ρ Y.ρ x).symm

end Classification

end UndergradKB.RepresentationTheory
