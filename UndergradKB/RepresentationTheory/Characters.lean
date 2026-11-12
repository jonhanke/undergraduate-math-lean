import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas
import UndergradKB.Common.Attr

/-! # Characters of finite groups: the basis of class functions (Etingof et al., §3.2 to §3.5)

Setting of the book's chapter 3: `G` a finite group, `k` an algebraically closed field whose characteristic does not
divide the order of `G`. Mathlib has the character, its class-function property and the first orthogonality relation
(`Representation.char_orthonormal`). Here:

* central elements of an algebra act by scalars on finite-dimensional irreducible modules (Problem 1.21);
* the dimension of an irreducible representation is nonzero in `k`;
* the characters of the irreducible representations form a basis of the class functions (Theorem 3.5);
* the number of irreducible representations (up to isomorphism) is the number of conjugacy classes (Corollary 3.6);
* the second orthogonality relation (Theorem 3.9) and the sum-of-squares formula (Theorem 3.1(ii)).

The proof of Theorem 3.5 avoids the Wedderburn decomposition: a class function orthogonal to every irreducible
character gives a central element of `k[G]` acting by zero on every simple submodule of `k[G]`, hence zero.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Representation MonoidAlgebra Module

/-! ### Central elements act by scalars -/

section Central

variable (k : Type*) {A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M] [FiniteDimensional k M] [IsSimpleModule A M] [IsAlgClosed k]

/-- **Etingof et al., Problem 1.21**: a central element of an algebra acts on a finite-dimensional irreducible
representation over an algebraically closed field by a scalar (the central character). -/
@[kb "etingof2011" "Problem 1.21, p. 10"]
theorem exists_smul_eq_of_mem_center (z : A) (hz : z ∈ Subalgebra.center k A) :
    ∃ c : k, ∀ m : M, z • m = c • m := by
  let f : Module.End A M :=
    { toFun := fun m ↦ z • m
      map_add' := smul_add z
      map_smul' := fun a m ↦ by
        simp only [RingHom.id_apply, smul_smul]
        rw [Subalgebra.mem_center_iff.mp hz a] }
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k (A := A) (V := M)).2 f
  refine ⟨c, fun m ↦ ?_⟩
  have := congrArg (fun φ : Module.End A M ↦ φ m) hc
  simpa [f, Module.algebraMap_end_apply] using this.symm

end Central

/-! ### Schur's lemma and the dimension of an irreducible representation -/

section Schur

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- Schur's lemma in the form used below: a linear endomorphism commuting with the action of `G` on a
finite-dimensional irreducible representation over an algebraically closed field is a scalar. -/
theorem exists_eq_smul_id_of_commute [IsAlgClosed k] [FiniteDimensional k V] [IsIrreducible ρ]
    (f : V →ₗ[k] V) (hf : ∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) : ∃ c : k, f = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2 ⟨f, hf⟩
  refine ⟨c, LinearMap.ext fun v ↦ ?_⟩
  have := congrArg (fun φ : IntertwiningMap ρ ρ ↦ φ v) hc
  simpa using this.symm

/-- The dimension of an irreducible representation of a finite group over an algebraically closed field whose
characteristic does not divide the group order is nonzero in the field. (The proof averages a rank-one operator
of trace one over the group.) -/
theorem finrank_ne_zero_of_isIrreducible [Fintype G] [Invertible (Nat.card G : k)] [IsAlgClosed k]
    [FiniteDimensional k V] [IsIrreducible ρ] : (finrank k V : k) ≠ 0 := by
  have hnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      exact Subsingleton.elim _ _
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k V, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff k v).mp h)
  let A : V →ₗ[k] V := LinearMap.smulRight φ v
  let T : V →ₗ[k] V := ∑ g : G, ρ g ∘ₗ A ∘ₗ ρ g⁻¹
  have hT : ∀ h, T ∘ₗ ρ h = ρ h ∘ₗ T := by
    intro h
    ext x
    simp only [T, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g ↦ ?_)
    simp only [Equiv.coe_mulLeft, map_mul, mul_apply_eq_comp, mul_inv_rev, inv_inv,
      Representation.self_inv_apply]
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_commute T hT
  have htr : LinearMap.trace k V T = (Fintype.card G : k) * φ v := by
    simp only [T, map_sum]
    have : ∀ g : G, LinearMap.trace k V (ρ g ∘ₗ A ∘ₗ ρ g⁻¹) = φ v := by
      intro g
      have hid : ρ g⁻¹ ∘ₗ ρ g = LinearMap.id := by ext; simp
      rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, hid, LinearMap.comp_id,
        LinearMap.trace_smulRight]
    simp [this]
  intro h0
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, h0, mul_zero] at htr
  have hG : (Fintype.card G : k) ≠ 0 := by
    rw [Fintype.card_eq_nat_card]; exact (isUnit_of_invertible _).ne_zero
  exact (mul_ne_zero hG hφ) htr.symm

end Schur

/-! ### Class functions and the pairing -/

variable (k G : Type*) [Field k] [Group G]

/-- The class functions on `G`: functions constant on conjugacy classes. -/
def classFunctions : Submodule k (G → k) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  add_mem' hf hg g h := by simp [hf g h, hg g h]
  zero_mem' := by simp
  smul_mem' c f hf g h := by simp [hf g h]

variable {k G}

theorem mem_classFunctions {f : G → k} : f ∈ classFunctions k G ↔ ∀ g h : G, f (h * g * h⁻¹) = f g :=
  Iff.rfl

theorem character_mem_classFunctions {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    ρ.character ∈ classFunctions k G := fun g h ↦ ρ.char_conj g h

theorem classFunctions_isConj {f : G → k} (hf : f ∈ classFunctions k G) {g g' : G} (h : IsConj g g') :
    f g = f g' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, hf]

/-- Class functions are functions on conjugacy classes. -/
noncomputable def classFunctionsEquiv : classFunctions k G ≃ₗ[k] (ConjClasses G → k) where
  toFun f C := f.1 C.exists_rep.choose
  invFun F := ⟨F ∘ ConjClasses.mk, fun g h ↦ by
    simp only [Function.comp_apply]
    exact congrArg F (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    ext g
    exact classFunctions_isConj f.2 (ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.exists_rep _).choose_spec)
  right_inv F := by
    ext C
    simp [(ConjClasses.exists_rep C).choose_spec]

theorem finrank_classFunctions [Finite G] : finrank k (classFunctions k G) = Nat.card (ConjClasses G) := by
  classical
  have := Fintype.ofFinite G
  rw [(classFunctionsEquiv (k := k) (G := G)).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

variable [Fintype G]

/-- The pairing of functions on `G` used in the orthogonality relations, `|G|⁻¹ ∑ f₁(g) f₂(g⁻¹)` (over the complex
numbers and for characters this is the book's Hermitian product, since `χ(g⁻¹)` is the conjugate of `χ(g)`). -/
noncomputable def pairing : (G → k) →ₗ[k] (G → k) →ₗ[k] k :=
  LinearMap.mk₂ k (fun f₁ f₂ ↦ (Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * f₂ g⁻¹)
    (fun _ _ _ ↦ by simp [add_mul, Finset.sum_add_distrib, mul_add])
    (fun _ _ _ ↦ by simp [Finset.mul_sum, mul_assoc, mul_left_comm])
    (fun _ _ _ ↦ by simp [mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [Finset.mul_sum, mul_left_comm])

theorem pairing_apply (f₁ f₂ : G → k) :
    pairing f₁ f₂ = (Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * f₂ g⁻¹ := rfl

/-! ### Class functions and central elements of the group algebra -/

/-- The element `∑ f(g) g⁻¹` of the group algebra attached to a function `f`. -/
noncomputable def centralElt (f : G → k) : k[G] := ∑ g : G, f g • of k G g⁻¹

theorem centralElt_comm {f : G → k} (hf : f ∈ classFunctions k G) (h : G) :
    of k G h * centralElt f = centralElt f * of k G h := by
  have key : of k G h * centralElt f * of k G h⁻¹ = centralElt f := by
    simp only [centralElt, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, ← map_mul]
    refine Fintype.sum_equiv (MulAut.conj h) _ _ (fun g ↦ ?_)
    show f g • of k G (h * g⁻¹ * h⁻¹) = f (h * g * h⁻¹) • of k G (h * g * h⁻¹)⁻¹
    rw [hf g h]
    congr 2
    group
  calc of k G h * centralElt f = of k G h * centralElt f * of k G h⁻¹ * of k G h := by
        rw [mul_assoc _ (of k G h⁻¹), ← map_mul, inv_mul_cancel, map_one, mul_one]
    _ = centralElt f * of k G h := by rw [key]

theorem trace_centralElt {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (f : G → k) :
    LinearMap.trace k V (ρ.asAlgebraHom (centralElt f)) = ∑ g : G, f g * ρ.character g⁻¹ := by
  simp [centralElt, map_sum, character]

theorem centralElt_eq_zero {f : G → k} (h : centralElt f = 0) : f = 0 := by
  classical
  funext g
  have := congrArg (fun x : k[G] ↦ x.coeff g⁻¹) h
  simpa [centralElt, coeff_sum, Finsupp.single_apply] using this

/-- An element of `k[G]` that kills every simple submodule of `k[G]` (by left multiplication) is zero, when `k[G]`
is semisimple. -/
theorem eq_zero_of_forall_simple [NeZero (Nat.card G : k)] (z : k[G])
    (hz : ∀ S : Submodule k[G] k[G], IsSimpleModule k[G] S → ∀ s ∈ S, z * s = 0) : z = 0 := by
  let K : Submodule k[G] k[G] :=
    { carrier := {x | ∀ a : k[G], z * (a * x) = 0}
      add_mem' := fun hx hy a ↦ by simp [mul_add, hx a, hy a]
      zero_mem' := fun a ↦ by simp
      smul_mem' := fun c x hx a ↦ by
        simp only [smul_eq_mul, Set.mem_setOf_eq, ← mul_assoc] at hx ⊢
        simpa [mul_assoc] using hx (a * c) }
  have hK : sSup {S : Submodule k[G] k[G] | IsSimpleModule k[G] S} ≤ K :=
    sSup_le fun S hS x hx a ↦ hz S hS _ (S.smul_mem a hx)
  rw [IsSemisimpleModule.sSup_simples_eq_top] at hK
  simpa using hK (Submodule.mem_top (x := (1 : k[G]))) 1

/-- Orbit-stabilizer for conjugation: the size of the conjugacy class of `g` times the order of its centralizer is
the order of `G`. -/
theorem card_isConj_mul_card_centralizer (g : G) :
    Nat.card {x // IsConj x g} * Nat.card (Subgroup.centralizer {g}) = Nat.card G := by
  classical
  have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  simp only [← Nat.card_eq_fintype_card] at h1
  rw [Subgroup.centralizer_eq_comap_stabilizer]
  change _ * Nat.card (MulAction.stabilizer (ConjAct G) g) = _
  have h2 : Nat.card {x // IsConj x g} = Nat.card (MulAction.orbit (ConjAct G) g) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ConjAct.mem_orbit_conjAct.symm)
  rw [h2, h1]
  rfl

/-! ### Irreducible representations as a type -/

variable (k G) in
/-- A finite-dimensional irreducible representation of `G` over `k`, bundled with its space (in the universe of
`k` and `G`); used to quantify over "all irreducible representations". -/
structure IrrRep (k : Type u) (G : Type v) [Field k] [Group G] where
  /-- The space of the representation. -/
  V : Type (max u v)
  [addCommGroup : AddCommGroup V]
  [module : Module k V]
  [finiteDimensional : FiniteDimensional k V]
  /-- The representation. -/
  ρ : Representation k G V
  [isIrreducible : IsIrreducible ρ]

attribute [instance] IrrRep.addCommGroup IrrRep.module IrrRep.finiteDimensional IrrRep.isIrreducible

section Main

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

instance : NeZero (Nat.card G : k) := ⟨(isUnit_of_invertible _).ne_zero⟩

variable (k G) in
/-- The set of characters of the irreducible representations of `G` over `k`. -/
noncomputable def irrChars : Set (G → k) := Set.range fun X : IrrRep k G ↦ X.ρ.character

open scoped Classical in
theorem pairing_character (X Y : IrrRep k G) :
    pairing X.ρ.character Y.ρ.character = if Nonempty (Representation.Equiv Y.ρ X.ρ) then 1 else 0 := by
  rw [pairing_apply, char_orthonormal]

/-- Two irreducible representations are isomorphic if and only if they have the same character. -/
theorem nonempty_equiv_iff_character_eq (X Y : IrrRep k G) :
    Nonempty (Representation.Equiv X.ρ Y.ρ) ↔ X.ρ.character = Y.ρ.character := by
  refine ⟨fun ⟨e⟩ ↦ char_iso e, fun h ↦ ?_⟩
  by_contra hne
  classical
  have h1 := pairing_character Y X
  have h2 := pairing_character Y Y
  rw [if_neg hne, h] at h1
  rw [if_pos ⟨Representation.Equiv.refl _⟩] at h2
  exact one_ne_zero (h2.symm.trans h1)

open scoped Classical in
theorem pairing_irrChars {χ ψ : G → k} (hχ : χ ∈ irrChars k G) (hψ : ψ ∈ irrChars k G) :
    pairing χ ψ = if χ = ψ then 1 else 0 := by
  obtain ⟨X, rfl⟩ := hχ
  obtain ⟨Y, rfl⟩ := hψ
  rw [pairing_character]
  by_cases h : X.ρ.character = Y.ρ.character
  · rw [if_pos ((nonempty_equiv_iff_character_eq Y X).mpr h.symm), if_pos h]
  · rw [if_neg (fun h' ↦ h ((nonempty_equiv_iff_character_eq Y X).mp h').symm), if_neg h]

theorem linearIndepOn_irrChars : LinearIndepOn k id (irrChars k G) := by
  classical
  rw [LinearIndepOn, linearIndependent_iff']
  intro s c hs i hi
  have := congrArg (pairing · (i : G → k)) hs
  simp only [map_sum, map_smul, map_zero, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, id_eq, smul_eq_mul] at this
  rw [Finset.sum_eq_single i] at this
  · simpa [pairing_irrChars i.2 i.2] using this
  · intro j _ hj
    rw [pairing_irrChars j.2 i.2, if_neg (fun h ↦ hj (Subtype.ext h))]
    simp
  · intro h; exact absurd hi h

theorem irrChars_finite : (irrChars k G).Finite := by
  have := LinearIndependent.finite_of_isNoetherian (linearIndepOn_irrChars (k := k) (G := G))
  exact Set.finite_coe_iff.mp this

noncomputable instance : Fintype (irrChars k G) := irrChars_finite.fintype

/-- A simple submodule of the group algebra, seen as an irreducible representation. -/
noncomputable def IrrRep.ofSimple (S : Submodule k[G] k[G]) [hS : IsSimpleModule k[G] S] : IrrRep k G :=
  let f : RestrictScalars k k[G] S →ₗ[k] k[G] :=
    { toFun := fun x ↦ (RestrictScalars.addEquiv k k[G] S x : k[G])
      map_add' := by simp
      map_smul' := fun c x ↦ by simp [RestrictScalars.addEquiv_map_smul, Algebra.smul_def] }
  have hfin : Module.Finite k (RestrictScalars k k[G] S) :=
    Module.Finite.of_injective f fun x y h ↦ (RestrictScalars.addEquiv k k[G] S).injective (Subtype.ext h)
  have hirr := (isSimpleModule_iff_irreducible_ofModule (k := k) (G := G) S).mp hS
  @IrrRep.mk k G _ _ (RestrictScalars k k[G] S) _ (RestrictScalars.module k k[G] S) hfin (ofModule S) hirr

/-- The key step of Theorem 3.5: a class function orthogonal to every irreducible character is zero. -/
theorem eq_zero_of_pairing_eq_zero {f : G → k} (hf : f ∈ classFunctions k G)
    (h : ∀ X : IrrRep k G, pairing f X.ρ.character = 0) : f = 0 := by
  apply centralElt_eq_zero
  apply eq_zero_of_forall_simple
  intro S hS s hs
  let X := IrrRep.ofSimple S
  have hcomm : ∀ g, X.ρ.asAlgebraHom (centralElt f) ∘ₗ X.ρ g = X.ρ g ∘ₗ X.ρ.asAlgebraHom (centralElt f) := by
    intro g
    rw [← asAlgebraHom_of, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul,
      centralElt_comm hf]
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_commute _ hcomm
  have htr := trace_centralElt X.ρ f
  have hp := h X
  rw [pairing_apply, mul_eq_zero, inv_eq_zero] at hp
  rcases hp with hp | hp
  · exact absurd hp (NeZero.ne _)
  rw [hp, hc, map_smul, LinearMap.trace_id, smul_eq_mul, mul_eq_zero] at htr
  rcases htr with rfl | htr
  · rw [zero_smul] at hc
    have := congrArg (fun φ : X.V →ₗ[k] X.V ↦ φ (show X.V from (RestrictScalars.addEquiv k k[G] S).symm ⟨s, hs⟩)) hc
    change (ofModule S).asAlgebraHom (centralElt f) ((RestrictScalars.addEquiv k k[G] S).symm ⟨s, hs⟩) = 0
      at this
    erw [ofModule_asAlgebraHom_apply_apply] at this
    simp only [AddEquiv.apply_symm_apply, map_eq_zero_iff _ (RestrictScalars.addEquiv k k[G] S).symm.injective] at this
    simpa using congrArg Subtype.val this
  · exact absurd htr (finrank_ne_zero_of_isIrreducible (ρ := X.ρ))

/-- Expansion of a class function in the irreducible characters. -/
theorem eq_sum_pairing_smul {f : G → k} (hf : f ∈ classFunctions k G) :
    f = ∑ χ : irrChars k G, pairing f χ • (χ : G → k) := by
  classical
  rw [← sub_eq_zero]
  refine eq_zero_of_pairing_eq_zero ?_ fun X ↦ ?_
  · refine Submodule.sub_mem _ hf (Submodule.sum_mem _ fun χ _ ↦ Submodule.smul_mem _ _ ?_)
    obtain ⟨X, hX⟩ := χ.2
    rw [← hX]
    exact character_mem_classFunctions _
  · have hX : X.ρ.character ∈ irrChars k G := ⟨X, rfl⟩
    simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ⟨_, hX⟩]
    · simp [pairing_irrChars hX hX]
    · intro χ _ hχ
      rw [pairing_irrChars χ.2 hX, if_neg (fun h ↦ hχ (Subtype.ext h)), mul_zero]
    · simp

/-- **Etingof et al., Theorem 3.5**: if `k` is algebraically closed and its characteristic does not divide the
order of `G`, the characters of the irreducible representations span the space of class functions; they are
linearly independent (`linearIndepOn_irrChars`), so they form a basis. -/
@[kb "etingof2011" "Theorem 3.5, p. 34"]
theorem span_irrChars : Submodule.span k (irrChars k G) = classFunctions k G := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨X, rfl⟩
    exact character_mem_classFunctions _
  · intro f hf
    rw [eq_sum_pairing_smul hf]
    exact Submodule.sum_mem _ fun χ _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span χ.2)

/-- **Etingof et al., Theorem 3.5** (basis form): the irreducible characters form a basis of the class
functions. -/
@[kb "etingof2011" "Theorem 3.5, p. 34"]
noncomputable def irrCharsBasis : Module.Basis (irrChars k G) k (classFunctions k G) :=
  (Module.Basis.span linearIndepOn_irrChars).map (LinearEquiv.ofEq _ _ (by
    rw [show (Set.range fun x : irrChars k G ↦ id (x : G → k)) = irrChars k G by ext; simp]
    exact span_irrChars))

/-- **Etingof et al., Corollary 3.6** (character form): the number of irreducible characters equals the number of
conjugacy classes. -/
@[kb "etingof2011" "Corollary 3.6, p. 34"]
theorem card_irrChars : Nat.card (irrChars k G) = Nat.card (ConjClasses G) := by
  rw [← finrank_classFunctions (k := k), Module.finrank_eq_card_basis (irrCharsBasis (k := k) (G := G)),
    Nat.card_eq_fintype_card]

/-- **Etingof et al., Corollary 3.6**: there is a family of pairwise non-isomorphic irreducible representations,
containing a copy of every irreducible representation, with exactly as many members as `G` has conjugacy
classes. -/
@[kb "etingof2011" "Corollary 3.6, p. 34"]
theorem exists_irreducibles_card_eq_card_conjClasses :
    ∃ (ι : Type (max u v)) (_ : Fintype ι) (X : ι → IrrRep k G),
      (∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j) ∧
      (∀ Y : IrrRep k G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) ∧
      Fintype.card ι = Nat.card (ConjClasses G) := by
  refine ⟨irrChars k G, inferInstance, fun χ ↦ χ.2.choose, ?_, ?_, ?_⟩
  · intro i j h
    apply Subtype.ext
    rw [← i.2.choose_spec, ← j.2.choose_spec]
    exact (nonempty_equiv_iff_character_eq _ _).mp h
  · intro Y
    refine ⟨⟨Y.ρ.character, Y, rfl⟩, ?_⟩
    rw [nonempty_equiv_iff_character_eq]
    exact (Exists.choose_spec (⟨Y, rfl⟩ : Y.ρ.character ∈ irrChars k G)).symm
  · rw [← Nat.card_eq_fintype_card, card_irrChars]

theorem mem_classFunctions_of_mem_irrChars (χ : irrChars k G) : (χ : G → k) ∈ classFunctions k G := by
  obtain ⟨X, hX⟩ := χ.2
  rw [← hX]
  exact character_mem_classFunctions _

open scoped Classical in
theorem pairing_indicator (h : G) (χ : irrChars k G) :
    pairing (fun x ↦ if IsConj x h then (1 : k) else 0) χ =
      (Nat.card G : k)⁻¹ * (Nat.card {x // IsConj x h} * (χ : G → k) h⁻¹) := by
  rw [pairing_apply]
  congr 1
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.sum_congr rfl (g := fun _ ↦ (χ : G → k) h⁻¹)]
  · rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro x hx
    rw [Finset.mem_filter] at hx
    apply classFunctions_isConj (mem_classFunctions_of_mem_irrChars χ)
    obtain ⟨c, hc⟩ := isConj_iff.mp hx.2
    exact isConj_iff.mpr ⟨c, by rw [← hc]; group⟩

open scoped Classical in
/-- **Etingof et al., Theorem 3.9** (second orthogonality relation): summing `χ(g) χ(h⁻¹)` over the irreducible
characters gives the order of the centralizer of `g` if `g` and `h` are conjugate, and `0` otherwise. (Over the
complex numbers `χ(h⁻¹)` is the complex conjugate of `χ(h)`, which is the book's form.) -/
@[kb "etingof2011" "Theorem 3.9, p. 38"]
theorem sum_irrChars_mul_inv (g h : G) :
    ∑ χ : irrChars k G, (χ : G → k) g * (χ : G → k) h⁻¹ =
      if IsConj g h then (Nat.card (Subgroup.centralizer {g}) : k) else 0 := by
  set δ : G → k := fun x ↦ if IsConj x h then 1 else 0 with hδdef
  have hδ : δ ∈ classFunctions k G := by
    intro x c
    have : IsConj (c * x * c⁻¹) h ↔ IsConj x h :=
      ⟨fun H ↦ (isConj_iff.mpr ⟨c, rfl⟩).trans H, fun H ↦ (isConj_iff.mpr ⟨c, rfl⟩).symm.trans H⟩
    simp only [δ, this]
  have hexp := congrFun (eq_sum_pairing_smul hδ) g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hδdef, pairing_indicator] at hexp
  have hN := card_isConj_mul_card_centralizer h
  have hG : (Nat.card G : k) ≠ 0 := NeZero.ne _
  have hNk : (Nat.card {x // IsConj x h} : k) ≠ 0 := by
    intro h0; apply hG; rw [← hN, Nat.cast_mul, h0, zero_mul]
  have key : ∑ χ : irrChars k G, (χ : G → k) g * (χ : G → k) h⁻¹ =
      (Nat.card G : k) / Nat.card {x // IsConj x h} * δ g := by
    show _ = _ * (if IsConj g h then 1 else 0)
    rw [hexp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    field_simp
  rw [key]
  by_cases hgh : IsConj g h
  · simp only [δ, if_pos hgh, mul_one]
    have hN' := card_isConj_mul_card_centralizer g
    have hNeq : Nat.card {x // IsConj x g} = Nat.card {x // IsConj x h} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ ⟨fun H ↦ H.trans hgh, fun H ↦ H.trans hgh.symm⟩)
    rw [div_eq_iff hNk, ← hNeq, ← Nat.cast_mul, Nat.mul_comm, hN']
  · rw [if_neg hgh]
    simp only [δ, if_neg hgh, mul_zero]

/-- **Etingof et al., Theorem 3.1(ii)** (sum of squares): the squares of the values at `1` of the irreducible
characters, that is the squares of the dimensions of the irreducible representations, add up to the order of `G`
(as elements of `k`). -/
@[kb "etingof2011" "Theorem 3.1, p. 33"]
theorem sum_irrChars_one_sq : ∑ χ : irrChars k G, (χ : G → k) 1 ^ 2 = Nat.card G := by
  classical
  have h := sum_irrChars_mul_inv (k := k) (1 : G) 1
  have hc : Subgroup.centralizer {(1 : G)} = ⊤ := by
    ext x; simp [Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_one, IsConj.refl, if_true, hc, Subgroup.card_top] at h
  simpa [sq] using h

/-- **Etingof et al., Theorem 3.1(ii)** in characteristic zero: for a complete family of pairwise non-isomorphic
irreducible representations, the squares of the dimensions add up to the order of `G`. -/
@[kb "etingof2011" "Theorem 3.1, p. 33"]
theorem sum_finrank_sq [CharZero k] {ι : Type*} [Fintype ι] (X : ι → IrrRep k G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep k G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    ∑ i, finrank k (X i).V ^ 2 = Nat.card G := by
  have hbij : Function.Bijective (fun i ↦ (⟨(X i).ρ.character, X i, rfl⟩ : irrChars k G)) := by
    refine ⟨fun i j h ↦ hinj i j ((nonempty_equiv_iff_character_eq _ _).mpr ?_), fun χ ↦ ?_⟩
    · exact congrArg Subtype.val h
    · obtain ⟨Y, hY⟩ := χ.2
      obtain ⟨i, hi⟩ := hsurj Y
      exact ⟨i, Subtype.ext (((nonempty_equiv_iff_character_eq _ _).mp hi).symm.trans hY)⟩
  have h := sum_irrChars_one_sq (k := k) (G := G)
  rw [← Fintype.sum_bijective _ hbij (fun i ↦ ((X i).ρ.character 1) ^ 2) _ (fun _ ↦ rfl)] at h
  simp only [char_one] at h
  exact_mod_cast h

end Main

end UndergradKB.RepresentationTheory
