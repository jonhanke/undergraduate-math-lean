import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Character
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import UndergradKB.RepresentationTheory.KostkaNumbers
import UndergradKB.RepresentationTheory.FrobeniusDefs
import UndergradKB.RepresentationTheory.SpechtModules
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.ComplexCharacters
import UndergradKB.Common.Attr

/-! # Kostka numbers as pairings of characters (a step of Etingof et al., Theorem 4.47)

* `finrank_hom_eq_finrank_intertwining`: for left ideals `S, S'` of `ℂ[G]`, `Hom_{ℂ[G]}(S, S')` has the same
  dimension as the space of intertwining maps between `ofModule S` and `ofModule S'`.
* `pairing_coeffChar_spechtChar`: the pairing of the function `g ↦ [x^μ] ∏_m (x_1^m + ⋯ + x_N^m)^{i_m(g)}`
  with the character of the Specht module `V_λ` is the Kostka number `K_{λμ}`.
* `exists_diagram_of_antitone`: an antitone `N`-tuple with sum `n` is the row length vector of a diagram.
-/

namespace UndergradKB.RepresentationTheory

open Representation

section Bridge

variable {G : Type*} [Group G] (S S' : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))

/-- The `ℂ`-module structure on the representation space of a left ideal, stated over the additive group
structure so that character-theoretic statements about `ofModule` elaborate. -/
noncomputable instance restrictModuleGrp (S : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)) :
    @Module ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) S) _
      (AddCommGroup.toAddCommMonoid (G := RestrictScalars ℂ (MonoidAlgebra ℂ G) S)) :=
  RestrictScalars.module ℂ (MonoidAlgebra ℂ G) S

/-- The `ℂ`-linear map between the representation spaces underlying a `ℂ[G]`-linear map of left ideals. -/
noncomputable def restrictHom (f : S →ₗ[MonoidAlgebra ℂ G] S') :
    RestrictScalars ℂ (MonoidAlgebra ℂ G) S →ₗ[ℂ] RestrictScalars ℂ (MonoidAlgebra ℂ G) S' where
  toFun x := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S').symm
    (f (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S x))
  map_add' x y := by simp
  map_smul' c x := by
    apply (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S').injective
    simp [RestrictScalars.addEquiv_map_smul]

lemma restrictHom_asAlgebraHom (f : S →ₗ[MonoidAlgebra ℂ G] S') (a : MonoidAlgebra ℂ G)
    (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) S) :
    restrictHom S S' f ((ofModule (k := ℂ) (G := G) S).asAlgebraHom a v) =
      (ofModule (k := ℂ) (G := G) S').asAlgebraHom a (restrictHom S S' f v) := by
  rw [ofModule_asAlgebraHom_apply_apply, ofModule_asAlgebraHom_apply_apply]
  simp [restrictHom]

/-- A `ℂ[G]`-linear map of left ideals gives an intertwining map of the associated representations. -/
noncomputable def homToIntertwining (f : S →ₗ[MonoidAlgebra ℂ G] S') :
    IntertwiningMap (ofModule (k := ℂ) (G := G) S) (ofModule (k := ℂ) (G := G) S') :=
  (restrictHom S S' f).intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
    have := restrictHom_asAlgebraHom S S' f (MonoidAlgebra.single g 1) v
    simpa [asAlgebraHom_single_one] using this)

lemma intertwining_asAlgebraHom
    (φ : IntertwiningMap (ofModule (k := ℂ) (G := G) S) (ofModule (k := ℂ) (G := G) S'))
    (a : MonoidAlgebra ℂ G) (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) S) :
    φ ((ofModule (k := ℂ) (G := G) S).asAlgebraHom a v) =
      (ofModule (k := ℂ) (G := G) S').asAlgebraHom a (φ v) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | single g r =>
    rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg _ (IntertwiningMap.isIntertwining _ _ φ g v)

/-- The `ℂ[G]`-linear map attached to an intertwining map. -/
noncomputable def intertwiningToHom
    (φ : IntertwiningMap (ofModule (k := ℂ) (G := G) S) (ofModule (k := ℂ) (G := G) S')) :
    S →ₗ[MonoidAlgebra ℂ G] S' where
  toFun x := RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S'
    (φ ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm x))
  map_add' x y := by simp
  map_smul' a x := by
    have h1 := intertwining_asAlgebraHom S S' φ a ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm x)
    rw [ofModule_asAlgebraHom_apply_apply, ofModule_asAlgebraHom_apply_apply] at h1
    simp only [AddEquiv.apply_symm_apply] at h1
    have h2 := congrArg (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S') h1
    simp only [AddEquiv.apply_symm_apply] at h2
    simpa using h2

/-- `Hom_{ℂ[G]}(S, S')` has the same dimension as the space of intertwining maps between the associated
representations. -/
lemma finrank_hom_eq_finrank_intertwining :
    Module.finrank ℂ (S →ₗ[MonoidAlgebra ℂ G] S') =
      Module.finrank ℂ (IntertwiningMap (ofModule (k := ℂ) (G := G) S) (ofModule (k := ℂ) (G := G) S')) := by
  let Ψ : (S →ₗ[MonoidAlgebra ℂ G] S') →ₗ[ℂ]
      IntertwiningMap (ofModule (k := ℂ) (G := G) S) (ofModule (k := ℂ) (G := G) S') :=
    { toFun := homToIntertwining S S'
      map_add' := fun f g => by
        refine IntertwiningMap.ext (LinearMap.ext fun x => ?_)
        simp [homToIntertwining, restrictHom]
      map_smul' := fun c f => by
        refine IntertwiningMap.ext (LinearMap.ext fun x => ?_)
        apply (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S').injective
        simp [homToIntertwining, restrictHom, RestrictScalars.addEquiv_map_smul]
        exact (algebraMap_smul (MonoidAlgebra ℂ G) c _).symm }
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective Ψ ⟨?_, ?_⟩)
  · intro f g h
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun φ => RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S'
      (φ ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm x))) h
    simpa [Ψ, homToIntertwining, restrictHom] using this
  · intro φ
    refine ⟨intertwiningToHom S S' φ, ?_⟩
    refine IntertwiningMap.ext (LinearMap.ext fun x => ?_)
    simp [Ψ, homToIntertwining, restrictHom, intertwiningToHom]

end Bridge

section Diagram

/-- Every antitone `N`-tuple of natural numbers with sum `n` is the list of the first `N` row lengths of a Young
diagram with `n` boxes and at most `N` rows. -/
theorem exists_diagram_of_antitone {n N : ℕ} (μ : Fin N → ℕ) (hμ : Antitone μ) (hsum : ∑ j, μ j = n) :
    ∃ mu : DiagramsOfSize n, mu.1.colLen 0 ≤ N ∧ ∀ j : Fin N, mu.1.rowLen j = μ j := by
  have hsorted : (List.ofFn μ).SortedGE := by
    intro i j hij
    have hij' : (⟨i.1, by simpa using i.2⟩ : Fin N) ≤ ⟨j.1, by simpa using j.2⟩ := hij
    simpa using hμ hij'
  set D : YoungDiagram := YoungDiagram.ofRowLens (List.ofFn μ) hsorted with hD
  have hrow : ∀ j : Fin N, D.rowLen j = μ j := by
    intro j
    have := YoungDiagram.rowLen_ofRowLens (w := List.ofFn μ) (hw := hsorted) (Fin.cast (by simp) j)
    simpa using this
  have hmem : ∀ c ∈ D.cells, c.1 < N := by
    intro c hc
    have := YoungDiagram.mem_ofRowLens.1 (show c ∈ D from hc)
    obtain ⟨h, _⟩ := this
    simpa using h
  have hcol : D.colLen 0 ≤ N := by
    by_contra hlt
    replace hlt := Nat.not_le.1 hlt
    have h1 : (N, 0) ∈ D := YoungDiagram.mem_iff_lt_colLen.2 hlt
    exact lt_irrefl _ (hmem _ h1)
  refine ⟨⟨D, ?_⟩, hcol, hrow⟩
  have hf : ∀ c ∈ D.cells, c.1 ∈ Finset.range N := fun c hc => Finset.mem_range.2 (hmem c hc)
  have hr : ∀ i ∈ Finset.range N, ({c ∈ D.cells | c.1 = i}).card = D.rowLen i := by
    intro i _hi
    rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise hf, Finset.sum_congr rfl hr]
  rw [← hsum, ← Fin.sum_univ_eq_sum_range (fun i => D.rowLen i) N]
  exact Finset.sum_congr rfl fun j _ => hrow j

end Diagram

section Perm

variable {n : ℕ} {la : YoungDiagram}

/-- The `ℂ`-linear identification of the representation space of the ideal `U_λ` with the subspace
`permSubspace (rowStab T)` of the group algebra. -/
noncomputable def permEquiv (T : la ≃ Fin n) :
    RestrictScalars ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (permIdeal T) ≃ₗ[ℂ]
      permSubspace (rowStab T) where
  toFun x := ⟨(RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (permIdeal T) x :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n))), (RestrictScalars.addEquiv ℂ _ (permIdeal T) x).2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp [RestrictScalars.addEquiv_map_smul]
    rw [Algebra.smul_def]
    rfl
  invFun y := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (permIdeal T)).symm
    ⟨y.1, y.2⟩
  left_inv x := by
    apply (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (permIdeal T)).injective
    simp
  right_inv y := by simp

lemma character_ofModule_permIdeal (T : la ≃ Fin n) (g : Equiv.Perm (Fin n)) :
    (ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (permIdeal T)).character g =
      LinearMap.trace ℂ (permSubspace (rowStab T)) (permAction (rowStab T) g) := by
  have h0 := LinearMap.trace_conj' ((ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (permIdeal T)) g)
    (permEquiv T)
  refine h0.symm.trans ?_
  congr 1

lemma pairing_comm_complex {G : Type*} [Group G] [Fintype G] (f h : G → ℂ) :
    pairing f h = pairing h f := by
  rw [pairing_apply, pairing_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [mul_comm])

instance finiteDimensional_restrict_permIdeal (T : la ≃ Fin n) :
    FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (permIdeal T)) := by
  have : Module.Finite ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :=
    Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  exact LinearEquiv.finiteDimensional (permEquiv T).symm

end Perm

/-- **Theorem 4.47 (a step of the proof).** The pairing of the character of the permutation module `U_μ`
(given by the coefficient of `x^μ` in `∏_m (x_1^m + ⋯ + x_N^m)^{i_m}`, by Theorem 4.46) with the character of the
Specht module `V_λ` is the Kostka number `K_{λμ} = dim Hom_{S_n}(U_μ, V_λ)`. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem pairing_coeffChar_spechtChar (n N : ℕ) (mu la : DiagramsOfSize n) (hN : mu.1.colLen 0 ≤ N) :
    pairing (fun g : Equiv.Perm (Fin n) =>
        (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm fun j : Fin N => mu.1.rowLen j))
      ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) =
        (kostka la mu : ℂ) := by
  have hinv : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have h1 : (fun g : Equiv.Perm (Fin n) =>
        (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm fun j : Fin N => mu.1.rowLen j)) =
      (ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (permIdeal (spechtTableau mu))).character := by
    funext g
    rw [character_ofModule_permIdeal, character_permIdeal_eq_coeff (spechtTableau mu) hN g]
    rfl
  rw [h1, pairing_comm_complex]
  show pairing (spechtIrrRep n la).ρ.character
    (ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (permIdeal (spechtTableau mu))).character = _
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (k := ℂ)
    (ρ := ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (permIdeal (spechtTableau mu)))
    (σ := (spechtIrrRep n la).ρ)
  have e := finrank_hom_eq_finrank_intertwining (permIdeal (spechtTableau mu)) (spechtModule la)
  rw [pairing_apply]
  refine key.trans ?_
  exact congrArg Nat.cast e.symm

end UndergradKB.RepresentationTheory
