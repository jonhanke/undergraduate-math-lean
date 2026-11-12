import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.DoubleCentralizer
import UndergradKB.RepresentationTheory.IsotypicDecomposition
import UndergradKB.RepresentationTheory.SpechtModules

/-! # Schur-Weyl duality (Etingof et al., 4.57 to 4.59)

* `span_tensorPowerMap_units_eq_centralizer`: over a field of characteristic zero the span of the operators
  `g ⊗ ⋯ ⊗ g` with `g` invertible is the whole commutant of the symmetric group (Proposition 4.58).
* `schurWeyl_duality`: the images of `ℂ[S_n]` and `U(gl V)` in `End(V^{⊗n})` are mutual centralizers and both
  semisimple (Theorem 4.57).
* `schurWeylDecomposition`: `V^{⊗n} ≅ ⨁_λ V_λ ⊗ Hom_{S_n}(V_λ, V^{⊗n})` over the Specht modules
  (Theorem 4.57), equivariant for `g ⊗ ⋯ ⊗ g` (`schurWeylDecomposition_equivariant`), with each multiplicity
  space zero or an irreducible `GL(V)`-representation (`swRep_subsingleton_or_isIrreducible`, Corollary 4.59).
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open PiTensorProduct
open scoped TensorProduct

section Prop458

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {n : ℕ}

/-- Expansion of `(g + t)^{⊗ n}` over the subsets of tensor factors that carry `g`. -/
theorem tensorPowerMap_add_smul_id (g : V →ₗ[k] V) (t : k) :
    tensorPowerMap n (g + t • (LinearMap.id : V →ₗ[k] V)) =
      ∑ s : Finset (Fin n), (∏ i : Fin n, if i ∈ s then (1 : k) else t) •
        PiTensorProduct.map (fun l : Fin n => if l ∈ s then g else (LinearMap.id : V →ₗ[k] V)) := by
  classical
  have h := (PiTensorProduct.mapMultilinear k (fun _ : Fin n => V) (fun _ : Fin n => V)).map_add_univ
    (fun _ => g) (fun _ => t • (LinearMap.id : V →ₗ[k] V))
  refine h.trans (Finset.sum_congr rfl fun s _ => ?_)
  have e : s.piecewise (fun _ : Fin n => g) (fun _ => t • (LinearMap.id : V →ₗ[k] V))
      = fun l => (if l ∈ s then (1 : k) else t) • (if l ∈ s then g else (LinearMap.id : V →ₗ[k] V)) := by
    funext l
    by_cases hl : l ∈ s <;> simp [Finset.piecewise, hl]
  rw [e, MultilinearMap.map_smul_univ]
  rfl

theorem isUnit_add_smul_id [FiniteDimensional k V] (g : V →ₗ[k] V) (t : k) (h : -t ∉ spectrum k g) :
    IsUnit (g + t • (LinearMap.id : V →ₗ[k] V)) := by
  have h1 := spectrum.notMem_iff.mp h
  have h2 := h1.neg
  convert h2 using 1
  simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]

/-- **Proposition 4.58 (span form).** In characteristic zero, for `V` finite-dimensional, the commutant of the
symmetric group in `End(V^{⊗n})` is spanned by the operators `g ⊗ ⋯ ⊗ g` with `g` invertible, i.e. by the
image of `GL(V)`. -/
@[kb "etingof2011" "Proposition 4.58, p. 65"]
theorem span_tensorPowerMap_units_eq_centralizer [CharZero k] [FiniteDimensional k V] :
    Submodule.span k (Set.range fun u : (V →ₗ[k] V)ˣ => tensorPowerMap n (u : V →ₗ[k] V))
      = (Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))).toSubmodule := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, rfl⟩
    refine (Subalgebra.mem_centralizer_iff (R := k)).mpr ?_
    rintro _ ⟨σ, rfl⟩
    refine LinearMap.ext fun x => ?_
    exact (tensorPowerMap_perm (u : V →ₗ[k] V) σ x).symm
  · rw [centralizer_perm_eq_span_tensorPowerMap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    show tensorPowerMap n g ∈ Submodule.span k
      (Set.range fun u : (V →ₗ[k] V)ˣ => tensorPowerMap n (u : V →ₗ[k] V))
    by_contra hx
    obtain ⟨φ, hφ, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    -- the polynomial in `t` computing `φ ((g + t)^{⊗ n})`
    let m : Finset (Fin n) → Module.End k (⨂[k] _ : Fin n, V) := fun s =>
      PiTensorProduct.map (fun l : Fin n => if l ∈ s then g else (LinearMap.id : V →ₗ[k] V))
    let Q : Polynomial k := ∑ s : Finset (Fin n),
      (∏ i : Fin n, if i ∈ s then (1 : Polynomial k) else Polynomial.X) * Polynomial.C (φ (m s))
    have hQ : ∀ t : k, Q.eval t = φ (tensorPowerMap n (g + t • (LinearMap.id : V →ₗ[k] V))) := by
      intro t
      rw [tensorPowerMap_add_smul_id, map_sum]
      simp only [Q, Polynomial.eval_finsetSum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_C]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ s <;> simp [hi]
    have hroots : Set.Infinite {t : k | Q.IsRoot t} := by
      have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
      have hfin : Set.Finite {t : k | -t ∈ spectrum k g} := by
        have := (Module.End.finite_spectrum g).preimage (f := fun t : k => -t) neg_injective.injOn
        exact this
      refine ((Set.infinite_univ (α := k)).sdiff hfin).mono ?_
      intro t ht
      have hu := isUnit_add_smul_id g t (by simpa using ht.2)
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hQ]
      obtain ⟨u, hu'⟩ := hu
      have hmem : tensorPowerMap n (g + t • (LinearMap.id : V →ₗ[k] V)) ∈
          Submodule.span k (Set.range fun u : (V →ₗ[k] V)ˣ => tensorPowerMap n (u : V →ₗ[k] V)) := by
        rw [← hu']
        exact Submodule.subset_span ⟨u, rfl⟩
      have h0 : φ (tensorPowerMap n (g + t • (LinearMap.id : V →ₗ[k] V))) ∈ (Submodule.span k
          (Set.range fun u : (V →ₗ[k] V)ˣ => tensorPowerMap n (u : V →ₗ[k] V))).map φ := ⟨_, hmem, rfl⟩
      rw [hW] at h0
      simpa using h0
    have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q hroots
    have h00 := hQ 0
    rw [hQ0] at h00
    simp only [Polynomial.eval_zero, zero_smul, add_zero, tensorPowerMap] at h00
    exact hφ h00.symm

end Prop458

section Duality

instance instFiniteDimensionalTensorPower {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (n : ℕ) : FiniteDimensional k (⨂[k] _ : Fin n, V) :=
  Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin n => Module.finBasis k V))

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)

instance instNeZeroNatCardPermFin : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
  ⟨by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero⟩

variable (V) in
/-- The image of the group algebra `ℂ[S_n]` in `End(V^{⊗n})`. -/
noncomputable def swImage : Subalgebra ℂ (Module.End ℂ (⨂[ℂ] _ : Fin n, V)) :=
  (tensorPowerPermRep ℂ n V).asAlgebraHom.range

theorem centralizer_swImage :
    Subalgebra.centralizer ℂ (swImage V n : Set (Module.End ℂ (⨂[ℂ] _ : Fin n, V)))
      = Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V)) := by
  apply le_antisymm
  · refine Subalgebra.centralizer_le _ _ _ ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨MonoidAlgebra.of ℂ _ σ, Representation.asAlgebraHom_of _ σ⟩
  · intro b hb
    have hb' := (Subalgebra.mem_centralizer_iff (R := ℂ)).mp hb
    refine (Subalgebra.mem_centralizer_iff (R := ℂ)).mpr ?_
    have key : ∀ r : MonoidAlgebra ℂ (Equiv.Perm (Fin n)),
        (tensorPowerPermRep ℂ n V).asAlgebraHom r * b = b * (tensorPowerPermRep ℂ n V).asAlgebraHom r := by
      intro r
      induction r using MonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
      | single σ c =>
        rw [Representation.asAlgebraHom_single, smul_mul_assoc, mul_smul_comm, hb' _ ⟨σ, rfl⟩]
    rintro _ ⟨r, rfl⟩
    exact key r

instance : IsSemisimpleRing (swImage V n) :=
  RingHom.isSemisimpleRing_of_surjective
    (((tensorPowerPermRep ℂ n V).asAlgebraHom.rangeRestrict).toRingHom)
    (AlgHom.rangeRestrict_surjective _)

/-- **Theorem 4.57 (Schur-Weyl duality, centralizer part).** For finite-dimensional `V` over `ℂ`, the image of
`ℂ[S_n]` and the image of `U(gl V)` (the algebra generated by the diagonal operators `Δ_n(b)`) in
`End(V^{⊗n})` are each other's centralizers, and both are semisimple. -/
@[kb "etingof2011" "Theorem 4.57, p. 65"]
theorem schurWeyl_duality :
    Subalgebra.centralizer ℂ (swImage V n : Set (Module.End ℂ (⨂[ℂ] _ : Fin n, V)))
        = Algebra.adjoin ℂ (Set.range (diagAction (k := ℂ) (V := V) n)) ∧
      Subalgebra.centralizer ℂ
        (Algebra.adjoin ℂ (Set.range (diagAction (k := ℂ) (V := V) n)) :
          Set (Module.End ℂ (⨂[ℂ] _ : Fin n, V))) = swImage V n ∧
      IsSemisimpleRing (swImage V n) ∧
      IsSemisimpleRing (Algebra.adjoin ℂ (Set.range (diagAction (k := ℂ) (V := V) n))) := by
  have h1 : Subalgebra.centralizer ℂ (swImage V n : Set (Module.End ℂ (⨂[ℂ] _ : Fin n, V)))
      = Algebra.adjoin ℂ (Set.range (diagAction (k := ℂ) (V := V) n)) := by
    rw [centralizer_swImage, centralizer_perm_eq_adjoin_diagAction]
  refine ⟨h1, ?_, inferInstance, ?_⟩
  · rw [← h1]
    exact centralizer_centralizer_eq (swImage V n)
  · rw [← h1]
    exact isSemisimpleRing_commutant (swImage V n)

end Duality

section SpechtCovering

/-- Auxiliary: a representation isomorphism commuting with the algebra action is a module map. -/
noncomputable def linearMapOfRepEquivAux {G : Type*} [Group G] {M N : Type*} [AddCommGroup M]
    [Module (MonoidAlgebra ℂ G) M] [AddCommGroup N] [Module (MonoidAlgebra ℂ G) N]
    (e : Representation.Equiv (Representation.ofModule (k := ℂ) (G := G) M)
      (Representation.ofModule (k := ℂ) (G := G) N))
    (key : ∀ (a : MonoidAlgebra ℂ G) (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) M),
      e ((Representation.ofModule (k := ℂ) (G := G) M).asAlgebraHom a v) =
        (Representation.ofModule (k := ℂ) (G := G) N).asAlgebraHom a (e v)) :
    M →ₗ[MonoidAlgebra ℂ G] N where
  toFun := fun s => (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) N)
    (e ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) M).symm s))
  map_add' := fun x y => by simp
  map_smul' := fun a s => by
    have h1 := key a ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) M).symm s)
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at h1
    simp only [AddEquiv.apply_symm_apply] at h1
    have h2 := congrArg (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) N) h1
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at h2
    simp only [AddEquiv.apply_symm_apply] at h2
    simp only [RingHom.id_apply]
    exact h2

/-- A representation isomorphism between the representations attached to two `ℂ[G]`-modules is a module
isomorphism. -/
noncomputable def linearEquivOfRepEquiv' {G : Type*} [Group G] {M N : Type*} [AddCommGroup M]
    [Module (MonoidAlgebra ℂ G) M] [AddCommGroup N] [Module (MonoidAlgebra ℂ G) N]
    (e : Representation.Equiv (Representation.ofModule (k := ℂ) (G := G) M)
      (Representation.ofModule (k := ℂ) (G := G) N)) :
    M ≃ₗ[MonoidAlgebra ℂ G] N := by
  have key : ∀ (a : MonoidAlgebra ℂ G) (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) M),
      e ((Representation.ofModule (k := ℂ) (G := G) M).asAlgebraHom a v) =
        (Representation.ofModule (k := ℂ) (G := G) N).asAlgebraHom a (e v) := by
    intro a v
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | single g r =>
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      simp only [LinearMap.smul_apply, map_smul]
      exact congrArg _ (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)
  have key' : ∀ (a : MonoidAlgebra ℂ G) (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) N),
      e.symm ((Representation.ofModule (k := ℂ) (G := G) N).asAlgebraHom a v) =
        (Representation.ofModule (k := ℂ) (G := G) M).asAlgebraHom a (e.symm v) := by
    intro a v
    have h := congrArg e.symm (key a (e.symm v))
    simp at h
    simpa using h.symm
  exact LinearEquiv.ofLinearMap
    (linearMapOfRepEquivAux e key) (linearMapOfRepEquivAux e.symm key') (by ext s; simp [linearMapOfRepEquivAux])
    (by ext s; simp [linearMapOfRepEquivAux])

/-- Every finite-dimensional simple module over `ℂ[S_n]` is isomorphic to a Specht module `V_λ`. -/
theorem exists_linearEquiv_spechtModule (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M]
    [IsScalarTower ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M] [FiniteDimensional ℂ M]
    [hM : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M] :
    ∃ la : DiagramsOfSize n, Nonempty (M ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] spechtModule la) := by
  let f : RestrictScalars ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M →ₗ[ℂ] M :=
    { toFun := fun x ↦ RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M x
      map_add' := by simp
      map_smul' := fun c x ↦ by
        simp only [RestrictScalars.addEquiv_map_smul, RingHom.id_apply]
        exact algebraMap_smul (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) c _ }
  have hfin : Module.Finite ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M) :=
    Module.Finite.of_injective f fun x y h ↦
      (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M).injective h
  have hirr := (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ)
    (G := Equiv.Perm (Fin n)) M).mp hM
  let Y : IrrRep ℂ (Equiv.Perm (Fin n)) :=
    @IrrRep.mk ℂ (Equiv.Perm (Fin n)) _ _ (RestrictScalars ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M) _
      (RestrictScalars.module ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) M) hfin
      (Representation.ofModule M) hirr
  obtain ⟨la, ⟨e⟩⟩ := exists_equiv_spechtModule n Y
  exact ⟨la, ⟨linearEquivOfRepEquiv' e⟩⟩

end SpechtCovering

section Decomposition

noncomputable instance instFintypeDiagramsOfSize (n : ℕ) : Fintype (DiagramsOfSize n) :=
  Fintype.ofEquiv _ YoungDiagram.equivPartition.symm

instance instIsSimpleModuleSpechtModule (n : ℕ) (la : DiagramsOfSize n) :
    IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (spechtModule la) :=
  isSimpleModule_span_youngSymmetrizerN (spechtTableau la)

instance instFiniteDimensionalSpechtModule (n : ℕ) (la : DiagramsOfSize n) :
    FiniteDimensional ℂ (spechtModule la) :=
  Module.Finite.of_injective ((spechtModule la).subtype.restrictScalars ℂ) Subtype.val_injective

variable (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- `V^{⊗n}` as a module over the group algebra `ℂ[S_n]`. -/
abbrev tensorPowerModule (n : ℕ) : Type := (tensorPowerPermRep ℂ n V).asModule

variable {V} (n : ℕ)

theorem spechtModule_nonIso (i j : DiagramsOfSize n) (hij : i ≠ j) :
    IsEmpty (spechtModule i ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] spechtModule j) :=
  isEmpty_linearEquiv_span_youngSymmetrizerN (spechtTableau i) (spechtTableau j)
    (fun h => hij (Subtype.ext h))

theorem spechtModule_cover (S : Submodule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (tensorPowerModule V n))
    (hS : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) S) :
    ∃ la : DiagramsOfSize n,
      Nonempty (spechtModule la ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] S) := by
  have : FiniteDimensional ℂ S :=
    Module.Finite.of_injective (S.subtype.restrictScalars ℂ) Subtype.val_injective
  obtain ⟨la, ⟨e⟩⟩ := exists_linearEquiv_spechtModule n S
  exact ⟨la, ⟨e.symm⟩⟩

/-- **Schur-Weyl decomposition.** `V^{⊗n} ≅ ⨁_λ V_λ ⊗ Hom_{S_n}(V_λ, V^{⊗n})` as `ℂ[S_n]`-modules, the sum
running over the diagrams `λ` with `n` boxes (equivalently the partitions of `n`) and `V_λ` the Specht
module. -/
@[kb "etingof2011" "Theorem 4.57, p. 65"]
noncomputable def schurWeylDecomposition :
    (Π la : DiagramsOfSize n, spechtModule la ⊗[ℂ]
      (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n))
      ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n :=
  isotypicDecomposition ℂ (fun la : DiagramsOfSize n => (spechtModule la : Type))
    (spechtModule_nonIso n) (spechtModule_cover n)

theorem tensorPowerMap_asAlgebraHom (g : V →ₗ[ℂ] V) (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)))
    (x : ⨂[ℂ] _ : Fin n, V) :
    tensorPowerMap n g ((tensorPowerPermRep ℂ n V).asAlgebraHom a x)
      = (tensorPowerPermRep ℂ n V).asAlgebraHom a (tensorPowerMap n g x) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single σ c => simp [Representation.asAlgebraHom_single, tensorPowerMap_perm]

theorem tensorPowerMap_one_apply (y : ⨂[ℂ] _ : Fin n, V) :
    tensorPowerMap n (1 : V →ₗ[ℂ] V) y = y := by
  rw [Module.End.one_eq_id, tensorPowerMap_id]
  rfl

theorem tensorPowerMap_mul_apply (g h : V →ₗ[ℂ] V) (y : ⨂[ℂ] _ : Fin n, V) :
    tensorPowerMap n (g * h) y = tensorPowerMap n g (tensorPowerMap n h y) := by
  rw [Module.End.mul_eq_comp, tensorPowerMap_comp]
  rfl

/-- The operator `g ⊗ ⋯ ⊗ g` as a `ℂ[S_n]`-linear endomorphism of `V^{⊗n}`. -/
noncomputable def tensorPowerEnd (g : V →ₗ[ℂ] V) :
    Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (tensorPowerModule V n) where
  toFun x := tensorPowerMap n g x
  map_add' x y := map_add (tensorPowerMap n g) x y
  map_smul' a x := tensorPowerMap_asAlgebraHom n g a x

theorem tensorPowerEnd_apply (g : V →ₗ[ℂ] V) (x : tensorPowerModule V n) :
    tensorPowerEnd n g x = tensorPowerMap n g x := rfl

/-- Post-composition with `g ⊗ ⋯ ⊗ g` on `Hom_{S_n}(V_λ, V^{⊗n})`. -/
noncomputable def swPost (la : DiagramsOfSize n) (g : V →ₗ[ℂ] V) :
    (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n) →ₗ[ℂ]
      (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n) where
  toFun f := tensorPowerEnd n g ∘ₗ f
  map_add' f f' := LinearMap.comp_add _ _ _
  map_smul' c f := by
    ext x
    simp

/-- The action of `GL(V)` on `Hom_{S_n}(V_λ, V^{⊗n})` by post-composition with `g ⊗ ⋯ ⊗ g`. -/
noncomputable def swRep (la : DiagramsOfSize n) :
    Representation ℂ (V →ₗ[ℂ] V)ˣ
      (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n) where
  toFun u := swPost n la (u : V →ₗ[ℂ] V)
  map_one' := by
    ext f x
    exact tensorPowerMap_one_apply n _
  map_mul' u v := by
    ext f x
    exact tensorPowerMap_mul_apply n _ _ _

theorem swRep_apply (la : DiagramsOfSize n) (u : (V →ₗ[ℂ] V)ˣ) (f) :
    swRep n la u f = tensorPowerEnd n (u : V →ₗ[ℂ] V) ∘ₗ f := rfl

theorem tensorPowerEnd_evalHom (g : V →ₗ[ℂ] V) (la : DiagramsOfSize n)
    (w : spechtModule la ⊗[ℂ]
      (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)) :
    tensorPowerEnd n g (evalHom ℂ (spechtModule la) (tensorPowerModule V n) w)
      = evalHom ℂ (spechtModule la) (tensorPowerModule V n)
        (TensorProduct.map LinearMap.id (swPost n la g) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul x f => simp [evalHom_tmul, swPost]
  | add w w' hw hw' => simp only [map_add, hw, hw']

/-- The Schur-Weyl decomposition intertwines `g ⊗ ⋯ ⊗ g` on `V^{⊗n}` with the action of `g` by
post-composition on the multiplicity spaces `Hom_{S_n}(V_λ, V^{⊗n})`. -/
@[kb "etingof2011" "Corollary 4.59, p. 65"]
theorem schurWeylDecomposition_equivariant (g : V →ₗ[ℂ] V)
    (z : Π la : DiagramsOfSize n, spechtModule la ⊗[ℂ]
      (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)) :
    tensorPowerEnd n g (schurWeylDecomposition n z)
      = schurWeylDecomposition n (fun la => TensorProduct.map LinearMap.id (swPost n la g) (z la)) := by
  change tensorPowerEnd n g (isotypicEval ℂ _ z) = isotypicEval ℂ _ _
  rw [isotypicEval_apply, isotypicEval_apply, map_sum]
  exact Finset.sum_congr rfl fun la _ => tensorPowerEnd_evalHom n g la (z la)

theorem centralizer_apply_asAlgebraHom {b : Module.End ℂ (⨂[ℂ] _ : Fin n, V)}
    (hb : b ∈ Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V)))
    (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (x : ⨂[ℂ] _ : Fin n, V) :
    b ((tensorPowerPermRep ℂ n V).asAlgebraHom a x)
      = (tensorPowerPermRep ℂ n V).asAlgebraHom a (b x) := by
  have hb' := (Subalgebra.mem_centralizer_iff (R := ℂ)).mp hb
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => simp [hy, hz]
  | single σ c =>
    have h := congr($(hb' _ ⟨σ, rfl⟩) x)
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, hb' _ ⟨σ, rfl⟩]

/-- An element of the commutant of the symmetric group is a `ℂ[S_n]`-linear endomorphism of `V^{⊗n}`. -/
noncomputable def centralizerEnd (b : Module.End ℂ (⨂[ℂ] _ : Fin n, V))
    (hb : b ∈ Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V))) :
    Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (tensorPowerModule V n) where
  toFun x := b x
  map_add' x y := map_add b x y
  map_smul' a x := centralizer_apply_asAlgebraHom n hb a x

/-- Every `ℂ[S_n]`-linear endomorphism of `V^{⊗n}` is in the commutant of the symmetric group. -/
theorem exists_centralizer_eq
    (h : Module.End (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (tensorPowerModule V n)) :
    ∃ (b : Module.End ℂ (⨂[ℂ] _ : Fin n, V))
      (hb : b ∈ Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V))),
      centralizerEnd n b hb = h := by
  let b : Module.End ℂ (⨂[ℂ] _ : Fin n, V) := h.restrictScalars ℂ
  have hb : b ∈ Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V)) := by
    refine (Subalgebra.mem_centralizer_iff (R := ℂ)).mpr ?_
    rintro _ ⟨σ, rfl⟩
    refine LinearMap.ext fun x => ?_
    have := h.map_smul (MonoidAlgebra.of ℂ _ σ) x
    change h ((tensorPowerPermRep ℂ n V).asAlgebraHom (MonoidAlgebra.of ℂ _ σ) x) =
      (tensorPowerPermRep ℂ n V).asAlgebraHom (MonoidAlgebra.of ℂ _ σ) (h x) at this
    rw [Representation.asAlgebraHom_of] at this
    exact this.symm
  exact ⟨b, hb, rfl⟩

/-- A subrepresentation of `Hom_{S_n}(V_λ, V^{⊗n})` under `GL(V)` is stable under post-composition with
every element of the commutant of `S_n` (by Proposition 4.58). -/
theorem comp_mem_of_subrepresentation (la : DiagramsOfSize n) (σ : Subrepresentation (swRep (V := V) n la))
    (b : Module.End ℂ (⨂[ℂ] _ : Fin n, V))
    (hb : b ∈ Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V)))
    (f : spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n) (hf : f ∈ σ) :
    centralizerEnd n b hb ∘ₗ f ∈ σ := by
  have hb' : b ∈ Submodule.span ℂ
      (Set.range fun u : (V →ₗ[ℂ] V)ˣ => tensorPowerMap n (u : V →ₗ[ℂ] V)) := by
    rw [span_tensorPowerMap_units_eq_centralizer]
    exact hb
  have key : ∀ b ∈ Submodule.span ℂ
      (Set.range fun u : (V →ₗ[ℂ] V)ˣ => tensorPowerMap n (u : V →ₗ[ℂ] V)),
      ∃ hb : b ∈ Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V)),
        centralizerEnd n b hb ∘ₗ f ∈ σ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨u, rfl⟩ := hb
      have hmem : tensorPowerMap n (u : V →ₗ[ℂ] V) ∈
          Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n V)) := by
        rw [← Subalgebra.mem_toSubmodule, ← span_tensorPowerMap_units_eq_centralizer]
        exact Submodule.subset_span ⟨u, rfl⟩
      exact ⟨hmem, σ.apply_mem_toSubmodule u hf⟩
    | zero =>
      refine ⟨Subalgebra.zero_mem _, ?_⟩
      have : centralizerEnd n 0 (Subalgebra.zero_mem _) ∘ₗ f = 0 := by
        ext x
        rfl
      rw [this]
      exact σ.toSubmodule.zero_mem
    | add b c hb hc ihb ihc =>
      obtain ⟨hb1, h1⟩ := ihb
      obtain ⟨hc1, h2⟩ := ihc
      refine ⟨Subalgebra.add_mem _ hb1 hc1, ?_⟩
      have : centralizerEnd n (b + c) (Subalgebra.add_mem _ hb1 hc1) ∘ₗ f
          = centralizerEnd n b hb1 ∘ₗ f + centralizerEnd n c hc1 ∘ₗ f := by
        ext x
        rfl
      rw [this]
      exact σ.toSubmodule.add_mem h1 h2
    | smul c b hb ihb =>
      obtain ⟨hb1, h1⟩ := ihb
      refine ⟨Subalgebra.smul_mem _ hb1 c, ?_⟩
      have : centralizerEnd n (c • b) (Subalgebra.smul_mem _ hb1 c) ∘ₗ f
          = c • (centralizerEnd n b hb1 ∘ₗ f) := by
        ext x
        rfl
      rw [this]
      exact σ.toSubmodule.smul_mem c h1
  obtain ⟨hb2, h⟩ := key b hb'
  exact h

/-- **Irreducibility of the multiplicity spaces.**  If `Hom_{S_n}(V_λ, V^{⊗n})` is nonzero, it is an
irreducible representation of `GL(V)` under post-composition with `g ⊗ ⋯ ⊗ g`. -/
@[kb "etingof2011" "Corollary 4.59, p. 65"]
theorem swRep_isIrreducible (la : DiagramsOfSize n)
    [Nontrivial (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)] :
    Representation.IsIrreducible (k := ℂ) (V := spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n) (swRep n la) := by
  have hnt : Nontrivial (Subrepresentation (swRep (V := V) n la)) := by
    obtain ⟨f, hf⟩ := exists_ne
      (0 : spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)
    refine ⟨⊥, ⊤, fun h => hf ?_⟩
    have h1 : f ∈ (⊤ : Subrepresentation (swRep (V := V) n la)) := trivial
    rw [← h] at h1
    exact h1
  refine { eq_bot_or_eq_top := fun σ => ?_ }
  by_cases h0 : ∀ f ∈ σ, f = 0
  · left
    refine SetLike.ext fun f => ⟨fun hf => ?_, fun hf => ?_⟩
    · exact h0 f hf
    · have : f = 0 := hf
      rw [this]
      exact σ.toSubmodule.zero_mem
  · right
    push Not at h0
    obtain ⟨f, hfσ, hf0⟩ := h0
    refine SetLike.ext fun f' => ⟨fun _ => trivial, fun _ => ?_⟩
    have hinj : Function.Injective f := LinearMap.injective_of_ne_zero hf0
    obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property f hinj f'
    obtain ⟨b, hb, rfl⟩ := exists_centralizer_eq n h
    rw [← hh]
    exact comp_mem_of_subrepresentation n la σ b hb f hfσ

/-- **Corollary 4.59 (dichotomy).** Each multiplicity space `L_λ = Hom_{S_n}(V_λ, V^{⊗n})` is either zero or an
irreducible representation of `GL(V)`. -/
@[kb "etingof2011" "Corollary 4.59, p. 65"]
theorem swRep_subsingleton_or_isIrreducible (la : DiagramsOfSize n) :
    Subsingleton (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n) ∨
      Representation.IsIrreducible (k := ℂ)
        (V := spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)
        (swRep n la) := by
  by_cases h : Nontrivial
      (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule V n)
  · exact Or.inr (swRep_isIrreducible n la)
  · exact Or.inl (not_nontrivial_iff_subsingleton.mp h)

end Decomposition

end UndergradKB.RepresentationTheory
