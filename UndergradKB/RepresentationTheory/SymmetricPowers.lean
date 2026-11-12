import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.SchurFunctors
import UndergradKB.RepresentationTheory.DoubleCentralizer

/-! # Symmetric powers: dimension (Etingof et al., Problem 1.49(d))

Mathlib defines the symmetric tensor power `SymmetricPower k ι V` (the quotient of the tensor power by
permutations of the factors) but gives no universal property and no dimension count. Here:

* `symLift`: the universal property for descending linear maps from the tensor power.
* `symBasis`: from a basis of `V` indexed by `ι`, a basis of the `n`-th symmetric power indexed by
  multisets `Sym ι n` of size `n` (pure tensors of basis vectors, one per multiset). Linear independence
  is checked by mapping to the polynomial ring `k[x_i : i ∈ ι]`, where these become distinct monomials.
* `finrank_symmetricPower`: `dim S^n V = choose (dim V + n - 1, n)`.
-/

namespace UndergradKB.RepresentationTheory

open scoped TensorProduct
open PiTensorProduct

section Lift

variable {k : Type} [CommRing k] {ι : Type} {V : Type*} [AddCommGroup V] [Module k V]
  {N : Type*} [AddCommGroup N] [Module k N]

/-- Universal property of the symmetric power: a linear map on the tensor power that is invariant
under permuting the factors of pure tensors descends to the symmetric power. -/
noncomputable def symLift (F : (⨂[k] _ : ι, V) →ₗ[k] N)
    (h : ∀ (e : Equiv.Perm ι) (f : ι → V), F (tprod k fun i => f (e i)) = F (tprod k f)) :
    SymmetricPower k ι V →ₗ[k] N where
  toFun := AddCon.lift _ F.toAddMonoidHom (AddCon.addConGen_le.2 (by
    intro x y hxy
    cases hxy with
    | perm e f => exact (h e f).symm))
  map_add' x y := map_add _ x y
  map_smul' r x := by
    induction x using AddCon.induction_on with
    | H x => exact map_smul F r x

/-- The descended map agrees with the original on the image of the quotient map. -/
theorem symLift_mk (F : (⨂[k] _ : ι, V) →ₗ[k] N)
    (h : ∀ (e : Equiv.Perm ι) (f : ι → V), F (tprod k fun i => f (e i)) = F (tprod k f))
    (x : ⨂[k] _ : ι, V) : symLift F h (SymmetricPower.mk k ι V x) = F x := rfl

end Lift

section Combinatorics

/-- Two functions out of `Fin n` with the same multiset of values differ by a permutation of `Fin n`. -/
theorem exists_perm_of_map_eq {α : Type*} {n : ℕ} (s t : Fin n → α)
    (h : Multiset.map s Finset.univ.val = Multiset.map t Finset.univ.val) :
    ∃ e : Equiv.Perm (Fin n), s = t ∘ e := by
  classical
  have hc : ∀ c : α, Fintype.card {a // s a = c} = Fintype.card {b // t b = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using this
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map _ a).symm

variable {ι : Type} [DecidableEq ι] {n : ℕ}

/-- The multiset of values of a function `Fin n → ι`, as an element of `Sym ι n`. -/
def msetOf (s : Fin n → ι) : Sym ι n := ⟨Multiset.map s Finset.univ.val, by simp⟩

theorem sum_single_eq (s : Fin n → ι) :
    ∑ i, Finsupp.single (s i) 1 = Multiset.toFinsupp (msetOf s).1 := by
  ext c
  rw [Finset.sum_apply', Multiset.toFinsupp_apply]
  show _ = Multiset.count c (Multiset.map s Finset.univ.val)
  rw [Multiset.count_map]
  simp only [Finsupp.single_apply, Finset.sum_boole]
  rw [← Finset.filter_val, ← Finset.card_def]
  simp [eq_comm]

omit [DecidableEq ι] in
theorem exists_msetOf [DecidableEq ι] (m : Sym ι n) : ∃ s : Fin n → ι, msetOf s = m := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  have hl : l.length = n := by simpa using hm
  subst hl
  refine ⟨fun i => l.get i, ?_⟩
  apply Subtype.ext
  simp [msetOf, Fin.univ_val_map]

theorem prod_X_eq_monomial {k : Type} [CommRing k] (s : Fin n → ι) :
    ∏ i, (MvPolynomial.X (s i) : MvPolynomial ι k) =
      MvPolynomial.monomial (Multiset.toFinsupp (msetOf s).1) 1 := by
  rw [← sum_single_eq, MvPolynomial.monomial_sum_one]
  rfl

end Combinatorics

section Basis

variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
  [Module k V] (b : Module.Basis ι k V) (n : ℕ)

/-- The map from the `n`-th symmetric power of `V` to the polynomial ring on the basis `b`, sending
`v₁ ⋯ vₙ` to the product of the corresponding linear forms (each `bᵢ` goes to the variable `Xᵢ`). -/
noncomputable def symPolyMap : SymmetricPower k (Fin n) V →ₗ[k] MvPolynomial ι k :=
  symLift (PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra k (Fin n) (MvPolynomial ι k)).compLinearMap
      fun _ => b.constr k (MvPolynomial.X : ι → MvPolynomial ι k)))
    (by
      intro e f
      simp only [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply]
      exact Equiv.prod_comp e (fun i => b.constr k (MvPolynomial.X : ι → MvPolynomial ι k) (f i)))

omit [DecidableEq ι] in
theorem symPolyMap_tprod (g : Fin n → V) :
    symPolyMap b n (SymmetricPower.tprod k g) =
      ∏ i, b.constr k (MvPolynomial.X : ι → MvPolynomial ι k) (g i) := by
  change symPolyMap b n (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k g)) = _
  simp [symPolyMap, symLift_mk]

/-- The spanning family of the symmetric power: for each multiset of size `n` of indices, the pure
tensor of the corresponding basis vectors. -/
noncomputable def symFamily (m : Sym ι n) : SymmetricPower k (Fin n) V :=
  SymmetricPower.tprod k fun i => b ((exists_msetOf m).choose i)

omit [Fintype ι] in
theorem symFamily_msetOf (s : Fin n → ι) :
    symFamily b n (msetOf s) = SymmetricPower.tprod k fun i => b (s i) := by
  unfold symFamily
  have hr := (exists_msetOf (msetOf s)).choose_spec
  generalize (exists_msetOf (msetOf s)).choose = r at hr ⊢
  obtain ⟨e, he⟩ := exists_perm_of_map_eq r s (congrArg Subtype.val hr)
  subst he
  exact SymmetricPower.tprod_equiv (R := k) e (fun i => b (s i))

theorem symFamily_linearIndependent : LinearIndependent k (symFamily (k := k) b n) := by
  refine LinearIndependent.of_comp (symPolyMap b n) ?_
  have hcomp : (symPolyMap b n ∘ symFamily (k := k) b n) =
      (fun d => MvPolynomial.monomial d (1 : k)) ∘ (fun m : Sym ι n => Multiset.toFinsupp m.1) := by
    funext m
    obtain ⟨s, rfl⟩ := exists_msetOf m
    simp only [Function.comp_apply]
    rw [symFamily_msetOf, symPolyMap_tprod, ← prod_X_eq_monomial]
    simp
  rw [hcomp]
  have hinj : Function.Injective (fun m : Sym ι n => Multiset.toFinsupp m.1) :=
    fun m m' h => Subtype.ext (Multiset.toFinsupp.injective h)
  have := (MvPolynomial.basisMonomials ι k).linearIndependent.comp _ hinj
  rw [MvPolynomial.coe_basisMonomials] at this
  exact this

theorem symFamily_span : ⊤ ≤ Submodule.span k (Set.range (symFamily (k := k) b n)) := by
  rw [← SymmetricPower.span_tprod_eq_top (R := k) (ι := Fin n) (M := V), Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  have hg : g = fun i => ∑ j, b.repr (g i) j • b j := by
    funext i
    exact (b.sum_repr (g i)).symm
  rw [hg, MultilinearMap.map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ ?_
  rw [← symFamily_msetOf]
  exact Submodule.subset_span ⟨_, rfl⟩

/-- A basis of the `n`-th symmetric power of `V`, indexed by multisets of size `n` of basis indices. -/
@[kb "etingof2011" "Problem 1.49(d), p. 18"]
noncomputable def symBasis : Module.Basis (Sym ι n) k (SymmetricPower k (Fin n) V) :=
  Module.Basis.mk (symFamily_linearIndependent b n) (symFamily_span b n)

theorem symBasis_apply (m : Sym ι n) : symBasis b n m = symFamily b n m := by
  simp [symBasis]

end Basis

/-- The dimension of the `n`-th symmetric power of an `d`-dimensional vector space is
`choose (d + n - 1) n`. -/
@[kb "etingof2011" "Problem 1.49(d), p. 18"]
theorem finrank_symmetricPower {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (SymmetricPower k (Fin n) V) = (Module.finrank k V + n - 1).choose n := by
  classical
  rw [Module.finrank_eq_card_basis (symBasis (Module.finBasis k V) n), Sym.card_sym_eq_choose,
    Fintype.card_fin]

section CharZero

variable (k : Type) [Field k] [CharZero k] (n : ℕ) (V : Type*) [AddCommGroup V] [Module k V]

/-- Symmetrization of the tensor power: the average of the permutation action over `S_n`. -/
noncomputable def symmetrizer : (⨂[k] _ : Fin n, V) →ₗ[k] ⨂[k] _ : Fin n, V :=
  ((Nat.factorial n : k)⁻¹) • ∑ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n V σ

variable {k n V}

omit [CharZero k] in
theorem symmetrizer_apply (x : ⨂[k] _ : Fin n, V) :
    symmetrizer k n V x = ((Nat.factorial n : k)⁻¹) • ∑ σ : Equiv.Perm (Fin n),
      tensorPowerPermRep k n V σ x := by
  simp [symmetrizer]

omit [CharZero k] in
theorem symmetrizer_tprod_perm (e : Equiv.Perm (Fin n)) (f : Fin n → V) :
    symmetrizer k n V (tprod k fun i => f (e i)) = symmetrizer k n V (tprod k f) := by
  rw [symmetrizer_apply, symmetrizer_apply]
  congr 1
  have h : ∀ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n V σ (tprod k fun i => f (e i)) =
      tensorPowerPermRep k n V (σ * e⁻¹) (tprod k f) := by
    intro σ
    simp [tensorPowerPermRep_tprod]
  simp_rw [h]
  exact Equiv.sum_comp (Equiv.mulRight e⁻¹) (fun σ => tensorPowerPermRep k n V σ (tprod k f))

omit [CharZero k] in
theorem mk_perm (σ : Equiv.Perm (Fin n)) (x : ⨂[k] _ : Fin n, V) :
    SymmetricPower.mk k (Fin n) V (tensorPowerPermRep k n V σ x) = SymmetricPower.mk k (Fin n) V x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, tensorPowerPermRep_tprod]
    congr 1
    exact SymmetricPower.tprod_equiv (R := k) σ⁻¹ f
  | add y z hy hz => simp only [map_add, hy, hz]

theorem mk_symmetrizer (x : ⨂[k] _ : Fin n, V) :
    SymmetricPower.mk k (Fin n) V (symmetrizer k n V x) = SymmetricPower.mk k (Fin n) V x := by
  rw [symmetrizer_apply, map_smul, map_sum]
  simp only [mk_perm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero n

theorem symmetrizer_of_mem (x : ⨂[k] _ : Fin n, V) (hx : x ∈ symmetricTensors k n V) :
    symmetrizer k n V x = x := by
  have hx' : ∀ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n V σ x = x :=
    (Representation.mem_invariants _ _).mp hx
  rw [symmetrizer_apply]
  simp only [hx', Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero n

theorem symmetrizer_mem (x : ⨂[k] _ : Fin n, V) : symmetrizer k n V x ∈ symmetricTensors k n V := by
  rw [symmetricTensors, Representation.mem_invariants]
  intro τ
  rw [symmetrizer_apply, map_smul]
  congr 1
  exact symmetrize_invariant x τ

variable (k n V) in
/-- The section of the quotient map from the symmetric tensors to the symmetric power: symmetrization,
descended to the quotient. -/
noncomputable def symmetrizerSymm : SymmetricPower k (Fin n) V →ₗ[k] ⨂[k] _ : Fin n, V :=
  symLift (symmetrizer k n V) symmetrizer_tprod_perm

/-- **Problem 1.49(e).** In characteristic zero the symmetric power `S^n V` is canonically isomorphic to
the space of symmetric tensors in `V^{⊗n}`: the quotient map restricts to a bijection from the symmetric
tensors onto `S^n V`. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem symmetricTensors_mk_bijective :
    Function.Bijective
      ((SymmetricPower.mk k (Fin n) V).comp (symmetricTensors k n V).subtype) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : SymmetricPower.mk k (Fin n) V (x : ⨂[k] _ : Fin n, V) = 0 := hx
    have h2 : symmetrizer k n V (x : ⨂[k] _ : Fin n, V) = 0 := by
      have := congrArg (symmetrizerSymm k n V) h1
      rwa [map_zero, symmetrizerSymm, symLift_mk] at this
    exact Subtype.ext (by rw [← symmetrizer_of_mem _ x.2, h2]; rfl)
  · intro y
    obtain ⟨x, rfl⟩ : ∃ x, SymmetricPower.mk k (Fin n) V x = y := by
      have := SymmetricPower.range_mk k (Fin n) V
      have hy : y ∈ LinearMap.range (SymmetricPower.mk k (Fin n) V) := by rw [this]; trivial
      exact hy
    exact ⟨⟨symmetrizer k n V x, symmetrizer_mem x⟩, mk_symmetrizer x⟩

end CharZero

end UndergradKB.RepresentationTheory
