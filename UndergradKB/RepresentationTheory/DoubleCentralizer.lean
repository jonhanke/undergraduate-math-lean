import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.SchurFunctors

/-! # Double centralizer theorem and the centralizer of the symmetric group (Etingof et al., 4.54 to 4.56)

* `centralizer_centralizer_eq`, `isSemisimpleRing_commutant`: for a semisimple subalgebra `A` of `End E`
  (`E` finite-dimensional), `A` is its own double commutant and the commutant is semisimple (Theorem 4.54;
  the decomposition `E = ⊕ Vᵢ ⊗ Wᵢ` is not formalized, and algebraic closedness is not needed for what is proved).
* `symmetricTensors_eq_span_purePowers`: in characteristic zero, symmetric tensors are spanned by pure powers
  `u ⊗ ⋯ ⊗ u` (Lemma 4.56, first part), proved by polarization (inclusion-exclusion over subsets).
* `centralizer_perm_eq_span_tensorPowerMap`, `centralizer_perm_eq_adjoin_diagAction`: the commutant of the
  symmetric group in `End(V^{⊗n})` is spanned by the operators `g ⊗ ⋯ ⊗ g` and equals the algebra generated
  by the diagonal operators `Δ_n(b)` (Theorem 4.55; the latter uses Newton's identities in characteristic zero).
-/

namespace UndergradKB.RepresentationTheory

open PiTensorProduct Finset
open scoped TensorProduct

section Newton

open MvPolynomial in
/-- Newton: in characteristic zero, the elementary symmetric functions of commuting elements lie in any
subalgebra containing all their power sums. -/
theorem aeval_esymm_mem {k : Type*} [Field k] [CharZero k] {C : Type*} [CommRing C] [Algebra k C]
    {n : ℕ} (x : Fin n → C) (Q : Subalgebra k C) (hQ : ∀ m, ∑ i, x i ^ m ∈ Q) (j : ℕ) :
    aeval x (esymm (Fin n) k j) ∈ Q := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have h := congrArg (aeval x) (mul_esymm_eq_sum (Fin n) k j)
      have hj' : (j : k) ≠ 0 := by exact_mod_cast hj.ne'
      have h2 : (j : k) • aeval x (esymm (Fin n) k j) ∈ Q := by
        have : (j : k) • aeval x (esymm (Fin n) k j)
            = aeval x ((j : MvPolynomial (Fin n) k) * esymm (Fin n) k j) := by
          simp [map_mul, Algebra.smul_def]
        rw [this, h]
        simp only [map_mul, map_pow, map_neg, map_one, map_sum]
        refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
          (Subalgebra.sum_mem _ fun a ha => ?_)
        have ha' := (Finset.mem_filter.mp ha).2
        refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _
          (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) (ih _ ha')) ?_
        simpa [psum] using hQ a.2
      have := Subalgebra.smul_mem Q h2 (j : k)⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hj', one_smul] at this

end Newton

section Polarization

variable {n : ℕ} {M : Type*} [AddCommGroup M]

/-- Inclusion-exclusion over subsets: summing over all `r : Fin n → Fin n` whose values lie in `S`, with
signs, isolates the surjective maps. -/
theorem signed_sum_subsets (F : (Fin n → Fin n) → M) :
    ∑ S : Finset (Fin n), ((-1 : ℤ) ^ (Sᶜ).card) • ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S), F r
      = ∑ r : Fin n → Fin n, if Function.Surjective r then F r else 0 := by
  classical
  have h1 : ∀ S : Finset (Fin n), ((-1 : ℤ) ^ (Sᶜ).card) • ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S), F r
      = ∑ r : Fin n → Fin n, if Finset.univ.image r ⊆ S then ((-1 : ℤ) ^ (Sᶜ).card) • F r else 0 := by
    intro S
    rw [Finset.smul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext r
    simp [Fintype.mem_piFinset, Finset.subset_iff]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h2 : (∑ S : Finset (Fin n), if Finset.univ.image r ⊆ S then ((-1 : ℤ) ^ (Sᶜ).card) • F r else 0)
      = (∑ S : Finset (Fin n), if Finset.univ.image r ⊆ S then ((-1 : ℤ) ^ (Sᶜ).card) else 0) • F r := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs <;> simp
  rw [h2]
  have h3 : (∑ S : Finset (Fin n), if Finset.univ.image r ⊆ S then ((-1 : ℤ) ^ (Sᶜ).card) else 0)
      = ∑ T ∈ ((Finset.univ.image r)ᶜ).powerset, (-1 : ℤ) ^ T.card := by
    rw [← Fintype.sum_bijective (fun S : Finset (Fin n) => Sᶜ) compl_involutive.bijective
      (fun T => if T ⊆ (Finset.univ.image r)ᶜ then (-1 : ℤ) ^ T.card else 0)]
    · rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext T
      simp
    · intro S
      have : S ⊆ (Finset.univ.image r)ᶜ ↔ Finset.univ.image r ⊆ Sᶜ := Finset.subset_compl_comm
      simp only [compl_compl, this]
  rw [h3, Finset.sum_powerset_neg_one_pow_card]
  have h4 : ((Finset.univ.image r)ᶜ = ∅) ↔ Function.Surjective r := by
    rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
    simp [Function.Surjective]
  by_cases h : Function.Surjective r
  · simp [h4.mpr h, h]
  · have : ¬ ((Finset.univ.image r)ᶜ = ∅) := fun h' => h (h4.mp h')
    simp [this, h]

/-- The sum over surjective self-maps of `Fin n` equals the sum over permutations. -/
theorem sum_surjective_eq_sum_perm (F : (Fin n → Fin n) → M) :
    ∑ r : Fin n → Fin n, (if Function.Surjective r then F r else 0) = ∑ σ : Equiv.Perm (Fin n), F σ := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun σ _ => (σ : Fin n → Fin n)) ?_ ?_ ?_ ?_
  · intro σ _
    simp [σ.surjective]
  · intro σ _ τ _ h
    exact DFunLike.coe_injective h
  · intro r hr
    have hs : Function.Surjective r := by simpa using hr
    exact ⟨Equiv.ofBijective r ⟨Finite.injective_iff_surjective.mpr hs, hs⟩,
      by simp, rfl⟩
  · intro σ _
    rfl

end Polarization

section Symmetric

variable (k : Type*) [Field k] [CharZero k] (n : ℕ) (U : Type*) [AddCommGroup U] [Module k U]

/-- The pure powers `u ⊗ ⋯ ⊗ u` in the tensor power `U^{⊗n}`. -/
def purePowers : Set (⨂[k] _ : Fin n, U) := Set.range fun u : U => tprod k fun _ : Fin n => u

/-- The symmetric tensors in `U^{⊗n}`: the invariants of the symmetric group acting by permuting factors. -/
noncomputable def symmetricTensors : Submodule k (⨂[k] _ : Fin n, U) :=
  Representation.invariants (tensorPowerPermRep k n U)

variable {k n U}

omit [CharZero k] in
/-- Polarization: the sum over all orderings of a family of vectors, tensored, is a combination of pure
powers (of sums of subfamilies). -/
theorem sum_perm_tprod_mem_span (f : Fin n → U) :
    ∑ σ : Equiv.Perm (Fin n), tprod k (fun i => f (σ i)) ∈ Submodule.span k (purePowers k n U) := by
  classical
  have key := signed_sum_subsets (M := ⨂[k] _ : Fin n, U) (fun r => tprod k (fun i => f (r i)))
  rw [sum_surjective_eq_sum_perm] at key
  rw [← key]
  refine Submodule.sum_mem _ fun S _ => ?_
  have h : ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S), tprod k (fun i => f (r i))
      = tprod k (fun _ : Fin n => ∑ i ∈ S, f i) := by
    rw [(tprod k).map_sum_finset (fun _ (i : Fin n) => f i) (fun _ => S)]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- **Lemma 4.56 (first part).** In characteristic zero the symmetric tensors in `U^{⊗n}` are spanned by the
pure powers `u ⊗ ⋯ ⊗ u`. -/
@[kb "etingof2011" "Lemma 4.56, p. 65"]
theorem symmetricTensors_eq_span_purePowers :
    symmetricTensors k n U = Submodule.span k (purePowers k n U) := by
  classical
  apply le_antisymm
  · intro x hx
    have hx' : ∀ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n U σ x = x :=
      (Representation.mem_invariants _ _).mp hx
    have hsum : ∀ y : ⨂[k] _ : Fin n, U,
        ∑ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n U σ y ∈ Submodule.span k (purePowers k n U) := by
      intro y
      induction y using PiTensorProduct.induction_on with
      | smul_tprod r f =>
        simp only [map_smul, ← Finset.smul_sum]
        refine Submodule.smul_mem _ _ ?_
        simp_rw [tensorPowerPermRep_tprod]
        exact (Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
          (fun σ => tprod k (fun i => f (σ i)))) ▸ sum_perm_tprod_mem_span f
      | add y z hy hz =>
        simp only [map_add, Finset.sum_add_distrib]
        exact Submodule.add_mem _ hy hz
    have hn : (Nat.factorial n : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have : x = ((Nat.factorial n : k))⁻¹ • ∑ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n U σ x := by
      simp_rw [hx']
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul k,
        smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (hsum x)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, rfl⟩
    refine (Representation.mem_invariants _ _).mpr fun σ => ?_
    rw [tensorPowerPermRep_tprod]

end Symmetric

section DoubleCentralizer

variable {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  (A : Subalgebra k (Module.End k E))

/-- The commutant of `A` in `End E`. -/
abbrev commutant : Subalgebra k (Module.End k E) := Subalgebra.centralizer k (A : Set (Module.End k E))

/-- An element of the commutant of `A` is an `A`-linear endomorphism of `E`. -/
noncomputable def commutantToEnd : commutant A →ₐ[k] Module.End A E where
  toFun b :=
    { toFun := fun x => b.1 x
      map_add' := fun x y => map_add b.1 x y
      map_smul' := fun a x => by
        have h := (Subalgebra.mem_centralizer_iff (R := k)).mp b.2 a.1 a.2
        exact (congr($h x)).symm }
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [FiniteDimensional k E] in
theorem commutantToEnd_bijective : Function.Bijective (commutantToEnd A) := by
  constructor
  · intro b c h
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    exact congr($h x)
  · intro g
    refine ⟨⟨g.restrictScalars k, (Subalgebra.mem_centralizer_iff (R := k)).mpr fun a ha => ?_⟩, rfl⟩
    refine LinearMap.ext fun x => ?_
    exact (g.map_smul ⟨a, ha⟩ x).symm

/-- The commutant of `A` is isomorphic, as an algebra, to `End_A(E)`. -/
noncomputable def commutantEquivEnd : commutant A ≃ₐ[k] Module.End A E :=
  AlgEquiv.ofBijective (commutantToEnd A) (commutantToEnd_bijective A)

/-- **Theorem 4.54 (second part).** The commutant of a semisimple subalgebra `A` of `End E` is semisimple. -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem isSemisimpleRing_commutant [IsSemisimpleRing A] : IsSemisimpleRing (commutant A) := by
  have : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  have : IsSemisimpleRing (Module.End A E) := IsSemisimpleRing.moduleEnd A E
  exact (commutantEquivEnd A).toRingEquiv.symm.isSemisimpleRing

/-- **Theorem 4.54 (first part).** For a semisimple subalgebra `A` of `End E`, `A` is the commutant of its
commutant (double centralizer theorem). -/
@[kb "etingof2011" "Theorem 4.54, p. 64"]
theorem centralizer_centralizer_eq [IsSemisimpleRing A] :
    Subalgebra.centralizer k (commutant A : Set (Module.End k E)) = A := by
  refine le_antisymm ?_ (Subalgebra.le_centralizer_centralizer k)
  intro T hT
  have hT' := (Subalgebra.mem_centralizer_iff (R := k)).mp hT
  let f : Module.End (Module.End A E) E :=
    { toFun := fun x => T x
      map_add' := fun x y => map_add T x y
      map_smul' := fun g x => by
        have hg : ((g.restrictScalars k : Module.End k E)) ∈ commutant A :=
          (Subalgebra.mem_centralizer_iff (R := k)).mpr fun a ha => by
            refine LinearMap.ext fun x => ?_
            exact (g.map_smul ⟨a, ha⟩ x).symm
        have h := hT' _ hg
        exact (congr($h x)).symm }
  classical
  let b := Module.finBasis k E
  obtain ⟨a, ha⟩ := jacobson_density f (Finset.univ.image b)
  refine (Subalgebra.mem_carrier.mp ?_ : T ∈ A)
  have : T = a.1 := by
    refine b.ext fun i => ?_
    have := ha (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    exact this
  rw [this]
  exact a.2

end DoubleCentralizer

section SchurWeylCentralizer

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] {n : ℕ}

/-- Every endomorphism of `V^{⊗n}` is a linear combination of tensor products of endomorphisms of `V`
(for `V` finite-dimensional): `End(V)^{⊗n} → End(V^{⊗n})` is surjective. -/
theorem piTensorHomMap_surjective :
    Function.Surjective (piTensorHomMap : (⨂[k] _ : Fin n, V →ₗ[k] V) →ₗ[k] _) := by
  classical
  let b := Module.finBasis k V
  let B := Basis.piTensorProduct (fun _ : Fin n => b)
  -- matrix units
  let u : Fin (Module.finrank k V) → Fin (Module.finrank k V) → V →ₗ[k] V :=
    fun a c => b.constr k (fun j => if j = c then b a else 0)
  have hu : ∀ a c j, u a c (b j) = if j = c then b a else 0 := fun a c j => by
    simp [u]
  have hunit : ∀ p q p' : Fin n → Fin (Module.finrank k V),
      piTensorHomMap (tprod k (fun i => u (q i) (p i))) (B p') = if p' = p then B q else 0 := by
    intro p q p'
    rw [Basis.piTensorProduct_apply, piTensorHomMap_tprod_tprod]
    simp_rw [hu]
    by_cases h : p' = p
    · subst h
      simp [B, Basis.piTensorProduct_apply]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      exact (tprod k).map_coord_zero i (by simp [hi])
  intro T
  have hT : T = piTensorHomMap (∑ p : Fin n → Fin (Module.finrank k V), ∑ q : Fin n → Fin (Module.finrank k V),
      (B.repr (T (B p)) q) • tprod k (fun i => u (q i) (p i))) := by
    refine B.ext fun p' => ?_
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hunit]
    rw [Finset.sum_eq_single p']
    · simp [B.sum_repr]
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  exact ⟨_, hT.symm⟩

omit [FiniteDimensional k V] in
/-- Conjugating `⊗ g_i` by a permutation of the tensor factors permutes the `g_i`. -/
theorem perm_conj_piTensorHomMap (σ : Equiv.Perm (Fin n)) (X : ⨂[k] _ : Fin n, V →ₗ[k] V)
    (y : ⨂[k] _ : Fin n, V) :
    tensorPowerPermRep k n V σ (piTensorHomMap X (tensorPowerPermRep k n V σ⁻¹ y))
      = piTensorHomMap (tensorPowerPermRep k n (V →ₗ[k] V) σ X) y := by
  induction X using PiTensorProduct.induction_on generalizing y with
  | smul_tprod r g =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s x =>
      simp [tensorPowerPermRep_tprod, Equiv.Perm.inv_def]
      congr! with i
      exact σ.apply_symm_apply i
    | add y z hy hz =>
      simp only [map_add, hy, hz]
  | add X Z hX hZ =>
    simp only [map_add, LinearMap.add_apply, hX, hZ]

/-- Symmetrization of an element of `End(V)^{⊗n}` is invariant under permutations. -/
theorem symmetrize_invariant {W : Type*} [AddCommGroup W] [Module k W] (X : ⨂[k] _ : Fin n, W)
    (τ : Equiv.Perm (Fin n)) :
    tensorPowerPermRep k n W τ (∑ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n W σ X)
      = ∑ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n W σ X := by
  simp only [map_sum]
  change ∑ σ, (tensorPowerPermRep k n W τ * tensorPowerPermRep k n W σ) X = _
  simp_rw [← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => tensorPowerPermRep k n W σ X)

/-- **Theorem 4.55 (span form).** In characteristic zero, for `V` finite-dimensional, the commutant in
`End(V^{⊗n})` of the symmetric group acting by permuting factors is the span of the operators
`g ⊗ ⋯ ⊗ g`, `g ∈ End V`. -/
@[kb "etingof2011" "Theorem 4.55, p. 64"]
theorem centralizer_perm_eq_span_tensorPowerMap [CharZero k] :
    (Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))).toSubmodule
      = Submodule.span k (Set.range fun g : V →ₗ[k] V => tensorPowerMap n g) := by
  classical
  apply le_antisymm
  · intro T hT
    have hT' : ∀ σ : Equiv.Perm (Fin n), ∀ y, tensorPowerPermRep k n V σ (T y)
        = T (tensorPowerPermRep k n V σ y) := by
      intro σ y
      have h := (Subalgebra.mem_centralizer_iff (R := k)).mp hT _ ⟨σ, rfl⟩
      exact congr($h y)
    obtain ⟨X, rfl⟩ := piTensorHomMap_surjective (k := k) (V := V) (n := n) T
    set X' : ⨂[k] _ : Fin n, V →ₗ[k] V :=
      ((Nat.factorial n : k))⁻¹ • ∑ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n (V →ₗ[k] V) σ X with hX'
    have hinv : X' ∈ symmetricTensors k n (V →ₗ[k] V) := by
      refine (Representation.mem_invariants _ _).mpr fun τ => ?_
      rw [hX', map_smul, symmetrize_invariant]
    have hΦ : piTensorHomMap X' = piTensorHomMap X := by
      rw [hX', map_smul]
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
      have : ∀ σ : Equiv.Perm (Fin n), piTensorHomMap (tensorPowerPermRep k n (V →ₗ[k] V) σ X) y
          = piTensorHomMap X y := by
        intro σ
        rw [← perm_conj_piTensorHomMap, ← hT']
        have h := tensorPowerPermRep_inv_apply σ⁻¹ (piTensorHomMap X y)
        rwa [inv_inv] at h
      simp_rw [this]
      have hn : (Nat.factorial n : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul k,
        smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [← hΦ]
    rw [symmetricTensors_eq_span_purePowers] at hinv
    have : piTensorHomMap X' ∈ Submodule.map (piTensorHomMap : (⨂[k] _ : Fin n, V →ₗ[k] V) →ₗ[k] _)
        (Submodule.span k (purePowers k n (V →ₗ[k] V))) := ⟨X', hinv, rfl⟩
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, by simp [tensorPowerMap, piTensorHomMap_tprod_eq_map]⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    refine (Subalgebra.mem_centralizer_iff (R := k)).mpr ?_
    rintro _ ⟨σ, rfl⟩
    refine LinearMap.ext fun x => ?_
    exact (tensorPowerMap_perm g σ x).symm

end SchurWeylCentralizer

section DiagonalAction

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {n : ℕ}

/-- The operator `1 ⊗ ⋯ ⊗ g ⊗ ⋯ ⊗ 1` on `V^{⊗n}`, with `g` in the `i`-th slot. -/
noncomputable def opAt (i : Fin n) (g : V →ₗ[k] V) : Module.End k (⨂[k] _ : Fin n, V) :=
  PiTensorProduct.map (Function.update (fun _ : Fin n => (LinearMap.id : V →ₗ[k] V)) i g)

/-- The diagonal action `Δ_n(g) = ∑ᵢ 1 ⊗ ⋯ ⊗ g ⊗ ⋯ ⊗ 1` of an endomorphism on `V^{⊗n}`. -/
noncomputable def diagAction (n : ℕ) (g : V →ₗ[k] V) : Module.End k (⨂[k] _ : Fin n, V) :=
  ∑ i : Fin n, opAt i g

theorem map_mul_map (f f' : Π _ : Fin n, V →ₗ[k] V) :
    PiTensorProduct.map f * PiTensorProduct.map f' = PiTensorProduct.map (fun l => f l * f' l) := by
  rw [Module.End.mul_eq_comp, ← PiTensorProduct.map_comp]
  rfl

theorem opAt_comm (i j : Fin n) (g : V →ₗ[k] V) : opAt i g * opAt j g = opAt j g * opAt i g := by
  classical
  unfold opAt
  rw [map_mul_map, map_mul_map]
  congr 1
  funext l
  by_cases hi : l = i <;> by_cases hj : l = j <;> simp [hi, hj, Function.update, Module.End.mul_eq_comp]

theorem opAt_pow (i : Fin n) (g : V →ₗ[k] V) (m : ℕ) : opAt i g ^ m = opAt i (g ^ m) := by
  classical
  induction m with
  | zero =>
    have : Function.update (fun _ : Fin n => (LinearMap.id : V →ₗ[k] V)) i (g ^ 0) = fun _ => LinearMap.id := by
      funext l
      by_cases hl : l = i <;> simp [hl, Module.End.one_eq_id]
    rw [pow_zero, opAt, this, PiTensorProduct.map_id]
    rfl
  | succ m ih =>
    rw [pow_succ, ih]
    unfold opAt
    rw [map_mul_map]
    congr 1
    funext l
    by_cases hl : l = i <;> simp [hl, pow_succ, Module.End.mul_eq_comp]

theorem perm_conj_opAt (σ : Equiv.Perm (Fin n)) (i : Fin n) (b : V →ₗ[k] V) (y : ⨂[k] _ : Fin n, V) :
    tensorPowerPermRep k n V σ (opAt i b (tensorPowerPermRep k n V σ⁻¹ y)) = opAt (σ i) b y := by
  classical
  have h := perm_conj_piTensorHomMap σ
    (tprod k (Function.update (fun _ : Fin n => (LinearMap.id : V →ₗ[k] V)) i b)) y
  rw [piTensorHomMap_tprod_eq_map] at h
  rw [tensorPowerPermRep_tprod, piTensorHomMap_tprod_eq_map] at h
  unfold opAt
  rw [h]
  congr 2
  funext l
  by_cases hl : l = σ i
  · subst hl
    simp
  · have : σ.symm l ≠ i := fun h' => hl (by rw [← h']; simp)
    simp [hl, this]

theorem diagAction_commute_perm (σ : Equiv.Perm (Fin n)) (b : V →ₗ[k] V) (z : ⨂[k] _ : Fin n, V) :
    tensorPowerPermRep k n V σ (diagAction n b z) = diagAction n b (tensorPowerPermRep k n V σ z) := by
  have key : ∀ i, tensorPowerPermRep k n V σ (opAt i b z) = opAt (σ i) b (tensorPowerPermRep k n V σ z) := by
    intro i
    have h := perm_conj_opAt σ i b (tensorPowerPermRep k n V σ z)
    rwa [tensorPowerPermRep_inv_apply] at h
  simp only [diagAction, LinearMap.sum_apply, map_sum, key]
  exact Equiv.sum_comp σ (fun i => opAt i b (tensorPowerPermRep k n V σ z))

/-- In characteristic zero, `g ⊗ ⋯ ⊗ g` lies in the algebra generated by the diagonal operators `Δ_n(b)`. -/
theorem tensorPowerMap_mem_adjoin_diagAction [CharZero k] (g : V →ₗ[k] V) :
    tensorPowerMap n g ∈ Algebra.adjoin k (Set.range (diagAction (k := k) (V := V) n)) := by
  classical
  let C : Subalgebra k (Module.End k (⨂[k] _ : Fin n, V)) :=
    Algebra.adjoin k (Set.range fun i : Fin n => opAt i g)
  have hcomm : (Set.range fun i : Fin n => opAt i g).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact opAt_comm i j g
  have : IsMulCommutative C := Algebra.isMulCommutative_adjoin k hcomm
  have hC : ∀ a b : C, a * b = b * a := fun a b => Std.Commutative.comm a b
  let _ : CommRing C := { (inferInstance : Ring C) with mul_comm := hC }
  let x : Fin n → C := fun i => ⟨opAt i g, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let Q : Subalgebra k C := (Algebra.adjoin k (Set.range (diagAction (k := k) (V := V) n))).comap C.val
  have hQ : ∀ m, ∑ i, x i ^ m ∈ Q := by
    intro m
    rw [Subalgebra.mem_comap]
    have : C.val (∑ i, x i ^ m) = diagAction n (g ^ m) := by
      simp only [map_sum, map_pow, diagAction]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact opAt_pow i g m
    rw [this]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  have h := aeval_esymm_mem x Q hQ n
  rw [Subalgebra.mem_comap] at h
  have hprod : ∀ s : Finset (Fin n), C.val (∏ i ∈ s, x i)
      = PiTensorProduct.map (fun l => if l ∈ s then g else LinearMap.id) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp; rfl
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, map_mul, ih]
      change opAt j g * _ = _
      unfold opAt
      rw [map_mul_map]
      congr 1
      funext l
      by_cases hl : l = j
      · subst hl
        simp [hj, Module.End.mul_eq_comp]
      · simp [hl, Module.End.mul_eq_comp]
  have hesymm : MvPolynomial.aeval x (MvPolynomial.esymm (Fin n) k n) = ∏ i, x i := by
    have h0 := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rw [Finset.card_univ, Fintype.card_fin] at h0
    simp [MvPolynomial.esymm, h0]
  rw [hesymm, hprod] at h
  simpa [tensorPowerMap] using h

end DiagonalAction

section SchurWeylDiagonal

variable {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {n : ℕ}

/-- **Theorem 4.55.** For finite-dimensional `V` over a field of characteristic zero, the commutant in
`End(V^{⊗n})` of the symmetric group (acting by permuting factors) is the subalgebra generated by the diagonal
operators `Δ_n(b) = ∑ᵢ 1 ⊗ ⋯ ⊗ b ⊗ ⋯ ⊗ 1`, i.e. the image of `U(gl V)`. -/
@[kb "etingof2011" "Theorem 4.55, p. 64"]
theorem centralizer_perm_eq_adjoin_diagAction :
    Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))
      = Algebra.adjoin k (Set.range (diagAction (k := k) (V := V) n)) := by
  apply le_antisymm
  · intro T hT
    have : T ∈ (Subalgebra.centralizer k (Set.range (tensorPowerPermRep k n V))).toSubmodule := hT
    rw [centralizer_perm_eq_span_tensorPowerMap] at this
    refine (Submodule.span_le (p := (Algebra.adjoin k (Set.range (diagAction (k := k) (V := V) n))).toSubmodule)).mpr ?_ this
    rintro _ ⟨g, rfl⟩
    exact tensorPowerMap_mem_adjoin_diagAction g
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨b, rfl⟩
    refine (Subalgebra.mem_centralizer_iff (R := k)).mpr ?_
    rintro _ ⟨σ, rfl⟩
    refine LinearMap.ext fun z => ?_
    exact diagAction_commute_perm σ b z

end SchurWeylDiagonal

end UndergradKB.RepresentationTheory
