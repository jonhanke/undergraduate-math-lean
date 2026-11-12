import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.MatrixElements

/-! # Complex representations: forms, conjugate and types (Etingof et al., Sections 3.6 and 4.1)

* Theorem 3.11 (uniqueness): two invariant positive definite Hermitian forms on an irreducible
  finite-dimensional complex representation are proportional by a positive real (`posDef_forms_proportional`),
  and an invariant positive definite Hermitian form exists on any representation of a finite group
  (`exists_invariantPosDefHermitian`).
* Section 3.6: the conjugate representation `conjRepresentation` (on `ConjSpace V`) is isomorphic to the dual
  (`nonempty_equiv_conj_dual`).
* Section 4.1: complex, real and quaternionic type; the vanishing of `∑_g χ(g²)` in the complex case.
* Definition 4.6: the group determinant as a multivariate polynomial.
* Lemma 4.14: conjugates of a sum of algebraic numbers are sums of conjugates of the summands.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open Representation Module
open scoped ComplexConjugate

section Conjugate

/-- The complex conjugate of a complex vector space: the same additive group, with the scalar `c` acting as
multiplication by `conj c`. -/
def ConjSpace (V : Type*) : Type _ := V

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

instance : AddCommGroup (ConjSpace V) := inferInstanceAs (AddCommGroup V)

instance : Module ℂ (ConjSpace V) := Module.compHom V (starRingEnd ℂ)

/-- The underlying vector of an element of the conjugate space. -/
def ConjSpace.val (x : ConjSpace V) : V := x

/-- Reinterpret a vector as an element of the conjugate space. -/
def ConjSpace.mk (x : V) : ConjSpace V := x

@[simp] theorem ConjSpace.val_mk (x : V) : (ConjSpace.mk x).val = x := rfl
@[simp] theorem ConjSpace.mk_val (x : ConjSpace V) : ConjSpace.mk x.val = x := rfl
@[simp] theorem ConjSpace.val_add (x y : ConjSpace V) : (x + y).val = x.val + y.val := rfl
theorem ConjSpace.val_injective : Function.Injective (ConjSpace.val (V := V)) := fun _ _ h => h

@[simp] theorem ConjSpace.val_zero : (0 : ConjSpace V).val = 0 := rfl
@[simp] theorem ConjSpace.val_smul (c : ℂ) (x : ConjSpace V) : (c • x).val = starRingEnd ℂ c • x.val := rfl
@[simp] theorem ConjSpace.mk_add (x y : V) : ConjSpace.mk (x + y) = ConjSpace.mk x + ConjSpace.mk y := rfl
@[simp] theorem ConjSpace.mk_smul (c : ℂ) (x : V) :
    ConjSpace.mk (starRingEnd ℂ c • x) = c • ConjSpace.mk x := rfl

/-- Coordinates in a basis identify the conjugate space with finitely supported functions, conjugating the
coordinates. -/
noncomputable def ConjSpace.equivFinsupp {ι : Type*} (b : Module.Basis ι ℂ V) :
    ConjSpace V ≃ₗ[ℂ] (ι →₀ ℂ) where
  toFun x := Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (b.repr x.val)
  invFun f := ConjSpace.mk (b.repr.symm (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) f))
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  left_inv x := by
    apply ConjSpace.val_injective
    apply b.repr.injective
    ext i
    simp
  right_inv f := by
    ext i
    simp

theorem ConjSpace.finrank_eq [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (ConjSpace V) ∧ finrank ℂ (ConjSpace V) = finrank ℂ V := by
  let b := Module.finBasis ℂ V
  let e := ConjSpace.equivFinsupp b
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq]
  simp

end Conjugate


section Forms

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- A sesquilinear form on a complex vector space (conjugate-linear in the first slot, linear in the
second) is a positive definite Hermitian form if it is conjugate-symmetric and `B v v` is a positive real
number for `v ≠ 0`. -/
structure IsPosDefHermitian (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  conj_symm : ∀ v w, conj (B v w) = B w v
  pos : ∀ v, v ≠ 0 → (B v v).im = 0 ∧ 0 < (B v v).re

/-- A form is invariant under a representation if every `ρ g` preserves it. -/
def IsInvariantForm (ρ : Representation ℂ G V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop :=
  ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w

theorem rep_apply_inv_apply (ρ : Representation ℂ G V) (g : G) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  rw [← mul_apply_eq_comp, ← map_mul]
  simp

variable {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

theorem IsPosDefHermitian.eq_zero (hB : IsPosDefHermitian B) {x : V} (h : ∀ v, B x v = 0) : x = 0 := by
  by_contra hx
  have := (hB.pos x hx).2
  rw [h x] at this
  simp at this

theorem IsPosDefHermitian.ext (hB : IsPosDefHermitian B) {x y : V} (h : ∀ v, B x v = B y v) : x = y := by
  have : x - y = 0 := hB.eq_zero fun v => by rw [map_sub, LinearMap.sub_apply, h v, sub_self]
  exact sub_eq_zero.mp this

/-- The conjugate-linear map `x ↦ B x ·` from `V` to its dual, as a linear map out of the conjugate space. -/
noncomputable def toDualConj (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : ConjSpace V →ₗ[ℂ] Module.Dual ℂ V where
  toFun x := B x.val
  map_add' x y := by simp
  map_smul' c x := by simp

theorem toDualConj_apply (x : ConjSpace V) (v : V) : toDualConj B x v = B x.val v := rfl

/-- For a positive definite Hermitian form on a finite-dimensional space, every linear functional is
`B x ·` for some `x` (a Riesz representation statement). -/
theorem IsPosDefHermitian.exists_repr [FiniteDimensional ℂ V] (hB : IsPosDefHermitian B)
    (f : Module.Dual ℂ V) : ∃ x : V, ∀ v, B x v = f v := by
  obtain ⟨hfin, hrank⟩ := ConjSpace.finrank_eq (V := V)
  have hinj : Function.Injective (toDualConj B) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply ConjSpace.val_injective
    exact hB.eq_zero fun v => by rw [← toDualConj_apply, hx]; rfl
  have hsurj : Function.Surjective (toDualConj B) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hrank, Subspace.dual_finrank_eq])).mp hinj
  obtain ⟨x, hx⟩ := hsurj f
  exact ⟨x.val, fun v => by rw [← toDualConj_apply, hx]⟩

/-- **Etingof et al., Theorem 3.11** (uniqueness): on an irreducible finite-dimensional complex
representation, two invariant positive definite Hermitian forms are proportional, by a positive real
factor. The proof is by Schur's lemma applied to the operator relating the two forms. -/
@[kb "etingof2011" "Theorem 3.11, p. 39"]
theorem posDef_forms_proportional [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} [IsIrreducible ρ]
    {B₁ B₂ : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (h₁ : IsPosDefHermitian B₁) (h₂ : IsPosDefHermitian B₂)
    (i₁ : IsInvariantForm ρ B₁) (i₂ : IsInvariantForm ρ B₂) :
    ∃ c : ℝ, 0 < c ∧ ∀ v w, B₂ v w = (c : ℂ) * B₁ v w := by
  choose A hA using fun w => h₁.exists_repr (B₂ w)
  let T : V →ₗ[ℂ] V :=
    { toFun := A
      map_add' := fun w w' => h₁.ext fun v => by
        rw [map_add, LinearMap.add_apply, hA, hA, hA, map_add, LinearMap.add_apply]
      map_smul' := fun c w => h₁.ext fun v => by
        rw [RingHom.id_apply, map_smulₛₗ, LinearMap.smul_apply, hA, map_smulₛₗ, LinearMap.smul_apply, hA] }
  have hT : ∀ w v, B₁ (T w) v = B₂ w v := hA
  have hcomm : ∀ g, T ∘ₗ ρ g = ρ g ∘ₗ T := by
    intro g
    ext w
    apply h₁.ext
    intro v
    simp only [LinearMap.comp_apply]
    calc B₁ (T (ρ g w)) v = B₂ (ρ g w) v := hT _ _
      _ = B₂ (ρ g w) (ρ g (ρ g⁻¹ v)) := by rw [rep_apply_inv_apply]
      _ = B₂ w (ρ g⁻¹ v) := i₂ g w _
      _ = B₁ (T w) (ρ g⁻¹ v) := (hT _ _).symm
      _ = B₁ (ρ g (T w)) (ρ g (ρ g⁻¹ v)) := (i₁ g _ _).symm
      _ = B₁ (ρ g (T w)) v := by rw [rep_apply_inv_apply]
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_commute T hcomm
  have hprop : ∀ v w, B₂ v w = conj c * B₁ v w := by
    intro v w
    rw [← hT, hc]
    simp
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine (IsSimpleOrder.bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤) ?_
    apply Subrepresentation.toSubmodule_injective
    ext v
    simp [hcon v]
  obtain ⟨hi1, hr1⟩ := h₁.pos v hv
  obtain ⟨hi2, hr2⟩ := h₂.pos v hv
  have e1 : B₁ v v = ((B₁ v v).re : ℂ) := Complex.ext (by simp) (by simp [hi1])
  have e2 : B₂ v v = ((B₂ v v).re : ℂ) := Complex.ext (by simp) (by simp [hi2])
  refine ⟨(B₂ v v).re / (B₁ v v).re, div_pos hr2 hr1, fun x y => ?_⟩
  have hcv : conj c = (((B₂ v v).re / (B₁ v v).re : ℝ) : ℂ) := by
    have := hprop v v
    rw [e1, e2] at this
    have hne : (((B₁ v v).re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr1.ne'
    push_cast
    rw [eq_div_iff hne]
    exact this.symm
  rw [hprop, hcv]


end Forms

section Existence

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A concrete invariant sesquilinear form on a finite-dimensional complex representation of a finite group:
choose a basis, take the standard Hermitian form on coordinates, and average over `G`. -/
noncomputable def averagedBasisForm (ρ : Representation ℂ G V) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w => ∑ g : G, ∑ i, conj ((Module.finBasis ℂ V).repr (ρ g v) i) *
      (Module.finBasis ℂ V).repr (ρ g w) i)
    (fun x y z => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y z => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem averagedBasisForm_apply (ρ : Representation ℂ G V) (v w : V) :
    averagedBasisForm ρ v w = ∑ g : G, ∑ i, conj ((Module.finBasis ℂ V).repr (ρ g v) i) *
      (Module.finBasis ℂ V).repr (ρ g w) i := rfl

theorem averagedBasisForm_isInvariant (ρ : Representation ℂ G V) :
    IsInvariantForm ρ (averagedBasisForm ρ) := by
  intro h v w
  have key : ∀ (g : G) (x : V), ρ g (ρ h x) = ρ (g * h) x := fun g x => by rw [map_mul]; rfl
  simp only [averagedBasisForm_apply, key]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => rfl)

theorem averagedBasisForm_isPosDefHermitian (ρ : Representation ℂ G V) :
    IsPosDefHermitian (averagedBasisForm ρ) := by
  refine ⟨fun v w => ?_, fun v hv => ?_⟩
  · simp only [averagedBasisForm_apply, map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  · have h : averagedBasisForm ρ v v =
        ((∑ g : G, ∑ i, ‖(Module.finBasis ℂ V).repr (ρ g v) i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [averagedBasisForm_apply, Complex.conj_mul']
      push_cast
      rfl
    rw [h]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    apply Finset.sum_pos'
    · intro g _
      exact Finset.sum_nonneg fun i _ => by positivity
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      have : (Module.finBasis ℂ V).repr v ≠ 0 := by simpa using hv
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp this
      refine Finset.sum_pos' (fun i _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
      have h2 : 0 < ‖(Module.finBasis ℂ V).repr v i‖ := norm_pos_iff.mpr hi
      simpa using pow_pos h2 2

/-- Existence half of Etingof et al., Theorem 3.11 for an arbitrary finite-dimensional complex representation
of a finite group (no inner product assumed beforehand): there is an invariant positive definite Hermitian
form. -/
theorem exists_invariantPosDefHermitian (ρ : Representation ℂ G V) :
    ∃ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, IsPosDefHermitian B ∧ IsInvariantForm ρ B :=
  ⟨averagedBasisForm ρ, averagedBasisForm_isPosDefHermitian ρ, averagedBasisForm_isInvariant ρ⟩

end Existence

section ConjugateRep

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- The complex conjugate representation: `G` acts on the conjugate space by the same maps. -/
noncomputable def conjRepresentation (ρ : Representation ℂ G V) : Representation ℂ G (ConjSpace V) where
  toFun g :=
    { toFun := fun x => ConjSpace.mk (ρ g x.val)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        show ConjSpace.mk (ρ g (starRingEnd ℂ c • x.val)) = _
        rw [map_smul]; rfl }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp] theorem conjRepresentation_val (ρ : Representation ℂ G V) (g : G) (x : ConjSpace V) :
    (conjRepresentation ρ g x).val = ρ g x.val := rfl

variable [Fintype G] [FiniteDimensional ℂ V]

/-- **Etingof et al., §3.6**: for a finite group, the complex conjugate of a finite-dimensional complex
representation is isomorphic to its dual (the isomorphism comes from an invariant positive definite
Hermitian form, `x ↦ B x ·`). -/
@[kb "etingof2011" "§3.6, p. 39"]
theorem nonempty_equiv_conj_dual (ρ : Representation ℂ G V) :
    Nonempty (Representation.Equiv (conjRepresentation ρ) ρ.dual) := by
  obtain ⟨B, hB, hinv⟩ := exists_invariantPosDefHermitian ρ
  have hint : ∀ (g : G) (x : ConjSpace V),
      toDualConj B (conjRepresentation ρ g x) = ρ.dual g (toDualConj B x) := by
    intro g x
    ext v
    simp only [toDualConj_apply, conjRepresentation_val, Representation.dual_apply]
    show B (ρ g x.val) v = (toDualConj B x) (ρ g⁻¹ v)
    have := hinv g x.val (ρ g⁻¹ v)
    rw [rep_apply_inv_apply] at this
    rw [toDualConj_apply]
    exact this
  let f : IntertwiningMap (conjRepresentation ρ) ρ.dual :=
    (toDualConj B).intertwiningMap_of_isIntertwiningMap _ _ hint
  obtain ⟨hfin, hrank⟩ := ConjSpace.finrank_eq (V := V)
  have hinj : Function.Injective (toDualConj B) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply ConjSpace.val_injective
    exact hB.eq_zero fun v => by rw [← toDualConj_apply, hx]; rfl
  have hsurj : Function.Surjective (toDualConj B) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hrank, Subspace.dual_finrank_eq])).mp hinj
  exact ⟨f.ofBijective ⟨hinj, hsurj⟩⟩

end ConjugateRep


section Types

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A bilinear form on a representation is invariant if every `ρ g` preserves it. -/
def IsInvariantBilinForm (ρ : Representation k G V) (B : LinearMap.BilinForm k V) : Prop :=
  ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w

/-- **Etingof et al., §4.1**: a representation is of complex type if it is not isomorphic to its dual.
(The book applies the trichotomy to irreducible complex representations.) -/
@[kb "etingof2011" "§4.1, p. 47"]
def IsComplexType (ρ : Representation k G V) : Prop :=
  ¬ Nonempty (Representation.Equiv ρ ρ.dual)

/-- **Etingof et al., §4.1**: a representation is of real type if it carries an invariant nondegenerate
symmetric bilinear form. -/
@[kb "etingof2011" "§4.1, p. 47"]
def IsRealType (ρ : Representation k G V) : Prop :=
  ∃ B : LinearMap.BilinForm k V, B.Nondegenerate ∧ (∀ v w, B v w = B w v) ∧ IsInvariantBilinForm ρ B

/-- **Etingof et al., §4.1**: a representation is of quaternionic type if it carries an invariant
nondegenerate skew-symmetric bilinear form. -/
@[kb "etingof2011" "§4.1, p. 47"]
def IsQuaternionicType (ρ : Representation k G V) : Prop :=
  ∃ B : LinearMap.BilinForm k V, B.Nondegenerate ∧ (∀ v w, B v w = - B w v) ∧ IsInvariantBilinForm ρ B

/-- A finite-dimensional representation with an invariant nondegenerate bilinear form is isomorphic to its
dual (via `v ↦ B v ·`). -/
theorem nonempty_equiv_dual_of_invariantForm [FiniteDimensional k V] {ρ : Representation k G V}
    {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate) (hinv : IsInvariantBilinForm ρ B) :
    Nonempty (Representation.Equiv ρ ρ.dual) := by
  have hint : ∀ (g : G) (v : V), (B.toDual hB) (ρ g v) = ρ.dual g ((B.toDual hB) v) := by
    intro g v
    ext w
    have := hinv g v (ρ g⁻¹ w)
    rw [show ρ g (ρ g⁻¹ w) = w by rw [← mul_apply_eq_comp, ← map_mul]; simp] at this
    rw [LinearMap.BilinForm.toDual_def, Representation.dual_apply]
    exact this
  let f : IntertwiningMap ρ ρ.dual :=
    (B.toDual hB : V →ₗ[k] Module.Dual k V).intertwiningMap_of_isIntertwiningMap _ _ hint
  exact ⟨f.ofBijective (B.toDual hB).bijective⟩

/-- A representation of real type is not of complex type. -/
theorem IsRealType.not_isComplexType [FiniteDimensional k V] {ρ : Representation k G V}
    (h : IsRealType ρ) : ¬ IsComplexType ρ := by
  obtain ⟨B, hB, -, hinv⟩ := h
  exact fun hc => hc (nonempty_equiv_dual_of_invariantForm hB hinv)

/-- A representation of quaternionic type is not of complex type. -/
theorem IsQuaternionicType.not_isComplexType [FiniteDimensional k V] {ρ : Representation k G V}
    (h : IsQuaternionicType ρ) : ¬ IsComplexType ρ := by
  obtain ⟨B, hB, -, hinv⟩ := h
  exact fun hc => hc (nonempty_equiv_dual_of_invariantForm hB hinv)

end Types

section FrobeniusSchurZero

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Orthogonality of the matrix elements of an irreducible representation `ρ` against those of its dual when
`ρ` is not isomorphic to its dual (only irreducibility of `ρ` is needed, since a nonzero intertwiner
`ρ* → ρ` is surjective, hence bijective for dimension reasons). -/
theorem sum_matrix_mul_dual_eq_zero (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (hne : ¬ Nonempty (Representation.Equiv ρ ρ.dual)) (i l : Fin (finrank ℂ V)) :
    ∑ g : G, LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ g) i l *
      LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ g) l i = 0 := by
  classical
  set b := Module.finBasis ℂ V with hb
  set A : Module.Dual ℂ V →ₗ[ℂ] V := (b.dualBasis.coord i).smulRight (b l) with hA
  have hint : ∀ (g : G) (v : Module.Dual ℂ V),
      averageMap ρ ρ.dual A (ρ.dual g v) = ρ g (averageMap ρ ρ.dual A v) := fun g v =>
    congrArg (fun φ : Module.Dual ℂ V →ₗ[ℂ] V => φ v) (averageMap_comp ρ ρ.dual A g)
  let f : IntertwiningMap ρ.dual ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap (ρ := ρ.dual) (σ := ρ) (averageMap ρ ρ.dual A) hint
  have hf0 : f = 0 := by
    rcases IsIrreducible.surjective_or_eq_zero (ρ := ρ) (σ := ρ.dual) f with hs | h0
    · exfalso
      have hinj : Function.Injective f.toLinearMap :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
          (by rw [Subspace.dual_finrank_eq])).mpr hs
      exact hne ⟨(f.ofBijective ⟨hinj, hs⟩).symm⟩
    · exact h0
  have hz : averageMap ρ ρ.dual A (b.dualBasis l) = 0 :=
    congrArg (fun f : IntertwiningMap ρ.dual ρ => f (b.dualBasis l)) hf0
  have := averageMap_entry ρ ρ.dual b b.dualBasis i l i l
  rw [hz] at this
  have hdual : ∀ g : G, LinearMap.toMatrix b.dualBasis b.dualBasis (ρ.dual g⁻¹) i l =
      LinearMap.toMatrix b b (ρ g) l i := by
    intro g
    rw [Representation.dual_apply, inv_inv, LinearMap.toMatrix_transpose]
    rfl
  simp only [hdual] at this
  simpa using this.symm

/-- **Etingof et al., Definition 4.3** (the vanishing case): for an irreducible finite-dimensional complex
representation that is not isomorphic to its dual (complex type), the Frobenius-Schur sum
`∑_g χ(g²)` is zero, so the indicator `|G|⁻¹ ∑_g χ(g²)` is `0`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
theorem sum_character_sq_eq_zero (ρ : Representation ℂ G V) [IsIrreducible ρ] (hc : IsComplexType ρ) :
    ∑ g : G, ρ.character (g ^ 2) = 0 := by
  classical
  set b := Module.finBasis ℂ V with hb
  have htr : ∀ g : G, ρ.character (g ^ 2) =
      ∑ i, ∑ l, LinearMap.toMatrix b b (ρ g) i l * LinearMap.toMatrix b b (ρ g) l i := by
    intro g
    rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, pow_two, map_mul,
      LinearMap.toMatrix_mul, Matrix.trace]
    simp [Matrix.mul_apply]
  simp only [htr]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun l _ => sum_matrix_mul_dual_eq_zero ρ hc i l

/-- **Etingof et al., Definition 4.3** (normalised form of the vanishing case): the indicator
`|G|⁻¹ ∑_g χ(g²)` of an irreducible representation of complex type is `0`. -/
@[kb "etingof2011" "Definition 4.3, p. 47"]
theorem card_inv_mul_sum_character_sq_eq_zero (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (hc : IsComplexType ρ) : (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character (g ^ 2) = 0 := by
  rw [sum_character_sq_eq_zero ρ hc, mul_zero]

end FrobeniusSchurZero

section GroupDeterminant

open MvPolynomial

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G] (R : Type*) [CommRing R]

/-- The matrix `(x_{gh})_{g,h ∈ G}` with entries the independent variables `x_g` of a polynomial ring. -/
noncomputable def groupMatrix : Matrix G G (MvPolynomial G R) := Matrix.of fun g h => X (g * h)

/-- **Etingof et al., Definition 4.6**: the Frobenius (group) determinant, the determinant of the matrix
`(x_{gh})` as a polynomial in the variables `x_g`, `g ∈ G`. (The matrix is indexed by `G` itself rather than
by an enumeration `g₁, …, gₙ`; a common reordering of rows and columns does not change a determinant.) -/
@[kb "etingof2011" "Definition 4.6, p. 48"]
noncomputable def groupDeterminant : MvPolynomial G R := (groupMatrix G R).det

variable {G R}

/-- Evaluating the group determinant at `a : G → R` gives the determinant of the numerical matrix
`(a (g h))`. -/
theorem eval_groupDeterminant (a : G → R) :
    eval a (groupDeterminant G R) = (Matrix.of fun g h : G => a (g * h)).det := by
  rw [groupDeterminant, RingHom.map_det]
  congr 1
  ext g h
  simp [groupMatrix]

variable (G R) in
/-- The group determinant is homogeneous of degree `|G|`. -/
theorem groupDeterminant_isHomogeneous : (groupDeterminant G R).IsHomogeneous (Fintype.card G) := by
  rw [groupDeterminant, Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : (∏ i : G, X (σ i * i) : MvPolynomial G R).IsHomogeneous (Fintype.card G) := by
    have := IsHomogeneous.prod (Finset.univ : Finset G) (fun i : G => (X (σ i * i) : MvPolynomial G R))
      (fun _ => 1) (fun i _ => isHomogeneous_X R _)
    simpa using this
  have hC := (isHomogeneous_C G (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R)).mul hprod
  rw [zero_add] at hC
  rw [Units.smul_def, zsmul_eq_mul]
  simpa [groupMatrix] using hC

end GroupDeterminant

section AlgebraicConjugates

open Polynomial IntermediateField

/-- **Etingof et al., Lemma 4.14**: let `x₁, …, xₙ` be algebraic over `F` (inside some extension `E`) and let
`β` be a root, in an algebraically closed field `K`, of the minimal polynomial of `x₁ + ⋯ + xₙ`. Then
`β = y₁ + ⋯ + yₙ` where each `yᵢ` is a root of the minimal polynomial of `xᵢ`. -/
@[kb "etingof2011" "Lemma 4.14, p. 51"]
theorem exists_conj_sum {F E K ι : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [IsAlgClosed K] [Fintype ι] (x : ι → E) (hx : ∀ i, IsAlgebraic F (x i)) {β : K}
    (hβ : aeval β (minpoly F (∑ i, x i)) = 0) :
    ∃ y : ι → K, (∀ i, aeval (y i) (minpoly F (x i)) = 0) ∧ β = ∑ i, y i := by
  classical
  set S : Set E := Set.range x with hS
  have hK : ∀ s ∈ S, IsIntegral F s ∧ ((minpoly F s).map (algebraMap F K)).Splits := by
    rintro s ⟨i, rfl⟩
    exact ⟨(isAlgebraic_iff_isIntegral).mp (hx i), IsAlgClosed.splits _⟩
  have hmem : ∀ i, x i ∈ adjoin F S := fun i => subset_adjoin F S ⟨i, rfl⟩
  have hsum : (∑ i, x i) ∈ adjoin F S := sum_mem fun i _ => hmem i
  obtain ⟨φ, hφ⟩ := exists_algHom_adjoin_of_splits_of_aeval hK hsum hβ
  refine ⟨fun i => φ ⟨x i, hmem i⟩, fun i => ?_, ?_⟩
  · have h1 : aeval (⟨x i, hmem i⟩ : adjoin F S) (minpoly F (x i)) = 0 := by
      apply (adjoin F S).val.injective
      have h := Polynomial.aeval_algHom_apply (adjoin F S).val (⟨x i, hmem i⟩ : adjoin F S)
        (minpoly F (x i))
      refine h.symm.trans ((minpoly.aeval F (x i)).trans (map_zero _).symm)
    rw [Polynomial.aeval_algHom_apply, h1, map_zero]
  · rw [← hφ]
    have : (⟨∑ i, x i, hsum⟩ : adjoin F S) = ∑ i, (⟨x i, hmem i⟩ : adjoin F S) := by
      apply Subtype.ext
      simp
    rw [this, map_sum]

/-- **Etingof et al., Lemma 4.14** in terms of conjugate roots (same field, e.g. algebraic numbers in `ℂ`
over `ℚ`): every conjugate of a sum of algebraic elements is the sum of conjugates of the summands. -/
@[kb "etingof2011" "Lemma 4.14, p. 51"]
theorem exists_isConjRoot_sum {F A ι : Type*} [Field F] [Field A] [Algebra F A] [IsAlgClosed A]
    [Fintype ι] (x : ι → A) (hx : ∀ i, IsAlgebraic F (x i)) {β : A}
    (hβ : IsConjRoot F (∑ i, x i) β) :
    ∃ y : ι → A, (∀ i, IsConjRoot F (x i) (y i)) ∧ β = ∑ i, y i := by
  obtain ⟨y, hy, hsum⟩ := exists_conj_sum x hx (hβ.aeval_eq_zero)
  exact ⟨y, fun i => isConjRoot_of_aeval_eq_zero ((isAlgebraic_iff_isIntegral).mp (hx i)) (hy i), hsum⟩

end AlgebraicConjugates

end UndergradKB.RepresentationTheory
