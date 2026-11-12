import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.CharactersMore
import UndergradKB.RepresentationTheory.CharactersChapter4
import UndergradKB.RepresentationTheory.Products

/-! # The group determinant factors into irreducibles (Etingof et al., Theorem 4.7)

Let `G` be a finite group and let `V₁, …, Vᵣ` be a complete list of pairwise non-isomorphic irreducible complex
representations.  For each `Vᵢ` put `Pᵢ(x) = det (∑_g x_g ρᵢ(g))`, a polynomial in the variables `x_g`.  We prove:

* `groupDeterminant_eq`: the group determinant equals `ε ∏ᵢ Pᵢ ^ dim Vᵢ`, where `ε = ±1` is the sign of the
  inversion permutation of `G` (the sign arises because the matrix `(x_{gh})` is the matrix of the regular
  representation only after the columns are reindexed by `h ↦ h⁻¹`; the book glosses over it);
* `nonempty_equiv_of_groupPoly_eq_smul`: if `Pᵢ` and `Pⱼ` are proportional then `Vᵢ ≅ Vⱼ`.

The factorization uses the algebra isomorphism `ℂ[G] ≅ ∏ᵢ End Vᵢ`, obtained from injectivity (via the orthogonality
relations for characters) and the dimension count `∑ (dim Vᵢ)² = |G|`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open Module

section DetPi

universe u v

variable {k : Type*} [Field k]

theorem det_pi_hetero_aux (ι : Type u) [Fintype ι] : ∀ (M : ι → Type v) [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] [∀ i, FiniteDimensional k (M i)] (f : ∀ i, M i →ₗ[k] M i),
    (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)).det = ∏ i, (f i).det := by
  refine Fintype.induction_empty_option (P := fun ι _ => ∀ (M : ι → Type v) [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] [∀ i, FiniteDimensional k (M i)] (f : ∀ i, M i →ₗ[k] M i),
    (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)).det = ∏ i, (f i).det) ?_ ?_ ?_ ι
  · intro α β _ e ih M _ _ _ f
    classical
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    let Φ := LinearEquiv.piCongrLeft k M e
    have h : (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
        Φ.toLinearMap ∘ₗ (LinearMap.pi fun a => (f (e a)).comp (LinearMap.proj a)) ∘ₗ Φ.symm.toLinearMap := by
      refine LinearMap.ext fun x => funext fun b => ?_
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.pi_apply,
        LinearMap.proj_apply]
      change _ = Equiv.piCongrLeft M e _ (e a)
      rw [Equiv.piCongrLeft_apply_apply]
      congr 1
    rw [h, LinearMap.det_conj _ Φ, ih (fun a => M (e a)) (fun a => f (e a))]
    exact Fintype.prod_equiv e _ _ (fun a => rfl)
  · intro M _ _ _ f
    simp [LinearMap.det_eq_one_of_subsingleton]
  · intro α _ ih M _ _ _ f
    let E := LinearEquiv.piOptionEquivProd k (M := M)
    have h : (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)) =
        E.symm.toLinearMap ∘ₗ (LinearMap.prodMap (f none)
          (LinearMap.pi fun i : α => (f (some i)).comp (LinearMap.proj i))) ∘ₗ E.symm.symm.toLinearMap := by
      ext x i
      cases i <;> simp [E, LinearEquiv.piOptionEquivProd]
    rw [h, LinearMap.det_conj _ E.symm, LinearMap.det_prodMap,
      ih (fun i => M (some i)) (fun i => f (some i)), Fintype.prod_option]

/-- The determinant of a "diagonal" endomorphism of a finite product of finite-dimensional spaces is the product
of the determinants of its components. -/
theorem det_pi_hetero {ι : Type u} [Fintype ι] {M : ι → Type v} [∀ i, AddCommGroup (M i)]
    [∀ i, Module k (M i)] [∀ i, FiniteDimensional k (M i)] (f : ∀ i, M i →ₗ[k] M i) :
    (LinearMap.pi fun i => (f i).comp (LinearMap.proj i)).det = ∏ i, (f i).det :=
  det_pi_hetero_aux ι M f

end DetPi

section DetEnd

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Left multiplication by `A` on `End V` has determinant `det A ^ dim V`. -/
theorem det_mulLeft_end (A : V →ₗ[k] V) :
    (LinearMap.mulLeft k A).det = A.det ^ finrank k V := by
  classical
  let b := Free.chooseBasis k V
  let e : (Free.ChooseBasisIndex k V → V) ≃ₗ[k] (V →ₗ[k] V) := b.constr k
  have h : LinearMap.mulLeft k A =
      e.toLinearMap ∘ₗ (LinearMap.pi fun i : Free.ChooseBasisIndex k V => A ∘ₗ LinearMap.proj i) ∘ₗ
        e.symm.toLinearMap := by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    conv_rhs => rw [show (LinearMap.pi fun i : Free.ChooseBasisIndex k V => A ∘ₗ LinearMap.proj i)
      (e.symm f) = A ∘ e.symm f from rfl]
    rw [show e (A ∘ e.symm f) = A.comp (e (e.symm f)) from Basis.constr_comp b k A _]
    simp only [LinearEquiv.apply_symm_apply, LinearMap.mulLeft_apply]
    rfl
  rw [h, LinearMap.det_conj _ e, LinearMap.det_pi (fun _ => A)]
  simp [Module.finrank_eq_card_chooseBasisIndex]

end DetEnd

open Representation
open scoped MonoidAlgebra

section Regular

universe w

variable {G : Type w} [Group G] [Fintype G] {ι : Type*} [Fintype ι] (X : ι → IrrRep ℂ G)

/-- The action of the group algebra on a family of irreducible representations. -/
noncomputable def actionRep : ℂ[G] →ₐ[ℂ] ∀ i, Module.End ℂ (X i).V :=
  AlgHom.pi fun i => (X i).ρ.asAlgebraHom

theorem actionRep_apply (a : ℂ[G]) (i : ι) : actionRep X a i = (X i).ρ.asAlgebraHom a := rfl

open scoped Classical in
/-- Orthogonality in the form used for injectivity: `∑ᵢ dim Vᵢ · χᵢ(x) = |G| δ_{x,1}`. -/
theorem sum_finrank_mul_character
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) (x : G) :
    ∑ i, (finrank ℂ (X i).V : ℂ) * (X i).ρ.character x = if x = 1 then (Nat.card G : ℂ) else 0 := by
  classical
  have hbij : Function.Bijective (fun i => (⟨(X i).ρ.character, X i, rfl⟩ : irrChars ℂ G)) := by
    refine ⟨fun i j h => hinj i j ((nonempty_equiv_iff_character_eq _ _).mpr ?_), fun χ => ?_⟩
    · exact congrArg Subtype.val h
    · obtain ⟨Y, hY⟩ := χ.2
      obtain ⟨i, hi⟩ := hsurj Y
      exact ⟨i, Subtype.ext (((nonempty_equiv_iff_character_eq _ _).mp hi).symm.trans hY)⟩
  have h := sum_irrChars_mul_inv (k := ℂ) (G := G) 1 x⁻¹
  rw [← Fintype.sum_bijective _ hbij (fun i => ((X i).ρ.character 1) * ((X i).ρ.character x)) _
    (fun _ => by simp)] at h
  have hc : Subgroup.centralizer {(1 : G)} = ⊤ := by
    ext y; simp [Subgroup.mem_centralizer_singleton_iff]
  simp only [char_one, isConj_one_right, inv_eq_one, hc, Subgroup.card_top] at h
  exact h

theorem trace_asAlgebraHom {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (β : ℂ[G]) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom β) = ∑ g, β.coeff g * ρ.character g := by
  classical
  induction β using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, hx, hy, MonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  | single g c =>
    rw [asAlgebraHom_single, map_smul]
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, Representation.character]

theorem eq_zero_of_actionRep_eq_zero
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ))
    (α : ℂ[G]) (h : actionRep X α = 0) : α = 0 := by
  classical
  ext g
  have key : ∀ h : G, (Nat.card G : ℂ) * α.coeff h⁻¹ = 0 := by
    intro h'
    have h1 : ∀ i, (X i).ρ.asAlgebraHom (α * MonoidAlgebra.single h' 1) = 0 := by
      intro i
      rw [map_mul, show (X i).ρ.asAlgebraHom α = 0 from congrFun h i, zero_mul]
    have h2 : ∑ i, (finrank ℂ (X i).V : ℂ) *
        LinearMap.trace ℂ (X i).V ((X i).ρ.asAlgebraHom (α * MonoidAlgebra.single h' 1)) = 0 := by
      simp [h1]
    simp only [trace_asAlgebraHom, Finset.mul_sum] at h2
    rw [Finset.sum_comm] at h2
    have h3 : ∀ g : G, ∑ i, (finrank ℂ (X i).V : ℂ) *
        ((α * MonoidAlgebra.single h' 1).coeff g * (X i).ρ.character g) =
        (α * MonoidAlgebra.single h' 1).coeff g * (if g = 1 then (Nat.card G : ℂ) else 0) := by
      intro g
      rw [← sum_finrank_mul_character X hinj hsurj g, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [h3] at h2
    simpa [mul_comm] using h2
  have := key g⁻¹
  rw [inv_inv] at this
  have hne : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simpa [hne] using this

theorem actionRep_bijective
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    Function.Bijective (actionRep X) := by
  have hi : Function.Injective (actionRep X) :=
    (injective_iff_map_eq_zero _).mpr fun a ha => eq_zero_of_actionRep_eq_zero X hinj hsurj a ha
  refine ⟨hi, ?_⟩
  have h1 : finrank ℂ ℂ[G] = Nat.card G := by
    rw [(MonoidAlgebra.coeffLinearEquiv ℂ).finrank_eq, Module.finrank_finsupp_self, Nat.card_eq_fintype_card]
  have h2 : finrank ℂ (∀ i, Module.End ℂ (X i).V) = Nat.card G := by
    rw [Module.finrank_pi_fintype, ← sum_finrank_sq X hinj hsurj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.finrank_linearMap, sq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h1.trans h2.symm)
    (f := (actionRep X).toLinearMap)).mp hi

/-- The linear isomorphism `ℂ[G] ≅ ∏ᵢ End Vᵢ` (Wedderburn) for a complete family of irreducible
representations. -/
noncomputable def actionRepEquiv
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    ℂ[G] ≃ₗ[ℂ] ∀ i, Module.End ℂ (X i).V :=
  LinearEquiv.ofBijective (actionRep X).toLinearMap (actionRep_bijective X hinj hsurj)

/-- Left multiplication by `α ∈ ℂ[G]` has determinant `∏ᵢ det (ρᵢ α) ^ dim Vᵢ`. -/
theorem det_mulLeft_eq_prod
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) (α : ℂ[G]) :
    (LinearMap.mulLeft ℂ α).det = ∏ i, ((X i).ρ.asAlgebraHom α).det ^ finrank ℂ (X i).V := by
  let e := actionRepEquiv X hinj hsurj
  have h : LinearMap.mulLeft ℂ α = e.symm.toLinearMap ∘ₗ
      (LinearMap.pi fun i => (LinearMap.mulLeft ℂ ((X i).ρ.asAlgebraHom α)) ∘ₗ LinearMap.proj i) ∘ₗ
        e.symm.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    change actionRep X (α * y) i = (X i).ρ.asAlgebraHom α * actionRep X y i
    rw [map_mul]
    rfl
  rw [h, LinearMap.det_conj _ e.symm, det_pi_hetero]
  exact Finset.prod_congr rfl fun i _ => det_mulLeft_end _

end Regular

section LinearSubstitution

open MvPolynomial

variable {K : Type*} [Field K] {α β : Type*}

/-- Substituting homogeneous linear forms does not increase the total degree. -/
theorem totalDegree_aeval_le (g : α → MvPolynomial β K) (hg : ∀ a, (g a).IsHomogeneous 1)
    (p : MvPolynomial α K) : (aeval g p).totalDegree ≤ p.totalDegree := by
  have hsum := congrArg (aeval g) (sum_homogeneousComponent p)
  rw [map_sum] at hsum
  rw [← hsum]
  refine totalDegree_finsetSum_le fun i hi => ?_
  have h1 : (aeval g (homogeneousComponent i p)).IsHomogeneous (1 * i) :=
    (homogeneousComponent_isHomogeneous i p).aeval g hg
  exact h1.totalDegree_le.trans (by rw [one_mul]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- If `D` is irreducible and the substitution `aeval ℓ` by homogeneous linear forms has a left inverse
`aeval m` (again a substitution by homogeneous linear forms), then `aeval ℓ D` is irreducible. -/
theorem irreducible_aeval_of_retraction (ℓ : α → MvPolynomial β K) (m : β → MvPolynomial α K)
    (hℓ : ∀ a, (ℓ a).IsHomogeneous 1) (hm : ∀ b, (m b).IsHomogeneous 1)
    (h : ∀ a, aeval m (ℓ a) = X a) {D : MvPolynomial α K} (hD : Irreducible D) :
    Irreducible (aeval ℓ D) := by
  have hcomp : ∀ p, aeval m (aeval ℓ p) = p := by
    intro p
    have : (aeval m).comp (aeval ℓ) = AlgHom.id K (MvPolynomial α K) := by
      refine MvPolynomial.algHom_ext fun a => ?_
      rw [AlgHom.comp_apply, aeval_X, h]
      rfl
    exact congrArg (fun F => F p) this
  have hD0 : D ≠ 0 := hD.ne_zero
  -- a factor whose image is a unit is a unit
  have key : ∀ a b : MvPolynomial β K, aeval ℓ D = a * b → IsUnit (aeval m a) → IsUnit a := by
    intro a b hab hua
    have hDab : D = aeval m a * aeval m b := by
      rw [← map_mul, ← hab, hcomp]
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := congrArg (aeval m) hab
      rw [hcomp, zero_mul, map_zero] at this
      exact hD0 this
    have hb0 : b ≠ 0 := by
      rintro rfl
      have := congrArg (aeval m) hab
      rw [hcomp, mul_zero, map_zero] at this
      exact hD0 this
    have hsa : aeval m a ≠ 0 := hua.ne_zero
    have hsb : aeval m b ≠ 0 := by
      intro h0
      exact hD0 (by rw [hDab, h0, mul_zero])
    have hta : (aeval m a).totalDegree = 0 := ((isUnit_iff_totalDegree_of_isReduced).mp hua).2
    have h1 : D.totalDegree = (aeval m b).totalDegree := by
      rw [hDab, totalDegree_mul_of_isDomain hsa hsb, hta, zero_add]
    have h2 : (aeval ℓ D).totalDegree ≤ D.totalDegree := totalDegree_aeval_le ℓ hℓ D
    have h3 : (aeval m b).totalDegree ≤ b.totalDegree := totalDegree_aeval_le m hm b
    rw [hab, totalDegree_mul_of_isDomain ha0 hb0] at h2
    have hta' : a.totalDegree = 0 := by omega
    have := totalDegree_eq_zero_iff_eq_C.mp hta'
    have hc : a.coeff 0 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at this
      exact ha0 this
    exact (isUnit_iff_totalDegree_of_isReduced).mpr ⟨isUnit_iff_ne_zero.mpr hc, hta'⟩
  refine ⟨fun hu => hD.not_isUnit ?_, fun a b hab => ?_⟩
  · have := hu.map (aeval m)
    rwa [hcomp] at this
  · have hDab : D = aeval m a * aeval m b := by
      rw [← map_mul, ← hab, hcomp]
    rcases hD.isUnit_or_isUnit hDab with h1 | h1
    · exact Or.inl (key a b hab h1)
    · exact Or.inr (key b a (by rw [hab, mul_comm]) h1)

end LinearSubstitution

section Polynomials

open MvPolynomial

universe w'

variable {G : Type w'} [Group G] [Fintype G]

/-- The basis `{g}` of the group algebra. -/
noncomputable def regBasis : Basis G ℂ ℂ[G] :=
  (Finsupp.basisSingleOne (R := ℂ) (ι := G)).map (MonoidAlgebra.coeffLinearEquiv ℂ).symm

theorem regBasis_repr (y : ℂ[G]) (g : G) : (regBasis (G := G)).repr y g = y.coeff g := by
  simp [regBasis]

theorem regBasis_apply (g : G) : (regBasis (G := G)) g = MonoidAlgebra.single g 1 := by
  simp [regBasis]

theorem toMatrix_mulLeft_regBasis [DecidableEq G] (α : ℂ[G]) :
    LinearMap.toMatrix regBasis regBasis (LinearMap.mulLeft ℂ α) =
      Matrix.of fun g h : G => α.coeff (g * h⁻¹) := by
  ext g h
  rw [LinearMap.toMatrix_apply, regBasis_repr, regBasis_apply]
  simp only [LinearMap.mulLeft_apply, Matrix.of_apply]
  have := MonoidAlgebra.coeff_mul_single_mul α (1 : ℂ) h (g * h⁻¹)
  rw [inv_mul_cancel_right, mul_one] at this
  exact this

/-- The polynomial `det (∑_g x_g ρ(g))` in the variables `x_g`, computed in the basis `finBasis` of `V`. -/
noncomputable def groupPoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : MvPolynomial G ℂ :=
  (Matrix.of fun i j : Fin (finrank ℂ V) => ∑ g : G,
    C ((LinearMap.toMatrix (finBasis ℂ V) (finBasis ℂ V) (ρ g)) i j) * X g).det

theorem eval_groupPoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (a : G → ℂ) :
    eval a (groupPoly ρ) = LinearMap.det (∑ g, a g • ρ g) := by
  rw [groupPoly, RingHom.map_det, ← LinearMap.det_toMatrix (finBasis ℂ V)]
  congr 1
  ext i j
  simp [map_sum, LinearMap.toMatrix_apply, Finset.sum_apply, mul_comm]

/-- The element `∑ a_g g` of the group algebra. -/
noncomputable def algElt (a : G → ℂ) : ℂ[G] := ∑ g, MonoidAlgebra.single g (a g)

theorem coeff_algElt (a : G → ℂ) (g : G) : (algElt a).coeff g = a g := by
  classical
  simp [algElt, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem asAlgebraHom_algElt {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (a : G → ℂ) : ρ.asAlgebraHom (algElt a) = ∑ g, a g • ρ g := by
  simp [algElt, map_sum, asAlgebraHom_single]

/-- **Etingof et al., Theorem 4.7** (factorisation): for a complete family `Vᵢ` of pairwise non-isomorphic
irreducible complex representations of `G`, the group determinant is `ε ∏ᵢ Pᵢ ^ dim Vᵢ` with
`Pᵢ = det (∑_g x_g ρᵢ(g))` and `ε = ±1` the sign of the permutation `g ↦ g⁻¹` of `G` (the book omits this sign:
the matrix `(x_{gh})` is the matrix of left multiplication on `ℂ[G]` only after the columns are reindexed by
`h ↦ h⁻¹`). -/
@[kb "etingof2011" "Theorem 4.7, p. 48"]
theorem groupDeterminant_eq [DecidableEq G] {ι : Type*} [Fintype ι] (X : ι → IrrRep ℂ G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    groupDeterminant G ℂ = C (((Equiv.Perm.sign (Equiv.inv G) : ℤˣ) : ℤ) : ℂ) *
      ∏ i, groupPoly (X i).ρ ^ finrank ℂ (X i).V := by
  refine MvPolynomial.funext fun a => ?_
  rw [eval_groupDeterminant]
  have hM : Matrix.of (fun g h : G => a (g * h)) =
      (Matrix.of fun g h : G => a (g * h⁻¹)).submatrix id (Equiv.inv G) := by
    ext g h
    simp
  have hM' : (Matrix.of fun g h : G => a (g * h⁻¹)) =
      LinearMap.toMatrix regBasis regBasis (LinearMap.mulLeft ℂ (algElt a)) := by
    rw [toMatrix_mulLeft_regBasis]
    ext g h
    simp [coeff_algElt]
  rw [hM, Matrix.det_permute', hM', LinearMap.det_toMatrix, det_mulLeft_eq_prod X hinj hsurj]
  simp [map_mul, map_prod, map_pow, eval_groupPoly, asAlgebraHom_algElt]

/-- **Etingof et al., Theorem 4.7** (irreducibility of the factors): for an irreducible complex representation
`X`, the polynomial `det (∑ x_g ρ_X(g))` is irreducible.  The operators `ρ(g)` span `End V` (density), so the
`n²` linear forms `∑_g ρ(g)_{ij} x_g` in the variables `x_g` admit a linear left inverse, and Lemma 4.8
(irreducibility of the generic determinant) transfers to `groupPoly`. -/
@[kb "etingof2011" "Theorem 4.7, p. 48"]
theorem irreducible_groupPoly (Y : IrrRep ℂ G) : Irreducible (groupPoly Y.ρ) := by
  classical
  let n := finrank ℂ Y.V
  let b := finBasis ℂ Y.V
  let R : G → Matrix (Fin n) (Fin n) ℂ := fun g => LinearMap.toMatrix b b (Y.ρ g)
  have hn : Nonempty (Fin n) := by
    have : Nontrivial Y.V := nontrivial_of_isIrreducible (ρ := Y.ρ)
    exact ⟨⟨0, Module.finrank_pos⟩⟩
  -- the linear forms
  let ℓ : Fin n × Fin n → MvPolynomial G ℂ := fun q => ∑ g, C (R g q.1 q.2) * X g
  have hgp : groupPoly Y.ρ = aeval ℓ (genericDet ℂ (Fin n)) := by
    rw [genericDet, AlgHom.map_det, groupPoly]
    congr 1
    ext i j
    simp [ℓ, R, Matrix.mvPolynomialX, b, n]
  -- matrix units are combinations of the `R g`
  have hspan : ∀ p : Fin n × Fin n, ∃ s : G → ℂ, ∀ q : Fin n × Fin n,
      ∑ g, s g * R g q.1 q.2 = if q = p then 1 else 0 := by
    intro p
    have h1 : (LinearMap.toMatrix b b).symm (Matrix.single p.1 p.2 (1 : ℂ)) ∈
        Submodule.span ℂ (Set.range Y.ρ) := by
      rw [span_range_eq_top Y.ρ]; trivial
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h1
    refine ⟨s, fun q => ?_⟩
    have h2 := congrArg (LinearMap.toMatrix b b) hs
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply] at h2
    have h3 := congrFun (congrFun h2 q.1) q.2
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply] at h3
    rw [show (∑ g, s g * R g q.1 q.2) = _ from h3]
    have : (p.1 = q.1 ∧ p.2 = q.2) ↔ q = p := by simp [Prod.ext_iff, eq_comm]
    exact if_congr this rfl rfl
  choose s hs using hspan
  let m : G → MvPolynomial (Fin n × Fin n) ℂ := fun g => ∑ p, C (s p g) * X p
  have hℓ : ∀ q, (ℓ q).IsHomogeneous 1 := fun q =>
    IsHomogeneous.sum _ _ _ fun g _ => isHomogeneous_C_mul_X _ g
  have hm : ∀ g, (m g).IsHomogeneous 1 := fun g =>
    IsHomogeneous.sum _ _ _ fun p _ => isHomogeneous_C_mul_X _ p
  have h : ∀ q, aeval m (ℓ q) = X q := by
    intro q
    calc aeval m (ℓ q) = ∑ g, C (R g q.1 q.2) * m g := by simp [ℓ]
      _ = ∑ g, ∑ p, C (s p g * R g q.1 q.2) * X p := by
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [m, Finset.mul_sum, map_mul]
        exact Finset.sum_congr rfl fun p _ => by ring
      _ = ∑ p, C (∑ g, s p g * R g q.1 q.2) * X p := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [map_sum, Finset.sum_mul]
      _ = X q := by
        simp only [hs]
        simp [apply_ite C, ite_mul, Finset.sum_ite_eq]
  rw [hgp]
  exact irreducible_aeval_of_retraction ℓ m hℓ hm h (irreducible_genericDet (K := ℂ) (ι := Fin n))

theorem trace_eq_neg_nextCoeff_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : V →ₗ[ℂ] V) : LinearMap.trace ℂ V f = -f.charpoly.nextCoeff := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Free.chooseBasis ℂ V), Matrix.trace_eq_neg_charpoly_nextCoeff,
    ← LinearMap.charpoly_def]

/-- **Etingof et al., Theorem 4.7** (the factors for non-isomorphic representations are not proportional):
if `det (∑ x_g ρ_X(g))` and `det (∑ x_g ρ_Y(g))` are proportional polynomials then `X ≅ Y`. -/
@[kb "etingof2011" "Theorem 4.7, p. 48"]
theorem nonempty_equiv_of_groupPoly_eq {X Y : IrrRep ℂ G} (c : ℂ)
    (h : groupPoly X.ρ = C c * groupPoly Y.ρ) : Nonempty (Representation.Equiv X.ρ Y.ρ) := by
  classical
  have ev : ∀ (s t : ℂ) (g0 : G), LinearMap.det (s • (1 : Module.End ℂ X.V) + t • X.ρ g0) =
      c * LinearMap.det (s • (1 : Module.End ℂ Y.V) + t • Y.ρ g0) := by
    intro s t g0
    have key : ∀ {V : Type _} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
        ∑ g, (Pi.single (1 : G) s + Pi.single g0 t : G → ℂ) g • ρ g = s • (1 : Module.End ℂ V) + t • ρ g0 := by
      intro V _ _ ρ
      simp [add_smul, Finset.sum_add_distrib, Pi.single_apply]
    have := congrArg (eval (Pi.single (1 : G) s + Pi.single g0 t : G → ℂ)) h
    rw [eval_groupPoly, map_mul, eval_C, eval_groupPoly, key, key] at this
    exact this
  have hc : c = 1 := by
    have := ev 1 0 1
    simpa using this.symm
  subst hc
  rw [nonempty_equiv_iff_character_eq]
  funext g0
  have hcp : (X.ρ g0).charpoly = (Y.ρ g0).charpoly := by
    refine Polynomial.funext fun r => ?_
    rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly]
    have := ev r (-1) g0
    rw [one_mul] at this
    simpa [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg] using this
  show LinearMap.trace ℂ X.V (X.ρ g0) = LinearMap.trace ℂ Y.V (Y.ρ g0)
  rw [trace_eq_neg_nextCoeff_charpoly, trace_eq_neg_nextCoeff_charpoly, hcp]

/-- **Etingof et al., Theorem 4.7** (all parts together): for a complete family of pairwise non-isomorphic
irreducible complex representations `Vᵢ`, the group determinant is `ε ∏ᵢ Pᵢ ^ dim Vᵢ`, the `Pᵢ` are
irreducible, and `Pᵢ`, `Pⱼ` are proportional only if `i = j`.  (By Corollary 3.6 the index type has as many
elements as `G` has conjugacy classes.) -/
@[kb "etingof2011" "Theorem 4.7, p. 48"]
theorem groupDeterminant_factorization [DecidableEq G] {ι : Type*} [Fintype ι] (X : ι → IrrRep ℂ G)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsurj : ∀ Y : IrrRep ℂ G, ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ)) :
    groupDeterminant G ℂ = C (((Equiv.Perm.sign (Equiv.inv G) : ℤˣ) : ℤ) : ℂ) *
        ∏ i, groupPoly (X i).ρ ^ finrank ℂ (X i).V ∧
      (∀ i, Irreducible (groupPoly (X i).ρ)) ∧
      (∀ i j (c : ℂ), groupPoly (X i).ρ = C c * groupPoly (X j).ρ → i = j) :=
  ⟨groupDeterminant_eq X hinj hsurj, fun i => irreducible_groupPoly (X i),
    fun i j c h => hinj i j (nonempty_equiv_of_groupPoly_eq c h)⟩

end Polynomials

end UndergradKB.RepresentationTheory
