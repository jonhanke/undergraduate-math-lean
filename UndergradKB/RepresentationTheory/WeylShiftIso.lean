import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Irreducible
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialRepsReducible
import UndergradKB.RepresentationTheory.WeylShift
import UndergradKB.RepresentationTheory.AlgebrasChapter2
import UndergradKB.RepresentationTheory.WeylCharacter
import UndergradKB.RepresentationTheory.FrobeniusTheorem
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The determinant twist as an isomorphism (Etingof et al., Proposition 4.64)

For diagrams `λ`, `μ` with at most `N` rows and `μ_j = λ_j + 1` for `j ≤ N`, the representations `L_μ` and
`L_λ ⊗ Λ^N V` of `GL_N(ℂ)` are isomorphic (`nonempty_equiv_swRepGL_add_one`).

The proof follows the plan of the book through the semisimple algebra `B = End_{S_m}(V^{⊗m})`, `m = |λ| + N`.
Both representations are homogeneous polynomial of degree `m` (`isHomogPolyRep_swRepGL`,
`isHomogPolyRep_tprod`), hence simple modules over `B`.  If they were not isomorphic, the density theorem would give
an element of `B` that is the identity on `L_λ ⊗ Λ^N V` and zero on every `L_ν`; but `B` acts faithfully on
`V^{⊗m} = ⨁ V_ν ⊗ L_ν`, so such an element is zero.  Hence `L_λ ⊗ Λ^N V` is isomorphic to some `L_ν`; comparing
characters at diagonal matrices (`eq_of_weylValue_eq`, via the injectivity of Schur polynomials) gives `ν = μ`.
-/

namespace UndergradKB.RepresentationTheory

open PiTensorProduct
open scoped TensorProduct

section Homog

variable {N : ℕ}

/-- Functions on `GL_N(ℂ)` given by homogeneous polynomials of degree `n` in the matrix entries. -/
def homogFunctions (N n : ℕ) : Submodule ℂ (GL (Fin N) ℂ → ℂ) where
  carrier := {f | ∃ P : MvPolynomial (Fin N × Fin N) ℂ, P.IsHomogeneous n ∧
    ∀ g, f g = MvPolynomial.eval (glEntries N ℂ g) P}
  add_mem' := by
    rintro _ _ ⟨P, hP, hf⟩ ⟨Q, hQ, hg⟩
    exact ⟨P + Q, hP.add hQ, fun g => by simp [hf, hg]⟩
  zero_mem' := ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun g => by simp⟩
  smul_mem' := by
    rintro c _ ⟨P, hP, hf⟩
    refine ⟨MvPolynomial.C c * P, ?_, fun g => by simp [hf]⟩
    simpa using (MvPolynomial.isHomogeneous_C _ c).mul hP

theorem mem_homogFunctions_mul {n n' : ℕ} {f f' : GL (Fin N) ℂ → ℂ} (hf : f ∈ homogFunctions N n)
    (hf' : f' ∈ homogFunctions N n') : (fun g => f g * f' g) ∈ homogFunctions N (n + n') := by
  obtain ⟨P, hP, hf⟩ := hf
  obtain ⟨Q, hQ, hf'⟩ := hf'
  exact ⟨P * Q, hP.mul hQ, fun g => by simp [hf, hf']⟩

theorem isHomogPolyRep_iff {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} :
    IsHomogPolyRep n ρ ↔ ∀ (w : W) (φ : Module.Dual ℂ W), (fun g => φ (ρ g w)) ∈ homogFunctions N n := by
  constructor
  · intro h w φ
    obtain ⟨P, hP, hg⟩ := h w φ
    exact ⟨P, hP, hg⟩
  · intro h w φ
    obtain ⟨P, hP, hg⟩ := h w φ
    exact ⟨P, hP, hg⟩

theorem isHomogPolyRep_of_basis {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ W)
    (h : ∀ i j, (fun g => b.repr (ρ g (b j)) i) ∈ homogFunctions N n) : IsHomogPolyRep n ρ := by
  rw [isHomogPolyRep_iff]
  intro w φ
  have key : (fun g => φ (ρ g w)) =
      ∑ j, b.repr w j • ∑ i, φ (b i) • (fun g => b.repr (ρ g (b j)) i) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have e := congrArg φ (b.sum_repr (ρ g (b j)))
    rw [map_sum] at e
    simp only [map_smul, smul_eq_mul] at e
    rw [← e]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [key]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i j))

theorem isHomogPolyRep_tensorPowerGL (n : ℕ) : IsHomogPolyRep n (tensorPowerGL N ℂ n) := by
  refine isHomogPolyRep_of_basis (Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun ℂ (Fin N))) ?_
  intro I J
  refine ⟨∏ l : Fin n, MvPolynomial.X (I l, J l), ?_, fun g => ?_⟩
  · have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
      (fun l => (MvPolynomial.X (I l, J l) : MvPolynomial (Fin N × Fin N) ℂ)) (fun _ => 1)
      (fun l _ => MvPolynomial.isHomogeneous_X _ _)
    simpa using this
  · simp [tensorPowerGL, tensorPowerMap, Basis.piTensorProduct_apply,
      Basis.piTensorProduct_repr_tprod_apply, glEntries]

theorem isHomogeneous_detPoly : (detPoly N ℂ).IsHomogeneous N := by
  unfold detPoly
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin N))
    (fun i => ((Matrix.mvPolynomialX (Fin N) (Fin N) ℂ) (σ i) i)) (fun _ => 1)
    (fun i _ => by simpa [Matrix.mvPolynomialX] using MvPolynomial.isHomogeneous_X ℂ (σ i, i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  rw [Units.smul_def, zsmul_eq_mul]
  have h0 : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin N × Fin N) ℂ).IsHomogeneous 0 := by
    have := MvPolynomial.isHomogeneous_C (Fin N × Fin N) ((Equiv.Perm.sign σ : ℤ) : ℂ)
    simpa using this
  simpa using h0.mul h

theorem isHomogPolyRep_detRep : IsHomogPolyRep N (detRep N ℂ 1) := by
  rw [isHomogPolyRep_iff]
  intro w φ
  rw [detRep_coeff]
  refine Submodule.smul_mem _ _ ?_
  exact ⟨detPoly N ℂ, isHomogeneous_detPoly, fun g => by simp [eval_detPoly]⟩

theorem isHomogPolyRep_tprod {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ W'] {n n' : ℕ}
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} {ρ' : Representation ℂ (GL (Fin N) ℂ) W'}
    (h : IsHomogPolyRep n ρ) (h' : IsHomogPolyRep n' ρ') : IsHomogPolyRep (n' + n) (ρ.tprod ρ') := by
  refine isHomogPolyRep_of_basis ((Module.finBasis ℂ W).tensorProduct (Module.finBasis ℂ W')) ?_
  rintro ⟨i, i'⟩ ⟨j, j'⟩
  have e1 := (isHomogPolyRep_iff.1 h) (Module.finBasis ℂ W j) ((Module.finBasis ℂ W).coord i)
  have e2 := (isHomogPolyRep_iff.1 h') (Module.finBasis ℂ W' j') ((Module.finBasis ℂ W').coord i')
  have := mem_homogFunctions_mul e2 e1
  convert this using 1
  funext g
  simp [Module.Basis.tensorProduct_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply]

/-- The additive group structure on the multiplicity space `L_λ` (it is a `ℂ`-vector space). -/
noncomputable instance instAddCommGroupSwHom (n : ℕ) (la : DiagramsOfSize n) :
    AddCommGroup (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule (Fin N → ℂ) n) :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem isHomogPolyRep_swRepGL (n : ℕ) (la : DiagramsOfSize n) : IsHomogPolyRep n (swRepGL N n la) := by
  let b := Module.finBasis ℂ (spechtModule la)
  let F : (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule (Fin N → ℂ) n) →ₗ[ℂ]
      (Fin (Module.finrank ℂ (spechtModule la)) → ⨂[ℂ] _ : Fin n, Fin N → ℂ) :=
    { toFun := fun f i => f (b i)
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  have hF : Function.Injective F := by
    intro f f' h
    have h' : f.restrictScalars ℂ = f'.restrictScalars ℂ := b.ext fun i => congrFun h i
    exact LinearMap.ext fun x => LinearMap.congr_fun h' x
  rw [isHomogPolyRep_iff]
  intro f φ
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective F (LinearMap.ker_eq_bot.mpr hF)
  have key : (fun g => φ (swRepGL N n la g f)) =
      ∑ i, (fun g => (φ ∘ₗ l ∘ₗ LinearMap.single ℂ (fun _ => ⨂[ℂ] _ : Fin n, Fin N → ℂ) i)
        (tensorPowerGL N ℂ n g (F f i))) := by
    funext g
    have h1 : φ (swRepGL N n la g f) = (φ ∘ₗ l) (F (swRepGL N n la g f)) := by
      simp only [LinearMap.comp_apply]
      exact (congrArg φ (LinearMap.congr_fun hl _)).symm
    have h2 : F (swRepGL N n la g f) = fun i => tensorPowerGL N ℂ n g (F f i) := rfl
    rw [h1, h2]
    simp only [Finset.sum_apply]
    conv_lhs => rw [← Finset.univ_sum_single (fun i => tensorPowerGL N ℂ n g (F f i))]
    rw [map_sum]
    rfl
  rw [key]
  exact Submodule.sum_mem _ fun i _ => isHomogPolyRep_iff.1 (isHomogPolyRep_tensorPowerGL n) _ _

end Homog

section SchurInj

open Finset

variable {N m : ℕ}

theorem perm_eq_one_of_strictAnti {s t : Fin N → ℕ} (hs : StrictAnti s) (ht : StrictAnti t)
    {σ : Equiv.Perm (Fin N)} (h : s = t ∘ σ) : σ = 1 := by
  have hm : StrictMono σ := by
    intro i j hij
    have h1 : s j < s i := hs hij
    rw [h] at h1
    exact ht.lt_iff_gt.1 h1
  let e : Fin N ≃o Fin N := ⟨σ, hm.le_iff_le⟩
  have : e = OrderIso.refl _ := Subsingleton.elim _ _
  refine Equiv.ext fun i => ?_
  have h3 : σ i = i := congrArg (fun f : Fin N ≃o Fin N => f i) this
  exact h3

theorem strictAnti_schurExp {a : Fin N → ℕ} (ha : Antitone a) : StrictAnti (schurExp a) := by
  intro i j hij
  have h1 := ha hij.le
  have h2 : (j.rev : ℕ) < (i.rev : ℕ) := by
    exact Fin.lt_def.1 (Fin.rev_lt_rev.2 hij)
  simp only [schurExp]
  omega

theorem coeff_alternant_self {s : Fin N → ℕ} (hs : StrictAnti s) :
    (alternant s : MvPolynomial (Fin N) ℂ).coeff (Finsupp.equivFunOnFinite.symm s) = 1 := by
  classical
  rw [coeff_alternant, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    have h := eq_comp_of_mapDomain_eq (a := s) (b := Finsupp.equivFunOnFinite.symm s) (σ := σ)
    by_cases hc : (Finsupp.equivFunOnFinite.symm s).mapDomain σ = Finsupp.equivFunOnFinite.symm s
    · exact absurd (perm_eq_one_of_strictAnti hs hs (h hc)) hσ
    · simp [hc]
  · simp

theorem eq_of_alternant_eq {s t : Fin N → ℕ} (hs : StrictAnti s) (ht : StrictAnti t)
    (h : (alternant s : MvPolynomial (Fin N) ℂ) = alternant t) : s = t := by
  classical
  have h1 := coeff_alternant_self hs
  rw [h, coeff_alternant] at h1
  by_contra hne
  have : ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (if (Finsupp.equivFunOnFinite.symm t).mapDomain σ = Finsupp.equivFunOnFinite.symm s then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases hc : (Finsupp.equivFunOnFinite.symm t).mapDomain σ = Finsupp.equivFunOnFinite.symm s
    · have this : t = s ∘ σ := eq_comp_of_mapDomain_eq hc
      have h2 : σ = 1 := perm_eq_one_of_strictAnti ht hs this
      subst h2
      exfalso
      apply hne
      funext i
      have := congrArg (fun d => d i) hc
      simpa using this.symm
    · simp [hc]
  rw [this] at h1
  exact zero_ne_one h1

theorem schurPoly_injective {a a' : Fin N → ℕ} (ha : Antitone a) (ha' : Antitone a')
    (h : (schurPoly a : MvPolynomial (Fin N) ℂ) = schurPoly a') : a = a' := by
  have h1 : (schurAlternant a : MvPolynomial (Fin N) ℂ) = schurAlternant a' := by
    rw [schurAlternant_eq_vandermondeDelta_mul_schurPoly, schurAlternant_eq_vandermondeDelta_mul_schurPoly, h]
  have h2 := eq_of_alternant_eq (strictAnti_schurExp ha) (strictAnti_schurExp ha') h1
  funext j
  have := congrFun h2 j
  simpa [schurExp] using this

/-- Diagrams with at most `N` rows and the same character at all diagonal matrices are equal. -/
theorem eq_of_weylValue_eq (la mu : DiagramsOfSize m) (hla : la.1.colLen 0 ≤ N) (hmu : mu.1.colLen 0 ≤ N)
    (h : ∀ x : Fin N → ℂ, (∀ i, x i ≠ 0) → weylValue la x = weylValue mu x) : la = mu := by
  apply eq_of_rowLen_eq hla hmu
  have key : (schurPoly (fun j : Fin N => la.1.rowLen j) : MvPolynomial (Fin N) ℂ) =
      schurPoly (fun j : Fin N => mu.1.rowLen j) := by
    have hP : (∏ i : Fin N, MvPolynomial.X i : MvPolynomial (Fin N) ℂ) *
        (schurPoly (fun j : Fin N => la.1.rowLen j) - schurPoly (fun j : Fin N => mu.1.rowLen j)) = 0 := by
      apply MvPolynomial.funext
      intro x
      by_cases hx : ∀ i, x i ≠ 0
      · have := h x hx
        simp only [weylValue, hla, hmu, ↓reduceIte] at this
        simp [this]
      · push Not at hx
        obtain ⟨i, hi⟩ := hx
        simp [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    have hne : (∏ i : Fin N, MvPolynomial.X i : MvPolynomial (Fin N) ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => MvPolynomial.X_ne_zero i
    exact sub_eq_zero.1 ((mul_eq_zero.1 hP).resolve_left hne)
  have := schurPoly_injective (fun i j hij => la.1.rowLen_anti i j hij) (fun i j hij => mu.1.rowLen_anti i j hij) key
  exact fun j => congrFun this j

end SchurInj

section BModules

variable (N m : ℕ)

/-- A finite-dimensional homogeneous polynomial representation of degree `m`, bundled together with its space. -/
structure PolyRepData where
  carrier : Type
  [acg : AddCommGroup carrier]
  [mod : Module ℂ carrier]
  [fd : FiniteDimensional ℂ carrier]
  ρ : Representation ℂ (GL (Fin N) ℂ) carrier
  hρ : IsHomogPolyRep m ρ

attribute [instance] PolyRepData.acg PolyRepData.mod PolyRepData.fd

variable {N m}

namespace PolyRepData

variable (d d' : PolyRepData N m)

/-- The linear map `End(V^{⊗m}) → End W` with `g ⊗ ⋯ ⊗ g ↦ ρ g`. -/
noncomputable def lin : Module.End ℂ (⨂[ℂ] _ : Fin m, Fin N → ℂ) →ₗ[ℂ] Module.End ℂ d.carrier :=
  (exists_linear_eq_rho d.hρ).choose

theorem lin_spec (g : GL (Fin N) ℂ) : d.lin (tensorPowerGL N ℂ m g) = d.ρ g :=
  (exists_linear_eq_rho d.hρ).choose_spec g

/-- The action of the commutant `B` of `S_m` on `W`. -/
noncomputable def alg : schurCommutant N m →ₐ[ℂ] Module.End ℂ d.carrier := schurAlgHom d.lin d.lin_spec

/-- The carrier of `d`, viewed as a module over `B`. -/
abbrev Mod : Type := d.carrier

noncomputable instance : Module (schurCommutant N m) d.Mod := Module.compHom d.carrier d.alg.toRingHom

theorem smul_def (b : schurCommutant N m) (w : d.Mod) : b • w = d.alg b w := rfl

instance : IsScalarTower ℂ (schurCommutant N m) d.Mod :=
  ⟨fun c b w => by
    show d.alg (c • b) w = c • d.alg b w
    rw [map_smul]
    rfl⟩

/-- The element `g ⊗ ⋯ ⊗ g` of `B`. -/
noncomputable def glElt (g : GL (Fin N) ℂ) : schurCommutant N m :=
  ⟨tensorPowerGL N ℂ m g, by
    rw [← Subalgebra.mem_toSubmodule, ← span_tensorPowerGL_eq]
    exact Submodule.subset_span ⟨g, rfl⟩⟩

theorem glElt_smul (g : GL (Fin N) ℂ) (w : d.Mod) : (glElt g : schurCommutant N m) • w = d.ρ g w := by
  rw [smul_def]
  show d.lin (tensorPowerGL N ℂ m g) w = _
  rw [d.lin_spec]

/-- The representation is irreducible: nonzero, with no proper nonzero invariant subspaces. -/
def GLSimple : Prop :=
  Nontrivial d.carrier ∧ ∀ U : Submodule ℂ d.carrier, (∀ g, ∀ w ∈ U, d.ρ g w ∈ U) → U = ⊥ ∨ U = ⊤

theorem GLSimple.isSimpleModule (h : d.GLSimple) : IsSimpleModule (schurCommutant N m) d.Mod := by
  obtain ⟨hn, hU⟩ := h
  have : Nontrivial d.Mod := hn
  refine { toNontrivial := (Submodule.nontrivial_iff _).2 this, eq_bot_or_eq_top := fun S => ?_ }
  have h1 : ∀ g, ∀ w ∈ S.restrictScalars ℂ, d.ρ g w ∈ S.restrictScalars ℂ := by
    intro g w hw
    rw [← glElt_smul]
    exact S.smul_mem _ hw
  rcases hU (S.restrictScalars ℂ) h1 with h | h
  · left
    apply Submodule.restrictScalars_injective ℂ (schurCommutant N m) d.Mod
    rw [h, Submodule.restrictScalars_bot]
  · right
    apply Submodule.restrictScalars_injective ℂ (schurCommutant N m) d.Mod
    rw [h, Submodule.restrictScalars_top]

variable {d d'}

theorem equiv_comm (e : d.Mod ≃ₗ[schurCommutant N m] d'.Mod) (g : GL (Fin N) ℂ) (w : d.Mod) :
    e (d.ρ g w) = d'.ρ g (e w) := by
  rw [← glElt_smul, ← glElt_smul, map_smul]

/-- A `B`-linear isomorphism is an isomorphism of representations. -/
noncomputable def repEquivOfEquiv (e : d.Mod ≃ₗ[schurCommutant N m] d'.Mod) : Representation.Equiv d.ρ d'.ρ :=
  Representation.Equiv.mk (e.restrictScalars ℂ) fun g => LinearMap.ext fun w => equiv_comm e g w

theorem trace_eq_of_equiv (e : d.Mod ≃ₗ[schurCommutant N m] d'.Mod) (g : GL (Fin N) ℂ) :
    LinearMap.trace ℂ _ (d.ρ g) = LinearMap.trace ℂ _ (d'.ρ g) := by
  have h : (e.restrictScalars ℂ).conj (d.ρ g) = d'.ρ g := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply]
    have := equiv_comm e g ((e.restrictScalars ℂ).symm x)
    simpa using this
  rw [← LinearMap.trace_conj' (d.ρ g) (e.restrictScalars ℂ), h]

/-- The twist `W ⊗ Λ^N V` by the determinant. -/
noncomputable def twist (d : PolyRepData N m) : PolyRepData N (m + N) where
  carrier := d.carrier ⊗[ℂ] ℂ
  ρ := d.ρ.tprod (detRep N ℂ 1)
  hρ := by
    have := isHomogPolyRep_tprod d.hρ isHomogPolyRep_detRep
    rwa [add_comm] at this

theorem rid_tprod (d : PolyRepData N m) (g : GL (Fin N) ℂ) (x : d.carrier ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ d.carrier ((d.ρ.tprod (detRep N ℂ 1)) g x) =
      ((g : Matrix (Fin N) (Fin N) ℂ).det) • d.ρ g (TensorProduct.rid ℂ d.carrier x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [Representation.tprod_apply, detRep, Matrix.GeneralLinearGroup.det, smul_smul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem twist_aux {d : PolyRepData N m} (hU : ∀ U : Submodule ℂ d.carrier, (∀ g, ∀ w ∈ U, d.ρ g w ∈ U) →
    U = ⊥ ∨ U = ⊤) (U : Submodule ℂ (d.carrier ⊗[ℂ] ℂ))
    (hUs : ∀ g, ∀ w ∈ U, (d.ρ.tprod (detRep N ℂ 1)) g w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have hdet : ∀ g : GL (Fin N) ℂ, ((g : Matrix (Fin N) (Fin N) ℂ).det) ≠ 0 := fun g =>
    Matrix.GeneralLinearGroup.det_ne_zero g
  have key := rid_tprod d
  have hinj : Function.Injective (TensorProduct.rid ℂ d.carrier).toLinearMap :=
    (TensorProduct.rid ℂ d.carrier).injective
  have h1 : ∀ g, ∀ v ∈ U.map (TensorProduct.rid ℂ d.carrier).toLinearMap,
      d.ρ g v ∈ U.map (TensorProduct.rid ℂ d.carrier).toLinearMap := by
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨((g : Matrix (Fin N) (Fin N) ℂ).det)⁻¹ • (d.ρ.tprod (detRep N ℂ 1)) g u,
      U.smul_mem _ (hUs g u hu), ?_⟩
    simp only [LinearEquiv.coe_coe, map_smul, key, smul_smul, inv_mul_cancel₀ (hdet g), one_smul]
  rcases hU _ h1 with h | h
  · left
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_bot]
  · right
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top]
    exact (LinearMap.range_eq_top.2 (TensorProduct.rid ℂ d.carrier).surjective).symm

theorem GLSimple.twist {d : PolyRepData N m} (h : d.GLSimple) : d.twist.GLSimple := by
  obtain ⟨hn, hU⟩ := h
  have hnt : Nontrivial (d.carrier ⊗[ℂ] ℂ) := (TensorProduct.rid ℂ d.carrier).toEquiv.nontrivial
  exact ⟨hnt, fun U hUs => twist_aux hU U hUs⟩

end PolyRepData

/-- The multiplicity space `L_ν` as a bundled homogeneous polynomial representation of degree `m`. -/
noncomputable def lData {N m : ℕ} (ν : DiagramsOfSize m) : PolyRepData N m where
  carrier := spechtModule ν →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin m))] tensorPowerModule (Fin N → ℂ) m
  ρ := swRepGL N m ν
  hρ := isHomogPolyRep_swRepGL m ν

theorem glSimple_lData {N m : ℕ} (ν : DiagramsOfSize m) (h : ν.1.colLen 0 ≤ N) :
    (lData (N := N) ν).GLSimple := by
  have hfin : Module.finrank ℂ (spechtModule ν →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin m))]
      tensorPowerModule (Fin N → ℂ) m) ≠ 0 := fun h0 => by
    have := (finrank_swRepGL_eq_zero_iff (N := N) ν).1 h0
    omega
  have hnt : Nontrivial (spechtModule ν →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin m))]
      tensorPowerModule (Fin N → ℂ) m) := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hfin)
  refine ⟨hnt, fun U hU => ?_⟩
  have hirr := (swRep_subsingleton_or_isIrreducible (V := Fin N → ℂ) m ν).resolve_left
    (not_subsingleton_iff_nontrivial.2 hnt)
  let U' : Subrepresentation (swRep (V := Fin N → ℂ) m ν) :=
    ⟨U, fun u v hv => by
      have := hU (Matrix.GeneralLinearGroup.toLin.symm u) v hv
      have h2 : (lData (N := N) ν).ρ (Matrix.GeneralLinearGroup.toLin.symm u) = swRep (V := Fin N → ℂ) m ν u := by
        show swRep (V := Fin N → ℂ) m ν (Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.toLin.symm u)) = _
        rw [MulEquiv.apply_symm_apply]
      rw [h2] at this
      exact this⟩
  rcases hirr.eq_bot_or_eq_top U' with h | h
  · left
    exact congrArg Subrepresentation.toSubmodule h
  · right
    exact congrArg Subrepresentation.toSubmodule h

section Faithful

variable {N m : ℕ}

/-- The Schur-Weyl decomposition as a `ℂ`-linear isomorphism onto `V^{⊗m}`. -/
noncomputable def swDec : (Π ν : DiagramsOfSize m, spechtModule ν ⊗[ℂ] (lData (N := N) ν).carrier)
    ≃ₗ[ℂ] ⨂[ℂ] _ : Fin m, Fin N → ℂ :=
  ((schurWeylDecomposition (V := Fin N → ℂ) m).restrictScalars ℂ).trans
    (tensorPowerPermRep ℂ m (Fin N → ℂ)).asModuleEquiv

theorem swDec_apply (z : Π ν : DiagramsOfSize m, spechtModule ν ⊗[ℂ] (lData (N := N) ν).carrier) :
    swDec z = schurWeylDecomposition (V := Fin N → ℂ) m z := rfl

/-- The Schur-Weyl decomposition intertwines every element of the span of the operators `g ⊗ ⋯ ⊗ g` with
the action on the multiplicity spaces. -/
theorem apply_swDec_of_mem_span
    (T : Module.End ℂ (⨂[ℂ] _ : Fin m, Fin N → ℂ))
    (hT : T ∈ Submodule.span ℂ (Set.range (tensorPowerGL N ℂ m)))
    (z : Π ν : DiagramsOfSize m, spechtModule ν ⊗[ℂ] (lData (N := N) ν).carrier) :
    T (swDec z) =
      swDec (fun ν => TensorProduct.map LinearMap.id ((lData (N := N) ν).lin T) (z ν)) := by
  induction hT using Submodule.span_induction generalizing z with
  | mem T hT =>
    obtain ⟨g, rfl⟩ := hT
    have h := schurWeylDecomposition_equivariant (V := Fin N → ℂ) m (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) ℂ)) z
    rw [tensorPowerEnd_apply] at h
    have h' : (fun la => TensorProduct.map LinearMap.id
        (swPost m la (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) ℂ))) (z la)) =
        fun ν => TensorProduct.map LinearMap.id ((lData (N := N) ν).lin (tensorPowerGL N ℂ m g)) (z ν) :=
      funext fun ν => by rw [(lData (N := N) ν).lin_spec]; rfl
    rw [h'] at h
    simp only [swDec_apply]
    exact h
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, TensorProduct.map_zero_right]
    exact (swDec (N := N) (m := m)).map_zero.symm
  | add T T' _ _ h1 h2 =>
    rw [LinearMap.add_apply, h1, h2, ← map_add]
    refine congrArg swDec (funext fun ν => ?_)
    simp [TensorProduct.map_add_right]
  | smul c T _ h1 =>
    rw [LinearMap.smul_apply, h1, ← map_smul]
    refine congrArg swDec (funext fun ν => ?_)
    simp [TensorProduct.map_smul_right]

theorem eq_zero_of_alg_eq_zero (b : schurCommutant N m)
    (hb : ∀ ν : DiagramsOfSize m, ν.1.colLen 0 ≤ N → (lData (N := N) ν).alg b = 0) : b = 0 := by
  have hlin : ∀ ν : DiagramsOfSize m, (lData (N := N) ν).lin (b : Module.End ℂ _) = 0 := by
    intro ν
    by_cases h : ν.1.colLen 0 ≤ N
    · exact hb ν h
    · have h0 : Module.finrank ℂ (spechtModule ν →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin m))]
          tensorPowerModule (Fin N → ℂ) m) = 0 := (finrank_swRepGL_eq_zero_iff (N := N) ν).2 (not_le.1 h)
      have hs : Subsingleton (spechtModule ν →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin m))]
          tensorPowerModule (Fin N → ℂ) m) := Module.finrank_zero_iff.1 h0
      exact LinearMap.ext fun x => @Subsingleton.elim _ hs _ _
  apply Subtype.ext
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz⟩ := swDec.surjective x
  have := apply_swDec_of_mem_span (b : Module.End ℂ _) (mem_span_tensorPowerGL b) z
  have hzero : (fun ν => TensorProduct.map LinearMap.id ((lData (N := N) ν).lin (b : Module.End ℂ _)) (z ν))
      = fun _ => 0 := funext fun ν => by
    rw [hlin ν, TensorProduct.map_zero_right]
    rfl
  rw [hzero] at this
  have h2 : (b : Module.End ℂ _) x = 0 := by
    rw [← hz, this]
    exact (swDec (N := N) (m := m)).map_zero
  exact h2

end Faithful

section Main

open Classical in
/-- The family of simple `B`-modules used in the density argument: `L_λ ⊗ Λ^N V` and the `L_ν` with at most `N`
rows. -/
noncomputable def idxData {n : ℕ} (N : ℕ) (la : DiagramsOfSize n) :
    Option {ν : DiagramsOfSize (n + N) // ν.1.colLen 0 ≤ N} → PolyRepData N (n + N)
  | none => (lData (N := N) la).twist
  | some ν => lData ν.1

theorem trace_twist_diag {n N : ℕ} (la : DiagramsOfSize n) (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    LinearMap.trace ℂ _ ((lData (N := N) la).twist.ρ (diagGL N x hx)) =
      (∏ i, x i) * LinearMap.trace ℂ _ (swRepGL N n la (diagGL N x hx)) := by
  show LinearMap.trace ℂ _ (TensorProduct.map (swRepGL N n la (diagGL N x hx))
    (detRep N ℂ 1 (diagGL N x hx))) = _
  rw [LinearMap.trace_tensorProduct']
  have : detRep N ℂ 1 (diagGL N x hx) = (∏ i, x i) • LinearMap.id := by
    ext
    simp [detRep, diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_diagonal]
  rw [this, map_smul, LinearMap.trace_id]
  simp [mul_comm]

theorem weylValue_eq_of_equiv {n N : ℕ} (la : DiagramsOfSize n) (ν : DiagramsOfSize (n + N))
    (e : (lData (N := N) la).twist.Mod ≃ₗ[schurCommutant N (n + N)] (lData (N := N) ν).Mod)
    (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    weylValue ν x = (∏ i, x i) * weylValue la x := by
  rw [← trace_swRepGL_diagonal ν x hx, ← trace_swRepGL_diagonal la x hx, ← trace_twist_diag la x hx]
  exact (PolyRepData.trace_eq_of_equiv e (diagGL N x hx)).symm

/-- **Etingof et al., Proposition 4.64.** `L_{λ + 1^N} ≅ L_λ ⊗ Λ^N V` as representations of `GL_N(ℂ)`. -/
@[kb "etingof2011" "Proposition 4.64, p. 67"]
theorem nonempty_equiv_swRepGL_add_one {n m N : ℕ} (la : DiagramsOfSize n) (mu : DiagramsOfSize m)
    (hla : la.1.colLen 0 ≤ N) (hmu : mu.1.colLen 0 ≤ N) (h : ∀ j : Fin N, mu.1.rowLen j = la.1.rowLen j + 1) :
    Nonempty (Representation.Equiv (swRepGL N m mu) ((swRepGL N n la).tprod (detRep N ℂ 1))) := by
  classical
  have hm : m = n + N := by
    rw [← sum_rowLen_eq mu hmu, ← sum_rowLen_eq la hla]
    simp [h, Finset.sum_add_distrib]
  subst hm
  have hdiag : ∀ x : Fin N → ℂ, (∀ i, x i ≠ 0) → weylValue mu x = (∏ i, x i) * weylValue la x := by
    intro x hx
    rw [← trace_swRepGL_diagonal mu x hx, ← trace_swRepGL_diagonal la x hx]
    exact trace_swRepGL_diagonal_add_one la mu hla hmu h x hx
  have hnon : Nonempty ((lData (N := N) la).twist.Mod ≃ₗ[schurCommutant N (n + N)] (lData (N := N) mu).Mod) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have hsimple : ∀ i, IsSimpleModule (schurCommutant N (n + N)) (idxData N la i).Mod := by
      rintro (_ | ⟨ν, hν⟩)
      · exact (glSimple_lData la hla).twist.isSimpleModule
      · exact (glSimple_lData ν hν).isSimpleModule
    have hV : ∀ i j, i ≠ j → IsEmpty ((idxData N la i).Mod ≃ₗ[schurCommutant N (n + N)] (idxData N la j).Mod) := by
      have key : ∀ ν : DiagramsOfSize (n + N), ν.1.colLen 0 ≤ N →
          Nonempty ((lData (N := N) la).twist.Mod ≃ₗ[schurCommutant N (n + N)] (lData (N := N) ν).Mod) → ν = mu := by
        intro ν hν ⟨e⟩
        exact eq_of_weylValue_eq ν mu hν hmu fun x hx =>
          (weylValue_eq_of_equiv la ν e x hx).trans (hdiag x hx).symm
      rintro (_ | ⟨ν, hν⟩) (_ | ⟨ν', hν'⟩) hij
      · exact absurd rfl hij
      · refine ⟨fun e => ?_⟩
        have := key ν' hν' ⟨e⟩
        subst this
        exact hcon.false e
      · refine ⟨fun e => ?_⟩
        have := key ν hν ⟨e.symm⟩
        subst this
        exact hcon.false e.symm
      · refine ⟨fun e => hij ?_⟩
        have : ν = ν' := eq_of_weylValue_eq ν ν' hν hν' fun x hx => by
          rw [← trace_swRepGL_diagonal ν x hx, ← trace_swRepGL_diagonal ν' x hx]
          exact PolyRepData.trace_eq_of_equiv e (diagGL N x hx)
        subst this
        rfl
    have := hsimple
    let g : ∀ i, Module.End ℂ (idxData N la i).Mod := fun i =>
      match i with
      | none => LinearMap.id
      | some _ => 0
    obtain ⟨b, hb⟩ := density_pi_surjective (k := ℂ) (A := schurCommutant N (n + N))
      (V := fun i => (idxData N la i).Mod) hV g
    have hb0 : b = 0 := by
      refine eq_zero_of_alg_eq_zero b fun ν hν => ?_
      have := congrFun hb (some ⟨ν, hν⟩)
      exact this
    have h1 := congrFun hb none
    have hnt : Nontrivial (lData (N := N) la).twist.carrier := (glSimple_lData la hla).twist.1
    obtain ⟨w, hw⟩ := exists_ne (0 : (lData (N := N) la).twist.carrier)
    have h2 := LinearMap.congr_fun h1 w
    subst hb0
    apply hw
    have h3 : (0 : schurCommutant N (n + N)) • w = 0 := zero_smul _ _
    have h4 : (g none) w = w := rfl
    exact ((h3.symm.trans h2).trans h4).symm
  obtain ⟨e⟩ := hnon
  exact ⟨(PolyRepData.repEquivOfEquiv e).symm⟩

end Main

end BModules

end UndergradKB.RepresentationTheory
