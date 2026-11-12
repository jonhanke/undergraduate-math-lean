import Mathlib.RingTheory.SimpleModule.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialRepsTensor
import UndergradKB.RepresentationTheory.SchurWeyl

/-! # Complete reducibility of homogeneous polynomial representations (Etingof et al., Theorem 4.66)

A representation `ρ` of `GL_N(ℂ)` is *homogeneous polynomial of degree `n`* (`IsHomogPolyRep`) when every coefficient
function `g ↦ φ (ρ g w)` is a homogeneous polynomial of degree `n` in the matrix entries of `g`.

* `exists_linear_eq_rho`: for such `ρ` on a finite-dimensional space `W`, there is a linear map
  `L : End(V^{⊗n}) → End W` with `L (g ⊗ ⋯ ⊗ g) = ρ g`, `V = ℂ^N`.
* `schurAlgHom`: `L` restricts to an algebra homomorphism on the commutant `B` of `S_n` in `End(V^{⊗n})`, which is
  spanned by the operators `g ⊗ ⋯ ⊗ g` (Proposition 4.58) and is semisimple (Theorem 4.57).
* `IsHomogPolyRep.exists_isCompl`: **complete reducibility.**  Every subrepresentation of `W` has an invariant
  complement, because `W` is a module over the semisimple algebra `B` whose submodules are the subrepresentations.

Weakenings versus Theorem 4.66: the representation is assumed homogeneous (a general polynomial representation is
the direct sum of its homogeneous parts, the eigenspaces of the scalar matrices, which is not formalized here); the
identification of the irreducible constituents with the `L_λ` and the decomposition of the polynomial functions on
`GL(V)` are not formalized.
-/

namespace UndergradKB.RepresentationTheory

open PiTensorProduct
open scoped TensorProduct

variable {N n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A representation of `GL_N(ℂ)` whose coefficient functions are homogeneous polynomials of degree `n` in the
matrix entries. -/
def IsHomogPolyRep (n : ℕ) (ρ : Representation ℂ (GL (Fin N) ℂ) W) : Prop :=
  ∀ (w : W) (φ : Module.Dual ℂ W), ∃ P : MvPolynomial (Fin N × Fin N) ℂ,
    P.IsHomogeneous n ∧ ∀ g, φ (ρ g w) = MvPolynomial.eval (glEntries N ℂ g) P

section Linear

variable [FiniteDimensional ℂ W] {ρ : Representation ℂ (GL (Fin N) ℂ) W}

/-- A homogeneous polynomial representation of degree `n` factors linearly through `g ↦ g ⊗ ⋯ ⊗ g`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem exists_linear_eq_rho (hρ : IsHomogPolyRep n ρ) :
    ∃ L : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ) →ₗ[ℂ] Module.End ℂ W,
      ∀ g, L (tensorPowerGL N ℂ n g) = ρ g := by
  classical
  let b := Module.finBasis ℂ W
  have hP : ∀ a c, ∃ ℓ : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ) →ₗ[ℂ] ℂ,
      ∀ g, ℓ (tensorPowerGL N ℂ n g) = b.coord a (ρ g (b c)) := by
    intro a c
    obtain ⟨P, hPh, hPe⟩ := hρ (b c) (b.coord a)
    obtain ⟨ℓ, hℓ⟩ := exists_linear_tensorPowerGL_of_isHomogeneous P hPh
    exact ⟨ℓ, fun g => (hℓ g).trans (hPe g).symm⟩
  choose ℓ hℓ using hP
  refine ⟨∑ a, ∑ c, (ℓ a c).smulRight (LinearMap.smulRight (b.coord c) (b a)), fun g => ?_⟩
  refine b.ext fun c' => ?_
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, hℓ, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, smul_smul]
  simp only [Finsupp.single_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact b.sum_repr (ρ g (b c'))

end Linear

section Algebra

/-- The additive group structure on `V^{⊗n}`, `V = ℂ^N`, stated for the additive monoid structure used by
`tensorPowerGL` (instance search does not find it through the product structure on `ℂ^N`). -/
noncomputable instance instAddCommGroupTensorPowerStd : AddCommGroup (⨂[ℂ] _ : Fin n, Fin N → ℂ) :=
  Module.addCommMonoidToAddCommGroup ℂ

variable (N n) in
/-- The commutant `B` of `S_n` in `End(V^{⊗n})`, `V = ℂ^N`. -/
noncomputable abbrev schurCommutant : Subalgebra ℂ (Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ)) :=
  Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n (Fin N → ℂ)))

/-- `B` is spanned by the operators `g ⊗ ⋯ ⊗ g`, `g ∈ GL_N(ℂ)` (Proposition 4.58). -/
theorem span_tensorPowerGL_eq :
    Submodule.span ℂ (Set.range (tensorPowerGL N ℂ n)) = (schurCommutant N n).toSubmodule := by
  rw [← span_tensorPowerMap_units_eq_centralizer]
  congr 1
  ext T
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Matrix.GeneralLinearGroup.toLin g, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨Matrix.GeneralLinearGroup.toLin.symm u, ?_⟩
    have : ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.toLin.symm u) :
        (Fin N → ℂ) →ₗ[ℂ] Fin N → ℂ)) = u := by rw [MulEquiv.apply_symm_apply]
    exact congrArg (tensorPowerMap n) this

theorem mem_span_tensorPowerGL (x : schurCommutant N n) :
    (x : Module.End ℂ _) ∈ Submodule.span ℂ (Set.range (tensorPowerGL N ℂ n)) := by
  rw [span_tensorPowerGL_eq]
  exact x.2

/-- `B` is semisimple (Theorem 4.57). -/
instance instIsSemisimpleRingSchurCommutant : IsSemisimpleRing (schurCommutant N n) := by
  have h : schurCommutant N n = commutant (swImage (Fin N → ℂ) n) := (centralizer_swImage n).symm
  rw [h]
  exact isSemisimpleRing_commutant _

variable {ρ : Representation ℂ (GL (Fin N) ℂ) W}
  (L : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ) →ₗ[ℂ] Module.End ℂ W) (hL : ∀ g, L (tensorPowerGL N ℂ n g) = ρ g)

include hL in
theorem map_mul_of_mem_span {x y : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ)}
    (hx : x ∈ Submodule.span ℂ (Set.range (tensorPowerGL N ℂ n)))
    (hy : y ∈ Submodule.span ℂ (Set.range (tensorPowerGL N ℂ n))) : L (x * y) = L x * L y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      rw [← map_mul (tensorPowerGL N ℂ n), hL, hL, hL, map_mul]
    | zero => simp
    | add y y' _ _ h1 h2 => rw [mul_add, map_add, map_add, h1, h2, mul_add]
    | smul c y _ h1 => rw [mul_smul_comm, map_smul, map_smul, h1, mul_smul_comm]
  | zero => simp
  | add x x' _ _ h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | smul c x _ h1 => rw [smul_mul_assoc, map_smul, map_smul, h1, smul_mul_assoc]

/-- The action of `B` on a homogeneous polynomial representation of degree `n`. -/
noncomputable def schurAlgHom : schurCommutant N n →ₐ[ℂ] Module.End ℂ W where
  toFun x := L x
  map_one' := by
    have : ((1 : schurCommutant N n) : Module.End ℂ _) = tensorPowerGL N ℂ n 1 := by simp
    rw [this, hL, map_one]
  map_mul' x y := map_mul_of_mem_span L hL (mem_span_tensorPowerGL x) (mem_span_tensorPowerGL y)
  map_zero' := by simp
  map_add' x y := by simp
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Subalgebra.coe_smul, Subalgebra.coe_one, map_smul, ← map_one (tensorPowerGL N ℂ n), hL, map_one]

theorem schurAlgHom_apply (x : schurCommutant N n) : schurAlgHom L hL x = L x := rfl

end Algebra

section Reducible

variable [FiniteDimensional ℂ W] {ρ : Representation ℂ (GL (Fin N) ℂ) W}

/-- **Etingof et al., Theorem 4.66 (complete reducibility), homogeneous case.**  Every subrepresentation of a
finite-dimensional homogeneous polynomial representation of `GL_N(ℂ)` has an invariant complement. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem IsHomogPolyRep.exists_isCompl (hρ : IsHomogPolyRep n ρ) (U : Submodule ℂ W)
    (hU : ∀ g, ∀ w ∈ U, ρ g w ∈ U) :
    ∃ U' : Submodule ℂ W, (∀ g, ∀ w ∈ U', ρ g w ∈ U') ∧ IsCompl U U' := by
  obtain ⟨L, hL⟩ := exists_linear_eq_rho hρ
  let φ := schurAlgHom L hL
  let : Module (schurCommutant N n) W := Module.compHom W φ.toRingHom
  have hsmul : ∀ (s : schurCommutant N n) (w : W), s • w = φ s w := fun _ _ => rfl
  have key : ∀ s : schurCommutant N n, ∀ w ∈ U, φ s w ∈ U := by
    intro s w hw
    rw [schurAlgHom_apply]
    suffices h : ∀ T ∈ Submodule.span ℂ (Set.range (tensorPowerGL N ℂ n)), L T w ∈ U from
      h _ (mem_span_tensorPowerGL s)
    intro T hs
    induction hs using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨g, rfl⟩ := hT
      rw [hL]
      exact hU g w hw
    | zero => simp
    | add T T' _ _ h1 h2 => rw [map_add, LinearMap.add_apply]; exact U.add_mem h1 h2
    | smul c T _ h1 => rw [map_smul, LinearMap.smul_apply]; exact U.smul_mem c h1
  let US : Submodule (schurCommutant N n) W :=
    { carrier := U
      add_mem' := U.add_mem
      zero_mem' := U.zero_mem
      smul_mem' := fun s w hw => by rw [hsmul]; exact key s w hw }
  have hss : IsSemisimpleModule (schurCommutant N n) W := IsSemisimpleRing.isSemisimpleModule
  obtain ⟨US', hc⟩ := @ComplementedLattice.exists_isCompl _ _ _ hss.toComplementedLattice US
  have hc1 : ∀ (c : ℂ) (w : W), (algebraMap ℂ (schurCommutant N n) c) • w = c • w := by
    intro c w
    rw [hsmul, φ.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self]
  let U' : Submodule ℂ W :=
    { carrier := US'
      add_mem' := US'.add_mem
      zero_mem' := US'.zero_mem
      smul_mem' := fun c w hw => by
        have := US'.smul_mem (algebraMap ℂ (schurCommutant N n) c) hw
        rwa [hc1] at this }
  have hgen : ∀ g, ∃ s : schurCommutant N n, ∀ w, ρ g w = s • w := by
    intro g
    have hmem : tensorPowerGL N ℂ n g ∈ schurCommutant N n := by
      rw [← Subalgebra.mem_toSubmodule, ← span_tensorPowerGL_eq]
      exact Submodule.subset_span ⟨g, rfl⟩
    exact ⟨⟨_, hmem⟩, fun w => by rw [hsmul, schurAlgHom_apply, hL]⟩
  refine ⟨U', fun g w hw => ?_, ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs⟩ := hgen g
    rw [hs]
    exact US'.smul_mem s hw
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact (Submodule.disjoint_def.1 hc.disjoint) x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : x ∈ US ⊔ US' := by rw [hc.codisjoint.eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact Submodule.mem_sup.2 ⟨y, hy, z, hz, rfl⟩

end Reducible

end UndergradKB.RepresentationTheory
