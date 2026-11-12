import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.GroupTheory.Perm.Sign
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.SchurFunctors
import UndergradKB.RepresentationTheory.DoubleCentralizer
import UndergradKB.RepresentationTheory.SymmetricPowers
import UndergradKB.RepresentationTheory.TensorAlgebraRows

/-! # Antisymmetric tensors and the trace on symmetric powers (Etingof et al., Problem 1.49(e)-(g))

* `antisymmetricTensors`: the tensors `x` in `V^{⊗n}` with `σ x = sign σ • x` for all permutations.
* `antisymmetricTensors_antiProj_bijective`: in characteristic zero the quotient map
  `V^{⊗n} → ⋀ⁿ V` restricts to a bijection from the antisymmetric tensors onto `⋀ⁿ V` (the analogue of
  `symmetricTensors_mk_bijective`).
* `symMap`: the functorial map `S^n f` on Mathlib's symmetric power.
* `trace_symMap_of_diagonal`: if `A` is diagonal in a basis `b` with eigenvalues `x i`, then the trace
  of `S^n A` is the sum over multisets of size `n` of indices of the product of the corresponding
  eigenvalues, i.e. the complete homogeneous symmetric polynomial `h_n` evaluated at the eigenvalues.

Weakening: the trace formula is proved for an endomorphism diagonalisable in a basis (not for a general
endomorphism, nor in the form of a statement about the characteristic polynomial).
-/

namespace UndergradKB.RepresentationTheory

open scoped TensorProduct
open PiTensorProduct

section Anti

variable (k : Type*) [Field k] [CharZero k] (n : ℕ) (V : Type*) [AddCommGroup V] [Module k V]

/-- The sign of a permutation as an element of the field. -/
def sgn {n : ℕ} (σ : Equiv.Perm (Fin n)) : k := (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : k)

variable {k n V}

omit [CharZero k] in
theorem sgn_mul (σ τ : Equiv.Perm (Fin n)) : sgn k (σ * τ) = sgn k σ * sgn k τ := by
  simp [sgn]

omit [CharZero k] in
theorem sgn_inv (σ : Equiv.Perm (Fin n)) : sgn k σ⁻¹ = sgn k σ := by
  simp [sgn]

omit [CharZero k] in
theorem sgn_mul_self (σ : Equiv.Perm (Fin n)) : sgn k σ * sgn k σ = 1 := by
  rw [← sgn_mul]
  simp [sgn]

omit [CharZero k] in
theorem units_smul_eq {M : Type*} [AddCommGroup M] [Module k M] (u : ℤˣ) (x : M) :
    u • x = ((u : ℤ) : k) • x := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]

variable (k n V)

/-- The antisymmetric tensors: those `x` with `σ x = sign σ • x` for every permutation `σ`. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
def antisymmetricTensors : Submodule k (⨂[k] _ : Fin n, V) where
  carrier := {x | ∀ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n V σ x = sgn k σ • x}
  add_mem' := by
    intro x y hx hy σ
    simp only [map_add, hx σ, hy σ, smul_add]
  zero_mem' := by intro σ; simp
  smul_mem' := by
    intro c x hx σ
    simp only [map_smul, hx σ]
    exact smul_comm _ _ _

/-- Antisymmetrization of the tensor power: the signed average of the permutation action. -/
noncomputable def antisymmetrizer : (⨂[k] _ : Fin n, V) →ₗ[k] ⨂[k] _ : Fin n, V :=
  ((Nat.factorial n : k)⁻¹) • ∑ σ : Equiv.Perm (Fin n), sgn k σ • tensorPowerPermRep k n V σ

variable {k n V}

omit [CharZero k] in
theorem antisymmetrizer_apply (x : ⨂[k] _ : Fin n, V) :
    antisymmetrizer k n V x = ((Nat.factorial n : k)⁻¹) • ∑ σ : Equiv.Perm (Fin n),
      sgn k σ • tensorPowerPermRep k n V σ x := by
  simp [antisymmetrizer]

/-- The projection from the tensor power onto the exterior power. -/
noncomputable def antiProj : (⨂[k] _ : Fin n, V) →ₗ[k] ⋀[k]^n V :=
  PiTensorProduct.lift (exteriorPower.ιMulti k n (M := V)).toMultilinearMap

omit [CharZero k] in
theorem antiProj_tprod (v : Fin n → V) : antiProj (tprod k v) = exteriorPower.ιMulti k n v := by
  simp [antiProj]

omit [CharZero k] in
theorem antiProj_perm (σ : Equiv.Perm (Fin n)) (x : ⨂[k] _ : Fin n, V) :
    antiProj (tensorPowerPermRep k n V σ x) = sgn k σ • antiProj x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, tensorPowerPermRep_tprod, antiProj_tprod]
    have h := (exteriorPower.ιMulti k n (M := V)).map_perm f σ⁻¹
    rw [show (fun i => f (σ⁻¹ i)) = f ∘ ⇑σ⁻¹ from rfl, h, units_smul_eq (k := k),
      Equiv.Perm.sign_inv]
    rw [smul_comm]
    rfl
  | add y z hy hz => simp only [map_add, hy, hz, smul_add]

omit [CharZero k] in
theorem antisymmetrizer_mem(x : ⨂[k] _ : Fin n, V) :
    antisymmetrizer k n V x ∈ antisymmetricTensors k n V := by
  intro τ
  rw [antisymmetrizer_apply, map_smul, map_sum]
  rw [smul_comm]
  congr 1
  have h : ∀ σ : Equiv.Perm (Fin n), tensorPowerPermRep k n V τ (sgn k σ • tensorPowerPermRep k n V σ x) =
      sgn k τ • (sgn k (τ * σ) • tensorPowerPermRep k n V (τ * σ) x) := by
    intro σ
    have e : tensorPowerPermRep k n V τ (tensorPowerPermRep k n V σ x) =
        tensorPowerPermRep k n V (τ * σ) x := by
      rw [map_mul]; rfl
    rw [map_smul, e, smul_smul, sgn_mul, ← mul_assoc, sgn_mul_self, one_mul]
  simp_rw [h]
  rw [← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ)
    (fun σ => sgn k σ • tensorPowerPermRep k n V σ x)

theorem antisymmetrizer_of_mem (x : ⨂[k] _ : Fin n, V) (hx : x ∈ antisymmetricTensors k n V) :
    antisymmetrizer k n V x = x := by
  rw [antisymmetrizer_apply]
  have h : ∀ σ : Equiv.Perm (Fin n), sgn k σ • tensorPowerPermRep k n V σ x = x := by
    intro σ
    rw [hx σ, smul_smul, sgn_mul_self, one_smul]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero n

theorem antiProj_antisymmetrizer (x : ⨂[k] _ : Fin n, V) :
    antiProj (antisymmetrizer k n V x) = antiProj x := by
  rw [antisymmetrizer_apply, map_smul, map_sum]
  have h : ∀ σ : Equiv.Perm (Fin n),
      antiProj (sgn k σ • tensorPowerPermRep k n V σ x) = antiProj x := by
    intro σ
    rw [map_smul, antiProj_perm, smul_smul, sgn_mul_self, one_smul]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero n

variable (k n V) in
/-- The alternating map `v ↦ (1/n!) ∑ sign σ • v_{σ(1)} ⊗ ⋯ ⊗ v_{σ(n)}`. -/
noncomputable def antiAlt : V [⋀^Fin n]→ₗ[k] ⨂[k] _ : Fin n, V :=
  ((Nat.factorial n : k)⁻¹) • MultilinearMap.alternatization (tprod k : MultilinearMap k (fun _ : Fin n => V) _)

omit [CharZero k] in
theorem antiAlt_apply (v : Fin n → V) :
    antiAlt k n V v = ((Nat.factorial n : k)⁻¹) • ∑ σ : Equiv.Perm (Fin n),
      sgn k σ • tprod k (fun i => v (σ i)) := by
  simp only [antiAlt, smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  congr 1

/-- The section of `antiProj`: the antisymmetrizer descended to the exterior power. -/
noncomputable def antiExt : ⋀[k]^n V →ₗ[k] ⨂[k] _ : Fin n, V :=
  exteriorPower.alternatingMapLinearEquiv (antiAlt k n V)

omit [CharZero k] in
theorem antiExt_antiProj(x : ⨂[k] _ : Fin n, V) :
    antiExt (antiProj x) = antisymmetrizer k n V x := by
  have : (antiExt (k := k) (n := n) (V := V)) ∘ₗ antiProj = antisymmetrizer k n V := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, antiProj_tprod, antiExt,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, antiAlt_apply, antisymmetrizer_apply,
      tensorPowerPermRep_tprod]
    congr 1
    rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [sgn_inv]
  exact congr($this x)

/-- **Problem 1.49(e), antisymmetric version.** In characteristic zero the exterior power `⋀ⁿ V` is
canonically isomorphic to the space of antisymmetric tensors in `V^{⊗n}`: the projection restricts to a
bijection from the antisymmetric tensors onto `⋀ⁿ V`. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem antisymmetricTensors_antiProj_bijective :
    Function.Bijective ((antiProj (k := k) (n := n) (V := V)).comp (antisymmetricTensors k n V).subtype) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : antiProj (x : ⨂[k] _ : Fin n, V) = 0 := hx
    have h2 : antisymmetrizer k n V (x : ⨂[k] _ : Fin n, V) = 0 := by
      rw [← antiExt_antiProj, h1, map_zero]
    exact Subtype.ext (by rw [← antisymmetrizer_of_mem _ x.2, h2]; rfl)
  · intro y
    obtain ⟨x, rfl⟩ : ∃ x, antiProj (k := k) (n := n) (V := V) x = y := by
      have hr : LinearMap.range (antiProj (k := k) (n := n) (V := V)) = ⊤ := by
        rw [eq_top_iff, ← exteriorPower.ιMulti_span, Submodule.span_le]
        rintro _ ⟨v, rfl⟩
        exact ⟨tprod k v, antiProj_tprod v⟩
      have hy : y ∈ LinearMap.range (antiProj (k := k) (n := n) (V := V)) := by rw [hr]; trivial
      exact hy
    exact ⟨⟨antisymmetrizer k n V x, antisymmetrizer_mem x⟩, antiProj_antisymmetrizer x⟩

end Anti

section Functorial

variable {k : Type} [CommRing k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- The functorial map `S^n f : S^n V → S^n W` induced by a linear map `f : V → W` on symmetric powers. -/
noncomputable def symMap (n : ℕ) (f : V →ₗ[k] W) :
    SymmetricPower k (Fin n) V →ₗ[k] SymmetricPower k (Fin n) W :=
  symLift ((SymmetricPower.mk k (Fin n) W).comp (tensorPowerMap n f)) (by
    intro e g
    simp only [LinearMap.comp_apply, tensorPowerMap, PiTensorProduct.map_tprod]
    exact SymmetricPower.tprod_equiv (R := k) e (fun i => f (g i)))

theorem symMap_tprod (n : ℕ) (f : V →ₗ[k] W) (g : Fin n → V) :
    symMap n f (SymmetricPower.tprod k g) = SymmetricPower.tprod k (fun i => f (g i)) := by
  change symMap n f (SymmetricPower.mk k (Fin n) V (PiTensorProduct.tprod k g)) = _
  simp [symMap, symLift_mk, tensorPowerMap]
  rfl

end Functorial

section Trace

variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V]
  [Module k V] (b : Module.Basis ι k V) (n : ℕ) (x : ι → k) (A : V →ₗ[k] V)

omit [Fintype ι] in
theorem symMap_symFamily(hA : ∀ i, A (b i) = x i • b i) (m : Sym ι n) :
    symMap n A (symFamily b n m) = ((m.1.map x).prod) • symFamily b n m := by
  obtain ⟨s, rfl⟩ := exists_msetOf m
  rw [symFamily_msetOf, symMap_tprod]
  simp only [hA]
  rw [MultilinearMap.map_smul_univ]
  congr 2
  simp [msetOf, Finset.prod_eq_multiset_prod]
  rfl

/-- **Problem 1.49(g), symmetric version.** If `A` is diagonal in the basis `b`, with `A bᵢ = xᵢ bᵢ`,
then the trace of `S^n A` is the sum over multisets of size `n` of indices of the product of the
corresponding eigenvalues, that is the complete homogeneous symmetric function `h_n(x)`. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem trace_symMap_of_diagonal (hA : ∀ i, A (b i) = x i • b i) :
    LinearMap.trace k _ (symMap n A) = ∑ m : Sym ι n, (m.1.map x).prod := by
  rw [LinearMap.trace_eq_matrix_trace k (symBasis b n), Matrix.trace]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, symBasis_apply, symMap_symFamily b n x A hA,
    ← symBasis_apply, map_smul]
  simp

end Trace

end UndergradKB.RepresentationTheory
