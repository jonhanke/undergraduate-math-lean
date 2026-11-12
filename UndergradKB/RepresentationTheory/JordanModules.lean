import Mathlib.Algebra.Module.PID
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.DFinsupp
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.AlgebrasChapter2b

/-! # Indecomposable `k[x]`-modules are Jordan blocks (Etingof et al., Example 1.19)

Over an algebraically closed field `k`, every finite-dimensional indecomposable `k[x]`-module is
isomorphic to a Jordan-block module `k[x]/(x - λ)ⁿ` with `n ≥ 1`.  The proof uses the structure
theorem for finitely generated torsion modules over a PID (Mathlib's `equiv_directSum_of_isTorsion`):
indecomposability forces a single nontrivial cyclic summand `k[x]/(pᵉ)` with `p` irreducible, and over an
algebraically closed field `p` is associated to `x - λ`.
-/

namespace UndergradKB.RepresentationTheory

open Polynomial Module

section JordanIndecomposable

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [Module k[X] V]
  [IsScalarTower k k[X] V]

/-- A finite-dimensional `k[x]`-module is a torsion module. -/
theorem isTorsion_of_finiteDimensional_polynomial [FiniteDimensional k V] :
    Module.IsTorsion k[X] V := by
  intro v
  let g : k[X] →ₗ[k] V := (LinearMap.toSpanSingleton k[X] V v).restrictScalars k
  have hg : ∀ p : k[X], g p = p • v := fun p => rfl
  have hnot : ¬ Function.Injective g := by
    intro hinj
    exact Polynomial.not_finite (R := k) (Module.Finite.of_injective g hinj)
  obtain ⟨p, hp0, hp⟩ : ∃ p : k[X], p ≠ 0 ∧ g p = 0 := by
    by_contra hcon
    exact hnot ((injective_iff_map_eq_zero g).2 fun p hp => by_contra fun h => hcon ⟨p, h, hp⟩)
  refine ⟨⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩, ?_⟩
  simpa [hg] using hp

/-- **Etingof et al., Example 1.19**: over an algebraically closed field, every finite-dimensional
indecomposable `k[x]`-module is isomorphic to a Jordan-block module `V_{λ,n} = k[x]/(x - λ)ⁿ` with `n ≥ 1`. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem exists_linearEquiv_jordanBlock_of_isIndecomposableModule [IsAlgClosed k]
    [FiniteDimensional k V] (hV : IsIndecomposableModule k[X] V) :
    ∃ (lam : k) (n : ℕ), 1 ≤ n ∧ Nonempty (V ≃ₗ[k[X]] JordanBlockModule k lam n) := by
  classical
  have : Module.Finite k[X] V := Module.Finite.of_restrictScalars_finite k k[X] V
  obtain ⟨ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_directSum_of_isTorsion
    (isTorsion_of_finiteDimensional_polynomial (k := k) (V := V))
  obtain ⟨v, hv⟩ := @exists_ne V hV.1 (0 : V)
  have hφv : φ v ≠ 0 := fun h => hv (φ.injective (by rw [h, map_zero]))
  obtain ⟨i0, hi0⟩ : ∃ i0, (φ v) i0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφv (DFinsupp.ext hcon)
  let M : ι → Type _ := fun i => k[X] ⧸ k[X] ∙ p i ^ e i
  let f : Module.End k[X] V :=
    φ.symm.toLinearMap ∘ₗ (DirectSum.lof k[X] ι M i0 ∘ₗ DirectSum.component k[X] ι M i0) ∘ₗ
      φ.toLinearMap
  have hf : ∀ x, φ (f x) = DirectSum.lof k[X] ι M i0 (φ x i0) := by
    intro x
    simp [f]
    rfl
  have hproj : ∀ x, f (f x) = f x := by
    intro x
    apply φ.injective
    rw [hf, hf]
    simp
  have hcompl : IsCompl (LinearMap.range f) (LinearMap.ker f) :=
    LinearMap.IsIdempotentElem.isCompl (f := f) (LinearMap.ext hproj)
  have hinj : Function.Injective (DirectSum.lof k[X] ι M i0) := fun a b h => by
    simpa using congrArg (DirectSum.component k[X] ι M i0) h
  rcases hV.2 _ _ hcompl with hr | hk
  · exfalso
    have h0 : f v = 0 := by
      have : f v ∈ LinearMap.range f := LinearMap.mem_range_self f v
      rw [hr] at this
      exact this
    have : φ (f v) = 0 := by rw [h0, map_zero]
    rw [hf] at this
    exact hi0 (hinj (by rw [this, map_zero]))
  · -- the component at `i0` is a bijection `V → M i0`
    let c : V →ₗ[k[X]] M i0 := DirectSum.component k[X] ι M i0 ∘ₗ φ.toLinearMap
    have hc_inj : Function.Injective c := by
      rw [← LinearMap.ker_eq_bot]
      rw [eq_bot_iff]
      intro x hx
      have hx' : (φ x) i0 = 0 := hx
      have : f x = 0 := φ.injective (by rw [hf, hx', map_zero, map_zero])
      have : x ∈ LinearMap.ker f := this
      rw [hk] at this
      exact this
    have hc_surj : Function.Surjective c := by
      intro y
      refine ⟨φ.symm (DirectSum.lof k[X] ι M i0 y), ?_⟩
      simp [c]
    let ψ : V ≃ₗ[k[X]] M i0 := LinearEquiv.ofBijective c ⟨hc_inj, hc_surj⟩
    -- identify the irreducible `p i0` with `X - C lam`
    have hdeg : (p i0).degree ≠ 0 := fun h => (hp i0).not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
    obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root (p i0) hdeg
    have hdvd : X - C lam ∣ p i0 := Polynomial.dvd_iff_isRoot.2 hlam
    have hass : Associated ((X - C lam) ^ e i0) (p i0 ^ e i0) :=
      ((irreducible_X_sub_C lam).associated_of_dvd (hp i0) hdvd).pow_pow
    have hspan : (k[X] ∙ p i0 ^ e i0) = Ideal.span {(X - C lam) ^ e i0} :=
      (Ideal.span_singleton_eq_span_singleton.2 hass).symm
    -- the exponent is positive, since `M i0` has a nonzero element
    have hpos : 1 ≤ e i0 := by
      by_contra hlt
      have h0 : e i0 = 0 := by omega
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ ((φ v) i0)
      apply hi0
      rw [← hr, Submodule.Quotient.mk_eq_zero]
      simp [h0]
    exact ⟨lam, e i0, hpos, ⟨ψ.trans (Submodule.quotEquivOfEq _ _ hspan)⟩⟩

end JordanIndecomposable

end UndergradKB.RepresentationTheory
