import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas
import UndergradKB.Common.Attr

/-! # Exterior powers and the determinant (Etingof et al., Problem 1.49)

* `exteriorPower_top_map`: for a basis `b` of an `N`-dimensional vector space, `⋀ᴺ f` multiplies the
  generator `b₁ ∧ ... ∧ b_N` of the top exterior power by `det f`.
* `det_comp_via_exteriorPower`: the multiplicativity of the determinant derived from functoriality
  of the top exterior power.
* `finrank_exteriorPower_eq`: `dim ⋀ⁿ V = choose (dim V) n` (from Mathlib).
* `trace_exteriorPower_map`: the trace of `⋀ⁿ f` is the sum of the principal `n × n` minors of the
  matrix of `f`.
* Not included: symmetric powers (dimension, trace), bimodule tensor associativity and Hom-tensor
  adjunction.
-/

namespace UndergradKB.RepresentationTheory

open Module

section Top

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {N : ℕ}

/-- The top exterior power `⋀ᴺ f` multiplies the generator `ιMulti b` by the determinant of `f`. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem exteriorPower_top_map (b : Basis (Fin N) k V) (f : V →ₗ[k] V) :
    exteriorPower.map N f (exteriorPower.ιMulti k N b) =
      LinearMap.det f • exteriorPower.ιMulti k N b := by
  rw [← sub_eq_zero]
  refine (forall_dual_apply_eq_zero_iff k _).1 fun φ => ?_
  have hg := AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (exteriorPower.ιMulti k N))
  have h1 := congrArg (fun g => g (f ∘ b)) hg
  simp only [LinearMap.compAlternatingMap_apply, smul_apply, smul_eq_mul,
    Basis.det_comp, Basis.det_self] at h1
  rw [exteriorPower.map_apply_ιMulti, map_sub, map_smul, h1]
  simp [mul_comm]

/-- The generator `ιMulti b` of the top exterior power is nonzero. -/
theorem ιMulti_basis_ne_zero (b : Basis (Fin N) k V) :
    exteriorPower.ιMulti k N b ≠ 0 := by
  intro h
  have := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h
  simp only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero, Basis.det_self] at this
  exact one_ne_zero this

/-- Multiplicativity of the determinant, derived from functoriality of the top exterior power. -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem det_comp_via_exteriorPower (b : Basis (Fin N) k V) (f g : V →ₗ[k] V) :
    LinearMap.det (f ∘ₗ g) = LinearMap.det f * LinearMap.det g := by
  have h1 := exteriorPower_top_map b (f ∘ₗ g)
  rw [exteriorPower.map_comp, LinearMap.comp_apply, exteriorPower_top_map, map_smul,
    exteriorPower_top_map, smul_smul] at h1
  have h2 := ιMulti_basis_ne_zero b
  have := smul_left_injective k h2 h1
  rw [mul_comm]
  exact this.symm

end Top

/-- The dimension of the `n`th exterior power of a finite-dimensional space is `choose (dim V) n`
(Mathlib's `exteriorPower.finrank_eq`). -/
@[kb "etingof2011" "Problem 1.49(d), p. 18"]
theorem finrank_exteriorPower_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (⋀[k]^n V) = (Module.finrank k V).choose n :=
  exteriorPower.finrank_eq k V n

section Trace

open Set.powersetCard

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I] [Fintype I]
  (n : ℕ) (b : Module.Basis I R M)

/-- The trace of the `n`th exterior power of an endomorphism is the sum of its principal `n × n`
minors (the `n`th elementary symmetric function of the eigenvalues). -/
@[kb "etingof2011" "Problem 1.49(e)-(g), p. 18"]
theorem trace_exteriorPower_map (f : M →ₗ[R] M) :
    LinearMap.trace R (⋀[R]^n M) (exteriorPower.map n f) =
      ∑ s : Set.powersetCard I n,
        (Matrix.of fun i j => LinearMap.toMatrix b b f (ofFinEmbEquiv.symm s i)
          (ofFinEmbEquiv.symm s j)).det := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (b.exteriorPower n), Matrix.trace]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply]

end Trace

end UndergradKB.RepresentationTheory
