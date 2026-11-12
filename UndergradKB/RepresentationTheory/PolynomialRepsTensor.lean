import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fintype.Sigma
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialReps

/-! # Homogeneous polynomials as functionals on tensor powers (Etingof et al., Theorem 4.66)

Every homogeneous polynomial of degree `n` in the `N²` matrix entries of `g` is a linear functional of the
tensor power `g ⊗ ⋯ ⊗ g` acting on `(ℂ^N)^{⊗ n}`. This is the polynomial-side input used to show that
polynomial representations of degree `n` occur inside sums of tensor powers.

* `tensorPowerMap_coeff`: the matrix coefficients of `g ⊗ ⋯ ⊗ g` in the product basis.
* `exists_linear_tensorPower_monomial`: the case of a monomial with exponent vector of total degree `n`.
* `exists_linear_tensorPower_of_isHomogeneous`: the general statement.
* `exists_linear_tensorPowerGL_of_isHomogeneous`: the same for elements of `GL_N(ℂ)`.
-/

namespace UndergradKB.RepresentationTheory

open Matrix MvPolynomial PiTensorProduct
open scoped TensorProduct

variable {N n : ℕ}

/-- Matrix coefficients of `g ⊗ ⋯ ⊗ g` in the product basis are products of matrix entries. -/
theorem tensorPowerMap_coeff (g : Matrix (Fin N) (Fin N) ℂ) (I J : Fin n → Fin N) :
    (Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun ℂ (Fin N))).repr
      (tensorPowerMap n (Matrix.mulVecLin g)
        (Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun ℂ (Fin N)) J)) I
      = ∏ l, g (I l) (J l) := by
  simp [tensorPowerMap, Basis.piTensorProduct_apply, Basis.piTensorProduct_repr_tprod_apply]

/-- A list of `n` matrix positions realizing a given exponent vector of total degree `n`. -/
theorem exists_index_of_degree (d : (Fin N × Fin N) →₀ ℕ) (h : ∑ p, d p = n) :
    ∃ f : Fin n → Fin N × Fin N, ∀ x : Fin N × Fin N → ℂ, ∏ l, x (f l) = ∏ p, x p ^ d p := by
  have hc : Fintype.card (Σ p, Fin (d p)) = Fintype.card (Fin n) := by
    simp [Fintype.card_sigma, h]
  let e := Fintype.equivOfCardEq hc
  refine ⟨fun l => (e.symm l).1, fun x => ?_⟩
  have h1 : ∏ l, x (e.symm l).1 = ∏ s : (Σ p, Fin (d p)), x s.1 :=
    Equiv.prod_comp e.symm (fun s : (Σ p, Fin (d p)) => x s.1)
  rw [h1, Fintype.prod_sigma]
  simp

/-- A monomial of degree `n` in the matrix entries is a linear functional of `g ⊗ ⋯ ⊗ g`. -/
theorem exists_linear_tensorPower_monomial (d : (Fin N × Fin N) →₀ ℕ) (h : ∑ p, d p = n) :
    ∃ ℓ : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ) →ₗ[ℂ] ℂ,
      ∀ g : Matrix (Fin N) (Fin N) ℂ,
        ℓ (tensorPowerMap n (Matrix.mulVecLin g)) = ∏ p, g p.1 p.2 ^ d p := by
  obtain ⟨f, hf⟩ := exists_index_of_degree d h
  let b := Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun ℂ (Fin N))
  refine ⟨(b.coord (fun l => (f l).1)) ∘ₗ
    (LinearMap.applyₗ (R := ℂ) (b (fun l => (f l).2))), fun g => ?_⟩
  have := tensorPowerMap_coeff g (fun l => (f l).1) (fun l => (f l).2)
  rw [← hf (fun p => g p.1 p.2)]
  simpa [b] using this

/-- Every homogeneous polynomial of degree `n` in the matrix entries is a linear functional of
`g ⊗ ⋯ ⊗ g`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem exists_linear_tensorPower_of_isHomogeneous (P : MvPolynomial (Fin N × Fin N) ℂ)
    (hP : P.IsHomogeneous n) :
    ∃ ℓ : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ) →ₗ[ℂ] ℂ,
      ∀ g : Matrix (Fin N) (Fin N) ℂ,
        ℓ (tensorPowerMap n (Matrix.mulVecLin g)) = MvPolynomial.eval (fun p => g p.1 p.2) P := by
  have key : ∀ d : (Fin N × Fin N) →₀ ℕ, ∑ p, d p = n →
      ∃ ℓ : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ) →ₗ[ℂ] ℂ,
        ∀ g : Matrix (Fin N) (Fin N) ℂ,
          ℓ (tensorPowerMap n (Matrix.mulVecLin g)) = ∏ p, g p.1 p.2 ^ d p :=
    fun d h => exists_linear_tensorPower_monomial d h
  choose! L hL using key
  have hdeg : ∀ d ∈ P.support, ∑ p, d p = n := by
    intro d hd
    have := hP (mem_support_iff.mp hd)
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    simpa [Pi.one_def] using this
  refine ⟨∑ d ∈ P.support, P.coeff d • L d, fun g => ?_⟩
  rw [MvPolynomial.eval_eq', LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp [hL d (hdeg d hd) g]

/-- The same statement for elements of `GL_N(ℂ)` acting on `(ℂ^N)^{⊗ n}`. -/
theorem exists_linear_tensorPowerGL_of_isHomogeneous (P : MvPolynomial (Fin N × Fin N) ℂ)
    (hP : P.IsHomogeneous n) :
    ∃ ℓ : Module.End ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ) →ₗ[ℂ] ℂ,
      ∀ g : GL (Fin N) ℂ, ℓ (tensorPowerGL N ℂ n g) = MvPolynomial.eval (glEntries N ℂ g) P := by
  obtain ⟨ℓ, hℓ⟩ := exists_linear_tensorPower_of_isHomogeneous P hP
  exact ⟨ℓ, fun g => hℓ (g : Matrix (Fin N) (Fin N) ℂ)⟩

end UndergradKB.RepresentationTheory
