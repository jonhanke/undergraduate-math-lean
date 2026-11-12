import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import UndergradKB.RepresentationTheory.SchurFunctors
import UndergradKB.RepresentationTheory.FrobeniusCounting
import UndergradKB.Common.Attr

/-! # The trace identity behind the Weyl character formula (Etingof et al., Theorem 4.63)

For a permutation `σ` of `Fin n` and a diagonal matrix `g = diag x` on `ℂ^N`, the trace of `σ` composed with
`g ⊗ ⋯ ⊗ g` on `(ℂ^N)^{⊗ n}` equals the polynomial `∏_m p_m^{i_m(σ)}` (`cyclePoly`) evaluated at `x`.

* `eval_cyclePoly_eq_sum`: the evaluation is the sum, over `σ`-invariant colourings `f : Fin n → Fin N`, of
  `∏_a x (f a)`;
* `trace_perm_comp_tensorPowerMap_diagonal`: the trace is the same sum, computed in the tensor basis.
-/

namespace UndergradKB.RepresentationTheory

open Finset
open scoped Classical TensorProduct

/-- Evaluating `cyclePoly` at `x` gives the sum over `σ`-invariant colourings of the monomial weights. -/
theorem eval_cyclePoly_eq_sum (n N : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin N → ℂ) :
    MvPolynomial.eval x (cyclePoly n N σ) =
      ∑ f ∈ univ.filter (fun f : Fin n → Fin N => f ∘ σ = f), ∏ a, x (f a) := by
  have h3 : cyclePoly n N σ = ∏ q : CycleClasses σ, MvPolynomial.psum (Fin N) ℂ (classSize σ q) := by
    unfold cyclePoly
    rw [prod_classSize_eq σ (fun m => MvPolynomial.psum (Fin N) ℂ m), Fintype.card_fin]
  rw [h3, map_prod]
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X]
  rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin N))) (fun q j => x j ^ classSize σ q),
    Fintype.piFinset_univ]
  have key : ∀ h : CycleClasses σ → Fin N,
      ∏ q, x (h q) ^ classSize σ q =
        ∏ a, x ((h ∘ Quotient.mk (Equiv.Perm.SameCycle.setoid σ)) a) := by
    intro h
    rw [← Finset.prod_fiberwise univ (Quotient.mk (Equiv.Perm.SameCycle.setoid σ))
      (fun a => x ((h ∘ Quotient.mk (Equiv.Perm.SameCycle.setoid σ)) a))]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => x (h q))
      (fun a ha => by simp only [mem_filter, mem_univ, true_and] at ha; simp [ha]), Finset.prod_const]
    rfl
  simp only [key]
  refine Finset.sum_bij (fun h _ => h ∘ Quotient.mk (Equiv.Perm.SameCycle.setoid σ)) ?_ ?_ ?_ ?_
  · intro h _
    simp only [mem_filter, mem_univ, true_and]
    funext a
    simp only [Function.comp_apply]
    congr 1
    exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.2 Equiv.Perm.SameCycle.rfl)
  · intro h1 _ h2 _ heq
    funext q
    induction q using Quotient.inductionOn with | _ a => exact congrFun heq a
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    refine ⟨Quotient.lift f (fun x y hxy => eq_of_sameCycle f σ hf hxy), mem_univ _, ?_⟩
    funext a
    rfl
  · intro h _
    rfl

/-- Trace of the permutation action composed with `g ⊗ ⋯ ⊗ g` for `g = diag x`: the weight sum over
`σ`-invariant colourings, computed in the tensor basis. -/
theorem trace_perm_comp_tensorPowerMap_diagonal_eq_sum (n N : ℕ) (σ : Equiv.Perm (Fin n))
    (x : Fin N → ℂ) :
    LinearMap.trace ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ)
        (tensorPowerPermRep ℂ n (Fin N → ℂ) σ ∘ₗ
          tensorPowerMap n (Matrix.mulVecLin (Matrix.diagonal x))) =
      ∑ f ∈ univ.filter (fun f : Fin n → Fin N => f ∘ σ = f), ∏ a, x (f a) := by
  set b := Basis.piTensorProduct (fun _ : Fin n => Pi.basisFun ℂ (Fin N)) with hb
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  have hI : ∀ I : Fin n → Fin N,
      LinearMap.toMatrix b b (tensorPowerPermRep ℂ n (Fin N → ℂ) σ ∘ₗ
          tensorPowerMap n (Matrix.mulVecLin (Matrix.diagonal x))) I I =
        if I ∘ ⇑σ⁻¹ = I then ∏ a, x (I a) else 0 := by
    intro I
    have e1 : (tensorPowerPermRep ℂ n (Fin N → ℂ) σ ∘ₗ
          tensorPowerMap n (Matrix.mulVecLin (Matrix.diagonal x))) (b I) =
        (∏ l, x (I l)) • PiTensorProduct.tprod ℂ (fun i => (Pi.basisFun ℂ (Fin N)) (I (σ⁻¹ i))) := by
      have e0 : ∀ l, Matrix.mulVecLin (Matrix.diagonal x) (Pi.basisFun ℂ (Fin N) (I l)) =
          x (I l) • Pi.basisFun ℂ (Fin N) (I l) := by
        intro l
        simp
        ext j
        by_cases h : j = I l <;> simp [h]
      simp only [hb, LinearMap.comp_apply, Basis.piTensorProduct_apply, tensorPowerMap,
        PiTensorProduct.map_tprod, e0, MultilinearMap.map_smul_univ, map_smul,
        tensorPowerPermRep_tprod]
    rw [LinearMap.toMatrix_apply, e1, map_smul]
    simp only [hb, Basis.piTensorProduct_repr_tprod_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hc : I ∘ ⇑σ⁻¹ = I
    · simp only [hc, ↓reduceIte]
      have : ∀ i, ((Pi.basisFun ℂ (Fin N)).repr ((Pi.basisFun ℂ (Fin N)) (I (σ⁻¹ i)))) (I i) = 1 := by
        intro i
        have := congrFun hc i
        simp_all
      rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const_one, mul_one]
    · simp only [hc, ↓reduceIte]
      obtain ⟨i, hi⟩ := not_forall.1 (fun h => hc (funext h))
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
      simp only [Function.comp_apply] at hi
      simp [Pi.single_apply]
      exact fun h => hi h.symm
  simp only [Matrix.diag, hI]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext f
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    funext a
    have := congrFun h (σ a)
    simpa using this.symm
  · intro h
    funext a
    have := congrFun h (σ⁻¹ a)
    simpa using this.symm

/-- The trace of `σ ∘ (g ⊗ ⋯ ⊗ g)` on `(ℂ^N)^{⊗ n}` for `g = diag x` is the polynomial
`∏_m p_m^{i_m(σ)}` evaluated at `x`. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem trace_perm_comp_tensorPowerMap_diagonal (n N : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin N → ℂ) :
    LinearMap.trace ℂ (⨂[ℂ] _ : Fin n, Fin N → ℂ)
        (tensorPowerPermRep ℂ n (Fin N → ℂ) σ ∘ₗ
          tensorPowerMap n (Matrix.mulVecLin (Matrix.diagonal x))) =
      MvPolynomial.eval x (cyclePoly n N σ) := by
  rw [trace_perm_comp_tensorPowerMap_diagonal_eq_sum, eval_cyclePoly_eq_sum]

end UndergradKB.RepresentationTheory
