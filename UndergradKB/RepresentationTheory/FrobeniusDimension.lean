import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.RingTheory.Polynomial.Pochhammer
import UndergradKB.RepresentationTheory.FrobeniusFormula
import UndergradKB.Common.Attr

/-! # The value of the Frobenius character at the identity (Etingof et al., formula (5), p. 63)

For `λ` with `∑ λ_i = n` and `l_i = λ_i + N - 1 - i`, the value `θ_λ(1)` of `frobChar` at the identity satisfies
`θ_λ(1) ∏ l_i! = n! ∏_{i<j} (l_i - l_j)`.  The proof expands `cyclePoly n N 1 = (x_1 + ⋯ + x_N)^n`
by the multinomial theorem, turns the signed sum into the determinant of falling factorials, and compares it with
the Vandermonde determinant.
-/

namespace UndergradKB.RepresentationTheory

open Finset
open scoped Classical

variable {n N : ℕ}

lemma classSize_one (q : CycleClasses (1 : Equiv.Perm (Fin n))) : classSize 1 q = 1 := by
  induction q using Quotient.inductionOn with | _ a => ?_
  unfold classSize
  rw [Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext b
  simp [Quotient.eq, Equiv.Perm.SameCycle.setoid]

lemma card_cycleClasses_one (n : ℕ) :
    Fintype.card (CycleClasses (1 : Equiv.Perm (Fin n))) = n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (CycleClasses (1 : Equiv.Perm (Fin n)))))
    (f := fun a => (Quotient.mk (Equiv.Perm.SameCycle.setoid 1) a)) (fun _ _ => mem_univ _)
  have h2 : ∀ q ∈ (univ : Finset (CycleClasses (1 : Equiv.Perm (Fin n)))),
      (univ.filter fun a : Fin n => (Quotient.mk (Equiv.Perm.SameCycle.setoid 1) a) = q).card = 1 :=
    fun q _ => classSize_one q
  rw [sum_congr rfl h2] at h
  simpa using h.symm

lemma cyclePoly_one (n N : ℕ) :
    cyclePoly n N 1 = (∑ i, MvPolynomial.X i : MvPolynomial (Fin N) ℂ) ^ n := by
  have h3 : cyclePoly n N 1 =
      ∏ q : CycleClasses (1 : Equiv.Perm (Fin n)), MvPolynomial.psum (Fin N) ℂ (classSize 1 q) := by
    unfold cyclePoly
    rw [prod_classSize_eq 1 (fun m => MvPolynomial.psum (Fin N) ℂ m), Fintype.card_fin]
  rw [h3]
  simp_rw [classSize_one]
  rw [prod_const, card_univ, card_cycleClasses_one]
  simp [MvPolynomial.psum]

lemma coeffChar_one_mul (α : Fin N → ℕ) (h : ∑ i, α i = n) :
    coeffChar n N α 1 * ∏ i, ((α i).factorial : ℂ) = n.factorial := by
  unfold coeffChar
  rw [cyclePoly_one, MvPolynomial.coeff_sum_X_pow_of_fintype]
  have hs : (Finsupp.equivFunOnFinite.symm α).sum (fun _ m => m) = n := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using h
  rw [if_pos hs, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  have := Nat.multinomial_spec (univ : Finset (Fin N)) (Finsupp.equivFunOnFinite.symm α)
  simp only [Finsupp.coe_equivFunOnFinite_symm] at this
  rw [h] at this
  have h2 := congrArg (Nat.cast : ℕ → ℂ) this
  push_cast at h2
  rw [← h2]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  ring

lemma term_mul {lam : Fin N → ℕ} (hs : ∑ i, lam i = n) (σ : Equiv.Perm (Fin N)) :
    (if TermOK lam σ then coeffChar n N (termExp lam σ) 1 else 0) *
        ∏ i, (((lam i + rhoExp N i).factorial : ℕ) : ℂ) =
      (n.factorial : ℂ) *
        ∏ i, (((lam i + rhoExp N i).descFactorial (rhoExp N (σ.symm i)) : ℕ) : ℂ) := by
  by_cases h : TermOK lam σ
  · rw [if_pos h]
    have h1 := coeffChar_one_mul (n := n) (termExp lam σ) ((sum_termExp h).trans hs)
    have h2 : ∀ i, (((lam i + rhoExp N i).factorial : ℕ) : ℂ) =
        (((termExp lam σ i).factorial : ℕ) : ℂ) *
          (((lam i + rhoExp N i).descFactorial (rhoExp N (σ.symm i)) : ℕ) : ℂ) := by
      intro i
      rw [← Nat.cast_mul, ← Nat.factorial_mul_descFactorial (h i)]
      rfl
    simp_rw [h2]
    rw [prod_mul_distrib, ← mul_assoc, h1]
  · rw [if_neg h, zero_mul]
    unfold TermOK at h
    push_neg at h
    obtain ⟨i, hi⟩ := h
    symm
    rw [mul_eq_zero]
    right
    refine prod_eq_zero (mem_univ i) ?_
    rw [Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
    exact hi

lemma sum_sign_prod_eq_det (M : Matrix (Fin N) (Fin N) ℂ) :
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M i (σ.symm i) = M.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => ?_
  simp [Equiv.Perm.sign_inv]

lemma det_descFactorial (v : Fin N → ℕ) :
    (Matrix.of fun i j : Fin N => (((v i).descFactorial (rhoExp N j) : ℕ) : ℂ)).det =
      ∏ i : Fin N, ∏ j ∈ Ioi i, (((v i : ℕ) : ℂ) - (v j : ℂ)) := by
  set M : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.of fun i j : Fin N => (((v i).descFactorial (rhoExp N j) : ℕ) : ℂ) with hM
  rw [← Matrix.det_submatrix_equiv_self Fin.revPerm M]
  have h1 : M.submatrix Fin.revPerm Fin.revPerm =
      Matrix.of fun i j : Fin N => ((descPochhammer ℂ j).eval (((v (Fin.rev i) : ℕ) : ℂ))) := by
    ext i j
    have := j.isLt
    simp only [hM, Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply,
      descPochhammer_eval_eq_descFactorial, rhoExp, Fin.val_rev]
    congr 2
    omega
  rw [h1, ← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i => (((v (Fin.rev i) : ℕ) : ℂ))) (fun j => descPochhammer ℂ j)
    (fun i => descPochhammer_natDegree ℂ i) (fun i => monic_descPochhammer ℂ i),
    Matrix.det_vandermonde]
  rw [prod_comm' (s' := fun j => Iio j) (t' := univ) (fun x y => by simp)]
  rw [← Equiv.prod_comp Fin.revPerm]
  refine prod_congr rfl fun a _ => ?_
  have hm := Fin.map_revPerm_Iio (Fin.rev a)
  rw [Fin.rev_rev] at hm
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [← hm, prod_map]
  simp [Fin.rev_rev]

/-- **Value of the Frobenius character at the identity** (cleared of denominators). -/
@[kb "etingof2011" "formula (5), p. 63"]
theorem frobChar_one (lam : Fin N → ℕ) (hs : ∑ i, lam i = n) :
    frobChar n N lam 1 * ∏ i, (((lam i + rhoExp N i).factorial : ℕ) : ℂ) =
      (n.factorial : ℂ) * ∏ i, ∏ j ∈ Ioi i,
        ((((lam i + rhoExp N i : ℕ)) : ℂ) - ((lam j + rhoExp N j : ℕ) : ℂ)) := by
  rw [frobChar_eq_sum', sum_mul]
  simp_rw [mul_assoc, term_mul hs]
  simp_rw [mul_left_comm _ (n.factorial : ℂ)]
  rw [← mul_sum]
  congr 1
  rw [← det_descFactorial (fun i => lam i + rhoExp N i), ← sum_sign_prod_eq_det]
  rfl

/-- **The dimension formula** `θ_λ(1) = n! ∏_{i<j} (l_i - l_j) / ∏ l_i!`. -/
@[kb "etingof2011" "formula (5), p. 63"]
theorem frobChar_one_eq (lam : Fin N → ℕ) (hs : ∑ i, lam i = n) :
    frobChar n N lam 1 = ((n.factorial : ℂ) * ∏ i, ∏ j ∈ Ioi i,
        ((((lam i + rhoExp N i : ℕ)) : ℂ) - ((lam j + rhoExp N j : ℕ) : ℂ))) /
      ∏ i, (((lam i + rhoExp N i).factorial : ℕ) : ℂ) := by
  have hne : ∏ i, (((lam i + rhoExp N i).factorial : ℕ) : ℂ) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => by exact_mod_cast Nat.factorial_ne_zero _
  rw [eq_div_iff hne]
  exact frobChar_one lam hs

end UndergradKB.RepresentationTheory
