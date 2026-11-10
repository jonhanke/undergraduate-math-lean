import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import UndergradKB.Common.Attr

/-!
# Ordinary generating functions: formal calculus and products (Keller--Trotter, Chapter 8)

Source: Keller--Trotter, *Applied Combinatorics* (2017), Section 8.2 (pp. 183--186).
-/

namespace UndergradKB.Combinatorics

open PowerSeries Finset

section Calculus

/-- `1/(1-x) = 1 + x + x^2 + ...` as a formal power series over `ℚ`. -/
lemma inv_one_sub_X : (1 - X : ℚ⟦X⟧)⁻¹ = mk 1 := by
  refine ((PowerSeries.eq_inv_iff_mul_eq_one ?_).2 (mk_one_mul_one_sub_eq_one ℚ)).symm
  simp

/-- `1/(1+x) = 1 - x + x^2 - ...` as a formal power series over `ℚ`. -/
lemma inv_one_add_X : (1 + X : ℚ⟦X⟧)⁻¹ = mk fun n => (-1 : ℚ) ^ n := by
  refine ((PowerSeries.eq_inv_iff_mul_eq_one ?_).2 (mk_neg_one_pow_mul_one_add_eq_one ℚ)).symm
  simp

/-- CO-197. Formal differentiation of `1/(1-x)`: `d/dx (1-x)⁻¹ = ((1-x)⁻¹)^2 = ∑ (n+1) x^n`. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
theorem derivative_inv_one_sub_X :
    derivative (1 - X : ℚ⟦X⟧)⁻¹ = ((1 - X : ℚ⟦X⟧)⁻¹) ^ 2 ∧
      ((1 - X : ℚ⟦X⟧)⁻¹) ^ 2 = mk fun n => (n : ℚ) + 1 := by
  constructor
  · rw [PowerSeries.derivative_inv']
    simp
  · rw [inv_one_sub_X]
    have h := mk_one_pow_eq_mk_choose_add (S := ℚ) (d := 1)
    rw [h]
    ext n
    simp [add_comm]

/-- CO-197. Term-by-term formal integration over `ℚ`: the constant term is `0` and the coefficient
of `x^(n+1)` is `a_n / (n+1)`. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
noncomputable def formalIntegral (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else coeff (n - 1) f / n

lemma coeff_formalIntegral_succ (f : ℚ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (formalIntegral f) = coeff n f / ((n : ℚ) + 1) := by
  simp [formalIntegral]

/-- CO-197. Differentiating the formal integral gives back the series. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
theorem derivative_formalIntegral (f : ℚ⟦X⟧) : derivative (formalIntegral f) = f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_formalIntegral_succ]
  field_simp

/-- CO-197. Integrating the derivative recovers the series up to its constant term. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
theorem formalIntegral_derivative (f : ℚ⟦X⟧) :
    formalIntegral (derivative f) = f - C (constantCoeff f) := by
  ext n
  rcases n with _ | n
  · simp [formalIntegral]
  · rw [coeff_formalIntegral_succ, PowerSeries.coeff_derivative]
    simp only [map_sub, PowerSeries.coeff_C]
    simp
    field_simp

/-- CO-197. The formal series `log(1+x) = ∑_{n ≥ 1} (-1)^(n+1) x^n / n`. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
noncomputable def formalLog1p : ℚ⟦X⟧ :=
  mk fun n => if n = 0 then 0 else (-1 : ℚ) ^ (n + 1) / n

/-- CO-197. `log(1+x)` is the formal integral of `1/(1+x)`, and its derivative is `(1+x)⁻¹`. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
theorem formalLog1p_eq_integral :
    formalLog1p = formalIntegral (1 + X : ℚ⟦X⟧)⁻¹ ∧ derivative formalLog1p = (1 + X : ℚ⟦X⟧)⁻¹ := by
  have h : formalLog1p = formalIntegral (1 + X : ℚ⟦X⟧)⁻¹ := by
    rw [inv_one_add_X]
    ext n
    rcases n with _ | n
    · simp [formalLog1p, formalIntegral]
    · simp only [formalLog1p, formalIntegral, coeff_mk]
      simp
      rw [pow_succ, pow_succ]
      ring
  exact ⟨h, by rw [h, derivative_formalIntegral]⟩

/-- CO-197. The series `∑ n! x^n` is a legitimate formal power series (it has no analytic
meaning, but formal power series need no convergence); its coefficients are the factorials. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
noncomputable def factorialSeries : ℚ⟦X⟧ := mk fun n => (n.factorial : ℚ)

theorem coeff_factorialSeries (n : ℕ) : coeff n factorialSeries = (n.factorial : ℚ) := by
  simp [factorialSeries]

end Calculus

section Products

open scoped Classical

/-- The generating function `∑_{s ∈ S} x^s` of a set `S ⊆ ℕ` of allowed values of a variable
(over `ℕ`, so that infinite `S` such as `{m | 1 ≤ m}` are allowed). -/
noncomputable def allowedSeries (S : Set ℕ) : ℕ⟦X⟧ := mk fun m => if m ∈ S then 1 else 0

/-- CO-199. Product principle for distributions with a restriction on each variable: the number of
solutions `l` of `∑ l i = n` with `l i ∈ S i` for every `i` equals the coefficient of `x^n` in
`∏ i, (∑_{s ∈ S i} x^s)`.  (Solutions are the elements of `finsuppAntidiag univ n`.) -/
@[kb "kellertrotter2017" "Example 8.4, p. 184"]
theorem card_solutions_eq_coeff_prod {ι : Type*} [Fintype ι] (S : ι → Set ℕ) (n : ℕ) :
    ((finsuppAntidiag (univ : Finset ι) n).filter fun l => ∀ i, l i ∈ S i).card =
      coeff n (∏ i, allowedSeries (S i)) := by
  rw [PowerSeries.coeff_prod]
  simp only [allowedSeries, coeff_mk]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.prod_boole]
  simp

/-- CO-199. Function form of the product principle: the set of `x : ι → ℕ` with `x i ∈ S i` and
`∑ x i = n` has as many elements as the coefficient of `x^n` in `∏ i, ∑_{s ∈ S i} x^s`. -/
@[kb "kellertrotter2017" "Example 8.4, p. 184"]
theorem ncard_solutions_eq_coeff_prod {ι : Type*} [Fintype ι] (S : ι → Set ℕ) (n : ℕ) :
    {x : ι → ℕ | (∀ i, x i ∈ S i) ∧ ∑ i, x i = n}.ncard =
      coeff n (∏ i, allowedSeries (S i)) := by
  rw [← card_solutions_eq_coeff_prod, ← Set.ncard_coe_finset]
  have h : {x : ι → ℕ | (∀ i, x i ∈ S i) ∧ ∑ i, x i = n} =
      (fun l : ι →₀ ℕ => (l : ι → ℕ)) ''
        ↑((finsuppAntidiag (univ : Finset ι) n).filter fun l => ∀ i, l i ∈ S i) := by
    ext x
    constructor
    · rintro ⟨hS, hsum⟩
      refine ⟨Finsupp.equivFunOnFinite.symm x, ?_, rfl⟩
      simp only [Finset.coe_filter, mem_finsuppAntidiag, Set.mem_ofPred_eq]
      refine ⟨⟨?_, Finset.subset_univ _⟩, hS⟩
      simpa [Finsupp.sum_fintype] using hsum
    · rintro ⟨l, hl, rfl⟩
      simp only [Finset.coe_filter, mem_finsuppAntidiag, Set.mem_ofPred_eq] at hl
      refine ⟨hl.2, ?_⟩
      simpa [Finsupp.sum_fintype] using hl.1.1
  rw [h, Set.ncard_image_of_injective _ DFunLike.coe_injective]

/-- `x / (1 - x)`, the generating function of "at least one" (positive part); over `ℕ` it is
`x * (1 + x + x^2 + ...)`, where `mk 1 = (1-x)⁻¹`. -/
noncomputable def positivePartSeries : ℕ⟦X⟧ := X * mk 1

lemma positivePartSeries_eq : positivePartSeries = allowedSeries {m | 1 ≤ m} := by
  ext m
  rcases m with _ | m
  · simp [positivePartSeries, allowedSeries]
  · simp [positivePartSeries, allowedSeries, PowerSeries.coeff_succ_X_mul]

/-- `(1 + x + x^2 + ...)^(d+1)` over `ℕ` (Mathlib states this over commutative rings). -/
lemma mk_one_pow_nat (d : ℕ) :
    (mk 1 : ℕ⟦X⟧) ^ (d + 1) = (mk fun n => Nat.choose (d + n) d : ℕ⟦X⟧) := by
  induction d with
  | zero => ext; simp
  | succ d hd =>
    ext n
    rw [pow_add, hd, pow_one, mul_comm, coeff_mul]
    simp_rw [coeff_mk, Pi.one_apply, one_mul]
    rw [Finset.sum_antidiagonal_choose_add, add_right_comm]

/-- CO-199. Compositions into five positive parts: the coefficient of `x^n` in `(x/(1-x))^5` is
`C(n-1, 4)`. -/
@[kb "kellertrotter2017" "Example 8.4, p. 184"]
theorem coeff_positivePartSeries_pow_five (n : ℕ) :
    coeff n (positivePartSeries ^ 5) = (n - 1).choose 4 := by
  have h : positivePartSeries ^ 5 = X ^ 5 * mk fun m => Nat.choose (4 + m) 4 := by
    rw [positivePartSeries, mul_pow, mk_one_pow_nat 4]
  rw [h, PowerSeries.coeff_X_pow_mul']
  split_ifs with h5
  · simp only [coeff_mk]
    congr 1
    omega
  · rw [Nat.choose_eq_zero_of_lt]
    omega

/-- CO-199. The number of ways to write `n` as an ordered sum of five positive integers (the book's
`(x/(1-x))^5` example) is `C(n-1, 4)`. -/
@[kb "kellertrotter2017" "Example 8.4, p. 184"]
theorem ncard_compositions_five_parts (n : ℕ) :
    {x : Fin 5 → ℕ | (∀ i, 1 ≤ x i) ∧ ∑ i, x i = n}.ncard = (n - 1).choose 4 := by
  have h := ncard_solutions_eq_coeff_prod (fun _ : Fin 5 => {m : ℕ | 1 ≤ m}) n
  simp only [Set.mem_ofPred_eq] at h
  rw [h, ← positivePartSeries_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    coeff_positivePartSeries_pow_five]

end Products

end UndergradKB.Combinatorics
