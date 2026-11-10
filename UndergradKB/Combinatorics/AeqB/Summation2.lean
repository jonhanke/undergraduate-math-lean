import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Field
import UndergradKB.Combinatorics.AeqB.Identities2
import UndergradKB.Combinatorics.Counting.Bell
import UndergradKB.Common.Attr

/-!
# Tree function, rooted labeled trees and Bell numbers as exponential generating functions

CO-211 (`exp (∑ m^(m-1) t^m / m!) = 1 + ∑ (n+1)^(n-1) t^n / n!`, eq. 2.2.3 of A=B),
CO-212 (the tree function satisfies `T = x e^T`) and CO-213 (the exponential generating
function of the Bell numbers is `exp (e^x - 1)`).  All three are identities of formal power series
over `ℚ`; the composition `exp ∘ g` is Mathlib's `PowerSeries.subst`.  The proofs show that both
sides solve `F' = g' F`, `F(0) = 1`, which has a unique formal solution.
-/

namespace UndergradKB.Combinatorics.AeqB
open Finset PowerSeries
open scoped Nat

/-- A formal solution of `F' = G F` is determined by `F(0)`. -/
lemma ode_unique (G F F' : ℚ⟦X⟧) (h1 : d⁄dX F = G * F) (h2 : d⁄dX F' = G * F')
    (h0 : coeff 0 F = coeff 0 F') : F = F' := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · exact h0
    · have e1 := congrArg (coeff n) h1
      have e2 := congrArg (coeff n) h2
      rw [coeff_derivative, coeff_mul] at e1 e2
      have hs : (∑ p ∈ antidiagonal n, coeff p.1 G * coeff p.2 F) =
          ∑ p ∈ antidiagonal n, coeff p.1 G * coeff p.2 F' :=
        sum_congr rfl fun p hp => by
          rw [ih p.2 (by have := mem_antidiagonal.1 hp; omega)]
      have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
      apply mul_right_cancel₀ hne
      rw [e1, e2, hs]

/-- `exp ∘ g` solves `F' = g' F` with `F(0) = 1`, for `g(0) = 0`. -/
lemma exp_subst_ode (g : ℚ⟦X⟧) (hg : constantCoeff g = 0) :
    d⁄dX ((exp ℚ).subst g) = d⁄dX g * (exp ℚ).subst g := by
  rw [derivative_subst (HasSubst.of_constantCoeff_zero' hg), derivative_exp, mul_comm]

lemma exp_subst_const (g : ℚ⟦X⟧) (hg : constantCoeff g = 0) :
    coeff 0 ((exp ℚ).subst g) = 1 := by
  have := constantCoeff_subst_of_constantCoeff_zero (a := g) hg (exp ℚ)
  rw [coeff_zero_eq_constantCoeff_apply]
  simp [constantCoeff_exp] at this
  exact this

/-! ### The tree function (CO-211, CO-212) -/

/-- The tree function `T(t) = ∑_{m ≥ 1} m^(m-1) t^m / m!`. -/
noncomputable def treeSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun m => if m = 0 then 0 else (((m ^ (m - 1) : ℕ) : ℚ) / (m ! : ℚ))

/-- The series `1 + ∑_{n ≥ 1} (n+1)^(n-1) t^n / n!`. -/
noncomputable def treeExpSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (((n + 1) ^ (n - 1) : ℕ) : ℚ) / (n ! : ℚ)

lemma treeSeries_const : constantCoeff treeSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [treeSeries]

lemma coeff_deriv_treeSeries (i : ℕ) :
    coeff i (d⁄dX treeSeries) = (((i + 1) ^ i : ℕ) : ℚ) / (i ! : ℚ) := by
  rw [coeff_derivative]
  simp only [treeSeries, coeff_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
    Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have h1 : (i ! : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((i : ℚ) + 1) ≠ 0 := by positivity
  field_simp

lemma deriv_treeExpSeries : d⁄dX treeExpSeries = d⁄dX treeSeries * treeExpSeries := by
  rw [mul_comm]
  ext n
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i treeExpSeries * coeff j (d⁄dX treeSeries))]
  have habel := congrArg (fun x : ℕ => (x : ℚ)) (Identities2.abel_special n)
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat] at habel
  have hn : (n ! : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have key : ∀ i ∈ range (n + 1), coeff i treeExpSeries * coeff (n - i) (d⁄dX treeSeries) =
      ((n.choose i : ℚ) * ((((i + 1) ^ (i - 1) : ℕ) : ℚ)) *
        ((((n - i + 1) ^ (n - i) : ℕ) : ℚ))) / (n ! : ℚ) := by
    intro i hi
    have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    rw [coeff_deriv_treeSeries]
    simp only [treeExpSeries, coeff_mk]
    rw [Nat.cast_choose ℚ hin]
    have h1 : (i ! : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have h2 : ((n - i)! : ℚ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
    field_simp
  rw [sum_congr rfl key, ← Finset.sum_div]
  simp only [treeExpSeries, coeff_mk, Nat.add_sub_cancel]
  have : ∑ i ∈ range (n + 1), (n.choose i : ℚ) * ((((i + 1) ^ (i - 1) : ℕ) : ℚ)) *
      ((((n - i + 1) ^ (n - i) : ℕ) : ℚ)) = (((n + 2) ^ n : ℕ) : ℚ) := by
    push_cast at habel ⊢
    rw [← habel]
  rw [this]
  have h3 : ((n + 1 : ℕ) ! : ℚ) = ((n : ℚ) + 1) * (n ! : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [h3]
  have h4 : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  rw [show ((n : ℚ) + 1 + 1) = n + 2 by ring]

/-- CO-211. Tree-function identity (eq. 2.2.3): as formal power series,
`exp (∑_{m ≥ 1} m^(m-1) t^m / m!) = 1 + ∑_{n ≥ 1} (n+1)^(n-1) t^n / n!`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (2.2.3), p. 33"]
theorem exp_treeSeries : (exp ℚ).subst treeSeries = treeExpSeries := by
  refine ode_unique (d⁄dX treeSeries) _ _ (exp_subst_ode _ treeSeries_const)
    deriv_treeExpSeries ?_
  rw [exp_subst_const _ treeSeries_const]
  simp [treeExpSeries]

/-- CO-212 (functional equation). The exponential generating function `T(x) = ∑ n^(n-1) x^n / n!`
of rooted labeled trees (Cayley's count `n^(n-1)`) satisfies `T = x e^T`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 194"]
theorem treeSeries_eq_X_mul_exp : treeSeries = X * (exp ℚ).subst treeSeries := by
  rw [exp_treeSeries]
  ext n
  rcases n with _ | n
  · simp [treeSeries]
  · rw [coeff_succ_X_mul]
    simp only [treeSeries, treeExpSeries, coeff_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ite_false, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    rcases n with _ | m
    · simp
    · have h1 : ((m + 1) ! : ℚ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
      have h2 : ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
      simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ]
      field_simp

/-! ### Bell numbers (CO-213) -/

/-- The exponential generating function `∑ B_n t^n / n!` of the Bell numbers. -/
noncomputable def bellSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (UndergradKB.Combinatorics.bellNumber n : ℚ) / (n ! : ℚ)

lemma deriv_bellSeries : d⁄dX bellSeries = d⁄dX (exp ℚ - 1) * bellSeries := by
  rw [map_sub, derivative_exp, derivative_one, sub_zero, mul_comm]
  ext n
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i bellSeries * coeff j (exp ℚ))]
  simp only [bellSeries, coeff_mk, coeff_exp, Algebra.algebraMap_self, RingHom.id_apply]
  have hb := congrArg (fun x : ℕ => (x : ℚ))
    (UndergradKB.Combinatorics.bellNumber_succ n)
  simp only [Nat.cast_sum, Nat.cast_mul] at hb
  have hn : (n ! : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have key : ∀ i ∈ range (n + 1),
      (UndergradKB.Combinatorics.bellNumber i : ℚ) / (i ! : ℚ) * (1 / ((n - i)! : ℚ)) =
        (n.choose i : ℚ) * (UndergradKB.Combinatorics.bellNumber i : ℚ) / (n ! : ℚ) := by
    intro i hi
    have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    rw [Nat.cast_choose ℚ hin]
    have h1 : (i ! : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have h2 : ((n - i)! : ℚ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
    field_simp
  rw [sum_congr rfl key, ← Finset.sum_div, ← hb, Nat.factorial_succ]
  push_cast
  field_simp

/-- CO-213. The exponential generating function of the Bell numbers is `exp (e^x - 1)`
(as formal power series: `B(x) = (exp ∘ (exp - 1))(x)`), a consequence of the recurrence
`B_{n+1} = ∑ C(n,k) B_k`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 195"]
theorem bellSeries_eq_exp_exp_sub_one : bellSeries = (exp ℚ).subst (exp ℚ - 1) := by
  have h0 : constantCoeff (exp ℚ - 1) = 0 := by simp [constantCoeff_exp]
  symm
  refine ode_unique (d⁄dX (exp ℚ - 1)) _ _ (exp_subst_ode _ h0) deriv_bellSeries ?_
  rw [exp_subst_const _ h0]
  simp [bellSeries, UndergradKB.Combinatorics.bellNumber]

end UndergradKB.Combinatorics.AeqB
