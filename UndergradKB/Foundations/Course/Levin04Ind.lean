import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.Lagrange
import UndergradKB.Common

/-! # Course layer: Levin, Chapter 4 (induction and sequences)
Rows of the checklist section "Induction and sequences" that are `in Mathlib` and stated only by Levin. -/

namespace UndergradKB.Foundations.Course

open Finset Polynomial

/-- FO-176. Two-step induction: `P 0`, `P 1`, and `P k ∧ P (k+1) → P (k+2)` give `P n` for all `n`. -/
@[kb "levin2025" "Example 4.6.2, p. 397"]
theorem levin_ex_4_6_2_two_step_induction (P : ℕ → Prop) (h0 : P 0) (h1 : P 1)
    (step : ∀ k, P k → P (k + 1) → P (k + 2)) : ∀ n, P n := fun n =>
  Nat.twoStepInduction h0 h1 step n

/-- FO-198. Telescoping: the sum of the differences `a (i+1) - a i` over `i < n` is `a n - a 0`. -/
@[kb "levin2025" "Telescoping §4.2.2, p. 350"]
theorem levin_s4_2_2_telescoping (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, (a (i + 1) - a i) = a n - a 0 :=
  Finset.sum_range_sub a n

/-- FO-204. A polynomial of degree at most `n` is determined by its values at `n+1` distinct points. -/
@[kb "levin2025" "Warning 4.3.11, p. 367"]
theorem levin_warning_4_3_11_poly_determined (n : ℕ) (f g : ℝ[X]) (hf : f.degree ≤ n)
    (hg : g.degree ≤ n) (s : Finset ℝ) (hs : s.card = n + 1)
    (h : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  have hn : ((n : ℕ) : WithBot ℕ) < (s.card : WithBot ℕ) := by
    rw [hs]; exact_mod_cast Nat.lt_succ_self n
  exact Polynomial.eq_of_degrees_lt_of_eval_finset_eq s (hf.trans_lt hn) (hg.trans_lt hn) h

/-- FO-206. For `x ≠ 1`, the geometric sum `1 + x + ... + x^(n-1)` equals `(x^n - 1)/(x - 1)`. -/
@[kb "levin2025" "Example 4.4.2, p. 375"]
theorem levin_ex_4_4_2_geom_sum (x : ℝ) (hx : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) :=
  geom_sum_eq hx n

/-- FO-206 (multiplied form). `(1 + x + ... + x^(n-1)) (x - 1) = x^n - 1`, with no hypothesis on `x`. -/
@[kb "levin2025" "Multiply, Shift, Subtract §4.4.2, p. 375"]
theorem levin_s4_4_2_geom_sum_mul (x : ℝ) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 :=
  geom_sum_mul x n

/-- FO-207. `r^n` solves a linear recurrence with constant coefficients exactly when `r` is a root
of its characteristic polynomial. -/
@[kb "levin2025" "Characteristic Roots, p. 377"]
theorem levin_char_roots_geom_solution_iff (E : LinearRecurrence ℝ) (r : ℝ) :
    (E.IsSolution fun n => r ^ n) ↔ E.charPoly.IsRoot r :=
  E.geom_sol_iff_root_charPoly r

/-- FO-208. A sequence solves a linear recurrence of the given order when each term is the
coefficient-weighted sum of the previous `order` terms. -/
@[kb "levin2025" "Def (D086), p. 379"]
theorem levin_d086_linear_recurrence_solution (E : LinearRecurrence ℝ) (u : ℕ → ℝ) :
    E.IsSolution u ↔ ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i) :=
  Iff.rfl

end UndergradKB.Foundations.Course
