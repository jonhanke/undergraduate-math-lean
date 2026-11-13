import Mathlib.Algebra.Polynomial.Div
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 3 (Stitz-Zeager): synthetic division

The synthetic division tableau of Section 3.2 for dividing `p(x) = aₙxⁿ + ⋯ + a₀` by `x - c`: the bottom row
starts with `aₙ`, and each later entry is the coefficient above it plus `c` times the previous bottom entry. The
bottom row lists the coefficients of the quotient followed by the remainder, which is `p(c)`. -/

namespace UndergradKB.Precalculus.Course

open Polynomial

/-- Synthetic division (Section 3.2): with `q` the quotient of `p` by `x - c`, `p = (x - c) q + p(c)`; the
quotient coefficients satisfy the tableau recursion `q_{k} = a_{k+1} + c q_{k+1}`, start from `q_{n-1} = aₙ`
(everything at degree `n` or higher is zero), and the remainder is the last entry `a₀ + c q₀ = p(c)` (PC-297). -/
@[kb "stitzzeager2013" "§3.2, p. 272"]
theorem box_3_2_synthetic_division (p : ℝ[X]) (c : ℝ) :
    p = (X - C c) * (p /ₘ (X - C c)) + C (p.eval c) ∧
    (∀ k, (p /ₘ (X - C c)).coeff k = p.coeff (k + 1) + c * (p /ₘ (X - C c)).coeff (k + 1)) ∧
    (∀ k, p.natDegree ≤ k → (p /ₘ (X - C c)).coeff k = 0) ∧
    p.eval c = p.coeff 0 + c * (p /ₘ (X - C c)).coeff 0 := by
  have hdiv : p = (X - C c) * (p /ₘ (X - C c)) + C (p.eval c) := by
    conv_lhs => rw [← modByMonic_add_div p (X - C c)]
    rw [modByMonic_X_sub_C_eq_C_eval, add_comm]
  refine ⟨hdiv, coeff_divByMonic_X_sub_C_rec p c, fun k hk => ?_, ?_⟩
  · rw [coeff_divByMonic_X_sub_C]
    exact Finset.sum_eq_zero fun i hi => by
      have := (Finset.mem_Icc.1 hi); omega
  · have h0 := congrArg (fun P => P.coeff 0) hdiv
    simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_sub, coeff_X_zero, zero_sub] at h0
    linarith

end UndergradKB.Precalculus.Course
