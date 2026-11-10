import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import UndergradKB.Common.Attr

/-!
# Stirling's approximation (Keller–Trotter, Section 11.3)

The leading term `n! ~ √(2πn) (n/e)^n` is Mathlib's `Stirling.factorial_isEquivalent_stirling`;
we restate it in the book's shape.  The book also quotes the refined series
`1 + 1/(12n) + 1/(288 n²) - 139/(51840 n³) + O(n⁻⁴)` without proof; Mathlib has only
Robbins' stepwise bound, from which we derive the two-sided first-correction bound
`√(2πn)(n/e)^n ≤ n! ≤ √(2πn)(n/e)^n e^{1/(12n)}`.  The terms of order `n⁻²` and beyond are not
formalized.
-/

namespace UndergradKB.Combinatorics

open Filter Topology Real Nat Asymptotics

namespace Stirling

/-- CO-526. Stirling's approximation: `n! ~ √(2πn) (n/e)^n`. -/
@[kb "kellertrotter2017" "text (Stirling's approximation), p. 255"]
theorem factorial_isEquivalent :
    (fun n : ℕ => (n ! : ℝ)) ~[atTop] fun n : ℕ => √(2 * π * n) * (n / exp 1) ^ n :=
  _root_.Stirling.factorial_isEquivalent_stirling.congr_right
    (Eventually.of_forall fun n => by beta_reduce; rw [mul_right_comm])

/-- The Stirling sequence is bounded above by `√π · exp (1/(12 n))` (Robbins' bound, summed). -/
theorem stirlingSeq_le_sqrt_pi_mul_exp {n : ℕ} (hn : n ≠ 0) :
    _root_.Stirling.stirlingSeq n ≤ √π * exp (1 / (12 * n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  set v : ℕ → ℝ := fun k =>
    Real.log (_root_.Stirling.stirlingSeq (k + 1)) - 1 / (12 * ((k + 1 : ℕ) : ℝ)) with hv
  have hmono : Monotone v := by
    refine monotone_nat_of_le_succ fun k => ?_
    have h := _root_.Stirling.log_stirlingSeq_sdiff_le (k + 1)
    simp only [hv]
    have e : (1 : ℝ) / (12 * ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) =
        1 / (12 * ((k + 1 : ℕ) : ℝ)) - 1 / (12 * ((k + 1 + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    rw [e] at h
    linarith
  have hlim : Tendsto v atTop (𝓝 (Real.log √π - 0)) := by
    refine Tendsto.sub ?_ ?_
    · exact ((_root_.Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)).log
        (by positivity))
    · have : Tendsto (fun k : ℕ => (1 : ℝ) / (12 * ((k + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun k : ℕ => (12 : ℝ) * ((k + 1 : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) |>.const_mul_atTop
            (by norm_num)
        exact h1.inv_tendsto_atTop.congr fun k => (one_div _).symm
      exact this
  have hle : v m ≤ Real.log √π - 0 := hmono.ge_of_tendsto hlim m
  have hpos := _root_.Stirling.stirlingSeq'_pos m
  calc _root_.Stirling.stirlingSeq (m + 1)
      = exp (Real.log (_root_.Stirling.stirlingSeq (m + 1))) := (exp_log hpos).symm
    _ ≤ exp (Real.log √π + 1 / (12 * ((m + 1 : ℕ) : ℝ))) := by
        apply exp_le_exp.2
        simp only [hv] at hle
        linarith
    _ = √π * exp (1 / (12 * ((m + 1 : ℕ) : ℝ))) := by
        rw [exp_add, exp_log (by positivity)]

/-- CO-526 (first correction). For `n ≥ 1`,
`√(2πn)(n/e)^n ≤ n! ≤ √(2πn)(n/e)^n · exp(1/(12 n))`: the first correction factor `1 + 1/(12n)` of
the refined Stirling series, as an explicit two-sided bound. -/
@[kb "kellertrotter2017" "text (Stirling's approximation), p. 255"]
theorem stirling_bounds {n : ℕ} (hn : n ≠ 0) :
    √(2 * π * n) * (n / exp 1) ^ n ≤ (n ! : ℝ) ∧
      (n ! : ℝ) ≤ √(2 * π * n) * (n / exp 1) ^ n * exp (1 / (12 * n)) := by
  refine ⟨_root_.Stirling.le_factorial_stirling n, ?_⟩
  have hs := stirlingSeq_le_sqrt_pi_mul_exp hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hden : 0 < √(2 * (n : ℝ)) * (n / exp 1) ^ n := by positivity
  have e1 : (n ! : ℝ) = _root_.Stirling.stirlingSeq n * (√(2 * (n : ℝ)) * (n / exp 1) ^ n) := by
    unfold _root_.Stirling.stirlingSeq
    field_simp
  have e2 : √(2 * π * n) * (n / exp 1) ^ n = √π * (√(2 * (n : ℝ)) * (n / exp 1) ^ n) := by
    rw [show 2 * π * (n : ℝ) = π * (2 * n) by ring, sqrt_mul (by positivity)]
    ring
  rw [e1, e2]
  calc _ ≤ √π * exp (1 / (12 * (n : ℝ))) * (√(2 * (n : ℝ)) * (n / exp 1) ^ n) :=
        mul_le_mul_of_nonneg_right hs hden.le
    _ = _ := by ring

end Stirling

end UndergradKB.Combinatorics
