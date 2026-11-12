import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import UndergradKB.Common

/-! # An irrational power of an irrational number can be rational

Hammack, *Book of Proof*, Section 7.4 (FO-136): there exist irrational `x, y` with `x^y` rational. Hammack gives two
proofs: a non-constructive one (either `√2^√2` is rational, or it is irrational and `(√2^√2)^√2 = 2`), and a
constructive one, `√2 ^ (log₂ 9) = 3`, which needs `log₂ 9` irrational. Both are formalized; powers are real powers
(`Real.rpow`).
-/

namespace UndergradKB.Foundations

open Real

/-- FO-136 (Hammack, §7.4, non-constructive proof). There are irrational numbers `x` and `y` such that `x^y` is
rational. -/
@[kb "hammack2018" "Prop §7.4, p. 166"]
theorem exists_irrational_rpow_rational :
    ∃ x y : ℝ, Irrational x ∧ Irrational y ∧ ¬ Irrational (x ^ y) := by
  by_cases h : Irrational (√2 ^ √2)
  · refine ⟨√2 ^ √2, √2, h, irrational_sqrt_two, ?_⟩
    rw [← rpow_mul (sqrt_nonneg 2), mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast, sq_sqrt (by norm_num)]
    exact fun h' => h'.ne_nat 2 (by norm_num)
  · exact ⟨√2, √2, irrational_sqrt_two, irrational_sqrt_two, h⟩

/-- FO-136 (Hammack, §7.4). `log₂ 9` is irrational: `2^(m/n) = 9` would give `2^m = 9^n`, an even number equal to an
odd one. -/
@[kb "hammack2018" "Prop §7.4, p. 166"]
theorem irrational_logb_two_nine : Irrational (logb 2 9) := by
  rintro ⟨q, hq⟩
  have hpos : 0 < logb 2 9 := logb_pos (by norm_num) (by norm_num)
  have h2q : (2 : ℝ) ^ (q : ℝ) = 9 := by rw [hq]; exact rpow_logb (by norm_num) (by norm_num) (by norm_num)
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq ▸ hpos
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q.num = m := ⟨q.num.toNat, (Int.toNat_of_nonneg hnum.le).symm⟩
  have hm0 : 0 < m := by omega
  have key : (2 : ℝ) ^ m = (9 : ℝ) ^ q.den := by
    have h1 : ((2 : ℝ) ^ (q : ℝ)) ^ (q.den : ℝ) = (2 : ℝ) ^ (m : ℝ) := by
      rw [← rpow_mul (by norm_num)]
      congr 1
      have : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
      rw [this, hm]; norm_cast
    rw [h2q, rpow_natCast, rpow_natCast] at h1
    exact h1.symm
  have key' : (2 : ℕ) ^ m = 9 ^ q.den := by exact_mod_cast key
  have h1 : Even ((2 : ℕ) ^ m) := (Nat.even_pow' hm0.ne').mpr even_two
  have h2 : Odd ((9 : ℕ) ^ q.den) := Odd.pow (by decide)
  rw [key'] at h1
  exact (Nat.not_even_iff_odd.mpr h2) h1

/-- FO-136 (Hammack, §7.4, constructive proof). `√2` and `log₂ 9` are irrational and `√2 ^ (log₂ 9) = 3`. -/
@[kb "hammack2018" "Prop §7.4, p. 166"]
theorem sqrt_two_rpow_logb_two_nine :
    Irrational √2 ∧ Irrational (logb 2 9) ∧ √2 ^ logb 2 9 = 3 := by
  refine ⟨irrational_sqrt_two, irrational_logb_two_nine, ?_⟩
  rw [sqrt_eq_rpow, ← rpow_mul (by norm_num), mul_comm, rpow_mul (by norm_num),
    rpow_logb (by norm_num) (by norm_num) (by norm_num), ← sqrt_eq_rpow]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]

end UndergradKB.Foundations
