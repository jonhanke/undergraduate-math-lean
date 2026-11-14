import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Central
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesLead

/-!
# Probability: the fair coin never has a finite mean waiting time to lead (Example 10.7)

For the fair coin, Peter is in the lead eventually with probability `1`
(`lead_total_probability`), but the expected time `E(T) = ∑ n r_n` until he first leads is infinite:
`(2k+1) r_{2k+1} = (2k+1) C_k / 2^{2k+1} ≥ 1/(2(k+1))`, by the lower bound
`4^k ≤ (2k+1) binom(2k, k)` for the central binomial coefficient.
-/

open Finset

namespace UndergradKB.Probability

lemma lead_fair_term_lower (k : ℕ) :
    1 / (2 * ((k : ℝ) + 1)) ≤ ((2 * k + 1 : ℕ) : ℝ) * leadR (1 / 2) (1 / 2) (2 * k + 1) := by
  rw [leadR_odd]
  have hc : ((k : ℝ) + 1) * catalan k = Nat.centralBinom k := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom k
  have hb : ((4 : ℝ) ^ k) ≤ (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_centralBinom k
  have e : (1 / 2 : ℝ) ^ (k + 1) * (1 / 2) ^ k = 1 / (2 * 4 ^ k) := by
    rw [← pow_add, show k + 1 + k = 2 * k + 1 by ring, pow_succ, pow_mul, one_div_pow, one_div_pow]; norm_num
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [mul_assoc, e, div_le_iff₀ (by positivity)]
  push_cast
  rw [← hc] at hb
  field_simp
  nlinarith

/-- Grinstead–Snell Example 10.7 (PR-179), the fair coin: if `p = q = 1/2`, the expected time
`E(T) = ∑ n r_n` until Peter first leads is infinite (the series diverges), although `∑ r_n = 1`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem lead_expected_time_fair {r : ℕ → ℝ} (hr : IsLeadSeq (1 / 2) (1 / 2) r) :
    ¬ Summable (fun n : ℕ => (n : ℝ) * r n) ∧ HasSum r 1 := by
  have hrr : r = leadR (1 / 2) (1 / 2) := funext (isLeadSeq_unique hr)
  have htot := (lead_total_probability (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) hr)
  refine ⟨?_, ?_⟩
  · subst hrr
    intro hs
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by simpa using hab
    have h2 := hs.comp_injective hinj
    have h3 : Summable (fun k : ℕ => 1 / (2 * ((k : ℝ) + 1))) :=
      Summable.of_nonneg_of_le (fun k => by positivity) lead_fair_term_lower h2
    have h4 : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) := by
      refine (h3.mul_left 2).congr fun k => ?_
      push_cast; field_simp
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h4)
  · have h := htot.1
    rw [show |(1 / 2 : ℝ) - 1 / 2| = 0 by norm_num] at h
    norm_num at h
    exact h

end UndergradKB.Probability
