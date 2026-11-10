import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Complex.Exponential
import Mathlib.NumberTheory.Real.Irrational
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology

/-- OpenStax Calculus 2:Example 6.10 (CA-370). The series for `arctan` on `|x| ≤ 1`: the partial sums of
`∑ (-1)^n x^(2n+1)/(2n+1)` tend to `Real.arctan x`. For `|x| < 1` this is Mathlib's expansion; `x = 1` is
Leibniz's series for `π/4` and `x = -1` follows by symmetry. -/
@[kb "openstaxcalculus2016" "2:Example 6.10 (part b), p. 499"]
theorem arctan_series {x : ℝ} (hx : |x| ≤ 1) :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) atTop
      (𝓝 (Real.arctan x)) := by
  rcases hx.lt_or_eq with hlt | heq
  · have := (Real.hasSum_arctan (x := x) (by simpa using hlt)).tendsto_sum_nat
    refine this.congr fun n => Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rfl
  · rcases abs_eq (zero_le_one' ℝ) |>.mp heq with rfl | rfl
    · rw [Real.arctan_one]
      refine Real.tendsto_sum_pi_div_four.congr fun n => Finset.sum_congr rfl fun i _ => ?_
      simp
    · rw [Real.arctan_neg, Real.arctan_one]
      refine Real.tendsto_sum_pi_div_four.neg.congr fun n => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, pow_mul]
      simp
      ring

/-- OpenStax Calculus 2:§6.3 Student Project (CA-382). The number `e = exp 1` is irrational. -/
@[kb "openstaxcalculus2016" "2:§6.3 Student Project (e is irrational), p. 518"]
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  rintro ⟨r, hr⟩
  set q := r.den with hqdef
  have hq : 0 < q := r.den_pos
  have hpq : Real.exp 1 * q = r.num := by
    rw [← hr, Rat.cast_def]
    have : (q : ℝ) ≠ 0 := by positivity
    field_simp
    rfl
  have hfact : (q.factorial : ℝ) = q * (q - 1).factorial := by
    exact_mod_cast (Nat.mul_factorial_pred hq.ne').symm
  set M : ℤ := r.num * ((q - 1).factorial : ℤ) -
    ∑ m ∈ range (q + 1), ((q.factorial / m.factorial : ℕ) : ℤ) with hMdef
  have hM : (M : ℝ) = q.factorial * (Real.exp 1 - ∑ m ∈ range (q + 1), 1 / (m.factorial : ℝ)) := by
    rw [hMdef]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_sum]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · rw [hfact, ← hpq]; ring
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hd : m.factorial ∣ q.factorial :=
        Nat.factorial_dvd_factorial (by simpa [Nat.lt_succ_iff] using hm)
      rw [Nat.cast_div hd (by positivity)]
      simp [div_eq_mul_inv]
  have hqf : (0 : ℝ) < q.factorial := by positivity
  have hq1 : ((q + 1).factorial : ℝ) = (q + 1) * q.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  -- lower bound
  have hlow := Real.sum_le_exp_of_nonneg (zero_le_one' ℝ) (q + 2)
  rw [Finset.sum_range_succ] at hlow
  simp only [one_pow] at hlow
  -- upper bound
  have hup := Real.exp_bound (x := 1) (by simp) (n := q + 1) (by omega)
  simp only [abs_one, one_pow, one_mul] at hup
  have hq2 : ((q + 1).factorial : ℝ) > 0 := by positivity
  have hM0 : (0 : ℝ) < M := by
    rw [hM]
    refine mul_pos hqf (sub_pos.mpr ?_)
    have : (0 : ℝ) < 1 / ((q + 1).factorial : ℝ) := by positivity
    linarith
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : (q.factorial : ℝ) * (((q + 1).succ : ℕ) / (((q + 1).factorial : ℝ) * ((q + 1 : ℕ) : ℝ))) < 1 := by
    rw [hq1]
    push_cast
    rw [← mul_div_assoc, div_lt_one (by positivity)]
    nlinarith
  have hM1 : (M : ℝ) < 1 := by
    rw [hM]
    refine lt_of_le_of_lt ?_ hb
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hup) hqf.le
  have h0 : (0 : ℤ) < M := by exact_mod_cast hM0
  have h1 : M < 1 := by exact_mod_cast hM1
  omega

end UndergradKB.Calculus
