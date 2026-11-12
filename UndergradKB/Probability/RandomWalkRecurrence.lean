import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.RandomWalk

/-! # Probability: recurrence of the one-dimensional random walk (Grinstead–Snell, Examples 12.1-12.3)

We show that the simple symmetric walk on `ℤ` returns to the origin with probability one: the first-return
probabilities `f_N` of `RandomWalk.lean` sum to `1`.  The proof telescopes `f_{2m} = u_{2m-2} - u_{2m}` and uses
that `u_{2m} = C(2m,m)/4^m` tends to `0`, via the bound `(2m+1) u_{2m}^2 ≤ 1`.

Dimensions `2` and `3` and the expected number of equalizations are not treated here. -/

open Finset Filter
open scoped Topology

namespace UndergradKB.Probability

/-- The key decay bound `(2k+1) c_k^2 ≤ 1`. -/
theorem c_sq_bound (k : ℕ) : (2 * (k : ℚ) + 1) * c k ^ 2 ≤ 1 := by
  induction k with
  | zero => simp [c_zero]
  | succ k ih =>
    have h := c_succ k
    have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hc : 0 ≤ c k ^ 2 := sq_nonneg _
    have hd : (2 * ((k : ℚ) + 1)) ^ 2 * c (k + 1) ^ 2 = (2 * k + 1) ^ 2 * c k ^ 2 := by
      rw [← mul_pow, h, mul_pow]
    push_cast
    have hpos : 0 < (2 * ((k : ℚ) + 1)) ^ 2 := by positivity
    have : (2 * ((k : ℚ) + 1)) ^ 2 * ((2 * ((k : ℚ) + 1) + 1) * c (k + 1) ^ 2) ≤
        (2 * ((k : ℚ) + 1)) ^ 2 * 1 := by
      have e : (2 * ((k : ℚ) + 1)) ^ 2 * ((2 * ((k : ℚ) + 1) + 1) * c (k + 1) ^ 2) =
          (2 * ((k : ℚ) + 1) + 1) * ((2 * k + 1) ^ 2 * c k ^ 2) := by
        rw [← hd]; ring
      rw [e]
      nlinarith [mul_nonneg (mul_nonneg hk hk) hc, mul_nonneg hk hc, hc]
    exact le_of_mul_le_mul_left this hpos

theorem c_nonneg (k : ℕ) : 0 ≤ c k := by unfold c; positivity

/-- `u_{2m} → 0`. -/
theorem c_tendsto_zero : Tendsto (fun k => (c k : ℝ)) atTop (𝓝 0) := by
  have hb : ∀ k, ((c k : ℝ)) ^ 2 ≤ 1 / (2 * (k : ℝ) + 1) := by
    intro k
    have := c_sq_bound k
    have h' : (2 * (k : ℝ) + 1) * (c k : ℝ) ^ 2 ≤ 1 := by exact_mod_cast this
    rw [le_div_iff₀ (by positivity)]; linarith
  have hlim : Tendsto (fun k : ℕ => 1 / (2 * (k : ℝ) + 1)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (2 * (k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    exact this.inv_tendsto_atTop.congr (fun k => by simp [one_div])
  have hsq : Tendsto (fun k => ((c k : ℝ)) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun k => sq_nonneg _) hb hlim
  have habs : Tendsto (fun k => |(c k : ℝ)|) atTop (𝓝 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

theorem f_zero : f 0 = 0 := by
  simp [f, firstCount, FR]

theorem f_two_mul (m : ℕ) : f (2 * m) = c (m - 1) - c m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [f_zero]
  · exact f_eq m hm

theorem f_nonneg (N : ℕ) : 0 ≤ f N := by
  unfold f; positivity

/-- Partial sums of the even-time first-return probabilities telescope: `Σ_{m ≤ n} f_{2m} = 1 - u_{2n}`. -/
theorem sum_f_two_mul (n : ℕ) : ∑ m ∈ range (n + 1), f (2 * m) = 1 - c n := by
  induction n with
  | zero => simp [f_zero, c_zero]
  | succ n ih =>
    rw [sum_range_succ, ih, f_two_mul]
    simp

theorem sum_f_two_mul_real (n : ℕ) :
    ∑ m ∈ range (n + 1), ((f (2 * m) : ℚ) : ℝ) = 1 - (c n : ℝ) := by
  rw [← Rat.cast_sum, sum_f_two_mul, Rat.cast_sub, Rat.cast_one]

theorem hasSum_f_two_mul_real : HasSum (fun k => ((f (2 * k) : ℚ) : ℝ)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => Rat.cast_nonneg.2 (f_nonneg _))]
  refine (tendsto_add_atTop_iff_nat (f := fun n => ∑ i ∈ range n, ((f (2 * i) : ℚ) : ℝ)) 1).1 ?_
  simp only [sum_f_two_mul_real]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub c_tendsto_zero

theorem hasSum_f_odd_real : HasSum (fun k => ((f (2 * k + 1) : ℚ) : ℝ)) 0 := by
  simp only [f_odd, Rat.cast_zero]
  exact hasSum_zero

/-- Grinstead–Snell Example 12.1 (PR-127). In one dimension the probability of an eventual return to the origin
is `1`: the first-return probabilities `f_N` (real-valued) sum to `1`. -/
@[kb "grinsteadsnell2006" "Example 12.1, p. 483"]
theorem hasSum_firstReturn : HasSum (fun N => ((f N : ℚ) : ℝ)) 1 := by
  have h := HasSum.even_add_odd (f := fun N => ((f N : ℚ) : ℝ)) hasSum_f_two_mul_real
    hasSum_f_odd_real
  rwa [add_zero] at h

/-- Grinstead–Snell Example 12.1 (PR-127), even-time form: `Σ_{m ≥ 1} f_{2m} = 1`. -/
@[kb "grinsteadsnell2006" "Example 12.1, p. 483"]
theorem hasSum_firstReturn_even : HasSum (fun m => (f (2 * (m + 1)) : ℝ)) 1 := by
  have hnn : ∀ N, 0 ≤ (f N : ℝ) := fun N => by exact_mod_cast f_nonneg N
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => hnn _)]
  have : ∀ n, ∑ i ∈ range n, (f (2 * (i + 1)) : ℝ) = 1 - (c n : ℝ) := by
    intro n
    have h := sum_f_two_mul n
    rw [sum_range_succ'] at h
    simp only [mul_zero, f_zero, add_zero] at h
    have : ∑ i ∈ range n, (f (2 * (i + 1)) : ℝ) = ((1 - c n : ℚ) : ℝ) := by
      rw [← h]; push_cast; rfl
    rw [this]; push_cast; ring
  simp only [this]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub c_tendsto_zero

end UndergradKB.Probability
