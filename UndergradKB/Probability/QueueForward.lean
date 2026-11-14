import Mathlib.Tactic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueContinuous

/-! # Probability: the forward equations of the queue (Grinstead–Snell Example 6.29)

Wave 7, a recorded loose end.  The law `p_t` of the queue length at time `t` obtained by uniformization
(`queueLawTime`) solves the Kolmogorov forward equations of the queue (a birth-death process with birth rate `λ`
and death rate `μ`), started from an empty queue:

  `p_0(k) = [k = 0]`, `p_t'(0) = -λ p_t(0) + μ p_t(1)`,
  `p_t'(k+1) = λ p_t(k) - (λ+μ) p_t(k+1) + μ p_t(k+2)`.

This checks that `queueLawTime` is the law of the queue of the book. -/

open Finset Filter Topology

namespace UndergradKB.Probability

/-- Term-by-term derivative of the exponential-type series `∑ (νs)^n/n! c_n` with bounded coefficients. -/
theorem hasDerivAt_expSeries_coeff (ν : ℝ) (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (y : ℝ) :
    HasDerivAt (fun s => ∑' n, (ν * s) ^ n / n.factorial * c n)
      (ν * ∑' n, (ν * y) ^ n / n.factorial * c (n + 1)) y := by
  have hsum : ∀ (d : ℕ → ℝ), (∀ n, |d n| ≤ 1) → ∀ s : ℝ,
      Summable fun n => (ν * s) ^ n / n.factorial * d n := by
    intro d hd s
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |ν * s|) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    exact mul_le_of_le_one_right (by positivity) (hd n)
  have hsplit : ∀ s : ℝ, ∑' n, (ν * s) ^ n / n.factorial * c n =
      c 0 + ∑' n, (ν * s) ^ (n + 1) / (n + 1).factorial * c (n + 1) := by
    intro s
    rw [(hsum c hc s).tsum_eq_zero_add]
    simp
  simp_rw [hsplit]
  apply HasDerivAt.const_add
  set R := |y| + 1 with hR
  have hmain := hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℝ) R) (y₀ := y)
    (g := fun n s => (ν * s) ^ (n + 1) / (n + 1).factorial * c (n + 1))
    (g' := fun n s => ν * ((ν * s) ^ n / n.factorial * c (n + 1)))
    (u := fun n => |ν| * ((|ν| * R) ^ n / n.factorial))
    ((Real.summable_pow_div_factorial (|ν| * R)).mul_left |ν|) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ ?_ (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith) ?_
    (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith)
  · rw [tsum_mul_left] at hmain
    exact hmain
  · intro n s _
    have h := (((hasDerivAt_id' s).const_mul ν).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
      |>.mul_const (c (n + 1))
    convert h using 1
    simp only [mul_one, Nat.add_sub_cancel]
    rw [Nat.factorial_succ, Nat.cast_mul]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  · intro n s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_mul]
    gcongr
    calc (|ν| * |s|) ^ n / n.factorial * |c (n + 1)| ≤ (|ν| * |s|) ^ n / n.factorial * 1 :=
          mul_le_mul_of_nonneg_left (hc _) (by positivity)
      _ ≤ (|ν| * R) ^ n / n.factorial := by
          rw [mul_one]
          gcongr
  · have := (hsum (fun n => c (n + 1)) (fun n => hc _) y).mul_left ν
    refine Summable.of_norm_bounded (((Real.summable_pow_div_factorial |ν * y|).mul_left |ν * y|)) ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast, pow_succ, Nat.factorial_succ,
      Nat.cast_mul]
    have hf : (0 : ℝ) < n.factorial := by positivity
    calc |ν * y| ^ n * |ν * y| / ((n + 1 : ℕ) * n.factorial) * |c (n + 1)|
        ≤ |ν * y| ^ n * |ν * y| / ((n + 1 : ℕ) * n.factorial) * 1 :=
          mul_le_mul_of_nonneg_left (hc _) (by positivity)
      _ ≤ |ν * y| * (|ν * y| ^ n / n.factorial) := by
          rw [mul_one, mul_comm (|ν * y| ^ n), mul_div_assoc]
          gcongr
          have : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
          nlinarith

section

variable {lam mu : ℝ}

theorem queueLaw_abs_le (hl : 0 < lam) (hm : 0 < mu) (n k : ℕ) : |queueLaw lam mu n k| ≤ 1 :=
  abs_le.2 ⟨by linarith [(queueLaw_prob hl hm n).1 k], queueLaw_le_one hl hm n k⟩

theorem queueLawTime_eq (lam mu t : ℝ) (k : ℕ) : queueLawTime lam mu t k =
    Real.exp (-((lam + mu) * t)) * ∑' n, ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu n k := by
  unfold queueLawTime poissonWeight
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- The derivative of the law at time `t` of the queue length, in terms of the next step of the jump chain. -/
theorem queueLawTime_hasDerivAt (hl : 0 < lam) (hm : 0 < mu) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s => queueLawTime lam mu s k)
      (-(lam + mu) * queueLawTime lam mu t k +
        (lam + mu) * (Real.exp (-((lam + mu) * t)) *
          ∑' n, ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu (n + 1) k)) t := by
  simp_rw [queueLawTime_eq]
  have he : HasDerivAt (fun s => Real.exp (-((lam + mu) * s))) (Real.exp (-((lam + mu) * t)) * -(lam + mu))
      t := by
    have := ((hasDerivAt_id t).const_mul (lam + mu)).neg.exp
    simpa using this
  have hF := hasDerivAt_expSeries_coeff (lam + mu) (fun n => queueLaw lam mu n k)
    (fun n => queueLaw_abs_le hl hm n k) t
  convert he.mul hF using 1
  ring

end

/-- Grinstead–Snell Example 6.29 (PR-209), the forward equations.  For arrival rate `λ > 0` and service rate
`μ > 0`, the law `p_t` of the queue length at time `t` (`queueLawTime`, by uniformization, started from an empty
queue) solves the Kolmogorov forward equations of the queue: `p_0(k) = [k = 0]`,
`p_t'(0) = -λ p_t(0) + μ p_t(1)` and `p_t'(k+1) = λ p_t(k) - (λ+μ) p_t(k+1) + μ p_t(k+2)` for every real `t`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_forward_equations {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) :
    (∀ k, queueLawTime lam mu 0 k = if k = 0 then 1 else 0) ∧
    (∀ t, HasDerivAt (fun s => queueLawTime lam mu s 0)
      (-lam * queueLawTime lam mu t 0 + mu * queueLawTime lam mu t 1) t) ∧
    (∀ k t, HasDerivAt (fun s => queueLawTime lam mu s (k + 1))
      (lam * queueLawTime lam mu t k - (lam + mu) * queueLawTime lam mu t (k + 1) +
        mu * queueLawTime lam mu t (k + 2)) t) := by
  have hp : lam + mu ≠ 0 := by linarith
  refine ⟨fun k => ?_, fun t => ?_, fun k t => ?_⟩
  · rw [queueLawTime_eq, mul_zero, neg_zero, Real.exp_zero, one_mul, tsum_eq_single 0]
    · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      exact (queueLaw_step hl hm 0).1 k
    · intro n hn; simp [zero_pow hn]
  · convert queueLawTime_hasDerivAt hl hm 0 t using 1
    have hstep : ∀ n, queueLaw lam mu (n + 1) 0 =
        (queueLaw lam mu n 0 + queueLaw lam mu n 1) * (mu / (lam + mu)) := fun n =>
      ((queueLaw_step hl hm n).2 0).unique (queueJump_col_zero lam mu _)
    simp_rw [hstep]
    have h0 := (hasDerivAt_expSeries_coeff (lam + mu) (fun n => queueLaw lam mu n 0)
      (fun n => queueLaw_abs_le hl hm n 0) t)
    have hs : ∀ j, Summable fun n => ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu n j := by
      intro j
      refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |(lam + mu) * t|) fun n => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
      exact mul_le_of_le_one_right (by positivity) (queueLaw_abs_le hl hm n j)
    have e : ∑' n, ((lam + mu) * t) ^ n / n.factorial *
        ((queueLaw lam mu n 0 + queueLaw lam mu n 1) * (mu / (lam + mu))) =
        (mu / (lam + mu)) * (∑' n, ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu n 0 +
          ∑' n, ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu n 1) := by
      rw [← (hs 0).tsum_add (hs 1), ← tsum_mul_left]
      exact tsum_congr fun n => by ring
    rw [e, queueLawTime_eq, queueLawTime_eq]
    field_simp
    ring
  · convert queueLawTime_hasDerivAt hl hm (k + 1) t using 1
    have hstep : ∀ n, queueLaw lam mu (n + 1) (k + 1) =
        queueLaw lam mu n k * (lam / (lam + mu)) + queueLaw lam mu n (k + 2) * (mu / (lam + mu)) :=
      fun n => ((queueLaw_step hl hm n).2 (k + 1)).unique (queueJump_col_succ lam mu _ k)
    simp_rw [hstep]
    have hs : ∀ j, Summable fun n => ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu n j := by
      intro j
      refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |(lam + mu) * t|) fun n => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
      exact mul_le_of_le_one_right (by positivity) (queueLaw_abs_le hl hm n j)
    have e : ∑' n, ((lam + mu) * t) ^ n / n.factorial *
        (queueLaw lam mu n k * (lam / (lam + mu)) + queueLaw lam mu n (k + 2) * (mu / (lam + mu))) =
        (lam / (lam + mu)) * ∑' n, ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu n k +
          (mu / (lam + mu)) * ∑' n, ((lam + mu) * t) ^ n / n.factorial * queueLaw lam mu n (k + 2) := by
      rw [← tsum_mul_left, ← tsum_mul_left, ← ((hs k).mul_left _).tsum_add ((hs (k + 2)).mul_left _)]
      exact tsum_congr fun n => by ring
    rw [e, queueLawTime_eq, queueLawTime_eq, queueLawTime_eq]
    field_simp
    ring

end UndergradKB.Probability
