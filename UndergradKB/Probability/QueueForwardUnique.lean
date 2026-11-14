import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueStartTime

/-! # Probability: the forward equations of the queue determine its law (Grinstead–Snell Example 6.29)

Wave 8, a recorded loose end (1).  Wave 7 checked that the uniformization law `queueLawTime` of the queue solves
the Kolmogorov forward equations; here these equations are shown to have only one bounded solution with given
initial values.  So every bounded family `p_t(k)` (for instance a family of probability laws) that satisfies the
forward equations of the queue on `t ≥ 0` and starts with `j` customers is the uniformization law
`queueLawTimeFrom j`.

Proof (Picard iteration in the sup norm): the difference `d` of two solutions solves the same equations, with
`d_0 = 0` and `|d_t(k)| ≤ M`; the right side of the equations is bounded by `c = 2(λ+μ)` times the sup of `|d|`,
so by induction `|d_t(k)| ≤ M (ct)^n / n!` for every `n`, and this tends to `0`. -/

open Filter Topology Set

namespace UndergradKB.Probability

/-- `p` solves the Kolmogorov forward equations of the queue with arrival rate `λ` and service rate `μ` on
`t ≥ 0`: each `p_t(k)` is continuous in `t ≥ 0`, and for `t > 0`, `p_t'(0) = -λ p_t(0) + μ p_t(1)` and
`p_t'(k+1) = λ p_t(k) - (λ+μ) p_t(k+1) + μ p_t(k+2)`. -/
structure QueueForwardSolution (lam mu : ℝ) (p : ℝ → ℕ → ℝ) : Prop where
  cont : ∀ k, ContinuousOn (fun s => p s k) (Ici 0)
  deriv_zero : ∀ t, 0 < t → HasDerivAt (fun s => p s 0) (-lam * p t 0 + mu * p t 1) t
  deriv_succ : ∀ k t, 0 < t → HasDerivAt (fun s => p s (k + 1))
    (lam * p t k - (lam + mu) * p t (k + 1) + mu * p t (k + 2)) t

section

variable {lam mu : ℝ}

theorem QueueForwardSolution.sub {p q : ℝ → ℕ → ℝ} (hp : QueueForwardSolution lam mu p)
    (hq : QueueForwardSolution lam mu q) : QueueForwardSolution lam mu fun t k => p t k - q t k where
  cont k := (hp.cont k).sub (hq.cont k)
  deriv_zero t ht := by
    convert (hp.deriv_zero t ht).sub (hq.deriv_zero t ht) using 1; ring
  deriv_succ k t ht := by
    convert (hp.deriv_succ k t ht).sub (hq.deriv_succ k t ht) using 1; ring

/-- The comparison step: if `D(0) = 0`, `D` is continuous on `t ≥ 0` and `|D'| ≤ B'` on `t > 0`, where
`B(s) = M (cs)^(n+1)/(n+1)!`, then `|D| ≤ B` on `t ≥ 0`. -/
theorem abs_le_of_deriv_bound {D D' : ℝ → ℝ} {M c : ℝ} (n : ℕ) (hD0 : D 0 = 0)
    (hDc : ContinuousOn D (Ici 0)) (hD : ∀ s, 0 < s → HasDerivAt D (D' s) s)
    (hb : ∀ s, 0 < s → |D' s| ≤ M * c * (c * s) ^ n / n.factorial) :
    ∀ t, 0 ≤ t → |D t| ≤ M * (c * t) ^ (n + 1) / (n + 1).factorial := by
  set B : ℝ → ℝ := fun s => M * (c * s) ^ (n + 1) / (n + 1).factorial with hB
  have hBd : ∀ s, HasDerivAt B (M * c * (c * s) ^ n / n.factorial) s := by
    intro s
    have h : HasDerivAt (fun s => (c * s) ^ (n + 1)) ((n + 1 : ℕ) * (c * s) ^ n * c) s := by
      have h0 := (hasDerivAt_pow (n + 1) (c * s)).comp s ((hasDerivAt_id' s).const_mul c)
      convert h0 using 1
      · rfl
      · rw [Nat.add_sub_cancel, mul_one]
    show HasDerivAt (fun s => M * (c * s) ^ (n + 1) / (n + 1).factorial) _ s
    convert (h.const_mul M).div_const ((n + 1).factorial : ℝ) using 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hB0 : B 0 = 0 := by simp [hB]
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun s => (hBd s).continuousAt
  have hconv : Convex ℝ (Ici (0 : ℝ)) := convex_Ici 0
  have hint : interior (Ici (0 : ℝ)) = Ioi 0 := interior_Ici
  -- `D - B` and `-D - B` are antitone on `t ≥ 0`
  have h1 : AntitoneOn (fun s => D s - B s) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos hconv (hDc.sub hBc.continuousOn) ?_ ?_
    · rw [hint]; intro s hs; exact ((hD s hs).sub (hBd s)).differentiableAt.differentiableWithinAt
    · rw [hint]; intro s hs
      rw [(show HasDerivAt (fun s => D s - B s) _ s from (hD s hs).sub (hBd s)).deriv]
      linarith [(abs_le.1 (hb s hs)).2]
  have h2 : AntitoneOn (fun s => -D s - B s) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos hconv (hDc.neg.sub hBc.continuousOn) ?_ ?_
    · rw [hint]; intro s hs; exact ((hD s hs).neg.sub (hBd s)).differentiableAt.differentiableWithinAt
    · rw [hint]; intro s hs
      rw [(show HasDerivAt (fun s => -D s - B s) _ s from (hD s hs).neg.sub (hBd s)).deriv]
      linarith [(abs_le.1 (hb s hs)).1]
  intro t ht
  have e1 := h1 (mem_Ici.2 le_rfl) ht ht
  have e2 := h2 (mem_Ici.2 le_rfl) ht ht
  simp only [hD0, hB0, sub_zero, neg_zero] at e1 e2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- A bounded solution of the forward equations that starts at `0` is `0` on `t ≥ 0`. -/
theorem queue_forward_zero (hl : 0 < lam) (hm : 0 < mu) {d : ℝ → ℕ → ℝ} (hd : QueueForwardSolution lam mu d)
    {M : ℝ} (hM : ∀ t, 0 ≤ t → ∀ k, |d t k| ≤ M) (h0 : ∀ k, d 0 k = 0) : ∀ t, 0 ≤ t → ∀ k, d t k = 0 := by
  set c := 2 * (lam + mu) with hc
  have hc0 : 0 ≤ c := by linarith
  have key : ∀ n : ℕ, ∀ k, ∀ t, 0 ≤ t → |d t k| ≤ M * (c * t) ^ n / n.factorial := by
    intro n
    induction n with
    | zero => intro k t ht; simpa using hM t ht k
    | succ n ih =>
      intro k t ht
      have hpos : ∀ s, 0 ≤ s → 0 ≤ M * (c * s) ^ n / n.factorial := fun s hs =>
        le_trans (abs_nonneg _) (ih 0 s hs)
      rcases k with _ | k
      · refine abs_le_of_deriv_bound n (h0 0) (hd.cont 0) (hd.deriv_zero) (fun s hs => ?_) t ht
        have a0 := ih 0 s hs.le
        have a1 := ih 1 s hs.le
        have := hpos s hs.le
        set m := M * (c * s) ^ n / n.factorial with hmdef
        have e : M * c * (c * s) ^ n / n.factorial = c * m := by rw [hmdef]; ring
        rw [e]
        calc |-lam * d s 0 + mu * d s 1| ≤ lam * |d s 0| + mu * |d s 1| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul, abs_neg, abs_of_pos hl, abs_of_pos hm]
          _ ≤ lam * m + mu * m := by gcongr
          _ ≤ c * m := by rw [hc]; nlinarith
      · refine abs_le_of_deriv_bound n (h0 (k + 1)) (hd.cont (k + 1)) (hd.deriv_succ k)
          (fun s hs => ?_) t ht
        have a0 := ih k s hs.le
        have a1 := ih (k + 1) s hs.le
        have a2 := ih (k + 2) s hs.le
        have := hpos s hs.le
        set m := M * (c * s) ^ n / n.factorial with hmdef
        have e : M * c * (c * s) ^ n / n.factorial = c * m := by rw [hmdef]; ring
        rw [e]
        calc |lam * d s k - (lam + mu) * d s (k + 1) + mu * d s (k + 2)|
            ≤ lam * |d s k| + (lam + mu) * |d s (k + 1)| + mu * |d s (k + 2)| := by
              refine (abs_add_le _ _).trans ?_
              refine add_le_add ((abs_sub _ _).trans ?_) ?_
              · rw [abs_mul, abs_mul, abs_of_pos hl, abs_of_pos (by linarith : 0 < lam + mu)]
              · rw [abs_mul, abs_of_pos hm]
          _ ≤ lam * m + (lam + mu) * m + mu * m := by gcongr
          _ ≤ c * m := by rw [hc]; nlinarith
  intro t ht k
  have hlim : Tendsto (fun n : ℕ => M * ((c * t) ^ n / n.factorial)) atTop (𝓝 (M * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (c * t)).const_mul M
  rw [mul_zero] at hlim
  have hle : |d t k| ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => by rw [← mul_div_assoc]; exact key n k t ht)
  exact abs_nonpos_iff.1 hle

/-- Uniqueness for the forward equations of the queue: two bounded solutions on `t ≥ 0` with the same
initial values agree on `t ≥ 0`. -/
theorem queue_forward_unique (hl : 0 < lam) (hm : 0 < mu) {p q : ℝ → ℕ → ℝ}
    (hp : QueueForwardSolution lam mu p) (hq : QueueForwardSolution lam mu q) {M : ℝ}
    (hpM : ∀ t, 0 ≤ t → ∀ k, |p t k| ≤ M) (hqM : ∀ t, 0 ≤ t → ∀ k, |q t k| ≤ M)
    (h0 : ∀ k, p 0 k = q 0 k) : ∀ t, 0 ≤ t → ∀ k, p t k = q t k := by
  intro t ht k
  have := queue_forward_zero hl hm (hp.sub hq) (M := M + M)
    (fun t ht k => (abs_sub _ _).trans (add_le_add (hpM t ht k) (hqM t ht k)))
    (fun k => by simp [h0 k]) t ht k
  linarith

/-- The uniformization law started with `j` customers solves the forward equations on `t ≥ 0`. -/
theorem queueLawTimeFrom_solution (hl : 0 < lam) (hm : 0 < mu) (j : ℕ) :
    QueueForwardSolution lam mu (queueLawTimeFrom lam mu j) where
  cont k := by
    rcases k with _ | k
    · exact fun t _ => ((queue_forward_equations_from hl hm j).2.1 t).continuousAt.continuousWithinAt
    · exact fun t _ => ((queue_forward_equations_from hl hm j).2.2 k t).continuousAt.continuousWithinAt
  deriv_zero t _ := (queue_forward_equations_from hl hm j).2.1 t
  deriv_succ k t _ := (queue_forward_equations_from hl hm j).2.2 k t

theorem queueLawTimeFrom_abs_le (hl : 0 < lam) (hm : 0 < mu) (j : ℕ) :
    ∀ t, 0 ≤ t → ∀ k, |queueLawTimeFrom lam mu j t k| ≤ 1 := by
  intro t ht k
  have h := queueLawTimeFrom_prob hl hm j ht
  rw [abs_of_nonneg (h.1 k)]
  exact le_hasSum h.2 k fun i _ => h.1 i

end

/-- Grinstead–Snell Example 6.29 (PR-209), the law of the queue is determined by its forward equations.  For
arrival rate `λ > 0` and service rate `μ > 0`, let `p_t(k)` be bounded on `t ≥ 0` (for instance, each `p_t` a
probability law), solve the Kolmogorov forward equations of the queue on `t ≥ 0`, and start with `j` customers
(`p_0(k) = [k = j]`).  Then `p_t` is the uniformization law `queueLawTimeFrom j` for every `t ≥ 0`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_forward_determines_law {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (j : ℕ) {p : ℝ → ℕ → ℝ}
    (hp : QueueForwardSolution lam mu p) {M : ℝ} (hpM : ∀ t, 0 ≤ t → ∀ k, |p t k| ≤ M)
    (h0 : ∀ k, p 0 k = if k = j then 1 else 0) :
    ∀ t, 0 ≤ t → ∀ k, p t k = queueLawTimeFrom lam mu j t k := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hpM 0 le_rfl 0)
  refine queue_forward_unique hl hm hp (queueLawTimeFrom_solution hl hm j) (M := max M 1)
    (fun t ht k => (hpM t ht k).trans (le_max_left _ _))
    (fun t ht k => (queueLawTimeFrom_abs_le hl hm j t ht k).trans (le_max_right _ _)) fun k => ?_
  rw [h0, queueLawTimeFrom_zero hl hm]

/-- The wave 7 uniformization law from an empty queue (`queueLawTime`) is the case `j = 0`. -/
theorem queueLawTime_eq_from (lam mu t : ℝ) (k : ℕ) : queueLawTime lam mu t k = queueLawTimeFrom lam mu 0 t k := by
  unfold queueLawTime queueLawTimeFrom poissonMix
  refine tsum_congr fun n => ?_
  unfold queueLaw queueLawFrom
  rw [queueTail_eq_tailIter, queueTail_eq_tailIter]

end UndergradKB.Probability
