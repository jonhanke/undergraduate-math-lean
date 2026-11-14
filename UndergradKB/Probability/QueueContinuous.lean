import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueConvergence

/-! # Probability: the queue in continuous time converges to its equilibrium (Grinstead–Snell Example 6.29)

Wave 7, a recorded loose end.  The queue of the book in continuous time is obtained from its jump chain
(`queueJump`) by uniformization: events (arrivals, and service completions or idle rings of the service clock)
happen at the times of a Poisson process of rate `ν = λ + μ`, independent of the jump chain.  Started from an
empty queue, the queue length at time `t` therefore has law

  `p_t(k) = ∑_n e^{-νt} (νt)^n / n! · P(X_n = k)`.

* `queueLawTime_prob`: `p_t` is a probability law on the queue lengths for every `t ≥ 0`.
* `queue_time_law_tendsto_geometric`: for `λ < μ`, `p_t(k) → (1-ρ)ρ^k` as `t → ∞` (the book's equilibrium).

The Poisson process and the independence are not constructed (Mathlib has no Poisson process); the law `p_t` is
the formula they give. -/

open Finset Filter Topology

namespace UndergradKB.Probability

/-- The Poisson weights `e^{-νt} (νt)^n / n!`. -/
noncomputable def poissonWeight (ν t : ℝ) (n : ℕ) : ℝ := Real.exp (-(ν * t)) * ((ν * t) ^ n / n.factorial)

theorem poissonWeight_hasSum (ν t : ℝ) : HasSum (poissonWeight ν t) 1 := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp (ν * t)).mul_left (Real.exp (-(ν * t)))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hs
  exact hs

theorem poissonWeight_nonneg {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeight ν t n := by
  unfold poissonWeight; positivity

/-- For fixed `n`, the Poisson weight tends to `0` as `t → ∞`. -/
theorem poissonWeight_tendsto_zero {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    Tendsto (fun t => poissonWeight ν t n) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hν)).div_const (n.factorial : ℝ)
  rw [zero_div] at h
  refine h.congr fun t => ?_
  simp only [Function.comp, id, poissonWeight]
  ring

/-- The law at time `t` of the queue length, started from an empty queue (uniformization). -/
noncomputable def queueLawTime (lam mu t : ℝ) (k : ℕ) : ℝ :=
  ∑' n, poissonWeight (lam + mu) t n * queueLaw lam mu n k

section

variable {lam mu : ℝ}

theorem queueLaw_le_one (hl : 0 < lam) (hm : 0 < mu) (n k : ℕ) : queueLaw lam mu n k ≤ 1 := by
  unfold queueLaw
  linarith [(queueTail_bounds hl hm n k).2.1, (queueTail_bounds hl hm n (k + 1)).1]

theorem queueLawTime_summable (hl : 0 < lam) (hm : 0 < mu) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    Summable fun n => poissonWeight (lam + mu) t n * queueLaw lam mu n k :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg (by linarith) ht n) ((queueLaw_prob hl hm n).1 k))
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg (by linarith) ht n) (queueLaw_le_one hl hm n k))
    (poissonWeight_hasSum _ t).summable

/-- The law at time `t ≥ 0` of the queue length is a probability law. -/
theorem queueLawTime_prob (hl : 0 < lam) (hm : 0 < mu) {t : ℝ} (ht : 0 ≤ t) :
    (∀ k, 0 ≤ queueLawTime lam mu t k) ∧ HasSum (queueLawTime lam mu t) 1 := by
  have hν : 0 ≤ lam + mu := by linarith
  set f : ℕ → ℕ → ℝ := fun n k => poissonWeight (lam + mu) t n * queueLaw lam mu n k with hf
  have hf0 : ∀ n k, 0 ≤ f n k := fun n k =>
    mul_nonneg (poissonWeight_nonneg hν ht n) ((queueLaw_prob hl hm n).1 k)
  have hrow : ∀ n, HasSum (f n) (poissonWeight (lam + mu) t n) := fun n => by
    simpa using ((queueLaw_prob hl hm n).2.mul_left (poissonWeight (lam + mu) t n))
  have hsum : Summable (Function.uncurry f) := by
    refine (summable_prod_of_nonneg (f := Function.uncurry f) (fun p => hf0 p.1 p.2)).2
      ⟨fun n => (hrow n).summable, ?_⟩
    exact (poissonWeight_hasSum _ t).summable.congr fun n => ((hrow n).tsum_eq).symm
  refine ⟨fun k => tsum_nonneg fun n => hf0 n k, ?_⟩
  have hcol : ∀ k, Summable fun n => f n k := fun k => queueLawTime_summable hl hm ht k
  have h := hsum.tsum_comm' (fun n => (hrow n).summable) hcol
  have hval : ∑' n, ∑' k, f n k = 1 := by
    rw [tsum_congr fun n => (hrow n).tsum_eq]
    exact (poissonWeight_hasSum _ t).tsum_eq
  have hsk : Summable fun k => ∑' n, f n k := by
    exact ((summable_prod_of_nonneg (f := fun p : ℕ × ℕ => Function.uncurry f p.swap)
      (fun p => hf0 p.2 p.1)).1 hsum.prod_symm).2
  rw [hval] at h
  have : HasSum (fun k => ∑' n, f n k) 1 := h ▸ hsk.hasSum
  exact this

end

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium in continuous time.  Let the arrival rate
be `λ > 0` and the service rate `μ > λ`, `ρ = λ/μ`.  Started from an empty queue, the law at time `t` of the
queue length (`queueLawTime`, by uniformization) converges to the geometric law: for every `k`,
`P(queue length at time t = k) → (1-ρ)ρ^k` as `t → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_time_law_tendsto_geometric {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) (k : ℕ) :
    Tendsto (fun t => queueLawTime lam mu t k) atTop (𝓝 (queueGeom (lam / mu) k)) := by
  have hm : 0 < mu := hl.trans hlm
  have hν : 0 < lam + mu := by linarith
  set π := queueGeom (lam / mu) k with hπ
  have hπ0 : 0 ≤ π := (queue_geometric_equilibrium hl hlm).1 k
  have hπ1 : π ≤ 1 := by
    have h := (queue_geometric_equilibrium hl hlm).2.1
    exact le_hasSum h k fun j _ => (queue_geometric_equilibrium hl hlm).1 j
  have hconv := queue_law_tendsto_geometric hl hlm k
  rw [Metric.tendsto_atTop] at hconv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv (ε / 2) (by positivity)
  -- the first `N` weights are eventually small
  have hfin : Tendsto (fun t => ∑ n ∈ range N, poissonWeight (lam + mu) t n) atTop (𝓝 0) := by
    have := tendsto_finsetSum (range N) fun n _ => poissonWeight_tendsto_zero hν n
    simpa using this
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 2) (by positivity)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  set w := poissonWeight (lam + mu) t with hw
  have hw0 : ∀ n, 0 ≤ w n := poissonWeight_nonneg hν.le ht0
  have hw1 := poissonWeight_hasSum (lam + mu) t
  -- `p_t(k) - π = ∑ w_n (P(X_n = k) - π)`
  have hdiff : HasSum (fun n => w n * (queueLaw lam mu n k - π)) (queueLawTime lam mu t k - π) := by
    have h1 := (queueLawTime_summable hl hm ht0 k).hasSum
    have h2 := hw1.mul_right π
    rw [one_mul] at h2
    have := h1.sub h2
    refine this.congr_fun ?_
    intro n; ring
  -- bound by `∑_{n<N} w_n + ε/2`
  set g : ℕ → ℝ := fun n => (if n < N then w n else 0) + w n * (ε / 2) with hg
  have hgsum : HasSum g (∑ n ∈ range N, w n + 1 * (ε / 2)) := by
    refine HasSum.add ?_ (hw1.mul_right _)
    have : HasSum (fun n => if n < N then w n else 0)
        (∑ n ∈ range N, if n < N then w n else 0) :=
      hasSum_sum_of_ne_finset_zero fun n hn => by simp only [mem_range] at hn; simp [hn]
    convert this using 1
    exact sum_congr rfl fun n hn => by simp [mem_range.1 hn]
  have hbound : ∀ n, ‖w n * (queueLaw lam mu n k - π)‖ ≤ g n := by
    intro n
    rw [norm_mul, Real.norm_of_nonneg (hw0 n), Real.norm_eq_abs]
    have hq0 := (queueLaw_prob hl hm n).1 k
    have hq1 := queueLaw_le_one hl hm n k
    by_cases hn : n < N
    · have : |queueLaw lam mu n k - π| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      have h3 : 0 ≤ w n * (ε / 2) := mul_nonneg (hw0 n) (by positivity)
      simp only [hg, hn, ite_true]
      nlinarith [mul_le_mul_of_nonneg_left this (hw0 n)]
    · have := hN n (by omega)
      rw [Real.dist_eq] at this
      simp only [hg, hn, ite_false, zero_add]
      exact mul_le_mul_of_nonneg_left this.le (hw0 n)
  have hnorm : ‖queueLawTime lam mu t k - π‖ ≤ ∑ n ∈ range N, w n + 1 * (ε / 2) := by
    rw [← hdiff.tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgsum.summable
    · exact (Summable.tsum_le_tsum hbound
        (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgsum.summable)
        hgsum.summable).trans_eq hgsum.tsum_eq
  have hsmall := hT t htT
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sum_nonneg fun n _ => hw0 n)] at hsmall
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  linarith

end UndergradKB.Probability
