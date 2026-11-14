import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueForward
import UndergradKB.Probability.QueueStart

/-! # Probability: the continuous-time queue from any start (Grinstead–Snell Example 6.29)

Wave 8, a recorded loose end (1), (2).  Wave 7 defined the law at time `t` of the queue length started from an
empty queue by uniformization (`queueLawTime`) and proved it solves the forward equations and converges to the
geometric law.  Here the queue starts with `j` customers:

  `p_t^{(j)}(k) = ∑_n e^{-νt} (νt)^n / n! · P_j(X_n = k)`,  `ν = λ + μ`,

where `P_j(X_n = k)` is the law of the jump chain started from `j` (`queueLawFrom`).

* `queueLawTimeFrom_prob`: a probability law for every `t ≥ 0`;
* `queue_forward_equations_from`: it solves the forward equations with `p_0^{(j)} = [k = j]`;
* `queue_time_law_from_tendsto_geometric`: for `λ < μ` it tends to the geometric law as `t → ∞`.

The arguments are those of wave 7, written once for any family of laws `c n` of a chain that moves by the
jump probabilities of the queue (`poissonMix`). -/

open Finset Filter Topology

namespace UndergradKB.Probability

/-- The Poisson mixture `∑_n e^{-νt} (νt)^n / n! · a_n`. -/
noncomputable def poissonMix (ν t : ℝ) (a : ℕ → ℝ) : ℝ := ∑' n, poissonWeight ν t n * a n

theorem poissonMix_summable {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (ha1 : ∀ n, a n ≤ 1) : Summable fun n => poissonWeight ν t n * a n :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (poissonWeight_nonneg hν ht n) (ha0 n))
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg hν ht n) (ha1 n)) (poissonWeight_hasSum ν t).summable

/-- A Poisson mixture of a convergent sequence in `[0, 1]` converges to the same limit as `t → ∞`. -/
theorem poissonMix_tendsto {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hconv : Tendsto a atTop (𝓝 L)) :
    Tendsto (fun t => poissonMix ν t a) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hconv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv (ε / 2) (by positivity)
  have hfin : Tendsto (fun t => ∑ n ∈ range N, poissonWeight ν t n) atTop (𝓝 0) := by
    have := tendsto_finsetSum (range N) fun n _ => poissonWeight_tendsto_zero hν n
    simpa using this
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 2) (by positivity)
  refine ⟨max T 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  set w := poissonWeight ν t with hw
  have hw0 : ∀ n, 0 ≤ w n := poissonWeight_nonneg hν.le ht0
  have hw1 := poissonWeight_hasSum ν t
  have hdiff : HasSum (fun n => w n * (a n - L)) (poissonMix ν t a - L) := by
    have h1 := (poissonMix_summable hν.le ht0 ha0 ha1).hasSum
    have h2 := hw1.mul_right L
    rw [one_mul] at h2
    exact (h1.sub h2).congr_fun fun n => by ring
  set g : ℕ → ℝ := fun n => (if n < N then w n else 0) + w n * (ε / 2) with hg
  have hgsum : HasSum g (∑ n ∈ range N, w n + 1 * (ε / 2)) := by
    refine HasSum.add ?_ (hw1.mul_right _)
    have : HasSum (fun n => if n < N then w n else 0)
        (∑ n ∈ range N, if n < N then w n else 0) :=
      hasSum_sum_of_ne_finset_zero fun n hn => by simp only [mem_range] at hn; simp [hn]
    convert this using 1
    exact sum_congr rfl fun n hn => by simp [mem_range.1 hn]
  have hbound : ∀ n, ‖w n * (a n - L)‖ ≤ g n := by
    intro n
    rw [norm_mul, Real.norm_of_nonneg (hw0 n), Real.norm_eq_abs]
    have hq0 := ha0 n
    have hq1 := ha1 n
    by_cases hn : n < N
    · have : |a n - L| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      have h3 : 0 ≤ w n * (ε / 2) := mul_nonneg (hw0 n) (by positivity)
      simp only [hg, hn, ite_true]
      nlinarith [mul_le_mul_of_nonneg_left this (hw0 n)]
    · have := hN n (by omega)
      rw [Real.dist_eq] at this
      simp only [hg, hn, ite_false, zero_add]
      exact mul_le_mul_of_nonneg_left this.le (hw0 n)
  have hs : Summable fun n => ‖w n * (a n - L)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgsum.summable
  have hnorm : ‖poissonMix ν t a - L‖ ≤ ∑ n ∈ range N, w n + 1 * (ε / 2) := by
    rw [← hdiff.tsum_eq]
    exact (norm_tsum_le_tsum_norm hs).trans
      ((Summable.tsum_le_tsum hbound hs hgsum.summable).trans_eq hgsum.tsum_eq)
  have hsmall := hT t htT
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sum_nonneg fun n _ => hw0 n)] at hsmall
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  linarith

/-- A Poisson mixture of the laws `c n` of a chain on `ℕ` is a probability law. -/
theorem poissonMix_prob {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (c : ℕ → ℕ → ℝ)
    (hc : ∀ n, (∀ k, 0 ≤ c n k) ∧ HasSum (c n) 1) :
    (∀ k, 0 ≤ poissonMix ν t (fun n => c n k)) ∧ HasSum (fun k => poissonMix ν t (fun n => c n k)) 1 := by
  have hc1 : ∀ n k, c n k ≤ 1 := fun n k => le_hasSum (hc n).2 k fun i _ => (hc n).1 i
  set f : ℕ → ℕ → ℝ := fun n k => poissonWeight ν t n * c n k with hf
  have hf0 : ∀ n k, 0 ≤ f n k := fun n k => mul_nonneg (poissonWeight_nonneg hν ht n) ((hc n).1 k)
  have hrow : ∀ n, HasSum (f n) (poissonWeight ν t n) := fun n => by
    simpa using ((hc n).2.mul_left (poissonWeight ν t n))
  have hsum : Summable (Function.uncurry f) := by
    refine (summable_prod_of_nonneg (f := Function.uncurry f) (fun p => hf0 p.1 p.2)).2
      ⟨fun n => (hrow n).summable, ?_⟩
    exact (poissonWeight_hasSum _ t).summable.congr fun n => ((hrow n).tsum_eq).symm
  refine ⟨fun k => tsum_nonneg fun n => hf0 n k, ?_⟩
  have hcol : ∀ k, Summable fun n => f n k := fun k =>
    poissonMix_summable hν ht (fun n => (hc n).1 k) (fun n => hc1 n k)
  have h := hsum.tsum_comm' (fun n => (hrow n).summable) hcol
  have hval : ∑' n, ∑' k, f n k = 1 := by
    rw [tsum_congr fun n => (hrow n).tsum_eq]
    exact (poissonWeight_hasSum _ t).tsum_eq
  have hsk : Summable fun k => ∑' n, f n k :=
    ((summable_prod_of_nonneg (f := fun p : ℕ × ℕ => Function.uncurry f p.swap)
      (fun p => hf0 p.2 p.1)).1 hsum.prod_symm).2
  rw [hval] at h
  exact h ▸ hsk.hasSum

theorem poissonMix_eq (ν t : ℝ) (a : ℕ → ℝ) : poissonMix ν t a =
    Real.exp (-(ν * t)) * ∑' n, (ν * t) ^ n / n.factorial * a n := by
  unfold poissonMix poissonWeight
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- Derivative in `t` of a Poisson mixture of bounded coefficients. -/
theorem poissonMix_hasDerivAt (ν : ℝ) {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => poissonMix ν s a)
      (-ν * poissonMix ν t a + ν * poissonMix ν t (fun n => a (n + 1))) t := by
  simp_rw [poissonMix_eq]
  have he : HasDerivAt (fun s => Real.exp (-(ν * s))) (Real.exp (-(ν * t)) * -ν) t := by
    have := ((hasDerivAt_id t).const_mul ν).neg.exp
    simpa using this
  convert he.mul (hasDerivAt_expSeries_coeff ν a ha t) using 1
  ring

theorem poissonMix_summable' (ν t : ℝ) {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1) :
    Summable fun n => poissonWeight ν t n * a n := by
  refine Summable.of_norm_bounded ((poissonWeight_hasSum ν t).summable.abs) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ha n)

theorem poissonMix_add (ν t : ℝ) {a b : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1) (hb : ∀ n, |b n| ≤ 1) (x y : ℝ) :
    poissonMix ν t (fun n => x * a n + y * b n) = x * poissonMix ν t a + y * poissonMix ν t b := by
  unfold poissonMix
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((poissonMix_summable' ν t ha).mul_left x).tsum_add ((poissonMix_summable' ν t hb).mul_left y)]
  exact tsum_congr fun n => by ring

/-- Poisson mixtures of the laws of a chain moving by the jump probabilities of the queue solve the forward
equations of the queue. -/
theorem poissonMix_forward {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (c : ℕ → ℕ → ℝ)
    (hc : ∀ n k, |c n k| ≤ 1)
    (h0 : ∀ n, c (n + 1) 0 = (c n 0 + c n 1) * (mu / (lam + mu)))
    (hs : ∀ n k, c (n + 1) (k + 1) = c n k * (lam / (lam + mu)) + c n (k + 2) * (mu / (lam + mu))) :
    (∀ t, HasDerivAt (fun s => poissonMix (lam + mu) s (fun n => c n 0))
      (-lam * poissonMix (lam + mu) t (fun n => c n 0) + mu * poissonMix (lam + mu) t (fun n => c n 1)) t) ∧
    (∀ k t, HasDerivAt (fun s => poissonMix (lam + mu) s (fun n => c n (k + 1)))
      (lam * poissonMix (lam + mu) t (fun n => c n k) -
        (lam + mu) * poissonMix (lam + mu) t (fun n => c n (k + 1)) +
        mu * poissonMix (lam + mu) t (fun n => c n (k + 2))) t) := by
  have hp : lam + mu ≠ 0 := by linarith
  refine ⟨fun t => ?_, fun k t => ?_⟩
  · convert poissonMix_hasDerivAt (lam + mu) (fun n => hc n 0) t using 1
    have e : (fun n => c (n + 1) 0) = fun n => (mu / (lam + mu)) * c n 0 + (mu / (lam + mu)) * c n 1 := by
      funext n; rw [h0]; ring
    rw [e, poissonMix_add _ _ (fun n => hc n 0) (fun n => hc n 1)]
    field_simp
    ring
  · convert poissonMix_hasDerivAt (lam + mu) (fun n => hc n (k + 1)) t using 1
    have e : (fun n => c (n + 1) (k + 1)) =
        fun n => (lam / (lam + mu)) * c n k + (mu / (lam + mu)) * c n (k + 2) := by
      funext n; rw [hs]; ring
    rw [e, poissonMix_add _ _ (fun n => hc n k) (fun n => hc n (k + 2))]
    field_simp
    ring

/-- The law at time `t` of the queue length, started with `j` customers (uniformization). -/
noncomputable def queueLawTimeFrom (lam mu : ℝ) (j : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  poissonMix (lam + mu) t fun n => queueLawFrom lam mu j n k

section

variable {lam mu : ℝ}

theorem queueLawFrom_abs_le (hl : 0 < lam) (hm : 0 < mu) (j n k : ℕ) : |queueLawFrom lam mu j n k| ≤ 1 :=
  abs_le.2 ⟨by linarith [(queueLawFrom_prob hl hm j n).1 k], queueLawFrom_le_one hl hm j n k⟩

/-- The law at time `t ≥ 0` of the queue length started with `j` customers is a probability law. -/
theorem queueLawTimeFrom_prob (hl : 0 < lam) (hm : 0 < mu) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∀ k, 0 ≤ queueLawTimeFrom lam mu j t k) ∧ HasSum (queueLawTimeFrom lam mu j t) 1 :=
  poissonMix_prob (by linarith) ht (fun n k => queueLawFrom lam mu j n k) (queueLawFrom_prob hl hm j)

theorem queueLawTimeFrom_zero (hl : 0 < lam) (hm : 0 < mu) (j k : ℕ) :
    queueLawTimeFrom lam mu j 0 k = if k = j then 1 else 0 := by
  unfold queueLawTimeFrom
  rw [poissonMix_eq, mul_zero, neg_zero, Real.exp_zero, one_mul, tsum_eq_single 0]
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    exact (queueLawFrom_step hl hm j 0).1 k
  · intro n hn; simp [zero_pow hn]

end

/-- Grinstead–Snell Example 6.29 (PR-209), the forward equations from any start.  For arrival rate `λ > 0` and
service rate `μ > 0`, the law `p_t` of the queue length at time `t` started with `j` customers
(`queueLawTimeFrom j`, by uniformization) solves the Kolmogorov forward equations of the queue:
`p_0(k) = [k = j]`, `p_t'(0) = -λ p_t(0) + μ p_t(1)` and
`p_t'(k+1) = λ p_t(k) - (λ+μ) p_t(k+1) + μ p_t(k+2)` for every real `t`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_forward_equations_from {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (j : ℕ) :
    (∀ k, queueLawTimeFrom lam mu j 0 k = if k = j then 1 else 0) ∧
    (∀ t, HasDerivAt (fun s => queueLawTimeFrom lam mu j s 0)
      (-lam * queueLawTimeFrom lam mu j t 0 + mu * queueLawTimeFrom lam mu j t 1) t) ∧
    (∀ k t, HasDerivAt (fun s => queueLawTimeFrom lam mu j s (k + 1))
      (lam * queueLawTimeFrom lam mu j t k - (lam + mu) * queueLawTimeFrom lam mu j t (k + 1) +
        mu * queueLawTimeFrom lam mu j t (k + 2)) t) := by
  have h := poissonMix_forward hl hm (fun n k => queueLawFrom lam mu j n k) (queueLawFrom_abs_le hl hm j)
    (fun n => ((queueLawFrom_step hl hm j n).2 0).unique (queueJump_col_zero lam mu _))
    (fun n k => ((queueLawFrom_step hl hm j n).2 (k + 1)).unique (queueJump_col_succ lam mu _ k))
  exact ⟨queueLawTimeFrom_zero hl hm j, h.1, h.2⟩

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium in continuous time from any start.  Let
`λ > 0`, `μ > λ`, `ρ = λ/μ`.  Started with `j` customers, the law at time `t` of the queue length
(`queueLawTimeFrom j`) converges to the geometric law: `P(queue length at time t = k) → (1-ρ)ρ^k` as `t → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_time_law_from_tendsto_geometric {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) (j k : ℕ) :
    Tendsto (fun t => queueLawTimeFrom lam mu j t k) atTop (𝓝 (queueGeom (lam / mu) k)) := by
  have hm : 0 < mu := hl.trans hlm
  have hg := queue_geometric_equilibrium hl hlm
  exact poissonMix_tendsto (by linarith) (fun n => (queueLawFrom_prob hl hm j n).1 k)
    (fun n => queueLawFrom_le_one hl hm j n k) (hg.1 k) (le_hasSum hg.2.1 k fun i _ => hg.1 i)
    (queue_law_from_tendsto_geometric hl hlm j k)

end UndergradKB.Probability
