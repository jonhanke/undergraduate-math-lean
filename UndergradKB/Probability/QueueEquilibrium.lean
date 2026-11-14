import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesQueueStock

/-! # Probability: the equilibrium law of the queue is unique (Grinstead–Snell Example 6.29)

Wave 7, a recorded loose end.  Wave 5 (`queue_geometric_equilibrium`) checked that the geometric law
`s_j = (1-ρ)ρ^j`, `ρ = λ/μ`, solves the balance equations of the queue.  Here the converse: the balance equations
of the queue length (a birth-death process with birth rate `λ` and death rate `μ`) determine the law.

* `queue_balance_unique`: a probability law on `ℕ` solving the global balance equations
  `λ s_0 = μ s_1`, `(λ+μ) s_{j+1} = λ s_j + μ s_{j+2}` exists only when `λ < μ`, and it is the geometric law.
* `queueJump`: the jump chain of the queue observed at the rings of a Poisson clock of rate `λ + μ`
  (a customer arrives with probability `λ/(λ+μ)`, a service ends with probability `μ/(λ+μ)`, nothing happens
  when the server is idle and the service clock rings); `queue_jump_stationary_iff`: its stationary laws are
  exactly the geometric law, and only when `λ < μ`.

Not proved here (a recorded loose end): the construction of the continuous-time queue process and the convergence of
its law to the geometric law. -/

open Finset Filter Topology

namespace UndergradKB.Probability

/-- From the global balance equations, detailed balance `λ s_j = μ s_{j+1}` for every `j`. -/
theorem queue_detailed_of_global {lam mu : ℝ} (s : ℕ → ℝ) (h0 : lam * s 0 = mu * s 1)
    (hj : ∀ j, (lam + mu) * s (j + 1) = lam * s j + mu * s (j + 2)) :
    ∀ j, lam * s j = mu * s (j + 1) := by
  intro j
  induction j with
  | zero => exact h0
  | succ j ih => have := hj j; linarith

/-- Grinstead–Snell Example 6.29 (PR-209), uniqueness of the equilibrium law.  Let the arrival rate be `λ > 0`
and the service rate `μ > 0`.  If a probability law `s` on the queue lengths `0, 1, 2, …` solves the global
balance equations of the queue, `λ s_0 = μ s_1` and `(λ+μ) s_{j+1} = λ s_j + μ s_{j+2}`, then `λ < μ` and
`s_j = (1-ρ)ρ^j` with `ρ = λ/μ`: the geometric law of the book is the only equilibrium, and there is none when
`λ ≥ μ`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_balance_unique {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (s : ℕ → ℝ)
    (hs : ∀ j, 0 ≤ s j) (h1 : HasSum s 1) (h0 : lam * s 0 = mu * s 1)
    (hj : ∀ j, (lam + mu) * s (j + 1) = lam * s j + mu * s (j + 2)) :
    lam < mu ∧ s = queueGeom (lam / mu) := by
  have hd := queue_detailed_of_global s h0 hj
  set ρ := lam / mu with hρ
  have hρ0 : 0 < ρ := by positivity
  have hpow : ∀ j, s j = s 0 * ρ ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := hd j
      rw [pow_succ, ← mul_assoc, ← ih, hρ]
      field_simp
      linarith
  -- `s 0 > 0`, since otherwise every term vanishes
  have hs0 : 0 < s 0 := by
    rcases (hs 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have : s = fun _ => 0 := funext fun j => by rw [hpow j, ← h, zero_mul]
      rw [this] at h1
      exact one_ne_zero (h1.unique hasSum_zero)
  -- the terms tend to `0`, so `ρ < 1`
  have hρ1 : ρ < 1 := by
    by_contra hc
    push Not at hc
    have ht := h1.summable.tendsto_atTop_zero
    have hge : ∀ j, s 0 ≤ s j := fun j => by
      rw [hpow j]; exact le_mul_of_one_le_right hs0.le (one_le_pow₀ hc)
    have : s 0 ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hge)
    linarith
  have hlm : lam < mu := by rwa [hρ, div_lt_one hm] at hρ1
  refine ⟨hlm, ?_⟩
  have hg := (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left (s 0)
  have e : s = fun j => s 0 * ρ ^ j := funext hpow
  rw [← e] at hg
  have hval := h1.unique hg
  have h1' : 0 < 1 - ρ := by linarith
  have : s 0 = 1 - ρ := by
    field_simp at hval; linarith
  funext j
  rw [hpow j, this]
  rfl

/-- The jump chain of the queue on a Poisson clock of rate `λ + μ` (uniformization): from `i` the queue goes to
`i + 1` with probability `λ/(λ+μ)`, to `i - 1` with probability `μ/(λ+μ)` when `i ≥ 1`, and stays at `0` with
probability `μ/(λ+μ)` when `i = 0`. -/
noncomputable def queueJump (lam mu : ℝ) (i k : ℕ) : ℝ :=
  if k = i + 1 then lam / (lam + mu)
  else if i = k + 1 then mu / (lam + mu)
  else if i = 0 ∧ k = 0 then mu / (lam + mu) else 0

theorem queueJump_row {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (i : ℕ) :
    (∀ k, 0 ≤ queueJump lam mu i k) ∧ HasSum (queueJump lam mu i) 1 := by
  have hp : 0 < lam + mu := by linarith
  refine ⟨fun k => ?_, ?_⟩
  · unfold queueJump; split_ifs <;> positivity
  · rcases i with _ | i
    · have : HasSum (queueJump lam mu 0) (∑ k ∈ {0, 1}, queueJump lam mu 0 k) :=
        hasSum_sum_of_ne_finset_zero fun k hk => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          unfold queueJump; simp [hk.1, hk.2]
      convert this using 1
      simp [queueJump]
      field_simp
      ring
    · have : HasSum (queueJump lam mu (i + 1)) (∑ k ∈ {i, i + 2}, queueJump lam mu (i + 1) k) :=
        hasSum_sum_of_ne_finset_zero fun k hk => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          unfold queueJump
          split_ifs with h1 h2 h3 <;> first | (exfalso; omega) | (exfalso; exact h3.1) | rfl
      convert this using 1
      rw [Finset.sum_pair (by omega)]
      have e : ¬ (i = i + 2) := by omega
      simp [queueJump, e]
      field_simp
      ring

/-- Column `0` of the stationarity equations of the jump chain. -/
theorem queueJump_col_zero (lam mu : ℝ) (s : ℕ → ℝ) :
    HasSum (fun i => s i * queueJump lam mu i 0) ((s 0 + s 1) * (mu / (lam + mu))) := by
  have : HasSum (fun i => s i * queueJump lam mu i 0) (∑ i ∈ {0, 1}, s i * queueJump lam mu i 0) :=
    hasSum_sum_of_ne_finset_zero fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      unfold queueJump
      split_ifs with h1 h2 h3 <;> first | (exfalso; omega) | simp
  convert this using 1
  simp [queueJump]
  ring

/-- Column `k + 1` of the stationarity equations of the jump chain. -/
theorem queueJump_col_succ (lam mu : ℝ) (s : ℕ → ℝ) (k : ℕ) :
    HasSum (fun i => s i * queueJump lam mu i (k + 1))
      (s k * (lam / (lam + mu)) + s (k + 2) * (mu / (lam + mu))) := by
  have : HasSum (fun i => s i * queueJump lam mu i (k + 1))
      (∑ i ∈ {k, k + 2}, s i * queueJump lam mu i (k + 1)) :=
    hasSum_sum_of_ne_finset_zero fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      unfold queueJump
      split_ifs with h1 h2 h3 <;> first | (exfalso; omega) | (exfalso; exact h3.2) | simp
  convert this using 1
  rw [Finset.sum_pair (by omega)]
  simp [queueJump]

/-- Grinstead–Snell Example 6.29 (PR-209), the equilibrium of the jump chain.  For arrival rate `λ > 0` and
service rate `μ > 0`, a probability law `s` on `ℕ` is stationary for the jump chain `queueJump` of the queue
(`∑_i s_i P(i,k) = s_k` for every `k`) if and only if `λ < μ` and `s` is the geometric law `(1-ρ)ρ^j`,
`ρ = λ/μ`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_jump_stationary_iff {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (s : ℕ → ℝ)
    (hs : ∀ j, 0 ≤ s j) (h1 : HasSum s 1) :
    (∀ k, HasSum (fun i => s i * queueJump lam mu i k) (s k)) ↔
      lam < mu ∧ s = queueGeom (lam / mu) := by
  have hp : 0 < lam + mu := by linarith
  constructor
  · intro hst
    apply queue_balance_unique hl hm s hs h1
    · have := (queueJump_col_zero lam mu s).unique (hst 0)
      field_simp at this
      linarith
    · intro j
      have := (queueJump_col_succ lam mu s j).unique (hst (j + 1))
      field_simp at this
      linarith
  · rintro ⟨hlm, rfl⟩
    obtain ⟨-, -, -, hbal, hb0, hglob⟩ := queue_geometric_equilibrium hl hlm
    intro k
    rcases k with _ | k
    · convert queueJump_col_zero lam mu (queueGeom (lam / mu)) using 1
      field_simp
      linarith
    · convert queueJump_col_succ lam mu (queueGeom (lam / mu)) k using 1
      field_simp
      linarith [hglob k]

end UndergradKB.Probability
