import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.MonotoneConvergence
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueEquilibrium

/-! # Probability: the queue converges to its equilibrium (Grinstead–Snell Example 6.29)

Wave 7, a recorded loose end.  The book asserts that "in equilibrium" the queue length is geometric.  Here, for
the jump chain `queueJump` of the queue (the queue observed at the rings of a Poisson clock of rate `λ + μ`),
started from an empty queue: the law after `n` steps tends to the geometric law `(1-ρ)ρ^k`, `ρ = λ/μ < 1`.

The proof works with the tails `G_n(k) = P(X_n ≥ k)`, which satisfy `G_n(0) = 1` and
`G_{n+1}(k+1) = α G_n(k) + β G_n(k+2)` (`α = λ/(λ+μ)`, `β = μ/(λ+μ)`).  This recursion is monotone, so
`G_n(k)` increases with `n` (the chain starts at the bottom) and stays below the geometric tail `ρ^k` (which it
fixes).  The limit solves the recursion, is at most `ρ^k`, and is therefore `ρ^k`. -/

open Finset Filter Topology

namespace UndergradKB.Probability

/-- The tails `P(X_n ≥ k)` of the jump chain of the queue started from an empty queue. -/
noncomputable def queueTail (lam mu : ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      lam / (lam + mu) * queueTail lam mu n k + mu / (lam + mu) * queueTail lam mu n (k + 2)

/-- The law `P(X_n = k)` of the jump chain of the queue started from an empty queue. -/
noncomputable def queueLaw (lam mu : ℝ) (n k : ℕ) : ℝ := queueTail lam mu n k - queueTail lam mu n (k + 1)

section

variable {lam mu : ℝ}

theorem queueTail_zero (n : ℕ) : queueTail lam mu n 0 = 1 := by
  cases n <;> simp [queueTail]

theorem queueTail_succ (n k : ℕ) : queueTail lam mu (n + 1) (k + 1) =
    lam / (lam + mu) * queueTail lam mu n k + mu / (lam + mu) * queueTail lam mu n (k + 2) := rfl

theorem queue_alpha_beta (hl : 0 < lam) (hm : 0 < mu) : lam / (lam + mu) + mu / (lam + mu) = 1 := by
  field_simp

theorem queueTail_bounds (hl : 0 < lam) (hm : 0 < mu) (n : ℕ) :
    ∀ k, 0 ≤ queueTail lam mu n k ∧ queueTail lam mu n k ≤ 1 ∧
      queueTail lam mu n (k + 1) ≤ queueTail lam mu n k := by
  have hab := queue_alpha_beta hl hm
  have ha : 0 ≤ lam / (lam + mu) := by positivity
  have hb : 0 ≤ mu / (lam + mu) := by positivity
  induction n with
  | zero => intro k; rcases k with _ | k <;> simp [queueTail]
  | succ n ih =>
    intro k
    rcases k with _ | k
    · refine ⟨by rw [queueTail_zero]; norm_num, by rw [queueTail_zero], ?_⟩
      rw [queueTail_zero, queueTail_succ]
      nlinarith [(ih 0).2.1, (ih 2).2.1]
    · rw [queueTail_succ, queueTail_succ]
      refine ⟨by nlinarith [(ih k).1, (ih (k + 2)).1], by nlinarith [(ih k).2.1, (ih (k + 2)).2.1], ?_⟩
      nlinarith [(ih k).2.2, (ih (k + 2)).2.2]

theorem queueTail_vanish (n : ℕ) : ∀ k, n < k → queueTail lam mu n k = 0 := by
  induction n with
  | zero => intro k hk; simp [queueTail, show k ≠ 0 by omega]
  | succ n ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [queueTail_succ, ih k (by omega), ih (k + 2) (by omega)]
    ring

theorem queueTail_mono (hl : 0 < lam) (hm : 0 < mu) (n : ℕ) :
    ∀ k, queueTail lam mu n k ≤ queueTail lam mu (n + 1) k := by
  have ha : 0 ≤ lam / (lam + mu) := by positivity
  have hb : 0 ≤ mu / (lam + mu) := by positivity
  induction n with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [queueTail]
    · simp only [queueTail, Nat.add_one_ne_zero, ite_false]
      exact (queueTail_bounds hl hm 1 (k + 1)).1
  | succ n ih =>
    intro k
    rcases k with _ | k
    · rw [queueTail_zero, queueTail_zero]
    · rw [queueTail_succ, queueTail_succ (n + 1)]
      nlinarith [ih k, ih (k + 2)]

theorem queueTail_le_geom (hl : 0 < lam) (hm : 0 < mu) (n : ℕ) :
    ∀ k, queueTail lam mu n k ≤ (lam / mu) ^ k := by
  have ha : 0 ≤ lam / (lam + mu) := by positivity
  have hb : 0 ≤ mu / (lam + mu) := by positivity
  have hρ : 0 ≤ lam / mu := by positivity
  -- the geometric tail is fixed by the recursion
  have hfix : ∀ k, lam / (lam + mu) * (lam / mu) ^ k + mu / (lam + mu) * (lam / mu) ^ (k + 2) =
      (lam / mu) ^ (k + 1) := by
    intro k
    rw [pow_succ, pow_add]
    field_simp
    ring
  induction n with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [queueTail]
    · simp only [queueTail, Nat.add_one_ne_zero, ite_false]
      positivity
  | succ n ih =>
    intro k
    rcases k with _ | k
    · rw [queueTail_zero, pow_zero]
    · rw [queueTail_succ, ← hfix k]
      nlinarith [ih k, ih (k + 2)]

/-- The law after `n` steps is a probability law on the queue lengths (supported on `0, …, n`). -/
theorem queueLaw_prob (hl : 0 < lam) (hm : 0 < mu) (n : ℕ) :
    (∀ k, 0 ≤ queueLaw lam mu n k) ∧ HasSum (queueLaw lam mu n) 1 := by
  refine ⟨fun k => by unfold queueLaw; linarith [(queueTail_bounds hl hm n k).2.2], ?_⟩
  have h : HasSum (queueLaw lam mu n) (∑ k ∈ range (n + 1), queueLaw lam mu n k) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      have hk' : n < k := by simpa using hk
      unfold queueLaw
      rw [queueTail_vanish n k hk', queueTail_vanish n (k + 1) (by omega), sub_zero]
  convert h using 1
  unfold queueLaw
  rw [sum_range_sub', queueTail_zero, queueTail_vanish n (n + 1) (by omega), sub_zero]

/-- The laws `queueLaw` are the laws of the jump chain `queueJump` started from an empty queue:
`P(X_0 = k) = [k = 0]` and `P(X_{n+1} = k) = ∑_i P(X_n = i) P(i, k)`. -/
theorem queueLaw_step (hl : 0 < lam) (hm : 0 < mu) (n : ℕ) :
    (∀ k, queueLaw lam mu 0 k = if k = 0 then 1 else 0) ∧
    ∀ k, HasSum (fun i => queueLaw lam mu n i * queueJump lam mu i k) (queueLaw lam mu (n + 1) k) := by
  have hab := queue_alpha_beta hl hm
  refine ⟨fun k => by rcases k with _ | k <;> simp [queueLaw, queueTail], fun k => ?_⟩
  rcases k with _ | k
  · convert queueJump_col_zero lam mu (queueLaw lam mu n) using 1
    unfold queueLaw
    rw [queueTail_zero, queueTail_succ, queueTail_zero]
    linear_combination (-1 : ℝ) * hab
  · convert queueJump_col_succ lam mu (queueLaw lam mu n) k using 1
    unfold queueLaw
    rw [queueTail_succ, queueTail_succ]
    ring

end

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium.  Let the arrival rate be `λ > 0` and the
service rate `μ > λ`, `ρ = λ/μ`.  Started from an empty queue, the law of the jump chain of the queue
(`queueLaw`, the laws of `queueJump` by `queueLaw_step`) converges to the geometric law: for every queue length
`k`, `P(X_n = k) → (1-ρ)ρ^k` as `n → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_law_tendsto_geometric {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) (k : ℕ) :
    Tendsto (fun n => queueLaw lam mu n k) atTop (𝓝 (queueGeom (lam / mu) k)) := by
  have hm : 0 < mu := hl.trans hlm
  have hab := queue_alpha_beta hl hm
  set ρ := lam / mu with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hm).2 hlm
  -- the tails converge (monotone and bounded)
  have hmono : ∀ j, Monotone fun n => queueTail lam mu n j := fun j =>
    monotone_nat_of_le_succ fun n => queueTail_mono hl hm n j
  have hbdd : ∀ j, BddAbove (Set.range fun n => queueTail lam mu n j) := fun j =>
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (queueTail_bounds hl hm n j).2.1⟩
  set G : ℕ → ℝ := fun j => ⨆ n, queueTail lam mu n j with hG
  have hT : ∀ j, Tendsto (fun n => queueTail lam mu n j) atTop (𝓝 (G j)) := fun j =>
    tendsto_atTop_ciSup (hmono j) (hbdd j)
  -- properties of the limit
  have hG0 : G 0 = 1 := tendsto_nhds_unique (hT 0) (by simp [queueTail_zero])
  have hGrec : ∀ j, G (j + 1) = lam / (lam + mu) * G j + mu / (lam + mu) * G (j + 2) := by
    intro j
    have h1 : Tendsto (fun n => queueTail lam mu (n + 1) (j + 1)) atTop (𝓝 (G (j + 1))) :=
      (hT (j + 1)).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => queueTail lam mu (n + 1) (j + 1)) atTop
        (𝓝 (lam / (lam + mu) * G j + mu / (lam + mu) * G (j + 2))) := by
      simp only [queueTail_succ]
      exact ((hT j).const_mul _).add ((hT (j + 2)).const_mul _)
    exact tendsto_nhds_unique h1 h2
  have hGle : ∀ j, G j ≤ ρ ^ j := fun j => ciSup_le fun n => queueTail_le_geom hl hm n j
  have hGnn : ∀ j, 0 ≤ G j := fun j =>
    le_trans (queueTail_bounds hl hm 0 j).1 (le_ciSup (hbdd j) 0)
  -- differences `D j = G j - G (j+1)` are geometric
  have hD : ∀ j, G j - G (j + 1) = ρ ^ j * (1 - G 1) := by
    intro j
    induction j with
    | zero => rw [hG0]; ring
    | succ j ih =>
      have h := hGrec j
      have e : G (j + 1) - G (j + 2) = ρ * (G j - G (j + 1)) := by
        rw [hρdef]
        field_simp at h ⊢
        linarith
      rw [e, ih, pow_succ]
      ring
  -- telescoping: `1 - G K = (1 - G 1) (1 - ρ^K)/(1 - ρ)`
  have hsum : ∀ K, (1 - G K) * (1 - ρ) = (1 - G 1) * (1 - ρ ^ K) := by
    intro K
    induction K with
    | zero => rw [hG0]; ring
    | succ K ih =>
      have := hD K
      rw [pow_succ]
      linear_combination ih + (1 - ρ) * this
  -- `G K → 0`, so `1 - G 1 = 1 - ρ`
  have hGK : Tendsto G atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1) hGnn hGle
  have hlim1 : Tendsto (fun K => (1 - G K) * (1 - ρ)) atTop (𝓝 ((1 - 0) * (1 - ρ))) :=
    (tendsto_const_nhds.sub hGK).mul_const _
  have hlim2 : Tendsto (fun K => (1 - G 1) * (1 - ρ ^ K)) atTop (𝓝 ((1 - G 1) * (1 - 0))) :=
    (tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1)).const_mul _
  have hG1 : 1 - G 1 = 1 - ρ := by
    have := tendsto_nhds_unique (hlim1.congr fun K => hsum K) hlim2
    linarith
  have hGval : ∀ j, G j = ρ ^ j := by
    intro j
    have h := hsum j
    rw [hG1] at h
    have h1 : 0 < 1 - ρ := by linarith
    have : (1 - G j) = 1 - ρ ^ j := by
      have := mul_right_cancel₀ h1.ne' (h.trans (mul_comm _ _))
      exact this
    linarith
  -- conclusion
  have := (hT k).sub (hT (k + 1))
  rw [hGval, hGval] at this
  have e : queueGeom ρ k = ρ ^ k - ρ ^ (k + 1) := by unfold queueGeom; rw [pow_succ]; ring
  rw [e]
  exact this

end UndergradKB.Probability
