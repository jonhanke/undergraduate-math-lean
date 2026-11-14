import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.MonotoneConvergence
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueConvergence

/-! # Probability: the queue converges to its equilibrium from any start (Grinstead–Snell Example 6.29)

Wave 8, a recorded loose end (2).  Wave 7 (`queue_law_tendsto_geometric`) proved that the jump chain
`queueJump` of the queue, started from an empty queue, converges to the geometric law.  The book names no
starting state; here the chain starts from any queue length `j`, or from any initial law.

The proof works again with tails `G_n(k) = P(X_n ≥ k)`, which satisfy `G_n(0) = 1` and the monotone recursion
`G_{n+1}(k+1) = α G_n(k) + β G_n(k+2)`.  The tails started from `j` lie between the tails started from `0`
(which increase to `ρ^k`) and the iterates of the supersolution `ρ^{(k-j)⁺}` (which decrease to a solution of
the recursion that tends to `0` in `k`, hence to `ρ^k`).  -/

open Finset Filter Topology

namespace UndergradKB.Probability

/-- The iterates of the tail recursion of the queue's jump chain from initial tails `H`. -/
noncomputable def tailIter (lam mu : ℝ) (H : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => H k
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      lam / (lam + mu) * tailIter lam mu H n k + mu / (lam + mu) * tailIter lam mu H n (k + 2)

/-- The tails `P(X_0 ≥ k)` of a queue started with `j` customers. -/
def startTail (j k : ℕ) : ℝ := if k ≤ j then 1 else 0

/-- The law `P(X_n = k)` of the jump chain of the queue started with `j` customers. -/
noncomputable def queueLawFrom (lam mu : ℝ) (j n k : ℕ) : ℝ :=
  tailIter lam mu (startTail j) n k - tailIter lam mu (startTail j) n (k + 1)

section

variable {lam mu : ℝ}

theorem tailIter_succ_succ (H : ℕ → ℝ) (n k : ℕ) : tailIter lam mu H (n + 1) (k + 1) =
    lam / (lam + mu) * tailIter lam mu H n k + mu / (lam + mu) * tailIter lam mu H n (k + 2) := rfl

theorem tailIter_at_zero {H : ℕ → ℝ} (hH : H 0 = 1) (n : ℕ) : tailIter lam mu H n 0 = 1 := by
  cases n with
  | zero => exact hH
  | succ n => rfl

theorem tailIter_shift (H : ℕ → ℝ) (n : ℕ) :
    ∀ k, tailIter lam mu H (n + 1) k = tailIter lam mu (tailIter lam mu H 1) n k := by
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    rcases k with _ | k
    · rfl
    · rw [tailIter_succ_succ H (n + 1) k, tailIter_succ_succ (tailIter lam mu H 1) n k, ih k, ih (k + 2)]

theorem tailIter_mono (hl : 0 < lam) (hm : 0 < mu) {H H' : ℕ → ℝ} (h : ∀ k, H k ≤ H' k) (n : ℕ) :
    ∀ k, tailIter lam mu H n k ≤ tailIter lam mu H' n k := by
  have ha : 0 ≤ lam / (lam + mu) := by positivity
  have hb : 0 ≤ mu / (lam + mu) := by positivity
  induction n with
  | zero => exact h
  | succ n ih =>
    intro k
    rcases k with _ | k
    · exact le_rfl
    · rw [tailIter_succ_succ, tailIter_succ_succ]
      nlinarith [ih k, ih (k + 2)]

theorem tailIter_nonneg (hl : 0 < lam) (hm : 0 < mu) {H : ℕ → ℝ} (h : ∀ k, 0 ≤ H k) (n : ℕ) :
    ∀ k, 0 ≤ tailIter lam mu H n k := by
  have ha : 0 ≤ lam / (lam + mu) := by positivity
  have hb : 0 ≤ mu / (lam + mu) := by positivity
  induction n with
  | zero => exact h
  | succ n ih =>
    intro k
    rcases k with _ | k
    · exact zero_le_one
    · rw [tailIter_succ_succ]
      exact add_nonneg (mul_nonneg ha (ih k)) (mul_nonneg hb (ih (k + 2)))

/-- If the initial tails are a supersolution (one step lowers them), the tails decrease with `n`. -/
theorem tailIter_anti (hl : 0 < lam) (hm : 0 < mu) {H : ℕ → ℝ} (h : ∀ k, tailIter lam mu H 1 k ≤ H k)
    (n : ℕ) : ∀ k, tailIter lam mu H (n + 1) k ≤ tailIter lam mu H n k := by
  intro k
  rw [tailIter_shift]
  exact tailIter_mono hl hm h n k

/-- The tails of the queue started from `j` are tails of a law: in `[0, 1]`, decreasing in `k`. -/
theorem tailIter_bounds (hl : 0 < lam) (hm : 0 < mu) {H : ℕ → ℝ} (hH0 : H 0 = 1)
    (hH : ∀ k, 0 ≤ H k ∧ H k ≤ 1 ∧ H (k + 1) ≤ H k) (n : ℕ) :
    ∀ k, 0 ≤ tailIter lam mu H n k ∧ tailIter lam mu H n k ≤ 1 ∧
      tailIter lam mu H n (k + 1) ≤ tailIter lam mu H n k := by
  have hab := queue_alpha_beta hl hm
  have ha : 0 ≤ lam / (lam + mu) := by positivity
  have hb : 0 ≤ mu / (lam + mu) := by positivity
  induction n with
  | zero => exact hH
  | succ n ih =>
    intro k
    rcases k with _ | k
    · refine ⟨by rw [tailIter_at_zero hH0]; norm_num, by rw [tailIter_at_zero hH0], ?_⟩
      rw [tailIter_at_zero hH0, tailIter_succ_succ, tailIter_at_zero hH0]
      nlinarith [(ih 0).2.1, (ih 2).2.1]
    · rw [tailIter_succ_succ, tailIter_succ_succ]
      refine ⟨by nlinarith [(ih k).1, (ih (k + 2)).1], by nlinarith [(ih k).2.1, (ih (k + 2)).2.1], ?_⟩
      nlinarith [(ih k).2.2, (ih (k + 2)).2.2]

theorem tailIter_vanish {H : ℕ → ℝ} {j : ℕ} (hH : ∀ k, j < k → H k = 0) (n : ℕ) :
    ∀ k, n + j < k → tailIter lam mu H n k = 0 := by
  induction n with
  | zero => intro k hk; exact hH k (by omega)
  | succ n ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [tailIter_succ_succ, ih k (by omega), ih (k + 2) (by omega)]
    ring

theorem queueTail_eq_tailIter (n : ℕ) : ∀ k, queueTail lam mu n k = tailIter lam mu (startTail 0) n k := by
  induction n with
  | zero => intro k; simp [queueTail, tailIter, startTail]
  | succ n ih =>
    intro k
    rcases k with _ | k
    · rw [queueTail_zero]; rfl
    · rw [queueTail_succ, tailIter_succ_succ, ih k, ih (k + 2)]

theorem startTail_props (j : ℕ) :
    startTail j 0 = 1 ∧ ∀ k, 0 ≤ startTail j k ∧ startTail j k ≤ 1 ∧ startTail j (k + 1) ≤ startTail j k := by
  refine ⟨by simp [startTail], fun k => ?_⟩
  unfold startTail
  refine ⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num, ?_⟩
  split_ifs <;> first | omega | norm_num

/-- A solution of the tail recursion with `G 0 = 1` that tends to `0` is the geometric tail `ρ^k`. -/
theorem queue_tail_fixed_eq {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) (G : ℕ → ℝ) (hG0 : G 0 = 1)
    (hGrec : ∀ j, G (j + 1) = lam / (lam + mu) * G j + mu / (lam + mu) * G (j + 2))
    (hGK : Tendsto G atTop (𝓝 0)) : ∀ j, G j = (lam / mu) ^ j := by
  have hm : 0 < mu := hl.trans hlm
  set ρ := lam / mu with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hm).2 hlm
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
  have hsum : ∀ K, (1 - G K) * (1 - ρ) = (1 - G 1) * (1 - ρ ^ K) := by
    intro K
    induction K with
    | zero => rw [hG0]; ring
    | succ K ih =>
      have := hD K
      rw [pow_succ]
      linear_combination ih + (1 - ρ) * this
  have hlim1 : Tendsto (fun K => (1 - G K) * (1 - ρ)) atTop (𝓝 ((1 - 0) * (1 - ρ))) :=
    (tendsto_const_nhds.sub hGK).mul_const _
  have hlim2 : Tendsto (fun K => (1 - G 1) * (1 - ρ ^ K)) atTop (𝓝 ((1 - G 1) * (1 - 0))) :=
    (tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1)).const_mul _
  have hG1 : 1 - G 1 = 1 - ρ := by
    have := tendsto_nhds_unique (hlim1.congr fun K => hsum K) hlim2
    linarith
  intro j
  have h := hsum j
  rw [hG1] at h
  have h1 : 0 < 1 - ρ := by linarith
  have : (1 - G j) = 1 - ρ ^ j := mul_right_cancel₀ h1.ne' (h.trans (mul_comm _ _))
  linarith

/-- The tails from an empty queue tend to the geometric tail. -/
theorem queueTail_tendsto (hl : 0 < lam) (hlm : lam < mu) (k : ℕ) :
    Tendsto (fun n => queueTail lam mu n k) atTop (𝓝 ((lam / mu) ^ k)) := by
  have e : ∀ n, queueTail lam mu n k = 1 - ∑ i ∈ range k, queueLaw lam mu n i := by
    intro n
    unfold queueLaw
    rw [sum_range_sub', queueTail_zero]
    ring
  have hs := tendsto_finsetSum (range k) fun i _ => queue_law_tendsto_geometric hl hlm i
  have e2 : ∑ i ∈ range k, queueGeom (lam / mu) i = 1 - (lam / mu) ^ k := by
    have : ∀ i, queueGeom (lam / mu) i = (lam / mu) ^ i - (lam / mu) ^ (i + 1) := fun i => by
      unfold queueGeom; rw [pow_succ]; ring
    simp_rw [this]
    rw [sum_range_sub', pow_zero]
  rw [e2] at hs
  simp_rw [e]
  convert (tendsto_const_nhds (x := (1 : ℝ))).sub hs using 2
  ring

/-- The supersolution `ρ^{(k-j)⁺}` of the tail recursion (needs `λ ≤ μ`). -/
theorem upperTail_super (hl : 0 < lam) (hlm : lam < mu) (j : ℕ) :
    ∀ k, tailIter lam mu (fun k => (lam / mu) ^ (k - j)) 1 k ≤ (lam / mu) ^ (k - j) := by
  have hm : 0 < mu := hl.trans hlm
  have hab := queue_alpha_beta hl hm
  have hp : 0 < lam + mu := by linarith
  intro k
  rcases k with _ | k
  · show (1 : ℝ) ≤ _
    simp
  · show lam / (lam + mu) * (lam / mu) ^ (k - j) + mu / (lam + mu) * (lam / mu) ^ (k + 2 - j) ≤
      (lam / mu) ^ (k + 1 - j)
    rcases lt_trichotomy (k + 1) j with h | h | h
    · rw [Nat.sub_eq_zero_of_le (by omega : k ≤ j), Nat.sub_eq_zero_of_le (by omega : k + 2 ≤ j),
        Nat.sub_eq_zero_of_le (by omega : k + 1 ≤ j)]
      simp only [pow_zero, mul_one]
      linarith
    · rw [Nat.sub_eq_zero_of_le (by omega : k ≤ j), show k + 2 - j = 1 by omega,
        show k + 1 - j = 0 by omega]
      simp only [pow_zero, mul_one, pow_one]
      have e : mu / (lam + mu) * (lam / mu) = lam / (lam + mu) := by field_simp
      rw [e, ← add_div, div_le_one hp]
      linarith
    · obtain ⟨m, hmk⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
      rw [show k - j = m by omega, show k + 2 - j = m + 2 by omega, show k + 1 - j = m + 1 by omega]
      apply le_of_eq
      rw [pow_succ, pow_add]
      field_simp
      ring

/-- The tails of the queue started from `j` tend to the geometric tail `ρ^k`. -/
theorem tailIter_start_tendsto (hl : 0 < lam) (hlm : lam < mu) (j k : ℕ) :
    Tendsto (fun n => tailIter lam mu (startTail j) n k) atTop (𝓝 ((lam / mu) ^ k)) := by
  have hm : 0 < mu := hl.trans hlm
  set ρ := lam / mu with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hm).2 hlm
  set U : ℕ → ℝ := fun k => ρ ^ (k - j) with hU
  have hU0 : U 0 = 1 := by simp [hU]
  have hUnn : ∀ k, 0 ≤ U k := fun k => by positivity
  -- lower and upper comparison
  have hlow : ∀ n k, queueTail lam mu n k ≤ tailIter lam mu (startTail j) n k := by
    intro n k
    rw [queueTail_eq_tailIter]
    exact tailIter_mono hl hm (fun k => by unfold startTail; split_ifs <;> first | omega | norm_num) n k
  have hupp : ∀ n k, tailIter lam mu (startTail j) n k ≤ tailIter lam mu U n k := by
    intro n k
    refine tailIter_mono hl hm (fun k => ?_) n k
    unfold startTail
    split_ifs with h
    · simp [hU, Nat.sub_eq_zero_of_le h]
    · exact hUnn k
  -- the upper iterates decrease to a limit `L`
  have hanti : ∀ k, Antitone fun n => tailIter lam mu U n k := fun k =>
    antitone_nat_of_succ_le fun n => tailIter_anti hl hm (upperTail_super hl hlm j) n k
  have hnn : ∀ n k, 0 ≤ tailIter lam mu U n k := fun n => tailIter_nonneg hl hm hUnn n
  have hbdd : ∀ k, BddBelow (Set.range fun n => tailIter lam mu U n k) := fun k =>
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hnn n k⟩
  set L : ℕ → ℝ := fun k => ⨅ n, tailIter lam mu U n k with hL
  have hT : ∀ k, Tendsto (fun n => tailIter lam mu U n k) atTop (𝓝 (L k)) := fun k =>
    tendsto_atTop_ciInf (hanti k) (hbdd k)
  have hL0 : L 0 = 1 := tendsto_nhds_unique (hT 0) (by simp [tailIter_at_zero hU0])
  have hLrec : ∀ i, L (i + 1) = lam / (lam + mu) * L i + mu / (lam + mu) * L (i + 2) := by
    intro i
    have h1 : Tendsto (fun n => tailIter lam mu U (n + 1) (i + 1)) atTop (𝓝 (L (i + 1))) :=
      (hT (i + 1)).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => tailIter lam mu U (n + 1) (i + 1)) atTop
        (𝓝 (lam / (lam + mu) * L i + mu / (lam + mu) * L (i + 2))) := by
      simp only [tailIter_succ_succ]
      exact ((hT i).const_mul _).add ((hT (i + 2)).const_mul _)
    exact tendsto_nhds_unique h1 h2
  have hLle : ∀ k, L k ≤ U k := fun k => ciInf_le (hbdd k) 0
  have hLnn : ∀ k, 0 ≤ L k := fun k => le_ciInf fun n => hnn n k
  have hUlim : Tendsto U atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp (tendsto_sub_atTop_nat j)
  have hLK : Tendsto L atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUlim hLnn hLle
  have hLval := queue_tail_fixed_eq hl hlm L hL0 hLrec hLK
  -- squeeze
  have hup := hT k
  rw [hLval k] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (queueTail_tendsto hl hlm k) hup
    (fun n => hlow n k) (fun n => hupp n k)

/-- The laws `queueLawFrom j` are the laws of the jump chain `queueJump` started with `j` customers:
`P(X_0 = k) = [k = j]` and `P(X_{n+1} = k) = ∑_i P(X_n = i) P(i, k)`. -/
theorem queueLawFrom_step (hl : 0 < lam) (hm : 0 < mu) (j n : ℕ) :
    (∀ k, queueLawFrom lam mu j 0 k = if k = j then 1 else 0) ∧
    ∀ k, HasSum (fun i => queueLawFrom lam mu j n i * queueJump lam mu i k) (queueLawFrom lam mu j (n + 1) k) := by
  have hab := queue_alpha_beta hl hm
  have h0 := (startTail_props j).1
  refine ⟨fun k => ?_, fun k => ?_⟩
  · show startTail j k - startTail j (k + 1) = _
    unfold startTail
    split_ifs <;> first | omega | norm_num
  rcases k with _ | k
  · convert queueJump_col_zero lam mu (queueLawFrom lam mu j n) using 1
    unfold queueLawFrom
    rw [tailIter_at_zero h0, tailIter_succ_succ, tailIter_at_zero h0]
    simp only [zero_add, Nat.reduceAdd]
    linear_combination (-1 : ℝ) * hab
  · convert queueJump_col_succ lam mu (queueLawFrom lam mu j n) k using 1
    unfold queueLawFrom
    rw [tailIter_succ_succ, tailIter_succ_succ]
    ring

/-- The law after `n` steps from `j` customers is a probability law (supported on `0, …, n + j`). -/
theorem queueLawFrom_prob (hl : 0 < lam) (hm : 0 < mu) (j n : ℕ) :
    (∀ k, 0 ≤ queueLawFrom lam mu j n k) ∧ HasSum (queueLawFrom lam mu j n) 1 := by
  have hb := tailIter_bounds (lam := lam) (mu := mu) hl hm (startTail_props j).1 (startTail_props j).2 n
  have hv : ∀ k, n + j < k → tailIter lam mu (startTail j) n k = 0 :=
    tailIter_vanish (fun k hk => by unfold startTail; simp [show ¬ k ≤ j by omega]) n
  refine ⟨fun k => by unfold queueLawFrom; linarith [(hb k).2.2], ?_⟩
  have h : HasSum (queueLawFrom lam mu j n) (∑ k ∈ range (n + j + 1), queueLawFrom lam mu j n k) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by
      have hk' : n + j < k := by simpa using hk
      unfold queueLawFrom
      rw [hv k hk', hv (k + 1) (by omega), sub_zero]
  convert h using 1
  unfold queueLawFrom
  rw [sum_range_sub', tailIter_at_zero (startTail_props j).1, hv (n + j + 1) (by omega), sub_zero]

theorem queueLawFrom_le_one (hl : 0 < lam) (hm : 0 < mu) (j n k : ℕ) : queueLawFrom lam mu j n k ≤ 1 := by
  have hb := tailIter_bounds (lam := lam) (mu := mu) hl hm (startTail_props j).1 (startTail_props j).2 n
  unfold queueLawFrom
  linarith [(hb k).2.1, (hb (k + 1)).1]

end

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium from any start.  Let the arrival rate be
`λ > 0` and the service rate `μ > λ`, `ρ = λ/μ`.  Started with `j` customers, the law of the jump chain of the
queue (`queueLawFrom j`, the laws of `queueJump` by `queueLawFrom_step`) converges to the geometric law: for
every queue length `k`, `P(X_n = k) → (1-ρ)ρ^k` as `n → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_law_from_tendsto_geometric {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) (j k : ℕ) :
    Tendsto (fun n => queueLawFrom lam mu j n k) atTop (𝓝 (queueGeom (lam / mu) k)) := by
  have e : queueGeom (lam / mu) k = (lam / mu) ^ k - (lam / mu) ^ (k + 1) := by
    unfold queueGeom; rw [pow_succ]; ring
  rw [e]
  exact (tailIter_start_tendsto hl hlm j k).sub (tailIter_start_tendsto hl hlm j (k + 1))

/-- The law after `n` steps of the jump chain of the queue whose initial queue length has law `π`
(law of total probability over the initial length). -/
noncomputable def queueLawMix (lam mu : ℝ) (π : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑' j, π j * queueLawFrom lam mu j n k

theorem queueLawMix_zero {lam mu : ℝ} (π : ℕ → ℝ) (k : ℕ) : queueLawMix lam mu π 0 k = π k := by
  unfold queueLawMix
  rw [tsum_eq_single k]
  · show π k * (startTail k k - startTail k (k + 1)) = π k
    simp [startTail]
  · intro j hj
    show π j * (startTail j k - startTail j (k + 1)) = 0
    unfold startTail
    split_ifs <;> first | omega | simp

/-- Grinstead–Snell Example 6.29 (PR-209), convergence to equilibrium from any initial law.  Let `λ > 0`,
`μ > λ`, `ρ = λ/μ`, and let the initial queue length have law `π` (a probability law on `ℕ`).  Then the law of
the jump chain of the queue after `n` steps converges to the geometric law: `P(X_n = k) → (1-ρ)ρ^k`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_law_mix_tendsto_geometric {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) (π : ℕ → ℝ)
    (hπ0 : ∀ j, 0 ≤ π j) (hπ : HasSum π 1) (k : ℕ) :
    Tendsto (fun n => queueLawMix lam mu π n k) atTop (𝓝 (queueGeom (lam / mu) k)) := by
  have hm : 0 < mu := hl.trans hlm
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun n j => π j * queueLawFrom lam mu j n k)
    (g := fun j => π j * queueGeom (lam / mu) k) hπ.summable
    (fun j => (queue_law_from_tendsto_geometric hl hlm j k).const_mul (π j))
    (Eventually.of_forall fun n j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 j),
        abs_of_nonneg ((queueLawFrom_prob hl hm j n).1 k)]
      exact mul_le_of_le_one_right (hπ0 j) (queueLawFrom_le_one hl hm j n k))
  rw [tsum_mul_right, hπ.tsum_eq, one_mul] at h
  exact h

end UndergradKB.Probability
