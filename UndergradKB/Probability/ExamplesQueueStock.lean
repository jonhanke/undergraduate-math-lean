import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Exponential
import UndergradKB.Common.Attr
import UndergradKB.Probability.RandomWalk
import UndergradKB.Probability.ArcSine
import UndergradKB.Probability.ContinuousDistributions

/-! # Probability: heads or tails with 40 tosses, Mr. Ace's stock system, the queue
(Grinstead–Snell Examples 1.4, 5.7, 6.16, 6.29)

* PR-207 (Example 1.4): for `2n` tosses (`n = 20` for the book's 40) the final winnings `2k - 2n` have
  probability `C(2n,k)/2^{2n}`, largest for winnings `0` and smallest for `±2n`; the number `2k` of times in the
  lead has probability `u_{2k} u_{2n-2k}` (the repo's Theorem 12.4, `leadCount_prob`), largest for `k = 0, n`
  and smallest for `k = n/2`.  The book only states these as guesses confirmed by simulation.
* PR-208 (Example 6.16): Mr. Ace's system on the fair `±1` walk has expected winnings `0` and is ahead after 20
  days with probability `639771/2^20 ≈ .6101`.
* PR-209 (Examples 5.7, 6.29): the queue.  The book asserts (without proof) that the queue length in equilibrium
  is geometric, Little's law, and that the waiting time is exponential with rate `μ - λ` ("the proof is too
  complicated to give here"); here the geometric law is checked against the balance equations, Little's law is a
  hypothesis, and the exponential law of the time in the system is derived from the geometric law by a series
  computation. -/

open Finset MeasureTheory ProbabilityTheory

namespace UndergradKB.Probability

/-! ## PR-207: heads or tails -/

/-- Probability, under the uniform law on `Fin N → Bool`, of the set of paths satisfying `P`. -/
def htProb (N : ℕ) (P : (Fin N → Bool) → Prop) [DecidablePred P] : ℚ :=
  ((univ.filter P).card : ℚ) / 2 ^ N

/-- `P(Peter's final winnings are 2k - 2n)` in `2n` tosses. -/
def htFinalProb (n k : ℕ) : ℚ := htProb (2 * n) fun ω => walkPos ω (2 * n) = 2 * (k : ℤ) - 2 * n

/-- `P(Peter is in the lead exactly 2k times)` in `2n` tosses (the repo's `leadCount`, with the book's convention
for the times when the winnings are `0`). -/
def htLeadProb (n k : ℕ) : ℚ := htProb (2 * n) fun ω => leadCount ω = 2 * k

theorem htFinalProb_eq (n k : ℕ) : htFinalProb n k = ((2 * n).choose k : ℚ) / 2 ^ (2 * n) := by
  unfold htFinalProb htProb
  have : (univ.filter fun ω : Fin (2 * n) → Bool => walkPos ω (2 * n) = 2 * (k : ℤ) - 2 * n) =
      univ.filter fun ω => ups ω = k := by
    apply filter_congr
    intro ω _
    rw [walkPos_of_le ω le_rfl, total_eq]
    push_cast
    omega
  rw [this, card_ups]

/-- Grinstead–Snell Example 1.4 (PR-207), final winnings.  In `2n` fair tosses (`n = 20` for the book's 40
tosses) Peter's final winnings `2k - 2n` have probability `C(2n,k)/2^{2n}`; this is largest for winnings `0`
(`k = n`) and smallest for the extreme winnings `±2n` (`k = 0` and `k = 2n`, which have equal probability
`1/2^{2n}`). -/
@[kb "grinsteadsnell2006" "Example 1.4, p. 13"]
theorem heads_tails_final_winnings (n : ℕ) :
    (∀ k, htFinalProb n k = ((2 * n).choose k : ℚ) / 2 ^ (2 * n)) ∧
    (∀ k, k ≤ 2 * n → htFinalProb n k ≤ htFinalProb n n ∧ htFinalProb n 0 ≤ htFinalProb n k) ∧
    htFinalProb n 0 = htFinalProb n (2 * n) ∧ htFinalProb n 0 = 1 / 2 ^ (2 * n) := by
  refine ⟨htFinalProb_eq n, fun k hk => ?_, ?_, ?_⟩
  · have hp : (0 : ℚ) < 2 ^ (2 * n) := by positivity
    rw [htFinalProb_eq, htFinalProb_eq, htFinalProb_eq]
    constructor
    · refine div_le_div_of_nonneg_right ?_ hp.le
      have : (2 * n).choose k ≤ (2 * n).choose n := by
        have := Nat.choose_le_middle k (2 * n)
        rwa [show 2 * n / 2 = n by omega] at this
      exact_mod_cast this
    · refine div_le_div_of_nonneg_right ?_ hp.le
      have : 1 ≤ (2 * n).choose k := Nat.choose_pos hk
      simpa using (by exact_mod_cast this : (1 : ℚ) ≤ ((2 * n).choose k : ℚ))
  · rw [htFinalProb_eq, htFinalProb_eq]; simp
  · rw [htFinalProb_eq]; simp

/-- The sequence `u_{2k} u_{2n-2k}` of the lead-time law, `k = 0, …, n`. -/
noncomputable def htLeadSeq (n k : ℕ) : ℚ := c k * c (n - k)

theorem c_pos' (k : ℕ) : 0 < c k := by
  unfold c
  have : 0 < (2 * k).choose k := Nat.choose_pos (by omega)
  positivity

theorem htLeadSeq_step (n k : ℕ) (h : 2 * k + 1 ≤ n) : htLeadSeq n (k + 1) ≤ htLeadSeq n k := by
  obtain ⟨m, hm⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
  have hkm : k ≤ m := by omega
  have e1 : n - (k + 1) = m := by omega
  have e2 : n - k = m + 1 := by omega
  unfold htLeadSeq
  rw [e1, e2]
  have h1 := c_succ k
  have h2 := c_succ m
  have hk := c_pos' k
  have hm' := c_pos' m
  have hk1 := c_pos' (k + 1)
  have hm1 := c_pos' (m + 1)
  have hkm' : (k : ℚ) ≤ m := by exact_mod_cast hkm
  have hpos : (0 : ℚ) < 4 * ((k : ℚ) + 1) * ((m : ℚ) + 1) := by positivity
  have key : 4 * ((k : ℚ) + 1) * ((m : ℚ) + 1) * (c (k + 1) * c m) ≤
      4 * ((k : ℚ) + 1) * ((m : ℚ) + 1) * (c k * c (m + 1)) := by
    have e3 : 4 * ((k : ℚ) + 1) * ((m : ℚ) + 1) * (c (k + 1) * c m) =
        2 * ((m : ℚ) + 1) * (2 * ((k : ℚ) + 1) * c (k + 1)) * c m := by ring
    have e4 : 4 * ((k : ℚ) + 1) * ((m : ℚ) + 1) * (c k * c (m + 1)) =
        2 * ((k : ℚ) + 1) * c k * (2 * ((m : ℚ) + 1) * c (m + 1)) := by ring
    rw [e3, e4, h1, h2]
    have h0 : 0 ≤ c k * c m := by positivity
    have hd : 0 ≤ ((k : ℚ) + 1) * (2 * m + 1) - ((m : ℚ) + 1) * (2 * k + 1) := by nlinarith
    nlinarith [mul_nonneg h0 hd]
  exact le_of_mul_le_mul_left key hpos

theorem htLeadSeq_anti (n : ℕ) : ∀ l j, j ≤ l → 2 * l ≤ n → htLeadSeq n l ≤ htLeadSeq n j := by
  intro l
  induction l with
  | zero => intro j hj _; obtain rfl : j = 0 := by omega
            exact le_rfl
  | succ l ih =>
    intro j hj hl
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact le_rfl
    · exact (htLeadSeq_step n l (by omega)).trans (ih j (by omega) (by omega))

theorem htLeadSeq_symm (n k : ℕ) (hk : k ≤ n) : htLeadSeq n (n - k) = htLeadSeq n k := by
  unfold htLeadSeq
  rw [show n - (n - k) = k by omega, mul_comm]

theorem htLeadProb_eq (n k : ℕ) (hk : k ≤ n) : htLeadProb n k = htLeadSeq n k := by
  unfold htLeadProb htProb htLeadSeq
  rw [leadCount_prob n k hk, u_two_mul, u_two_mul]

/-- Grinstead–Snell Example 1.4 (PR-207), times in the lead.  In `2n` fair tosses (`n = 20` for the book's 40
tosses) Peter is in the lead exactly `2k` times with probability `u_{2k} u_{2n-2k}` (the repo's Theorem 12.4,
`leadCount_prob`); this is largest for `k = 0` and `k = n` (which have equal probability `u_{2n}`) and, when
`n` is even, smallest for `k = n/2`.  For 40 tosses: 0 or 40 times in the lead is most likely, 20 least likely. -/
@[kb "grinsteadsnell2006" "Example 1.4, p. 13"]
theorem heads_tails_lead_times (n : ℕ) :
    (∀ k, k ≤ n → htLeadProb n k = u (2 * k) * u (2 * (n - k))) ∧
    htLeadProb n 0 = htLeadProb n n ∧
    (∀ k, k ≤ n → htLeadProb n k ≤ htLeadProb n 0) ∧
    (∀ h, n = 2 * h → ∀ k, k ≤ n → htLeadProb n h ≤ htLeadProb n k) := by
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, fun h hh k hk => ?_⟩
  · rw [htLeadProb_eq n k hk, htLeadSeq, u_two_mul, u_two_mul]
  · rw [htLeadProb_eq n 0 (by omega), htLeadProb_eq n n le_rfl]
    have := htLeadSeq_symm n 0 (Nat.zero_le n)
    rw [Nat.sub_zero] at this
    exact this.symm
  · rw [htLeadProb_eq n k hk, htLeadProb_eq n 0 (by omega)]
    by_cases h2 : 2 * k ≤ n
    · exact htLeadSeq_anti n k 0 (by omega) h2
    · rw [← htLeadSeq_symm n k hk]
      exact htLeadSeq_anti n (n - k) 0 (by omega) (by omega)
  · rw [htLeadProb_eq n h (by omega), htLeadProb_eq n k hk]
    by_cases h2 : 2 * k ≤ n
    · exact htLeadSeq_anti n h k (by omega) (by omega)
    · rw [← htLeadSeq_symm n k hk]
      exact htLeadSeq_anti n h (n - k) (by omega) (by omega)

/-! ## PR-209: the queue -/

/-- The geometric law `s_j = (1 - ρ) ρ^j` of the queue length in equilibrium. -/
noncomputable def queueGeom (ρ : ℝ) (j : ℕ) : ℝ := (1 - ρ) * ρ ^ j

/-- Grinstead–Snell Example 6.29 (PR-209), the means: exponential interarrival and service times with rates
`λ, μ > 0` have means `1/λ` and `1/μ`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_exponential_means {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) :
    ∫ x, x ∂(expMeasure lam) = 1 / lam ∧ ∫ x, x ∂(expMeasure mu) = 1 / mu :=
  ⟨integral_expMeasure hl, integral_expMeasure hm⟩

/-- Grinstead–Snell Example 6.29 (PR-209), the equilibrium queue length.  For arrival rate `λ`, service rate `μ`
with traffic intensity `ρ = λ/μ < 1`, the law `s_j = (1-ρ)ρ^j` is a probability law with mean `ρ/(1-ρ)` which
satisfies the detailed balance equations `λ s_j = μ s_{j+1}` and the global balance equations of the
birth-death chain (`λ s_0 = μ s_1` and `(λ+μ) s_{j+1} = λ s_j + μ s_{j+2}`).  (The book asserts that this is
the equilibrium law; it does not derive it.) -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_geometric_equilibrium {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) :
    (∀ j, 0 ≤ queueGeom (lam / mu) j) ∧ HasSum (queueGeom (lam / mu)) 1 ∧
    HasSum (fun j : ℕ => (j : ℝ) * queueGeom (lam / mu) j) ((lam / mu) / (1 - lam / mu)) ∧
    (∀ j, lam * queueGeom (lam / mu) j = mu * queueGeom (lam / mu) (j + 1)) ∧
    lam * queueGeom (lam / mu) 0 = mu * queueGeom (lam / mu) 1 ∧
    (∀ j, (lam + mu) * queueGeom (lam / mu) (j + 1) =
      lam * queueGeom (lam / mu) j + mu * queueGeom (lam / mu) (j + 2)) := by
  have hm : 0 < mu := hl.trans hlm
  have h0 : 0 < lam / mu := by positivity
  have h1 : lam / mu < 1 := (div_lt_one hm).2 hlm
  have h1' : 0 < 1 - lam / mu := by linarith
  have hbal : ∀ j, lam * queueGeom (lam / mu) j = mu * queueGeom (lam / mu) (j + 1) := by
    intro j
    unfold queueGeom
    rw [pow_succ]
    field_simp
  refine ⟨fun j => ?_, ?_, ?_, hbal, hbal 0, fun j => ?_⟩
  · unfold queueGeom; positivity
  · have := (hasSum_geometric_of_lt_one h0.le h1).mul_left (1 - lam / mu)
    have e : queueGeom (lam / mu) = fun i => (1 - lam / mu) * (lam / mu) ^ i := rfl
    rw [e]
    rwa [mul_inv_cancel₀ h1'.ne'] at this
  · have := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := lam / mu)
      (by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1)).mul_left (1 - lam / mu)
    convert this using 1
    · funext j; unfold queueGeom; ring
    · field_simp
  · have a := hbal j
    have b := hbal (j + 1)
    linarith

/-- Grinstead–Snell Example 6.29 (PR-209), Little's law consequence.  With `ρ = λ/μ < 1`, the geometric law has
mean `N = ρ/(1-ρ)`; if Little's law `N = λ T` holds (the book does not prove it, and here it is the hypothesis
`hL` on the numbers `N`, `T`), then `T = 1/(μ - λ)`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_little_waiting_time {lam mu N T : ℝ} (hl : 0 < lam) (hlm : lam < mu)
    (hN : N = (lam / mu) / (1 - lam / mu)) (hL : N = lam * T) : T = 1 / (mu - lam) := by
  have hm : 0 < mu := hl.trans hlm
  have h2 : mu - lam ≠ 0 := by linarith
  have h3 : N = lam / (mu - lam) := by
    rw [hN]; field_simp
  rw [h3] at hL
  field_simp at hL ⊢
  nlinarith [hL]

/-- Grinstead–Snell Example 5.7 (PR-209), the time in the system in equilibrium.  A customer who finds `j`
customers ahead with probability `(1-ρ)ρ^j` (`ρ = λ/μ < 1`) and then spends `j+1` independent exponential(`μ`)
service times in the system has total time of density `∑_j (1-ρ)ρ^j · gamma(j+1, μ)(t)` (the Erlang
densities `μ^{j+1} t^j e^{-μt}/j!`), and this is the exponential density of rate `μ - λ`, for every real `t`.
(The book only asserts that the waiting time is exponential, "the proof is too complicated to give here".) -/
@[kb "grinsteadsnell2006" "Example 5.7, p. 216"]
theorem queue_time_in_system_density {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) (t : ℝ) :
    HasSum (fun j : ℕ => queueGeom (lam / mu) j * gammaPDFReal ((j : ℝ) + 1) mu t)
      (exponentialPDFReal (mu - lam) t) := by
  have hm : 0 < mu := hl.trans hlm
  by_cases ht : 0 ≤ t
  · have hs := (NormedSpace.expSeries_div_hasSum_exp (lam * t)).mul_left
      ((mu - lam) * Real.exp (-(mu * t)))
    rw [← Real.exp_eq_exp_ℝ] at hs
    convert hs using 1
    · funext j
      unfold queueGeom gammaPDFReal
      have e1 : mu ^ ((j : ℝ) + 1) = mu ^ (j + 1) := by
        exact_mod_cast Real.rpow_natCast mu (j + 1)
      have e2 : t ^ ((j : ℝ) + 1 - 1) = t ^ j := by simp
      have e3 : Real.Gamma ((j : ℝ) + 1) = (j.factorial : ℝ) := Real.Gamma_nat_eq_factorial j
      have e4 : (lam / mu) ^ j = lam ^ j / mu ^ j := div_pow _ _ _
      simp only [ht, ↓reduceIte, e1, e2, e3, e4]
      field_simp
      ring
    · have : exponentialPDFReal (mu - lam) t = (mu - lam) * Real.exp (-((mu - lam) * t)) := by
        simp [exponentialPDFReal, gammaPDFReal, ht]
      rw [this, mul_assoc, ← Real.exp_add]
      congr 2
      ring
  · have h0 : ∀ j : ℕ, queueGeom (lam / mu) j * gammaPDFReal ((j : ℝ) + 1) mu t = 0 := by
      intro j; simp [gammaPDFReal, ht]
    have : exponentialPDFReal (mu - lam) t = 0 := by simp [exponentialPDFReal, gammaPDFReal, ht]
    rw [this]
    rw [show (fun j : ℕ => queueGeom (lam / mu) j * gammaPDFReal ((j : ℝ) + 1) mu t) = fun _ => 0
      from funext h0]
    exact hasSum_zero

/-! ## PR-208: Mr. Ace's stock system -/

/-- Mr. Ace's holding indicator from a position function `w` (`w k` = price at time `k` minus the first-day
price `V`): he holds the stock at time `0` (he buys at `V`), sells when the price reaches `V + 1`, and buys again
when it falls back to `V`.  The value at time `i` is a function of `w 0, …, w i` only. -/
def aceHoldW (w : ℕ → ℤ) : ℕ → Bool
  | 0 => true
  | i + 1 => if w (i + 1) = 1 then false else if w (i + 1) = 0 then true else aceHoldW w i

/-- Whether Mr. Ace holds the stock during day `i + 1` (before the move `ω i` of that day). -/
def aceHold {n : ℕ} (ω : Fin n → Bool) (i : ℕ) : Bool := aceHoldW (walkPos ω) i

/-- Mr. Ace's winnings: the sum over the days of (holding before the day's move) times (the move). -/
def aceWin {n : ℕ} (ω : Fin n → Bool) : ℤ := ∑ i : Fin n, if aceHold ω i then step (ω i) else 0

theorem aceHoldW_congr {w w' : ℕ → ℤ} {i : ℕ} (h : ∀ k, k ≤ i → w k = w' k) :
    aceHoldW w i = aceHoldW w' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [aceHoldW]
    rw [h (i + 1) le_rfl, ih fun k hk => h k (by omega)]

/-- Reversing the move of day `i + 1` (coordinate `i`). -/
def aceFlip {n : ℕ} (i : Fin n) (ω : Fin n → Bool) : Fin n → Bool := Function.update ω i (!ω i)

theorem aceFlip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (aceFlip i) := by
  intro ω
  funext j
  by_cases h : j = i <;> simp [aceFlip, h]

theorem walkPos_aceFlip {n : ℕ} (i : Fin n) (ω : Fin n → Bool) {k : ℕ} (hk : k ≤ i) :
    walkPos (aceFlip i ω) k = walkPos ω k := by
  unfold walkPos
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) < k
  · have : j ≠ i := fun h => by rw [h] at hj; omega
    simp [aceFlip, this]
  · simp [hj]

theorem aceHold_aceFlip {n : ℕ} (i : Fin n) (ω : Fin n → Bool) :
    aceHold (aceFlip i ω) i = aceHold ω i :=
  aceHoldW_congr fun _ hk => walkPos_aceFlip i ω hk

theorem ace_day_sum_zero {n : ℕ} (i : Fin n) :
    ∑ ω : Fin n → Bool, (if aceHold ω i then step (ω i) else 0) = 0 := by
  set S := ∑ ω : Fin n → Bool, (if aceHold ω i then step (ω i) else 0) with hS
  have h1 : S = ∑ ω : Fin n → Bool, (if aceHold (aceFlip i ω) i then step (aceFlip i ω i) else 0) :=
    (Equiv.sum_comp (aceFlip_involutive i).toPerm
      (fun ω : Fin n → Bool => if aceHold ω i then step (ω i) else 0)).symm
  have h2 : ∀ ω : Fin n → Bool, (if aceHold (aceFlip i ω) i then step (aceFlip i ω i) else 0) =
      -(if aceHold ω i then step (ω i) else 0) := by
    intro ω
    rw [aceHold_aceFlip]
    have : aceFlip i ω i = !ω i := by simp [aceFlip]
    rw [this, step_not]
    split_ifs <;> simp
  rw [sum_congr rfl fun ω _ => h2 ω, sum_neg_distrib] at h1
  omega

/-- Grinstead–Snell Example 6.16 (PR-208), expected winnings.  On the fair `±1` walk (uniform measure on
`Fin n → Bool`) Mr. Ace's winnings (the sum over days of the holding indicator, which depends only on earlier
moves, times the move) have expectation exactly `0`, for every number `n` of days. -/
@[kb "grinsteadsnell2006" "Example 6.16, p. 249"]
theorem ace_expected_winnings (n : ℕ) : (∑ ω : Fin n → Bool, (aceWin ω : ℚ)) / 2 ^ n = 0 := by
  have h : ∑ ω : Fin n → Bool, aceWin ω = 0 := by
    unfold aceWin
    rw [sum_comm]
    exact sum_eq_zero fun i _ => ace_day_sum_zero i
  have h' : (∑ ω : Fin n → Bool, (aceWin ω : ℚ)) = 0 := by exact_mod_cast h
  rw [h', zero_div]

/-! ### The exact distribution after 20 days by a dynamic program -/

theorem walkPos_init {n : ℕ} (ω : Fin (n + 1) → Bool) {k : ℕ} (hk : k ≤ n) :
    walkPos ω k = walkPos (Fin.init ω) k := by
  unfold walkPos
  rw [Fin.sum_univ_castSucc]
  have : ¬ n < k := by omega
  simp [Fin.init, this]

theorem walkPos_last {n : ℕ} (ω : Fin (n + 1) → Bool) :
    walkPos ω (n + 1) = walkPos (Fin.init ω) n + step (ω (Fin.last n)) := by
  unfold walkPos
  rw [Fin.sum_univ_castSucc]
  simp [Fin.init]

theorem aceHold_init {n : ℕ} (ω : Fin (n + 1) → Bool) {i : ℕ} (hi : i ≤ n) :
    aceHold ω i = aceHold (Fin.init ω) i :=
  aceHoldW_congr fun _ hk => walkPos_init ω (le_trans hk hi)

theorem aceWin_succ {n : ℕ} (ω : Fin (n + 1) → Bool) :
    aceWin ω = aceWin (Fin.init ω) + (if aceHold ω n then step (ω (Fin.last n)) else 0) := by
  unfold aceWin
  rw [Fin.sum_univ_castSucc]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have : aceHold ω i = aceHold (Fin.init ω) i := aceHold_init ω (by have := i.isLt; omega)
  simp [this, Fin.init]

/-- State of the system: (position, holding, winnings). -/
abbrev AceState := ℤ × Bool × ℤ

/-- One day's transition of the state under the move `b`. -/
def aceStep (s : AceState) (b : Bool) : AceState :=
  (s.1 + step b, if s.1 + step b = 1 then false else if s.1 + step b = 0 then true else s.2.1,
    s.2.2 + if s.2.1 then step b else 0)

/-- The state after the path `ω` of `n` days, computed by the transition. -/
def aceState : (n : ℕ) → (Fin n → Bool) → AceState
  | 0, _ => (0, true, 0)
  | n + 1, ω => aceStep (aceState n (Fin.init ω)) (ω (Fin.last n))

theorem aceState_eq (n : ℕ) : ∀ ω : Fin n → Bool, aceState n ω = (walkPos ω n, aceHold ω n, aceWin ω) := by
  induction n with
  | zero => intro ω; simp [aceState, walkPos_zero, aceHold, aceHoldW, aceWin]
  | succ n ih =>
    intro ω
    rw [aceState, ih, aceStep, aceWin_succ, walkPos_last, aceHold_init ω le_rfl]
    have : aceHold ω (n + 1) = if walkPos ω (n + 1) = 1 then false else
        if walkPos ω (n + 1) = 0 then true else aceHold ω n := by
      simp [aceHold, aceHoldW]
    rw [this, walkPos_last, aceHold_init ω le_rfl]

/-- Insert `c` into the association list at key `k`, adding to an existing entry. -/
def dpAdd (k : AceState) (c : ℕ) : List (AceState × ℕ) → List (AceState × ℕ)
  | [] => [(k, c)]
  | (k', c') :: l => if k' = k then (k', c' + c) :: l else (k', c') :: dpAdd k c l

/-- One day of the dynamic program on the table of (state, number of paths) pairs. -/
def dpStep (l : List (AceState × ℕ)) : List (AceState × ℕ) :=
  l.foldr (fun e acc => dpAdd (aceStep e.1 true) e.2 (dpAdd (aceStep e.1 false) e.2 acc)) []

/-- The table after `n` days. -/
def dpRun : ℕ → List (AceState × ℕ)
  | 0 => [((0, true, 0), 1)]
  | n + 1 => dpStep (dpRun n)

/-- `∑_entries count * h(state)`. -/
def dpSum (h : AceState → ℕ) (l : List (AceState × ℕ)) : ℕ := (l.map fun e => e.2 * h e.1).sum

theorem dpSum_add (h : AceState → ℕ) (k : AceState) (c : ℕ) (l : List (AceState × ℕ)) :
    dpSum h (dpAdd k c l) = dpSum h l + c * h k := by
  induction l with
  | nil => simp [dpAdd, dpSum]
  | cons e l ih =>
    obtain ⟨k', c'⟩ := e
    by_cases hk : k' = k
    · subst hk; simp [dpAdd, dpSum]; ring
    · simp only [dpAdd, hk, ↓reduceIte, dpSum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; ring

theorem dpSum_step (h : AceState → ℕ) (l : List (AceState × ℕ)) :
    dpSum h (dpStep l) = dpSum (fun s => h (aceStep s true)) l + dpSum (fun s => h (aceStep s false)) l := by
  induction l with
  | nil => simp [dpStep, dpSum]
  | cons e l ih =>
    simp only [dpStep, List.foldr_cons] at ih ⊢
    rw [dpSum_add, dpSum_add, ih]
    simp only [dpSum, List.map_cons, List.sum_cons]
    ring

theorem sum_aceState (h : AceState → ℕ) (n : ℕ) :
    ∑ ω : Fin n → Bool, h (aceState n ω) = dpSum h (dpRun n) := by
  induction n generalizing h with
  | zero => simp [aceState, dpRun, dpSum]
  | succ n ih =>
    rw [dpRun, dpSum_step, ← ih, ← ih]
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [aceState, Fin.snocEquiv_apply]

/-- Number of paths of 20 days after which Mr. Ace is ahead, from the dynamic program. -/
theorem ace_dp_20 : dpSum (fun s => if 0 < s.2.2 then 1 else 0) (dpRun 20) = 639771 := by
  decide +kernel

/-- Grinstead–Snell Example 6.16 (PR-208), ahead after 20 days.  Exactly `639771` of the `2^20` equally likely
20-day paths leave Mr. Ace with positive winnings, so he is ahead with probability `639771/2^20 = .61013…`,
the book's "about .610"; yet the expectation is `0` (`ace_expected_winnings`). The count is obtained by a
dynamic program over (price offset, holding, winnings) proved equal to the path count. -/
@[kb "grinsteadsnell2006" "Example 6.16, p. 249"]
theorem ace_ahead_after_20_days :
    (univ.filter fun ω : Fin 20 → Bool => 0 < aceWin ω).card = 639771 ∧
    ((univ.filter fun ω : Fin 20 → Bool => 0 < aceWin ω).card : ℚ) / 2 ^ 20 = 639771 / 2 ^ 20 ∧
    (0.6101 : ℚ) < 639771 / 2 ^ 20 ∧ (639771 : ℚ) / 2 ^ 20 < 0.6102 := by
  have h : (univ.filter fun ω : Fin 20 → Bool => 0 < aceWin ω).card = 639771 := by
    rw [← ace_dp_20, ← sum_aceState, card_filter]
    refine sum_congr rfl fun ω _ => ?_
    rw [aceState_eq]
  refine ⟨h, by rw [h]; norm_num, by norm_num, by norm_num⟩

end UndergradKB.Probability
