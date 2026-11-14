import Mathlib.Probability.Independence.Basic
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueStart

/-! # Probability: arrivals see the equilibrium of the queue (Grinstead–Snell Example 6.29)

Wave 8, a recorded loose end (4).  The book's computation of the time in the system (Example 6.29) assumes that
a customer arriving at the queue in equilibrium finds a geometric number `(1-ρ)ρ^j` of customers ahead.  In the
uniformized description of the queue the rings of the clock are arrivals or service rings according to
independent coins: from `i` the queue goes to `i + 1` on an arrival ring (probability `α = λ/(λ+μ)`) and to
`i - 1` (or stays at `0`) on a service ring.  Here the chain is driven by independent variables
`Z 0` (the initial length) and `Z (n+1)` (the coin of ring `n`, value `1` for an arrival):

* `coinChain_indepFun`: the queue length before ring `n` is independent of the coin of ring `n`;
* `coinChain_law_step`: the laws of `coinChain` are those of the jump chain `queueJump`;
* `queue_arrivals_see_equilibrium`: in equilibrium (geometric initial law) the number found by the customer
  arriving at ring `n` is geometric, for every `n`;
* `queue_arrivals_see_equilibrium_limit`: from `j` customers, the law of the number found tends to it. -/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UndergradKB.Probability

/-- One step of the queue's jump chain driven by a coin `c` (`c = 1`: arrival ring). -/
def queueStep (i c : ℕ) : ℕ := if c = 1 then i + 1 else i - 1

/-- The jump chain driven by `z`: `z 0` is the initial length, `z (n+1)` the coin of ring `n`. -/
def coinChainSeq (z : ℕ → ℕ) : ℕ → ℕ
  | 0 => z 0
  | n + 1 => queueStep (coinChainSeq z n) (z (n + 1))

theorem coinChainSeq_congr {z z' : ℕ → ℕ} (n : ℕ) (h : ∀ i ≤ n, z i = z' i) :
    coinChainSeq z n = coinChainSeq z' n := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    show queueStep (coinChainSeq z n) (z (n + 1)) = queueStep (coinChainSeq z' n) (z' (n + 1))
    rw [ih fun i hi => h i (by omega), h (n + 1) le_rfl]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The queue length before ring `n` of the chain driven by `Z`. -/
def coinChain (Z : ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) : ℕ := coinChainSeq (fun i => Z i ω) n

theorem measurable_coinChain {Z : ℕ → Ω → ℕ} (hZ : ∀ i, Measurable (Z i)) (n : ℕ) :
    Measurable (coinChain Z n) := by
  induction n with
  | zero => exact hZ 0
  | succ n ih =>
    have h : coinChain Z (n + 1) = fun ω => queueStep (coinChain Z n ω) (Z (n + 1) ω) := rfl
    rw [h]
    exact (measurable_of_countable (Function.uncurry queueStep)).comp (ih.prodMk (hZ (n + 1)))

/-- The queue length before ring `n` is independent of the coin of ring `n`. -/
theorem coinChain_indepFun {Z : ℕ → Ω → ℕ} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P) (n : ℕ) :
    IndepFun (coinChain Z n) (Z (n + 1)) P := by
  have h := hind.indepFun_finset (Finset.range (n + 1)) {n + 1} (by simp) hZ
  set φ : (Finset.range (n + 1) → ℕ) → ℕ := fun v =>
    coinChainSeq (fun i => if hi : i ∈ Finset.range (n + 1) then v ⟨i, hi⟩ else 0) n with hφ
  set ψ : (({n + 1} : Finset ℕ) → ℕ) → ℕ := fun w => w ⟨n + 1, by simp⟩ with hψ
  have hφm : Measurable φ := measurable_of_countable φ
  have hψm : Measurable ψ := measurable_pi_apply _
  have h2 := h.comp hφm hψm
  have e1 : φ ∘ (fun ω (i : Finset.range (n + 1)) => Z i ω) = coinChain Z n := by
    funext ω
    simp only [Function.comp, hφ, coinChain]
    exact coinChainSeq_congr n fun i hi => by
      rw [dite_eq_left (Finset.mem_range.2 (by omega))]
  have e2 : ψ ∘ (fun ω (i : ({n + 1} : Finset ℕ)) => Z i ω) = Z (n + 1) := rfl
  rwa [e1, e2] at h2

/-- The number found by the customer arriving at ring `n` has the law of the queue length before ring `n`:
`P(X_n = k and ring n is an arrival) = P(X_n = k) P(ring n is an arrival)`. -/
theorem coinChain_arrival {Z : ℕ → Ω → ℕ} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P) (n : ℕ)
    (s : Set ℕ) (c : Set ℕ) :
    P.real {ω | coinChain Z n ω ∈ s ∧ Z (n + 1) ω ∈ c} =
      P.real {ω | coinChain Z n ω ∈ s} * P.real {ω | Z (n + 1) ω ∈ c} := by
  have h := (coinChain_indepFun hZ hind n).measure_inter_preimage_eq_mul s c (MeasurableSet.of_discrete)
    (MeasurableSet.of_discrete)
  simp only [Measure.real]
  rw [← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal h

variable [IsProbabilityMeasure P]

/-- The laws of the coin-driven chain are those of the jump chain `queueJump` of the queue:
`P(X_{n+1} = k) = ∑_i P(X_n = i) P(i, k)`, when the coin of every ring is an arrival with probability
`λ/(λ+μ)`. -/
theorem coinChain_law_step {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) {Z : ℕ → Ω → ℕ}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hC : ∀ n, P.real {ω | Z (n + 1) ω = 1} = lam / (lam + mu)) (n k : ℕ) :
    HasSum (fun i => P.real {ω | coinChain Z n ω = i} * queueJump lam mu i k)
      (P.real {ω | coinChain Z (n + 1) ω = k}) := by
  have hab := queue_alpha_beta hl hm
  have hC' : P.real {ω | Z (n + 1) ω ∈ ({1} : Set ℕ)ᶜ} = mu / (lam + mu) := by
    have e : {ω | Z (n + 1) ω ∈ ({1} : Set ℕ)ᶜ} = {ω | Z (n + 1) ω = 1}ᶜ := by ext; simp
    rw [e, probReal_compl_eq_one_sub (measurableSet_eq_fun (hZ (n + 1)) measurable_const), hC n]
    linarith
  have hup : P.real {ω | Z (n + 1) ω ∈ ({1} : Set ℕ)} = lam / (lam + mu) := by simpa using hC n
  have hY := measurable_coinChain hZ n
  -- split according to the coin of ring `n`
  have hsplit : ∀ s t : Set ℕ, (∀ ω, coinChain Z (n + 1) ω = k ↔
      (Z (n + 1) ω = 1 ∧ coinChain Z n ω ∈ s) ∨ (Z (n + 1) ω ≠ 1 ∧ coinChain Z n ω ∈ t)) →
      P.real {ω | coinChain Z (n + 1) ω = k} =
        P.real {ω | coinChain Z n ω ∈ s} * (lam / (lam + mu)) +
        P.real {ω | coinChain Z n ω ∈ t} * (mu / (lam + mu)) := by
    intro s t hst
    have e : {ω | coinChain Z (n + 1) ω = k} =
        {ω | coinChain Z n ω ∈ s ∧ Z (n + 1) ω ∈ ({1} : Set ℕ)} ∪
          {ω | coinChain Z n ω ∈ t ∧ Z (n + 1) ω ∈ ({1} : Set ℕ)ᶜ} := by
      ext ω; rw [mem_ofPred_eq, hst ω]; simp [and_comm]
    have hd : Disjoint {ω | coinChain Z n ω ∈ s ∧ Z (n + 1) ω ∈ ({1} : Set ℕ)}
        {ω | coinChain Z n ω ∈ t ∧ Z (n + 1) ω ∈ ({1} : Set ℕ)ᶜ} :=
      Set.disjoint_left.2 fun ω h1 h2 => h2.2 h1.2
    have hm2 : MeasurableSet {ω | coinChain Z n ω ∈ t ∧ Z (n + 1) ω ∈ ({1} : Set ℕ)ᶜ} :=
      (hY (MeasurableSet.of_discrete (s := t))).inter
        (hZ (n + 1) (MeasurableSet.of_discrete (s := ({1} : Set ℕ)ᶜ)))
    rw [e, measureReal_union (μ := P) hd hm2,
      coinChain_arrival hZ hind, coinChain_arrival hZ hind, hup, hC']
  rcases k with _ | k
  · have h := hsplit ∅ {0, 1} fun ω => by
      show queueStep _ _ = 0 ↔ _
      by_cases hc : Z (n + 1) ω = 1
      · simp [queueStep, hc, coinChain]
      · simp only [queueStep, coinChain, hc, ite_false, false_and, false_or, ne_eq, not_false_eq_true, true_and,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor <;> intro h <;> omega
    rw [h]
    convert queueJump_col_zero lam mu (fun i => P.real {ω | coinChain Z n ω = i}) using 1
    have e : {ω | coinChain Z n ω ∈ ({0, 1} : Set ℕ)} =
        {ω | coinChain Z n ω = 0} ∪ {ω | coinChain Z n ω = 1} := by ext; simp
    have hd : Disjoint {ω | coinChain Z n ω = 0} {ω | coinChain Z n ω = 1} :=
      Set.disjoint_left.2 fun ω (h1 : coinChain Z n ω = 0) (h2 : coinChain Z n ω = 1) => by omega
    rw [e, measureReal_union (μ := P) hd (hY (MeasurableSet.of_discrete (s := ({1} : Set ℕ))))]
    simp
  · have h := hsplit {k} {k + 2} fun ω => by
      show queueStep _ _ = k + 1 ↔ _
      by_cases hc : Z (n + 1) ω = 1
      · simp [queueStep, hc, coinChain]
      · simp only [queueStep, coinChain, hc, ite_false, false_and, false_or, ne_eq, not_false_eq_true, true_and,
          Set.mem_singleton_iff]
        constructor <;> intro h <;> omega
    rw [h]
    convert queueJump_col_succ lam mu (fun i => P.real {ω | coinChain Z n ω = i}) k using 1
    simp

/-- Grinstead–Snell Example 6.29 (PR-209), arrivals see the equilibrium.  Let `λ > 0` and `μ > λ`,
`ρ = λ/μ`.  Drive the jump chain of the queue by independent variables `Z 0` (the initial queue length, with the
geometric law `(1-ρ)ρ^k`) and `Z (n+1)` (the coin of ring `n`: an arrival, value `1`, with probability
`λ/(λ+μ)`).  Then for every ring `n` and every `k`, the conditional probability that the customer arriving at
ring `n` finds `k` customers in the queue is `(1-ρ)ρ^k`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_arrivals_see_equilibrium {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) {Z : ℕ → Ω → ℕ}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hC : ∀ n, P.real {ω | Z (n + 1) ω = 1} = lam / (lam + mu))
    (h0 : ∀ k, P.real {ω | Z 0 ω = k} = queueGeom (lam / mu) k) (n k : ℕ) :
    P.real {ω | coinChain Z n ω = k ∧ Z (n + 1) ω = 1} / P.real {ω | Z (n + 1) ω = 1} =
      queueGeom (lam / mu) k := by
  have hm : 0 < mu := hl.trans hlm
  have hg := queue_geometric_equilibrium hl hlm
  have hstat := (queue_jump_stationary_iff hl hm (queueGeom (lam / mu)) hg.1 hg.2.1).2 ⟨hlm, rfl⟩
  have hlaw : ∀ n k, P.real {ω | coinChain Z n ω = k} = queueGeom (lam / mu) k := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      intro k
      have h := coinChain_law_step hl hm hZ hind hC n k
      simp_rw [ih] at h
      exact h.unique (hstat k)
  have h := coinChain_arrival hZ hind n {k} {1}
  simp only [mem_singleton_iff] at h
  rw [h, hlaw, hC]
  have : 0 < lam / (lam + mu) := by positivity
  field_simp

/-- Grinstead–Snell Example 6.29 (PR-209), arrivals see the equilibrium in the limit.  As in
`queue_arrivals_see_equilibrium`, but the queue starts with `j` customers (`Z 0 = j` almost surely): the
conditional probability that the customer arriving at ring `n` finds `k` customers tends to `(1-ρ)ρ^k` as
`n → ∞`. -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem queue_arrivals_see_equilibrium_limit {lam mu : ℝ} (hl : 0 < lam) (hlm : lam < mu) {Z : ℕ → Ω → ℕ}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hC : ∀ n, P.real {ω | Z (n + 1) ω = 1} = lam / (lam + mu)) {j : ℕ}
    (h0 : P.real {ω | Z 0 ω = j} = 1) (k : ℕ) :
    Tendsto (fun n => P.real {ω | coinChain Z n ω = k ∧ Z (n + 1) ω = 1} / P.real {ω | Z (n + 1) ω = 1})
      atTop (𝓝 (queueGeom (lam / mu) k)) := by
  have hm : 0 < mu := hl.trans hlm
  have hinit : ∀ k, P.real {ω | Z 0 ω = k} = if k = j then 1 else 0 := by
    intro k
    split_ifs with hk
    · rw [hk, h0]
    · have hsub : {ω | Z 0 ω = k} ⊆ {ω | Z 0 ω = j}ᶜ := fun ω hω h => hk (hω.symm.trans h)
      have := measureReal_mono (μ := P) hsub
      rw [probReal_compl_eq_one_sub (measurableSet_eq_fun (hZ 0) measurable_const), h0, sub_self] at this
      exact le_antisymm this measureReal_nonneg
  have hlaw : ∀ n k, P.real {ω | coinChain Z n ω = k} = queueLawFrom lam mu j n k := by
    intro n
    induction n with
    | zero => intro k; rw [(queueLawFrom_step hl hm j 0).1 k]; exact hinit k
    | succ n ih =>
      intro k
      have h := coinChain_law_step hl hm hZ hind hC n k
      simp_rw [ih] at h
      exact h.unique ((queueLawFrom_step hl hm j n).2 k)
  have e : ∀ n, P.real {ω | coinChain Z n ω = k ∧ Z (n + 1) ω = 1} / P.real {ω | Z (n + 1) ω = 1} =
      queueLawFrom lam mu j n k := by
    intro n
    have h := coinChain_arrival hZ hind n {k} {1}
    simp only [mem_singleton_iff] at h
    rw [h, hlaw, hC]
    have : 0 < lam / (lam + mu) := by positivity
    field_simp
  simp_rw [e]
  exact queue_law_from_tendsto_geometric hl hlm j k

end UndergradKB.Probability
