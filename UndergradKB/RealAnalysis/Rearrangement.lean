import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

/-!
# Rearranging the alternating harmonic series to any sum (Lebl, Example 2.6.4)

For every real `L` there is a bijection `σ : ℕ → ℕ` such that the rearranged alternating harmonic series
`∑ (-1)^{σ n} / (σ n + 1)` converges to `L` (Riemann's rearrangement theorem for this series). Neither Mathlib (whose
`HasSum` is unconditional) nor ReasBook (which has only the identity rearrangement) states it.

The proof is the book's greedy algorithm, done for two sequences `u, v > 0` tending to `0` whose sums diverge (the
positive terms `u p = 1/(2p+1)` and the absolute values `v q = 1/(2q+2)` of the negative terms): while the running
sum is `≤ L` add the next unused `u`, otherwise subtract the next unused `v`. Both kinds are used infinitely often
(the sums diverge), so every index is used exactly once; once the unused terms are below `ε` and the running sum has
crossed `L`, it stays within `ε` of `L`.
-/

open Filter Topology Finset

namespace UndergradKB.RealAnalysis

namespace Rearrangement

variable (u v : ℕ → ℝ) (L : ℝ)

/-- The greedy state after `n` steps: (number of `u` terms used, number of `v` terms used, running sum). -/
noncomputable def state : ℕ → ℕ × ℕ × ℝ
  | 0 => (0, 0, 0)
  | n + 1 =>
    if (state n).2.2 ≤ L then ((state n).1 + 1, (state n).2.1, (state n).2.2 + u (state n).1)
    else ((state n).1, (state n).2.1 + 1, (state n).2.2 - v (state n).2.1)

/-- Number of `u` terms used in the first `n` steps. -/
noncomputable def P (n : ℕ) : ℕ := (state u v L n).1
/-- Number of `v` terms used in the first `n` steps. -/
noncomputable def Q (n : ℕ) : ℕ := (state u v L n).2.1
/-- The running sum after `n` steps. -/
noncomputable def S (n : ℕ) : ℝ := (state u v L n).2.2

/-- The term added at step `n`. -/
noncomputable def term (n : ℕ) : ℝ := if S u v L n ≤ L then u (P u v L n) else -v (Q u v L n)

/-- The index (in the alternating enumeration: `u p` at `2p`, `-v q` at `2q+1`) of the term added at step `n`. -/
noncomputable def σ (n : ℕ) : ℕ := if S u v L n ≤ L then 2 * P u v L n else 2 * Q u v L n + 1

variable {u v L}

lemma P_zero : P u v L 0 = 0 := rfl
lemma Q_zero : Q u v L 0 = 0 := rfl
lemma S_zero : S u v L 0 = 0 := rfl

lemma succ_of_le {n : ℕ} (h : S u v L n ≤ L) :
    P u v L (n + 1) = P u v L n + 1 ∧ Q u v L (n + 1) = Q u v L n ∧
      S u v L (n + 1) = S u v L n + u (P u v L n) := by
  simp only [S] at h
  simp [P, Q, S, state, h]

lemma succ_of_lt {n : ℕ} (h : L < S u v L n) :
    P u v L (n + 1) = P u v L n ∧ Q u v L (n + 1) = Q u v L n + 1 ∧
      S u v L (n + 1) = S u v L n - v (Q u v L n) := by
  simp only [S] at h
  simp [P, Q, S, state, not_le.2 h]

lemma S_succ (n : ℕ) : S u v L (n + 1) = S u v L n + term u v L n := by
  by_cases h : S u v L n ≤ L
  · rw [(succ_of_le h).2.2]; simp only [term, h, ↓reduceIte]
  · rw [(succ_of_lt (not_le.1 h)).2.2]; simp only [term, h, ↓reduceIte, sub_eq_add_neg]

lemma S_eq_sum (n : ℕ) : S u v L n = ∑ k ∈ range n, term u v L k := by
  induction n with
  | zero => simp [S_zero]
  | succ n ih => rw [S_succ, ih, sum_range_succ]

lemma P_succ_le (n : ℕ) : P u v L (n + 1) ≤ P u v L n + 1 := by
  by_cases h : S u v L n ≤ L
  · rw [(succ_of_le h).1]
  · rw [(succ_of_lt (not_le.1 h)).1]; omega

lemma Q_succ_le (n : ℕ) : Q u v L (n + 1) ≤ Q u v L n + 1 := by
  by_cases h : S u v L n ≤ L
  · rw [(succ_of_le h).2.1]; omega
  · rw [(succ_of_lt (not_le.1 h)).2.1]

lemma P_mono : Monotone (P u v L) := by
  refine monotone_nat_of_le_succ fun n => ?_
  by_cases h : S u v L n ≤ L
  · rw [(succ_of_le h).1]; omega
  · rw [(succ_of_lt (not_le.1 h)).1]

lemma Q_mono : Monotone (Q u v L) := by
  refine monotone_nat_of_le_succ fun n => ?_
  by_cases h : S u v L n ≤ L
  · rw [(succ_of_le h).2.1]
  · rw [(succ_of_lt (not_le.1 h)).2.1]; omega

lemma σ_ne_of_lt {k m : ℕ} (hkm : k < m) : σ u v L k ≠ σ u v L m := by
  have hP : S u v L k ≤ L → P u v L k < P u v L m := fun hk =>
    lt_of_lt_of_le (by rw [(succ_of_le hk).1]; omega) (P_mono (Nat.succ_le_of_lt hkm))
  have hQ : L < S u v L k → Q u v L k < Q u v L m := fun hk =>
    lt_of_lt_of_le (by rw [(succ_of_lt hk).2.1]; omega) (Q_mono (Nat.succ_le_of_lt hkm))
  unfold σ
  split_ifs with hk hm hm
  · have := hP hk; omega
  · omega
  · omega
  · have := hQ (not_le.1 hk); omega

lemma σ_injective : Function.Injective (σ u v L) := by
  intro k m h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkm | hkm
  · exact σ_ne_of_lt hkm h
  · exact σ_ne_of_lt hkm h.symm

/-! ### Both kinds of terms are used infinitely often -/

variable (hu : ∀ n, 0 < u n) (hv : ∀ n, 0 < v n)
  (hU : Tendsto (fun m => ∑ j ∈ range m, u j) atTop atTop)
  (hV : Tendsto (fun m => ∑ j ∈ range m, v j) atTop atTop)
include hV in
/-- The running sum does not stay above `L` forever. -/
lemma exists_le_after (n₀ : ℕ) : ∃ n ≥ n₀, S u v L n ≤ L := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k, Q u v L (n₀ + k) = Q u v L n₀ + k ∧
      S u v L (n₀ + k) = S u v L n₀ + ∑ j ∈ range (Q u v L n₀), v j - ∑ j ∈ range (Q u v L n₀ + k), v j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := succ_of_lt (hcon (n₀ + k) (by omega))
      rw [← add_assoc, h.2.1, h.2.2, ih.1, ih.2, ← add_assoc, sum_range_succ]
      exact ⟨rfl, by ring⟩
  obtain ⟨M, hM⟩ := (tendsto_atTop.1 hV) (S u v L n₀ + ∑ j ∈ range (Q u v L n₀), v j - L + 1) |>.exists_forall_of_atTop
  have h1 := hM (Q u v L n₀ + M) (by omega)
  have h2 := hcon (n₀ + M) (by omega)
  rw [(key M).2] at h2
  linarith

include hU in
/-- The running sum does not stay at or below `L` forever. -/
lemma exists_gt_after (n₀ : ℕ) : ∃ n ≥ n₀, L < S u v L n := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k, P u v L (n₀ + k) = P u v L n₀ + k ∧
      S u v L (n₀ + k) = S u v L n₀ - ∑ j ∈ range (P u v L n₀), u j + ∑ j ∈ range (P u v L n₀ + k), u j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := succ_of_le (hcon (n₀ + k) (by omega))
      rw [← add_assoc, h.1, h.2.2, ih.1, ih.2, ← add_assoc, sum_range_succ]
      exact ⟨rfl, by ring⟩
  obtain ⟨M, hM⟩ := (tendsto_atTop.1 hU) (L - S u v L n₀ + ∑ j ∈ range (P u v L n₀), u j + 1)
    |>.exists_forall_of_atTop
  have h1 := hM (P u v L n₀ + M) (by omega)
  have h2 := hcon (n₀ + M) (by omega)
  rw [(key M).2] at h2
  linarith

include hV in
lemma P_unbounded (B : ℕ) : ∃ n, B ≤ P u v L n := by
  induction B with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ B ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hmL⟩ := exists_le_after hV n
    exact ⟨m + 1, by rw [(succ_of_le hmL).1]; have := P_mono (u := u) (v := v) (L := L) hm; omega⟩

include hU in
lemma Q_unbounded (B : ℕ) : ∃ n, B ≤ Q u v L n := by
  induction B with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ B ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, hmL⟩ := exists_gt_after hU n
    exact ⟨m + 1, by rw [(succ_of_lt hmL).2.1]; have := Q_mono (u := u) (v := v) (L := L) hm; omega⟩

include hU hV in
lemma σ_surjective : Function.Surjective (σ u v L) := by
  classical
  intro t
  rcases Nat.even_or_odd' t with ⟨p, rfl | rfl⟩
  · -- the step at which the `p`-th `u` term is used
    have hex : ∃ n, p + 1 ≤ P u v L n := P_unbounded hV (p + 1)
    have hnP : p + 1 ≤ P u v L (Nat.find hex) := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by intro h; rw [h, P_zero] at hnP; omega
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hm] at hnP
    have hmP : ¬ p + 1 ≤ P u v L m := Nat.find_min hex (by omega)
    have hle := P_succ_le (u := u) (v := v) (L := L) m
    have hS : S u v L m ≤ L := by
      by_contra h
      rw [(succ_of_lt (not_le.1 h)).1] at hnP
      exact hmP hnP
    refine ⟨m, ?_⟩
    simp only [σ, hS, ↓reduceIte]
    omega
  · have hex : ∃ n, p + 1 ≤ Q u v L n := Q_unbounded hU (p + 1)
    have hnQ : p + 1 ≤ Q u v L (Nat.find hex) := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by intro h; rw [h, Q_zero] at hnQ; omega
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hm] at hnQ
    have hmQ : ¬ p + 1 ≤ Q u v L m := Nat.find_min hex (by omega)
    have hle := Q_succ_le (u := u) (v := v) (L := L) m
    have hS : L < S u v L m := by
      by_contra h
      rw [(succ_of_le (not_lt.1 h)).2.1] at hnQ
      exact hmQ hnQ
    refine ⟨m, ?_⟩
    simp only [σ, not_le.2 hS, ↓reduceIte]
    omega

include hu hv hU hV in
/-- The greedy running sums converge to `L`. -/
lemma tendsto_S (hu0 : Tendsto u atTop (𝓝 0)) (hv0 : Tendsto v atTop (𝓝 0)) :
    Tendsto (S u v L) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_atTop.1 hu0) ε hε
  obtain ⟨K₂, hK₂⟩ := (Metric.tendsto_atTop.1 hv0) ε hε
  have huε : ∀ j ≥ max K₁ K₂, u j < ε := fun j hj => by
    have := hK₁ j (le_of_max_le_left hj); rw [Real.dist_eq, sub_zero, abs_of_pos (hu j)] at this; exact this
  have hvε : ∀ j ≥ max K₁ K₂, v j < ε := fun j hj => by
    have := hK₂ j (le_of_max_le_right hj); rw [Real.dist_eq, sub_zero, abs_of_pos (hv j)] at this; exact this
  obtain ⟨n₁, hn₁⟩ := P_unbounded (u := u) (v := v) (L := L) hV (max K₁ K₂)
  obtain ⟨n₂, hn₂⟩ := Q_unbounded (u := u) (v := v) (L := L) hU (max K₁ K₂)
  set n₀ := max n₁ n₂
  have hPK : ∀ n ≥ n₀, max K₁ K₂ ≤ P u v L n := fun n hn => hn₁.trans (P_mono (le_of_max_le_left hn))
  have hQK : ∀ n ≥ n₀, max K₁ K₂ ≤ Q u v L n := fun n hn => hn₂.trans (Q_mono (le_of_max_le_right hn))
  -- a crossing of `L` after `n₀`
  obtain ⟨m, hm, hmL⟩ := exists_le_after (u := u) (v := v) (L := L) hV n₀
  have hex : ∃ k, L < S u v L (m + k) := by
    obtain ⟨m', hm', h⟩ := exists_gt_after (u := u) (v := v) (L := L) hU m
    exact ⟨m' - m, by rwa [Nat.add_sub_cancel' hm']⟩
  classical
  set k := Nat.find hex
  have hk : L < S u v L (m + k) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by intro h; rw [h, add_zero] at hk; linarith
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  have hprev : S u v L (m + k') ≤ L := not_lt.1 (Nat.find_min hex (by omega))
  have hstart : |S u v L (m + k) - L| < ε := by
    rw [hk', ← add_assoc, (succ_of_le hprev).2.2] at hk ⊢
    have := huε (P u v L (m + k')) (hPK (m + k') (by omega))
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hu (P u v L (m + k'))]
  refine ⟨m + k, fun n hn => ?_⟩
  rw [Real.dist_eq]
  induction n, hn using Nat.le_induction with
  | base => exact hstart
  | succ n hn ih =>
    rw [abs_sub_lt_iff] at ih ⊢
    by_cases h : S u v L n ≤ L
    · rw [(succ_of_le h).2.2]
      have := huε (P u v L n) (hPK n (by omega))
      constructor <;> linarith [hu (P u v L n)]
    · rw [(succ_of_lt (not_le.1 h)).2.2]
      have := hvε (Q u v L n) (hQK n (by omega))
      constructor <;> linarith [hv (Q u v L n), not_le.1 h]

end Rearrangement

open Rearrangement in
/-- **Rearranging the alternating harmonic series to any sum.** For every real `L` there is a bijection
`σ : ℕ → ℕ` such that `∑_{n} (-1)^{σ n} / (σ n + 1)` (partial sums in the order `σ 0, σ 1, …`) converges to `L`. -/
@[kb "lebl2026" "Example 2.6.4, p. 103"]
theorem alternating_harmonic_rearrangement (L : ℝ) :
    ∃ σ : ℕ → ℕ, Function.Bijective σ ∧
      Tendsto (fun N => ∑ n ∈ range N, (-1 : ℝ) ^ σ n / ((σ n : ℝ) + 1)) atTop (𝓝 L) := by
  set u : ℕ → ℝ := fun p => 1 / (2 * (p : ℝ) + 1)
  set v : ℕ → ℝ := fun q => 1 / (2 * (q : ℝ) + 2)
  have hu : ∀ n, 0 < u n := fun n => by simp only [u]; positivity
  have hv : ∀ n, 0 < v n := fun n => by simp only [v]; positivity
  have hH := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hV : Tendsto (fun m => ∑ j ∈ range m, v j) atTop atTop := by
    have : (fun m => ∑ j ∈ range m, v j) = fun m => (1 / 2 : ℝ) * ∑ j ∈ range m, 1 / ((j : ℝ) + 1) := by
      funext m
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      simp only [v]
      field_simp
    rw [this]
    exact hH.const_mul_atTop (by norm_num)
  have hU : Tendsto (fun m => ∑ j ∈ range m, u j) atTop atTop := by
    refine tendsto_atTop_mono (fun m => sum_le_sum fun j _ => ?_) hV
    simp only [u, v]
    gcongr
    linarith
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hu0 : Tendsto u atTop (𝓝 0) :=
    squeeze_zero (fun n => (hu n).le) (fun n => by
      simp only [u]; gcongr; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) hlim
  have hv0 : Tendsto v atTop (𝓝 0) :=
    squeeze_zero (fun n => (hv n).le) (fun n => by
      simp only [v]; exact one_div_le_one_div_of_le (by positivity) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])) hlim
  refine ⟨σ u v L, ⟨σ_injective, σ_surjective hU hV⟩, ?_⟩
  have hterm : ∀ n, (-1 : ℝ) ^ σ u v L n / ((σ u v L n : ℝ) + 1) = term u v L n := by
    intro n
    unfold σ term
    split_ifs with h
    · simp only [u, pow_mul, neg_one_sq, one_pow]
      push_cast
      ring
    · simp only [v, pow_succ, pow_mul]
      push_cast
      ring
  simp_rw [hterm, ← S_eq_sum]
  exact tendsto_S hu hv hU hV hu0 hv0

end UndergradKB.RealAnalysis
