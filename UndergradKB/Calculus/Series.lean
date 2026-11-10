import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology

/-! ## Sequences and series as limits of partial sums -/

/-- OpenStax Calculus 2:§5.1 (CA-334). The geometric sequence `r ^ n`: tends to `0` if `|r| < 1`, to `1` if
`r = 1`, to infinity if `r > 1`, and has no limit at all if `r ≤ -1`. -/
@[kb "openstaxcalculus2016" "2:§5.1 Geometric sequence properties (5.1)-(5.4), p. 393"]
theorem geometric_sequence_limits (r : ℝ) :
    (|r| < 1 → Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0)) ∧
    (r = 1 → Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 1)) ∧
    (1 < r → Tendsto (fun n : ℕ => r ^ n) atTop atTop) ∧
    (r ≤ -1 → ∀ L : ℝ, ¬ Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 L)) := by
  refine ⟨tendsto_pow_atTop_nhds_zero_of_abs_lt_one, ?_, tendsto_pow_atTop_atTop_of_one_lt, ?_⟩
  · rintro rfl
    simp
  · intro hr L hL
    have h1 : Tendsto (fun n : ℕ => r ^ (n + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => r ^ (n + 1)) atTop (𝓝 (r * L)) := by
      simpa [pow_succ'] using hL.const_mul r
    have hL2 : L = r * L := tendsto_nhds_unique h1 h2
    have hL0 : L = 0 := by
      have : (1 - r) * L = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    have hge : ∀ n : ℕ, 1 ≤ |r ^ n| := fun n => by
      rw [abs_pow]
      exact one_le_pow₀ (by rw [abs_of_nonpos (by linarith)]; linarith)
    have := (continuous_abs.tendsto L |>.comp hL)
    rw [hL0, abs_zero] at this
    have h3 := ge_of_tendsto this (Eventually.of_forall hge)
    linarith

/-- OpenStax Calculus 2:§5.2 (CA-339). A series with nonnegative terms converges (in the book's sense: the partial
sums `∑_{i<n} a i` tend to `S`) exactly when it has sum `S` in Mathlib's sense (`HasSum`). -/
@[kb "openstaxcalculus2016" "2:§5.2 Definition (infinite series, partial sums, sum), p. 404"]
theorem series_converges_iff_hasSum_of_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (S : ℝ) :
    Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S) ↔ HasSum a S :=
  (hasSum_iff_tendsto_nat_of_nonneg ha S).symm

/-- OpenStax Calculus 2:§5.2 (CA-339). Mathlib's `HasSum` (unconditional convergence) implies convergence of the
partial sums in the book's sense. -/
@[kb "openstaxcalculus2016" "2:§5.2 Definition (infinite series, partial sums, sum), p. 404"]
theorem tendsto_partial_sums_of_hasSum {a : ℕ → ℝ} {S : ℝ} (h : HasSum a S) :
    Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S) :=
  h.tendsto_sum_nat

/-- OpenStax Calculus 2:§5.2 (CA-343). Telescoping series: if `b n → L`, the partial sums of
`∑ (b n - b (n+1))` are `b 0 - b n` and tend to `b 0 - L`. -/
@[kb "openstaxcalculus2016" "2:§5.2 Definition (telescoping series), p. 414"]
theorem telescoping_series {b : ℕ → ℝ} {L : ℝ} (hb : Tendsto b atTop (𝓝 L)) :
    (∀ n, ∑ i ∈ range n, (b i - b (i + 1)) = b 0 - b n) ∧
    Tendsto (fun n => ∑ i ∈ range n, (b i - b (i + 1))) atTop (𝓝 (b 0 - L)) := by
  have h : ∀ n, ∑ i ∈ range n, (b i - b (i + 1)) = b 0 - b n := fun n => by
    rw [Finset.sum_range_sub']
  refine ⟨h, ?_⟩
  have : (fun n => ∑ i ∈ range n, (b i - b (i + 1))) = fun n => b 0 - b n := funext h
  rw [this]
  exact tendsto_const_nhds.sub hb

/-- OpenStax Calculus 2:Theorem 5.8 (CA-344). Divergence test: if the terms do not tend to `0`, the series
does not converge (partial sums have no limit). -/
@[kb "openstaxcalculus2016" "2:Theorem 5.8, p. 422"]
theorem series_diverges_of_not_tendsto_zero {a : ℕ → ℝ} (h : ¬ Tendsto a atTop (𝓝 0)) :
    ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S) := by
  intro S hS
  apply h
  have h1 : Tendsto (fun n => ∑ i ∈ range (n + 1), a i) atTop (𝓝 S) :=
    hS.comp (tendsto_add_atTop_nat 1)
  have h2 := h1.sub hS
  rw [sub_self] at h2
  refine h2.congr (fun n => ?_)
  rw [Finset.sum_range_succ]
  ring

/-- OpenStax Calculus 2:Theorem 5.8 (CA-344). The converse of the divergence test fails: the harmonic series
has terms tending to `0` but its partial sums are unbounded. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.8, p. 422"]
theorem divergence_test_converse_fails :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) ∧
    ¬ ∃ S : ℝ, Tendsto (fun n => ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) atTop (𝓝 S) := by
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  rintro ⟨S, hS⟩
  have := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have h2 := this.eventually (eventually_gt_atTop (S + 1))
  have h3 := hS.eventually (gt_mem_nhds (show S < S + 1 by linarith))
  obtain ⟨n, hn1, hn2⟩ := (h2.and h3).exists
  linarith

/-! ## Limit comparison test -/

/-- If eventually `0 ≤ a n ≤ C * b n` and `∑ b n` converges then `∑ a n` converges. -/
theorem summable_of_eventually_le_mul {a b : ℕ → ℝ} {C : ℝ} (hb : Summable b)
    (h : ∀ᶠ n in atTop, 0 ≤ a n ∧ a n ≤ C * b n) : Summable a := by
  refine Summable.of_norm_bounded_eventually_nat (hb.mul_left C) ?_
  filter_upwards [h] with n hn
  rw [Real.norm_of_nonneg hn.1]
  exact hn.2

/-- OpenStax Calculus 2:Theorem 5.12 (CA-349), case `0 < L < ∞`. For positive terms with `a n / b n → L`,
`0 < L`, the series `∑ a n` converges iff `∑ b n` does (for positive terms, convergence is `Summable`). -/
@[kb "openstaxcalculus2016" "2:Theorem 5.12, p. 439"]
theorem limit_comparison_pos {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) {L : ℝ}
    (hL : 0 < L) (h : Tendsto (fun n => a n / b n) atTop (𝓝 L)) :
    Summable a ↔ Summable b := by
  have h1 : ∀ᶠ n in atTop, a n / b n < 2 * L :=
    h.eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ n in atTop, L / 2 < a n / b n :=
    h.eventually (lt_mem_nhds (by linarith))
  constructor
  · intro hs
    refine summable_of_eventually_le_mul (C := 2 / L) hs ?_
    filter_upwards [h2] with n hn
    refine ⟨(hb n).le, ?_⟩
    have := (lt_div_iff₀ (hb n)).mp hn
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    nlinarith [hb n]
  · intro hs
    refine summable_of_eventually_le_mul (C := 2 * L) hs ?_
    filter_upwards [h1] with n hn
    refine ⟨(ha n).le, ?_⟩
    have := (div_lt_iff₀ (hb n)).mp hn
    linarith

/-- OpenStax Calculus 2:Theorem 5.12 (CA-349), case `L = 0`: if `a n / b n → 0` and `∑ b n` converges
then `∑ a n` converges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.12, p. 439"]
theorem limit_comparison_zero {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (h : Tendsto (fun n => a n / b n) atTop (𝓝 0)) (hs : Summable b) : Summable a := by
  refine summable_of_eventually_le_mul (C := 1) hs ?_
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  refine ⟨(ha n).le, ?_⟩
  have := (div_lt_iff₀ (hb n)).mp hn
  linarith

/-- OpenStax Calculus 2:Theorem 5.12 (CA-349), case `L = ∞`: if `a n / b n → ∞` and `∑ b n` diverges
then `∑ a n` diverges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.12, p. 439"]
theorem limit_comparison_top {a b : ℕ → ℝ} (_ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (h : Tendsto (fun n => a n / b n) atTop atTop) (hs : ¬ Summable b) : ¬ Summable a := by
  intro hsa
  apply hs
  refine summable_of_eventually_le_mul (C := 1) hsa ?_
  filter_upwards [h.eventually (eventually_ge_atTop 1)] with n hn
  refine ⟨(hb n).le, ?_⟩
  have := (le_div_iff₀ (hb n)).mp hn
  linarith

/-! ## Root test -/

/-- OpenStax Calculus 2:Theorem 5.17 (CA-359), convergent case. If `|a n| ^ (1/n) → ρ` with `ρ < 1`, then the
series `∑ a n` converges absolutely. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.17, p. 461"]
theorem root_test_summable {a : ℕ → ℝ} {ρ : ℝ}
    (h : Tendsto (fun n : ℕ => |a n| ^ (1 / (n : ℝ))) atTop (𝓝 ρ)) (hρ : ρ < 1) :
    Summable (fun n => |a n|) := by
  obtain ⟨r, hρr, hr1⟩ := exists_between hρ
  have hr0 : 0 < r := by
    have := h.eventually (gt_mem_nhds hρr)
    obtain ⟨n, hn⟩ := this.exists
    exact lt_of_le_of_lt (by positivity) hn
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0.le hr1) ?_
  filter_upwards [h.eventually (gt_mem_nhds hρr), eventually_gt_atTop 0] with n hn hn0
  simp only [Real.norm_eq_abs, abs_abs]
  have hn0' : n ≠ 0 := hn0.ne'
  have : |a n| = (|a n| ^ (1 / (n : ℝ))) ^ n := by
    rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hn0']
  rw [this]
  exact pow_le_pow_left₀ (by positivity) hn.le n

/-- If eventually `|a n| ^ (1/n) > 1` then `a n` does not tend to `0`. -/
theorem not_tendsto_zero_of_root_eventually_gt_one {a : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop, 1 < |a n| ^ (1 / (n : ℝ))) : ¬ Tendsto a atTop (𝓝 0) := by
  intro h0
  have h1 : ∀ᶠ n in atTop, |a n| < 1 := by
    have := (continuous_abs.tendsto 0 |>.comp h0).eventually (gt_mem_nhds (show |(0:ℝ)| < 1 by simp))
    simpa using this
  obtain ⟨n, ⟨hn, hn0⟩, hn1⟩ := ((h.and (eventually_gt_atTop 0)).and h1).exists
  have hn0' : n ≠ 0 := hn0.ne'
  have : |a n| = (|a n| ^ (1 / (n : ℝ))) ^ n := by
    rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hn0']
  have h2 : 1 ≤ (|a n| ^ (1 / (n : ℝ))) ^ n :=
    one_le_pow₀ hn.le
  linarith

/-- OpenStax Calculus 2:Theorem 5.17 (CA-359), divergent case. If `|a n| ^ (1/n) → ρ` with `ρ > 1`, then
`a n` does not tend to `0`, so the series `∑ a n` diverges (its partial sums have no limit). -/
@[kb "openstaxcalculus2016" "2:Theorem 5.17, p. 461"]
theorem root_test_diverges {a : ℕ → ℝ} {ρ : ℝ}
    (h : Tendsto (fun n : ℕ => |a n| ^ (1 / (n : ℝ))) atTop (𝓝 ρ)) (hρ : 1 < ρ) :
    ¬ Tendsto a atTop (𝓝 0) ∧ ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S) := by
  have key := not_tendsto_zero_of_root_eventually_gt_one (a := a)
    (h.eventually (lt_mem_nhds hρ))
  exact ⟨key, series_diverges_of_not_tendsto_zero key⟩

/-- OpenStax Calculus 2:Theorem 5.17 (CA-359), infinite case. If `|a n| ^ (1/n) → ∞` then `a n` does not tend
to `0` and the series diverges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.17, p. 461"]
theorem root_test_diverges_top {a : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => |a n| ^ (1 / (n : ℝ))) atTop atTop) :
    ¬ Tendsto a atTop (𝓝 0) ∧ ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ range n, a i) atTop (𝓝 S) := by
  have key := not_tendsto_zero_of_root_eventually_gt_one (a := a)
    (h.eventually (eventually_gt_atTop 1))
  exact ⟨key, series_diverges_of_not_tendsto_zero key⟩

/-- OpenStax Calculus 2:Theorem 5.17 (CA-359), `ρ = 1` is inconclusive: for `a n = 1/n` (divergent, harmonic) and
`a n = 1/n²` (convergent) the quantity `|a n| ^ (1/n)` tends to `1` in both cases. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.17, p. 461"]
theorem root_test_inconclusive :
    Tendsto (fun n : ℕ => |1 / (n : ℝ)| ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
    ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) ∧
    Tendsto (fun n : ℕ => |1 / (n : ℝ) ^ 2| ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 1) :=
    tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
  have e1 : ∀ n : ℕ, |1 / (n : ℝ)| ^ (1 / (n : ℝ)) = ((n : ℝ) ^ (1 / (n : ℝ)))⁻¹ := fun n => by
    rw [abs_of_nonneg (by positivity), one_div, Real.inv_rpow (Nat.cast_nonneg n)]
  have e2 : ∀ n : ℕ, |1 / (n : ℝ) ^ 2| ^ (1 / (n : ℝ)) = (((n : ℝ) ^ (1 / (n : ℝ)))⁻¹) ^ 2 := fun n => by
    rw [abs_of_nonneg (by positivity), one_div, Real.inv_rpow (by positivity), inv_pow,
      ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
      ← Real.rpow_mul (Nat.cast_nonneg n), mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [e1]
    simpa using hn.inv₀ one_ne_zero
  · simpa [one_div] using Real.not_summable_natCast_inv
  · simp_rw [e2]
    simpa using (hn.inv₀ one_ne_zero).pow 2
  · simp [one_div]

end UndergradKB.Calculus
