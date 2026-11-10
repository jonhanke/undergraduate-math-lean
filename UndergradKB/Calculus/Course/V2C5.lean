import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Series
import UndergradKB.Calculus.AlternatingSeries
import UndergradKB.Calculus.RiemannRearrangement

/-!
# OpenStax Calculus Volume 2, Chapter 5 (sequences and series): course layer

Thin wrappers around Mathlib. Sequences are `ℕ → ℝ`; convergence is `Filter.Tendsto u atTop (𝓝 L)`;
a series converges to `S` when `HasSum` (unconditional, which for nonnegative terms or absolutely
convergent series agrees with the classical notion). Series are indexed from `0` unless stated.
-/

namespace UndergradKB.Calculus.Course.V2C5

open Filter Topology Set MeasureTheory

/-- OpenStax Calculus 2:§5.1 Definition (epsilon-N) (CA-328).
A sequence converges to `L` iff for every `ε > 0` the terms are within `ε` of `L` from some index on. -/
@[kb "openstaxcalculus2016" "2:§5.1 Definition (convergent sequence, limit), p. 386"]
theorem sequence_converges_iff_epsilon_N (u : ℕ → ℝ) (L : ℝ) :
    Tendsto u atTop (𝓝 L) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - L| < ε := by
  simp only [Metric.tendsto_atTop, Real.dist_eq]

/-- OpenStax Calculus 2:§5.1 text on divergence to infinity (CA-329).
A sequence tends to infinity iff its terms eventually exceed every bound. -/
@[kb "openstaxcalculus2016" "2:§5.1 text on divergence to infinity, p. 385"]
theorem sequence_tendsto_atTop_iff (u : ℕ → ℝ) :
    Tendsto u atTop atTop ↔ ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < u n := by
  rw [tendsto_atTop_atTop]
  constructor
  · intro h M
    obtain ⟨N, hN⟩ := h (M + 1)
    exact ⟨N, fun n hn => by linarith [hN n hn]⟩
  · intro h M
    obtain ⟨N, hN⟩ := h M
    exact ⟨N, fun n hn => (hN n hn).le⟩

/-- OpenStax Calculus 2:Theorem 5.1 (CA-330).
If `f x → L` as `x → ∞` and `a n = f n`, then `a n → L`. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.1, p. 388"]
theorem sequence_limit_of_function_limit (f : ℝ → ℝ) (L : ℝ) (h : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => f n) atTop (𝓝 L) :=
  h.comp tendsto_natCast_atTop_atTop

/-- OpenStax Calculus 2:Theorem 5.2 (CA-331), sum rule. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.2, p. 388"]
theorem sequence_limit_add {a b : ℕ → ℝ} {A B : ℝ} (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) : Tendsto (fun n => a n + b n) atTop (𝓝 (A + B)) :=
  ha.add hb

/-- OpenStax Calculus 2:Theorem 5.2 (CA-331), difference rule. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.2, p. 388"]
theorem sequence_limit_sub {a b : ℕ → ℝ} {A B : ℝ} (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) : Tendsto (fun n => a n - b n) atTop (𝓝 (A - B)) :=
  ha.sub hb

/-- OpenStax Calculus 2:Theorem 5.2 (CA-331), constant multiple rule. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.2, p. 388"]
theorem sequence_limit_const_mul {a : ℕ → ℝ} {A : ℝ} (c : ℝ) (ha : Tendsto a atTop (𝓝 A)) :
    Tendsto (fun n => c * a n) atTop (𝓝 (c * A)) :=
  ha.const_mul c

/-- OpenStax Calculus 2:Theorem 5.2 (CA-331), product rule. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.2, p. 388"]
theorem sequence_limit_mul {a b : ℕ → ℝ} {A B : ℝ} (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) : Tendsto (fun n => a n * b n) atTop (𝓝 (A * B)) :=
  ha.mul hb

/-- OpenStax Calculus 2:Theorem 5.2 (CA-331), quotient rule when the limit of the denominator
is nonzero. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.2, p. 388"]
theorem sequence_limit_div {a b : ℕ → ℝ} {A B : ℝ} (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) (hB : B ≠ 0) : Tendsto (fun n => a n / b n) atTop (𝓝 (A / B)) :=
  ha.div hb hB

/-- OpenStax Calculus 2:Theorem 5.3 (CA-332).
If `a n → L` and `f` is continuous at `L`, then `f (a n) → f L`. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.3, p. 391"]
theorem sequence_limit_continuous_comp {a : ℕ → ℝ} {L : ℝ} (f : ℝ → ℝ) (ha : Tendsto a atTop (𝓝 L))
    (hf : ContinuousAt f L) : Tendsto (fun n => f (a n)) atTop (𝓝 (f L)) :=
  hf.tendsto.comp ha

/-- OpenStax Calculus 2:Theorem 5.4 (CA-333), squeeze theorem for sequences.
If `a n ≤ b n ≤ c n` eventually and `a n`, `c n` tend to `L`, then `b n → L`. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.4, p. 392"]
theorem sequence_squeeze {a b c : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (𝓝 L))
    (hc : Tendsto c atTop (𝓝 L)) (hab : ∀ᶠ n in atTop, a n ≤ b n)
    (hbc : ∀ᶠ n in atTop, b n ≤ c n) : Tendsto b atTop (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' ha hc hab hbc

/-- OpenStax Calculus 2:Theorem 5.5 (CA-337).
A convergent real sequence is bounded. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.5, p. 394"]
theorem convergent_sequence_bounded {u : ℕ → ℝ} {L : ℝ} (h : Tendsto u atTop (𝓝 L)) :
    ∃ M : ℝ, ∀ n, |u n| ≤ M := by
  obtain ⟨M, hM⟩ := h.abs.bddAbove_range
  exact ⟨M, fun n => hM ⟨n, rfl⟩⟩

/-- OpenStax Calculus 2:Theorem 5.6 (CA-338), increasing case.
A bounded sequence that is nondecreasing from some index on converges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.6, p. 395"]
theorem bounded_eventually_monotone_converges {u : ℕ → ℝ} {M : ℝ} (N : ℕ)
    (hmono : ∀ n ≥ N, u n ≤ u (n + 1)) (hbd : ∀ n, |u n| ≤ M) :
    ∃ L : ℝ, Tendsto u atTop (𝓝 L) := by
  have hm : Monotone (fun k => u (k + N)) :=
    monotone_nat_of_le_succ fun k => by
      have := hmono (k + N) (by omega)
      simpa [add_right_comm] using this
  have hb : BddAbove (range fun k => u (k + N)) :=
    ⟨M, by rintro _ ⟨k, rfl⟩; exact (le_abs_self _).trans (hbd _)⟩
  exact ⟨_, (tendsto_add_atTop_iff_nat N).mp (tendsto_atTop_ciSup hm hb)⟩

/-- OpenStax Calculus 2:Theorem 5.6 (CA-338), decreasing case.
A bounded sequence that is nonincreasing from some index on converges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.6, p. 395"]
theorem bounded_eventually_antitone_converges {u : ℕ → ℝ} {M : ℝ} (N : ℕ)
    (hanti : ∀ n ≥ N, u (n + 1) ≤ u n) (hbd : ∀ n, |u n| ≤ M) :
    ∃ L : ℝ, Tendsto u atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := bounded_eventually_monotone_converges (u := fun n => -u n) (M := M) N
    (fun n hn => by simpa using hanti n hn) (fun n => by simpa using hbd n)
  exact ⟨-L, by simpa using hL.neg⟩

/-- OpenStax Calculus 2:§5.2 The Harmonic Series (5.5) (CA-340).
The partial sums of `1 + 1/2 + 1/3 + ⋯` grow without bound. -/
@[kb "openstaxcalculus2016" "2:§5.2 The Harmonic Series (5.5), p. 406"]
theorem harmonic_series_partial_sums_tendsto_atTop :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- OpenStax Calculus 2:§5.2 The Harmonic Series (5.5) (CA-340).
The harmonic series is not summable. -/
@[kb "openstaxcalculus2016" "2:§5.2 The Harmonic Series (5.5), p. 406"]
theorem harmonic_series_not_summable : ¬ Summable (fun n : ℕ => (n : ℝ)⁻¹) :=
  Real.not_summable_natCast_inv

/-- OpenStax Calculus 2:Theorem 5.7 (CA-341), sums of series. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.7, p. 407"]
theorem series_add {a b : ℕ → ℝ} {A B : ℝ} (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (fun n => a n + b n) (A + B) :=
  ha.add hb

/-- OpenStax Calculus 2:Theorem 5.7 (CA-341), differences of series. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.7, p. 407"]
theorem series_sub {a b : ℕ → ℝ} {A B : ℝ} (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (fun n => a n - b n) (A - B) :=
  ha.sub hb

/-- OpenStax Calculus 2:Theorem 5.7 (CA-341), constant multiples of series. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.7, p. 407"]
theorem series_const_mul {a : ℕ → ℝ} {A : ℝ} (c : ℝ) (ha : HasSum a A) :
    HasSum (fun n => c * a n) (c * A) :=
  ha.mul_left c

/-- OpenStax Calculus 2:§5.2 Definition (geometric series) (CA-342).
For `|r| < 1` the geometric series `∑ a r ^ n` (book index `n ≥ 1` with `r ^ (n-1)`) has sum `a / (1 - r)`. -/
@[kb "openstaxcalculus2016" "2:§5.2 Definition (geometric series), p. 408"]
theorem geometric_series_sum (a r : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => a * r ^ n) (a / (1 - r)) := by
  simpa [div_eq_mul_inv] using (hasSum_geometric_of_abs_lt_one hr).mul_left a

/-- OpenStax Calculus 2:§5.2 Definition (geometric series) (CA-342).
For `a ≠ 0` and `|r| ≥ 1` the geometric series `∑ a r ^ n` diverges. -/
@[kb "openstaxcalculus2016" "2:§5.2 Definition (geometric series), p. 408"]
theorem geometric_series_diverges (a r : ℝ) (ha : a ≠ 0) (hr : 1 ≤ |r|) :
    ¬ Summable (fun n : ℕ => a * r ^ n) := by
  intro h
  have h2 : Summable (fun n : ℕ => r ^ n) := (summable_mul_left_iff ha).mp h
  have := summable_geometric_iff_norm_lt_one.mp h2
  rw [Real.norm_eq_abs] at this
  linarith

/-- OpenStax Calculus 2:Theorem 5.9 (CA-345), integral test.
For `f` nonnegative and decreasing on `[1, ∞)`, `∑ f n` converges iff `∫_1^∞ f` converges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.9, p. 425"]
theorem integral_test (f : ℝ → ℝ) (hanti : AntitoneOn f (Ici 1)) (hnn : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ f x) :
    Summable (fun n : ℕ => f ((n : ℝ) + 1)) ↔ IntegrableOn f (Ioi 1) := by
  have hanti' : AntitoneOn f (Ici ((1 : ℕ) : ℝ)) := by simpa using hanti
  have hnn' : ∀ t ∈ Ioi ((1 : ℕ) : ℝ), 0 ≤ f t := by simpa using hnn
  constructor
  · intro h
    have h' : Summable (fun n : ℕ => f (((n + 1 : ℕ) : ℝ))) := by simpa using h
    simpa using AntitoneOn.integrableOn_Ioi_of_summable_comp_add (N := 1) hanti' h' hnn'
  · intro h
    have h1 : Summable (fun n : ℕ => f n) :=
      AntitoneOn.summable_of_integrableOn_Ioi (N := 1) hanti' (by simpa using h) hnn'
    simpa using (summable_nat_add_iff 1).mpr h1

/-- OpenStax Calculus 2:§5.3 Definition (p-series) (CA-346).
The p-series `∑ 1 / n ^ p` (`n ≥ 1`) converges iff `p > 1`. -/
@[kb "openstaxcalculus2016" "2:§5.3 Definition (p-series), p. 427"]
theorem p_series_converges_iff (p : ℝ) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ p) ↔ 1 < p := by
  have h := summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ p) 1
  rw [Real.summable_one_div_nat_rpow] at h
  simpa using h

/-- OpenStax Calculus 2:Theorem 5.10 (CA-347), remainder estimate.
For `f` nonnegative, decreasing and integrable on `[N, ∞)`, the tail `R_N = ∑_{n > N} f n` satisfies
`∫_{N+1}^∞ f ≤ R_N ≤ ∫_N^∞ f`. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.10, p. 428"]
theorem integral_test_remainder_bounds (f : ℝ → ℝ) (N : ℕ) (hanti : AntitoneOn f (Ici (N : ℝ)))
    (hint : IntegrableOn f (Ioi (N : ℝ))) (hnn : ∀ x ∈ Ioi (N : ℝ), 0 ≤ f x) :
    (∫ x in Ioi ((N : ℝ) + 1), f x) ≤ ∑' n : ℕ, f ((n + N + 1 : ℕ) : ℝ) ∧
      ∑' n : ℕ, f ((n + N + 1 : ℕ) : ℝ) ≤ ∫ x in Ioi (N : ℝ), f x := by
  refine ⟨?_, AntitoneOn.tsum_comp_add_le_integral N hanti hint hnn⟩
  have hs : Summable (fun n : ℕ => f n) := AntitoneOn.summable_of_integrableOn_Ioi hanti hint hnn
  have := AntitoneOn.integral_le_tsum_comp_add (N + 1) (hanti.mono (Ici_subset_Ici.mpr (by simp)))
    hs (fun t ht => hnn t (by simp only [mem_Ioi, Nat.cast_add, Nat.cast_one] at ht ⊢; linarith))
  simpa [add_assoc, add_comm, add_left_comm] using this

/-- OpenStax Calculus 2:Theorem 5.11 (CA-348), comparison test (convergence part).
If `0 ≤ a n ≤ b n` and `∑ b n` converges, then `∑ a n` converges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.11, p. 436"]
theorem comparison_test_converges {a b : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n) (hle : ∀ n, a n ≤ b n)
    (hb : Summable b) : Summable a :=
  Summable.of_nonneg_of_le h0 hle hb

/-- OpenStax Calculus 2:Theorem 5.11 (CA-348), comparison test (divergence part).
If `0 ≤ a n ≤ b n` and `∑ a n` diverges, then `∑ b n` diverges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.11, p. 436"]
theorem comparison_test_diverges {a b : ℕ → ℝ} (h0 : ∀ n, 0 ≤ a n) (hle : ∀ n, a n ≤ b n)
    (ha : ¬ Summable a) : ¬ Summable b :=
  fun hb => ha (Summable.of_nonneg_of_le h0 hle hb)

/-- OpenStax Calculus 2:Theorem 5.13 (CA-351), alternating series test.
If `b` is decreasing with limit `0`, the partial sums of `∑ (-1)^n b n` (book index `(-1)^(n+1) b_n`
from `n = 1`) converge. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.13, p. 447"]
theorem alternating_series_test {b : ℕ → ℝ} (hb : Antitone b) (h0 : Tendsto b atTop (𝓝 0)) :
    ∃ l : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * b i) atTop (𝓝 l) :=
  hb.tendsto_alternating_series_of_tendsto_zero h0

/-- OpenStax Calculus 2:Theorem 5.15 (CA-354).
An absolutely convergent series converges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.15, p. 449"]
theorem absolutely_convergent_series_converges {a : ℕ → ℝ} (h : Summable fun n => |a n|) :
    Summable a :=
  Summable.of_norm (by simpa [Real.norm_eq_abs] using h)

/-- OpenStax Calculus 2:§5.5 text after Example 5.21 (CA-356).
Rearranging an absolutely convergent series by a bijection `σ` of the indices does not change its sum. -/
@[kb "openstaxcalculus2016" "2:§5.5 text after Example 5.21, p. 450"]
theorem rearrangement_of_absolutely_convergent_series {a : ℕ → ℝ} (h : Summable fun n => |a n|)
    (σ : ℕ ≃ ℕ) : HasSum (fun n => a (σ n)) (∑' n, a n) := by
  have := (absolutely_convergent_series_converges h).hasSum
  exact (σ.hasSum_iff).mpr this

/-- OpenStax Calculus 2:Theorem 5.16 (CA-358), ratio test, `ρ < 1`.
If `|a (n+1) / a n| → ρ < 1` (terms eventually nonzero) the series converges absolutely. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.16, p. 458"]
theorem ratio_test_converges {a : ℕ → ℝ} {ρ : ℝ} (hρ : ρ < 1) (hne : ∀ᶠ n in atTop, a n ≠ 0)
    (h : Tendsto (fun n => |a (n + 1) / a n|) atTop (𝓝 ρ)) : Summable fun n => |a n| := by
  refine summable_of_ratio_test_tendsto_lt_one (f := fun n => |a n|) hρ ?_ ?_
  · filter_upwards [hne] with n hn using abs_ne_zero.mpr hn
  · simpa [abs_div, Real.norm_eq_abs] using h

/-- OpenStax Calculus 2:Theorem 5.16 (CA-358), ratio test, `ρ > 1`.
If `|a (n+1) / a n| → ρ > 1` the series diverges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.16, p. 458"]
theorem ratio_test_diverges {a : ℕ → ℝ} {ρ : ℝ} (hρ : 1 < ρ)
    (h : Tendsto (fun n => |a (n + 1) / a n|) atTop (𝓝 ρ)) : ¬ Summable a := by
  refine not_summable_of_ratio_test_tendsto_gt_one (f := a) hρ ?_
  simpa [abs_div, Real.norm_eq_abs] using h

/-- OpenStax Calculus 2:Theorem 5.16 (CA-358), ratio test, `ρ = ∞`.
If `|a (n+1) / a n| → ∞` the series diverges. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.16, p. 458"]
theorem ratio_test_diverges_of_tendsto_atTop {a : ℕ → ℝ}
    (h : Tendsto (fun n => |a (n + 1) / a n|) atTop atTop) : ¬ Summable a := by
  have h2 : ∀ᶠ n in atTop, 2 ≤ |a (n + 1) / a n| := h.eventually_ge_atTop 2
  have hne : ∀ᶠ n in atTop, a n ≠ 0 := by
    filter_upwards [h2] with n hn h0
    simp [h0] at hn
    linarith
  refine not_summable_of_ratio_norm_eventually_ge (f := a) (r := 2) (by norm_num) ?_ ?_
  · exact (hne.mono fun n hn => by simpa using hn).frequently
  · filter_upwards [h2, hne] with n hn hn0
    have hpos : 0 < |a n| := abs_pos.mpr hn0
    rw [abs_div, le_div_iff₀ hpos] at hn
    simpa [Real.norm_eq_abs, mul_comm] using hn

/-! ## Results proved in undergrad-kb -/

/-- OpenStax Calculus 2:Theorem 5.8 (CA-344). Divergence test: if `a n` does not tend to `0`, the
series `∑ a n` diverges; the converse fails (the harmonic series diverges although `1/n → 0`). -/
@[kb "openstaxcalculus2016" "2:Theorem 5.8, p. 422"]
theorem divergence_test :
    (∀ {a : ℕ → ℝ}, ¬ Tendsto a atTop (𝓝 0) →
      ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 S)) ∧
    (Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) ∧
      ¬ ∃ S : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)) atTop (𝓝 S)) :=
  ⟨fun h => UndergradKB.Calculus.series_diverges_of_not_tendsto_zero h,
    UndergradKB.Calculus.divergence_test_converse_fails⟩

/-- OpenStax Calculus 2:Theorem 5.12 (CA-349). Limit comparison test for positive terms with
`a n / b n → L`: for `0 < L < ∞` both series converge or both diverge; for `L = 0` convergence
of `∑ b n` gives that of `∑ a n`; for `L = ∞` divergence of `∑ b n` gives that of `∑ a n`. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.12, p. 439"]
theorem limit_comparison_test {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) :
    (∀ {L : ℝ}, 0 < L → Tendsto (fun n => a n / b n) atTop (𝓝 L) →
      (Summable a ↔ Summable b)) ∧
    (Tendsto (fun n => a n / b n) atTop (𝓝 0) → Summable b → Summable a) ∧
    (Tendsto (fun n => a n / b n) atTop atTop → ¬ Summable b → ¬ Summable a) :=
  ⟨fun hL h => UndergradKB.Calculus.limit_comparison_pos ha hb hL h,
    fun h hs => UndergradKB.Calculus.limit_comparison_zero ha hb h hs,
    fun h hs => UndergradKB.Calculus.limit_comparison_top ha hb h hs⟩

/-- OpenStax Calculus 2:Theorem 5.14 (CA-352). Remainder estimate for alternating series: for a
decreasing sequence `b n → 0` with `∑ (-1)^i b i = S`, the partial sum over the first `N` terms
is within `b N` of `S`. -/
@[kb "openstaxcalculus2016" "2:Theorem 5.14, p. 448"]
theorem alternating_series_remainder_estimate {b : ℕ → ℝ} (hb : Antitone b)
    (h0 : Tendsto b atTop (𝓝 0)) {S : ℝ}
    (hS : Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * b i) atTop (𝓝 S)) (N : ℕ) :
    |S - ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * b i| ≤ b N :=
  UndergradKB.Calculus.alternating_series_remainder hb h0 hS N

/-- OpenStax Calculus 2:Theorem 5.17 (CA-359). Root test: if `|a n|^(1/n) → ρ`, then `ρ < 1` gives
absolute convergence, `ρ > 1` (or the limit `∞`) gives divergence, and `ρ = 1` is inconclusive
(the harmonic series diverges and `∑ 1/n²` converges, both with `ρ = 1`). -/
@[kb "openstaxcalculus2016" "2:Theorem 5.17, p. 461"]
theorem root_test :
    (∀ {a : ℕ → ℝ} {ρ : ℝ},
      Tendsto (fun n : ℕ => |a n| ^ (1 / (n : ℝ))) atTop (𝓝 ρ) → ρ < 1 →
      Summable (fun n => |a n|)) ∧
    (∀ {a : ℕ → ℝ} {ρ : ℝ},
      Tendsto (fun n : ℕ => |a n| ^ (1 / (n : ℝ))) atTop (𝓝 ρ) → 1 < ρ →
      ¬ Tendsto a atTop (𝓝 0) ∧
        ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 S)) ∧
    (∀ {a : ℕ → ℝ},
      Tendsto (fun n : ℕ => |a n| ^ (1 / (n : ℝ))) atTop atTop →
      ¬ Tendsto a atTop (𝓝 0) ∧
        ∀ S : ℝ, ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 S)) ∧
    (Tendsto (fun n : ℕ => |1 / (n : ℝ)| ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
      ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) ∧
      Tendsto (fun n : ℕ => |1 / (n : ℝ) ^ 2| ^ (1 / (n : ℝ))) atTop (𝓝 1) ∧
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2)) :=
  ⟨fun h hρ => UndergradKB.Calculus.root_test_summable h hρ,
    fun h hρ => UndergradKB.Calculus.root_test_diverges h hρ,
    fun h => UndergradKB.Calculus.root_test_diverges_top h,
    UndergradKB.Calculus.root_test_inconclusive⟩

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 2:§5.1 Geometric sequence properties (5.1)-(5.4) (CA-334). The sequence
`r^n` tends to `0` when `|r| < 1`, to `1` when `r = 1`, to infinity when `r > 1`, and has no
limit when `r ≤ -1`. -/
@[kb "openstaxcalculus2016" "2:§5.1 Geometric sequence properties (5.1)-(5.4), p. 393"]
theorem geometric_sequence_behavior (r : ℝ) :
    (|r| < 1 → Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0)) ∧
    (r = 1 → Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 1)) ∧
    (1 < r → Tendsto (fun n : ℕ => r ^ n) atTop atTop) ∧
    (r ≤ -1 → ∀ L : ℝ, ¬ Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 L)) :=
  UndergradKB.Calculus.geometric_sequence_limits r

/-- OpenStax Calculus 2:§5.2 Definition (infinite series, partial sums, sum) (CA-339). A series
converges to `S` when its partial sums tend to `S`; for nonnegative terms this agrees with
Mathlib's `HasSum`, and in general `HasSum` implies convergence of the partial sums. -/
@[kb "openstaxcalculus2016" "2:§5.2 Definition (infinite series, partial sums, sum), p. 404"]
theorem infinite_series_partial_sums :
    (∀ {a : ℕ → ℝ}, (∀ n, 0 ≤ a n) → ∀ S : ℝ,
      (Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 S) ↔ HasSum a S)) ∧
    (∀ {a : ℕ → ℝ} {S : ℝ}, HasSum a S →
      Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 S)) :=
  ⟨fun ha S => UndergradKB.Calculus.series_converges_iff_hasSum_of_nonneg ha S,
    fun h => UndergradKB.Calculus.tendsto_partial_sums_of_hasSum h⟩

/-- OpenStax Calculus 2:§5.2 Definition (telescoping series) (CA-343). If `b n → L`, the partial
sums of `∑ (b n - b (n+1))` equal `b 0 - b n` and tend to `b 0 - L`. -/
@[kb "openstaxcalculus2016" "2:§5.2 Definition (telescoping series), p. 414"]
theorem telescoping_series_sum {b : ℕ → ℝ} {L : ℝ} (hb : Tendsto b atTop (𝓝 L)) :
    (∀ n, ∑ i ∈ Finset.range n, (b i - b (i + 1)) = b 0 - b n) ∧
    Tendsto (fun n => ∑ i ∈ Finset.range n, (b i - b (i + 1))) atTop (𝓝 (b 0 - L)) :=
  UndergradKB.Calculus.telescoping_series hb

/-- OpenStax Calculus 2:Example 5.21 (CA-355). The alternating harmonic series converges, but the
series of absolute values (the harmonic series) does not, so the convergence is conditional. -/
@[kb "openstaxcalculus2016" "2:Example 5.21, p. 449"]
theorem alternating_harmonic_conditionally_convergent :
    (∃ S : ℝ, Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i / ((i : ℝ) + 1)) atTop (𝓝 S)) ∧
    ¬ Summable (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1)|) :=
  UndergradKB.Calculus.alternating_harmonic_series

/-- OpenStax Calculus 2:Example 5.22 (CA-357). A conditionally convergent series has positive and
negative parts that both diverge to infinity, and can be rearranged to sum to any real number
(Riemann); in particular the alternating harmonic series can be rearranged to sum to any `L`. -/
@[kb "openstaxcalculus2016" "2:Example 5.22, p. 451"]
theorem conditionally_convergent_rearrangement :
    (∀ {a : ℕ → ℝ} {S : ℝ}, Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 S) →
      ¬ Summable a →
      Tendsto (fun n => ∑ i ∈ Finset.range n, UndergradKB.Calculus.posPart a i) atTop atTop ∧
      Tendsto (fun n => ∑ i ∈ Finset.range n, UndergradKB.Calculus.negPart a i) atTop atTop) ∧
    (∀ {a : ℕ → ℝ} {S : ℝ}, Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 S) →
      ¬ Summable (fun n => |a n|) → ∀ L : ℝ,
      ∃ σ : ℕ ≃ ℕ, Tendsto (fun n => ∑ i ∈ Finset.range n, a (σ i)) atTop (𝓝 L)) ∧
    (∀ L : ℝ, ∃ σ : ℕ ≃ ℕ,
      Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ (σ i) / ((σ i : ℝ) + 1)) atTop (𝓝 L)) :=
  ⟨fun hS habs => UndergradKB.Calculus.conditionally_convergent_parts_diverge hS habs,
    fun hS habs L => UndergradKB.Calculus.riemann_rearrangement hS habs L,
    fun L => UndergradKB.Calculus.alternating_harmonic_rearrangement L⟩

end UndergradKB.Calculus.Course.V2C5
