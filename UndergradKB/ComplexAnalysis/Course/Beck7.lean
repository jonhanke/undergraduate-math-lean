import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Chapter 7 (Power Series): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`).

Beck's series `∑_{k≥1} b_k` are modelled through the partial sums `S_n = b_1 + ... + b_n`
(`partialSum`), and "the series converges with limit `L`" is `SeriesLimit b L`, i.e. `S_n → L`.
Sequences are indexed by `ℕ` and a function `f : G → ℂ` on a domain `G` is a function `ℂ → ℂ`
whose values off `G` do not matter. The open disk `D[a, r]` of the book is `Metric.ball a r`. -/

namespace UndergradKB.ComplexAnalysis.Course.Beck7
open Filter Topology Metric Finset
open scoped Nat NNReal ENNReal

/-- The `n`-th partial sum `b 1 + ... + b n` of the series `∑_{k ≥ 1} b k`. -/
def partialSum {E : Type*} [AddCommMonoid E] (b : ℕ → E) (n : ℕ) : E :=
  ∑ k ∈ range n, b (k + 1)

/-- The series `∑_{k ≥ 1} b k` converges with limit `L`: its partial sums tend to `L`. -/
def SeriesLimit {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (b : ℕ → E) (L : E) : Prop :=
  Tendsto (partialSum b) atTop (𝓝 L)

lemma exists_seriesLimit_iff_summable {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) :
    (∃ L, SeriesLimit b L) ↔ Summable (fun k => b (k + 1)) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, (hasSum_iff_tendsto_nat_of_nonneg (fun k => hb _) L).2 hL⟩
  · intro h
    exact ⟨_, h.hasSum.tendsto_sum_nat⟩

/-! ### Section 7.1 -/

/-- Beck Definition 7.1.1 (CX-091). Convergence of a sequence to `L`, in the epsilon-`N` form. -/
@[kb "beck2025" "Definition 7.1.1, p. 111"]
theorem tendsto_iff_epsilon_N (a : ℕ → ℂ) (L : ℂ) :
    Tendsto a atTop (𝓝 L) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖a n - L‖ < ε := by
  simp [Metric.tendsto_atTop, dist_eq_norm]

/-- Beck Example 7.1.2 (CX-091). `i^n / n → 0`. -/
@[kb "beck2025" "Example 7.1.2, p. 111"]
theorem tendsto_I_pow_div : Tendsto (fun n : ℕ => Complex.I ^ n / n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [norm_div, norm_pow] using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)

/-- Beck Example 7.1.3 (CX-091). The sequence `i^n` diverges. -/
@[kb "beck2025" "Example 7.1.3, p. 111"]
theorem I_pow_diverges : ¬ ∃ L : ℂ, Tendsto (fun n : ℕ => Complex.I ^ n) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h1 : Tendsto (fun k : ℕ => 4 * k) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have h2 : Tendsto (fun k : ℕ => 4 * k + 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
  have e1 := hL.comp h1
  have e2 := hL.comp h2
  have f1 : (fun n : ℕ => Complex.I ^ n) ∘ (fun k : ℕ => 4 * k) = fun _ => (1 : ℂ) := by
    funext k
    simp only [Function.comp, pow_mul]
    have : Complex.I ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
    rw [this, one_pow]
  have f2 : (fun n : ℕ => Complex.I ^ n) ∘ (fun k : ℕ => 4 * k + 2) = fun _ => (-1 : ℂ) := by
    funext k
    simp only [Function.comp, pow_add, pow_mul]
    have : Complex.I ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
    rw [this, one_pow, one_mul, Complex.I_sq]
  rw [f1] at e1
  rw [f2] at e2
  have := (tendsto_nhds_unique e1 tendsto_const_nhds).symm.trans
    (tendsto_nhds_unique e2 tendsto_const_nhds)
  norm_num at this

/-- Beck Proposition 7.1.4 (CX-092). Limit laws for sequences, the shifted sequence, and
`f (lim a_n) = lim f (a_n)` for `f` continuous at the limit. -/
@[kb "beck2025" "Proposition 7.1.4, p. 112"]
theorem sequence_limit_laws (a b : ℕ → ℂ) (A B c : ℂ)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    Tendsto (fun n => a n + c * b n) atTop (𝓝 (A + c * B)) ∧
    Tendsto (fun n => a n * b n) atTop (𝓝 (A * B)) ∧
    (B ≠ 0 → Tendsto (fun n => a n / b n) atTop (𝓝 (A / B))) ∧
    Tendsto (fun n => a (n + 1)) atTop (𝓝 A) ∧
    (∀ f : ℂ → ℂ, ContinuousAt f A → Tendsto (fun n => f (a n)) atTop (𝓝 (f A))) :=
  ⟨ha.add (hb.const_mul c), ha.mul hb, fun hB => ha.div hb hB,
    ha.comp (tendsto_add_atTop_nat 1), fun _ hf => hf.tendsto.comp ha⟩

/-- Beck Axiom 7.1.6 (CX-093). Monotone sequence property: a bounded monotone real sequence
converges (a theorem in Mathlib, from the completeness of `ℝ`). -/
@[kb "beck2025" "Axiom 7.1.6, p. 112"]
theorem monotone_sequence_property (a : ℕ → ℝ) (hm : Monotone a ∨ Antitone a)
    (hb : ∃ M : ℝ, ∀ n, |a n| ≤ M) : ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  obtain ⟨M, hM⟩ := hb
  rcases hm with h | h
  · exact ⟨_, tendsto_atTop_ciSup h ⟨M, by rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (hM n)⟩⟩
  · exact ⟨_, tendsto_atTop_ciInf h
      ⟨-M, by rintro _ ⟨n, rfl⟩; linarith [neg_abs_le (a n), hM n]⟩⟩

/-- The partial sum `1 + 1/2 + 1/6 + ... + 1/n!` of Example 7.1.7, as the series
`∑_{k ≥ 1} 1/k!`. -/
lemma partialSum_inv_factorial_tendsto :
    Tendsto (partialSum (fun k : ℕ => 1 / (k ! : ℝ))) atTop (𝓝 (Real.exp 1 - 1)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (h.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h3 := h2.sub_const 1
  refine h3.congr fun n => ?_
  simp only [Function.comp, partialSum]
  rw [Finset.sum_range_succ']
  simp

/-- Beck Example 7.1.7 (CX-094). The sequence `a_n = 1/1! + 1/2! + ... + 1/n!` is increasing,
bounded by `3`, and its limit is `e - 1`. -/
@[kb "beck2025" "Example 7.1.7, p. 112"]
theorem exp_one_sequence :
    Monotone (partialSum (fun k : ℕ => 1 / (k ! : ℝ))) ∧
    (∀ n, partialSum (fun k : ℕ => 1 / (k ! : ℝ)) n ≤ 3) ∧
    Tendsto (partialSum (fun k : ℕ => 1 / (k ! : ℝ))) atTop (𝓝 (Real.exp 1 - 1)) := by
  have hmono : Monotone (partialSum (fun k : ℕ => 1 / (k ! : ℝ))) := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [partialSum, Finset.sum_range_succ]
    have : (0 : ℝ) ≤ 1 / ((n + 1 : ℕ)! : ℝ) := by positivity
    linarith
  have hlim := partialSum_inv_factorial_tendsto
  refine ⟨hmono, fun n => ?_, hlim⟩
  have := hmono.ge_of_tendsto hlim n
  have h2 := Real.exp_one_lt_d9
  norm_num at h2
  linarith

/-- Beck Example 7.1.8 (CX-094). For `0 ≤ r < 1`, `r^n → 0`. -/
@[kb "beck2025" "Example 7.1.8, p. 113"]
theorem pow_tendsto_zero (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1

/-- Beck Theorem 7.1.9 (CX-095). Archimedean property: every real number is below some integer. -/
@[kb "beck2025" "Theorem 7.1.9, p. 113"]
theorem archimedean (x : ℝ) : ∃ N : ℤ, x < N := by
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact ⟨n, by exact_mod_cast hn⟩

/-- Beck Proposition 7.1.10 (CX-096). Exponentials beat polynomials, and factorials beat
exponentials. -/
@[kb "beck2025" "Proposition 7.1.10, p. 113"]
theorem exponentials_beat_polynomials :
    (∀ (p : Polynomial ℂ) (c : ℂ), 1 < ‖c‖ →
      Tendsto (fun n : ℕ => p.eval (n : ℂ) / c ^ n) atTop (𝓝 0)) ∧
    (∀ c : ℂ, Tendsto (fun n : ℕ => c ^ n / (n ! : ℂ)) atTop (𝓝 0)) := by
  constructor
  · intro p c hc
    have key : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℂ) ^ k / c ^ n) atTop (𝓝 0) := by
      intro k
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa [norm_div, norm_pow] using tendsto_pow_const_div_const_pow_of_one_lt k hc
    have : ∀ n : ℕ, p.eval (n : ℂ) / c ^ n =
        ∑ k ∈ range (p.natDegree + 1), p.coeff k * ((n : ℂ) ^ k / c ^ n) := by
      intro n
      rw [Polynomial.eval_eq_sum_range, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [this]
    have h := tendsto_finsetSum (range (p.natDegree + 1))
      (fun k _ => (key k).const_mul (p.coeff k))
    simpa using h
  · intro c
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_div, norm_pow] using FloorSemiring.tendsto_pow_div_factorial_atTop ‖c‖

/-! ### Section 7.2 -/

/-- Beck Example 7.2.2 (CX-097). For `|z| < 1`, `∑_{k ≥ 1} z^k = z / (1 - z)`. -/
@[kb "beck2025" "Example 7.2.2, p. 114"]
theorem geometric_series_from_one (z : ℂ) (hz : ‖z‖ < 1) :
    SeriesLimit (fun k : ℕ => z ^ k) (z / (1 - z)) := by
  have h := (hasSum_geometric_of_norm_lt_one hz).tendsto_sum_nat.const_mul z
  rw [div_eq_mul_inv]
  unfold SeriesLimit
  refine h.congr fun n => ?_
  rw [partialSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => (pow_succ' z k).symm

/-- Beck Example 7.2.3 (CX-097). The telescoping series `∑_{k ≥ 1} 1 / (k² + k) = 1`. -/
@[kb "beck2025" "Example 7.2.3, p. 114"]
theorem telescoping_series : SeriesLimit (fun k : ℕ => 1 / ((k : ℝ) ^ 2 + k)) 1 := by
  have h : ∀ n : ℕ, partialSum (fun k : ℕ => 1 / ((k : ℝ) ^ 2 + k)) n = 1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp [partialSum]
    | succ n ih =>
      have e : partialSum (fun k : ℕ => 1 / ((k : ℝ) ^ 2 + k)) (n + 1) =
          partialSum (fun k : ℕ => 1 / ((k : ℝ) ^ 2 + k)) n + 1 / (((n + 1 : ℕ) : ℝ) ^ 2 + (n + 1 : ℕ)) := by
        simp only [partialSum, Finset.sum_range_succ]
      rw [e, ih]
      push_cast
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      have : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring
  unfold SeriesLimit
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
  rw [sub_zero] at this
  exact this.congr fun n => (h n).symm

/-- Beck Corollary 7.2.4 (CX-098). A series of nonnegative real terms converges iff its partial
sums are bounded. -/
@[kb "beck2025" "Corollary 7.2.4, p. 115"]
theorem series_nonneg_converges_iff_bounded (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) :
    (∃ L, SeriesLimit b L) ↔ ∃ M : ℝ, ∀ n, partialSum b n ≤ M := by
  have hmono : Monotone (partialSum b) := by
    apply monotone_nat_of_le_succ
    intro n
    simp only [partialSum, Finset.sum_range_succ]
    linarith [hb (n + 1)]
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, fun n => hmono.ge_of_tendsto hL n⟩
  · rintro ⟨M, hM⟩
    exact ⟨_, tendsto_atTop_ciSup hmono ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩⟩

/-- Beck Example 7.2.5 (CX-098). `∑_{k ≥ 1} 1/k! = e - 1`. -/
@[kb "beck2025" "Example 7.2.5, p. 115"]
theorem sum_inv_factorial : SeriesLimit (fun k : ℕ => 1 / (k ! : ℝ)) (Real.exp 1 - 1) :=
  partialSum_inv_factorial_tendsto

/-- Beck Proposition 7.2.7 (CX-099). If a series converges, its terms tend to `0`. -/
@[kb "beck2025" "Proposition 7.2.7, p. 115"]
theorem terms_tendsto_zero (b : ℕ → ℂ) (L : ℂ) (h : SeriesLimit b L) :
    Tendsto b atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => partialSum b (n + 1) - partialSum b n) atTop (𝓝 (L - L)) :=
    (h.comp (tendsto_add_atTop_nat 1)).sub h
  rw [sub_self] at h1
  rw [← tendsto_add_atTop_iff_nat 1]
  refine h1.congr fun n => ?_
  simp [partialSum, Finset.sum_range_succ]

/-- Beck Corollary 7.2.8 (CX-099). Test for divergence: if the terms do not tend to `0`, the
series diverges. -/
@[kb "beck2025" "Corollary 7.2.8, p. 115"]
theorem divergence_test (b : ℕ → ℂ) (h : ¬ Tendsto b atTop (𝓝 0)) : ¬ ∃ L, SeriesLimit b L :=
  fun ⟨L, hL⟩ => h (terms_tendsto_zero b L hL)

/-- Beck Example 7.2.9 (CX-099). For `|z| ≥ 1`, the geometric series `∑ z^k` diverges. -/
@[kb "beck2025" "Example 7.2.9, p. 115"]
theorem geometric_series_diverges (z : ℂ) (hz : 1 ≤ ‖z‖) : ¬ ∃ L, SeriesLimit (fun k : ℕ => z ^ k) L := by
  apply divergence_test
  intro h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h 1 one_pos
  have := hN N le_rfl
  rw [dist_eq_norm, sub_zero, norm_pow] at this
  have := one_le_pow₀ hz (n := N)
  linarith

/-- Beck Example 7.2.10 (CX-100). The harmonic series diverges. -/
@[kb "beck2025" "Example 7.2.10, p. 115"]
theorem harmonic_series_diverges : ¬ ∃ L : ℝ, SeriesLimit (fun k : ℕ => 1 / (k : ℝ)) L := by
  rintro ⟨L, hL⟩
  have h := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have h2 : Tendsto (partialSum (fun k : ℕ => 1 / (k : ℝ))) atTop atTop := by
    refine h.congr fun n => ?_
    simp [partialSum]
  exact not_tendsto_nhds_of_tendsto_atTop h2 L hL

/-- Beck Proposition 7.2.11 (CX-101). Integral test, in terms of the finite integrals
`∫_1^{n+1} f`: for `f` nonnegative and nonincreasing on `[1, ∞)`,
`∫_1^{n+1} f ≤ ∑_{k=1}^n f(k)` and `∑_{k=1}^{n+1} f(k) ≤ f(1) + ∫_1^{n+1} f`. Letting `n → ∞`
gives the book's inequalities for the improper integral. -/
@[kb "beck2025" "Proposition 7.2.11, p. 115"]
theorem integral_test (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1)) (n : ℕ) :
    (∫ t in (1 : ℝ)..((n : ℝ) + 1), f t) ≤ partialSum (fun k : ℕ => f k) n ∧
    partialSum (fun k : ℕ => f k) (n + 1) ≤ f 1 + ∫ t in (1 : ℝ)..((n : ℝ) + 1), f t := by
  have hanti : AntitoneOn f (Set.Icc 1 (1 + (n : ℝ))) := hf.mono fun x hx => hx.1
  have h1 := hanti.integral_le_sum
  have h2 := hanti.sum_le_integral
  rw [add_comm (1 : ℝ) n] at h1 h2
  constructor
  · have e0 : partialSum (fun k : ℕ => f k) n = ∑ i ∈ range n, f (1 + (i : ℝ)) := by
      simp only [partialSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rw [add_comm]
    rw [e0]
    exact h1
  · have e : partialSum (fun k : ℕ => f k) (n + 1) =
        ∑ i ∈ range n, f (1 + ((i + 1 : ℕ) : ℝ)) + f 1 := by
      simp only [partialSum]
      rw [Finset.sum_range_succ']
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring_nf
    rw [e]
    linarith

/-- Beck Corollary 7.2.13 (CX-101). For `f` continuous, nonnegative and nonincreasing on `[1, ∞)`,
`∑ f(k)` converges iff `∫_1^∞ f` is finite (the integrals `∫_1^{n+1} f` stay bounded). -/
@[kb "beck2025" "Corollary 7.2.13, p. 115"]
theorem integral_test_convergence (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hnn : ∀ x, 1 ≤ x → 0 ≤ f x) :
    (∃ L, SeriesLimit (fun k : ℕ => f k) L) ↔
      ∃ M : ℝ, ∀ n : ℕ, (∫ t in (1 : ℝ)..((n : ℝ) + 1), f t) ≤ M := by
  have hnn' : ∀ k : ℕ, 0 ≤ f ((k : ℕ) : ℝ) ∨ k = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inr h
    · exact Or.inl (hnn _ (by exact_mod_cast h))
  constructor
  · rintro ⟨L, hL⟩
    have hmono : Monotone (partialSum (fun k : ℕ => f k)) := by
      apply monotone_nat_of_le_succ
      intro n
      simp only [partialSum, Finset.sum_range_succ]
      have := hnn ((n + 1 : ℕ) : ℝ) (by exact_mod_cast Nat.succ_pos n)
      linarith
    exact ⟨L, fun n => ((integral_test f hf n).1).trans (hmono.ge_of_tendsto hL n)⟩
  · rintro ⟨M, hM⟩
    have hmono : Monotone (partialSum (fun k : ℕ => f k)) := by
      apply monotone_nat_of_le_succ
      intro n
      simp only [partialSum, Finset.sum_range_succ]
      have := hnn ((n + 1 : ℕ) : ℝ) (by exact_mod_cast Nat.succ_pos n)
      linarith
    refine ⟨_, tendsto_atTop_ciSup hmono ⟨f 1 + M, ?_⟩⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := hnn 1 le_rfl
      have := hM 0
      have : (∫ t in (1 : ℝ)..(((0 : ℕ) : ℝ) + 1), f t) = 0 := by simp
      simp only [partialSum, Finset.range_zero, Finset.sum_empty]
      linarith [hnn 1 le_rfl, hM 0]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact ((integral_test f hf m).2).trans (by linarith [hM m])

/-- Beck Example 7.2.14 (CX-102). The `p`-series `∑_{k ≥ 1} 1/k^p` converges iff `p > 1`. -/
@[kb "beck2025" "Example 7.2.14, p. 116"]
theorem p_series_converges_iff (p : ℝ) :
    (∃ L, SeriesLimit (fun k : ℕ => 1 / (k : ℝ) ^ p) L) ↔ 1 < p := by
  rw [exists_seriesLimit_iff_summable (fun k => by positivity)]
  rw [summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ p) 1]
  exact Real.summable_one_div_nat_rpow

/-- Beck Theorem 7.2.16 (CX-103). An absolutely convergent series converges. -/
@[kb "beck2025" "Theorem 7.2.16, p. 116"]
theorem absolutely_convergent_converges (b : ℕ → ℂ) (h : ∃ L, SeriesLimit (fun k => ‖b k‖) L) :
    ∃ L, SeriesLimit b L := by
  rw [exists_seriesLimit_iff_summable (fun k => norm_nonneg _)] at h
  have h2 : Summable (fun k => b (k + 1)) := Summable.of_norm h
  exact ⟨_, h2.hasSum.tendsto_sum_nat⟩

/-- Beck Example 7.2.17 (CX-104). For `Re z > 1` the series `∑_{k ≥ 1} 1/k^z` converges; its
value is the Riemann zeta function. -/
@[kb "beck2025" "Example 7.2.17, p. 117"]
theorem zeta_series (z : ℂ) (hz : 1 < z.re) :
    SeriesLimit (fun k : ℕ => 1 / (k : ℂ) ^ z) (riemannZeta z) := by
  have hs : Summable (fun k : ℕ => 1 / ((k : ℕ) : ℂ) ^ z) :=
    Complex.summable_one_div_nat_cpow.2 hz
  have h2 : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ)) : ℂ) ^ z) :=
    (summable_nat_add_iff (f := fun k : ℕ => 1 / ((k : ℕ) : ℂ) ^ z) 1).2 hs
  have := h2.hasSum.tendsto_sum_nat
  push_cast at this
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hz]
  refine this.congr fun n => ?_
  simp [partialSum]

/-- Beck Example 7.2.18 (CX-105). The alternating harmonic series converges, but does not
converge absolutely. -/
@[kb "beck2025" "Example 7.2.18, p. 117"]
theorem alternating_harmonic_series :
    (∃ L : ℝ, SeriesLimit (fun k : ℕ => (-1) ^ (k + 1) / (k : ℝ)) L) ∧
    ¬ ∃ L : ℝ, SeriesLimit (fun k : ℕ => |(-1) ^ (k + 1) / (k : ℝ)|) L := by
  refine ⟨?_, ?_⟩
  · have hanti : Antitone (fun i : ℕ => 1 / ((i : ℝ) + 1)) := by
      intro i j hij
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨l, ?_⟩
    refine hl.congr fun n => ?_
    simp only [partialSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  · have : (fun k : ℕ => |(-1 : ℝ) ^ (k + 1) / (k : ℝ)|) = fun k : ℕ => 1 / (k : ℝ) := by
      funext k
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
    rw [this]
    exact harmonic_series_diverges

/-! ### Section 7.3 -/

/-- Beck Definition 7.3.1 (CX-106). Pointwise and uniform convergence of `f n : G → ℂ` to `F`,
in the epsilon-`N` form. -/
@[kb "beck2025" "Definition 7.3.1, p. 118"]
theorem pointwise_uniform_convergence_iff (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (G : Set ℂ) :
    (TendstoUniformlyOn f F atTop G ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ G, ‖f n z - F z‖ < ε) ∧
    ((∀ z ∈ G, Tendsto (fun n => f n z) atTop (𝓝 (F z))) ↔
      ∀ z ∈ G, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖f n z - F z‖ < ε) := by
  constructor
  · simp only [Metric.tendstoUniformlyOn_iff, eventually_atTop, dist_eq_norm, norm_sub_rev (F _)]
  · refine forall₂_congr fun z _ => ?_
    simp [Metric.tendsto_atTop, dist_eq_norm]

/-- Beck Example 7.3.2 (CX-106). The functions `z^n` converge pointwise to `0` on the open unit
disk. -/
@[kb "beck2025" "Example 7.3.2, p. 118"]
theorem pow_pointwise_unit_disk :
    ∀ z ∈ ball (0 : ℂ) 1, Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0) := by
  intro z hz
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using hz)

/-- Beck Example 7.3.3 (CX-106). The functions `z^n` converge uniformly to `0` on the disk of
radius `1/2`. -/
@[kb "beck2025" "Example 7.3.3, p. 118"]
theorem pow_uniform_half_disk :
    TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => z ^ n) (fun _ => 0) atTop (ball (0 : ℂ) (1 / 2)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [h.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_eq_norm, zero_sub, norm_neg, norm_pow]
  have hz' : ‖z‖ ≤ 1 / 2 := by simpa using (mem_ball_zero_iff.1 hz).le
  exact (pow_le_pow_left₀ (norm_nonneg z) hz' n).trans_lt hn

/-- Beck Proposition 7.3.4 (CX-107). A uniform limit of continuous functions is continuous. -/
@[kb "beck2025" "Proposition 7.3.4, p. 119"]
theorem uniform_limit_continuous (G : Set ℂ) (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hc : ∀ n, ContinuousOn (f n) G) (hu : TendstoUniformlyOn f F atTop G) : ContinuousOn F G :=
  hu.continuousOn (Eventually.of_forall hc).frequently

/-- Beck Example 7.3.5 (CX-107). On `[0, 1]` the functions `x^n` converge pointwise to the
discontinuous function that is `0` on `[0, 1)` and `1` at `1`, so the convergence is not
uniform. -/
@[kb "beck2025" "Example 7.3.5, p. 119"]
theorem x_pow_not_uniform :
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 (if x = 1 then 1 else 0))) ∧
    ¬ ContinuousOn (fun x : ℝ => if x = 1 then (1 : ℝ) else 0) (Set.Icc 0 1) ∧
    ¬ TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => x ^ n) (fun x : ℝ => if x = 1 then (1 : ℝ) else 0)
      atTop (Set.Icc 0 1) := by
  have hdisc : ¬ ContinuousOn (fun x : ℝ => if x = 1 then (1 : ℝ) else 0) (Set.Icc 0 1) := by
    intro hc
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1 (hc 1 h1) (1 / 2) (by norm_num)
    set x : ℝ := max 0 (1 - δ / 2) with hx
    have hx0 : 0 ≤ x := le_max_left _ _
    have hx1 : x < 1 := max_lt zero_lt_one (by linarith)
    have hxd : dist x 1 < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have : 1 - δ / 2 ≤ x := le_max_right _ _
      linarith
    have := h ⟨hx0, hx1.le⟩ hxd
    simp [hx1.ne, Real.dist_eq] at this
    norm_num at this
  refine ⟨fun x hx => ?_, hdisc, fun hu => hdisc ?_⟩
  · by_cases h : x = 1
    · simp [h]
    · simp only [h, ite_false]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hx.1 (lt_of_le_of_ne hx.2 h)
  · exact hu.continuousOn (Eventually.of_forall fun n => (continuous_pow n).continuousOn).frequently

/-- Beck Proposition 7.3.7 (CX-109). Weierstrass M-test: if `|f_k| ≤ M_k` on `G` and `∑ M_k`
converges, then `∑ f_k` and `∑ |f_k|` converge uniformly on `G`. -/
@[kb "beck2025" "Proposition 7.3.7, p. 119"]
theorem weierstrass_M_test (G : Set ℂ) (f : ℕ → ℂ → ℂ) (M : ℕ → ℝ)
    (hfM : ∀ k, ∀ z ∈ G, ‖f k z‖ ≤ M k) (hM : ∃ L, SeriesLimit M L) :
    (∃ F, TendstoUniformlyOn (fun n z => partialSum (fun k => f k z) n) F atTop G) ∧
    (∃ F, TendstoUniformlyOn (fun n z => partialSum (fun k => ‖f k z‖) n) F atTop G) := by
  rcases G.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨⟨0, tendstoUniformlyOn_empty⟩, ⟨0, tendstoUniformlyOn_empty⟩⟩
  have hM0 : ∀ k, 0 ≤ M k := fun k => (norm_nonneg _).trans (hfM k z₀ hz₀)
  have hs := (exists_seriesLimit_iff_summable hM0).1 hM
  exact ⟨⟨_, tendstoUniformlyOn_tsum_nat (f := fun n z => f (n + 1) z) hs
      (fun n x hx => hfM (n + 1) x hx)⟩,
    ⟨_, tendstoUniformlyOn_tsum_nat (f := fun n z => ‖f (n + 1) z‖) hs
      (fun n x hx => by simpa using hfM (n + 1) x hx)⟩⟩

/-- Beck Example 7.3.8 (CX-110). For `0 < r < 1`, the geometric series `∑_{k ≥ 1} z^k` converges
uniformly to `z / (1 - z)` for `|z| ≤ r`. -/
@[kb "beck2025" "Example 7.3.8, p. 120"]
theorem geometric_series_uniform (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => partialSum (fun k => z ^ k) n)
      (fun z => z / (1 - z)) atTop (closedBall 0 r) := by
  have hM : ∃ L, SeriesLimit (fun k : ℕ => r ^ k) L := by
    rw [exists_seriesLimit_iff_summable (fun k => by positivity)]
    exact (summable_geometric_of_lt_one hr0.le hr1).comp_injective (add_left_injective 1)
  obtain ⟨F, hF⟩ := (weierstrass_M_test (closedBall 0 r) (fun k z => z ^ k) (fun k => r ^ k)
    (fun k z hz => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg z) (by simpa using hz) k) hM).1
  refine hF.congr_right fun z hz => ?_
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt (by simpa using hz) hr1
  exact tendsto_nhds_unique (hF.tendsto_at hz) (geometric_series_from_one z hz1)

/-! ### Section 7.4 -/

/-- Beck Example 7.4.2 (CX-110). The geometric series `∑_{k ≥ 0} z^k` equals `1 / (1 - z)` and
converges absolutely for `|z| < 1`, uniformly for `|z| ≤ r < 1`, and diverges for `|z| ≥ 1`. -/
@[kb "beck2025" "Example 7.4.2, p. 121"]
theorem geometric_series_from_zero :
    (∀ z : ℂ, ‖z‖ < 1 → HasSum (fun k : ℕ => z ^ k) (1 / (1 - z)) ∧
      Summable (fun k : ℕ => ‖z ^ k‖)) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 →
      TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => ∑ k ∈ range n, z ^ k) (fun z => 1 / (1 - z))
        atTop (closedBall 0 r)) ∧
    (∀ z : ℂ, 1 ≤ ‖z‖ → ¬ ∃ L, Tendsto (fun n : ℕ => ∑ k ∈ range n, z ^ k) atTop (𝓝 L)) := by
  refine ⟨fun z hz => ⟨?_, ?_⟩, fun r hr0 hr1 => ?_, fun z hz => ?_⟩
  · simpa [one_div] using hasSum_geometric_of_norm_lt_one hz
  · simpa using summable_geometric_of_lt_one (norm_nonneg z) hz
  · have hu := summable_geometric_of_lt_one hr0 hr1
    have h := tendstoUniformlyOn_tsum_nat (f := fun (k : ℕ) (z : ℂ) => z ^ k) (s := closedBall 0 r) hu
      (fun k z hz => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg z) (by simpa using hz) k)
    refine h.congr_right fun z hz => ?_
    have hz1 : ‖z‖ < 1 := lt_of_le_of_lt (by simpa using hz) hr1
    simp [tsum_geometric_of_norm_lt_one hz1, one_div]
  · rintro ⟨L, hL⟩
    apply geometric_series_diverges z hz
    refine ⟨L - 1, ?_⟩
    have := (hL.comp (tendsto_add_atTop_nat 1)).sub_const 1
    refine this.congr fun n => ?_
    simp only [Function.comp, partialSum]
    rw [Finset.sum_range_succ' (fun k => z ^ k) n]
    simp [pow_zero]

/-- The radius of convergence of the power series `∑ c_k (z - z₀)^k` (it does not depend on `z₀`). -/
noncomputable def radiusOfConvergence (c : ℕ → ℂ) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars ℂ c).radius

lemma terms_tendsto_zero_of_partial_sums {t : ℕ → ℂ} {L : ℂ}
    (h : Tendsto (fun n => ∑ k ∈ range n, t k) atTop (𝓝 L)) : Tendsto t atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ∑ k ∈ range (n + 1), t k - ∑ k ∈ range n, t k) atTop (𝓝 (L - L)) :=
    (h.comp (tendsto_add_atTop_nat 1)).sub h
  rw [sub_self] at h1
  refine h1.congr fun n => ?_
  simp [Finset.sum_range_succ]

/-- Beck Theorem 7.4.3 and Definition 7.4.4 (CX-112). For the power series `∑_{k ≥ 0} c_k (z - z₀)^k`
there is a radius of convergence `R ∈ [0, ∞]` such that the series converges absolutely for
`|z - z₀| < R`, absolutely and uniformly for `|z - z₀| ≤ r < R`, and diverges for `|z - z₀| > R`. -/
@[kb "beck2025" "Theorem 7.4.3, p. 121"]
theorem radius_of_convergence (c : ℕ → ℂ) (z₀ : ℂ) :
    ∃ R : ℝ≥0∞,
      (∀ z : ℂ, (‖z - z₀‖₊ : ℝ≥0∞) < R → Summable (fun k => ‖c k * (z - z₀) ^ k‖)) ∧
      (∀ r : ℝ≥0, (r : ℝ≥0∞) < R →
        (∃ F, TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => ∑ k ∈ range n, c k * (z - z₀) ^ k) F atTop
          (closedBall z₀ r)) ∧
        (∃ F, TendstoUniformlyOn (fun (n : ℕ) (z : ℂ) => ∑ k ∈ range n, ‖c k * (z - z₀) ^ k‖) F
          atTop (closedBall z₀ r))) ∧
      (∀ z : ℂ, R < (‖z - z₀‖₊ : ℝ≥0∞) →
        ¬ ∃ L, Tendsto (fun n : ℕ => ∑ k ∈ range n, c k * (z - z₀) ^ k) atTop (𝓝 L)) := by
  set p := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hnorm : ∀ k, ‖p k‖ = ‖c k‖ := fun k => FormalMultilinearSeries.ofScalars_norm ℂ c k
  refine ⟨radiusOfConvergence c, ?_, ?_, ?_⟩
  · intro z hz
    have := p.summable_norm_mul_pow hz
    simpa [hnorm, norm_mul, norm_pow] using this
  · intro r hr
    have hu : Summable (fun k => ‖c k‖ * (r : ℝ) ^ k) := by
      simpa [hnorm] using p.summable_norm_mul_pow hr
    have hb : ∀ k, ∀ z ∈ closedBall z₀ (r : ℝ), ‖c k * (z - z₀) ^ k‖ ≤ ‖c k‖ * (r : ℝ) ^ k := by
      intro k z hz
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using hz) k) (norm_nonneg _)
    exact ⟨⟨_, tendstoUniformlyOn_tsum_nat (f := fun k z => c k * (z - z₀) ^ k) hu hb⟩,
      ⟨_, tendstoUniformlyOn_tsum_nat (f := fun k z => ‖c k * (z - z₀) ^ k‖) hu
        (fun k z hz => by simpa using hb k z hz)⟩⟩
  · intro z hz ⟨L, hL⟩
    have ht := terms_tendsto_zero_of_partial_sums hL
    have h2 : Tendsto (fun n => ‖p n‖ * (‖z - z₀‖₊ : ℝ) ^ n) atTop (𝓝 0) := by
      have := ht.norm
      simpa [hnorm, norm_mul, norm_pow] using this
    exact absurd (p.le_radius_of_tendsto h2) (not_le.2 hz)

/-- Beck Proposition 7.4.5 (CX-113). If a power series converges at `w`, it converges
absolutely at every `z` closer to the center. -/
@[kb "beck2025" "Proposition 7.4.5, p. 121"]
theorem converges_at_w_implies_absolute (c : ℕ → ℂ) (z₀ w : ℂ)
    (h : ∃ L, Tendsto (fun n : ℕ => ∑ k ∈ range n, c k * (w - z₀) ^ k) atTop (𝓝 L)) :
    ∀ z : ℂ, ‖z - z₀‖ < ‖w - z₀‖ → Summable (fun k => ‖c k * (z - z₀) ^ k‖) := by
  obtain ⟨L, hL⟩ := h
  set p := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hnorm : ∀ k, ‖p k‖ = ‖c k‖ := fun k => FormalMultilinearSeries.ofScalars_norm ℂ c k
  have ht := (terms_tendsto_zero_of_partial_sums hL).norm
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  have hle : (‖w - z₀‖₊ : ℝ≥0∞) ≤ p.radius := by
    refine p.le_radius_of_bound C fun n => ?_
    have := hC ⟨n, rfl⟩
    simpa [hnorm, norm_mul, norm_pow] using this
  intro z hz
  have hlt : (‖z - z₀‖₊ : ℝ≥0∞) < p.radius :=
    lt_of_lt_of_le (by exact_mod_cast hz) hle
  have := p.summable_norm_mul_pow hlt
  simpa [hnorm, norm_mul, norm_pow] using this

/-- Beck Corollary 7.4.9 (CX-115). A power series is continuous on its disk of convergence. -/
@[kb "beck2025" "Corollary 7.4.9, p. 123"]
theorem power_series_continuousOn (c : ℕ → ℂ) (z₀ : ℂ) :
    ContinuousOn (fun z => ∑' k, c k * (z - z₀) ^ k)
      {z : ℂ | (‖z - z₀‖₊ : ℝ≥0∞) < radiusOfConvergence c} := by
  set p := FormalMultilinearSeries.ofScalars ℂ c with hp
  have h := p.continuousOn
  have h2 : ContinuousOn (fun z : ℂ => p.sum (z - z₀))
      {z : ℂ | (‖z - z₀‖₊ : ℝ≥0∞) < radiusOfConvergence c} := by
    refine h.comp (continuous_sub_right z₀).continuousOn fun z hz => ?_
    rw [Metric.mem_eball, edist_zero_right]
    exact hz
  refine h2.congr fun z _ => ?_
  show _ = ∑' n, (FormalMultilinearSeries.ofScalars ℂ c n) fun _ => z - z₀
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-! ### Section 7.5 -/

/-- Beck, Squeeze Theorem (CX-117), exercises of Chapter 7. If `a_n ≤ b_n ≤ c_n` and `a_n`, `c_n`
tend to `L`, then so does `b_n`. -/
@[kb "beck2025" "Squeeze Theorem §7.5, p. 125"]
theorem squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ) (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : Tendsto a atTop (𝓝 L)) (hc : Tendsto c atTop (𝓝 L)) : Tendsto b atTop (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hc hab hbc

end UndergradKB.ComplexAnalysis.Course.Beck7
