import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Probability: Little's law along a sample path (Grinstead–Snell Example 6.29)

Wave 7, a recorded loose end.  The book uses Little's law `N = λT` (mean number in the system equals the arrival
rate times the mean time in the system) without proof, citing Ross.  Here the law is proved for one sample path of
any queue (the deterministic form of Stidham): customer `i` arrives at time `a i` (nondecreasing, `a 0 ≥ 0`) and
stays `w i ≥ 0` in the system; `queueNumber a w t` is the number in the system at time `t`.

* `integral_queueNumber_bounds`: with `m` the number of arrivals by time `T`, the area `∫_0^T N(t) dt` is at most
  the total time `∑_{i<m} w_i` of these customers, and at least the total time of any first `m'` customers who
  have all left by time `T`.
* `little_law_sample_path`: if the arrival rate `λ = lim n / a_n > 0` and the mean time in the system
  `W = lim (w_0 + ⋯ + w_{n-1})/n` exist, then the time average `(1/T) ∫_0^T N(t) dt` tends to `λ W`.

For the book's queue the two limits exist almost surely (the strong law of large numbers for the arrivals and the
regenerative structure of the queue); that step needs the queue process, which is not built here
(a recorded loose end). -/

open Finset Filter Topology MeasureTheory Set

namespace UndergradKB.Probability

/-- The number of customers in the system at time `t`: those `i` with `a i ≤ t < a i + w i`. -/
noncomputable def queueNumber (a w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' i, (Ico (a i) (a i + w i)).indicator (1 : ℝ → ℝ) t

theorem queueNumber_eq_sum (a w : ℕ → ℝ) (ha : Monotone a) {T t : ℝ} {n : ℕ} (hn : T < a n)
    (ht : t ≤ T) :
    queueNumber a w t = ∑ i ∈ range n, (Ico (a i) (a i + w i)).indicator (1 : ℝ → ℝ) t := by
  unfold queueNumber
  apply tsum_eq_sum
  intro i hi
  have hni : n ≤ i := by simpa using hi
  have : T < a i := hn.trans_le (ha hni)
  exact indicator_of_notMem (fun h => by linarith [h.1]) _

theorem integral_indicator_Ico_le {p q T : ℝ} (hpq : p ≤ q) :
    ∫ t in Ioc 0 T, (Ico p q).indicator (1 : ℝ → ℝ) t ≤ q - p := by
  rw [integral_indicator_one measurableSet_Ico, Measure.real_def,
    Measure.restrict_apply measurableSet_Ico]
  have h : volume (Ico p q ∩ Ioc 0 T) ≤ volume (Ico p q) := measure_mono inter_subset_left
  rw [Real.volume_Ico] at h
  calc _ ≤ (ENNReal.ofReal (q - p)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = q - p := ENNReal.toReal_ofReal (by linarith)

theorem integral_indicator_Ico_nonneg (p q T : ℝ) :
    0 ≤ ∫ t in Ioc 0 T, (Ico p q).indicator (1 : ℝ → ℝ) t :=
  integral_nonneg fun t => indicator_nonneg (fun _ _ => zero_le_one) t

theorem integral_indicator_Ico_eq {p q T : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hqT : q ≤ T) :
    ∫ t in Ioc 0 T, (Ico p q).indicator (1 : ℝ → ℝ) t = q - p := by
  refine le_antisymm (integral_indicator_Ico_le hpq) ?_
  rw [integral_indicator_one measurableSet_Ico, Measure.real_def,
    Measure.restrict_apply measurableSet_Ico]
  have h : volume (Ioo p q) ≤ volume (Ico p q ∩ Ioc 0 T) := by
    apply measure_mono
    intro t ht
    exact ⟨⟨ht.1.le, ht.2⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hfin : volume (Ico p q ∩ Ioc 0 T) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
  rw [Real.volume_Ioo] at h
  calc q - p = (ENNReal.ofReal (q - p)).toReal := (ENNReal.toReal_ofReal (by linarith)).symm
    _ ≤ _ := ENNReal.toReal_mono hfin h

/-- The area under the queue-length curve up to time `T ≥ 0` is a finite sum over the customers who arrived by
time `T` (any `n` with `T < a n` bounds them). -/
theorem integral_queueNumber_eq_sum (a w : ℕ → ℝ) (ha : Monotone a) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (hn : T < a n) :
    ∫ t in (0 : ℝ)..T, queueNumber a w t =
      ∑ i ∈ range n, ∫ t in Ioc 0 T, (Ico (a i) (a i + w i)).indicator (1 : ℝ → ℝ) t := by
  rw [intervalIntegral.integral_of_le hT]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun t ht => queueNumber_eq_sum a w ha hn ht.2)]
  apply integral_finsetSum
  intro i _
  exact (integrableOn_const (C := (1 : ℝ)) (by simp)).indicator measurableSet_Ico

/-- Bounds for the area under the queue-length curve.  Let `T ≥ 0` and let `n` be such that `T < a n`, so
that only customers `0, …, n-1` arrive by time `T`.  Then `∫_0^T N(t) dt ≤ ∑_{i<n} w_i`, and for any `m'` such
that customers `0, …, m'-1` have all left by time `T`, `∑_{i<m'} w_i ≤ ∫_0^T N(t) dt`. -/
theorem integral_queueNumber_bounds (a w : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0)
    (hw : ∀ i, 0 ≤ w i) {T : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : T < a n) :
    ∫ t in (0 : ℝ)..T, queueNumber a w t ≤ ∑ i ∈ range n, w i ∧
    ∀ m', (∀ i < m', a i + w i ≤ T) → ∑ i ∈ range m', w i ≤ ∫ t in (0 : ℝ)..T, queueNumber a w t := by
  rw [integral_queueNumber_eq_sum a w ha hT hn]
  refine ⟨sum_le_sum fun i _ => ?_, fun m' hm' => ?_⟩
  · have := integral_indicator_Ico_le (T := T) (le_add_of_nonneg_right (hw i)) (p := a i)
    linarith
  · have hm'n : m' ≤ n := by
      by_contra h
      push Not at h
      have := hm' n h
      linarith [hw n]
    calc ∑ i ∈ range m', w i
        = ∑ i ∈ range m', ∫ t in Ioc 0 T, (Ico (a i) (a i + w i)).indicator (1 : ℝ → ℝ) t := by
          refine sum_congr rfl fun i hi => ?_
          rw [integral_indicator_Ico_eq (ha0.trans (ha (Nat.zero_le i)))
            (le_add_of_nonneg_right (hw i)) (hm' i (by simpa using hi))]
          ring
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hm'n)
          fun i _ _ => integral_indicator_Ico_nonneg _ _ _

/-- Arrival times with a positive arrival rate `λ = lim n / a_n` are eventually positive and at least
`n / (2λ)`. -/
theorem arrivals_eventually_ge (a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) {lam : ℝ} (hlam : 0 < lam)
    (hA : Tendsto (fun n : ℕ => (n : ℝ) / a n) atTop (𝓝 lam)) :
    ∀ᶠ n in atTop, 0 < a n ∧ (n : ℝ) / (2 * lam) < a n := by
  have h := hA.eventually (Ioo_mem_nhds (show lam / 2 < lam by linarith)
    (show lam < 2 * lam by linarith))
  filter_upwards [h] with n hn
  have han : 0 ≤ a n := ha0.trans (ha (Nat.zero_le n))
  have hpos : 0 < a n := by
    rcases han.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', div_zero] at hn; linarith [hn.1]
  refine ⟨hpos, ?_⟩
  have := hn.2
  rw [div_lt_iff₀ hpos] at this
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- The time in the system of customer `n` is small compared to `n`: `w_n / (n+1) → 0`. -/
theorem sojourn_div_tendsto_zero (w : ℕ → ℝ) {W : ℝ}
    (hW : Tendsto (fun n : ℕ => (∑ i ∈ range n, w i) / n) atTop (𝓝 W)) :
    Tendsto (fun n : ℕ => w n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (∑ i ∈ range (n + 1), w i) / ((n : ℝ) + 1)) atTop (𝓝 W) := by
    have := (tendsto_add_atTop_iff_nat 1).2 hW
    simpa using this
  have h2 : Tendsto (fun n : ℕ => (∑ i ∈ range n, w i) / n * ((n : ℝ) / (n + 1))) atTop (𝓝 (W * 1)) :=
    hW.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  rw [mul_one] at h2
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [sum_range_succ]
  field_simp
  ring

/-- Grinstead–Snell Example 6.29 (PR-209), Little's law `N = λT` along a sample path.  Customer `i` arrives at
time `a i` (nondecreasing, `a 0 ≥ 0`) and stays `w i ≥ 0` in the system; `N(t)` is the number in the system at
time `t`.  If the arrival rate `λ = lim_n n / a_n` exists and is positive and the mean time in the system
`W = lim_n (w_0 + ⋯ + w_{n-1})/n` exists, then the mean number in the system `lim_T (1/T) ∫_0^T N(t) dt` exists
and equals `λ W`.  (The book uses this law without proof; this is the deterministic form of the law due to
Stidham.) -/
@[kb "grinsteadsnell2006" "Example 6.29, p. 283"]
theorem little_law_sample_path (a w : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0) (hw : ∀ i, 0 ≤ w i)
    {lam W : ℝ} (hlam : 0 < lam)
    (hA : Tendsto (fun n : ℕ => (n : ℝ) / a n) atTop (𝓝 lam))
    (hW : Tendsto (fun n : ℕ => (∑ i ∈ range n, w i) / n) atTop (𝓝 W)) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, queueNumber a w t) / T) atTop (𝓝 (lam * W)) := by
  set S : ℕ → ℝ := fun n => ∑ i ∈ range n, w i with hS
  have hev := arrivals_eventually_ge a ha ha0 hlam hA
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  -- the arrival times are unbounded
  have hunb : ∀ T : ℝ, ∃ n, T < a n := by
    intro T
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * lam * T)
    refine ⟨max k N0, ?_⟩
    have h := (hN0 (max k N0) (le_max_right _ _)).2
    have hk' : (k : ℝ) ≤ (max k N0 : ℕ) := by exact_mod_cast le_max_left k N0
    have : T < ((max k N0 : ℕ) : ℝ) / (2 * lam) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  classical
  -- `m T`: the number of arrivals by time `T`
  set m : ℝ → ℕ := fun T => Nat.find (hunb T) with hm
  have hm1 : ∀ T, T < a (m T) := fun T => Nat.find_spec (hunb T)
  have hm2 : ∀ T i, i < m T → a i ≤ T := fun T i hi => not_lt.1 (Nat.find_min (hunb T) hi)
  have hmt : Tendsto m atTop atTop := by
    refine tendsto_atTop_atTop.2 fun N => ⟨a N, fun T hT => ?_⟩
    by_contra h
    push Not at h
    have := hm1 T
    linarith [ha h.le]
  -- `m T / T → λ`
  have hmT : Tendsto (fun T => (m T : ℝ) / T) atTop (𝓝 lam) := by
    have hlow : Tendsto (fun T => (m T : ℝ) / a (m T)) atTop (𝓝 lam) := hA.comp hmt
    have hatop : Tendsto a atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_
        (tendsto_natCast_atTop_atTop.atTop_div_const (show 0 < 2 * lam by positivity))
      filter_upwards [hev] with n hn using hn.2.le
    have hg : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / a n) atTop (𝓝 lam) := by
      have : Tendsto (fun n : ℕ => (n : ℝ) / a n + 1 / a n) atTop (𝓝 (lam + 0)) :=
        hA.add (by simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hatop)
      rw [add_zero] at this
      refine this.congr fun n => ?_
      push_cast
      ring
    have hup : Tendsto (fun T => (m T : ℝ) / a (m T - 1)) atTop (𝓝 lam) := by
      have := hg.comp (tendsto_sub_atTop_nat 1 |>.comp hmt)
      refine this.congr' ?_
      filter_upwards [hmt.eventually (eventually_ge_atTop 1)] with T hT
      simp only [Function.comp]
      congr 2
      omega
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hmt.eventually (eventually_ge_atTop N0), eventually_gt_atTop 0] with T hT hT0
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hT0 (hm1 T).le
    · filter_upwards [hmt.eventually (eventually_ge_atTop (N0 + 1)), eventually_gt_atTop 0] with T hT hT0
      have hpos := (hN0 (m T - 1) (by omega)).1
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos (hm2 T _ (by omega))
  -- `S (m T) / T → λ W`
  have hf : Tendsto (fun T => S (m T) / T) atTop (𝓝 (lam * W)) := by
    have := (hW.comp hmt).mul hmT
    rw [mul_comm W lam] at this
    refine this.congr' ?_
    filter_upwards [hmt.eventually (eventually_ge_atTop 1)] with T hT
    have : (m T : ℝ) ≠ 0 := by exact_mod_cast (show m T ≠ 0 by omega)
    simp only [Function.comp, hS]
    field_simp
  -- `W ≥ 0`
  have hW0 : 0 ≤ W := ge_of_tendsto' hW fun n => div_nonneg (sum_nonneg fun i _ => hw i) (Nat.cast_nonneg _)
  -- the time in the system is eventually small compared to the arrival time
  have hsmall : ∀ δ > 0, ∀ᶠ n in atTop, w n ≤ δ * a n := by
    intro δ hδ
    have h := (sojourn_div_tendsto_zero w hW).eventually
      (gt_mem_nhds (show (0 : ℝ) < δ / (4 * lam) by positivity))
    filter_upwards [h, hev, eventually_ge_atTop 1] with n hn hn' h1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    rw [div_lt_iff₀ (by positivity)] at hn
    have : (n : ℝ) / (2 * lam) * δ ≤ a n * δ := mul_le_mul_of_nonneg_right hn'.2.le hδ.le
    have e : δ / (4 * lam) * ((n : ℝ) + 1) ≤ (n : ℝ) / (2 * lam) * δ := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hdl := mul_pos hδ hlam
      nlinarith [mul_le_mul_of_nonneg_left hn1 hdl.le]
    linarith
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro b hb
    obtain ⟨c, hc0, hc1, hcb⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ b < c * (lam * W) := by
      rcases lt_or_ge b 0 with hb0 | hb0
      · exact ⟨1 / 2, by norm_num, by norm_num, by nlinarith [mul_nonneg hlam.le hW0]⟩
      · have hLW : 0 < lam * W := lt_of_le_of_lt hb0 hb
        refine ⟨(1 + b / (lam * W)) / 2, by positivity, ?_, ?_⟩
        · have : b / (lam * W) < 1 := (div_lt_one hLW).2 hb
          linarith
        · have : b / (lam * W) * (lam * W) = b := div_mul_cancel₀ _ hLW.ne'
          have e : (1 + b / (lam * W)) / 2 * (lam * W) = (lam * W + b / (lam * W) * (lam * W)) / 2 := by
            ring
          rw [e, this]; linarith
    have hfc : Tendsto (fun T => c * (S (m (c * T)) / (c * T))) atTop (𝓝 (c * (lam * W))) :=
      (hf.comp (tendsto_id.const_mul_atTop hc0)).const_mul c
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hsmall ((1 - c) / c) (by
      have : 0 < 1 - c := by linarith
      positivity))
    set M := ∑ i ∈ range N1, (a i + w i) with hM
    filter_upwards [hfc.eventually (lt_mem_nhds hcb), eventually_gt_atTop (max M 0)] with T hT hTM
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right _ _) hTM
    have hTM' : M < T := lt_of_le_of_lt (le_max_left _ _) hTM
    have heq : c * (S (m (c * T)) / (c * T)) = S (m (c * T)) / T := by
      field_simp
    rw [heq] at hT
    refine lt_of_lt_of_le hT (div_le_div_of_nonneg_right ?_ hT0.le)
    refine (integral_queueNumber_bounds a w ha ha0 hw hT0.le (hm1 T)).2 _ fun i hi => ?_
    have hai : a i ≤ c * T := hm2 _ i hi
    rcases lt_or_ge i N1 with hiN | hiN
    · have : a i + w i ≤ M :=
        single_le_sum (f := fun i => a i + w i)
          (fun j _ => add_nonneg (ha0.trans (ha (Nat.zero_le j))) (hw j)) (mem_range.2 hiN)
      linarith
    · have hwi := hN1 i hiN
      have : (1 - c) / c * a i ≤ (1 - c) / c * (c * T) :=
        mul_le_mul_of_nonneg_left hai (div_nonneg (by linarith) hc0.le)
      have e : (1 - c) / c * (c * T) = (1 - c) * T := by field_simp
      linarith
  · -- upper bound
    intro b hb
    filter_upwards [hf.eventually (gt_mem_nhds hb), eventually_gt_atTop 0] with T hT hT0
    refine lt_of_le_of_lt (div_le_div_of_nonneg_right ?_ hT0.le) hT
    exact (integral_queueNumber_bounds a w ha ha0 hw hT0.le (hm1 T)).1

end UndergradKB.Probability
