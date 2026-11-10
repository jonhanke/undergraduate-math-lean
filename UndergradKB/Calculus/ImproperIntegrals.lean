import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import UndergradKB.Common.Attr

/-! # Calculus: improper integrals

OpenStax Calculus 2 §3.7. The book defines `∫_a^∞ f` as the limit of `∫_a^t f` as `t → ∞`; Mathlib's `∫ x in Ioi a`
is a Lebesgue integral. For nonnegative continuous integrands the two notions agree: the limit exists iff `f` is
integrable on `Ioi a`. -/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace UndergradKB.Calculus

/-- OpenStax Calculus 2:§3.7 Definition (CA-241): if `f` is integrable on `(a,∞)` then `∫_a^t f → ∫_{(a,∞)} f`
as `t → ∞`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Definition (infinite intervals, Eq. 3.16-3.18), p. 296"]
theorem tendsto_intervalIntegral_of_integrableOn_Ioi {f : ℝ → ℝ} {a : ℝ}
    (hf : IntegrableOn f (Ioi a)) :
    Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 (∫ x in Ioi a, f x)) :=
  intervalIntegral_tendsto_integral_Ioi a hf tendsto_id

/-- OpenStax Calculus 2:§3.7 Definition (CA-241): for a nonnegative `f` continuous on `[a,∞)`, the improper
integral converges in the book's sense (the limit of `∫_a^t f` as `t → ∞` exists) iff `f` is integrable on
`(a,∞)`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Definition (infinite intervals, Eq. 3.16-3.18), p. 296"]
theorem converges_Ioi_iff_integrableOn {f : ℝ → ℝ} {a : ℝ} (hc : ContinuousOn f (Ici a))
    (hnn : ∀ x, a ≤ x → 0 ≤ f x) :
    (∃ L, Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 L)) ↔ IntegrableOn f (Ioi a) := by
  constructor
  · rintro ⟨L, hL⟩
    have hint : ∀ s t, a ≤ s → s ≤ t → IntervalIntegrable f volume s t := fun s t hs hst =>
      (hc.mono (fun x hx => le_trans hs (by rw [uIcc_of_le hst] at hx; exact hx.1))).intervalIntegrable
    have hint' : ∀ t, a ≤ t → IntervalIntegrable f volume a t := fun t ht => hint a t le_rfl ht
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded L a (b := fun t => max t a)
      (l := atTop) ?_ (tendsto_atTop_mono (fun t => le_max_left _ _) tendsto_id) ?_
    · intro t
      have := (hint' (max t a) (le_max_right _ _)).1
      exact this
    · filter_upwards [eventually_ge_atTop a] with t ht
      have e : max t a = t := max_eq_left ht
      have h1 : ∫ x in a..t, ‖f x‖ = ∫ x in a..t, f x :=
        integral_congr fun x hx => by
          rw [uIcc_of_le ht] at hx
          exact Real.norm_of_nonneg (hnn x hx.1)
      simp only [e]
      rw [h1]
      refine ge_of_tendsto hL ?_
      filter_upwards [eventually_ge_atTop t] with s hs
      rw [← integral_add_adjacent_intervals (hint' t ht) (hint t s ht hs)]
      have : 0 ≤ ∫ x in t..s, f x := intervalIntegral.integral_nonneg hs
        fun x hx => hnn x (le_trans ht hx.1)
      linarith
  · intro h
    exact ⟨_, tendsto_intervalIntegral_of_integrableOn_Ioi h⟩

/-- OpenStax Calculus 2:§3.7 comparison theorem for improper integrals (CA-243 family), in the book's limit
sense: if `0 ≤ f ≤ g` on `[a,∞)`, both continuous, and `∫_a^t g` has a limit as `t → ∞`, then so does `∫_a^t f`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Theorem 3.7 (comparison test), p. 306"]
theorem converges_of_le_of_converges {f g : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (hg : ContinuousOn g (Ici a)) (h0 : ∀ x, a ≤ x → 0 ≤ f x) (hfg : ∀ x, a ≤ x → f x ≤ g x)
    (hconv : ∃ L, Tendsto (fun t => ∫ x in a..t, g x) atTop (𝓝 L)) :
    ∃ L, Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 L) := by
  rw [converges_Ioi_iff_integrableOn hg (fun x hx => (h0 x hx).trans (hfg x hx))] at hconv
  rw [converges_Ioi_iff_integrableOn hf h0]
  refine hconv.mono' (hf.mono Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_of_nonneg (h0 x (le_of_lt hx))]
  exact hfg x (le_of_lt hx)

/-- Divergence half of the comparison theorem: if `0 ≤ f ≤ g` and `∫_a^t f` has no limit, then `∫_a^t g` has
none. -/
@[kb "openstaxcalculus2016" "2:§3.7 Theorem 3.7 (comparison test), p. 306"]
theorem diverges_of_le_of_diverges {f g : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (hg : ContinuousOn g (Ici a)) (h0 : ∀ x, a ≤ x → 0 ≤ f x) (hfg : ∀ x, a ≤ x → f x ≤ g x)
    (hdiv : ¬ ∃ L, Tendsto (fun t => ∫ x in a..t, f x) atTop (𝓝 L)) :
    ¬ ∃ L, Tendsto (fun t => ∫ x in a..t, g x) atTop (𝓝 L) :=
  fun h => hdiv (converges_of_le_of_converges hf hg h0 hfg h)

private lemma continuousOn_rpow_Ici {a : ℝ} (ha : 0 < a) (s : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ s) (Ici a) :=
  continuousOn_id.rpow_const fun _ hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx))

/-- OpenStax Calculus 2:§3.7 (CA-243), `p`-test at infinity: `∫_1^t x^(-p)` has a limit as `t → ∞` iff `p > 1`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Example 3.56 (p-integral), p. 306"]
theorem converges_Ioi_one_rpow_iff (p : ℝ) :
    (∃ L, Tendsto (fun t => ∫ x in (1 : ℝ)..t, x ^ (-p)) atTop (𝓝 L)) ↔ 1 < p := by
  rw [converges_Ioi_iff_integrableOn (continuousOn_rpow_Ici one_pos _)
    (fun _ hx => Real.rpow_nonneg (by linarith) _), integrableOn_Ioi_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

/-- The improper integral `∫_1^∞ x^(-p)` equals `1/(p-1)` for `p > 1`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Example 3.56 (p-integral), p. 306"]
theorem tendsto_intervalIntegral_rpow {p : ℝ} (hp : 1 < p) :
    Tendsto (fun t => ∫ x in (1 : ℝ)..t, x ^ (-p)) atTop (𝓝 (1 / (p - 1))) := by
  have h := tendsto_intervalIntegral_of_integrableOn_Ioi
    ((integrableOn_Ioi_rpow_iff one_pos).2 (show -p < -1 by linarith))
  rw [integral_Ioi_rpow_of_lt (show -p < -1 by linarith) one_pos, Real.one_rpow] at h
  convert h using 2
  have : -p + 1 ≠ 0 := by linarith
  have : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- OpenStax Calculus 2:Example 3.48 (CA-244): the improper integral `∫_1^∞ π (1/x)^2 dx` (volume of the solid
obtained by revolving `y = 1/x`, disk method) converges to `π`. -/
@[kb "openstaxcalculus2016" "2:Example 3.48 (Gabriel's horn), p. 298"]
theorem gabriel_volume :
    Tendsto (fun t => ∫ x in (1 : ℝ)..t, π * (1 / x) ^ 2) atTop (𝓝 π) := by
  have h := tendsto_intervalIntegral_rpow (p := 2) (by norm_num)
  have h2 := h.const_mul π
  have e : ∀ x : ℝ, π * (1 / x) ^ 2 = π * x ^ (-(2 : ℝ)) := fun x => by
    rw [show -(2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    simp
  simp only [e]
  simp only [intervalIntegral.integral_const_mul]
  have h3 : π * (1 / ((2 : ℝ) - 1)) = π := by norm_num
  rw [h3] at h2
  exact h2

/-- OpenStax Calculus 2:Example 3.48 (CA-244): the area under `y = 1/x` over `[1,∞)` is infinite, i.e.
`∫_1^t dx/x` has no limit as `t → ∞`. -/
@[kb "openstaxcalculus2016" "2:Example 3.47, p. 297"]
theorem gabriel_area_diverges :
    ¬ ∃ L, Tendsto (fun t => ∫ x in (1 : ℝ)..t, 1 / x) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h : Tendsto (fun t => ∫ x in (1 : ℝ)..t, 1 / x) atTop atTop := by
    have : (fun t => ∫ x in (1 : ℝ)..t, 1 / x) =ᶠ[atTop] Real.log := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [integral_one_div_of_pos one_pos ht]
      simp
    exact Real.tendsto_log_atTop.congr' this.symm
  exact not_tendsto_nhds_of_tendsto_atTop h L hL

/-! ### Infinite discontinuity at an endpoint -/

/-- OpenStax Calculus 2:§3.7 Definition (CA-242): if `f` is integrable on `(a,b]` then
`∫_t^b f → ∫_{(a,b]} f` as `t → a⁺`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Definition (infinite discontinuity, Eq. 3.19-3.21), p. 302"]
theorem tendsto_intervalIntegral_left_endpoint {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Ioc a b)) :
    Tendsto (fun t => ∫ x in t..b, f x) (𝓝[>] a) (𝓝 (∫ x in Ioc a b, f x)) := by
  have hI : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hf
  have hcont := intervalIntegral.continuousOn_primitive_interval' hI
    (show b ∈ uIcc a b from right_mem_uIcc)
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have h1 : Tendsto (fun t => ∫ x in b..t, f x) (𝓝[>] a) (𝓝 (∫ x in b..a, f x)) := by
    refine (hcont.continuousWithinAt ha).tendsto.mono_left ?_
    rw [uIcc_of_le hab.le, nhdsWithin]
    exact le_inf nhdsWithin_le_nhds (le_principal_iff.2 (Icc_mem_nhdsGT hab))
  have e1 : ∀ t, ∫ x in t..b, f x = -∫ x in b..t, f x := fun t => integral_symm b t
  have e2 : ∫ x in Ioc a b, f x = -∫ x in b..a, f x := by
    rw [integral_symm a b, neg_neg, intervalIntegral.integral_of_le hab.le]
  rw [show (fun t => ∫ x in t..b, f x) = fun t => -∫ x in b..t, f x from funext e1, e2]
  exact h1.neg

/-- OpenStax Calculus 2:§3.7 Definition (CA-242): for a nonnegative `f` continuous on `(a,b]`, the improper
integral converges in the book's sense (`∫_t^b f` has a limit as `t → a⁺`) iff `f` is integrable on `(a,b]`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Definition (infinite discontinuity, Eq. 3.19-3.21), p. 302"]
theorem converges_Ioc_iff_integrableOn {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Ioc a b)) (hnn : ∀ x ∈ Ioc a b, 0 ≤ f x) :
    (∃ L, Tendsto (fun t => ∫ x in t..b, f x) (𝓝[>] a) (𝓝 L)) ↔ IntegrableOn f (Ioc a b) := by
  constructor
  · rintro ⟨L, hL⟩
    have hint : ∀ s t, a < s → s ≤ t → t ≤ b → IntervalIntegrable f volume s t := fun s t hs hst htb =>
      (hc.mono (fun x hx => by
        rw [uIcc_of_le hst] at hx
        exact ⟨lt_of_lt_of_le hs hx.1, le_trans hx.2 htb⟩)).intervalIntegrable
    -- the cut-off `a' t`
    let a' : ℝ → ℝ := fun t => if a < t ∧ t < b then t else b
    have hev : ∀ᶠ t in 𝓝[>] a, a < t ∧ t < b := by
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hab] with t h1 h2
      exact ⟨h1, h2.2⟩
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (I := L) (a := a')
      (l := 𝓝[>] a) ?_ ?_ ?_
    · intro t
      by_cases ht : a < t ∧ t < b
      · have : a' t = t := by simp [a', ht]
        rw [this]
        exact ((hint t b ht.1 ht.2.le le_rfl).1)
      · have : a' t = b := by simp [a', ht]
        rw [this]
        simp
    · refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hev] with t ht
      simp [a', ht]
    · filter_upwards [hev] with t ht
      have : a' t = t := by simp [a', ht]
      rw [this, ← intervalIntegral.integral_of_le ht.2.le]
      have h1 : ∫ x in t..b, ‖f x‖ = ∫ x in t..b, f x :=
        integral_congr fun x hx => by
          rw [uIcc_of_le ht.2.le] at hx
          exact Real.norm_of_nonneg (hnn x ⟨lt_of_lt_of_le ht.1 hx.1, hx.2⟩)
      rw [h1]
      refine ge_of_tendsto hL ?_
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      rw [← integral_add_adjacent_intervals (hint s t hs.1 hs.2.le ht.2.le) (hint t b ht.1 ht.2.le le_rfl)]
      have : 0 ≤ ∫ x in s..t, f x := intervalIntegral.integral_nonneg hs.2.le
        fun x hx => hnn x ⟨lt_of_lt_of_le hs.1 hx.1, le_trans hx.2 ht.2.le⟩
      linarith
  · intro h
    exact ⟨_, tendsto_intervalIntegral_left_endpoint hab h⟩

/-- OpenStax Calculus 2:§3.7 (CA-242), `p`-test at the origin: `∫_t^1 x^(-p)` has a limit as `t → 0⁺` iff `p < 1`. -/
@[kb "openstaxcalculus2016" "2:§3.7 Example 3.52, p. 302"]
theorem converges_Ioc_zero_one_rpow_iff (p : ℝ) :
    (∃ L, Tendsto (fun t => ∫ x in t..(1 : ℝ), x ^ (-p)) (𝓝[>] 0) (𝓝 L)) ↔ p < 1 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ (-p)) (Ioc 0 1) :=
    continuousOn_id.rpow_const fun _ hx => Or.inl (ne_of_gt hx.1)
  rw [converges_Ioc_iff_integrableOn one_pos hc
    (fun x hx => Real.rpow_nonneg hx.1.le _),
    integrableOn_Ioc_iff_integrableOn_Ioo (by simp),
    intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

end UndergradKB.Calculus
