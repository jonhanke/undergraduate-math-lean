import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Set Filter Topology

/-! ### Reciprocal powers (CA-054) -/

theorem tendsto_pow_sub_nhdsNE (a : ℝ) (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => (x - a) ^ n) (𝓝[≠] a) (𝓝 0) := by
  have : Tendsto (fun x : ℝ => (x - a) ^ n) (𝓝 a) (𝓝 ((a - a) ^ n)) :=
    ((continuous_id.sub continuous_const).pow n).tendsto a
  rw [sub_self, zero_pow hn] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- OpenStax Calculus 1:Theorem 2.3 (CA-054), `n` even: `1/(x-a)^n → +∞` as `x → a`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.3, p. 136"]
theorem tendsto_inv_pow_sub_even (a : ℝ) {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    Tendsto (fun x : ℝ => 1 / (x - a) ^ n) (𝓝[≠] a) atTop := by
  have h0 : Tendsto (fun x : ℝ => (x - a) ^ n) (𝓝[≠] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_sub_nhdsNE a n hn0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hn.pow_pos (sub_ne_zero.mpr hx)
  exact (tendsto_inv_nhdsGT_zero.comp h0).congr fun x => by simp

/-- OpenStax Calculus 1:Theorem 2.3 (CA-054), `n` odd, from the right: `1/(x-a)^n → +∞` as `x → a⁺`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.3, p. 136"]
theorem tendsto_inv_pow_sub_odd_right (a : ℝ) {n : ℕ} (hn : Odd n) :
    Tendsto (fun x : ℝ => 1 / (x - a) ^ n) (𝓝[>] a) atTop := by
  have h0 : Tendsto (fun x : ℝ => (x - a) ^ n) (𝓝[>] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (tendsto_pow_sub_nhdsNE a n hn.pos.ne').mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact pow_pos (sub_pos.mpr (show a < x from hx)) n
  exact (tendsto_inv_nhdsGT_zero.comp h0).congr fun x => by simp

/-- OpenStax Calculus 1:Theorem 2.3 (CA-054), `n` odd, from the left: `1/(x-a)^n → -∞` as `x → a⁻`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.3, p. 136"]
theorem tendsto_inv_pow_sub_odd_left (a : ℝ) {n : ℕ} (hn : Odd n) :
    Tendsto (fun x : ℝ => 1 / (x - a) ^ n) (𝓝[<] a) atBot := by
  have h0 : Tendsto (fun x : ℝ => (x - a) ^ n) (𝓝[<] a) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (tendsto_pow_sub_nhdsNE a n hn.pos.ne').mono_left (nhdsWithin_mono _ (fun x hx => ne_of_lt hx))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact hn.pow_neg (sub_neg.mpr (show x < a from hx))
  exact (tendsto_inv_nhdsLT_zero.comp h0).congr fun x => by simp

/-! ### Vertical asymptotes and discontinuity types (CA-055, CA-078) -/

/-- OpenStax Calculus 1:§2.2 Definition (vertical asymptote) (CA-055). The line `x = a` is a vertical
asymptote of `f` when at least one one-sided limit of `f` at `a` is `+∞` or `-∞`. -/
@[kb "openstaxcalculus2016" "1:§2.2 Definition (vertical asymptote), p. 136"]
def IsVerticalAsymptote (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto f (𝓝[>] a) atTop ∨ Tendsto f (𝓝[>] a) atBot ∨
    Tendsto f (𝓝[<] a) atTop ∨ Tendsto f (𝓝[<] a) atBot

/-- OpenStax Calculus 1:Example 2.10 (CA-055). `x = a` is a vertical asymptote of `1/(x-a)`. -/
@[kb "openstaxcalculus2016" "1:Example 2.10, p. 137"]
theorem isVerticalAsymptote_inv_sub (a : ℝ) : IsVerticalAsymptote (fun x => 1 / (x - a)) a :=
  Or.inl (by simpa using tendsto_inv_pow_sub_odd_right a (n := 1) odd_one)

/-- OpenStax Calculus 1:§2.4 Definition (CA-078). A removable discontinuity of `f` at `a`: the limit as
`x → a` exists, but `f` is not continuous at `a`. -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (types of discontinuities), p. 168"]
def IsRemovableDiscontinuity (f : ℝ → ℝ) (a : ℝ) : Prop :=
  (∃ L, Tendsto f (𝓝[≠] a) (𝓝 L)) ∧ ¬ ContinuousAt f a

/-- OpenStax Calculus 1:§2.4 Definition (CA-078). A jump discontinuity of `f` at `a`: both one-sided
limits exist and are different. -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (types of discontinuities), p. 168"]
def IsJumpDiscontinuity (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L₁ L₂, L₁ ≠ L₂ ∧ Tendsto f (𝓝[<] a) (𝓝 L₁) ∧ Tendsto f (𝓝[>] a) (𝓝 L₂)

/-- OpenStax Calculus 1:§2.4 Definition (CA-078). An infinite discontinuity of `f` at `a`: a one-sided
limit is infinite (that is, `x = a` is a vertical asymptote). -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (types of discontinuities), p. 168"]
def IsInfiniteDiscontinuity (f : ℝ → ℝ) (a : ℝ) : Prop := IsVerticalAsymptote f a

/-- OpenStax Calculus 1:§2.4 (CA-078). A jump discontinuity is not removable. -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (types of discontinuities), p. 168"]
theorem IsJumpDiscontinuity.not_removable {f : ℝ → ℝ} {a : ℝ} (h : IsJumpDiscontinuity f a) :
    ¬ IsRemovableDiscontinuity f a := by
  obtain ⟨L₁, L₂, hne, h1, h2⟩ := h
  rintro ⟨⟨L, hL⟩, -⟩
  apply hne
  have e1 := tendsto_nhds_unique h1 (hL.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_lt hx)))
  have e2 := tendsto_nhds_unique h2 (hL.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx)))
  rw [e1, e2]

/-- OpenStax Calculus 1:§2.4 (CA-078). A jump discontinuity is a genuine discontinuity. -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (types of discontinuities), p. 168"]
theorem IsJumpDiscontinuity.not_continuousAt {f : ℝ → ℝ} {a : ℝ} (h : IsJumpDiscontinuity f a) :
    ¬ ContinuousAt f a := by
  intro hc
  obtain ⟨L₁, L₂, hne, h1, h2⟩ := h
  apply hne
  have c1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio a))
  have c2 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))
  rw [tendsto_nhds_unique h1 c1, tendsto_nhds_unique h2 c2]

/-- OpenStax Calculus 1:§2.4 (CA-078). An infinite discontinuity is not removable: `f` has no finite
limit at `a` when a one-sided limit is infinite. -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (types of discontinuities), p. 168"]
theorem IsInfiniteDiscontinuity.not_removable {f : ℝ → ℝ} {a : ℝ} (h : IsInfiniteDiscontinuity f a) :
    ¬ IsRemovableDiscontinuity f a := by
  rintro ⟨⟨L, hL⟩, -⟩
  have hR := hL.mono_left (nhdsWithin_mono a (fun x (hx : x ∈ Ioi a) => ne_of_gt hx))
  have hLt := hL.mono_left (nhdsWithin_mono a (fun x (hx : x ∈ Iio a) => ne_of_lt hx))
  rcases h with h | h | h | h
  · exact not_tendsto_nhds_of_tendsto_atTop h L hR
  · exact not_tendsto_nhds_of_tendsto_atBot h L hR
  · exact not_tendsto_nhds_of_tendsto_atTop h L hLt
  · exact not_tendsto_nhds_of_tendsto_atBot h L hLt

/-! ### M-delta definition of infinite limits (CA-074) -/

theorem tendsto_atTop_iff_lt {α : Type*} {l : Filter α} {f : α → ℝ} :
    Tendsto f l atTop ↔ ∀ M : ℝ, ∀ᶠ x in l, M < f x :=
  ⟨fun h M => (tendsto_atTop.mp h (M + 1)).mono fun x hx => by linarith,
    fun h => tendsto_atTop.mpr fun M => (h M).mono fun x hx => hx.le⟩

theorem tendsto_atBot_iff_lt {α : Type*} {l : Filter α} {f : α → ℝ} :
    Tendsto f l atBot ↔ ∀ M : ℝ, ∀ᶠ x in l, f x < M :=
  ⟨fun h M => (tendsto_atBot.mp h (M - 1)).mono fun x hx => by linarith,
    fun h => tendsto_atBot.mpr fun M => (h M).mono fun x hx => hx.le⟩

/-- OpenStax Calculus 1:§2.5 Definition (infinite limits, epsilon-delta) (CA-074): `f(x) → +∞` as `x → a`
iff for every `M` there is `δ > 0` such that `0 < |x - a| < δ` gives `f x > M`. -/
@[kb "openstaxcalculus2016" "1:§2.5 Definition (infinite limits, epsilon-delta), p. 186"]
theorem tendsto_atTop_nhdsNE_iff (f : ℝ → ℝ) (a : ℝ) :
    Tendsto f (𝓝[≠] a) atTop ↔ ∀ M : ℝ, ∃ δ > 0, ∀ x, 0 < |x - a| → |x - a| < δ → M < f x := by
  rw [tendsto_atTop_iff_lt]
  refine forall_congr' fun M => ?_
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine exists_congr fun δ => and_congr_right fun _ => forall_congr' fun x => ?_
  simp only [Real.dist_eq, abs_pos, sub_ne_zero]
  constructor
  · intro h h1 h2
    exact h h2 h1
  · intro h h2 h1
    exact h h1 h2

/-- OpenStax Calculus 1:§2.5 Definition (CA-074): `f(x) → -∞` as `x → a` iff for every `M` there is
`δ > 0` with `0 < |x - a| < δ` giving `f x < M`. -/
@[kb "openstaxcalculus2016" "1:§2.5 Definition (infinite limits, epsilon-delta), p. 186"]
theorem tendsto_atBot_nhdsNE_iff (f : ℝ → ℝ) (a : ℝ) :
    Tendsto f (𝓝[≠] a) atBot ↔ ∀ M : ℝ, ∃ δ > 0, ∀ x, 0 < |x - a| → |x - a| < δ → f x < M := by
  rw [tendsto_atBot_iff_lt]
  refine forall_congr' fun M => ?_
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine exists_congr fun δ => and_congr_right fun _ => forall_congr' fun x => ?_
  simp only [Real.dist_eq, abs_pos, sub_ne_zero]
  constructor
  · intro h h1 h2
    exact h h2 h1
  · intro h h2 h1
    exact h h1 h2

/-! ### Root law (CA-062) and trigonometric limit (CA-069) -/

/-- Real odd root: the real `n`-th root of `x` for odd `n` (sign-preserving), `x^(1/n)` for `x ≥ 0` and
`-(-x)^(1/n)` for `x < 0`; written without a case split as `max(x,0)^(1/n) - max(-x,0)^(1/n)`. -/
noncomputable def oddRoot (n : ℕ) (x : ℝ) : ℝ :=
  (max x 0) ^ ((1 : ℝ) / n) - (max (-x) 0) ^ ((1 : ℝ) / n)

theorem continuous_oddRoot {n : ℕ} (hn : n ≠ 0) : Continuous (oddRoot n) := by
  have hq : (0 : ℝ) ≤ 1 / n := by positivity
  unfold oddRoot
  exact ((Real.continuous_rpow_const hq).comp (continuous_id.max continuous_const)).sub
    ((Real.continuous_rpow_const hq).comp ((continuous_neg).max continuous_const))

theorem oddRoot_pow {n : ℕ} (hn : Odd n) (x : ℝ) : (oddRoot n x) ^ n = x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.pos.ne'
  have key : ∀ y : ℝ, 0 ≤ y → (y ^ ((1 : ℝ) / n)) ^ n = y := by
    intro y hy
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy, one_div_mul_cancel hn0, Real.rpow_one]
  rcases le_total 0 x with h | h
  · have : oddRoot n x = x ^ ((1 : ℝ) / n) := by
      unfold oddRoot
      rw [max_eq_left h, max_eq_right (by linarith), Real.zero_rpow (by positivity), sub_zero]
    rw [this, key x h]
  · have : oddRoot n x = -((-x) ^ ((1 : ℝ) / n)) := by
      unfold oddRoot
      rw [max_eq_right h, max_eq_left (by linarith), Real.zero_rpow (by positivity), zero_sub]
    rw [this, hn.neg_pow, key (-x) (by linarith), neg_neg]

/-- OpenStax Calculus 1:Theorem 2.5 (CA-062), odd roots: for odd `n`, if `f → L` then `ⁿ√f → ⁿ√L`
(real odd root, valid for every `L`). -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem tendsto_oddRoot {l : Filter ℝ} {f : ℝ → ℝ} {L : ℝ} {n : ℕ} (hn : Odd n)
    (h : Tendsto f l (𝓝 L)) : Tendsto (fun x => oddRoot n (f x)) l (𝓝 (oddRoot n L)) :=
  ((continuous_oddRoot hn.pos.ne').tendsto L).comp h

/-- OpenStax Calculus 1:Theorem 2.5 (CA-062), even roots: for `n ≥ 1` and `L ≥ 0`, if `f → L` then
`f(x)^(1/n) → L^(1/n)` (for even `n` the root is only meaningful for `f ≥ 0`). -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem tendsto_rpow_root {l : Filter ℝ} {f : ℝ → ℝ} {L : ℝ} {n : ℕ} (hn : n ≠ 0) (_hL : 0 ≤ L)
    (h : Tendsto f l (𝓝 L)) :
    Tendsto (fun x => (f x) ^ ((1 : ℝ) / n)) l (𝓝 (L ^ ((1 : ℝ) / n))) :=
  ((Real.continuousAt_rpow_const L _ (Or.inr (by positivity))).tendsto).comp h

/-- OpenStax Calculus 1:Example 2.25 (CA-069): `(1 - cos θ)/θ → 0` as `θ → 0`. -/
@[kb "openstaxcalculus2016" "1:Example 2.25, p. 159"]
theorem tendsto_one_sub_cos_div :
    Tendsto (fun θ : ℝ => (1 - Real.cos θ) / θ) (𝓝[≠] 0) (𝓝 0) := by
  have h := (hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_cos 0))
  rw [Real.sin_zero, neg_zero] at h
  have h2 := h.neg
  rw [neg_zero] at h2
  refine h2.congr fun θ => ?_
  simp [slope_def_field, Real.cos_zero]
  ring

end UndergradKB.Calculus
