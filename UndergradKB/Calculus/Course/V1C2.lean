import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import UndergradKB.Common.Attr
import UndergradKB.Calculus.Limits
import UndergradKB.Calculus.Trig

/-!
# OpenStax Calculus Volume 1, Chapter 2 (limits): course layer

Thin wrappers around Mathlib. A limit `lim_{x→a}` is `Filter.Tendsto` along the punctured
neighbourhood `𝓝[≠] a`; one-sided limits use `𝓝[<] a` and `𝓝[>] a`.
-/

namespace UndergradKB.Calculus.Course.V1C2

open Filter Topology

/-- OpenStax Calculus 1:§2.1 Definition (secant line) (CA-046).
The secant through `(a, f a)` and `(x, f x)` has slope `(f x - f a)/(x - a)`. -/
@[kb "openstaxcalculus2016" "1:§2.1 Definition (secant line), p. 115"]
theorem secant_slope (f : ℝ → ℝ) (a x : ℝ) : slope f a x = (f x - f a) / (x - a) :=
  slope_def_field f a x

/-- OpenStax Calculus 1:§2.1 tangent line (definition in text) (CA-047).
The tangent slope `L` at `a` is the limit of the secant slopes; this is exactly `HasDerivAt f L a`. -/
@[kb "openstaxcalculus2016" "1:§2.1 tangent line (definition in text), p. 116"]
theorem tangent_slope_is_limit_of_secants (f : ℝ → ℝ) (a L : ℝ) :
    HasDerivAt f L a ↔ Tendsto (fun x => (f x - f a) / (x - a)) (𝓝[≠] a) (𝓝 L) := by
  have : slope f a = fun x => (f x - f a) / (x - a) := by
    funext x
    exact slope_def_field f a x
  rw [hasDerivAt_iff_tendsto_slope, this]

/-- OpenStax Calculus 1:Theorem 2.1 (CA-050).
`lim_{x→a} x = a` and `lim_{x→a} c = c`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.1, p. 130"]
theorem limit_id_const (a c : ℝ) :
    Tendsto (fun x : ℝ => x) (𝓝[≠] a) (𝓝 a) ∧ Tendsto (fun _ : ℝ => c) (𝓝[≠] a) (𝓝 c) :=
  ⟨tendsto_id.mono_left nhdsWithin_le_nhds, tendsto_const_nhds⟩

/-- OpenStax Calculus 1:Theorem 2.2 (CA-052).
The two-sided limit is `L` exactly when both one-sided limits are `L`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.2, p. 133"]
theorem limit_iff_one_sided_limits (f : ℝ → ℝ) (a L : ℝ) :
    Tendsto f (𝓝[≠] a) (𝓝 L) ↔ Tendsto f (𝓝[<] a) (𝓝 L) ∧ Tendsto f (𝓝[>] a) (𝓝 L) := by
  rw [← nhdsLT_sup_nhdsGT, tendsto_sup]

section LimitLaws

variable {f g : ℝ → ℝ} {a L M : ℝ}

/-- OpenStax Calculus 1:Theorem 2.5 (CA-056). Sum law for limits. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem limit_sum (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M)) :
    Tendsto (fun x => f x + g x) (𝓝[≠] a) (𝓝 (L + M)) :=
  hf.add hg

/-- OpenStax Calculus 1:Theorem 2.5 (CA-057). Difference law for limits. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem limit_difference (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M)) :
    Tendsto (fun x => f x - g x) (𝓝[≠] a) (𝓝 (L - M)) :=
  hf.sub hg

/-- OpenStax Calculus 1:Theorem 2.5 (CA-058). Constant multiple law for limits. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem limit_constant_multiple (c : ℝ) (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) :
    Tendsto (fun x => c * f x) (𝓝[≠] a) (𝓝 (c * L)) :=
  hf.const_mul c

/-- OpenStax Calculus 1:Theorem 2.5 (CA-059). Product law for limits. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem limit_product (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M)) :
    Tendsto (fun x => f x * g x) (𝓝[≠] a) (𝓝 (L * M)) :=
  hf.mul hg

/-- OpenStax Calculus 1:Theorem 2.5 (CA-060). Quotient law for limits, `M ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem limit_quotient (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hg : Tendsto g (𝓝[≠] a) (𝓝 M))
    (hM : M ≠ 0) : Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 (L / M)) :=
  hf.div hg hM

/-- OpenStax Calculus 1:Theorem 2.5 (CA-061). Power law for limits. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem limit_power (n : ℕ) (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) :
    Tendsto (fun x => f x ^ n) (𝓝[≠] a) (𝓝 (L ^ n)) :=
  hf.pow n

/-- OpenStax Calculus 1:§2.3 one-sided limit laws (text) (CA-065).
The sum and product laws hold along any one-sided neighbourhood `𝓝[s] a`, in particular for
`s = Set.Iio a` (left limits) and `s = Set.Ioi a` (right limits). -/
@[kb "openstaxcalculus2016" "1:§2.3 one-sided limit laws (text), p. 154"]
theorem one_sided_limit_laws (s : Set ℝ) (hf : Tendsto f (𝓝[s] a) (𝓝 L))
    (hg : Tendsto g (𝓝[s] a) (𝓝 M)) :
    Tendsto (fun x => f x + g x) (𝓝[s] a) (𝓝 (L + M)) ∧
      Tendsto (fun x => f x * g x) (𝓝[s] a) (𝓝 (L * M)) :=
  ⟨hf.add hg, hf.mul hg⟩

/-- OpenStax Calculus 1:Theorem 2.7 (CA-066).
Squeeze theorem: if `f ≤ g ≤ h` near `a` (off `a`) and `f`, `h` tend to `L`, so does `g`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.7, p. 157"]
theorem squeeze_theorem (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) (hh : Tendsto g (𝓝[≠] a) (𝓝 L))
    {k : ℝ → ℝ} (hfk : ∀ᶠ x in 𝓝[≠] a, f x ≤ k x) (hkh : ∀ᶠ x in 𝓝[≠] a, k x ≤ g x) :
    Tendsto k (𝓝[≠] a) (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hh hfk hkh

/-- OpenStax Calculus 1:Theorem 2.9 (CA-080).
Composite limit theorem: if `f` is continuous at `L` and `g → L`, then `f (g x) → f L`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.9, p. 171"]
theorem limit_of_composition (hf : ContinuousAt f L) {g : ℝ → ℝ}
    (hg : Tendsto g (𝓝[≠] a) (𝓝 L)) : Tendsto (fun x => f (g x)) (𝓝[≠] a) (𝓝 (f L)) :=
  hf.tendsto.comp hg

end LimitLaws

/-- OpenStax Calculus 1:Theorem 2.6 (CA-063).
For polynomials `p`, `q`: `lim p(x) = p(a)`, and `lim p(x)/q(x) = p(a)/q(a)` when `q(a) ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.6, p. 150"]
theorem limit_polynomial_rational (p q : Polynomial ℝ) (a : ℝ) :
    Tendsto (fun x => p.eval x) (𝓝[≠] a) (𝓝 (p.eval a)) ∧
      (q.eval a ≠ 0 →
        Tendsto (fun x => p.eval x / q.eval x) (𝓝[≠] a) (𝓝 (p.eval a / q.eval a))) := by
  have hp : Tendsto (fun x => p.eval x) (𝓝[≠] a) (𝓝 (p.eval a)) :=
    (p.continuous.tendsto a).mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun x => q.eval x) (𝓝[≠] a) (𝓝 (q.eval a)) :=
    (q.continuous.tendsto a).mono_left nhdsWithin_le_nhds
  exact ⟨hp, fun h => hp.div hq h⟩

/-- OpenStax Calculus 1:§2.3 observation (equal functions have equal limits) (CA-064).
If `f x = g x` for `x ≠ a` in an interval around `a`, a limit of `f` at `a` is a limit of `g`. -/
@[kb "openstaxcalculus2016" "1:§2.3 observation (equal functions have equal limits), p. 151"]
theorem limit_eq_of_eq_near (f g : ℝ → ℝ) (a L δ : ℝ) (hδ : 0 < δ)
    (h : ∀ x ∈ Set.Ioo (a - δ) (a + δ), x ≠ a → f x = g x)
    (hf : Tendsto f (𝓝[≠] a) (𝓝 L)) : Tendsto g (𝓝[≠] a) (𝓝 L) := by
  refine hf.congr' ?_
  have hI : ∀ᶠ x in 𝓝 a, x ∈ Set.Ioo (a - δ) (a + δ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  exact eventually_nhdsWithin_iff.2 (hI.mono fun x hx hne => h x hx hne)

/-- OpenStax Calculus 1:§2.3 trigonometric limits (text) (CA-067).
`sin θ → 0` and `cos θ → 1` as `θ → 0`. -/
@[kb "openstaxcalculus2016" "1:§2.3 trigonometric limits (text), p. 158"]
theorem limit_sin_cos_zero :
    Tendsto Real.sin (𝓝[≠] 0) (𝓝 0) ∧ Tendsto Real.cos (𝓝[≠] 0) (𝓝 1) := by
  constructor
  · have hc : Continuous Real.sin := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · have hc : Continuous Real.cos := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- OpenStax Calculus 1:§2.3 trigonometric limits (text) (CA-068).
`sin θ / θ → 1` as `θ → 0`. -/
@[kb "openstaxcalculus2016" "1:§2.3 trigonometric limits (text), p. 159"]
theorem limit_sin_div_self : Tendsto (fun θ : ℝ => Real.sin θ / θ) (𝓝[≠] 0) (𝓝 1) :=
  Real.tendsto_sin_div_nhdsNE_zero

/-- OpenStax Calculus 1:§2.5 Definition (epsilon-delta definition of a limit) (CA-070).
`lim_{x→a} f x = L` iff for every `ε > 0` there is `δ > 0` with `|f x - L| < ε` whenever
`0 < |x - a| < δ`. -/
@[kb "openstaxcalculus2016" "1:§2.5 Definition (epsilon-delta definition of a limit), p. 177"]
theorem limit_epsilon_delta (f : ℝ → ℝ) (a L : ℝ) :
    Tendsto f (𝓝[≠] a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| → |x - a| < δ → |f x - L| < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  refine forall₂_congr fun ε hε => exists_congr fun δ => and_congr_right fun _ => ?_
  constructor
  · intro h x h0 h1
    have := h (x := x) (by simpa [sub_eq_zero] using h0.ne') (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  · intro h x hx hd
    rw [Real.dist_eq] at hd ⊢
    exact h x (abs_pos.2 (sub_ne_zero.2 hx)) hd

/-- OpenStax Calculus 1:§2.5 Definition (triangle inequality) (CA-071).
`|a + b| ≤ |a| + |b|`. -/
@[kb "openstaxcalculus2016" "1:§2.5 Definition (triangle inequality), p. 183"]
theorem triangle_inequality (a b : ℝ) : |a + b| ≤ |a| + |b| :=
  abs_add_le a b

/-- OpenStax Calculus 1:§2.5 Definition (one-sided epsilon-delta limits) (CA-073).
Limits from the right and from the left in epsilon-delta form. -/
@[kb "openstaxcalculus2016" "1:§2.5 Definition (one-sided epsilon-delta limits), p. 185"]
theorem one_sided_limit_epsilon_delta (f : ℝ → ℝ) (a L : ℝ) :
    (Tendsto f (𝓝[>] a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x - a → x - a < δ → |f x - L| < ε) ∧
    (Tendsto f (𝓝[<] a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < a - x → a - x < δ → |f x - L| < ε) := by
  constructor
  · rw [Metric.tendsto_nhdsWithin_nhds]
    refine forall₂_congr fun ε hε => exists_congr fun δ => and_congr_right fun _ => ?_
    constructor
    · intro h x h0 h1
      have := h (x := x) (Set.mem_Ioi.2 (by linarith))
        (by rw [Real.dist_eq, abs_of_pos h0]; exact h1)
      rwa [Real.dist_eq] at this
    · intro h x hx hd
      have hx' : 0 < x - a := by simpa using hx
      rw [Real.dist_eq, abs_of_pos hx'] at hd
      rw [Real.dist_eq]
      exact h x hx' hd
  · rw [Metric.tendsto_nhdsWithin_nhds]
    refine forall₂_congr fun ε hε => exists_congr fun δ => and_congr_right fun _ => ?_
    constructor
    · intro h x h0 h1
      have := h (x := x) (Set.mem_Iio.2 (by linarith))
        (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith)
      rwa [Real.dist_eq] at this
    · intro h x hx hd
      have hx' : 0 < a - x := by simpa using hx
      rw [Real.dist_eq, abs_of_neg (by linarith)] at hd
      rw [Real.dist_eq]
      exact h x hx' (by linarith)

/-- OpenStax Calculus 1:§2.4 Definition (continuity at a point) (CA-076).
`f` is continuous at `a` iff the limit of `f` at `a` (off `a`) equals `f a`. -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (continuity at a point), p. 165"]
theorem continuousAt_iff_limit_eq_value (f : ℝ → ℝ) (a : ℝ) :
    ContinuousAt f a ↔ Tendsto f (𝓝[≠] a) (𝓝 (f a)) :=
  continuousAt_iff_punctured_nhds

/-- OpenStax Calculus 1:Theorem 2.8 (CA-077).
Polynomials are continuous everywhere, and rational functions at points where the denominator
does not vanish. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.8, p. 168"]
theorem polynomial_rational_continuous (p q : Polynomial ℝ) :
    Continuous (fun x => p.eval x) ∧
      ∀ a, q.eval a ≠ 0 → ContinuousAt (fun x => p.eval x / q.eval x) a :=
  ⟨p.continuous, fun _ h => p.continuous.continuousAt.div q.continuous.continuousAt h⟩

/-- OpenStax Calculus 1:§2.4 Continuity from the right and left; continuity over an interval (CA-079).
For `a < b`, continuity on `[a, b]` is continuity at each point of `(a, b)` together with
continuity from the right at `a` and from the left at `b`. -/
@[kb "openstaxcalculus2016" "1:§2.4 Continuity from the right and left; continuity over an interval, p. 170"]
theorem continuousOn_Icc_iff (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    ContinuousOn f (Set.Icc a b) ↔
      (∀ x ∈ Set.Ioo a b, ContinuousAt f x) ∧ ContinuousWithinAt f (Set.Ici a) a ∧
        ContinuousWithinAt f (Set.Iic b) b := by
  constructor
  · intro h
    refine ⟨fun x hx => (h x (Set.Ioo_subset_Icc_self hx)).continuousAt
      (Icc_mem_nhds hx.1 hx.2), ?_, ?_⟩
    · exact (continuousWithinAt_Icc_iff_Ici hab).1 (h a ⟨le_rfl, hab.le⟩)
    · exact (continuousWithinAt_Icc_iff_Iic hab).1 (h b ⟨hab.le, le_rfl⟩)
  · rintro ⟨h1, h2, h3⟩ x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · exact (continuousWithinAt_Icc_iff_Ici hab).2 h2
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · exact (continuousWithinAt_Icc_iff_Iic hab).2 h3
    exact (h1 x ⟨hax, hxb⟩).continuousWithinAt

/-- OpenStax Calculus 1:Theorem 2.11 (CA-082).
Intermediate value theorem: a function continuous on `[a, b]` takes every value between `f a`
and `f b` at some point of `[a, b]`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.11, p. 172"]
theorem intermediate_value_theorem (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (y : ℝ)
    (hy : (f a ≤ y ∧ y ≤ f b) ∨ (f b ≤ y ∧ y ≤ f a)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  rcases hy with hy | hy
  · exact intermediate_value_Icc hab hf ⟨hy.1, hy.2⟩
  · exact intermediate_value_Icc' hab hf ⟨hy.1, hy.2⟩

/-! ## Results proved in undergrad-kb -/

/-- OpenStax Calculus 1:Theorem 2.3 (CA-054). For a positive integer `n`, `1/(x-a)^n → +∞` as
`x → a` when `n` is even, and for odd `n` it tends to `+∞` from the right and `-∞` from the left. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.3, p. 136"]
theorem infinite_limit_inv_pow (a : ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    (Even n → Tendsto (fun x : ℝ => 1 / (x - a) ^ n) (𝓝[≠] a) atTop) ∧
    (Odd n → Tendsto (fun x : ℝ => 1 / (x - a) ^ n) (𝓝[>] a) atTop ∧
      Tendsto (fun x : ℝ => 1 / (x - a) ^ n) (𝓝[<] a) atBot) :=
  ⟨fun hn => UndergradKB.Calculus.tendsto_inv_pow_sub_even a hn hn0,
    fun hn => ⟨UndergradKB.Calculus.tendsto_inv_pow_sub_odd_right a hn,
      UndergradKB.Calculus.tendsto_inv_pow_sub_odd_left a hn⟩⟩

/-- OpenStax Calculus 1:Theorem 2.5 (CA-062). Root law: if `f → L` then the `n`-th root of `f`
tends to the `n`-th root of `L`; all `L` for `n` odd (with the real odd root `oddRoot`), and
`L ≥ 0` for `n` even (root as the power `1/n`). -/
@[kb "openstaxcalculus2016" "1:Theorem 2.5, p. 149"]
theorem root_law {l : Filter ℝ} {f : ℝ → ℝ} {L : ℝ} {n : ℕ} (h : Tendsto f l (𝓝 L)) :
    (Odd n → Tendsto (fun x => UndergradKB.Calculus.oddRoot n (f x)) l
      (𝓝 (UndergradKB.Calculus.oddRoot n L))) ∧
    (n ≠ 0 → 0 ≤ L →
      Tendsto (fun x => (f x) ^ ((1 : ℝ) / n)) l (𝓝 (L ^ ((1 : ℝ) / n)))) :=
  ⟨fun hn => UndergradKB.Calculus.tendsto_oddRoot hn h,
    fun hn hL => UndergradKB.Calculus.tendsto_rpow_root hn hL h⟩

/-- OpenStax Calculus 1:Theorem 2.10 (CA-081). The trigonometric functions are continuous on their
domains: `tan` and `sec` where `cos ≠ 0`, `cot` and `csc` where `sin ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 2.10, p. 171"]
theorem trig_functions_continuous_on_domain :
    ContinuousOn Real.tan {x | Real.cos x ≠ 0} ∧ ContinuousOn Real.cot {x | Real.sin x ≠ 0} ∧
    ContinuousOn UndergradKB.Calculus.sec {x | Real.cos x ≠ 0} ∧
    ContinuousOn UndergradKB.Calculus.csc {x | Real.sin x ≠ 0} :=
  ⟨UndergradKB.Calculus.continuousOn_tan', UndergradKB.Calculus.continuousOn_cot,
    UndergradKB.Calculus.continuousOn_sec, UndergradKB.Calculus.continuousOn_csc⟩

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 1:§2.2 Definition (one-sided limits) (CA-051). The left (right) limit of `f`
at `a` is `L` when `f x` gets close to `L` as `x` approaches `a` through values below (above) `a`. -/
@[kb "openstaxcalculus2016" "1:§2.2 Definition (one-sided limits), p. 132"]
theorem one_sided_limit_def (f : ℝ → ℝ) (a L : ℝ) :
    (Tendsto f (𝓝[<] a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄, x ∈ Set.Iio a → dist x a < δ → dist (f x) L < ε) ∧
    (Tendsto f (𝓝[>] a) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi a → dist x a < δ → dist (f x) L < ε) :=
  ⟨Metric.tendsto_nhdsWithin_nhds, Metric.tendsto_nhdsWithin_nhds⟩

/-- OpenStax Calculus 1:§2.2 Definition (infinite limits) (CA-053). The limit of `f` at `a` (from
the left, from the right, or two-sided) is `+∞` (resp. `-∞`) when `f` eventually exceeds (resp. falls
below) every bound near `a`. -/
@[kb "openstaxcalculus2016" "1:§2.2 Definition (infinite limits), p. 134"]
theorem infinite_limit_def (f : ℝ → ℝ) (a : ℝ) :
    (Tendsto f (𝓝[<] a) atTop ↔ ∀ M : ℝ, ∀ᶠ x in 𝓝[<] a, M ≤ f x) ∧
    (Tendsto f (𝓝[>] a) atTop ↔ ∀ M : ℝ, ∀ᶠ x in 𝓝[>] a, M ≤ f x) ∧
    (Tendsto f (𝓝[≠] a) atTop ↔ ∀ M : ℝ, ∀ᶠ x in 𝓝[≠] a, M ≤ f x) ∧
    (Tendsto f (𝓝[<] a) atBot ↔ ∀ M : ℝ, ∀ᶠ x in 𝓝[<] a, f x ≤ M) ∧
    (Tendsto f (𝓝[>] a) atBot ↔ ∀ M : ℝ, ∀ᶠ x in 𝓝[>] a, f x ≤ M) ∧
    (Tendsto f (𝓝[≠] a) atBot ↔ ∀ M : ℝ, ∀ᶠ x in 𝓝[≠] a, f x ≤ M) :=
  ⟨Filter.tendsto_atTop, Filter.tendsto_atTop, Filter.tendsto_atTop,
    Filter.tendsto_atBot, Filter.tendsto_atBot, Filter.tendsto_atBot⟩

/-- OpenStax Calculus 1:§2.2 Definition (vertical asymptote) (CA-055). The line `x = a` is a vertical
asymptote of `f` when some one-sided limit of `f` at `a` is `+∞` or `-∞`; for instance `1/(x-a)` has
one at `a`. -/
@[kb "openstaxcalculus2016" "1:§2.2 Definition (vertical asymptote), p. 136"]
theorem vertical_asymptote_def (f : ℝ → ℝ) (a : ℝ) :
    (UndergradKB.Calculus.IsVerticalAsymptote f a ↔
      (Tendsto f (𝓝[>] a) atTop ∨ Tendsto f (𝓝[>] a) atBot ∨
        Tendsto f (𝓝[<] a) atTop ∨ Tendsto f (𝓝[<] a) atBot)) ∧
    UndergradKB.Calculus.IsVerticalAsymptote (fun x => 1 / (x - a)) a :=
  ⟨Iff.rfl, UndergradKB.Calculus.isVerticalAsymptote_inv_sub a⟩

/-- OpenStax Calculus 1:§2.3 trigonometric limits (text) (CA-069). The quotient `(1 - cos θ)/θ`
tends to `0` as `θ → 0`. -/
@[kb "openstaxcalculus2016" "1:§2.3 trigonometric limits (text), p. 160"]
theorem limit_one_sub_cos_div_self :
    Tendsto (fun θ : ℝ => (1 - Real.cos θ) / θ) (𝓝[≠] 0) (𝓝 0) :=
  UndergradKB.Calculus.tendsto_one_sub_cos_div

/-- OpenStax Calculus 1:§2.5 Definition (infinite limits, epsilon-delta) (CA-074). The limit at `a`
is `+∞` (resp. `-∞`) exactly when for every bound `M` there is `δ > 0` such that `f x > M` (resp.
`f x < M`) whenever `0 < |x - a| < δ`. -/
@[kb "openstaxcalculus2016" "1:§2.5 Definition (infinite limits, epsilon-delta), p. 186"]
theorem infinite_limit_epsilon_delta (f : ℝ → ℝ) (a : ℝ) :
    (Tendsto f (𝓝[≠] a) atTop ↔
      ∀ M : ℝ, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → M < f x) ∧
    (Tendsto f (𝓝[≠] a) atBot ↔
      ∀ M : ℝ, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → f x < M) :=
  ⟨UndergradKB.Calculus.tendsto_atTop_nhdsNE_iff f a,
    UndergradKB.Calculus.tendsto_atBot_nhdsNE_iff f a⟩

/-- OpenStax Calculus 1:§2.4 Definition (types of discontinuities) (CA-078). A removable
discontinuity has a limit but is not continuous, a jump has different finite one-sided limits, an
infinite one has a vertical asymptote; jump and infinite discontinuities are never removable. -/
@[kb "openstaxcalculus2016" "1:§2.4 Definition (types of discontinuities), p. 168"]
theorem types_of_discontinuities (f : ℝ → ℝ) (a : ℝ) :
    (UndergradKB.Calculus.IsRemovableDiscontinuity f a ↔
      (∃ L, Tendsto f (𝓝[≠] a) (𝓝 L)) ∧ ¬ContinuousAt f a) ∧
    (UndergradKB.Calculus.IsJumpDiscontinuity f a ↔
      ∃ L₁ L₂, L₁ ≠ L₂ ∧ Tendsto f (𝓝[<] a) (𝓝 L₁) ∧ Tendsto f (𝓝[>] a) (𝓝 L₂)) ∧
    (UndergradKB.Calculus.IsInfiniteDiscontinuity f a ↔
      UndergradKB.Calculus.IsVerticalAsymptote f a) ∧
    (UndergradKB.Calculus.IsJumpDiscontinuity f a →
      ¬UndergradKB.Calculus.IsRemovableDiscontinuity f a) ∧
    (UndergradKB.Calculus.IsInfiniteDiscontinuity f a →
      ¬UndergradKB.Calculus.IsRemovableDiscontinuity f a) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, UndergradKB.Calculus.IsJumpDiscontinuity.not_removable,
    UndergradKB.Calculus.IsInfiniteDiscontinuity.not_removable⟩

end UndergradKB.Calculus.Course.V1C2
