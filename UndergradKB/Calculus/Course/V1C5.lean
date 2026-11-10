import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr
import UndergradKB.Calculus.RiemannSums
import UndergradKB.Calculus.IntegralsFTC
import UndergradKB.Calculus.ExpLog
import UndergradKB.Calculus.AreasBetween
import UndergradKB.Calculus.TrigIntegrals

/-! Course layer, OpenStax Calculus Volume 1, Chapter 5 (integration). -/

namespace UndergradKB.Calculus.Course.V1C5

open Set MeasureTheory intervalIntegral
open scoped Interval

/-- OpenStax Calculus 1:§5.1 Rule (properties of sigma notation) (CA-179). A constant summed
`n` times gives `n * c`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (properties of sigma notation), p. 447"]
theorem sigma_const (n : ℕ) (c : ℝ) : ∑ _i ∈ Finset.Icc 1 n, c = n * c := by
  simp

/-- OpenStax Calculus 1:§5.1 Rule (properties of sigma notation) (CA-179). Constants factor out
of a finite sum. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (properties of sigma notation), p. 447"]
theorem sigma_const_mul (n : ℕ) (c : ℝ) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, c * a i = c * ∑ i ∈ Finset.Icc 1 n, a i :=
  (Finset.mul_sum _ _ _).symm

/-- OpenStax Calculus 1:§5.1 Rule (properties of sigma notation) (CA-179). Sums split termwise. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (properties of sigma notation), p. 447"]
theorem sigma_add (n : ℕ) (a b : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, (a i + b i) = ∑ i ∈ Finset.Icc 1 n, a i + ∑ i ∈ Finset.Icc 1 n, b i :=
  Finset.sum_add_distrib

/-- OpenStax Calculus 1:§5.1 Rule (properties of sigma notation) (CA-179). Differences split
termwise. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (properties of sigma notation), p. 447"]
theorem sigma_sub (n : ℕ) (a b : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, (a i - b i) = ∑ i ∈ Finset.Icc 1 n, a i - ∑ i ∈ Finset.Icc 1 n, b i :=
  Finset.sum_sub_distrib _ _

/-- OpenStax Calculus 1:§5.1 Rule (properties of sigma notation) (CA-179). A sum from `m` to `n`
is the sum from `1` to `n` minus the sum from `1` to `m - 1`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (properties of sigma notation), p. 447"]
theorem sigma_split (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n + 1) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc m n, a i = ∑ i ∈ Finset.Icc 1 n, a i - ∑ i ∈ Finset.Icc 1 (m - 1), a i := by
  have h := Finset.sum_Ico_consecutive a hm hmn
  have e1 : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by ext x; simp
  have e2 : Finset.Ico m (n + 1) = Finset.Icc m n := by ext x; simp
  have e3 : Finset.Ico 1 m = Finset.Icc 1 (m - 1) := by ext x; simp; omega
  rw [e1, e2, e3] at h
  linarith

/-- OpenStax Calculus 1:Theorem 5.1 (CA-187). A function continuous on `[a,b]` is integrable
there. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.1, p. 465"]
theorem continuousOn_integrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : IntervalIntegrable f volume a b :=
  hf.intervalIntegrable_of_Icc hab

/-- OpenStax Calculus 1:§5.2 Rule (property 1 of definite integral) (CA-189). The integral from
`a` to `a` is zero. -/
@[kb "openstaxcalculus2016" "1:§5.2 Rule (property 1 of definite integral), p. 472"]
theorem integral_same_limits (f : ℝ → ℝ) (a : ℝ) : ∫ x in a..a, f x = 0 :=
  intervalIntegral.integral_same

/-- OpenStax Calculus 1:§5.2 Rule (property 2 of definite integral) (CA-190). Reversing the
limits flips the sign. -/
@[kb "openstaxcalculus2016" "1:§5.2 Rule (property 2 of definite integral), p. 472"]
theorem integral_reverse_limits (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in b..a, f x = -∫ x in a..b, f x :=
  intervalIntegral.integral_symm a b

/-- OpenStax Calculus 1:§5.2 Rule (property 3 of definite integral) (CA-191). The integral of a
sum is the sum of the integrals. -/
@[kb "openstaxcalculus2016" "1:§5.2 Rule (property 3 of definite integral), p. 472"]
theorem integral_add_functions {f g : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (f x + g x) = (∫ x in a..b, f x) + ∫ x in a..b, g x :=
  intervalIntegral.integral_add hf hg

/-- OpenStax Calculus 1:§5.2 Rule (property 4 of definite integral) (CA-191). The integral of a
difference is the difference of the integrals. -/
@[kb "openstaxcalculus2016" "1:§5.2 Rule (property 4 of definite integral), p. 472"]
theorem integral_sub_functions {f g : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (f x - g x) = (∫ x in a..b, f x) - ∫ x in a..b, g x :=
  intervalIntegral.integral_sub hf hg

/-- OpenStax Calculus 1:§5.2 Rule (property 5 of definite integral) (CA-192). A constant factor
comes out of the integral. -/
@[kb "openstaxcalculus2016" "1:§5.2 Rule (property 5 of definite integral), p. 472"]
theorem integral_const_mul_function (f : ℝ → ℝ) (a b c : ℝ) :
    ∫ x in a..b, c * f x = c * ∫ x in a..b, f x :=
  intervalIntegral.integral_const_mul c f

/-- OpenStax Calculus 1:§5.2 Rule (property 6 of definite integral) (CA-193). Additivity over
adjacent intervals. -/
@[kb "openstaxcalculus2016" "1:§5.2 Rule (property 6 of definite integral), p. 472"]
theorem integral_adjacent_intervals {f : ℝ → ℝ} {a b c : ℝ} (hab : IntervalIntegrable f volume a b)
    (hbc : IntervalIntegrable f volume b c) :
    (∫ x in a..b, f x) + ∫ x in b..c, f x = ∫ x in a..c, f x :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- OpenStax Calculus 1:Theorem 5.2 (CA-194), part (i). Nonnegative integrand, nonnegative
integral. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.2, p. 473"]
theorem integral_nonneg_of_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, 0 ≤ f x) :
    0 ≤ ∫ x in a..b, f x :=
  intervalIntegral.integral_nonneg hab hf

/-- OpenStax Calculus 1:Theorem 5.2 (CA-194), part (ii). Integrals preserve pointwise order. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.2, p. 473"]
theorem integral_mono_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ x ∈ Icc a b, f x ≤ g x) : ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
  intervalIntegral.integral_mono_on hab hf hg h

/-- OpenStax Calculus 1:Theorem 5.2 (CA-194), part (iii). If `m ≤ f ≤ M` on `[a,b]` then the
integral lies between `m (b-a)` and `M (b-a)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.2, p. 473"]
theorem integral_bounds_of_bounds {f : ℝ → ℝ} {a b m M : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hm : ∀ x ∈ Icc a b, m ≤ f x)
    (hM : ∀ x ∈ Icc a b, f x ≤ M) :
    m * (b - a) ≤ ∫ x in a..b, f x ∧ ∫ x in a..b, f x ≤ M * (b - a) := by
  have h1 := intervalIntegral.integral_mono_on hab intervalIntegrable_const hf hm
  have h2 := intervalIntegral.integral_mono_on hab hf intervalIntegrable_const hM
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
  constructor <;> linarith

/-- OpenStax Calculus 1:§5.2 Definition (average value) (CA-195). The average value of `f` on
`[a,b]` equals the integral divided by `b - a`. -/
@[kb "openstaxcalculus2016" "1:§5.2 Definition (average value), p. 475"]
theorem average_value_eq_integral_div (f : ℝ → ℝ) (a b : ℝ) :
    (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) :=
  interval_average_eq_div f a b

/-- OpenStax Calculus 1:Theorem 5.3 (CA-196). Mean value theorem for integrals: a continuous
function on `[a,b]` (with `a < b`) attains its average value at some point of the interval. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.3, p. 481"]
theorem mean_value_theorem_for_integrals {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, f c = (∫ x in a..b, f x) / (b - a) := by
  obtain ⟨c, hc, h⟩ := exists_eq_interval_average hab.ne (by rwa [uIcc_of_le hab.le])
  rw [interval_average_eq_div] at h
  rw [uIoo_of_le hab.le] at hc
  exact ⟨c, Ioo_subset_Icc_self hc, h⟩

/-- OpenStax Calculus 1:Theorem 5.4 (CA-197). Fundamental theorem of calculus, part 1: if `f` is
continuous on `[a,b]` then `F x = ∫ a..x f` has derivative `f x` at each interior point. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.4, p. 483"]
theorem ftc_part_one {f : ℝ → ℝ} {a b x : ℝ} (hf : ContinuousOn f (Icc a b))
    (hx : x ∈ Ioo a b) : HasDerivAt (fun t => ∫ s in a..t, f s) (f x) x := by
  have hax : a ≤ x := hx.1.le
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · exact (hf.mono (Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hax
  · exact (hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  · exact hf.continuousAt (Icc_mem_nhds hx.1 hx.2)

/-- OpenStax Calculus 1:Theorem 5.4 (CA-197), global form. For continuous `f`, `F x = ∫ a..x f`
satisfies `F' = f` everywhere. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.4, p. 483"]
theorem ftc_part_one_continuous {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (fun t => ∫ s in a..t, f s) (f x) x :=
  (hf.integral_hasStrictDerivAt a x).hasDerivAt

/-- OpenStax Calculus 1:Theorem 5.5 (CA-199). Fundamental theorem of calculus, part 2: if `F' = f`
on `[a,b]` with `f` continuous, then `∫ a..b f = F b - F a`. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.5, p. 486"]
theorem ftc_part_two {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) : ∫ x in a..b, f x = F b - F a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hF x ?_) ?_
  · rwa [uIcc_of_le hab] at hx
  · exact hf.intervalIntegrable_of_Icc hab

/-- OpenStax Calculus 1:Theorem 5.6 (CA-199). Net change: the new value equals the old value plus
the integral of the rate of change. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.6, p. 497"]
theorem net_change {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) : F b = F a + ∫ x in a..b, f x := by
  rw [ftc_part_two hab hf hF]
  ring

/-- OpenStax Calculus 1:Theorem 5.8 (CA-204). Substitution for definite integrals:
`∫ a..b f(g x) g'(x) dx = ∫ g a..g b f(u) du` for `f` continuous and `g` with continuous
derivative. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.8, p. 519"]
theorem substitution_definite {f g g' : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x ∈ [[a, b]], HasDerivAt g (g' x) x) (hg' : ContinuousOn g' [[a, b]])
    (hf : Continuous f) : ∫ x in a..b, f (g x) * g' x = ∫ u in g a..g b, f u :=
  intervalIntegral.integral_comp_mul_deriv hg hg' hf

/-- OpenStax Calculus 1:§5.6 Rule (integration formulas involving logarithmic functions)
(CA-206). If `0` is not between `a` and `b`, then `∫ a..b du/u = ln (b/a)`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integration formulas involving logarithmic functions), p. 529"]
theorem integral_inv_eq_log_div {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) :
    ∫ u in a..b, u⁻¹ = Real.log (b / a) :=
  integral_inv h

/-- OpenStax Calculus 1:§5.6 Rule (integration formulas involving logarithmic functions)
(CA-206). `ln |u|` is an antiderivative of `1/u` on `u ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integration formulas involving logarithmic functions), p. 529"]
theorem hasDerivAt_log_abs {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t => Real.log |t|) u⁻¹ u := by
  have : (fun t : ℝ => Real.log |t|) = Real.log := funext Real.log_abs
  rw [this]
  exact Real.hasDerivAt_log hu

/-! ## Results proved in undergrad-kb -/

/-- OpenStax Calculus 1:§5.1 Rule (sums and powers of integers) (CA-180). Closed forms for
`1 + ... + n`, the sum of the first `n` squares, and the sum of the first `n` cubes. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (sums and powers of integers), p. 448"]
theorem sums_of_powers_of_integers :
    (∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (i : ℝ) = n * (n + 1) / 2) ∧
    (∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6) ∧
    (∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2) :=
  ⟨UndergradKB.Calculus.sum_Icc_id, UndergradKB.Calculus.sum_Icc_sq,
    UndergradKB.Calculus.sum_Icc_cube⟩

/-- OpenStax Calculus 1:§5.1 Rule (left-endpoint approximation) (CA-182). For `f` continuous on
`[a, b]`, the left- and right-endpoint approximations `L_n` and `R_n` converge to `∫ a..b f`
as `n → ∞`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (left-endpoint approximation), p. 450"]
theorem endpoint_approximations_converge {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto (fun n => UndergradKB.Calculus.leftSum f a b n) Filter.atTop
      (nhds (∫ x in a..b, f x)) ∧
    Filter.Tendsto (fun n => UndergradKB.Calculus.rightSum f a b n) Filter.atTop
      (nhds (∫ x in a..b, f x)) :=
  ⟨UndergradKB.Calculus.tendsto_leftSum hab hf, UndergradKB.Calculus.tendsto_rightSum hab hf⟩

/-- OpenStax Calculus 1:§5.4 Rule (integrals of even and odd functions) (CA-202). For `f`
continuous: if `f` is even, `∫ -a..a f = 2 ∫ 0..a f`; if `f` is odd, `∫ -a..a f = 0`. -/
@[kb "openstaxcalculus2016" "1:§5.4 Rule (integrals of even and odd functions), p. 501"]
theorem integral_even_odd_symmetric {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    ((∀ x, f (-x) = f x) → ∫ x in (-a)..a, f x = 2 * ∫ x in (0 : ℝ)..a, f x) ∧
    ((∀ x, f (-x) = -f x) → ∫ x in (-a)..a, f x = 0) :=
  ⟨fun h => UndergradKB.Calculus.integral_symm_even hf a h,
    fun h => UndergradKB.Calculus.integral_symm_odd hf a h⟩

/-- OpenStax Calculus 1:Theorem 5.7 (CA-203). Substitution: if `F` is an antiderivative of `f` and
`g` is differentiable then `F ∘ g` is an antiderivative of `(f ∘ g) g'`; for definite integrals,
`∫ a..b f(g x) g'(x) dx = ∫ g a..g b f(u) du`. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.7, p. 515"]
theorem substitution_rule {F f g g' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) :
    (∀ x, HasDerivAt (fun x => F (g x)) (f (g x) * g' x) x) ∧
    (Continuous f → Continuous g' → ∀ a b : ℝ,
      ∫ x in a..b, f (g x) * g' x = ∫ u in g a..g b, f u) :=
  ⟨UndergradKB.Calculus.hasDerivAt_comp_antiderivative hF hg,
    fun hf hg' a b => UndergradKB.Calculus.integral_substitution hf hg hg' a b⟩

/-- OpenStax Calculus 1:§5.6 Rule (integrals of exponential functions) (CA-205). `e^u` is its own
antiderivative with `∫ a..b e^u = e^b - e^a`; for `c > 0`, `c ≠ 1`, `c^u / ln c` is an antiderivative
of `c^u` and `∫ a..b c^u = (c^b - c^a)/ln c`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integrals of exponential functions), p. 524"]
theorem integrals_of_exponentials :
    (∀ a b : ℝ, ∫ u in a..b, Real.exp u = Real.exp b - Real.exp a) ∧
    (∀ u : ℝ, HasDerivAt Real.exp (Real.exp u) u) ∧
    (∀ {c : ℝ}, 0 < c → c ≠ 1 → ∀ u : ℝ,
      HasDerivAt (fun y : ℝ => c ^ y / Real.log c) (c ^ u) u) ∧
    (∀ {c : ℝ}, 0 < c → c ≠ 1 → ∀ a b : ℝ, ∫ u in a..b, c ^ u = (c ^ b - c ^ a) / Real.log c) :=
  ⟨UndergradKB.Calculus.integral_exp_eq, UndergradKB.Calculus.hasDerivAt_exp_antiderivative,
    @UndergradKB.Calculus.hasDerivAt_rpow_antiderivative, @UndergradKB.Calculus.integral_rpow_eq⟩

/-- OpenStax Calculus 1:§5.6 Rule (integration formulas involving logarithmic functions) (CA-207).
`u ln u - u` is an antiderivative of `ln u`, so `∫ a..b ln u du = b ln b - a ln a - b + a`; the
`log_c` versions divide by `ln c`. -/
@[kb "openstaxcalculus2016" "1:§5.6 Rule (integration formulas involving logarithmic functions), p. 529"]
theorem integrals_of_logarithms :
    (∀ {u : ℝ}, u ≠ 0 → HasDerivAt (fun y : ℝ => y * Real.log y - y) (Real.log u) u) ∧
    (∀ a b : ℝ, ∫ u in a..b, Real.log u = b * Real.log b - a * Real.log a - b + a) ∧
    (∀ (a : ℝ) {u : ℝ}, u ≠ 0 →
      HasDerivAt (fun y : ℝ => (y * Real.log y - y) / Real.log a) (Real.logb a u) u) ∧
    (∀ c a b : ℝ, ∫ u in a..b, Real.logb c u =
      (b * Real.log b - a * Real.log a - b + a) / Real.log c) :=
  ⟨@UndergradKB.Calculus.hasDerivAt_mul_log_sub, UndergradKB.Calculus.integral_log_eq,
    @UndergradKB.Calculus.hasDerivAt_logb_antiderivative, UndergradKB.Calculus.integral_logb_eq⟩

/-- OpenStax Calculus 1:§5.7 Rule (inverse trigonometric integrals, formula 1) (CA-208). For
`a > 0`, `arcsin (u/a)` is an antiderivative of `1/√(a² - u²)` on `|u| < a`, so
`∫ b..c dx/√(a²-x²) = arcsin (c/a) - arcsin (b/a)` for `|b|, |c| < a`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 1), p. 534"]
theorem integral_arcsin_form :
    (∀ {a u : ℝ}, 0 < a → |u| < a →
      HasDerivAt (fun u => Real.arcsin (u / a)) (1 / √(a ^ 2 - u ^ 2)) u) ∧
    (∀ {a b c : ℝ}, 0 < a → |b| < a → |c| < a →
      ∫ x in b..c, 1 / √(a ^ 2 - x ^ 2) = Real.arcsin (c / a) - Real.arcsin (b / a)) :=
  ⟨@UndergradKB.Calculus.hasDerivAt_arcsin_div, @UndergradKB.Calculus.integral_inv_sqrt_sq_sub⟩

/-- OpenStax Calculus 1:§5.7 Rule (inverse trigonometric integrals, formula 2) (CA-209). For
`a ≠ 0`, `(1/a) arctan (u/a)` is an antiderivative of `1/(a² + u²)`, so
`∫ b..c dx/(a²+x²) = (1/a)(arctan (c/a) - arctan (b/a))`. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 2), p. 534"]
theorem integral_arctan_form :
    (∀ {a : ℝ}, a ≠ 0 → ∀ u : ℝ,
      HasDerivAt (fun u => (1 / a) * Real.arctan (u / a)) (1 / (a ^ 2 + u ^ 2)) u) ∧
    (∀ {a : ℝ}, a ≠ 0 → ∀ b c : ℝ, ∫ x in b..c, 1 / (a ^ 2 + x ^ 2) =
      (1 / a) * Real.arctan (c / a) - (1 / a) * Real.arctan (b / a)) :=
  ⟨@UndergradKB.Calculus.hasDerivAt_arctan_div, @UndergradKB.Calculus.integral_inv_sq_add_sq'⟩

/-- OpenStax Calculus 1:§5.7 Rule (inverse trigonometric integrals, formula 3) (CA-210). For
`a > 0`, `(1/a) arcsec (|u|/a)` is an antiderivative of `1/(u √(u² - a²))` on `|u| > a`, so the
definite integral over an interval avoiding `[-a, a]` is the difference of its values. -/
@[kb "openstaxcalculus2016" "1:§5.7 Rule (inverse trigonometric integrals, formula 3), p. 534"]
theorem integral_arcsec_form :
    (∀ {a u : ℝ}, 0 < a → a < |u| →
      HasDerivAt (fun u => (1 / a) * UndergradKB.Calculus.arcsec (|u| / a))
        (1 / (u * √(u ^ 2 - a ^ 2))) u) ∧
    (∀ {a b c : ℝ}, 0 < a → (∀ x ∈ Set.uIcc b c, a < |x|) →
      ∫ x in b..c, 1 / (x * √(x ^ 2 - a ^ 2)) =
        (1 / a) * UndergradKB.Calculus.arcsec (|c| / a) -
          (1 / a) * UndergradKB.Calculus.arcsec (|b| / a)) :=
  ⟨@UndergradKB.Calculus.hasDerivAt_arcsec_div,
    @UndergradKB.Calculus.integral_inv_mul_sqrt_sq_sub⟩

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 1:§5.1 Definition (partition, regular partition) (CA-181). The regular
partition of `[a, b]` into `n` pieces has points `a + i (b - a)/n`; it starts at `a`, ends at `b`,
is increasing, and consecutive points are `(b - a)/n` apart. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (partition, regular partition), p. 450"]
theorem regular_partition_def (a b : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∀ i : ℕ, UndergradKB.Calculus.regularPartition a b n i = a + i * ((b - a) / n)) ∧
    UndergradKB.Calculus.regularPartition a b n 0 = a ∧
    UndergradKB.Calculus.regularPartition a b n n = b ∧
    (∀ i : ℕ, UndergradKB.Calculus.regularPartition a b n (i + 1) -
        UndergradKB.Calculus.regularPartition a b n i = (b - a) / n) ∧
    (a ≤ b → Monotone (UndergradKB.Calculus.regularPartition a b n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine ⟨fun _ => rfl, by simp [UndergradKB.Calculus.regularPartition], ?_, ?_,
    fun h => UndergradKB.Calculus.regularPartition_mono h n⟩
  · unfold UndergradKB.Calculus.regularPartition
    field_simp
    ring
  · intro i
    unfold UndergradKB.Calculus.regularPartition
    push_cast
    ring

/-- OpenStax Calculus 1:§5.1 Definition (Riemann sum) (CA-183). The Riemann sum of `f` on a regular
partition with tag points `c i` is `Δx ∑ f (c i)`; for continuous `f` and tags in the subintervals
these sums converge to the integral. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (Riemann sum), p. 456"]
theorem riemann_sum_def {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∀ (n : ℕ) (c : ℕ → ℝ), UndergradKB.Calculus.taggedSum f a b n c =
      (b - a) / n * ∑ i ∈ Finset.range n, f (c i)) ∧
    ∀ c : ℕ → ℕ → ℝ,
      (∀ n i : ℕ, i < n → c n i ∈ Icc (UndergradKB.Calculus.regularPartition a b n i)
        (UndergradKB.Calculus.regularPartition a b n (i + 1))) →
      Filter.Tendsto (fun n => UndergradKB.Calculus.taggedSum f a b n (c n)) Filter.atTop
        (nhds (∫ x in a..b, f x)) :=
  ⟨fun _ _ => rfl, fun c hc => UndergradKB.Calculus.tendsto_taggedSum hab hf c hc⟩

/-- OpenStax Calculus 1:§5.1 Definition (area under a curve) (CA-184). For continuous `f` on
`[a, b]` the left, right and arbitrary-tag Riemann sums all converge to the integral, which is the
area under the graph when `f ≥ 0`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (area under a curve), p. 456"]
theorem area_under_curve_as_limit {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto (fun n => UndergradKB.Calculus.leftSum f a b n) Filter.atTop
      (nhds (∫ x in a..b, f x)) ∧
    Filter.Tendsto (fun n => UndergradKB.Calculus.rightSum f a b n) Filter.atTop
      (nhds (∫ x in a..b, f x)) ∧
    ∀ c : ℕ → ℕ → ℝ,
      (∀ n i : ℕ, i < n → c n i ∈ Icc (UndergradKB.Calculus.regularPartition a b n i)
        (UndergradKB.Calculus.regularPartition a b n (i + 1))) →
      Filter.Tendsto (fun n => UndergradKB.Calculus.taggedSum f a b n (c n)) Filter.atTop
        (nhds (∫ x in a..b, f x)) :=
  ⟨UndergradKB.Calculus.tendsto_leftSum hab hf, UndergradKB.Calculus.tendsto_rightSum hab hf,
    fun c hc => UndergradKB.Calculus.tendsto_taggedSum hab hf c hc⟩

/-- OpenStax Calculus 1:§5.1 Definition (upper sum, lower sum) (CA-185). For a monotone `f` the
endpoint sums bracket the integral: the left sum is a lower sum and the right sum an upper sum for
increasing `f`, and the roles swap for decreasing `f`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (upper sum, lower sum), p. 457"]
theorem upper_lower_sums_monotone {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n) :
    (MonotoneOn f (Icc a b) →
      UndergradKB.Calculus.leftSum f a b n ≤ ∫ x in a..b, f x ∧
        ∫ x in a..b, f x ≤ UndergradKB.Calculus.rightSum f a b n) ∧
    (AntitoneOn f (Icc a b) →
      UndergradKB.Calculus.rightSum f a b n ≤ ∫ x in a..b, f x ∧
        ∫ x in a..b, f x ≤ UndergradKB.Calculus.leftSum f a b n) :=
  ⟨fun h => ⟨UndergradKB.Calculus.leftSum_le_integral_of_monotoneOn hab h hn,
      UndergradKB.Calculus.integral_le_rightSum_of_monotoneOn hab h hn⟩,
    fun h => ⟨UndergradKB.Calculus.rightSum_le_integral_of_antitoneOn hab h hn,
      UndergradKB.Calculus.integral_le_leftSum_of_antitoneOn hab h hn⟩⟩

/-- OpenStax Calculus 1:§5.2 Definition (definite integral) (CA-186). For continuous `f` the
integral is the limit of Riemann sums over regular partitions with arbitrary tags, and `f` is
integrable; the sums are within `(b - a) ε` of the integral when `f` varies by at most `ε` over
steps of width `(b - a)/n`. -/
@[kb "openstaxcalculus2016" "1:§5.2 Definition (definite integral), p. 464"]
theorem definite_integral_as_limit_of_riemann_sums {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    IntervalIntegrable f volume a b ∧
    (∀ c : ℕ → ℕ → ℝ,
      (∀ n i : ℕ, i < n → c n i ∈ Icc (UndergradKB.Calculus.regularPartition a b n i)
        (UndergradKB.Calculus.regularPartition a b n (i + 1))) →
      Filter.Tendsto (fun n => UndergradKB.Calculus.taggedSum f a b n (c n)) Filter.atTop
        (nhds (∫ x in a..b, f x))) ∧
    (∀ {n : ℕ}, 0 < n → ∀ {ε : ℝ},
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| ≤ (b - a) / n → |f x - f y| ≤ ε) →
      ∀ {c : ℕ → ℝ}, (∀ i < n, c i ∈ Icc (UndergradKB.Calculus.regularPartition a b n i)
        (UndergradKB.Calculus.regularPartition a b n (i + 1))) →
      |UndergradKB.Calculus.taggedSum f a b n c - ∫ x in a..b, f x| ≤ (b - a) * ε) :=
  ⟨hf.intervalIntegrable_of_Icc hab, fun c hc => UndergradKB.Calculus.tendsto_taggedSum hab hf c hc,
    fun {_} hn {_} hε {_} hc => UndergradKB.Calculus.taggedSum_error_le hab hf hn hε hc⟩

/-- OpenStax Calculus 1:§5.2 Definition (net signed area, total area) (CA-188). For continuous `f`
the area above the axis minus the area below it equals the integral, and the total area between
the graph and the axis is the integral of `|f|`. -/
@[kb "openstaxcalculus2016" "1:§5.2 Definition (net signed area, total area), p. 471"]
theorem net_signed_and_total_area {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ 0 < p.2 ∧ p.2 < f p.1}).toReal -
        (volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ f p.1 < p.2 ∧ p.2 < 0}).toReal =
      ∫ x in a..b, f x ∧
    volume {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ (0 < p.2 ∧ p.2 < f p.1 ∨ f p.1 < p.2 ∧ p.2 < 0)} =
      ENNReal.ofReal (∫ x in a..b, |f x|) :=
  ⟨UndergradKB.Calculus.net_signed_area hf hab, UndergradKB.Calculus.total_area hf hab⟩

/-- OpenStax Calculus 1:Example 5.18 (CA-198). The derivative of an integral with a variable upper
limit is `f (u x) u'(x)`, and with variable limits `g` and `h` it is `f (h x) h'(x) - f (g x) g'(x)`. -/
@[kb "openstaxcalculus2016" "1:Example 5.18, p. 485"]
theorem derivative_of_integral_variable_limits {f : ℝ → ℝ} (hf : Continuous f) :
    (∀ {u : ℝ → ℝ} {u' x : ℝ}, HasDerivAt u u' x → ∀ a : ℝ,
      HasDerivAt (fun x => ∫ t in a..u x, f t) (f (u x) * u') x) ∧
    (∀ {g h : ℝ → ℝ} {g' h' x : ℝ}, HasDerivAt g g' x → HasDerivAt h h' x →
      HasDerivAt (fun x => ∫ t in g x..h x, f t) (f (h x) * h' - f (g x) * g') x) :=
  ⟨fun hu a => UndergradKB.Calculus.hasDerivAt_integral_upper hf hu a,
    fun hg hh => UndergradKB.Calculus.hasDerivAt_integral_both hf hg hh⟩

end UndergradKB.Calculus.Course.V1C5
