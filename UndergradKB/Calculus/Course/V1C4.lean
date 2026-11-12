import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import UndergradKB.Common.Attr
import UndergradKB.Calculus.DerivativeApplications
import UndergradKB.Calculus.LHopital
import UndergradKB.Calculus.Newton
import UndergradKB.Calculus.TangentsAntiderivatives
import UndergradKB.Calculus.ExpLog
import UndergradKB.Calculus.EndBehavior

/-! Course layer, OpenStax Calculus Volume 1, Chapter 4 (applications of derivatives). -/

namespace UndergradKB.Calculus.Course.V1C4

open Filter Topology Asymptotics Set

/-- OpenStax Calculus 1:§4.2 Linear approximation (CA-133). Near `a` the function differs from its
tangent line by `o(x - a)`. -/
@[kb "openstaxcalculus2016" "1:§4.2 Linear approximation, p. 316"]
theorem linearization_error_isLittleO {f : ℝ → ℝ} {a : ℝ} (h : DifferentiableAt ℝ f a) :
    (fun x => f x - (f a + deriv f a * (x - a))) =o[𝓝 a] fun x => x - a := by
  have := hasDerivAt_iff_isLittleO.mp h.hasDerivAt
  refine this.congr_left fun x => ?_
  simp only [smul_eq_mul]
  ring

/-- OpenStax Calculus 1:§4.2 Differentials and approximating change (CA-136). The actual change
`f (x + dx) - f x` differs from the differential `f' x * dx` by `o(dx)`. -/
@[kb "openstaxcalculus2016" "1:§4.2 Differentials and approximating change, p. 321"]
theorem change_sub_differential_isLittleO {f : ℝ → ℝ} {x : ℝ} (h : DifferentiableAt ℝ f x) :
    (fun dx => (f (x + dx) - f x) - deriv f x * dx) =o[𝓝 0] fun dx => dx := by
  have := hasDerivAt_iff_isLittleO_nhds_zero.mp h.hasDerivAt
  refine this.congr_left fun dx => ?_
  simp only [smul_eq_mul]
  ring

/-- OpenStax Calculus 1:§4.3 Definition (absolute extrema) (CA-138). `c` is an absolute maximum of
`f` on `D` iff `f x ≤ f c` for all `x ∈ D`. -/
@[kb "openstaxcalculus2016" "1:§4.3 Definition (absolute extrema), p. 326"]
theorem absolute_max_iff {f : ℝ → ℝ} {D : Set ℝ} {c : ℝ} :
    IsMaxOn f D c ↔ ∀ x ∈ D, f x ≤ f c := isMaxOn_iff

/-- OpenStax Calculus 1:§4.3 Definition (absolute extrema) (CA-138). `c` is an absolute minimum of
`f` on `D` iff `f c ≤ f x` for all `x ∈ D`. -/
@[kb "openstaxcalculus2016" "1:§4.3 Definition (absolute extrema), p. 326"]
theorem absolute_min_iff {f : ℝ → ℝ} {D : Set ℝ} {c : ℝ} :
    IsMinOn f D c ↔ ∀ x ∈ D, f c ≤ f x := isMinOn_iff

/-- OpenStax Calculus 1:Theorem 4.1 (CA-139). A continuous function on a closed bounded interval
has an absolute maximum and an absolute minimum there (extreme value theorem). -/
@[kb "openstaxcalculus2016" "1:Theorem 4.1, p. 327"]
theorem extreme_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f c) ∧ ∃ d ∈ Icc a b, ∀ x ∈ Icc a b, f d ≤ f x := by
  obtain ⟨c, hc, h1⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hf
  obtain ⟨d, hd, h2⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hf
  exact ⟨⟨c, hc, isMaxOn_iff.1 h1⟩, ⟨d, hd, isMinOn_iff.1 h2⟩⟩

/-- OpenStax Calculus 1:§4.3 Definition (local extrema) (CA-140). A local maximum at `c` means
`f x ≤ f c` for all `x` within some radius of `c`. -/
@[kb "openstaxcalculus2016" "1:§4.3 Definition (local extrema), p. 328"]
theorem local_max_iff {f : ℝ → ℝ} {c : ℝ} :
    IsLocalMax f c ↔ ∃ ε > 0, ∀ x, |x - c| < ε → f x ≤ f c := by
  rw [IsLocalMax, IsMaxFilter, Metric.eventually_nhds_iff]
  simp only [Real.dist_eq]

/-- OpenStax Calculus 1:§4.3 Definition (local extrema) (CA-140). A local minimum at `c` means
`f c ≤ f x` for all `x` within some radius of `c`. -/
@[kb "openstaxcalculus2016" "1:§4.3 Definition (local extrema), p. 328"]
theorem local_min_iff {f : ℝ → ℝ} {c : ℝ} :
    IsLocalMin f c ↔ ∃ ε > 0, ∀ x, |x - c| < ε → f c ≤ f x := by
  rw [IsLocalMin, IsMinFilter, Metric.eventually_nhds_iff]
  simp only [Real.dist_eq]

/-- OpenStax Calculus 1:Theorem 4.2 (CA-141). If `f` is differentiable at a local extremum `c`,
then `f' c = 0` (Fermat's theorem). -/
@[kb "openstaxcalculus2016" "1:Theorem 4.2, p. 329"]
theorem fermat_local_extremum {f : ℝ → ℝ} {c : ℝ} (hf : DifferentiableAt ℝ f c)
    (h : IsLocalExtr f c) : deriv f c = 0 :=
  h.hasDerivAt_eq_zero hf.hasDerivAt

/-- OpenStax Calculus 1:Theorem 4.4 (CA-144). Rolle's theorem: `f` continuous on `[a,b]`,
differentiable on `(a,b)`, with `f a = f b`, has a point `c ∈ (a,b)` with `f' c = 0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.4, p. 338"]
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) (hfab : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_zero hab hfc hfab
    (f' := deriv f) fun x hx => (hfd.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  exact ⟨c, hc, h⟩

/-- OpenStax Calculus 1:Theorem 4.5 (CA-145). Mean value theorem: `f` continuous on `[a,b]` and
differentiable on `(a,b)` has `c ∈ (a,b)` with `f' c = (f b - f a)/(b - a)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.5, p. 341"]
theorem mean_value_theorem {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

/-- OpenStax Calculus 1:Theorem 4.6 (CA-146). A function differentiable on an open interval
with zero derivative there is constant on it. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.6, p. 344"]
theorem constant_of_deriv_zero {f : ℝ → ℝ} {a b : ℝ} (hf : DifferentiableOn ℝ f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, deriv f x = 0) {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    f x = f y :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hf (fun z hz => h z hz) hx hy

/-- OpenStax Calculus 1:Theorem 4.7 (CA-147). Two functions with equal derivatives on an open
interval differ by a constant there. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.7, p. 344"]
theorem eq_add_const_of_deriv_eq {f g : ℝ → ℝ} {a b : ℝ} (hf : DifferentiableOn ℝ f (Ioo a b))
    (hg : DifferentiableOn ℝ g (Ioo a b)) (h : ∀ x ∈ Ioo a b, deriv f x = deriv g x) :
    ∃ C : ℝ, ∀ x ∈ Ioo a b, f x = g x + C :=
  isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo hf hg (fun z hz => h z hz)

/-- OpenStax Calculus 1:Theorem 4.8 (CA-148), increasing part. A function continuous on `(a,b)`
with `f' > 0` there is strictly increasing. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.8, p. 345"]
theorem strictMonoOn_of_deriv_pos_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, 0 < deriv f x) : StrictMonoOn f (Ioo a b) :=
  strictMonoOn_of_deriv_pos (convex_Ioo a b) hf (by simpa using h)

/-- OpenStax Calculus 1:Theorem 4.8 (CA-148), decreasing part: `f' < 0` inside makes `f` strictly
decreasing. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.8, p. 345"]
theorem strictAntiOn_of_deriv_neg_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, deriv f x < 0) : StrictAntiOn f (Ioo a b) :=
  strictAntiOn_of_deriv_neg (convex_Ioo a b) hf (by simpa using h)

/-- OpenStax Calculus 1:Theorem 4.10 (CA-151), concave up. `f'' > 0` on an interval makes the
graph strictly concave up (`StrictConvexOn`), and `f'` strictly increasing. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.10, p. 353"]
theorem concave_up_of_second_deriv_pos {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, 0 < deriv^[2] f x) : StrictConvexOn ℝ (Ioo a b) f :=
  strictConvexOn_of_deriv2_pos (convex_Ioo a b) hf (by simpa using h)

/-- OpenStax Calculus 1:Theorem 4.10 (CA-151), concave down. `f'' < 0` on an interval makes the
graph strictly concave down (`StrictConcaveOn`). -/
@[kb "openstaxcalculus2016" "1:Theorem 4.10, p. 353"]
theorem concave_down_of_second_deriv_neg {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, deriv^[2] f x < 0) : StrictConcaveOn ℝ (Ioo a b) f :=
  strictConcaveOn_of_deriv2_neg (convex_Ioo a b) hf (by simpa using h)

/-- OpenStax Calculus 1:Theorem 4.11 (CA-153), minimum case. If `f' c = 0`, `f` continuous at `c`
and `f'' c > 0` then `c` is a local minimum (second derivative test). -/
@[kb "openstaxcalculus2016" "1:Theorem 4.11, p. 356"]
theorem second_derivative_test_min {f : ℝ → ℝ} {c : ℝ} (hc : ContinuousAt f c)
    (h1 : deriv f c = 0) (h2 : 0 < deriv (deriv f) c) : IsLocalMin f c :=
  isLocalMin_of_deriv_deriv_pos h2 h1 hc

/-- OpenStax Calculus 1:Theorem 4.11 (CA-153), maximum case. If `f' c = 0`, `f` continuous at `c`
and `f'' c < 0` then `c` is a local maximum. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.11, p. 356"]
theorem second_derivative_test_max {f : ℝ → ℝ} {c : ℝ} (hc : ContinuousAt f c)
    (h1 : deriv f c = 0) (h2 : deriv (deriv f) c < 0) : IsLocalMax f c :=
  isLocalMax_of_deriv_deriv_neg h2 h1 hc

/-- OpenStax Calculus 1:§4.6 Definition (formal limit at infinity) (CA-154). `f x → L` as
`x → ∞` iff for every `ε > 0` there is `N` with `|f x - L| < ε` whenever `x > N`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (formal limit at infinity), p. 367"]
theorem tendsto_atTop_nhds_iff_eps_N {f : ℝ → ℝ} {L : ℝ} :
    Tendsto f atTop (𝓝 L) ↔ ∀ ε > 0, ∃ N : ℝ, ∀ x > N, |f x - L| < ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
    exact ⟨N, fun x hx => by simpa [Real.dist_eq] using hN x hx.le⟩
  · intro h
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N + 1, fun x hx => by simpa [Real.dist_eq] using hN x (by linarith)⟩

/-- OpenStax Calculus 1:§4.6 Definition (formal infinite limit at infinity) (CA-156). `f x → ∞`
as `x → ∞` iff `f x` exceeds every bound `M` once `x` is large enough. -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (formal infinite limit at infinity), p. 368"]
theorem tendsto_atTop_atTop_iff_bound {f : ℝ → ℝ} :
    Tendsto f atTop atTop ↔ ∀ M : ℝ, ∃ N : ℝ, ∀ x > N, M < f x := by
  rw [tendsto_atTop_atTop]
  constructor
  · intro h M
    obtain ⟨N, hN⟩ := h (M + 1)
    exact ⟨N, fun x hx => by have := hN x hx.le; linarith⟩
  · intro h M
    obtain ⟨N, hN⟩ := h M
    exact ⟨N + 1, fun x hx => (hN x (by linarith)).le⟩

/-- OpenStax Calculus 1:§4.6 Limit laws remark (CA-157). The sum law holds at `+∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Limit laws remark, p. 364"]
theorem tendsto_add_atTop {f g : ℝ → ℝ} {L M : ℝ} (hf : Tendsto f atTop (𝓝 L))
    (hg : Tendsto g atTop (𝓝 M)) : Tendsto (fun x => f x + g x) atTop (𝓝 (L + M)) :=
  hf.add hg

/-- OpenStax Calculus 1:§4.6 Limit laws remark (CA-157). The product law holds at `+∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Limit laws remark, p. 364"]
theorem tendsto_mul_atTop {f g : ℝ → ℝ} {L M : ℝ} (hf : Tendsto f atTop (𝓝 L))
    (hg : Tendsto g atTop (𝓝 M)) : Tendsto (fun x => f x * g x) atTop (𝓝 (L * M)) :=
  hf.mul hg

/-- OpenStax Calculus 1:§4.6 Limit laws remark (CA-157). Squeeze theorem at `+∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Limit laws remark, p. 364"]
theorem squeeze_atTop {f g h : ℝ → ℝ} {L : ℝ} (hf : Tendsto f atTop (𝓝 L))
    (hh : Tendsto h atTop (𝓝 L)) (h1 : ∀ x, f x ≤ g x) (h2 : ∀ x, g x ≤ h x) :
    Tendsto g atTop (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hf hh h1 h2

/-- OpenStax Calculus 1:§4.6 Limit laws remark (CA-157). Squeeze theorem at `-∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Limit laws remark, p. 364"]
theorem squeeze_atBot {f g h : ℝ → ℝ} {L : ℝ} (hf : Tendsto f atBot (𝓝 L))
    (hh : Tendsto h atBot (𝓝 L)) (h1 : ∀ x, f x ≤ g x) (h2 : ∀ x, g x ≤ h x) :
    Tendsto g atBot (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hf hh h1 h2

/-- OpenStax Calculus 1:§4.6 End behavior for polynomial functions (CA-159). A real polynomial
is asymptotic to its leading term as `x → +∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior for polynomial functions, p. 371"]
theorem polynomial_asymptotic_leading_term (p : Polynomial ℝ) :
    (fun x => p.eval x) ~[atTop] fun x => p.leadingCoeff * x ^ p.natDegree :=
  p.isEquivalent_atTop_lead

/-- OpenStax Calculus 1:§4.6 End behavior for polynomial functions (CA-159). A nonconstant
polynomial with positive leading coefficient tends to `+∞` as `x → +∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior for polynomial functions, p. 371"]
theorem polynomial_tendsto_atTop (p : Polynomial ℝ) (hdeg : 0 < p.degree)
    (hlead : 0 ≤ p.leadingCoeff) : Tendsto (fun x => p.eval x) atTop atTop :=
  Polynomial.tendsto_atTop_of_leadingCoeff_nonneg p hdeg hlead

/-- OpenStax Calculus 1:§4.6 End behavior for rational functions (CA-160). If `deg p < deg q`
then `p/q → 0` as `x → +∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior for rational functions, p. 372"]
theorem rational_tendsto_zero (p q : Polynomial ℝ) (hdeg : p.degree < q.degree) :
    Tendsto (fun x => p.eval x / q.eval x) atTop (𝓝 0) :=
  Polynomial.div_tendsto_atTop_zero_of_degree_lt p q hdeg

/-- OpenStax Calculus 1:§4.6 End behavior for rational functions (CA-160). If `deg p = deg q`
then `p/q` tends to the ratio of leading coefficients. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior for rational functions, p. 372"]
theorem rational_tendsto_leading_ratio (p q : Polynomial ℝ) (hdeg : p.degree = q.degree) :
    Tendsto (fun x => p.eval x / q.eval x) atTop (𝓝 (p.leadingCoeff / q.leadingCoeff)) :=
  Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq p q hdeg

/-- OpenStax Calculus 1:§4.6 End behavior for rational functions (CA-160). If `deg p > deg q`
and the leading-coefficient ratio is nonnegative, `p/q → +∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior for rational functions, p. 372"]
theorem rational_tendsto_atTop_of_degree_gt (p q : Polynomial ℝ) (hdeg : q.degree < p.degree)
    (hq : q ≠ 0) (hlead : 0 ≤ p.leadingCoeff / q.leadingCoeff) :
    Tendsto (fun x => p.eval x / q.eval x) atTop atTop :=
  Polynomial.div_tendsto_atTop_of_degree_gt p q hdeg hq hlead

/-- OpenStax Calculus 1:§4.6 End behavior for rational functions (CA-160). If `deg p > deg q`
and the leading-coefficient ratio is nonpositive, `p/q → -∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior for rational functions, p. 372"]
theorem rational_tendsto_atBot_of_degree_gt (p q : Polynomial ℝ) (hdeg : q.degree < p.degree)
    (hq : q ≠ 0) (hlead : p.leadingCoeff / q.leadingCoeff ≤ 0) :
    Tendsto (fun x => p.eval x / q.eval x) atTop atBot :=
  Polynomial.div_tendsto_atBot_of_degree_gt p q hdeg hq hlead

/-- OpenStax Calculus 1:Table 4.5 (CA-162). End behavior of the exponential: `e^x → ∞` at `+∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of exponential and logarithm, p. 377"]
theorem exp_tendsto_atTop : Tendsto Real.exp atTop atTop :=
  Real.tendsto_exp_atTop

/-- OpenStax Calculus 1:§4.6 End behavior of exponential (CA-162). `e^x → 0` as `x → -∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of exponential and logarithm, p. 377"]
theorem exp_tendsto_zero_atBot : Tendsto Real.exp atBot (𝓝 0) :=
  Real.tendsto_exp_atBot

/-- OpenStax Calculus 1:§4.6 End behavior of logarithm (CA-162). `ln x → ∞` as `x → ∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of exponential and logarithm, p. 377"]
theorem log_tendsto_atTop : Tendsto Real.log atTop atTop :=
  Real.tendsto_log_atTop

/-- OpenStax Calculus 1:§4.6 End behavior of logarithm (CA-162). `ln x → -∞` as `x → 0⁺`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of exponential and logarithm, p. 377"]
theorem log_tendsto_atBot_zero_right : Tendsto Real.log (𝓝[>] 0) atBot :=
  Real.tendsto_log_nhdsGT_zero

/-- OpenStax Calculus 1:Theorem 4.12 (CA-163). L'Hôpital's rule for the `0/0` form at a point:
if `f, g → 0` at `a`, `g' ≠ 0` near `a` and `f'/g'` has limit `l` (any filter limit, finite or
infinite), then `f/g` has the same limit. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.12, p. 404"]
theorem lhopital_zero_over_zero {f f' g g' : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hff' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[≠] a) (𝓝 0)) (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[≠] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l :=
  HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv

/-- OpenStax Calculus 1:Example 4.41 (CA-166). `x ln x → 0` as `x → 0⁺`. -/
@[kb "openstaxcalculus2016" "1:Example 4.41, p. 408"]
theorem x_mul_log_tendsto_zero : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  simpa using this

/-- OpenStax Calculus 1:Example 4.43 (CA-167). `x^(1/x) → 1` as `x → ∞`. -/
@[kb "openstaxcalculus2016" "1:Example 4.43, p. 410"]
theorem rpow_one_div_tendsto_one : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / x)) atTop (𝓝 1) :=
  tendsto_rpow_div

/-- OpenStax Calculus 1:Example 4.45 (CA-170). `e^x` grows faster than every power: `e^x / x^p → ∞`. -/
@[kb "openstaxcalculus2016" "1:Example 4.45, p. 413"]
theorem exp_div_rpow_tendsto_atTop (p : ℝ) :
    Tendsto (fun x : ℝ => Real.exp x / x ^ p) atTop atTop :=
  tendsto_exp_div_rpow_atTop p

/-- OpenStax Calculus 1:Example 4.45 (CA-171). `ln x` grows slower than every positive power:
`ln x / x^p → 0` as `x → ∞`, for `p > 0`. -/
@[kb "openstaxcalculus2016" "1:Example 4.45, p. 414"]
theorem log_div_rpow_tendsto_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => Real.log x / x ^ p) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero

/-! ## Results proved in this library -/

/-- OpenStax Calculus 1:Theorem 4.3 (CA-143). For `f` continuous on `[a, b]`, any absolute extremum
on `[a, b]` is at an endpoint or at a critical point, and both extrema exist at such points. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.3, p. 332"]
theorem extrema_at_endpoint_or_critical_point {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    (∀ x ∈ Icc a b, IsMaxOn f (Icc a b) x →
      x = a ∨ x = b ∨ UndergradKB.Calculus.IsCriticalPoint1 f (Icc a b) x) ∧
    (∀ x ∈ Icc a b, IsMinOn f (Icc a b) x →
      x = a ∨ x = b ∨ UndergradKB.Calculus.IsCriticalPoint1 f (Icc a b) x) ∧
    ((∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x ∧
        (x = a ∨ x = b ∨ UndergradKB.Calculus.IsCriticalPoint1 f (Icc a b) x)) ∧
      (∃ x ∈ Icc a b, IsMinOn f (Icc a b) x ∧
        (x = a ∨ x = b ∨ UndergradKB.Calculus.IsCriticalPoint1 f (Icc a b) x))) :=
  ⟨fun _ hx h => UndergradKB.Calculus.isMaxOn_Icc_endpoint_or_critical hx h,
    fun _ hx h => UndergradKB.Calculus.isMinOn_Icc_endpoint_or_critical hx h,
    UndergradKB.Calculus.exists_extrema_endpoint_or_critical hab hf⟩

/-- OpenStax Calculus 1:Theorem 4.9 (CA-149). First derivative test at `c`, for `f` continuous at
`c` and differentiable near `c` (except possibly at `c`): `+` to `-` gives a local maximum, `-` to
`+` a local minimum, and no sign change gives no local extremum. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.9, p. 349"]
theorem first_derivative_test {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcont : ContinuousAt f c) (hd : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ f x) :
    ((∀ x ∈ Ioo a c, 0 < deriv f x) → (∀ x ∈ Ioo c b, deriv f x < 0) → IsLocalMax f c) ∧
    ((∀ x ∈ Ioo a c, deriv f x < 0) → (∀ x ∈ Ioo c b, 0 < deriv f x) → IsLocalMin f c) ∧
    ((∀ x ∈ Ioo a c, 0 < deriv f x) → (∀ x ∈ Ioo c b, 0 < deriv f x) → ¬ IsLocalExtr f c) ∧
    ((∀ x ∈ Ioo a c, deriv f x < 0) → (∀ x ∈ Ioo c b, deriv f x < 0) → ¬ IsLocalExtr f c) :=
  ⟨fun h1 h2 => UndergradKB.Calculus.first_derivative_test_max hac hcb hcont hd h1 h2,
    fun h1 h2 => UndergradKB.Calculus.first_derivative_test_min hac hcb hcont hd h1 h2,
    fun h1 h2 => UndergradKB.Calculus.first_derivative_test_no_change_pos hac hcb hcont hd h1 h2,
    fun h1 h2 => UndergradKB.Calculus.first_derivative_test_no_change_neg hac hcb hcont hd h1 h2⟩

/-- OpenStax Calculus 1:Theorem 4.13 (CA-164). L'Hôpital's rule for the `∞/∞` form: if `|g| → ∞`
and `f'/g'` has limit `L`, then `f/g` has limit `L`; stated for `x → a` from the right, from the
left, from both sides, and for `x → +∞` and `x → -∞`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.13, p. 406"]
theorem lhopital_infinity_over_infinity :
    (∀ {f g f' g' : ℝ → ℝ} {a L : ℝ},
      (∀ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x) → (∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x) →
      (∀ᶠ x in 𝓝[>] a, g' x ≠ 0) → Tendsto (fun x => |g x|) (𝓝[>] a) atTop →
      Tendsto (fun x => f' x / g' x) (𝓝[>] a) (𝓝 L) →
      Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L)) ∧
    (∀ {f g f' g' : ℝ → ℝ} {a L : ℝ},
      (∀ᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x) → (∀ᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x) →
      (∀ᶠ x in 𝓝[<] a, g' x ≠ 0) → Tendsto (fun x => |g x|) (𝓝[<] a) atTop →
      Tendsto (fun x => f' x / g' x) (𝓝[<] a) (𝓝 L) →
      Tendsto (fun x => f x / g x) (𝓝[<] a) (𝓝 L)) ∧
    (∀ {f g f' g' : ℝ → ℝ} {a L : ℝ},
      (∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x) → (∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x) →
      (∀ᶠ x in 𝓝[≠] a, g' x ≠ 0) → Tendsto (fun x => |g x|) (𝓝[≠] a) atTop →
      Tendsto (fun x => f' x / g' x) (𝓝[≠] a) (𝓝 L) →
      Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 L)) ∧
    (∀ {f g f' g' : ℝ → ℝ} {L : ℝ},
      (∀ᶠ x in atTop, HasDerivAt f (f' x) x) → (∀ᶠ x in atTop, HasDerivAt g (g' x) x) →
      (∀ᶠ x in atTop, g' x ≠ 0) → Tendsto (fun x => |g x|) atTop atTop →
      Tendsto (fun x => f' x / g' x) atTop (𝓝 L) →
      Tendsto (fun x => f x / g x) atTop (𝓝 L)) ∧
    (∀ {f g f' g' : ℝ → ℝ} {L : ℝ},
      (∀ᶠ x in atBot, HasDerivAt f (f' x) x) → (∀ᶠ x in atBot, HasDerivAt g (g' x) x) →
      (∀ᶠ x in atBot, g' x ≠ 0) → Tendsto (fun x => |g x|) atBot atTop →
      Tendsto (fun x => f' x / g' x) atBot (𝓝 L) →
      Tendsto (fun x => f x / g x) atBot (𝓝 L)) :=
  ⟨@UndergradKB.Calculus.lhopital_infty_nhdsGT, @UndergradKB.Calculus.lhopital_infty_nhdsLT,
    @UndergradKB.Calculus.lhopital_infty_nhdsNE, @UndergradKB.Calculus.lhopital_infty_atTop,
    @UndergradKB.Calculus.lhopital_infty_atBot⟩

/-- OpenStax Calculus 1:§4.9 Newton's method iteration formula (Equation 4.8) (CA-172). The Newton
iterates satisfy `x_{n+1} = x_n - f(x_n)/f'(x_n)`, and for `f` twice continuously differentiable with
a simple root `r`, they converge quadratically to `r` from any start close enough to `r`. -/
@[kb "openstaxcalculus2016" "1:§4.9 Newton's method iteration formula (Equation 4.8), p. 418"]
theorem newtons_method {f : ℝ → ℝ} {r : ℝ} (hf : ContDiff ℝ 2 f) (hr : f r = 0)
    (hr' : deriv f r ≠ 0) :
    (∀ (f' : ℝ → ℝ) (x₀ : ℝ) (n : ℕ), UndergradKB.Calculus.newtonSeq f f' x₀ (n + 1) =
      UndergradKB.Calculus.newtonSeq f f' x₀ n -
        f (UndergradKB.Calculus.newtonSeq f f' x₀ n) / f' (UndergradKB.Calculus.newtonSeq f f' x₀ n)) ∧
    ∃ δ > 0, ∃ C : ℝ, ∀ x₀, |x₀ - r| ≤ δ →
      (∀ n, |UndergradKB.Calculus.newtonSeq f (deriv f) x₀ (n + 1) - r| ≤
        C * |UndergradKB.Calculus.newtonSeq f (deriv f) x₀ n - r| ^ 2) ∧
      Tendsto (UndergradKB.Calculus.newtonSeq f (deriv f) x₀) atTop (𝓝 r) :=
  ⟨fun f' x₀ n => Function.iterate_succ_apply' (UndergradKB.Calculus.newtonStep f f') n x₀,
    UndergradKB.Calculus.newton_local_convergence_of_contDiff hf hr hr'⟩

/-- OpenStax Calculus 1:Theorem 4.15 (CA-175). For `n ≠ -1`, `x^(n+1)/(n+1)` is an antiderivative
of `x^n` (real exponents on `x > 0`, integer exponents away from `0`, natural exponents
everywhere). -/
@[kb "openstaxcalculus2016" "1:Theorem 4.15, p. 430"]
theorem antiderivative_power_rule :
    (∀ {n : ℝ}, n ≠ -1 → UndergradKB.Calculus.IsAntiderivOn (fun x => x ^ (n + 1) / (n + 1))
      (fun x => x ^ n) (Ioi 0)) ∧
    (∀ {n : ℤ}, n ≠ -1 → ∀ {I : Set ℝ}, (∀ x ∈ I, x ≠ 0) →
      UndergradKB.Calculus.IsAntiderivOn (fun x => x ^ (n + 1) / ((n : ℝ) + 1))
        (fun x => x ^ n) I) ∧
    (∀ n : ℕ, UndergradKB.Calculus.IsAntiderivOn (fun x => x ^ (n + 1) / ((n : ℝ) + 1))
      (fun x => x ^ n) univ) :=
  ⟨@UndergradKB.Calculus.isAntiderivOn_rpow, @UndergradKB.Calculus.isAntiderivOn_zpow,
    UndergradKB.Calculus.isAntiderivOn_pow⟩

/-- OpenStax Calculus 1:Table 4.13 Integration Formulas (CA-176). Antiderivatives of the basic
functions `e^x`, `1/x`, `sin`, `cos`, `sec²`, `sec tan`, `csc²`, `csc cot`, `1/√(1-x²)` and
`1/(1+x²)`, each on its natural domain. -/
@[kb "openstaxcalculus2016" "1:Table 4.13 Integration Formulas, p. 431"]
theorem table_of_antiderivatives :
    UndergradKB.Calculus.IsAntiderivOn Real.exp Real.exp univ ∧
    UndergradKB.Calculus.IsAntiderivOn Real.log (fun x => 1 / x) {x | x ≠ 0} ∧
    UndergradKB.Calculus.IsAntiderivOn (fun x => -Real.cos x) Real.sin univ ∧
    UndergradKB.Calculus.IsAntiderivOn Real.sin Real.cos univ ∧
    UndergradKB.Calculus.IsAntiderivOn Real.tan (fun x => 1 / Real.cos x ^ 2)
      {x | Real.cos x ≠ 0} ∧
    UndergradKB.Calculus.IsAntiderivOn (fun x => 1 / Real.cos x)
      (fun x => 1 / Real.cos x * (Real.sin x / Real.cos x)) {x | Real.cos x ≠ 0} ∧
    UndergradKB.Calculus.IsAntiderivOn (fun x => -(Real.cos x / Real.sin x))
      (fun x => 1 / Real.sin x ^ 2) {x | Real.sin x ≠ 0} ∧
    UndergradKB.Calculus.IsAntiderivOn (fun x => -(1 / Real.sin x))
      (fun x => 1 / Real.sin x * (Real.cos x / Real.sin x)) {x | Real.sin x ≠ 0} ∧
    UndergradKB.Calculus.IsAntiderivOn Real.arcsin (fun x => 1 / √(1 - x ^ 2)) (Ioo (-1) 1) ∧
    UndergradKB.Calculus.IsAntiderivOn Real.arctan (fun x => 1 / (1 + x ^ 2)) univ :=
  ⟨UndergradKB.Calculus.isAntiderivOn_exp, UndergradKB.Calculus.isAntiderivOn_inv,
    UndergradKB.Calculus.isAntiderivOn_sin, UndergradKB.Calculus.isAntiderivOn_cos,
    UndergradKB.Calculus.isAntiderivOn_sec_sq, UndergradKB.Calculus.isAntiderivOn_sec_tan,
    UndergradKB.Calculus.isAntiderivOn_csc_sq, UndergradKB.Calculus.isAntiderivOn_csc_cot,
    UndergradKB.Calculus.isAntiderivOn_arcsin, UndergradKB.Calculus.isAntiderivOn_arctan⟩

/-- OpenStax Calculus 1:Theorem 4.16 (CA-177). Antiderivatives respect sums, differences and
constant multiples. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.16, p. 433"]
theorem antiderivative_linearity {F G f g : ℝ → ℝ} {I : Set ℝ}
    (hF : UndergradKB.Calculus.IsAntiderivOn F f I) (hG : UndergradKB.Calculus.IsAntiderivOn G g I) :
    UndergradKB.Calculus.IsAntiderivOn (fun x => F x + G x) (fun x => f x + g x) I ∧
    UndergradKB.Calculus.IsAntiderivOn (fun x => F x - G x) (fun x => f x - g x) I ∧
    ∀ k : ℝ, UndergradKB.Calculus.IsAntiderivOn (fun x => k * F x) (fun x => k * f x) I :=
  ⟨hF.add hG, hF.sub hG, fun k => hF.const_mul k⟩

/-! ## Wave 3: further results -/

/-- OpenStax Calculus 1:Example 4.7 (CA-134). For small `x`, `(1 + x)^n` is approximately `1 + n x`:
the derivative at `0` is `n` and the error is little-o of `x`. -/
@[kb "openstaxcalculus2016" "1:Example 4.7, p. 319"]
theorem linearization_one_add_rpow (n : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + x) ^ n) n 0 ∧
    (fun x : ℝ => (1 + x) ^ n - (1 + n * x)) =o[𝓝 0] fun x => x :=
  ⟨UndergradKB.Calculus.hasDerivAt_one_add_rpow n, UndergradKB.Calculus.one_add_rpow_isLittleO n⟩

/-- OpenStax Calculus 1:§4.3 Definition (critical point) (CA-142). A critical point of `f` is an
interior point `c` of the domain `D` where `f` is not differentiable or `f'(c) = 0`. -/
@[kb "openstaxcalculus2016" "1:§4.3 Definition (critical point), p. 329"]
theorem critical_point_def (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) :
    UndergradKB.Calculus.IsCriticalPoint1 f D c ↔
      c ∈ interior D ∧ (¬DifferentiableAt ℝ f c ∨ deriv f c = 0) :=
  Iff.rfl

/-- OpenStax Calculus 1:§4.5 Definition (concave up, concave down) (CA-150). A differentiable `f` is
concave up (down) on `I` when `f'` is strictly increasing (decreasing) there; on an open interval
this agrees with strict convexity (concavity). -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (concave up, concave down), p. 352"]
theorem concave_up_down_def (f : ℝ → ℝ) (I : Set ℝ) :
    (UndergradKB.Calculus.ConcaveUpOn f I ↔ DifferentiableOn ℝ f I ∧ StrictMonoOn (deriv f) I) ∧
    (UndergradKB.Calculus.ConcaveDownOn f I ↔ DifferentiableOn ℝ f I ∧ StrictAntiOn (deriv f) I) ∧
    (IsOpen I → Convex ℝ I → UndergradKB.Calculus.ConcaveUpOn f I → StrictConvexOn ℝ I f) ∧
    (IsOpen I → Convex ℝ I → UndergradKB.Calculus.ConcaveDownOn f I → StrictConcaveOn ℝ I f) :=
  ⟨Iff.rfl, Iff.rfl, UndergradKB.Calculus.ConcaveUpOn.strictConvexOn,
    UndergradKB.Calculus.ConcaveDownOn.strictConcaveOn⟩

/-- OpenStax Calculus 1:§4.5 Definition (inflection point) (CA-152). `(c, f c)` is an inflection
point when `f` is continuous at `c` and the concavity changes at `c`; a sign change of `f''` from
positive to negative gives one. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (inflection point), p. 353"]
theorem inflection_point_def (f : ℝ → ℝ) (c : ℝ) :
    (UndergradKB.Calculus.IsInflectionPoint f c ↔
      ContinuousAt f c ∧ ∃ a b, a < c ∧ c < b ∧
        (UndergradKB.Calculus.ConcaveUpOn f (Set.Ioo a c) ∧
            UndergradKB.Calculus.ConcaveDownOn f (Set.Ioo c b) ∨
          UndergradKB.Calculus.ConcaveDownOn f (Set.Ioo a c) ∧
            UndergradKB.Calculus.ConcaveUpOn f (Set.Ioo c b))) ∧
    (∀ {a b : ℝ}, a < c → c < b → ContinuousAt f c →
      (∀ x ∈ Set.Ioo a b, x ≠ c → DifferentiableAt ℝ f x) →
      (∀ x ∈ Set.Ioo a b, x ≠ c → DifferentiableAt ℝ (deriv f) x) →
      (∀ x ∈ Set.Ioo a c, 0 < deriv (deriv f) x) →
      (∀ x ∈ Set.Ioo c b, deriv (deriv f) x < 0) →
      UndergradKB.Calculus.IsInflectionPoint f c) :=
  ⟨Iff.rfl, fun {_ _} => UndergradKB.Calculus.isInflectionPoint_of_deriv2_sign_change⟩

/-- OpenStax Calculus 1:§4.6 Definition (horizontal asymptote) (CA-155). The line `y = L` is a
horizontal asymptote when `f` tends to `L` at `+∞` or at `-∞`; for example `y = 0` for `1/x`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (horizontal asymptote), p. 363"]
theorem horizontal_asymptote_def (f : ℝ → ℝ) (L : ℝ) :
    (UndergradKB.Calculus.IsHorizontalAsymptote f L ↔
      Tendsto f atTop (𝓝 L) ∨ Tendsto f atBot (𝓝 L)) ∧
    UndergradKB.Calculus.IsHorizontalAsymptote (fun x => 1 / x) 0 :=
  ⟨Iff.rfl, UndergradKB.Calculus.isHorizontalAsymptote_inv⟩

/-- OpenStax Calculus 1:§4.6 End behavior of power functions (CA-158). For a positive integer `n`,
`x^n → +∞` at `+∞`; at `-∞` it tends to `+∞` for even `n` and `-∞` for odd `n`; a positive (negative)
coefficient keeps (flips) the sign at `+∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of power functions, p. 370"]
theorem end_behavior_power_functions {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => x ^ n) atTop atTop ∧
    (Even n → Tendsto (fun x : ℝ => x ^ n) atBot atTop) ∧
    (Odd n → Tendsto (fun x : ℝ => x ^ n) atBot atBot) ∧
    (∀ c : ℝ, 0 < c → Tendsto (fun x : ℝ => c * x ^ n) atTop atTop) ∧
    (∀ c : ℝ, c < 0 → Tendsto (fun x : ℝ => c * x ^ n) atTop atBot) :=
  ⟨UndergradKB.Calculus.tendsto_pow_atTop_kb hn,
    fun h => UndergradKB.Calculus.tendsto_pow_atBot_even h hn,
    fun h => UndergradKB.Calculus.tendsto_pow_atBot_odd h,
    fun _ hc => (UndergradKB.Calculus.tendsto_pow_atTop_kb hn).const_mul_atTop hc,
    fun _ hc => (UndergradKB.Calculus.tendsto_pow_atTop_kb hn).const_mul_atTop_of_neg hc⟩

/-- OpenStax Calculus 1:§4.6 Definition (oblique asymptote) (CA-161). When `deg p = deg q + 1`, long
division gives `p / q = m x + b` plus a remainder part, and `p/q` approaches the line `y = m x + b`
at both infinities. -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (oblique asymptote), p. 375"]
theorem oblique_asymptote_def (f : ℝ → ℝ) (m b : ℝ) (p q : Polynomial ℝ) (hq : q ≠ 0)
    (hdeg : p.degree = q.degree + 1) :
    (UndergradKB.Calculus.IsObliqueAsymptote f m b ↔
      m ≠ 0 ∧ (Tendsto (fun x => f x - (m * x + b)) atTop (𝓝 0) ∨
        Tendsto (fun x => f x - (m * x + b)) atBot (𝓝 0))) ∧
    ∃ m b : ℝ, p / q = Polynomial.C m * Polynomial.X + Polynomial.C b ∧ m ≠ 0 ∧
      Tendsto (fun x => Polynomial.eval x p / Polynomial.eval x q - (m * x + b)) atTop (𝓝 0) ∧
      Tendsto (fun x => Polynomial.eval x p / Polynomial.eval x q - (m * x + b)) atBot (𝓝 0) :=
  ⟨Iff.rfl, UndergradKB.Calculus.rational_oblique_asymptote p q hq hdeg⟩

/-- OpenStax Calculus 1:Example 4.44 (CA-168). `x^x → 1` as `x → 0⁺`, an indeterminate form of type
`0^0`; this rests on `x ln x → 0` and `ln x * x^r → 0`. -/
@[kb "openstaxcalculus2016" "1:Example 4.44, p. 411"]
theorem limit_x_pow_x_zero_right :
    Tendsto (fun x : ℝ => x ^ x) (𝓝[>] 0) (𝓝 1) ∧
    Continuous (fun x : ℝ => x * Real.log x) ∧
    (∀ {r : ℝ}, 0 < r → Tendsto (fun x : ℝ => Real.log x * x ^ r) (𝓝[>] 0) (𝓝 0)) :=
  ⟨UndergradKB.Calculus.tendsto_rpow_self_zero_right, Real.continuous_mul_log,
    @tendsto_log_mul_rpow_nhdsGT_zero⟩

/-- OpenStax Calculus 1:§4.8 Growth rates definition (CA-169). `f` grows faster than `g` when `f/g`
tends to `+∞`, and at the same rate when `f/g` tends to a nonzero constant; `e^x` outgrows every
power and every positive power outgrows `ln`. -/
@[kb "openstaxcalculus2016" "1:§4.8 Growth rates definition, p. 412"]
theorem growth_rates_def (f g : ℝ → ℝ) :
    (UndergradKB.Calculus.GrowsFasterThan f g ↔ Tendsto (fun x => f x / g x) atTop atTop) ∧
    (UndergradKB.Calculus.SameGrowthRate f g ↔
      ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun x => f x / g x) atTop (𝓝 c)) ∧
    (∀ n : ℕ, UndergradKB.Calculus.GrowsFasterThan Real.exp fun x => x ^ n) ∧
    (∀ {r : ℝ}, 0 < r → UndergradKB.Calculus.GrowsFasterThan (fun x => x ^ r) Real.log) :=
  ⟨Iff.rfl, Iff.rfl, UndergradKB.Calculus.exp_growsFasterThan_pow,
    @UndergradKB.Calculus.rpow_growsFasterThan_log⟩

/-- OpenStax Calculus 1:§4.10 Definition (antiderivative) (CA-173). `F` is an antiderivative of `f`
on `I` when `F' = f` at every point of `I`; two antiderivatives on an interval differ by a
constant. -/
@[kb "openstaxcalculus2016" "1:§4.10 Definition (antiderivative), p. 428"]
theorem antiderivative_def (F f : ℝ → ℝ) (I : Set ℝ) :
    (UndergradKB.Calculus.IsAntiderivOn F f I ↔ ∀ x ∈ I, HasDerivAt F (f x) x) ∧
    (∀ {G : ℝ → ℝ}, I.OrdConnected → UndergradKB.Calculus.IsAntiderivOn F f I →
      UndergradKB.Calculus.IsAntiderivOn G f I → ∃ C, ∀ x ∈ I, F x = G x + C) :=
  ⟨Iff.rfl, fun {_} => UndergradKB.Calculus.IsAntiderivOn.eq_add_const⟩

end UndergradKB.Calculus.Course.V1C4
