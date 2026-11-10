import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UndergradKB.Common.Attr

/-! # Calculus: the fundamental theorem and techniques of integration (part 1)

OpenStax Calculus 1 §§5.3-5.5 and Calculus 2 §§1.1-1.4, 3.1: variable limits, symmetry, substitution, parts. -/

open MeasureTheory Set Real intervalIntegral

namespace UndergradKB.Calculus

/-- OpenStax Calculus 1:Example 5.18 (CA-198): for continuous `f` and a differentiable `u`,
`d/dx ∫_a^{u x} f = f (u x) * u' x`. -/
@[kb "openstaxcalculus2016" "1:Example 5.18, p. 485"]
theorem hasDerivAt_integral_upper {f : ℝ → ℝ} (hf : Continuous f) {u : ℝ → ℝ} {u' x : ℝ}
    (hu : HasDerivAt u u' x) (a : ℝ) :
    HasDerivAt (fun x => ∫ t in a..u x, f t) (f (u x) * u') x :=
  (hf.integral_hasStrictDerivAt a (u x)).hasDerivAt.comp x hu

/-- OpenStax Calculus 1:Example 5.19 (CA-198): `d/dx ∫_{g x}^{h x} f = f (h x) h' x - f (g x) g' x`. -/
@[kb "openstaxcalculus2016" "1:Example 5.19, p. 485"]
theorem hasDerivAt_integral_both {f : ℝ → ℝ} (hf : Continuous f) {g h : ℝ → ℝ} {g' h' x : ℝ}
    (hg : HasDerivAt g g' x) (hh : HasDerivAt h h' x) :
    HasDerivAt (fun x => ∫ t in g x..h x, f t) (f (h x) * h' - f (g x) * g') x := by
  have := (hasDerivAt_integral_upper hf hh 0).sub (hasDerivAt_integral_upper hf hg 0)
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  rw [integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

/-- Helper: for continuous `f`, `∫_{-a}^0 f x = ∫_0^a f (-x)`. -/
private lemma integral_neg_half {f : ℝ → ℝ} (a : ℝ) :
    ∫ x in (-a)..0, f x = ∫ x in (0 : ℝ)..a, f (-x) := by
  rw [intervalIntegral.integral_comp_neg (fun x => f x)]
  simp

/-- OpenStax Calculus 1:§5.4 Rule (CA-202): for even continuous `f`, `∫_{-a}^a f = 2 ∫_0^a f`. -/
@[kb "openstaxcalculus2016" "1:§5.4 Rule (integrals of even and odd functions), p. 501"]
theorem integral_symm_even {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ)
    (heven : ∀ x, f (-x) = f x) :
    ∫ x in (-a)..a, f x = 2 * ∫ x in (0 : ℝ)..a, f x := by
  rw [← integral_add_adjacent_intervals (hf.intervalIntegrable (-a) 0) (hf.intervalIntegrable 0 a),
    integral_neg_half]
  simp only [heven]
  ring

/-- OpenStax Calculus 1:§5.4 Rule (CA-202): for odd continuous `f`, `∫_{-a}^a f = 0`. -/
@[kb "openstaxcalculus2016" "1:§5.4 Rule (integrals of even and odd functions), p. 501"]
theorem integral_symm_odd {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ)
    (hodd : ∀ x, f (-x) = -f x) :
    ∫ x in (-a)..a, f x = 0 := by
  rw [← integral_add_adjacent_intervals (hf.intervalIntegrable (-a) 0) (hf.intervalIntegrable 0 a),
    integral_neg_half]
  simp only [hodd, intervalIntegral.integral_neg]
  ring

/-- OpenStax Calculus 1:Theorem 5.7 (CA-203): if `F' = f` and `g` is differentiable, then
`F ∘ g` is an antiderivative of `f (g x) * g' x`. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.7, p. 515"]
theorem hasDerivAt_comp_antiderivative {F f g g' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) :
    ∀ x, HasDerivAt (fun x => F (g x)) (f (g x) * g' x) x :=
  fun x => (hF (g x)).comp x (hg x)

/-- OpenStax Calculus 1:Theorem 5.7, definite form (CA-203): for `g` with continuous derivative and
`f` continuous, `∫_a^b f (g x) g' x dx = ∫_{g a}^{g b} f`. -/
@[kb "openstaxcalculus2016" "1:Theorem 5.7, p. 515"]
theorem integral_substitution {f g g' : ℝ → ℝ} (hf : Continuous f) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hg' : Continuous g') (a b : ℝ) :
    ∫ x in a..b, f (g x) * g' x = ∫ u in g a..g b, f u :=
  integral_comp_mul_deriv (fun x _ => hg x) hg'.continuousOn hf

/-- OpenStax Calculus 2:Theorem 3.1 (CA-213), antiderivative form: if `u`, `v` are differentiable and
`H' = v u'` then `u v - H` is an antiderivative of `u v'` (that is, `∫ u dv = u v - ∫ v du`). -/
@[kb "openstaxcalculus2016" "2:Theorem 3.1, p. 240"]
theorem hasDerivAt_parts_antiderivative {u v u' v' H : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hH : ∀ x, HasDerivAt H (v x * u' x) x) :
    ∀ x, HasDerivAt (fun x => u x * v x - H x) (u x * v' x) x := by
  intro x
  have := ((hu x).mul (hv x)).sub (hH x)
  convert this using 1
  ring

/-- OpenStax Calculus 2:Theorem 3.1 (CA-213), definite form for continuously differentiable `u`, `v`:
`∫_a^b u v' = u b v b - u a v a - ∫_a^b u' v`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.1, p. 240"]
theorem integral_parts {u v u' v' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hu' : Continuous u') (hv' : Continuous v') (a b : ℝ) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul (fun x _ => hu x) (fun x _ => hv x)
    (hu'.intervalIntegrable _ _) (hv'.intervalIntegrable _ _)

end UndergradKB.Calculus
