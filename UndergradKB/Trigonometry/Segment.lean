import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import UndergradKB.Common.Attr

/-! # Area of a circular segment (Corral §4.3)

The segment of the disc of radius `r` cut off by a chord whose central angle is `θ` (`0 ≤ θ ≤ 2π`) is placed
symmetrically about the positive `x`-axis: the chord joins the points of angles `±θ/2`, i.e. lies on the line
`x = r cos (θ/2)`, and the segment is the part of the open disc beyond it (`circSegment r θ`). Its area, as the
Lebesgue measure on `ℝ × ℝ`, is `½ r² (θ - sin θ)` (`volume_circSegment`).

Proof: the segment is the region between the graphs of `∓√(r² - x²)` over `r cos (θ/2) < x < r`
(`MeasureTheory.volume_regionBetween_eq_integral`), and `x √(r² - x²) + r² arcsin (x / r)` is an antiderivative
of `2 √(r² - x²)`.
-/

namespace UndergradKB.Trigonometry

open Real Set MeasureTheory

/-- The circular segment of the open disc of radius `r` centred at the origin cut off by the chord through the
points of angles `±θ/2`: the points of the disc with `x > r cos (θ/2)`. -/
def circSegment (r θ : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < r ^ 2 ∧ r * cos (θ / 2) < p.1}

/-- The ends of the chord, `(r cos (θ/2), ± r sin (θ/2))`, lie on the circle and on the line bounding the
segment. -/
theorem chord_ends_on_circle (r θ : ℝ) :
    (r * cos (θ / 2)) ^ 2 + (r * sin (θ / 2)) ^ 2 = r ^ 2 ∧
      (r * cos (θ / 2)) ^ 2 + (-(r * sin (θ / 2))) ^ 2 = r ^ 2 := by
  constructor <;> nlinarith [sin_sq_add_cos_sq (θ / 2)]

private lemma circSegment_eq {r θ : ℝ} (hr : 0 < r) :
    circSegment r θ = regionBetween (fun x => -√(r ^ 2 - x ^ 2)) (fun x => √(r ^ 2 - x ^ 2))
      (Ioo (r * cos (θ / 2)) r) := by
  ext ⟨x, y⟩
  simp only [circSegment, regionBetween, mem_ofPred_eq, mem_Ioo]
  have key : y ^ 2 < r ^ 2 - x ^ 2 ↔ -√(r ^ 2 - x ^ 2) < y ∧ y < √(r ^ 2 - x ^ 2) := by
    rw [← abs_lt, Real.lt_sqrt (abs_nonneg y), sq_abs]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h2, ?_⟩, key.1 (by linarith)⟩
    nlinarith [sq_nonneg y]
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨by linarith [key.2 h3], h1⟩

private lemma hasDerivAt_antideriv {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun x => x * √(r ^ 2 - x ^ 2) + r ^ 2 * arcsin (x / r)) (2 * √(r ^ 2 - x ^ 2)) x := by
  have hpos : 0 < r ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1 : x / r ≠ -1 := by
    intro h; rw [div_eq_iff hr.ne'] at h; linarith [hx.1]
  have h2 : x / r ≠ 1 := by
    intro h; rw [div_eq_iff hr.ne'] at h; linarith [hx.2]
  have hs : HasDerivAt (fun x => √(r ^ 2 - x ^ 2)) ((-(2 * x)) / (2 * √(r ^ 2 - x ^ 2))) x := by
    have := ((hasDerivAt_pow 2 x).const_sub (r ^ 2)).sqrt hpos.ne'
    convert this using 1; simp
  have ha := (Real.hasDerivAt_arcsin h1 h2).comp x ((hasDerivAt_id x).div_const r)
  have := ((hasDerivAt_id x).mul hs).add (ha.const_mul (r ^ 2))
  convert this using 1
  · rfl
  set S := √(r ^ 2 - x ^ 2) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 hpos
  have hS2 : S ^ 2 = r ^ 2 - x ^ 2 := Real.sq_sqrt hpos.le
  have hsq : √(1 - (x / r) ^ 2) = S / r := by
    rw [show 1 - (x / r) ^ 2 = (r ^ 2 - x ^ 2) / r ^ 2 by field_simp, Real.sqrt_div hpos.le,
      Real.sqrt_sq hr.le]
  simp only [id]
  rw [hsq]
  field_simp
  linarith [hS2]

/-- **Area of a circular segment** (Corral §4.3): the segment cut off by a chord with central angle `θ`
(`0 ≤ θ ≤ 2π`) in a circle of radius `r > 0` has area `½ r² (θ - sin θ)`. (TR-086) -/
@[kb "corraltrig" "Box §4.3 (area of a segment), p. 104"]
theorem volume_circSegment {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) (hθ' : θ ≤ 2 * π) :
    volume (circSegment r θ) = ENNReal.ofReal (r ^ 2 * (θ - sin θ) / 2) := by
  set c := r * cos (θ / 2) with hc
  have hc1 : -r ≤ c := by
    have := neg_one_le_cos (θ / 2); nlinarith
  have hc2 : c ≤ r := by
    have := cos_le_one (θ / 2); nlinarith
  have hcont : Continuous fun x : ℝ => √(r ^ 2 - x ^ 2) := by fun_prop
  rw [circSegment_eq hr, Measure.volume_eq_prod,
    volume_regionBetween_eq_integral
      ((show Continuous fun x : ℝ => -√(r ^ 2 - x ^ 2) by fun_prop).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self)
      (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo
      (fun x _ => neg_le_self (Real.sqrt_nonneg _))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc2]
  have hfun : (fun x => √(r ^ 2 - x ^ 2)) - (fun x => -√(r ^ 2 - x ^ 2)) =
      fun x => 2 * √(r ^ 2 - x ^ 2) := by
    funext x; simp only [Pi.sub_apply]; ring
  rw [hfun, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc2 (by fun_prop)
    (fun x hx => hasDerivAt_antideriv hr ⟨by linarith [hx.1], hx.2⟩)
    ((continuous_const.mul hcont).intervalIntegrable _ _)]
  have hθ2 : 0 ≤ θ / 2 := by linarith
  have hθ2' : θ / 2 ≤ π := by linarith
  have hsin : 0 ≤ sin (θ / 2) := sin_nonneg_of_nonneg_of_le_pi hθ2 hθ2'
  have hsq : √(r ^ 2 - c ^ 2) = r * sin (θ / 2) := by
    rw [show r ^ 2 - c ^ 2 = (r * sin (θ / 2)) ^ 2 by rw [hc]; nlinarith [sin_sq_add_cos_sq (θ / 2)],
      Real.sqrt_sq (mul_nonneg hr.le hsin)]
  have harc : arcsin (c / r) = π / 2 - θ / 2 := by
    rw [hc, mul_div_cancel_left₀ _ hr.ne', arcsin_eq_pi_div_two_sub_arccos, arccos_cos hθ2 hθ2']
  simp only [sub_self, Real.sqrt_zero, mul_zero, zero_add, div_self hr.ne', arcsin_one, hsq, harc]
  have h2 : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
    rw [← sin_two_mul]; ring_nf
  rw [h2, hc]
  ring

end UndergradKB.Trigonometry
