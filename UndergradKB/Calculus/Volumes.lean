import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Measure
import UndergradKB.Calculus.MassCentroid
import UndergradKB.Common.Attr

/-! # Calculus: volumes of solids

OpenStax Calculus 1 §§6.2-6.3 and Calculus 2 §§2.2-2.3: slicing, disks, washers, cylindrical shells. Solids live
in `ℝ × ℝ × ℝ` with Lebesgue measure `volume`, and volumes are genuine measures (values in `ℝ≥0∞`). -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-- Area of a closed disk of radius `r` in the plane `ℝ × ℝ`. -/
lemma volume_disk (r : ℝ) (hr : 0 ≤ r) :
    volume {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2} = ENNReal.ofReal (π * r ^ 2) := by
  have h1 : {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2} =
      Complex.measurableEquivRealProd.symm ⁻¹' Metric.closedBall (0 : ℂ) r := by
    ext q
    simp only [mem_ofPred_eq, mem_preimage, Complex.measurableEquivRealProd_symm_apply,
      Metric.mem_closedBall, dist_zero_right, Complex.norm_def]
    rw [Complex.normSq_apply]
    rw [Real.sqrt_le_left hr]
    constructor <;> intro h <;> nlinarith
  rw [h1, Complex.volume_preserving_equiv_real_prod.symm.measure_preimage
    measurableSet_closedBall.nullMeasurableSet, Complex.volume_closedBall]
  rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr, mul_comm]
  congr 1
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- Area of an open disk of radius `r` in the plane `ℝ × ℝ`. -/
lemma volume_opendisk (r : ℝ) (hr : 0 ≤ r) :
    volume {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} = ENNReal.ofReal (π * r ^ 2) := by
  have h1 : {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < r ^ 2} =
      Complex.measurableEquivRealProd.symm ⁻¹' Metric.ball (0 : ℂ) r := by
    ext q
    simp only [mem_ofPred_eq, mem_preimage, Complex.measurableEquivRealProd_symm_apply,
      Metric.mem_ball, dist_zero_right, Complex.norm_def]
    rw [Complex.normSq_apply]
    have hs : 0 ≤ q.1 * q.1 + q.2 * q.2 :=
      add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    rw [← Real.sqrt_sq hr, Real.sqrt_lt_sqrt_iff hs, Real.sqrt_sq hr]
    constructor <;> intro h <;> nlinarith
  rw [h1, Complex.volume_preserving_equiv_real_prod.symm.measure_preimage
    measurableSet_ball.nullMeasurableSet, Complex.volume_ball]
  rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr, mul_comm]
  congr 1
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- OpenStax Calculus 1:§6.2 slicing method (CA-253), measure-theoretic form. The volume of a measurable solid
`S ⊆ ℝ × (ℝ × ℝ)` is the (lower) integral of the areas of its cross-sections `{q | (x, q) ∈ S}` perpendicular to
the first axis. -/
@[kb "openstaxcalculus2016" "1:§6.2 slicing method, p. 561"]
theorem volume_eq_lintegral_slices {S : Set (ℝ × ℝ × ℝ)} (hS : MeasurableSet S) :
    volume S = ∫⁻ x, volume (Prod.mk x ⁻¹' S) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod_apply hS

/-- OpenStax Calculus 1:§6.2 slicing method (CA-253), calculus form. If the cross-section of a measurable solid at
`x ∈ [a, b]` is the plane set `T x` with area `A x` (continuous, nonnegative), and the solid lies over `[a, b]`,
then the volume is `∫_a^b A`. -/
@[kb "openstaxcalculus2016" "1:§6.2 slicing method, p. 561"]
theorem volume_solid_of_slices {a b : ℝ} (hab : a ≤ b) (T : ℝ → Set (ℝ × ℝ)) (A : ℝ → ℝ)
    (hS : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1})
    (hA : ContinuousOn A (Icc a b)) (hA0 : ∀ x ∈ Icc a b, 0 ≤ A x)
    (hT : ∀ x ∈ Icc a b, volume (T x) = ENNReal.ofReal (A x)) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1} = ENNReal.ofReal (∫ x in a..b, A x) := by
  rw [volume_eq_lintegral_slices hS]
  have h1 : ∀ x, volume (Prod.mk x ⁻¹' {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1}) =
      (Icc a b).indicator (fun x => ENNReal.ofReal (A x)) x := by
    intro x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx, ← hT x hx]
      congr 1
      ext q
      simp only [mem_preimage, mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    · rw [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ T p.1} = ∅ := by
        ext q
        simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hx h.1
      rw [this, measure_empty]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (hA.integrableOn_Icc)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hA0)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- Measurability of the solids `{p | p.1 ∈ [a,b] ∧ p.2 ∈ T p.1}` below, used for the disk and washer solids. -/
lemma measurableSet_solid_of_cont {a b : ℝ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ g p.1 ^ 2 ≤ p.2.1 ^ 2 + p.2.2 ^ 2 ∧
      p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} := by
  have h1 : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b} :=
    measurableSet_Icc.preimage measurable_fst
  have h2 : MeasurableSet {p : ℝ × ℝ × ℝ | g p.1 ^ 2 ≤ p.2.1 ^ 2 + p.2.2 ^ 2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h3 : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

/-- OpenStax Calculus 1:§6.2 Rule: The Disk Method (6.3) (CA-256). Revolving the region under `y = f x`
(`f` continuous) over `[a, b]` about the `x`-axis gives the solid `{(x, y, z) | x ∈ [a, b], y² + z² ≤ f(x)²}`;
its volume is `π ∫_a^b f²`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: The Disk Method (6.3), p. 566"]
theorem volume_disk_method {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} =
      ENNReal.ofReal (π * ∫ x in a..b, f x ^ 2) := by
  have hm := measurableSet_solid_of_cont (a := a) (b := b) hf (g := fun _ => 0) continuous_const
  have key := volume_solid_of_slices hab (fun x => {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ f x ^ 2})
    (fun x => π * f x ^ 2) ?_ (by fun_prop) (fun x _ => by positivity) ?_
  · rw [intervalIntegral.integral_const_mul] at key
    convert key using 3
  · convert hm using 2
    ext p
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using add_nonneg (sq_nonneg p.2.1) (sq_nonneg p.2.2), h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  · intro x _
    have := volume_disk (|f x|) (abs_nonneg _)
    rwa [sq_abs] at this

/-- OpenStax Calculus 1:§6.2 Rule: The Washer Method (6.5) (CA-258). The region between `0 ≤ g ≤ f` over `[a, b]`
revolved about the `x`-axis is `{(x, y, z) | x ∈ [a, b], g(x)² ≤ y² + z² ≤ f(x)²}`; its volume is
`π ∫_a^b (f² - g²)`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: The Washer Method (6.5), p. 570"]
theorem volume_washer_method {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) (hgf : ∀ x ∈ Icc a b, g x ≤ f x) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ g p.1 ^ 2 ≤ p.2.1 ^ 2 + p.2.2 ^ 2 ∧
      p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} =
      ENNReal.ofReal (π * ∫ x in a..b, (f x ^ 2 - g x ^ 2)) := by
  have hm := measurableSet_solid_of_cont (a := a) (b := b) hf hg
  have key := volume_solid_of_slices hab
    (fun x => {q : ℝ × ℝ | g x ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 ∧ q.1 ^ 2 + q.2 ^ 2 ≤ f x ^ 2})
    (fun x => π * (f x ^ 2 - g x ^ 2)) hm (by fun_prop)
    (fun x hx => by
      have := hgf x hx
      have := hg0 x hx
      have : g x ^ 2 ≤ f x ^ 2 := by nlinarith
      exact mul_nonneg pi_pos.le (by linarith)) ?_
  · rw [intervalIntegral.integral_const_mul] at key
    exact key
  · intro x hx
    have hgx := hg0 x hx
    have hfx : 0 ≤ f x := hgx.trans (hgf x hx)
    have hset : {q : ℝ × ℝ | g x ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 ∧ q.1 ^ 2 + q.2 ^ 2 ≤ f x ^ 2} =
        {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ f x ^ 2} \ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < g x ^ 2} := by
      ext q
      simp only [mem_ofPred_eq, mem_sdiff, not_lt]
      tauto
    have hsub : {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < g x ^ 2} ⊆ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ f x ^ 2} := by
      intro q hq
      have : g x ^ 2 ≤ f x ^ 2 := by nlinarith [hgf x hx]
      simp only [mem_ofPred_eq] at hq ⊢
      linarith
    have hmeas : MeasurableSet {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < g x ^ 2} :=
      measurableSet_lt (by fun_prop) (by fun_prop)
    rw [hset, measure_sdiff hsub hmeas.nullMeasurableSet (by rw [volume_opendisk _ hgx]; exact ENNReal.ofReal_ne_top),
      volume_disk _ hfx, volume_opendisk _ hgx, ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    ring_nf

/-- The coordinate change `(x, y, z) ↦ (y, x, z)` preserves volume (used to move the axis of revolution from the
`x`-axis to the `y`-axis). -/
theorem measurePreserving_swap12 :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.2.1, p.1, p.2.2)) volume volume := by
  have h1 := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)).symm
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have h3 := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ)
  exact h3.comp (h2.comp h1)

/-- OpenStax Calculus 1:§6.2 Rule: Disk Method around the y-axis (6.4) (CA-257). The region between `x = g(y)`
and the `y`-axis over `[c, d]` revolved about the `y`-axis is `{(x, y, z) | y ∈ [c, d], x² + z² ≤ g(y)²}`; its
volume is `π ∫_c^d g²`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: Disk Method around the y-axis (6.4), p. 568"]
theorem volume_disk_method_y {c d : ℝ} (hcd : c ≤ d) {g : ℝ → ℝ} (hg : Continuous g) :
    volume {p : ℝ × ℝ × ℝ | p.2.1 ∈ Icc c d ∧ p.1 ^ 2 + p.2.2 ^ 2 ≤ g p.2.1 ^ 2} =
      ENNReal.ofReal (π * ∫ y in c..d, g y ^ 2) := by
  have hm := measurableSet_solid_of_cont (a := c) (b := d) hg (g := fun _ => 0) continuous_const
  have hS : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc c d ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ g p.1 ^ 2} := by
    have h1 : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc c d} :=
      measurableSet_Icc.preimage measurable_fst
    have h3 : MeasurableSet {p : ℝ × ℝ × ℝ | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ g p.1 ^ 2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact h1.inter h3
  rw [← volume_disk_method hcd hg, ← measurePreserving_swap12.measure_preimage hS.nullMeasurableSet]
  rfl

/-- OpenStax Calculus 1:§6.2 Rule: Washer Method around the y-axis (CA-259). The region between `0 ≤ u ≤ v` over
`[c, d]` (as functions of `y`) revolved about the `y`-axis is
`{(x, y, z) | y ∈ [c, d], u(y)² ≤ x² + z² ≤ v(y)²}`; its volume is `π ∫_c^d (v² - u²)`. -/
@[kb "openstaxcalculus2016" "1:§6.2 Rule: Washer Method around the y-axis, p. 571"]
theorem volume_washer_method_y {c d : ℝ} (hcd : c ≤ d) {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ y ∈ Icc c d, 0 ≤ u y) (huv : ∀ y ∈ Icc c d, u y ≤ v y) :
    volume {p : ℝ × ℝ × ℝ | p.2.1 ∈ Icc c d ∧ u p.2.1 ^ 2 ≤ p.1 ^ 2 + p.2.2 ^ 2 ∧
      p.1 ^ 2 + p.2.2 ^ 2 ≤ v p.2.1 ^ 2} =
      ENNReal.ofReal (π * ∫ y in c..d, (v y ^ 2 - u y ^ 2)) := by
  have hS := measurableSet_solid_of_cont (a := c) (b := d) hv hu
  rw [← volume_washer_method hcd hv hu hu0 huv, ← measurePreserving_swap12.measure_preimage hS.nullMeasurableSet]
  rfl

/-- OpenStax Calculus 1:Example 6.6 (CA-254). A pyramid of height `h` over a square base of side `a`, with apex on
the `x`-axis at `x = h` and base in the plane `x = 0`, has volume `a² h / 3`. The cross-section at `x` is the
square of side `a (h - x) / h`. -/
@[kb "openstaxcalculus2016" "1:Example 6.6, p. 561"]
theorem volume_pyramid {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc 0 h ∧ |p.2.1| ≤ a * (h - p.1) / (2 * h) ∧
      |p.2.2| ≤ a * (h - p.1) / (2 * h)} = ENNReal.ofReal (a ^ 2 * h / 3) := by
  have hS : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc 0 h ∧ |p.2.1| ≤ a * (h - p.1) / (2 * h) ∧
      |p.2.2| ≤ a * (h - p.1) / (2 * h)} := by
    have h1 : MeasurableSet {p : ℝ × ℝ × ℝ | p.1 ∈ Icc 0 h} :=
      measurableSet_Icc.preimage measurable_fst
    have h2 : MeasurableSet {p : ℝ × ℝ × ℝ | |p.2.1| ≤ a * (h - p.1) / (2 * h)} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h3 : MeasurableSet {p : ℝ × ℝ × ℝ | |p.2.2| ≤ a * (h - p.1) / (2 * h)} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter h3)
  have key := volume_solid_of_slices (a := 0) (b := h) hh.le
    (fun x => Icc (-(a * (h - x) / (2 * h))) (a * (h - x) / (2 * h)) ×ˢ
      Icc (-(a * (h - x) / (2 * h))) (a * (h - x) / (2 * h)))
    (fun x => a ^ 2 * (h - x) ^ 2 / h ^ 2) ?_ (by fun_prop) (fun x _ => by positivity) ?_
  · have hint : ∫ x in (0 : ℝ)..h, a ^ 2 * (h - x) ^ 2 / h ^ 2 = a ^ 2 * h / 3 := by
      have : ∀ x : ℝ, a ^ 2 * (h - x) ^ 2 / h ^ 2 = (a ^ 2 / h ^ 2) * (h - x) ^ 2 := fun x => by ring
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (fun x => x ^ 2) h]
      simp only [integral_pow, sub_self, sub_zero]
      field_simp
      ring
    rw [hint] at key
    convert key using 2
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  · convert hS using 2
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  · intro x hx
    have hw : 0 ≤ a * (h - x) / (2 * h) := by
      have : 0 ≤ h - x := by linarith [hx.2]
      positivity
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
    congr 1
    field_simp
    ring

/-- OpenStax Calculus 3:Example 5.32 Analysis (CA-576). A right circular cone of base radius `R` and height `h`
(apex at the origin, axis the `x`-axis, base in the plane `x = h`) has volume `π R² h / 3`; it is the solid of
revolution of `y = R x / h`. -/
@[kb "openstaxcalculus2016" "3:Example 5.32 Analysis, p. 480"]
theorem volume_cone {R h : ℝ} (hh : 0 < h) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc 0 h ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (R * p.1 / h) ^ 2} =
      ENNReal.ofReal (π * R ^ 2 * h / 3) := by
  rw [volume_disk_method hh.le (f := fun x => R * x / h) (by fun_prop)]
  congr 1
  have : ∀ x : ℝ, (R * x / h) ^ 2 = (R ^ 2 / h ^ 2) * x ^ 2 := fun x => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  simp only [integral_pow]
  field_simp
  ring

/-- Polar coordinates in the plane: the lintegral of a function of the radius `√(x² + z²)`, supported on the
annulus `a ≤ r ≤ b`, is `2π ∫_a^b r f(r) dr`. -/
lemma lintegral_radial {a b : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) :
    ∫⁻ q : ℝ × ℝ, (Icc a b).indicator (fun ρ => ENNReal.ofReal (f ρ)) (√(q.1 ^ 2 + q.2 ^ 2)) =
      ENNReal.ofReal (2 * π * ∫ x in Icc a b, x * f x) := by
  set F : ℝ × ℝ → ENNReal := fun q => (Icc a b).indicator (fun ρ => ENNReal.ofReal (f ρ)) (√(q.1 ^ 2 + q.2 ^ 2))
    with hF
  rw [← lintegral_comp_polarCoord_symm F]
  have h1 : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • F (polarCoord.symm p) =
      (Icc a b).indicator (fun r => ENNReal.ofReal (r * f r)) p.1 := by
    intro p hp
    have hr : 0 < p.1 := hp.1
    have hsq : √((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) = p.1 := by
      have : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
        have := Real.sin_sq_add_cos_sq p.2
        nlinarith
      rw [this, Real.sqrt_sq hr.le]
    simp only [hF, polarCoord_symm_apply, hsq, smul_eq_mul]
    by_cases hx : p.1 ∈ Icc a b
    · rw [indicator_of_mem hx, indicator_of_mem hx, ← ENNReal.ofReal_mul hr.le]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet h1]
  have htar : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  set G : ℝ → ENNReal := (Icc a b).indicator (fun r => ENNReal.ofReal (r * f r)) with hG
  have hGm : Measurable G :=
    (Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Icc
  have hcont : ContinuousOn (fun r => r * f r) (Icc a b) :=
    (continuous_id.mul hf).continuousOn
  rw [htar, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [lintegral_mul_const _ hGm]
  have hsupp : Function.support G ⊆ Ioi 0 := by
    intro r hr
    by_contra hneg
    apply hr
    have hr0 : r ≤ 0 := not_lt.1 hneg
    by_cases hx : r ∈ Icc a b
    · have : r = 0 := le_antisymm hr0 (ha.trans hx.1)
      simp [hG, this]
    · simp [hG, indicator_of_notMem hx]
  rw [setLIntegral_eq_of_support_subset hsupp, hG, lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (ha.trans hx.1) (hf0 x hx))),
    ← ENNReal.ofReal_mul (setIntegral_nonneg measurableSet_Icc fun x hx =>
      mul_nonneg (ha.trans hx.1) (hf0 x hx))]
  congr 1
  ring

/-- OpenStax Calculus 1:§6.3 Method of Cylindrical Shells around the x-axis (CA-261). The region between `x = 0` and
`x = g(y)` over `y ∈ [c, d]`, `0 ≤ c`, revolved about the `x`-axis, is
`{(x, y, z) | c ≤ √(y² + z²) ≤ d, 0 ≤ x ≤ g(√(y² + z²))}`; its volume is `2π ∫_c^d y g(y) dy`. -/
@[kb "openstaxcalculus2016" "1:§6.3 Method of Cylindrical Shells around the x-axis, p. 582"]
theorem volume_shell_method_x {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ y ∈ Icc c d, 0 ≤ g y) :
    volume {p : ℝ × ℝ × ℝ | c ≤ √(p.2.1 ^ 2 + p.2.2 ^ 2) ∧ √(p.2.1 ^ 2 + p.2.2 ^ 2) ≤ d ∧
      0 ≤ p.1 ∧ p.1 ≤ g (√(p.2.1 ^ 2 + p.2.2 ^ 2))} =
      ENNReal.ofReal (2 * π * ∫ y in c..d, y * g y) := by
  set S' : Set (ℝ × ℝ × ℝ) := {p | c ≤ √(p.2.1 ^ 2 + p.2.2 ^ 2) ∧ √(p.2.1 ^ 2 + p.2.2 ^ 2) ≤ d ∧
      0 ≤ p.1 ∧ p.1 ≤ g (√(p.2.1 ^ 2 + p.2.2 ^ 2))} with hS'
  have hm : MeasurableSet S' := by
    have hsq : Measurable fun p : ℝ × ℝ × ℝ => √(p.2.1 ^ 2 + p.2.2 ^ 2) := by fun_prop
    have hfm : Measurable g := hg.measurable
    exact (measurableSet_le measurable_const hsq).inter
      ((measurableSet_le hsq measurable_const).inter
        ((measurableSet_le measurable_const measurable_fst).inter
          (measurableSet_le measurable_fst (hfm.comp hsq))))
  have h1 : volume S' = ENNReal.ofReal (2 * π * ∫ x in Icc c d, x * g x) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm, ← lintegral_radial hc hg hg0]
    refine lintegral_congr fun q => ?_
    by_cases hx : √(q.1 ^ 2 + q.2 ^ 2) ∈ Icc c d
    · rw [indicator_of_mem hx]
      have : (fun y : ℝ => (y, q)) ⁻¹' S' = Icc 0 (g (√(q.1 ^ 2 + q.2 ^ 2))) := by
        ext y
        simp only [hS', mem_preimage, mem_ofPred_eq, mem_Icc]
        exact ⟨fun h => h.2.2, fun h => ⟨hx.1, hx.2, h⟩⟩
      rw [this, Real.volume_Icc, sub_zero]
    · rw [indicator_of_notMem hx]
      have : (fun y : ℝ => (y, q)) ⁻¹' S' = ∅ := by
        ext y
        simp only [hS', mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hx ⟨h.1, h.2.1⟩
      rw [this, measure_empty]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd] at h1
  exact h1

/-- OpenStax Calculus 1:§6.3 Rule: The Method of Cylindrical Shells (6.6) (CA-260). The region under `y = f(x) ≥ 0`
over `[a, b]` (`0 ≤ a`) revolved about the `y`-axis is
`{(x, y, z) | a ≤ √(x² + z²) ≤ b, 0 ≤ y ≤ f(√(x² + z²))}`; its volume is `2π ∫_a^b x f(x) dx`. -/
@[kb "openstaxcalculus2016" "1:§6.3 Rule: The Method of Cylindrical Shells (6.6), p. 580"]
theorem volume_shell_method {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) :
    volume {p : ℝ × ℝ × ℝ | a ≤ √(p.1 ^ 2 + p.2.2 ^ 2) ∧ √(p.1 ^ 2 + p.2.2 ^ 2) ≤ b ∧
      0 ≤ p.2.1 ∧ p.2.1 ≤ f (√(p.1 ^ 2 + p.2.2 ^ 2))} =
      ENNReal.ofReal (2 * π * ∫ x in a..b, x * f x) := by
  have hm : MeasurableSet {p : ℝ × ℝ × ℝ | a ≤ √(p.2.1 ^ 2 + p.2.2 ^ 2) ∧ √(p.2.1 ^ 2 + p.2.2 ^ 2) ≤ b ∧
      0 ≤ p.1 ∧ p.1 ≤ f (√(p.2.1 ^ 2 + p.2.2 ^ 2))} := by
    have hsq : Measurable fun p : ℝ × ℝ × ℝ => √(p.2.1 ^ 2 + p.2.2 ^ 2) := by fun_prop
    have hfm : Measurable f := hf.measurable
    exact (measurableSet_le measurable_const hsq).inter
      ((measurableSet_le hsq measurable_const).inter
        ((measurableSet_le measurable_const measurable_fst).inter
          (measurableSet_le measurable_fst (hfm.comp hsq))))
  rw [← volume_shell_method_x ha hab hf hf0, ← measurePreserving_swap12.measure_preimage hm.nullMeasurableSet]
  rfl

/-- OpenStax Calculus 1:§6.3 shell formula for the axis `x = -k` (CA-262). The region under `y = f(x) ≥ 0` over
`[a, b]` (with `0 ≤ a + k`) revolved about the vertical line `x = -k` (in the plane `z = 0`) is
`{(x, y, z) | a + k ≤ √((x+k)² + z²) ≤ b + k, 0 ≤ y ≤ f(√((x+k)² + z²) - k)}`; its volume is
`2π ∫_a^b (x + k) f(x) dx`. -/
@[kb "openstaxcalculus2016" "1:§6.3 shell formula for axis x=-k, p. 583"]
theorem volume_shell_method_shifted {a b k : ℝ} (ha : 0 ≤ a + k) (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : Continuous f) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) :
    volume {p : ℝ × ℝ × ℝ | a + k ≤ √((p.1 + k) ^ 2 + p.2.2 ^ 2) ∧ √((p.1 + k) ^ 2 + p.2.2 ^ 2) ≤ b + k ∧
      0 ≤ p.2.1 ∧ p.2.1 ≤ f (√((p.1 + k) ^ 2 + p.2.2 ^ 2) - k)} =
      ENNReal.ofReal (2 * π * ∫ x in a..b, (x + k) * f x) := by
  have h := volume_shell_method (a := a + k) (b := b + k) ha (by linarith) (f := fun r => f (r - k))
    (by fun_prop) (fun x hx => hf0 _ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hint : ∫ x in (a + k)..(b + k), x * f (x - k) = ∫ x in a..b, (x + k) * f x := by
    have := intervalIntegral.integral_comp_add_right (a := a) (b := b) (fun x => (x) * f (x - k)) k
    simp only [add_sub_cancel_right] at this
    exact this.symm
  rw [hint] at h
  have hsq : Measurable fun p : ℝ × ℝ × ℝ => √(p.1 ^ 2 + p.2.2 ^ 2) := by fun_prop
  have hfm : Measurable fun r => f (r - k) := by fun_prop
  have hm : MeasurableSet {p : ℝ × ℝ × ℝ | a + k ≤ √(p.1 ^ 2 + p.2.2 ^ 2) ∧ √(p.1 ^ 2 + p.2.2 ^ 2) ≤ b + k ∧
      0 ≤ p.2.1 ∧ p.2.1 ≤ f (√(p.1 ^ 2 + p.2.2 ^ 2) - k)} :=
    (measurableSet_le measurable_const hsq).inter
      ((measurableSet_le hsq measurable_const).inter
        ((measurableSet_le measurable_const
            (measurable_fst.comp measurable_snd : Measurable fun p : ℝ × ℝ × ℝ => p.2.1)).inter
          (measurableSet_le (measurable_fst.comp measurable_snd : Measurable fun p : ℝ × ℝ × ℝ => p.2.1)
            (hfm.comp hsq))))
  have hmp : MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.1 + k, p.2)) volume volume :=
    (measurePreserving_add_right (volume : Measure ℝ) k).prod
      (MeasurePreserving.id (volume : Measure (ℝ × ℝ)))
  rw [← h, ← hmp.measure_preimage hm.nullMeasurableSet]
  rfl

/-- OpenStax Calculus 1:Theorem 6.8 (CA-269). A disk of radius `r` with radial
density `ρ(‖q‖)` has mass `∬_disk ρ(‖q‖) = 2π ∫_0^r x ρ(x) dx`, as a lower Lebesgue integral. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.8, p. 605"]
theorem lintegral_disk_radial {r : ℝ} (hr : 0 ≤ r) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hρ0 : ∀ x ∈ Icc 0 r, 0 ≤ ρ x) :
    ∫⁻ q in {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2}, ENNReal.ofReal (ρ (√(q.1 ^ 2 + q.2 ^ 2))) =
      ENNReal.ofReal (2 * π * ∫ x in (0 : ℝ)..r, x * ρ x) := by
  have hm : MeasurableSet {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h1 : ∀ q : ℝ × ℝ, {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2}.indicator
      (fun q => ENNReal.ofReal (ρ (√(q.1 ^ 2 + q.2 ^ 2)))) q =
      (Icc 0 r).indicator (fun x => ENNReal.ofReal (ρ x)) (√(q.1 ^ 2 + q.2 ^ 2)) := by
    intro q
    have hs : 0 ≤ q.1 ^ 2 + q.2 ^ 2 := by positivity
    have hiff : q ∈ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2} ↔ √(q.1 ^ 2 + q.2 ^ 2) ∈ Icc 0 r := by
      simp only [mem_ofPred_eq, mem_Icc]
      rw [Real.sqrt_le_left hr]
      exact ⟨fun h => ⟨Real.sqrt_nonneg _, h⟩, fun h => h.2⟩
    by_cases hq : q ∈ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2}
    · rw [indicator_of_mem hq, indicator_of_mem (hiff.1 hq)]
    · rw [indicator_of_notMem hq, indicator_of_notMem (fun h => hq (hiff.2 h))]
  rw [← lintegral_indicator hm]
  simp_rw [h1]
  rw [lintegral_radial le_rfl hρ hρ0, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]

/-- OpenStax Calculus 1:Theorem 6.14 (CA-280), Pappus. A region between `0 ≤ g ≤ f` (continuous, over `[a, b]`,
nondegenerate: positive area `A`) revolved about the `x`-axis, which it does not cross, sweeps a solid of volume
`2π ȳ A`, where `ȳ` is the `y`-coordinate of the centroid (constant density `1`) and `A` its area. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.14, p. 631"]
theorem pappus_x_axis {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) (hgf : ∀ x ∈ Icc a b, g x ≤ f x)
    (hA : 0 < volume.real (lamina f g a b)) :
    volume {p : ℝ × ℝ × ℝ | p.1 ∈ Icc a b ∧ g p.1 ^ 2 ≤ p.2.1 ^ 2 + p.2.2 ^ 2 ∧
      p.2.1 ^ 2 + p.2.2 ^ 2 ≤ f p.1 ^ 2} =
      ENNReal.ofReal (2 * π * (laminaCenter 1 (lamina f g a b)).2 * volume.real (lamina f g a b)) := by
  rw [volume_washer_method hab hf hg hg0 hgf]
  obtain ⟨h1, h2, -⟩ := lamina_mass_moments hf hg hab hgf 1
  congr 1
  have hm : laminaMass 1 (lamina f g a b) = volume.real (lamina f g a b) := by simp [laminaMass]
  have hne : laminaMass 1 (lamina f g a b) ≠ 0 := by rw [hm]; exact hA.ne'
  have hx : (laminaCenter 1 (lamina f g a b)).2 =
      (∫ x in a..b, (f x ^ 2 - g x ^ 2) / 2) / volume.real (lamina f g a b) := by
    simp only [laminaCenter]
    rw [h2, hm]
    ring
  have hA' := hA.ne'
  rw [hx, intervalIntegral.integral_div]
  field_simp

end UndergradKB.Calculus
