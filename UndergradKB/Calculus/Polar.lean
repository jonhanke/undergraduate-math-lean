import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import UndergradKB.Common.Attr

/-! # Calculus: polar coordinates

Mathlib has the polar-coordinate change of variables (`polarCoord`, `lintegral_comp_polarCoord_symm`) but works
with `r > 0` and `θ ∈ (-π, π)`.  Here the book's polar points `(r, θ)` (any real `r`, `θ`) are the points
`polarPoint r θ = (r cos θ, r sin θ)` of `ℝ × ℝ`: non-uniqueness of representations, lines and circles, polar
curves as parametric curves, symmetry tests, spirals and roses, area of a polar region (a Lebesgue measure
statement) and the polar arc length integrand. -/

namespace UndergradKB.Calculus

open Real Filter Topology Set intervalIntegral MeasureTheory
open scoped ENNReal

/-- The point of the plane with polar coordinates `(r, θ)` (any real `r` and `θ`). -/
noncomputable def polarPoint (r θ : ℝ) : ℝ × ℝ := (r * cos θ, r * sin θ)

/-! ## Representations, lines and circles -/

/-- OpenStax Calculus 2:§7.3 Non-uniqueness of polar coordinates (CA-401): `(r, θ + 2πn)` is the same point as
`(r, θ)`. -/
@[kb "openstaxcalculus2016" "2:§7.3 Non-uniqueness of polar coordinates, p. 577"]
theorem polarPoint_add_int_mul_two_pi (r θ : ℝ) (n : ℤ) :
    polarPoint r (θ + n * (2 * π)) = polarPoint r θ := by
  simp [polarPoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- OpenStax Calculus 2:§7.3 Non-uniqueness of polar coordinates (CA-401): `(-r, θ + π)` is the same point as
`(r, θ)`. -/
@[kb "openstaxcalculus2016" "2:§7.3 Non-uniqueness of polar coordinates, p. 577"]
theorem polarPoint_neg_add_pi (r θ : ℝ) : polarPoint (-r) (θ + π) = polarPoint r θ := by
  simp [polarPoint]

/-- OpenStax Calculus 2:§7.3 Non-uniqueness of polar coordinates (CA-401): conversely, two representations
with positive radius of the same point have the same radius and angles differing by a multiple of `2π`. -/
@[kb "openstaxcalculus2016" "2:§7.3 Non-uniqueness of polar coordinates, p. 577"]
theorem polarPoint_eq_iff {r r' θ θ' : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    polarPoint r θ = polarPoint r' θ' ↔ r = r' ∧ ∃ n : ℤ, θ' = θ + n * (2 * π) := by
  constructor
  · intro h
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : r ^ 2 = (r * cos θ) ^ 2 + (r * sin θ) ^ 2 := by
      linear_combination (-(r ^ 2)) * sin_sq_add_cos_sq θ
    have e2 : r' ^ 2 = (r' * cos θ') ^ 2 + (r' * sin θ') ^ 2 := by
      linear_combination (-(r' ^ 2)) * sin_sq_add_cos_sq θ'
    have hsq : r ^ 2 = r' ^ 2 := by rw [e1, e2, h1, h2]
    have hrr : r = r' := by
      rcases sq_eq_sq_iff_abs_eq_abs _ _ |>.mp hsq |> fun h => abs_eq_abs.mp h with h | h
      · exact h
      · linarith
    subst hrr
    have hc : cos θ = cos θ' := mul_left_cancel₀ hr.ne' h1
    have hs : sin θ = sin θ' := mul_left_cancel₀ hr.ne' h2
    have hang : ((θ : ℝ) : Real.Angle) = (θ' : Real.Angle) :=
      Real.Angle.cos_sin_inj (by simpa using hc) (by simpa using hs)
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
    exact ⟨rfl, ⟨-k, by push_cast; linarith⟩⟩
  · rintro ⟨rfl, n, rfl⟩
    exact (polarPoint_add_int_mul_two_pi r θ n).symm

/-- OpenStax Calculus 2:Example 7.13 (CA-402): the polar equation `θ = α` describes the line through the pole
(`r` any real number): the points `(r cos α, r sin α)` are exactly the points of `ℝ × ℝ` with
`y cos α = x sin α`; for `cos α ≠ 0` this is `y = tan α · x`. -/
@[kb "openstaxcalculus2016" "2:Example 7.13, p. 580"]
theorem polar_theta_eq_line (α : ℝ) :
    {q : ℝ × ℝ | ∃ r : ℝ, q = polarPoint r α} = {q : ℝ × ℝ | q.2 * cos α = q.1 * sin α} ∧
    (cos α ≠ 0 → {q : ℝ × ℝ | ∃ r : ℝ, q = polarPoint r α} = {q : ℝ × ℝ | q.2 = tan α * q.1}) := by
  have h1 : {q : ℝ × ℝ | ∃ r : ℝ, q = polarPoint r α} = {q : ℝ × ℝ | q.2 * cos α = q.1 * sin α} := by
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, polarPoint, Prod.mk.injEq]
    constructor
    · rintro ⟨r, rfl, rfl⟩
      ring
    · intro h
      refine ⟨x * cos α + y * sin α, ?_, ?_⟩
      · linear_combination (-sin α) * h + (-x) * sin_sq_add_cos_sq α
      · linear_combination (cos α) * h + (-y) * sin_sq_add_cos_sq α
  refine ⟨h1, fun hc => ?_⟩
  rw [h1]
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, tan_eq_sin_div_cos]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- OpenStax Calculus 2:Example 7.13 (CA-402): for `k > 0` the polar equation `r = k` describes the circle of
radius `k` about the origin: `{(k cos θ, k sin θ)} = {x^2 + y^2 = k^2}`. -/
@[kb "openstaxcalculus2016" "2:Example 7.13, p. 580"]
theorem polar_r_eq_circle (k : ℝ) (hk : 0 < k) :
    {q : ℝ × ℝ | ∃ θ : ℝ, q = polarPoint k θ} = {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 = k ^ 2} := by
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq, polarPoint, Prod.mk.injEq]
  constructor
  · rintro ⟨θ, rfl, rfl⟩
    nlinarith [sin_sq_add_cos_sq θ]
  · intro h
    set z : ℂ := ⟨x, y⟩ with hz
    have hn : ‖z‖ = k := by
      rw [Complex.norm_def, Complex.normSq_apply]
      rw [Real.sqrt_eq_iff_mul_self_eq (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) hk.le]
      simp [hz]
      nlinarith
    refine ⟨Complex.arg z, ?_, ?_⟩
    · have := Complex.norm_mul_cos_arg z
      rw [hn] at this
      simpa [hz] using this.symm
    · have := Complex.norm_mul_sin_arg z
      rw [hn] at this
      simpa [hz] using this.symm

/-! ## Polar curves as parametric curves -/

/-- The polar curve `r = f θ` as a parametric curve `θ ↦ (f θ cos θ, f θ sin θ)`. -/
noncomputable def polarCurve (f : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ := polarPoint (f θ) θ

/-- OpenStax Calculus 2:§7.3 Polar curve as parametric curve (CA-405): the points of the polar curve `r = f θ`
are exactly the points `(x(θ), y(θ))` with `x = f θ cos θ`, `y = f θ sin θ`. -/
@[kb "openstaxcalculus2016" "2:§7.3 Polar curve as parametric curve, p. 586"]
theorem polarCurve_range (f : ℝ → ℝ) :
    {q : ℝ × ℝ | ∃ r θ : ℝ, r = f θ ∧ q = polarPoint r θ} = range (polarCurve f) ∧
    ∀ θ, polarCurve f θ = (f θ * cos θ, f θ * sin θ) := by
  refine ⟨?_, fun θ => rfl⟩
  ext q
  simp only [mem_ofPred_eq, mem_range, polarCurve]
  constructor
  · rintro ⟨r, θ, rfl, rfl⟩
    exact ⟨θ, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨f θ, θ, rfl, rfl⟩

/-! ## Symmetry -/

/-- The set of points of the plane having a polar representation in `G ⊆ ℝ × ℝ` (pairs `(r, θ)`). -/
noncomputable def polarImage (G : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := (fun p => polarPoint p.1 p.2) '' G

/-- OpenStax Calculus 2:Theorem 7.5, 3:Theorem 1.5 (CA-406), polar axis: if `(r, θ) ∈ G` implies `(r, -θ) ∈ G`,
the point set is symmetric about the polar axis (`(x, y) ↦ (x, -y)`). -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_symm_axis (G : Set (ℝ × ℝ)) (h : ∀ p ∈ G, (p.1, -p.2) ∈ G) :
    ∀ q ∈ polarImage G, (q.1, -q.2) ∈ polarImage G := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨(p.1, -p.2), h p hp, by simp [polarPoint]⟩

/-- OpenStax Calculus 2:Theorem 7.5 (CA-406), polar axis, alternative test: `(r, θ) ∈ G` implies
`(-r, π - θ) ∈ G`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_symm_axis' (G : Set (ℝ × ℝ)) (h : ∀ p ∈ G, (-p.1, π - p.2) ∈ G) :
    ∀ q ∈ polarImage G, (q.1, -q.2) ∈ polarImage G := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨(-p.1, π - p.2), h p hp, ?_⟩
  simp [polarPoint, Real.cos_pi_sub, Real.sin_pi_sub]

/-- OpenStax Calculus 2:Theorem 7.5 (CA-406), pole: `(r, θ) ∈ G` implies `(-r, θ) ∈ G` gives symmetry about the
pole (`(x, y) ↦ (-x, -y)`). -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_symm_pole (G : Set (ℝ × ℝ)) (h : ∀ p ∈ G, (-p.1, p.2) ∈ G) :
    ∀ q ∈ polarImage G, (-q.1, -q.2) ∈ polarImage G := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨(-p.1, p.2), h p hp, by simp [polarPoint]⟩

/-- OpenStax Calculus 2:Theorem 7.5 (CA-406), pole, alternative test: `(r, θ) ∈ G` implies `(r, θ + π) ∈ G`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_symm_pole' (G : Set (ℝ × ℝ)) (h : ∀ p ∈ G, (p.1, p.2 + π) ∈ G) :
    ∀ q ∈ polarImage G, (-q.1, -q.2) ∈ polarImage G := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨(p.1, p.2 + π), h p hp, ?_⟩
  simp [polarPoint]

/-- OpenStax Calculus 2:Theorem 7.5 (CA-406), line `θ = π/2`: `(r, θ) ∈ G` implies `(r, π - θ) ∈ G` gives
symmetry about the vertical axis (`(x, y) ↦ (-x, y)`). -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_symm_vertical (G : Set (ℝ × ℝ)) (h : ∀ p ∈ G, (p.1, π - p.2) ∈ G) :
    ∀ q ∈ polarImage G, (-q.1, q.2) ∈ polarImage G := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨(p.1, π - p.2), h p hp, ?_⟩
  simp [polarPoint, Real.cos_pi_sub, Real.sin_pi_sub]

/-- OpenStax Calculus 2:Theorem 7.5 (CA-406), line `θ = π/2`, alternative test: `(r, θ) ∈ G` implies
`(-r, -θ) ∈ G`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_symm_vertical' (G : Set (ℝ × ℝ)) (h : ∀ p ∈ G, (-p.1, -p.2) ∈ G) :
    ∀ q ∈ polarImage G, (-q.1, q.2) ∈ polarImage G := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨(-p.1, -p.2), h p hp, ?_⟩
  simp [polarPoint]

/-- OpenStax Calculus 2:Theorem 7.5 (CA-406), for graphs `r = f θ`: if `f (-θ) = f θ` for all `θ`, the curve is
symmetric about the polar axis; if `f (π - θ) = f θ`, about the vertical axis; if `f (θ + π) = f θ`, about the
pole. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.5, p. 586"]
theorem polar_curve_symmetry (f : ℝ → ℝ) :
    ((∀ θ, f (-θ) = f θ) →
      ∀ q ∈ polarImage {p | p.1 = f p.2}, (q.1, -q.2) ∈ polarImage {p | p.1 = f p.2}) ∧
    ((∀ θ, f (π - θ) = f θ) →
      ∀ q ∈ polarImage {p | p.1 = f p.2}, (-q.1, q.2) ∈ polarImage {p | p.1 = f p.2}) ∧
    ((∀ θ, f (θ + π) = f θ) →
      ∀ q ∈ polarImage {p | p.1 = f p.2}, (-q.1, -q.2) ∈ polarImage {p | p.1 = f p.2}) := by
  refine ⟨fun h => polar_symm_axis _ ?_, fun h => polar_symm_vertical _ ?_,
    fun h => polar_symm_pole' _ ?_⟩
  · intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    rw [h, hp]
  · intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    rw [h, hp]
  · intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    rw [h, hp]

/-! ## Spirals and roses -/

/-- The Archimedean spiral `r = a + b θ` (OpenStax Calculus 2:Example 7.14): the radius is an affine function of
the angle (`r = k θ` is the case `a = 0`). -/
noncomputable def archimedeanSpiral (a b θ : ℝ) : ℝ := a + b * θ

/-- A logarithmic spiral `r = a e^{b θ}` (OpenStax Calculus 2:Example 7.14): the radius is exponential in the
angle. -/
noncomputable def logSpiral (a b θ : ℝ) : ℝ := a * exp (b * θ)

/-- OpenStax Calculus 2:Example 7.14 (CA-404): along an Archimedean spiral the radius grows by the constant
amount `2π b` per turn; along a logarithmic spiral it is multiplied by the constant `e^{2π b}` per turn. -/
@[kb "openstaxcalculus2016" "2:Example 7.14, p. 584"]
theorem spiral_per_turn (a b θ : ℝ) :
    archimedeanSpiral a b (θ + 2 * π) = archimedeanSpiral a b θ + 2 * π * b ∧
    logSpiral a b (θ + 2 * π) = logSpiral a b θ * exp (2 * π * b) := by
  unfold archimedeanSpiral logSpiral
  refine ⟨by ring, ?_⟩
  rw [mul_add, exp_add, mul_assoc]
  ring_nf

/-- OpenStax Calculus 2:§7.3 Remark on petals of roses (CA-403), the periodicity part: the rose `r = a cos(nθ)`
with `n` an odd integer returns to the same point after `θ ↦ θ + π` (so the whole curve is traced for
`0 ≤ θ ≤ π`), while for even `n` the rose is traced over a full turn (the radius at `θ + π` is the same
number, the point is the opposite one). -/
@[kb "openstaxcalculus2016" "2:§7.3 Remark on petals of roses, p. 584"]
theorem rose_period (a : ℝ) (n : ℕ) (θ : ℝ) :
    (Odd n → polarPoint (a * cos (n * (θ + π))) (θ + π) = polarPoint (a * cos (n * θ)) θ) ∧
    (Even n → polarPoint (a * cos (n * (θ + π))) (θ + π) = polarPoint (-(a * cos (n * θ))) θ) := by
  have hcos : ∀ k : ℕ, cos (k * (θ + π)) = cos (k * θ + k * π) := fun k => by rw [mul_add]
  refine ⟨fun ⟨m, hm⟩ => ?_, fun ⟨m, hm⟩ => ?_⟩
  · have : cos (n * (θ + π)) = -cos (n * θ) := by
      rw [hcos, hm]
      push_cast
      have : ((2 * m + 1 : ℝ)) * θ + (2 * m + 1) * π = (2 * m + 1) * θ + π + (m : ℤ) * (2 * π) := by
        push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi, Real.cos_add_pi]
    simp [polarPoint, this]
  · have : cos (n * (θ + π)) = cos (n * θ) := by
      rw [hcos, hm]
      push_cast
      have : ((m + m : ℝ)) * θ + (m + m) * π = (m + m) * θ + (m : ℤ) * (2 * π) := by
        push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    simp [polarPoint, this]

/-! ## Area of a polar region -/

theorem radial_lintegral (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ r in Ioc 0 c, ENNReal.ofReal r = ENNReal.ofReal (c ^ 2 / 2) := by
  have h1 : IntegrableOn (fun r : ℝ => r) (Ioc 0 c) := continuous_id.integrableOn_Ioc
  have h2 := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Ioc 0 c)) (f := fun r : ℝ => r)
    h1 (by
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun r hr => ?_)
      exact hr.1.le)
  rw [← h2, ← integral_of_le hc, integral_id]
  congr 1
  ring

theorem region_lintegral (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ θ, 0 ≤ g θ) (α β : ℝ) (hab : α ≤ β) :
    ∫⁻ p in {p : ℝ × ℝ | p.2 ∈ Ico α β ∧ 0 < p.1 ∧ p.1 ≤ g p.2}, ENNReal.ofReal p.1 =
      ENNReal.ofReal (∫ θ in α..β, g θ ^ 2 / 2) := by
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ∈ Ico α β ∧ 0 < p.1 ∧ p.1 ≤ g p.2} with hT
  have hTm : MeasurableSet T := by
    have h1 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ico α β} := measurable_snd measurableSet_Ico
    have h2 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} := measurableSet_lt measurable_const measurable_fst
    have h3 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ g p.2} :=
      measurableSet_le measurable_fst (hg.measurable.comp measurable_snd)
    exact h1.inter (h2.inter h3)
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1) := measurable_fst.ennreal_ofReal
  rw [Measure.volume_eq_prod, ← lintegral_indicator hTm,
    lintegral_prod_symm _ (hmeas.indicator hTm).aemeasurable]
  have hinner : ∀ θ : ℝ, ∫⁻ r : ℝ, T.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) (r, θ) =
      (Ico α β).indicator (fun θ => ENNReal.ofReal (g θ ^ 2 / 2)) θ := by
    intro θ
    by_cases hθ : θ ∈ Ico α β
    · have : (fun r : ℝ => T.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) (r, θ)) =
          (Ioc 0 (g θ)).indicator (fun r => ENNReal.ofReal r) := by
        funext r
        by_cases hr : r ∈ Ioc 0 (g θ)
        · have : (r, θ) ∈ T := ⟨hθ, hr.1, hr.2⟩
          simp [indicator_of_mem this, indicator_of_mem hr]
        · have : (r, θ) ∉ T := fun h => hr ⟨h.2.1, h.2.2⟩
          simp [indicator_of_notMem this, indicator_of_notMem hr]
      rw [this, lintegral_indicator measurableSet_Ioc, radial_lintegral _ (hg0 θ),
        indicator_of_mem hθ]
    · have : (fun r : ℝ => T.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) (r, θ)) = fun _ => 0 := by
        funext r
        have : (r, θ) ∉ T := fun h => hθ h.1
        simp [indicator_of_notMem this]
      rw [this, indicator_of_notMem hθ]
      simp
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_congr Ico_ae_eq_Ioc,
    integral_of_le hab]
  have hcont : Continuous (fun θ => g θ ^ 2 / 2) := (hg.pow 2).div_const 2
  rw [ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Ioc]
  exact (ae_restrict_iff' measurableSet_Ioc).mpr
    (Eventually.of_forall fun r _ => by have := hg0 r; positivity)

/-- The region swept by the polar curve `r = f θ` between the pole and the curve, for `α ≤ θ ≤ β`:
`{(r cos θ, r sin θ) | α ≤ θ ≤ β, 0 ≤ r ≤ f θ}` (OpenStax Calculus 2:Theorem 7.6). -/
def polarRegion (f : ℝ → ℝ) (α β : ℝ) : Set (ℝ × ℝ) :=
  {q | ∃ θ ∈ Icc α β, ∃ r ∈ Icc 0 (f θ), q = polarPoint r θ}

theorem polar_region_volume_aux (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ θ, 0 ≤ g θ) (α β : ℝ)
    (hab : α < β) (h2π : β - α ≤ 2 * π) :
    volume (polarRegion g α β) = ENNReal.ofReal (∫ θ in α..β, g θ ^ 2 / 2) := by
  set T : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 ∈ Ico α β ∧ 0 < p.1 ∧ p.1 ≤ g p.2} with hT
  have hTm : MeasurableSet T := by
    have h1 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ico α β} := measurable_snd measurableSet_Ico
    have h2 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} := measurableSet_lt measurable_const measurable_fst
    have h3 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ g p.2} :=
      measurableSet_le measurable_fst (hg.measurable.comp measurable_snd)
    exact h1.inter (h2.inter h3)
  have hG : ∀ p : ℝ × ℝ, polarCoord.symm p = polarPoint p.1 p.2 := fun p => rfl
  have hinj : InjOn polarCoord.symm T := by
    intro p hp p' hp' h
    rw [hG, hG] at h
    obtain ⟨hr, n, hn⟩ := (polarPoint_eq_iff hp.2.1 hp'.2.1).mp h
    have hn0 : n = 0 := by
      have h1 : (n : ℝ) * (2 * π) < 1 * (2 * π) := by
        have := hp.1.1; have := hp'.1.2; have := hp.1.2; have := hp'.1.1
        nlinarith [hp.1.1, hp'.1.2]
      have h2 : -1 * (2 * π) < (n : ℝ) * (2 * π) := by
        have := hp.1.2; have := hp'.1.1
        nlinarith [hp.1.2, hp'.1.1]
      have hpi := Real.pi_pos
      have h1' : (n : ℝ) < 1 := lt_of_mul_lt_mul_right h1 (by positivity)
      have h2' : (-1 : ℝ) < n := lt_of_mul_lt_mul_right h2 (by positivity)
      have h1'' : n < 1 := by exact_mod_cast h1'
      have h2'' : -1 < n := by exact_mod_cast h2'
      omega
    subst hn0
    exact Prod.ext hr (by simpa using hn.symm)
  have hsub1 : polarCoord.symm '' T ⊆ polarRegion g α β := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.2, ⟨hp.1.1, hp.1.2.le⟩, p.1, ⟨hp.2.1.le, hp.2.2⟩, (hG p)⟩
  -- the line through the pole at angle `β` is null
  set φ : ℝ × ℝ →ₗ[ℝ] ℝ := cos β • LinearMap.snd ℝ ℝ ℝ - sin β • LinearMap.fst ℝ ℝ ℝ with hφ
  have hN : volume (LinearMap.ker φ : Set (ℝ × ℝ)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    have := congrArg (fun L : ℝ × ℝ →ₗ[ℝ] ℝ => L (-sin β, cos β)) h
    simp [hφ] at this
    nlinarith [sin_sq_add_cos_sq β]
  have hsub2 : polarRegion g α β ⊆ polarCoord.symm '' T ∪ (LinearMap.ker φ : Set (ℝ × ℝ)) := by
    rintro _ ⟨θ, hθ, r, hr, rfl⟩
    by_cases h0 : r = 0
    · right
      simp [hφ, polarPoint, h0]
    by_cases hb : θ = β
    · right
      simp only [SetLike.mem_coe, LinearMap.mem_ker, hφ, polarPoint, hb]
      simp
      ring
    · left
      exact ⟨(r, θ), ⟨⟨hθ.1, lt_of_le_of_ne hθ.2 hb⟩, lt_of_le_of_ne hr.1 (Ne.symm h0), hr.2⟩,
        (hG _)⟩
  have hvol : volume (polarCoord.symm '' T) = ENNReal.ofReal (∫ θ in α..β, g θ ^ 2 / 2) := by
    have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hTm
      (f := polarCoord.symm) (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) hinj
      (fun _ => 1)
    rw [setLIntegral_one] at h
    rw [h, ← region_lintegral g hg hg0 α β hab.le]
    refine setLIntegral_congr_fun hTm (fun p hp => ?_)
    simp [det_fderivPolarCoordSymm, abs_of_pos hp.2.1]
  apply le_antisymm
  · calc volume (polarRegion g α β) ≤ volume (polarCoord.symm '' T ∪ (LinearMap.ker φ : Set (ℝ × ℝ))) :=
          measure_mono hsub2
      _ ≤ volume (polarCoord.symm '' T) + volume (LinearMap.ker φ : Set (ℝ × ℝ)) := measure_union_le _ _
      _ = _ := by rw [hN, add_zero, hvol]
  · rw [← hvol]
    exact measure_mono hsub1

/-- OpenStax Calculus 2:Theorem 7.6, 3:Theorem 1.6 (CA-407): if `f` is continuous and nonnegative on `[α, β]`
with `0 < β - α ≤ 2π`, the region between the pole and the polar curve `r = f θ` (`α ≤ θ ≤ β`) has area
(Lebesgue measure in `ℝ × ℝ`) `(1/2) ∫_α^β f(θ)^2 dθ`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.6, p. 593"]
theorem polar_region_area (f : ℝ → ℝ) (α β : ℝ) (hf : ContinuousOn f (Icc α β))
    (hf0 : ∀ θ ∈ Icc α β, 0 ≤ f θ) (hab : α < β) (h2π : β - α ≤ 2 * π) :
    volume (polarRegion f α β) = ENNReal.ofReal (1 / 2 * ∫ θ in α..β, f θ ^ 2) := by
  set g : ℝ → ℝ := fun θ => f (projIcc α β hab.le θ) with hg
  have hgc : Continuous g :=
    hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun θ => (projIcc α β hab.le θ).2)
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ => hf0 _ (projIcc α β hab.le θ).2
  have hgf : ∀ θ ∈ Icc α β, g θ = f θ := fun θ hθ => by
    simp [hg, projIcc_of_mem hab.le hθ]
  have hreg : polarRegion f α β = polarRegion g α β := by
    ext q
    simp only [polarRegion, mem_ofPred_eq]
    constructor <;> rintro ⟨θ, hθ, r, hr, hq⟩ <;> exact ⟨θ, hθ, r, by simpa [hgf θ hθ] using hr, hq⟩
  rw [hreg, polar_region_volume_aux g hgc hg0 α β hab h2π]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine integral_congr fun θ hθ => ?_
  rw [uIcc_of_le hab.le] at hθ
  simp [hgf θ hθ]
  ring

/-! ## Arc length -/

/-- OpenStax Calculus 2:Theorem 7.7, 3:Theorem 1.7 (CA-408): for the polar curve `r = f θ`, i.e. the parametric
curve `x = f cos θ`, `y = f sin θ`, the parametric arc length integrand `√(x'^2 + y'^2)` equals
`√(f^2 + f'^2)`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.7, p. 596"]
theorem polar_arc_length_integrand (f f' : ℝ → ℝ) (θ : ℝ) (hf : HasDerivAt f (f' θ) θ) :
    √(deriv (fun s => f s * cos s) θ ^ 2 + deriv (fun s => f s * sin s) θ ^ 2) =
      √(f θ ^ 2 + f' θ ^ 2) := by
  have h1 : HasDerivAt (fun s => f s * cos s) (f' θ * cos θ + f θ * -sin θ) θ :=
    hf.mul (hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun s => f s * sin s) (f' θ * sin θ + f θ * cos θ) θ :=
    hf.mul (hasDerivAt_sin θ)
  rw [h1.deriv, h2.deriv]
  congr 1
  nlinarith [sin_sq_add_cos_sq θ]

/-- OpenStax Calculus 2:Theorem 7.7, 3:Theorem 1.7 (CA-408): the polar arc length
`∫_α^β √(x'(θ)^2 + y'(θ)^2) dθ` of the parametric curve `x = f cos θ`, `y = f sin θ` equals
`∫_α^β √(f(θ)^2 + f'(θ)^2) dθ` when `f` has derivative `f'` on `[α, β]`. -/
@[kb "openstaxcalculus2016" "2:Theorem 7.7, p. 596"]
theorem polar_arc_length (f f' : ℝ → ℝ) (α β : ℝ) (hf : ∀ θ ∈ uIcc α β, HasDerivAt f (f' θ) θ) :
    ∫ θ in α..β, √(deriv (fun s => f s * cos s) θ ^ 2 + deriv (fun s => f s * sin s) θ ^ 2) =
      ∫ θ in α..β, √(f θ ^ 2 + f' θ ^ 2) :=
  integral_congr fun θ hθ => polar_arc_length_integrand f f' θ (hf θ hθ)

end UndergradKB.Calculus
