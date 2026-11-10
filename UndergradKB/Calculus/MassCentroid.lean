import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr

/-! # Calculus: mass, work, force, centers of mass and centroids

OpenStax Calculus 1 §§6.5-6.6 and Calculus 2 §§2.5-2.6. Mass, work and force are bridging definitions (integrals,
as in the book); laminas are modelled by plane regions in `ℝ × ℝ` whose mass and moments are genuine integrals
against Lebesgue measure, and the book's one-variable formulas are proved from them by Fubini. -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-! ### Mass, work, hydrostatic force -/

/-- Bridging definition (OpenStax Calculus 1:Theorem 6.7): mass of a thin rod over `[a, b]` with linear density
`ρ` is `∫_a^b ρ`. -/
noncomputable def rodMass (ρ : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, ρ x

/-- OpenStax Calculus 1:Theorem 6.7 (CA-268). The mass of a rod is the measure with density `ρ`: the measure
`withDensity ρ` of `[a, b]` is the (nonnegative) mass `∫_a^b ρ`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.7, p. 603"]
theorem rodMass_eq_withDensity {a b : ℝ} (hab : a ≤ b) {ρ : ℝ → ℝ} (hρ : ContinuousOn ρ (Icc a b))
    (hρ0 : ∀ x ∈ Icc a b, 0 ≤ ρ x) :
    (volume.withDensity fun x => ENNReal.ofReal (ρ x)) (Icc a b) = ENNReal.ofReal (rodMass ρ a b) := by
  rw [withDensity_apply _ measurableSet_Icc, rodMass,
    ← ofReal_integral_eq_lintegral_ofReal hρ.integrableOn_Icc
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hρ0)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- Bridging definition (OpenStax Calculus 1:Definition 6.12): work done by a force `F` moving an object from `a` to
`b` along the axis is `∫_a^b F`. -/
noncomputable def work (F : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, F x

/-- OpenStax Calculus 1:§6.5 Definition (work) (CA-270). A constant force `F` moving an object from `a` to `b`
does work `F (b - a)`. -/
@[kb "openstaxcalculus2016" "1:§6.5 Definition (work) (6.12), p. 606"]
theorem work_const (F a b : ℝ) : work (fun _ => F) a b = F * (b - a) := by
  simp [work, mul_comm]

/-- Bridging definition (OpenStax Calculus 1:Equation 6.13): force on a vertical plate in a liquid of
weight-density `γ`, with depth function `d` and width function `w` over `[a, b]`. -/
noncomputable def hydrostaticForce (γ : ℝ) (d w : ℝ → ℝ) (a b : ℝ) : ℝ := γ * ∫ x in a..b, d x * w x

/-- OpenStax Calculus 1:Equation 6.13 (CA-273), sanity check. A rectangular plate of width `w₀` over `[a, b]` at
constant depth `s` feels force `γ s w₀ (b - a)`, i.e. pressure times area (CA-272). -/
@[kb "openstaxcalculus2016" "1:Equation 6.13 (hydrostatic force), p. 613"]
theorem hydrostaticForce_const (γ s w₀ a b : ℝ) :
    hydrostaticForce γ (fun _ => s) (fun _ => w₀) a b = γ * s * (w₀ * (b - a)) := by
  simp [hydrostaticForce, mul_assoc, mul_comm]

/-! ### Point masses -/

/-- Moment of point masses `m i` at positions `x i` on a line (OpenStax Calculus 1:Theorem 6.9). -/
def moment {ι : Type*} (s : Finset ι) (m x : ι → ℝ) : ℝ := ∑ i ∈ s, m i * x i

/-- Center of mass of point masses on a line: moment over total mass (OpenStax Calculus 1:Theorem 6.9). -/
noncomputable def centerOfMass {ι : Type*} (s : Finset ι) (m x : ι → ℝ) : ℝ :=
  moment s m x / ∑ i ∈ s, m i

/-- OpenStax Calculus 1:Theorem 6.9 (CA-274). The book's center of mass is Mathlib's `Finset.centerMass`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.9, p. 620"]
theorem centerOfMass_eq_centerMass {ι : Type*} (s : Finset ι) (m x : ι → ℝ) :
    centerOfMass s m x = s.centerMass m x := by
  simp [centerOfMass, moment, Finset.centerMass, div_eq_inv_mul]

/-- OpenStax Calculus 1:Theorem 6.9 (CA-274): translating all positions by `c` translates the center of mass by
`c` (total mass nonzero). -/
@[kb "openstaxcalculus2016" "1:Theorem 6.9, p. 620"]
theorem centerOfMass_add_const {ι : Type*} (s : Finset ι) (m x : ι → ℝ) (c : ℝ) (hm : ∑ i ∈ s, m i ≠ 0) :
    centerOfMass s m (fun i => x i + c) = centerOfMass s m x + c := by
  simp only [centerOfMass, moment, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  field_simp

/-- Moment about the `x`-axis of planar point masses: `M_x = ∑ m y` (OpenStax Calculus 1:Theorem 6.10). -/
def momentX {ι : Type*} (s : Finset ι) (m : ι → ℝ) (p : ι → ℝ × ℝ) : ℝ := ∑ i ∈ s, m i * (p i).2

/-- Moment about the `y`-axis of planar point masses: `M_y = ∑ m x` (OpenStax Calculus 1:Theorem 6.10). -/
def momentY {ι : Type*} (s : Finset ι) (m : ι → ℝ) (p : ι → ℝ × ℝ) : ℝ := ∑ i ∈ s, m i * (p i).1

/-- Center of mass of planar point masses `(M_y / m, M_x / m)` (OpenStax Calculus 1:Theorem 6.10). -/
noncomputable def centerOfMass2 {ι : Type*} (s : Finset ι) (m : ι → ℝ) (p : ι → ℝ × ℝ) : ℝ × ℝ :=
  (momentY s m p / ∑ i ∈ s, m i, momentX s m p / ∑ i ∈ s, m i)

/-- OpenStax Calculus 1:Theorem 6.10 (CA-275). The planar center of mass is `Finset.centerMass` in `ℝ × ℝ`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.10, p. 621"]
theorem centerOfMass2_eq_centerMass {ι : Type*} (s : Finset ι) (m : ι → ℝ) (p : ι → ℝ × ℝ) :
    centerOfMass2 s m p = s.centerMass m p := by
  ext <;> simp [centerOfMass2, momentX, momentY, Finset.centerMass, div_eq_inv_mul, Prod.fst_sum,
    Prod.snd_sum]

/-! ### Laminas -/

/-- The plane region between the graphs `g ≤ f` over `[a, b]` (a lamina). -/
def lamina (f g : ℝ → ℝ) (a b : ℝ) : Set (ℝ × ℝ) := {q | q.1 ∈ Icc a b ∧ g q.1 ≤ q.2 ∧ q.2 ≤ f q.1}

/-- Mass of a lamina of constant density `ρ` occupying `R`: density times area. Bridging definition
(OpenStax Calculus 1:Theorem 6.12). -/
noncomputable def laminaMass (ρ : ℝ) (R : Set (ℝ × ℝ)) : ℝ := ρ * volume.real R

/-- Moment `M_x = ρ ∬_R y` about the `x`-axis. -/
noncomputable def laminaMx (ρ : ℝ) (R : Set (ℝ × ℝ)) : ℝ := ρ * ∫ q in R, q.2

/-- Moment `M_y = ρ ∬_R x` about the `y`-axis. -/
noncomputable def laminaMy (ρ : ℝ) (R : Set (ℝ × ℝ)) : ℝ := ρ * ∫ q in R, q.1

/-- Center of mass (centroid when `ρ` is constant) `(M_y / m, M_x / m)` of a lamina. -/
noncomputable def laminaCenter (ρ : ℝ) (R : Set (ℝ × ℝ)) : ℝ × ℝ :=
  (laminaMy ρ R / laminaMass ρ R, laminaMx ρ R / laminaMass ρ R)

section lamina

variable {f g : ℝ → ℝ} {a b : ℝ}

lemma measurableSet_lamina (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    MeasurableSet (lamina f g a b) := by
  have h1 : MeasurableSet {q : ℝ × ℝ | q.1 ∈ Icc a b} := measurableSet_Icc.preimage measurable_fst
  have h2 : MeasurableSet {q : ℝ × ℝ | g q.1 ≤ q.2} :=
    measurableSet_le (hg.measurable.comp measurable_fst) measurable_snd
  have h3 : MeasurableSet {q : ℝ × ℝ | q.2 ≤ f q.1} :=
    measurableSet_le measurable_snd (hf.measurable.comp measurable_fst)
  exact h1.inter (h2.inter h3)

lemma isCompact_lamina (hf : Continuous f) (hg : Continuous g) (a b : ℝ) : IsCompact (lamina f g a b) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn (hf.continuousOn)
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn (hg.continuousOn)
  have hcl : IsClosed (lamina f g a b) := by
    have h1 : IsClosed {q : ℝ × ℝ | q.1 ∈ Icc a b} := isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {q : ℝ × ℝ | g q.1 ≤ q.2} :=
      isClosed_le (hg.comp continuous_fst) continuous_snd
    have h3 : IsClosed {q : ℝ × ℝ | q.2 ≤ f q.1} :=
      isClosed_le continuous_snd (hf.comp continuous_fst)
    exact h1.inter (h2.inter h3)
  refine IsCompact.of_isClosed_subset ((isCompact_Icc (a := a) (b := b)).prod
    (isCompact_Icc (a := -D) (b := C))) hcl ?_
  rintro q ⟨hq1, hq2, hq3⟩
  refine ⟨hq1, ?_, ?_⟩
  · have := hD q.1 hq1
    rw [Real.norm_eq_abs, abs_le] at this
    linarith [this.1]
  · have := hC q.1 hq1
    rw [Real.norm_eq_abs, abs_le] at this
    linarith [this.2]

/-- Fubini for a lamina: the integral of a continuous function over the region between `g ≤ f` is the iterated
integral. -/
lemma setIntegral_lamina (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b)
    (hgf : ∀ x ∈ Icc a b, g x ≤ f x) {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) :
    ∫ q in lamina f g a b, φ q = ∫ x in a..b, ∫ y in (g x)..(f x), φ (x, y) := by
  have hm := measurableSet_lamina hf hg a b
  have hint : Integrable ((lamina f g a b).indicator φ) :=
    (integrable_indicator_iff hm).2 (hφ.continuousOn.integrableOn_compact (isCompact_lamina hf hg a b))
  rw [← integral_indicator hm, Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hint)]
  have h1 : ∀ x, ∫ y, (lamina f g a b).indicator φ (x, y) =
      (Icc a b).indicator (fun x => ∫ y in (g x)..(f x), φ (x, y)) x := by
    intro x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
      have : ∀ y, (lamina f g a b).indicator φ (x, y) = (Icc (g x) (f x)).indicator (fun y => φ (x, y)) y := by
        intro y
        by_cases hy : y ∈ Icc (g x) (f x)
        · rw [indicator_of_mem hy, indicator_of_mem]
          exact ⟨hx, hy.1, hy.2⟩
        · rw [indicator_of_notMem hy, indicator_of_notMem]
          exact fun h => hy ⟨h.2.1, h.2.2⟩
      simp_rw [this]
      rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (hgf x hx)]
    · rw [indicator_of_notMem hx]
      have : ∀ y, (lamina f g a b).indicator φ (x, y) = 0 := by
        intro y
        rw [indicator_of_notMem]
        exact fun h => hx h.1
      simp_rw [this]
      simp
  simp_rw [h1]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- Area of the lamina between `g ≤ f` is `∫ (f - g)`. -/
lemma volume_real_lamina (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b)
    (hgf : ∀ x ∈ Icc a b, g x ≤ f x) :
    volume.real (lamina f g a b) = ∫ x in a..b, (f x - g x) := by
  have := setIntegral_lamina hf hg hab hgf (φ := fun _ => 1) continuous_const
  rw [setIntegral_const] at this
  simpa using this

/-- OpenStax Calculus 1:Theorem 6.13 (CA-279). For a lamina of constant density `ρ` between the graphs `g ≤ f` over
`[a, b]`: mass `ρ ∫ (f - g)`, moment about the `x`-axis `ρ ∫ (f² - g²)/2`, moment about the `y`-axis
`ρ ∫ x (f - g)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.13, p. 626"]
theorem lamina_mass_moments (hf : Continuous f) (hg : Continuous g) (hab : a ≤ b)
    (hgf : ∀ x ∈ Icc a b, g x ≤ f x) (ρ : ℝ) :
    laminaMass ρ (lamina f g a b) = ρ * ∫ x in a..b, (f x - g x) ∧
    laminaMx ρ (lamina f g a b) = ρ * ∫ x in a..b, (f x ^ 2 - g x ^ 2) / 2 ∧
    laminaMy ρ (lamina f g a b) = ρ * ∫ x in a..b, x * (f x - g x) := by
  refine ⟨by rw [laminaMass, volume_real_lamina hf hg hab hgf], ?_, ?_⟩
  · rw [laminaMx, setIntegral_lamina hf hg hab hgf (φ := fun q => q.2) continuous_snd]
    congr 2
    ext x
    rw [integral_id]
  · rw [laminaMy, setIntegral_lamina hf hg hab hgf (φ := fun q => q.1) continuous_fst]
    congr 2
    ext x
    simp [mul_comm]

/-- OpenStax Calculus 1:Theorem 6.12 (CA-278). A lamina of constant density `ρ` under `y = f(x) ≥ 0` over `[a, b]`
(the case `g = 0` of CA-279): mass `ρ ∫ f`, `M_x = ρ ∫ f²/2`, `M_y = ρ ∫ x f`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.12, p. 624"]
theorem lamina_under_graph (hf : Continuous f) (hab : a ≤ b) (hf0 : ∀ x ∈ Icc a b, 0 ≤ f x) (ρ : ℝ) :
    laminaMass ρ (lamina f (fun _ => 0) a b) = ρ * ∫ x in a..b, f x ∧
    laminaMx ρ (lamina f (fun _ => 0) a b) = ρ * ∫ x in a..b, f x ^ 2 / 2 ∧
    laminaMy ρ (lamina f (fun _ => 0) a b) = ρ * ∫ x in a..b, x * f x := by
  obtain ⟨h1, h2, h3⟩ := lamina_mass_moments hf (continuous_const (y := (0 : ℝ))) hab hf0 ρ
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- OpenStax Calculus 1:Theorem 6.11 (CA-277). If the lamina between `g ≤ f` over `[c - h, c + h]` is symmetric about
the vertical line `x = c` (`f(c - t) = f(c + t)`, same for `g`), its first moment is `c` times its mass, so its
center of mass (centroid) has `x`-coordinate `c`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.11, p. 622"]
theorem lamina_symmetric_centroid_x (hf : Continuous f) (hg : Continuous g) {c h : ℝ} (hh : 0 ≤ h)
    (hgf : ∀ x ∈ Icc (c - h) (c + h), g x ≤ f x) (hfs : ∀ t, f (c - t) = f (c + t))
    (hgs : ∀ t, g (c - t) = g (c + t)) (ρ : ℝ) :
    laminaMy ρ (lamina f g (c - h) (c + h)) = c * laminaMass ρ (lamina f g (c - h) (c + h)) := by
  have hab : c - h ≤ c + h := by linarith
  obtain ⟨h1, -, h3⟩ := lamina_mass_moments hf hg hab hgf ρ
  rw [h1, h3]
  have key : ∫ x in (c - h)..(c + h), (x - c) * (f x - g x) = 0 := by
    have hrefl := intervalIntegral.integral_comp_sub_left (a := c - h) (b := c + h)
      (fun x => (x - c) * (f x - g x)) (c + c)
    have hrw : ∀ x : ℝ, ((c + c - x) - c) * (f (c + c - x) - g (c + c - x)) = -((x - c) * (f x - g x)) := by
      intro x
      have e1 : f (c + c - x) = f x := by
        have := hfs (x - c)
        rwa [show c - (x - c) = c + c - x by ring, show c + (x - c) = x by ring] at this
      have e2 : g (c + c - x) = g x := by
        have := hgs (x - c)
        rwa [show c - (x - c) = c + c - x by ring, show c + (x - c) = x by ring] at this
      rw [e1, e2]
      ring
    simp only [hrw, intervalIntegral.integral_neg] at hrefl
    rw [show c + c - (c + h) = c - h by ring, show c + c - (c - h) = c + h by ring] at hrefl
    linarith
  have key2 : ∫ x in (c - h)..(c + h), x * (f x - g x) =
      c * ∫ x in (c - h)..(c + h), (f x - g x) := by
    rw [← intervalIntegral.integral_const_mul]
    have : ∀ x, x * (f x - g x) = (x - c) * (f x - g x) + c * (f x - g x) := fun x => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add, key, zero_add]
    · exact ((continuous_id.sub continuous_const).mul (hf.sub hg)).intervalIntegrable _ _
    · exact (continuous_const.mul (hf.sub hg)).intervalIntegrable _ _
  rw [key2]
  ring

end lamina

end UndergradKB.Calculus
