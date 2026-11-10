import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Probability.Independence.Basic
import UndergradKB.Common.Attr

/-! # Calculus: multiple integrals

Volume of the ellipsoid, Fubini over Type I / Type II regions and over solids between two surfaces,
and polar coordinates. -/

namespace UndergradKB.Calculus

open MeasureTheory Metric Set

/-! ## Volume of an ellipsoid -/

/-- OpenStax Calculus 3:Example 5.53 (CA-588). The ellipsoid `x²/a² + y²/b² + z²/c² ≤ 1` in Euclidean
3-space has volume `(4/3) π a b c`. It is the image of the closed unit ball under the diagonal linear
map `diag(a, b, c)` of determinant `a b c`. -/
@[kb "openstaxcalculus2016" "3:Example 5.53, p. 525"]
theorem ellipsoid_volume (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    volume {p : EuclideanSpace ℝ (Fin 3) | (p 0 / a) ^ 2 + (p 1 / b) ^ 2 + (p 2 / c) ^ 2 ≤ 1} =
      ENNReal.ofReal (4 / 3 * Real.pi * a * b * c) := by
  let bs := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Matrix.toLin bs bs (Matrix.diagonal ![a, b, c])
  have hdet : LinearMap.det L = a * b * c := by
    simp only [L, LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  have hL : ∀ (q : EuclideanSpace ℝ (Fin 3)) (i : Fin 3), L q i = ![a, b, c] i * q i := by
    intro q i
    fin_cases i <;> simp [L, bs, Matrix.toLin_apply, Matrix.mulVec_diagonal, Fin.sum_univ_three]
  have himg : {p : EuclideanSpace ℝ (Fin 3) | (p 0 / a) ^ 2 + (p 1 / b) ^ 2 + (p 2 / c) ^ 2 ≤ 1}
      = L '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    ext p
    constructor
    · intro hp
      refine ⟨!₂[p 0 / a, p 1 / b, p 2 / c], ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
        rw [Real.sqrt_le_one]
        simpa [Fin.sum_univ_three] using hp
      · ext i
        rw [hL]
        fin_cases i <;> simp <;> field_simp
    · rintro ⟨q, hq, rfl⟩
      rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_one] at hq
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hq
      have h0 : L q 0 = a * q 0 := by simpa using hL q 0
      have h1 : L q 1 = b * q 1 := by simpa using hL q 1
      have h2 : L q 2 = c * q 2 := by simpa using hL q 2
      show (L q 0 / a) ^ 2 + (L q 1 / b) ^ 2 + (L q 2 / c) ^ 2 ≤ 1
      rw [h0, h1, h2, mul_div_cancel_left₀ _ ha.ne', mul_div_cancel_left₀ _ hb.ne',
        mul_div_cancel_left₀ _ hc.ne']
      exact hq
  rw [himg, Measure.addHaar_image_linearMap, hdet, EuclideanSpace.volume_closedBall_fin_three]
  rw [abs_of_pos (by positivity), ENNReal.ofReal_one, one_pow, one_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-! ## Fubini over regions between two graphs -/

section Fubini

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- The closed region `{(x, z) | x ∈ D, u1 x ≤ z ≤ u2 x}` between the graphs of `u1` and `u2` over
`D`. It is a Type I region when `α = ℝ` and `D = [a, b]`, and the solid between two surfaces over a
planar region `D` when `α = ℝ × ℝ`. -/
def regionBetweenClosed (u1 u2 : α → ℝ) (D : Set α) : Set (α × ℝ) :=
  {p | p.1 ∈ D ∧ p.2 ∈ Icc (u1 p.1) (u2 p.1)}

theorem measurableSet_regionBetweenClosed {u1 u2 : α → ℝ} {D : Set α} (hD : MeasurableSet D)
    (h1 : Measurable u1) (h2 : Measurable u2) : MeasurableSet (regionBetweenClosed u1 u2 D) := by
  have : regionBetweenClosed u1 u2 D = {p | p.1 ∈ D} ∩ {p | u1 p.1 ≤ p.2} ∩ {p | p.2 ≤ u2 p.1} := by
    ext p; simp [regionBetweenClosed, and_assoc]
  rw [this]
  exact ((measurable_fst hD).inter (measurableSet_le (h1.comp measurable_fst) measurable_snd)).inter
    (measurableSet_le measurable_snd (h2.comp measurable_fst))

omit [MeasurableSpace α] in
theorem slice_integral_indicator {u1 u2 : α → ℝ} {D : Set α} (hle : ∀ x ∈ D, u1 x ≤ u2 x)
    (f : α × ℝ → ℝ) (x : α) :
    ∫ z, (regionBetweenClosed u1 u2 D).indicator f (x, z) =
      D.indicator (fun x => ∫ z in u1 x..u2 x, f (x, z)) x := by
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx]
    have : (fun z => (regionBetweenClosed u1 u2 D).indicator f (x, z)) =
        (Icc (u1 x) (u2 x)).indicator (fun z => f (x, z)) := by
      ext z
      by_cases hz : z ∈ Icc (u1 x) (u2 x)
      · rw [indicator_of_mem hz, indicator_of_mem]; exact ⟨hx, hz⟩
      · rw [indicator_of_notMem hz, indicator_of_notMem]; exact fun h => hz h.2
    simp only [this]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (hle x hx)]
  · rw [indicator_of_notMem hx]
    have : ∀ z, (regionBetweenClosed u1 u2 D).indicator f (x, z) = 0 := fun z =>
      indicator_of_notMem (fun h : (x, z) ∈ regionBetweenClosed u1 u2 D => hx h.1) _
    simp [this]

/-- Fubini over the region between two graphs:the integral of an integrable `f` over
`{(x, z) | x ∈ D, u1 x ≤ z ≤ u2 x}` is the iterated integral with `z` from `u1 x` to `u2 x` inside. -/
theorem setIntegral_regionBetweenClosed {u1 u2 : α → ℝ} {D : Set α} (hD : MeasurableSet D)
    (h1 : Measurable u1) (h2 : Measurable u2) (hle : ∀ x ∈ D, u1 x ≤ u2 x)
    {f : α × ℝ → ℝ} (hf : IntegrableOn f (regionBetweenClosed u1 u2 D) (μ.prod volume)) :
    ∫ p in regionBetweenClosed u1 u2 D, f p ∂(μ.prod volume) =
      ∫ x in D, (∫ z in u1 x..u2 x, f (x, z)) ∂μ := by
  have hE := measurableSet_regionBetweenClosed hD h1 h2
  rw [← integral_indicator hE]
  have hint : Integrable ((regionBetweenClosed u1 u2 D).indicator f) (μ.prod volume) :=
    (integrable_indicator_iff hE).2 hf
  rw [integral_prod _ hint, ← integral_indicator hD]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact slice_integral_indicator hle f x

omit [SFinite μ] in
/-- The slice integral `x ↦ ∫ z in u1 x..u2 x, f (x, z)` of an integrable `f` over the region between
two graphs is integrable over `D`. -/
theorem integrableOn_slice_regionBetweenClosed {u1 u2 : α → ℝ} {D : Set α} (hD : MeasurableSet D)
    (h1 : Measurable u1) (h2 : Measurable u2) (hle : ∀ x ∈ D, u1 x ≤ u2 x)
    {f : α × ℝ → ℝ} (hf : IntegrableOn f (regionBetweenClosed u1 u2 D) (μ.prod volume)) :
    IntegrableOn (fun x => ∫ z in u1 x..u2 x, f (x, z)) D μ := by
  have hE := measurableSet_regionBetweenClosed hD h1 h2
  have hint : Integrable ((regionBetweenClosed u1 u2 D).indicator f) (μ.prod volume) :=
    (integrable_indicator_iff hE).2 hf
  have h := hint.integral_prod_left
  have h' : Integrable (D.indicator fun x => ∫ z in u1 x..u2 x, f (x, z)) μ := by
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact slice_integral_indicator hle f x
  exact (integrable_indicator_iff hD).1 h'

theorem isCompact_regionBetweenClosed {β : Type*} [TopologicalSpace β] [T2Space β]
    {u1 u2 : β → ℝ} {D : Set β}
    (hD : IsCompact D) (h1 : ContinuousOn u1 D) (h2 : ContinuousOn u2 D) :
    IsCompact (regionBetweenClosed u1 u2 D) := by
  obtain ⟨m, hm⟩ := (hD.image_of_continuousOn h1).bddBelow
  obtain ⟨M, hM⟩ := (hD.image_of_continuousOn h2).bddAbove
  have hsub : regionBetweenClosed u1 u2 D ⊆ D ×ˢ Icc m M := by
    rintro ⟨x, z⟩ ⟨hx, hz1, hz2⟩
    exact ⟨hx, (hm ⟨x, hx, rfl⟩).trans hz1, hz2.trans (hM ⟨x, hx, rfl⟩)⟩
  refine IsCompact.of_isClosed_subset (hD.prod isCompact_Icc) ?_ hsub
  have hc : ContinuousOn (fun p : β × ℝ => (p.2 - u1 p.1, u2 p.1 - p.2)) (D ×ˢ univ) := by
    refine ContinuousOn.prodMk ?_ ?_
    · exact continuousOn_snd.sub (h1.comp continuousOn_fst (fun p (hp : p ∈ D ×ˢ univ) => hp.1))
    · exact (h2.comp continuousOn_fst (fun p (hp : p ∈ D ×ˢ univ) => hp.1)).sub continuousOn_snd
  have := hc.preimage_isClosed_of_isClosed (hD.isClosed.prod isClosed_univ)
    ((isClosed_Ici (a := (0 : ℝ))).prod (isClosed_Ici (a := (0 : ℝ))))
  convert this using 1
  ext ⟨x, z⟩
  simp [regionBetweenClosed]

end Fubini

/-- A Type I region: `a ≤ x ≤ b`, `g1 x ≤ y ≤ g2 x`. -/
def typeIRegion (a b : ℝ) (g1 g2 : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (g1 p.1) (g2 p.1)}

/-- A Type II region: `c ≤ y ≤ d`, `h1 y ≤ x ≤ h2 y`. -/
def typeIIRegion (c d : ℝ) (h1 h2 : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc c d ∧ p.1 ∈ Icc (h1 p.2) (h2 p.2)}

/-- OpenStax Calculus 3:Definition (Type I and Type II regions) (CA-565). A Type I region (for continuous
`g1 ≤ g2`) is compact, hence measurable, of finite measure, and continuous functions on it are
integrable. -/
@[kb "openstaxcalculus2016" "3:Definition (Type I and Type II regions), p. 449"]
theorem isCompact_typeIRegion (a b : ℝ) {g1 g2 : ℝ → ℝ} (h1 : Continuous g1) (h2 : Continuous g2) :
    IsCompact (typeIRegion a b g1 g2) :=
  isCompact_regionBetweenClosed isCompact_Icc h1.continuousOn h2.continuousOn

/-- OpenStax Calculus 3:Definition (Type I and Type II regions) (CA-565). The Type II analogue. -/
@[kb "openstaxcalculus2016" "3:Definition (Type I and Type II regions), p. 449"]
theorem isCompact_typeIIRegion (c d : ℝ) {h1 h2 : ℝ → ℝ} (hc1 : Continuous h1) (hc2 : Continuous h2) :
    IsCompact (typeIIRegion c d h1 h2) := by
  have : typeIIRegion c d h1 h2 = Prod.swap ⁻¹' typeIRegion c d h1 h2 := by
    ext p; simp [typeIIRegion, typeIRegion]
  rw [this]
  exact (Homeomorph.prodComm ℝ ℝ).isCompact_preimage.2 (isCompact_typeIRegion c d hc1 hc2)

/-- Fubini over a Type I region for an integrable (not necessarily continuous) function. -/
theorem setIntegral_typeI_of_integrableOn {a b : ℝ} (hab : a ≤ b) {g1 g2 : ℝ → ℝ}
    (h1 : Continuous g1) (h2 : Continuous g2) (hle : ∀ x ∈ Icc a b, g1 x ≤ g2 x) {f : ℝ × ℝ → ℝ}
    (hint : IntegrableOn f (typeIRegion a b g1 g2)) :
    ∫ p in typeIRegion a b g1 g2, f p = ∫ x in a..b, ∫ y in g1 x..g2 x, f (x, y) := by
  have := setIntegral_regionBetweenClosed (μ := (volume : Measure ℝ)) measurableSet_Icc
    h1.measurable h2.measurable hle hint
  rw [← Measure.volume_eq_prod] at this
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact this

/-- OpenStax Calculus 3:Theorem 5.4 (CA-567). Fubini over a Type I region: for `f` continuous on
`{a ≤ x ≤ b, g1 x ≤ y ≤ g2 x}` (`g1 ≤ g2` continuous), the double integral is the iterated integral
with `y` from `g1 x` to `g2 x` inside and `x` from `a` to `b` outside. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.4, p. 451"]
theorem setIntegral_typeI {a b : ℝ} (hab : a ≤ b) {g1 g2 : ℝ → ℝ} (h1 : Continuous g1)
    (h2 : Continuous g2) (hle : ∀ x ∈ Icc a b, g1 x ≤ g2 x) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (typeIRegion a b g1 g2)) :
    ∫ p in typeIRegion a b g1 g2, f p = ∫ x in a..b, ∫ y in g1 x..g2 x, f (x, y) :=
  setIntegral_typeI_of_integrableOn hab h1 h2 hle
    (hf.integrableOn_compact (isCompact_typeIRegion a b h1 h2))

/-- OpenStax Calculus 3:Theorem 5.4 (CA-567). Fubini over a Type II region: for `f` continuous on
`{c ≤ y ≤ d, h1 y ≤ x ≤ h2 y}`, the double integral is the iterated integral with `x` from `h1 y` to
`h2 y` inside and `y` from `c` to `d` outside. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.4, p. 451"]
theorem setIntegral_typeII {c d : ℝ} (hcd : c ≤ d) {h1 h2 : ℝ → ℝ} (hc1 : Continuous h1)
    (hc2 : Continuous h2) (hle : ∀ y ∈ Icc c d, h1 y ≤ h2 y) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (typeIIRegion c d h1 h2)) :
    ∫ p in typeIIRegion c d h1 h2, f p = ∫ y in c..d, ∫ x in h1 y..h2 y, f (x, y) := by
  have hpre : typeIRegion c d h1 h2 = Prod.swap ⁻¹' typeIIRegion c d h1 h2 := by
    ext p; simp [typeIIRegion, typeIRegion]
  have hsw : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have h := hsw.setIntegral_preimage_emb (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding
    f (typeIIRegion c d h1 h2)
  rw [← h, ← hpre]
  exact setIntegral_typeI hcd hc1 hc2 hle (g1 := h1) (g2 := h2) (f := fun p => f p.swap)
    (hf.comp continuous_swap.continuousOn (fun p hp => by rw [hpre] at hp; exact hp))

/-- OpenStax Calculus 3:Theorem 5.10 (CA-580). A continuous function on the solid between two
continuous surfaces `z = u1 x`, `z = u2 x` over a compact planar region `D` has triple integral equal to
the double integral over `D` of the integral in `z` from `u1` to `u2`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.10, p. 496"]
theorem setIntegral_solid {D : Set (ℝ × ℝ)} (hD : IsCompact D) {u1 u2 : ℝ × ℝ → ℝ}
    (h1 : Continuous u1) (h2 : Continuous u2) (hle : ∀ x ∈ D, u1 x ≤ u2 x)
    {f : (ℝ × ℝ) × ℝ → ℝ} (hf : ContinuousOn f (regionBetweenClosed u1 u2 D)) :
    ∫ p in regionBetweenClosed u1 u2 D, f p =
      ∫ x in D, (∫ z in u1 x..u2 x, f (x, z)) := by
  have hint : IntegrableOn f (regionBetweenClosed u1 u2 D) (volume.prod volume) :=
    hf.integrableOn_compact (isCompact_regionBetweenClosed hD h1.continuousOn h2.continuousOn)
  exact setIntegral_regionBetweenClosed (μ := (volume : Measure (ℝ × ℝ))) hD.measurableSet
    h1.measurable h2.measurable hle hint

/-- OpenStax Calculus 3:Theorem 5.10 (CA-580). Triple iterated integral over the solid between two
surfaces above a Type I region `D`: `z` from `u1 (x, y)` to `u2 (x, y)` innermost, then `y` from
`g1 x` to `g2 x`, then `x` from `a` to `b`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.10, p. 496"]
theorem setIntegral_solid_typeI {a b : ℝ} (hab : a ≤ b) {g1 g2 : ℝ → ℝ} (hg1 : Continuous g1)
    (hg2 : Continuous g2) (hg : ∀ x ∈ Icc a b, g1 x ≤ g2 x) {u1 u2 : ℝ × ℝ → ℝ}
    (h1 : Continuous u1) (h2 : Continuous u2) (hle : ∀ x ∈ typeIRegion a b g1 g2, u1 x ≤ u2 x)
    {f : (ℝ × ℝ) × ℝ → ℝ}
    (hf : ContinuousOn f (regionBetweenClosed u1 u2 (typeIRegion a b g1 g2))) :
    ∫ p in regionBetweenClosed u1 u2 (typeIRegion a b g1 g2), f p =
      ∫ x in a..b, ∫ y in g1 x..g2 x, ∫ z in u1 (x, y)..u2 (x, y), f ((x, y), z) := by
  have hD := isCompact_typeIRegion a b hg1 hg2
  rw [setIntegral_solid hD h1 h2 hle hf]
  have hint : IntegrableOn f (regionBetweenClosed u1 u2 (typeIRegion a b g1 g2))
      (volume.prod volume) :=
    hf.integrableOn_compact (isCompact_regionBetweenClosed hD h1.continuousOn h2.continuousOn)
  exact setIntegral_typeI_of_integrableOn hab hg1 hg2 hg
    (integrableOn_slice_regionBetweenClosed (μ := (volume : Measure (ℝ × ℝ))) hD.measurableSet
      h1.measurable h2.measurable hle hint)

/-! ## Polar coordinates -/

/-- Change of variables for the polar map on a measurable set `R` of `(r, θ)` with `r > 0` and
`-π < θ < π`: `∫_{polar image of R} f = ∫_R r f(r cos θ, r sin θ) d(r, θ)`. -/
theorem setIntegral_polarCoord_symm_image {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hRt : R ⊆ polarCoord.target) (f : ℝ × ℝ → ℝ) :
    ∫ p in polarCoord.symm '' R, f p = ∫ q in R, q.1 • f (polarCoord.symm q) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hR
    (fun q _ => (hasFDerivAt_polarCoord_symm q).hasFDerivWithinAt)
    (polarCoord.symm.injOn.mono (by simpa using hRt))]
  refine setIntegral_congr_fun hR fun q hq => ?_
  rw [det_fderivPolarCoordSymm, abs_of_pos (hRt hq).1]

/-- The polar region `{(r cos θ, r sin θ) | α ≤ θ ≤ β, h1 θ ≤ r ≤ h2 θ}`. -/
noncomputable def polarRegionBetween (a b : ℝ) (h1 h2 : ℝ → ℝ) : Set (ℝ × ℝ) :=
  (fun q : ℝ × ℝ => (q.2 * Real.cos q.1, q.2 * Real.sin q.1)) ''
    regionBetweenClosed h1 h2 (Icc a b)

/-- OpenStax Calculus 3:Theorem 5.8 (CA-574), polar rectangle case (CA-573) when `h1`, `h2` are constant.
For `f` continuous on the polar region `{α ≤ θ ≤ β, h1 θ ≤ r ≤ h2 θ}` (with `-π < α ≤ β < π` and
`0 ≤ h1 ≤ h2` continuous), the double integral is `∫_α^β ∫_{h1 θ}^{h2 θ} f(r cos θ, r sin θ) r dr dθ`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.8, p. 477"]
theorem setIntegral_polarRegionBetween {a b : ℝ} (hab : a ≤ b) (ha : -Real.pi < a) (hb : b < Real.pi)
    {h1 h2 : ℝ → ℝ} (hc1 : Continuous h1) (hc2 : Continuous h2) (h0 : ∀ θ, 0 ≤ h1 θ)
    (hle : ∀ θ, h1 θ ≤ h2 θ) {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (polarRegionBetween a b h1 h2)) :
    ∫ p in polarRegionBetween a b h1 h2, f p =
      ∫ θ in a..b, ∫ r in h1 θ..h2 θ, r * f (r * Real.cos θ, r * Real.sin θ) := by
  set E := regionBetweenClosed h1 h2 (Icc a b) with hEdef
  set Q : ℝ × ℝ → ℝ × ℝ := fun q => (q.2 * Real.cos q.1, q.2 * Real.sin q.1) with hQ
  have hEm : MeasurableSet E :=
    measurableSet_regionBetweenClosed measurableSet_Icc hc1.measurable hc2.measurable
  have hEc : IsCompact E := isCompact_regionBetweenClosed isCompact_Icc hc1.continuousOn hc2.continuousOn
  have hQc : Continuous Q := by fun_prop
  -- the open part r > 0
  set E' := E ∩ {q | 0 < q.2} with hE'
  have hE'm : MeasurableSet E' := hEm.inter (measurableSet_lt measurable_const measurable_snd)
  set g : ℝ × ℝ → ℝ := fun y => y.2 * f (Q y) with hg
  -- Step A: drop the origin
  have hA : ∫ p in Q '' E, f p = ∫ p in Q '' E', f p := by
    refine setIntegral_congr_set ?_
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (t := ({0} : Set (ℝ × ℝ))) ?_ (measure_singleton _)
      rintro p ⟨⟨y, hyE, rfl⟩, hnot⟩
      by_contra hne
      apply hnot
      rcases (show 0 ≤ y.2 from (h0 y.1).trans hyE.2.1).eq_or_lt with h | h
      · exfalso; apply hne
        simp only [hQ, ← h, zero_mul]; rfl
      · exact ⟨y, ⟨hyE, h⟩, rfl⟩
    · rw [Set.sdiff_eq_empty.2 (image_mono inter_subset_left)]; simp
  -- Step B: polar change of variables
  have hRimg : polarCoord.symm '' (Prod.swap ⁻¹' E') = Q '' E' := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.swap, hq, by simp [hQ]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.swap, by simpa using hy, by simp [hQ]⟩
  have hRt : Prod.swap ⁻¹' E' ⊆ polarCoord.target := by
    rintro q ⟨⟨hθ, hr⟩, hpos⟩
    simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo]
    have e1 : a ≤ q.2 := hθ.1
    have e2 : q.2 ≤ b := hθ.2
    exact ⟨hpos, by linarith, by linarith⟩
  have hB : ∫ p in Q '' E', f p = ∫ q in Prod.swap ⁻¹' E', q.1 • f (polarCoord.symm q) := by
    rw [← hRimg]
    exact setIntegral_polarCoord_symm_image (measurable_swap hE'm) hRt f
  -- Step C: swap the variables
  have hsw : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap
  have hC : ∫ q in Prod.swap ⁻¹' E', q.1 • f (polarCoord.symm q) = ∫ y in E', g y := by
    have := hsw.setIntegral_preimage_emb
      (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding g E'
    rw [← this]
    refine setIntegral_congr_fun (measurable_swap hE'm) fun q _ => ?_
    simp [hg, hQ]
  -- Step D: put the origin ray back
  have hD : ∫ y in E', g y = ∫ y in E, g y := by
    rw [← integral_indicator hE'm, ← integral_indicator hEm]
    congr 1
    ext y
    by_cases hy : y ∈ E
    · by_cases hy2 : 0 < y.2
      · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ E' from ⟨hy, hy2⟩)]
      · have : y.2 = 0 := le_antisymm (not_lt.1 hy2) ((h0 y.1).trans hy.2.1)
        rw [indicator_of_mem hy]
        simp [hg, this]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h : y ∈ E' => hy h.1)]
  -- Step E: Fubini
  have hgc : ContinuousOn g E := by
    refine continuousOn_snd.mul (hf.comp hQc.continuousOn ?_)
    exact fun y hy => ⟨y, hy, rfl⟩
  have hE_int : IntegrableOn g E (volume.prod volume) := hgc.integrableOn_compact hEc
  have hE := setIntegral_regionBetweenClosed (μ := (volume : Measure ℝ)) measurableSet_Icc
    hc1.measurable hc2.measurable (fun θ _ => hle θ) hE_int
  rw [← Measure.volume_eq_prod] at hE
  have hS : polarRegionBetween a b h1 h2 = Q '' E := rfl
  rw [hS, hA, hB, hC, hD]
  have hE' : ∫ y in E, g y = ∫ θ in Icc a b, ∫ r in h1 θ..h2 θ, r * f (r * Real.cos θ, r * Real.sin θ) := hE
  rw [hE', intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

/-- OpenStax Calculus 3:Definition (double integral over a polar rectangle, eq. 5.8) (CA-573). Over the
polar rectangle `c ≤ r ≤ d`, `α ≤ θ ≤ β` the double integral is the iterated integral of
`f(r cos θ, r sin θ) r` (that is, `dA = r dr dθ`). -/
@[kb "openstaxcalculus2016" "3:Definition (double integral over a polar rectangle, eq. 5.8), p. 474"]
theorem setIntegral_polarRectangle {a b c d : ℝ} (hab : a ≤ b) (ha : -Real.pi < a)
    (hb : b < Real.pi) (hc : 0 ≤ c) (hcd : c ≤ d) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (polarRegionBetween a b (fun _ => c) (fun _ => d))) :
    ∫ p in polarRegionBetween a b (fun _ => c) (fun _ => d), f p =
      ∫ θ in a..b, ∫ r in c..d, r * f (r * Real.cos θ, r * Real.sin θ) :=
  setIntegral_polarRegionBetween hab ha hb continuous_const continuous_const (fun _ => hc)
    (fun _ => hcd) hf

/-- OpenStax Calculus 3:Definition (double integral over a polar rectangle, eq. 5.8) (CA-573). The
polar change of variables over the whole plane: `∫_{ℝ²} f = ∫_{r>0, -π<θ<π} r f(r cos θ, r sin θ)`. -/
@[kb "openstaxcalculus2016" "3:Definition (double integral over a polar rectangle, eq. 5.8), p. 474"]
theorem integral_plane_polar (f : ℝ × ℝ → ℝ) :
    ∫ p, f p = ∫ q in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      q.1 * f (q.1 * Real.cos q.2, q.1 * Real.sin q.2) :=
  (integral_comp_polarCoord_symm f).symm

/-- OpenStax Calculus 3:Example 5.67 (CA-601). The Jacobian determinant of the polar coordinate map
`(r, θ) ↦ (r cos θ, r sin θ)` is `r`: its derivative has determinant `r`. -/
@[kb "openstaxcalculus2016" "3:Example 5.67, p. 557"]
theorem det_polar_jacobian (r θ : ℝ) :
    (fderivPolarCoordSymm (r, θ)).det = r := det_fderivPolarCoordSymm (r, θ)

/-! ## Cylindrical coordinates -/

/-- The cylindrical coordinate map `(r, θ, z) ↦ (r cos θ, r sin θ, z)`, as a map `(ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ`
with the point `((r, θ), z)`. -/
noncomputable def cylindricalCoord : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  Prod.map polarCoord.symm id

theorem hasFDerivAt_cylindricalCoord (p : (ℝ × ℝ) × ℝ) :
    HasFDerivAt cylindricalCoord
      ((fderivPolarCoordSymm p.1).prodMap (ContinuousLinearMap.id ℝ ℝ)) p :=
  HasFDerivAt.prodMap p (hasFDerivAt_polarCoord_symm p.1) (hasFDerivAt_id p.2)

/-- OpenStax Calculus 3:Example 5.72 (a) (CA-601). The Jacobian determinant of the cylindrical
coordinate map `(r, θ, z) ↦ (r cos θ, r sin θ, z)` is `r`. -/
@[kb "openstaxcalculus2016" "3:Example 5.72 (a), p. 564"]
theorem det_cylindrical_jacobian (r θ : ℝ) :
    ((fderivPolarCoordSymm (r, θ)).prodMap (ContinuousLinearMap.id ℝ ℝ)).det = r := by
  have h : ((fderivPolarCoordSymm (r, θ)).prodMap (ContinuousLinearMap.id ℝ ℝ)).det =
      (fderivPolarCoordSymm (r, θ)).det * (ContinuousLinearMap.id ℝ ℝ).det := by
    simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap]
    exact LinearMap.det_prodMap _ _
  rw [h, det_fderivPolarCoordSymm]
  simp

/-- OpenStax Calculus 3:Definition (triple integral in cylindrical coordinates, eq. 5.11) (CA-583).
Change of variables in cylindrical coordinates over a measurable set `R` of `((r, θ), z)` with `r > 0`
and `-π < θ < π`: `∫_{cyl R} f = ∫_R r f(r cos θ, r sin θ, z)`, that is `dV = r dz dr dθ`. -/
@[kb "openstaxcalculus2016" "3:Definition (triple integral in cylindrical coordinates, eq. 5.11), p. 513"]
theorem setIntegral_cylindricalCoord_image {R : Set ((ℝ × ℝ) × ℝ)} (hR : MeasurableSet R)
    (hRt : R ⊆ polarCoord.target ×ˢ univ) (f : (ℝ × ℝ) × ℝ → ℝ) :
    ∫ p in cylindricalCoord '' R, f p = ∫ q in R, q.1.1 * f (cylindricalCoord q) := by
  have hinj : InjOn cylindricalCoord R := by
    rintro ⟨q, z⟩ hq ⟨q', z'⟩ hq' h
    have h' : polarCoord.symm q = polarCoord.symm q' ∧ z = z' := by
      simpa [cylindricalCoord, Prod.map] using h
    have := polarCoord.symm.injOn (by simpa using (hRt hq).1) (by simpa using (hRt hq').1) h'.1
    rw [this, h'.2]
  have : (volume : Measure ((ℝ × ℝ) × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hR
    (fun q _ => (hasFDerivAt_cylindricalCoord q).hasFDerivWithinAt) hinj]
  refine setIntegral_congr_fun hR fun q hq => ?_
  rw [det_cylindrical_jacobian q.1.1 q.1.2, abs_of_pos (hRt hq).1.1]
  rfl

/-! ## Spherical coordinates -/

section Spherical

open Real

/-- The spherical coordinate map `(ρ, φ, θ) ↦ (ρ sin φ cos θ, ρ sin φ sin θ, ρ cos φ)`, on points
`v = ![ρ, φ, θ]` of `Fin 3 → ℝ`. -/
noncomputable def sphericalCoord (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 0 * sin (v 1) * cos (v 2), v 0 * sin (v 1) * sin (v 2), v 0 * cos (v 1)]

/-- The Jacobian matrix of `sphericalCoord` at `![ρ, φ, θ]`: columns are the partial derivatives in
`ρ`, `φ`, `θ`. -/
noncomputable def sphericalJacobianMatrix (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sin (v 1) * cos (v 2), v 0 * cos (v 1) * cos (v 2), -(v 0 * sin (v 1) * sin (v 2));
     sin (v 1) * sin (v 2), v 0 * cos (v 1) * sin (v 2), v 0 * sin (v 1) * cos (v 2);
     cos (v 1), -(v 0 * sin (v 1)), 0]

/-- OpenStax Calculus 3:Definition (triple integral in spherical coordinates) (CA-585). The
determinant of the Jacobian matrix of the spherical coordinate map is `ρ² sin φ`. -/
@[kb "openstaxcalculus2016" "3:Definition (triple integral in spherical coordinates), p. 519"]
theorem det_sphericalJacobianMatrix (v : Fin 3 → ℝ) :
    (sphericalJacobianMatrix v).det = v 0 ^ 2 * sin (v 1) := by
  rw [Matrix.det_fin_three]
  simp only [sphericalJacobianMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  have h := sin_sq_add_cos_sq (v 2)
  have h2 := sin_sq_add_cos_sq (v 1)
  linear_combination (v 0 ^ 2 * sin (v 1) * (cos (v 1) ^ 2 + sin (v 1) ^ 2)) * h +
    (v 0 ^ 2 * sin (v 1)) * h2

/-- The Fréchet derivative of `sphericalCoord`. -/
noncomputable def sphericalFDeriv (v : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (Matrix.toLin' (sphericalJacobianMatrix v)).toContinuousLinearMap

theorem hasFDerivAt_sphericalCoord (v : Fin 3 → ℝ) :
    HasFDerivAt sphericalCoord (sphericalFDeriv v) v := by
  rw [hasFDerivAt_pi']
  intro i
  have h0 : HasFDerivAt (fun x : Fin 3 → ℝ => x 0) (ContinuousLinearMap.proj 0) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt
  have h1 : HasFDerivAt (fun x : Fin 3 → ℝ => x 1) (ContinuousLinearMap.proj 1) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).hasFDerivAt
  have h2 : HasFDerivAt (fun x : Fin 3 → ℝ => x 2) (ContinuousLinearMap.proj 2) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasFDerivAt
  have hs := (hasDerivAt_sin (v 1)).comp_hasFDerivAt v h1
  have hc := (hasDerivAt_cos (v 1)).comp_hasFDerivAt v h1
  have hs1 := (hasDerivAt_sin (v 2)).comp_hasFDerivAt v h2
  have hc1 := (hasDerivAt_cos (v 2)).comp_hasFDerivAt v h2
  fin_cases i
  · have e : (fun x : Fin 3 → ℝ => sphericalCoord x 0) =
        ((fun x : Fin 3 → ℝ => x 0) * (sin ∘ fun x => x 1)) * (cos ∘ fun x => x 2) := by
      ext x; simp [sphericalCoord]
    show HasFDerivAt (fun x : Fin 3 → ℝ => sphericalCoord x 0) _ v
    rw [e]
    refine ((h0.mul hs).mul hc1).congr_fderiv ?_
    ext w
    simp [sphericalFDeriv, sphericalJacobianMatrix, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_three]
    ring
  · have e : (fun x : Fin 3 → ℝ => sphericalCoord x 1) =
        ((fun x : Fin 3 → ℝ => x 0) * (sin ∘ fun x => x 1)) * (sin ∘ fun x => x 2) := by
      ext x; simp [sphericalCoord]
    show HasFDerivAt (fun x : Fin 3 → ℝ => sphericalCoord x 1) _ v
    rw [e]
    refine ((h0.mul hs).mul hs1).congr_fderiv ?_
    ext w
    simp [sphericalFDeriv, sphericalJacobianMatrix, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_three]
    ring
  · have e : (fun x : Fin 3 → ℝ => sphericalCoord x 2) =
        (fun x : Fin 3 → ℝ => x 0) * (cos ∘ fun x => x 1) := by
      ext x; simp [sphericalCoord]
    show HasFDerivAt (fun x : Fin 3 → ℝ => sphericalCoord x 2) _ v
    rw [e]
    refine (h0.mul hc).congr_fderiv ?_
    ext w
    simp [sphericalFDeriv, sphericalJacobianMatrix, Matrix.toLin'_apply,
      dotProduct, Fin.sum_univ_three]
    ring

/-- OpenStax Calculus 3:Example 5.72 (b) (CA-585, CA-601). The derivative of the spherical coordinate
map has determinant `ρ² sin φ`. -/
@[kb "openstaxcalculus2016" "3:Example 5.72 (b), p. 564"]
theorem det_sphericalFDeriv (v : Fin 3 → ℝ) :
    (sphericalFDeriv v).det = v 0 ^ 2 * sin (v 1) := by
  rw [← det_sphericalJacobianMatrix]
  simp only [sphericalFDeriv, ContinuousLinearMap.det]
  exact LinearMap.det_toLin' _

/-- The domain `ρ > 0`, `0 < φ < π`, `-π < θ < π` of spherical coordinates, on `![ρ, φ, θ]`. -/
def sphericalDomain : Set (Fin 3 → ℝ) :=
  {v | 0 < v 0 ∧ 0 < v 1 ∧ v 1 < π ∧ -π < v 2 ∧ v 2 < π}

theorem sphericalCoord_injOn : InjOn sphericalCoord sphericalDomain := by
  intro v hv w hw h
  obtain ⟨hv0, hv1, hv1', hv2, hv2'⟩ := hv
  obtain ⟨hw0, hw1, hw1', hw2, hw2'⟩ := hw
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  simp only [sphericalCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  have sv := sin_pos_of_pos_of_lt_pi hv1 hv1'
  have sw := sin_pos_of_pos_of_lt_pi hw1 hw1'
  have hp : polarCoord.symm (v 0 * sin (v 1), v 2) = polarCoord.symm (w 0 * sin (w 1), w 2) := by
    simp only [polarCoord_symm_apply]
    rw [Prod.mk.injEq]
    constructor
    · linarith [e0]
    · linarith [e1]
  have := polarCoord.symm.injOn
    (show (v 0 * sin (v 1), v 2) ∈ polarCoord.symm.source by
      simp only [OpenPartialHomeomorph.symm_source, polarCoord_target]
      exact ⟨mul_pos hv0 sv, hv2, hv2'⟩)
    (show (w 0 * sin (w 1), w 2) ∈ polarCoord.symm.source by
      simp only [OpenPartialHomeomorph.symm_source, polarCoord_target]
      exact ⟨mul_pos hw0 sw, hw2, hw2'⟩) hp
  simp only [Prod.mk.injEq] at this
  obtain ⟨hr, hθ⟩ := this
  have hρ : v 0 = w 0 := by
    have h1 : (v 0) ^ 2 = (w 0) ^ 2 := by
      have a1 : (v 0 * sin (v 1)) ^ 2 + (v 0 * cos (v 1)) ^ 2 = v 0 ^ 2 := by
        nlinarith [sin_sq_add_cos_sq (v 1)]
      have a2 : (w 0 * sin (w 1)) ^ 2 + (w 0 * cos (w 1)) ^ 2 = w 0 ^ 2 := by
        nlinarith [sin_sq_add_cos_sq (w 1)]
      rw [← a1, ← a2, hr, e2]
    nlinarith [sq_nonneg (v 0 - w 0), sq_nonneg (v 0 + w 0)]
  have hcos : cos (v 1) = cos (w 1) := by
    rw [hρ] at e2
    exact mul_left_cancel₀ hw0.ne' e2
  have hφ : v 1 = w 1 :=
    injOn_cos ⟨hv1.le, hv1'.le⟩ ⟨hw1.le, hw1'.le⟩ hcos
  ext i
  fin_cases i
  · exact hρ
  · exact hφ
  · exact hθ

/-- OpenStax Calculus 3:Definition (triple integral in spherical coordinates) (CA-585). Change of
variables in spherical coordinates over a measurable set `R` of `![ρ, φ, θ]` inside the domain
`ρ > 0`, `0 < φ < π`, `-π < θ < π`: `∫_{sph R} f = ∫_R ρ² sin φ · f(ρ sin φ cos θ, ρ sin φ sin θ, ρ cos φ)`,
that is `dV = ρ² sin φ dρ dφ dθ`. -/
@[kb "openstaxcalculus2016" "3:Definition (triple integral in spherical coordinates), p. 519"]
theorem setIntegral_sphericalCoord_image {R : Set (Fin 3 → ℝ)} (hR : MeasurableSet R)
    (hRd : R ⊆ sphericalDomain) (f : (Fin 3 → ℝ) → ℝ) :
    ∫ p in sphericalCoord '' R, f p =
      ∫ v in R, v 0 ^ 2 * sin (v 1) * f (sphericalCoord v) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hR
    (fun q _ => (hasFDerivAt_sphericalCoord q).hasFDerivWithinAt) (sphericalCoord_injOn.mono hRd)]
  refine setIntegral_congr_fun hR fun q hq => ?_
  obtain ⟨h0, h1, h1', -, -⟩ := hRd hq
  rw [det_sphericalFDeriv, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sin_pos_of_pos_of_lt_pi h1 h1').le)]
  rfl

end Spherical

/-! ## Improper double integrals over an unbounded rectangle -/

/-- OpenStax Calculus 3:Theorem 5.7 (CA-569). If `f` is integrable on the unbounded rectangle
`[a, ∞) × [c, ∞)`, its integral there is the limit of the integrals over the boxes `[a, b] × [c, d]`
as `b, d → ∞` (jointly, i.e. along `atTop` of `ℝ × ℝ`). -/
@[kb "openstaxcalculus2016" "3:Theorem 5.7, p. 462"]
theorem tendsto_setIntegral_Icc_prod_Ici {a c : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Ici a ×ˢ Ici c)) :
    Filter.Tendsto (fun p : ℝ × ℝ => ∫ x in Icc a p.1 ×ˢ Icc c p.2, f x) Filter.atTop
      (nhds (∫ x in Ici a ×ˢ Ici c, f x)) := by
  have hcov : AECover (volume.restrict (Ici a ×ˢ Ici c)) (Filter.atTop : Filter (ℝ × ℝ))
      (fun p : ℝ × ℝ => Icc a p.1 ×ˢ Icc c p.2) := by
    refine ⟨?_, fun p => measurableSet_Icc.prod measurableSet_Icc⟩
    rw [ae_restrict_iff' (measurableSet_Ici.prod measurableSet_Ici)]
    refine Filter.Eventually.of_forall fun x hx => ?_
    filter_upwards [Filter.eventually_ge_atTop x] with p hp
    exact ⟨⟨hx.1, hp.1⟩, ⟨hx.2, hp.2⟩⟩
  have := hcov.integral_tendsto_of_countably_generated hf
  refine this.congr fun p => ?_
  rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc),
    inter_eq_self_of_subset_left (prod_mono Icc_subset_Ici_self Icc_subset_Ici_self)]

/-- OpenStax Calculus 3:Theorem 5.7 (CA-569). The improper double integral as an iterated limit of
integrals over boxes: for `f` integrable on `[a, ∞) × [c, ∞)`,
`∫∫ f = lim_{b, d → ∞} ∫_a^b ∫_c^d f(x, y) dy dx`. -/
@[kb "openstaxcalculus2016" "3:Theorem 5.7, p. 462"]
theorem tendsto_intervalIntegral_prod_Ici {a c : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Ici a ×ˢ Ici c)) :
    Filter.Tendsto (fun p : ℝ × ℝ => ∫ x in a..p.1, ∫ y in c..p.2, f (x, y)) Filter.atTop
      (nhds (∫ x in Ici a ×ˢ Ici c, f x)) := by
  refine (tendsto_setIntegral_Icc_prod_Ici hf).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (a, c)] with p hp
  have hb : IntegrableOn f (Icc a p.1 ×ˢ Icc c p.2) :=
    hf.mono_set (prod_mono Icc_subset_Ici_self Icc_subset_Ici_self)
  have := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) f hb
  refine this.trans ?_
  rw [intervalIntegral.integral_of_le hp.1, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [intervalIntegral.integral_of_le hp.2, ← integral_Icc_eq_integral_Ioc]

/-! ## Joint densities -/

section JointDensity

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A joint density of the pair `(X, Y)` under the measure `P`: a measurable `f : ℝ × ℝ → [0, ∞]`
such that the law of `(X, Y)` has density `f` with respect to Lebesgue measure on the plane. (For a
probability measure this is Mathlib's `HasPDF` for the pair, with `pdf` equal to `f` a.e.) -/
def IsJointDensity (P : Measure Ω) (X Y : Ω → ℝ) (f : ℝ × ℝ → ENNReal) : Prop :=
  Measurable f ∧ P.map (fun ω => (X ω, Y ω)) = volume.withDensity f

/-- OpenStax Calculus 3:Definition (joint density function) (CA-570). If `f` is a joint density of
`(X, Y)`, then `P((X, Y) ∈ D)` is the double integral of `f` over `D`. -/
@[kb "openstaxcalculus2016" "3:Definition (joint density function), p. 463"]
theorem IsJointDensity.measure_preimage {P : Measure Ω} {X Y : Ω → ℝ} {f : ℝ × ℝ → ENNReal}
    (hX : Measurable X) (hY : Measurable Y) (hf : IsJointDensity P X Y f) {D : Set (ℝ × ℝ)}
    (hD : MeasurableSet D) : P {ω | (X ω, Y ω) ∈ D} = ∫⁻ p in D, f p := by
  have h := congrArg (fun m => m D) hf.2
  rw [Measure.map_apply (hX.prodMk hY) hD, withDensity_apply _ hD] at h
  exact h

/-- OpenStax Calculus 3:Definition (joint density function) (CA-570). The total integral of a joint
density is `P(Ω) = 1` for a probability measure. -/
@[kb "openstaxcalculus2016" "3:Definition (joint density function), p. 463"]
theorem IsJointDensity.lintegral_eq_one {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    {f : ℝ × ℝ → ENNReal} (hX : Measurable X) (hY : Measurable Y) (hf : IsJointDensity P X Y f) :
    ∫⁻ p, f p = 1 := by
  have := hf.measure_preimage hX hY MeasurableSet.univ
  simpa using this.symm

/-- OpenStax Calculus 3:Definition (independent random variables) (CA-571). If `f₁` and `f₂` are
densities of `X` and `Y`, then `X` and `Y` are independent iff `(x, y) ↦ f₁ x * f₂ y` is a joint density of
`(X, Y)`. -/
@[kb "openstaxcalculus2016" "3:Definition (independent random variables), p. 463"]
theorem indepFun_iff_jointDensity_mul {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {f₁ f₂ : ℝ → ENNReal} (hf₁ : Measurable f₁)
    (hf₂ : Measurable f₂) (h₁ : P.map X = volume.withDensity f₁)
    (h₂ : P.map Y = volume.withDensity f₂) :
    IndepFun X Y P ↔ IsJointDensity P X Y (fun p => f₁ p.1 * f₂ p.2) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, h₁, h₂,
    prod_withDensity hf₁ hf₂, ← Measure.volume_eq_prod]
  exact ⟨fun h => ⟨by fun_prop, h⟩, fun h => h.2⟩

/-- OpenStax Calculus 3:Definition (independent random variables) (CA-571). For independent `X`, `Y`
with densities `f₁`, `f₂`, `P(X ∈ A, Y ∈ B) = (∫_A f₁)(∫_B f₂)`, as an equality of integrals. -/
@[kb "openstaxcalculus2016" "3:Definition (independent random variables), p. 463"]
theorem measure_inter_preimage_eq_lintegral_mul {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {f₁ f₂ : ℝ → ENNReal}
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (h₁ : P.map X = volume.withDensity f₁)
    (h₂ : P.map Y = volume.withDensity f₂) (hind : IndepFun X Y P) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P {ω | X ω ∈ A ∧ Y ω ∈ B} = (∫⁻ x in A, f₁ x) * ∫⁻ y in B, f₂ y := by
  have hj := (indepFun_iff_jointDensity_mul hX hY hf₁ hf₂ h₁ h₂).1 hind
  have := hj.measure_preimage hX hY (hA.prod hB)
  have e : {ω | (X ω, Y ω) ∈ A ×ˢ B} = {ω | X ω ∈ A ∧ Y ω ∈ B} := rfl
  rw [e] at this
  rw [this, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul hf₁.aemeasurable hf₂.aemeasurable]

end JointDensity

end UndergradKB.Calculus
