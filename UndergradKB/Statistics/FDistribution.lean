import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import UndergradKB.Statistics.StudentT

/-!
# The F distribution

OpenStax *Introductory Statistics 2e*, §13.3-13.4: the `F` statistic is a ratio of two independent chi-square
variables, each divided by its degrees of freedom; it is nonnegative and its density is skewed to the right.
Mathlib has no `F` law. We define it by its density

  `f(x) = Γ((d₁+d₂)/2) / (Γ(d₁/2) Γ(d₂/2)) · (d₁/d₂)^(d₁/2) · x^(d₁/2 - 1) · (1 + d₁ x / d₂)^(-(d₁+d₂)/2)`  for `x > 0`

and prove `hasLaw_fDistribution`: if `U ~ χ²(d₁)`, `V ~ χ²(d₂)` are independent then `(U/d₁)/(V/d₂)` has this law.
The proof follows `UndergradKB.Statistics.StudentT`: integrate over `u` for fixed `v` with the substitution
`u = (d₁ v / d₂) x`, swap the integrals (Tonelli) and evaluate the remaining gamma integral in `v`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

/-- The density of the F distribution with `d₁` numerator and `d₂` denominator degrees of freedom. -/
noncomputable def fPDFReal (d₁ d₂ x : ℝ) : ℝ :=
  if 0 < x then
    Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) * (d₁ / d₂) ^ (d₁ / 2) *
      x ^ (d₁ / 2 - 1) * (1 + d₁ * x / d₂) ^ (-((d₁ + d₂) / 2))
  else 0

/-- The F distribution with `d₁`, `d₂` degrees of freedom, as a measure on `ℝ` with density `fPDFReal d₁ d₂`. -/
noncomputable def fDistribution (d₁ d₂ : ℝ) : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (fPDFReal d₁ d₂ x)

@[fun_prop]
lemma measurable_fPDFReal (d₁ d₂ : ℝ) : Measurable (fPDFReal d₁ d₂) := by
  unfold fPDFReal
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-- **The F distribution lives on the positive reals** (§13.3, "F is nonnegative"). -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem fDistribution_Iic_zero (d₁ d₂ : ℝ) : fDistribution d₁ d₂ (Iic 0) = 0 := by
  rw [fDistribution, withDensity_apply _ measurableSet_Iic,
    setLIntegral_congr_fun measurableSet_Iic (g := fun _ ↦ 0)
      fun x (hx : x ≤ 0) ↦ by simp [fPDFReal, not_lt.2 hx]]
  simp

/-! ### The substitution on `(0, ∞)` -/

/-- Linear substitution on `(0, ∞)`: `∫_{u>0} G(u) du = c ∫_{x>0} G(c x) dx` for `c > 0`. -/
lemma setLIntegral_Ioi_eq_mul_comp_mul {c : ℝ} (hc : 0 < c) {G : ℝ → ENNReal} (hG : Measurable G) :
    ∫⁻ u in Ioi 0, G u = ENNReal.ofReal c * ∫⁻ x in Ioi 0, G (c * x) := by
  have h := lintegral_eq_mul_lintegral_comp_mul hc
    (G := (Ioi (0 : ℝ)).indicator G) (hG.indicator measurableSet_Ioi)
  rw [lintegral_indicator measurableSet_Ioi] at h
  rw [h, ← lintegral_indicator measurableSet_Ioi]
  congr 2
  funext t
  have : 0 < c * t ↔ 0 < t := mul_pos_iff_of_pos_left hc
  by_cases ht : 0 < t
  · simp [indicator, ht, this.2 ht]
  · simp [indicator, ht, this]

/-! ### The kernel identity -/

/-- The joint integrand after the substitution, as a function of `v` (the second chi-square value) and `x`. -/
noncomputable def fKernel (d₁ d₂ v x : ℝ) : ℝ :=
  (1 / 2) ^ (d₂ / 2) / Gamma (d₂ / 2) * v ^ (d₂ / 2 - 1) * exp (-(1 / 2 * v)) *
    (d₁ * v / d₂ * ((1 / 2) ^ (d₁ / 2) / Gamma (d₁ / 2) * (d₁ * v / d₂ * x) ^ (d₁ / 2 - 1) *
      exp (-(1 / 2 * (d₁ * v / d₂ * x)))))

lemma fKernel_eq {d₁ d₂ v x : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hv : 0 < v) (hx : 0 < x) :
    fKernel d₁ d₂ v x = (1 / 2) ^ (d₂ / 2) / Gamma (d₂ / 2) * ((1 / 2) ^ (d₁ / 2) / Gamma (d₁ / 2)) *
      (d₁ / d₂) ^ (d₁ / 2) * x ^ (d₁ / 2 - 1) *
      (v ^ ((d₁ + d₂) / 2 - 1) * exp (-((1 + d₁ * x / d₂) / 2 * v))) := by
  have hc : 0 < d₁ * v / d₂ := by positivity
  have hca : (d₁ * v / d₂) ^ (d₁ / 2) = (d₁ / d₂) ^ (d₁ / 2) * v ^ (d₁ / 2) := by
    rw [show d₁ * v / d₂ = d₁ / d₂ * v by ring, mul_rpow (by positivity) hv.le]
  have h1 : (d₁ * v / d₂) * (d₁ * v / d₂ * x) ^ (d₁ / 2 - 1) =
      (d₁ * v / d₂) ^ (d₁ / 2) * x ^ (d₁ / 2 - 1) := by
    rw [mul_rpow hc.le hx.le, rpow_sub_one hc.ne']
    field_simp
  have hvp : v ^ (d₂ / 2 - 1) * v ^ (d₁ / 2) = v ^ ((d₁ + d₂) / 2 - 1) := by
    rw [← rpow_add hv]
    congr 1
    ring
  have he : exp (-(1 / 2 * v)) * exp (-(1 / 2 * (d₁ * v / d₂ * x))) =
      exp (-((1 + d₁ * x / d₂) / 2 * v)) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  unfold fKernel
  rw [← hvp, ← he]
  linear_combination ((1 / 2) ^ (d₂ / 2) / Gamma (d₂ / 2) * ((1 / 2) ^ (d₁ / 2) / Gamma (d₁ / 2)) *
      v ^ (d₂ / 2 - 1) * exp (-(1 / 2 * v)) * exp (-(1 / 2 * (d₁ * v / d₂ * x)))) * h1 +
    ((1 / 2) ^ (d₂ / 2) / Gamma (d₂ / 2) * ((1 / 2) ^ (d₁ / 2) / Gamma (d₁ / 2)) *
      v ^ (d₂ / 2 - 1) * exp (-(1 / 2 * v)) * exp (-(1 / 2 * (d₁ * v / d₂ * x))) *
      x ^ (d₁ / 2 - 1)) * hca

/-- The constants combine to the F density. -/
lemma f_constant {d₁ d₂ x : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hx : 0 < x) :
    (1 / 2) ^ (d₂ / 2) / Gamma (d₂ / 2) * ((1 / 2) ^ (d₁ / 2) / Gamma (d₁ / 2)) * (d₁ / d₂) ^ (d₁ / 2) *
      x ^ (d₁ / 2 - 1) *
      ((1 / ((1 + d₁ * x / d₂) / 2)) ^ ((d₁ + d₂) / 2) * Gamma ((d₁ + d₂) / 2)) =
      fPDFReal d₁ d₂ x := by
  have hu : 0 < 1 + d₁ * x / d₂ := by positivity
  have h2 : (1 / 2 : ℝ) ^ (d₂ / 2) * (1 / 2) ^ (d₁ / 2) *
      (1 / ((1 + d₁ * x / d₂) / 2)) ^ ((d₁ + d₂) / 2) = (1 + d₁ * x / d₂) ^ (-((d₁ + d₂) / 2)) := by
    rw [← rpow_add (by norm_num), show d₂ / 2 + d₁ / 2 = (d₁ + d₂) / 2 by ring,
      ← mul_rpow (by norm_num) (by positivity), show 1 / 2 * (1 / ((1 + d₁ * x / d₂) / 2)) =
        (1 + d₁ * x / d₂)⁻¹ by field_simp, inv_rpow hu.le, ← rpow_neg hu.le]
  unfold fPDFReal
  rw [if_pos hx]
  calc _ = ((1 / 2 : ℝ) ^ (d₂ / 2) * (1 / 2) ^ (d₁ / 2) *
        (1 / ((1 + d₁ * x / d₂) / 2)) ^ ((d₁ + d₂) / 2)) *
        (Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) * (d₁ / d₂) ^ (d₁ / 2) *
          x ^ (d₁ / 2 - 1)) := by ring
    _ = _ := by rw [h2]; ring

/-- The integral of the kernel over `v > 0` is the F density. -/
lemma lintegral_fKernel {d₁ d₂ x : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hx : 0 < x) :
    ∫⁻ v in Ioi 0, ENNReal.ofReal (fKernel d₁ d₂ v x) = ENNReal.ofReal (fPDFReal d₁ d₂ x) := by
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have hG2 := Gamma_pos_of_pos (by positivity : 0 < d₂ / 2)
  rw [setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) ↦ by
      rw [fKernel_eq hd₁ hd₂ hv hx, ENNReal.ofReal_mul (by positivity)],
    lintegral_const_mul _ (by fun_prop),
    lintegral_rpow_mul_exp_neg_mul_Ioi (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), f_constant hd₁ hd₂ hx]

/-! ### The law of `(U/d₁)/(V/d₂)` -/

/-- Integration formula behind the F law: for independent `U ~ χ²(d₁)` and `V ~ χ²(d₂)` (product law),
`E[F((U/d₁)/(V/d₂))] = ∫ F(x) f(x) dx`. -/
theorem lintegral_f_ratio {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) {F : ℝ → ENNReal}
    (hF : Measurable F) :
    ∫⁻ p, F ((p.1 / d₁) / (p.2 / d₂)) ∂((chiSquared d₁).prod (chiSquared d₂)) =
      ∫⁻ x, ENNReal.ofReal (fPDFReal d₁ d₂ x) * F x := by
  have := isProbabilityMeasure_chiSquared' hd₁
  have := isProbabilityMeasure_chiSquared' hd₂
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have hG2 := Gamma_pos_of_pos (by positivity : 0 < d₂ / 2)
  have hm : Measurable fun p : ℝ × ℝ ↦ F ((p.1 / d₁) / (p.2 / d₂)) := by fun_prop
  have : SFinite (gammaMeasure (d₁ / 2) (1 / 2)) := inferInstanceAs (SFinite (chiSquared d₁))
  rw [lintegral_prod_symm' _ hm]
  unfold chiSquared
  rw [lintegral_gammaMeasure _ _ (Measurable.lintegral_prod_left' hm)]
  calc _ = ∫⁻ v in Ioi 0, ∫⁻ x in Ioi 0, ENNReal.ofReal (fKernel d₁ d₂ v x) * F x := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) ↦ ?_
        have hc : 0 < d₁ * v / d₂ := by positivity
        rw [lintegral_gammaMeasure _ _ (by fun_prop : Measurable fun u ↦ F ((u / d₁) / (v / d₂))),
          setLIntegral_Ioi_eq_mul_comp_mul hc (by fun_prop),
          ← lintegral_const_mul _ (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
        refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        have hxe : (d₁ * v / d₂ * x / d₁) / (v / d₂) = x := by field_simp
        have hk : ENNReal.ofReal (fKernel d₁ d₂ v x) =
            ENNReal.ofReal ((1 / 2) ^ (d₂ / 2) / Gamma (d₂ / 2) * v ^ (d₂ / 2 - 1) *
              exp (-(1 / 2 * v))) * (ENNReal.ofReal (d₁ * v / d₂) *
              ENNReal.ofReal ((1 / 2) ^ (d₁ / 2) / Gamma (d₁ / 2) * (d₁ * v / d₂ * x) ^ (d₁ / 2 - 1) *
                exp (-(1 / 2 * (d₁ * v / d₂ * x))))) := by
          unfold fKernel
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (d₂ / 2) / Gamma (d₂ / 2) *
            v ^ (d₂ / 2 - 1) * exp (-(1 / 2 * v))), ENNReal.ofReal_mul hc.le]
        rw [hk, hxe]
        ring
    _ = ∫⁻ x in Ioi 0, ∫⁻ v in Ioi 0, ENNReal.ofReal (fKernel d₁ d₂ v x) * F x := by
        refine lintegral_lintegral_swap ?_
        unfold fKernel
        fun_prop
    _ = ∫⁻ x in Ioi 0, ENNReal.ofReal (fPDFReal d₁ d₂ x) * F x := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        rw [lintegral_mul_const _ (by unfold fKernel; fun_prop), lintegral_fKernel hd₁ hd₂ hx]
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun x hx ↦ ?_
        by_contra h
        have h' : ¬ 0 < x := h
        exact hx (by simp [fPDFReal, h'])

/-- The F density integrates to one. -/
theorem isProbabilityMeasure_fDistribution {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    IsProbabilityMeasure (fDistribution d₁ d₂) := by
  have := isProbabilityMeasure_chiSquared' hd₁
  have := isProbabilityMeasure_chiSquared' hd₂
  constructor
  have h := lintegral_f_ratio hd₁ hd₂ (F := fun _ ↦ 1) measurable_const
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [fDistribution, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← h]

/-- The law of `(U/d₁)/(V/d₂)` under the product of `χ²(d₁)` and `χ²(d₂)` is the F law. -/
theorem map_prod_fDistribution {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ((chiSquared d₁).prod (chiSquared d₂)).map (fun p : ℝ × ℝ ↦ (p.1 / d₁) / (p.2 / d₂)) =
      fDistribution d₁ d₂ := by
  have hg : Measurable fun p : ℝ × ℝ ↦ (p.1 / d₁) / (p.2 / d₂) := by fun_prop
  ext A hA
  rw [Measure.map_apply hg hA, ← lintegral_indicator_one (hg hA), fDistribution,
    withDensity_apply _ hA, ← lintegral_indicator hA]
  have h := lintegral_f_ratio hd₁ hd₂ (F := A.indicator 1) (measurable_one.indicator hA)
  have h1 : ∀ p : ℝ × ℝ, ((fun p : ℝ × ℝ ↦ (p.1 / d₁) / (p.2 / d₂)) ⁻¹' A).indicator 1 p =
      A.indicator (1 : ℝ → ENNReal) ((p.1 / d₁) / (p.2 / d₂)) := by
    intro p
    by_cases hp : (p.1 / d₁) / (p.2 / d₂) ∈ A <;> simp [hp]
  have h2 : ∀ t, A.indicator (fun x ↦ ENNReal.ofReal (fPDFReal d₁ d₂ x)) t =
      ENNReal.ofReal (fPDFReal d₁ d₂ t) * A.indicator 1 t := by
    intro t
    by_cases ht : t ∈ A <;> simp [ht]
  rw [lintegral_congr fun p ↦ h1 p, h]
  exact lintegral_congr fun t ↦ (h2 t).symm

/-- **The F law** (§13.3). If `U` is chi-square with `d₁` degrees of freedom, `V` is chi-square with `d₂`
degrees of freedom and `U`, `V` are independent, then `F = (U/d₁)/(V/d₂)` has the F distribution with
`d₁` numerator and `d₂` denominator degrees of freedom. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem hasLaw_fDistribution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U V : Ω → ℝ} {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hU : HasLaw U (chiSquared d₁) P)
    (hV : HasLaw V (chiSquared d₂) P) (hind : IndepFun U V P) :
    HasLaw (fun ω ↦ (U ω / d₁) / (V ω / d₂)) (fDistribution d₁ d₂) P := by
  have hg : Measurable fun p : ℝ × ℝ ↦ (p.1 / d₁) / (p.2 / d₂) := by fun_prop
  have hpair : AEMeasurable (fun ω ↦ (U ω, V ω)) P := hU.aemeasurable.prodMk hV.aemeasurable
  refine ⟨by fun_prop, ?_⟩
  have hmap : P.map (fun ω ↦ (U ω, V ω)) = (chiSquared d₁).prod (chiSquared d₂) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hind, hU.map_eq,
      hV.map_eq]
  rw [← map_prod_fDistribution hd₁ hd₂, ← hmap,
    AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hpair]
  rfl

/-- The F variable is almost surely positive (hence nonnegative). -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem hasLaw_fDistribution_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {d₁ d₂ : ℝ} (hX : HasLaw X (fDistribution d₁ d₂) P) : ∀ᵐ ω ∂P, 0 < X ω := by
  have h : P {ω | X ω ≤ 0} = 0 := by
    rw [hX.measure_eq (p := fun y ↦ y ≤ 0) measurableSet_Iic]
    exact fDistribution_Iic_zero d₁ d₂
  rw [ae_iff]
  simpa [not_lt] using h

/-- **Reciprocal of an F variable** (§13.4): swapping the roles of numerator and denominator, `1/F` has the
F distribution with `d₂`, `d₁` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§13.4, p. 701"]
theorem hasLaw_inv_fDistribution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U V : Ω → ℝ} {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hU : HasLaw U (chiSquared d₁) P)
    (hV : HasLaw V (chiSquared d₂) P) (hind : IndepFun U V P) :
    HasLaw (fun ω ↦ ((U ω / d₁) / (V ω / d₂))⁻¹) (fDistribution d₂ d₁) P := by
  have h := hasLaw_fDistribution hd₂ hd₁ hV hU hind.symm
  simpa only [inv_div] using h

end UndergradKB.Statistics
