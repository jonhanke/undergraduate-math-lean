import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import UndergradKB.Statistics.ChiSquared

/-!
# The Student t distribution

OpenStax *Introductory Statistics 2e*, §8.2: for a normal population the statistic `(x̄ - μ) / (s / √n)` follows the
Student t distribution with `n - 1` degrees of freedom; the t distribution is symmetric about `0` and bell shaped.
Mathlib has no Student t law. We define it by its density

  `f_ν(t) = Γ((ν+1)/2) / (√(νπ) Γ(ν/2)) · (1 + t²/ν)^(-(ν+1)/2)`

and prove the fact every t procedure rests on (`hasLaw_studentT`): if `Z` is standard normal, `V` is chi-square
with `ν` degrees of freedom and `Z`, `V` are independent, then `Z / √(V/ν)` has this law. In particular the density
integrates to one (`isProbabilityMeasure_studentT`). The proof integrates over `z` for fixed `v` with the linear
substitution `z = √(v/ν) t`, swaps the integrals (Tonelli) and evaluates the remaining gamma integral in `v`.
The application to a normal sample is in `UndergradKB.Statistics.NormalSample`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

/-- The density of the Student t distribution with `ν` degrees of freedom. -/
noncomputable def studentTPDFReal (ν x : ℝ) : ℝ :=
  Gamma ((ν + 1) / 2) / (√(ν * π) * Gamma (ν / 2)) * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))

/-- The Student t distribution with `ν` degrees of freedom, as a measure on `ℝ` with density `studentTPDFReal ν`. -/
noncomputable def studentT (ν : ℝ) : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (studentTPDFReal ν x)

@[fun_prop]
lemma measurable_studentTPDFReal (ν : ℝ) : Measurable (studentTPDFReal ν) := by
  unfold studentTPDFReal; fun_prop

lemma studentTPDFReal_pos {ν : ℝ} (hν : 0 < ν) (x : ℝ) : 0 < studentTPDFReal ν x := by
  unfold studentTPDFReal
  have := Gamma_pos_of_pos (by positivity : 0 < (ν + 1) / 2)
  have := Gamma_pos_of_pos (by positivity : 0 < ν / 2)
  positivity

/-- **Symmetry of the t density** (§8.2): `f_ν(-t) = f_ν(t)`. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem studentTPDFReal_neg (ν x : ℝ) : studentTPDFReal ν (-x) = studentTPDFReal ν x := by
  simp [studentTPDFReal]

/-- **The t density is bell shaped** (§8.2): it increases on `(-∞, 0]` and decreases on `[0, ∞)`; that is,
`f_ν(t) ≤ f_ν(s)` whenever `|s| ≤ |t|`. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem studentTPDFReal_le_of_abs_le {ν : ℝ} (hν : 0 < ν) {s t : ℝ} (h : |s| ≤ |t|) :
    studentTPDFReal ν t ≤ studentTPDFReal ν s := by
  unfold studentTPDFReal
  have := Gamma_pos_of_pos (by positivity : 0 < (ν + 1) / 2)
  have := Gamma_pos_of_pos (by positivity : 0 < ν / 2)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith [show 0 < (ν + 1) / 2 by positivity])
  have : s ^ 2 ≤ t ^ 2 := sq_le_sq.2 h
  gcongr

/-! ### The linear substitution and the inner Gaussian integral -/

/-- Linear substitution for the lower integral on `ℝ`: `∫ G(z) dz = c ∫ G(c t) dt` for `c > 0`. -/
lemma lintegral_eq_mul_lintegral_comp_mul {c : ℝ} (hc : 0 < c) {G : ℝ → ENNReal} (hG : Measurable G) :
    ∫⁻ z, G z = ENNReal.ofReal c * ∫⁻ t, G (c * t) := by
  rw [← lintegral_map hG (measurable_const_mul c), Real.map_volume_mul_left hc.ne',
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.2 hc),
    mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

/-- For a standard normal `Z` and `c > 0`: `E[F(Z / c)] = ∫ c φ(c t) F(t) dt`, with `φ` the standard normal
density. -/
lemma lintegral_gaussianReal_comp_div {c : ℝ} (hc : 0 < c) {F : ℝ → ENNReal} (hF : Measurable F) :
    ∫⁻ z, F (z / c) ∂(gaussianReal 0 1) =
      ∫⁻ t, ENNReal.ofReal (c * gaussianPDFReal 0 1 (c * t)) * F t := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gaussianPDF _ _) (by fun_prop : Measurable fun z ↦ F (z / c)),
    lintegral_eq_mul_lintegral_comp_mul hc (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_congr fun t ↦ ?_
  simp only [Pi.mul_apply, gaussianPDF, mul_div_cancel_left₀ _ hc.ne']
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le]

/-! ### The kernel identity -/

/-- The joint integrand after the substitution, as a function of `v` (the chi-square value) and `t`. -/
noncomputable def studentTKernel (ν v t : ℝ) : ℝ :=
  (1 / 2) ^ (ν / 2) / Gamma (ν / 2) * v ^ (ν / 2 - 1) * exp (-(1 / 2 * v)) *
    (√(v / ν) * gaussianPDFReal 0 1 (√(v / ν) * t))

lemma studentTKernel_eq {ν v : ℝ} (hν : 0 < ν) (hv : 0 < v) (t : ℝ) :
    studentTKernel ν v t = (1 / 2) ^ (ν / 2) / Gamma (ν / 2) * (√(2 * π))⁻¹ * (√ν)⁻¹ *
      (v ^ ((ν + 1) / 2 - 1) * exp (-((1 + t ^ 2 / ν) / 2 * v))) := by
  have hsq : √(v / ν) ^ 2 = v / ν := sq_sqrt (by positivity)
  have hp : v ^ ((ν + 1) / 2 - 1) = v ^ (ν / 2 - 1) * √v := by
    rw [sqrt_eq_rpow, ← rpow_add hv]
    congr 1
    ring
  have he : exp (-(1 / 2 * v)) * exp (-(√(v / ν) * t - 0) ^ 2 / (2 * 1)) =
      exp (-((1 + t ^ 2 / ν) / 2 * v)) := by
    rw [← exp_add]
    congr 1
    rw [sub_zero, mul_pow, hsq]
    field_simp
    ring
  unfold studentTKernel gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  rw [hp, ← he, sqrt_div hv.le]
  have : 0 < √ν := sqrt_pos.2 hν
  field_simp

/-- The constant: `c_ν (2/(1 + t²/ν))^((ν+1)/2) Γ((ν+1)/2)` is the t density. -/
lemma studentT_constant {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    (1 / 2) ^ (ν / 2) / Gamma (ν / 2) * (√(2 * π))⁻¹ * (√ν)⁻¹ *
      ((1 / ((1 + t ^ 2 / ν) / 2)) ^ ((ν + 1) / 2) * Gamma ((ν + 1) / 2)) = studentTPDFReal ν t := by
  have hu : 0 < 1 + t ^ 2 / ν := by positivity
  have hG := Gamma_pos_of_pos (by positivity : 0 < ν / 2)
  have h2 : (2 : ℝ) ^ ((ν + 1) / 2) = 2 ^ (ν / 2) * √2 := by
    rw [sqrt_eq_rpow, ← rpow_add two_pos]
    congr 1
    ring
  unfold studentTPDFReal
  rw [show 1 / ((1 + t ^ 2 / ν) / 2) = 2 / (1 + t ^ 2 / ν) by field_simp,
    div_rpow zero_le_two hu.le, h2, div_rpow zero_le_one zero_le_two, one_rpow,
    rpow_neg hu.le, sqrt_mul (by positivity), sqrt_mul hν.le]
  have : 0 < (2 : ℝ) ^ (ν / 2) := by positivity
  have : 0 < (1 + t ^ 2 / ν) ^ ((ν + 1) / 2) := by positivity
  have : 0 < √2 := by positivity
  have : 0 < √π := sqrt_pos.2 pi_pos
  have : 0 < √ν := sqrt_pos.2 hν
  field_simp

/-- The integral of the kernel over `v > 0` is the t density. -/
lemma lintegral_studentTKernel {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    ∫⁻ v in Ioi 0, ENNReal.ofReal (studentTKernel ν v t) = ENNReal.ofReal (studentTPDFReal ν t) := by
  have hG := Gamma_pos_of_pos (by positivity : 0 < ν / 2)
  rw [setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) ↦ by
      rw [studentTKernel_eq hν hv t, ENNReal.ofReal_mul (by positivity)],
    lintegral_const_mul _ (by fun_prop),
    lintegral_rpow_mul_exp_neg_mul_Ioi (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), studentT_constant hν t]

/-! ### The law of `Z / √(V/ν)` -/

/-- Integration formula behind the t law: for independent `Z ~ N(0,1)` and `V ~ χ²(ν)` (product law),
`E[F(Z/√(V/ν))] = ∫ F(t) f_ν(t) dt`. -/
theorem lintegral_studentT_ratio {ν : ℝ} (hν : 0 < ν) {F : ℝ → ENNReal} (hF : Measurable F) :
    ∫⁻ p, F (p.1 / √(p.2 / ν)) ∂((gaussianReal 0 1).prod (chiSquared ν)) =
      ∫⁻ t, ENNReal.ofReal (studentTPDFReal ν t) * F t := by
  have := isProbabilityMeasure_chiSquared' hν
  have hm : Measurable fun p : ℝ × ℝ ↦ F (p.1 / √(p.2 / ν)) := by fun_prop
  rw [lintegral_prod_symm' _ hm, chiSquared,
    lintegral_gammaMeasure _ _ (Measurable.lintegral_prod_left' hm)]
  calc ∫⁻ v in Ioi 0, ENNReal.ofReal ((1 / 2) ^ (ν / 2) / Gamma (ν / 2) * v ^ (ν / 2 - 1) *
          exp (-(1 / 2 * v))) * ∫⁻ z, F (z / √(v / ν)) ∂(gaussianReal 0 1)
      = ∫⁻ v in Ioi 0, ∫⁻ t, ENNReal.ofReal (studentTKernel ν v t) * F t := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) ↦ ?_
        have hc : 0 < √(v / ν) := sqrt_pos.2 (div_pos hv hν)
        rw [lintegral_gaussianReal_comp_div hc hF, ← lintegral_const_mul _ (by fun_prop)]
        refine lintegral_congr fun t ↦ ?_
        have hG := Gamma_pos_of_pos (by positivity : 0 < ν / 2)
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), studentTKernel]
    _ = ∫⁻ t, ∫⁻ v in Ioi 0, ENNReal.ofReal (studentTKernel ν v t) * F t := by
        refine lintegral_lintegral_swap ?_
        unfold studentTKernel
        fun_prop
    _ = ∫⁻ t, ENNReal.ofReal (studentTPDFReal ν t) * F t := by
        refine lintegral_congr fun t ↦ ?_
        rw [lintegral_mul_const _ (by unfold studentTKernel; fun_prop), lintegral_studentTKernel hν]

/-- The Student t density integrates to one. -/
instance isProbabilityMeasure_studentT {ν : ℝ} [Fact (0 < ν)] : IsProbabilityMeasure (studentT ν) := by
  have hν : 0 < ν := Fact.out
  have := isProbabilityMeasure_chiSquared' hν
  constructor
  have h := lintegral_studentT_ratio hν (F := fun _ ↦ 1) measurable_const
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [studentT, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← h]

lemma isProbabilityMeasure_studentT' {ν : ℝ} (hν : 0 < ν) : IsProbabilityMeasure (studentT ν) :=
  have : Fact (0 < ν) := ⟨hν⟩
  inferInstance

/-- The law of `Z / √(V/ν)` under the product of `N(0,1)` and `χ²(ν)` is the Student t law. -/
theorem map_prod_studentT {ν : ℝ} (hν : 0 < ν) :
    ((gaussianReal 0 1).prod (chiSquared ν)).map (fun p : ℝ × ℝ ↦ p.1 / √(p.2 / ν)) = studentT ν := by
  have hg : Measurable fun p : ℝ × ℝ ↦ p.1 / √(p.2 / ν) := by fun_prop
  ext A hA
  rw [Measure.map_apply hg hA, ← lintegral_indicator_one (hg hA), studentT, withDensity_apply _ hA,
    ← lintegral_indicator hA]
  have h := lintegral_studentT_ratio hν (F := A.indicator 1) (measurable_one.indicator hA)
  have h1 : ∀ p : ℝ × ℝ, ((fun p : ℝ × ℝ ↦ p.1 / √(p.2 / ν)) ⁻¹' A).indicator 1 p =
      A.indicator (1 : ℝ → ENNReal) (p.1 / √(p.2 / ν)) := by
    intro p
    by_cases hp : p.1 / √(p.2 / ν) ∈ A <;> simp [hp]
  have h2 : ∀ t, A.indicator (fun x ↦ ENNReal.ofReal (studentTPDFReal ν x)) t =
      ENNReal.ofReal (studentTPDFReal ν t) * A.indicator 1 t := by
    intro t
    by_cases ht : t ∈ A <;> simp [ht]
  rw [lintegral_congr fun p ↦ h1 p, h]
  exact lintegral_congr fun t ↦ (h2 t).symm

/-- **The Student t law** (§8.2). If `Z` has the standard normal law, `V` has the chi-square law with `ν`
degrees of freedom and `Z`, `V` are independent, then `T = Z / √(V/ν)` has the Student t distribution with
`ν` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem hasLaw_studentT {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z V : Ω → ℝ} {ν : ℝ} (hν : 0 < ν) (hZ : HasLaw Z (gaussianReal 0 1) P)
    (hV : HasLaw V (chiSquared ν) P) (hind : IndepFun Z V P) :
    HasLaw (fun ω ↦ Z ω / √(V ω / ν)) (studentT ν) P := by
  have hg : Measurable fun p : ℝ × ℝ ↦ p.1 / √(p.2 / ν) := by fun_prop
  have hpair : AEMeasurable (fun ω ↦ (Z ω, V ω)) P := hZ.aemeasurable.prodMk hV.aemeasurable
  refine ⟨by fun_prop, ?_⟩
  have hmap : P.map (fun ω ↦ (Z ω, V ω)) = (gaussianReal 0 1).prod (chiSquared ν) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hV.aemeasurable).1 hind, hZ.map_eq,
      hV.map_eq]
  rw [← map_prod_studentT hν, ← hmap, AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hpair]
  rfl

end UndergradKB.Statistics
