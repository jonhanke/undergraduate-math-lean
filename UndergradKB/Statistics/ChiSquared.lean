import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import UndergradKB.Statistics.MGF

/-!
# The chi-square distribution

OpenStax *Introductory Statistics 2e*, §11.1: the chi-square distribution with `k` degrees of freedom is the law of
a sum of `k` squares of independent standard normal variables; it has mean `k` and standard deviation `√(2k)`.

Mathlib has the gamma law (`ProbabilityTheory.gammaMeasure a r`, shape `a`, rate `r`) but no chi-square law. We
define `chiSquared k := gammaMeasure (k/2) (1/2)` (the usual definition) and prove the book's description:
* `mgf_gammaMeasure`: the moment generating function of the gamma law is `(r/(r - t))^a` for `t < r`;
* `hasLaw_sq_chiSquared_one`: the square of a standard normal variable is chi-square with one degree of freedom;
* `hasLaw_sum_chiSquared`: independent chi-square variables add, degrees of freedom add;
* `hasLaw_sum_sq_chiSquared`: the sum of squares of `n` independent standard normals is chi-square with `n`
  degrees of freedom;
* `integral_id_chiSquared`, `variance_id_chiSquared`: mean `k` and variance `2k`.
The laws are identified through moment generating functions (`UndergradKB.Statistics.ext_of_mgf_eqOn`).
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

/-! ### Integrals of nonnegative functions given by a lower integral -/

/-- A nonnegative function whose lower Lebesgue integral is `ofReal c` is integrable, with integral `c`. -/
lemma integrable_integral_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hnn : 0 ≤ᵐ[μ] f) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal c) :
    Integrable f μ ∧ ∫ x, f x ∂μ = c := by
  refine ⟨⟨hf, (hasFiniteIntegral_iff_ofReal hnn).2 (h ▸ ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf, h, ENNReal.toReal_ofReal hc]

/-- The gamma integral in lower-integral form: `∫₀^∞ x^(a-1) e^(-b x) dx = Γ(a) / b^a`. -/
lemma lintegral_rpow_mul_exp_neg_mul_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal (x ^ (a - 1) * exp (-(b * x))) =
      ENNReal.ofReal ((1 / b) ^ a * Gamma a) := by
  have hI : IntegrableOn (fun x : ℝ ↦ x ^ (a - 1) * exp (-(b * x))) (Ioi 0) := by
    by_contra h
    have h0 := integral_undef h
    rw [integral_rpow_mul_exp_neg_mul_Ioi ha hb] at h0
    have : 0 < (1 / b) ^ a * Gamma a := by positivity
    linarith
  rw [← integral_rpow_mul_exp_neg_mul_Ioi ha hb, ofReal_integral_eq_lintegral_ofReal hI]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
  positivity

/-! ### The gamma law -/

/-- Integration of a nonnegative function against the gamma law, as an integral over `(0, ∞)`. -/
lemma lintegral_gammaMeasure (a r : ℝ) {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ x, g x ∂(gammaMeasure a r) =
      ∫⁻ x in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) * g x := by
  have hm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hm hg, ← lintegral_add_compl _ measurableSet_Ioi,
    compl_Ioi]
  have h0 : ∫⁻ x in Iic 0, (gammaPDF a r * g) x = 0 := by
    rw [← setLIntegral_congr Iio_ae_eq_Iic]
    refine (setLIntegral_congr_fun measurableSet_Iio fun x (hx : x < 0) ↦ ?_).trans lintegral_zero
    simp [gammaPDF_of_neg hx]
  rw [h0, add_zero]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
  simp [gammaPDF_of_nonneg hx.le]

/-- The moment generating function of the gamma law, in lower-integral form: for `t < r`,
`∫ e^(t x) dΓ(a, r) = (r / (r - t))^a`. -/
lemma lintegral_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫⁻ x, ENNReal.ofReal (exp (t * x)) ∂(gammaMeasure a r) = ENNReal.ofReal ((r / (r - t)) ^ a) := by
  rw [lintegral_gammaMeasure a r (by fun_prop)]
  have hrt : 0 < r - t := by linarith
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  calc ∫⁻ x in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) *
          ENNReal.ofReal (exp (t * x))
      = ∫⁻ x in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a) *
          ENNReal.ofReal (x ^ (a - 1) * exp (-((r - t) * x))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show -((r - t) * x) = -(r * x) + t * x by ring, exp_add]
        ring
    _ = ENNReal.ofReal (r ^ a / Gamma a) * ENNReal.ofReal ((1 / (r - t)) ^ a * Gamma a) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_rpow_mul_exp_neg_mul_Ioi ha hrt]
    _ = ENNReal.ofReal ((r / (r - t)) ^ a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_rpow hr.le hrt.le, div_rpow zero_le_one hrt.le, one_rpow]
        field_simp

/-- The moment generating function of the gamma law `Γ(a, r)` (shape `a`, rate `r`) is finite for `t < r`
and equals `(r / (r - t))^a`. -/
theorem mgf_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) ∧
      mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a := by
  have := integrable_integral_of_lintegral (μ := gammaMeasure a r) (f := fun x ↦ exp (t * x))
    (by fun_prop) (ae_of_all _ fun x ↦ (exp_pos _).le)
    (rpow_nonneg (div_nonneg hr.le (by linarith)) a) (lintegral_exp_mul_gammaMeasure ha hr ht)
  exact ⟨this.1, by simpa [mgf] using this.2⟩

/-! ### Identifying a law by its moment generating function -/

/-- A random variable whose moment generating function agrees near `0` with that of a law `μ` (both finite)
has law `μ`. -/
lemma hasLaw_of_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {μ : Measure ℝ} [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ)
    (hXi : ∀ t ∈ Ioo (-δ) δ, Integrable (fun ω ↦ exp (t * X ω)) P)
    (hμ : ∀ t ∈ Ioo (-δ) δ, Integrable (fun x ↦ exp (t * x)) μ)
    (h : ∀ t ∈ Ioo (-δ) δ, mgf X P t = mgf id μ t) : HasLaw X μ P := by
  refine ⟨hX, ?_⟩
  have hmap := map_eq_of_mgf_eqOn (P' := μ) (Y := id) hX aemeasurable_id hδ hXi
    (by simpa using hμ) (by simpa using h)
  simpa using hmap

/-! ### The chi-square law -/

/-- The chi-square law with `k` degrees of freedom: the gamma law of shape `k/2` and rate `1/2`. -/
noncomputable def chiSquared (k : ℝ) : Measure ℝ := gammaMeasure (k / 2) (1 / 2)

instance isProbabilityMeasure_chiSquared {k : ℝ} [Fact (0 < k)] : IsProbabilityMeasure (chiSquared k) :=
  isProbabilityMeasure_gammaMeasure (by have := (Fact.out : 0 < k); positivity) (by norm_num)

lemma isProbabilityMeasure_chiSquared' {k : ℝ} (hk : 0 < k) : IsProbabilityMeasure (chiSquared k) :=
  isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)

/-- The moment generating function of the chi-square law with `k` degrees of freedom: for `t < 1/2` it is
finite and equals `(1 - 2t)^(-k/2)`. -/
theorem mgf_chiSquared {k t : ℝ} (hk : 0 < k) (ht : t < 1 / 2) :
    Integrable (fun x ↦ exp (t * x)) (chiSquared k) ∧
      mgf id (chiSquared k) t = (1 - 2 * t) ^ (-(k / 2)) := by
  obtain ⟨h1, h2⟩ := mgf_gammaMeasure (a := k / 2) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2) ht
  refine ⟨h1, ?_⟩
  rw [chiSquared, h2, rpow_neg (by linarith), ← inv_rpow (by linarith)]
  congr 1
  field_simp

/-- If the moment generating function of `X` is `(1 - 2t)^(-k/2)` near `0`, then `X` is chi-square with `k`
degrees of freedom. -/
lemma hasLaw_chiSquared_of_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) {k δ : ℝ} (hk : 0 < k) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hXi : ∀ t ∈ Ioo (-δ) δ, Integrable (fun ω ↦ exp (t * X ω)) P)
    (h : ∀ t ∈ Ioo (-δ) δ, mgf X P t = (1 - 2 * t) ^ (-(k / 2))) : HasLaw X (chiSquared k) P := by
  have := isProbabilityMeasure_chiSquared' hk
  refine hasLaw_of_mgf hX hδ hXi (fun t ht ↦ (mgf_chiSquared hk (by linarith [ht.2])).1) fun t ht ↦ ?_
  rw [h t ht, (mgf_chiSquared hk (by linarith [ht.2])).2]

/-- The moment generating function of `Z²` for a standard normal `Z`, in lower-integral form:
`∫ e^(t z²) dN(0,1) = (1 - 2t)^(-1/2)` for `t < 1/2`. -/
lemma lintegral_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (exp (t * x ^ 2)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal ((1 - 2 * t) ^ (-(1 / 2 : ℝ))) := by
  have hb : 0 < 1 / 2 - t := by linarith
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gaussianPDF _ _) (by fun_prop)]
  have hpt : ∀ x : ℝ, (gaussianPDF 0 1 * fun x ↦ ENNReal.ofReal (exp (t * x ^ 2))) x =
      ENNReal.ofReal ((√(2 * π))⁻¹ * exp (-(1 / 2 - t) * x ^ 2)) := by
    intro x
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← exp_add]
    congr 3
    ring
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul _)
    (ae_of_all _ fun x ↦ by positivity), integral_const_mul, integral_gaussian]
  congr 1
  have h12 : 0 < 1 - 2 * t := by linarith
  rw [rpow_neg h12.le, ← sqrt_eq_rpow, ← sqrt_inv, ← sqrt_inv, ← sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- **Chi-square with one degree of freedom.** The square of a standard normal variable `Z` has the chi-square
law with one degree of freedom. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem hasLaw_sq_chiSquared_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) : HasLaw (fun ω ↦ Z ω ^ 2) (chiSquared 1) P := by
  have key : ∀ t : ℝ, t < 1 / 2 → Integrable (fun ω ↦ exp (t * Z ω ^ 2)) P ∧
      mgf (fun ω ↦ Z ω ^ 2) P t = (1 - 2 * t) ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have h := integrable_integral_of_lintegral (μ := gaussianReal 0 1) (f := fun x ↦ exp (t * x ^ 2))
      (by fun_prop) (ae_of_all _ fun x ↦ (exp_pos _).le) (by apply rpow_nonneg; linarith)
      (lintegral_exp_mul_sq_gaussianReal ht)
    rw [← hZ.map_eq] at h
    refine ⟨(integrable_map_measure (by fun_prop) hZ.aemeasurable).1 h.1, ?_⟩
    rw [← h.2, integral_map hZ.aemeasurable (by fun_prop)]
    rfl
  refine hasLaw_chiSquared_of_mgf (by fun_prop) one_pos (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
    (fun t ht ↦ (key t ht.2).1) fun t ht ↦ ?_
  rw [(key t ht.2).2]

/-- **Sums of independent chi-square variables.** If `X₁, …, Xₙ` are independent and `Xᵢ` is chi-square with
`kᵢ` degrees of freedom, then `X₁ + ⋯ + Xₙ` is chi-square with `k₁ + ⋯ + kₙ` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem hasLaw_sum_chiSquared {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Finset ι} (hs : s.Nonempty) {X : ι → Ω → ℝ} {k : ι → ℝ} (hk : ∀ i ∈ s, 0 < k i)
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hX : ∀ i ∈ s, HasLaw (X i) (chiSquared (k i)) P) :
    HasLaw (∑ i ∈ s, X i) (chiSquared (∑ i ∈ s, k i)) P := by
  have hpos : 0 < ∑ i ∈ s, k i := Finset.sum_pos hk hs
  have hone : ∀ i ∈ s, ∀ t : ℝ, t < 1 / 2 → Integrable (fun ω ↦ exp (t * X i ω)) P ∧
      mgf (X i) P t = (1 - 2 * t) ^ (-(k i / 2)) := by
    intro i hi t ht
    have h := mgf_chiSquared (hk i hi) ht
    rw [← (hX i hi).map_eq] at h
    refine ⟨(integrable_map_measure (by fun_prop) (hX i hi).aemeasurable).1 h.1, ?_⟩
    rw [← h.2, mgf_id_map (hX i hi).aemeasurable]
  refine hasLaw_chiSquared_of_mgf (by fun_prop) hpos (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
    (fun t ht ↦ hind.integrable_exp_mul_sum hmeas fun i hi ↦ (hone i hi t ht.2).1) fun t ht ↦ ?_
  rw [hind.mgf_sum hmeas, Finset.prod_congr rfl fun i hi ↦ (hone i hi t ht.2).2,
    ← rpow_sum_of_pos (by linarith [ht.2]), Finset.sum_neg_distrib, Finset.sum_div]

/-- **The chi-square law as a sum of squares** (§11.1). If `Z₁, …, Zₙ` (`n ≥ 1`) are independent standard normal
variables, then `Z₁² + ⋯ + Zₙ²` has the chi-square law with `n` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem hasLaw_sum_sq_chiSquared {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Finset ι} (hs : s.Nonempty) {Z : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hZ : ∀ i ∈ s, HasLaw (Z i) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ ∑ i ∈ s, Z i ω ^ 2) (chiSquared s.card) P := by
  have hind2 : iIndepFun (fun i ω ↦ Z i ω ^ 2) P :=
    hind.comp (fun _ x ↦ x ^ 2) fun _ ↦ by fun_prop
  have h := hasLaw_sum_chiSquared (k := fun _ ↦ (1 : ℝ)) hs (fun _ _ ↦ one_pos)
    (fun i ↦ (hmeas i).pow_const 2) hind2 fun i hi ↦ hasLaw_sq_chiSquared_one (hZ i hi)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  convert h using 1
  ext ω
  simp [Finset.sum_apply]

/-! ### Mean and variance -/

/-- Moments of the gamma law: `∫ x^p dΓ(a, r) = Γ(a + p) / (Γ(a) r^p)` for `p ≥ 0`, in lower-integral form. -/
lemma lintegral_rpow_gammaMeasure {a r p : ℝ} (ha : 0 < a) (hr : 0 < r) (hp : 0 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (max x 0 ^ p) ∂(gammaMeasure a r) =
      ENNReal.ofReal (Gamma (a + p) / (Gamma a * r ^ p)) := by
  rw [lintegral_gammaMeasure a r (by fun_prop)]
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  calc ∫⁻ x in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) *
          ENNReal.ofReal (max x 0 ^ p)
      = ∫⁻ x in Ioi 0, ENNReal.ofReal (r ^ a / Gamma a) *
          ENNReal.ofReal (x ^ (a + p - 1) * exp (-(r * x))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          max_eq_left hx.le]
        congr 1
        rw [show a + p - 1 = (a - 1) + p by ring, rpow_add hx]
        ring
    _ = ENNReal.ofReal (r ^ a / Gamma a) * ENNReal.ofReal ((1 / r) ^ (a + p) * Gamma (a + p)) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_rpow_mul_exp_neg_mul_Ioi (by linarith) hr]
    _ = ENNReal.ofReal (Gamma (a + p) / (Gamma a * r ^ p)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_rpow zero_le_one hr.le, one_rpow, rpow_add hr]
        field_simp

/-- On the gamma law, `x = max x 0` almost everywhere (the law lives on `[0, ∞)`). -/
lemma ae_nonneg_gammaMeasure (a r : ℝ) : ∀ᵐ x ∂(gammaMeasure a r), 0 ≤ x := by
  have hm : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, ae_withDensity_iff hm]
  refine ae_of_all _ fun x hx ↦ ?_
  by_contra h
  exact hx (gammaPDF_of_neg (not_le.mp h))

/-- Moments of the gamma law, `∫ x^n dΓ(a, r) = Γ(a + n) / (Γ(a) r^n)` for a natural number `n`, with
integrability. -/
lemma integral_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x ↦ x ^ n) (gammaMeasure a r) ∧
      ∫ x, x ^ n ∂(gammaMeasure a r) = Gamma (a + n) / (Gamma a * r ^ (n : ℝ)) := by
  have hae : (fun x : ℝ ↦ x ^ n) =ᵐ[gammaMeasure a r] fun x ↦ max x 0 ^ (n : ℝ) := by
    filter_upwards [ae_nonneg_gammaMeasure a r] with x hx
    rw [max_eq_left hx, rpow_natCast]
  have h := integrable_integral_of_lintegral (μ := gammaMeasure a r) (f := fun x ↦ max x 0 ^ (n : ℝ))
    (by fun_prop) (ae_of_all _ fun x ↦ rpow_nonneg (le_max_right _ _) _)
    (div_nonneg (Gamma_pos_of_pos (by positivity : 0 < a + n)).le
      (mul_pos (Gamma_pos_of_pos ha) (rpow_pos_of_pos hr _)).le)
    (lintegral_rpow_gammaMeasure ha hr (Nat.cast_nonneg n))
  exact ⟨h.1.congr hae.symm, by rw [integral_congr_ae hae, h.2]⟩

/-- **Mean of the chi-square law** (§11.1): the chi-square law with `k` degrees of freedom has mean `k`. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem integral_id_chiSquared {k : ℝ} (hk : 0 < k) : ∫ x, x ∂(chiSquared k) = k := by
  have h := (integral_pow_gammaMeasure (a := k / 2) (r := 1 / 2) (by positivity) (by norm_num) 1).2
  simp only [pow_one, Nat.cast_one, rpow_one] at h
  rw [chiSquared, h, Gamma_add_one (show k / 2 ≠ 0 by positivity)]
  have := Gamma_pos_of_pos (by positivity : 0 < k / 2)
  field_simp

/-- **Variance of the chi-square law** (§11.1): the chi-square law with `k` degrees of freedom has variance `2k`
(standard deviation `√(2k)`). -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem variance_id_chiSquared {k : ℝ} (hk : 0 < k) : variance id (chiSquared k) = 2 * k := by
  have := isProbabilityMeasure_chiSquared' hk
  have h2 := integral_pow_gammaMeasure (a := k / 2) (r := 1 / 2) (by positivity) (by norm_num) 2
  have hm : MemLp id 2 (chiSquared k) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h2.1
  have hG := Gamma_pos_of_pos (by positivity : 0 < k / 2)
  have g2 : Gamma (k / 2 + ((2 : ℕ) : ℝ)) = (k / 2 + 1) * (k / 2) * Gamma (k / 2) := by
    rw [show k / 2 + ((2 : ℕ) : ℝ) = (k / 2 + 1) + 1 by norm_num; ring,
      Gamma_add_one (by positivity), Gamma_add_one (by positivity)]
    ring
  have e2 : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂(chiSquared k) = (k / 2 + 1) * (k / 2) * 4 := by
    have : ∫ x, (id ^ 2 : ℝ → ℝ) x ∂(chiSquared k) = ∫ x, x ^ 2 ∂(gammaMeasure (k / 2) (1 / 2)) := rfl
    rw [this, h2.2, g2]
    have : ((1 : ℝ) / 2) ^ ((2 : ℕ) : ℝ) = 1 / 4 := by norm_num
    rw [this]
    field_simp
  rw [variance_eq_sub hm, e2]
  have e1 : ∫ x, id x ∂(chiSquared k) = k := integral_id_chiSquared hk
  rw [e1]
  ring

end UndergradKB.Statistics
