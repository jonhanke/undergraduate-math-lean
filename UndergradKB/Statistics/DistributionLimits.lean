import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Real
import UndergradKB.Common.Attr
import UndergradKB.Statistics.ChiSquared
import UndergradKB.Statistics.Discrete
import UndergradKB.Statistics.Limits
import UndergradKB.Statistics.StudentT

/-!
# Limiting shapes of the chi-square, t and hypergeometric distributions

OpenStax *Introductory Statistics 2e*, remarks in §11.1, §8.2 and §4.5:

* ST-096: for many degrees of freedom the chi-square law is approximately normal (central limit theorem
  applied to the squares of independent standard normals, which have mean `1` and variance `2`);
* ST-076: the Student t density has heavier tails than the standard normal density (their ratio tends to
  infinity);
* ST-044: for a large population the hypergeometric probabilities are approximately binomial.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Filter Topology Asymptotics

/-! ### ST-096: the chi-square law is approximately normal -/

section ChiSquareNormal

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'}

/-- The square of a standard normal variable has mean `1` and variance `2`, and is square integrable. -/
lemma sq_gaussian_moments [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) :
    P[fun ω ↦ Z ω ^ 2] = 1 ∧ Var[fun ω ↦ Z ω ^ 2; P] = 2 ∧ MemLp (fun ω ↦ Z ω ^ 2) 2 P := by
  have h1 := hasLaw_sq_chiSquared_one hZ
  have := isProbabilityMeasure_chiSquared' one_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [h1.integral_eq]
    simpa using integral_id_chiSquared one_pos
  · rw [h1.variance_eq]
    simpa using variance_id_chiSquared one_pos
  · have h2 := integral_pow_gammaMeasure (a := 1 / 2) (r := 1 / 2) (by norm_num) (by norm_num) 2
    have hm : MemLp id 2 (chiSquared 1) :=
      (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (by simpa [chiSquared] using h2.1)
    exact h1.memLp hm

/-- **The chi-square law is approximately normal for many degrees of freedom (ST-096).** Let
`Z₀, Z₁, …` be independent standard normal variables. Then for every `k ≥ 1` the sum `Z₀² + ⋯ + Z_{k-1}²` has
the chi-square law with `k` degrees of freedom, and the standardised sums `(∑_{i<k} Zᵢ² - k)/√(2k)` converge in
distribution to a standard normal variable as `k → ∞`. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem chiSquared_approx_normal [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {Z : ℕ → Ω → ℝ}
    {W : Ω' → ℝ} (hW : HasLaw W (gaussianReal 0 1) P') (hmeas : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) :
    (∀ k : ℕ, 0 < k → HasLaw (fun ω ↦ ∑ i ∈ Finset.range k, Z i ω ^ 2) (chiSquared k) P) ∧
    TendstoInDistribution
      (fun (k : ℕ) ω ↦ (∑ i ∈ Finset.range k, Z i ω ^ 2 - k) / √(2 * k)) atTop W (fun _ ↦ P) P' := by
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · have := hasLaw_sum_sq_chiSquared (s := Finset.range k) (Finset.nonempty_range_iff.2 hk.ne') hmeas
      hind (fun i _ ↦ hZ i)
    simpa using this
  · obtain ⟨hm, hv, hL⟩ := sq_gaussian_moments (hZ 0)
    have hind2 : iIndepFun (fun i ω ↦ Z i ω ^ 2) P :=
      hind.comp (fun _ x ↦ x ^ 2) fun _ ↦ by fun_prop
    have hident : ∀ i, IdentDistrib (fun ω ↦ Z i ω ^ 2) (fun ω ↦ Z 0 ω ^ 2) P P := fun i ↦
      (hasLaw_sq_chiSquared_one (hZ i)).identDistrib (hasLaw_sq_chiSquared_one (hZ 0))
    have h := tendstoInDistribution_standardized (X := fun i ω ↦ Z i ω ^ 2) hW hL
      (by rw [hv]; norm_num) hind2 hident
    convert h using 1
    funext k ω
    simp only [hm, hv, mul_one, div_eq_inv_mul, mul_comm (k : ℝ) 2]

end ChiSquareNormal

/-! ### ST-076: heavy tails of the t density -/

section HeavyTails

/-- **The t density has heavier tails than the normal density (ST-076).** For every `ν > 0` the ratio of the
Student t density with `ν` degrees of freedom to the standard normal density tends to infinity as `t → ∞`. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem tendsto_studentTPDFReal_div_gaussianPDFReal {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun t : ℝ ↦ studentTPDFReal ν t / gaussianPDFReal 0 1 t) atTop atTop := by
  set s : ℝ := (ν + 1) / 2 with hs
  have hs0 : 0 < s := by positivity
  set K : ℝ := 2 * (1 + 1 / ν) with hK
  have hK0 : 0 < K := by positivity
  set c0 : ℝ := Gamma s / (√(ν * π) * Gamma (ν / 2)) with hc0
  have hG1 := Gamma_pos_of_pos hs0
  have hG2 := Gamma_pos_of_pos (by positivity : 0 < ν / 2)
  have hc0pos : 0 < c0 := by positivity
  set D : ℝ := c0 * √(2 * π) * (K ^ s)⁻¹ with hD
  have hDpos : 0 < D := by positivity
  have hy : Tendsto (fun t : ℝ ↦ t ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).atTop_div_const two_pos
  have hf : Tendsto (fun t : ℝ ↦ exp (t ^ 2 / 2) / (t ^ 2 / 2) ^ s) atTop atTop :=
    (tendsto_exp_div_rpow_atTop s).comp hy
  refine tendsto_atTop_mono' atTop ?_ (hf.const_mul_atTop hDpos)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hy0 : 0 < t ^ 2 / 2 := by positivity
  have ha : 0 < 1 + t ^ 2 / ν := by positivity
  have hle : 1 + t ^ 2 / ν ≤ K * (t ^ 2 / 2) := by
    rw [hK]
    have : t ^ 2 / ν = t ^ 2 * (1 / ν) := by ring
    nlinarith
  have hpow : (K * (t ^ 2 / 2)) ^ (-s) ≤ (1 + t ^ 2 / ν) ^ (-s) :=
    rpow_le_rpow_of_nonpos ha hle (by linarith)
  have hgauss : gaussianPDFReal 0 1 t = (√(2 * π))⁻¹ * exp (-t ^ 2 / 2) := by
    simp [gaussianPDFReal]
  rw [neg_div, exp_neg] at hgauss
  have heq : studentTPDFReal ν t / gaussianPDFReal 0 1 t =
      c0 * √(2 * π) * (1 + t ^ 2 / ν) ^ (-s) * exp (t ^ 2 / 2) := by
    have hsq : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
    have hep := exp_pos (t ^ 2 / 2)
    rw [hgauss]
    unfold studentTPDFReal
    rw [← hs, ← hc0]
    field_simp
  rw [heq]
  have hmul : (K * (t ^ 2 / 2)) ^ (-s) = (K ^ s)⁻¹ * ((t ^ 2 / 2) ^ s)⁻¹ := by
    rw [mul_rpow hK0.le hy0.le, rpow_neg hK0.le, rpow_neg hy0.le]
  have hE := exp_pos (t ^ 2 / 2)
  have hsq : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
  calc D * (exp (t ^ 2 / 2) / (t ^ 2 / 2) ^ s)
      = c0 * √(2 * π) * ((K ^ s)⁻¹ * ((t ^ 2 / 2) ^ s)⁻¹) * exp (t ^ 2 / 2) := by
        rw [hD]; field_simp
    _ ≤ c0 * √(2 * π) * (1 + t ^ 2 / ν) ^ (-s) * exp (t ^ 2 / 2) := by
        rw [← hmul]
        gcongr

end HeavyTails

/-! ### ST-044: the binomial approximates the hypergeometric -/

section HyperBinomial

/-- **The binomial approximates the hypergeometric for a large population (ST-044).** Suppose a population
has `A k` successes and `B k` failures, both tending to infinity, with success fraction
`A k / (A k + B k) → p`. Then for a fixed sample size `n` and `x ≤ n`, the hypergeometric probability of `x`
successes tends to the binomial probability `C(n, x) p^x (1 - p)^(n - x)`. -/
@[kb "openstaxintrostats2e" "§4.5, p. 258"]
theorem tendsto_hypergeometricPMF_binomial {A B : ℕ → ℕ} {p : ℝ} (hA : Tendsto A atTop atTop)
    (hB : Tendsto B atTop atTop)
    (hp : Tendsto (fun k ↦ (A k : ℝ) / ((A k : ℝ) + B k)) atTop (𝓝 p)) (n x : ℕ) (hx : x ≤ n) :
    Tendsto (fun k ↦ hypergeometricPMF (A k) (B k) n x) atTop
      (𝓝 ((n.choose x : ℝ) * p ^ x * (1 - p) ^ (n - x))) := by
  have hN : Tendsto (fun k ↦ A k + B k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_add_right _ _) hA
  have e1 := (isEquivalent_choose x).comp_tendsto hA
  have e2 := (isEquivalent_choose (n - x)).comp_tendsto hB
  have e3 := (isEquivalent_choose n).comp_tendsto hN
  have e := (e1.mul e2).div e3
  have hq : Tendsto (fun k ↦ (B k : ℝ) / ((A k : ℝ) + B k)) atTop (𝓝 (1 - p)) := by
    have h1 : Tendsto (fun k ↦ 1 - (A k : ℝ) / ((A k : ℝ) + B k)) atTop (𝓝 (1 - p)) :=
      tendsto_const_nhds.sub hp
    refine h1.congr' ?_
    have hApos := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hA
    filter_upwards [hApos.eventually_gt_atTop 0, (tendsto_natCast_atTop_atTop (R := ℝ)).comp hB
      |>.eventually_gt_atTop 0] with k h1 h2
    simp only [Function.comp] at h1 h2
    field_simp
    ring
  have hfac : (n.factorial : ℝ) / (x.factorial * (n - x).factorial) = n.choose x := by
    have := Nat.choose_mul_factorial_mul_factorial hx
    have h1 : (0 : ℝ) < x.factorial := by exact_mod_cast x.factorial_pos
    have h2 : (0 : ℝ) < (n - x).factorial := by exact_mod_cast (n - x).factorial_pos
    rw [div_eq_iff (by positivity)]
    exact_mod_cast this.symm.trans (by ring)
  have hlim : Tendsto (fun k ↦ (n.choose x : ℝ) * ((A k : ℝ) / ((A k : ℝ) + B k)) ^ x *
      ((B k : ℝ) / ((A k : ℝ) + B k)) ^ (n - x)) atTop (𝓝 ((n.choose x : ℝ) * p ^ x * (1 - p) ^ (n - x))) :=
    ((tendsto_const_nhds.mul (hp.pow x))).mul (hq.pow (n - x))
  have hv : (fun k ↦ (n.choose x : ℝ) * ((A k : ℝ) / ((A k : ℝ) + B k)) ^ x *
      ((B k : ℝ) / ((A k : ℝ) + B k)) ^ (n - x)) =ᶠ[atTop]
      fun k ↦ (((A k : ℝ) ^ x / x.factorial) * ((B k : ℝ) ^ (n - x) / (n - x).factorial)) /
        ((((A k + B k : ℕ) : ℝ) ^ n) / n.factorial) := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).comp hN |>.eventually_gt_atTop 0] with k hk
    simp only [Function.comp] at hk
    push_cast at hk ⊢
    rw [← hfac, div_pow, div_pow]
    have h1 : (0 : ℝ) < x.factorial := by exact_mod_cast x.factorial_pos
    have h2 : (0 : ℝ) < (n - x).factorial := by exact_mod_cast (n - x).factorial_pos
    have h3 : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    have hnx : ((A k : ℝ) + B k) ^ n = ((A k : ℝ) + B k) ^ x * ((A k : ℝ) + B k) ^ (n - x) := by
      rw [← pow_add, Nat.add_sub_cancel' hx]
    rw [hnx]
    field_simp
  have hv' := (IsEquivalent.tendsto_nhds_iff e).2 (hlim.congr' hv)
  refine hv'.congr' ?_
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).comp hN |>.eventually_gt_atTop 0] with k hk
  simp [hypergeometricPMF, Function.comp]

end HyperBinomial

end UndergradKB.Statistics
