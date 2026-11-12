import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Roots
import UndergradKB.Common.Attr

/-!
# Moment and ordinary generating functions; independence criteria (Grinstead–Snell, chapters 4 and 10)
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace UndergradKB.Probability

section Mgf

/-- Grinstead–Snell Example 10.15 (PR-105). The uniform law on `[0,1]` has moment generating function
`(e^t - 1)/t` for `t ≠ 0`. -/
@[kb "grinsteadsnell2006" "Example 10.15, p. 402"]
theorem mgf_uniform_unit {t : ℝ} (ht : t ≠ 0) :
    mgf id (volume.restrict (Icc (0 : ℝ) 1)) t = (Real.exp t - 1) / t := by
  unfold mgf
  simp only [id]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) ht, integral_exp]
  simp
  field_simp

/-- Grinstead–Snell Example 10.16 (PR-105). The exponential law of rate `r` has moment generating
function `r/(r - t)` for `t < r`. -/
@[kb "grinsteadsnell2006" "Example 10.16, p. 403"]
theorem mgf_exponential {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) := by
  unfold mgf expMeasure gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 r)
    (measurable_gammaPDFReal 1 r).ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hnn : ∀ x, ((gammaPDF 1 r x).toReal) = gammaPDFReal 1 r x := fun x => by
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr x)]
  simp_rw [hnn, smul_eq_mul, id]
  have hzero : ∀ x ∈ (Ici (0 : ℝ))ᶜ, gammaPDFReal 1 r x * Real.exp (t * x) = 0 := fun x hx => by
    simp only [mem_compl_iff, mem_Ici, not_le] at hx
    simp [gammaPDFReal, not_le.2 hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Ici_eq_integral_Ioi]
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), gammaPDFReal 1 r x * Real.exp (t * x) =
      r * Real.exp ((t - r) * x) := fun x hx => by
    have : (0 : ℝ) ≤ x := le_of_lt hx
    simp only [gammaPDFReal, if_pos this]
    simp [Real.Gamma_one, ← Real.exp_add]
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_exp_mul_Ioi (by linarith)]
  have : (t - r) ≠ 0 := by linarith
  simp
  field_simp
  ring

/-- Grinstead–Snell Example 10.17 (PR-105). A normal variable with mean `μ` and variance `v` has
moment generating function `exp (μ t + v t² / 2)`. -/
@[kb "grinsteadsnell2006" "Example 10.17, p. 403"]
theorem mgf_normal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ v) P) (t : ℝ) :
    mgf X P t = Real.exp (μ * t + v * t ^ 2 / 2) :=
  mgf_gaussianReal hX t

/-- Grinstead–Snell Example 10.1 (PR-105). If `X` is uniform on `{1, …, n}` (`n ≥ 1`), its moment
generating function is `(e^t + e^{2t} + ... + e^{nt}) / n`. -/
@[kb "grinsteadsnell2006" "Example 10.1, p. 375"]
theorem mgf_uniform_discrete {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {n : ℕ} (hX : HasLaw X ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.Icc 1 n, Measure.dirac (k : ℝ)) P) (t : ℝ) :
    mgf X P t = (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, Real.exp (t * k) := by
  rw [← mgf_id_map hX.aemeasurable, hX.map_eq]
  unfold mgf
  rw [integral_smul_measure, integral_finsetSum_measure (fun k _ => integrable_dirac
    enorm_lt_top)]
  simp [ENNReal.toReal_inv]

end Mgf

section OrdinaryGF

/-- Grinstead–Snell Theorem 10.1 (PR-103). Two random variables with values in `{0, …, n}` whose
ordinary generating functions `∑ P(X = j) tʲ` agree on the interval `[0,1]` (indeed on any infinite set)
have the same distribution. -/
@[kb "grinsteadsnell2006" "Theorem 10.1, p. 376"]
theorem eq_of_genFun_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : Ω → ℕ} {Y : Ω' → ℕ}
    {n : ℕ} (hXm : Measurable X) (hYm : Measurable Y) (hX : ∀ ω, X ω ≤ n) (hY : ∀ ω, Y ω ≤ n)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∑ j ∈ Finset.range (n + 1), P.real {ω | X ω = j} * t ^ j =
      ∑ j ∈ Finset.range (n + 1), P'.real {ω | Y ω = j} * t ^ j) :
    P.map X = P'.map Y := by
  set f : Polynomial ℝ := ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (P.real {ω | X ω = j} - P'.real {ω | Y ω = j}) * Polynomial.X ^ j with hf
  have hroot : ∀ t ∈ Icc (0 : ℝ) 1, f.IsRoot t := by
    intro t ht
    have := h t ht
    simp only [Polynomial.IsRoot, hf, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, sub_mul,
      Finset.sum_sub_distrib]
    linarith
  have hzero : f = 0 := Polynomial.eq_zero_of_infinite_isRoot f
    ((Set.Icc_infinite zero_lt_one).mono hroot)
  have hcoef : ∀ j ≤ n, P.real {ω | X ω = j} = P'.real {ω | Y ω = j} := by
    intro j hj
    have := congrArg (fun q => Polynomial.coeff q j) hzero
    simp only [hf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simp only [ite_true] at this
      linarith
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hj'
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) hj'
  refine Measure.ext_of_singleton fun j => ?_
  rw [Measure.map_apply hXm (measurableSet_singleton j),
    Measure.map_apply hYm (measurableSet_singleton j)]
  by_cases hj : j ≤ n
  · have := hcoef j hj
    simp only [measureReal_def] at this
    have h1 : (P (X ⁻¹' {j})) ≠ ⊤ := measure_ne_top _ _
    have h2 : (P' (Y ⁻¹' {j})) ≠ ⊤ := measure_ne_top _ _
    exact (ENNReal.toReal_eq_toReal_iff' h1 h2).1 this
  · have e1 : X ⁻¹' {j} = ∅ := by
      ext ω; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hω; exact hj (hω ▸ hX ω)
    have e2 : Y ⁻¹' {j} = ∅ := by
      ext ω; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hω; exact hj (hω ▸ hY ω)
    rw [e1, e2]
    simp

end OrdinaryGF

section Independence

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Theorem 4.2 (PR-047), two variables. Random variables `X`, `Y` whose joint law has
a density are independent iff the joint density is (almost everywhere) the product of the marginal
densities. -/
@[kb "grinsteadsnell2006" "Theorem 4.2, p. 173"]
theorem indepFun_iff_joint_density {X Y : Ω → ℝ}
    [HasPDF (fun ω => (X ω, Y ω)) P (volume.prod volume)] :
    IndepFun X Y P ↔ pdf (fun ω => (X ω, Y ω)) P (volume.prod volume) =ᵐ[volume.prod volume]
      fun z => pdf X P volume z.1 * pdf Y P volume z.2 :=
  pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf

/-- Grinstead–Snell Definition 4.7 (PR-046). Two real random variables are independent iff
`P(X ≤ x, Y ≤ y) = P(X ≤ x) P(Y ≤ y)` for all `x`, `y`. -/
@[kb "grinsteadsnell2006" "Definition 4.7, p. 173"]
theorem indepFun_iff_cdf_mul {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    IndepFun X Y P ↔ ∀ x y : ℝ, P ({ω | X ω ≤ x} ∩ {ω | Y ω ≤ y}) =
      P {ω | X ω ≤ x} * P {ω | Y ω ≤ y} := by
  constructor
  · intro h x y
    exact h.measure_inter_preimage_eq_mul (Iic x) (Iic y) measurableSet_Iic measurableSet_Iic
  · intro h
    have hgen : ∀ Z : Ω → ℝ, MeasurableSpace.comap Z (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.generateFrom ((fun s => Z ⁻¹' s) '' range (Iic : ℝ → Set ℝ)) := by
      intro Z
      rw [← MeasurableSpace.comap_generateFrom]
      congr 1
      rw [← borel_eq_generateFrom_Iic ℝ]
      exact BorelSpace.measurable_eq
    have hpi : ∀ Z : Ω → ℝ, IsPiSystem ((fun s => Z ⁻¹' s) '' range (Iic : ℝ → Set ℝ)) := fun Z =>
      isPiSystem_Iic.comap Z
    refine IndepSets.indep hX.comap_le hY.comap_le (hpi X) (hpi Y) (hgen X) (hgen Y) ?_
    rw [IndepSets_iff]
    rintro _ _ ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact h x y

end Independence

section Bernoulli

open unitInterval

/-- Grinstead–Snell Definition 3.5 (PR-027). In a Bernoulli trials process (`n` independent trials,
each a success with probability `p`), the number of successes has the binomial law `Bin(n, p)`. -/
@[kb "grinsteadsnell2006" "Definition 3.5, p. 104"]
theorem hasLaw_sum_bernoulli {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {p : unitInterval} {X : Fin n → Ω → ℝ}
    (hlaw : ∀ i, HasLaw (X i) Ber(1, 0, p) P) (hind : iIndepFun X P) :
    HasLaw (fun ω => ∑ i, X i ω) Bin(ℝ, n, p) P := by
  have hmeas : ∀ i, AEMeasurable (X i) P := fun i => (hlaw i).aemeasurable
  refine ⟨Finset.aemeasurable_fun_sum _ fun i _ => hmeas i, ?_⟩
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [hind.charFun_map_fun_sum_eq_prod hmeas, Finset.prod_apply]
  have hber : ∀ i, charFun (P.map (X i)) t = (p : ℝ) * Complex.exp (t * Complex.I) + (1 - (p : ℝ)) := by
    intro i
    rw [(hlaw i).map_eq, charFun_apply_real, integral_bernoulliMeasure]
    simp [Complex.real_smul]
  simp_rw [hber]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, charFun_apply_real,
    integral_map_cast_binomial]
  have : Finset.Iic n = Finset.range (n + 1) := by
    ext k; simp [Nat.lt_succ_iff]
  rw [this, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.real_smul]
  have hk : Complex.exp (t * (k : ℝ) * Complex.I) = Complex.exp (t * Complex.I) ^ k := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, hk]
  push_cast
  ring

end Bernoulli

end UndergradKB.Probability
