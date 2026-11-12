import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import UndergradKB.Statistics.StudentT

/-!
# Limit theorems used by the confidence-interval chapters

OpenStax *Introductory Statistics 2e*, §7.3, §8.2, §8.3, §9.3.

* the standardised Central Limit Theorem (`tendstoInDistribution_standardized`), from Mathlib's version;
* the normal approximation of the binomial count and of the sample proportion of Bernoulli trials;
* the Student t density tends to the standard normal density as the degrees of freedom grow.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Filter Topology

section CLT

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

/-- **Standardised Central Limit Theorem.** For independent identically distributed `Xᵢ` with finite,
nonzero variance `v` and mean `μ`, `(Sₙ - nμ)/√(n v)` converges in distribution to `N(0, 1)`. -/
theorem tendstoInDistribution_standardized [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hY : HasLaw Y (gaussianReal 0 1) P') (hX : MemLp (X 0) 2 P) (hv : Var[X 0; P] ≠ 0)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√(n * Var[X 0; P]))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' := by
  have hvpos : 0 < Var[X 0; P] := lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hv)
  have hY' : HasLaw (fun ω ↦ √Var[X 0; P] * Y ω) (gaussianReal 0 Var[X 0; P].toNNReal) P' := by
    convert gaussianReal_const_mul hY (√Var[X 0; P]) using 2
    · simp
    · ext
      simp [sq_sqrt hvpos.le, hvpos.le]
  have h := (tendstoInDistribution_inv_sqrt_mul_sum_sub hY' hX hindep hident).continuous_comp
    (g := fun x ↦ x / √Var[X 0; P]) (by fun_prop)
  convert h using 1
  · funext n ω
    simp only [Function.comp]
    rw [sqrt_mul (Nat.cast_nonneg n)]
    have : 0 < √Var[X 0; P] := sqrt_pos.2 hvpos
    by_cases hn : n = 0
    · simp [hn]
    · have : 0 < √(n : ℝ) := sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
      field_simp
  · funext ω
    have : 0 < √Var[X 0; P] := sqrt_pos.2 hvpos
    simp only [Function.comp]
    field_simp

/-- Moments of a 0/1 variable with success probability `p`. -/
private lemma bernoulli_moments [IsProbabilityMeasure P] {p : ℝ} (hmeas : Measurable (X 0))
    (h01 : ∀ ω, X 0 ω = 0 ∨ X 0 ω = 1) (hp : P.real {ω | X 0 ω = 1} = p) :
    P[X 0] = p ∧ Var[X 0; P] = p * (1 - p) ∧ MemLp (X 0) 2 P := by
  have hA : MeasurableSet {ω | X 0 ω = 1} := hmeas (measurableSet_singleton 1)
  have hind : X 0 = Set.indicator {ω | X 0 ω = 1} 1 := by
    funext ω
    rcases h01 ω with h | h <;> simp [Set.indicator, h]
  have hmean : P[X 0] = p := by
    rw [hind, integral_indicator_one hA, hp]
  have hL : MemLp (X 0) 2 P :=
    MemLp.of_bound hmeas.aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by rcases h01 ω with h | h <;> simp [h])
  refine ⟨hmean, ?_, hL⟩
  rw [variance_eq_sub hL]
  have : P[X 0 ^ 2] = p := by
    rw [← hmean]
    congr 1
    funext ω
    rcases h01 ω with h | h <;> simp [h]
  rw [this, hmean]
  ring

/-- **Normal approximation of the binomial count (ST-069).** Let `X₀, X₁, …` be independent, identically
distributed 0/1 variables with `P(Xᵢ = 1) = p`, `0 < p < 1` (Bernoulli trials), so `Sₙ = X₀ + ⋯ + X_{n-1}` is
binomial with parameters `n`, `p`. Then `(Sₙ - n p)/√(n p (1 - p))` converges in distribution to `N(0, 1)`. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem tendstoInDistribution_binomial_count [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hY : HasLaw Y (gaussianReal 0 1) P')
    (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hprob : P.real {ω | X 0 ω = 1} = p) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (∑ k ∈ Finset.range n, X k ω - n * p) / √(n * p * (1 - p)))
      atTop Y (fun _ ↦ P) P' := by
  obtain ⟨hm, hv, hL⟩ := bernoulli_moments (P := P) (hmeas 0) (h01 0) hprob
  have hvne : Var[X 0; P] ≠ 0 := by
    rw [hv]
    exact (mul_pos hp0 (by linarith)).ne'
  have h := tendstoInDistribution_standardized hY hL hvne hindep hident
  convert h using 1
  funext n ω
  rw [hm, hv, div_eq_inv_mul, mul_assoc]

/-- **Normal approximation of the sample proportion (ST-078, ST-086).** For Bernoulli trials
`X₀, X₁, …` (independent, identically distributed 0/1 variables with `P(Xᵢ = 1) = p`, `0 < p < 1`) the sample
proportion `p̂ₙ = (X₀ + ⋯ + X_{n-1})/n` satisfies: `√n (p̂ₙ - p)/√(p (1 - p))` converges in distribution to
`N(0, 1)`. -/
@[kb "openstaxintrostats2e" "§8.3, p. 431"]
theorem tendstoInDistribution_sampleProportion [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hY : HasLaw Y (gaussianReal 0 1) P')
    (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hprob : P.real {ω | X 0 ω = 1} = p) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √n * ((∑ k ∈ Finset.range n, X k ω) / n - p) / √(p * (1 - p)))
      atTop Y (fun _ ↦ P) P' := by
  have h := tendstoInDistribution_binomial_count hp0 hp1 hY hmeas h01 hprob hindep hident
  convert h using 1
  funext n ω
  have hq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : 0 < √(n : ℝ) := sqrt_pos.2 hn'
    have h2 : 0 < √(p * (1 - p)) := sqrt_pos.2 hq
    rw [show (n : ℝ) * p * (1 - p) = n * (p * (1 - p)) by ring, sqrt_mul hn'.le]
    have : √(n : ℝ) ^ 2 = n := sq_sqrt hn'.le
    field_simp
    rw [this]

end CLT

section StudentTLimit

/-- Upper half of Wendel's inequality: `Γ(x + 1/2) ≤ √x Γ(x)`, from log-convexity of `Γ`. -/
lemma gamma_half_upper {x : ℝ} (hx : 0 < x) : Gamma (x + 1 / 2) ≤ √x * Gamma x := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1) (a := 1 / 2)
    (b := 1 / 2) hx (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [show 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring, Gamma_add_one hx.ne'] at h
  have hG := Gamma_pos_of_pos hx
  rw [← mul_rpow hG.le (by positivity), ← sqrt_eq_rpow] at h
  have : √(Gamma x * (x * Gamma x)) = √x * Gamma x := by
    rw [show Gamma x * (x * Gamma x) = x * Gamma x ^ 2 by ring, sqrt_mul hx.le, sqrt_sq hG.le]
  linarith

/-- Lower half of Wendel's inequality: `x Γ(x) / √(x + 1/2) ≤ Γ(x + 1/2)`. -/
lemma gamma_half_lower {x : ℝ} (hx : 0 < x) : x / √(x + 1 / 2) * Gamma x ≤ Gamma (x + 1 / 2) := by
  have hx2 : 0 < x + 1 / 2 := by positivity
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + 1 / 2) (t := x + 3 / 2)
    (a := 1 / 2) (b := 1 / 2) hx2 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  rw [show 1 / 2 * (x + 1 / 2) + 1 / 2 * (x + 3 / 2) = x + 1 by ring,
    show x + 3 / 2 = (x + 1 / 2) + 1 by ring, Gamma_add_one hx2.ne',
    Gamma_add_one hx.ne'] at h
  have hG := Gamma_pos_of_pos hx2
  rw [← mul_rpow hG.le (by positivity), ← sqrt_eq_rpow] at h
  have : √(Gamma (x + 1 / 2) * ((x + 1 / 2) * Gamma (x + 1 / 2))) =
      √(x + 1 / 2) * Gamma (x + 1 / 2) := by
    rw [show Gamma (x + 1 / 2) * ((x + 1 / 2) * Gamma (x + 1 / 2)) =
      (x + 1 / 2) * Gamma (x + 1 / 2) ^ 2 by ring, sqrt_mul hx2.le, sqrt_sq hG.le]
  have hs : 0 < √(x + 1 / 2) := sqrt_pos.2 hx2
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  linarith

/-- The Gamma ratio `Γ(x + 1/2) / (Γ(x) √x)` tends to `1` as `x → ∞`. -/
lemma tendsto_gamma_half_ratio :
    Tendsto (fun x : ℝ ↦ Gamma (x + 1 / 2) / (Gamma x * √x)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun x : ℝ ↦ √((1 + (1 / 2) / x)⁻¹)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun x : ℝ ↦ (1 + (1 / 2) / x)⁻¹) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := (1 / 2 : ℝ))).div_atTop tendsto_id)).inv₀ (by norm_num)
      simpa using this
    have h2 := (continuous_sqrt.tendsto 1).comp h1
    rwa [sqrt_one] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hG := Gamma_pos_of_pos hx
    have hx2 : 0 < x + 1 / 2 := by positivity
    have hs : 0 < √(x + 1 / 2) := sqrt_pos.2 hx2
    have hsx : 0 < √x := sqrt_pos.2 hx
    rw [le_div_iff₀ (by positivity)]
    have e : √((1 + (1 / 2) / x)⁻¹) = √x / √(x + 1 / 2) := by
      rw [← sqrt_div hx.le]
      congr 1
      field_simp
    have h := gamma_half_lower hx
    have hxx : √x * √x = x := mul_self_sqrt hx.le
    calc _ = x / √(x + 1 / 2) * Gamma x := by
          rw [e]
          field_simp
          exact sq_sqrt hx.le
      _ ≤ _ := h
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hG := Gamma_pos_of_pos hx
    have hsx : 0 < √x := sqrt_pos.2 hx
    rw [div_le_one (by positivity)]
    linarith [gamma_half_upper hx]

/-- The factor `(1 + t²/ν)^(-(ν+1)/2)` tends to `e^(-t²/2)`. -/
lemma tendsto_studentT_factor (t : ℝ) :
    Tendsto (fun ν : ℝ ↦ (1 + t ^ 2 / ν) ^ (-((ν + 1) / 2))) atTop (𝓝 (exp (-t ^ 2 / 2))) := by
  have hb : Tendsto (fun ν : ℝ ↦ 1 + t ^ 2 / ν) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := t ^ 2)).div_atTop tendsto_id)
    simpa using this
  have h1 := (tendsto_one_add_div_rpow_exp (t ^ 2)).rpow_const
    (p := -(1 / 2)) (Or.inl (exp_pos _).ne')
  have h2 := hb.rpow_const (p := -(1 / 2)) (Or.inl one_ne_zero)
  have h := h1.mul h2
  rw [one_rpow, mul_one, ← exp_mul] at h
  have e : t ^ 2 * -(1 / 2) = -t ^ 2 / 2 := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν
  have hpos : 0 < 1 + t ^ 2 / ν := by positivity
  rw [← rpow_mul hpos.le, ← rpow_add hpos]
  congr 1
  ring

/-- **The t density tends to the standard normal density (ST-076).** For each fixed `t`, as the degrees of
freedom `ν → ∞`, `f_ν(t)` tends to the standard normal density at `t`. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem tendsto_studentTPDFReal_gaussianPDFReal (t : ℝ) :
    Tendsto (fun ν : ℝ ↦ studentTPDFReal ν t) atTop (𝓝 (gaussianPDFReal 0 1 t)) := by
  have hr : Tendsto (fun ν : ℝ ↦ Gamma (ν / 2 + 1 / 2) / (Gamma (ν / 2) * √(ν / 2))) atTop (𝓝 1) :=
    tendsto_gamma_half_ratio.comp (tendsto_id.atTop_div_const two_pos)
  have h := (hr.div_const (√(2 * π))).mul (tendsto_studentT_factor t)
  have e : 1 / √(2 * π) * exp (-t ^ 2 / 2) = gaussianPDFReal 0 1 t := by
    simp [gaussianPDFReal]
  rw [one_div] at h
  rw [← e]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ν hν
  have hG := Gamma_pos_of_pos (by positivity : 0 < ν / 2)
  have h2 : √(ν * π) = √(2 * π) * √(ν / 2) := by
    rw [← sqrt_mul (by positivity)]
    congr 1
    ring
  have h3 : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
  have h4 : 0 < √(ν / 2) := sqrt_pos.2 (by positivity)
  unfold studentTPDFReal
  rw [h2, show (ν + 1) / 2 = ν / 2 + 1 / 2 by ring]
  field_simp

end StudentTLimit

end UndergradKB.Statistics
