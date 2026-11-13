import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.StrongLaw
import UndergradKB.Common.Attr
import UndergradKB.Statistics.TwoProportions

/-!
# Two independent samples of arbitrary sizes

OpenStax *Introductory Statistics 2e*, §10.2 and §10.3 (ST-092, ST-093).

Wave 2 proved the normal limit of the difference of two sample means (proportions) when the two
sample sizes grow in a fixed ratio. Here the sizes `n_A k`, `n_B k` are arbitrary sequences tending
to infinity. The proof uses characteristic functions directly: the standardised difference is
`∑_{i < n_A} α X'ᵢ - ∑_{j < n_B} β Y'ⱼ` with standardised summands and weights satisfying
`n_A α² + n_B β² = 1`, so its characteristic function is `φ_A(α t)^{n_A} φ_B(-β t)^{n_B}`, and
`φ(a t)^n - exp(-n a² t²/2) → 0` whenever `n a² ≤ 1` and `n → ∞` (Taylor expansion of `φ` to order
two, `taylor_charFun_two`, and `‖zⁿ - wⁿ‖ ≤ n ‖z - w‖` on the unit disc). Lévy's continuity theorem
(`TendstoInDistribution.of_tendsto_charFun`) finishes the proof.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Filter Topology Complex

section Triangular

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

lemma norm_pow_sub_pow_le_of_norm_le_one {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ n * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : z ^ (n + 1) - w ^ (n + 1) = z * (z ^ n - w ^ n) + (z - w) * w ^ n := by ring
    rw [h]
    calc _ ≤ ‖z * (z ^ n - w ^ n)‖ + ‖(z - w) * w ^ n‖ := norm_add_le _ _
      _ = ‖z‖ * ‖z ^ n - w ^ n‖ + ‖z - w‖ * ‖w‖ ^ n := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ 1 * (n * ‖z - w‖) + ‖z - w‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := by push_cast; ring

lemma norm_cexp_neg_sq_le_one (x : ℝ) : ‖cexp (-(x : ℂ) ^ 2 / 2)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have : (-(x : ℂ) ^ 2 / 2).re = -x ^ 2 / 2 := by
    rw [show (-(x : ℂ) ^ 2 / 2) = ((-x ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [this, Real.exp_le_one_iff]
  have := sq_nonneg x
  linarith

/-- Second-order agreement of a standardised characteristic function with the Gaussian one. -/
lemma charFun_sub_gauss_isLittleO [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P)
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) :
    (fun s : ℝ ↦ charFun (P.map X) s - cexp (-(s : ℂ) ^ 2 / 2)) =o[𝓝 0] fun s ↦ s ^ 2 := by
  have hG0 : (gaussianReal 0 1)[id] = 0 := by simp [integral_id_gaussianReal]
  have hG1 : (gaussianReal 0 1)[id ^ 2] = 1 := by
    have h := variance_of_integral_eq_zero (μ := gaussianReal 0 1) aemeasurable_id hG0
    rw [variance_id_gaussianReal] at h
    simpa using h.symm
  have hG := taylor_charFun_two (P := gaussianReal 0 1) aemeasurable_id hG0 hG1
  have := (taylor_charFun_two hX h0 h1).sub hG
  convert this using 2 with s
  rw [Measure.map_id, charFun_gaussianReal]
  push_cast
  ring_nf

/-- Triangular-array step: if `n_k → ∞` and `n_k a_k² ≤ 1`, then
`φ(a_k t)^{n_k} - exp(-n_k a_k² t²/2) → 0` for a standardised characteristic function `φ`. -/
lemma tendsto_charFun_pow_sub_gauss [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P)
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) {n : ℕ → ℕ} {a : ℕ → ℝ} (hn : Tendsto n atTop atTop)
    (hna : ∀ k, (n k : ℝ) * a k ^ 2 ≤ 1) (t : ℝ) :
    Tendsto (fun k ↦ charFun (P.map X) (a k * t) ^ n k -
      cexp (-(((n k : ℝ) * a k ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) atTop (𝓝 0) := by
  -- `a k → 0`
  have ha2 : Tendsto (fun k ↦ a k ^ 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun k ↦ ((n k : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)
    refine squeeze_zero' (Eventually.of_forall fun k ↦ sq_nonneg _) ?_ hinv
    filter_upwards [hn.eventually_ge_atTop 1] with k hk
    have hk' : (0 : ℝ) < n k := by exact_mod_cast hk
    rw [← one_div, le_div_iff₀ hk']
    linarith [hna k]
  have ha : Tendsto (fun k ↦ a k * t) atTop (𝓝 0) := by
    have : Tendsto (fun k ↦ √(a k ^ 2)) atTop (𝓝 0) := by
      have h := (continuous_sqrt.tendsto 0).comp ha2
      rw [Real.sqrt_zero] at h
      exact h
    have h' : Tendsto (fun k ↦ |a k|) atTop (𝓝 0) := by simpa [Real.sqrt_sq_eq_abs] using this
    have : Tendsto a atTop (𝓝 0) := (tendsto_zero_iff_abs_tendsto_zero _).2 h'
    simpa using this.mul_const t
  have ho := (charFun_sub_gauss_isLittleO hX h0 h1).comp_tendsto ha
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) (g := fun k ↦
    (n k : ℝ) * ‖charFun (P.map X) (a k * t) - cexp (-((a k * t : ℝ) : ℂ) ^ 2 / 2)‖) ?_
  · have hw : cexp (-(((n k : ℝ) * a k ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) =
        cexp (-((a k * t : ℝ) : ℂ) ^ 2 / 2) ^ n k := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hw]
    exact norm_pow_sub_pow_le_of_norm_le_one (norm_charFun_le_one _) (norm_cexp_neg_sq_le_one _) _
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (t ^ 2 + 1) := by positivity
    filter_upwards [ho.def hε'] with k hk
    simp only [Function.comp_apply, Real.norm_eq_abs, dist_zero_right] at hk ⊢
    have hn0 : (0 : ℝ) ≤ n k := by positivity
    rw [abs_of_nonneg (by positivity)]
    calc (n k : ℝ) * ‖charFun (P.map X) (a k * t) - cexp (-((a k * t : ℝ) : ℂ) ^ 2 / 2)‖
        ≤ n k * (ε / (t ^ 2 + 1) * |(a k * t) ^ 2|) := by gcongr
      _ = ε / (t ^ 2 + 1) * t ^ 2 * (n k * a k ^ 2) := by
          rw [abs_of_nonneg (sq_nonneg _)]; ring
      _ ≤ ε / (t ^ 2 + 1) * t ^ 2 * 1 := by gcongr; exact hna k
      _ < ε := by
          rw [mul_one, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith

end Triangular

section TwoSample

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'}

lemma norm_cexp_neg_mul_sq_le_one {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    ‖cexp (-(c : ℂ) * (t : ℂ) ^ 2 / 2)‖ ≤ 1 := by
  have h := norm_cexp_neg_sq_le_one (√c * t)
  convert h using 3
  push_cast
  rw [mul_pow, ← Complex.ofReal_pow (√c), Real.sq_sqrt hc]
  ring

/-- Standardised moments of a variable with mean `μ` and standard deviation `σ`. -/
lemma standardized_moments [IsProbabilityMeasure P] {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hL : MemLp X 2 P) (hμ : P[X] = μ) (hv : Var[X; P] = σ ^ 2) :
    P[fun ω ↦ (X ω - μ) / σ] = 0 ∧ P[(fun ω ↦ (X ω - μ) / σ) ^ 2] = 1 := by
  have hint := hL.integrable one_le_two
  constructor
  · simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, integral_sub hint (integrable_const _), hμ]
    simp
  · have hvar := variance_eq_integral hL.aestronglyMeasurable.aemeasurable
    rw [hμ, hv] at hvar
    simp only [Pi.pow_apply, div_pow]
    rw [integral_div, ← hvar]
    have : σ ^ 2 ≠ 0 := by positivity
    field_simp

/-- Weight bound: `n (σ / (n s))² ≤ 1` when `s² = σ²/n + τ`, `τ ≥ 0`. -/
lemma weight_sq_le_one {σ s τ : ℝ} {n : ℕ} (hσ : 0 < σ) (hτ : 0 ≤ τ)
    (hs : s ^ 2 = σ ^ 2 / n + τ) : (n : ℝ) * (σ / (n * s)) ^ 2 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    have hs2 : 0 < s ^ 2 := by rw [hs]; positivity
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs2
    rw [div_pow, mul_pow, ← mul_div_assoc, div_le_one (by positivity)]
    have : (n : ℝ) * σ ^ 2 = n ^ 2 * (σ ^ 2 / n) := by field_simp
    rw [this, hs]
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hτ]

lemma weight_sq_sum {σ σ' s : ℝ} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hσ : 0 < σ) (hσ' : 0 < σ')
    (hs : s ^ 2 = σ ^ 2 / n + σ' ^ 2 / m) :
    (n : ℝ) * (σ / (n * s)) ^ 2 + (m : ℝ) * (σ' / (m * s)) ^ 2 = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs2 : 0 < s ^ 2 := by rw [hs]; positivity
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs2
  rw [div_pow, div_pow, mul_pow, mul_pow]
  field_simp
  rw [hs]
  field_simp

/-- **Two independent samples, arbitrary sizes (ST-092).** Let `X₀, X₁, …` (population A, mean `μ_A`,
standard deviation `σ_A > 0`) and `Y₀, Y₁, …` (population B, mean `μ_B`, standard deviation
`σ_B > 0`) be independent (`Sum.elim X Y` is an independent family), identically distributed within
each population, with finite variance. Let the sample sizes `n_A k`, `n_B k` both tend to infinity,
in any manner. Then
`((x̄_A - x̄_B) - (μ_A - μ_B)) / √(σ_A²/n_A + σ_B²/n_B)` converges in distribution to `N(0, 1)`:
for large samples the difference of the sample means is approximately normal with mean `μ_A - μ_B`
and standard deviation `√(σ_A²/n_A + σ_B²/n_B)`, whatever the populations. -/
@[kb "openstaxintrostats2e" "§10.2, p. 531"]
theorem tendstoInDistribution_two_sample_means [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {μA μB σA σB : ℝ} (hσA : 0 < σA) (hσB : 0 < σB)
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hLX : MemLp (X 0) 2 P) (hLY : MemLp (Y 0) 2 P)
    (hμA : P[X 0] = μA) (hμB : P[Y 0] = μB) (hvA : Var[X 0; P] = σA ^ 2)
    (hvB : Var[Y 0; P] = σB ^ 2) (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {nA nB : ℕ → ℕ} (hnA : Tendsto nA atTop atTop) (hnB : Tendsto nB atTop atTop) :
    TendstoInDistribution
      (fun k ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
          (∑ j ∈ Finset.range (nB k), Y j ω) / nB k - (μA - μB)) /
          √(σA ^ 2 / nA k + σB ^ 2 / nB k))
      atTop Z (fun _ ↦ P) P' := by
  classical
  have hmX : ∀ i, AEMeasurable (X i) P := fun i ↦ (hidentX i).aemeasurable_fst
  have hmY : ∀ i, AEMeasurable (Y i) P := fun i ↦ (hidentY i).aemeasurable_fst
  set s : ℕ → ℝ := fun k ↦ √(σA ^ 2 / nA k + σB ^ 2 / nB k) with hs
  have hs2 : ∀ k, s k ^ 2 = σA ^ 2 / nA k + σB ^ 2 / nB k := fun k ↦ Real.sq_sqrt (by positivity)
  set α : ℕ → ℝ := fun k ↦ σA / (nA k * s k) with hα
  set β : ℕ → ℝ := fun k ↦ σB / (nB k * s k) with hβ
  -- standardised family
  set f : ℕ ⊕ ℕ → ℝ → ℝ := Sum.elim (fun _ x ↦ (x - μA) / σA) (fun _ x ↦ (x - μB) / σB) with hf
  have hfm : ∀ i, Measurable (f i) := by
    intro i; rcases i with i | i <;> simp only [hf, Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  set c : ℕ → ℕ ⊕ ℕ → ℝ := fun k ↦ Sum.elim (fun _ ↦ α k) (fun _ ↦ -β k) with hc
  set V : ℕ → ℕ ⊕ ℕ → Ω → ℝ := fun k i ω ↦ c k i * f i (Sum.elim X Y i ω) with hV
  have hmW : ∀ i, AEMeasurable (Sum.elim X Y i) P := by
    intro i; rcases i with i | i
    · exact hmX i
    · exact hmY i
  have hVind : ∀ k, iIndepFun (V k) P := fun k ↦
    (hindep.comp f hfm).comp (fun i x ↦ c k i * x) (fun _ ↦ measurable_const_mul _)
  have hVm : ∀ k i, AEMeasurable (V k i) P := fun k i ↦
    ((hfm i).comp_aemeasurable (hmW i)).const_mul _
  -- standardised moments
  obtain ⟨hA0, hA1⟩ := standardized_moments hσA hLX hμA hvA
  obtain ⟨hB0, hB1⟩ := standardized_moments hσB hLY hμB hvB
  have hmA : AEMeasurable (fun ω ↦ (X 0 ω - μA) / σA) P := by
    have := hmX 0; fun_prop
  have hmB : AEMeasurable (fun ω ↦ (Y 0 ω - μB) / σB) P := by
    have := hmY 0; fun_prop
  set φA := charFun (P.map (fun ω ↦ (X 0 ω - μA) / σA)) with hφA
  set φB := charFun (P.map (fun ω ↦ (Y 0 ω - μB) / σB)) with hφB
  -- the statistic as a weighted sum
  have hsum : ∀ᶠ k in atTop, ∀ ω,
      ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
          (∑ j ∈ Finset.range (nB k), Y j ω) / nB k - (μA - μB)) / s k =
        ∑ i ∈ (Finset.range (nA k)).disjSum (Finset.range (nB k)), V k i ω := by
    filter_upwards [hnA.eventually_ge_atTop 1, hnB.eventually_ge_atTop 1] with k hka hkb ω
    have ha' : (0 : ℝ) < nA k := by exact_mod_cast hka
    have hb' : (0 : ℝ) < nB k := by exact_mod_cast hkb
    have hsk : 0 < s k := Real.sqrt_pos.2 (by positivity)
    rw [Finset.sum_disjSum]
    simp only [hV, hc, hf, hα, hβ, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_div,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_range, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
    generalize ∑ i ∈ Finset.range (nA k), X i ω = SA
    generalize ∑ j ∈ Finset.range (nB k), Y j ω = SB
    field_simp
    ring
  -- characteristic function of the weighted sum
  have hchar : ∀ k t, charFun (P.map (fun ω ↦
      ∑ i ∈ (Finset.range (nA k)).disjSum (Finset.range (nB k)), V k i ω)) t =
      φA (α k * t) ^ nA k * φB (-β k * t) ^ nB k := by
    intro k t
    rw [iIndepFun.charFun_map_fun_finsetSum_eq_prod (fun i _ ↦ hVm k i) ((hVind k).restrict _),
      Finset.prod_disjSum]
    have h1 : ∀ i ∈ Finset.range (nA k), charFun (P.map (V k (Sum.inl i))) t = φA (α k * t) := by
      intro i _
      simp only [hV, hc, hf, Sum.elim_inl]
      rw [charFun_map_mul_comp (f := fun ω ↦ (X i ω - μA) / σA) (by have := hmX i; fun_prop)]
      have : P.map (fun ω ↦ (X i ω - μA) / σA) = P.map (fun ω ↦ (X 0 ω - μA) / σA) :=
        ((hidentX i).comp (show Measurable (fun x : ℝ ↦ (x - μA) / σA) by fun_prop)).map_eq
      rw [this]
    have h2 : ∀ i ∈ Finset.range (nB k), charFun (P.map (V k (Sum.inr i))) t = φB (-β k * t) := by
      intro i _
      simp only [hV, hc, hf, Sum.elim_inr]
      rw [charFun_map_mul_comp (f := fun ω ↦ (Y i ω - μB) / σB) (by have := hmY i; fun_prop)]
      have : P.map (fun ω ↦ (Y i ω - μB) / σB) = P.map (fun ω ↦ (Y 0 ω - μB) / σB) :=
        ((hidentY i).comp (show Measurable (fun x : ℝ ↦ (x - μB) / σB) by fun_prop)).map_eq
      rw [this]
    simp only [Pi.mul_apply, Finset.prod_apply]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_const, Finset.prod_const,
      Finset.card_range, Finset.card_range]
  refine TendstoInDistribution.of_tendsto_charFun (fun k ↦ ?_) hZ.aemeasurable (fun t ↦ ?_)
  · exact ((((Finset.aemeasurable_fun_sum _ fun i _ ↦ hmX i).div_const _).sub
      ((Finset.aemeasurable_fun_sum _ fun i _ ↦ hmY i).div_const _)).sub_const _).div_const _
  have hG : charFun (P'.map Z) t = cexp (-((1 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    rw [hZ.map_eq, charFun_gaussianReal]
    push_cast
    ring_nf
  rw [hG]
  have h1 := tendsto_charFun_pow_sub_gauss hmA hA0 hA1 hnA (a := α)
    (fun k ↦ weight_sq_le_one hσA (by positivity) (hs2 k)) t
  have h2 := tendsto_charFun_pow_sub_gauss hmB hB0 hB1 hnB (a := fun k ↦ -β k)
    (fun k ↦ by
      rw [neg_sq]
      exact weight_sq_le_one hσB (τ := σA ^ 2 / nA k) (by positivity) (by rw [hs2]; ring)) t
  set u : ℕ → ℂ := fun k ↦ φA (α k * t) ^ nA k with hu
  set v : ℕ → ℂ := fun k ↦ φB (-β k * t) ^ nB k with hv
  set p : ℕ → ℂ := fun k ↦ cexp (-(((nA k : ℝ) * α k ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) with hp
  set q : ℕ → ℂ := fun k ↦ cexp (-(((nB k : ℝ) * (-β k) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) with hq
  have hpq : ∀ᶠ k in atTop, p k * q k = cexp (-((1 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    filter_upwards [hnA.eventually_ge_atTop 1, hnB.eventually_ge_atTop 1] with k hka hkb
    have h : (nA k : ℝ) * α k ^ 2 + nB k * β k ^ 2 = 1 := weight_sq_sum hka hkb hσA hσB (hs2 k)
    simp only [hp, hq, ← Complex.exp_add]
    congr 1
    rw [neg_sq, ← h]
    push_cast
    ring
  have hlim : Tendsto (fun k ↦ u k * v k) atTop
      (𝓝 (cexp (-((1 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
      (g := fun k ↦ ‖u k - p k‖ + ‖v k - q k‖) ?_
    · filter_upwards [hpq] with k hk
      rw [← hk]
      have hvle : ‖v k‖ ≤ 1 := by
        simp only [hv, norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
      have hple : ‖p k‖ ≤ 1 := norm_cexp_neg_mul_sq_le_one (by positivity) t
      have : u k * v k - p k * q k = (u k - p k) * v k + p k * (v k - q k) := by ring
      rw [this]
      calc _ ≤ ‖(u k - p k) * v k‖ + ‖p k * (v k - q k)‖ := norm_add_le _ _
        _ = ‖u k - p k‖ * ‖v k‖ + ‖p k‖ * ‖v k - q k‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖u k - p k‖ * 1 + 1 * ‖v k - q k‖ := by gcongr
        _ = _ := by ring
    · have h3 := h1.norm.add h2.norm
      rw [norm_zero, add_zero] at h3
      exact h3
  refine hlim.congr' ?_
  filter_upwards [hsum] with k hk
  have hT : (fun ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
      (∑ j ∈ Finset.range (nB k), Y j ω) / nB k - (μA - μB)) / s k) =
      fun ω ↦ ∑ i ∈ (Finset.range (nA k)).disjSum (Finset.range (nB k)), V k i ω := funext hk
  rw [hT, hchar]

/-- **Two proportions, arbitrary sizes (ST-093).** For independent 0/1 samples from populations A and B
(success probabilities `0 < p_A, p_B < 1`) with sample sizes `n_A k`, `n_B k` tending to infinity in any
manner, `((p'_A - p'_B) - (p_A - p_B)) / √(p_A q_A/n_A + p_B q_B/n_B)` tends to `N(0, 1)` in
distribution. This removes the fixed size ratio of `tendstoInDistribution_two_proportions`. -/
@[kb "openstaxintrostats2e" "§10.3, p. 534"]
theorem tendstoInDistribution_two_proportions_sizes [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {pA pB : ℝ} (hA0 : 0 < pA)
    (hA1 : pA < 1) (hB0 : 0 < pB) (hB1 : pB < 1) (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hmX : ∀ i, Measurable (X i)) (hmY : ∀ i, Measurable (Y i))
    (h01X : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (h01Y : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hprobA : P.real {ω | X 0 ω = 1} = pA) (hprobB : P.real {ω | Y 0 ω = 1} = pB)
    (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {nA nB : ℕ → ℕ} (hnA : Tendsto nA atTop atTop) (hnB : Tendsto nB atTop atTop) :
    TendstoInDistribution
      (fun k ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
          (∑ j ∈ Finset.range (nB k), Y j ω) / nB k - (pA - pB)) /
          √(pA * (1 - pA) / nA k + pB * (1 - pB) / nB k))
      atTop Z (fun _ ↦ P) P' := by
  obtain ⟨hmA, hvA, hLA⟩ := bern_moments (P := P) (hmX 0) (h01X 0) hprobA
  obtain ⟨hmB, hvB, hLB⟩ := bern_moments (P := P) (hmY 0) (h01Y 0) hprobB
  have hqA : 0 < pA * (1 - pA) := mul_pos hA0 (by linarith)
  have hqB : 0 < pB * (1 - pB) := mul_pos hB0 (by linarith)
  have hA : √(pA * (1 - pA)) ^ 2 = pA * (1 - pA) := Real.sq_sqrt hqA.le
  have hB : √(pB * (1 - pB)) ^ 2 = pB * (1 - pB) := Real.sq_sqrt hqB.le
  have h := tendstoInDistribution_two_sample_means (Real.sqrt_pos.2 hqA) (Real.sqrt_pos.2 hqB) hZ
    hLA hLB hmA hmB (hvA.trans hA.symm) (hvB.trans hB.symm) hindep hidentX hidentY hnA hnB
  rw [hA, hB] at h
  exact h

/-- The pooled sample proportion `p_c = (x_A + x_B) / (n_A + n_B)` of two 0/1 samples of sizes `m`
and `n`. -/
noncomputable def pooledProportion {Ω : Type*} (X Y : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) : ℝ :=
  ((∑ i ∈ Finset.range m, X i ω) + ∑ j ∈ Finset.range n, Y j ω) / ((m : ℝ) + n)

lemma abs_weighted_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y p : ℝ) :
    |(a * x + b * y) / (a + b) - p| ≤ |x - p| + |y - p| := by
  have hab : 0 < a + b := add_pos ha hb
  have h : (a * x + b * y) / (a + b) - p = a / (a + b) * (x - p) + b / (a + b) * (y - p) := by
    field_simp
    ring
  rw [h]
  have hwa : |a / (a + b)| ≤ 1 := by
    rw [abs_of_pos (div_pos ha hab), div_le_one hab]; linarith
  have hwb : |b / (a + b)| ≤ 1 := by
    rw [abs_of_pos (div_pos hb hab), div_le_one hab]; linarith
  calc _ ≤ |a / (a + b) * (x - p)| + |b / (a + b) * (y - p)| := abs_add_le _ _
    _ = |a / (a + b)| * |x - p| + |b / (a + b)| * |y - p| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |x - p| + 1 * |y - p| := by gcongr
    _ = _ := by ring

lemma pooled_identity {D q c w : ℝ} (hq : 0 < q) (hc : 0 < c) (hw : 0 < w) :
    D / √(c * w) = (D - 0) / √(q * w) * √q / √c := by
  rw [Real.sqrt_mul hc.le, Real.sqrt_mul hq.le]
  have h1 : 0 < √q := Real.sqrt_pos.2 hq
  have h2 : 0 < √c := Real.sqrt_pos.2 hc
  have h3 : 0 < √w := Real.sqrt_pos.2 hw
  field_simp
  ring

/-- **Pooled two-proportion test (ST-093).** Under the null hypothesis `p_A = p_B = p` (`0 < p < 1`),
the test statistic of the book, with the pooled proportion `p_c = (x_A + x_B)/(n_A + n_B)`,
`z = (p'_A - p'_B) / √(p_c (1 - p_c) (1/n_A + 1/n_B))`,
tends to `N(0, 1)` in distribution as both sample sizes tend to infinity (in any manner). -/
@[kb "openstaxintrostats2e" "§10.3, p. 534"]
theorem tendstoInDistribution_pooled_two_proportions [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {p : ℝ} (h0 : 0 < p) (h1 : p < 1)
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hmX : ∀ i, Measurable (X i)) (hmY : ∀ i, Measurable (Y i))
    (h01X : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (h01Y : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hprobA : P.real {ω | X 0 ω = 1} = p) (hprobB : P.real {ω | Y 0 ω = 1} = p)
    (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    {nA nB : ℕ → ℕ} (hnA : Tendsto nA atTop atTop) (hnB : Tendsto nB atTop atTop) :
    TendstoInDistribution
      (fun k ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
          (∑ j ∈ Finset.range (nB k), Y j ω) / nB k) /
          √(pooledProportion X Y (nA k) (nB k) ω * (1 - pooledProportion X Y (nA k) (nB k) ω) *
            (1 / nA k + 1 / nB k)))
      atTop Z (fun _ ↦ P) P' := by
  classical
  obtain ⟨hmA, -, hLA⟩ := bern_moments (P := P) (hmX 0) (h01X 0) hprobA
  obtain ⟨hmB, -, hLB⟩ := bern_moments (P := P) (hmY 0) (h01Y 0) hprobB
  set q := p * (1 - p) with hq
  have hq0 : 0 < q := mul_pos h0 (by linarith)
  set δ := q / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδq : δ < q := by linarith
  set g : ℝ × ℝ → ℝ := fun z ↦ z.1 * √q / √(max (z.2 * (1 - z.2)) δ) with hg
  have hgc : Continuous g := by
    refine (continuous_fst.mul continuous_const).div (Real.continuous_sqrt.comp
      ((continuous_snd.mul (continuous_const.sub continuous_snd)).max continuous_const)) ?_
    intro z
    exact (Real.sqrt_pos.2 (lt_of_lt_of_le hδ (le_max_right _ _))).ne'
  have hSX : ∀ k, Measurable fun ω ↦ ∑ i ∈ Finset.range (nA k), X i ω :=
    fun k ↦ Finset.measurable_fun_sum _ fun i _ ↦ hmX i
  have hSY : ∀ k, Measurable fun ω ↦ ∑ j ∈ Finset.range (nB k), Y j ω :=
    fun k ↦ Finset.measurable_fun_sum _ fun i _ ↦ hmY i
  have hPm : ∀ k, Measurable (pooledProportion X Y (nA k) (nB k)) := fun k ↦
    ((hSX k).add (hSY k)).div_const _
  have hT := tendstoInDistribution_two_proportions_sizes h0 h1 h0 h1 hZ hmX hmY h01X h01Y hprobA
    hprobB hindep hidentX hidentY hnA hnB
  -- strong law for each sample, then for the pooled proportion
  have hAae : ∀ᵐ ω ∂P, Tendsto (fun k ↦ (∑ i ∈ Finset.range (nA k), X i ω) / nA k) atTop (𝓝 p) := by
    have h := strong_law_ae_real X (hLA.integrable one_le_two)
      (fun i j hij ↦ hindep.indepFun (Sum.inl_injective.ne hij)) hidentX
    filter_upwards [h] with ω hω
    rw [hmA] at hω
    exact hω.comp hnA
  have hBae : ∀ᵐ ω ∂P, Tendsto (fun k ↦ (∑ j ∈ Finset.range (nB k), Y j ω) / nB k) atTop (𝓝 p) := by
    have h := strong_law_ae_real Y (hLB.integrable one_le_two)
      (fun i j hij ↦ hindep.indepFun (Sum.inr_injective.ne hij)) hidentY
    filter_upwards [h] with ω hω
    rw [hmB] at hω
    exact hω.comp hnB
  have hcae : ∀ᵐ ω ∂P, Tendsto (fun k ↦ pooledProportion X Y (nA k) (nB k) ω) atTop (𝓝 p) := by
    filter_upwards [hAae, hBae] with ω hA hB
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun k ↦ ‖(∑ i ∈ Finset.range (nA k), X i ω) / nA k - p‖ +
        ‖(∑ j ∈ Finset.range (nB k), Y j ω) / nB k - p‖) atTop (𝓝 0) := by
      have h := ((tendsto_iff_norm_sub_tendsto_zero.1 hA).add (tendsto_iff_norm_sub_tendsto_zero.1 hB))
      rw [add_zero] at h
      exact h
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [hnA.eventually_ge_atTop 1, hnB.eventually_ge_atTop 1] with k hka hkb
    have ha' : (0 : ℝ) < nA k := by exact_mod_cast hka
    have hb' : (0 : ℝ) < nB k := by exact_mod_cast hkb
    have h := abs_weighted_sub_le ha' hb' ((∑ i ∈ Finset.range (nA k), X i ω) / nA k)
      ((∑ j ∈ Finset.range (nB k), Y j ω) / nB k) p
    have he : (nA k * ((∑ i ∈ Finset.range (nA k), X i ω) / nA k) +
        nB k * ((∑ j ∈ Finset.range (nB k), Y j ω) / nB k)) / (nA k + nB k) =
        pooledProportion X Y (nA k) (nB k) ω := by
      simp only [pooledProportion]
      field_simp
    rw [he] at h
    simpa only [Real.norm_eq_abs] using h
  have hPconv : TendstoInMeasure P (fun k ↦ pooledProportion X Y (nA k) (nB k)) atTop
      (fun _ ↦ p) :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (hPm k).aestronglyMeasurable) hcae
  -- Slutsky's theorem
  have hsl := hT.continuous_comp_prodMk_of_tendstoInMeasure_const hgc hPconv
    fun k ↦ (hPm k).aemeasurable
  have hgZ : (fun ω ↦ g (Z ω, p)) = Z := by
    funext ω
    simp only [hg]
    rw [max_eq_left (by rw [← hq]; exact hδq.le)]
    have : 0 < √q := Real.sqrt_pos.2 hq0
    rw [← hq]
    field_simp
  rw [hgZ] at hsl
  -- the statistic agrees with `g` eventually, almost surely
  have hZcm : ∀ k, Measurable fun ω ↦ ((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
      (∑ j ∈ Finset.range (nB k), Y j ω) / nB k) /
      √(pooledProportion X Y (nA k) (nB k) ω * (1 - pooledProportion X Y (nA k) (nB k) ω) *
        (1 / nA k + 1 / nB k)) := by
    intro k
    have := hSX k; have := hSY k; have := hPm k
    fun_prop
  have hgm : ∀ k, Measurable fun ω ↦ g (((∑ i ∈ Finset.range (nA k), X i ω) / nA k -
      (∑ j ∈ Finset.range (nB k), Y j ω) / nB k - (p - p)) / √(q / nA k + q / nB k),
      pooledProportion X Y (nA k) (nB k) ω) := by
    intro k
    have := hSX k; have := hSY k; have := hPm k
    exact hgc.measurable.comp (by fun_prop)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hsl ?_ fun k ↦ (hZcm k).aemeasurable
  refine tendstoInMeasure_of_tendsto_ae (fun k ↦ ((hZcm k).sub (hgm k)).aestronglyMeasurable) ?_
  filter_upwards [hcae] with ω hω
  have hcq : Tendsto (fun k ↦ pooledProportion X Y (nA k) (nB k) ω *
      (1 - pooledProportion X Y (nA k) (nB k) ω)) atTop (𝓝 q) :=
    hω.mul (tendsto_const_nhds.sub hω)
  have hev : ∀ᶠ k in atTop, δ ≤ pooledProportion X Y (nA k) (nB k) ω *
      (1 - pooledProportion X Y (nA k) (nB k) ω) :=
    (hcq.eventually (lt_mem_nhds hδq)).mono fun _ h ↦ h.le
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev, hnA.eventually_ge_atTop 1, hnB.eventually_ge_atTop 1] with k hk hka hkb
  have ha' : (0 : ℝ) < nA k := by exact_mod_cast hka
  have hb' : (0 : ℝ) < nB k := by exact_mod_cast hkb
  simp only [Pi.sub_apply, Pi.zero_apply, hg]
  rw [max_eq_left hk, sub_self, show q / nA k + q / nB k = q * (1 / nA k + 1 / nB k) by ring,
    pooled_identity hq0 (lt_of_lt_of_le hδ hk) (by positivity), sub_self]

end TwoSample

end UndergradKB.Statistics
