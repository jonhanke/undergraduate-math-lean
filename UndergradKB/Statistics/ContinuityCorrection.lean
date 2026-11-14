import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Portmanteau
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.Limits

/-!
# The continuity correction for the normal approximation of the binomial (OpenStax *Introductory Statistics 2e*, §7.3)

* convergence in distribution to `N(0,1)` gives convergence of `P(Zₙ ≤ x)` to `Φ x` (the standard normal
  law has no atoms), and in fact uniformly in `x` (Pólya);
* `Φ` is Lipschitz;
* the binomial count is integer valued, so `{S ≤ k} = {S ≤ k + 1/2}`;
* hence `P(S ≤ k)` is uniformly close to `Φ((k + 1/2 - n p)/√(n p (1-p)))` for large `n`, for all integers `k`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Set Filter Topology

local notation "Φ" => cdf (gaussianReal 0 1)

section Cdf

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'} {Z : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

/-- OpenStax Introductory Statistics 2e §7.3 (ST-069). If `Zₙ` converges in distribution to a standard
normal variable, then for each `x` the probability `P(Zₙ ≤ x)` converges to the z-table value `Φ x`. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem tendsto_prob_le_of_tendstoInDistribution [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hT : TendstoInDistribution Z atTop Y (fun _ => P) P') (x : ℝ) :
    Tendsto (fun n => P.real {ω | Z n ω ≤ x}) atTop (𝓝 (Φ x)) := by
  have hnull : (P'.map Y) (frontier (Set.Iic x)) = 0 := by
    rw [hY.map_eq, frontier_Iic]; exact gaussianReal_zero_one_singleton x
  have hP : ∀ n, IsProbabilityMeasure (P.map (Z n)) := fun n => inferInstance
  have hP' : IsProbabilityMeasure (P'.map Y) := inferInstance
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μs := fun n => (⟨P.map (Z n), hP n⟩ : ProbabilityMeasure ℝ))
    (μ := (⟨P'.map Y, hP'⟩ : ProbabilityMeasure ℝ))
    hT.tendsto (E := Set.Iic x) hnull
  have key2 := (ENNReal.tendsto_toReal (measure_ne_top (P'.map Y) (Set.Iic x))).comp key
  have hlim : ((P'.map Y) (Set.Iic x)).toReal = Φ x := by
    rw [hY.map_eq, cdf_eq_real]; rfl
  rw [← hlim]
  refine key2.congr fun n => ?_
  change ((P.map (Z n)) (Set.Iic x)).toReal = _
  rw [Measure.map_apply_of_aemeasurable (hT.forall_aemeasurable n) measurableSet_Iic,
    measureReal_def]
  rfl

/-- OpenStax Introductory Statistics 2e §7.3 (ST-069). The z-table is Lipschitz: the standard normal
density is at most `1`, so `|Φ b - Φ a| ≤ |b - a|`. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem abs_stdNormalCdf_sub_le (a b : ℝ) : |Φ b - Φ a| ≤ |b - a| := by
  have key : ∀ a b : ℝ, a ≤ b → Φ b - Φ a ≤ b - a := by
    intro a b hab
    have h1 : Φ b - Φ a = (gaussianReal 0 1 (Ioc a b)).toReal := by
      have := (cdf (gaussianReal 0 1)).measure_Ioc a b
      rw [measure_cdf] at this
      rw [this, ENNReal.toReal_ofReal (sub_nonneg.2 ((cdf (gaussianReal 0 1)).mono hab))]
    rw [h1, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
        fun x _ => gaussianPDFReal_nonneg 0 1 x)]
    have hb : ∀ x : ℝ, ‖gaussianPDFReal 0 1 x‖ ≤ 1 := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x), gaussianPDFReal_def]
      have h2 : (1 : ℝ) ≤ √(2 * Real.pi * ((1 : NNReal) : ℝ)) := by
        rw [Real.one_le_sqrt]
        simp only [NNReal.coe_one, mul_one]
        linarith [Real.pi_gt_three]
      have h3 : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (x - 0) ^ 2 := sq_nonneg _
        have h4 : -(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)) = -((x - 0) ^ 2 / 2) := by
          simp [neg_div]
        rw [h4]; exact neg_nonpos.2 (div_nonneg this (by norm_num))
      have h5 : (√(2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
      calc _ ≤ 1 * 1 := mul_le_mul h5 h3 (Real.exp_pos _).le zero_le_one
        _ = 1 := one_mul 1
    have := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) (s := Ioc a b)
      (f := gaussianPDFReal 0 1) (C := 1) (by simp) (Filter.Eventually.of_forall fun x _ => hb x)
    calc _ ≤ ‖∫ x in Ioc a b, gaussianPDFReal 0 1 x‖ := (by rw [Real.norm_eq_abs]; exact le_abs_self _)
      _ ≤ 1 * volume.real (Ioc a b) := this
      _ = b - a := by simp [Measure.real, Real.volume_Ioc, hab]
  rcases le_total a b with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg (sub_nonneg.2 ((cdf (gaussianReal 0 1)).mono h))]
    exact key a b h
  · rw [abs_sub_comm, abs_sub_comm b a, abs_of_nonneg (sub_nonneg.2 h),
      abs_of_nonneg (sub_nonneg.2 ((cdf (gaussianReal 0 1)).mono h))]
    exact key b a h

/-- OpenStax Introductory Statistics 2e §7.3 (ST-069). Pólya-type uniformity: if `Zₙ` converges in
distribution to a standard normal variable, then `P(Zₙ ≤ x)` is within `ε` of `Φ x` for all `x` at once,
as soon as `n` is large. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem uniform_cdf_of_tendstoInDistribution [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hT : TendstoInDistribution Z atTop Y (fun _ => P) P') {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |P.real {ω | Z n ω ≤ x} - Φ x| ≤ ε := by
  have h1 := tendsto_prob_le_of_tendstoInDistribution hY hT
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨A, hA⟩ := eventually_atBot.1 ((tendsto_order.1 (tendsto_cdf_atBot (gaussianReal 0 1))).2
    (ε / 4) hε4)
  obtain ⟨B, hB⟩ := eventually_atTop.1 ((tendsto_order.1 (tendsto_cdf_atTop (gaussianReal 0 1))).1
    (1 - ε / 4) (by linarith))
  set M : ℝ := max (max (-A) B) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hlo : Φ (-M) < ε / 4 := hA _ (by
    have : -A ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith)
  have hhi : 1 - ε / 4 < Φ M := hB _ (le_trans (le_max_right _ _) (le_max_left _ _))
  set N : ℕ := ⌈8 * M / ε⌉₊ with hN
  set g : ℕ → ℝ := fun j => -M + j * (ε / 4) with hg
  have hgN : M ≤ g N := by
    have h8 : 8 * M / ε ≤ N := Nat.le_ceil _
    have : 8 * M ≤ N * ε := by rwa [div_le_iff₀ hε] at h8
    simp only [hg]; nlinarith
  have hev : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (N + 1), |P.real {ω | Z n ω ≤ g j} - Φ (g j)| ≤ ε / 4 := by
    refine (Filter.eventually_all_finset _).2 fun j _ => ?_
    have := Metric.tendsto_nhds.1 (h1 (g j)) (ε / 4) hε4
    filter_upwards [this] with n hn
    exact (Real.dist_eq _ _ ▸ hn).le
  filter_upwards [hev] with n hn x
  have hmono : ∀ {x y : ℝ}, x ≤ y → P.real {ω | Z n ω ≤ x} ≤ P.real {ω | Z n ω ≤ y} :=
    fun hxy => measureReal_mono (fun ω h => le_trans h hxy)
  have hF0 : ∀ x, 0 ≤ P.real {ω | Z n ω ≤ x} := fun x => measureReal_nonneg
  have hF1 : ∀ x, P.real {ω | Z n ω ≤ x} ≤ 1 := fun x => measureReal_le_one
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x => cdf_nonneg _ _
  have hΦ1 : ∀ x, Φ x ≤ 1 := fun x => cdf_le_one _ _
  have hΦm : ∀ {x y : ℝ}, x ≤ y → Φ x ≤ Φ y := fun h => (cdf (gaussianReal 0 1)).mono h
  have hg0 : g 0 = -M := by simp [hg]
  rw [abs_le]
  by_cases hx0 : x < g 0
  · have a1 := (abs_le.1 (hn 0 (by simp))).2
    have a2 := hF1 x
    have a3 := hmono hx0.le
    have a4 := hΦm hx0.le
    rw [hg0] at a1 a4 a3
    constructor <;> linarith [hF0 x, hΦ0 x]
  by_cases hxN : g N ≤ x
  · have a1 := (abs_le.1 (hn N (by simp))).1
    have a3 := hmono hxN
    have a4 := hΦm hxN
    have a5 := hΦm hgN
    constructor <;> linarith [hF1 x, hΦ1 x]
  push Not at hx0 hxN
  have hδ : 0 < ε / 4 := hε4
  have hnn : 0 ≤ (x + M) / (ε / 4) := div_nonneg (by simp only [hg] at hx0; linarith) hδ.le
  set j := ⌊(x + M) / (ε / 4)⌋₊ with hj
  have hj1 : (j : ℝ) ≤ (x + M) / (ε / 4) := Nat.floor_le hnn
  have hj2 : (x + M) / (ε / 4) < j + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hδ] at hj1
  rw [div_lt_iff₀ hδ] at hj2
  have hjN : j < N := by
    have : (x + M) / (ε / 4) < N := by
      rw [div_lt_iff₀ hδ]; simp only [hg] at hxN; linarith
    exact (Nat.floor_lt hnn).2 this
  have a1 := abs_le.1 (hn j (by simp; omega))
  have a2 := abs_le.1 (hn (j + 1) (by simp; omega))
  have hgj : g j ≤ x := by simp only [hg]; linarith
  have hgj1 : x ≤ g (j + 1) := by simp only [hg]; push_cast; linarith
  have lip := abs_stdNormalCdf_sub_le (g j) (g (j + 1))
  have hd : |g (j + 1) - g j| = ε / 4 := by
    have : g (j + 1) - g j = ε / 4 := by simp only [hg]; push_cast; ring
    rw [this, abs_of_pos hδ]
  rw [hd] at lip
  have lip' := (abs_le.1 lip).2
  have b1 := hmono hgj
  have b2 := hmono hgj1
  have b3 := hΦm hgj
  have b4 := hΦm hgj1
  constructor <;> linarith

end Cdf

section Binomial

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- A sum of `0/1` values is a natural number. -/
lemma sum_range_eq_natCast (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (n : ℕ) (ω : Ω) :
    ∃ m : ℕ, ∑ i ∈ Finset.range n, X i ω = (m : ℝ) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    rw [Finset.sum_range_succ, hm]
    rcases h01 n ω with h | h
    · exact ⟨m, by rw [h]; simp⟩
    · exact ⟨m + 1, by rw [h]; push_cast; ring⟩

/-- OpenStax Introductory Statistics 2e §7.3 (ST-069). The binomial count `Sₙ` takes integer values,
so for an integer `k` the events `{Sₙ ≤ k}`, `{Sₙ ≤ k + 1/2}` and `{Sₙ < k + 1}` coincide: this is why
one evaluates the normal approximation at `k + 1/2`. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem binomial_le_eq_le_add_half (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (n : ℕ) (k : ℤ) :
    {ω | ∑ i ∈ Finset.range n, X i ω ≤ (k : ℝ)} = {ω | ∑ i ∈ Finset.range n, X i ω ≤ (k : ℝ) + 1 / 2} ∧
    {ω | ∑ i ∈ Finset.range n, X i ω ≤ (k : ℝ)} = {ω | ∑ i ∈ Finset.range n, X i ω < (k : ℝ) + 1} := by
  constructor <;> ext ω <;> obtain ⟨m, hm⟩ := sum_range_eq_natCast h01 n ω <;>
    simp only [Set.mem_setOf_eq, hm] <;>
    have hc : ((m : ℤ) : ℝ) = (m : ℝ) := by simp
  · rw [← hc]
    constructor
    · intro h; linarith
    · intro h
      by_contra hlt
      have : k + 1 ≤ (m : ℤ) := by
        have : k < (m : ℤ) := by
          have : (k : ℝ) < ((m : ℤ) : ℝ) := by rw [hc]; linarith [not_le.1 hlt]
          exact_mod_cast this
        omega
      have : ((k + 1 : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
  · rw [← hc]
    constructor
    · intro h; linarith
    · intro h
      have : (m : ℤ) < k + 1 := by
        have : ((m : ℤ) : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; exact h
        exact_mod_cast this
      have : (m : ℤ) ≤ k := by omega
      exact_mod_cast this

variable [IsProbabilityMeasure P]

/-- The standardised count `(Sₙ - n p)/√(n p (1-p))` as a function of the outcome. -/
private lemma standardised_le_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n : ℕ} (hn : 1 ≤ n) (c s : ℝ) :
    s ≤ c ↔ (s - n * p) / √(n * p * (1 - p)) ≤ (c - n * p) / √(n * p * (1 - p)) := by
  have hpos : 0 < (n : ℝ) * p * (1 - p) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact mul_pos (mul_pos this hp0) (by linarith)
  rw [div_le_div_iff_of_pos_right (Real.sqrt_pos.2 hpos)]
  constructor <;> intro h <;> linarith

variable {P' : Measure ℝ}

/-- **Uniform normal approximation of the binomial.** OpenStax Introductory Statistics 2e §7.3 (ST-069).
For Bernoulli trials with `0 < p < 1`, for every `ε > 0` and all large `n`, simultaneously for every real
`x`, `P(Sₙ ≤ n p + x √(n p (1-p)))` is within `ε` of `Φ x`; equivalently
`P(Sₙ ≤ k)` is within `ε` of `Φ((k - n p)/√(n p (1-p)))` for every real `k`. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem binomial_normal_approx_uniform {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hprob : P.real {ω | X 0 ω = 1} = p) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ,
      |P.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ k} - Φ ((k - n * p) / √(n * p * (1 - p)))| ≤ ε := by
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) := ⟨aemeasurable_id, by simp⟩
  have hT := tendstoInDistribution_binomial_count (P' := gaussianReal 0 1) hp0 hp1 hY hmeas h01
    hprob hindep hident
  filter_upwards [uniform_cdf_of_tendstoInDistribution hY hT hε, eventually_ge_atTop 1] with n hn hn1 k
  have := hn ((k - n * p) / √(n * p * (1 - p)))
  have hset : {ω | ∑ i ∈ Finset.range n, X i ω ≤ k} = {ω | (∑ i ∈ Finset.range n, X i ω - n * p) /
      √(n * p * (1 - p)) ≤ (k - n * p) / √(n * p * (1 - p))} := by
    ext ω
    exact standardised_le_iff hp0 hp1 hn1 k _
  rw [hset]
  exact this

/-- **Normal approximation with the continuity correction.** OpenStax Introductory Statistics 2e §7.3
(ST-069). For Bernoulli trials with `0 < p < 1`, every `ε > 0`, all large `n`, and every integer `k`,
the binomial probability `P(Sₙ ≤ k)` is within `ε` of `Φ((k + 1/2 - n p)/√(n p (1-p)))`. -/
@[kb "openstaxintrostats2e" "§7.3, p. 384"]
theorem binomial_continuity_correction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hmeas : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hprob : P.real {ω | X 0 ω = 1} = p) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℤ,
      |P.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ (k : ℝ)} -
        Φ (((k : ℝ) + 1 / 2 - n * p) / √(n * p * (1 - p)))| ≤ ε := by
  filter_upwards [binomial_normal_approx_uniform hp0 hp1 hmeas h01 hprob hindep hident hε] with n hn k
  rw [(binomial_le_eq_le_add_half h01 n k).1]
  exact hn ((k : ℝ) + 1 / 2)

end Binomial

end UndergradKB.Statistics
