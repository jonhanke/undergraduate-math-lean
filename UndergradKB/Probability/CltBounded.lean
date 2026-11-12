import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Complex.Exponential
import UndergradKB.Common.Attr

/-!
# Central limit theorem for bounded, non-identically distributed summands (Grinstead–Snell, chapter 9)

Theorem 9.5: independent uniformly bounded random variables whose variances add up to infinity
satisfy the central limit theorem. The proof is by Lévy's continuity theorem: the characteristic function
of a bounded centred variable is `1 - σ²u²/2` up to `O(|u|³ σ²)`, and the product of such factors at
`u = t/s_n` tends to `e^{-t²/2}`.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology Real

namespace UndergradKB.Probability

/-- A product of complex numbers of norm at most one moves by at most the sum of the factor moves. -/
private lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have h1 : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg (g i))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    calc ‖f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i‖
        = ‖f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i‖ := by ring_nf
      _ ≤ ‖f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖ + ‖(f a - g a) * ∏ i ∈ s, g i‖ := norm_add_le _ _
      _ ≤ 1 * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ + ‖f a - g a‖ * 1 := by
          rw [norm_mul, norm_mul]
          gcongr
      _ ≤ _ := by linarith

/-- Taylor estimate for the characteristic function of a bounded centred variable. -/
private lemma charFun_taylor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) {B : ℝ}
    (hbd : ∀ᵐ ω ∂P, |Z ω| ≤ B) (h0 : ∫ ω, Z ω ∂P = 0) {u : ℝ} (hu : |u| * B ≤ 1) :
    ‖charFun (P.map Z) u - ((1 - (∫ ω, Z ω ^ 2 ∂P) * u ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      2 / 9 * |u| ^ 3 * B * ∫ ω, Z ω ^ 2 ∂P := by
  have hB : 0 ≤ B := by
    obtain ⟨ω, hω⟩ := hbd.exists
    exact le_trans (abs_nonneg _) hω
  have hZint : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable B
    (hbd.mono fun ω h => by simpa using h)
  have hZ2int : Integrable (fun ω => Z ω ^ 2) P := Integrable.of_bound
    (hZ.pow_const 2).aestronglyMeasurable (B ^ 2) (hbd.mono fun ω h => by
      simpa [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2)
  set f : Ω → ℂ := fun ω => cexp (u * Z ω * I) with hf
  set g : Ω → ℂ := fun ω =>
    ((1 - u ^ 2 * Z ω ^ 2 / 2 : ℝ) : ℂ) + ((u * Z ω : ℝ) : ℂ) * I with hg
  have hfint : Integrable f P := by
    refine Integrable.of_bound (C := 1) (by fun_prop) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    have : (u * Z ω * I : ℂ) = ((u * Z ω : ℝ) : ℂ) * I := by push_cast; ring
    simp only [hf, this, Complex.norm_exp_ofReal_mul_I, le_refl]
  have hgint : Integrable g P := by
    have h1 : Integrable (fun ω => ((1 - u ^ 2 * Z ω ^ 2 / 2 : ℝ) : ℂ)) P :=
      (((integrable_const (1 : ℝ)).sub (hZ2int.const_mul (u ^ 2) |>.div_const 2))).ofReal
    have h2 : Integrable (fun ω => ((u * Z ω : ℝ) : ℂ)) P := (hZint.const_mul u).ofReal
    exact h1.add (h2.mul_const I)
  have hintg : ∫ ω, g ω ∂P = ((1 - (∫ ω, Z ω ^ 2 ∂P) * u ^ 2 / 2 : ℝ) : ℂ) := by
    have h1 : Integrable (fun ω => ((1 - u ^ 2 * Z ω ^ 2 / 2 : ℝ) : ℂ)) P :=
      (((integrable_const (1 : ℝ)).sub (hZ2int.const_mul (u ^ 2) |>.div_const 2))).ofReal
    have h2 : Integrable (fun ω => ((u * Z ω : ℝ) : ℂ)) P := (hZint.const_mul u).ofReal
    simp only [hg]
    rw [integral_add h1 (h2.mul_const I), integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal,
      integral_const_mul, h0, integral_sub (integrable_const _) (hZ2int.const_mul (u ^ 2) |>.div_const 2),
      integral_div, integral_const_mul]
    simp
    ring_nf
  have hpt : ∀ᵐ ω ∂P, ‖f ω - g ω‖ ≤ 2 / 9 * |u| ^ 3 * B * Z ω ^ 2 := by
    filter_upwards [hbd] with ω hω
    have hy : ‖(u * Z ω * I : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, mul_one]
      simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc |u| * |Z ω| ≤ |u| * B := by gcongr
        _ ≤ 1 := hu
    have hb := Complex.exp_bound hy (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, (u * Z ω * I : ℂ) ^ m / (m.factorial : ℂ) = g ω := by
      simp only [hg, Finset.sum_range_succ, Finset.sum_range_zero]
      push_cast
      simp [Nat.factorial]
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hs] at hb
    refine hb.trans ?_
    have hn : ‖(u * Z ω * I : ℂ)‖ = |u| * |Z ω| := by
      simp [Complex.norm_mul, abs_mul]
    rw [hn]
    have h3 : |Z ω| ^ 3 ≤ B * Z ω ^ 2 := by
      calc |Z ω| ^ 3 = |Z ω| * Z ω ^ 2 := by rw [← sq_abs (Z ω)]; ring
        _ ≤ B * Z ω ^ 2 := by gcongr
    have hc : ((3 : ℕ).succ : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ = 2 / 9 := by
      norm_num [Nat.factorial]
    rw [hc]
    calc (|u| * |Z ω|) ^ 3 * (2 / 9) = 2 / 9 * |u| ^ 3 * |Z ω| ^ 3 := by ring
      _ ≤ 2 / 9 * |u| ^ 3 * (B * Z ω ^ 2) := by gcongr
      _ = _ := by ring
  have hbint : Integrable (fun ω => 2 / 9 * |u| ^ 3 * B * Z ω ^ 2) P := hZ2int.const_mul _
  have := norm_integral_le_of_norm_le hbint hpt
  rw [integral_sub hfint hgint, hintg, integral_const_mul] at this
  rw [charFun_apply_real, integral_map hZ.aemeasurable (by fun_prop)]
  exact this

/-- Comparison of `1 - c` with `exp (-c)` for small `c ≥ 0`. -/
private lemma norm_one_sub_sub_exp_neg {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ‖((1 - c : ℝ) : ℂ) - cexp (-(c : ℂ))‖ ≤ 3 / 4 * c ^ 2 := by
  have hx : ‖(-(c : ℂ))‖ ≤ 1 := by simpa [abs_of_nonneg h0] using h1
  have hb := Complex.exp_bound hx (n := 2) (by norm_num)
  have hs : ∑ m ∈ Finset.range 2, (-(c : ℂ)) ^ m / (m.factorial : ℂ) = ((1 - c : ℝ) : ℂ) := by
    simp [Finset.sum_range_succ]
    ring
  rw [hs, norm_sub_rev] at hb
  refine hb.trans (le_of_eq ?_)
  have : ‖(-(c : ℂ))‖ = c := by simp [abs_of_nonneg h0]
  rw [this]
  norm_num [Nat.factorial]
  ring

/-- The analytic core of the central limit theorem for bounded summands. -/
private lemma tendsto_prod_charFun {σ : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hσ0 : ∀ k, 0 ≤ σ k)
    (hσB : ∀ k, σ k ≤ B ^ 2) {φ : ℕ → ℝ → ℂ} (hφ1 : ∀ k u, ‖φ k u‖ ≤ 1)
    (hφ : ∀ k u, |u| * B ≤ 1 →
      ‖φ k u - ((1 - σ k * u ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 2 / 9 * |u| ^ 3 * B * σ k)
    (hV : Tendsto (fun n => ∑ k ∈ Finset.range n, σ k) atTop atTop) (t : ℝ) :
    Tendsto (fun n => ∏ k ∈ Finset.range n, φ k (t / √(∑ j ∈ Finset.range n, σ j))) atTop
      (𝓝 (cexp (-((t ^ 2 / 2 : ℝ) : ℂ)))) := by
  set V : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, σ k with hVdef
  have hsq : Tendsto (fun n => √(V n)) atTop atTop := Real.tendsto_sqrt_atTop.comp hV
  have hε : Tendsto (fun n => 2 / 9 * |t| ^ 3 * B * (√(V n))⁻¹ + 3 / 16 * B ^ 2 * t ^ 4 * (V n)⁻¹)
      atTop (𝓝 0) := by
    have h1 := tendsto_inv_atTop_zero.comp hsq
    have h2 := tendsto_inv_atTop_zero.comp hV
    simpa using (h1.const_mul (2 / 9 * |t| ^ 3 * B)).add (h2.const_mul (3 / 16 * B ^ 2 * t ^ 4))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hε
  filter_upwards [hV.eventually_gt_atTop 0, hsq.eventually_ge_atTop (|t| * B)] with n hVn hsn
  set s := √(V n) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hVn
  have hVs : V n = s ^ 2 := (Real.sq_sqrt hVn.le).symm
  set u := t / s with hudef
  have hu : |u| * B ≤ 1 := by
    rw [hudef, abs_div, abs_of_pos hs, div_mul_eq_mul_div, div_le_one hs]
    exact hsn
  have hBu : B ^ 2 * u ^ 2 ≤ 1 := by
    have : B ^ 2 * u ^ 2 = (|u| * B) ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [this]
    exact pow_le_one₀ (by positivity) hu
  have hc0 : ∀ k, 0 ≤ σ k * u ^ 2 / 2 := fun k => by have := hσ0 k; positivity
  have hc1 : ∀ k, σ k * u ^ 2 / 2 ≤ 1 / 2 := fun k => by
    have := hσB k
    have h2 : σ k * u ^ 2 ≤ B ^ 2 * u ^ 2 := by gcongr
    linarith
  set b : ℕ → ℂ := fun k => ((1 - σ k * u ^ 2 / 2 : ℝ) : ℂ) with hb
  set d : ℕ → ℂ := fun k => cexp (-((σ k * u ^ 2 / 2 : ℝ) : ℂ)) with hd
  have hbn : ∀ k ∈ Finset.range n, ‖b k‖ ≤ 1 := fun k _ => by
    simp only [hb, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> linarith [hc0 k, hc1 k]
  have hdn : ∀ k ∈ Finset.range n, ‖d k‖ ≤ 1 := fun k _ => by
    simp only [hd]
    rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.neg_re, Complex.ofReal_re]
    linarith [hc0 k]
  have h1 := norm_prod_sub_prod_le (Finset.range n) (fun k => φ k u) b
    (fun k _ => hφ1 k u) hbn
  have h2 := norm_prod_sub_prod_le (Finset.range n) b d hbn hdn
  have h3 : ∏ k ∈ Finset.range n, d k = cexp (-((t ^ 2 / 2 : ℝ) : ℂ)) := by
    simp only [hd]
    rw [← Complex.exp_sum, Finset.sum_neg_distrib]
    congr 2
    rw [← Complex.ofReal_sum, ← Finset.sum_div, ← Finset.sum_mul]
    have : ∑ k ∈ Finset.range n, σ k = s ^ 2 := hVs
    rw [this, hudef]
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  have h4 : ∑ k ∈ Finset.range n, ‖φ k u - b k‖ ≤ 2 / 9 * |u| ^ 3 * B * V n := by
    calc _ ≤ ∑ k ∈ Finset.range n, 2 / 9 * |u| ^ 3 * B * σ k :=
          Finset.sum_le_sum fun k _ => hφ k u hu
      _ = _ := by rw [← Finset.mul_sum]
  have h5 : ∑ k ∈ Finset.range n, ‖b k - d k‖ ≤ 3 / 4 * (B ^ 2 * u ^ 2 / 2) * (V n * u ^ 2 / 2) := by
    calc _ ≤ ∑ k ∈ Finset.range n, 3 / 4 * (B ^ 2 * u ^ 2 / 2) * (σ k * u ^ 2 / 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hk := norm_one_sub_sub_exp_neg (hc0 k) (by linarith [hc1 k])
          refine hk.trans ?_
          have h2 : σ k * u ^ 2 / 2 ≤ B ^ 2 * u ^ 2 / 2 := by
            have := hσB k
            have : σ k * u ^ 2 ≤ B ^ 2 * u ^ 2 := by gcongr
            linarith
          have := hc0 k
          nlinarith
      _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_mul]
  have h6 := norm_sub_le_norm_sub_add_norm_sub (∏ k ∈ Finset.range n, φ k u)
    (∏ k ∈ Finset.range n, b k) (∏ k ∈ Finset.range n, d k)
  rw [h3] at h6 h2
  refine h6.trans ?_
  refine (add_le_add (h1.trans h4) (h2.trans h5)).trans (le_of_eq ?_)
  rw [hVs, hudef]
  have hs0 : s ≠ 0 := hs.ne'
  rw [abs_div, abs_of_pos hs]
  field_simp
  ring

section Main

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Grinstead–Snell Theorem 9.5 (PR-101), convergence in distribution. Let `X_k` be independent random
variables with `|X_k| ≤ A` and variances `σ_k²` such that `s_n² = σ_0² + ... + σ_{n-1}²` tends to
infinity. Then `(S_n - E S_n) / s_n` converges in distribution to a standard normal variable. -/
@[kb "grinsteadsnell2006" "Theorem 9.5, p. 353"]
theorem clt_bounded {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P') {A : ℝ}
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k, ∀ᵐ ω ∂P, |X k ω| ≤ A)
    (hindep : iIndepFun X P)
    (hV : Tendsto (fun n => ∑ k ∈ Finset.range n, Var[X k; P]) atTop atTop) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(∑ k ∈ Finset.range n, Var[X k; P]))⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - ∑ k ∈ Finset.range n, P[X k]))
      atTop Y (fun _ => P) P' := by
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℕ → Ω → ℝ, Z = fun k ω => X k ω - P[X k] := ⟨_, rfl⟩
  have hZmeas : ∀ k, Measurable (Z k) := fun k => by
    rw [hZdef]; exact (hmeas k).sub_const _
  have hA : 0 ≤ A := by
    obtain ⟨ω, hω⟩ := (hbd 0).exists
    exact (abs_nonneg _).trans hω
  have hXint : ∀ k, Integrable (X k) P := fun k =>
    Integrable.of_bound (hmeas k).aestronglyMeasurable A (hbd k |>.mono fun ω h => by simpa using h)
  have hmean : ∀ k, |P[X k]| ≤ A := fun k => by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := X k) (C := A)
      ((hbd k).mono fun ω h => by simpa using h)
    simpa using this
  have hZbd : ∀ k, ∀ᵐ ω ∂P, |Z k ω| ≤ 2 * A := fun k => by
    filter_upwards [hbd k] with ω hω
    have := hmean k
    calc |Z k ω| = |X k ω - P[X k]| := by rw [hZdef]
      _ ≤ |X k ω| + |P[X k]| := abs_sub _ _
      _ ≤ 2 * A := by linarith
  have hZ0 : ∀ k, ∫ ω, Z k ω ∂P = 0 := fun k => by
    simp only [hZdef]
    rw [integral_sub (hXint k) (integrable_const _)]
    simp
  have hvar : ∀ k, Var[X k; P] = ∫ ω, Z k ω ^ 2 ∂P := fun k => by
    rw [hZdef]
    exact variance_eq_integral (hmeas k).aemeasurable
  have hσ0 : ∀ k, 0 ≤ Var[X k; P] := fun k => variance_nonneg _ _
  have hσB : ∀ k, Var[X k; P] ≤ (2 * A) ^ 2 := fun k => by
    rw [hvar]
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => Z k ω ^ 2) (C := (2 * A) ^ 2)
      ((hZbd k).mono fun ω h => by
        simpa [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2)
    simpa using (le_abs_self _).trans this
  have hindZ : iIndepFun Z P := by
    rw [hZdef]
    have h := hindep.comp (fun k (x : ℝ) => x - P[X k]) (fun k => measurable_id.sub_const _)
    exact h
  have hcf : ∀ (n : ℕ) (t : ℝ), charFun (P.map (fun ω => (√(∑ k ∈ Finset.range n, Var[X k; P]))⁻¹ *
      ∑ k ∈ Finset.range n, Z k ω)) t =
      ∏ k ∈ Finset.range n, charFun (P.map (Z k)) ((√(∑ k ∈ Finset.range n, Var[X k; P]))⁻¹ * t) := by
    intro n t
    rw [charFun_map_mul_comp (Finset.aemeasurable_fun_sum _ fun k _ => (hZmeas k).aemeasurable),
      (hindZ.restrict _).charFun_map_fun_finsetSum_eq_prod (fun k _ => (hZmeas k).aemeasurable)]
    simp
  have hfun : ∀ n, (fun ω => (√(∑ k ∈ Finset.range n, Var[X k; P]))⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - ∑ k ∈ Finset.range n, P[X k])) =
      fun ω => (√(∑ k ∈ Finset.range n, Var[X k; P]))⁻¹ * ∑ k ∈ Finset.range n, Z k ω := by
    intro n
    funext ω
    simp only [hZdef, Finset.sum_sub_distrib]
  refine TendstoInDistribution.of_tendsto_charFun (fun n => ?_) hY.aemeasurable (fun t => ?_)
  · rw [hfun n]
    exact (Finset.aemeasurable_fun_sum _ fun k _ => (hZmeas k).aemeasurable).const_mul _
  · simp_rw [hfun, hcf, hY.map_eq, charFun_gaussianReal]
    have := tendsto_prod_charFun (σ := fun k => Var[X k; P]) (B := 2 * A) (by positivity) hσ0 hσB
      (φ := fun k u => charFun (P.map (Z k)) u) (fun k u => by
        have : IsProbabilityMeasure (P.map (Z k)) :=
          (Measure.isProbabilityMeasure_map_iff (hZmeas k).aemeasurable).2 inferInstance
        exact norm_charFun_le_one u)
      (fun k u hu => by
        have := charFun_taylor (hZmeas k) (hZbd k) (hZ0 k) hu
        rw [← hvar k] at this
        exact this) hV t
    simp_rw [div_eq_inv_mul] at this
    convert this using 2
    congr 1
    simp
    ring

/-- The boundary of a closed interval is null for the standard normal law. -/
private theorem gaussian_frontier_Icc_null {a b : ℝ} (hab : a ≤ b) :
    gaussianReal 0 1 (frontier (Set.Icc a b)) = 0 := by
  rw [frontier_Icc hab]
  have : (volume : Measure ℝ) {a, b} = 0 := (Set.toFinite _).measure_zero _
  exact gaussianReal_absolutelyContinuous 0 one_ne_zero this

/-- Portmanteau for intervals: convergence in distribution to a standard normal variable gives
convergence of interval probabilities. -/
private theorem tendsto_Icc_of_tendstoInDistribution {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hT : TendstoInDistribution X atTop Y (fun _ => P) P') {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => P.real {ω | a ≤ X n ω ∧ X n ω ≤ b}) atTop
      (𝓝 (∫ x in a..b, gaussianPDFReal 0 1 x)) := by
  have hnull : (P'.map Y) (frontier (Set.Icc a b)) = 0 := by
    rw [hY.map_eq]; exact gaussian_frontier_Icc_null hab
  have hP : ∀ n, IsProbabilityMeasure (P.map (X n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hT.forall_aemeasurable n)).2 inferInstance
  have hP' : IsProbabilityMeasure (P'.map Y) := inferInstance
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μs := fun n => (⟨P.map (X n), hP n⟩ : ProbabilityMeasure ℝ))
    (μ := (⟨P'.map Y, hP'⟩ : ProbabilityMeasure ℝ))
    hT.tendsto (E := Set.Icc a b) hnull
  have key2 := (ENNReal.tendsto_toReal (measure_ne_top (P'.map Y) (Set.Icc a b))).comp key
  have hlim : ((P'.map Y) (Set.Icc a b)).toReal = ∫ x in a..b, gaussianPDFReal 0 1 x := by
    rw [hY.map_eq, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
        fun x _ => gaussianPDFReal_nonneg 0 1 x),
      intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [← hlim]
  refine key2.congr fun n => ?_
  change ((P.map (X n)) (Set.Icc a b)).toReal = _
  rw [Measure.map_apply_of_aemeasurable (hT.forall_aemeasurable n) measurableSet_Icc,
    measureReal_def]
  rfl

/-- Grinstead–Snell Theorem 9.5 (PR-101), interval form. For independent random variables with
`|X_k| ≤ A` and `s_n² = Var(S_n) → ∞`, the probability that `(S_n - E S_n)/s_n` lies in `[a, b]` tends to
the standard normal integral `∫_a^b φ`. -/
@[kb "grinsteadsnell2006" "Theorem 9.5, p. 353"]
theorem clt_bounded_interval {X : ℕ → Ω → ℝ} {A : ℝ}
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k, ∀ᵐ ω ∂P, |X k ω| ≤ A)
    (hindep : iIndepFun X P)
    (hV : Tendsto (fun n => ∑ k ∈ Finset.range n, Var[X k; P]) atTop atTop) {a b : ℝ}
    (hab : a ≤ b) :
    Tendsto (fun n : ℕ => P.real {ω |
        a ≤ (√(∑ k ∈ Finset.range n, Var[X k; P]))⁻¹ *
          (∑ k ∈ Finset.range n, X k ω - ∑ k ∈ Finset.range n, P[X k]) ∧
        (√(∑ k ∈ Finset.range n, Var[X k; P]))⁻¹ *
          (∑ k ∈ Finset.range n, X k ω - ∑ k ∈ Finset.range n, P[X k]) ≤ b}) atTop
      (𝓝 (∫ x in a..b, gaussianPDFReal 0 1 x)) := by
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨aemeasurable_id, by simp⟩
  exact tendsto_Icc_of_tendstoInDistribution hY (clt_bounded hY hmeas hbd hindep hV) hab

end Main

end UndergradKB.Probability
