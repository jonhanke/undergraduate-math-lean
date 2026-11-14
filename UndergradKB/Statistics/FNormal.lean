import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.StrongLaw
import UndergradKB.Common.Attr
import UndergradKB.Statistics.DistributionLimits
import UndergradKB.Statistics.FDistribution
import UndergradKB.Statistics.TwoSample

/-!
# The F law is approximately normal for many degrees of freedom

OpenStax *Introductory Statistics 2e*, §13.3 (row ST-116, a recorded loose end): as the degrees of freedom of
the numerator and of the denominator both grow, the F curve approaches a normal curve.

Let `Z₀, Z₁, …` and `W₀, W₁, …` be independent standard normal variables, and
`F = ((Z₀² + ⋯ + Z_{m-1}²)/m) / ((W₀² + ⋯ + W_{n-1}²)/n)`, which has the F law with `m` and `n` degrees of freedom
(`hasLaw_fRatio_normalSamples`). When `m` and `n` tend to infinity, in any manner, `(F - 1)/√(2/m + 2/n)` converges in
distribution to a standard normal variable (`tendstoInDistribution_fStatistic`): the F law is approximately normal
with mean `1` and variance `2/m + 2/n`.

Proof: the numerator and the denominator are sample means of the squares `Zᵢ²`, `Wⱼ²` (mean `1`, variance `2`), so
the two-sample central limit theorem for arbitrary sizes (`tendstoInDistribution_two_sample_means`) gives the
normal limit of the difference of numerator and denominator, scaled by `√(2/m + 2/n)`; the denominator tends to `1`
almost surely by the strong law, and Slutsky's theorem divides by it.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Filter Topology

section FNormal

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'}

/-- **The F statistic of two normal samples has the F law (§13.3).** If `Z₀, Z₁, …` and `W₀, W₁, …` are
independent standard normal variables, then for `m, n ≥ 1` the ratio
`((Z₀² + ⋯ + Z_{m-1}²)/m) / ((W₀² + ⋯ + W_{n-1}²)/n)` has the F law with `m` and `n` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem hasLaw_fRatio_normalSamples [IsProbabilityMeasure P] {Z W : ℕ → Ω → ℝ} (hmZ : ∀ i, Measurable (Z i))
    (hmW : ∀ j, Measurable (W j)) (hind : iIndepFun (Sum.elim Z W) P)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) (hW : ∀ j, HasLaw (W j) (gaussianReal 0 1) P)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    HasLaw (fun ω ↦ ((∑ i ∈ Finset.range m, Z i ω ^ 2) / m) / ((∑ j ∈ Finset.range n, W j ω ^ 2) / n))
      (fDistribution m n) P := by
  classical
  have hZind : iIndepFun Z P := hind.precomp (g := Sum.inl) Sum.inl_injective
  have hWind : iIndepFun W P := hind.precomp (g := Sum.inr) Sum.inr_injective
  have hU : HasLaw (fun ω ↦ ∑ i ∈ Finset.range m, Z i ω ^ 2) (chiSquared m) P := by
    simpa using hasLaw_sum_sq_chiSquared (s := Finset.range m) (Finset.nonempty_range_iff.2 hm.ne')
      hmZ hZind fun i _ ↦ hZ i
  have hV : HasLaw (fun ω ↦ ∑ j ∈ Finset.range n, W j ω ^ 2) (chiSquared n) P := by
    simpa using hasLaw_sum_sq_chiSquared (s := Finset.range n) (Finset.nonempty_range_iff.2 hn.ne')
      hmW hWind fun j _ ↦ hW j
  set S : Finset (ℕ ⊕ ℕ) := (Finset.range m).map Function.Embedding.inl with hS
  set T : Finset (ℕ ⊕ ℕ) := (Finset.range n).map Function.Embedding.inr with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [hS, hT, Finset.mem_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at ha hb
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, hj⟩ := hb
    exact Sum.inr_ne_inl hj
  have hmeas : ∀ i, Measurable (Sum.elim Z W i) := by
    intro i
    cases i with
    | inl i => exact hmZ i
    | inr j => exact hmW j
  have hi := hind.indepFun_finset S T hST hmeas
  have hφ : Measurable fun x : S → ℝ ↦ ∑ i, x i ^ 2 := by fun_prop
  have hψ : Measurable fun x : T → ℝ ↦ ∑ j, x j ^ 2 := by fun_prop
  have hUV : IndepFun (fun ω ↦ ∑ i ∈ Finset.range m, Z i ω ^ 2)
      (fun ω ↦ ∑ j ∈ Finset.range n, W j ω ^ 2) P := by
    have h := hi.comp hφ hψ
    have e1 : ((fun x : S → ℝ ↦ ∑ i, x i ^ 2) ∘ fun ω (i : S) ↦ Sum.elim Z W i ω) =
        fun ω ↦ ∑ i ∈ Finset.range m, Z i ω ^ 2 := by
      funext ω
      simp only [Function.comp_apply]
      rw [Finset.sum_coe_sort S (fun i ↦ Sum.elim Z W i ω ^ 2), hS, Finset.sum_map]
      rfl
    have e2 : ((fun x : T → ℝ ↦ ∑ j, x j ^ 2) ∘ fun ω (j : T) ↦ Sum.elim Z W j ω) =
        fun ω ↦ ∑ j ∈ Finset.range n, W j ω ^ 2 := by
      funext ω
      simp only [Function.comp_apply]
      rw [Finset.sum_coe_sort T (fun j ↦ Sum.elim Z W j ω ^ 2), hT, Finset.sum_map]
      rfl
    rw [e1, e2] at h
    exact h
  exact hasLaw_fDistribution (by exact_mod_cast hm) (by exact_mod_cast hn) hU hV hUV

/-- **The F law is approximately normal for many degrees of freedom (§13.3, ST-116).** Let `Z₀, Z₁, …` and
`W₀, W₁, …` be independent standard normal variables, and let the degrees of freedom `m k`, `n k` both tend to
infinity, in any manner. The F statistic
`F_k = ((Z₀² + ⋯ + Z_{m_k-1}²)/m_k) / ((W₀² + ⋯ + W_{n_k-1}²)/n_k)`, which has the F law with `m_k` and `n_k`
degrees of freedom (`hasLaw_fRatio_normalSamples`), satisfies `(F_k - 1)/√(2/m_k + 2/n_k) → N(0, 1)` in distribution:
for large degrees of freedom the F curve is close to a normal curve with mean `1` and variance
`2/m + 2/n`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem tendstoInDistribution_fStatistic [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z W : ℕ → Ω → ℝ} {G : Ω' → ℝ} (hG : HasLaw G (gaussianReal 0 1) P')
    (hmZ : ∀ i, Measurable (Z i)) (hmW : ∀ j, Measurable (W j)) (hind : iIndepFun (Sum.elim Z W) P)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) (hW : ∀ j, HasLaw (W j) (gaussianReal 0 1) P)
    {m n : ℕ → ℕ} (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    TendstoInDistribution
      (fun k ω ↦ (((∑ i ∈ Finset.range (m k), Z i ω ^ 2) / m k) /
          ((∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k) - 1) / √(2 / m k + 2 / n k))
      atTop G (fun _ ↦ P) P' := by
  classical
  obtain ⟨hμX, hvX, hLX⟩ := sq_gaussian_moments (hZ 0)
  obtain ⟨hμY, hvY, hLY⟩ := sq_gaussian_moments (hW 0)
  have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hindXY : iIndepFun (Sum.elim (fun i ω ↦ Z i ω ^ 2) (fun j ω ↦ W j ω ^ 2)) P := by
    have h : Sum.elim (fun i ω ↦ Z i ω ^ 2) (fun j ω ↦ W j ω ^ 2) =
        fun i ω ↦ Sum.elim Z W i ω ^ 2 := by
      funext i ω
      cases i <;> rfl
    rw [h]
    exact hind.comp (fun _ x ↦ x ^ 2) fun _ ↦ by fun_prop
  have hidX : ∀ i, IdentDistrib (fun ω ↦ Z i ω ^ 2) (fun ω ↦ Z 0 ω ^ 2) P P := fun i ↦
    (hasLaw_sq_chiSquared_one (hZ i)).identDistrib (hasLaw_sq_chiSquared_one (hZ 0))
  have hidY : ∀ j, IdentDistrib (fun ω ↦ W j ω ^ 2) (fun ω ↦ W 0 ω ^ 2) P P := fun j ↦
    (hasLaw_sq_chiSquared_one (hW j)).identDistrib (hasLaw_sq_chiSquared_one (hW 0))
  have hT := tendstoInDistribution_two_sample_means (σA := √2) (σB := √2) (by positivity) (by positivity)
    hG hLX hLY hμX hμY (by rw [hvX, hsq]) (by rw [hvY, hsq]) hindXY hidX hidY hm hn
  -- the denominator tends to `1` almost surely (strong law)
  have hVae : ∀ᵐ ω ∂P, Tendsto (fun k ↦ (∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k) atTop (𝓝 1) := by
    have h := strong_law_ae_real (fun j ω ↦ W j ω ^ 2) (hLY.integrable one_le_two)
      (fun i j hij ↦ hindXY.indepFun (Sum.inr_injective.ne hij)) hidY
    filter_upwards [h] with ω hω
    rw [hμY] at hω
    exact hω.comp hn
  have hSU : ∀ k, Measurable fun ω ↦ ∑ i ∈ Finset.range (m k), Z i ω ^ 2 :=
    fun k ↦ Finset.measurable_fun_sum _ fun i _ ↦ (hmZ i).pow_const 2
  have hSV : ∀ k, Measurable fun ω ↦ ∑ j ∈ Finset.range (n k), W j ω ^ 2 :=
    fun k ↦ Finset.measurable_fun_sum _ fun j _ ↦ (hmW j).pow_const 2
  have hVm : ∀ k, Measurable fun ω ↦ (∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k :=
    fun k ↦ (hSV k).div_const _
  have hVconv : TendstoInMeasure P (fun k ω ↦ (∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k) atTop
      (fun _ ↦ 1) :=
    tendstoInMeasure_of_tendsto_ae (fun k ↦ (hVm k).aestronglyMeasurable) hVae
  -- Slutsky's theorem: divide by the denominator, kept away from `0`
  set g : ℝ × ℝ → ℝ := fun z ↦ z.1 / max z.2 (1 / 2) with hg
  have hgc : Continuous g := by
    refine continuous_fst.div (continuous_snd.max continuous_const) fun z ↦ ?_
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)).ne'
  have hsl := hT.continuous_comp_prodMk_of_tendstoInMeasure_const hgc hVconv
    fun k ↦ (hVm k).aemeasurable
  have hgG : (fun ω ↦ g (G ω, 1)) = G := by
    funext ω
    simp only [hg]
    rw [max_eq_left (by norm_num), div_one]
  rw [hgG] at hsl
  have hFm : ∀ k, Measurable fun ω ↦ (((∑ i ∈ Finset.range (m k), Z i ω ^ 2) / m k) /
      ((∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k) - 1) / √(2 / m k + 2 / n k) := by
    intro k
    have := hSU k; have := hSV k
    fun_prop
  have hgm : ∀ k, Measurable fun ω ↦ g (((∑ i ∈ Finset.range (m k), Z i ω ^ 2) / m k -
      (∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k - (1 - 1)) / √(√2 ^ 2 / m k + √2 ^ 2 / n k),
      (∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k) := by
    intro k
    have := hSU k; have := hSV k
    exact hgc.measurable.comp (by fun_prop)
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hsl ?_ fun k ↦ (hFm k).aemeasurable
  refine tendstoInMeasure_of_tendsto_ae (fun k ↦ ((hFm k).sub (hgm k)).aestronglyMeasurable) ?_
  filter_upwards [hVae] with ω hω
  have hev : ∀ᶠ k in atTop, 1 / 2 ≤ (∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k :=
    (hω.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono fun _ h ↦ h.le
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev, hm.eventually_ge_atTop 1, hn.eventually_ge_atTop 1] with k hk hka hkb
  have ha' : (0 : ℝ) < m k := by exact_mod_cast hka
  have hb' : (0 : ℝ) < n k := by exact_mod_cast hkb
  have hV0 : (∑ j ∈ Finset.range (n k), W j ω ^ 2) / n k ≠ 0 := by
    have : (0 : ℝ) < 1 / 2 := by norm_num
    exact (lt_of_lt_of_le this hk).ne'
  have hs0 : √(2 / m k + 2 / n k) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hVne : ∑ j ∈ Finset.range (n k), W j ω ^ 2 ≠ 0 := (div_ne_zero_iff.1 hV0).1
  simp only [Pi.sub_apply, Pi.zero_apply, hg]
  rw [max_eq_left hk, hsq, sub_self, sub_zero]
  generalize √(2 / m k + 2 / n k) = s at hs0 ⊢
  generalize ∑ j ∈ Finset.range (n k), W j ω ^ 2 = V at hVne ⊢
  generalize ∑ i ∈ Finset.range (m k), Z i ω ^ 2 = U
  field_simp
  ring

end FNormal

end UndergradKB.Statistics
