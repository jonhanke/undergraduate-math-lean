import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import UndergradKB.Common.Attr
import UndergradKB.Statistics.HomogeneitySizesCLT
import UndergradKB.Statistics.Homogeneity

/-!
# The chi-square test of homogeneity, sample sizes growing in any manner (§11.4)

`Homogeneity.lean` proves the chi-square limit of the statistic of homogeneity when the sample sizes stay in a
fixed ratio. Here the sample from population `i` has size `Nᵢ(n)`, and the only assumption is `Nᵢ(n) → ∞` for every
`i`: the book's test, as it is used, with no relation between the sizes.

`tendstoInDistribution_homogeneityStatisticN`: under the null hypothesis the statistic
`∑ (O_ij - E_ij)²/E_ij` (expected count = row total × column total / grand total) converges in distribution to the
chi-square law with `(r - 1)(c - 1)` degrees of freedom.

Proof. With `Vᵢⱼ = (Oᵢⱼ - Nᵢ bⱼ)/√Nᵢ`, weights `αᵢ = √(Nᵢ/N)` and pooled proportions `B̂ⱼ = Cⱼ/N`, the statistic is
`G(V, α, B̂) = ∑ (Vᵢⱼ - αᵢ ∑ₖ αₖ Vₖⱼ)² / B̂ⱼ`, continuous where `B̂ > 0`. `V` converges in distribution to a Gaussian
table (`tendstoInDistribution_homVectorN`), `B̂ → b` almost surely (strong law), but the weights `α` need not
converge. They stay on the unit sphere, which is compact, so every subsequence has a further subsequence along which
`α → a`; along it Slutsky's theorem gives the limit `‖(I - aaᵀ) Z (I - ββᵀ)‖²`, which has the chi-square law with
`(r - 1)(c - 1)` degrees of freedom whatever the unit vector `a` (`hasLaw_tableProj_chiSquared`). Since the limit
does not depend on the subsequence, the whole sequence converges.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Finset Filter Topology

/-! ### Subsequences -/

section Subseq

variable {E Ω Ω' : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
  [IsProbabilityMeasure P']

/-- A subsequence of a sequence converging in distribution converges in distribution. -/
lemma TendstoInDistribution.comp_tendsto_atTop {X : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    TendstoInDistribution (fun k ↦ X (φ k)) atTop Z (fun _ ↦ P) P' where
  forall_aemeasurable k := h.forall_aemeasurable (φ k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hφ

/-- Convergence in distribution from convergence along a further subsequence of every subsequence. -/
lemma tendstoInDistribution_of_subseq {X : ℕ → Ω → E} {Z : Ω' → E} (hX : ∀ n, AEMeasurable (X n) P)
    (hZ : AEMeasurable Z P')
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, TendstoInDistribution (fun k ↦ X (ns (ms k))) atTop Z (fun _ ↦ P) P') :
    TendstoInDistribution X atTop Z (fun _ ↦ P) P' where
  forall_aemeasurable := hX
  aemeasurable_limit := hZ
  tendsto := tendsto_of_subseq_tendsto fun ns hns ↦ by
    obtain ⟨ms, hms⟩ := h ns hns
    exact ⟨ms, hms.tendsto⟩

end Subseq

section HomogeneityN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {r c : ℕ}

/-- The column total `C_j = ∑ᵢ O_ij`. -/
noncomputable def homColTotalN (Y : Fin r → ℕ → Ω → Fin c) (N : Fin r → ℕ → ℕ) (n : ℕ) (j : Fin c) (ω : Ω) :
    ℝ :=
  ∑ i, homCountN Y N n i j ω

/-- The expected count `E_ij = (row total)(column total)/(grand total) = Nᵢ C_j / ∑ₖ Nₖ`. -/
noncomputable def homExpectedN (Y : Fin r → ℕ → Ω → Fin c) (N : Fin r → ℕ → ℕ) (n : ℕ) (i : Fin r) (j : Fin c)
    (ω : Ω) : ℝ :=
  (N i n : ℝ) * homColTotalN Y N n j ω / ∑ i', (N i' n : ℝ)

/-- The test statistic of homogeneity `∑_{i,j} (O_ij - E_ij)² / E_ij` for samples of sizes `N i n`. -/
noncomputable def homogeneityStatisticN (Y : Fin r → ℕ → Ω → Fin c) (N : Fin r → ℕ → ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, (homCountN Y N n i j ω - homExpectedN Y N n i j ω) ^ 2 / homExpectedN Y N n i j ω

lemma measurable_homogeneityStatisticN {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (N : Fin r → ℕ → ℕ) (n : ℕ) : Measurable (homogeneityStatisticN Y N n) := by
  have hC : ∀ j, Measurable fun ω ↦ homColTotalN Y N n j ω := fun j ↦
    Finset.measurable_sum _ fun i _ ↦ measurable_homCountN hmeas N n i j
  have hE : ∀ i j, Measurable fun ω ↦ homExpectedN Y N n i j ω := fun i j ↦
    ((hC j).const_mul _).div_const _
  unfold homogeneityStatisticN
  exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    (((measurable_homCountN hmeas N n i j).sub (hE i j)).pow_const 2).div (hE i j)

/-- The size weights `αᵢ = √(Nᵢ / ∑ₖ Nₖ)`. -/
noncomputable def homWeight (N : Fin r → ℕ → ℕ) (n : ℕ) : Fin r → ℝ :=
  fun i ↦ √((N i n : ℝ) / ∑ i', (N i' n : ℝ))

/-- `G(v, α, β̂) = ∑_{i,j} (v_ij - αᵢ ∑ₖ αₖ v_kj)² / max(β̂_j, δ)`; continuous for `δ > 0`. -/
noncomputable def homGN (δ : ℝ) (q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ))) : ℝ :=
  ∑ i, ∑ j, (q.1 (i, j) - q.2.1 i * ∑ k, q.2.1 k * q.1 (k, j)) ^ 2 / max (q.2.2 j) δ

lemma continuous_homGN {δ : ℝ} (hδ : 0 < δ) : Continuous (homGN (r := r) (c := c) δ) := by
  unfold homGN
  refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
  have hx : ∀ x : Fin r × Fin c,
      Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦ q.1 x :=
    fun x ↦ (PiLp.continuous_apply 2 _ x).comp continuous_fst
  have ha : ∀ k : Fin r,
      Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦ q.2.1 k :=
    fun k ↦ (continuous_apply k).comp (continuous_fst.comp continuous_snd)
  have e1 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦
      (q.1 (i, j) - q.2.1 i * ∑ k, q.2.1 k * q.1 (k, j) : ℝ) :=
    (hx (i, j)).sub ((ha i).mul (continuous_finsetSum
      (f := fun k (q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ))) ↦ q.2.1 k * q.1 (k, j))
      univ fun k _ ↦ (ha k).mul (hx (k, j))))
  have e2 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦
      (max (q.2.2 j) δ : ℝ) :=
    ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).max continuous_const
  exact (e1.pow 2).div e2 fun q ↦ (lt_of_lt_of_le hδ (le_max_right _ _)).ne'

/-- The algebraic identity behind the eventual equality of the statistic and `G`. -/
private lemma homN_term_identity {s T O Ni Cj b : ℝ} (hs2 : s ^ 2 = Ni) (hs : s ≠ 0) (hT : T ≠ 0)
    (hC : Cj ≠ 0) :
    ((O - Ni * b) / s - s * (Cj - T * b) / T) ^ 2 / (Cj / T) = (O - Ni * Cj / T) ^ 2 / (Ni * Cj / T) := by
  subst hs2
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- Once every sample is non-empty and every pooled proportion `C_j/N` is at least `δ`, the statistic equals
`G(V, α, B̂)`. -/
lemma homogeneityStatisticN_eq_homGN {N : Fin r → ℕ → ℕ} {n : ℕ} (hN : ∀ i, N i n ≠ 0)
    (hTpos : 0 < ∑ i, (N i n : ℝ)) (b : Fin c → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (Y : Fin r → ℕ → Ω → Fin c) (ω : Ω)
    (hle : ∀ j, δ ≤ homColTotalN Y N n j ω / ∑ i, (N i n : ℝ)) :
    homogeneityStatisticN Y N n ω = homGN δ (homVectorN Y N b n ω,
      (homWeight N n, fun j ↦ homColTotalN Y N n j ω / ∑ i, (N i n : ℝ))) := by
  set T : ℝ := ∑ i, (N i n : ℝ) with hT_def
  have hNpos : ∀ i, (0 : ℝ) < N i n := fun i ↦ Nat.cast_pos.2 (Nat.pos_of_ne_zero (hN i))
  have hTnn : 0 ≤ T := sum_nonneg fun i _ ↦ (hNpos i).le
  have hT : T ≠ 0 := hTpos.ne'
  have hsq : ∀ i, √(N i n : ℝ) ≠ 0 := fun i ↦ (sqrt_pos.2 (hNpos i)).ne'
  have hrT : √T ≠ 0 := (sqrt_pos.2 hTpos).ne'
  have hv : ∀ i j, (homVectorN Y N b n ω) (i, j) =
      (homCountN Y N n i j ω - (N i n : ℝ) * b j) / √(N i n : ℝ) := fun i j ↦ by
    simp only [homVectorN, WithLp.ofLp_toLp]
  have hcol : ∀ i j, homWeight N n i * ∑ k, homWeight N n k * (homVectorN Y N b n ω) (k, j) =
      √(N i n : ℝ) * (homColTotalN Y N n j ω - T * b j) / T := by
    intro i j
    have hk : ∀ k, homWeight N n k * (homVectorN Y N b n ω) (k, j) =
        (homCountN Y N n k j ω - (N k n : ℝ) * b j) / √T := by
      intro k
      rw [hv, homWeight, Real.sqrt_div' _ hTnn]
      have := hsq k
      field_simp
    simp_rw [hk]
    rw [← sum_div, sum_sub_distrib, ← sum_mul, homWeight, Real.sqrt_div' _ hTnn]
    unfold homColTotalN
    rw [← hT_def]
    field_simp
    rw [sq_sqrt hTnn]
  unfold homogeneityStatisticN homGN homExpectedN
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only
  rw [hcol, hv, max_eq_left (hle j), ← hT_def]
  have hCpos : homColTotalN Y N n j ω / T ≠ 0 := (lt_of_lt_of_le hδ (hle j)).ne'
  have hC : homColTotalN Y N n j ω ≠ 0 := fun h ↦ hCpos (by rw [h, zero_div])
  have e := homN_term_identity (O := homCountN Y N n i j ω) (b := b j) (sq_sqrt (hNpos i).le) (hsq i) hT hC
  exact e.symm

/-- At the limit, `G(Gaussian table, a, b) = ‖(I - aaᵀ) Z (I - ββᵀ)‖²` with `β_j = √b_j`. -/
lemma homGN_homLimit {b : Fin c → ℝ} (hb : ∀ j, 0 < b j) {δ : ℝ} (hδ : ∀ j, δ ≤ b j) (a : Fin r → ℝ)
    (z : Fin r × Fin c → ℝ) :
    homGN δ (homLimit (fun _ ↦ 1) b z, (a, b)) = ∑ i, ∑ j, tableProj a (fun j ↦ √(b j)) z i j ^ 2 := by
  set β : Fin c → ℝ := fun j ↦ √(b j) with hβ_def
  have hβ2 : ∀ j, β j ^ 2 = b j := fun j ↦ sq_sqrt (hb j).le
  have hβ0 : ∀ j, β j ≠ 0 := fun j ↦ (sqrt_pos.2 (hb j)).ne'
  set w : Fin r → Fin c → ℝ := fun i j ↦ z (i, j) - β j * ∑ l, β l * z (i, l) with hw_def
  have hv : ∀ i j, (homLimit (fun _ ↦ 1) b z) (i, j) = β j * w i j := by
    intro i j
    have hβapp : ∀ l, √(b l) = β l := fun l ↦ rfl
    simp only [homLimit, WithLp.ofLp_toLp, hβapp, Nat.cast_one, Real.sqrt_one, one_mul, hw_def]
    rw [← hβ2 j]
    ring
  have hproj : ∀ i j, w i j - a i * ∑ k, a k * w k j = tableProj a β z i j := by
    intro i j
    simp only [hw_def, tableProj, mul_sub, sum_sub_distrib]
    have h1 : ∑ k, a k * (β j * ∑ l, β l * z (k, l)) = β j * ∑ k, ∑ l, a k * β l * z (k, l) := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun l _ ↦ by ring
    rw [h1]
    ring
  unfold homGN
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only
  rw [max_eq_left (hδ j), hv]
  have hs : ∑ k, a k * (β j * w k j) = β j * ∑ k, a k * w k j := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ ↦ by ring
  simp_rw [hv]
  rw [hs, ← hproj, ← hβ2 j]
  have := hβ0 j
  field_simp

/-- **The chi-square test of homogeneity, sizes growing in any manner (§11.4, ST-099).** Samples are drawn
independently from `r ≥ 2` populations, the sample from population `i` having size `N i n`; each individual falls
in one of `c ≥ 2` categories. Under the null hypothesis that every population has the same category probabilities
`b_j > 0` (all draws independent, the draws from one population identically distributed with
`P(category j) = b_j`), if every sample size tends to infinity (in any manner, with no relation between the
populations) then the statistic `∑_{i,j} (O_ij - E_ij)² / E_ij` with `E_ij = (row total)(column total)/(grand total)`
converges in distribution to the chi-square law with `(r - 1)(c - 1)` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.4, p. 589"]
theorem tendstoInDistribution_homogeneityStatisticN [IsProbabilityMeasure P] {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] (hr : 2 ≤ r) (hc : 2 ≤ c)
    {N : Fin r → ℕ → ℕ} (hN : ∀ i, Tendsto (N i) atTop atTop)
    {b : Fin c → ℝ} (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (hind : iIndepFun (fun x : Fin r × ℕ ↦ Y x.1 x.2) P) (hident : ∀ i m, IdentDistrib (Y i m) (Y i 0) P P)
    (hprob : ∀ i j, P.real {ω | Y i 0 ω = j} = b j)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) P') :
    TendstoInDistribution (homogeneityStatisticN Y N) atTop W (fun _ ↦ P) P' := by
  -- a positive lower bound for the category probabilities
  have hne : (univ : Finset (Fin c)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  set δ : ℝ := univ.inf' hne b / 2 with hδ_def
  have hinf : 0 < univ.inf' hne b := (lt_inf'_iff hne).2 fun j _ ↦ hb j
  have hδ : 0 < δ := half_pos hinf
  have hδlt : ∀ j, δ < b j := fun j ↦ lt_of_lt_of_le (half_lt_self hinf) (inf'_le b (mem_univ j))
  -- eventually every sample is non-empty
  have hNev : ∀ᶠ n in atTop, ∀ i, N i n ≠ 0 :=
    eventually_all.2 fun i ↦ ((hN i).eventually_ge_atTop 1).mono fun n hn ↦ by omega
  -- the pooled proportions converge almost surely
  set T : ℕ → ℝ := fun n ↦ ∑ i, (N i n : ℝ) with hT_def
  set B : ℕ → Ω → Fin c → ℝ := fun n ω j ↦ homColTotalN Y N n j ω / T n with hB_def
  have hBmeas : ∀ n, Measurable (B n) := fun n ↦ measurable_pi_iff.2 fun j ↦
    (Finset.measurable_sum _ fun i _ ↦ measurable_homCountN hmeas N n i j).div_const _
  have hcell : ∀ i j, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ homCountN Y N n i j ω / (N i n : ℝ)) atTop (𝓝 (b j)) := by
    intro i j
    have hindi : iIndepFun (Y i) P := hind.precomp (g := fun m : ℕ ↦ (i, m)) fun m m' h ↦ by
      simpa using h
    have h := ae_tendsto_average (hmeas i) hindi (hident i)
      (f := fun y : Fin c ↦ if y = j then (1 : ℝ) else 0) (measurable_of_finite _) (M := 1)
      fun y ↦ by split_ifs <;> simp
    have hint : ∫ ω, (fun y : Fin c ↦ if y = j then (1 : ℝ) else 0) (Y i 0 ω) ∂P = b j := by
      refine (integral_comp_fin (P := P) (hmeas i 0) (fun y : Fin c ↦ if y = j then (1 : ℝ) else 0)).trans ?_
      simp_rw [hprob i]
      simp
    filter_upwards [h] with ω hω
    rw [hint] at hω
    refine (hω.comp (hN i)).congr fun n ↦ ?_
    simp only [Function.comp, homCountN_eq]
  have hBae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ B n ω) atTop (𝓝 b) := by
    have hall : ∀ᵐ ω ∂P, ∀ i j,
        Tendsto (fun n : ℕ ↦ homCountN Y N n i j ω / (N i n : ℝ)) atTop (𝓝 (b j)) :=
      ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ hcell i j
    filter_upwards [hall] with ω hω
    refine tendsto_pi_nhds.2 fun j ↦ ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsum : Tendsto (fun n ↦ ∑ i, |homCountN Y N n i j ω / (N i n : ℝ) - b j|) atTop (𝓝 0) := by
      have := tendsto_finsetSum (univ : Finset (Fin r)) fun i _ ↦
        ((hω i j).sub_const (b j)).abs
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hsum
    filter_upwards [hNev] with n hn
    have hNpos : ∀ i, (0 : ℝ) < N i n := fun i ↦ Nat.cast_pos.2 (Nat.pos_of_ne_zero (hn i))
    have i0 : Fin r := ⟨0, by omega⟩
    have hTpos : 0 < T n := sum_pos (fun i _ ↦ hNpos i) ⟨i0, mem_univ _⟩
    have hrepr : B n ω j - b j = ∑ i, (N i n : ℝ) / T n * (homCountN Y N n i j ω / (N i n : ℝ) - b j) := by
      have e1 : ∀ i, (N i n : ℝ) / T n * (homCountN Y N n i j ω / (N i n : ℝ) - b j) =
          homCountN Y N n i j ω / T n - (N i n : ℝ) / T n * b j := fun i ↦ by
        have := (hNpos i).ne'
        field_simp
      have hsumN : ∑ i, (N i n : ℝ) / T n = 1 := by
        rw [← sum_div]
        exact div_self hTpos.ne'
      simp_rw [e1]
      rw [sum_sub_distrib, ← sum_mul, hsumN, one_mul, ← sum_div]
      rfl
    rw [Real.norm_eq_abs, hrepr]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    rw [abs_mul, abs_of_nonneg (div_nonneg (hNpos i).le hTpos.le)]
    have hle1 : (N i n : ℝ) / T n ≤ 1 := by
      rw [div_le_one hTpos]
      exact single_le_sum (f := fun i ↦ (N i n : ℝ)) (fun k _ ↦ (hNpos k).le) (mem_univ i)
    exact mul_le_of_le_one_left (abs_nonneg _) hle1
  -- the vector, the function `G` and its arguments
  set V := homVectorN Y N b with hV_def
  have hVmeas : ∀ n, Measurable (V n) := measurable_homVectorN hmeas N b
  set D : ℕ → Ω → ℝ := fun n ω ↦ homGN δ (V n ω, (homWeight N n, B n ω)) with hD_def
  have hDmeas : ∀ n, Measurable (D n) := fun n ↦
    (continuous_homGN hδ).measurable.comp ((hVmeas n).prodMk (measurable_const.prodMk (hBmeas n)))
  have hvec := tendstoInDistribution_homVectorN hN hb hbsum hmeas hind hident hprob
  -- the weights stay in a compact set and have unit norm
  have hαmem : ∀ n, homWeight N n ∈ Set.Icc (0 : Fin r → ℝ) 1 := by
    intro n
    refine ⟨fun i ↦ sqrt_nonneg _, fun i ↦ ?_⟩
    show √((N i n : ℝ) / ∑ i', (N i' n : ℝ)) ≤ 1
    rw [sqrt_le_one]
    rcases eq_or_lt_of_le (sum_nonneg fun k _ ↦ Nat.cast_nonneg (N k n) : (0 : ℝ) ≤ ∑ i', (N i' n : ℝ))
      with h0 | hpos
    · rw [← h0, div_zero]; exact zero_le_one
    · rw [div_le_one hpos]
      exact single_le_sum (f := fun i ↦ (N i n : ℝ)) (fun k _ ↦ Nat.cast_nonneg _) (mem_univ i)
  have hαnorm : ∀ᶠ n in atTop, ∑ i, homWeight N n i ^ 2 = 1 := by
    filter_upwards [hNev] with n hn
    have hpos : (0 : ℝ) < ∑ i', (N i' n : ℝ) :=
      sum_pos (fun i _ ↦ Nat.cast_pos.2 (Nat.pos_of_ne_zero (hn i))) ⟨⟨0, by omega⟩, mem_univ _⟩
    simp only [homWeight]
    simp_rw [sq_sqrt (div_nonneg (Nat.cast_nonneg _) hpos.le)]
    rw [← sum_div, div_self hpos.ne']
  -- convergence of `G(V, α, B̂)` along subsequences
  have hlaw : ∀ a : Fin r → ℝ, ∑ i, a i ^ 2 = 1 →
      (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1).map
        (fun z ↦ homGN δ (homLimit (fun _ ↦ 1) b z, (a, b))) =
        chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1)) := by
    intro a ha
    have hβ : ∑ j, (fun j ↦ √(b j)) j ^ 2 = 1 := by
      simp_rw [sq_sqrt (hb _).le]
      exact hbsum
    rw [← (hasLaw_tableProj_chiSquared hr hc a _ ha hβ).map_eq]
    congr 1
    funext z
    exact homGN_homLimit hb (fun j ↦ (hδlt j).le) a z
  have hD : TendstoInDistribution D atTop W (fun _ ↦ P) P' := by
    refine tendstoInDistribution_of_subseq (fun n ↦ (hDmeas n).aemeasurable) hW.aemeasurable
      fun ns hns ↦ ?_
    obtain ⟨a, -, φ, hφ, hαφ⟩ := (isCompact_Icc (a := (0 : Fin r → ℝ)) (b := 1)).tendsto_subseq
      (x := fun k ↦ homWeight N (ns k)) fun k ↦ hαmem (ns k)
    have hψ : Tendsto (fun k ↦ ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
    have ha : ∑ i, a i ^ 2 = 1 := by
      have hc1 : Tendsto (fun k ↦ ∑ i, homWeight N (ns (φ k)) i ^ 2) atTop (𝓝 (∑ i, a i ^ 2)) :=
        tendsto_finsetSum _ fun i _ ↦ ((continuous_apply i).continuousAt.tendsto.comp hαφ).pow 2
      exact tendsto_nhds_unique hc1 (tendsto_const_nhds.congr' ((hψ.eventually hαnorm).mono
        fun k hk ↦ hk.symm))
    refine ⟨φ, ?_⟩
    have hYm : TendstoInMeasure P (fun k ω ↦ (homWeight N (ns (φ k)), B (ns (φ k)) ω)) atTop
        (fun _ ↦ (a, b)) := by
      refine tendstoInMeasure_of_tendsto_ae (fun k ↦ (measurable_const.prodMk
        (hBmeas (ns (φ k)))).aestronglyMeasurable) ?_
      filter_upwards [hBae] with ω hω
      exact hαφ.prodMk_nhds (hω.comp hψ)
    have hsl := (TendstoInDistribution.comp_tendsto_atTop hvec hψ
      ).continuous_comp_prodMk_of_tendstoInMeasure_const
      (continuous_homGN hδ) hYm fun k ↦ (measurable_const.prodMk (hBmeas (ns (φ k)))).aemeasurable
    exact TendstoInDistribution.of_map_eq_limit hsl hW.aemeasurable (by rw [hW.map_eq, hlaw a ha])
  -- the statistic and `G` agree eventually, almost surely
  have hdiff : TendstoInMeasure P (homogeneityStatisticN Y N - D) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((measurable_homogeneityStatisticN hmeas N n).sub (hDmeas n)).aestronglyMeasurable) ?_
    filter_upwards [hBae] with ω hω
    have h1 : ∀ j, ∀ᶠ n in atTop, δ ≤ B n ω j := fun j ↦
      (((continuous_apply j).continuousAt.tendsto.comp hω).eventually (lt_mem_nhds (hδlt j))).mono
        fun n hn ↦ hn.le
    have h2 : ∀ᶠ n in atTop, ∀ j, δ ≤ B n ω j := eventually_all.2 h1
    have hev : ∀ᶠ n in atTop, (homogeneityStatisticN Y N - D) n ω = 0 := by
      filter_upwards [h2, hNev] with n hn hn1
      rw [Pi.sub_apply, Pi.sub_apply, sub_eq_zero]
      exact homogeneityStatisticN_eq_homGN hn1
        (sum_pos (fun i _ ↦ Nat.cast_pos.2 (Nat.pos_of_ne_zero (hn1 i))) ⟨⟨0, by omega⟩, mem_univ _⟩) b hδ Y ω hn
    exact tendsto_const_nhds.congr' (hev.mono fun n hn ↦ hn.symm)
  exact tendstoInDistribution_of_tendstoInMeasure_sub (homogeneityStatisticN Y N) W hD hdiff
    fun n ↦ (measurable_homogeneityStatisticN hmeas N n).aemeasurable

end HomogeneityN

end UndergradKB.Statistics
