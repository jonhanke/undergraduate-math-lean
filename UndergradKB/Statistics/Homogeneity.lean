import UndergradKB.Common.Attr
import UndergradKB.Statistics.HomogeneityCLT
import UndergradKB.Statistics.IndependenceTest

/-!
# The chi-square test of homogeneity (OpenStax *Introductory Statistics 2e*, §11.4)

Independent samples are drawn from `r ≥ 2` populations and each individual is classified in one of `c ≥ 2`
categories. The sample from population `i` has size `sᵢ n` (sizes in a fixed ratio `s₁ : ⋯ : s_r`), `O_ij` is the
observed count of category `j` in sample `i`, the column total is `C_j = ∑ᵢ O_ij`, the grand total is
`N = ∑ᵢ sᵢ n` and the expected count is `E_ij = (sᵢ n) C_j / N` (row total times column total over grand total). The
test of homogeneity uses the same statistic `∑ (O_ij - E_ij)² / E_ij` as the test of independence and the same
`(r - 1)(c - 1)` degrees of freedom.

`tendstoInDistribution_homogeneityStatistic`: under the null hypothesis (every population has the same category
probabilities `b_j > 0`) the statistic converges in distribution to the chi-square law with `(r - 1)(c - 1)` degrees
of freedom.

Proof. The table `(O_ij - sᵢ n b_j)/√n` converges in distribution to `√sᵢ` times the row projections of a Gaussian
table (`tendstoInDistribution_homVector`); the pooled proportions `C_j/N` converge almost surely to `b_j` (strong
law); eventually the statistic is a continuous function of these two (the pooled proportions stay away from `0`), so
Slutsky's theorem gives the limit, which is again `‖(I - ααᵀ) Z (I - ββᵀ)‖²` (`hasLaw_tableProj_chiSquared`), now with
`αᵢ = √(sᵢ/∑ s)` and `β_j = √b_j`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Finset Filter Topology

section Homogeneity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {r c : ℕ}

/-- The column total `C_j = ∑ᵢ O_ij` (all samples together). -/
noncomputable def homColTotal (Y : Fin r → ℕ → Ω → Fin c) (sz : Fin r → ℕ) (n : ℕ) (j : Fin c) (ω : Ω) : ℝ :=
  ∑ i, homCount Y sz n i j ω

/-- The expected count `E_ij = (row total)(column total)/(grand total)`: the row total is the sample size `sᵢ n`
and the grand total is `∑ᵢ sᵢ n`. -/
noncomputable def homExpected (Y : Fin r → ℕ → Ω → Fin c) (sz : Fin r → ℕ) (n : ℕ) (i : Fin r) (j : Fin c)
    (ω : Ω) : ℝ :=
  ((sz i : ℝ) * n) * homColTotal Y sz n j ω / ∑ i', (sz i' : ℝ) * n

/-- The test statistic of homogeneity `∑_{i,j} (O_ij - E_ij)² / E_ij` (§11.4). -/
noncomputable def homogeneityStatistic (Y : Fin r → ℕ → Ω → Fin c) (sz : Fin r → ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, (homCount Y sz n i j ω - homExpected Y sz n i j ω) ^ 2 / homExpected Y sz n i j ω

lemma measurable_homCount {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (sz : Fin r → ℕ) (n : ℕ) (i : Fin r) (j : Fin c) : Measurable fun ω ↦ homCount Y sz n i j ω := by
  have h : ∀ ω, homCount Y sz n i j ω = ∑ m ∈ range (sz i * n), if Y i m ω = j then (1 : ℝ) else 0 := by
    intro ω
    rw [sum_boole]
    rfl
  simp_rw [h]
  exact Finset.measurable_sum _ fun m _ ↦
    Measurable.ite (hmeas i m (measurableSet_singleton j)) measurable_const measurable_const

lemma measurable_homogeneityStatistic {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (sz : Fin r → ℕ) (n : ℕ) : Measurable (homogeneityStatistic Y sz n) := by
  have hC : ∀ j, Measurable fun ω ↦ homColTotal Y sz n j ω := fun j ↦
    Finset.measurable_sum _ fun i _ ↦ measurable_homCount hmeas sz n i j
  have hE : ∀ i j, Measurable fun ω ↦ homExpected Y sz n i j ω := fun i j ↦
    ((hC j).const_mul _).div_const _
  unfold homogeneityStatistic
  exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    (((measurable_homCount hmeas sz n i j).sub (hE i j)).pow_const 2).div (hE i j)

/-! ### The statistic as a continuous function -/

/-- `G(w, β̂) = ∑_{i,j} (w_ij - (sᵢ/∑s) ∑_k w_kj)² / (sᵢ max(β̂_j, δ))`; continuous for `δ > 0`. -/
noncomputable def homG (sz : Fin r → ℕ) (δ : ℝ) (q : EuclideanSpace ℝ (Fin r × Fin c) × (Fin c → ℝ)) : ℝ :=
  ∑ i, ∑ j, (q.1 (i, j) - (sz i : ℝ) / (∑ i', (sz i' : ℝ)) * ∑ k, q.1 (k, j)) ^ 2 /
    ((sz i : ℝ) * max (q.2 j) δ)

lemma continuous_homG (sz : Fin r → ℕ) (hsz : ∀ i, 0 < sz i) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (homG (c := c) sz δ) := by
  unfold homG
  refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
  have hx : ∀ x : Fin r × Fin c,
      Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × (Fin c → ℝ) ↦ q.1 x :=
    fun x ↦ (PiLp.continuous_apply 2 _ x).comp continuous_fst
  have e1 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × (Fin c → ℝ) ↦
      (q.1 (i, j) - (sz i : ℝ) / (∑ i', (sz i' : ℝ)) * ∑ k, q.1 (k, j) : ℝ) :=
    (hx (i, j)).sub (continuous_const.mul (continuous_finsetSum
      (f := fun k (q : EuclideanSpace ℝ (Fin r × Fin c) × (Fin c → ℝ)) ↦ q.1 (k, j)) univ
      fun k _ ↦ hx (k, j)))
  have e2 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × (Fin c → ℝ) ↦
      ((sz i : ℝ) * max (q.2 j) δ : ℝ) :=
    continuous_const.mul (((continuous_apply j).comp continuous_snd).max continuous_const)
  have hs : (0 : ℝ) < sz i := Nat.cast_pos.2 (hsz i)
  exact (e1.pow 2).div e2 fun q ↦ (mul_pos hs (lt_of_lt_of_le hδ (le_max_right _ _))).ne'

/-- The algebraic identity behind the eventual equality of the statistic and `G`. -/
private lemma hom_term_identity {n t S O Cj s b : ℝ} (ht : t ^ 2 = n) (ht0 : t ≠ 0) (hS : S ≠ 0)
    (hs : s ≠ 0) (hC : Cj ≠ 0) :
    ((O - s * n * b) / t - s / S * ((Cj - S * n * b) / t)) ^ 2 / (s * (Cj / (S * n))) =
      (O - s * n * Cj / (S * n)) ^ 2 / (s * n * Cj / (S * n)) := by
  subst ht
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- Once `n ≥ 1` and every pooled proportion `C_j/N` is at least `δ`, the statistic equals `G`. -/
lemma homogeneityStatistic_eq_homG [Nonempty (Fin r)] {sz : Fin r → ℕ} (hsz : ∀ i, 0 < sz i) {b : Fin c → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (Y : Fin r → ℕ → Ω → Fin c) {n : ℕ} (hn : n ≠ 0) (ω : Ω)
    (hle : ∀ j, δ ≤ homColTotal Y sz n j ω / ((∑ i, (sz i : ℝ)) * n)) :
    homogeneityStatistic Y sz n ω = homG sz δ (homVector Y sz b n ω,
      fun j ↦ homColTotal Y sz n j ω / ((∑ i, (sz i : ℝ)) * n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  set S : ℝ := ∑ i, (sz i : ℝ) with hS_def
  have hS : S ≠ 0 := (sum_pos (fun i _ ↦ Nat.cast_pos.2 (hsz i)) univ_nonempty).ne'
  set t : ℝ := √(n : ℝ) with ht_def
  have ht : t ^ 2 = n := sq_sqrt (Nat.cast_nonneg n)
  have ht0 : t ≠ 0 := (sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))).ne'
  have hv : ∀ i j, (homVector Y sz b n ω) (i, j) = (homCount Y sz n i j ω - (sz i : ℝ) * n * b j) / t := by
    intro i j
    simp only [homVector, WithLp.ofLp_toLp, ht_def]
  have hcol : ∀ j, ∑ k, (homVector Y sz b n ω) (k, j) = (homColTotal Y sz n j ω - S * n * b j) / t := by
    intro j
    simp_rw [hv]
    have e : ∑ i, (sz i : ℝ) * n * b j = S * n * b j := by rw [hS_def, sum_mul, sum_mul]
    rw [← sum_div, sum_sub_distrib, e]
    unfold homColTotal
    rfl
  unfold homogeneityStatistic homG homExpected
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only
  rw [hv, hcol, max_eq_left (hle j)]
  have hCpos : homColTotal Y sz n j ω / (S * n) ≠ 0 := (lt_of_lt_of_le hδ (hle j)).ne'
  have hC : homColTotal Y sz n j ω ≠ 0 := fun h ↦ hCpos (by rw [h, zero_div])
  have hs : (sz i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hsz i).ne'
  have hsumn : ∑ i', (sz i' : ℝ) * n = S * n := by rw [hS_def, sum_mul]
  rw [hsumn]
  rw [hom_term_identity ht ht0 hS hs hC]

/-- At the limit, `G(√sᵢ (row projections of a Gaussian table), b) = ‖(I - ααᵀ) Z (I - ββᵀ)‖²` with
`αᵢ = √(sᵢ/∑s)` and `β_j = √b_j`. -/
lemma homG_homLimit [Nonempty (Fin r)] {sz : Fin r → ℕ} (hsz : ∀ i, 0 < sz i) {b : Fin c → ℝ} (hb : ∀ j, 0 < b j)
    {δ : ℝ} (hδ : ∀ j, δ ≤ b j) (z : Fin r × Fin c → ℝ) :
    homG sz δ (homLimit sz b z, b) =
      ∑ i, ∑ j, tableProj (fun i ↦ √((sz i : ℝ) / ∑ i', (sz i' : ℝ))) (fun j ↦ √(b j)) z i j ^ 2 := by
  set S : ℝ := ∑ i', (sz i' : ℝ) with hS_def
  have hSpos : 0 < S := sum_pos (fun i _ ↦ Nat.cast_pos.2 (hsz i)) univ_nonempty
  set α : Fin r → ℝ := fun i ↦ √((sz i : ℝ) / S) with hα_def
  set β : Fin c → ℝ := fun j ↦ √(b j) with hβ_def
  set rS : ℝ := √S with hrS
  have hrS0 : rS ≠ 0 := (sqrt_pos.2 hSpos).ne'
  have hα2 : ∀ i, α i ^ 2 = (sz i : ℝ) / S := fun i ↦ sq_sqrt (div_nonneg (Nat.cast_nonneg _) hSpos.le)
  have hβ2 : ∀ j, β j ^ 2 = b j := fun j ↦ sq_sqrt (hb j).le
  have hσ : ∀ i, √(sz i : ℝ) = rS * α i := by
    intro i
    rw [hrS, hα_def, ← sqrt_mul hSpos.le]
    congr 1
    field_simp
  have hα0 : ∀ i, α i ≠ 0 := fun i ↦ (sqrt_pos.2 (div_pos (Nat.cast_pos.2 (hsz i)) hSpos)).ne'
  have hβ0 : ∀ j, β j ≠ 0 := fun j ↦ (sqrt_pos.2 (hb j)).ne'
  have hw : ∀ i j, (homLimit sz b z) (i, j) =
      rS * α i * β j * (z (i, j) - β j * ∑ l, β l * z (i, l)) := by
    intro i j
    have hβapp : ∀ l, √(b l) = β l := fun l ↦ rfl
    simp only [homLimit, WithLp.ofLp_toLp, hβapp]
    rw [hσ, ← hβ2 j]
    ring
  have hcol : ∀ j, ∑ k, (homLimit sz b z) (k, j) =
      rS * β j * ∑ k, α k * (z (k, j) - β j * ∑ l, β l * z (k, l)) := by
    intro j
    simp_rw [hw]
    rw [mul_sum]
    exact sum_congr rfl fun k _ ↦ by ring
  have hdouble : ∀ j, ∑ k, α k * (z (k, j) - β j * ∑ l, β l * z (k, l)) =
      ∑ k, α k * z (k, j) - β j * ∑ k, ∑ l, α k * β l * z (k, l) := by
    intro j
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [mul_sub, mul_sum, mul_sum, mul_sum]
    congr 1
    exact sum_congr rfl fun l _ ↦ by ring
  unfold homG
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only
  rw [hw, hcol, max_eq_left (hδ j), hdouble, ← hS_def]
  have hsz_eq : (sz i : ℝ) = α i ^ 2 * S := by rw [hα2]; field_simp
  have hS_eq : S = rS ^ 2 := (sq_sqrt hSpos.le).symm
  rw [hsz_eq, ← hβ2 j]
  unfold tableProj
  rw [hS_eq]
  have := hα0 i
  have := hβ0 j
  field_simp
  ring

end Homogeneity

/-! ### The theorem -/

section MainHom

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {r c : ℕ}

/-- **The chi-square test of homogeneity (§11.4, ST-099).** Samples are drawn independently from `r ≥ 2`
populations, with sizes `sᵢ n` in a fixed ratio (`sᵢ > 0`); each individual falls in one of `c ≥ 2` categories.
Under the null hypothesis that every population has the same category probabilities `b_j > 0` (all draws
independent, the draws from one population identically distributed with `P(category j) = b_j`), the statistic
`∑_{i,j} (O_ij - E_ij)² / E_ij` with expected counts `E_ij = (row total)(column total)/(grand total)` converges in
distribution, as `n → ∞`, to the chi-square law with `(r - 1)(c - 1)` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.4, p. 589"]
theorem tendstoInDistribution_homogeneityStatistic [IsProbabilityMeasure P] {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] (hr : 2 ≤ r) (hc : 2 ≤ c)
    {sz : Fin r → ℕ} (hsz : ∀ i, 0 < sz i) {b : Fin c → ℝ} (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (hind : iIndepFun (fun x : Fin r × ℕ ↦ Y x.1 x.2) P) (hident : ∀ i m, IdentDistrib (Y i m) (Y i 0) P P)
    (hprob : ∀ i j, P.real {ω | Y i 0 ω = j} = b j)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) P') :
    TendstoInDistribution (homogeneityStatistic Y sz) atTop W (fun _ ↦ P) P' := by
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  set S : ℝ := ∑ i, (sz i : ℝ) with hS_def
  have hSpos : 0 < S := sum_pos (fun i _ ↦ Nat.cast_pos.2 (hsz i)) univ_nonempty
  -- a positive lower bound for the category probabilities
  have hne : (univ : Finset (Fin c)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  set δ : ℝ := univ.inf' hne b / 2 with hδ_def
  have hinf : 0 < univ.inf' hne b := (lt_inf'_iff hne).2 fun j _ ↦ hb j
  have hδ : 0 < δ := half_pos hinf
  have hδlt : ∀ j, δ < b j := fun j ↦ lt_of_lt_of_le (half_lt_self hinf) (inf'_le b (mem_univ j))
  -- the pooled proportions converge almost surely
  set B : ℕ → Ω → Fin c → ℝ := fun n ω j ↦ homColTotal Y sz n j ω / (S * n) with hB_def
  have hBmeas : ∀ n, Measurable (B n) := fun n ↦ measurable_pi_iff.2 fun j ↦
    (Finset.measurable_sum _ fun i _ ↦ measurable_homCount hmeas sz n i j).div_const _
  have hcell : ∀ i j, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ homCount Y sz n i j ω / ((sz i : ℝ) * n)) atTop (𝓝 (b j)) := by
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
    have hN : Tendsto (fun n : ℕ ↦ sz i * n) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ Nat.le_mul_of_pos_left n (hsz i)) tendsto_id
    filter_upwards [h] with ω hω
    rw [hint] at hω
    have := hω.comp hN
    refine this.congr fun n ↦ ?_
    simp only [Function.comp, Nat.cast_mul]
    rw [sum_boole]
    rfl
  have hBae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ B n ω) atTop (𝓝 b) := by
    have hall : ∀ᵐ ω ∂P, ∀ i j,
        Tendsto (fun n : ℕ ↦ homCount Y sz n i j ω / ((sz i : ℝ) * n)) atTop (𝓝 (b j)) :=
      ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ hcell i j
    filter_upwards [hall] with ω hω
    refine tendsto_pi_nhds.2 fun j ↦ ?_
    have hlim : Tendsto (fun n : ℕ ↦ ∑ i, (sz i : ℝ) / S * (homCount Y sz n i j ω / ((sz i : ℝ) * n)))
        atTop (𝓝 (∑ i, (sz i : ℝ) / S * b j)) :=
      tendsto_finsetSum _ fun i _ ↦ (hω i j).const_mul _
    have hval : ∑ i, (sz i : ℝ) / S * b j = b j := by
      rw [← sum_mul, ← sum_div, ← hS_def, div_self hSpos.ne', one_mul]
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [hB_def, homColTotal, sum_div]
    refine sum_congr rfl fun i _ ↦ ?_
    have hs : (sz i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hsz i).ne'
    field_simp
  have hBm : TendstoInMeasure P B atTop (fun _ ↦ b) :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hBmeas n).aestronglyMeasurable) hBae
  -- Slutsky's theorem
  have hvec := tendstoInDistribution_homVector hsz hb hbsum hmeas hind hident hprob
  have hsl := hvec.continuous_comp_prodMk_of_tendstoInMeasure_const (continuous_homG sz hsz hδ) hBm
    fun n ↦ (hBmeas n).aemeasurable
  -- the statistic and `G` agree eventually, almost surely
  have hVmeas : ∀ n, Measurable (homVector Y sz b n) := by
    intro n
    unfold homVector
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun x ↦
      ((measurable_homCount hmeas sz n x.1 x.2).sub_const _).div_const _)
  have hGmeas : ∀ n, Measurable fun ω ↦ homG sz δ (homVector Y sz b n ω, B n ω) := fun n ↦
    (continuous_homG sz hsz hδ).measurable.comp ((hVmeas n).prodMk (hBmeas n))
  have hdiff : TendstoInMeasure P
      (homogeneityStatistic Y sz - fun n ω ↦ homG sz δ (homVector Y sz b n ω, B n ω)) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((measurable_homogeneityStatistic hmeas sz n).sub (hGmeas n)).aestronglyMeasurable) ?_
    filter_upwards [hBae] with ω hω
    have h1 : ∀ j, ∀ᶠ n in atTop, δ ≤ B n ω j := fun j ↦
      (((continuous_apply j).continuousAt.tendsto.comp hω).eventually (lt_mem_nhds (hδlt j))).mono
        fun n hn ↦ hn.le
    have h2 : ∀ᶠ n in atTop, ∀ j, δ ≤ B n ω j := eventually_all.2 h1
    have hev : ∀ᶠ n in atTop,
        (homogeneityStatistic Y sz - fun n ω ↦ homG sz δ (homVector Y sz b n ω, B n ω)) n ω = 0 := by
      filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
      rw [Pi.sub_apply, Pi.sub_apply, sub_eq_zero]
      exact homogeneityStatistic_eq_homG hsz hδ Y (by omega) ω hn
    exact tendsto_const_nhds.congr' (hev.mono fun n hn ↦ hn.symm)
  have hconv := tendstoInDistribution_of_tendstoInMeasure_sub (homogeneityStatistic Y sz) _ hsl hdiff
    fun n ↦ (measurable_homogeneityStatistic hmeas sz n).aemeasurable
  -- the law of the limit
  have hlim : (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1).map
      (fun z ↦ homG sz δ (homLimit sz b z, b)) = chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1)) := by
    have hα : ∑ i, (fun i ↦ √((sz i : ℝ) / S)) i ^ 2 = 1 := by
      simp_rw [sq_sqrt (div_nonneg (Nat.cast_nonneg _) hSpos.le)]
      rw [← sum_div, div_self hSpos.ne']
    have hβ : ∑ j, (fun j ↦ √(b j)) j ^ 2 = 1 := by
      simp_rw [sq_sqrt (hb _).le]
      exact hbsum
    rw [← (hasLaw_tableProj_chiSquared hr hc _ _ hα hβ).map_eq]
    congr 1
    funext z
    exact homG_homLimit hsz hb (fun j ↦ (hδlt j).le) z
  exact TendstoInDistribution.of_map_eq_limit hconv hW.aemeasurable (by rw [hW.map_eq, hlim])

end MainHom

end UndergradKB.Statistics
