import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import UndergradKB.Common.Attr
import UndergradKB.Statistics.TableProjection

/-!
# The chi-square test of independence (OpenStax *Introductory Statistics 2e*, §11.3)

Each of `n` independent individuals is classified by a row variable with `r ≥ 2` values and a column variable with
`c ≥ 2` values. `O_ij` is the observed count of cell `(i, j)`, `R_i` and `C_j` are the row and column totals and
`E_ij = R_i C_j / n` is the expected count under independence. The test of independence uses
`χ² = ∑_{i,j} (O_ij - E_ij)² / E_ij` and refers it to the chi-square law with `(r - 1)(c - 1)` degrees of freedom.

`tendstoInDistribution_independenceStatistic`: under the null hypothesis (the two variables are independent, with
marginal probabilities `a_i > 0`, `b_j > 0`) the statistic converges in distribution to that law.

Proof. Write `p_ij = a_i b_j`. The vector `n^{-1/2}((O_ij - n p_ij)/√p_ij)` converges in distribution to the
Gaussian vector `w = z - ⟪u, z⟫ u` (`tendstoInDistribution_pearsonSum`). The margins `R_i/n`, `C_j/n` converge almost
surely to `a_i`, `b_j` (strong law). Eventually (almost surely), `χ²` equals `G(vector, margins)` for one continuous
function `G` (the expected counts are bounded away from `0`), so Slutsky's theorem (Mathlib) gives the limit
`G(w, (a, b))`, which is `‖(I - ααᵀ) Z (I - ββᵀ)‖²` with `α = (√a_i)`, `β = (√b_j)` and `Z` a standard Gaussian
table: chi-square with `(r - 1)(c - 1)` degrees of freedom (`hasLaw_tableProj_chiSquared`).
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Finset Filter Topology

section Table

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {r c : ℕ}

/-- The row total `R_i = ∑_j O_ij` of row `i` after `n` observations. -/
noncomputable def rowTotal (C : ℕ → Ω → Fin r × Fin c) (n : ℕ) (i : Fin r) (ω : Ω) : ℝ :=
  ∑ j, observedCount C n (i, j) ω

/-- The column total `C_j = ∑_i O_ij` of column `j` after `n` observations. -/
noncomputable def colTotal (C : ℕ → Ω → Fin r × Fin c) (n : ℕ) (j : Fin c) (ω : Ω) : ℝ :=
  ∑ i, observedCount C n (i, j) ω

/-- The expected count `E_ij = (row total)(column total)/(grand total)` of cell `(i, j)` (§11.3). -/
noncomputable def expectedCount (C : ℕ → Ω → Fin r × Fin c) (n : ℕ) (i : Fin r) (j : Fin c) (ω : Ω) : ℝ :=
  rowTotal C n i ω * colTotal C n j ω / n

/-- The test statistic of independence `∑_{i,j} (O_ij - E_ij)² / E_ij` (§11.3). -/
noncomputable def independenceStatistic (C : ℕ → Ω → Fin r × Fin c) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, (observedCount C n (i, j) ω - expectedCount C n i j ω) ^ 2 / expectedCount C n i j ω

omit [MeasurableSpace Ω] in
lemma observedCount_eq_sum {ι : Type*} [DecidableEq ι] (C : ℕ → Ω → ι) (n : ℕ) (x : ι) (ω : Ω) :
    observedCount C n x ω = ∑ m ∈ range n, if C m ω = x then (1 : ℝ) else 0 := by
  rw [sum_boole]
  rfl

lemma measurable_observedCount {ι : Type*} [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {C : ℕ → Ω → ι} (hmeas : ∀ m, Measurable (C m)) (n : ℕ) (x : ι) :
    Measurable fun ω ↦ observedCount C n x ω := by
  simp_rw [observedCount_eq_sum]
  exact Finset.measurable_sum _ fun m _ ↦
    Measurable.ite (hmeas m (measurableSet_singleton x)) measurable_const measurable_const

omit [MeasurableSpace Ω] in
lemma rowTotal_eq_sum (C : ℕ → Ω → Fin r × Fin c) (n : ℕ) (i : Fin r) (ω : Ω) :
    rowTotal C n i ω = ∑ m ∈ range n, if (C m ω).1 = i then (1 : ℝ) else 0 := by
  unfold rowTotal
  simp_rw [observedCount_eq_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ ↦ ?_
  rcases C m ω with ⟨x₁, x₂⟩
  by_cases h : x₁ = i
  · subst h
    simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h]

omit [MeasurableSpace Ω] in
lemma colTotal_eq_sum (C : ℕ → Ω → Fin r × Fin c) (n : ℕ) (j : Fin c) (ω : Ω) :
    colTotal C n j ω = ∑ m ∈ range n, if (C m ω).2 = j then (1 : ℝ) else 0 := by
  unfold colTotal
  simp_rw [observedCount_eq_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ ↦ ?_
  rcases C m ω with ⟨x₁, x₂⟩
  by_cases h : x₂ = j
  · subst h
    simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h]

/-- Strong law for a bounded function of independent identically distributed observations. -/
lemma ae_tendsto_average [IsProbabilityMeasure P] {ι : Type*} [MeasurableSpace ι] {C : ℕ → Ω → ι}
    (hmeas : ∀ m, Measurable (C m)) (hind : iIndepFun C P) (hident : ∀ m, IdentDistrib (C m) (C 0) P P)
    {f : ι → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ m ∈ range n, f (C m ω)) / n) atTop (𝓝 (∫ ω, f (C 0 ω) ∂P)) := by
  have hint : Integrable (fun ω ↦ f (C 0 ω)) P :=
    Integrable.of_bound (hf.comp (hmeas 0)).aestronglyMeasurable M
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hM _)
  have hind' : iIndepFun (fun m ω ↦ f (C m ω)) P := hind.comp (fun _ ↦ f) fun _ ↦ hf
  have h := strong_law_ae (fun m ω ↦ f (C m ω)) hint (fun i j hij ↦ hind'.indepFun hij)
    (fun m ↦ (hident m).comp hf)
  filter_upwards [h] with ω hω
  convert hω using 2 with n
  rw [smul_eq_mul, inv_mul_eq_div]

omit [MeasurableSpace Ω] in
/-- Coordinates of `pearsonSum`: `n^{-1/2} (O_x - n p_x)/√p_x`. -/
lemma pearsonSum_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (C : ℕ → Ω → ι) (n : ℕ) (ω : Ω)
    (x : ι) : (pearsonSum p C n ω) x = (√(n : ℝ))⁻¹ * ((observedCount C n x ω - n * p x) / √(p x)) := by
  have hO : ∑ m ∈ range n, ((if C m ω = x then (1 : ℝ) else 0) - p x) = observedCount C n x ω - n * p x := by
    rw [sum_sub_distrib, ← observedCount_eq_sum, sum_const, card_range, nsmul_eq_mul]
  simp only [pearsonSum, pearsonVector, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
  rw [← sum_div, hO]

lemma measurable_rowTotal {C : ℕ → Ω → Fin r × Fin c} (hmeas : ∀ m, Measurable (C m)) (n : ℕ) (i : Fin r) :
    Measurable fun ω ↦ rowTotal C n i ω :=
  Finset.measurable_sum _ fun j _ ↦ measurable_observedCount hmeas n (i, j)

lemma measurable_colTotal {C : ℕ → Ω → Fin r × Fin c} (hmeas : ∀ m, Measurable (C m)) (n : ℕ) (j : Fin c) :
    Measurable fun ω ↦ colTotal C n j ω :=
  Finset.measurable_sum _ fun i _ ↦ measurable_observedCount hmeas n (i, j)

lemma measurable_independenceStatistic {C : ℕ → Ω → Fin r × Fin c} (hmeas : ∀ m, Measurable (C m))
    (n : ℕ) : Measurable (independenceStatistic C n) := by
  have hE : ∀ i j, Measurable fun ω ↦ expectedCount C n i j ω := fun i j ↦
    ((measurable_rowTotal hmeas n i).mul (measurable_colTotal hmeas n j)).div_const _
  unfold independenceStatistic
  exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    (((measurable_observedCount hmeas n (i, j)).sub (hE i j)).pow_const 2).div (hE i j)

/-! ### The statistic as a continuous function of the count vector and the margins -/

/-- `G(x, (α, β)) = ∑_{i,j} (v_ij - b_j ∑_l v_il - α_i ∑_k v_kj)² / max(α_i β_j, δ)` with `v_ij = √(a_i b_j) x_ij`;
continuous for `δ > 0`. -/
noncomputable def indepG (a : Fin r → ℝ) (b : Fin c → ℝ) (δ : ℝ)
    (q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ))) : ℝ :=
  ∑ i, ∑ j, (√(a i * b j) * q.1 (i, j) - b j * ∑ l, √(a i * b l) * q.1 (i, l)
      - q.2.1 i * ∑ k, √(a k * b j) * q.1 (k, j)) ^ 2 / max (q.2.1 i * q.2.2 j) δ

lemma continuous_indepG (a : Fin r → ℝ) (b : Fin c → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (indepG a b δ) := by
  unfold indepG
  refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
  have hx : ∀ x : Fin r × Fin c,
      Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦ q.1 x :=
    fun x ↦ (PiLp.continuous_apply 2 _ x).comp continuous_fst
  have hα : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦ q.2.1 i :=
    (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have hβ : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦ q.2.2 j :=
    (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  have h1 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦
      (√(a i * b j) * q.1 (i, j) - b j * ∑ l, √(a i * b l) * q.1 (i, l)
        - q.2.1 i * ∑ k, √(a k * b j) * q.1 (k, j)) ^ 2 := by
    have e1 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦
        (√(a i * b j) * q.1 (i, j) : ℝ) := continuous_const.mul (hx (i, j))
    have e2 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦
        (b j * ∑ l, √(a i * b l) * q.1 (i, l) : ℝ) :=
      continuous_const.mul (continuous_finsetSum (f := fun l (q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ))) ↦
          √(a i * b l) * q.1 (i, l)) univ
        fun l _ ↦ continuous_const.mul (hx (i, l)))
    have e3 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦
        (q.2.1 i * ∑ k, √(a k * b j) * q.1 (k, j) : ℝ) :=
      hα.mul (continuous_finsetSum (f := fun k (q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ))) ↦
          √(a k * b j) * q.1 (k, j)) univ
        fun k _ ↦ continuous_const.mul (hx (k, j)))
    exact ((e1.sub e2).sub e3).pow 2
  have h2 : Continuous fun q : EuclideanSpace ℝ (Fin r × Fin c) × ((Fin r → ℝ) × (Fin c → ℝ)) ↦
      max (q.2.1 i * q.2.2 j) δ := (hα.mul hβ).max continuous_const
  exact h1.div h2 fun q ↦ (lt_of_lt_of_le hδ (le_max_right _ _)).ne'

/-- The algebraic identity behind the eventual equality of the statistic and `G`. -/
private lemma term_identity {n s O R C a b : ℝ} (hs : s ^ 2 = n) (hs0 : s ≠ 0) (hR : R ≠ 0) (hC : C ≠ 0) :
    (s⁻¹ * (O - n * (a * b)) - b * (s⁻¹ * (R - n * a)) - R / n * (s⁻¹ * (C - n * b))) ^ 2 /
      (R / n * (C / n)) = (O - R * C / n) ^ 2 / (R * C / n) := by
  subst hs
  field_simp
  ring

omit [MeasurableSpace Ω] in
/-- Once `n ≥ 1` and every product of margins `(R_i/n)(C_j/n)` is at least `δ`, the statistic equals `G`. -/
lemma independenceStatistic_eq_indepG {a : Fin r → ℝ} {b : Fin c → ℝ} (ha : ∀ i, 0 < a i)
    (hb : ∀ j, 0 < b j) (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1) {δ : ℝ} (hδ : 0 < δ)
    (C : ℕ → Ω → Fin r × Fin c) {n : ℕ} (hn : n ≠ 0) (ω : Ω)
    (hle : ∀ i j, δ ≤ rowTotal C n i ω / n * (colTotal C n j ω / n)) :
    independenceStatistic C n ω = indepG a b δ (pearsonSum (fun x ↦ a x.1 * b x.2) C n ω,
      (fun i ↦ rowTotal C n i ω / n, fun j ↦ colTotal C n j ω / n)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  set s : ℝ := √(n : ℝ) with hs_def
  have hs : s ^ 2 = n := sq_sqrt (Nat.cast_nonneg n)
  have hs0 : s ≠ 0 := (sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))).ne'
  have hv : ∀ i j, √(a i * b j) * (pearsonSum (fun x ↦ a x.1 * b x.2) C n ω) (i, j) =
      s⁻¹ * (observedCount C n (i, j) ω - n * (a i * b j)) := by
    intro i j
    rw [pearsonSum_apply]
    have : √(a i * b j) ≠ 0 := (sqrt_pos.2 (mul_pos (ha i) (hb j))).ne'
    field_simp
    rw [← hs_def]
    ring
  have hrow : ∀ i, ∑ l, √(a i * b l) * (pearsonSum (fun x ↦ a x.1 * b x.2) C n ω) (i, l) =
      s⁻¹ * (rowTotal C n i ω - n * a i) := by
    intro i
    simp_rw [hv]
    rw [← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum, hbsum, mul_one]
    rfl
  have hcol : ∀ j, ∑ k, √(a k * b j) * (pearsonSum (fun x ↦ a x.1 * b x.2) C n ω) (k, j) =
      s⁻¹ * (colTotal C n j ω - n * b j) := by
    intro j
    simp_rw [hv]
    rw [← mul_sum, sum_sub_distrib, ← mul_sum, ← sum_mul, hasum, one_mul]
    rfl
  unfold independenceStatistic indepG
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only
  rw [hv, hrow, hcol, max_eq_left (hle i j)]
  have hRC : rowTotal C n i ω / n * (colTotal C n j ω / n) ≠ 0 := (lt_of_lt_of_le hδ (hle i j)).ne'
  have hR : rowTotal C n i ω ≠ 0 := fun h ↦ hRC (by rw [h]; ring)
  have hC : colTotal C n j ω ≠ 0 := fun h ↦ hRC (by rw [h]; ring)
  unfold expectedCount
  rw [term_identity hs hs0 hR hC]

omit [MeasurableSpace Ω] in
/-- At the limit, `G(w, (a, b)) = ‖(I - ααᵀ) Z (I - ββᵀ)‖²` with `α = (√a_i)`, `β = (√b_j)`. -/
lemma indepG_pearsonLimit {a : Fin r → ℝ} {b : Fin c → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1) {δ : ℝ} (hδ : ∀ i j, δ ≤ a i * b j)
    (z : Fin r × Fin c → ℝ) :
    indepG a b δ (pearsonLimit (fun x ↦ a x.1 * b x.2) z, (a, b)) =
      ∑ i, ∑ j, tableProj (fun i ↦ √(a i)) (fun j ↦ √(b j)) z i j ^ 2 := by
  set α : Fin r → ℝ := fun i ↦ √(a i) with hα_def
  set β : Fin c → ℝ := fun j ↦ √(b j) with hβ_def
  have hαsq : ∀ i, α i ^ 2 = a i := fun i ↦ sq_sqrt (ha i).le
  have hβsq : ∀ j, β j ^ 2 = b j := fun j ↦ sq_sqrt (hb j).le
  have hsq : ∀ i j, √(a i * b j) = α i * β j := fun i j ↦ sqrt_mul (ha i).le _
  have hβ1 : ∑ l, β l ^ 2 = 1 := by simp_rw [hβsq]; exact hbsum
  have hα1 : ∑ k, α k ^ 2 = 1 := by simp_rw [hαsq]; exact hasum
  set S : ℝ := ∑ k, ∑ l, α k * β l * z (k, l) with hS
  have hw : ∀ i j, (pearsonLimit (fun x ↦ a x.1 * b x.2) z) (i, j) = z (i, j) - S * (α i * β j) := by
    intro i j
    simp only [pearsonLimit, WithLp.ofLp_toLp]
    rw [Fintype.sum_prod_type]
    simp_rw [hsq]
    rfl
  have hv : ∀ i j, √(a i * b j) * (pearsonLimit (fun x ↦ a x.1 * b x.2) z) (i, j) =
      α i * β j * (z (i, j) - S * (α i * β j)) := by
    intro i j
    rw [hw, hsq]
  have hrow : ∀ i, ∑ l, √(a i * b l) * (pearsonLimit (fun x ↦ a x.1 * b x.2) z) (i, l) =
      α i * (∑ l, β l * z (i, l) - S * α i) := by
    intro i
    simp_rw [hv]
    have h : ∀ l, α i * β l * (z (i, l) - S * (α i * β l)) =
        α i * (β l * z (i, l)) - S * α i ^ 2 * β l ^ 2 := fun l ↦ by ring
    rw [sum_congr rfl fun l _ ↦ h l, sum_sub_distrib, ← mul_sum, ← mul_sum, hβ1]
    ring
  have hcol : ∀ j, ∑ k, √(a k * b j) * (pearsonLimit (fun x ↦ a x.1 * b x.2) z) (k, j) =
      β j * (∑ k, α k * z (k, j) - S * β j) := by
    intro j
    simp_rw [hv]
    have h : ∀ k, α k * β j * (z (k, j) - S * (α k * β j)) =
        β j * (α k * z (k, j)) - S * β j ^ 2 * α k ^ 2 := fun k ↦ by ring
    rw [sum_congr rfl fun k _ ↦ h k, sum_sub_distrib, ← mul_sum, ← mul_sum, hα1]
    ring
  unfold indepG
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only
  rw [hv, hrow, hcol, max_eq_left (hδ i j), ← hαsq i, ← hβsq j]
  have hαi : α i ≠ 0 := (sqrt_pos.2 (ha i)).ne'
  have hβj : β j ≠ 0 := (sqrt_pos.2 (hb j)).ne'
  unfold tableProj
  field_simp
  ring

end Table

/-! ### The theorem -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {r c : ℕ}

/-- **The chi-square test of independence (§11.3, ST-098).** Individuals `C₀, C₁, …` are independent and
identically distributed; each falls in cell `(i, j)` of an `r × c` table (`r, c ≥ 2`). Under the null hypothesis
that the row and column variables are independent, with marginal probabilities `a_i > 0` and `b_j > 0`
(`P(C = (i, j)) = a_i b_j`), the statistic `∑_{i,j} (O_ij - E_ij)² / E_ij` with expected counts
`E_ij = (row total)(column total)/n` converges in distribution, as `n → ∞`, to the chi-square law with
`(r - 1)(c - 1)` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.3, p. 585"]
theorem tendstoInDistribution_independenceStatistic [IsProbabilityMeasure P] {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] (hr : 2 ≤ r) (hc : 2 ≤ c)
    {a : Fin r → ℝ} {b : Fin c → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hasum : ∑ i, a i = 1)
    (hbsum : ∑ j, b j = 1) {C : ℕ → Ω → Fin r × Fin c} (hmeas : ∀ m, Measurable (C m))
    (hind : iIndepFun C P) (hident : ∀ m, IdentDistrib (C m) (C 0) P P)
    (hprob : ∀ i j, P.real {ω | C 0 ω = (i, j)} = a i * b j)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) P') :
    TendstoInDistribution (independenceStatistic C) atTop W (fun _ ↦ P) P' := by
  set p : Fin r × Fin c → ℝ := fun x ↦ a x.1 * b x.2 with hp_def
  have hp : ∀ x, 0 < p x := fun x ↦ mul_pos (ha _) (hb _)
  have hpsum : ∑ x, p x = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hp_def, ← mul_sum, hbsum, mul_one, hasum]
  have hprob' : ∀ x, P.real {ω | C 0 ω = x} = p x := fun x ↦ hprob x.1 x.2
  -- a positive lower bound for the products of the margins
  have hne : (univ : Finset (Fin r × Fin c)).Nonempty := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), mem_univ _⟩
  set δ : ℝ := univ.inf' hne p / 2 with hδ_def
  have hinf : 0 < univ.inf' hne p := (lt_inf'_iff hne).2 fun x _ ↦ hp x
  have hδ : 0 < δ := half_pos hinf
  have hδlt : ∀ i j, δ < a i * b j := fun i j ↦
    lt_of_lt_of_le (half_lt_self hinf) (inf'_le p (mem_univ (i, j)))
  -- the margins converge almost surely
  set Y : ℕ → Ω → (Fin r → ℝ) × (Fin c → ℝ) :=
    fun n ω ↦ (fun i ↦ rowTotal C n i ω / n, fun j ↦ colTotal C n j ω / n) with hY_def
  have hYmeas : ∀ n, Measurable (Y n) := fun n ↦
    (measurable_pi_iff.2 fun i ↦ (measurable_rowTotal hmeas n i).div_const _).prodMk
      (measurable_pi_iff.2 fun j ↦ (measurable_colTotal hmeas n j).div_const _)
  have hrow : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ rowTotal C n i ω / n) atTop (𝓝 (a i)) := by
    intro i
    have h := ae_tendsto_average hmeas hind hident (f := fun x : Fin r × Fin c ↦ if x.1 = i then (1 : ℝ) else 0)
      (measurable_of_finite _) (M := 1) fun x ↦ by split_ifs <;> simp
    have hint : ∫ ω, (fun x : Fin r × Fin c ↦ if x.1 = i then (1 : ℝ) else 0) (C 0 ω) ∂P = a i := by
      refine (integral_comp_fin (P := P) (hmeas 0) (fun x : Fin r × Fin c ↦ if x.1 = i then (1 : ℝ) else 0)).trans ?_
      rw [Fintype.sum_prod_type]
      simp_rw [hprob', hp_def]
      simp [← mul_sum, hbsum]
    filter_upwards [h] with ω hω
    rw [hint] at hω
    simpa only [rowTotal_eq_sum] using hω
  have hcol : ∀ j, ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ colTotal C n j ω / n) atTop (𝓝 (b j)) := by
    intro j
    have h := ae_tendsto_average hmeas hind hident (f := fun x : Fin r × Fin c ↦ if x.2 = j then (1 : ℝ) else 0)
      (measurable_of_finite _) (M := 1) fun x ↦ by split_ifs <;> simp
    have hint : ∫ ω, (fun x : Fin r × Fin c ↦ if x.2 = j then (1 : ℝ) else 0) (C 0 ω) ∂P = b j := by
      refine (integral_comp_fin (P := P) (hmeas 0) (fun x : Fin r × Fin c ↦ if x.2 = j then (1 : ℝ) else 0)).trans ?_
      rw [Fintype.sum_prod_type]
      simp_rw [hprob', hp_def]
      simp [← sum_mul, hasum]
    filter_upwards [h] with ω hω
    rw [hint] at hω
    simpa only [colTotal_eq_sum] using hω
  have hYae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (a, b)) := by
    filter_upwards [ae_all_iff.2 hrow, ae_all_iff.2 hcol] with ω h1 h2
    exact (tendsto_pi_nhds.2 h1).prodMk_nhds (tendsto_pi_nhds.2 h2)
  have hYm : TendstoInMeasure P Y atTop (fun _ ↦ (a, b)) :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hYmeas n).aestronglyMeasurable) hYae
  -- Slutsky's theorem
  have hvec := tendstoInDistribution_pearsonSum hp hpsum hmeas hind hident hprob'
  have hsl := hvec.continuous_comp_prodMk_of_tendstoInMeasure_const (continuous_indepG a b hδ) hYm
    fun n ↦ (hYmeas n).aemeasurable
  -- the statistic and `G` agree eventually, almost surely
  have hGmeas : ∀ n, Measurable fun ω ↦ indepG a b δ (pearsonSum p C n ω, Y n ω) := fun n ↦
    (continuous_indepG a b hδ).measurable.comp ((measurable_pearsonSum hmeas n).prodMk (hYmeas n))
  have hdiff : TendstoInMeasure P
      (independenceStatistic C - fun n ω ↦ indepG a b δ (pearsonSum p C n ω, Y n ω)) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((measurable_independenceStatistic hmeas n).sub (hGmeas n)).aestronglyMeasurable) ?_
    filter_upwards [hYae] with ω hω
    have h1 : ∀ i j, ∀ᶠ n in atTop, δ ≤ (Y n ω).1 i * (Y n ω).2 j := by
      intro i j
      have ht : Tendsto (fun n ↦ (Y n ω).1 i * (Y n ω).2 j) atTop (𝓝 (a i * b j)) :=
        ((continuous_apply i).continuousAt.tendsto.comp (hω.fst_nhds)).mul
          ((continuous_apply j).continuousAt.tendsto.comp (hω.snd_nhds))
      exact (ht.eventually (lt_mem_nhds (hδlt i j))).mono fun n hn ↦ hn.le
    have h2 : ∀ᶠ n in atTop, ∀ i j, δ ≤ (Y n ω).1 i * (Y n ω).2 j :=
      eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ h1 i j
    have hev : ∀ᶠ n in atTop,
        (independenceStatistic C - fun n ω ↦ indepG a b δ (pearsonSum p C n ω, Y n ω)) n ω = 0 := by
      filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
      rw [Pi.sub_apply, Pi.sub_apply, sub_eq_zero]
      exact independenceStatistic_eq_indepG ha hb hasum hbsum hδ C (by omega) ω hn
    exact tendsto_const_nhds.congr' (hev.mono fun n hn ↦ hn.symm)
  have hconv := tendstoInDistribution_of_tendstoInMeasure_sub (independenceStatistic C) _ hsl hdiff
    fun n ↦ (measurable_independenceStatistic hmeas n).aemeasurable
  -- the law of the limit
  have hlim : (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1).map
      (fun z ↦ indepG a b δ (pearsonLimit p z, (a, b))) = chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1)) := by
    have hα : ∑ i, (fun i ↦ √(a i)) i ^ 2 = 1 := by
      simp_rw [sq_sqrt (ha _).le]
      exact hasum
    have hβ : ∑ j, (fun j ↦ √(b j)) j ^ 2 = 1 := by
      simp_rw [sq_sqrt (hb _).le]
      exact hbsum
    rw [← (hasLaw_tableProj_chiSquared hr hc _ _ hα hβ).map_eq]
    congr 1
    funext z
    exact indepG_pearsonLimit ha hb hasum hbsum (fun i j ↦ (hδlt i j).le) z
  exact TendstoInDistribution.of_map_eq_limit hconv hW.aemeasurable (by rw [hW.map_eq, hlim])

end Main

end UndergradKB.Statistics
