import UndergradKB.Statistics.NormalSample

/-!
# The test of significance of the correlation coefficient

OpenStax *Introductory Statistics 2e*, §12.4: to test whether the population correlation is zero one uses
`t = r √(n - 2) / √(1 - r²)`, which under the null hypothesis has the Student t law with `n - 2` degrees of freedom.
The book's assumptions (§12.4): the `x` values are given; for each `x` the `y` value is normal, with the same
standard deviation, independently; under the null hypothesis the mean of `y` does not depend on `x`. So the model is:
`x : Fin n → ℝ` fixed and not constant, `Y₁, …, Yₙ` independent `N(μ, σ)` (`IsNormalSample`).

Proof: rotate the standardized sample by an orthonormal basis whose first two vectors are `(1, …, 1)/√n` and the
normalized centered `x`; then `r = W₁ / √(W₁² + R)` with `R = ∑_{j ≥ 2} Wⱼ²` chi-square with `n - 2` degrees of
freedom independent of `W₁`, and `t = W₁ / √(R / (n - 2))`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

/-- The normalized centered data vector `(xᵢ - x̄) / √Sxx`. -/
noncomputable def centeredUnit (x : Fin n → ℝ) : Fin n → ℝ := fun i ↦ (x i - mean x) / √(sumSqDev x)

lemma sumProdDev_eq_sum_centered (x y : Fin n → ℝ) :
    sumProdDev x y = ∑ i, (x i - mean x) * y i := by
  have h := sum_sub_mean x
  simp only [sumProdDev, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h, zero_mul, sub_zero]

/-- An orthonormal basis of `ℝⁿ` containing `(1, …, 1)/√n` and the normalized centered `x`. -/
lemma exists_orthonormalBasis_ones_centered {i₀ i₁ : Fin n} (h01 : i₀ ≠ i₁) (x : Fin n → ℝ)
    (hx : 0 < sumSqDev x) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      b i₀ = WithLp.toLp 2 (fun _ ↦ 1 / √n) ∧ b i₁ = WithLp.toLp 2 (centeredUnit x) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i₀
  have hsx : 0 < √(sumSqDev x) := sqrt_pos.2 hx
  set v : Fin n → EuclideanSpace ℝ (Fin n) := fun i ↦
    if i = i₀ then WithLp.toLp 2 (fun _ ↦ 1 / √n) else WithLp.toLp 2 (centeredUnit x) with hv
  have h00 : inner ℝ (v i₀) (v i₀) = (1 : ℝ) := by
    simp only [hv, ite_true, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_mul_div_comm, one_mul, mul_self_sqrt hn.le]
    field_simp
  have h11 : inner ℝ (v i₁) (v i₁) = (1 : ℝ) := by
    simp only [hv, if_neg h01.symm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, centeredUnit]
    have e : ∀ i, (x i - mean x) / √(sumSqDev x) * ((x i - mean x) / √(sumSqDev x)) =
        (x i - mean x) ^ 2 / sumSqDev x := fun i ↦ by rw [div_mul_div_comm, mul_self_sqrt hx.le, sq]
    simp_rw [e]
    rw [← Finset.sum_div, div_eq_one_iff_eq hx.ne']
    rfl
  have h01' : inner ℝ (v i₀) (v i₁) = (0 : ℝ) := by
    simp only [hv, ite_true, if_neg h01.symm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      centeredUnit]
    rw [← Finset.sum_mul, ← Finset.sum_div, sum_sub_mean, zero_div, zero_mul]
  have h10' : inner ℝ (v i₁) (v i₀) = (0 : ℝ) := by rw [real_inner_comm, h01']
  have n0 : ‖v i₀‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at h00
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h00
  have n1 : ‖v i₁‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at h11
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h11
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (by simp) (v := v) (s := {i₀, i₁}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hi hj
      simp only [Set.domRestrict_apply, Subtype.mk.injEq]
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · simp [n0]
      · simp [h01, h01']
      · simp [h01.symm, h10']
      · simp [n1])
  refine ⟨b, ?_, ?_⟩
  · rw [hb i₀ (by simp)]
    simp [hv]
  · rw [hb i₁ (by simp)]
    simp [hv, h01.symm]

/-- With such a basis, the `i₁` coordinate of `y` is `Sxy / √Sxx`. -/
lemma rotate_centered {i₁ : Fin n} (x : Fin n → ℝ)
    {b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    (hb : b i₁ = WithLp.toLp 2 (centeredUnit x)) (y : Fin n → ℝ) :
    rotate b y i₁ = sumProdDev x y / √(sumSqDev x) := by
  simp only [rotate, hb, centeredUnit, sumProdDev_eq_sum_centered, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The correlation is unchanged when `y` is replaced by `(y - μ)/σ`, `σ > 0`. -/
lemma correlation_standardize (hn : 0 < n) (x y : Fin n → ℝ) {μ σ : ℝ} (hσ : 0 < σ) :
    correlation x (fun i ↦ (y i - μ) / σ) = correlation x y := by
  have hm : mean (fun i ↦ (y i - μ) / σ) = (mean y - μ) / σ := by
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [mean, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hp : sumProdDev x (fun i ↦ (y i - μ) / σ) = sumProdDev x y / σ := by
    simp only [sumProdDev, hm, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
    ring
  have hs : sumSqDev (fun i ↦ (y i - μ) / σ) = sumSqDev y / σ ^ 2 := by
    simp only [sumSqDev, hm, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
    ring
  simp only [correlation, hp, hs]
  rw [show sumSqDev x * (sumSqDev y / σ ^ 2) = (sumSqDev x * sumSqDev y) / σ ^ 2 by ring,
    sqrt_div' _ (by positivity), sqrt_sq hσ.le]
  by_cases h0 : √(sumSqDev x * sumSqDev y) = 0
  · simp [h0]
  field_simp

/-- **The t test for the correlation coefficient** (§12.4). Let `x₁, …, xₙ` (`n ≥ 3`) be given, not all equal,
and let `Y₁, …, Yₙ` be independent `N(μ, σ)` (the null hypothesis: `y` does not depend on `x`). Then
`r √(n - 2) / √(1 - r²)`, with `r` the sample correlation of the pairs `(xᵢ, Yᵢ)`, has the Student t law with
`n - 2` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§12.4, p. 642"]
theorem hasLaw_correlation_tStatistic [IsProbabilityMeasure P] (x : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hn : 3 ≤ n) {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ correlation x (fun i ↦ Y i ω) * √((n : ℝ) - 2) /
      √(1 - correlation x (fun i ↦ Y i ω) ^ 2)) (studentT ((n : ℝ) - 2)) P := by
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  set Z : Fin n → Ω → ℝ := fun i ω ↦ (Y i ω - μ) / σ with hZdef
  have hZm : ∀ i, Measurable (Z i) := fun i ↦ by have := hY.measurable i; fun_prop
  have hZind : iIndepFun Z P := hY.indep.comp (fun _ y ↦ (y - μ) / σ) fun _ ↦ by fun_prop
  have hZlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P := fun i ↦ hasLaw_standardize hσ (hY.hasLaw i)
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_ones_centered h01 x hx
  obtain ⟨hWind, hWlaw⟩ := iIndepFun_rotate hZm hZind hZlaw b
  set W : Fin n → Ω → ℝ := fun j ω ↦ rotate b (fun i ↦ Z i ω) j with hWdef
  have hWm : ∀ j, Measurable (W j) := fun j ↦ by simp only [hWdef]; fun_prop
  set T : Finset (Fin n) := (univ.erase i₀).erase i₁ with hT
  have hcard : (T.card : ℝ) = (n : ℝ) - 2 := by
    rw [hT, Finset.card_erase_of_mem (by simp [h01.symm]), Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hne : T.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < T.card := by rw [hcard]; exact hn2
    exact_mod_cast this
  have hV := hasLaw_sum_sq_chiSquared hne hWm hWind fun j _ ↦ hWlaw j
  rw [hcard] at hV
  have hST : Disjoint ({i₁} : Finset (Fin n)) T := by simp [hT]
  have hf : Measurable fun w : ({i₁} : Finset (Fin n)) → ℝ ↦ w ⟨i₁, mem_singleton_self _⟩ :=
    measurable_pi_apply _
  have hg : Measurable fun w : ↥T → ℝ ↦ ∑ j, w j ^ 2 := by fun_prop
  have hind := (hWind.indepFun_finset {i₁} T hST hWm).comp hf hg
  have hind' : IndepFun (W i₁) (fun ω ↦ ∑ j ∈ T, W j ω ^ 2) P := by
    convert hind using 1
    · rfl
    funext ω
    exact (Finset.sum_coe_sort T fun j ↦ W j ω ^ 2).symm
  have h : HasLaw (fun ω ↦ W i₁ ω / √((∑ j ∈ T, W j ω ^ 2) / ((n : ℝ) - 2)))
      (studentT ((n : ℝ) - 2)) P := hasLaw_studentT hn2 (hWlaw i₁) hV hind'
  convert h using 1
  funext ω
  -- the identity `t = W₁ / √(R / (n - 2))`
  have hr : correlation x (fun i ↦ Y i ω) = W i₁ ω / √(W i₁ ω ^ 2 + ∑ j ∈ T, W j ω ^ 2) := by
    rw [← correlation_standardize (by omega) x (fun i ↦ Y i ω) hσ (μ := μ)]
    have hp : sumProdDev x (fun i ↦ (Y i ω - μ) / σ) = √(sumSqDev x) * W i₁ ω := by
      rw [show (fun i ↦ (Y i ω - μ) / σ) = fun i ↦ Z i ω from rfl]
      simp only [hWdef]
      rw [rotate_centered x hb1]
      field_simp [(sqrt_pos.2 hx).ne']
    have hs : sumSqDev (fun i ↦ (Y i ω - μ) / σ) = W i₁ ω ^ 2 + ∑ j ∈ T, W j ω ^ 2 := by
      have := sumSqDev_eq_sum_erase_rotate i₀ hb0 (fun i ↦ Z i ω)
      rw [show (fun i ↦ (Y i ω - μ) / σ) = fun i ↦ Z i ω from rfl, this, hT,
        ← Finset.add_sum_erase _ _ (by simp [h01.symm] : i₁ ∈ univ.erase i₀)]
    simp only [correlation, hp, hs]
    rw [sqrt_mul hx.le]
    by_cases h0 : √(W i₁ ω ^ 2 + ∑ j ∈ T, W j ω ^ 2) = 0
    · simp [h0]
    have : 0 < √(sumSqDev x) := sqrt_pos.2 hx
    field_simp
  rw [hr]
  set A := W i₁ ω
  set R := ∑ j ∈ T, W j ω ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  by_cases hS : A ^ 2 + R = 0
  · have hA : A = 0 := by nlinarith [sq_nonneg A]
    simp [hA]
  have hSpos : 0 < A ^ 2 + R := lt_of_le_of_ne (by positivity) (Ne.symm hS)
  have h1 : 1 - (A / √(A ^ 2 + R)) ^ 2 = R / (A ^ 2 + R) := by
    rw [div_pow, sq_sqrt hSpos.le]
    field_simp
    ring
  rw [h1, sqrt_div' _ hSpos.le, sqrt_div' _ hn2.le]
  by_cases hR0 : √R = 0
  · simp [hR0]
  have : 0 < √(A ^ 2 + R) := sqrt_pos.2 hSpos
  have : 0 < √((n : ℝ) - 2) := sqrt_pos.2 hn2
  field_simp

end UndergradKB.Statistics
