import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Statistics.StudentT
import UndergradKB.Statistics.Data

/-!
# The sample mean and sample variance of a normal sample

OpenStax *Introductory Statistics 2e* uses three facts about a simple random sample `X₁, …, Xₙ` from a normal
population `N(μ, σ)` (`n ≥ 2`):
* §7.1: the sample mean `x̄` is exactly normal with mean `μ` and standard deviation `σ/√n`
  (`hasLaw_sampleMean_normal`);
* §11.6: `(n - 1) s² / σ²` has the chi-square law with `n - 1` degrees of freedom
  (`hasLaw_sampleVariance_chiSquared`), which justifies the test of a single variance;
* §8.2 and §9.3: `(x̄ - μ) / (s / √n)` has the Student t law with `n - 1` degrees of freedom
  (`hasLaw_tStatistic`), which justifies the t interval and the t test.
Behind the last two is the independence of `x̄` and `s²` (`indepFun_sampleMean_sampleVariance`).

The proof is the classical rotation argument (Helmert): standardize to `Zᵢ = (Xᵢ - μ)/σ`; the vector `Z` is
standard Gaussian on `ℝⁿ`; choose an orthonormal basis `b` of `ℝⁿ` whose first vector is `(1, …, 1)/√n`; the
coordinates `Wⱼ = ⟪bⱼ, Z⟫` are again independent standard normal (`stdGaussian_map`), `W₀ = √n z̄` and
`∑ (Zᵢ - z̄)² = ∑_{j ≠ 0} Wⱼ²`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### Rotating a standard normal sample -/

section Rotation

variable {n : ℕ}

/-- The coordinates of a vector in an orthonormal basis of `ℝⁿ`, as a map `(Fin n → ℝ) → (Fin n → ℝ)`. -/
noncomputable def rotate (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j ↦ ∑ i, b j i * x i

lemma rotate_eq (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (x : Fin n → ℝ) :
    rotate b x = WithLp.ofLp (b.repr (WithLp.toLp 2 x)) := by
  ext j
  simp [rotate, OrthonormalBasis.repr_apply_apply, PiLp.inner_apply, mul_comm]

@[fun_prop]
lemma measurable_rotate (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    Measurable (rotate b) := by
  unfold rotate; fun_prop

/-- Rotation preserves the standard Gaussian law on `ℝⁿ` (product of standard normals). -/
lemma map_rotate_pi (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map (rotate b) =
      Measure.pi fun _ : Fin n ↦ gaussianReal 0 1 := by
  have hf : rotate b = WithLp.ofLp ∘ b.repr ∘ WithLp.toLp 2 := funext (rotate_eq b)
  have h1 : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by fun_prop
  have h2 : Measurable (b.repr : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
    b.repr.continuous.measurable
  have h3 : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by fun_prop
  rw [hf, ← Measure.map_map h3 (h2.comp h1), ← Measure.map_map h2 h1, map_pi_eq_stdGaussian,
    stdGaussian_map b.repr, ← map_pi_eq_stdGaussian, Measure.map_map h3 h1]
  exact Measure.map_id

/-- The sum of squares is preserved by rotation: `∑ⱼ (b x)ⱼ² = ∑ᵢ xᵢ²`. -/
lemma sum_sq_rotate (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (x : Fin n → ℝ) :
    ∑ j, rotate b x j ^ 2 = ∑ i, x i ^ 2 := by
  have h := b.repr.norm_map (WithLp.toLp 2 x)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq] at h
  rw [rotate_eq]
  simpa using h

/-- If `Z₁, …, Zₙ` are independent standard normal variables and `b` is an orthonormal basis, the coordinates
`Wⱼ = ∑ᵢ bⱼᵢ Zᵢ` are again independent standard normal variables. -/
theorem iIndepFun_rotate [IsProbabilityMeasure P] {Z : Fin n → Ω → ℝ} (hmeas : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    iIndepFun (fun j ω ↦ rotate b (fun i ↦ Z i ω) j) P ∧
      ∀ j, HasLaw (fun ω ↦ rotate b (fun i ↦ Z i ω) j) (gaussianReal 0 1) P := by
  have hZm : Measurable fun ω i ↦ Z i ω := Measurable.of_eval hmeas
  have hZv : P.map (fun ω i ↦ Z i ω) = Measure.pi fun _ : Fin n ↦ gaussianReal 0 1 := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hmeas i).aemeasurable).1 hind]
    congr
    funext i
    exact (hZ i).map_eq
  have hWv : P.map (fun ω ↦ rotate b (fun i ↦ Z i ω)) = Measure.pi fun _ : Fin n ↦ gaussianReal 0 1 := by
    rw [← map_rotate_pi b, ← hZv, Measure.map_map (measurable_rotate b) hZm]
    rfl
  have hWj : ∀ j, HasLaw (fun ω ↦ rotate b (fun i ↦ Z i ω) j) (gaussianReal 0 1) P := by
    intro j
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω ↦ rotate b (fun i ↦ Z i ω) j) = Function.eval j ∘ fun ω ↦ rotate b (fun i ↦ Z i ω) :=
      rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (by fun_prop), hWv, Measure.pi_map_eval]
    simp
  refine ⟨(iIndepFun_iff_map_fun_eq_pi_map fun j ↦ (hWj j).aemeasurable).2 ?_, hWj⟩
  rw [hWv]
  congr
  funext j
  exact (hWj j).map_eq.symm

end Rotation

/-! ### The basis whose first vector is the normalized all-ones vector -/

section Helmert

variable {n : ℕ}

/-- There is an orthonormal basis of `ℝⁿ` whose vector of index `i₀` is `(1, …, 1)/√n`. -/
lemma exists_orthonormalBasis_ones (i₀ : Fin n) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      b i₀ = WithLp.toLp 2 (fun _ ↦ 1 / √n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i₀
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (by simp) (v := fun _ : Fin n ↦ WithLp.toLp 2 (fun _ ↦ 1 / √n))
    (s := {i₀}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [mem_singleton_iff] at hi hj
      subst hi hj
      simp only [Set.domRestrict_apply, ite_true, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [div_mul_div_comm, one_mul, mul_self_sqrt hn.le]
      field_simp)
  exact ⟨b, hb i₀ rfl⟩

/-- With such a basis, the `i₀` coordinate of `x` is `√n · x̄`. -/
lemma rotate_ones (i₀ : Fin n) {b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    (hb : b i₀ = WithLp.toLp 2 (fun _ ↦ 1 / √n)) (x : Fin n → ℝ) :
    rotate b x i₀ = √n * mean x := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i₀
  have hs : 0 < √(n : ℝ) := sqrt_pos.2 hn
  simp only [rotate, hb, mean]
  rw [← Finset.mul_sum]
  field_simp
  rw [sq_sqrt hn.le]
  ring

/-- `∑ (xᵢ - x̄)² = ∑ xᵢ² - n x̄²`. -/
lemma sumSqDev_eq_sum_sq_sub (x : Fin n → ℝ) : sumSqDev x = ∑ i, x i ^ 2 - n * mean x ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sumSqDev]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hsum : ∑ i, x i = n * mean x := by simp only [mean]; field_simp
  simp only [sumSqDev, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- With such a basis, `∑ (xᵢ - x̄)² = ∑_{j ≠ i₀} (b x)ⱼ²`. -/
lemma sumSqDev_eq_sum_erase_rotate (i₀ : Fin n) {b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    (hb : b i₀ = WithLp.toLp 2 (fun _ ↦ 1 / √n)) (x : Fin n → ℝ) :
    sumSqDev x = ∑ j ∈ univ.erase i₀, rotate b x j ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i₀
  rw [Finset.sum_erase_eq_sub (mem_univ _), sum_sq_rotate, rotate_ones i₀ hb, mul_pow, sq_sqrt hn.le,
    sumSqDev_eq_sum_sq_sub]

end Helmert

/-! ### The normal sample -/

section NormalSample

variable {n : ℕ} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Standardizing a normal variable: if `X ~ N(μ, σ)` (variance `σ²`), then `(X - μ)/σ ~ N(0, 1)`. -/
lemma hasLaw_standardize {X : Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hX : HasLaw X (gaussianReal μ (σ ^ 2).toNNReal) P) :
    HasLaw (fun ω ↦ (X ω - μ) / σ) (gaussianReal 0 1) P := by
  have h := gaussianReal_div_const (gaussianReal_sub_const hX μ) σ
  convert h using 2
  · simp
  · apply NNReal.eq
    rw [NNReal.coe_div, Real.coe_toNNReal _ (sq_nonneg σ)]
    simp [hσ.ne']

/-- The hypotheses of the book's normal-population results: `X₁, …, Xₙ` independent, each `N(μ, σ)`. -/
structure IsNormalSample (X : Fin n → Ω → ℝ) (μ σ : ℝ) (P : Measure Ω) : Prop where
  measurable : ∀ i, Measurable (X i)
  indep : iIndepFun X P
  hasLaw : ∀ i, HasLaw (X i) (gaussianReal μ (σ ^ 2).toNNReal) P

/-- The rotated standardized sample: independent standard normals `W`, with
`x̄ = μ + σ W_{i₀}/√n` and `(n - 1) s² = σ² ∑_{j ≠ i₀} Wⱼ²`. -/
lemma exists_rotation {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hX : IsNormalSample X μ σ P)
    (i₀ : Fin n) :
    ∃ W : Fin n → Ω → ℝ, (∀ j, Measurable (W j)) ∧ iIndepFun W P ∧
      (∀ j, HasLaw (W j) (gaussianReal 0 1) P) ∧
      (∀ ω, mean (fun i ↦ X i ω) = μ + σ * W i₀ ω / √n) ∧
      (∀ ω, sumSqDev (fun i ↦ X i ω) = σ ^ 2 * ∑ j ∈ univ.erase i₀, W j ω ^ 2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i₀
  set Z : Fin n → Ω → ℝ := fun i ω ↦ (X i ω - μ) / σ with hZdef
  have hZm : ∀ i, Measurable (Z i) := fun i ↦ by have := hX.measurable i; fun_prop
  have hZind : iIndepFun Z P := hX.indep.comp (fun _ x ↦ (x - μ) / σ) fun _ ↦ by fun_prop
  have hZlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P := fun i ↦ hasLaw_standardize hσ (hX.hasLaw i)
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_ones i₀
  obtain ⟨hWind, hWlaw⟩ := iIndepFun_rotate hZm hZind hZlaw b
  refine ⟨fun j ω ↦ rotate b (fun i ↦ Z i ω) j, fun j ↦ by fun_prop, hWind, hWlaw, fun ω ↦ ?_,
    fun ω ↦ ?_⟩
  · simp only
    rw [rotate_ones i₀ hb]
    have hmZ : mean (fun i ↦ Z i ω) = (mean (fun i ↦ X i ω) - μ) / σ := by
      simp only [hZdef, mean, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hmZ]
    have : 0 < √(n : ℝ) := sqrt_pos.2 hn
    field_simp
    ring
  · rw [← sumSqDev_eq_sum_erase_rotate i₀ hb]
    have hmZ : mean (fun i ↦ Z i ω) = (mean (fun i ↦ X i ω) - μ) / σ := by
      simp only [hZdef, mean, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    unfold sumSqDev
    rw [hmZ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hZdef]
    field_simp
    ring

/-- **The sample mean of a normal sample is normal** (§7.1). If `X₁, …, Xₙ` (`n ≥ 1`) are independent
`N(μ, σ)`, then `x̄` has the normal law with mean `μ` and variance `σ²/n` (standard deviation `σ/√n`). -/
@[kb "openstaxintrostats2e" "§7.1, p. 378"]
theorem hasLaw_sampleMean_normal {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ mean fun i ↦ X i ω) (gaussianReal μ (σ ^ 2 / n).toNNReal) P := by
  obtain ⟨W, -, -, hWlaw, hmean, -⟩ := exists_rotation hσ hX ⟨0, hn⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := gaussianReal_const_add (gaussianReal_const_mul (hWlaw ⟨0, hn⟩) (σ / √n)) μ
  have heq : (fun ω ↦ mean fun i ↦ X i ω) = fun ω ↦ μ + σ / √n * W ⟨0, hn⟩ ω := by
    funext ω
    rw [hmean ω]
    ring
  rw [heq]
  rw [show σ / √n * 0 + μ = μ by ring, mul_one] at h
  convert h using 2
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity)]
  simp [div_pow, sq_sqrt hn'.le]

/-- **Independence of the sample mean and the sample variance** for a normal sample (`n ≥ 2`). -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem indepFun_sampleMean_sampleVariance {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hn : 2 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) :
    IndepFun (fun ω ↦ mean fun i ↦ X i ω) (fun ω ↦ sampleVariance fun i ↦ X i ω) P := by
  set i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨W, hWm, hWind, -, hmean, hss⟩ := exists_rotation hσ hX i₀
  have hST : Disjoint ({i₀} : Finset (Fin n)) (univ.erase i₀) := by simp
  have h := hWind.indepFun_finset {i₀} (univ.erase i₀) hST hWm
  have hf : Measurable fun w : ({i₀} : Finset (Fin n)) → ℝ ↦ μ + σ * w ⟨i₀, mem_singleton_self _⟩ / √n := by
    fun_prop
  have hg : Measurable fun w : ↥(Finset.univ.erase i₀) → ℝ ↦
      σ ^ 2 * (∑ j, w j ^ 2) / ((n : ℝ) - 1) := by fun_prop
  have := h.comp hf hg
  convert this using 1
  · funext ω
    simp [hmean ω]
  · funext ω
    simp only [Function.comp_apply, sampleVariance, hss ω]
    congr 2
    exact (Finset.sum_coe_sort (univ.erase i₀) fun j ↦ W j ω ^ 2).symm

/-- **The chi-square law of the sample variance** (§11.6). If `X₁, …, Xₙ` (`n ≥ 2`) are independent `N(μ, σ)`,
then `(n - 1) s² / σ²` has the chi-square law with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.6, p. 593"]
theorem hasLaw_sampleVariance_chiSquared {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hn : 2 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ ((n : ℝ) - 1) * (sampleVariance fun i ↦ X i ω) / σ ^ 2) (chiSquared ((n : ℝ) - 1)) P := by
  set i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨W, hWm, hWind, hWlaw, -, hss⟩ := exists_rotation hσ hX i₀
  have hne : (univ.erase i₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have h := hasLaw_sum_sq_chiSquared hne hWm hWind fun j _ ↦ hWlaw j
  have hcard : ((univ.erase i₀).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp
  rw [hcard] at h
  convert h using 1
  funext ω
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp only [sampleVariance, hss ω]
  field_simp

/-- **The Student t law of the t statistic** (§8.2, §9.3). If `X₁, …, Xₙ` (`n ≥ 2`) are independent `N(μ, σ)`,
then `(x̄ - μ) / (s / √n)` has the Student t law with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§8.2, p. 427"]
theorem hasLaw_tStatistic {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hn : 2 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω) - μ) / (sampleStdDev (fun i ↦ X i ω) / √n))
      (studentT ((n : ℝ) - 1)) P := by
  set i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨W, hWm, hWind, hWlaw, hmean, hss⟩ := exists_rotation hσ hX i₀
  have hne : (univ.erase i₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hcard : ((univ.erase i₀).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hV := hasLaw_sum_sq_chiSquared hne hWm hWind fun j _ ↦ hWlaw j
  rw [hcard] at hV
  have hST : Disjoint ({i₀} : Finset (Fin n)) (univ.erase i₀) := by simp
  have hf : Measurable fun w : ({i₀} : Finset (Fin n)) → ℝ ↦ w ⟨i₀, mem_singleton_self _⟩ :=
    measurable_pi_apply _
  have hg : Measurable fun w : ↥(Finset.univ.erase i₀) → ℝ ↦ ∑ j, w j ^ 2 := by fun_prop
  have hind := (hWind.indepFun_finset {i₀} (univ.erase i₀) hST hWm).comp hf hg
  have hind' : IndepFun (W i₀) (fun ω ↦ ∑ j ∈ univ.erase i₀, W j ω ^ 2) P := by
    convert hind using 1
    · rfl
    funext ω
    exact (Finset.sum_coe_sort (univ.erase i₀) fun j ↦ W j ω ^ 2).symm
  have h := hasLaw_studentT hn1 (hWlaw i₀) hV hind'
  convert h using 1
  funext ω
  have hn0 : (0 : ℝ) < n := by linarith
  have hsn : 0 < √(n : ℝ) := sqrt_pos.2 hn0
  have hV0 : 0 ≤ ∑ j ∈ univ.erase i₀, W j ω ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  simp only [sampleStdDev, sampleVariance, hss ω, hmean ω]
  set S := ∑ j ∈ univ.erase i₀, W j ω ^ 2 with hS
  rw [show σ ^ 2 * S / ((n : ℝ) - 1) = σ ^ 2 * (S / ((n : ℝ) - 1)) by ring, sqrt_mul (sq_nonneg σ),
    sqrt_sq hσ.le]
  by_cases hV : √(S / ((n : ℝ) - 1)) = 0
  · simp [hV]
  field_simp
  ring

end NormalSample

end UndergradKB.Statistics
