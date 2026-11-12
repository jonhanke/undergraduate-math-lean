import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.FDistribution
import UndergradKB.Statistics.Anova

/-!
# The F test of one-way analysis of variance

OpenStax *Introductory Statistics 2e*, §13.1–13.2: for `k` groups from normal populations with a common standard
deviation, under the null hypothesis that all the group means are equal, the ratio
`F = MS_between / MS_within` has the F distribution with `k - 1` and `n - k` degrees of freedom.

Model (the book's assumptions under the null hypothesis): observations `Y₁, …, Yₙ` independent `N(μ, σ)`, with a
group label `g : Fin n → Fin k`, every group nonempty, `2 ≤ k < n`.

Proof: rotate the standardized sample by an orthonormal basis of `ℝⁿ` whose first `k` vectors span the group
indicators, the first of them being `(1, …, 1)/√n` (an orthonormal basis `c` of `ℝᵏ` with first vector
`(√(nⱼ/n))ⱼ`, transported by `a ↦ (a_{g i} / √n_{g i})ᵢ`). Then `SS_between` is the sum of squares of the
coordinates `1, …, k - 1` and `SS_within` that of the coordinates `k, …, n - 1`: independent chi-square variables.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n k : ℕ}

/-! ### Sums over groups -/

lemma sum_comp_group (g : Fin n → Fin k) (F : Fin k → ℝ) :
    ∑ i, F (g i) = ∑ j, (groupSize g j : ℝ) * F j := by
  rw [← Finset.sum_fiberwise univ g]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2], sum_const, nsmul_eq_mul]
  rfl

lemma sum_groupSize (g : Fin n → Fin k) : ∑ j, (groupSize g j : ℝ) = n := by
  have h := sum_comp_group g (fun _ ↦ (1 : ℝ))
  simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [← h]

/-- The group sum `Sⱼ = ∑_{g i = j} zᵢ`. -/
noncomputable def groupSum (z : Fin n → ℝ) (g : Fin n → Fin k) (j : Fin k) : ℝ :=
  ∑ i ∈ univ.filter (fun i ↦ g i = j), z i

lemma sum_mul_comp_group (g : Fin n → Fin k) (F : Fin k → ℝ) (z : Fin n → ℝ) :
    ∑ i, F (g i) * z i = ∑ j, F j * groupSum z g j := by
  rw [← Finset.sum_fiberwise univ g]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2], ← Finset.mul_sum]
  rfl

/-- `SS_between = ∑ⱼ Sⱼ²/nⱼ - n z̄²` when every group is nonempty. -/
lemma ssBetween_eq (z : Fin n → ℝ) (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j) :
    ssBetween z g = ∑ j, groupSum z g j ^ 2 / groupSize g j - n * mean z ^ 2 := by
  have hn : ∑ j, groupSum z g j = ∑ i, z i := by
    have := sum_mul_comp_group g (fun _ ↦ (1 : ℝ)) z
    simpa using this.symm
  have hgm : ∀ j, groupMean z g j = groupSum z g j / groupSize g j := fun j ↦ rfl
  have hsum : ∑ i, z i = n * mean z := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [mean]
    simp only [mean]
    field_simp
  simp only [ssBetween, hgm]
  have e : ∀ j, (groupSize g j : ℝ) * (groupSum z g j / groupSize g j - mean z) ^ 2 =
      groupSum z g j ^ 2 / groupSize g j - 2 * mean z * groupSum z g j + groupSize g j * mean z ^ 2 := by
    intro j
    have : (groupSize g j : ℝ) ≠ 0 := by have := hg j; positivity
    field_simp
    ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hn,
    hsum, sum_groupSize]
  ring

/-! ### The basis adapted to the groups -/

/-- The vector of `ℝⁿ` attached to `a ∈ ℝᵏ`: `(a_{g i} / √n_{g i})ᵢ`. -/
noncomputable def groupLift (g : Fin n → Fin k) (a : Fin k → ℝ) : Fin n → ℝ :=
  fun i ↦ a (g i) / √(groupSize g (g i))

lemma inner_groupLift (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j) (a a' : Fin k → ℝ) :
    ∑ i, groupLift g a i * groupLift g a' i = ∑ j, a j * a' j := by
  have := sum_comp_group g (fun j ↦ a j / √(groupSize g j) * (a' j / √(groupSize g j)))
  simp only [groupLift]
  rw [this]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h0 : (0 : ℝ) < groupSize g j := by exact_mod_cast hg j
  rw [div_mul_div_comm, mul_self_sqrt h0.le]
  field_simp

lemma sum_groupLift_mul (g : Fin n → Fin k) (a : Fin k → ℝ) (z : Fin n → ℝ) :
    ∑ i, groupLift g a i * z i = ∑ j, a j * (groupSum z g j / √(groupSize g j)) := by
  have := sum_mul_comp_group g (fun j ↦ a j / √(groupSize g j)) z
  simp only [groupLift]
  rw [this]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

lemma natCast_pos_of_groupSize (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j) (j₀ : Fin k) :
    (0 : ℝ) < n := by
  rw [← sum_groupSize g]
  exact Finset.sum_pos (fun j _ ↦ by exact_mod_cast hg j) ⟨j₀, mem_univ _⟩

/-- An orthonormal basis of `ℝᵏ` whose first vector is `(√(nⱼ/n))ⱼ`. -/
lemma exists_basis_groupWeights (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j) (j₀ : Fin k) :
    ∃ c : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)),
      c j₀ = WithLp.toLp 2 (fun j ↦ √(groupSize g j / n)) := by
  have hn := natCast_pos_of_groupSize g hg j₀
  obtain ⟨c, hc⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin k)) (by simp)
    (v := fun _ : Fin k ↦ WithLp.toLp 2 (fun j ↦ √(groupSize g j / n))) (s := {j₀}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [mem_singleton_iff] at hi hj
      subst hi hj
      simp only [Set.domRestrict_apply, ite_true, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [Finset.sum_congr rfl fun j _ ↦ mul_self_sqrt (by positivity), ← Finset.sum_div,
        sum_groupSize, div_self hn.ne'])
  exact ⟨c, hc j₀ rfl⟩

/-- An orthonormal basis `b` of `ℝⁿ` whose vector of index `m < k` is the lift of the `m`-th vector of a basis `c`
of `ℝᵏ` with first vector `(√(nⱼ/n))ⱼ`. -/
lemma exists_basis_groups (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j) (hkn : k ≤ n) (j₀ : Fin k) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
      (c : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))),
      c j₀ = WithLp.toLp 2 (fun j ↦ √(groupSize g j / n)) ∧
      ∀ m : Fin k, b (Fin.castLE hkn m) = WithLp.toLp 2 (groupLift g fun j ↦ c m j) := by
  obtain ⟨c, hc0⟩ := exists_basis_groupWeights g hg j₀
  have hc := orthonormal_iff_ite.1 c.orthonormal
  set v : Fin n → EuclideanSpace ℝ (Fin n) := fun i ↦
    if h : i.val < k then WithLp.toLp 2 (groupLift g fun j ↦ c ⟨i.val, h⟩ j) else 0 with hv
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (by simp) (v := v) (s := {i | i.val < k}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨i', hi'⟩
      have hi2 : i.val < k := hi
      have hi2' : i'.val < k := hi'
      have key := hc ⟨i.val, hi2⟩ ⟨i'.val, hi2'⟩
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at key
      simp only [Set.domRestrict_apply, hv, dif_pos hi2, dif_pos hi2', PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial]
      rw [inner_groupLift g hg, key]
      congr 1
      simp [Fin.ext_iff, Subtype.ext_iff])
  refine ⟨b, c, hc0, fun m ↦ ?_⟩
  rw [hb (Fin.castLE hkn m) (by simp)]
  simp [hv]

/-- The coordinates of index `m < k`: `(b z)_m = (c a)_m` with `aⱼ = Sⱼ / √nⱼ`. -/
lemma rotate_castLE (g : Fin n → Fin k) (hkn : k ≤ n)
    {b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    {c : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))}
    (hb : ∀ m : Fin k, b (Fin.castLE hkn m) = WithLp.toLp 2 (groupLift g fun j ↦ c m j))
    (z : Fin n → ℝ) (m : Fin k) :
    rotate b z (Fin.castLE hkn m) = rotate c (fun j ↦ groupSum z g j / √(groupSize g j)) m := by
  simp only [rotate, hb, PiLp.toLp_apply]
  exact sum_groupLift_mul g _ z

lemma rotate_groupWeights (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j) (j₀ : Fin k)
    {c : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))}
    (hc : c j₀ = WithLp.toLp 2 (fun j ↦ √(groupSize g j / n))) (z : Fin n → ℝ) :
    rotate c (fun j ↦ groupSum z g j / √(groupSize g j)) j₀ = √n * mean z := by
  have hn := natCast_pos_of_groupSize g hg j₀
  have hsum : ∑ j, groupSum z g j = ∑ i, z i := by
    have := sum_mul_comp_group g (fun _ ↦ (1 : ℝ)) z
    simpa using this.symm
  have e : ∀ j, √(groupSize g j / n) * (groupSum z g j / √(groupSize g j)) = groupSum z g j / √n := by
    intro j
    have h0 : (0 : ℝ) < groupSize g j := by exact_mod_cast hg j
    have : 0 < √(groupSize g j : ℝ) := sqrt_pos.2 h0
    rw [sqrt_div h0.le]
    field_simp
  simp only [rotate, hc, PiLp.toLp_apply]
  rw [Finset.sum_congr rfl fun j _ ↦ e j, ← Finset.sum_div, hsum, mean]
  have : 0 < √(n : ℝ) := sqrt_pos.2 hn
  field_simp
  rw [sq_sqrt hn.le]

/-- `SS_between` and `SS_within` as sums of squared coordinates. -/
lemma ss_eq_sum_rotate (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j) (hkn : k ≤ n) (j₀ : Fin k)
    {b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))}
    {c : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))}
    (hc : c j₀ = WithLp.toLp 2 (fun j ↦ √(groupSize g j / n)))
    (hb : ∀ m : Fin k, b (Fin.castLE hkn m) = WithLp.toLp 2 (groupLift g fun j ↦ c m j))
    (z : Fin n → ℝ) :
    ssBetween z g = ∑ i ∈ (univ.erase j₀).map (Fin.castLEEmb hkn), rotate b z i ^ 2 ∧
      ssWithin z g = ∑ i ∈ (univ.map (Fin.castLEEmb hkn))ᶜ, rotate b z i ^ 2 := by
  have hn := natCast_pos_of_groupSize g hg j₀
  set a : Fin k → ℝ := fun j ↦ groupSum z g j / √(groupSize g j) with ha
  have hsa : ∑ j, a j ^ 2 = ∑ j, groupSum z g j ^ 2 / groupSize g j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h0 : (0 : ℝ) < groupSize g j := by exact_mod_cast hg j
    rw [ha, div_pow, sq_sqrt h0.le]
  have hrot : ∀ m : Fin k, rotate b z (Fin.castLE hkn m) = rotate c a m := rotate_castLE g hkn hb z
  have hC : ∑ i ∈ univ.map (Fin.castLEEmb hkn), rotate b z i ^ 2 =
      ∑ j, groupSum z g j ^ 2 / groupSize g j := by
    rw [Finset.sum_map]
    simp only [Fin.castLEEmb_apply, hrot]
    rw [sum_sq_rotate, hsa]
  have hB : ssBetween z g = ∑ i ∈ (univ.erase j₀).map (Fin.castLEEmb hkn), rotate b z i ^ 2 := by
    rw [ssBetween_eq z g hg, Finset.sum_map, ← hsa, ← sum_sq_rotate c a,
      ← Finset.add_sum_erase _ _ (mem_univ j₀)]
    simp only [Fin.castLEEmb_apply, hrot]
    rw [ha, rotate_groupWeights g hg j₀ hc z, mul_pow, sq_sqrt hn.le]
    ring
  refine ⟨hB, ?_⟩
  have htot := sumSqDev_eq_ssBetween_add_ssWithin z g
  have hss := sumSqDev_eq_sum_sq_sub z
  have hall := sum_sq_rotate b z
  rw [← Finset.sum_add_sum_compl (univ.map (Fin.castLEEmb hkn)), hC] at hall
  rw [ssBetween_eq z g hg] at htot
  linarith

/-! ### The F statistic of a normal sample -/

lemma groupMean_standardize (y : Fin n → ℝ) (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j)
    {μ σ : ℝ} (hσ : 0 < σ) (j : Fin k) :
    groupMean (fun i ↦ (y i - μ) / σ) g j = (groupMean y g j - μ) / σ := by
  have h0 : (groupSize g j : ℝ) ≠ 0 := by have := hg j; positivity
  have hc : ((univ.filter fun i ↦ g i = j).card : ℝ) = groupSize g j := rfl
  simp only [groupMean, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hc]
  field_simp

lemma mean_standardize (y : Fin n → ℝ) (hn : 0 < n) {μ σ : ℝ} (hσ : 0 < σ) :
    mean (fun i ↦ (y i - μ) / σ) = (mean y - μ) / σ := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp only [mean, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The F statistic does not change when the data are standardized. -/
lemma fStatistic_standardize (y : Fin n → ℝ) (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j)
    (hn : 0 < n) {μ σ : ℝ} (hσ : 0 < σ) :
    fStatistic (fun i ↦ (y i - μ) / σ) g = fStatistic y g := by
  have hB : ssBetween (fun i ↦ (y i - μ) / σ) g = ssBetween y g / σ ^ 2 := by
    simp only [ssBetween, groupMean_standardize y g hg hσ, mean_standardize y hn hσ, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
    ring
  have hW : ssWithin (fun i ↦ (y i - μ) / σ) g = ssWithin y g / σ ^ 2 := by
    simp only [ssWithin, groupMean_standardize y g hg hσ, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
    ring
  simp only [fStatistic, msBetween, msWithin, hB, hW]
  by_cases h : ssWithin y g = 0
  · simp [h]
  field_simp

/-- **The F test of one-way analysis of variance** (§13.2). Let `Y₁, …, Yₙ` be independent `N(μ, σ)` (the null
hypothesis: all group means equal, common standard deviation), with group labels `g : Fin n → Fin k`, every group
nonempty and `2 ≤ k < n`. Then `F = MS_between / MS_within` has the F distribution with `k - 1` and `n - k`
degrees of freedom. -/
@[kb "openstaxintrostats2e" "§13.2, p. 691"]
theorem hasLaw_fStatistic [IsProbabilityMeasure P] (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j)
    (hk : 2 ≤ k) (hkn : k < n) {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ fStatistic (fun i ↦ Y i ω) g) (fDistribution ((k : ℝ) - 1) ((n : ℝ) - k)) P := by
  set j₀ : Fin k := ⟨0, by omega⟩
  obtain ⟨b, c, hc0, hb⟩ := exists_basis_groups g hg hkn.le j₀
  set Z : Fin n → Ω → ℝ := fun i ω ↦ (Y i ω - μ) / σ with hZdef
  have hZm : ∀ i, Measurable (Z i) := fun i ↦ by have := hY.measurable i; fun_prop
  have hZind : iIndepFun Z P := hY.indep.comp (fun _ y ↦ (y - μ) / σ) fun _ ↦ by fun_prop
  have hZlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P := fun i ↦ hasLaw_standardize hσ (hY.hasLaw i)
  obtain ⟨hWind, hWlaw⟩ := iIndepFun_rotate hZm hZind hZlaw b
  set W : Fin n → Ω → ℝ := fun j ω ↦ rotate b (fun i ↦ Z i ω) j with hWdef
  have hWm : ∀ j, Measurable (W j) := fun j ↦ by simp only [hWdef]; fun_prop
  set A : Finset (Fin n) := (univ.erase j₀).map (Fin.castLEEmb hkn.le) with hA
  set B : Finset (Fin n) := (univ.map (Fin.castLEEmb hkn.le))ᶜ with hB
  have h2k : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hnk : (0 : ℝ) < (n : ℝ) - k := by linarith
  have hAc : (A.card : ℝ) = (k : ℝ) - 1 := by
    rw [hA, Finset.card_map, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.cast_sub (by omega)]
    simp
  have hBc : (B.card : ℝ) = (n : ℝ) - k := by
    rw [hB, Finset.card_compl, Finset.card_map, Finset.card_univ, Fintype.card_fin, Fintype.card_fin,
      Nat.cast_sub hkn.le]
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < A.card := by rw [hAc]; exact hk1
    exact_mod_cast this
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < B.card := by rw [hBc]; exact hnk
    exact_mod_cast this
  have hU := hasLaw_sum_sq_chiSquared hAne hWm hWind fun j _ ↦ hWlaw j
  have hV := hasLaw_sum_sq_chiSquared hBne hWm hWind fun j _ ↦ hWlaw j
  rw [hAc] at hU
  rw [hBc] at hV
  have hAB : Disjoint A B := by
    rw [hA, hB]
    exact Finset.disjoint_left.2 fun i hiA hiB ↦
      (Finset.mem_compl.1 hiB) (Finset.map_subset_map.2 (Finset.erase_subset _ _) hiA)
  have hf : Measurable fun w : ↥A → ℝ ↦ ∑ j, w j ^ 2 := by fun_prop
  have hg' : Measurable fun w : ↥B → ℝ ↦ ∑ j, w j ^ 2 := by fun_prop
  have hind := (hWind.indepFun_finset A B hAB hWm).comp hf hg'
  have hind' : IndepFun (fun ω ↦ ∑ j ∈ A, W j ω ^ 2) (fun ω ↦ ∑ j ∈ B, W j ω ^ 2) P := by
    convert hind using 1
    · funext ω
      exact (Finset.sum_coe_sort A fun j ↦ W j ω ^ 2).symm
    · funext ω
      exact (Finset.sum_coe_sort B fun j ↦ W j ω ^ 2).symm
  have h : HasLaw (fun ω ↦ ((∑ j ∈ A, W j ω ^ 2) / ((k : ℝ) - 1)) /
      ((∑ j ∈ B, W j ω ^ 2) / ((n : ℝ) - k))) (fDistribution ((k : ℝ) - 1) ((n : ℝ) - k)) P :=
    hasLaw_fDistribution hk1 hnk hU hV hind'
  convert h using 1
  funext ω
  rw [← fStatistic_standardize (fun i ↦ Y i ω) g hg (by omega) hσ (μ := μ)]
  obtain ⟨h1, h2⟩ := ss_eq_sum_rotate g hg hkn.le j₀ hc0 hb (fun i ↦ Z i ω)
  simp only [fStatistic, msBetween, msWithin]
  rw [show (fun i ↦ (Y i ω - μ) / σ) = fun i ↦ Z i ω from rfl, h1, h2]

end UndergradKB.Statistics
