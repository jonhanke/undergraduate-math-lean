import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.ChiSquared

/-!
# Pearson's chi-square statistic (OpenStax *Introductory Statistics 2e*, §11.2)

A die with `k ≥ 2` faces (categories) shows face `i` with probability `pᵢ > 0`. After `n` independent rolls
let `Oᵢ` be the observed count of face `i` and `Eᵢ = n pᵢ` the expected count. The goodness-of-fit test of §11.2
uses the statistic `χ² = ∑ᵢ (Oᵢ - Eᵢ)² / Eᵢ` and refers it to the chi-square law with `k - 1` degrees of freedom.
`tendstoInDistribution_pearsonStatistic` proves that this is the limit law as `n → ∞`.

Proof (the classical one):
* write `(Oᵢ - n pᵢ)/√(n pᵢ) = n^{-1/2} ∑_{m<n} Yₘᵢ` with independent identically distributed vectors
  `Yₘ = ((1{Cₘ = i} - pᵢ)/√pᵢ)ᵢ`, so that `χ² = ‖n^{-1/2} ∑ Yₘ‖²`;
* multivariate central limit theorem: by the Cramér-Wold theorem (Mathlib) and the one-dimensional central
  limit theorem (Mathlib), `n^{-1/2} ∑ Yₘ` converges in distribution to the projection `G = Z - ⟪u, Z⟫ u` of a
  standard Gaussian vector `Z` along the unit vector `u = (√pᵢ)ᵢ`: both sides have, in every direction `t`,
  the centred normal law of variance `‖t‖² - ⟪u, t⟫²`;
* continuous mapping: `χ²` converges in distribution to `‖G‖²`;
* rotation: in an orthonormal basis whose vector `i₀` is `u`, `‖G‖² = ∑_{j ≠ i₀} Wⱼ²` with independent standard
  normal `Wⱼ`, so `‖G‖²` is chi-square with `k - 1` degrees of freedom (`hasLaw_sum_sq_chiSquared`).
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Finset Filter RealInnerProductSpace

/-! ### Linear combinations of independent standard normal variables -/

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {k : ℕ}

/-- There is an orthonormal basis of `ℝᵏ` whose vector of index `i₀` is a given unit vector `u`. -/
lemma exists_orthonormalBasis_eq (i₀ : Fin k) (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)), b i₀ = u := by
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin k)) (by simp) (v := fun _ : Fin k ↦ u) (s := {i₀}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi hj
      simp only [Set.domRestrict_apply, ite_true, real_inner_self_eq_norm_sq, hu, one_pow])
  exact ⟨b, hb i₀ rfl⟩

/-- If `Z₁, …, Z_k` are independent standard normal variables and `c ∈ ℝᵏ`, then `∑ cᵢ Zᵢ` is normal with mean
`0` and variance `∑ cᵢ²`. -/
lemma hasLaw_sum_mul_stdNormal [IsProbabilityMeasure P] {Z : Fin k → Ω → ℝ} (hmeas : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) (c : Fin k → ℝ) :
    HasLaw (fun ω ↦ ∑ i, c i * Z i ω) (gaussianReal 0 (∑ i, c i ^ 2).toNNReal) P := by
  set s : ℝ := ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin k))‖ with hs_def
  have hs2 : s ^ 2 = ∑ i, c i ^ 2 := by
    rw [hs_def, EuclideanSpace.real_norm_sq_eq]
  by_cases hs : s = 0
  · have hc : ∀ i, c i = 0 := by
      intro i
      have h0 : ∑ i, c i ^ 2 = 0 := by rw [← hs2, hs]; ring
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (c i))).1 h0 i (mem_univ _)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    simp only [hc, zero_mul, sum_const_zero]
    exact ⟨aemeasurable_const, by simp⟩
  · have hspos : 0 < s := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs)
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · exact absurd (by simp [hs_def, EuclideanSpace.norm_eq] : s = 0) hs
      · exact h
    set i₀ : Fin k := ⟨0, hk⟩
    set u : EuclideanSpace ℝ (Fin k) := s⁻¹ • WithLp.toLp 2 c with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_of_nonneg hspos.le, ← hs_def, inv_mul_cancel₀ hs]
    obtain ⟨b, hb⟩ := exists_orthonormalBasis_eq i₀ u hu
    obtain ⟨-, hW⟩ := iIndepFun_rotate hmeas hind hZ b
    have h := gaussianReal_const_mul (hW i₀) s
    have hfun : (fun ω ↦ ∑ i, c i * Z i ω) = fun ω ↦ s * rotate b (fun i ↦ Z i ω) i₀ := by
      funext ω
      simp only [rotate, hb, hu_def, PiLp.smul_apply, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      field_simp
    rw [hfun]
    convert h using 2
    · ring
    · ext
      simp [hs2, sum_nonneg (fun i _ ↦ sq_nonneg (c i))]

/-- `hasLaw_sum_mul_stdNormal` for independent standard normal variables indexed by any finite type. -/
lemma hasLaw_sum_mul_stdNormal_fintype {ι : Type*} [Fintype ι] [IsProbabilityMeasure P] {Z : ι → Ω → ℝ}
    (hmeas : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (c : ι → ℝ) :
    HasLaw (fun ω ↦ ∑ i, c i * Z i ω) (gaussianReal 0 (∑ i, c i ^ 2).toNNReal) P := by
  set e := Fintype.equivFin ι
  have h := hasLaw_sum_mul_stdNormal (Z := fun j ↦ Z (e.symm j)) (fun j ↦ hmeas _)
    (hind.precomp e.symm.injective) (fun j ↦ hZ _) (fun j ↦ c (e.symm j))
  have h1 : (fun ω ↦ ∑ j, c (e.symm j) * Z (e.symm j) ω) = fun ω ↦ ∑ i, c i * Z i ω :=
    funext fun ω ↦ e.symm.sum_comp (fun i ↦ c i * Z i ω)
  have h2 : ∑ j, c (e.symm j) ^ 2 = ∑ i, c i ^ 2 := e.symm.sum_comp (fun i ↦ c i ^ 2)
  rw [h1, h2] at h
  exact h

end Gaussian

/-- Convergence in distribution depends on the limit variable only through its law. -/
lemma TendstoInDistribution.of_map_eq_limit {ι E Ω Ω' Ω'' : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {μ'' : Measure Ω''} [IsProbabilityMeasure μ''] {X : ι → Ω → E} {l : Filter ι} {Z : Ω' → E}
    {W : Ω'' → E} (h : TendstoInDistribution X l Z (fun _ ↦ μ) μ') (hW : AEMeasurable W μ'')
    (heq : μ''.map W = μ'.map Z) :
    TendstoInDistribution X l W (fun _ ↦ μ) μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hW
  tendsto := by
    convert h.tendsto using 3
    exact congrArg nhds (Subtype.ext heq)

/-! ### Counts, the statistic, and its vector form -/

section Pearson

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {k : ℕ}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The observed count `Oᵢ` of category `i` among the first `n` observations `C 0, …, C (n-1)`. -/
noncomputable def observedCount (C : ℕ → Ω → ι) (n : ℕ) (i : ι) (ω : Ω) : ℝ :=
  ((range n).filter fun m ↦ C m ω = i).card

/-- Pearson's goodness-of-fit statistic `∑ᵢ (Oᵢ - Eᵢ)² / Eᵢ` with expected counts `Eᵢ = n pᵢ` (§11.2). -/
noncomputable def pearsonStatistic (p : ι → ℝ) (C : ℕ → Ω → ι) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, (observedCount C n i ω - n * p i) ^ 2 / (n * p i)

/-- The centred, scaled indicator vector `((1{c = i} - pᵢ)/√pᵢ)ᵢ` of one observation `c`. -/
noncomputable def pearsonVector (p : ι → ℝ) (c : ι) : EuclideanSpace ℝ (ι) :=
  WithLp.toLp 2 fun i ↦ ((if c = i then 1 else 0) - p i) / √(p i)

/-- `n^{-1/2}` times the sum of the vectors of the first `n` observations. -/
noncomputable def pearsonSum (p : ι → ℝ) (C : ℕ → Ω → ι) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (ι) :=
  (√(n : ℝ))⁻¹ • ∑ m ∈ range n, pearsonVector p (C m ω)

omit [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma pearsonStatistic_eq_norm_sq {p : ι → ℝ} (hp : ∀ i, 0 < p i) (C : ℕ → Ω → ι) (n : ℕ)
    (ω : Ω) : pearsonStatistic p C n ω = ‖pearsonSum p C n ω‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold pearsonStatistic
  refine sum_congr rfl fun i _ ↦ ?_
  have hO : ∑ m ∈ range n, ((if C m ω = i then (1 : ℝ) else 0) - p i) =
      observedCount C n i ω - n * p i := by
    rw [sum_sub_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul]
    rfl
  have hcoord : (pearsonSum p C n ω) i =
      (√(n : ℝ))⁻¹ * ((∑ m ∈ range n, ((if C m ω = i then (1 : ℝ) else 0) - p i)) / √(p i)) := by
    simp only [pearsonSum, pearsonVector, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
    rw [sum_div]
  rw [hcoord, hO, mul_pow, div_pow, inv_pow, sq_sqrt (Nat.cast_nonneg n), sq_sqrt (hp i).le]
  ring

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The inner product of the vector of observation `c` with a direction `t`. -/
lemma inner_pearsonVector {p : ι → ℝ} (c : ι) (t : EuclideanSpace ℝ (ι)) :
    ⟪pearsonVector p c, t⟫ = t c / √(p c) - ∑ i, √(p i) * t i := by
  have h : ∀ i, ((if c = i then (1 : ℝ) else 0) - p i) / √(p i) * t i =
      (if c = i then t c / √(p c) else 0) - √(p i) * t i := by
    intro i
    by_cases hci : c = i
    · subst hci
      simp only [ite_true]
      rw [sub_div, div_sqrt]
      ring
    · simp only [hci, ite_false]
      rw [zero_sub, neg_div, neg_mul, div_sqrt]
      ring
  simp only [pearsonVector, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [mul_comm (t _), h]
  rw [sum_sub_distrib, sum_ite_eq]
  simp

omit [DecidableEq ι] in
/-- The expectation of `g(C)` for a variable `C` with finitely many values. -/
lemma integral_comp_fin [IsProbabilityMeasure P] {C : Ω → ι} (hC : Measurable C) (g : ι → ℝ) :
    ∫ ω, g (C ω) ∂P = ∑ j, g j * P.real {ω | C ω = j} := by
  rw [← integral_map hC.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [map_measureReal_apply hC (measurableSet_singleton j), smul_eq_mul, mul_comm]
  rfl

/-! ### Mean and variance of one observation in a direction -/

omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma sum_dir_mul {p : ι → ℝ} (hsum : ∑ i, p i = 1) (t : EuclideanSpace ℝ (ι)) :
    ∑ j, (t j / √(p j) - ∑ i, √(p i) * t i) * p j = 0 := by
  have h : ∀ j, (t j / √(p j) - ∑ i, √(p i) * t i) * p j =
      √(p j) * t j - (∑ i, √(p i) * t i) * p j := by
    intro j
    rw [sub_mul, div_mul_eq_mul_div, mul_div_assoc, div_sqrt]
    ring
  rw [sum_congr rfl fun j _ ↦ h j, sum_sub_distrib, ← mul_sum, hsum, mul_one, sub_self]

private lemma sq_term {s q a m : ℝ} (hs : 0 < s) (hq : q = s ^ 2) :
    (a / s - m) ^ 2 * q = a ^ 2 - 2 * m * (s * a) + m ^ 2 * q := by
  subst hq
  field_simp
  ring

omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma sum_sq_dir_mul {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (t : EuclideanSpace ℝ (ι)) :
    ∑ j, (t j / √(p j) - ∑ i, √(p i) * t i) ^ 2 * p j = ∑ j, t j ^ 2 - (∑ i, √(p i) * t i) ^ 2 := by
  rw [sum_congr rfl fun j _ ↦ sq_term (sqrt_pos.2 (hp j)) (sq_sqrt (hp j).le).symm, sum_add_distrib,
    sum_sub_distrib, ← mul_sum, ← mul_sum, hsum]
  ring

omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma sum_sq_proj {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) (t : ι → ℝ) :
    ∑ i, (t i - (∑ j, √(p j) * t j) * √(p i)) ^ 2 = ∑ i, t i ^ 2 - (∑ j, √(p j) * t j) ^ 2 := by
  have h : ∀ i, (t i - (∑ j, √(p j) * t j) * √(p i)) ^ 2 =
      t i ^ 2 - 2 * (∑ j, √(p j) * t j) * (√(p i) * t i) + (∑ j, √(p j) * t j) ^ 2 * p i := by
    intro i
    have := sq_sqrt (hp i).le
    linear_combination (∑ j, √(p j) * t j) ^ 2 * this
  rw [sum_congr rfl fun i _ ↦ h i, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hsum]
  ring

/-- One observation `C` with `P(C = j) = pⱼ`: in a direction `t` its vector has mean `0`, is square integrable,
and has variance `‖t‖² - ⟪u, t⟫²` where `u = (√pᵢ)ᵢ`. -/
lemma pearson_moments [IsProbabilityMeasure P] {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    {C : Ω → ι} (hC : Measurable C) (hprob : ∀ j, P.real {ω | C ω = j} = p j)
    (t : EuclideanSpace ℝ (ι)) :
    P[fun ω ↦ ⟪pearsonVector p (C ω), t⟫] = 0 ∧ MemLp (fun ω ↦ ⟪pearsonVector p (C ω), t⟫) 2 P ∧
      Var[fun ω ↦ ⟪pearsonVector p (C ω), t⟫; P] = ∑ i, t i ^ 2 - (∑ i, √(p i) * t i) ^ 2 := by
  set g : ι → ℝ := fun c ↦ ⟪pearsonVector p c, t⟫ with hg
  have hgv : ∀ c, g c = t c / √(p c) - ∑ i, √(p i) * t i := fun c ↦ inner_pearsonVector c t
  have hmean : P[fun ω ↦ g (C ω)] = 0 := by
    rw [integral_comp_fin hC g]
    simp_rw [hprob, hgv]
    exact sum_dir_mul hsum t
  have hL : MemLp (fun ω ↦ g (C ω)) 2 P :=
    MemLp.of_bound ((measurable_of_finite g).comp hC).aestronglyMeasurable (∑ j, |g j|)
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs]
        exact single_le_sum (f := fun j ↦ |g j|) (fun j _ ↦ abs_nonneg (g j)) (mem_univ (C ω)))
  refine ⟨hmean, hL, ?_⟩
  rw [variance_eq_sub hL, hmean]
  have h2 : P[(fun ω ↦ g (C ω)) ^ 2] = ∑ j, g j ^ 2 * P.real {ω | C ω = j} :=
    integral_comp_fin hC (fun c ↦ g c ^ 2)
  rw [h2]
  simp_rw [hprob, hgv]
  rw [sum_sq_dir_mul hp hsum t]
  ring

/-! ### The limit vector -/

/-- The limit of `pearsonSum`: the projection `z - ⟪u, z⟫ u` of `z` along the unit vector `u = (√pᵢ)ᵢ`. -/
noncomputable def pearsonLimit (p : ι → ℝ) (z : ι → ℝ) : EuclideanSpace ℝ (ι) :=
  WithLp.toLp 2 fun i ↦ z i - (∑ j, √(p j) * z j) * √(p i)

omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma inner_pearsonLimit (p : ι → ℝ) (z : ι → ℝ) (t : EuclideanSpace ℝ (ι)) :
    ⟪pearsonLimit p z, t⟫ = ∑ i, (t i - (∑ j, √(p j) * t j) * √(p i)) * z i := by
  have h1 : ∑ i, (z i - (∑ j, √(p j) * z j) * √(p i)) * t i =
      ∑ i, z i * t i - (∑ j, √(p j) * z j) * ∑ i, √(p i) * t i := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  have h2 : ∑ i, (t i - (∑ j, √(p j) * t j) * √(p i)) * z i =
      ∑ i, z i * t i - (∑ j, √(p j) * t j) * ∑ i, √(p i) * z i := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  calc ⟪pearsonLimit p z, t⟫ = ∑ i, (z i - (∑ j, √(p j) * z j) * √(p i)) * t i := by
        simp only [pearsonLimit, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
        exact sum_congr rfl fun i _ ↦ by simp [mul_comm]
    _ = _ := by rw [h1, h2]; ring

/-- In an orthonormal basis whose vector `i₀` is `u = (√pᵢ)ᵢ`, the squared length of the limit vector is the sum
of the squares of the other `k - 1` coordinates of `z`. -/
lemma norm_sq_pearsonLimit {p : Fin k → ℝ} (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) {i₀ : Fin k}
    {b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))}
    (hb : b i₀ = WithLp.toLp 2 fun i ↦ √(p i)) (z : Fin k → ℝ) :
    ‖pearsonLimit p z‖ ^ 2 = ∑ j ∈ univ.erase i₀, rotate b z j ^ 2 := by
  have hrot : rotate b z i₀ = ∑ i, √(p i) * z i := by
    simp [rotate, hb]
  rw [sum_erase_eq_sub (mem_univ i₀), sum_sq_rotate, hrot, EuclideanSpace.real_norm_sq_eq]
  simp only [pearsonLimit]
  exact sum_sq_proj hp hsum z

omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The limit vector has, in each direction `t`, the centred normal law of variance `‖t‖² - ⟪u, t⟫²`. -/
lemma hasLaw_inner_pearsonLimit {p : ι → ℝ} (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (t : EuclideanSpace ℝ (ι)) :
    HasLaw (fun z ↦ ⟪pearsonLimit p z, t⟫)
      (gaussianReal 0 (∑ i, t i ^ 2 - (∑ i, √(p i) * t i) ^ 2).toNNReal)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  have hZm : ∀ i, Measurable fun z : ι → ℝ ↦ z i := fun i ↦ measurable_pi_apply i
  have hZind : iIndepFun (fun i (z : ι → ℝ) ↦ z i) (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
    iIndepFun_pi (X := fun _ x ↦ x) fun _ ↦ aemeasurable_id
  have hZlaw : ∀ i, HasLaw (fun z : ι → ℝ ↦ z i) (gaussianReal 0 1)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
    fun i ↦ ⟨(hZm i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have h := hasLaw_sum_mul_stdNormal_fintype hZm hZind hZlaw fun i ↦ t i - (∑ j, √(p j) * t j) * √(p i)
  rw [sum_sq_proj hp hsum] at h
  simp_rw [inner_pearsonLimit]
  exact h

lemma measurable_pearsonSum {p : ι → ℝ} {C : ℕ → Ω → ι} (hmeas : ∀ m, Measurable (C m)) (n : ℕ) :
    Measurable (pearsonSum p C n) := by
  unfold pearsonSum
  have hm : ∀ m, Measurable fun ω ↦ pearsonVector p (C m ω) :=
    fun m ↦ (measurable_of_finite (pearsonVector p)).comp (hmeas m)
  exact (Finset.measurable_sum (range n) fun m _ ↦ hm m).const_smul ((√(n : ℝ))⁻¹ : ℝ)

/-- **Multivariate central limit theorem for category counts.** For independent identically distributed
observations `Cₘ` with `P(C = i) = pᵢ > 0`, the vector `((Oᵢ - n pᵢ)/√(n pᵢ))ᵢ` converges in distribution to the
projection `z - ⟪u, z⟫ u` of a standard Gaussian vector `z` along `u = (√pᵢ)ᵢ` (Cramér-Wold theorem plus the
one-dimensional central limit theorem). -/
theorem tendstoInDistribution_pearsonSum [IsProbabilityMeasure P] {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) {C : ℕ → Ω → ι} (hmeas : ∀ m, Measurable (C m)) (hind : iIndepFun C P)
    (hident : ∀ m, IdentDistrib (C m) (C 0) P P) (hprob : ∀ i, P.real {ω | C 0 ω = i} = p i) :
    TendstoInDistribution (pearsonSum p C) atTop (pearsonLimit p) (fun _ ↦ P)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
  have hG : Measurable (pearsonLimit p) := by
    unfold pearsonLimit
    fun_prop
  rw [tendstoInDistribution_iff_tendstoInDistribution_inner hG.aemeasurable
    fun n ↦ (measurable_pearsonSum hmeas n).aemeasurable]
  intro t
  set X : ℕ → Ω → ℝ := fun m ω ↦ ⟪pearsonVector p (C m ω), t⟫ with hX
  obtain ⟨hmean, hL, hvar⟩ := pearson_moments hp hsum (hmeas 0) hprob t
  have hlaw : HasLaw (fun z ↦ ⟪pearsonLimit p z, t⟫) (gaussianReal 0 Var[X 0; P].toNNReal)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := by
    rw [hX, hvar]
    exact hasLaw_inner_pearsonLimit hp hsum t
  have hXind : iIndepFun X P :=
    hind.comp (fun _ c ↦ ⟪pearsonVector p c, t⟫) fun _ ↦ measurable_of_finite _
  have hXid : ∀ m, IdentDistrib (X m) (X 0) P P :=
    fun m ↦ (hident m).comp (measurable_of_finite fun c ↦ ⟪pearsonVector p c, t⟫)
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hlaw hL hXind hXid
  refine h.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  simp only [pearsonSum, real_inner_smul_left, sum_inner, hX]
  have h0 : ∫ x, ⟪pearsonVector p (C 0 x), t⟫ ∂P = 0 := hmean
  rw [h0, mul_zero, sub_zero]

/-- **Pearson's theorem (§11.2, ST-097).** Let `C₀, C₁, …` be independent observations, identically
distributed, each falling in category `i ∈ {0, …, k-1}` (`k ≥ 2`) with probability `pᵢ > 0`, `∑ pᵢ = 1`.
Let `Oᵢ` be the observed count of category `i` among the first `n` observations and `Eᵢ = n pᵢ` the expected
count. Then the goodness-of-fit statistic `χ² = ∑ᵢ (Oᵢ - Eᵢ)² / Eᵢ` converges in distribution, as `n → ∞`, to
the chi-square law with `k - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.2, p. 576"]
theorem tendstoInDistribution_pearsonStatistic [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {p : Fin k → ℝ} (hk : 2 ≤ k) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) {C : ℕ → Ω → Fin k} (hmeas : ∀ m, Measurable (C m)) (hind : iIndepFun C P)
    (hident : ∀ m, IdentDistrib (C m) (C 0) P P) (hprob : ∀ i, P.real {ω | C 0 ω = i} = p i)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared ((k : ℝ) - 1)) P') :
    TendstoInDistribution (pearsonStatistic p C) atTop W (fun _ ↦ P) P' := by
  set P₀ : Measure (Fin k → ℝ) := Measure.pi fun _ ↦ gaussianReal 0 1 with hP₀
  have hZm : ∀ i, Measurable fun z : Fin k → ℝ ↦ z i := fun i ↦ measurable_pi_apply i
  have hZind : iIndepFun (fun i (z : Fin k → ℝ) ↦ z i) P₀ :=
    iIndepFun_pi (X := fun _ x ↦ x) fun _ ↦ aemeasurable_id
  have hZlaw : ∀ i, HasLaw (fun z : Fin k → ℝ ↦ z i) (gaussianReal 0 1) P₀ :=
    fun i ↦ ⟨(hZm i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hvec := tendstoInDistribution_pearsonSum hp hsum hmeas hind hident hprob
  -- continuous mapping
  have hnorm := hvec.continuous_comp (g := fun x ↦ ‖x‖ ^ 2) (by fun_prop)
  -- the law of the limit
  have hk0 : 0 < k := by omega
  set i₀ : Fin k := ⟨0, hk0⟩
  set u : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 fun i ↦ √(p i) with hu_def
  have hu2 : ‖u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, hu_def, ← hsum]
    exact sum_congr rfl fun i _ ↦ sq_sqrt (hp i).le
  have hu : ‖u‖ = 1 := by
    rw [← sqrt_sq (norm_nonneg u), hu2, sqrt_one]
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_eq i₀ u hu
  obtain ⟨hWind, hWlaw⟩ := iIndepFun_rotate hZm hZind hZlaw b
  have hne : (univ.erase i₀).Nonempty := ⟨⟨1, by omega⟩, by simp [i₀, Fin.ext_iff]⟩
  have hchi := hasLaw_sum_sq_chiSquared hne (fun j ↦ by fun_prop) hWind fun j _ ↦ hWlaw j
  have hcard : ((univ.erase i₀).card : ℝ) = (k : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcard] at hchi
  have hlim : P₀.map (fun z ↦ ‖pearsonLimit p z‖ ^ 2) = chiSquared ((k : ℝ) - 1) := by
    rw [← hchi.map_eq]
    congr 1
    funext z
    exact norm_sq_pearsonLimit hp hsum hb z
  refine (TendstoInDistribution.of_map_eq_limit hnorm hW.aemeasurable ?_).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  · rw [hW.map_eq, ← hlim]
    rfl
  · exact (pearsonStatistic_eq_norm_sq hp C n ω).symm

end Pearson

end UndergradKB.Statistics
