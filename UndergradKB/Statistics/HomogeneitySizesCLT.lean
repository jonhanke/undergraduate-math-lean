import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold
import UndergradKB.Common.Attr
import UndergradKB.Statistics.HomogeneityCLT

/-!
# Count table of a test of homogeneity, sample sizes growing in any manner (§11.4)

`HomogeneityCLT.lean` treats samples whose sizes `sᵢ n` stay in a fixed ratio. Here the sample from
population `i` has an arbitrary size `Nᵢ(n)`, with `Nᵢ(n) → ∞` for each `i` and no relation between the
populations. Each row of the table is centred and scaled by the square root of its own size:
`Vᵢⱼ = (Oᵢⱼ - Nᵢ bⱼ)/√Nᵢ`. The main result, `tendstoInDistribution_homVectorN`, says that this table converges
in distribution to the Gaussian table `homLimit 1 b` (independent rows, each the projection of `(√bⱼ zᵢⱼ)ⱼ`).

Proof: by Cramér-Wold it suffices to treat `⟪V, t⟫ = ∑ᵢ (√Nᵢ)⁻¹ ∑_{m < Nᵢ} gᵢ(Yᵢₘ)`. All the summands are
independent, so its characteristic function is `∏ᵢ φᵢ(s/√Nᵢ)^{Nᵢ}`, and each factor converges by the
one-dimensional central limit theorem composed with `Nᵢ(n) → ∞`. This is the product lemma for convergence in
distribution of independent components, done through characteristic functions.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Finset Filter RealInnerProductSpace Complex Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {r c : ℕ}

/-- Observed count of category `j` in the sample of size `N i n` from population `i`. -/
noncomputable def homCountN (Y : Fin r → ℕ → Ω → Fin c) (N : Fin r → ℕ → ℕ) (n : ℕ) (i : Fin r) (j : Fin c)
    (ω : Ω) : ℝ :=
  ((Finset.range (N i n)).filter fun m ↦ Y i m ω = j).card

/-- The table `(O_ij - Nᵢ b_j)/√Nᵢ`, each row scaled by its own sample size. -/
noncomputable def homVectorN (Y : Fin r → ℕ → Ω → Fin c) (N : Fin r → ℕ → ℕ) (b : Fin c → ℝ) (n : ℕ)
    (ω : Ω) : EuclideanSpace ℝ (Fin r × Fin c) :=
  WithLp.toLp 2 fun x ↦ (homCountN Y N n x.1 x.2 ω - (N x.1 n : ℝ) * b x.2) / √(N x.1 n : ℝ)

omit [MeasurableSpace Ω] in
lemma homCountN_eq (Y : Fin r → ℕ → Ω → Fin c) (N : Fin r → ℕ → ℕ) (n : ℕ) (i : Fin r) (j : Fin c) (ω : Ω) :
    homCountN Y N n i j ω = ∑ m ∈ range (N i n), if Y i m ω = j then (1 : ℝ) else 0 := by
  rw [sum_boole]
  rfl

lemma measurable_homCountN {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (N : Fin r → ℕ → ℕ) (n : ℕ) (i : Fin r) (j : Fin c) : Measurable fun ω ↦ homCountN Y N n i j ω := by
  simp_rw [homCountN_eq]
  exact Finset.measurable_sum _ fun m _ ↦
    Measurable.ite (hmeas i m (measurableSet_singleton j)) measurable_const measurable_const

lemma measurable_homVectorN {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (N : Fin r → ℕ → ℕ) (b : Fin c → ℝ) (n : ℕ) : Measurable (homVectorN Y N b n) := by
  unfold homVectorN
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun x ↦
    ((measurable_homCountN hmeas N n x.1 x.2).sub_const _).div_const _)

omit [MeasurableSpace Ω] in
/-- The inner product of the table with a direction `t`, as a sum over the draws. -/
lemma inner_homVectorN (Y : Fin r → ℕ → Ω → Fin c) (N : Fin r → ℕ → ℕ) (b : Fin c → ℝ) (n : ℕ)
    (ω : Ω) (t : EuclideanSpace ℝ (Fin r × Fin c)) :
    ⟪homVectorN Y N b n ω, t⟫ = ∑ i, ∑ m ∈ range (N i n),
      (√(N i n : ℝ))⁻¹ * (t (i, Y i m ω) - ∑ l, b l * t (i, l)) := by
  simp only [homVectorN, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← mul_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have h1 : ∑ m ∈ range (N i n), t (i, Y i m ω) =
      ∑ j, t (i, j) * homCountN Y N n i j ω := by
    simp_rw [homCountN_eq, mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun m _ ↦ ?_
    simp
  have h2 : ∑ j, t (i, j) * ((N i n : ℝ) * b j) = (N i n : ℝ) * ∑ l, b l * t (i, l) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [h1]
  simp_rw [div_eq_inv_mul]
  have h3 : ∀ j, t (i, j) * ((√(N i n : ℝ))⁻¹ * (homCountN Y N n i j ω - (N i n : ℝ) * b j)) =
      (√(N i n : ℝ))⁻¹ * (t (i, j) * homCountN Y N n i j ω - t (i, j) * ((N i n : ℝ) * b j)) :=
    fun j ↦ by ring
  simp_rw [h3]
  rw [← mul_sum, sum_sub_distrib, h2]

/-- One factor of the characteristic function: the central limit theorem for the row `i`, along `Nᵢ(n) → ∞`. -/
lemma tendsto_charFun_row [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hX : MemLp (X 0) 2 P)
    (h0 : P[X 0] = 0) (hind : iIndepFun X P) (hident : ∀ m, IdentDistrib (X m) (X 0) P P)
    {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) (s : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (X 0)) ((√(M n : ℝ))⁻¹ * s) ^ M n) atTop
      (𝓝 (charFun (gaussianReal 0 Var[X 0; P].toNNReal) s)) := by
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 Var[X 0; P].toNNReal) (gaussianReal 0 Var[X 0; P].toNNReal) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have h := (tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hind hident).tendsto_charFun s
  rw [Measure.map_id] at h
  have h' := h.comp hM
  refine h'.congr fun n ↦ ?_
  simp only [Function.comp_apply, h0, mul_zero, sub_zero]
  exact charFun_inv_sqrt_mul_sum hind hident

/-- **Central limit theorem for the table of a test of homogeneity, sizes growing in any manner.** In `r`
independent samples (population `i` contributes `N i n` draws, all draws independent, identically distributed
within a population with category probabilities `b_j > 0` summing to `1`), if every `N i n → ∞` then the table
`(O_ij - Nᵢ b_j)/√Nᵢ` converges in distribution to the Gaussian table `homLimit 1 b`. -/
theorem tendstoInDistribution_homVectorN [IsProbabilityMeasure P] {N : Fin r → ℕ → ℕ}
    (hN : ∀ i, Tendsto (N i) atTop atTop)
    {b : Fin c → ℝ} (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1) {Y : Fin r → ℕ → Ω → Fin c}
    (hmeas : ∀ i m, Measurable (Y i m)) (hind : iIndepFun (fun x : Fin r × ℕ ↦ Y x.1 x.2) P)
    (hident : ∀ i m, IdentDistrib (Y i m) (Y i 0) P P) (hprob : ∀ i j, P.real {ω | Y i 0 ω = j} = b j) :
    TendstoInDistribution (homVectorN Y N b) Filter.atTop (homLimit (fun _ ↦ 1) b) (fun _ ↦ P)
      (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1) := by
  classical
  have hG : Measurable (homLimit (fun _ : Fin r ↦ 1) b) := by
    unfold homLimit
    fun_prop
  rw [tendstoInDistribution_iff_tendstoInDistribution_inner hG.aemeasurable
    fun n ↦ (measurable_homVectorN hmeas N b n).aemeasurable]
  intro t
  set mm : Fin r → ℝ := fun i ↦ ∑ l, b l * t (i, l) with hmm
  set g : Fin r → Fin c → ℝ := fun i y ↦ t (i, y) - mm i with hg
  have hgm : ∀ i, Measurable (g i) := fun i ↦ measurable_of_finite _
  have hg0 : ∀ i, ∑ l, g i l * b l = 0 := by
    intro i
    have : ∀ l, g i l * b l = b l * t (i, l) - mm i * b l := fun l ↦ by simp only [hg]; ring
    simp_rw [this]
    rw [sum_sub_distrib, ← mul_sum, hbsum, mul_one, hmm]
    simp
  -- the rows, one variable per draw
  set X : Fin r → ℕ → Ω → ℝ := fun i m ω ↦ g i (Y i m ω) with hX
  have hXm : ∀ i m, Measurable (X i m) := fun i m ↦ (hgm i).comp (hmeas i m)
  have hXind2 : iIndepFun (fun x : Fin r × ℕ ↦ X x.1 x.2) P :=
    hind.comp (fun x y ↦ g x.1 y) fun x ↦ hgm x.1
  have hXind : ∀ i, iIndepFun (X i) P := fun i ↦
    hXind2.precomp (g := fun m : ℕ ↦ (i, m)) fun m m' h ↦ by simpa using h
  have hXid : ∀ i m, IdentDistrib (X i m) (X i 0) P P := fun i m ↦ (hident i m).comp (hgm i)
  have hmom : ∀ i, P[X i 0] = 0 ∧ MemLp (X i 0) 2 P ∧ Var[X i 0; P] = ∑ l, g i l ^ 2 * b l := fun i ↦
    fin_moments (P := P) (C := Y i 0) (hmeas i 0) (hprob i) (g i) (hg0 i)
  -- the inner product as a sum of independent terms
  set S : ℕ → Finset (Fin r × ℕ) := fun n ↦
    ((univ : Finset (Fin r)).sigma fun i ↦ range (N i n)).map (Equiv.sigmaEquivProd _ _).toEmbedding
    with hS
  set W : ℕ → Fin r × ℕ → Ω → ℝ := fun n x ω ↦ (√(N x.1 n : ℝ))⁻¹ * X x.1 x.2 ω with hW
  have hsumS : ∀ n (f : Fin r × ℕ → ℝ), ∑ x ∈ S n, f x = ∑ i, ∑ m ∈ range (N i n), f (i, m) := by
    intro n f
    rw [hS, sum_map, sum_sigma]
    rfl
  have hprodS : ∀ n (f : Fin r × ℕ → ℂ), ∏ x ∈ S n, f x = ∏ i, ∏ m ∈ range (N i n), f (i, m) := by
    intro n f
    rw [hS, prod_map, prod_sigma]
    rfl
  have hinner : ∀ n, (fun ω ↦ ⟪homVectorN Y N b n ω, t⟫) = fun ω ↦ ∑ x ∈ S n, W n x ω := by
    intro n
    funext ω
    rw [inner_homVectorN Y N b n ω t, hsumS]
  have hWind : ∀ n, iIndepFun (W n) P := fun n ↦
    hXind2.comp (fun x y ↦ (√(N x.1 n : ℝ))⁻¹ * y) fun _ ↦ measurable_const_mul _
  have hWm : ∀ n x, AEMeasurable (W n x) P := fun n x ↦ ((hXm x.1 x.2).const_mul _).aemeasurable
  have hchar : ∀ n s, charFun (P.map fun ω ↦ ⟪homVectorN Y N b n ω, t⟫) s =
      ∏ i, charFun (P.map (X i 0)) ((√(N i n : ℝ))⁻¹ * s) ^ N i n := by
    intro n s
    rw [hinner n, iIndepFun.charFun_map_fun_finsetSum_eq_prod (fun x _ ↦ hWm n x)
      ((hWind n).restrict _), Finset.prod_apply, hprodS]
    refine prod_congr rfl fun i _ ↦ ?_
    have h1 : ∀ m ∈ range (N i n), charFun (P.map (W n (i, m))) s =
        charFun (P.map (X i 0)) ((√(N i n : ℝ))⁻¹ * s) := by
      intro m _
      simp only [hW]
      rw [charFun_map_mul_comp (hXm i m).aemeasurable, (hXid i m).map_eq]
    rw [prod_congr rfl h1, prod_const, card_range]
  -- the limit
  have hlimlaw := hasLaw_inner_homLimit (sz := fun _ : Fin r ↦ 1) hb t
  have hv : ∀ i, (0 : ℝ) ≤ ∑ l, g i l ^ 2 * b l := fun i ↦
    sum_nonneg fun l _ ↦ mul_nonneg (sq_nonneg _) (hb l).le
  have hlimchar : ∀ s, charFun ((Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1).map
      fun z ↦ ⟪homLimit (fun _ : Fin r ↦ 1) b z, t⟫) s =
      ∏ i, charFun (gaussianReal 0 Var[X i 0; P].toNNReal) s := by
    intro s
    rw [hlimlaw.map_eq, charFun_gaussianReal]
    simp_rw [charFun_gaussianReal, (fun i ↦ (hmom i).2.2)]
    rw [← Complex.exp_sum]
    congr 1
    have e1 : ((((∑ i, ((1 : ℕ) : ℝ) * ∑ l, (t (i, l) - ∑ l', b l' * t (i, l')) ^ 2 * b l).toNNReal :
        NNReal) : ℝ)) = ∑ i, ∑ l, g i l ^ 2 * b l := by
      rw [Real.coe_toNNReal _ (sum_nonneg fun i _ ↦ by simpa using hv i)]
      simp [hg, hmm]
    have e2 : ∀ i, (((∑ l, g i l ^ 2 * b l).toNNReal : NNReal) : ℝ) = ∑ l, g i l ^ 2 * b l :=
      fun i ↦ Real.coe_toNNReal _ (hv i)
    simp only [ofReal_zero, mul_zero, zero_mul, zero_sub]
    rw [show ((((∑ i, ((1 : ℕ) : ℝ) * ∑ l, (t (i, l) - ∑ l', b l' * t (i, l')) ^ 2 * b l).toNNReal :
        NNReal) : ℝ) : ℂ) = ((∑ i, ∑ l, g i l ^ 2 * b l : ℝ) : ℂ) by rw [e1]]
    simp_rw [e2]
    push_cast
    rw [sum_mul, sum_div, ← sum_neg_distrib]
  refine TendstoInDistribution.of_tendsto_charFun
    (fun n ↦ ((continuous_id.inner continuous_const).measurable.comp
      (measurable_homVectorN hmeas N b n)).aemeasurable)
    ((continuous_id.inner continuous_const).measurable.comp hG).aemeasurable fun s ↦ ?_
  simp_rw [hchar, hlimchar]
  exact tendsto_finsetProd _ fun i _ ↦
    tendsto_charFun_row (hmom i).2.1 (hmom i).1 (hXind i) (hXid i) (hN i) s

end UndergradKB.Statistics
