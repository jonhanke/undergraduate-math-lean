import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.CramerWold
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Pearson
import UndergradKB.Statistics.TwoProportions

/-!
# Central limit theorem for the count table of a test of homogeneity (§11.4)

There are `r` populations and `c` categories. Population `i` is sampled `sz i` times per "round", so that after
`n` rounds the sample from population `i` has size `sz i * n`. The main result,
`tendstoInDistribution_homVector`, says that the centred and scaled table `(O_ij - sz_i n b_j)/√n` converges in
distribution to a Gaussian vector `homLimit`.

Proof: group the observations into rounds; the round vectors are independent and identically distributed
(blocks of an independent family), and Cramér-Wold plus the one-dimensional central limit theorem finish, exactly
as for `tendstoInDistribution_pearsonSum`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Finset Filter RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {r c : ℕ}

/-- Observed count of category `j` in the sample of size `sz i * n` from population `i`. -/
noncomputable def homCount (Y : Fin r → ℕ → Ω → Fin c) (sz : Fin r → ℕ) (n : ℕ) (i : Fin r) (j : Fin c)
    (ω : Ω) : ℝ :=
  ((Finset.range (sz i * n)).filter fun m ↦ Y i m ω = j).card

/-- The centred and scaled count table `(O_ij - sz_i n b_j)/√n`. -/
noncomputable def homVector (Y : Fin r → ℕ → Ω → Fin c) (sz : Fin r → ℕ) (b : Fin c → ℝ) (n : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (Fin r × Fin c) :=
  WithLp.toLp 2 fun x ↦ (homCount Y sz n x.1 x.2 ω - (sz x.1 : ℝ) * n * b x.2) / √(n : ℝ)

/-- The Gaussian limit: row `i` is `√sz_i` times the projection of `(√b_j z_ij)_j`. -/
noncomputable def homLimit (sz : Fin r → ℕ) (b : Fin c → ℝ) (z : Fin r × Fin c → ℝ) :
    EuclideanSpace ℝ (Fin r × Fin c) :=
  WithLp.toLp 2 fun x ↦ √(sz x.1 : ℝ) * (√(b x.2) * z x - b x.2 * ∑ l, √(b l) * z (x.1, l))

/-! ### Rounds -/

/-- The slots of one round: the `k`-th draw from population `i`, for `k < sz i`. -/
abbrev HomSlot (sz : Fin r → ℕ) : Type := (i : Fin r) × Fin (sz i)

/-- The draws made in round `m`, indexed by slots. -/
def blockVec (Y : Fin r → ℕ → Ω → Fin c) (sz : Fin r → ℕ) (m : ℕ) (ω : Ω) : HomSlot sz → Fin c :=
  fun j ↦ Y j.1 (sz j.1 * m + j.2) ω

/-- The centred indicator table of one round of draws. -/
noncomputable def roundVec (sz : Fin r → ℕ) (b : Fin c → ℝ) (y : HomSlot sz → Fin c) :
    EuclideanSpace ℝ (Fin r × Fin c) :=
  WithLp.toLp 2 fun x ↦ ∑ k : Fin (sz x.1), ((if y ⟨x.1, k⟩ = x.2 then (1 : ℝ) else 0) - b x.2)

lemma homSum_range_blocks (f : ℕ → ℝ) (a n : ℕ) :
    ∑ m ∈ range n, ∑ k ∈ range a, f (a * m + k) = ∑ i ∈ range (a * n), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]

omit [MeasurableSpace Ω] in
lemma homVector_eq (Y : Fin r → ℕ → Ω → Fin c) (sz : Fin r → ℕ) (b : Fin c → ℝ) (n : ℕ) (ω : Ω) :
    homVector Y sz b n ω =
      (√(n : ℝ))⁻¹ • ∑ m ∈ range n, roundVec sz b (blockVec Y sz m ω) := by
  ext ⟨i, j⟩
  simp only [homVector, roundVec, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
  have hfin : ∀ m, ∑ k : Fin (sz i), ((if blockVec Y sz m ω ⟨i, k⟩ = j then (1 : ℝ) else 0) - b j) =
      ∑ k ∈ range (sz i), ((if Y i (sz i * m + k) ω = j then (1 : ℝ) else 0) - b j) :=
    fun m ↦ Fin.sum_univ_eq_sum_range
      (fun k ↦ ((if Y i (sz i * m + k) ω = j then (1 : ℝ) else 0) - b j)) (sz i)
  have key : ∑ m ∈ range n, ∑ k ∈ range (sz i),
      ((if Y i (sz i * m + k) ω = j then (1 : ℝ) else 0) - b j) =
      homCount Y sz n i j ω - (sz i : ℝ) * n * b j := by
    refine (homSum_range_blocks (fun t ↦ ((if Y i t ω = j then (1 : ℝ) else 0) - b j)) (sz i) n).trans ?_
    rw [sum_sub_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul]
    simp only [homCount, Nat.cast_mul]
  rw [sum_congr rfl fun m _ ↦ hfin m, key, div_eq_inv_mul]

lemma measurable_blockVec {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m)) (sz : Fin r → ℕ)
    (m : ℕ) : Measurable (blockVec Y sz m) :=
  measurable_pi_iff.2 fun _ ↦ hmeas _ _

lemma measurable_homVector {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m)) (sz : Fin r → ℕ)
    (b : Fin c → ℝ) (n : ℕ) : Measurable (homVector Y sz b n) := by
  have : homVector Y sz b n = fun ω ↦
      (√(n : ℝ))⁻¹ • ∑ m ∈ range n, roundVec sz b (blockVec Y sz m ω) :=
    funext fun ω ↦ homVector_eq Y sz b n ω
  rw [this]
  exact (Finset.measurable_sum (range n) fun m _ ↦
    (measurable_of_finite (roundVec sz b)).comp (measurable_blockVec hmeas sz m)).const_smul
      ((√(n : ℝ))⁻¹ : ℝ)

/-- The inner product of a round table with a direction `t`. -/
lemma inner_roundVec (sz : Fin r → ℕ) (b : Fin c → ℝ) (y : HomSlot sz → Fin c)
    (t : EuclideanSpace ℝ (Fin r × Fin c)) :
    ⟪roundVec sz b y, t⟫ = ∑ j : HomSlot sz, (t (j.1, y j) - ∑ l, b l * t (j.1, l)) := by
  simp only [roundVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine sum_congr rfl fun i _ ↦ ?_
  simp_rw [mul_sum]
  refine (Finset.sum_comm (s := (univ : Finset (Fin c))) (t := (univ : Finset (Fin (sz i))))).trans ?_
  refine sum_congr rfl fun k _ ↦ ?_
  have h : ∀ l, t (i, l) * ((if y ⟨i, k⟩ = l then (1 : ℝ) else 0) - b l) =
      (if y ⟨i, k⟩ = l then t (i, l) else 0) - b l * t (i, l) := by
    intro l
    split_ifs <;> ring
  simp_rw [h]
  rw [sum_sub_distrib, sum_ite_eq]
  simp

/-! ### One draw: mean and variance -/

lemma fin_moments [IsProbabilityMeasure P] {C : Ω → Fin c} (hC : Measurable C) {b : Fin c → ℝ}
    (hprob : ∀ l, P.real {ω | C ω = l} = b l) (g : Fin c → ℝ) (hg : ∑ l, g l * b l = 0) :
    P[fun ω ↦ g (C ω)] = 0 ∧ MemLp (fun ω ↦ g (C ω)) 2 P ∧
      Var[fun ω ↦ g (C ω); P] = ∑ l, g l ^ 2 * b l := by
  have hmean : P[fun ω ↦ g (C ω)] = 0 := by
    rw [integral_comp_fin hC g]
    simp_rw [hprob]
    exact hg
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
  simp_rw [hprob]
  ring

/-! ### The limit -/

lemma inner_homLimit (sz : Fin r → ℕ) (b : Fin c → ℝ) (z : Fin r × Fin c → ℝ)
    (t : EuclideanSpace ℝ (Fin r × Fin c)) :
    ⟪homLimit sz b z, t⟫ =
      ∑ x : Fin r × Fin c, (√(sz x.1 : ℝ) * √(b x.2) * (t x - ∑ l, b l * t (x.1, l))) * z x := by
  simp only [homLimit, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ ↦ ?_
  dsimp only
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ l, √(b l) * z (i, l) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ l, b l * t (i, l) := ⟨_, rfl⟩
  rw [← hS, ← hM]
  have h1 : ∑ l, t (i, l) * (√(sz i : ℝ) * (√(b l) * z (i, l) - b l * S)) =
      ∑ l, (√(sz i : ℝ) * √(b l) * t (i, l) * z (i, l) - √(sz i : ℝ) * S * (b l * t (i, l))) :=
    sum_congr rfl fun l _ ↦ by ring
  have h2 : ∑ l, √(sz i : ℝ) * √(b l) * (t (i, l) - M) * z (i, l) =
      ∑ l, (√(sz i : ℝ) * √(b l) * t (i, l) * z (i, l) - √(sz i : ℝ) * M * (√(b l) * z (i, l))) :=
    sum_congr rfl fun l _ ↦ by ring
  rw [h1, h2, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← hS, ← hM]
  ring

/-- The distribution of the limit in a direction `t`, as a normal law. -/
lemma hasLaw_inner_homLimit {sz : Fin r → ℕ} {b : Fin c → ℝ} (hb : ∀ j, 0 < b j)
    (t : EuclideanSpace ℝ (Fin r × Fin c)) :
    HasLaw (fun z ↦ ⟪homLimit sz b z, t⟫)
      (gaussianReal 0 (∑ i, (sz i : ℝ) * ∑ l, (t (i, l) - ∑ l', b l' * t (i, l')) ^ 2 * b l).toNNReal)
      (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1) := by
  have hZm : ∀ i, Measurable fun z : Fin r × Fin c → ℝ ↦ z i := fun i ↦ measurable_pi_apply i
  have hZind : iIndepFun (fun i (z : Fin r × Fin c → ℝ) ↦ z i)
      (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1) :=
    iIndepFun_pi (X := fun _ x ↦ x) fun _ ↦ aemeasurable_id
  have hZlaw : ∀ i, HasLaw (fun z : Fin r × Fin c → ℝ ↦ z i) (gaussianReal 0 1)
      (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1) :=
    fun i ↦ ⟨(hZm i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have h := hasLaw_sum_mul_stdNormal_fintype hZm hZind hZlaw
    fun x : Fin r × Fin c ↦ √(sz x.1 : ℝ) * √(b x.2) * (t x - ∑ l, b l * t (x.1, l))
  have hsum : ∑ x : Fin r × Fin c, (√(sz x.1 : ℝ) * √(b x.2) * (t x - ∑ l, b l * t (x.1, l))) ^ 2 =
      ∑ i, (sz i : ℝ) * ∑ l, (t (i, l) - ∑ l', b l' * t (i, l')) ^ 2 * b l := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ ↦ ?_
    rw [mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg _), sq_sqrt (hb l).le]
    ring
  rw [hsum] at h
  have hf : (fun z : Fin r × Fin c → ℝ ↦ ⟪homLimit sz b z, t⟫) =
      fun z ↦ ∑ x : Fin r × Fin c, (√(sz x.1 : ℝ) * √(b x.2) * (t x - ∑ l, b l * t (x.1, l))) * z x :=
    funext fun z ↦ inner_homLimit sz b z t
  rw [hf]
  exact h

/-! ### The theorem -/

lemma homSlot_ext {sz : Fin r → ℕ} (m : ℕ) {j j' : HomSlot sz}
    (h : ((j.1, sz j.1 * m + j.2) : Fin r × ℕ) = (j'.1, sz j'.1 * m + j'.2)) : j = j' := by
  obtain ⟨i, k⟩ := j
  obtain ⟨i', k'⟩ := j'
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have : k = k' := Fin.ext (by omega)
  rw [this]

lemma homSlot_disj {sz : Fin r → ℕ} (hsz : ∀ i, 0 < sz i) (m m' : ℕ) {j j' : HomSlot sz}
    (h : ((j.1, sz j.1 * m + j.2) : Fin r × ℕ) = (j'.1, sz j'.1 * m' + j'.2)) : m = m' := by
  obtain ⟨i, k⟩ := j
  obtain ⟨i', k'⟩ := j'
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have := congrArg (· / sz i) h2
  simp only [Nat.mul_add_div (hsz i), Nat.div_eq_of_lt k.2, Nat.div_eq_of_lt k'.2] at this
  simpa using this

/-- **Central limit theorem for the table of counts in a test of homogeneity (§11.4).** In `r` independent
samples (population `i` contributes `sz i * n` draws, all independent, identically distributed within a
population with category probabilities `b_j > 0` summing to `1`), the table `(O_ij - sz_i n b_j)/√n` converges in
distribution to the Gaussian vector `homLimit`. -/
theorem tendstoInDistribution_homVector [IsProbabilityMeasure P] {sz : Fin r → ℕ} (hsz : ∀ i, 0 < sz i)
    {b : Fin c → ℝ} (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1) {Y : Fin r → ℕ → Ω → Fin c}
    (hmeas : ∀ i m, Measurable (Y i m)) (hind : iIndepFun (fun x : Fin r × ℕ ↦ Y x.1 x.2) P)
    (hident : ∀ i m, IdentDistrib (Y i m) (Y i 0) P P) (hprob : ∀ i j, P.real {ω | Y i 0 ω = j} = b j) :
    TendstoInDistribution (homVector Y sz b) Filter.atTop (homLimit sz b) (fun _ ↦ P)
      (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1) := by
  classical
  have hG : Measurable (homLimit sz b) := by
    unfold homLimit
    fun_prop
  rw [tendstoInDistribution_iff_tendstoInDistribution_inner hG.aemeasurable
    fun n ↦ (measurable_homVector hmeas sz b n).aemeasurable]
  intro t
  -- probabilities of every draw
  have hprob' : ∀ i m j, P.real {ω | Y i m ω = j} = b j := by
    intro i m j
    have h : P {ω | Y i m ω = j} = P {ω | Y i 0 ω = j} :=
      (hident i m).measure_mem_eq (measurableSet_singleton j)
    rw [measureReal_def, h, ← measureReal_def]
    exact hprob i j
  set mm : Fin r → ℝ := fun i ↦ ∑ l, b l * t (i, l) with hmm
  set X : ℕ → Ω → ℝ := fun m ω ↦ ⟪roundVec sz b (blockVec Y sz m ω), t⟫ with hX
  -- slots, blocks
  let e : ℕ → HomSlot sz → Fin r × ℕ := fun m j ↦ (j.1, sz j.1 * m + j.2)
  have hW : ∀ x : Fin r × ℕ, Measurable (fun ω ↦ Y x.1 x.2 ω) := fun x ↦ hmeas _ _
  have hblocks := iIndepFun_blocks (κ := HomSlot sz) (W := fun x : Fin r × ℕ ↦ Y x.1 x.2) hind hW e
    (fun m m' j j' h ↦ homSlot_disj hsz m m' h)
  have hlaw : ∀ m j, P.map ((fun x : Fin r × ℕ ↦ Y x.1 x.2) (e m j)) =
      P.map ((fun x : Fin r × ℕ ↦ Y x.1 x.2) (e 0 j)) :=
    fun m j ↦ (hident _ _).map_eq.trans (hident _ _).map_eq.symm
  have hid := blocks_identDistrib (κ := HomSlot sz) (W := fun x : Fin r × ℕ ↦ Y x.1 x.2) hind hW e
    (fun m j j' h ↦ homSlot_ext m h) hlaw
  have hφ : Measurable fun y : HomSlot sz → Fin c ↦ ⟪roundVec sz b y, t⟫ := measurable_of_finite _
  have hXind : iIndepFun X P := hblocks.comp (fun _ y ↦ ⟪roundVec sz b y, t⟫) fun _ ↦ hφ
  have hXid : ∀ m, IdentDistrib (X m) (X 0) P P := fun m ↦ (hid m).comp hφ
  -- one round in direction t
  set f : HomSlot sz → Ω → ℝ := fun j ω ↦ (t (j.1, Y j.1 (sz j.1 * 0 + j.2) ω) - mm j.1) with hf
  have hg0 : ∀ i, ∑ l, (t (i, l) - mm i) * b l = 0 := by
    intro i
    have : ∀ l, (t (i, l) - mm i) * b l = b l * t (i, l) - mm i * b l := fun l ↦ by ring
    simp_rw [this]
    rw [sum_sub_distrib, ← mul_sum, hbsum, mul_one, hmm]
    simp
  have hmom : ∀ j : HomSlot sz, P[f j] = 0 ∧ MemLp (f j) 2 P ∧
      Var[f j; P] = ∑ l, (t (j.1, l) - mm j.1) ^ 2 * b l := fun j ↦
    fin_moments (P := P) (C := fun ω ↦ Y j.1 (sz j.1 * 0 + j.2) ω) (hmeas _ _)
      (fun l ↦ hprob' _ _ l) (fun y ↦ t (j.1, y) - mm j.1) (hg0 j.1)
  have hfun : X 0 = ∑ j : HomSlot sz, f j := by
    funext ω
    rw [Finset.sum_apply]
    exact inner_roundVec sz b _ t
  have hmem : ∀ j ∈ (Finset.univ : Finset (HomSlot sz)), MemLp (f j) 2 P := fun j _ ↦ (hmom j).2.1
  have hXmean : P[X 0] = 0 := by
    have h1 : ∀ j ∈ (Finset.univ : Finset (HomSlot sz)), Integrable (f j) P :=
      fun j _ ↦ (hmem j ‹_›).integrable one_le_two
    have e1 : ∫ ω, X 0 ω ∂P = ∫ ω, ∑ j, f j ω ∂P :=
      integral_congr_ae (ae_of_all _ fun ω ↦ by rw [hfun, Finset.sum_apply])
    rw [e1, integral_finsetSum _ h1]
    exact sum_eq_zero fun j _ ↦ (hmom j).1
  have hXL : MemLp (X 0) 2 P := by
    rw [hfun]
    exact memLp_finsetSum' _ hmem
  have hXvar : Var[X 0; P] = ∑ i, (sz i : ℝ) * ∑ l, (t (i, l) - mm i) ^ 2 * b l := by
    have hpair : Set.Pairwise (↑(Finset.univ : Finset (HomSlot sz))) fun i j ↦ f i ⟂ᵢ[P] f j := by
      intro j _ j' _ hjj
      have hne' : ((j.1, sz j.1 * 0 + j.2) : Fin r × ℕ) ≠ (j'.1, sz j'.1 * 0 + j'.2) :=
        fun h ↦ hjj (homSlot_ext 0 h)
      have h := (hind.indepFun hne').comp (measurable_of_finite fun y : Fin c ↦ t (j.1, y) - mm j.1)
        (measurable_of_finite fun y : Fin c ↦ t (j'.1, y) - mm j'.1)
      exact h
    rw [hfun, IndepFun.variance_sum hmem hpair]
    simp_rw [fun j ↦ (hmom j).2.2]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine sum_congr rfl fun i _ ↦ ?_
    dsimp only
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlim : HasLaw (fun z ↦ ⟪homLimit sz b z, t⟫) (gaussianReal 0 Var[X 0; P].toNNReal)
      (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1) := by
    rw [hXvar]
    exact hasLaw_inner_homLimit hb t
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hlim hXL hXind hXid
  refine h.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  simp only [homVector_eq, real_inner_smul_left, sum_inner, hX]
  rw [hXmean, mul_zero, sub_zero]

end UndergradKB.Statistics
