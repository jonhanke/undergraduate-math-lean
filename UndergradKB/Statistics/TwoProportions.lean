import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Limits

/-!
# Two independent proportions

OpenStax *Introductory Statistics 2e*, §10.3 (ST-093).

For independent Bernoulli samples `X₀, X₁, …` (success probability `p_A`) and `Y₀, Y₁, …`
(success probability `p_B`) with sample sizes `n_A = a n`, `n_B = b n`, the standardised difference
of sample proportions tends to `N(0, 1)` in distribution.

The proof is a block trick: the variables
`D_m = (X_{am} + ⋯ + X_{am+a-1})/a - (Y_{bm} + ⋯ + Y_{bm+b-1})/b`
are independent (functions of disjoint blocks of an independent family) and identically distributed,
with mean `p_A - p_B` and variance `p_A q_A / a + p_B q_B / b`, and `∑_{m<n} D_m = n (p'_A - p'_B)`.
The standardised Central Limit Theorem (`tendstoInDistribution_standardized`) finishes the proof.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Filter Topology

section Blocks

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Functions of pairwise disjoint blocks of an independent family are independent: if
`W` is an independent family and the index blocks `e m : κ → ι` (`m : ℕ`) are pairwise disjoint,
then the block vectors `ω ↦ (W (e m j) ω)ⱼ` are independent. -/
lemma iIndepFun_blocks [Fintype κ] {β : Type*} [MeasurableSpace β] {W : ι → Ω → β} (hW : iIndepFun W P)
    (hmeas : ∀ i, Measurable (W i)) (e : ℕ → κ → ι)
    (hdisj : ∀ m m' j j', e m j = e m' j' → m = m') :
    iIndepFun (fun m ω j ↦ W (e m j) ω) P := by
  classical
  have := hW.isProbabilityMeasure
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  induction T using Finset.induction_on with
  | empty => simp
  | insert n T hn ih =>
    have ih' := ih (fun m hm => hsets m (Finset.mem_insert_of_mem hm))
    have hmemU : ∀ m ∈ T, ∀ j, e m j ∈ T.biUnion (fun m => Finset.univ.image (e m)) :=
      fun m hm j => Finset.mem_biUnion.2 ⟨m, hm, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩
    have hmemV : ∀ j, e n j ∈ Finset.univ.image (e n) :=
      fun j => Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    have hUV : Disjoint (T.biUnion (fun m => Finset.univ.image (e m)))
        (Finset.univ.image (e n)) := by
      rw [Finset.disjoint_left]
      intro i hi hiV
      obtain ⟨m, hm, hi'⟩ := Finset.mem_biUnion.1 hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi'
      obtain ⟨j', -, hj'⟩ := Finset.mem_image.1 hiV
      have := hdisj n m j' j hj'
      subst this
      exact hn hm
    have hind := hW.indepFun_finset _ _ hUV hmeas
    let BU : Set ((T.biUnion (fun m => Finset.univ.image (e m))) → β) :=
      ⋂ m : T, (fun x j ↦ x ⟨e m j, hmemU m m.2 j⟩) ⁻¹' sets m
    let BV : Set ((Finset.univ.image (e n)) → β) :=
      (fun x j ↦ x ⟨e n j, hmemV j⟩) ⁻¹' sets n
    have hBU : MeasurableSet BU :=
      MeasurableSet.iInter fun m ↦
        (measurable_pi_iff.2 fun j ↦ measurable_pi_apply _)
          (hsets m (Finset.mem_insert_of_mem m.2))
    have hBV : MeasurableSet BV :=
      (measurable_pi_iff.2 fun j ↦ measurable_pi_apply _)
        (hsets n (Finset.mem_insert_self n T))
    have hA : (⋂ m ∈ T, (fun ω j ↦ W (e m j) ω) ⁻¹' sets m) =
        (fun ω (i : T.biUnion (fun m => Finset.univ.image (e m))) ↦ W i ω) ⁻¹' BU := by
      ext ω
      simp [BU]
    have hB : (fun ω j ↦ W (e n j) ω) ⁻¹' sets n =
        (fun ω (i : Finset.univ.image (e n)) ↦ W i ω) ⁻¹' BV := rfl
    have key := (indepFun_iff_measure_inter_preimage_eq_mul.1 hind) BU BV hBU hBV
    rw [Finset.set_biInter_insert, Finset.prod_insert hn, ← ih', hA, hB, inter_comm, mul_comm]
    exact key

/-- Blocks of an independent family with the same marginals in each block position are identically
distributed. -/
lemma blocks_identDistrib [Fintype κ] {β : Type*} [MeasurableSpace β] {W : ι → Ω → β} (hW : iIndepFun W P)
    (hmeas : ∀ i, Measurable (W i)) (e : ℕ → κ → ι) (hinj : ∀ m, Function.Injective (e m))
    (hlaw : ∀ m j, P.map (W (e m j)) = P.map (W (e 0 j))) (m : ℕ) :
    IdentDistrib (fun ω j ↦ W (e m j) ω) (fun ω j ↦ W (e 0 j) ω) P P := by
  have := hW.isProbabilityMeasure
  refine ⟨(measurable_pi_iff.2 fun j ↦ hmeas _).aemeasurable,
    (measurable_pi_iff.2 fun j ↦ hmeas _).aemeasurable, ?_⟩
  have hm : iIndepFun (fun j ↦ W (e m j)) P := hW.precomp (hinj m)
  have h0 : iIndepFun (fun j ↦ W (e 0 j)) P := hW.precomp (hinj 0)
  rw [hm.map_fun_eq_pi_map fun j ↦ (hmeas _).aemeasurable,
    h0.map_fun_eq_pi_map fun j ↦ (hmeas _).aemeasurable]
  congr 1
  funext j
  exact hlaw m j

end Blocks

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Moments of a 0/1 variable with success probability `p`. -/
lemma bern_moments [IsProbabilityMeasure P] {f : Ω → ℝ} {p : ℝ} (hmeas : Measurable f)
    (h01 : ∀ ω, f ω = 0 ∨ f ω = 1) (hp : P.real {ω | f ω = 1} = p) :
    P[f] = p ∧ Var[f; P] = p * (1 - p) ∧ MemLp f 2 P := by
  have hA : MeasurableSet {ω | f ω = 1} := hmeas (measurableSet_singleton 1)
  have hind : f = Set.indicator {ω | f ω = 1} 1 := by
    funext ω
    rcases h01 ω with h | h <;> simp [Set.indicator, h]
  have hmean : P[f] = p := by
    rw [hind, integral_indicator_one hA, hp]
  have hL : MemLp f 2 P :=
    MemLp.of_bound hmeas.aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by rcases h01 ω with h | h <;> simp [h])
  refine ⟨hmean, ?_, hL⟩
  rw [variance_eq_sub hL]
  have : P[f ^ 2] = p := by
    rw [← hmean]
    congr 1
    funext ω
    rcases h01 ω with h | h <;> simp [h]
  rw [this, hmean]
  ring

private lemma moments_of_identDistrib {f g : Ω → ℝ} {p v : ℝ} (h : IdentDistrib f g P P)
    (hg : P[g] = p ∧ Var[g; P] = v ∧ MemLp g 2 P) : P[f] = p ∧ Var[f; P] = v ∧ MemLp f 2 P :=
  ⟨h.integral_eq.trans hg.1, h.variance_eq.trans hg.2.1, h.symm.memLp_snd hg.2.2⟩

end Moments

section TwoProportions

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'} {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}

/-- Index of the `j`-th member of the `m`-th block: `X_{am+k}` or `Y_{bm+k}`. -/
private def blockIdx (a b m : ℕ) : Fin a ⊕ Fin b → ℕ ⊕ ℕ
  | .inl k => .inl (a * m + k)
  | .inr k => .inr (b * m + k)

/-- Weight of the `j`-th member in the block difference: `1/a` for `X`, `-1/b` for `Y`. -/
private noncomputable def blockWeight (a b : ℕ) : Fin a ⊕ Fin b → ℝ
  | .inl _ => 1 / a
  | .inr _ => -(1 / b)

/-- The block difference `D_m = (X_{am} + ⋯ + X_{am+a-1})/a - (Y_{bm} + ⋯ + Y_{bm+b-1})/b`. -/
private noncomputable def blockDiff (a b : ℕ) (X Y : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ j : Fin a ⊕ Fin b, blockWeight a b j * Sum.elim X Y (blockIdx a b m j) ω

private lemma blockIdx_disj {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∀ m m' j j', blockIdx a b m j = blockIdx a b m' j' → m = m' := by
  intro m m' j j' h
  rcases j with k | k <;> rcases j' with k' | k' <;> simp only [blockIdx] at h
  · have h2 : a * m + k = a * m' + k' := Sum.inl_injective h
    have := congrArg (· / a) h2
    simp only [Nat.mul_add_div ha, Nat.div_eq_of_lt k.2, Nat.div_eq_of_lt k'.2] at this
    simpa using this
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · have h2 : b * m + k = b * m' + k' := Sum.inr_injective h
    have := congrArg (· / b) h2
    simp only [Nat.mul_add_div hb, Nat.div_eq_of_lt k.2, Nat.div_eq_of_lt k'.2] at this
    simpa using this

private lemma blockIdx_inj (a b m : ℕ) : Function.Injective (blockIdx a b m) := by
  intro j j' h
  rcases j with k | k <;> rcases j' with k' | k' <;> simp only [blockIdx] at h
  · have h2 : a * m + k = a * m + k' := Sum.inl_injective h
    exact congrArg Sum.inl (Fin.ext (by omega))
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · have h2 : b * m + k = b * m + k' := Sum.inr_injective h
    exact congrArg Sum.inr (Fin.ext (by omega))

private lemma sum_range_blocks (f : ℕ → ℝ) (a n : ℕ) :
    ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range a, f (a * m + k) = ∑ i ∈ Finset.range (a * n), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]

private lemma blockDiff_eq (a b : ℕ) (X Y : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    blockDiff a b X Y m ω =
      (∑ k ∈ Finset.range a, X (a * m + k) ω) / a - (∑ k ∈ Finset.range b, Y (b * m + k) ω) / b := by
  simp only [blockDiff, Fintype.sum_sum_type, blockWeight, blockIdx, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun k ↦ X (a * m + k) ω) a,
    Fin.sum_univ_eq_sum_range (fun k ↦ Y (b * m + k) ω) b]
  ring

/-- **Two independent proportions (ST-093).** Let `X₀, X₁, …` (population A, `P(Xᵢ = 1) = p_A`) and
`Y₀, Y₁, …` (population B, `P(Yⱼ = 1) = p_B`) be 0/1 variables with `0 < p_A, p_B < 1`, all independent
(`Sum.elim X Y` is an independent family over `ℕ ⊕ ℕ`), identically distributed within each
population. Take sample sizes `n_A = a n`, `n_B = b n` (`a, b > 0`). Then the standardised difference of the
sample proportions `p'_A = (X₀ + ⋯ + X_{an-1})/(a n)`, `p'_B = (Y₀ + ⋯ + Y_{bn-1})/(b n)`,
`((p'_A - p'_B) - (p_A - p_B)) / √(p_A q_A / n_A + p_B q_B / n_B)`, converges in distribution to
`N(0, 1)` as `n → ∞`. In other words `p'_A - p'_B` is approximately normal with mean `p_A - p_B` and
standard deviation `√(p_A q_A/n_A + p_B q_B/n_B)`. -/
@[kb "openstaxintrostats2e" "§10.3, p. 534"]
theorem tendstoInDistribution_two_proportions [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {pA pB : ℝ} (hA0 : 0 < pA) (hA1 : pA < 1)
    (hB0 : 0 < pB) (hB1 : pB < 1) (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hmX : ∀ i, Measurable (X i)) (hmY : ∀ i, Measurable (Y i))
    (h01X : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (h01Y : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hprobA : P.real {ω | X 0 ω = 1} = pA) (hprobB : P.real {ω | Y 0 ω = 1} = pB)
    (hindep : iIndepFun (Sum.elim X Y) P)
    (hidentX : ∀ i, IdentDistrib (X i) (X 0) P P) (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦
        ((∑ i ∈ Finset.range (a * n), X i ω) / ((a * n : ℕ) : ℝ) -
            (∑ j ∈ Finset.range (b * n), Y j ω) / ((b * n : ℕ) : ℝ) - (pA - pB)) /
          √(pA * (1 - pA) / ((a * n : ℕ) : ℝ) + pB * (1 - pB) / ((b * n : ℕ) : ℝ)))
      atTop Z (fun _ ↦ P) P' := by
  classical
  have hmW : ∀ i, Measurable (Sum.elim X Y i) := fun i ↦ by
    rcases i with i | i
    · exact hmX i
    · exact hmY i
  -- moments of single trials
  obtain ⟨hmA, hvA, hLA⟩ := bern_moments (P := P) (hmX 0) (h01X 0) hprobA
  obtain ⟨hmB, hvB, hLB⟩ := bern_moments (P := P) (hmY 0) (h01Y 0) hprobB
  have hXi := fun i ↦ moments_of_identDistrib (hidentX i) ⟨hmA, hvA, hLA⟩
  have hYi := fun i ↦ moments_of_identDistrib (hidentY i) ⟨hmB, hvB, hLB⟩
  -- block structure
  set D : ℕ → Ω → ℝ := fun m ↦ blockDiff a b X Y m with hD
  have hF : Measurable (fun x : Fin a ⊕ Fin b → ℝ ↦ ∑ j, blockWeight a b j * x j) := by
    fun_prop
  have hZind := iIndepFun_blocks (κ := Fin a ⊕ Fin b) hindep hmW (blockIdx a b)
    (blockIdx_disj ha hb)
  have hDind : iIndepFun D P :=
    hZind.comp (fun _ x ↦ ∑ j, blockWeight a b j * x j) (fun _ ↦ hF)
  have hlaw : ∀ m j, P.map (Sum.elim X Y (blockIdx a b m j)) =
      P.map (Sum.elim X Y (blockIdx a b 0 j)) := by
    intro m j
    rcases j with k | k
    · exact (hidentX _).map_eq.trans (hidentX _).map_eq.symm
    · exact (hidentY _).map_eq.trans (hidentY _).map_eq.symm
  have hDident : ∀ m, IdentDistrib (D m) (D 0) P P := fun m ↦
    (blocks_identDistrib hindep hmW (blockIdx a b) (blockIdx_inj a b) hlaw m).comp hF
  -- moments of the block difference
  have hWmom : ∀ j : Fin a ⊕ Fin b,
      P[Sum.elim X Y (blockIdx a b 0 j)] = Sum.elim (fun _ ↦ pA) (fun _ ↦ pB) j ∧
      Var[Sum.elim X Y (blockIdx a b 0 j); P] =
        Sum.elim (fun _ ↦ pA * (1 - pA)) (fun _ ↦ pB * (1 - pB)) j ∧
      MemLp (Sum.elim X Y (blockIdx a b 0 j)) 2 P := by
    intro j
    rcases j with k | k
    · exact hXi _
    · exact hYi _
  have hfun : D 0 = ∑ j : Fin a ⊕ Fin b,
      (fun ω ↦ blockWeight a b j * Sum.elim X Y (blockIdx a b 0 j) ω) := by
    funext ω
    simp [hD, blockDiff, Finset.sum_apply]
  have hmem : ∀ j ∈ (Finset.univ : Finset (Fin a ⊕ Fin b)),
      MemLp (fun ω ↦ blockWeight a b j * Sum.elim X Y (blockIdx a b 0 j) ω) 2 P :=
    fun j _ ↦ (hWmom j).2.2.const_mul _
  have hDmean : P[D 0] = pA - pB := by
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin a ⊕ Fin b)), Integrable
        (fun ω ↦ blockWeight a b j * Sum.elim X Y (blockIdx a b 0 j) ω) P :=
      fun j _ ↦ ((hWmom j).2.2.integrable one_le_two).const_mul _
    have := integral_finsetSum Finset.univ h1
    simp only [hD, blockDiff]
    rw [this]
    simp only [integral_const_mul, Fintype.sum_sum_type, blockWeight]
    have hint : ∀ j, ∫ ω, Sum.elim X Y (blockIdx a b 0 j) ω ∂P =
        Sum.elim (fun _ ↦ pA) (fun _ ↦ pB) j := fun j ↦ (hWmom j).1
    simp only [hint, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
    ring
  have hDvar : Var[D 0; P] = pA * (1 - pA) / a + pB * (1 - pB) / b := by
    have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin a ⊕ Fin b)))
        fun i j ↦ (fun ω ↦ blockWeight a b i * Sum.elim X Y (blockIdx a b 0 i) ω) ⟂ᵢ[P]
          (fun ω ↦ blockWeight a b j * Sum.elim X Y (blockIdx a b 0 j) ω) := by
      intro i _ j _ hij
      exact (hindep.indepFun (fun h ↦ hij (blockIdx_inj a b 0 h))).comp
        (measurable_const_mul _) (measurable_const_mul _)
    rw [hfun, IndepFun.variance_sum hmem hpair]
    simp only [variance_const_mul, Fintype.sum_sum_type, blockWeight]
    have hvar : ∀ j, Var[Sum.elim X Y (blockIdx a b 0 j); P] =
        Sum.elim (fun _ ↦ pA * (1 - pA)) (fun _ ↦ pB * (1 - pB)) j := fun j ↦ (hWmom j).2.1
    simp only [hvar, Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    field_simp
  have hDL : MemLp (D 0) 2 P := by
    rw [hfun]
    exact memLp_finsetSum' _ hmem
  have hV : 0 < pA * (1 - pA) / a + pB * (1 - pB) / b := by
    have h1 : 0 < pA * (1 - pA) := mul_pos hA0 (by linarith)
    have h2 : 0 < pB * (1 - pB) := mul_pos hB0 (by linarith)
    have : (0 : ℝ) < a := by exact_mod_cast ha
    have : (0 : ℝ) < b := by exact_mod_cast hb
    positivity
  have h := tendstoInDistribution_standardized (X := D) hZ hDL (by rw [hDvar]; exact hV.ne')
    hDind hDident
  convert h using 1
  funext n ω
  rw [hDvar, hDmean]
  have hsum : ∑ k ∈ Finset.range n, D k ω = (∑ i ∈ Finset.range (a * n), X i ω) / a -
      (∑ j ∈ Finset.range (b * n), Y j ω) / b := by
    simp only [hD, blockDiff_eq]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      sum_range_blocks (fun i ↦ X i ω) a n, sum_range_blocks (fun i ↦ Y i ω) b n]
  rw [hsum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    generalize (∑ i ∈ Finset.range (a * n), X i ω) = SA
    generalize (∑ j ∈ Finset.range (b * n), Y j ω) = SB
    have hd : pA * (1 - pA) / ((a * n : ℕ) : ℝ) + pB * (1 - pB) / ((b * n : ℕ) : ℝ) =
        (pA * (1 - pA) / a + pB * (1 - pB) / b) / n := by
      push_cast
      field_simp
    rw [hd, sqrt_mul hn'.le, sqrt_div hV.le]
    push_cast
    have hs : √(n : ℝ) ^ 2 = n := sq_sqrt hn'.le
    have hs0 : 0 < √(n : ℝ) := sqrt_pos.2 hn'
    have ht0 : 0 < √(pA * (1 - pA) / a + pB * (1 - pB) / b) := sqrt_pos.2 hV
    generalize √(n : ℝ) = s at *
    generalize √(pA * (1 - pA) / a + pB * (1 - pB) / b) = t at *
    rw [← hs]
    field_simp

end TwoProportions

end UndergradKB.Statistics
