import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.QuadraticDiscriminant
import UndergradKB.Common.Attr

/-! # Probability: basic facts (Grinstead–Snell)

Partitions, inclusion-exclusion, total probability, Bayes' formula, conditional expectation and the
correlation coefficient, for an abstract probability measure. -/

open MeasureTheory ProbabilityTheory Finset

namespace UndergradKB.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Grinstead–Snell Theorem 1.3 (PR-005). If the events `A i`, `i ∈ s`, partition the sample space,
then `P E` is the sum of the `P (E ∩ A i)`. -/
@[kb "grinsteadsnell2006" "Theorem 1.3, p. 31"]
theorem measure_eq_sum_inter_partition (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hd : Set.PairwiseDisjoint (↑s) A)
    (hU : ⋃ i ∈ s, A i = Set.univ) {E : Set Ω} (hE : MeasurableSet E) :
    P E = ∑ i ∈ s, P (E ∩ A i) := by
  have : E = ⋃ i ∈ s, E ∩ A i := by
    rw [← Set.inter_iUnion₂, hU, Set.inter_univ]
  conv_lhs => rw [this]
  refine measure_biUnion_finset ?_ (fun i hi => hE.inter (hA i hi))
  intro i hi j hj hij
  exact (hd hi hj hij).mono Set.inter_subset_right Set.inter_subset_right

/-- Real-valued form of `measure_eq_sum_inter_partition`. -/
@[kb "grinsteadsnell2006" "Theorem 1.3, p. 31"]
theorem real_eq_sum_inter_partition [IsProbabilityMeasure P] (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hd : Set.PairwiseDisjoint (↑s) A)
    (hU : ⋃ i ∈ s, A i = Set.univ) {E : Set Ω} (hE : MeasurableSet E) :
    P.real E = ∑ i ∈ s, P.real (E ∩ A i) := by
  simp only [measureReal_def]
  rw [measure_eq_sum_inter_partition s A hA hd hU hE, ENNReal.toReal_sum]
  intro i _; exact measure_ne_top _ _

/-- Grinstead–Snell Corollary 1.1 (PR-005). `P A = P (A ∩ B) + P (A ∩ Bᶜ)`. -/
@[kb "grinsteadsnell2006" "Corollary 1.1, p. 32"]
theorem measure_eq_inter_add_inter_compl [IsProbabilityMeasure P] {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P.real A = P.real (A ∩ B) + P.real (A ∩ Bᶜ) := by
  have := measureReal_inter_add_sdiff (μ := P) (s := A) hB
  rw [Set.sdiff_eq] at this
  linarith

/-! ### Inclusion-exclusion -/

section IncExc

variable [DecidableEq ι]

lemma indicator_union_eq (s : Finset ι) (A : ι → Set Ω) (ω : Ω) :
    (⋃ i ∈ s, A i).indicator (1 : Ω → ℝ) ω =
      ∑ t ∈ s.powerset.filter (·.Nonempty),
        (-1) ^ (t.card + 1) * (⋂ i ∈ t, A i).indicator (1 : Ω → ℝ) ω := by
  classical
  have h1 : ∀ i, (1 : ℝ) - (A i).indicator 1 ω = if ω ∉ A i then 1 else 0 := by
    intro i; by_cases h : ω ∈ A i <;> simp [h]
  have hprod : ∏ i ∈ s, (1 - (A i).indicator (1 : Ω → ℝ) ω) =
      1 - (⋃ i ∈ s, A i).indicator (1 : Ω → ℝ) ω := by
    simp_rw [h1]
    rw [Finset.prod_boole]
    by_cases h : ∃ i ∈ s, ω ∈ A i
    · obtain ⟨i, hi, hω⟩ := h
      have : ω ∈ ⋃ i ∈ s, A i := Set.mem_biUnion hi hω
      rw [Set.indicator_of_mem this, if_neg]
      · simp
      · intro h; exact h i hi hω
    · push_neg at h
      have : ω ∉ ⋃ i ∈ s, A i := by simpa using h
      rw [Set.indicator_of_notMem this, if_pos h]
      simp
  have hexp : ∏ i ∈ s, (1 - (A i).indicator (1 : Ω → ℝ) ω) =
      ∑ t ∈ s.powerset, (-1) ^ t.card * (⋂ i ∈ t, A i).indicator (1 : Ω → ℝ) ω := by
    have := Finset.prod_add (fun i => -(A i).indicator (1 : Ω → ℝ) ω) (fun _ => (1 : ℝ)) s
    simp only [Finset.prod_const_one, mul_one] at this
    simp_rw [sub_eq_neg_add]
    rw [this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_neg]
    congr 1
    by_cases h : ∀ i ∈ t, ω ∈ A i
    · have : ω ∈ ⋂ i ∈ t, A i := by simpa using h
      rw [Set.indicator_of_mem this]
      exact Finset.prod_eq_one fun i hi => Set.indicator_of_mem (h i hi) _
    · push_neg at h
      obtain ⟨i, hi, hω⟩ := h
      have : ω ∉ ⋂ i ∈ t, A i := by simpa using ⟨i, hi, hω⟩
      rw [Set.indicator_of_notMem this]
      exact Finset.prod_eq_zero hi (Set.indicator_of_notMem hω _)
  have hsplit := Finset.sum_filter_add_sum_filter_not s.powerset (·.Nonempty)
    (fun t => (-1) ^ t.card * (⋂ i ∈ t, A i).indicator (1 : Ω → ℝ) ω)
  have hempty : ∑ t ∈ s.powerset.filter (fun t => ¬ t.Nonempty),
      (-1 : ℝ) ^ t.card * (⋂ i ∈ t, A i).indicator (1 : Ω → ℝ) ω = 1 := by
    have : s.powerset.filter (fun t => ¬ t.Nonempty) = {∅} := by
      ext t; simp only [mem_filter, mem_powerset, Finset.not_nonempty_iff_eq_empty,
        mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ empty_subset _, h⟩⟩
    rw [this]; simp
  have hneg : ∑ t ∈ s.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (t.card + 1) * (⋂ i ∈ t, A i).indicator (1 : Ω → ℝ) ω =
      -∑ t ∈ s.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ t.card * (⋂ i ∈ t, A i).indicator (1 : Ω → ℝ) ω := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hneg]
  linarith

/-- Grinstead–Snell Theorem 3.8 (PR-031). Inclusion-exclusion for a probability measure: the
probability of a finite union is the alternating sum of the probabilities of the intersections over
nonempty subfamilies. -/
@[kb "grinsteadsnell2006" "Theorem 3.8, p. 112"]
theorem real_biUnion_eq_sum_inter [IsProbabilityMeasure P] (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    P.real (⋃ i ∈ s, A i) = ∑ t ∈ s.powerset.filter (·.Nonempty),
      (-1) ^ (t.card + 1) * P.real (⋂ i ∈ t, A i) := by
  have hU : MeasurableSet (⋃ i ∈ s, A i) := Finset.measurableSet_biUnion s hA
  have hI : ∀ t ∈ s.powerset.filter (·.Nonempty), MeasurableSet (⋂ i ∈ t, A i) := by
    intro t ht
    have := (mem_powerset.1 (mem_filter.1 ht).1)
    exact Finset.measurableSet_biInter t fun i hi => hA i (this hi)
  rw [← integral_indicator_one hU]
  simp_rw [indicator_union_eq]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [integral_const_mul, integral_indicator_one (hI t ht)]
  · intro t ht
    exact ((integrable_const (1 : ℝ)).indicator (hI t ht)).const_mul _

end IncExc

/-! ### Total probability and Bayes' formula -/

/-- Grinstead–Snell §4.1 total probability (PR-038), in `ℝ≥0∞`. For a finite measurable partition
`E i` of the sample space, `P F = ∑ P(F | E i) P(E i)`. -/
@[kb "grinsteadsnell2006" "§4.1 total probability, p. 154"]
theorem measure_eq_sum_cond_mul [IsProbabilityMeasure P] (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) (hd : Set.PairwiseDisjoint (↑s) E)
    (hU : ⋃ i ∈ s, E i = Set.univ) {F : Set Ω} (hF : MeasurableSet F) :
    P F = ∑ i ∈ s, (P[F | E i]) * P (E i) := by
  rw [measure_eq_sum_inter_partition s E hE hd hU hF]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cond_mul_eq_inter (hE i hi), Set.inter_comm]

/-- Grinstead–Snell §4.1 total probability (PR-038). For a finite measurable partition `E i` with
`P (E i) > 0`, `P F = ∑ P(F | E i) P(E i)` (real-valued; the positivity is not needed). -/
@[kb "grinsteadsnell2006" "§4.1 total probability, p. 154"]
theorem real_eq_sum_cond_mul [IsProbabilityMeasure P] (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) (hd : Set.PairwiseDisjoint (↑s) E)
    (hU : ⋃ i ∈ s, E i = Set.univ) (_hpos : ∀ i ∈ s, 0 < P (E i)) {F : Set Ω}
    (hF : MeasurableSet F) :
    P.real F = ∑ i ∈ s, (P[|E i]).real F * P.real (E i) := by
  simp only [measureReal_def]
  rw [measure_eq_sum_cond_mul s E hE hd hU hF, ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro i _; exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- Grinstead–Snell §4.1 Bayes' formula (PR-039). For a finite measurable partition `H j` with
`P (H j) > 0` and an event `E` with `P E > 0`,
`P(H i | E) = P(E | H i) P(H i) / ∑ j, P(E | H j) P(H j)`. -/
@[kb "grinsteadsnell2006" "§4.1 Bayes' formula, p. 154"]
theorem real_cond_eq_bayes [IsProbabilityMeasure P] (s : Finset ι) (H : ι → Set Ω)
    (hH : ∀ i ∈ s, MeasurableSet (H i)) (hd : Set.PairwiseDisjoint (↑s) H)
    (hU : ⋃ i ∈ s, H i = Set.univ) (hpos : ∀ i ∈ s, 0 < P (H i)) {E : Set Ω}
    (hE : MeasurableSet E) (hPE : 0 < P E) {i : ι} (hi : i ∈ s) :
    (P[|E]).real (H i) =
      (P[|H i]).real E * P.real (H i) / ∑ j ∈ s, (P[|H j]).real E * P.real (H j) := by
  rw [← real_eq_sum_cond_mul s H hH hd hU hpos hE]
  have hne : P.real E ≠ 0 := by
    simp only [measureReal_def]
    exact (ENNReal.toReal_pos hPE.ne' (measure_ne_top _ _)).ne'
  rw [eq_div_iff hne]
  have := cond_eq_inv_mul_cond_mul (μ := P) hE (hH i hi)
  simp only [measureReal_def] at hne ⊢
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  field_simp

/-! ### Conditional expectation given an event -/

/-- Grinstead–Snell Definition 6.2 (PR-070). The conditional expectation `E(X | F)` of a random
variable `X` given an event `F`: the expectation of `X` under the conditioned measure `P[|F]`. -/
noncomputable def condExpEvent (P : Measure Ω) (X : Ω → ℝ) (F : Set Ω) : ℝ :=
  ∫ ω, X ω ∂(P[|F])

/-- Grinstead–Snell Theorem 6.5 (PR-070). For a finite measurable partition `F j` with positive
probabilities and an integrable `X`, `E(X) = ∑ E(X | F j) P(F j)`. -/
@[kb "grinsteadsnell2006" "Theorem 6.5, p. 247"]
theorem integral_eq_sum_condExpEvent [IsProbabilityMeasure P] (s : Finset ι) (F : ι → Set Ω)
    (hF : ∀ i ∈ s, MeasurableSet (F i)) (hd : Set.PairwiseDisjoint (↑s) F)
    (hU : ⋃ i ∈ s, F i = Set.univ) (hpos : ∀ i ∈ s, 0 < P (F i)) {X : Ω → ℝ}
    (hX : Integrable X P) :
    ∫ ω, X ω ∂P = ∑ i ∈ s, condExpEvent P X (F i) * P.real (F i) := by
  have hmeas : P = ∑ i ∈ s, P (F i) • (P[|F i]) := by
    ext A hA
    simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [measure_eq_sum_inter_partition s F hF hd hU hA]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_comm, cond_mul_eq_inter (hF i hi), Set.inter_comm]
  have hint : ∀ i ∈ s, Integrable X (P (F i) • (P[|F i])) := by
    intro i hi
    have h1 : Integrable X (P[|F i]) := by
      unfold ProbabilityTheory.cond
      exact hX.restrict.smul_measure (ENNReal.inv_ne_top.2 (hpos i hi).ne')
    exact h1.smul_measure (measure_ne_top _ _)
  conv_lhs => rw [hmeas]
  rw [integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, smul_eq_mul, mul_comm]
  rfl

/-! ### Correlation -/

section Correlation

variable {X Y : Ω → ℝ}

/-- Grinstead–Snell §6.3 correlation (PR-078). The correlation coefficient
`ρ(X, Y) = cov(X, Y) / (σ_X σ_Y)`. -/
noncomputable def correlation (X Y : Ω → ℝ) (P : Measure Ω) : ℝ :=
  cov[X, Y; P] / (Real.sqrt Var[X; P] * Real.sqrt Var[Y; P])

/-- Grinstead–Snell §6.3 covariance (PR-078). Independent random variables with finite second
moments are uncorrelated: `ρ(X, Y) = 0`. -/
@[kb "grinsteadsnell2006" "§6.3 correlation, p. 289"]
theorem IndepFun.correlation_eq_zero (h : IndepFun X Y P) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    correlation X Y P = 0 := by
  rw [correlation, h.covariance_eq_zero hX hY, zero_div]

/-- Cauchy–Schwarz for covariance: `cov(X, Y)^2 ≤ Var X * Var Y`. -/
theorem covariance_sq_le [IsProbabilityMeasure P] (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] ^ 2 ≤ Var[X; P] * Var[Y; P] := by
  have key : ∀ t : ℝ, 0 ≤ Var[Y; P] * (t * t) + 2 * cov[X, Y; P] * t + Var[X; P] := by
    intro t
    have h := variance_nonneg (fun ω => t * Y ω + X ω) P
    have e : Var[fun ω => t * Y ω + X ω; P] =
        Var[Y; P] * (t * t) + 2 * cov[X, Y; P] * t + Var[X; P] := by
      rw [variance_fun_add (hY.const_mul t) hX, variance_const_mul,
        covariance_const_mul_left, covariance_comm]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- Grinstead–Snell §6.3 correlation (PR-078). The correlation coefficient satisfies
`|ρ(X, Y)| ≤ 1`. -/
@[kb "grinsteadsnell2006" "§6.3 correlation, p. 289"]
theorem abs_correlation_le_one [IsProbabilityMeasure P] (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    |correlation X Y P| ≤ 1 := by
  unfold correlation
  set D := Real.sqrt Var[X; P] * Real.sqrt Var[Y; P] with hD
  have hDnn : 0 ≤ D := by positivity
  rcases hDnn.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    have hsq : D ^ 2 = Var[X; P] * Var[Y; P] := by
      rw [hD, mul_pow, Real.sq_sqrt (variance_nonneg _ _), Real.sq_sqrt (variance_nonneg _ _)]
    exact abs_le_of_sq_le_sq' (by rw [hsq]; exact covariance_sq_le hX hY) hDnn |> fun h =>
      abs_le.2 h

end Correlation

end UndergradKB.Probability
