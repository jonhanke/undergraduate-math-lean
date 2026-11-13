import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.Basic
import UndergradKB.Common.Attr

/-!
# Probability rules (OpenStax *Introductory Statistics 2e*, chapters 3 and 4)

Equally likely outcomes, tree-diagram rules, Venn-diagram identities, and the long-run average
interpretation of the expected value of a game.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

section EquallyLikely

variable {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω] [MeasurableSingletonClass Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Each outcome of an equally likely finite sample space has probability `1 / |Ω|`. -/
theorem equally_likely_singleton (h : ∀ x y : Ω, P {x} = P {y}) (x : Ω) :
    P {x} = 1 / (Fintype.card Ω : ℝ≥0∞) := by
  have hsum : (Fintype.card Ω : ℝ≥0∞) * P {x} = 1 := by
    have : P (Set.univ : Set Ω) = ∑ y : Ω, P {y} := by
      simp
    rw [measure_univ] at this
    rw [this, Finset.sum_congr rfl (fun y _ => h y x)]
    simp
  rw [one_div]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm] at hsum)

/-- ST-019 (OpenStax Introductory Statistics 2e, §3.1). If every outcome of a finite sample space
is equally likely (all singletons have the same probability), then the probability of any event
`A` is the number of outcomes in `A` divided by the number of outcomes in the sample space. -/
@[kb "openstaxintrostats2e" "§3.1, p. 179"]
theorem equally_likely_prob (h : ∀ x y : Ω, P {x} = P {y}) (A : Set Ω) :
    P A = (A.ncard : ℝ≥0∞) / (Fintype.card Ω : ℝ≥0∞) := by
  classical
  have hA : P A = ∑ x ∈ A.toFinset, P {x} := by
    simp
  obtain ⟨x0⟩ : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := P)
    simp [Set.univ_eq_empty_iff.mpr hne] at this
  rw [hA, Finset.sum_congr rfl (fun y _ => (equally_likely_singleton P h y)), Finset.sum_const,
    nsmul_eq_mul, Set.ncard_eq_toFinset_card']
  simp [div_eq_mul_inv]

/-- Real-valued form of ST-019 (OpenStax Introductory Statistics 2e, §3.1): `P(A) = |A| / |Ω|`. -/
@[kb "openstaxintrostats2e" "§3.1, p. 179"]
theorem equally_likely_prob_real (h : ∀ x y : Ω, P {x} = P {y}) (A : Set Ω) :
    P.real A = (A.ncard : ℝ) / (Fintype.card Ω : ℝ) := by
  rw [Measure.real, equally_likely_prob P h A, ENNReal.toReal_div]
  simp

end EquallyLikely

section Tree

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- ST-031(a) (OpenStax Introductory Statistics 2e, §3.5, tree diagrams). Law of total
probability: if finitely many events `A i` (`i ∈ s`) are pairwise disjoint, measurable, and cover
the sample space, then `P(B) = Σ P(A i) · P(B | A i)`; each branch of the tree contributes the
product of probabilities along its path. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem total_probability {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hdisj : Set.PairwiseDisjoint (↑s : Set ι) A)
    (hcover : ⋃ i ∈ s, A i = Set.univ) (B : Set Ω) (hB : MeasurableSet B) :
    P B = ∑ i ∈ s, P (A i) * P[B | A i] := by
  have h1 : B = ⋃ i ∈ s, (A i ∩ B) := by
    rw [← Set.iUnion₂_inter, hcover, Set.univ_inter]
  have hd : Set.PairwiseDisjoint (↑s : Set ι) (fun i => A i ∩ B) :=
    fun i hi j hj hij => (hdisj hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  calc P B = P (⋃ i ∈ s, (A i ∩ B)) := by rw [← h1]
    _ = ∑ i ∈ s, P (A i ∩ B) :=
        measure_biUnion_finset hd (fun i hi => (hmeas i hi).inter hB)
    _ = ∑ i ∈ s, P (A i) * P[B | A i] := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [mul_comm, cond_mul_eq_inter (hmeas i hi)]

/-- Fintype form of ST-031(a) (OpenStax Introductory Statistics 2e, §3.5): for a finite partition
`A : ι → Set Ω` indexed by a finite type, `P(B) = Σ_i P(A i) · P(B | A i)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem total_probability_fintype {ι : Type*} [Fintype ι] (A : ι → Set Ω)
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = Set.univ) (B : Set Ω) (hB : MeasurableSet B) :
    P B = ∑ i, P (A i) * P[B | A i] :=
  total_probability P Finset.univ A (fun i _ => hmeas i) (fun i _ j _ h => hdisj h)
    (by simpa using hcover) B hB

/-- ST-031(b), two-step path (OpenStax Introductory Statistics 2e, §3.5): multiplying along a
branch of a tree, `P(A and B) = P(A) · P(B | A)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem tree_path_two {A : Set Ω} (hA : MeasurableSet A) (B : Set Ω) :
    P (A ∩ B) = P A * P[B | A] := by
  rw [mul_comm, cond_mul_eq_inter hA]

/-- ST-031(b), three-step path (OpenStax Introductory Statistics 2e, §3.5):
`P(A and B and C) = P(A) · P(B | A) · P(C | A and B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem tree_path_three {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (C : Set Ω) :
    P (A ∩ B ∩ C) = P A * P[B | A] * P[C | A ∩ B] := by
  rw [tree_path_two P (hA.inter hB) C, tree_path_two P hA B]

end Tree

section Venn

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {A B : Set Ω}

/-- ST-033 (OpenStax Introductory Statistics 2e, §3.5, Venn diagrams): the part of `A` outside `B`
has probability `P(A) - P(A and B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem venn_inter_compl (hB : MeasurableSet B) :
    P.real (A ∩ Bᶜ) = P.real A - P.real (A ∩ B) := by
  have := measureReal_inter_add_sdiff (μ := P) (s := A) hB
  rw [Set.sdiff_eq] at this
  linarith

/-- ST-033 (OpenStax Introductory Statistics 2e, §3.5): De Morgan, `(A or B)' = A' and B'`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem venn_deMorgan_union : P ((A ∪ B)ᶜ) = P (Aᶜ ∩ Bᶜ) := by
  rw [Set.compl_union]

/-- ST-033 (OpenStax Introductory Statistics 2e, §3.5): De Morgan, `(A and B)' = A' or B'`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem venn_deMorgan_inter : P ((A ∩ B)ᶜ) = P (Aᶜ ∪ Bᶜ) := by
  rw [Set.compl_inter]

/-- ST-033 (OpenStax Introductory Statistics 2e, §3.5): the three regions of a two-circle Venn
diagram, `P(A or B) = P(A and B') + P(A and B) + P(A' and B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem venn_three_regions (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P (A ∪ B) = P (A ∩ Bᶜ) + P (A ∩ B) + P (Aᶜ ∩ B) := by
  have h1 : A ∪ B = (A ∩ Bᶜ) ∪ ((A ∩ B) ∪ (Aᶜ ∩ B)) := by
    ext x; by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]
  have d1 : Disjoint (A ∩ B) (Aᶜ ∩ B) :=
    Set.disjoint_left.mpr fun x hx hy => hy.1 hx.1
  have d2 : Disjoint (A ∩ Bᶜ) ((A ∩ B) ∪ (Aᶜ ∩ B)) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hxb⟩ (⟨_, hb⟩ | ⟨_, hb⟩) <;> exact hxb hb
  rw [h1, measure_union d2 ((hA.inter hB).union (hA.compl.inter hB)),
    measure_union d1 (hA.compl.inter hB), add_assoc]

/-- ST-033 (OpenStax Introductory Statistics 2e, §3.5): the probability of neither event is
`1 - P(A) - P(B) + P(A and B)`. -/
@[kb "openstaxintrostats2e" "§3.5, p. 200"]
theorem venn_neither (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P.real (Aᶜ ∩ Bᶜ) = 1 - P.real A - P.real B + P.real (A ∩ B) := by
  rw [← Set.compl_union, probReal_compl_eq_one_sub (hA.union hB)]
  have := measureReal_union_add_inter (μ := P) (s := A) hB
  linarith

end Venn

section LongRun

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expectation of a random variable with values in a finite set `S` is
`Σ_{x ∈ S} x · P(X = x)`. -/
theorem integral_eq_sum_of_finite_values (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Finset ℝ) (X : Ω → ℝ) (hX : Measurable X) (hS : ∀ ω, X ω ∈ S) :
    ∫ ω, X ω ∂P = ∑ x ∈ S, x * P.real (X ⁻¹' {x}) := by
  classical
  have h1 : (fun ω => X ω) = fun ω => ∑ x ∈ S, (X ⁻¹' {x}).indicator (fun _ => x) ω := by
    funext ω
    rw [Finset.sum_eq_single (X ω)]
    · simp
    · intro b _ hb
      simp [Set.indicator, hb.symm]
    · intro h; exact absurd (hS ω) h
  rw [h1, integral_finsetSum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_indicator_const _ (hX (measurableSet_singleton x))]
    simp [mul_comm]
  · intro x _
    exact (integrable_const x).indicator (hX (measurableSet_singleton x))

variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- ST-037 (OpenStax Introductory Statistics 2e, §4.2, expected value of a game): if the gains
`X 0, X 1, ...` of successive plays are independent, identically distributed and take values in a
finite set `S` of reals, then almost surely the average gain over the first `n` plays converges to
the expected value `Σ_{x ∈ S} x · P(X 0 = x)`. -/
@[kb "openstaxintrostats2e" "§4.2, p. 241"]
theorem long_run_average_gain (S : Finset ℝ) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hS : ∀ i ω, X i ω ∈ S)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, X k ω) atTop
      (𝓝 (∑ x ∈ S, x * P.real (X 0 ⁻¹' {x}))) := by
  have hint : Integrable (X 0) P := by
    refine Integrable.of_bound (hmeas 0).aestronglyMeasurable (∑ x ∈ S, |x|) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun x : ℝ => |x|) (fun x _ => abs_nonneg x) (hS 0 ω)
  have h := strong_law_ae (μ := P) X hint
    (fun i j hij => hindep.indepFun hij) hident
  rw [← integral_eq_sum_of_finite_values P S (X 0) (hmeas 0) (hS 0)]
  simpa [smul_eq_mul] using h

/-- ST-037 corollary (OpenStax Introductory Statistics 2e, §4.2): in a fair game, whose expected
value `Σ x · P(X 0 = x)` is zero, the average gain per play tends to zero almost surely. -/
@[kb "openstaxintrostats2e" "§4.2, p. 241"]
theorem fair_game_average_gain (S : Finset ℝ) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hS : ∀ i ω, X i ω ∈ S)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfair : ∑ x ∈ S, x * P.real (X 0 ⁻¹' {x}) = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, X k ω) atTop (𝓝 0) := by
  have := long_run_average_gain P S X hmeas hS hindep hident
  rwa [hfair] at this

end LongRun

end UndergradKB.Statistics
