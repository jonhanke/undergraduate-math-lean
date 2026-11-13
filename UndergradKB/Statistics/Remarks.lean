import Mathlib.Probability.UniformOn
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Inference

/-!
# Mathematical content behind several remarks of OpenStax *Introductory Statistics 2e*

Five places where the book makes a remark rather than stating a result, with the underlying fact proved:
grouped-data means (§2.5), sampling with and without replacement (§3.2), contingency tables (§3.4),
the long-run reading of a confidence level (§8.1), and the slope of a line (§12.1).
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

/-! ### ST-008: the mean of grouped data -/

section Grouped

variable {n : ℕ}

/-- ST-008 (OpenStax Introductory Statistics 2e, §2.5). If every datum `x i` lies within `h` of the
midpoint `m i` of its class, then the mean of the data differs from the mean of the midpoints by at
most `h`. -/
@[kb "openstaxintrostats2e" "§2.5, p. 109"]
theorem abs_mean_sub_mean_midpoints_le (x m : Fin n → ℝ) (h : ℝ) (hn : 1 ≤ n)
    (hxm : ∀ i, |x i - m i| ≤ h) : |mean x - mean m| ≤ h := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold mean
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hn', div_le_iff₀ hn']
  calc |∑ i, (x i - m i)| ≤ ∑ i, |x i - m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, h := Finset.sum_le_sum fun i _ => hxm i
    _ = h * n := by simp [mul_comm]

/-- ST-008 (OpenStax Introductory Statistics 2e, §2.5). Replacing each datum by the midpoint of its
class (`cls i` is the class of datum `i`, `mid c` the midpoint of class `c`), the mean of the
midpoints is the frequency-weighted midpoint `∑ fᶜ · midᶜ / ∑ fᶜ`, where `fᶜ` is the number of
data in class `c`. -/
@[kb "openstaxintrostats2e" "§2.5, p. 109"]
theorem mean_midpoints_eq_weighted {κ : Type*} [Fintype κ] [DecidableEq κ] (cls : Fin n → κ)
    (mid : κ → ℝ) :
    mean (fun i => mid (cls i)) =
      (∑ c, ((univ.filter fun i => cls i = c).card : ℝ) * mid c) /
        ∑ c, ((univ.filter fun i => cls i = c).card : ℝ) := by
  have hden : (∑ c, ((univ.filter fun i => cls i = c).card : ℝ)) = n := by
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := (univ : Finset κ))
      (f := cls) (fun _ _ => mem_univ _)
    rw [← Nat.cast_sum, ← this]
    simp
  have hnum : (∑ i, mid (cls i)) = ∑ c, ((univ.filter fun i => cls i = c).card : ℝ) * mid c := by
    rw [← Finset.sum_fiberwise (s := (univ : Finset (Fin n))) (g := cls)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2])]
    simp
  rw [hden, ← hnum]
  rfl

end Grouped

/-! ### Uniform measures on finsets, as real numbers -/

section Uniform

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [DecidableEq Ω]

lemma real_uniformOn_finset (D T : Finset Ω) :
    (uniformOn (D : Set Ω)).real (T : Set Ω) = ((D ∩ T).card : ℝ) / D.card := by
  rw [Measure.real, uniformOn_apply_finset]
  simp [ENNReal.toReal_div]

end Uniform

/-! ### ST-029: sampling with and without replacement -/

section Sampling

variable {N : ℕ}

private lemma real_uniform_pair (S T : Finset (Fin N)) :
    (uniformOn (Set.univ : Set (Fin N × Fin N))).real ((S ×ˢ T : Finset (Fin N × Fin N)) : Set _) =
      ((S.card : ℝ) / N) * ((T.card : ℝ) / N) := by
  have := real_uniformOn_finset (Finset.univ : Finset (Fin N × Fin N)) (S ×ˢ T)
  rw [Finset.coe_univ] at this
  rw [this]
  simp only [Finset.univ_inter, Finset.card_product, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  push_cast
  rw [div_mul_div_comm]

/-- ST-029 (OpenStax Introductory Statistics 2e, §3.2). Drawing twice with replacement from `N`
equally likely items: the pair of draws is uniform on `Fin N × Fin N`, and the first and second draws
are independent. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem withReplacement_indep [NeZero N] :
    IndepFun (Prod.fst : Fin N × Fin N → Fin N) Prod.snd
      (uniformOn (Set.univ : Set (Fin N × Fin N))) := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  obtain ⟨S, rfl⟩ : ∃ S : Finset (Fin N), (S : Set (Fin N)) = s := ⟨s.toFinite.toFinset, by simp⟩
  obtain ⟨T, rfl⟩ : ∃ T : Finset (Fin N), (T : Set (Fin N)) = t := ⟨t.toFinite.toFinset, by simp⟩
  have h1 : (Prod.fst ⁻¹' (S : Set (Fin N)) : Set (Fin N × Fin N)) = ((S ×ˢ Finset.univ : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  have h2 : (Prod.snd ⁻¹' (T : Set (Fin N)) : Set (Fin N × Fin N)) = ((Finset.univ ×ˢ T : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  have h3 : (Prod.fst ⁻¹' (S : Set (Fin N)) ∩ Prod.snd ⁻¹' (T : Set (Fin N)) : Set (Fin N × Fin N)) =
      ((S ×ˢ T : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hfin : ∀ u : Set (Fin N × Fin N), (uniformOn (Set.univ : Set (Fin N × Fin N))) u ≠ ∞ :=
    fun u => measure_ne_top _ u
  rw [← ofReal_measureReal (hfin _), ← ofReal_measureReal (hfin _), ← ofReal_measureReal (hfin _),
    ← ENNReal.ofReal_mul measureReal_nonneg, h3, h1, h2, real_uniform_pair, real_uniform_pair,
    real_uniform_pair]
  congr 1
  simp only [Finset.card_univ, Fintype.card_fin]
  field_simp

/-- ST-029 (OpenStax Introductory Statistics 2e, §3.2). With replacement, each draw lands in a set
`A` of items with probability `|A| / N` (first draw). -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem withReplacement_first_prob [NeZero N] (A : Finset (Fin N)) :
    (uniformOn (Set.univ : Set (Fin N × Fin N))).real {p | p.1 ∈ A} = (A.card : ℝ) / N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have : {p : Fin N × Fin N | p.1 ∈ A} = ((A ×ˢ Finset.univ : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  rw [this, real_uniform_pair]
  simp only [Finset.card_univ, Fintype.card_fin]
  field_simp

/-- ST-029 (OpenStax Introductory Statistics 2e, §3.2). With replacement, the second draw lands in a
set `A` with probability `|A| / N` as well. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem withReplacement_second_prob [NeZero N] (A : Finset (Fin N)) :
    (uniformOn (Set.univ : Set (Fin N × Fin N))).real {p | p.2 ∈ A} = (A.card : ℝ) / N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have : {p : Fin N × Fin N | p.2 ∈ A} = ((Finset.univ ×ˢ A : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  rw [this, real_uniform_pair]
  simp only [Finset.card_univ, Fintype.card_fin]
  field_simp

/-- The set of ordered pairs of distinct items, as a finset. -/
private abbrev offDiagPairs (N : ℕ) : Finset (Fin N × Fin N) := (Finset.univ : Finset (Fin N)).offDiag

private lemma card_offDiagPairs (N : ℕ) : ((offDiagPairs N).card : ℝ) = N * (N - 1) := by
  have h : (offDiagPairs N).card = N * N - N := by
    simp [offDiagPairs, Finset.offDiag_card]
  have hN : N ≤ N * N := Nat.le_mul_self N
  rw [h, Nat.cast_sub hN]
  push_cast
  ring

private lemma card_offDiag_inter_first (A : Finset (Fin N)) :
    ((offDiagPairs N ∩ (A ×ˢ Finset.univ)).card : ℝ) = A.card * (N - 1) := by
  have hsub : A.card ≤ N := by simpa using Finset.card_le_univ A
  have e : offDiagPairs N ∩ (A ×ˢ Finset.univ) = A.offDiag ∪ A ×ˢ Aᶜ := by
    ext ⟨a, b⟩
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [offDiagPairs, ha, hb, Finset.mem_offDiag] <;> rintro rfl <;> contradiction
  have hd : Disjoint A.offDiag (A ×ˢ Aᶜ) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp [Finset.mem_offDiag] at h1 h2
    exact h2.2 h1.2.1
  rw [e, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.offDiag_card,
    Finset.card_compl]
  simp only [Fintype.card_fin]
  have : A.card ≤ A.card * A.card := Nat.le_mul_self _
  push_cast [Nat.cast_sub this, Nat.cast_sub hsub]
  ring

private lemma card_offDiag_inter_second (A : Finset (Fin N)) :
    ((offDiagPairs N ∩ (Finset.univ ×ˢ A)).card : ℝ) = A.card * (N - 1) := by
  have hsub : A.card ≤ N := by simpa using Finset.card_le_univ A
  have e : offDiagPairs N ∩ (Finset.univ ×ˢ A) = A.offDiag ∪ Aᶜ ×ˢ A := by
    ext ⟨a, b⟩
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [offDiagPairs, ha, hb, Finset.mem_offDiag] <;> rintro rfl <;> contradiction
  have hd : Disjoint A.offDiag (Aᶜ ×ˢ A) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp [Finset.mem_offDiag] at h1 h2
    exact h2.1 h1.1
  rw [e, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.offDiag_card,
    Finset.card_compl]
  simp only [Fintype.card_fin]
  have : A.card ≤ A.card * A.card := Nat.le_mul_self _
  push_cast [Nat.cast_sub this, Nat.cast_sub hsub]
  ring

private lemma card_offDiag_inter_both (A : Finset (Fin N)) :
    ((offDiagPairs N ∩ (A ×ˢ A)).card : ℝ) = A.card * (A.card - 1) := by
  have e : offDiagPairs N ∩ (A ×ˢ A) = A.offDiag := by
    ext ⟨a, b⟩
    simp [offDiagPairs, Finset.mem_offDiag]
    tauto
  have : A.card ≤ A.card * A.card := Nat.le_mul_self _
  rw [e, Finset.offDiag_card, Nat.cast_sub this]
  push_cast
  ring

/-- ST-029 (OpenStax Introductory Statistics 2e, §3.2). Drawing two distinct items without
replacement from `N` items (ordered pairs of distinct items equally likely): the probability that
both draws land in `A` is `|A| (|A| - 1) / (N (N - 1))`. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem withoutReplacement_both_prob (A : Finset (Fin N)) :
    (uniformOn ((offDiagPairs N : Finset (Fin N × Fin N)) : Set (Fin N × Fin N))).real
        ({p | p.1 ∈ A} ∩ {p | p.2 ∈ A}) =
      (A.card : ℝ) * (A.card - 1) / (N * (N - 1)) := by
  have : ({p | p.1 ∈ A} ∩ {p | p.2 ∈ A} : Set (Fin N × Fin N)) = ((A ×ˢ A : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  rw [this, real_uniformOn_finset, card_offDiag_inter_both, card_offDiagPairs]

/-- ST-029 (OpenStax Introductory Statistics 2e, §3.2). Without replacement, each single draw still
lands in `A` with probability `|A| / N` (first draw). -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem withoutReplacement_first_prob (hN : 2 ≤ N) (A : Finset (Fin N)) :
    (uniformOn ((offDiagPairs N : Finset (Fin N × Fin N)) : Set (Fin N × Fin N))).real {p | p.1 ∈ A} =
      (A.card : ℝ) / N := by
  have : {p : Fin N × Fin N | p.1 ∈ A} = ((A ×ˢ Finset.univ : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  have hN' : (N : ℝ) ≥ 2 := by exact_mod_cast hN
  rw [this, real_uniformOn_finset, card_offDiag_inter_first, card_offDiagPairs]
  field_simp
  have : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- ST-029 (OpenStax Introductory Statistics 2e, §3.2). Without replacement, the second draw lands in
`A` with probability `|A| / N`. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem withoutReplacement_second_prob (hN : 2 ≤ N) (A : Finset (Fin N)) :
    (uniformOn ((offDiagPairs N : Finset (Fin N × Fin N)) : Set (Fin N × Fin N))).real {p | p.2 ∈ A} =
      (A.card : ℝ) / N := by
  have : {p : Fin N × Fin N | p.2 ∈ A} = ((Finset.univ ×ˢ A : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    ext p; simp
  have hN' : (N : ℝ) ≥ 2 := by exact_mod_cast hN
  rw [this, real_uniformOn_finset, card_offDiag_inter_second, card_offDiagPairs]
  have : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- ST-029 (OpenStax Introductory Statistics 2e, §3.2). Without replacement the two draws are NOT
independent: for a set `A` with `0 < |A| < N`, the probability that both draws are in `A` differs from
the product `(|A| / N)²` of the single-draw probabilities. -/
@[kb "openstaxintrostats2e" "§3.2, p. 183"]
theorem withoutReplacement_not_indep (hN : 2 ≤ N) (A : Finset (Fin N)) (h0 : 0 < A.card)
    (hlt : A.card < N) :
    (uniformOn ((offDiagPairs N : Finset (Fin N × Fin N)) : Set (Fin N × Fin N))).real
        ({p | p.1 ∈ A} ∩ {p | p.2 ∈ A}) ≠
      (uniformOn ((offDiagPairs N : Finset (Fin N × Fin N)) : Set (Fin N × Fin N))).real {p | p.1 ∈ A} *
        (uniformOn ((offDiagPairs N : Finset (Fin N × Fin N)) : Set (Fin N × Fin N))).real {p | p.2 ∈ A} := by
  rw [withoutReplacement_both_prob, withoutReplacement_first_prob hN,
    withoutReplacement_second_prob hN]
  have hN' : (N : ℝ) ≥ 2 := by exact_mod_cast hN
  have ha : (0 : ℝ) < A.card := by exact_mod_cast h0
  have hl : (A.card : ℝ) < N := by exact_mod_cast hlt
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (N : ℝ) ≠ 0 := by linarith
  intro h
  field_simp at h
  nlinarith

end Sampling

/-! ### ST-030: contingency tables -/

section Contingency

variable {Ω ρ γ : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [DecidableEq ρ] [DecidableEq γ]

private lemma real_uniform_univ_filter (p : Ω → Prop) [DecidablePred p] :
    (uniformOn (Set.univ : Set Ω)).real {ω | p ω} =
      ((univ.filter p).card : ℝ) / Fintype.card Ω := by
  classical
  have e : {ω | p ω} = ((univ.filter p : Finset Ω) : Set Ω) := by ext; simp
  have := real_uniformOn_finset (Finset.univ : Finset Ω) (univ.filter p)
  rw [Finset.coe_univ] at this
  rw [e, this]
  simp

/-- ST-030 (OpenStax Introductory Statistics 2e, §3.4). In a contingency table (individuals of a
population labelled by a row `r` and a column `c`), the probability that a uniformly chosen
individual lies in row `i` is the row total over the grand total. -/
@[kb "openstaxintrostats2e" "§3.4, p. 194"]
theorem contingency_row_prob (r : Ω → ρ) (i : ρ) :
    (uniformOn (Set.univ : Set Ω)).real {ω | r ω = i} =
      ((univ.filter fun ω => r ω = i).card : ℝ) / Fintype.card Ω :=
  real_uniform_univ_filter _

/-- ST-030 (OpenStax Introductory Statistics 2e, §3.4). The probability of being in row `i` and
column `j` is the cell count over the grand total. -/
@[kb "openstaxintrostats2e" "§3.4, p. 194"]
theorem contingency_cell_prob (r : Ω → ρ) (c : Ω → γ) (i : ρ) (j : γ) :
    (uniformOn (Set.univ : Set Ω)).real {ω | r ω = i ∧ c ω = j} =
      ((univ.filter fun ω => r ω = i ∧ c ω = j).card : ℝ) / Fintype.card Ω :=
  real_uniform_univ_filter _

/-- ST-030 (OpenStax Introductory Statistics 2e, §3.4). The conditional probability of column `j`
given row `i` is the cell count divided by the row total, provided the row total is positive. -/
@[kb "openstaxintrostats2e" "§3.4, p. 194"]
theorem contingency_cond_prob (r : Ω → ρ) (c : Ω → γ) (i : ρ) (j : γ)
    (hrow : 0 < (univ.filter fun ω => r ω = i).card) :
    (cond (uniformOn (Set.univ : Set Ω)) {ω | r ω = i} {ω | c ω = j}).toReal =
      ((univ.filter fun ω => r ω = i ∧ c ω = j).card : ℝ) /
        (univ.filter fun ω => r ω = i).card := by
  classical
  set P := uniformOn (Set.univ : Set Ω) with hP
  have hms : MeasurableSet {ω | r ω = i} := (Set.toFinite _).measurableSet
  rw [cond_apply hms, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have h1 := contingency_cell_prob r c i j
  have h2 := contingency_row_prob r i
  have e : {ω | r ω = i} ∩ {ω | c ω = j} = {ω | r ω = i ∧ c ω = j} := by ext; simp
  rw [e]
  change (P.real {ω | r ω = i})⁻¹ * P.real {ω | r ω = i ∧ c ω = j} = _
  rw [h1, h2]
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hr : (0 : ℝ) < (univ.filter fun ω => r ω = i).card := by exact_mod_cast hrow
  field_simp

end Contingency

/-! ### ST-074: the long-run meaning of a confidence level -/

section ConfidenceLevel

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma identDistrib_indicator {P : Measure Ω} [IsProbabilityMeasure P] {E F : Set Ω}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (h : P E = P F) :
    IdentDistrib (E.indicator (fun _ => (1 : ℝ))) (F.indicator (fun _ => (1 : ℝ))) P P := by
  classical
  refine ⟨(measurable_const.indicator hE).aemeasurable, (measurable_const.indicator hF).aemeasurable,
    ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_const.indicator hE) hs,
    Measure.map_apply (measurable_const.indicator hF) hs]
  have key : ∀ G : Set Ω, MeasurableSet G → P G = P E →
      (G.indicator (fun _ => (1 : ℝ))) ⁻¹' s =
        (if (1 : ℝ) ∈ s then G else ∅) ∪ (if (0 : ℝ) ∈ s then Gᶜ else ∅) := by
    intro G _ _
    ext ω
    by_cases hω : ω ∈ G <;> by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s <;>
      simp [hω, h1, h0, Set.indicator]
  have hcompl : P Eᶜ = P Fᶜ := by
    rw [prob_compl_eq_one_sub hE, prob_compl_eq_one_sub hF, h]
  have dE : (E.indicator (fun _ => (1 : ℝ))) ⁻¹' s =
      (if (1 : ℝ) ∈ s then E else ∅) ∪ (if (0 : ℝ) ∈ s then Eᶜ else ∅) := key E hE rfl
  have dF : (F.indicator (fun _ => (1 : ℝ))) ⁻¹' s =
      (if (1 : ℝ) ∈ s then F else ∅) ∪ (if (0 : ℝ) ∈ s then Fᶜ else ∅) := key F hF h.symm
  rw [dE, dF]
  by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h0 : (0 : ℝ) ∈ s <;> simp [h1, h0, h, hcompl]

variable {P : Measure Ω} [IsProbabilityMeasure P]

open scoped Classical in
/-- ST-074 (OpenStax Introductory Statistics 2e, §8.1). Long-run reading of a confidence level:
if experiments are repeated independently, the `k`-th producing an event `E k` ("the interval
covers the parameter") with probability `1 - α`, then almost surely the fraction of the first `n`
experiments for which the event occurs tends to `1 - α`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem coverage_fraction_tendsto (E : ℕ → Set Ω) (hmeas : ∀ k, MeasurableSet (E k))
    (hindep : iIndepSet E P) (α : ℝ) (hprob : ∀ k, P.real (E k) = 1 - α) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (((range n).filter (fun k => ω ∈ E k)).card : ℝ) / n) atTop (𝓝 (1 - α)) := by
  classical
  set X : ℕ → Ω → ℝ := fun k => (E k).indicator (fun _ => (1 : ℝ)) with hX
  have hXm : ∀ k, Measurable (X k) := fun k => measurable_const.indicator (hmeas k)
  have hind : iIndepFun X P := hindep.iIndepFun_indicator
  have hP : ∀ k, P (E k) = P (E 0) := fun k => by
    rw [← ofReal_measureReal (measure_ne_top P _), ← ofReal_measureReal (measure_ne_top P (E 0)),
      hprob k, hprob 0]
  have hident : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
    identDistrib_indicator (hmeas k) (hmeas 0) (hP k)
  have hint : Integrable (X 0) P :=
    (integrable_const (1 : ℝ)).indicator (hmeas 0)
  have h := strong_law_ae (μ := P) X hint (fun i j hij => hind.indepFun hij) hident
  have hexp : P[X 0] = 1 - α := by
    rw [hX]
    simp only
    rw [integral_indicator_const _ (hmeas 0)]
    simp [hprob 0]
  filter_upwards [h] with ω hω
  rw [hexp] at hω
  refine (hω.congr fun n => ?_)
  simp only [hX, smul_eq_mul, Set.indicator_apply]
  rw [Finset.sum_boole]
  simp [div_eq_inv_mul]

variable {n : ℕ} {μ σ : ℝ}

open scoped Classical in
/-- ST-074 (OpenStax Introductory Statistics 2e, §8.1). For the z interval of a normal sample: if the
samples `S k` (`k = 0, 1, …`) are normal with mean `μ` and standard deviation `σ`, the events "the
`k`-th interval covers `μ`" are independent (and measurable), and `z` gives confidence level
`1 - α`, then almost surely the fraction of the first `m` intervals covering `μ` tends to `1 - α`. -/
@[kb "openstaxintrostats2e" "§8.1, p. 418"]
theorem zInterval_coverage_fraction_tendsto (hn : 1 ≤ n) (hσ : 0 < σ) (S : ℕ → Fin n → Ω → ℝ)
    (hS : ∀ k, IsNormalSample (S k) μ σ P) {z α : ℝ} (hα : α ≤ 1)
    (hz : gaussianReal 0 1 (Set.Icc (-z) z) = ENNReal.ofReal (1 - α))
    (hmeas : ∀ k, MeasurableSet {ω | mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ))})
    (hindep : iIndepSet (fun k => {ω | mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ))}) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun m : ℕ => (((range m).filter (fun k => mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ)))).card : ℝ) / m) atTop (𝓝 (1 - α)) := by
  have hp : ∀ k, P.real {ω | mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ))} = 1 - α := fun k => by
    rw [Measure.real, zInterval_confidence_level hn hσ (hS k) hz,
      ENNReal.toReal_ofReal (by linarith)]
  convert coverage_fraction_tendsto
    (fun k => {ω | mean (fun i ↦ S k i ω) - z * (σ / √(n : ℝ)) ≤ μ ∧
        μ ≤ mean (fun i ↦ S k i ω) + z * (σ / √(n : ℝ))}) hmeas hindep α hp

end ConfidenceLevel

/-! ### ST-102: the slope of a line -/

/-- ST-102 (OpenStax Introductory Statistics 2e, §12.1). Along the line `y = a + b x`, moving from
`x₁` to `x₂` changes `y` by `b (x₂ - x₁)`; in particular a one-unit increase in `x` changes `y` by the
slope `b`. -/
@[kb "openstaxintrostats2e" "§12.1, p. 628"]
theorem line_change (a b x₁ x₂ : ℝ) : (a + b * x₂) - (a + b * x₁) = b * (x₂ - x₁) := by
  ring

/-- ST-102 (OpenStax Introductory Statistics 2e, §12.1). A one-unit increase in `x` changes the
value of the line `y = a + b x` by exactly the slope `b`. -/
@[kb "openstaxintrostats2e" "§12.1, p. 628"]
theorem line_unit_change (a b x : ℝ) : (a + b * (x + 1)) - (a + b * x) = b := by
  ring

/-- ST-102 (OpenStax Introductory Statistics 2e, §12.1). The intercept `a` of the line `y = a + b x`
is its value at `x = 0`. -/
@[kb "openstaxintrostats2e" "§12.1, p. 628"]
theorem line_intercept (a b : ℝ) : a + b * 0 = a := by
  ring

end UndergradKB.Statistics
