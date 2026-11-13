import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr

/-! # Probability: worked examples on expectation (Grinstead–Snell, Chapter 6)

Examples 6.2, 6.3 (tosses until the first head, St. Petersburg), 6.9, 6.10 (expectation of a
product), 6.12 (craps), 6.13 (roulette), 6.17, 6.18 (one die, averages of dice). -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Probability

/-! ## Examples 6.2 and 6.3: first head, St. Petersburg (PR-137) -/

/-- The success probability `1/2` of a fair coin, as an element of `[0,1]`. -/
noncomputable def halfProb : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

lemma halfProb_coe : ((halfProb : unitInterval) : ℝ) = 1 / 2 := rfl

lemma halfProb_ne : halfProb ≠ 0 := by
  intro h
  have := congrArg (fun x : unitInterval => (x : ℝ)) h
  simp [halfProb_coe] at this

/-- The law of the number of tosses of a fair coin up to and including the first head: the
geometric law of the number of failures, shifted by one. -/
noncomputable def firstHeadLaw : Measure ℕ := (geometricMeasure halfProb).map Nat.succ

instance : IsProbabilityMeasure firstHeadLaw := by
  unfold firstHeadLaw
  infer_instance

lemma firstHeadLaw_singleton (i : ℕ) (hi : 1 ≤ i) :
    firstHeadLaw.real {i} = (1 / 2 : ℝ) ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [firstHeadLaw, measureReal_def, Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
  have : Nat.succ ⁻¹' {k + 1} = {k} := by ext; simp
  rw [this, ← measureReal_def, geometricMeasure_real_singleton halfProb_ne]
  simp only [halfProb_coe]
  ring

lemma firstHeadLaw_integral : ∫ x, (x : ℝ) ∂firstHeadLaw = 2 := by
  rw [firstHeadLaw, integral_map (by fun_prop) (by fun_prop),
    integral_geometricMeasure halfProb_ne]
  simp only [halfProb_coe, smul_eq_mul, Nat.cast_succ]
  have h1 : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hs1 := (hasSum_coe_mul_geometric_of_norm_lt_one h1).summable
  have hs2 := (hasSum_geometric_of_norm_lt_one h1).summable
  have : ∀ n : ℕ, (1 - 1 / 2 : ℝ) ^ n * (1 / 2) * (n + 1)
      = (1 / 2) * (n * (1 / 2 : ℝ) ^ n) + (1 / 2) * (1 / 2 : ℝ) ^ n := by
    intro n; norm_num; ring
  simp_rw [this]
  rw [Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one h1, tsum_geometric_of_norm_lt_one h1]
  norm_num

/-- Grinstead–Snell Example 6.2 (PR-137). A random variable `X` (the number of tosses of a fair
coin until the first head) with `P(X = i) = 2⁻ⁱ` for `i ≥ 1`, i.e. with law `firstHeadLaw`, has
those probabilities and mean `E(X) = 2`. -/
@[kb "grinsteadsnell2006" "Example 6.2, p. 234"]
theorem first_head_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ}
    (hX : HasLaw X firstHeadLaw P) :
    (∀ i : ℕ, 1 ≤ i → P.real {ω | X ω = i} = (1 / 2 : ℝ) ^ i) ∧ ∫ ω, (X ω : ℝ) ∂P = 2 := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have h := hX.map_eq
    have : P.real {ω | X ω = i} = (P.map X).real {i} := by
      rw [measureReal_def, measureReal_def, Measure.map_apply_of_aemeasurable hX.aemeasurable
        (MeasurableSet.singleton _)]
      rfl
    rw [this, h, firstHeadLaw_singleton i hi]
  · have := hX.integral_comp (f := fun x : ℕ => (x : ℝ)) (by fun_prop)
    simpa [Function.comp_def, firstHeadLaw_integral] using this

/-- Grinstead–Snell Example 6.3 (PR-137), the law form. The St. Petersburg payment `2^n`, where
`n` is the number of tosses up to the first head, has no expectation: the series
`∑ 2ⁿ · 2⁻ⁿ = ∑ 1` diverges. -/
@[kb "grinsteadsnell2006" "Example 6.3, p. 235"]
theorem st_petersburg_not_integrable :
    ¬ Integrable (fun n : ℕ => (2 : ℝ) ^ n) firstHeadLaw := by
  rw [firstHeadLaw, integrable_map_measure (by fun_prop) (by fun_prop),
    Function.comp_def, integrable_geometricMeasure_iff halfProb_ne]
  intro h
  have h2 : (fun n : ℕ => (1 - ((halfProb : unitInterval) : ℝ)) ^ n * (halfProb : ℝ) *
      ‖(2 : ℝ) ^ (Nat.succ n)‖) = fun _ => (1 : ℝ) := by
    funext n
    simp only [halfProb_coe, norm_pow, Real.norm_ofNat, Nat.succ_eq_add_one]
    rw [pow_succ]
    have : (1 - 1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
      rw [← mul_pow]; norm_num
    linear_combination this
  rw [h2] at h
  simpa using h.tendsto_atTop_zero

/-- Grinstead–Snell Example 6.3 (PR-137), the random-variable form: if `X` is the number of
tosses until the first head, the St. Petersburg payment `2^X` is not integrable. -/
@[kb "grinsteadsnell2006" "Example 6.3, p. 235"]
theorem st_petersburg_payment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ}
    (hX : HasLaw X firstHeadLaw P) :
    ¬ Integrable (fun ω => (2 : ℝ) ^ X ω) P := by
  intro h
  exact st_petersburg_not_integrable
    (by rw [← hX.map_eq]; exact (integrable_map_measure (by fun_prop) hX.aemeasurable).2 h)

/-! ## Uniform measures on finite types -/

/-- The uniform probability measure on a finite nonempty type: mass `1/card` at each point. -/
noncomputable def fairMeasure (α : Type*) [Fintype α] [MeasurableSpace α] : Measure α :=
  ((Fintype.card α : ℝ≥0∞)⁻¹) • Measure.count

instance (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] : IsProbabilityMeasure (fairMeasure α) := by
  refine ⟨?_⟩
  simp only [fairMeasure, smul_apply, Measure.count_univ, smul_eq_mul]
  rw [ENat.card_eq_coe_fintype_card]
  simp [ENNReal.inv_mul_cancel]

lemma integral_fairMeasure (α : Type*) [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) :
    ∫ a, f a ∂fairMeasure α = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  rw [fairMeasure, integral_smul_measure, integral_count]
  simp [ENNReal.toReal_inv]

/-! ## Examples 6.9 and 6.10: expectation of a product (PR-138) -/

/-- Number of heads (`1` for heads, `0` for tails) in one toss. -/
def headsCount (b : Bool) : ℝ := if b then 1 else 0

/-- Grinstead–Snell Example 6.9 (PR-138). For two independent fair tosses (the uniform
measure on `Bool × Bool`), `E(X₁ X₂) = E(X₁) E(X₂) = 1/4`. -/
@[kb "grinsteadsnell2006" "Example 6.9, p. 242"]
theorem two_tosses_product :
    ∫ ω, headsCount ω.1 * headsCount ω.2 ∂fairMeasure (Bool × Bool) = 1 / 4 ∧
    (∫ ω, headsCount ω.1 ∂fairMeasure (Bool × Bool)) *
      (∫ ω, headsCount ω.2 ∂fairMeasure (Bool × Bool)) = 1 / 4 := by
  simp only [integral_fairMeasure, Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool,
    Fintype.sum_bool, headsCount]
  norm_num

/-- Grinstead–Snell Example 6.10 (PR-138). For one toss `X` of a fair coin and `Y = 1 - X`,
`E(XY) = 0` although `E(X) E(Y) = 1/4`. -/
@[kb "grinsteadsnell2006" "Example 6.10, p. 242"]
theorem one_toss_dependent_product :
    ∫ b, headsCount b * (1 - headsCount b) ∂fairMeasure Bool = 0 ∧
    (∫ b, headsCount b ∂fairMeasure Bool) * (∫ b, (1 - headsCount b) ∂fairMeasure Bool)
      = 1 / 4 := by
  simp only [integral_fairMeasure, Fintype.card_bool, Fintype.sum_bool, headsCount]
  norm_num

/-! ## Example 6.12: craps (PR-139) -/

/-- Probability that two fair dice have sum `s`, by counting the 36 equally likely pairs. -/
def diceSumProb (s : ℕ) : ℚ :=
  ((univ.filter fun x : Fin 6 × Fin 6 => x.1.val + x.2.val + 2 = s).card : ℚ) / 36

/-- The points of craps. -/
def crapsPoints : Finset ℕ := {4, 5, 6, 8, 9, 10}

/-- The player's probability of winning at craps, by the book's two-stage tree: win at once on
7 or 11, otherwise with point `r` win with the conditional probability `P(r) / (P(r) + P(7))`
that `r` comes before `7`. -/
def crapsWinProb : ℚ :=
  diceSumProb 7 + diceSumProb 11 +
    ∑ r ∈ crapsPoints, diceSumProb r * (diceSumProb r / (diceSumProb r + diceSumProb 7))

/-- Grinstead–Snell Example 6.12 (PR-139). The probability of winning at craps is `244/495`, so
the loss probability is `251/495` and the expected winnings of a one-dollar bet are
`244/495 - 251/495 = -7/495`. -/
@[kb "grinsteadsnell2006" "Example 6.12, p. 243"]
theorem craps_win_probability :
    crapsWinProb = 244 / 495 ∧ crapsWinProb - (1 - crapsWinProb) = -7 / 495 := by
  have h : crapsWinProb = 244 / 495 := by
    have h4 : diceSumProb 4 = 3 / 36 := by decide +kernel
    have h5 : diceSumProb 5 = 4 / 36 := by decide +kernel
    have h6 : diceSumProb 6 = 5 / 36 := by decide +kernel
    have h7 : diceSumProb 7 = 6 / 36 := by decide +kernel
    have h8 : diceSumProb 8 = 5 / 36 := by decide +kernel
    have h9 : diceSumProb 9 = 4 / 36 := by decide +kernel
    have h10 : diceSumProb 10 = 3 / 36 := by decide +kernel
    have h11 : diceSumProb 11 = 2 / 36 := by decide +kernel
    simp [crapsWinProb, crapsPoints, h4, h5, h6, h7, h8, h9, h10, h11]
    norm_num
  exact ⟨h, by rw [h]; norm_num⟩

/-- Grinstead–Snell Example 6.12 (PR-139), stage two. The probability that the point `r`
(probability `q` per roll) comes up before `7` (probability `s` per roll), summed over the
number `n` of rolls that show neither, is the geometric series `∑ (1 - q - s)ⁿ q = q / (q + s)`. -/
@[kb "grinsteadsnell2006" "Example 6.12, p. 243"]
theorem craps_point_before_seven {q s : ℝ} (hq : 0 < q) (hs : 0 ≤ s) (h : q + s < 2) :
    ∑' n : ℕ, (1 - q - s) ^ n * q = q / (q + s) := by
  have h1 : ‖1 - q - s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one h1]
  have : 1 - (1 - q - s) = q + s := by ring
  rw [this]; field_simp

/-- Grinstead–Snell Example 6.12 (PR-139), stage two for the dice: for each point `r` the
series over the rolls equals the conditional probability used in `crapsWinProb`. -/
@[kb "grinsteadsnell2006" "Example 6.12, p. 243"]
theorem craps_point_series (r : ℕ) (hr : r ∈ crapsPoints) :
    ∑' n : ℕ, (1 - (diceSumProb r : ℝ) - (diceSumProb 7 : ℝ)) ^ n * (diceSumProb r : ℝ)
      = ((diceSumProb r / (diceSumProb r + diceSumProb 7) : ℚ) : ℝ) := by
  have key : ∀ r ∈ crapsPoints, 0 < diceSumProb r ∧ diceSumProb r + diceSumProb 7 < 2 := by
    intro r hr
    simp only [crapsPoints, mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by decide +kernel, by decide +kernel⟩
  obtain ⟨hq, hlt⟩ := key r hr
  have h7 : (0 : ℚ) ≤ diceSumProb 7 := by decide +kernel
  have := craps_point_before_seven (q := (diceSumProb r : ℝ)) (s := (diceSumProb 7 : ℝ))
    (by exact_mod_cast hq) (by exact_mod_cast h7) (by exact_mod_cast hlt)
  rw [this]; push_cast; rfl

/-! ## Example 6.13: roulette (PR-140) -/

/-- Grinstead–Snell Example 6.13 (PR-140). On a Las Vegas wheel of 38 equally likely slots, of
which the set `R` of 18 is red, the winnings `X` of a one-dollar bet on red (`+1` on red, `-1`
otherwise) have mean `-1/19` (the book's `-.0526`). -/
@[kb "grinsteadsnell2006" "Example 6.13, p. 245"]
theorem roulette_expected_winnings (R : Finset (Fin 38)) (hR : R.card = 18) :
    ∫ ω, (if ω ∈ R then (1 : ℝ) else -1) ∂fairMeasure (Fin 38) = -1 / 19 := by
  rw [integral_fairMeasure, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  have h2 : (univ.filter fun a : Fin 38 => a ∉ R).card = 20 := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin 38)))
      (fun a => a ∈ R)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hR] at this
    simp at this; omega
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hR, h2]
  simp; norm_num

/-! ## Examples 6.17 and 6.18: one die and averages of dice (PR-141) -/

/-- The value `1, …, 6` shown by the face `i : Fin 6`. -/
def dieValue (i : Fin 6) : ℝ := (i : ℕ) + 1

/-- The law of one fair die as a measure on `ℝ`. -/
noncomputable def dieLaw : Measure ℝ := (fairMeasure (Fin 6)).map dieValue

instance : IsProbabilityMeasure dieLaw := by
  unfold dieLaw; infer_instance

lemma dieLaw_memLp : MemLp id 2 dieLaw := by
  unfold dieLaw
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact MemLp.of_discrete

/-- Grinstead–Snell Example 6.17 (PR-141), on the sample space `Fin 6`. For one roll of a fair
die, `E(X) = 7/2` and `V(X) = 35/12`. -/
@[kb "grinsteadsnell2006" "Example 6.17, p. 265"]
theorem die_mean_variance :
    ∫ i, dieValue i ∂fairMeasure (Fin 6) = 7 / 2 ∧
    Var[dieValue; fairMeasure (Fin 6)] = 35 / 12 := by
  have hm : ∫ i, dieValue i ∂fairMeasure (Fin 6) = 7 / 2 := by
    simp only [integral_fairMeasure, Fin.sum_univ_six, dieValue, Fintype.card_fin]
    norm_num
  refine ⟨hm, ?_⟩
  rw [variance_eq_sub MemLp.of_discrete]
  simp only [Pi.pow_apply]
  rw [integral_fairMeasure, hm]
  simp only [Fin.sum_univ_six, dieValue, Fintype.card_fin]
  norm_num

/-- Grinstead–Snell Example 6.17 (PR-141), the law form: a random variable `X` with the law of a
fair die has `E(X) = 7/2` and `V(X) = 35/12`. -/
@[kb "grinsteadsnell2006" "Example 6.17, p. 265"]
theorem die_law_mean_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X dieLaw P) : P[X] = 7 / 2 ∧ Var[X; P] = 35 / 12 := by
  have hmap : ∀ f : ℝ → ℝ, Measurable f → AEMeasurable f dieLaw := fun f hf => hf.aemeasurable
  refine ⟨?_, ?_⟩
  · rw [hX.integral_eq, dieLaw, integral_map (by fun_prop) (by fun_prop)]
    exact die_mean_variance.1
  · rw [hX.variance_eq, dieLaw, variance_map aemeasurable_id (by fun_prop)]
    exact die_mean_variance.2

/-- Grinstead–Snell Example 6.18 (PR-141). If `X₀, X₁, …` are independent rolls of a fair die,
the average `A_n = (X₀ + ⋯ + X_{n-1}) / n` of `n ≥ 1` rolls has variance `35/(12 n)`. -/
@[kb "grinsteadsnell2006" "Example 6.18, p. 269"]
theorem die_average_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hind : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) dieLaw P) {n : ℕ} (hn : 1 ≤ n) :
    Var[(n : ℝ)⁻¹ • ∑ i ∈ range n, X i; P] = 35 / (12 * n) := by
  have hv : ∀ i, Var[X i; P] = 35 / 12 := fun i => (die_law_mean_variance (hX i)).2
  rw [variance_smul, IndepFun.variance_sum (fun i _ => (hX i).memLp dieLaw_memLp)
    (fun i _ j _ hij => hind.indepFun hij)]
  simp only [hv, sum_const, card_range, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

end UndergradKB.Probability
