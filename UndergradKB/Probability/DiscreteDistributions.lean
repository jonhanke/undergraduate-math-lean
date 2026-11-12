import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Vandermonde
import UndergradKB.Common.Attr

namespace UndergradKB.Probability

open MeasureTheory ProbabilityTheory Set

/-! ### Odds -/

/-- Grinstead–Snell Definition 1.4 (PR-008). If the odds `r : s` of an event equal `p / (1 - p)`
for a probability `0 < p < 1`, then `p = r / (r + s)`. -/
@[kb "grinsteadsnell2006" "Definition 1.4, p. 36"]
theorem prob_eq_of_odds {p r s : ℝ} (_hp0 : 0 < p) (hp1 : p < 1) (hr : 0 < r) (hs : 0 < s)
    (h : r / s = p / (1 - p)) : p = r / (r + s) := by
  have h1 : 0 < 1 - p := by linarith
  rw [div_eq_div_iff hs.ne' h1.ne'] at h
  rw [eq_div_iff (by positivity)]
  nlinarith

/-! ### Geometric distribution (trials up to and including the first success) -/

/-- The law of the number of trials `T ≥ 1` up to and including the first success: Mathlib's
`geometricMeasure` (which counts failures) shifted by one. -/
noncomputable def trialsLaw (p : unitInterval) : Measure ℕ :=
  (geometricMeasure p).map (· + 1)

instance (p : unitInterval) : IsProbabilityMeasure (trialsLaw p) :=
  (Measure.isProbabilityMeasure_map_iff
    (by fun_prop : AEMeasurable (fun n : ℕ => n + 1) (geometricMeasure p))).2 inferInstance

theorem trialsLaw_real_singleton {p : unitInterval} (hp : p ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (trialsLaw p).real {n} = (1 - (p : ℝ)) ^ (n - 1) * p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [measureReal_def, trialsLaw, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have : (fun x : ℕ => x + 1) ⁻¹' {m + 1} = {m} := by ext; simp
  rw [this, ← measureReal_def, geometricMeasure_real_singleton hp]
  simp

/-- The point masses of the number of trials add up to one. -/
theorem hasSum_trialsLaw {p : unitInterval} (hp : p ≠ 0) :
    HasSum (fun n : ℕ => (trialsLaw p).real {n + 1}) 1 := by
  convert hasSum_one_geometricMeasure hp using 1
  ext n
  rw [trialsLaw_real_singleton hp (by omega)]
  simp

/-- The probability `1/2` as an element of the unit interval. -/
noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem half_ne_zero : half ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp [half] at this

/-- Grinstead–Snell Example 1.13 (PR-009). A fair coin is tossed until the first head: the first
head occurs at toss `n ≥ 1` with probability `2⁻ⁿ`. -/
@[kb "grinsteadsnell2006" "Example 1.13, p. 37"]
theorem firstHead_real_singleton {n : ℕ} (hn : 1 ≤ n) :
    (trialsLaw half).real {n} = ((1 : ℝ) / 2) ^ n := by
  rw [trialsLaw_real_singleton half_ne_zero hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  simp [half, pow_succ, h2]

/-- Grinstead–Snell Example 1.13 (PR-009): the masses `2⁻ⁿ`, `n ≥ 1`, sum to `1`. -/
@[kb "grinsteadsnell2006" "Example 1.13, p. 37"]
theorem firstHead_hasSum :
    HasSum (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) 1 := by
  convert hasSum_trialsLaw half_ne_zero using 1
  ext n
  rw [firstHead_real_singleton (by omega)]

/-! ### Mean and variance of the geometric distribution -/

section MeanVar

variable {p : unitInterval}

private theorem q_lt_one (hp : p ≠ 0) : (1 - (p : ℝ)) < 1 := by
  have : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  linarith

private theorem q_nonneg (p : unitInterval) : 0 ≤ (1 - (p : ℝ)) := by
  linarith [p.2.2]

private theorem p_pos (hp : p ≠ 0) : (0 : ℝ) < p :=
  lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))

private theorem integral_trialsLaw (hp : p ≠ 0) (f : ℕ → ℝ) :
    ∫ n, f n ∂trialsLaw p = ∑' n : ℕ, ((1 - (p : ℝ)) ^ n * p) * f (n + 1) := by
  rw [trialsLaw, integral_map (by fun_prop) (measurable_from_top.aestronglyMeasurable),
    integral_geometricMeasure hp]
  simp

/-- Grinstead–Snell Example 6.4 (PR-079), law form: the mean of the number of trials up to the
first success is `1/p`. -/
@[kb "grinsteadsnell2006" "Example 6.4, p. 236"]
theorem trialsLaw_mean (hp : p ≠ 0) : ∫ n, (n : ℝ) ∂trialsLaw p = 1 / p := by
  have hp' := p_pos hp
  have hq := q_lt_one hp
  have hq0 := q_nonneg p
  rw [integral_trialsLaw hp]
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := 1 - (p : ℝ))
    (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq)).mul_left (p : ℝ)
  have h2 := (hasSum_geometric_of_lt_one hq0 hq).mul_left (p : ℝ)
  convert (h1.add h2).tsum_eq using 1
  · congr 1; ext n; push_cast; ring
  · have : (1 - (1 - (p : ℝ))) = p := by ring
    rw [this]; field_simp; ring

/-- Grinstead–Snell Example 6.19 (PR-079), law form: the variance of the number of trials up to
the first success is `q / p²`, where `q = 1 - p`. -/
@[kb "grinsteadsnell2006" "Example 6.19, p. 270"]
theorem trialsLaw_variance_integral (hp : p ≠ 0) :
    ∫ n, ((n : ℝ) - 1 / p) ^ 2 ∂trialsLaw p = (1 - (p : ℝ)) / (p : ℝ) ^ 2 := by
  have hp' := p_pos hp
  have hq := q_lt_one hp
  have hq0 := q_nonneg p
  have hn : ‖1 - (p : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq
  rw [integral_trialsLaw hp]
  have h0 := (hasSum_geometric_of_lt_one hq0 hq)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hn
  have h := ((h2.add (h1.mul_left (2 * (1 - 1 / (p : ℝ))))).add
    (h0.mul_left ((1 - 1 / (p : ℝ)) ^ 2))).mul_left (p : ℝ)
  convert h.tsum_eq using 1
  · congr 1; ext n; push_cast; ring
  · have : (1 - (1 - (p : ℝ))) = p := by ring
    rw [this]; field_simp; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Grinstead–Snell Example 6.4 (PR-079), random variable form: if `X` counts the trials up to and
including the first success (law `trialsLaw p`), then `E(X) = 1/p`. -/
@[kb "grinsteadsnell2006" "Example 6.4, p. 236"]
theorem geometric_expectation {X : Ω → ℕ} (hX : HasLaw X (trialsLaw p) P) (hp : p ≠ 0) :
    ∫ ω, (X ω : ℝ) ∂P = 1 / p := by
  have := hX.integral_comp (f := fun n : ℕ => (n : ℝ)) measurable_from_top.aestronglyMeasurable
  simpa [Function.comp_def, trialsLaw_mean hp] using this

/-- Grinstead–Snell Example 6.19 (PR-079), random variable form: with `X` as above,
`V(X) = q / p²`. -/
@[kb "grinsteadsnell2006" "Example 6.19, p. 270"]
theorem geometric_variance {X : Ω → ℕ} (hX : HasLaw X (trialsLaw p) P) (hp : p ≠ 0) :
    Var[fun ω => (X ω : ℝ); P] = (1 - (p : ℝ)) / (p : ℝ) ^ 2 := by
  have hm : AEMeasurable (fun ω => (X ω : ℝ)) P :=
    (measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp_aemeasurable hX.aemeasurable
  rw [variance_eq_integral hm, geometric_expectation hX hp]
  have := hX.integral_comp (f := fun n : ℕ => ((n : ℝ) - 1 / p) ^ 2)
    (measurable_from_top.aestronglyMeasurable)
  rw [← trialsLaw_variance_integral hp]
  simpa [Function.comp_def] using this

end MeanVar

/-! ### Memorylessness -/

section Memoryless

variable {p : unitInterval}

private theorem geometric_tail_real (hp : p ≠ 0) (k : ℕ) :
    (geometricMeasure p).real {n | k ≤ n} = (1 - (p : ℝ)) ^ k := by
  have hmeas : MeasurableSet {n : ℕ | k ≤ n} := MeasurableSet.of_discrete
  have h1 : {n : ℕ | k ≤ n}ᶜ = ↑(Finset.range k) := by
    ext t; simp
  have hcompl := measureReal_compl (μ := geometricMeasure p) hmeas
  rw [probReal_univ, h1, ← sum_measureReal_singleton] at hcompl
  simp_rw [geometricMeasure_real_singleton hp] at hcompl
  rw [← Finset.sum_mul] at hcompl
  have := mul_neg_geom_sum (1 - (p : ℝ)) k
  have e : (1 - (1 - (p : ℝ))) = p := by ring
  rw [e] at this
  rw [mul_comm, this] at hcompl
  linarith

/-- Tail of the number of trials: `P(T > k) = q ^ k` (the probability that the first `k` trials
all fail). -/
theorem trialsLaw_tail (hp : p ≠ 0) (k : ℕ) :
    trialsLaw p {t | k < t} = ENNReal.ofReal ((1 - (p : ℝ)) ^ k) := by
  have : (fun n : ℕ => n + 1) ⁻¹' {t | k < t} = {n | k ≤ n} := by
    ext n; simp
  rw [trialsLaw, Measure.map_apply (by fun_prop) MeasurableSet.of_discrete, this,
    ← geometric_tail_real hp k, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Grinstead–Snell §5.1, memoryless property (PR-051). For the number of trials `T` up to the
first success, `P(T > r + s | T > r) = P(T > s)`. We assume `p ≠ 1` so that the conditioning event
`T > r` has positive probability. -/
@[kb "grinsteadsnell2006" "§5.1 memoryless property, p. 194"]
theorem trialsLaw_memoryless (hp : p ≠ 0) (hp1 : p ≠ 1) (r s : ℕ) :
    (trialsLaw p)[{t | r + s < t} | {t | r < t}] = trialsLaw p {t | s < t} := by
  have hq : 0 < (1 - (p : ℝ)) := by
    have : (p : ℝ) ≠ 1 := fun h => hp1 (Subtype.ext h)
    have := p.2.2
    exact sub_pos.2 (lt_of_le_of_ne this ‹_›)
  have hsub : {t : ℕ | r < t} ∩ {t | r + s < t} = {t | r + s < t} := by
    ext t; simp only [mem_inter_iff, mem_ofPred_eq]; omega
  rw [cond_apply MeasurableSet.of_discrete, hsub, trialsLaw_tail hp, trialsLaw_tail hp,
    trialsLaw_tail hp, pow_add, ← ENNReal.ofReal_inv_of_pos (pow_pos hq r),
    ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_pos hq r).le)]
  congr 1
  field_simp

end Memoryless

/-! ### Negative binomial distribution -/

/-- Grinstead–Snell §5.1 (PR-052): the negative binomial mass `u(x, k, p) = C(x-1, k-1) p^k q^(x-k)`,
the probability that the `k`-th success occurs at trial `x` (meaningful for `x ≥ k ≥ 1`);
here `q = 1 - p`. -/
noncomputable def negBinomMass (x k : ℕ) (p : ℝ) : ℝ :=
  ((x - 1).choose (k - 1) : ℝ) * p ^ k * (1 - p) ^ (x - k)

/-- Grinstead–Snell §5.1 negative binomial distribution (PR-052): for `k ≥ 1` and `0 < p ≤ 1`, the
masses `u(x, k, p)`, `x = k, k+1, ...` (written `x = j + k`) sum to `1`. -/
@[kb "grinsteadsnell2006" "§5.1 negative binomial distribution, p. 195"]
theorem hasSum_negBinomMass {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun j : ℕ => negBinomMass (j + k) k p) 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hq : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one m hq).mul_left (p ^ (m + 1))
  have e : (1 - (1 - p)) = p := by ring
  rw [e, one_div, ← div_eq_mul_inv, div_self (pow_ne_zero _ hp0.ne')] at h
  convert h using 1
  · ext j
    simp only [negBinomMass]
    have e1 : j + (m + 1) - 1 = j + m := by omega
    have e2 : j + (m + 1) - (m + 1) = j := by omega
    rw [e1, e2, Nat.add_sub_cancel]
    ring

/-- Grinstead–Snell §5.1 (PR-052), indexed by the trial number `x`: the masses `u(x, k, p)` for
`x ≥ k` (and `0` below `k`) sum to `1`. -/
@[kb "grinsteadsnell2006" "§5.1 negative binomial distribution, p. 195"]
theorem hasSum_negBinomMass_trial {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun x : ℕ => if k ≤ x then negBinomMass x k p else 0) 1 := by
  rw [← hasSum_nat_add_iff' k]
  have h : ∑ i ∈ Finset.range k, (if k ≤ i then negBinomMass i k p else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => by simp [(Finset.mem_range.1 hi).not_ge])
  rw [h, sub_zero]
  convert hasSum_negBinomMass hk hp0 hp1 using 1
  ext j
  simp [add_comm j k]

/-! ### Hypergeometric distribution -/

/-- Grinstead–Snell §5.1 (PR-055): the hypergeometric mass `h(a, b, n, k) = C(a,k) C(b,n-k) / C(a+b,n)`,
the probability that `n` objects drawn without replacement from `a` special and `b` ordinary
objects include exactly `k` special ones. -/
noncomputable def hyperMass (a b n k : ℕ) : ℝ :=
  (a.choose k : ℝ) * (b.choose (n - k)) / ((a + b).choose n)

theorem vandermonde_range (a b n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), a.choose k * b.choose (n - k) = (a + b).choose n := by
  rw [Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.choose i * b.choose j) n]

/-- Grinstead–Snell §5.1 hypergeometric distribution (PR-055): the masses `h(a, b, n, k)`,
`0 ≤ k ≤ n`, sum to `1` when `n ≤ a + b` (Vandermonde's identity). -/
@[kb "grinsteadsnell2006" "§5.1 hypergeometric distribution, p. 201"]
theorem sum_hyperMass (a b n : ℕ) (hn : n ≤ a + b) :
    ∑ k ∈ Finset.range (n + 1), hyperMass a b n k = 1 := by
  have hpos : (0 : ℝ) < ((a + b).choose n : ℝ) := by exact_mod_cast Nat.choose_pos hn
  unfold hyperMass
  rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast vandermonde_range a b n

private theorem sum_mul_choose_choose (a b n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), k * (a.choose k * b.choose (n - k)) =
      if a = 0 ∨ n = 0 then 0 else a * (a + b - 1).choose (n - 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [true_or, if_true]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp [Nat.choose_eq_zero_of_lt hk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or, or_self, if_false]
  rw [Finset.sum_range_succ']
  have : ∀ k ∈ Finset.range (n' + 1),
      (k + 1) * ((a' + 1).choose (k + 1) * b.choose (n' + 1 - (k + 1)))
      = (a' + 1) * (a'.choose k * b.choose (n' - k)) := by
    intro k _
    have := Nat.add_one_mul_choose_eq a' k
    rw [Nat.add_sub_add_right]
    calc (k + 1) * ((a' + 1).choose (k + 1) * b.choose (n' - k))
        = ((a' + 1).choose (k + 1) * (k + 1)) * b.choose (n' - k) := by ring
      _ = _ := by rw [← this]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, vandermonde_range]
  simp only [zero_mul, mul_zero, add_zero]
  congr 2
  omega

/-- Grinstead–Snell §5.1 hypergeometric distribution (PR-055): the mean number of special objects
drawn is `n a / (a + b)`. -/
@[kb "grinsteadsnell2006" "§5.1 hypergeometric distribution, p. 201"]
theorem hyperMass_mean (a b n : ℕ) (hn : n ≤ a + b) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * hyperMass a b n k = (n : ℝ) * a / (a + b) := by
  have hpos : (0 : ℝ) < ((a + b).choose n : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have key : ∑ k ∈ Finset.range (n + 1), (k : ℝ) * hyperMass a b n k
      = ((∑ k ∈ Finset.range (n + 1), k * (a.choose k * b.choose (n - k)) : ℕ) : ℝ)
        / ((a + b).choose n) := by
    unfold hyperMass
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [key, sum_mul_choose_choose]
  by_cases h : a = 0 ∨ n = 0
  · rw [if_pos h]
    rcases h with rfl | rfl <;> simp
  · rw [if_neg h]
    push_neg at h
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have e : a' + 1 + b - 1 = a' + b := by omega
    rw [e]
    have h2 := Nat.add_one_mul_choose_eq (a' + b) n'
    have h3 : (a' + 1 + b) = a' + b + 1 := by omega
    rw [h3] at hpos ⊢
    have h2' : ((a' + b + 1 : ℕ) : ℝ) * ((a' + b).choose n' : ℝ)
        = ((a' + b + 1).choose (n' + 1) : ℝ) * (n' + 1 : ℕ) := by exact_mod_cast h2
    have hab : (0 : ℝ) < (a' + 1 : ℕ) + b := by positivity
    push_cast at h2' ⊢
    rw [div_eq_div_iff hpos.ne' (by positivity)]
    nlinarith [h2']

end UndergradKB.Probability
