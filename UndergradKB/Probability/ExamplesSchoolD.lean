import Mathlib.Probability.UniformOn
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Binomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete
import UndergradKB.Probability.ExamplesSchoolB
import UndergradKB.Probability.ExamplesLimits

/-! # Probability: school-level worked examples, part D (Grinstead–Snell, chapters 1 to 6)

The de Méré dice problem (Example 1.3), horse races as intervals of `[0,1)` (Example 1.5), the
region under a parabola in the unit square (Example 2.2), `n + √n ∼ n` (Example 3.4), the Galton
board (Example 3.10), the two-armed bandit with a uniform prior (Example 4.24) and an average
height (Example 6.5). -/

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal unitInterval

namespace UndergradKB.Probability

/-! ## Example 1.3: de Méré (PR-193) -/

/-- At least one outcome in `t` in `n` independent uniform rolls of a die with outcome set `α`
(the uniform measure on `Fin n → α`): `1 - (1 - |t|/|α|)^n`. -/
lemma dice_atLeastOne {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (n : ℕ) (t : Finset α) :
    (uniformOn (Set.univ : Set (Fin n → α)) {ω | ∃ i, ω i ∈ t}).toReal =
      1 - (1 - (#t : ℝ) / Fintype.card α) ^ n := by
  classical
  rw [uniform_real_pred]
  have hnot : (univ.filter fun ω : Fin n → α => ¬ ∃ i, ω i ∈ t) =
      Fintype.piFinset (fun _ : Fin n => tᶜ) := by
    ext ω; simp
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n → α)))
    (fun ω => ∃ i, ω i ∈ t)
  rw [hnot, Fintype.card_piFinset] at h
  simp only [Finset.prod_const, Finset.card_univ, Finset.card_compl, Fintype.card_fun,
    Fintype.card_fin] at h
  have hle : #t ≤ Fintype.card α := Finset.card_le_univ t
  have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h' : (#(univ.filter fun ω : Fin n → α => ∃ i, ω i ∈ t) : ℝ) =
      (Fintype.card α : ℝ) ^ n - ((Fintype.card α : ℝ) - #t) ^ n := by
    have := congrArg (Nat.cast (R := ℝ)) h
    push_cast [Nat.cast_sub hle] at this
    linarith
  rw [h', Fintype.card_fun, Fintype.card_fin]
  push_cast
  field_simp
  have hp : (Fintype.card α : ℝ) ^ n ≠ 0 := by positivity
  rw [mul_sub, mul_one, div_pow, mul_div_cancel₀ _ hp]

/-- Grinstead–Snell Example 1.3 (PR-193), first game. `n` independent rolls of one die are the
uniform measure on `Fin n → Fin 6` (face `5` is the six). The probability of at least one six in
`n` rolls is `1 - (5/6)^n`; for `n = 4` it is `1 - (5/6)^4 = 671/1296`, which exceeds `1/2` and
rounds to the book's `.518` (it lies in `[.5175, .5185)`). -/
@[kb "grinsteadsnell2006" "Example 1.3, p. 12"]
theorem demere_one_die (n : ℕ) :
    (uniformOn (Set.univ : Set (Fin n → Fin 6)) {ω | ∃ i, ω i = 5}).toReal = 1 - (5 / 6) ^ n ∧
    (uniformOn (Set.univ : Set (Fin 4 → Fin 6)) {ω | ∃ i, ω i = 5}).toReal = 1 - (5 / 6) ^ 4 ∧
    1 / 2 < 1 - ((5 : ℝ) / 6) ^ 4 ∧ 0.5175 ≤ 1 - ((5 : ℝ) / 6) ^ 4 ∧
      1 - ((5 : ℝ) / 6) ^ 4 < 0.5185 := by
  have key : ∀ m : ℕ, (uniformOn (Set.univ : Set (Fin m → Fin 6)) {ω | ∃ i, ω i = 5}).toReal =
      1 - (5 / 6) ^ m := by
    intro m
    have := dice_atLeastOne (α := Fin 6) m {5}
    have e : ({ω : Fin m → Fin 6 | ∃ i, ω i = 5}) = {ω | ∃ i, ω i ∈ ({5} : Finset (Fin 6))} := by
      ext ω; simp
    rw [e, this]
    norm_num
  refine ⟨key n, key 4, ?_, ?_, ?_⟩ <;> norm_num

/-- Grinstead–Snell Example 1.3 (PR-193), second game. `n` independent rolls of a pair of dice are
the uniform measure on `Fin n → Fin 6 × Fin 6` (the pair `(5, 5)` is a double six). The probability
of at least one double six in `n` rolls is `1 - (35/36)^n`; it is below `1/2` for every `n ≤ 24`
(at `n = 24` it is about `.491`, in `(.4905, .4915)`) and above `1/2` for `n = 25` (about `.506`,
in `(.5055, .5065)`), so `25` rolls is the least number that makes the bet favorable. -/
@[kb "grinsteadsnell2006" "Example 1.3, p. 12"]
theorem demere_two_dice (n : ℕ) :
    (uniformOn (Set.univ : Set (Fin n → Fin 6 × Fin 6)) {ω | ∃ i, ω i = (5, 5)}).toReal =
      1 - (35 / 36) ^ n ∧
    (∀ m ≤ 24, 1 - ((35 : ℝ) / 36) ^ m < 1 / 2) ∧
    (0.4905 < 1 - ((35 : ℝ) / 36) ^ 24 ∧ 1 - ((35 : ℝ) / 36) ^ 24 < 0.4915) ∧
    (1 / 2 < 1 - ((35 : ℝ) / 36) ^ 25 ∧ 0.5055 < 1 - ((35 : ℝ) / 36) ^ 25 ∧
      1 - ((35 : ℝ) / 36) ^ 25 < 0.5065) := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · have := dice_atLeastOne (α := Fin 6 × Fin 6) n {(5, 5)}
    have e : ({ω : Fin n → Fin 6 × Fin 6 | ∃ i, ω i = (5, 5)}) =
        {ω | ∃ i, ω i ∈ ({(5, 5)} : Finset (Fin 6 × Fin 6))} := by
      ext ω; simp
    rw [e, this]
    norm_num
  · intro m hm
    have h1 : ((35 : ℝ) / 36) ^ 24 ≤ ((35 : ℝ) / 36) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    have h2 : (1 : ℝ) / 2 < ((35 : ℝ) / 36) ^ 24 := by norm_num
    linarith
  all_goals norm_num

/-! ## Example 1.5: horse races (PR-194) -/

/-- Mass of a subinterval of `[0,1)` under the uniform law `volume.restrict [0,1)`. -/
lemma uniform_Ico_real {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ((volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ico a b)).toReal = b - a := by
  rw [Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 (Set.Ico_subset_Ico ha hb), Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith)]

/-- Grinstead–Snell Example 1.5 (PR-194), the four horses. For `x` uniform on `[0,1)` the intervals
`[0,.3)`, `[.3,.7)`, `[.7,.9)`, `[.9,1)` have probabilities `.3, .4, .2, .1`. -/
@[kb "grinsteadsnell2006" "Example 1.5, p. 14"]
theorem horse_race_intervals :
    ((volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ico 0 0.3)).toReal = 0.3 ∧
    ((volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ico 0.3 0.7)).toReal = 0.4 ∧
    ((volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ico 0.7 0.9)).toReal = 0.2 ∧
    ((volume.restrict (Set.Ico (0 : ℝ) 1)) (Set.Ico 0.9 1)).toReal = 0.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [uniform_Ico_real (by norm_num) (by norm_num) (by norm_num)] <;>
    norm_num

/-- Grinstead–Snell Example 1.5 (PR-194), general form. For nonnegative weights `w : Fin k → ℝ`
with sum `1`, the interval `[∑_{j<i} wⱼ, ∑_{j≤i} wⱼ)` of `[0,1)` has uniform probability `wᵢ`
(so these intervals realize any given win probabilities). -/
@[kb "grinsteadsnell2006" "Example 1.5, p. 14"]
theorem horse_race_general {k : ℕ} (w : Fin k → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (i : Fin k) :
    ((volume.restrict (Set.Ico (0 : ℝ) 1))
      (Set.Ico (∑ j ∈ univ.filter (· < i), w j) (∑ j ∈ univ.filter (· ≤ i), w j))).toReal = w i := by
  have hset : univ.filter (· ≤ i) = insert i (univ.filter (· < i)) := by
    ext j; simp [le_iff_eq_or_lt]
  have hi : i ∉ univ.filter (· < i) := by simp
  have e : ∑ j ∈ univ.filter (· ≤ i), w j = w i + ∑ j ∈ univ.filter (· < i), w j := by
    rw [hset, Finset.sum_insert hi]
  have h0 : 0 ≤ ∑ j ∈ univ.filter (· < i), w j := Finset.sum_nonneg fun j _ => hw j
  have h1 : ∑ j ∈ univ.filter (· ≤ i), w j ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => hw j
  rw [uniform_Ico_real h0 (by rw [e]; linarith [hw i]) h1, e]
  ring

/-! ## Example 2.2: a point under the parabola (PR-195) -/

/-- Grinstead–Snell Example 2.2 (PR-195). For a point `(x, y)` chosen uniformly in the unit square
(Lebesgue measure on `[0,1] × [0,1]`, total mass `1`), the event `y ≤ x²` has probability `1/3`. -/
@[kb "grinsteadsnell2006" "Example 2.2, p. 50"]
theorem parabola_probability :
    (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) Set.univ = 1 ∧
    ((volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) {p : ℝ × ℝ | p.2 ≤ p.1 ^ 2}).toReal
      = 1 / 3 := by
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) =
      (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  rw [hprod]
  refine ⟨?_, ?_⟩
  · rw [Measure.prod_apply MeasurableSet.univ]
    simp
  · have hS : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1 ^ 2} :=
      measurableSet_le measurable_snd (by fun_prop)
    rw [Measure.prod_apply hS]
    have hinner : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (volume.restrict (Set.Icc (0 : ℝ) 1)) (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 ≤ p.1 ^ 2}) =
          ENNReal.ofReal (x ^ 2) := by
      intro x hx
      have hm : MeasurableSet (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 ≤ p.1 ^ 2}) :=
        measurable_prodMk_left hS
      rw [Measure.restrict_apply hm]
      have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 ≤ p.1 ^ 2} ∩ Set.Icc 0 1 = Set.Icc 0 (x ^ 2) := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩
          exact ⟨h1, h2, by nlinarith [hx.1, hx.2]⟩
      rw [this, Real.volume_Icc, sub_zero]
    rw [setLIntegral_congr_fun measurableSet_Icc hinner]
    have hint : IntegrableOn (fun x : ℝ => x ^ 2) (Set.Icc (0 : ℝ) 1) volume :=
      (continuous_pow 2).continuousOn.integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun x : ℝ => x ^ 2) :=
      Filter.Eventually.of_forall fun x => sq_nonneg x
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    norm_num

/-! ## Example 3.4: `n + √n ∼ n` (PR-196) -/

/-- Grinstead–Snell Example 3.4 (PR-196). `n + √n` is asymptotically equal to `n` in the sense of
Definition 3.3 (`Asymptotics.IsEquivalent`, equivalently the ratio `(n + √n)/n` tends to `1`). -/
@[kb "grinsteadsnell2006" "Example 3.4, p. 89"]
theorem add_sqrt_isEquivalent :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (n : ℝ) + Real.sqrt n) (fun n : ℕ => (n : ℝ)) ∧
    Tendsto (fun n : ℕ => ((n : ℝ) + Real.sqrt n) / n) atTop (𝓝 1) := by
  have hb : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn using by exact_mod_cast hn.ne'
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + Real.sqrt n) / n) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 := h0.const_add 1
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
    have : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn'.le).symm
    field_simp
    nlinarith
  exact ⟨(Asymptotics.isEquivalent_iff_tendsto_one hb).2 ht, ht⟩

/-! ## Example 3.10: the Galton board (PR-197) -/

/-- Grinstead–Snell Example 3.10 (PR-197). A Galton board with `n` rows is a Bernoulli trials
process (the product of `n` coins, a right deflection being a success with probability `p`, each
row independent of the others); the final slot is the number of right deflections, and it is `k`
with probability `C(n,k) p^k (1-p)^(n-k)`. -/
@[kb "grinsteadsnell2006" "Example 3.10, p. 107"]
theorem galton_board_slot (p : unitInterval) (n : ℕ) :
    iIndepFun (fun (i : Fin n) (x : Fin n → Bool) => x i) (Measure.pi fun _ : Fin n => coin p) ∧
    (∀ i : Fin n, (Measure.pi fun _ : Fin n => coin p).real {x | x i = true} = p) ∧
    ∀ k : ℕ, ((Measure.pi fun _ : Fin n => coin p).map successCount).real {k} =
      (n.choose k) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  obtain ⟨_, hind, hp, hlaw⟩ := bernoulli_trials_process p n
  exact ⟨hind, hp, fun k => by rw [hlaw k, binomial_real_singleton]⟩

/-! ## Example 4.24: the two-armed bandit (PR-198) -/

lemma beta_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, x * betaPDFReal a b x = a / (a + b) := by
  have key : ∀ x, x * betaPDFReal a b x =
      (beta (a + 1) b / beta a b) * betaPDFReal (a + 1) b x := by
    intro x
    have := betaPDFReal_mul_pow ha hb 1 0 x
    simp only [pow_one, pow_zero, mul_one, Nat.cast_one, Nat.cast_zero, add_zero] at this
    rw [mul_comm, this]
  simp_rw [key]
  rw [integral_const_mul, integral_betaPDFReal (by linarith) hb]
  unfold beta
  have hg1 := (Real.Gamma_pos_of_pos ha).ne'
  have hg2 := (Real.Gamma_pos_of_pos hb).ne'
  have hg3 := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hg4 := (Real.Gamma_pos_of_pos (by linarith : 0 < a + 1 + b)).ne'
  rw [Real.Gamma_add_one ha.ne', show a + 1 + b = (a + b) + 1 by ring,
    Real.Gamma_add_one (add_pos ha hb).ne']
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  field_simp

/-- Grinstead–Snell Example 4.24 (PR-198). For a machine whose success probability `x` has the
uniform prior (the beta`(1,1)` density) and has produced `w` wins and `l` losses (likelihood
`C(w+l, w) x^w (1-x)^l`), the posterior density is the beta`(w+1, l+1)` density, and the posterior
probability of a win on the next play, `∫ x · (posterior density)`, is `(w+1)/(w+l+2)`. -/
@[kb "grinsteadsnell2006" "Example 4.24, p. 178"]
theorem bandit_posterior (w l : ℕ) :
    (∀ x : ℝ, ((w + l).choose w * (x ^ w * (1 - x) ^ l) * betaPDFReal 1 1 x) /
        (∫ y, ((w + l).choose w * (y ^ w * (1 - y) ^ l) * betaPDFReal 1 1 y))
      = betaPDFReal ((w : ℝ) + 1) ((l : ℝ) + 1) x) ∧
    ∫ x, x * (((w + l).choose w * (x ^ w * (1 - x) ^ l) * betaPDFReal 1 1 x) /
        (∫ y, ((w + l).choose w * (y ^ w * (1 - y) ^ l) * betaPDFReal 1 1 y)))
      = ((w : ℝ) + 1) / ((w : ℝ) + l + 2) := by
  have hpost : ∀ x : ℝ, ((w + l).choose w * (x ^ w * (1 - x) ^ l) * betaPDFReal 1 1 x) /
        (∫ y, ((w + l).choose w * (y ^ w * (1 - y) ^ l) * betaPDFReal 1 1 y))
      = betaPDFReal ((w : ℝ) + 1) ((l : ℝ) + 1) x := by
    intro x
    have := beta_posterior (α := 1) (β := 1) one_pos one_pos w l x
    rwa [add_comm (1 : ℝ) w, add_comm (1 : ℝ) l] at this
  refine ⟨hpost, ?_⟩
  simp_rw [hpost]
  rw [beta_mean (by positivity) (by positivity)]
  congr 1
  ring

/-! ## Example 6.5: the heights of a basketball team (PR-202) -/

/-- The heights, in inches, of the twelve players. -/
def teamHeights : Fin 12 → ℝ := ![69, 69, 66, 68, 71, 65, 67, 66, 66, 67, 70, 72]

/-- Grinstead–Snell Example 6.5 (PR-202). The average of the twelve heights
`69, 69, 66, 68, 71, 65, 67, 66, 66, 67, 70, 72` is exactly `816/12 = 68`, and this is the expected
value of the height `X` of a player chosen uniformly at random. Erratum: the book prints `67.9`;
the correct value is `68` (the sum is `816`). -/
@[kb "grinsteadsnell2006" "Example 6.5, p. 236"]
theorem team_heights_expectation :
    (∑ i, teamHeights i) = 816 ∧ (∑ i, teamHeights i) / 12 = 68 ∧
    ∫ i, teamHeights i ∂(uniformOn (Set.univ : Set (Fin 12))) = 68 ∧
    ∫ i, teamHeights i ∂(uniformOn (Set.univ : Set (Fin 12))) ≠ 67.9 := by
  have hs : (∑ i, teamHeights i) = 816 := by
    simp [teamHeights, Fin.sum_univ_succ]
    norm_num
  have hI : ∫ i, teamHeights i ∂(uniformOn (Set.univ : Set (Fin 12))) = 68 := by
    rw [uniform_integral, hs]
    norm_num
  refine ⟨hs, by rw [hs]; norm_num, hI, by rw [hI]; norm_num⟩

end UndergradKB.Probability
