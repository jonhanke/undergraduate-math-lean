import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesDiscrete

/-!
# Paradoxes: beagles and envelopes (Grinstead–Snell, Section 4.3)

Geller's beagles (Example 4.27), the two envelopes problem and Finn's version (Example 4.28), the
Brams–Kilgour distribution for which switching always pays (Example 4.29), and the strategy that beats
`1/2` for guessing the smaller envelope (Example 4.30).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace UndergradKB.Probability

/-! ### Geller's beagles (PR-170) -/

/-- Grinstead–Snell Example 4.27 (PR-170). Two puppies with independent, equally likely sexes (uniform
measure on `Bool × Bool`, `true` for male): given that at least one is male, the probability that both
are male is `1/3`. -/
@[kb "grinsteadsnell2006" "Example 4.27, p. 184"]
theorem beagles_bothMale :
    ((uniformOn (Set.univ : Set Family))[{f | f.1 = true ∧ f.2 = true} |
        {f | f.1 = true ∨ f.2 = true}]).toReal = 1 / 3 :=
  twoChildren_atLeastOneBoy

/-! ### Finn's version (PR-171) -/

/-- Ali's amount in Finn's version: a fair coin (`true` = heads) gives her `$5` or `$10`. -/
def finnAli (c : Bool) : ℝ := if c then 5 else 10

/-- Baba's amount in Finn's version: the other envelope. -/
def finnBaba (c : Bool) : ℝ := if c then 10 else 5

/-- Grinstead–Snell Example 4.28 (PR-171). In Finn's version the coin decides which of the `$5`, `$10`
envelopes Ali gets; Baba gets the other. Ali's expected amount if she keeps hers equals her expected
amount if she switches, namely `15/2`. -/
@[kb "grinsteadsnell2006" "Example 4.28, p. 186"]
theorem finn_keep_eq_switch :
    ∫ c, finnAli c ∂(uniformOn (Set.univ : Set Bool)) = 15 / 2 ∧
    ∫ c, finnBaba c ∂(uniformOn (Set.univ : Set Bool)) = 15 / 2 := by
  rw [uniform_integral, uniform_integral]
  simp [finnAli, finnBaba, Fintype.sum_bool]
  norm_num

/-! ### The Brams–Kilgour distribution (PR-172) -/

/-- The distribution of the smaller amount `X` in Example 4.29: `p_x = (1/3)(2/3)^(k-1)` if `x = 2^k`
with `k ≥ 1`, and `0` otherwise. -/
noncomputable def bramsP (x : ℕ) : ℝ := by
  classical
  exact if h : ∃ k : ℕ, x = 2 ^ (k + 1) then (1 / 3) * (2 / 3) ^ (Classical.choose h) else 0

lemma bramsP_pow (k : ℕ) : bramsP (2 ^ (k + 1)) = (1 / 3) * (2 / 3) ^ k := by
  have h : ∃ j : ℕ, 2 ^ (k + 1) = 2 ^ (j + 1) := ⟨k, rfl⟩
  have hc : Classical.choose h = k := by
    have := Classical.choose_spec h
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  unfold bramsP
  rw [dif_pos h, hc]

lemma bramsP_not (x : ℕ) (h : ¬ ∃ k : ℕ, x = 2 ^ (k + 1)) : bramsP x = 0 := by
  unfold bramsP
  rw [dif_neg h]

lemma bramsP_one : bramsP 1 = 0 := by
  apply bramsP_not
  rintro ⟨k, hk⟩
  have : (2 : ℕ) ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2
  omega

/-- Grinstead–Snell Example 4.29 (PR-172), part 1. `p_x` is a probability distribution on the positive
integers (it sums to `1`). -/
@[kb "grinsteadsnell2006" "Example 4.29, p. 187"]
theorem brams_hasSum : HasSum bramsP 1 := by
  have hg : HasSum (fun k : ℕ => (1 / 3 : ℝ) * (2 / 3) ^ k) 1 := by
    have := (hasSum_geometric_of_lt_one (r := (2 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_left (1 / 3)
    convert this using 1; norm_num
  have hinj : Function.Injective (fun k : ℕ => 2 ^ (k + 1)) := fun a b h => by
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  rw [← hinj.hasSum_iff]
  · convert hg using 1
    ext k; exact bramsP_pow k
  · intro x hx
    apply bramsP_not
    rintro ⟨k, hk⟩
    exact hx ⟨k, hk.symm⟩

/-- The book's switching expectation when the observed amount is `x`, with `a = p_{x/2}`, `b = p_x`:
`a/(a+b) · (x/2) + b/(a+b) · 2x`. -/
noncomputable def switchExp (a b x : ℝ) : ℝ := a / (a + b) * (x / 2) + b / (a + b) * (2 * x)

/-- Grinstead–Snell Example 4.29 (PR-172), part 2 (the book's criterion (4.6)). For an amount `x > 0` and
positive weights `a = p_{x/2}`, `b = p_x`, switching pays on average (`switchExp > x`) iff
`a/(a+b) < 2/3`. -/
@[kb "grinsteadsnell2006" "Example 4.29, p. 187"]
theorem switchExp_gt_iff {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    x < switchExp a b x ↔ a / (a + b) < 2 / 3 := by
  have hab : 0 < a + b := by linarith
  have h : b / (a + b) = 1 - a / (a + b) := by field_simp; ring
  unfold switchExp
  rw [h]
  constructor <;> intro H <;> nlinarith

/-- Grinstead–Snell Example 4.29 (PR-172), part 3. For `x = 2^k` with `k ≥ 2` (both `x/2` and `x` are
possible values of the smaller amount), `p_{x/2}/(p_{x/2}+p_x) = 3/5`, so switching pays on average:
`switchExp > x`. For `x = 2` only the point `(2, 4)` is possible (`p_1 = 0`), and switching also pays. -/
@[kb "grinsteadsnell2006" "Example 4.29, p. 187"]
theorem brams_switch_pays :
    (∀ k : ℕ, bramsP (2 ^ (k + 1)) / (bramsP (2 ^ (k + 1)) + bramsP (2 ^ (k + 2))) = 3 / 5 ∧
      (2 ^ (k + 2) : ℝ) < switchExp (bramsP (2 ^ (k + 1))) (bramsP (2 ^ (k + 2))) (2 ^ (k + 2))) ∧
    bramsP 1 = 0 ∧ (2 : ℝ) < switchExp (bramsP 1) (bramsP 2) 2 := by
  refine ⟨fun k => ?_, bramsP_one, ?_⟩
  · have e1 := bramsP_pow k
    have e2 := bramsP_pow (k + 1)
    have hr : bramsP (2 ^ (k + 1)) / (bramsP (2 ^ (k + 1)) + bramsP (2 ^ (k + 2))) = 3 / 5 := by
      rw [e1, e2, pow_succ]
      have hp : (0 : ℝ) < (2 / 3) ^ k := by positivity
      field_simp
      ring
    refine ⟨hr, ?_⟩
    have hb : 0 < bramsP (2 ^ (k + 1)) := by rw [e1]; positivity
    have hc : 0 < bramsP (2 ^ (k + 2)) := by rw [e2]; positivity
    exact (switchExp_gt_iff hb hc (by positivity)).2 (by rw [hr]; norm_num)
  · have h2 : bramsP 2 = 1 / 3 := by
      have := bramsP_pow 0
      simpa using this
    rw [bramsP_one, h2]
    unfold switchExp
    norm_num

/-! ### Guessing the smaller envelope (PR-173) -/

/-- The guess is correct in Example 4.30 when the envelope opened shows `o`, the other holds `t`, and
the number of tosses to the first head is `N = n + 1` (so `Z = N + 1/2`): the strategy says "opened is
smaller" iff `Z > o`. -/
def guessCorrect (o t n : ℕ) : Prop :=
  ((o : ℝ) < (n + 1 : ℝ) + 1 / 2 ∧ o < t) ∨ (¬ (o : ℝ) < (n + 1 : ℝ) + 1 / 2 ∧ t < o)

open Classical in
/-- Probability of a correct guess for fixed distinct amounts `x`, `y`: the coin (which envelope is
opened, probability `1/2` each) and the number of tosses `N = n + 1` (probability `2^-(n+1)`). -/
noncomputable def guessProb (x y : ℕ) : ℝ :=
  ∑' n : ℕ, ∑ c : Bool, (1 / 2 : ℝ) * (1 / 2) ^ (n + 1) *
    (if guessCorrect (if c then x else y) (if c then y else x) n then 1 else 0)

/-- `Z = N + 1/2` lies strictly between `x` and `y` (here `N = n + 1`). -/
def zBetween (x y n : ℕ) : Prop := min x y ≤ n + 1 ∧ n + 1 < max x y

lemma real_lt_iff (o n : ℕ) : (o : ℝ) < (n + 1 : ℝ) + 1 / 2 ↔ o ≤ n + 1 := by
  constructor
  · intro h
    by_contra h'
    have : ((n + 1 + 1 : ℕ) : ℝ) ≤ o := by exact_mod_cast (by omega : n + 1 + 1 ≤ o)
    push_cast at this
    linarith
  · intro h
    have : (o : ℝ) ≤ n + 1 := by exact_mod_cast h
    linarith

open Classical in
lemma guess_term (x y n : ℕ) (hxy : x ≠ y) :
    ∑ c : Bool, (1 / 2 : ℝ) * (1 / 2) ^ (n + 1) *
      (if guessCorrect (if c then x else y) (if c then y else x) n then 1 else 0)
      = (1 / 2) ^ (n + 1) * (1 / 2 + 1 / 2 * (if zBetween x y n then 1 else 0)) := by
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, guessCorrect, real_lt_iff,
    zBetween]
  rcases lt_or_gt_of_ne hxy with h | h
  · simp only [min_eq_left h.le, max_eq_right h.le]
    by_cases h1 : x ≤ n + 1 <;> by_cases h2 : y ≤ n + 1 <;> by_cases h3 : n + 1 < y <;>
      simp [h1, h2, h3, h, not_lt.2 h.le] <;> first | omega | (ring_nf; done) | skip
  · simp only [min_eq_right h.le, max_eq_left h.le]
    by_cases h1 : x ≤ n + 1 <;> by_cases h2 : y ≤ n + 1 <;> by_cases h3 : n + 1 < x <;>
      simp [h1, h2, h3, h, not_lt.2 h.le] <;> first | omega | (ring_nf; done) | skip

lemma guess_summable_w : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
  refine ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_right
    (1 / 2)).congr (fun n => ?_)
  ring

lemma guess_hasSum_w : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
  have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_right (1 / 2)
  convert this using 1
  · ext n; ring
  · norm_num

open Classical in
/-- Grinstead–Snell Example 4.30 (PR-173). Fix distinct positive integers `x`, `y` in the two envelopes.
Choose the opened envelope by a fair coin, let `N` be the number of tosses to the first head
(`P(N = n) = 2^-n`) and `Z = N + 1/2`; guess "opened is smaller" iff `Z` exceeds the opened amount. The
probability of a correct guess is `1/2 + (1/2) P(Z between x and y)`, which is strictly greater than `1/2`. -/
@[kb "grinsteadsnell2006" "Example 4.30, p. 188"]
theorem guessProb_eq_gt {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    guessProb x y = 1 / 2 + 1 / 2 * ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (if zBetween x y n then 1 else 0) ∧
    (0 : ℝ) < ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (if zBetween x y n then 1 else 0) ∧
    1 / 2 < guessProb x y := by
  have hs : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * (if zBetween x y n then 1 else 0)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) guess_summable_w
    split_ifs <;> simp
  have e : guessProb x y = 1 / 2 +
      1 / 2 * ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (if zBetween x y n then 1 else 0) := by
    unfold guessProb
    simp_rw [guess_term x y _ hxy]
    have key : ∀ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (1 / 2 + 1 / 2 * (if zBetween x y n then 1 else 0)) =
        1 / 2 * (1 / 2 : ℝ) ^ (n + 1) + 1 / 2 * ((1 / 2 : ℝ) ^ (n + 1) * (if zBetween x y n then 1 else 0)) :=
      fun n => by ring
    simp_rw [key]
    rw [Summable.tsum_add (guess_summable_w.mul_left _) (hs.mul_left _), tsum_mul_left, tsum_mul_left,
      guess_hasSum_w.tsum_eq]
    norm_num
  have hpos : (0 : ℝ) < ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * (if zBetween x y n then 1 else 0) := by
    refine hs.tsum_pos (fun n => by positivity) (min x y - 1) ?_
    have hb : zBetween x y (min x y - 1) := by
      unfold zBetween
      omega
    rw [if_pos hb]; positivity
  exact ⟨e, hpos, by rw [e]; linarith⟩

end UndergradKB.Probability
