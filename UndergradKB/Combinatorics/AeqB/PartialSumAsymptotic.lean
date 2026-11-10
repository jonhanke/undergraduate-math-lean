import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB.PartialSumAsymptotic
open Finset Filter Topology Asymptotics

/-- Normalised terms `C(3n, n-i) / C(3n, n)` (zero when `i > n`). -/
noncomputable def f (n i : ℕ) : ℝ :=
  if i ≤ n then ((3 * n).choose (n - i) : ℝ) / ((3 * n).choose n : ℝ) else 0

private lemma choose_ne (n : ℕ) : ((3 * n).choose n : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'

private lemma f_nonneg (n i : ℕ) : 0 ≤ f n i := by
  unfold f; split_ifs <;> positivity

private lemma rec_real (n i : ℕ) (h : i + 1 ≤ n) :
    ((3 * n).choose (n - (i + 1)) : ℝ) * (2 * n + i + 1)
      = ((3 * n).choose (n - i) : ℝ) * ((n : ℝ) - i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := Nat.choose_succ_right_eq (3 * (i + 1 + m)) m
  have e1 : i + 1 + m - (i + 1) = m := by omega
  have e2 : i + 1 + m - i = m + 1 := by omega
  have e3 : 3 * (i + 1 + m) - m = 2 * (i + 1 + m) + i + 1 := by omega
  rw [e1, e2]
  rw [e3] at h1
  have := congrArg (Nat.cast : ℕ → ℝ) h1
  push_cast at this ⊢
  linear_combination (-1 : ℝ) * this

private lemma f_succ (n i : ℕ) (h : i + 1 ≤ n) :
    f n (i + 1) = f n i * (((n : ℝ) - i) / (2 * n + i + 1)) := by
  have hr := rec_real n i h
  have hC := choose_ne n
  have hd : (2 * (n : ℝ) + i + 1) ≠ 0 := by positivity
  unfold f
  rw [if_pos h, if_pos (by omega), div_mul_div_comm, div_eq_div_iff hC (mul_ne_zero hC hd)]
  linear_combination ((3 * n).choose n : ℝ) * hr

private lemma f_le (i : ℕ) : ∀ n, f n i ≤ (1 / 2) ^ i := by
  induction i with
  | zero =>
    intro n
    unfold f
    simp only [Nat.zero_le, if_true, Nat.sub_zero, pow_zero]
    rw [div_self (choose_ne n)]
  | succ i ih =>
    intro n
    by_cases h : i + 1 ≤ n
    · rw [f_succ n i h, pow_succ]
      have h2 : ((n : ℝ) - i) / (2 * n + i + 1) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith
      have h3 : 0 ≤ ((n : ℝ) - i) / (2 * n + i + 1) := by
        apply div_nonneg
        · have : (i : ℝ) + 1 ≤ n := by exact_mod_cast h
          linarith
        · positivity
      exact mul_le_mul (ih n) h2 h3 (by positivity)
    · have : f n (i + 1) = 0 := by unfold f; rw [if_neg h]
      rw [this]; positivity

private lemma ratio_tendsto (i : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) - i) / (2 * n + i + 1)) atTop (𝓝 (1 / 2)) := by
  have heq : (fun n : ℕ => ((n : ℝ) - i) / (2 * n + i + 1))
      = fun n : ℕ => 1 / 2 - ((3 * (i : ℝ) + 1) / 2) / (2 * n + i + 1) := by
    funext n
    have : (2 * (n : ℝ) + i + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [heq]
  have hat : Tendsto (fun n : ℕ => 2 * (n : ℝ) + i + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith) tendsto_natCast_atTop_atTop
  have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
    (Tendsto.div_atTop (tendsto_const_nhds (x := (3 * (i : ℝ) + 1) / 2)) hat)
  simpa using this

private lemma f_tendsto (i : ℕ) : Tendsto (fun n => f n i) atTop (𝓝 ((1 / 2 : ℝ) ^ i)) := by
  induction i with
  | zero =>
    have : (fun n => f n 0) = fun _ => (1 : ℝ) := by
      funext n
      unfold f
      simp only [Nat.zero_le, if_true, Nat.sub_zero]
      exact div_self (choose_ne n)
    rw [this]; simpa using tendsto_const_nhds
  | succ i ih =>
    have h := ih.mul (ratio_tendsto i)
    rw [← pow_succ] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    exact (f_succ n i hn).symm

private lemma sum_eq (n : ℕ) :
    (∑ k ∈ range (n + 1), ((3 * n).choose k : ℝ)) / ((3 * n).choose n : ℝ)
      = ∑' i, f n i := by
  rw [tsum_eq_sum (s := range (n + 1)) (fun i hi => by
    unfold f; rw [if_neg (by simpa using hi)])]
  rw [← Finset.sum_range_reflect, div_eq_mul_inv, Finset.sum_mul]
  refine sum_congr rfl fun i hi => ?_
  have : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  unfold f
  rw [if_pos this]
  congr 3

/-- CO-463. The partial sum `∑_{k ≤ n} C(3n,k)` divided by its last term `C(3n,n)` tends
to `2`.  (The book derives this from the exact identity (7.3.9); here a direct proof by
dominated convergence with the geometric bound `C(3n,n-i)/C(3n,n) ≤ 2⁻ⁱ`.) -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.3.6, p. 144"]
theorem partial_sum_ratio_tendsto :
    Tendsto (fun n : ℕ => (∑ k ∈ range (n + 1), ((3 * n).choose k : ℝ)) /
      ((3 * n).choose n : ℝ)) atTop (𝓝 2) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := f)
    (g := fun i => (1 / 2 : ℝ) ^ i) (bound := fun i => (1 / 2 : ℝ) ^ i)
    (summable_geometric_two) f_tendsto
    (Eventually.of_forall fun n i => by
      rw [Real.norm_of_nonneg (f_nonneg n i)]; exact f_le i n)
  have h2 : ∑' i : ℕ, (1 / 2 : ℝ) ^ i = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  rw [h2] at h
  simpa only [sum_eq] using h

/-- CO-463. Book-shaped form: `∑_{k ≤ n} C(3n,k) ~ 2 C(3n,n)` as `n → ∞`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.3.6, p. 144"]
theorem partial_sum_isEquivalent :
    (fun n : ℕ => ∑ k ∈ range (n + 1), ((3 * n).choose k : ℝ))
      ~[atTop] fun n : ℕ => 2 * ((3 * n).choose n : ℝ) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have h := partial_sum_ratio_tendsto.div_const 2
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
  refine h.congr fun n => ?_
  simp only [Pi.div_apply]
  rw [div_div, mul_comm (((3 * n).choose n : ℕ) : ℝ) 2]

end UndergradKB.Combinatorics.AeqB.PartialSumAsymptotic
