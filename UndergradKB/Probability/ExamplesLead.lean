import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-!
# Probability: first time in the lead (Grinstead–Snell, Examples 10.7 and 10.14)

The recursion, closed form (Catalan numbers), generating function, total mass and mean of the time
at which Peter is first in the lead, and the chain letter sold to one person.
-/

open Finset

namespace UndergradKB.Probability

/-! ### The recursion and its closed form -/

/-- The book's recursion for `r_n`, the probability that Peter is first in the lead at time `n`:
`r_n = 0` for even `n`, `r_1 = p`, and `r_n = q (r_1 r_{n-2} + r_3 r_{n-4} + ⋯ + r_{n-2} r_1)`
for odd `n > 1`. -/
def IsLeadSeq (p q : ℝ) (r : ℕ → ℝ) : Prop :=
  (∀ n, Even n → r n = 0) ∧ r 1 = p ∧
    ∀ n, Odd n → 1 < n →
      r n = q * ∑ a ∈ range ((n - 1) / 2), r (2 * a + 1) * r (n - 2 - 2 * a)

/-- The closed form `r_{2k+1} = C_k p^{k+1} q^k`, `r_{2k} = 0`. -/
noncomputable def leadR (p q : ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 1 then (catalan (n / 2) : ℝ) * p ^ (n / 2 + 1) * q ^ (n / 2) else 0

lemma leadR_odd (p q : ℝ) (k : ℕ) :
    leadR p q (2 * k + 1) = (catalan k : ℝ) * p ^ (k + 1) * q ^ k := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [leadR, h1, h2]

lemma leadR_even (p q : ℝ) (k : ℕ) : leadR p q (2 * k) = 0 := by
  have h1 : ¬ (2 * k) % 2 = 1 := by omega
  simp [leadR]

lemma leadR_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (n : ℕ) : 0 ≤ leadR p q n := by
  unfold leadR; split_ifs <;> positivity

lemma catalan_conv_real (k : ℕ) :
    ∑ a ∈ range (k + 1), (catalan a : ℝ) * catalan (k - a) = catalan (k + 1) := by
  have h := catalan_succ' k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => catalan i * catalan j) k] at h
  exact_mod_cast h.symm

lemma isLeadSeq_leadR (p q : ℝ) : IsLeadSeq p q (leadR p q) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro n ⟨k, rfl⟩
    rw [← two_mul, leadR_even]
  · have := leadR_odd p q 0
    simpa using this
  · rintro n ⟨k, rfl⟩ hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e1 : (2 * (j + 1) + 1 - 1) / 2 = j + 1 := by omega
    rw [e1]
    have e2 : ∀ a ∈ range (j + 1), leadR p q (2 * a + 1) * leadR p q (2 * (j + 1) + 1 - 2 - 2 * a)
        = p ^ (j + 2) * q ^ j * ((catalan a : ℝ) * catalan (j - a)) := by
      intro a ha
      have ha' : a ≤ j := by simpa [Nat.lt_succ_iff] using ha
      have e3 : 2 * (j + 1) + 1 - 2 - 2 * a = 2 * (j - a) + 1 := by omega
      rw [e3, leadR_odd, leadR_odd]
      have : p ^ (a + 1) * p ^ (j - a + 1) = p ^ (j + 2) := by
        rw [← pow_add]; congr 1; omega
      have h2 : q ^ a * q ^ (j - a) = q ^ j := by
        rw [← pow_add]; congr 1; omega
      calc _ = (p ^ (a + 1) * p ^ (j - a + 1)) * (q ^ a * q ^ (j - a)) *
            ((catalan a : ℝ) * catalan (j - a)) := by ring
        _ = _ := by rw [this, h2]
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, catalan_conv_real, leadR_odd]
    ring

lemma isLeadSeq_unique {p q : ℝ} {r : ℕ → ℝ} (hr : IsLeadSeq p q r) : ∀ n, r n = leadR p q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with he | ho
    · rw [hr.1 n he]; obtain ⟨k, rfl⟩ := he; rw [← two_mul, leadR_even]
    · by_cases h1 : n = 1
      · subst h1; rw [hr.2.1]; have := leadR_odd p q 0; simpa using this.symm
      · have hn : 1 < n := by obtain ⟨k, rfl⟩ := ho; omega
        rw [hr.2.2 n ho hn, (isLeadSeq_leadR p q).2.2 n ho hn]
        congr 1
        refine Finset.sum_congr rfl fun a ha => ?_
        obtain ⟨k, rfl⟩ := ho
        have : a < k := by
          have := Finset.mem_range.1 ha; omega
        rw [ih (2 * a + 1) (by omega), ih (2 * k + 1 - 2 - 2 * a) (by omega)]

/-- Grinstead–Snell Example 10.7 (PR-179), closed form: the book's recursion for the first time in
the lead is solved by `r_{2k+1} = C_k p^{k+1} q^k`, `r_{2k} = 0` (`C_k` the Catalan numbers), and
this is the only solution. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem lead_closed_form (p q : ℝ) :
    IsLeadSeq p q (leadR p q) ∧
      ∀ r, IsLeadSeq p q r → ∀ k, r (2 * k + 1) = (catalan k : ℝ) * p ^ (k + 1) * q ^ k ∧
        r (2 * k) = 0 := by
  refine ⟨isLeadSeq_leadR p q, fun r hr k => ?_⟩
  refine ⟨?_, ?_⟩
  · rw [isLeadSeq_unique hr, leadR_odd]
  · rw [isLeadSeq_unique hr, leadR_even]

/-! ### The Catalan generating function on `[0, 1/4]` -/

lemma catalan_term_succ (x : ℝ) (k : ℕ) :
    (catalan (k + 1) : ℝ) * x ^ (k + 1) = x * ∑ ij ∈ antidiagonal k,
      ((catalan ij.1 : ℝ) * x ^ ij.1) * ((catalan ij.2 : ℝ) * x ^ ij.2) := by
  rw [catalan_succ']
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have := Finset.mem_antidiagonal.1 hij
  rw [← this, pow_succ, pow_add]; ring

/-- Partial sums of `∑ C_k x^k` are bounded by any `m` with `1 + x m² ≤ m`. -/
lemma catalan_partial_le {x m : ℝ} (hx : 0 ≤ x) (hm : 1 + x * m ^ 2 ≤ m) (N : ℕ) :
    ∑ k ∈ range N, (catalan k : ℝ) * x ^ k ≤ m := by
  set f : ℕ → ℝ := fun k => (catalan k : ℝ) * x ^ k with hf
  have fnn : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  have hstep : ∀ k, f (k + 1) = x * ∑ ij ∈ antidiagonal k, f ij.1 * f ij.2 :=
    fun k => catalan_term_succ x k
  have hm0 : 0 ≤ m := by nlinarith [mul_nonneg hx (sq_nonneg m)]
  induction N with
  | zero => simpa using hm0
  | succ N ih =>
    rw [Finset.sum_range_succ']
    have h0 : (catalan 0 : ℝ) * x ^ 0 = 1 := by simp
    have hsum : ∑ k ∈ range N, f (k + 1) = x * ∑ k ∈ range N, ∑ ij ∈ antidiagonal k,
        f ij.1 * f ij.2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hstep k
    have hflip : ∑ k ∈ range N, ∑ ij ∈ antidiagonal k, f ij.1 * f ij.2
        = ∑ i ∈ range N, ∑ j ∈ range (N - i), f i * f j := by
      rw [← Finset.sum_range_diag_flip N (fun i j => f i * f j)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * f j) k]
    have hle : ∑ i ∈ range N, ∑ j ∈ range (N - i), f i * f j
        ≤ (∑ i ∈ range N, f i) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => mul_nonneg (fnn i) (fnn j)
      exact Finset.range_mono (Nat.sub_le N i)
    have hS0 : 0 ≤ ∑ i ∈ range N, f i := Finset.sum_nonneg fun i _ => fnn i
    have h2 : (∑ i ∈ range N, f i) ^ 2 ≤ m ^ 2 := by gcongr
    rw [hsum, h0]
    nlinarith [mul_le_mul_of_nonneg_left ((hflip ▸ hle).trans h2) hx]

lemma catalan_hasSum_aux {x m : ℝ} (hx : 0 ≤ x) (hm : 1 + x * m ^ 2 ≤ m) :
    Summable (fun k => (catalan k : ℝ) * x ^ k) ∧
      ∑' k, (catalan k : ℝ) * x ^ k ≤ m := by
  have nn : ∀ k, 0 ≤ (catalan k : ℝ) * x ^ k := fun k => by positivity
  have hs := summable_of_sum_range_le nn (catalan_partial_le hx hm)
  exact ⟨hs, hs.tsum_le_of_sum_range_le (catalan_partial_le hx hm)⟩

lemma catalan_tsum_eq {x : ℝ} (hx : 0 ≤ x) (hs : Summable (fun k => (catalan k : ℝ) * x ^ k)) :
    ∑' k, (catalan k : ℝ) * x ^ k = 1 + x * (∑' k, (catalan k : ℝ) * x ^ k) ^ 2 := by
  set f : ℕ → ℝ := fun k => (catalan k : ℝ) * x ^ k with hf
  have fnn : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  have hstep : ∀ k, f (k + 1) = x * ∑ ij ∈ antidiagonal k, f ij.1 * f ij.2 :=
    fun k => catalan_term_succ x k
  have hn : Summable (fun k => ‖f k‖) := by simpa [Real.norm_of_nonneg (fnn _)] using hs
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn hn
  conv_lhs => rw [hs.tsum_eq_zero_add]
  have h0 : f 0 = 1 := by simp [hf]
  have : ∑' k, f (k + 1) = x * (∑' k, f k) ^ 2 := by
    rw [sq, hprod, ← tsum_mul_left]
    exact tsum_congr fun k => hstep k
  rw [h0, this]

/-- Catalan generating function: `∑ C_k x^k = (1 - √(1-4x)) / (2x)` for `0 < x ≤ 1/4`. -/
lemma catalan_hasSum {x : ℝ} (hx : 0 < x) (hx4 : x ≤ 1 / 4) :
    HasSum (fun k => (catalan k : ℝ) * x ^ k) ((1 - Real.sqrt (1 - 4 * x)) / (2 * x)) := by
  set s := Real.sqrt (1 - 4 * x) with hs
  have hs2 : s ^ 2 = 1 - 4 * x := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hm : 1 + x * ((1 - s) / (2 * x)) ^ 2 = (1 - s) / (2 * x) := by
    field_simp; nlinarith
  obtain ⟨hsum, hle⟩ := catalan_hasSum_aux hx.le hm.le
  have heq := catalan_tsum_eq hx.le hsum
  set C := ∑' k, (catalan k : ℝ) * x ^ k
  set m := (1 - s) / (2 * x)
  have hC : (C - m) * (1 - x * (C + m)) = 0 := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith
  have hxm : x * m = (1 - s) / 2 := by simp only [m]; field_simp
  have : C = m := by
    rcases mul_eq_zero.1 hC with h | h
    · linarith
    · have hxC : x * C ≤ x * m := mul_le_mul_of_nonneg_left hle hx.le
      have : x * C = x * m := by nlinarith
      exact mul_left_cancel₀ hx.ne' this
  rw [← this]
  exact hsum.hasSum

/-! ### Generating function -/

lemma lead_hasSum_closed {p q z : ℝ} (hp : 0 < p) (hq : 0 < q) (hz : z ≠ 0)
    (hz4 : 4 * p * q * z ^ 2 ≤ 1) :
    HasSum (fun n => leadR p q n * z ^ n) ((1 - Real.sqrt (1 - 4 * p * q * z ^ 2)) / (2 * q * z)) := by
  have hx : 0 < p * q * z ^ 2 := by positivity
  have hx4 : p * q * z ^ 2 ≤ 1 / 4 := by linarith
  have h := (catalan_hasSum hx hx4).mul_left (p * z)
  have hval : p * z * ((1 - Real.sqrt (1 - 4 * (p * q * z ^ 2))) / (2 * (p * q * z ^ 2)))
      = (1 - Real.sqrt (1 - 4 * p * q * z ^ 2)) / (2 * q * z) := by
    have : 1 - 4 * (p * q * z ^ 2) = 1 - 4 * p * q * z ^ 2 := by ring
    rw [this]; field_simp
  rw [hval] at h
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · convert h using 1
    funext k
    simp only [Function.comp, leadR_odd]
    ring
  · intro n hn
    have : n % 2 ≠ 1 := by
      intro h1; exact hn ⟨n / 2, by simp only; omega⟩
    simp [leadR, this]

/-- Grinstead–Snell Example 10.7 (PR-179), generating function: for `4pqz² ≤ 1` (in particular
`|z| ≤ 1`) the series `h(z) = ∑ r_n z^n` converges, satisfies `h = pz + qz h²`, and for `z ≠ 0`
equals `(1 - √(1 - 4pqz²)) / (2qz)`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem lead_generating_function {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {r : ℕ → ℝ}
    (hr : IsLeadSeq p q r) {z : ℝ} (hz4 : 4 * p * q * z ^ 2 ≤ 1) :
    Summable (fun n => r n * z ^ n) ∧
      ∑' n, r n * z ^ n = p * z + q * z * (∑' n, r n * z ^ n) ^ 2 ∧
      (z ≠ 0 → ∑' n, r n * z ^ n = (1 - Real.sqrt (1 - 4 * p * q * z ^ 2)) / (2 * q * z)) := by
  have hrr : r = leadR p q := funext (isLeadSeq_unique hr)
  subst hrr
  by_cases hz : z = 0
  · subst hz
    have h0 : ∀ n, leadR p q n * (0 : ℝ) ^ n = if n = 0 then leadR p q 0 else 0 := by
      intro n; rcases n with _ | n <;> simp
    have hl0 : leadR p q 0 = 0 := by simpa using leadR_even p q 0
    have : ∀ n, leadR p q n * (0 : ℝ) ^ n = 0 := by
      intro n; rw [h0]; split_ifs <;> simp [hl0]
    simp [this]
  · have hs := lead_hasSum_closed hp hq hz hz4
    refine ⟨hs.summable, ?_, fun _ => hs.tsum_eq⟩
    rw [hs.tsum_eq]
    set s := Real.sqrt (1 - 4 * p * q * z ^ 2)
    have hs2 : s ^ 2 = 1 - 4 * p * q * z ^ 2 := Real.sq_sqrt (by linarith)
    field_simp
    nlinarith

/-- Grinstead–Snell Example 10.7 (PR-179), probability of ever leading: with `p + q = 1`,
`∑ r_n = (1 - |p - q|) / (2q)`, which is `p/q` if `p < q` and `1` if `p ≥ q`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem lead_total_probability {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1)
    {r : ℕ → ℝ} (hr : IsLeadSeq p q r) :
    HasSum r ((1 - |p - q|) / (2 * q)) ∧
      (1 - |p - q|) / (2 * q) = (if p < q then p / q else 1) := by
  have hrr : r = leadR p q := funext (isLeadSeq_unique hr)
  subst hrr
  have h4 : 4 * p * q * 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p - q)]
  have h := lead_hasSum_closed hp hq one_ne_zero h4
  have hsq : Real.sqrt (1 - 4 * p * q * 1 ^ 2) = |p - q| := by
    rw [← Real.sqrt_sq_eq_abs]; congr 1
    have : q = 1 - p := by linarith
    subst this; ring
  rw [hsq] at h
  refine ⟨by simpa using h, ?_⟩
  split_ifs with hlt
  · rw [abs_of_neg (by linarith)]; field_simp; linarith
  · rw [abs_of_nonneg (by linarith)]; field_simp; linarith

/-! ### Expected waiting time -/

lemma lead_deriv_summable {p q ρ : ℝ} (hp : 0 < p) (hq : 0 < q) (hρ : 0 < ρ)
    (hρ4 : 4 * p * q * ρ ^ 2 < 1) :
    Summable (fun n : ℕ => leadR p q n * ((n : ℝ) * ρ ^ (n - 1))) := by
  set a := 4 * p * q * ρ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b hab => by simpa using hab
  have hv : Summable (fun k : ℕ => p * (2 * (k : ℝ) * a ^ k + a ^ k)) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := a) (by
      rw [Real.norm_of_nonneg ha0]; exact hρ4)
    have h2 : Summable (fun k : ℕ => a ^ k) := summable_geometric_of_lt_one ha0 hρ4
    simp only [pow_one] at h1
    refine (((h1.mul_left 2).add h2).mul_left p).congr fun k => ?_
    ring
  rw [← hinj.summable_iff]
  · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hv
    · have := leadR_nonneg hp.le hq.le (2 * k + 1)
      simp only [Function.comp]; positivity
    · simp only [Function.comp, leadR_odd]
      have e : 2 * k + 1 - 1 = 2 * k := by omega
      rw [e, pow_mul]
      have hcat : (catalan k : ℝ) ≤ 4 ^ k := by
        rw [catalan_eq_centralBinom_div]
        have h1 : (Nat.centralBinom k / (k + 1) : ℕ) ≤ 4 ^ k :=
          (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow k)
        exact_mod_cast h1
      have e2 : p ^ (k + 1) * q ^ k = p * (p * q) ^ k := by rw [mul_pow, pow_succ]; ring
      have e3 : a ^ k = 4 ^ k * (p * q) ^ k * (ρ ^ 2) ^ k := by
        rw [ha, show 4 * p * q * ρ ^ 2 = 4 * (p * q) * ρ ^ 2 by ring, mul_pow, mul_pow]
      have hpq : 0 ≤ (p * q) ^ k * (ρ ^ 2) ^ k := by positivity
      calc (catalan k : ℝ) * p ^ (k + 1) * q ^ k * (((2 * k + 1 : ℕ) : ℝ) * (ρ ^ 2) ^ k)
          = p * (catalan k : ℝ) * ((p * q) ^ k * (ρ ^ 2) ^ k) * ((2 * k + 1 : ℕ) : ℝ) := by
            rw [mul_assoc (catalan k : ℝ), e2]; ring
        _ ≤ p * 4 ^ k * ((p * q) ^ k * (ρ ^ 2) ^ k) * ((2 * k + 1 : ℕ) : ℝ) := by gcongr
        _ = p * (2 * (k : ℝ) * a ^ k + a ^ k) := by rw [e3]; push_cast; ring
  · intro n hn
    have : n % 2 ≠ 1 := by
      intro h1; exact hn ⟨n / 2, by simp only; omega⟩
    simp [leadR, this]

/-- Grinstead–Snell Example 10.7 (PR-179), expected waiting time: if `p > q` (with `p + q = 1`),
`E(T) = ∑ n r_n = 1/(p - q)`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem lead_expected_time {p q : ℝ} (hq : 0 < q) (hpq : p + q = 1) (hlt : q < p)
    {r : ℕ → ℝ} (hr : IsLeadSeq p q r) :
    HasSum (fun n : ℕ => (n : ℝ) * r n) (1 / (p - q)) := by
  have hp : 0 < p := by linarith
  have hrr : r = leadR p q := funext (isLeadSeq_unique hr)
  subst hrr
  have hqp : q = 1 - p := by linarith
  set t := 4 * p * q with ht
  have ht1 : t < 1 := by nlinarith [sq_pos_of_pos (sub_pos.2 hlt)]
  have ht0 : 0 < t := by positivity
  set ρ := Real.sqrt (2 / (1 + t)) with hρ
  have hρ2 : ρ ^ 2 = 2 / (1 + t) := Real.sq_sqrt (by positivity)
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  have hρ1 : 1 < ρ := by
    have : 1 < ρ ^ 2 := by rw [hρ2, lt_div_iff₀ (by positivity)]; linarith
    nlinarith
  have hρ4 : 4 * p * q * ρ ^ 2 < 1 := by
    rw [← ht, hρ2, mul_div_assoc', div_lt_one (by positivity)]; linarith
  have hu := lead_deriv_summable hp hq hρ0 hρ4
  -- term-by-term differentiation on (-ρ, ρ)
  have hd : HasDerivAt (fun z => ∑' n, leadR p q n * z ^ n)
      (∑' n : ℕ, leadR p q n * ((n : ℝ) * (1 : ℝ) ^ (n - 1))) 1 := by
    refine hasDerivAt_tsum_of_isPreconnected (g := fun n z => leadR p q n * z ^ n)
      (g' := fun n z => leadR p q n * ((n : ℝ) * z ^ (n - 1))) (t := Set.Ioo (-ρ) ρ)
      (u := fun n : ℕ => leadR p q n * ((n : ℝ) * ρ ^ (n - 1))) hu isOpen_Ioo
      isPreconnected_Ioo (fun n y _ => (hasDerivAt_pow n y).const_mul _) ?_
      (y₀ := 1) ⟨by linarith, hρ1⟩ ?_ ⟨by linarith, hρ1⟩
    · intro n y hy
      have hy' : |y| < ρ := abs_lt.2 hy
      have h0 := leadR_nonneg hp.le hq.le n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_mul, abs_pow, Nat.abs_cast]
      gcongr
    · have h4 : 4 * p * q * 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p - q)]
      simpa using (lead_hasSum_closed hp hq one_ne_zero h4).summable
  have hsum1 : Summable (fun n : ℕ => leadR p q n * ((n : ℝ) * (1 : ℝ) ^ (n - 1))) := by
    refine Summable.of_norm_bounded hu fun n => ?_
    have h0 := leadR_nonneg hp.le hq.le n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_mul, abs_pow, Nat.abs_cast]
    simp only [abs_one, one_pow]
    gcongr
    exact one_le_pow₀ hρ1.le
  -- the explicit form near 1
  have hs : Real.sqrt (1 - 4 * p * q * 1 ^ 2) = p - q := by
    rw [← Real.sqrt_sq (by linarith : 0 ≤ p - q)]; congr 1; subst hqp; ring
  have hF : HasDerivAt (fun z : ℝ => (1 - Real.sqrt (1 - 4 * p * q * z ^ 2)) / (2 * q * z))
      (1 / (p - q)) 1 := by
    have h1 : HasDerivAt (fun z : ℝ => 1 - 4 * p * q * z ^ 2) (-(4 * p * q * ((2 : ℕ) * 1 ^ (2 - 1)))) 1 :=
      ((hasDerivAt_pow 2 (1 : ℝ)).const_mul (4 * p * q)).const_sub 1
    have h2 := (h1.sqrt (by
      have : 1 - 4 * p * q * (1 : ℝ) ^ 2 = (p - q) ^ 2 := by subst hqp; ring
      rw [this]; positivity)).const_sub 1
    have h3 : HasDerivAt (fun z : ℝ => 2 * q * z) (2 * q * 1) 1 :=
      (hasDerivAt_id (1 : ℝ)).const_mul (2 * q)
    have h2' : HasDerivAt (fun x : ℝ => 1 - Real.sqrt (1 - 4 * p * q * x ^ 2)) _ 1 := h2
    have h4 := HasDerivAt.fun_div h2' h3 (by positivity)
    convert h4 using 1
    rw [hs]
    have hd0 : p - q ≠ 0 := by linarith
    field_simp
    subst hqp
    ring
  have heq : (fun z => ∑' n, leadR p q n * z ^ n) =ᶠ[nhds (1 : ℝ)]
      (fun z : ℝ => (1 - Real.sqrt (1 - 4 * p * q * z ^ 2)) / (2 * q * z)) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 by norm_num) hρ1] with z hz
    have hz4 : 4 * p * q * z ^ 2 ≤ 1 := by
      have : z ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hz.1.le hz.2.le 2
      nlinarith [mul_pos hp hq]
    exact (lead_hasSum_closed hp hq hz.1.ne' hz4).tsum_eq
  have := hd.unique (hF.congr_of_eventuallyEq heq)
  have hfin := hsum1.hasSum
  rw [this] at hfin
  convert hfin using 1
  funext n
  simp [mul_comm]

/-! ### Example 10.14: the chain letter sold to one person -/

/-- Expected winnings of a chain-letter buyer who sells to at most one person, each person selling
with probability `p`: `-100 + 50 p + 50 p^12`. -/
noncomputable def chainLetterWinnings (p : ℝ) : ℝ := -100 + 50 * p + 50 * p ^ 12

/-- Grinstead–Snell Example 10.14 (PR-180): the one-buyer chain letter is unfavourable, i.e. the
expected winnings are negative for every `p ∈ [0, 1)` (and vanish at `p = 1`). -/
@[kb "grinsteadsnell2006" "Example 10.14, p. 396"]
theorem chain_letter_unfavorable :
    (∀ p : ℝ, 0 ≤ p → p < 1 → chainLetterWinnings p < 0) ∧ chainLetterWinnings 1 = 0 := by
  refine ⟨fun p hp0 hp1 => ?_, by simp [chainLetterWinnings]; norm_num⟩
  have h : p ^ 12 ≤ 1 := pow_le_one₀ hp0 hp1.le
  unfold chainLetterWinnings
  linarith

/-- Grinstead–Snell Example 10.14 (PR-180), branching version: with mean offspring `m ≥ 0` the
expected winnings `50 m + 50 m^12 - 100` are positive iff `m > 1`, and for
`p₀ = 0.2, p₁ = 0.5, p₂ = 0.3` (so `m = p₁ + 2 p₂ = 1.1`) they are about `112`. -/
@[kb "grinsteadsnell2006" "Example 10.14, p. 396"]
theorem chain_letter_branching :
    (∀ m : ℝ, 0 ≤ m → (50 * m + 50 * m ^ 12 - 100 > 0 ↔ 1 < m)) ∧
      |50 * (1.1 + 1.1 ^ 12) - 100 - (112 : ℝ)| < 0.2 := by
  refine ⟨fun m hm => ⟨fun h => ?_, fun h => ?_⟩, by norm_num [abs_lt]⟩
  · by_contra hc
    push Not at hc
    have : m ^ 12 ≤ 1 := pow_le_one₀ hm hc
    linarith
  · have : 1 < m ^ 12 := one_lt_pow₀ h (by norm_num)
    linarith

end UndergradKB.Probability
