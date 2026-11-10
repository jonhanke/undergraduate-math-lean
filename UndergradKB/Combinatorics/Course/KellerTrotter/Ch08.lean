import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Binomial
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 8 (Recurrence Equations and Generating Functions): thin course wrappers
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

open Finset PowerSeries

/-- CO-195. The constant sequence `1` has generating function `1/(1-x)`: the series
`1 + x + x^2 + ...` times `1 - x` is `1`. -/
@[kb "kellertrotter2017" "Example 8.1, p. 182"]
theorem ex_8_1 : (PowerSeries.mk fun _ => (1 : ℚ)) * (1 - X) = 1 :=
  PowerSeries.mk_one_mul_one_sub_eq_one ℚ

/-- CO-196. Finite geometric sum in product form: `(1 + x + ... + x^(n-1)) (1 - x) = 1 - x^n`. -/
@[kb "kellertrotter2017" "text (8.1.1), p. 183"]
theorem text_p183_geometric_sum {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n :=
  geom_sum_mul_neg x n

/-- CO-198. The `n`-th coefficient of a product of generating functions is the convolution
`∑_{k=0}^n a_k b_{n-k}`. -/
@[kb "kellertrotter2017" "Proposition 8.3, p. 183"]
theorem prop_8_3 {R : Type*} [CommSemiring R] (A B : PowerSeries R) (n : ℕ) :
    coeff n (A * B) = ∑ k ∈ range (n + 1), coeff k A * coeff (n - k) B := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- CO-200. Putting `k` identical apples among `n` children: the coefficient of `x^k` in
`(1/(1-x))^n` (that is `(1 + x + x^2 + ...)^n`) is `C(k+n-1, k)`; here `n = d+1 ≥ 1`. -/
@[kb "kellertrotter2017" "Example 8.7, p. 188"]
theorem ex_8_7 (d k : ℕ) :
    coeff k ((PowerSeries.mk fun _ => (1 : ℚ)) ^ (d + 1)) = ((k + d).choose k : ℚ) := by
  show coeff k ((PowerSeries.mk 1 : ℚ⟦X⟧) ^ (d + 1)) = _
  rw [PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk, Nat.add_comm d k,
    Nat.choose_symm_add]

/-- CO-039. `P(p,k+1) = P(p,k) (p - k)` for the generalized falling factorial. -/
@[kb "kellertrotter2017" "Lemma 8.11, p. 190"]
theorem lem_8_11 (p : ℝ) (k : ℕ) :
    (descPochhammer ℝ (k + 1)).eval p = (descPochhammer ℝ k).eval p * (p - k) := by
  rw [descPochhammer_succ_right]
  simp

/-- CO-201. Newton's binomial theorem: `(1+x)^p = ∑ C(p,n) x^n` for real `p` and `|x| < 1`. -/
@[kb "kellertrotter2017" "Theorem 8.10, p. 190"]
theorem thm_8_10 (p x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose p n * x ^ n) ((1 + x) ^ p) := by
  have hx' : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    simpa using hx
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := p)).hasSum (y := x) (by simpa using hx')
  have hc : ∀ n : ℕ, (binomialSeries ℝ p).coeff n = Ring.choose p n := fun n => by
    rw [FormalMultilinearSeries.coeff, binomialSeries_apply]
    simp [Pi.one_def, List.ofFn_const]
  simpa [hc, mul_comm] using h

/-- CO-193. The number of partitions of `n` into odd parts equals the number of partitions
of `n` into distinct parts (Example 1.10, p. 35, in the text; Theorem 8.16 proves it). -/
@[kb "kellertrotter2017" "Theorem 8.16, p. 193"]
theorem thm_8_16 (n : ℕ) : (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card :=
  Nat.Partition.card_odds_eq_card_distincts n

/-- CO-205. The exponential generating function of `1, 1, 1, ...` is `e^x`, hence that of `2^n`
is `e^(2x)`: `(e^x)^2 = e^(2x)`. -/
@[kb "kellertrotter2017" "Example 8.17, p. 194"]
theorem ex_8_17 : exp ℚ ^ 2 = rescale (2 : ℚ) (exp ℚ) := by
  simpa using exp_pow_eq_rescale_exp (A := ℚ) 2


/-! ### Definitions of Chapter 8 in the book's terms -/

/-- CO-194. The generating function of a sequence `(a_n)` is the formal power series
`∑ a_n x^n`: its coefficients are the `a_n`, and `F(0) = a_0`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) generating function, p. 181"]
theorem def_p181_generating_function {R : Type*} [Semiring R] (a : ℕ → R) :
    (∀ n, coeff n (mk a) = a n) ∧ constantCoeff (mk a) = a 0 :=
  ⟨fun n => coeff_mk n a, by simp⟩

/-- CO-037. The generalized falling factorial: `P(p,0) = 1` and `P(p,k+1) = p · P(p-1,k)`
(Mathlib's `descPochhammer`). -/
@[kb "kellertrotter2017" "Definition 8.8, p. 190"]
theorem def_8_8_falling_factorial (p : ℝ) (k : ℕ) :
    (descPochhammer ℝ 0).eval p = 1 ∧
      (descPochhammer ℝ (k + 1)).eval p = p * (descPochhammer ℝ k).eval (p - 1) := by
  refine ⟨by simp, ?_⟩
  rw [descPochhammer_succ_left]
  simp [Polynomial.eval_comp]

/-- CO-037. `P(p,k) = p (p-1) ⋯ (p-k+1)`. -/
@[kb "kellertrotter2017" "Definition 8.8, p. 190"]
theorem def_8_8_falling_factorial_prod (p : ℝ) (k : ℕ) :
    (descPochhammer ℝ k).eval p = ∏ i ∈ range k, (p - i) :=
  descPochhammer_eval_eq_prod_range k p

/-- CO-038. The binomial coefficient of a real number: `C(p,k) = P(p,k)/k!`
(Mathlib's `Ring.choose`). -/
@[kb "kellertrotter2017" "Definition 8.9, p. 190"]
theorem def_8_9_binomial (p : ℝ) (k : ℕ) :
    Ring.choose p k = (∏ i ∈ range k, (p - i)) / (k.factorial : ℝ) := by
  rw [Ring.choose_eq_smul, ← descPochhammer_eval_eq_prod_range]
  have : (descPochhammer ℤ k).smeval p = (descPochhammer ℝ k).eval p := by
    rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      descPochhammer_map]
  rw [this, smul_eq_mul]
  ring

/-- CO-192. An integer partition of `n` is an unordered sum of positive integers equal to `n`
(a multiset of positive parts with sum `n`); partitions into odd parts and into distinct parts
are the subfamilies `Nat.Partition.odds` and `Nat.Partition.distincts`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) partition of an integer, p. 192"]
theorem def_p192_partition (n : ℕ) (p : n.Partition) :
    (∀ i ∈ p.parts, 0 < i) ∧ p.parts.sum = n ∧
      (p ∈ Nat.Partition.odds n ↔ ∀ i ∈ p.parts, ¬ Even i) ∧
      (p ∈ Nat.Partition.distincts n ↔ p.parts.Nodup) :=
  ⟨fun _ h => p.parts_pos h, p.parts_sum, by simp [Nat.Partition.odds, Nat.Partition.restricted],
    by simp [Nat.Partition.distincts]⟩

end UndergradKB.Combinatorics.Course.KellerTrotter
