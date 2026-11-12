import UndergradKB.Combinatorics.Counting.Basic2
import UndergradKB.Combinatorics.Counting.OGF
import UndergradKB.Combinatorics.Counting.EGF
import UndergradKB.Combinatorics.Counting.TreesEGF
import UndergradKB.Combinatorics.Recurrence.GeneratingFunction
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 8: course wrappers of results proved in this library (wave 3)
-/

open PowerSeries PowerSeries.WithPiTopology

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch08b

/-- CO-197. Formal power series can be differentiated and integrated termwise: for example
`d/dx (1-x)⁻¹ = (1-x)⁻² = ∑ (n+1) xⁿ`, integration inverts differentiation, and
`log(1+x)` is the integral of `(1+x)⁻¹`. -/
@[kb "kellertrotter2017" "Example 8.2, p. 183"]
theorem ex_8_2_termwise_calculus :
    (PowerSeries.derivative (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ =
        (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 ∧
      (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 = PowerSeries.mk fun n : ℕ => (n : ℚ) + 1) ∧
    (∀ f : PowerSeries ℚ, PowerSeries.derivative (formalIntegral f) = f) ∧
    (∀ f : PowerSeries ℚ,
      formalIntegral (PowerSeries.derivative f) = f - PowerSeries.C (PowerSeries.constantCoeff f)) ∧
    (formalLog1p = formalIntegral (1 + PowerSeries.X : PowerSeries ℚ)⁻¹ ∧
      PowerSeries.derivative formalLog1p = (1 + PowerSeries.X : PowerSeries ℚ)⁻¹) :=
  ⟨derivative_inv_one_sub_X, derivative_formalIntegral, formalIntegral_derivative,
    formalLog1p_eq_integral⟩

/-- CO-199. Counting solutions of `x₁ + ⋯ + x_k = n` with each `xᵢ` restricted to a set `Sᵢ`: the
count is the coefficient of `xⁿ` in the product of the per-variable generating functions; for
five positive parts it is `C(n-1, 4)`. -/
@[kb "kellertrotter2017" "Example 8.4-8.6, pp. 184-186"]
theorem ex_8_4_to_8_6_restricted_solutions :
    (∀ {ι : Type} [Fintype ι] (S : ι → Set ℕ) (n : ℕ),
      {x : ι → ℕ | (∀ i, x i ∈ S i) ∧ ∑ i, x i = n}.ncard =
        PowerSeries.coeff n (∏ i : ι, allowedSeries (S i))) ∧
    (∀ n : ℕ, {x : Fin 5 → ℕ | (∀ i, 1 ≤ x i) ∧ ∑ i, x i = n}.ncard = (n - 1).choose 4) :=
  ⟨fun S n => ncard_solutions_eq_coeff_prod S n, ncard_compositions_five_parts⟩

/-- CO-040. `C(-1/2, k) = (-1)^k C(2k, k) / 2^(2k)`. -/
@[kb "kellertrotter2017" "Lemma 8.12, p. 191"]
theorem lem_8_12_choose_neg_half (k : ℕ) :
    Ring.choose (-1 / 2 : ℚ) k = (-1) ^ k * ((2 * k).choose k : ℚ) / 2 ^ (2 * k) :=
  choose_neg_half k

/-- CO-202. The series `(1-4x)^(-1/2)` is the generating function of the central binomial
coefficients `C(2n, n)`: the series `∑ C(2n,n) xⁿ` has constant term `1` and its square is
`(1-4x)⁻¹`. -/
@[kb "kellertrotter2017" "Theorem 8.13, p. 192"]
theorem thm_8_13_central_binom_series :
    PowerSeries.constantCoeff Recurrence.centralBinomSeries = 1 ∧
      Recurrence.centralBinomSeries ^ 2 * (1 - 4 * PowerSeries.X) = 1 :=
  Recurrence.centralBinomSeries_sq_mul

/-- CO-041. `∑_{k=0}^n C(2k,k) C(2n-2k,n-k) = 4ⁿ`. -/
@[kb "kellertrotter2017" "Corollary 8.14, p. 192"]
theorem cor_8_14_sum_central_binom (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (2 * k).choose k * (2 * (n - k)).choose (n - k) = 4 ^ n :=
  sum_centralBinom_mul n

/-- CO-203. The generating function of the partition numbers `p(n)` is the infinite product
`∏_{m ≥ 1} 1 / (1 - x^m)`. -/
@[kb "kellertrotter2017" "text (generating function of p_n), p. 192"]
theorem text_p192_partition_gf :
    HasProd (fun i : ℕ => (1 - PowerSeries.X ^ (i + 1) : PowerSeries ℚ)⁻¹)
      (PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ℚ)) :=
  Recurrence.hasProd_partition_card

/-- CO-204. The exponential generating function of `(aₙ)` is `∑ aₙ xⁿ / n!`; `eˣ` is the egf of
the constant sequence `1`, and the product of egfs is the egf of the binomial convolution. -/
@[kb "kellertrotter2017" "Definition (unnumbered) exponential generating function, p. 194"]
theorem def_p194_egf :
    (egfSeries fun _ : ℕ => (1 : ℚ)) = PowerSeries.exp ℚ ∧
      ∀ a b : ℕ → ℚ, egfSeries a * egfSeries b =
        egfSeries fun n => ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a k * b (n - k) :=
  ⟨egfSeries_one, egfSeries_mul⟩

/-- CO-206. Counting strings with per-letter count constraints: the answer is `n!` times the
coefficient of `xⁿ` in the product of per-letter egf factors; examples are `(3ⁿ+1)/2` ternary
strings with an even number of `0`s, `3ⁿ - 2·2ⁿ + 1` ternary strings with a `0` and a `1`, and the
passcode count `33847837`. -/
@[kb "kellertrotter2017" "Example 8.18-8.20, pp. 195-196"]
theorem ex_8_18_to_8_20_string_counts :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (p : ι → ℕ → Prop),
      (stringCount n p : ℚ) =
        (n.factorial : ℚ) * PowerSeries.coeff n (∏ i : ι, egfFactor (p i))) ∧
    (∀ n : ℕ, 2 * stringCount n (fun i : Fin 3 => if i = 0 then fun m => Even m else fun _ => True)
        = 3 ^ n + 1) ∧
    (∀ n : ℕ, stringCount n (fun i : Fin 3 => if i = 2 then fun _ => True else fun m => 0 < m) +
        2 * 2 ^ n = 3 ^ n + 1) ∧
    stringCount 8 passcodeConstraint = 33847837 :=
  ⟨fun n p => stringCount_eq n p, ternary_even_zeros, ternary_zero_and_one, passcode_count⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch08b
