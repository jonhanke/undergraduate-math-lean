import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Pi
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 2 (Strings, Sets, Binomial Coefficients): thin course wrappers

Each theorem restates a book item in the book's terms and is proved by a Mathlib declaration.
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

open Finset

/-- CO-002. The size of a product of finitely many finite sets is the product of the sizes. -/
@[kb "kellertrotter2017" "Example 2.1, p. 42"]
theorem ex_2_1 {ι : Type*} [DecidableEq ι] [Fintype ι] (X : ι → Type*) [∀ i, Fintype (X i)] :
    Fintype.card (∀ i, X i) = ∏ i, Fintype.card (X i) :=
  Fintype.card_pi

/-- CO-003. There are `|X|^n` strings of length `n` over a finite alphabet `X`
(in particular `2^n` bit strings). -/
@[kb "kellertrotter2017" "Example 2.2, p. 42"]
theorem ex_2_2 (X : Type*) [Fintype X] (n : ℕ) :
    Fintype.card (Fin n → X) = Fintype.card X ^ n := by
  simp

/-- CO-003. Bit strings of length `n`: there are `2^n` of them. -/
@[kb "kellertrotter2017" "Example 2.2, p. 42"]
theorem ex_2_2_bits (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- CO-005. The number of permutations (injective strings) of length `n` from an `m`-set is
`P(m,n) = m (m-1) ... (m-n+1)`. -/
@[kb "kellertrotter2017" "Proposition 2.6, p. 44"]
theorem prop_2_6 (X : Type*) [Fintype X] (n : ℕ) :
    Fintype.card (Fin n ↪ X) = (Fintype.card X).descFactorial n := by
  simp [Fintype.card_embedding_eq]

/-- CO-027. `C(n,k) = P(n,k) / k!`. -/
@[kb "kellertrotter2017" "Proposition 2.9, p. 45"]
theorem prop_2_9 (n k : ℕ) : n.choose k = n.descFactorial k / k.factorial :=
  Nat.choose_eq_descFactorial_div_factorial n k

/-- CO-027. `C(n,k) = n! / (k! (n-k)!)` for `k ≤ n`, in multiplied-out form. -/
@[kb "kellertrotter2017" "Proposition 2.9, p. 45"]
theorem prop_2_9_factorial {n k : ℕ} (h : k ≤ n) :
    n.choose k * (k.factorial * (n - k).factorial) = n.factorial := by
  rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial h]

/-- CO-028. `C(n,k) = C(n,n-k)`. -/
@[kb "kellertrotter2017" "Proposition 2.10, p. 46"]
theorem prop_2_10 {n k : ℕ} (h : k ≤ n) : n.choose k = n.choose (n - k) :=
  (Nat.choose_symm h).symm

/-- CO-029. The binomial coefficients `C(n,i)` sum to `2^n`. -/
@[kb "kellertrotter2017" "Example 2.17, p. 48"]
theorem ex_2_17 (n : ℕ) : ∑ i ∈ range (n + 1), n.choose i = 2 ^ n :=
  Nat.sum_range_choose n

/-- CO-030. `C(k,k) + C(k+1,k) + ... + C(n,k) = C(n+1,k+1)` (also Proposition 3.14, p. 77). -/
@[kb "kellertrotter2017" "Example 2.18, p. 48"]
theorem ex_2_18 (n k : ℕ) : ∑ i ∈ Icc k n, i.choose k = (n + 1).choose (k + 1) :=
  Nat.sum_Icc_choose n k

/-- CO-032. `∑ C(n,i)^2 = C(2n,n)`. -/
@[kb "kellertrotter2017" "Example 2.20, p. 49"]
theorem ex_2_20 (n : ℕ) : ∑ i ∈ range (n + 1), (n.choose i) ^ 2 = (2 * n).choose n :=
  Nat.sum_range_choose_sq n

/-- CO-009. Putting `n` identical objects into `r` distinct cells (empty cells allowed) can be
done in `C(n+r-1, r-1)` ways: here as the number of weak compositions of `n` into `r` parts. -/
@[kb "kellertrotter2017" "Example 2.23, p. 49"]
theorem ex_2_23 (r n : ℕ) (hr : 0 < r) :
    #((univ : Finset (Fin r)).finsuppAntidiag n) = (n + r - 1).choose (r - 1) := by
  rw [Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [card_univ, Fintype.card_fin]
  rw [show n + r - 1 = r - 1 + n by omega, Nat.choose_symm_add]
  congr 1
  omega

/-- CO-033. The binomial theorem. -/
@[kb "kellertrotter2017" "Theorem 2.30, p. 53"]
theorem thm_2_30 {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) * n.choose i :=
  add_pow x y n

/-- CO-035. The multinomial theorem. -/
@[kb "kellertrotter2017" "Theorem 2.33, p. 54"]
theorem thm_2_33 {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → R) (n : ℕ) :
    (∑ i ∈ s, x i) ^ n =
      ∑ k ∈ piAntidiag s n, Nat.multinomial s k * ∏ i ∈ s, x i ^ k i :=
  Finset.sum_pow_eq_sum_piAntidiag s x n


/-! ### Definitions of Chapter 2 in the book's terms -/

/-- CO-001. An `X`-string of length `n` is a function from an `n`-element index set to `X`; there
are `|X|^n` of them, in particular `2^n` bit strings. -/
@[kb "kellertrotter2017" "Definition (unnumbered) X-string, p. 41"]
theorem def_p41_string (X : Type*) [Fintype X] (n : ℕ) :
    Fintype.card (Fin n → X) = Fintype.card X ^ n ∧ Fintype.card (Fin n → Fin 2) = 2 ^ n := by
  simp

/-- CO-004. Injective strings of length `n` over an `m`-set (permutations of length `n`) are
counted by `P(m,n) = m!/(m-n)!`, the falling product `Nat.descFactorial`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) permutation, P(m,n), p. 44"]
theorem def_p44_permutation (m n : ℕ) :
    Fintype.card (Fin n ↪ Fin m) = m.descFactorial n := by
  simp [Fintype.card_embedding_eq]

/-- CO-006. `C(n,k)` is the number of `k`-element subsets of an `n`-element set. -/
@[kb "kellertrotter2017" "Definition (unnumbered) combination, binomial coefficient, p. 45"]
theorem def_p45_combination {α : Type*} (s : Finset α) (k : ℕ) :
    #(s.powersetCard k) = s.card.choose k :=
  Finset.card_powersetCard k s

/-- CO-034. The multinomial coefficient `n!/(k_1! ⋯ k_r!)`: it satisfies
`(∏ k_i!) · multinomial = (∑ k_i)!`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) multinomial coefficient, p. 54"]
theorem def_p54_multinomial {ι : Type*} (s : Finset ι) (k : ι → ℕ) :
    (∏ i ∈ s, (k i).factorial) * Nat.multinomial s k = (∑ i ∈ s, k i).factorial :=
  Nat.multinomial_spec s k

end UndergradKB.Combinatorics.Course.KellerTrotter
