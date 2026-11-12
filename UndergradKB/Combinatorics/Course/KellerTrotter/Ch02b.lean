import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import UndergradKB.Combinatorics.Counting.Basic
import UndergradKB.Combinatorics.Counting.Misc
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 2: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch02b

open Finset

/-- CO-007. Subsets of an `n`-set correspond to bit strings of length `n`: there are `2^n` bit
strings, `C(n,k)` of them with `k` ones, and the ones of the string of `s` number `|s|`. -/
@[kb "kellertrotter2017" "Exercise 2.12, p. 46"]
theorem ex_2_12_bit_strings :
    (∀ n : ℕ, Fintype.card (Fin n → Bool) = 2 ^ n) ∧
    (∀ n k : ℕ, #{f : Fin n → Bool | #{i | f i = true} = k} = n.choose k) ∧
    (∀ (n : ℕ) (s : Finset (Fin n)), #{i | subsetEquivBits (Fin n) s i = true} = #s) :=
  ⟨card_bitStrings, card_bitStrings_with_ones, subsetEquivBits_card⟩

/-- CO-031. `∑ᵢ C(n,i) 2^i = 3^n`, counting ternary strings by their positions not equal to `2`. -/
@[kb "kellertrotter2017" "Example 2.19, p. 48"]
theorem ex_2_19_sum_choose_two_pow (n : ℕ) :
    ∑ i ∈ range (n + 1), n.choose i * 2 ^ i = 3 ^ n :=
  sum_choose_mul_two_pow n

/-- CO-008. The number of ways to write `n` as an ordered sum of `r` positive integers is
`C(n-1, r-1)`. -/
@[kb "kellertrotter2017" "Example 2.21, p. 49"]
theorem ex_2_21_positive_compositions (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    #(positiveCompositions r n) = (n - 1).choose (r - 1) :=
  card_positiveCompositions r n hr hn

/-- CO-010. Counting integer solutions with lower bounds `a i` of `∑ xᵢ = n` and of `∑ xᵢ ≤ n`
reduces to binomial coefficients; for positive (nonnegative) variables the counts are
`C(n-1,r-1)` (`C(n+r-1,r-1)`). -/
@[kb "kellertrotter2017" "Example 2.24, p. 50"]
theorem ex_2_24_2_25_solution_counts {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ (a : ι → ℕ) (n : ℕ), ∑ i, a i ≤ n →
      #(lowerBoundedSolutions a n) =
        (Fintype.card ι + (n - ∑ i, a i) - 1).choose (n - ∑ i, a i)) ∧
    (∀ (a : ι → ℕ) (n : ℕ), n < ∑ i, a i → #(lowerBoundedSolutions a n) = 0) ∧
    (∀ r n : ℕ, 0 < r → 0 < n → #(positiveCompositions r n) = (n - 1).choose (r - 1)) ∧
    (∀ r n : ℕ, 0 < r → #(piAntidiag (univ : Finset (Fin r)) n) = (n + r - 1).choose (r - 1)) ∧
    (∀ (a : ι → ℕ) (n : ℕ), ∑ i, a i ≤ n →
      #(lowerBoundedIneqSolutions a n) =
        (Fintype.card ι + (n - ∑ i, a i)).choose (n - ∑ i, a i)) :=
  ⟨fun a n h => card_lowerBoundedSolutions a n h,
   fun a n h => card_lowerBoundedSolutions_of_lt a n h,
   fun r n hr hn => card_solutions_pos r n hr hn,
   fun r n hr => card_solutions_nonneg r n hr,
   fun a n h => card_lowerBoundedIneqSolutions a n h⟩

/-- CO-011. A lattice path is a list of integer points each reached from the previous one by a
step right or up (partial: the characterization that every such path starting at `s` is the
path of an H/V word). -/
@[kb "kellertrotter2017" "Definition (unnumbered) lattice path, p. 50"]
theorem def_lattice_path_word (l : List (ℤ × ℤ)) (s : ℤ × ℤ) (hl : IsLatticePath l)
    (hs : l.head? = some s) : ∃ w, pathOfWord s w = l :=
  exists_word_of_isLatticePath l s hl hs

/-- CO-012. The number of lattice paths from `(m,n)` to `(p,q)` is `C((p-m)+(q-n), p-m)`. -/
@[kb "kellertrotter2017" "Example 2.27, p. 51"]
theorem ex_2_27_lattice_paths (m n p q : ℤ) (hmp : m ≤ p) (hnq : n ≤ q) :
    (latticePaths (m, n) (p, q)).ncard = (((p - m) + (q - n)).toNat).choose (p - m).toNat :=
  ncard_latticePaths' m n p q hmp hnq

/-- CO-013. The number of lattice paths from `(0,0)` to `(n,n)` never above the diagonal is the
Catalan number `C(2n,n)/(n+1)`. -/
@[kb "kellertrotter2017" "Example 2.28, p. 51"]
theorem ex_2_28_catalan (n : ℕ) :
    (goodPaths n).card = catalan n ∧ (goodPaths n).card = n.centralBinom / (n + 1) :=
  ⟨card_goodPaths_eq_catalan n, card_goodPaths_eq_centralBinom_div n⟩

/-- CO-014. Reflection: the bad paths to `(m+1, m+1)` are in bijection with all paths to
`(m, m+2)`, so good paths number `C(2m+2, m+1) - C(2m+2, m)`. -/
@[kb "kellertrotter2017" "Example 2.28, p. 51"]
theorem ex_2_28_reflection (m : ℕ) :
    (badPaths (m + 1)).card = (stepWords m (m + 2)).card ∧
    (goodPaths (m + 1)).card + (2 * m + 2).choose m = (2 * m + 2).choose (m + 1) :=
  ⟨card_badPaths_succ m, card_goodPaths_succ_add_choose m⟩

/-- CO-015. The number of rearrangements of a word with letter multiplicities `k i` is the
multinomial coefficient `n! / (k₁! ⋯ k_r!)`. -/
@[kb "kellertrotter2017" "Example 2.32, p. 54"]
theorem ex_2_32_rearrangements {α : Type*} [DecidableEq α] (m : Multiset α) {r : ℕ}
    (k : Fin r → ℕ) :
    (arrangements m).card = (Multiset.card m).factorial / ∏ a ∈ m.toFinset, (m.count a).factorial ∧
    (arrangements (∑ i, Multiset.replicate (k i) i)).card = Nat.multinomial Finset.univ k :=
  ⟨card_arrangements m, card_words_with_multiplicities k⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch02b
