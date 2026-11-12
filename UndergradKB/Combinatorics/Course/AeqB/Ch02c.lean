import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import UndergradKB.Combinatorics.AeqB.TripleSum
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 2: course wrappers of results proved in this library (wave 4)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch02c

open Finset UndergradKB.Combinatorics.AeqB

/-- CO-043. The sum of `C(i+j,i) C(j+k,j) C(k+i,k)` over `i + j + k = n` (with `k = n - i - j`)
equals the partial sum `∑_{j ≤ n} C(2j,j)`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation 2.2.2, p. 33"]
theorem eq_2_2_2_triple_binom_sum (n : ℕ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
      (i + j).choose i * (j + (n - i - j)).choose j * ((n - i - j) + i).choose (n - i - j)
      = ∑ j ∈ range (n + 1), (2 * j).choose j :=
  triple_binom_sum n

end UndergradKB.Combinatorics.Course.AeqB.Ch02c
