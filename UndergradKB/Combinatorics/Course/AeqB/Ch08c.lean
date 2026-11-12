import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Choose.Central
import UndergradKB.Combinatorics.AeqB.RotheHagen
import UndergradKB.Combinatorics.AeqB.NotClosedForm
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 8: course wrappers of results proved in this library (wave 4)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch08c

open Finset UndergradKB.Combinatorics.AeqB

/-- CO-051. The Rothe–Hagen convolution `∑_k C(tk+r,k) C(tn-tk+s,n-k) r/(tk+r) = C(tn+r+s,n)`
(generalized binomial coefficients), with the non-degeneracy hypothesis `tk + r ≠ 0`; the case
`t = 3, r = 1, s = 0` is also covered by the underlying file. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.1.1, p. 152"]
theorem ex_8_1_1_rothe_hagen (t r s : ℝ) (n : ℕ) (h : ∀ k ≤ n, t * k + r ≠ 0) :
    ∑ k ∈ range (n + 1), rhGbinom (t * k + r) k * rhGbinom (t * n - t * k + s) (n - k) *
        (r / (t * k + r)) = rhGbinom (t * n + r + s) n :=
  rothe_hagen_book t r s n h

/-- CO-502 (partial). Franel numbers `∑_k C(n,k)^3`, derangement numbers, central trinomial
coefficients and involution numbers are not closed forms (not a fixed number of hypergeometric
terms); the fifth example of the theorem, the sum of the first third of `C(3n,k)`, is not covered. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.8.1, p. 170"]
theorem thm_8_8_1_not_closed_form (K : Type*) [Field K] [CharZero K] :
    ¬ IsClosedForm (fun n : ℕ => (franel n : K)) ∧
    ¬ IsClosedForm (fun n : ℕ => (numDerangements n : K)) ∧
    ¬ IsClosedForm (fun n : ℕ => (centralTrinomial n : K)) ∧
    ¬ IsClosedForm (fun n : ℕ => (Involutions.involutionNumber n : K)) :=
  ⟨franel_not_closedForm K, derangements_not_closedForm K, centralTrinomial_not_closedForm K,
    involutions_not_closedForm K⟩

end UndergradKB.Combinatorics.Course.AeqB.Ch08c
