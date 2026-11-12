import UndergradKB.Combinatorics.Probability.Discrete
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 10: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch10b

open Probability

/-- CO-240. Linearity of expectation: the expectation of a finite sum of random variables is the
sum of their expectations. -/
@[kb "kellertrotter2017" "Proposition 10.17, p. 244"]
theorem prop_10_17_expect_sum {Ω : Type*} [Fintype Ω] (μ : FinProbSpace Ω) {ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ) :
    (μ.expect fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.expect (X i) :=
  FinProbSpace.expect_finset_sum μ s X

/-- CO-241. The number of successes in `n` Bernoulli trials with success probability `q` has
expectation `n q`. -/
@[kb "kellertrotter2017" "Example 10.18, p. 244"]
theorem ex_10_18_expect_successes (n : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ((bernoulliSpace n h0 h1).expect fun ω : Fin n → Bool => ((Finset.univ.filter fun i : Fin n => ω i = true).card : ℝ)) =
      n * q :=
  expect_successes n h0 h1

/-- CO-245. The number of successes in `n` Bernoulli trials with success probability `q` has
variance `n q (1-q)`. -/
@[kb "kellertrotter2017" "Example 10.22, p. 246"]
theorem ex_10_22_variance_successes (n : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ((bernoulliSpace n h0 h1).variance fun ω : Fin n → Bool =>
        ((Finset.univ.filter fun i : Fin n => ω i = true).card : ℝ)) =
      n * q * (1 - q) :=
  variance_successes n h0 h1

/-- CO-248. Repeated independent sampling that stops at the first occurrence of a winning event
(probability `a`) or losing event (probability `b`) wins with probability `a / (a + b)`: the
series `∑ₖ (1-a-b)^k a` sums to `a / (a+b)`. -/
@[kb "kellertrotter2017" "Example 10.28, p. 249"]
theorem ex_10_28_win_probability (a b : ℝ) (hab : a + b ≤ 1) (hpos : 0 < a + b) :
    HasSum (fun k : ℕ => (1 - a - b) ^ k * a) (a / (a + b)) :=
  FinProbSpace.hasSum_win a b hab hpos

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch10b
