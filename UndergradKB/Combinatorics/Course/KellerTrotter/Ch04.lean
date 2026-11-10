import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Count
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 4 (Pigeonhole Principle): thin course wrappers
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

/-- CO-071. An injection from `X` to `Y` forces `|X| ≤ |Y|`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) 1-1 function, p. 83"]
theorem text_p83_injection_card {X Y : Type*} [Fintype X] [Fintype Y] {f : X → Y}
    (hf : Function.Injective f) : Fintype.card X ≤ Fintype.card Y :=
  Fintype.card_le_of_injective f hf

/-- CO-072. Pigeonhole: if `|X| > |Y|` and `f : X → Y`, two distinct elements of `X` have the
same image. -/
@[kb "kellertrotter2017" "Proposition 4.1, p. 83"]
theorem prop_4_1 {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y)
    (h : Fintype.card Y < Fintype.card X) : ∃ x x' : X, x ≠ x' ∧ f x = f x' :=
  Fintype.exists_ne_map_eq_of_card_lt f h

/-- CO-524. Euclid: there are infinitely many primes (above every bound there is a prime). -/
@[kb "kellertrotter2017" "text (infinitely many primes), p. 89"]
theorem text_p89_infinitude_of_primes (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n


/-! ### Asymptotic notation and `π(n)` -/

open Filter Asymptotics Topology in
/-- CO-521. `f = O(g)`: there are `c` and `n₀` with `|f n| ≤ c |g n|` for all `n ≥ n₀`
(for nonnegative functions this is the book's `f(n) ≤ c g(n)`). -/
@[kb "kellertrotter2017" "Definition (unnumbered) big oh, p. 87"]
theorem def_p87_bigO (f g : ℕ → ℝ) :
    f =O[atTop] g ↔ ∃ c : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |f n| ≤ c * |g n| := by
  simp only [Asymptotics.isBigO_iff, Filter.eventually_atTop, Real.norm_eq_abs]

open Filter Asymptotics Topology in
/-- CO-522. For positive `g`, `f = o(g)` exactly when `f(n)/g(n)` tends to `0`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) little oh, p. 88"]
theorem def_p88_littleO (f g : ℕ → ℝ) (hg : ∀ n, 0 < g n) :
    f =o[atTop] g ↔ Tendsto (fun n => f n / g n) atTop (𝓝 0) :=
  Asymptotics.isLittleO_iff_tendsto fun n h => absurd h (hg n).ne'

/-- CO-523. `π(n)` is the number of primes at most `n`. -/
@[kb "kellertrotter2017" "text (pi(n)), p. 88"]
theorem text_p88_primeCounting (n : ℕ) :
    Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

end UndergradKB.Combinatorics.Course.KellerTrotter
