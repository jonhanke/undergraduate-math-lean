import UndergradKB.Combinatorics.Counting.Basic2
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 7: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch07b

/-- CO-181. The number of functions `[n] → [m]` avoiding a set `S` of `k` values is `(m-k)^n`. -/
@[kb "kellertrotter2017" "Lemma 7.8, p. 170"]
theorem lem_7_8_functions_avoiding (n m : ℕ) (S : Finset (Fin m)) :
    Fintype.card { f : Fin n → Fin m // ∀ i : Fin n, f i ∉ S } = (m - S.card) ^ n :=
  card_functions_avoiding n m S

/-- CO-184. The number of surjections `[n] → [m]` is `∑ₖ (-1)^k C(m,k) (m-k)^n`. -/
@[kb "kellertrotter2017" "Theorem 7.9, p. 170"]
theorem thm_7_9_surjections (n m : ℕ) :
    (Fintype.card { f : Fin n → Fin m // Function.Surjective f } : ℤ) =
      ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (m.choose k : ℤ) * ((m : ℤ) - k) ^ n :=
  card_surjections n m

/-- CO-182. The number of permutations of `[n]` fixing every point of a set `S` of size `k`
is `(n-k)!`. -/
@[kb "kellertrotter2017" "Lemma 7.10, p. 171"]
theorem lem_7_10_perms_fixing (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card { σ : Equiv.Perm (Fin n) // ∀ i ∈ S, σ i = i } = (n - S.card).factorial :=
  card_perms_fixing n S

/-- CO-186. The number of derangements of `[n]` is `∑ₖ (-1)^k C(n,k) (n-k)!`. -/
@[kb "kellertrotter2017" "Theorem 7.11, p. 171"]
theorem thm_7_11_derangements (n : ℕ) :
    (Fintype.card (derangements (Fin n)) : ℤ) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k).factorial : ℤ) :=
  card_derangements_sum n

/-- CO-190. If distinct primes `p₁, …, p_k` all divide `n`, then exactly `n / (p₁ ⋯ p_k)` of the
integers `1, …, n` are divisible by all of them. -/
@[kb "kellertrotter2017" "Proposition 7.15, p. 174"]
theorem prop_7_15_multiples_of_primes (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hn : ∀ p ∈ P, p ∣ n) :
    {x ∈ Finset.Icc 1 n | ∀ p ∈ P, p ∣ x}.card = n / ∏ p ∈ P, p :=
  card_multiples_of_primes n P hP hn

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch07b
