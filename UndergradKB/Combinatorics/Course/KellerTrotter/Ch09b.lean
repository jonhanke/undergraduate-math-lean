import UndergradKB.Combinatorics.Counting.Basic2
import UndergradKB.Combinatorics.Counting.TreesEGF
import UndergradKB.Combinatorics.Recurrence.GeneratingFunction
import UndergradKB.Combinatorics.Recurrence.Examples
import UndergradKB.Combinatorics.Recurrence.General
import UndergradKB.Combinatorics.Recurrence.Linear
import UndergradKB.Combinatorics.Recurrence.Wave2Solve
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 9: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch09b

open Recurrence

/-- CO-218. Binary strings of length `n` with no two consecutive `1`s: there are `2` of length `1`,
`3` of length `2`, and `a_{n+2} = a_{n+1} + a_n` (a Fibonacci number). -/
@[kb "kellertrotter2017" "Example 9.3, p. 209"]
theorem ex_9_3_binary_no_11 :
    (binGood 1).card = 2 ∧ (binGood 2).card = 3 ∧
      (∀ n : ℕ, (binGood (n + 2)).card = (binGood (n + 1)).card + (binGood n).card) ∧
      ∀ n : ℕ, (binGood n).card = Nat.fib (n + 2) :=
  ⟨binGood_card_one, binGood_card_two, binGood_card_succ_succ, binGood_card_eq_fib⟩

/-- CO-219. Ternary strings of length `n` avoiding the substring `20`: `t₁ = 3`, `t₂ = 8` and
`t_{n+2} = 3 t_{n+1} - t_n`. -/
@[kb "kellertrotter2017" "Example 9.4, p. 209"]
theorem ex_9_4_ternary_no_20 :
    (ternGood 1).card = 3 ∧ (ternGood 2).card = 8 ∧
      (∀ n : ℕ, (ternGood (n + 2)).card + (ternGood n).card = 3 * (ternGood (n + 1)).card) ∧
      ∀ n : ℕ, ((ternGood (n + 2)).card : ℤ) =
        3 * ((ternGood (n + 1)).card : ℤ) - (ternGood n).card :=
  ⟨ternGood_card_one, ternGood_card_two, ternGood_card_succ_succ, ternGood_card_recurrence⟩

/-- CO-220 (partial). `n` lines in general position cut the plane into `1 + C(n+1, 2)` regions: any
sequence with `r₀ = 1` and `r_{n+1} = r_n + n + 1` has this closed form (the geometric derivation of
the recurrence is not formalized). -/
@[kb "kellertrotter2017" "text (lines and regions), p. 210"]
theorem text_p210_lines_regions (r : ℕ → ℕ) (h0 : r 0 = 1) (hr : ∀ n, r (n + 1) = r n + (n + 1)) :
    ∀ n : ℕ, r n = 1 + (n + 1).choose 2 :=
  lines_regions_closed_form r h0 hr

/-- CO-221. A linear recurrence with constant coefficients `c₀ a_{n+k} + ⋯ + c_k a_n = g(n)` holds
exactly when the characteristic polynomial of the coefficients, evaluated at the advancement
operator, sends `a` to `g`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) linear recurrence equation, p. 211"]
theorem def_p211_linear_recurrence {K : Type*} [Field K] {k : ℕ} (c : Fin (k + 1) → K)
    (g a : ℕ → K) :
    IsLinearRecSolution c g a ↔ (Polynomial.aeval (advance (K := K)) (charPoly c)) a = g :=
  isLinearRecSolution_iff_aeval c g a

/-- CO-222. The advancement operator `A` acts by `(A f)(n) = f(n+1)`, so `p(A) f` at `n` is
`∑ᵢ pᵢ f(n+i)`. -/
@[kb "kellertrotter2017" "text (advancement operator), p. 212"]
theorem text_p212_advancement_operator {K : Type*} [Field K] (p : Polynomial K) (f : ℕ → K)
    (n : ℕ) :
    (Polynomial.aeval (advance (K := K)) p) f n =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * f (n + i) :=
  aeval_advance_apply p f n

/-- CO-223. If `0` is an `m`-fold root, `p(A) = A^m q(A)`, then solutions of `p(A) f = g` are
translates of solutions of `q(A) f = g`, so one may assume a nonzero constant term. -/
@[kb "kellertrotter2017" "text (9.3.3), p. 213"]
theorem text_p213_zero_root_translate {K : Type*} [Field K] (m : ℕ) (q : Polynomial K)
    (f h : ℕ → K) :
    (Polynomial.aeval (advance (K := K)) (Polynomial.X ^ m * q)) f =
        (Polynomial.aeval (advance (K := K)) q) ((advance (K := K) ^ m) f) ∧
      ((advance (K := K) ^ m) fun n => if m ≤ n then h (n - m) else 0) = h :=
  ⟨aeval_X_pow_mul_apply m q f, advance_pow_translate m h⟩

/-- CO-472. Algorithm for homogeneous constant-coefficient advancement equations over an
algebraically closed field: for monic `p` with `p(0) ≠ 0`, the roots `r i` of `p` with multiplicities
`m i` give the general solution `∑ c_{ij} nʲ rⁱⁿ`; each `nʲ rⁿ` with `j < m` is a solution when
`(A - r)^m ∣ p`. -/
@[kb "kellertrotter2017" "Example 9.9-9.13, pp. 214-217"]
theorem ex_9_9_to_9_13_homogeneous_algorithm {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (p : Polynomial K) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0) :
    ∃ (k : ℕ) (r : Fin k → K) (m : Fin k → ℕ),
      Function.Injective r ∧ (∀ i, r i ≠ 0) ∧ (∀ i, p.IsRoot (r i)) ∧
        ∀ f : ℕ → K, (Polynomial.aeval (advance (K := K)) p) f = 0 ↔
          ∃ c : (i : Fin k) → Fin (m i) → K,
            ∀ n : ℕ, f n = ∑ i : Fin k, ∑ j : Fin (m i), c i j * (n : K) ^ (j : ℕ) * r i ^ n :=
  solutions_alg_closed p hp h0

/-- CO-473. Nonhomogeneous equations: given a particular solution `f₀` of `p(A) f = g`, the general
solution is `f₀` plus the general solution of the homogeneous equation. -/
@[kb "kellertrotter2017" "Example 9.14-9.17, pp. 218-221"]
theorem ex_9_14_to_9_17_nonhomogeneous {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (p : Polynomial K) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0) (g f₀ : ℕ → K)
    (hf₀ : (Polynomial.aeval (advance (K := K)) p) f₀ = g) :
    ∃ (k : ℕ) (r : Fin k → K) (m : Fin k → ℕ),
      Function.Injective r ∧ (∀ i, r i ≠ 0) ∧
        ∀ f : ℕ → K, (Polynomial.aeval (advance (K := K)) p) f = g ↔
          ∃ c : (i : Fin k) → Fin (m i) → K,
            ∀ n : ℕ, f n = f₀ n + ∑ i : Fin k, ∑ j : Fin (m i), c i j * (n : K) ^ (j : ℕ) * r i ^ n :=
  nonhomogeneous_general_solution p hp h0 g f₀ hf₀

/-- CO-226. If `(A - r) f = 0` with `r ≠ 0` then `f(n) = f(0) rⁿ` (and conversely). -/
@[kb "kellertrotter2017" "Lemma 9.19, p. 224"]
theorem lem_9_19_first_order {K : Type*} [Field K] (r : K) (f : ℕ → K) :
    (Polynomial.aeval (advance (K := K)) (Polynomial.X - Polynomial.C r)) f = 0 ↔
      ∀ n : ℕ, f n = f 0 * r ^ n :=
  advance_sub_eq_zero_iff r f

/-- CO-227. Every solution of `p(A) f = g` is a fixed particular solution plus a solution of the
homogeneous equation `p(A) f = 0`. -/
@[kb "kellertrotter2017" "Lemma 9.20, p. 224"]
theorem lem_9_20_particular_plus_homogeneous {K : Type*} [Field K] (p : Polynomial K)
    (g f₀ : ℕ → K) (hf₀ : (Polynomial.aeval (advance (K := K)) p) f₀ = g) (f : ℕ → K) :
    (Polynomial.aeval (advance (K := K)) p) f = g ↔
      ∃ h : ℕ → K, (Polynomial.aeval (advance (K := K)) p) h = 0 ∧ f = f₀ + h :=
  solution_eq_particular_add_homogeneous p g f₀ hf₀ f

/-- CO-228. If `p(A) = (A - r₁) ⋯ (A - r_k)` with distinct roots, the solutions of `p(A) f = 0`
are exactly `f(n) = c₁ r₁ⁿ + ⋯ + c_k r_kⁿ`. -/
@[kb "kellertrotter2017" "Theorem 9.21, p. 224"]
theorem thm_9_21_distinct_roots {K : Type*} [Field K] {k : ℕ} (r : Fin k → K)
    (hr : Function.Injective r) (f : ℕ → K) :
    (Polynomial.aeval (advance (K := K)) (∏ i : Fin k, (Polynomial.X - Polynomial.C (r i)))) f = 0 ↔
      ∃ c : Fin k → K, ∀ n : ℕ, f n = ∑ i : Fin k, c i * r i ^ n :=
  solutions_distinct_roots r hr f

/-- CO-229. The solutions of `(A - r)^k f = 0` (with `r ≠ 0`) are exactly
`f(n) = (c₁ + c₂ n + ⋯ + c_k n^{k-1}) rⁿ`. -/
@[kb "kellertrotter2017" "Lemma 9.22, p. 225"]
theorem lem_9_22_repeated_root {K : Type*} [Field K] [CharZero K] (k : ℕ) (r : K) (hr : r ≠ 0)
    (f : ℕ → K) :
    (Polynomial.aeval (advance (K := K)) ((Polynomial.X - Polynomial.C r) ^ k)) f = 0 ↔
      ∃ c : Fin k → K, ∀ n : ℕ, f n = (∑ j : Fin k, c j * (n : K) ^ (j : ℕ)) * r ^ n :=
  solutions_repeated_root k r hr f

/-- CO-230. For `p(A) = ∏ (A - rᵢ)^{mᵢ}` with distinct nonzero roots, the solutions of `p(A) f = 0`
are the sums of terms `c_{ij} nʲ rᵢⁿ`, one family per root with multiplicity. -/
@[kb "kellertrotter2017" "text (9.5.4), p. 226"]
theorem text_p226_general_solution {K : Type*} [Field K] [CharZero K] {k : ℕ} (r : Fin k → K)
    (m : Fin k → ℕ) (hr : Function.Injective r) (hr0 : ∀ i, r i ≠ 0) (f : ℕ → K) :
    (Polynomial.aeval (advance (K := K))
        (∏ i : Fin k, (Polynomial.X - Polynomial.C (r i)) ^ m i)) f = 0 ↔
      ∃ c : (i : Fin k) → Fin (m i) → K,
        ∀ n : ℕ, f n = ∑ i : Fin k, ∑ j : Fin (m i), c i j * (n : K) ^ (j : ℕ) * r i ^ n :=
  solutions_general r m hr hr0 f

/-- CO-474. Solving linear recurrences with generating functions: multiplying the series of `a` by
the (reversed) characteristic polynomial `q` gives a polynomial of degree `< k`, and conversely; for
instance `(1 + x - 6x²)(∑ (6/5·2ⁿ - 1/5·(-3)ⁿ) xⁿ) = 1 + 4x`. -/
@[kb "kellertrotter2017" "Example 9.24-9.25, pp. 226-227"]
theorem ex_9_24_9_25_generating_function_method :
    (∀ {R : Type} [CommRing R] (k : ℕ) (q : Polynomial R), q.natDegree ≤ k → ∀ a : ℕ → R,
      (∀ n, k ≤ n → ∑ i ∈ Finset.range (k + 1), q.coeff i * a (n - i) = 0) →
        ∃ P : Polynomial R, P.degree < k ∧ (q : PowerSeries R) * PowerSeries.mk a = P) ∧
    (∀ {R : Type} [CommRing R] (k : ℕ) (q P : Polynomial R) (a : ℕ → R), P.degree < k →
      (q : PowerSeries R) * PowerSeries.mk a = P →
        ∀ n, k ≤ n → ∑ i ∈ Finset.range (n + 1), q.coeff i * a (n - i) = 0) ∧
    ((1 + PowerSeries.X - 6 * PowerSeries.X ^ 2 : PowerSeries ℚ) *
        PowerSeries.mk (fun n : ℕ => 6 / 5 * 2 ^ n - 1 / 5 * (-3) ^ n) = 1 + 4 * PowerSeries.X) :=
  ⟨fun k q hq a ha => genfun_mul_reversed_isPolynomial k q hq a ha,
    fun k q P a hP h => recurrence_of_genfun_mul_isPolynomial k q P a hP h, genfun_example⟩

/-- CO-129. Rooted unlabeled binary ordered trees (RUBOTs, every vertex has `0` or `2` children)
with `n` leaves: a tree has one more leaf than internal vertices, and the number of RUBOTs with
`n ≥ 1` leaves is the Catalan number `C(n-1)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) rooted binary ordered tree, p. 229"]
theorem def_p229_rubot :
    (∀ t : BinaryTree Unit, t.numLeaves = t.numNodes + 1) ∧
      ∀ n : ℕ, 1 ≤ n → {t : BinaryTree Unit | t.numLeaves = n}.ncard = catalan (n - 1) :=
  ⟨binaryTree_numLeaves_eq, ncard_binaryTree_numLeaves⟩

/-- CO-207. The numbers `c_n` of RUBOTs by leaf count satisfy `c_n = ∑_{k=1}^{n-1} c_k c_{n-k}`, and
their generating function `C(x)` satisfies `C = x + C²`. -/
@[kb "kellertrotter2017" "text (RUBOT recurrence), p. 229"]
theorem text_p229_rubot_recurrence :
    (∀ n : ℕ, 2 ≤ n → rubotCount n = ∑ k ∈ Finset.Ico 1 n, rubotCount k * rubotCount (n - k)) ∧
      rubotSeries = PowerSeries.X + rubotSeries ^ 2 :=
  ⟨rubotCount_recurrence, rubotSeries_eq_X_add_sq⟩

/-- CO-042. `C(1/2, k) = (-1)^{k-1} C(2k-2, k-1) / (k 2^{2k-1})` for `k ≥ 1`. -/
@[kb "kellertrotter2017" "Lemma 9.27, p. 231"]
theorem lem_9_27_choose_half (k : ℕ) (hk : 1 ≤ k) :
    Ring.choose (1 / 2 : ℚ) k =
      (-1) ^ (k - 1) * ((2 * k - 2).choose (k - 1) : ℚ) / (k * 2 ^ (2 * k - 1)) :=
  choose_half k hk

/-- CO-208. The generating function of RUBOTs by leaves is `C(x) = (1 - √(1-4x))/2`: the series
`1 - 2C` has constant term `1` and square `1 - 4x`; hence `c_{n+1}` is the Catalan number
`C(2n, n)/(n+1)`. -/
@[kb "kellertrotter2017" "Theorem 9.28, p. 231"]
theorem thm_9_28_rubot_gf :
    (PowerSeries.constantCoeff (1 - 2 * rubotSeries) = 1 ∧
      (1 - 2 * rubotSeries) ^ 2 = 1 - 4 * PowerSeries.X) ∧
    ∀ n : ℕ, (rubotCount (n + 1) : ℚ) = n.centralBinom / (n + 1) :=
  ⟨rubotSeries_sqrt, rubotCount_eq_centralBinom_div⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch09b
