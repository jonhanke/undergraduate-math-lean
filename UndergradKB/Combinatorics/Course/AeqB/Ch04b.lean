import Mathlib.Algebra.Polynomial.Eval.Defs
import UndergradKB.Combinatorics.AeqB.Identities
import UndergradKB.Combinatorics.AeqB.Database
import UndergradKB.Combinatorics.AeqB.Proper
import UndergradKB.Combinatorics.AeqB.Celine
import UndergradKB.Combinatorics.AeqB.CelineMulti
import UndergradKB.Combinatorics.AeqB.QFundamental
import UndergradKB.Combinatorics.AeqB.RecurrenceCheck
import UndergradKB.Combinatorics.AeqB.Gosper
import UndergradKB.Common.Attr

/-!
# A=B, Chapter 4: course wrappers of results proved in this library (wave 3)
-/

open Finset Polynomial Filter
open UndergradKB.Combinatorics.AeqB

namespace UndergradKB.Combinatorics.Course.AeqB.Ch04b

/-- CO-047. `∑_k k C(n,k) = n 2^{n-1}`, derived by Sister Celine's method. -/
@[kb "petkovsekwilfzeilberger1996" "Example 4.1.1, p. 65"]
theorem ex_4_1_1_sum_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * n.choose k = n * 2 ^ (n - 1) :=
  sum_mul_choose n

/-- CO-387. A recurrence for the summand with coefficients free of `k` (and finitely supported
in `k`) sums to a recurrence for `f n = ∑_k F n k`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 67"]
theorem text_p67_sum_recurrence {K : Type*} [CommRing K] (F : ℤ → ℤ → K) (r : ℕ)
    (c : ℕ → ℤ → K) (hfin : ∀ n, (Function.support (F n)).Finite)
    (hrec : ∀ n k, ∑ i ∈ range (r + 1), c i n * F (n + i) k = 0) (n : ℤ) :
    ∑ i ∈ range (r + 1), c i n * ∑ᶠ k, F (n + i) k = 0 :=
  sum_recurrence F r c hfin hrec n

/-- CO-388. Soundness of Sister Celine's method: a kernel element of the coefficient-matching
linear system gives a `k`-free recurrence for a proper hypergeometric term, and the system has a
nontrivial kernel once the degree bound is below the number of unknowns. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) Sister Celine's algorithm, p. 69"]
theorem def_p69_celine_algorithm {K : Type*} [Field K] [CharZero K]
    (D : ProperHypergeometricData K) (hx : D.x ≠ 0) {I J : ℕ} :
    (∀ (b : Fin (I + 1) × Fin (J + 1) → K[X]), b ∈ LinearMap.ker (Celine.celineMap D I J) →
      ∀ (n k : ℤ), D.eval n k ≠ 0 →
      (∀ i ≤ I, ∀ j ≤ J, D.WellDefinedAt (n - j) (k - i)) →
      ∑ p : Fin (I + 1) × Fin (J + 1), (b p * C (D.x ^ (p.1 : ℕ))).eval (n : K) *
        D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0) ∧
    (Celine.degBound D I J + 1 < (I + 1) * (J + 1) →
      LinearMap.ker (Celine.celineMap D I J) ≠ ⊥) :=
  ⟨fun b hb n k hF hwd => Celine.celine_sound D hx b hb n k hF hwd,
    fun h => Celine.celineMap_ker_ne_bot D h⟩

/-- CO-234. The Laguerre polynomials `L_n(x) = ∑ (-1)^k C(n,k) x^k / k!` satisfy
`n L_n + (x+1-2n) L_{n-1} + (n-1) L_{n-2} = 0` (equivalently, in shifted form). -/
@[kb "petkovsekwilfzeilberger1996" "Example 4.3.2, p. 71"]
theorem ex_4_3_2_laguerre_recurrence :
    (∀ (n : ℕ) (x : ℚ), ((n : ℚ) + 2) * laguerre (n + 2) x + (x - 2 * n - 3) * laguerre (n + 1) x
      + ((n : ℚ) + 1) * laguerre n x = 0) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ x : ℚ, (n : ℚ) * laguerre n x + (x + 1 - 2 * n) * laguerre (n - 1) x
      + ((n : ℚ) - 1) * laguerre (n - 2) x = 0) :=
  ⟨laguerre_recurrence, fun n hn x => laguerre_recurrence' n hn x⟩

/-- CO-048. Reed-Dawson identity: `∑_k C(n,k) C(2k,k) (-2)^{n-k}` is `0` for odd `n` and
`C(n,n/2)` for even `n`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 4.3.3, p. 73"]
theorem ex_4_3_3_reed_dawson (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℤ) * ((2 * k).choose k : ℤ) * (-2) ^ (n - k)
      = if 2 ∣ n then (n.choose (n / 2) : ℤ) else 0 :=
  reed_dawson n

/-- CO-389. The Fundamental Theorem: a proper hypergeometric term satisfies a nontrivial
`k`-free recurrence with polynomial coefficients of the explicit orders `(I*, J*)`; also for any
orders `(I, J)` whose degree bound is below the number of unknowns. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.4.1, p. 75"]
theorem thm_4_4_1_fundamental_theorem {K : Type*} [Field K] [CharZero K]
    (D : ProperHypergeometricData K) (hx : D.x ≠ 0) :
    ∃ a : Fin (Celine.iStar D + 1) × Fin (Celine.jStar D + 1) → K[X], a ≠ 0 ∧
      ∀ n k : ℤ, D.eval n k ≠ 0 →
        (∀ i ≤ Celine.iStar D, ∀ j ≤ Celine.jStar D, D.WellDefinedAt (n - j) (k - i)) →
        ∑ p : Fin (Celine.iStar D + 1) × Fin (Celine.jStar D + 1), (a p).eval (n : K) *
          D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 :=
  Celine.fundamental_theorem D hx

/-- CO-390. Shift of a factorial of a linear form: `F(n-j,k-i)/F(n,k)` for `F = (an+bk+c)!` is a
falling-factorial polynomial reciprocal when `aj + bi ≥ 0` and a rising-factorial polynomial when
`aj + bi < 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (4.4.4), p. 76"]
theorem eq_4_4_4_shift_factorial :
    (∀ (a b c n k i j : ℤ), 0 ≤ a * j + b * i → 0 ≤ a * (n - j) + b * (k - i) + c →
      ((((a * (n - j) + b * (k - i) + c).toNat).factorial : ℕ) : ℤ) *
          ffPoly (a * j + b * i).toNat (a * n + b * k + c) =
        (((a * n + b * k + c).toNat).factorial : ℕ)) ∧
    (∀ (a b c n k i j : ℤ), a * j + b * i < 0 → 0 ≤ a * n + b * k + c →
      ((((a * (n - j) + b * (k - i) + c).toNat).factorial : ℕ) : ℤ) =
        (((a * n + b * k + c).toNat).factorial : ℕ) *
          rfPoly (a * j + b * i).natAbs (a * n + b * k + c)) :=
  ⟨fun a b c n k i j hs h => shift_factorial_of_nonneg a b c n k i j hs h,
    fun a b c n k i j hs h => shift_factorial_of_neg a b c n k i j hs h⟩

/-- CO-391. Finite verification of an identity: two solutions of a polynomial-coefficient
recurrence agree everywhere once they agree on a finite initial segment (forward form with no
bad roots, backward form, and the existence of the computable check bound `N`). -/
@[kb "petkovsekwilfzeilberger1996" "text, pp. 79-80"]
theorem text_p79_finite_check {K : Type*} [Field K] [CharZero K] :
    (∀ (J m : ℕ) (a : ℕ → K[X]), (∀ k : ℕ, m ≤ k → ¬ (a J).IsRoot (k : K)) →
      ∀ f g : ℕ → K,
      (∀ n, m ≤ n → ∑ j ∈ range (J + 1), (a j).eval (n : K) * f (n + j) = 0) →
      (∀ n, m ≤ n → ∑ j ∈ range (J + 1), (a j).eval (n : K) * g (n + j) = 0) →
      (∀ i, i < J → f (m + i) = g (m + i)) → ∀ n, m ≤ n → f n = g n) ∧
    (∀ (J N : ℕ) (b : ℕ → K[X]), (∀ k : ℕ, N < k → ¬ (b 0).IsRoot (k : K)) →
      ∀ f g : ℕ → K,
      (∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * f (n - i) = 0) →
      (∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * g (n - i) = 0) →
      (∀ n, n ≤ J + N → f n = g n) → ∀ n, f n = g n) ∧
    (∀ (J : ℕ) (b : ℕ → K[X]), b 0 ≠ 0 →
      ∃ N : ℕ, ∀ f g : ℕ → K,
        (∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * f (n - i) = 0) →
        (∀ n, J ≤ n → ∑ i ∈ range (J + 1), (b i).eval (n : K) * g (n - i) = 0) →
        (∀ n, n ≤ J + N → f n = g n) → ∀ n, f n = g n) :=
  ⟨fun J m a hroot f g hf hg hinit => eq_of_polynomial_recurrence J m a hroot f g hf hg hinit,
    fun J N b hroot f g hf hg hinit => eq_of_backward_recurrence J N b hroot f g hf hg hinit,
    fun J b hb => exists_finite_check_bound J b hb⟩

/-- CO-393. (partial) Multivariate Fundamental Theorem: a proper hypergeometric term in `r ≥ 1`
summation variables satisfies a nontrivial `k`-free recurrence with polynomial coefficients of
explicit order bounds `(multiI, multiJ)`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.5.1, p. 81"]
theorem thm_4_5_1_multivariate_fundamental_theorem {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (D : CelineMulti.ProperHypergeometricDataMulti K r) (hr : 0 < r) (hz : ∀ t, D.z t ≠ 0) :
    ∃ α : (Fin r → Fin (CelineMulti.multiI D + 1)) × Fin (CelineMulti.multiJ D + 1) →
        Polynomial K, α ≠ 0 ∧
      ∀ (n : ℤ) (k : Fin r → ℤ), D.eval n k ≠ 0 →
        (∀ i : Fin r → ℕ, (∀ t, i t ≤ CelineMulti.multiI D) → ∀ j ≤ CelineMulti.multiJ D,
          D.WellDefinedAt (n - j) (fun t => k t - (i t : ℤ))) →
        ∑ p : (Fin r → Fin (CelineMulti.multiI D + 1)) × Fin (CelineMulti.multiJ D + 1),
          (α p).eval (n : K) *
            D.eval (n - (p.2 : ℕ)) (fun t => k t - ((p.1 t : ℕ) : ℤ)) = 0 :=
  CelineMulti.exists_kfree_recurrence_multi D hr hz

/-- CO-394. The `q`-version of the Fundamental Theorem: a `q`-proper hypergeometric term satisfies
a nontrivial `k`-free recurrence with polynomial coefficients in `q^n`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.5.2, p. 81"]
theorem thm_4_5_2_q_fundamental_theorem {K : Type*} [Field K]
    (D : QAnalogue.QProperData K) (q : K) (hq : q ≠ 0) (hξ : D.ξ ≠ 0) :
    ∃ I : ℕ, ∃ α : Fin (I + 1) × Fin (QFundamental.qJStar D + 1) → K[X], α ≠ 0 ∧
      ∀ n k : ℤ, D.eval q n k ≠ 0 →
        (∀ i ≤ I, ∀ j ≤ QFundamental.qJStar D, QFundamental.IsDefinedAt D q (n - j) (k - i)) →
        ∑ p : Fin (I + 1) × Fin (QFundamental.qJStar D + 1), (α p).eval (q ^ n) *
          D.eval q (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 :=
  QFundamental.q_fundamental_theorem D q hq hξ

/-- CO-396. Writing `z_n = y(n) t_n`, the equation `z_{n+1} - z_n = t_n` becomes a rational-function
equation for `y`; a hypergeometric `t` with `q t(n+1) = p t(n)` is Gosper-summable iff the
polynomial equation `p u(n+1) v(n) - q u(n) v(n+1) = q v(n) v(n+1)` has a solution with `v ≠ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 85"]
theorem text_p85_gosper_reduction {K : Type*} [Field K] [CharZero K] {t : ℕ → K} {p q : K[X]}
    (ht : IsHypergeometric t) (hq : q ≠ 0)
    (hrel : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * t (n + 1) = p.eval (n : K) * t n) :
    IsGosperSummable t ↔ ∃ u v : K[X], v ≠ 0 ∧
      p * u.comp (X + 1) * v - q * u * v.comp (X + 1) = q * v * v.comp (X + 1) :=
  isGosperSummable_iff ht hq hrel

/-- CO-397. Gosper's form: if `p b c = q a c(n+1)`, then `y = b(n-1) x / c` solves the reduced
equation exactly when `a x(n+1) - b(n-1) x = c`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 85-86"]
theorem text_p85_gosper_form_equiv {K : Type*} [Field K] [CharZero K] {a b c p q x : K[X]}
    (hq : q ≠ 0) (hc : c ≠ 0) (hform : p * b * c = q * a * c.comp (X + 1)) :
    p * (b.comp (X - 1) * x).comp (X + 1) * c - q * (b.comp (X - 1) * x) * c.comp (X + 1)
        = q * c * c.comp (X + 1) ↔
      a * x.comp (X + 1) - b.comp (X - 1) * x = c :=
  gosper_form_equiv hq hc hform

end UndergradKB.Combinatorics.Course.AeqB.Ch04b
