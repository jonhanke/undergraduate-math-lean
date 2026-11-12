import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import UndergradKB.Combinatorics.AeqB.Background
import UndergradKB.Combinatorics.AeqB.Database
import UndergradKB.Combinatorics.AeqB.Summation2
import UndergradKB.Combinatorics.AeqB.RecurrenceCheck
import UndergradKB.Combinatorics.AeqB.WZ
import UndergradKB.Combinatorics.AeqB.WZProof
import UndergradKB.Combinatorics.AeqB.Certificates
import UndergradKB.Common.Attr

/-!
# A=B, Chapter 2: course wrappers of results proved in this library (wave 3)
-/

open Finset
open scoped Nat
open UndergradKB.Combinatorics.AeqB

namespace UndergradKB.Combinatorics.Course.AeqB.Ch02b

/-- CO-233. The Franel numbers `f n = ∑_k C(n,k)^3` satisfy the three-term recurrence
`8(n+1)^2 f(n) + (7n^2+21n+16) f(n+1) - (n+2)^2 f(n+2) = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 31"]
theorem text_p31_franel_recurrence (n : ℕ) :
    8 * ((n : ℚ) + 1) ^ 2 * franel n + (7 * (n : ℚ) ^ 2 + 21 * n + 16) * franel (n + 1)
      - ((n : ℚ) + 2) ^ 2 * franel (n + 2) = 0 :=
  franel_recurrence n

/-- CO-351. Smith's determinant: `det (gcd (i,j)) = φ(1) φ(2) ⋯ φ(n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 32"]
theorem text_p32_det_gcd_matrix (n : ℕ) :
    (gcdMatrix n).det = ∏ m ∈ Icc 1 n, ((Nat.totient m : ℕ) : ℤ) :=
  UndergradKB.Combinatorics.det_gcdMatrix n

/-- CO-211. The tree-function identity: `exp (∑ m^{m-1} t^m / m!) = 1 + ∑ (n+1)^{n-1} t^n / n!`,
stated as the substitution of the tree series into the exponential series. -/
@[kb "petkovsekwilfzeilberger1996" "Equation 2.2.3, p. 33"]
theorem eq_2_2_3_exp_treeSeries : (PowerSeries.exp ℚ).subst treeSeries = treeExpSeries :=
  exp_treeSeries

/-- CO-044. The alternating cube sum `∑_s (-1)^s C(2m,s)^3 = (-1)^m (3m)!/(m!)^3`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation 2.2.4, p. 33"]
theorem eq_2_2_4_alternating_choose_cube (m : ℕ) :
    ∑ s ∈ Finset.range (2 * m + 1), (-1 : ℚ) ^ s * ((2 * m).choose s : ℚ) ^ 3
      = (-1 : ℚ) ^ m * ((3 * m) ! : ℚ) / ((m !) ^ 3 : ℚ) :=
  alternating_choose_cube m

/-- CO-386. Zeilberger's principle: if a summand has a recurrence in `n` with `k`-free
coefficients, the claimed answer satisfies the same recurrence, and the first values agree, then
the sum equals the answer for all `n ≥ n₀`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 34"]
theorem text_p34_zeilberger_principle {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (J n0 : ℕ) (a : ℕ → ℕ → R)
    (hlead : ∀ n, n0 ≤ n → a J n ≠ 0) (s : ℕ → Finset ι) (F : ℕ → ι → R) (answer : ℕ → R)
    (hsum : ∀ n, n0 ≤ n →
      ∑ j ∈ range (J + 1), a j n * ∑ k ∈ s (n + j), F (n + j) k = 0)
    (hans : ∀ n, n0 ≤ n → ∑ j ∈ range (J + 1), a j n * answer (n + j) = 0)
    (hinit : ∀ i, i < J → ∑ k ∈ s (n0 + i), F (n0 + i) k = answer (n0 + i)) :
    ∀ n, n0 ≤ n → ∑ k ∈ s n, F n k = answer n :=
  zeilberger_principle J n0 a hlead s F answer hsum hans hinit

/-- CO-439. The WZ proof algorithm: if `R` is a certificate (`F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)`
with `G = R F`), the summand has finite support in `k`, and the sum equals `1` at `n₀`, then it
equals `1` for all `n`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 36"]
theorem text_p36_wz_proof {K : Type*} [CommRing K] (F R : ℤ → ℤ → K)
    (hWZ : ∀ n k, F (n + 1) k - F n k = R n (k + 1) * F n (k + 1) - R n k * F n k)
    (hF : ∀ n, (Function.support (F n)).Finite)
    (hG : ∀ n, (Function.support fun k => R n k * F n k).Finite)
    (n₀ : ℤ) (h₀ : ∑ᶠ k, F n₀ k = 1) (n : ℤ) : ∑ᶠ k, F n k = 1 :=
  wz_proof F R hWZ hF hG n₀ h₀ n

/-- CO-440. If `F, G` satisfy the WZ equation and `F n ·`, `G n ·` have finite support, then
`∑_k F n k` does not depend on `n`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 36"]
theorem text_p36_wz_finsum_const {E : Type*} [AddCommGroup E] {F G : ℤ → ℤ → E}
    (h : ∀ n k : ℤ, F (n + 1) k - F n k = G n (k + 1) - G n k)
    (hF : ∀ n, (Function.support (F n)).Finite)
    (hG : ∀ n, (Function.support (G n)).Finite) (n m : ℤ) :
    ∑ᶠ k, F n k = ∑ᶠ k, F m k :=
  WZEq.finsum_const h hF hG n m

/-- CO-441. Routine verification: a recurrence `∑ a_{ij} F(n-j,k-i) = 0` for `F` with
shift ratios `ρ` holds iff the rational-function identity `∑ a_{ij} ρ_{ij} = 0` holds
(when `F n k ≠ 0`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) routinely verifiable, p. 37"]
theorem def_p37_routinely_verifiable {L : Type*} [Field L] (s : Finset (ℕ × ℕ))
    (a : ℕ → ℕ → L) (F : ℤ → ℤ → L) (n k : ℤ) (ρ : ℕ → ℕ → L)
    (hρ : ∀ p ∈ s, F (n - p.2) (k - p.1) = ρ p.1 p.2 * F n k) (h0 : F n k ≠ 0) :
    ∑ p ∈ s, a p.1 p.2 * F (n - p.2) (k - p.1) = 0 ↔ ∑ p ∈ s, a p.1 p.2 * ρ p.1 p.2 = 0 :=
  recurrence_iff_ratio_identity s a F n k ρ hρ h0

/-- CO-442. The WZ certificate `R(n,k) = (k-1)/n` for the summand
`(n-i)!(n-j)!(i-1)!(j-1)!/((n-1)!(k-1)!(n-i-j+k)!(i-k)!(j-k)!)` (whose sum over `k` is `1`). -/
@[kb "petkovsekwilfzeilberger1996" "Example 2.3.2, p. 38"]
theorem ex_2_3_2_mon_cert (i j n k : ℤ) (_hi : 1 ≤ i) (_hj : 1 ≤ j) (hni : i ≤ n) (hnj : j ≤ n)
    (hk : 1 ≤ k) (h1 : i + j ≤ n + k) (h2 : k + 1 ≤ i) (h3 : k + 1 ≤ j) :
    monF i j (n + 1) k - monF i j n k
      = monR n (k + 1) * monF i j n (k + 1) - monR n k * monF i j n k :=
  mon_cert i j n k _hi _hj hni hnj hk h1 h2 h3

end UndergradKB.Combinatorics.Course.AeqB.Ch02b
