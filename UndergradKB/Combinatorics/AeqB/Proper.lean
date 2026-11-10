import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import UndergradKB.Combinatorics.AeqB.WZ
import UndergradKB.Common.Attr

/-!
# Proper hypergeometric terms (Petkovsek-Wilf-Zeilberger, "A = B", Chapter 4)

Doubly hypergeometric functions, proper hypergeometric terms (eq. 4.4.1), the shift-ratio of a
factorial of a linear form (eq. 4.4.4/4.4.5), and the passage from a `k`-free recurrence of the
summand to a recurrence of the sum.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Finset

/-! ### Doubly hypergeometric functions -/

/-- CO-374. `F(n,k)` is doubly hypergeometric when both `F(n+1,k)/F(n,k)` and `F(n,k+1)/F(n,k)`
are rational functions of `n` and `k` (stated multiplicatively with polynomial numerators and
denominators, as in `IsHypergeometric₂`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) doubly hypergeometric, p. 68"]
def IsDoublyHypergeometric {K : Type*} [CommRing K] (F : ℤ → ℤ → K) : Prop :=
  IsHypergeometric₂ F

/-! ### Proper hypergeometric terms -/

section Proper

variable (K : Type*) [Field K]

/-- The data of a proper hypergeometric term (eq. 4.4.1): a polynomial `P(n,k)`, integer coefficient
vectors `(a_i, b_i, c_i)` for the numerator factorials and `(u_j, v_j, w_j)` for the denominator
factorials, and the base `x` of `x^k`. -/
structure ProperHypergeometricData where
  /-- number of factorials in the numerator -/
  uu : ℕ
  /-- number of factorials in the denominator -/
  vv : ℕ
  /-- the polynomial `P(n,k)` -/
  P : MvPolynomial (Fin 2) K
  a : Fin uu → ℤ
  b : Fin uu → ℤ
  c : Fin uu → ℤ
  u : Fin vv → ℤ
  v : Fin vv → ℤ
  w : Fin vv → ℤ
  /-- the base of `x^k` -/
  x : K

variable {K}

/-- `m!` for an integer `m` (only meaningful for `m ≥ 0`). -/
noncomputable def intFact (m : ℤ) : K := ((m.toNat).factorial : K)

/-- `1/m!` for an integer `m`, which is `0` for negative `m` (the book's convention). -/
noncomputable def intInvFact (m : ℤ) : K := if 0 ≤ m then ((m.toNat).factorial : K)⁻¹ else 0

namespace ProperHypergeometricData

/-- CO-375. The value at `(n, k)` of the term
`P(n,k) ∏ (a_i n + b_i k + c_i)! / ∏ (u_j n + v_j k + w_j)! · x^k`, with `1/m! = 0` for `m < 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (4.4.1), p. 74"]
noncomputable def eval (D : ProperHypergeometricData K) (n k : ℤ) : K :=
  D.P.eval ![(n : K), (k : K)] * (∏ i, intFact (D.a i * n + D.b i * k + D.c i)) *
    (∏ j, intInvFact (D.u j * n + D.v j * k + D.w j)) * D.x ^ k

/-- The term is well defined at `(n, k)` when no numerator factorial has a negative argument. -/
def WellDefinedAt (D : ProperHypergeometricData K) (n k : ℤ) : Prop :=
  ∀ i, 0 ≤ D.a i * n + D.b i * k + D.c i

/-- If the term is well defined and some denominator factorial has a negative argument, the value
is `0` (as in the book). -/
theorem eval_eq_zero_of_neg (D : ProperHypergeometricData K) (n k : ℤ) (j : Fin D.vv)
    (hj : D.u j * n + D.v j * k + D.w j < 0) : D.eval n k = 0 := by
  have : intInvFact (K := K) (D.u j * n + D.v j * k + D.w j) = 0 := by
    simp [intInvFact, not_le.2 hj]
  have h2 : (∏ j, intInvFact (K := K) (D.u j * n + D.v j * k + D.w j)) = 0 :=
    prod_eq_zero (Finset.mem_univ j) this
  simp [eval, h2]

end ProperHypergeometricData

/-- The book's example `C(n,k) 2^k = n! / (k! (n-k)!) · 2^k` is proper hypergeometric. -/
noncomputable def binomTwoPowData : ProperHypergeometricData ℚ where
  uu := 1
  vv := 2
  P := 1
  a := ![1]
  b := ![0]
  c := ![0]
  u := ![0, 1]
  v := ![1, -1]
  w := ![0, 0]
  x := 2

/-- `binomTwoPowData` evaluates to `C(n,k) 2^k` for `0 ≤ k ≤ n`. -/
theorem binomTwoPowData_eval (n k : ℕ) (hk : k ≤ n) :
    binomTwoPowData.eval n k = (n.choose k : ℚ) * 2 ^ k := by
  have h3 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h4 : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
  have e : (((n : ℤ) + -(k : ℤ)).toNat) = n - k := by omega
  show (MvPolynomial.eval ![(((n : ℤ) : ℚ)), (((k : ℤ) : ℚ))] (1 : MvPolynomial (Fin 2) ℚ)) *
      (∏ i : Fin 1, intFact (![(1 : ℤ)] i * n + ![(0 : ℤ)] i * k + ![(0 : ℤ)] i)) *
      (∏ j : Fin 2, intInvFact (![(0 : ℤ), 1] j * n + ![(1 : ℤ), -1] j * k + ![(0 : ℤ), 0] j)) *
        (2 : ℚ) ^ (k : ℤ) = _
  simp [Fin.prod_univ_two, intFact, intInvFact, e, hk, Nat.cast_choose ℚ hk]
  field_simp

end Proper

/-! ### Shift ratio of a factorial of a linear form -/

/-- The falling factorial polynomial `ff(x, y) = ∏_{j=0}^{x-1} (y - j)` of the proof of the
Fundamental Theorem. -/
def ffPoly (x : ℕ) (y : ℤ) : ℤ := ∏ j ∈ range x, (y - j)

/-- The rising factorial polynomial `rf(x, y) = ∏_{j=1}^{x} (y + j)`. -/
def rfPoly (x : ℕ) (y : ℤ) : ℤ := ∏ j ∈ range x, (y + (j + 1))

theorem factorial_sub_mul_ffPoly (N s : ℕ) (h : s ≤ N) :
    (((N - s).factorial : ℕ) : ℤ) * ffPoly s N = (N.factorial : ℕ) := by
  induction s with
  | zero => simp [ffPoly]
  | succ s ih =>
    have ih := ih (by omega)
    have e : N - s = (N - (s + 1)) + 1 := by omega
    have e2 : ((N - s : ℕ) : ℤ) = (N : ℤ) - s := by omega
    rw [ffPoly, prod_range_succ, ← ffPoly]
    rw [e, Nat.factorial_succ] at ih
    push_cast at ih ⊢
    have e3 : ((N - (s + 1) : ℕ) : ℤ) + 1 = (N : ℤ) - s := by omega
    rw [e3] at ih
    linear_combination ih

theorem factorial_add_eq_mul_rfPoly (N t : ℕ) :
    (((N + t).factorial : ℕ) : ℤ) = (N.factorial : ℕ) * rfPoly t N := by
  induction t with
  | zero => simp [rfPoly]
  | succ t ih =>
    rw [rfPoly, prod_range_succ, ← rfPoly, ← add_assoc, Nat.factorial_succ]
    push_cast at ih ⊢
    rw [ih]
    ring

/-- CO-390 (case `aj + bi ≥ 0`, eq. 4.4.4/4.4.5). For `F(n,k) = (an+bk+c)!`, the ratio
`F(n-j, k-i) / F(n,k)` is the reciprocal of the falling factorial polynomial
`ff(aj+bi, an+bk+c)`: stated without division as
`F(n-j,k-i) · ff(aj+bi, an+bk+c) = F(n,k)` (when both arguments are nonnegative). -/
@[kb "petkovsekwilfzeilberger1996" "Equation (4.4.4), p. 76"]
theorem shift_factorial_of_nonneg (a b c n k i j : ℤ) (hs : 0 ≤ a * j + b * i)
    (h : 0 ≤ a * (n - j) + b * (k - i) + c) :
    ((((a * (n - j) + b * (k - i) + c).toNat).factorial : ℕ) : ℤ) *
        ffPoly (a * j + b * i).toNat (a * n + b * k + c) =
      (((a * n + b * k + c).toNat).factorial : ℕ) := by
  have hrw : a * (n - j) + b * (k - i) + c = (a * n + b * k + c) - (a * j + b * i) := by ring
  rw [hrw] at h ⊢
  generalize a * n + b * k + c = N at *
  generalize a * j + b * i = s at *
  have h1 := factorial_sub_mul_ffPoly N.toNat s.toNat (by omega)
  have e1 : ((N.toNat : ℕ) : ℤ) = N := by omega
  have e2 : N.toNat - s.toNat = (N - s).toNat := by omega
  rw [e2, e1] at h1
  exact h1

/-- CO-390 (case `aj + bi < 0`, eq. 4.4.4/4.4.5). The ratio `F(n-j,k-i) / F(n,k)` is the rising
factorial polynomial `rf(|aj+bi|, an+bk+c)`: `F(n-j,k-i) = F(n,k) · rf(|aj+bi|, an+bk+c)`
(when the argument of `F(n,k)` is nonnegative). -/
@[kb "petkovsekwilfzeilberger1996" "Equation (4.4.4), p. 76"]
theorem shift_factorial_of_neg (a b c n k i j : ℤ) (hs : a * j + b * i < 0)
    (h : 0 ≤ a * n + b * k + c) :
    ((((a * (n - j) + b * (k - i) + c).toNat).factorial : ℕ) : ℤ) =
      (((a * n + b * k + c).toNat).factorial : ℕ) *
        rfPoly (a * j + b * i).natAbs (a * n + b * k + c) := by
  have hrw : a * (n - j) + b * (k - i) + c = (a * n + b * k + c) - (a * j + b * i) := by ring
  rw [hrw]
  generalize a * n + b * k + c = N at *
  generalize a * j + b * i = s at *
  have h1 := factorial_add_eq_mul_rfPoly N.toNat s.natAbs
  have e1 : ((N.toNat : ℕ) : ℤ) = N := by omega
  have e2 : N.toNat + s.natAbs = (N - s).toNat := by omega
  rw [e2, e1] at h1
  exact h1

/-! ### From a `k`-free recurrence of the summand to a recurrence of the sum -/

/-- CO-387. If the summand satisfies a recurrence `∑_i c_i(n) F(n+i, k) = 0` for all integers
`n, k`, whose coefficients `c_i(n)` do not depend on `k`, and each `F(n, ·)` has finite support,
then the sum `f(n) = ∑_k F(n,k)` satisfies the same recurrence `∑_i c_i(n) f(n+i) = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 67"]
theorem sum_recurrence {K : Type*} [CommRing K] (F : ℤ → ℤ → K) (r : ℕ) (c : ℕ → ℤ → K)
    (hfin : ∀ n, (Function.support (F n)).Finite)
    (hrec : ∀ n k, ∑ i ∈ range (r + 1), c i n * F (n + i) k = 0) (n : ℤ) :
    ∑ i ∈ range (r + 1), c i n * ∑ᶠ k, F (n + i) k = 0 := by
  classical
  let T : Finset ℤ := (range (r + 1)).biUnion fun i => (hfin (n + i)).toFinset
  have hT : ∀ i ∈ range (r + 1), ∑ᶠ k, F (n + i) k = ∑ k ∈ T, F (n + i) k := by
    intro i hi
    refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset, T]
    exact ⟨i, hi, hk⟩
  rw [sum_congr rfl fun i hi => by rw [hT i hi]]
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_eq_zero fun k _ => hrec n k

end UndergradKB.Combinatorics.AeqB
