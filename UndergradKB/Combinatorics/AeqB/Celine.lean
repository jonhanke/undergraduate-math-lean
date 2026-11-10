import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import UndergradKB.Combinatorics.AeqB.Proper
import UndergradKB.Common.Attr

/-!
# Sister Celine's method and the Fundamental Theorem (Petkovsek–Wilf–Zeilberger, "A = B", §4.3–4.4)

For a proper hypergeometric term
`F(n,k) = P(n,k) ∏ (a_s n + b_s k + c_s)! / ∏ (u_s n + v_s k + w_s)! · x^k`
(`ProperHypergeometricData`, eq. (4.4.1)) Sister Celine's method looks for a `k`-free recurrence
`∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n-j, k-i) = 0`.  Steps 3–4 of the method (divide by `F(n,k)`, reduce the
ratios of factorials, clear the common denominator (4.4.9)) turn the recurrence into the vanishing of a
polynomial in `k` with coefficients linear in the unknowns `a_{ij}(n)`:
`∑ a_{ij}(n) x^{-i} Q_{ij}(n,k) = 0`, where `Q_{ij} = ν_{ij} Δ / δ_{ij}` is the explicit polynomial
`celineQ`.  Step 5 (equating coefficients of powers of `k`) is the kernel of the `K[n]`-linear map
`celineMap`.

* `celine_sound` (correctness of the method): every kernel vector gives a recurrence that holds at every
  point where `F(n,k) ≠ 0` and all the values `F(n-j,k-i)` are well defined.
* `celineMap_ker_ne_bot` (the method succeeds): the kernel is nonzero as soon as the number of unknowns
  `(I+1)(J+1)` exceeds the number of equations, which grows only linearly in `I, J`.
* `fundamental_theorem` (Theorem 4.4.1), with the explicit orders `(I*, J*)` of (4.4.3).

The polynomials are elements of `K[n][k] = K[X][Y]` (`Polynomial (Polynomial K)`), evaluated with
`Polynomial.evalEval n k`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Finset

namespace Celine

/-! ### Linear algebra: more unknowns than equations -/

/-- If `m` polynomials over an integral domain `R` all have degree at most `d` and `d + 1 < m`, some
nontrivial `R`-linear combination of them vanishes (a homogeneous linear system with more unknowns
than equations has a nonzero solution). -/
theorem exists_ne_zero_sum_C_mul_eq_zero {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Q : ι → R[X]) (d : ℕ) (hQ : ∀ i, (Q i).natDegree ≤ d)
    (hcard : d + 1 < Fintype.card ι) :
    ∃ b : ι → R, b ≠ 0 ∧ ∑ i, C (b i) * Q i = 0 := by
  let e := Fintype.equivFin ι
  let M : Matrix ι ι R := fun r i => (Q i).coeff (e r)
  have hdet : M.det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero (e.symm ⟨Fintype.card ι - 1, by omega⟩) fun i => ?_
    simp only [M, Equiv.apply_symm_apply]
    exact coeff_eq_zero_of_natDegree_lt (by have := hQ i; omega)
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  ext m
  rw [finsetSum_coeff, coeff_zero]
  simp only [coeff_C_mul]
  by_cases hm : m < Fintype.card ι
  · have := congrFun hMv (e.symm ⟨m, hm⟩)
    simp only [Matrix.mulVec, dotProduct, M, Equiv.apply_symm_apply, Pi.zero_apply] at this
    rw [← this]
    exact sum_congr rfl fun i _ => mul_comm _ _
  · exact sum_eq_zero fun i _ => by
      rw [coeff_eq_zero_of_natDegree_lt (by have := hQ i; omega), mul_zero]

/-! ### Falling and rising factorials of integers, in `K` -/

variable {K : Type*} [Field K]

/-- `ff(A, y) = y (y-1) ⋯ (y-A+1)` (value in `K`). -/
def ffVal (A : ℕ) (y : K) : K := ∏ t ∈ range A, (y - t)

/-- `rf(U, y) = (y+1) (y+2) ⋯ (y+U)` (value in `K`). -/
def rfVal (U : ℕ) (y : K) : K := ∏ t ∈ range U, (y + (t + 1))

theorem ffVal_split (A s : ℕ) (h : s ≤ A) (y : K) :
    ffVal A y = ffVal s y * ffVal (A - s) (y - s) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ffVal, ffVal, ffVal, prod_range_add]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  push_cast; ring

theorem rfVal_split (U s : ℕ) (h : s ≤ U) (y : K) :
    rfVal U y = rfVal s y * rfVal (U - s) (y + s) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, rfVal, rfVal, rfVal, prod_range_add]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  push_cast; ring

variable [CharZero K]

/-- `1/(m-1)! = m · 1/m!` for every integer `m` (with `1/m! = 0` for `m < 0`). -/
theorem intInvFact_sub_one (m : ℤ) : intInvFact (K := K) (m - 1) = m * intInvFact m := by
  by_cases h1 : 1 ≤ m
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, m = N + 1 := ⟨(m - 1).toNat, by omega⟩
    have e1 : ((N : ℤ) + 1 - 1).toNat = N := by omega
    have e2 : ((N : ℤ) + 1).toNat = N + 1 := by omega
    simp only [intInvFact, (by omega : (0 : ℤ) ≤ N + 1 - 1), (by omega : (0 : ℤ) ≤ N + 1),
      ite_true, e1, e2, Nat.factorial_succ]
    have : ((N.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : (N : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    push_cast
    field_simp
  · by_cases h0 : m = 0
    · subst h0; simp [intInvFact]
    · have : intInvFact (K := K) (m - 1) = 0 := by simp [intInvFact]; omega
      have h' : intInvFact (K := K) m = 0 := by simp [intInvFact]; omega
      rw [this, h', mul_zero]

/-- `m! = m · (m-1)!` for `m ≥ 1`. -/
theorem intFact_eq_mul (m : ℤ) (h : 1 ≤ m) : intFact (K := K) m = m * intFact (m - 1) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, m = N + 1 := ⟨(m - 1).toNat, by omega⟩
  have e1 : ((N : ℤ) + 1 - 1).toNat = N := by omega
  have e2 : ((N : ℤ) + 1).toNat = N + 1 := by omega
  simp only [intFact, e1, e2, Nat.factorial_succ]
  push_cast
  ring

/-- `1/(y-s)! = 1/y! · ff(s, y)` for all integers `y` (both sides vanish when `y - s < 0 ≤ y`). -/
theorem intInvFact_sub (y : ℤ) (s : ℕ) :
    intInvFact (K := K) (y - s) = intInvFact y * ffVal s (y : K) := by
  induction s with
  | zero => simp [ffVal]
  | succ s ih =>
    rw [ffVal, prod_range_succ, ← ffVal, ← mul_assoc, ← ih]
    have := intInvFact_sub_one (K := K) (y - s)
    rw [show y - s - 1 = y - ((s + 1 : ℕ) : ℤ) by push_cast; ring] at this
    rw [this]; push_cast; ring

/-- `1/y! = 1/(y+s)! · rf(s, y)` for all integers `y`. -/
theorem intInvFact_add (y : ℤ) (s : ℕ) :
    intInvFact (K := K) y = intInvFact (y + s) * rfVal s (y : K) := by
  induction s with
  | zero => simp [rfVal]
  | succ s ih =>
    rw [rfVal, prod_range_succ, ← rfVal, ih]
    have := intInvFact_sub_one (K := K) (y + ((s + 1 : ℕ) : ℤ))
    rw [show y + ((s + 1 : ℕ) : ℤ) - 1 = y + s by push_cast; ring] at this
    rw [this]; push_cast; ring

/-- `y! = (y-s)! · ff(s, y)` when `y - s ≥ 0`. -/
theorem intFact_eq_sub (y : ℤ) (s : ℕ) (h : 0 ≤ y - s) :
    intFact (K := K) y = intFact (y - s) * ffVal s (y : K) := by
  induction s with
  | zero => simp [ffVal]
  | succ s ih =>
    rw [ffVal, prod_range_succ, ← ffVal, ih (by push_cast at h; omega)]
    have := intFact_eq_mul (K := K) (y - s) (by push_cast at h; omega)
    rw [show y - s - 1 = y - ((s + 1 : ℕ) : ℤ) by push_cast; ring] at this
    rw [this]; push_cast; ring

/-- `(y+s)! = y! · rf(s, y)` when `y ≥ 0`. -/
theorem intFact_add (y : ℤ) (s : ℕ) (h : 0 ≤ y) :
    intFact (K := K) (y + s) = intFact y * rfVal s (y : K) := by
  induction s with
  | zero => simp [rfVal]
  | succ s ih =>
    rw [rfVal, prod_range_succ, ← rfVal, ← mul_assoc, ← ih]
    have := intFact_eq_mul (K := K) (y + ((s + 1 : ℕ) : ℤ)) (by omega)
    rw [show y + ((s + 1 : ℕ) : ℤ) - 1 = y + s by push_cast; ring] at this
    rw [this]; push_cast; ring

/-! ### Polynomials in `K[n][k]` -/

/-- The linear form `a n + b k + c` as a polynomial in `K[n][k]`. -/
def lin (a b c : ℤ) : K[X][X] := C (C (b : K)) * X + C (C (a : K) * X + C (c : K))

theorem evalEval_lin (a b c n k : ℤ) :
    (lin (K := K) a b c).evalEval (n : K) (k : K) = ((a * n + b * k + c : ℤ) : K) := by
  simp [lin, evalEval]; ring

theorem natDegree_lin_le (a b c : ℤ) : (lin (K := K) a b c).natDegree ≤ 1 := natDegree_linear_le

/-- `ff(A, p) = ∏_{t < A} (p - t)` for a polynomial `p`. -/
def ffPol (A : ℕ) (p : K[X][X]) : K[X][X] := ∏ t ∈ range A, (p - C (C (t : K)))

/-- `rf(U, p) = ∏_{t < U} (p + t + 1)` for a polynomial `p`. -/
def rfPol (U : ℕ) (p : K[X][X]) : K[X][X] := ∏ t ∈ range U, (p + C (C ((t : K) + 1)))

theorem evalEval_ffPol (A : ℕ) (p : K[X][X]) (x y : K) :
    (ffPol A p).evalEval x y = ffVal A (p.evalEval x y) := by
  simp [ffPol, ffVal, evalEval, eval_prod]

theorem evalEval_rfPol (U : ℕ) (p : K[X][X]) (x y : K) :
    (rfPol U p).evalEval x y = rfVal U (p.evalEval x y) := by
  simp [rfPol, rfVal, evalEval, eval_prod]

theorem natDegree_ffPol_le (A : ℕ) {p : K[X][X]} (hp : p.natDegree ≤ 1) :
    (ffPol A p).natDegree ≤ A := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ t ∈ range A, (p - C (C (t : K))).natDegree ≤ ∑ _t ∈ range A, 1 :=
        sum_le_sum fun t _ => by rw [natDegree_sub_C]; exact hp
    _ = A := by simp

theorem natDegree_rfPol_le (U : ℕ) {p : K[X][X]} (hp : p.natDegree ≤ 1) :
    (rfPol U p).natDegree ≤ U := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ t ∈ range U, (p + C (C ((t : K) + 1))).natDegree ≤ ∑ _t ∈ range U, 1 :=
        sum_le_sum fun t _ => by rw [natDegree_add_C]; exact hp
    _ = U := by simp

/-! ### The factor ratios (4.4.5) after clearing the common denominator (4.4.9) -/

/-- For a numerator factorial `(a n + b k + c)!`, the falling factorial of the common denominator
(4.4.9) has first argument `A = a⁺ J + b⁺ I`. -/
def numA (a b : ℤ) (I J : ℕ) : ℕ := (max a 0 * J + max b 0 * I).toNat

/-- For a denominator factorial `(u n + v k + w)!`, the rising factorial of (4.4.9) has first
argument `U = (-u)⁺ J + (-v)⁺ I`. -/
def denU (u v : ℤ) (I J : ℕ) : ℕ := (max (-u) 0 * J + max (-v) 0 * I).toNat

/-- The contribution of a numerator factorial `(a n + b k + c)!` to `ν_{ij} Δ / δ_{ij}`:
`ff(A - s, y - s)` if `s = a j + b i ≥ 0` and `rf(|s|, y) ff(A, y)` if `s < 0`, `y = a n + b k + c`. -/
def numQ (a b c : ℤ) (I J i j : ℕ) : K[X][X] :=
  if 0 ≤ a * j + b * i then
    ffPol (numA a b I J - (a * j + b * i).toNat) (lin a b c - C (C ((a * j + b * i : ℤ) : K)))
  else rfPol (a * j + b * i).natAbs (lin a b c) * ffPol (numA a b I J) (lin a b c)

/-- The contribution of a denominator factorial `1/(u n + v k + w)!` to `ν_{ij} Δ / δ_{ij}`:
`ff(s, y) rf(U, y)` if `s = u j + v i ≥ 0` and `rf(U - |s|, y + |s|)` if `s < 0`. -/
def denQ (u v w : ℤ) (I J i j : ℕ) : K[X][X] :=
  if 0 ≤ u * j + v * i then
    ffPol (u * j + v * i).toNat (lin u v w) * rfPol (denU u v I J) (lin u v w)
  else rfPol (denU u v I J - (u * j + v * i).natAbs)
    (lin u v w + C (C (((u * j + v * i).natAbs : ℕ) : K)))

theorem le_numA (a b : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    a * j + b * i ≤ numA a b I J := by
  have h1 : a * j ≤ max a 0 * J := by
    rcases le_or_gt 0 a with ha | ha
    · rw [max_eq_left ha]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) ha
    · rw [max_eq_right ha.le]; nlinarith
  have h2 : b * i ≤ max b 0 * I := by
    rcases le_or_gt 0 b with hb | hb
    · rw [max_eq_left hb]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hb
    · rw [max_eq_right hb.le]; nlinarith
  unfold numA; omega

theorem neg_le_denU (u v : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    -(u * j + v * i) ≤ denU u v I J := by
  have h1 : -(u * j) ≤ max (-u) 0 * J := by
    rcases le_or_gt 0 (-u) with ha | ha
    · rw [max_eq_left ha]; nlinarith
    · rw [max_eq_right ha.le]; nlinarith
  have h2 : -(v * i) ≤ max (-v) 0 * I := by
    rcases le_or_gt 0 (-v) with hb | hb
    · rw [max_eq_left hb]; nlinarith
    · rw [max_eq_right hb.le]; nlinarith
  unfold denU; omega

theorem natDegree_numQ_le (a b c : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    (numQ (K := K) a b c I J i j).natDegree ≤ a.natAbs * J + b.natAbs * I := by
  have hA : (numA a b I J : ℤ) ≤ (a.natAbs * J + b.natAbs * I : ℕ) := by
    unfold numA
    rw [Int.toNat_of_nonneg (by positivity)]
    push_cast
    have h1 : max a 0 * J ≤ |a| * J :=
      mul_le_mul_of_nonneg_right (max_le (le_abs_self a) (abs_nonneg a)) (by positivity)
    have h2 : max b 0 * I ≤ |b| * I :=
      mul_le_mul_of_nonneg_right (max_le (le_abs_self b) (abs_nonneg b)) (by positivity)
    linarith
  unfold numQ
  split_ifs with hs
  · refine (natDegree_ffPol_le _ ?_).trans (by omega)
    exact (natDegree_sub_C).le.trans (natDegree_lin_le _ _ _)
  · refine (natDegree_mul_le).trans ?_
    have e1 := natDegree_rfPol_le (a * j + b * i).natAbs (natDegree_lin_le (K := K) a b c)
    have e2 := natDegree_ffPol_le (numA a b I J) (natDegree_lin_le (K := K) a b c)
    -- `|s| + A ≤ |a| J + |b| I`
    have key : ((a * j + b * i).natAbs : ℤ) + numA a b I J ≤ (a.natAbs * J + b.natAbs * I : ℕ) := by
      unfold numA
      rw [Int.toNat_of_nonneg (by positivity)]
      push_cast
      rw [abs_of_neg (by omega : a * j + b * i < 0)]
      rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
      · exfalso
        have := mul_nonneg ha (Nat.cast_nonneg (α := ℤ) j)
        have := mul_nonneg hb (Nat.cast_nonneg (α := ℤ) i)
        omega
      · rw [max_eq_left ha, max_eq_right hb.le, abs_of_nonneg ha, abs_of_neg hb]
        have : (0 : ℤ) ≤ a * j := mul_nonneg ha (Nat.cast_nonneg j)
        nlinarith
      · rw [max_eq_right ha.le, max_eq_left hb, abs_of_neg ha, abs_of_nonneg hb]
        have : (0 : ℤ) ≤ b * i := mul_nonneg hb (Nat.cast_nonneg i)
        nlinarith
      · rw [max_eq_right ha.le, max_eq_right hb.le, abs_of_neg ha, abs_of_neg hb]
        nlinarith
    omega

theorem natDegree_denQ_le (u v w : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    (denQ (K := K) u v w I J i j).natDegree ≤ u.natAbs * J + v.natAbs * I := by
  have hU : (denU u v I J : ℤ) ≤ (u.natAbs * J + v.natAbs * I : ℕ) := by
    unfold denU
    rw [Int.toNat_of_nonneg (by positivity)]
    push_cast
    have h1 : max (-u) 0 * J ≤ |u| * J :=
      mul_le_mul_of_nonneg_right (max_le (neg_le_abs u) (abs_nonneg u)) (by positivity)
    have h2 : max (-v) 0 * I ≤ |v| * I :=
      mul_le_mul_of_nonneg_right (max_le (neg_le_abs v) (abs_nonneg v)) (by positivity)
    linarith
  unfold denQ
  split_ifs with hs
  · refine (natDegree_mul_le).trans ?_
    have e1 := natDegree_ffPol_le (u * j + v * i).toNat (natDegree_lin_le (K := K) u v w)
    have e2 := natDegree_rfPol_le (denU u v I J) (natDegree_lin_le (K := K) u v w)
    have key : ((u * j + v * i).toNat : ℤ) + denU u v I J ≤ (u.natAbs * J + v.natAbs * I : ℕ) := by
      unfold denU
      rw [Int.toNat_of_nonneg hs, Int.toNat_of_nonneg (by positivity)]
      push_cast
      rcases le_or_gt 0 u with ha | ha <;> rcases le_or_gt 0 v with hb | hb
      · rw [max_eq_right (by omega), max_eq_right (by omega), abs_of_nonneg ha, abs_of_nonneg hb]
        nlinarith
      · rw [max_eq_right (by omega), max_eq_left (by omega), abs_of_nonneg ha, abs_of_neg hb]
        nlinarith
      · rw [max_eq_left (by omega), max_eq_right (by omega), abs_of_neg ha, abs_of_nonneg hb]
        nlinarith
      · rw [max_eq_left (by omega), max_eq_left (by omega), abs_of_neg ha, abs_of_neg hb]
        nlinarith
    omega
  · refine (natDegree_rfPol_le _ ?_).trans (by omega)
    exact (natDegree_add_C).le.trans (natDegree_lin_le _ _ _)

/-- The numerator identity behind (4.4.5): with `y = a n + b k + c ≥ 0` and the shifted argument
`a(n-j) + b(k-i) + c ≥ 0`, `(a(n-j)+b(k-i)+c)! · ff(A, y) = y! · numQ(n,k)`. -/
theorem intFact_shift_mul_ffVal (a b c n k : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J)
    (h0 : 0 ≤ a * n + b * k + c) (h1 : 0 ≤ a * (n - j) + b * (k - i) + c) :
    intFact (K := K) (a * (n - j) + b * (k - i) + c) *
        ffVal (numA a b I J) (((a * n + b * k + c : ℤ)) : K) =
      intFact (a * n + b * k + c) * (numQ (K := K) a b c I J i j).evalEval (n : K) (k : K) := by
  have hrw : a * (n - j) + b * (k - i) + c = (a * n + b * k + c) - (a * j + b * i) := by ring
  have hle := le_numA a b hi hj
  rw [hrw]
  unfold numQ
  split_ifs with hs
  · rw [evalEval_ffPol, evalEval_sub, evalEval_lin, evalEval_C, eval_C]
    have hsle : (a * j + b * i).toNat ≤ numA a b I J := by omega
    rw [ffVal_split _ _ hsle]
    have e : ((a * j + b * i).toNat : ℤ) = a * j + b * i := Int.toNat_of_nonneg hs
    have := intFact_eq_sub (K := K) (a * n + b * k + c) (a * j + b * i).toNat (by omega)
    rw [e] at this
    rw [this]
    have e2 : (((a * j + b * i).toNat : ℕ) : K) = ((a * j + b * i : ℤ) : K) := by
      rw [← e]; push_cast; rfl
    rw [e2]
    push_cast
    ring
  · rw [evalEval_mul, evalEval_rfPol, evalEval_ffPol, evalEval_lin]
    have e : a * n + b * k + c - (a * j + b * i) =
        (a * n + b * k + c) + ((a * j + b * i).natAbs : ℤ) := by omega
    rw [e, intFact_add _ _ h0]
    ring

/-- The denominator identity behind (4.4.5): for all integers,
`1/(u(n-j)+v(k-i)+w)! · rf(U, y) = 1/y! · denQ(n,k)`, `y = u n + v k + w`. -/
theorem intInvFact_shift_mul_rfVal (u v w n k : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    intInvFact (K := K) (u * (n - j) + v * (k - i) + w) *
        rfVal (denU u v I J) (((u * n + v * k + w : ℤ)) : K) =
      intInvFact (u * n + v * k + w) * (denQ (K := K) u v w I J i j).evalEval (n : K) (k : K) := by
  have hrw : u * (n - j) + v * (k - i) + w = (u * n + v * k + w) - (u * j + v * i) := by ring
  have hle := neg_le_denU u v hi hj
  rw [hrw]
  unfold denQ
  split_ifs with hs
  · rw [evalEval_mul, evalEval_rfPol, evalEval_ffPol, evalEval_lin]
    have e : ((u * j + v * i).toNat : ℤ) = u * j + v * i := Int.toNat_of_nonneg hs
    have := intInvFact_sub (K := K) (u * n + v * k + w) (u * j + v * i).toNat
    rw [e] at this
    rw [this]
    ring
  · rw [evalEval_rfPol, evalEval_add, evalEval_lin, evalEval_C, eval_C]
    have hsle : (u * j + v * i).natAbs ≤ denU u v I J := by omega
    rw [rfVal_split _ _ hsle]
    have e : u * n + v * k + w - (u * j + v * i) =
        (u * n + v * k + w) + ((u * j + v * i).natAbs : ℤ) := by omega
    rw [e, intInvFact_add (K := K) (u * n + v * k + w) (u * j + v * i).natAbs]
    push_cast
    ring

/-! ### The polynomial factor `P(n - j, k - i)` -/

/-- `P(n - j, k - i)` as a polynomial in `K[n][k]`. -/
def pShift (P : MvPolynomial (Fin 2) K) (i j : ℕ) : K[X][X] :=
  MvPolynomial.aeval (fun t : Fin 2 => ![C (X - C (j : K)), X - C (C (i : K))] t) P

theorem evalEval_pShift (P : MvPolynomial (Fin 2) K) (i j : ℕ) (n k : ℤ) :
    (pShift P i j).evalEval (n : K) (k : K) = P.eval ![((n - j : ℤ) : K), ((k - i : ℤ) : K)] := by
  unfold pShift
  induction P using MvPolynomial.induction_on with
  | C a => simp [evalEval, Polynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, evalEval_add, hp, hq, map_add]
  | mul_X p t hp =>
    rw [map_mul, evalEval_mul, hp, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    fin_cases t <;> simp [evalEval]

theorem natDegree_pShift_le (P : MvPolynomial (Fin 2) K) (i j : ℕ) :
    (pShift P i j).natDegree ≤ P.totalDegree := by
  classical
  unfold pShift
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun v hv => ?_
  have hv' := MvPolynomial.le_totalDegree hv
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hv'
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : (algebraMap K K[X][X] (P.coeff v)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply, natDegree_C]
  have h2 : ((C (X - C (j : K)) : K[X][X]) ^ v 0).natDegree = 0 := by
    rw [← C_pow, natDegree_C]
  have h3 : ((X - C (C (i : K)) : K[X][X]) ^ v 1).natDegree ≤ v 1 :=
    natDegree_pow_le.trans (by rw [natDegree_X_sub_C, mul_one])
  refine natDegree_mul_le.trans ?_
  have := (natDegree_mul_le (p := (C (X - C (j : K)) : K[X][X]) ^ v 0)
    (q := (X - C (C (i : K)) : K[X][X]) ^ v 1))
  omega

/-! ### Steps 3–5 of Sister Celine's method -/

/-- Steps 3–4 of Sister Celine's method (CO-388): the polynomial `Q_{ij} = ν_{ij} Δ / δ_{ij}` of
(4.4.10).  With `Δ` the common denominator (4.4.9) (without the factor `P(n,k)`, which we do not
divide by), `F(n-j, k-i) Δ(n,k) = x^{-i} H(n,k) Q_{ij}(n,k)`, where `F(n,k) = P(n,k) H(n,k)`
(`eval_shift_mul_deltaVal`). -/
def celineQ (D : ProperHypergeometricData K) (I J i j : ℕ) : K[X][X] :=
  pShift D.P i j * (∏ s, numQ (D.a s) (D.b s) (D.c s) I J i j) *
    ∏ s, denQ (D.u s) (D.v s) (D.w s) I J i j

/-- The common bound for the degrees in `k` of the `Q_{ij}`: it grows linearly in `I, J`. -/
def degBound (D : ProperHypergeometricData K) (I J : ℕ) : ℕ :=
  D.P.totalDegree + ∑ s, ((D.a s).natAbs * J + (D.b s).natAbs * I) +
    ∑ s, ((D.u s).natAbs * J + (D.v s).natAbs * I)

theorem natDegree_celineQ_le (D : ProperHypergeometricData K) {I J i j : ℕ} (hi : i ≤ I)
    (hj : j ≤ J) : (celineQ D I J i j).natDegree ≤ degBound D I J := by
  unfold celineQ degBound
  refine natDegree_mul_le.trans ?_
  have h1 := natDegree_mul_le (p := pShift D.P i j)
    (q := ∏ s, numQ (K := K) (D.a s) (D.b s) (D.c s) I J i j)
  have h2 := natDegree_pShift_le D.P i j
  have h3 : (∏ s, numQ (K := K) (D.a s) (D.b s) (D.c s) I J i j).natDegree ≤
      ∑ s, ((D.a s).natAbs * J + (D.b s).natAbs * I) :=
    (natDegree_prod_le _ _).trans (sum_le_sum fun s _ => natDegree_numQ_le _ _ _ hi hj)
  have h4 : (∏ s, denQ (K := K) (D.u s) (D.v s) (D.w s) I J i j).natDegree ≤
      ∑ s, ((D.u s).natAbs * J + (D.v s).natAbs * I) :=
    (natDegree_prod_le _ _).trans (sum_le_sum fun s _ => natDegree_denQ_le _ _ _ hi hj)
  omega

/-- The value at `(n, k)` of the common denominator (4.4.9) without `P(n,k)`:
`∏ ff(a_s⁺ J + b_s⁺ I, a_s n + b_s k + c_s) ∏ rf((-u_s)⁺ J + (-v_s)⁺ I, u_s n + v_s k + w_s)`. -/
def deltaVal (D : ProperHypergeometricData K) (I J : ℕ) (n k : ℤ) : K :=
  (∏ s, ffVal (numA (D.a s) (D.b s) I J) ((D.a s * n + D.b s * k + D.c s : ℤ) : K)) *
    ∏ s, rfVal (denU (D.u s) (D.v s) I J) ((D.u s * n + D.v s * k + D.w s : ℤ) : K)

/-- `H(n,k) x^k = ∏ (a_s n + b_s k + c_s)! / ∏ (u_s n + v_s k + w_s)! · x^k`. -/
def hVal (D : ProperHypergeometricData K) (n k : ℤ) : K :=
  (∏ s, intFact (D.a s * n + D.b s * k + D.c s)) *
    (∏ s, intInvFact (D.u s * n + D.v s * k + D.w s)) * D.x ^ k

/-- CO-390 / CO-388 (steps 3–4). The ratio `F(n-j,k-i)/F(n,k)` after clearing the common
denominator: `F(n-j, k-i) Δ(n,k) = x^{-i} H(n,k) x^k Q_{ij}(n,k)`, at points where `F(n,k)` and
`F(n-j,k-i)` are well defined. -/
theorem eval_shift_mul_deltaVal (D : ProperHypergeometricData K) (hx : D.x ≠ 0) {I J i j : ℕ}
    (hi : i ≤ I) (hj : j ≤ J) (n k : ℤ) (h0 : D.WellDefinedAt n k)
    (h1 : D.WellDefinedAt (n - j) (k - i)) :
    D.eval (n - j) (k - i) * deltaVal D I J n k =
      D.x ^ (-(i : ℤ)) * hVal D n k * (celineQ D I J i j).evalEval (n : K) (k : K) := by
  have e1 : (∏ s, intFact (K := K) (D.a s * (n - j) + D.b s * (k - i) + D.c s)) *
      (∏ s, ffVal (numA (D.a s) (D.b s) I J) ((D.a s * n + D.b s * k + D.c s : ℤ) : K)) =
      (∏ s, intFact (D.a s * n + D.b s * k + D.c s)) *
        ∏ s, (numQ (K := K) (D.a s) (D.b s) (D.c s) I J i j).evalEval (n : K) (k : K) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun s _ => intFact_shift_mul_ffVal _ _ _ _ _ hi hj (h0 s) (h1 s)
  have e2 : (∏ s, intInvFact (K := K) (D.u s * (n - j) + D.v s * (k - i) + D.w s)) *
      (∏ s, rfVal (denU (D.u s) (D.v s) I J) ((D.u s * n + D.v s * k + D.w s : ℤ) : K)) =
      (∏ s, intInvFact (D.u s * n + D.v s * k + D.w s)) *
        ∏ s, (denQ (K := K) (D.u s) (D.v s) (D.w s) I J i j).evalEval (n : K) (k : K) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun s _ => intInvFact_shift_mul_rfVal _ _ _ _ _ hi hj
  have e3 : D.x ^ (k - (i : ℤ)) = D.x ^ (-(i : ℤ)) * D.x ^ k := by
    rw [← zpow_add₀ hx]; ring_nf
  unfold ProperHypergeometricData.eval deltaVal hVal celineQ
  rw [evalEval_mul, evalEval_mul, evalEval_pShift, evalEval_prod, evalEval_prod, e3]
  calc _ = (MvPolynomial.eval ![((n - j : ℤ) : K), ((k - i : ℤ) : K)] D.P) *
        ((∏ s, intFact (K := K) (D.a s * (n - j) + D.b s * (k - i) + D.c s)) *
          (∏ s, ffVal (numA (D.a s) (D.b s) I J) ((D.a s * n + D.b s * k + D.c s : ℤ) : K))) *
        ((∏ s, intInvFact (K := K) (D.u s * (n - j) + D.v s * (k - i) + D.w s)) *
          (∏ s, rfVal (denU (D.u s) (D.v s) I J) ((D.u s * n + D.v s * k + D.w s : ℤ) : K))) *
        (D.x ^ (-(i : ℤ)) * D.x ^ k) := by push_cast; ring
    _ = _ := by rw [e1, e2]; ring

/-- At a point where `F(n,k) ≠ 0` and all `F(n-j,k-i)` (`i ≤ I`, `j ≤ J`) are well defined, the
common denominator `Δ(n,k)` does not vanish. -/
theorem deltaVal_ne_zero (D : ProperHypergeometricData K) {I J : ℕ} {n k : ℤ}
    (hF : D.eval n k ≠ 0) (hwd : ∀ i ≤ I, ∀ j ≤ J, D.WellDefinedAt (n - j) (k - i)) :
    deltaVal D I J n k ≠ 0 := by
  unfold deltaVal
  refine mul_ne_zero (prod_ne_zero_iff.2 fun s _ => ?_) (prod_ne_zero_iff.2 fun s _ => ?_)
  · -- the corner `(i, j)` maximizing `a_s j + b_s i`
    set a := D.a s
    set b := D.b s
    have hc := hwd (if 0 < b then I else 0) (by split_ifs <;> omega)
      (if 0 < a then J else 0) (by split_ifs <;> omega) s
    have hcorner : a * ((if 0 < a then J else 0 : ℕ) : ℤ) + b * ((if 0 < b then I else 0 : ℕ) : ℤ)
        = max a 0 * J + max b 0 * I := by
      rcases le_or_gt a 0 with ha | ha <;> rcases le_or_gt b 0 with hb | hb
      · simp [not_lt.2 ha, not_lt.2 hb, max_eq_right ha, max_eq_right hb]
      · simp [not_lt.2 ha, hb, max_eq_right ha, max_eq_left hb.le]
      · simp [ha, not_lt.2 hb, max_eq_left ha.le, max_eq_right hb]
      · simp [ha, hb, max_eq_left ha.le, max_eq_left hb.le]
    have hA : (numA a b I J : ℤ) ≤ a * n + b * k + D.c s := by
      unfold numA
      rw [Int.toNat_of_nonneg (by positivity), ← hcorner]
      have : a * (n - ((if 0 < a then J else 0 : ℕ) : ℤ)) + b * (k - ((if 0 < b then I else 0 : ℕ) : ℤ))
          + D.c s ≥ 0 := hc
      linarith
    unfold ffVal
    refine prod_ne_zero_iff.2 fun t ht => ?_
    have ht' := mem_range.1 ht
    have : ((a * n + b * k + D.c s : ℤ) : K) - (t : K) = ((a * n + b * k + D.c s - t : ℤ) : K) := by
      push_cast; ring
    rw [this, Int.cast_ne_zero]
    omega
  · have hy : 0 ≤ D.u s * n + D.v s * k + D.w s := by
      by_contra hneg
      exact hF (D.eval_eq_zero_of_neg n k s (not_le.1 hneg))
    unfold rfVal
    refine prod_ne_zero_iff.2 fun t _ => ?_
    have : ((D.u s * n + D.v s * k + D.w s : ℤ) : K) + ((t : K) + 1) =
        ((D.u s * n + D.v s * k + D.w s + t + 1 : ℤ) : K) := by push_cast; ring
    rw [this, Int.cast_ne_zero]
    omega

/-- Step 5 of Sister Celine's method (CO-388): the unknown coefficients `b = (b_{ij}(n))` (the
`a_{ij}(n) x^{-i}`) must make the numerator polynomial `∑ b_{ij}(n) Q_{ij}(n,k)` vanish identically
in `k`, i.e. lie in the kernel of this `K[n]`-linear map (equating the coefficients of all powers of
`k` to zero is `Polynomial.ext`). -/
@[kb "petkovsekwilfzeilberger1996" "Sister Celine's algorithm, steps 1-5, p. 69"]
def celineMap (D : ProperHypergeometricData K) (I J : ℕ) :
    (Fin (I + 1) × Fin (J + 1) → K[X]) →ₗ[K[X]] K[X][X] where
  toFun b := ∑ p, C (b p) * celineQ D I J p.1 p.2
  map_add' b b' := by simp [add_mul, sum_add_distrib]
  map_smul' c b := by
    simp only [Pi.smul_apply, smul_eq_mul, C_mul, mul_assoc, RingHom.id_apply]
    rw [Polynomial.smul_eq_C_mul, mul_sum]

/-- CO-388. Correctness of Sister Celine's method: every solution `b` of the linear system of step 5
gives the `k`-free recurrence `∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n-j, k-i) = 0` with
`a_{ij}(n) = b_{ij}(n) x^i`, valid at every point `(n,k)` where `F(n,k) ≠ 0` and all the values
`F(n-j, k-i)` are well defined. -/
@[kb "petkovsekwilfzeilberger1996" "Sister Celine's algorithm, steps 1-5, p. 69"]
theorem celine_sound (D : ProperHypergeometricData K) (hx : D.x ≠ 0) {I J : ℕ}
    (b : Fin (I + 1) × Fin (J + 1) → K[X]) (hb : b ∈ LinearMap.ker (celineMap D I J))
    (n k : ℤ) (hF : D.eval n k ≠ 0) (hwd : ∀ i ≤ I, ∀ j ≤ J, D.WellDefinedAt (n - j) (k - i)) :
    ∑ p : Fin (I + 1) × Fin (J + 1), (b p * C (D.x ^ (p.1 : ℕ))).eval (n : K) *
      D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 := by
  have hΔ := deltaVal_ne_zero D hF hwd
  have h0 : D.WellDefinedAt n k := by simpa using hwd 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  have hb' : (∑ p : Fin (I + 1) × Fin (J + 1), C (b p) * celineQ D I J p.1 p.2).evalEval
      (n : K) (k : K) = 0 := by
    rw [LinearMap.mem_ker] at hb
    change (∑ p, C (b p) * celineQ D I J p.1 p.2) = 0 at hb
    rw [hb, evalEval_zero]
  rw [evalEval_finsetSum] at hb'
  refine (mul_left_inj' hΔ).1 ?_
  rw [zero_mul, sum_mul]
  calc ∑ p : Fin (I + 1) × Fin (J + 1), (b p * C (D.x ^ (p.1 : ℕ))).eval (n : K) *
        D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) * deltaVal D I J n k
      = ∑ p : Fin (I + 1) × Fin (J + 1), hVal D n k *
          (C (b p) * celineQ D I J p.1 p.2).evalEval (n : K) (k : K) := by
        refine sum_congr rfl fun p _ => ?_
        rw [mul_assoc, eval_shift_mul_deltaVal D hx (Nat.lt_succ_iff.1 p.1.2)
          (Nat.lt_succ_iff.1 p.2.2) n k h0
          (hwd _ (Nat.lt_succ_iff.1 p.1.2) _ (Nat.lt_succ_iff.1 p.2.2))]
        rw [eval_mul, eval_C, evalEval_mul, evalEval_C]
        have : D.x ^ (p.1 : ℕ) * D.x ^ (-((p.1 : ℕ) : ℤ)) = 1 := by
          rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hx)]
        linear_combination (eval (n : K) (b p) * hVal D n k *
          (celineQ D I J p.1 p.2).evalEval (n : K) (k : K)) * this
    _ = 0 := by rw [← mul_sum, hb', mul_zero]

/-- CO-388 / CO-389. Sister Celine's method succeeds as soon as the number `(I+1)(J+1)` of unknowns
exceeds the number `degBound D I J + 1` of equations (one per power of `k`): the kernel of step 5 is
then nonzero. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.4.1 (proof), p. 77-78"]
theorem celineMap_ker_ne_bot (D : ProperHypergeometricData K) {I J : ℕ}
    (h : degBound D I J + 1 < (I + 1) * (J + 1)) : LinearMap.ker (celineMap D I J) ≠ ⊥ := by
  classical
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_sum_C_mul_eq_zero
    (fun p : Fin (I + 1) × Fin (J + 1) => celineQ D I J p.1 p.2) (degBound D I J)
    (fun p => natDegree_celineQ_le D (Nat.lt_succ_iff.1 p.1.2) (Nat.lt_succ_iff.1 p.2.2))
    (by simpa using h)
  rw [Submodule.ne_bot_iff]
  exact ⟨b, hb, hb0⟩

/-- The recurrence is nontrivial: `a_{ij} = b_{ij} x^i` is nonzero when `b` is. -/
theorem mul_C_pow_ne_zero (D : ProperHypergeometricData K) (hx : D.x ≠ 0) {I J : ℕ}
    {b : Fin (I + 1) × Fin (J + 1) → K[X]} (hb : b ≠ 0) :
    (fun p : Fin (I + 1) × Fin (J + 1) => b p * C (D.x ^ (p.1 : ℕ))) ≠ 0 := by
  intro h
  apply hb
  funext p
  have := congrFun h p
  simp only [Pi.zero_apply, mul_eq_zero, C_eq_zero] at this
  exact this.resolve_right (pow_ne_zero _ hx)

/-- CO-389. A proper hypergeometric term satisfies a nontrivial `k`-free recurrence
`∑_{i ≤ I, j ≤ J} a_{ij}(n) F(n-j, k-i) = 0` of any span `(I, J)` with
`degBound D I J + 1 < (I+1)(J+1)`, valid at every point where `F(n,k) ≠ 0` and all the values of `F`
in the recurrence are well defined. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.4.1, p. 75"]
theorem exists_kfree_recurrence (D : ProperHypergeometricData K) (hx : D.x ≠ 0) {I J : ℕ}
    (h : degBound D I J + 1 < (I + 1) * (J + 1)) :
    ∃ a : Fin (I + 1) × Fin (J + 1) → K[X], a ≠ 0 ∧
      ∀ n k : ℤ, D.eval n k ≠ 0 → (∀ i ≤ I, ∀ j ≤ J, D.WellDefinedAt (n - j) (k - i)) →
        ∑ p : Fin (I + 1) × Fin (J + 1), (a p).eval (n : K) *
          D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 := by
  obtain ⟨b, hb, hb0⟩ := Submodule.ne_bot_iff _ |>.1 (celineMap_ker_ne_bot D h)
  exact ⟨_, mul_C_pow_ne_zero D hx hb0, fun n k hF hwd => celine_sound D hx b hb n k hF hwd⟩

/-- The order `J* = ∑ |b_s| + ∑ |v_s|` of (4.4.3). -/
def jStar (D : ProperHypergeometricData K) : ℕ := ∑ s, (D.b s).natAbs + ∑ s, (D.v s).natAbs

/-- The order `I* = 1 + deg P + J* (∑ |a_s| + ∑ |u_s| - 1)` of (4.4.3) (with truncated subtraction:
when all `a_s, u_s` vanish this is `1 + deg P`). -/
def iStar (D : ProperHypergeometricData K) : ℕ :=
  1 + D.P.totalDegree + jStar D * ((∑ s, (D.a s).natAbs + ∑ s, (D.u s).natAbs) - 1)

theorem degBound_eq (D : ProperHypergeometricData K) (I J : ℕ) :
    degBound D I J = D.P.totalDegree + (∑ s, (D.a s).natAbs + ∑ s, (D.u s).natAbs) * J +
      (∑ s, (D.b s).natAbs + ∑ s, (D.v s).natAbs) * I := by
  unfold degBound
  simp only [sum_add_distrib, ← sum_mul]
  ring

/-- The orders `(I*, J*)` make the unknowns outnumber the equations. -/
theorem degBound_star_lt (D : ProperHypergeometricData K) :
    degBound D (iStar D) (jStar D) + 1 < (iStar D + 1) * (jStar D + 1) := by
  rw [degBound_eq]
  unfold iStar
  set A := ∑ s, (D.a s).natAbs + ∑ s, (D.u s).natAbs
  set B := jStar D
  set d := D.P.totalDegree
  have hB : ∑ s, (D.b s).natAbs + ∑ s, (D.v s).natAbs = B := rfl
  rw [hB]
  rcases A with _ | A
  · simp only [zero_mul, Nat.zero_sub, mul_zero, add_zero]
    nlinarith
  · simp only [Nat.add_sub_cancel]
    nlinarith

/-- CO-389. **Fundamental Theorem** (Theorem 4.4.1). Let `F(n,k)` be a proper hypergeometric term
(with `x ≠ 0`). Then `F` satisfies a nontrivial `k`-free recurrence
`∑_{i=0}^{I} ∑_{j=0}^{J} a_{ij}(n) F(n-j, k-i) = 0` with polynomial coefficients `a_{ij}(n)`, not all
zero, at every point `(n,k)` at which `F(n,k) ≠ 0` and all the values of `F` in the recurrence are
well defined; moreover one can take `(I, J) = (I*, J*)` of (4.4.3). -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.4.1, p. 75"]
theorem fundamental_theorem (D : ProperHypergeometricData K) (hx : D.x ≠ 0) :
    ∃ a : Fin (iStar D + 1) × Fin (jStar D + 1) → K[X], a ≠ 0 ∧
      ∀ n k : ℤ, D.eval n k ≠ 0 →
        (∀ i ≤ iStar D, ∀ j ≤ jStar D, D.WellDefinedAt (n - j) (k - i)) →
        ∑ p : Fin (iStar D + 1) × Fin (jStar D + 1), (a p).eval (n : K) *
          D.eval (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 :=
  exists_kfree_recurrence D hx (degBound_star_lt D)

end Celine

end UndergradKB.Combinatorics.AeqB
