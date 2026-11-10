import Mathlib.Algebra.Polynomial.Bivariate
import UndergradKB.Combinatorics.AeqB.Celine
import UndergradKB.Combinatorics.AeqB.QAnalogue
import UndergradKB.Common.Attr

/-!
# The q-version of the Fundamental Theorem (Petkovsek–Wilf–Zeilberger, "A = B", Theorem 4.5.2)

A q-proper hypergeometric term (4.5.5)
`F(n,k) = ∏_s Q(a_s n + b_s k, c_s) / ∏_s Q(u_s n + v_s k, w_s) · q^{α n² + β n k + γ k² + δ k + ε n} ξ^k`
satisfies a nontrivial `k`-free recurrence `∑_{i ≤ I, j ≤ J} α_{ij}(q^n) F(n-j, k-i) = 0` with
`J = ∑ b_s² + ∑ v_s² + 2|γ|` (`q_fundamental_theorem`).

The proof is Sister Celine's counting argument (as in `Celine.lean`): after multiplying by a common
factor `Δ(n,k) q^{kT}`, each shifted term becomes `κ_{ij}(n) H(n,k) E_{ij}(q^n, q^k)` with `E_{ij}` a
polynomial in `q^k` (coefficients polynomials in `q^n`) of degree at most `I J* + J A₂` — linear in
`I` with slope `J*` — so for `J = J*` and `I` large the `(I+1)(J+1)` unknowns outnumber the equations.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Finset QAnalogue

namespace QFundamental

variable {K : Type*} [Field K]

/-! ### Products of q-factors -/

/-- `∏_{t<m} (1 - c q^{y-t})`. -/
def dnVal (q c : K) (y : ℤ) (m : ℕ) : K := ∏ t ∈ range m, (1 - c * q ^ (y - t))

/-- `∏_{t<m} (1 - c q^{y+t+1})`. -/
def upVal (q c : K) (y : ℤ) (m : ℕ) : K := ∏ t ∈ range m, (1 - c * q ^ (y + t + 1))

theorem qFac_eq_mul_dnVal (q c : K) (y m : ℕ) (h : m ≤ y) :
    qFac q c y = qFac q c (y - m) * dnVal q c y m := by
  induction m with
  | zero => simp [dnVal]
  | succ m ih =>
    rw [ih (by omega), show y - m = (y - (m + 1)) + 1 by omega, qFac_succ, dnVal, dnVal,
      prod_range_succ]
    have e : q ^ ((y - (m + 1)) + 1) = q ^ ((y : ℤ) - (m : ℤ)) := by
      rw [← zpow_natCast]; congr 1; push_cast [show m + 1 ≤ y from h]; ring
    rw [e]; ring

theorem qFac_add (q c : K) (y m : ℕ) : qFac q c (y + m) = qFac q c y * upVal q c y m := by
  induction m with
  | zero => simp [upVal]
  | succ m ih =>
    rw [← add_assoc, qFac_succ, ih, upVal, upVal, prod_range_succ]
    have e : q ^ (y + m + 1) = q ^ ((y : ℤ) + (m : ℤ) + 1) := by
      rw [← zpow_natCast]; push_cast; ring_nf
    rw [e]; ring

theorem dnVal_add (q c : K) (y : ℤ) (s r : ℕ) :
    dnVal q c y (s + r) = dnVal q c y s * dnVal q c (y - s) r := by
  rw [dnVal, dnVal, dnVal, prod_range_add]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  congr 3; push_cast; ring

theorem upVal_add (q c : K) (y : ℤ) (s r : ℕ) :
    upVal q c y (s + r) = upVal q c y s * upVal q c (y + s) r := by
  rw [upVal, upVal, upVal, prod_range_add]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  congr 3; push_cast; ring

/-- The numerator ratio: for `y ≥ 0`, `y - s ≥ 0`, `s ≤ A`,
`Q(y - s) · ∏_{t<A}(1 - c q^{y-t}) = Q(y) · (remaining factors)`. -/
theorem num_ratio (q c : K) (y s : ℤ) (A : ℕ) (hy : 0 ≤ y) (hys : 0 ≤ y - s) (hsA : s ≤ A) :
    qFac q c (y - s).toNat * dnVal q c y A = qFac q c y.toNat *
      (if 0 ≤ s then dnVal q c (y - s) (A - s.toNat)
        else upVal q c y s.natAbs * dnVal q c y A) := by
  split_ifs with hs
  · have h1 := qFac_eq_mul_dnVal q c y.toNat s.toNat (by omega)
    have h2 := dnVal_add q c y s.toNat (A - s.toNat)
    rw [show s.toNat + (A - s.toNat) = A by omega] at h2
    have e1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy
    have e2 : (y - s).toNat = y.toNat - s.toNat := by omega
    have e3 : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs
    rw [e1] at h1
    rw [e3] at h2
    rw [h2, h1, e2]; ring
  · have e2 : (y - s).toNat = y.toNat + s.natAbs := by omega
    have e1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy
    rw [e2, qFac_add, e1]; ring

/-- The denominator ratio: with `Q(y), Q(y - s) ≠ 0`,
`Q(y - s)⁻¹ · ∏_{t<U}(1 - w q^{y+t+1}) = Q(y)⁻¹ · (remaining factors)`. -/
theorem den_ratio (q w : K) (y s : ℤ) (U : ℕ) (hy : 0 ≤ y) (hys : 0 ≤ y - s) (hsU : -s ≤ U)
    (hQ : qFac q w y.toNat ≠ 0) (hQs : qFac q w (y - s).toNat ≠ 0) :
    (qFac q w (y - s).toNat)⁻¹ * upVal q w y U = (qFac q w y.toNat)⁻¹ *
      (if 0 ≤ s then dnVal q w y s.toNat * upVal q w y U
        else upVal q w (y - s) (U - s.natAbs)) := by
  have e1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy
  split_ifs with hs
  · have h1 := qFac_eq_mul_dnVal q w y.toNat s.toNat (by omega)
    have e2 : (y - s).toNat = y.toNat - s.toNat := by omega
    rw [e1] at h1
    rw [e2] at hQs ⊢
    have hdn : dnVal q w y s.toNat ≠ 0 := by rw [h1] at hQ; exact right_ne_zero_of_mul hQ
    rw [h1]
    field_simp
  · have e2 : (y - s).toNat = y.toNat + s.natAbs := by omega
    have h1 := qFac_add q w y.toNat s.natAbs
    rw [e1] at h1
    rw [e2] at hQs ⊢
    rw [h1] at hQs ⊢
    have hup : upVal q w y s.natAbs ≠ 0 := right_ne_zero_of_mul hQs
    have h2 := upVal_add q w y s.natAbs (U - s.natAbs)
    rw [show s.natAbs + (U - s.natAbs) = U by omega] at h2
    rw [h2, show y + (s.natAbs : ℤ) = y - s by omega]
    field_simp

/-! ### Exponent bookkeeping -/

theorem zpow_toNat_pow (q : K) (z m : ℤ) (hm : 0 ≤ m) : (q ^ z) ^ m.toNat = q ^ (z * m) := by
  rw [← zpow_natCast, ← zpow_mul, Int.toNat_of_nonneg hm]

theorem prod_zpow_eq (q : K) (hq : q ≠ 0) {ι : Type*} (S : Finset ι) (e : ι → ℤ) :
    ∏ s ∈ S, q ^ e s = q ^ (∑ s ∈ S, e s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih => rw [prod_insert hx, sum_insert hx, ih, zpow_add₀ hq]

theorem qcomb (q : K) (hq : q ≠ 0) (a b c : ℤ) (x y : K) :
    q ^ a * (q ^ b * x * (q ^ c * y)) = q ^ (a + b + c) * (x * y) := by
  rw [zpow_add₀ hq, zpow_add₀ hq]; ring

theorem max_eq_max_neg_add (a : ℤ) : max a 0 = max (-a) 0 + a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by omega)]; ring
  · rw [max_eq_right h, max_eq_left (by omega)]; ring

/-! ### The polynomial factors -/

/-- The factor `q^{a⁻ n + b⁻ k} (1 - c q^{a n + b k + e})` as a polynomial in `N = q^n`, `Q = q^k`:
`N^{a⁻} Q^{b⁻} - c q^e N^{a⁺} Q^{b⁺}`. -/
def fpoly (q c : K) (a b e : ℤ) : K[X][X] :=
  C (X ^ (max (-a) 0).toNat) * X ^ (max (-b) 0).toNat -
    C (C (c * q ^ e) * X ^ (max a 0).toNat) * X ^ (max b 0).toNat

theorem evalEval_fpoly (q c : K) (hq : q ≠ 0) (a b e n k : ℤ) :
    (fpoly q c a b e).evalEval (q ^ n) (q ^ k) =
      q ^ (max (-a) 0 * n + max (-b) 0 * k) * (1 - c * q ^ (a * n + b * k + e)) := by
  simp only [fpoly, evalEval_sub, evalEval_mul, evalEval_C, evalEval_X, evalEval_pow, eval_pow,
    eval_X, eval_mul, eval_C]
  rw [zpow_toNat_pow q n _ (le_max_right _ _), zpow_toNat_pow q k _ (le_max_right _ _),
    zpow_toNat_pow q n _ (le_max_right _ _), zpow_toNat_pow q k _ (le_max_right _ _)]
  rw [mul_sub, mul_one, mul_left_comm (q ^ _) c, ← zpow_add₀ hq, ← zpow_add₀ hq,
    mul_assoc c, mul_assoc, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 2
  · ring
  · congr 1
    rw [max_eq_max_neg_add a, max_eq_max_neg_add b]; ring

theorem natDegree_fpoly_le (q c : K) (a b e : ℤ) : (fpoly q c a b e).natDegree ≤ b.natAbs := by
  unfold fpoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_C_mul_X_pow_le _ _).trans ?_; omega
  · refine (natDegree_C_mul_X_pow_le _ _).trans ?_; omega

/-- `∏_{t<m} fpoly(e₀ - t)`. -/
def dnPoly (q c : K) (a b e0 : ℤ) (m : ℕ) : K[X][X] := ∏ t ∈ range m, fpoly q c a b (e0 - t)

/-- `∏_{t<m} fpoly(e₀ + t + 1)`. -/
def upPoly (q c : K) (a b e0 : ℤ) (m : ℕ) : K[X][X] := ∏ t ∈ range m, fpoly q c a b (e0 + t + 1)

theorem evalEval_dnPoly (q c : K) (hq : q ≠ 0) (a b e0 : ℤ) (m : ℕ) (n k : ℤ) :
    (dnPoly q c a b e0 m).evalEval (q ^ n) (q ^ k) =
      q ^ (m * (max (-a) 0 * n + max (-b) 0 * k)) * dnVal q c (a * n + b * k + e0) m := by
  rw [dnPoly, evalEval_prod, dnVal]
  simp only [evalEval_fpoly q c hq]
  rw [prod_mul_distrib, prod_const, card_range, ← zpow_natCast, ← zpow_mul, mul_comm (_ : ℤ) (m : ℤ)]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  congr 3; ring

theorem evalEval_upPoly (q c : K) (hq : q ≠ 0) (a b e0 : ℤ) (m : ℕ) (n k : ℤ) :
    (upPoly q c a b e0 m).evalEval (q ^ n) (q ^ k) =
      q ^ (m * (max (-a) 0 * n + max (-b) 0 * k)) * upVal q c (a * n + b * k + e0) m := by
  rw [upPoly, evalEval_prod, upVal]
  simp only [evalEval_fpoly q c hq]
  rw [prod_mul_distrib, prod_const, card_range, ← zpow_natCast, ← zpow_mul, mul_comm (_ : ℤ) (m : ℤ)]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  congr 3; ring

theorem natDegree_dnPoly_le (q c : K) (a b e0 : ℤ) (m : ℕ) :
    (dnPoly q c a b e0 m).natDegree ≤ m * b.natAbs := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ t ∈ range m, (fpoly q c a b (e0 - t)).natDegree ≤ ∑ _t ∈ range m, b.natAbs :=
        sum_le_sum fun t _ => natDegree_fpoly_le _ _ _ _ _
    _ = m * b.natAbs := by simp

theorem natDegree_upPoly_le (q c : K) (a b e0 : ℤ) (m : ℕ) :
    (upPoly q c a b e0 m).natDegree ≤ m * b.natAbs := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ t ∈ range m, (fpoly q c a b (e0 + t + 1)).natDegree ≤ ∑ _t ∈ range m, b.natAbs :=
        sum_le_sum fun t _ => natDegree_fpoly_le _ _ _ _ _
    _ = m * b.natAbs := by simp

/-! ### The factor of a numerator `Q(a n + b k, c)` -/

/-- Number of linear factors contributed by a numerator factor at the shift `(i, j)`. -/
def numNf (a b : ℤ) (I J i j : ℕ) : ℕ :=
  if 0 ≤ a * j + b * i then Celine.numA a b I J - (a * j + b * i).toNat
  else (a * j + b * i).natAbs + Celine.numA a b I J

theorem numNf_le (a b : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    numNf a b I J i j ≤ a.natAbs * J + b.natAbs * I := by
  have hA : (Celine.numA a b I J : ℤ) ≤ (a.natAbs * J + b.natAbs * I : ℕ) := by
    unfold Celine.numA
    rw [Int.toNat_of_nonneg (by positivity)]
    push_cast
    have h1 : max a 0 * J ≤ |a| * J :=
      mul_le_mul_of_nonneg_right (max_le (le_abs_self a) (abs_nonneg a)) (by positivity)
    have h2 : max b 0 * I ≤ |b| * I :=
      mul_le_mul_of_nonneg_right (max_le (le_abs_self b) (abs_nonneg b)) (by positivity)
    linarith
  unfold numNf
  split_ifs with hs
  · omega
  · have key : ((a * j + b * i).natAbs : ℤ) + Celine.numA a b I J ≤
        (a.natAbs * J + b.natAbs * I : ℕ) := by
      unfold Celine.numA
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

/-- The polynomial `E` contributed by a numerator factor `Q(a n + b k, c)` at the shift `(i,j)`:
`Q^{b⁻ (M - nf)}` times the products of the factors `fpoly`. -/
def numE (q c : K) (a b : ℤ) (I J i j : ℕ) : K[X][X] :=
  X ^ ((max (-b) 0).toNat * (a.natAbs * J + b.natAbs * I - numNf a b I J i j)) *
    if 0 ≤ a * j + b * i then
      dnPoly q c a b (-(a * j + b * i)) (Celine.numA a b I J - (a * j + b * i).toNat)
    else upPoly q c a b 0 (a * j + b * i).natAbs * dnPoly q c a b 0 (Celine.numA a b I J)

/-- The ratio of the numerator factor after clearing the common factor `∏_{t<A}(1 - c q^{y-t})`. -/
def trueNum (q c : K) (a b : ℤ) (I J i j : ℕ) (n k : ℤ) : K :=
  if 0 ≤ a * j + b * i then
    dnVal q c (a * n + b * k - (a * j + b * i)) (Celine.numA a b I J - (a * j + b * i).toNat)
  else upVal q c (a * n + b * k) (a * j + b * i).natAbs * dnVal q c (a * n + b * k)
    (Celine.numA a b I J)

theorem evalEval_numE (q c : K) (hq : q ≠ 0) (a b : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J)
    (n k : ℤ) :
    (numE q c a b I J i j).evalEval (q ^ n) (q ^ k) =
      q ^ (k * (max (-b) 0 * (a.natAbs * J + b.natAbs * I : ℕ)) +
        n * ((numNf a b I J i j : ℕ) * max (-a) 0)) * trueNum q c a b I J i j n k := by
  have hle := numNf_le a b hi hj
  unfold numE trueNum
  rw [evalEval_mul, evalEval_pow, evalEval_X, ← zpow_natCast, ← zpow_mul]
  have hb : ((max (-b) 0).toNat : ℤ) = max (-b) 0 := Int.toNat_of_nonneg (le_max_right _ _)
  split_ifs with hs
  · rw [evalEval_dnPoly q c hq, ← mul_assoc, ← zpow_add₀ hq]
    have hnf : numNf a b I J i j = Celine.numA a b I J - (a * j + b * i).toNat := by
      simp [numNf, hs]
    congr 2
    rw [hnf] at hle ⊢
    push_cast [hle, hb]
    ring
  · rw [evalEval_mul, evalEval_upPoly q c hq, evalEval_dnPoly q c hq, add_zero, qcomb q hq]
    have hnf : numNf a b I J i j = (a * j + b * i).natAbs + Celine.numA a b I J := by
      simp [numNf, hs]
    congr 2
    rw [hnf] at hle ⊢
    push_cast [hle, hb]
    ring

theorem natDegree_numE_le (q c : K) (a b : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    (numE q c a b I J i j).natDegree ≤ b.natAbs * (a.natAbs * J + b.natAbs * I) := by
  have hle := numNf_le a b hi hj
  have hb : (max (-b) 0).toNat ≤ b.natAbs := by omega
  unfold numE
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have key : (if 0 ≤ a * j + b * i then
      dnPoly q c a b (-(a * j + b * i)) (Celine.numA a b I J - (a * j + b * i).toNat)
      else upPoly q c a b 0 (a * j + b * i).natAbs * dnPoly q c a b 0 (Celine.numA a b I J)
      ).natDegree ≤ numNf a b I J i j * b.natAbs := by
    unfold numNf
    split_ifs with hs
    · exact natDegree_dnPoly_le _ _ _ _ _ _
    · refine natDegree_mul_le.trans ?_
      have := natDegree_upPoly_le q c a b 0 (a * j + b * i).natAbs
      have := natDegree_dnPoly_le q c a b 0 (Celine.numA a b I J)
      nlinarith
  have h1 : (max (-b) 0).toNat * (a.natAbs * J + b.natAbs * I - numNf a b I J i j) ≤
      b.natAbs * (a.natAbs * J + b.natAbs * I - numNf a b I J i j) := Nat.mul_le_mul_right _ hb
  have h2 : b.natAbs * (a.natAbs * J + b.natAbs * I - numNf a b I J i j) +
      numNf a b I J i j * b.natAbs = b.natAbs * (a.natAbs * J + b.natAbs * I) := by
    rw [mul_comm (numNf a b I J i j), ← mul_add, Nat.sub_add_cancel hle]
  omega

/-! ### The factor of a denominator `1/Q(u n + v k, w)` -/

/-- Number of linear factors contributed by a denominator factor at the shift `(i, j)`. -/
def denNf (u v : ℤ) (I J i j : ℕ) : ℕ :=
  if 0 ≤ u * j + v * i then (u * j + v * i).toNat + Celine.denU u v I J
  else Celine.denU u v I J - (u * j + v * i).natAbs

theorem denNf_le (u v : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    denNf u v I J i j ≤ u.natAbs * J + v.natAbs * I := by
  have hU : (Celine.denU u v I J : ℤ) ≤ (u.natAbs * J + v.natAbs * I : ℕ) := by
    unfold Celine.denU
    rw [Int.toNat_of_nonneg (by positivity)]
    push_cast
    have h1 : max (-u) 0 * J ≤ |u| * J :=
      mul_le_mul_of_nonneg_right (max_le (neg_le_abs u) (abs_nonneg u)) (by positivity)
    have h2 : max (-v) 0 * I ≤ |v| * I :=
      mul_le_mul_of_nonneg_right (max_le (neg_le_abs v) (abs_nonneg v)) (by positivity)
    linarith
  unfold denNf
  split_ifs with hs
  · have key : ((u * j + v * i).toNat : ℤ) + Celine.denU u v I J ≤
        (u.natAbs * J + v.natAbs * I : ℕ) := by
      unfold Celine.denU
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
  · omega

/-- The polynomial `E` contributed by a denominator factor `1/Q(u n + v k, w)` at the shift `(i,j)`. -/
def denE (q w : K) (u v : ℤ) (I J i j : ℕ) : K[X][X] :=
  X ^ ((max (-v) 0).toNat * (u.natAbs * J + v.natAbs * I - denNf u v I J i j)) *
    if 0 ≤ u * j + v * i then
      dnPoly q w u v 0 (u * j + v * i).toNat * upPoly q w u v 0 (Celine.denU u v I J)
    else upPoly q w u v (-(u * j + v * i)) (Celine.denU u v I J - (u * j + v * i).natAbs)

/-- The ratio of the denominator factor after clearing the common factor
`∏_{t<U}(1 - w q^{y+t+1})`. -/
def trueDen (q w : K) (u v : ℤ) (I J i j : ℕ) (n k : ℤ) : K :=
  if 0 ≤ u * j + v * i then
    dnVal q w (u * n + v * k) (u * j + v * i).toNat * upVal q w (u * n + v * k) (Celine.denU u v I J)
  else upVal q w (u * n + v * k - (u * j + v * i)) (Celine.denU u v I J - (u * j + v * i).natAbs)

theorem evalEval_denE (q w : K) (hq : q ≠ 0) (u v : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J)
    (n k : ℤ) :
    (denE q w u v I J i j).evalEval (q ^ n) (q ^ k) =
      q ^ (k * (max (-v) 0 * (u.natAbs * J + v.natAbs * I : ℕ)) +
        n * ((denNf u v I J i j : ℕ) * max (-u) 0)) * trueDen q w u v I J i j n k := by
  have hle := denNf_le u v hi hj
  unfold denE trueDen
  rw [evalEval_mul, evalEval_pow, evalEval_X, ← zpow_natCast, ← zpow_mul]
  have hb : ((max (-v) 0).toNat : ℤ) = max (-v) 0 := Int.toNat_of_nonneg (le_max_right _ _)
  split_ifs with hs
  · rw [evalEval_mul, evalEval_dnPoly q w hq, evalEval_upPoly q w hq, add_zero, qcomb q hq]
    have hnf : denNf u v I J i j = (u * j + v * i).toNat + Celine.denU u v I J := by
      simp [denNf, hs]
    congr 2
    rw [hnf] at hle ⊢
    push_cast [hle, hb]
    ring
  · rw [evalEval_upPoly q w hq, ← mul_assoc, ← zpow_add₀ hq]
    have hnf : denNf u v I J i j = Celine.denU u v I J - (u * j + v * i).natAbs := by
      simp [denNf, hs]
    congr 2
    rw [hnf] at hle ⊢
    push_cast [hle, hb]
    ring

theorem natDegree_denE_le (q w : K) (u v : ℤ) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    (denE q w u v I J i j).natDegree ≤ v.natAbs * (u.natAbs * J + v.natAbs * I) := by
  have hle := denNf_le u v hi hj
  have hb : (max (-v) 0).toNat ≤ v.natAbs := by omega
  unfold denE
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have key : (if 0 ≤ u * j + v * i then
      dnPoly q w u v 0 (u * j + v * i).toNat * upPoly q w u v 0 (Celine.denU u v I J)
      else upPoly q w u v (-(u * j + v * i)) (Celine.denU u v I J - (u * j + v * i).natAbs)
      ).natDegree ≤ denNf u v I J i j * v.natAbs := by
    unfold denNf
    split_ifs with hs
    · refine natDegree_mul_le.trans ?_
      have := natDegree_dnPoly_le q w u v 0 (u * j + v * i).toNat
      have := natDegree_upPoly_le q w u v 0 (Celine.denU u v I J)
      nlinarith
    · exact natDegree_upPoly_le _ _ _ _ _ _
  have h1 : (max (-v) 0).toNat * (u.natAbs * J + v.natAbs * I - denNf u v I J i j) ≤
      v.natAbs * (u.natAbs * J + v.natAbs * I - denNf u v I J i j) := Nat.mul_le_mul_right _ hb
  have h2 : v.natAbs * (u.natAbs * J + v.natAbs * I - denNf u v I J i j) +
      denNf u v I J i j * v.natAbs = v.natAbs * (u.natAbs * J + v.natAbs * I) := by
    rw [mul_comm (denNf u v I J i j), ← mul_add, Nat.sub_add_cancel hle]
  omega

/-! ### Assembling the polynomials `E_{ij}` -/

/-- A q-proper term is *defined* at `(n,k)` if all arguments are nonnegative and no denominator
factor vanishes. -/
def IsDefinedAt (D : QProperData K) (q : K) (n k : ℤ) : Prop :=
  (∀ s, 0 ≤ D.a s * n + D.b s * k) ∧ (∀ s, 0 ≤ D.u s * n + D.v s * k) ∧
    ∀ s, qFac q (D.w s) (D.u s * n + D.v s * k).toNat ≠ 0

/-- The exponent of `q^k` coming from `q^{β n k + γ k²}` at the shift `(i, j)`, made nonnegative. -/
def expQ (D : QProperData K) (I J i j : ℕ) : ℤ :=
  max D.β 0 * J + 2 * max D.γ 0 * I - D.β * j - 2 * D.γ * i

theorem expQ_nonneg (D : QProperData K) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    0 ≤ expQ D I J i j := by
  unfold expQ
  have h1 : D.β * j ≤ max D.β 0 * J := by
    rcases le_or_gt 0 D.β with h | h
    · rw [max_eq_left h]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) h
    · rw [max_eq_right h.le]; nlinarith
  have h2 : D.γ * i ≤ max D.γ 0 * I := by
    rcases le_or_gt 0 D.γ with h | h
    · rw [max_eq_left h]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi) h
    · rw [max_eq_right h.le]; nlinarith
  linarith

/-- The polynomial `E_{ij}(N, Q)` (`N = q^n`, `Q = q^k`). -/
def qE (D : QProperData K) (q : K) (I J i j : ℕ) : K[X][X] :=
  X ^ (expQ D I J i j).toNat * (∏ s, numE q (D.c s) (D.a s) (D.b s) I J i j) *
    ∏ s, denE q (D.w s) (D.u s) (D.v s) I J i j

/-- The bound for the degrees in `Q = q^k`: `I (2|γ| + ∑ b_s² + ∑ v_s²) + J (|β| + ∑ |a_s b_s| + ∑ |u_s v_s|)`. -/
def degB (D : QProperData K) (I J : ℕ) : ℕ :=
  (D.β.natAbs * J + 2 * D.γ.natAbs * I) +
    ∑ s, (D.b s).natAbs * ((D.a s).natAbs * J + (D.b s).natAbs * I) +
    ∑ s, (D.v s).natAbs * ((D.u s).natAbs * J + (D.v s).natAbs * I)

theorem natDegree_qE_le (D : QProperData K) (q : K) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    (qE D q I J i j).natDegree ≤ degB D I J := by
  unfold qE degB
  refine natDegree_mul_le.trans ?_
  have h1 := natDegree_mul_le (p := (X : K[X][X]) ^ (expQ D I J i j).toNat)
    (q := ∏ s, numE q (D.c s) (D.a s) (D.b s) I J i j)
  rw [natDegree_X_pow] at h1
  have h2 : (∏ s, numE q (D.c s) (D.a s) (D.b s) I J i j).natDegree ≤
      ∑ s, (D.b s).natAbs * ((D.a s).natAbs * J + (D.b s).natAbs * I) :=
    (natDegree_prod_le _ _).trans (sum_le_sum fun s _ => natDegree_numE_le _ _ _ _ hi hj)
  have h3 : (∏ s, denE q (D.w s) (D.u s) (D.v s) I J i j).natDegree ≤
      ∑ s, (D.v s).natAbs * ((D.u s).natAbs * J + (D.v s).natAbs * I) :=
    (natDegree_prod_le _ _).trans (sum_le_sum fun s _ => natDegree_denE_le _ _ _ _ hi hj)
  have h4 : (expQ D I J i j).toNat ≤ D.β.natAbs * J + 2 * D.γ.natAbs * I := by
    rw [Int.toNat_le]
    push_cast
    unfold expQ
    have hb : max D.β 0 * (J : ℤ) - D.β * j ≤ (D.β.natAbs : ℤ) * J := by
      rcases le_or_gt 0 D.β with h | h
      · rw [max_eq_left h, Int.natCast_natAbs, abs_of_nonneg h]
        have : (0 : ℤ) ≤ D.β * j := mul_nonneg h (Nat.cast_nonneg j)
        linarith
      · rw [max_eq_right h.le, Int.natCast_natAbs, abs_of_neg h]
        have : D.β * j ≥ D.β * J := by nlinarith
        nlinarith
    have hg : 2 * max D.γ 0 * (I : ℤ) - 2 * D.γ * i ≤ 2 * (D.γ.natAbs : ℤ) * I := by
      rcases le_or_gt 0 D.γ with h | h
      · rw [max_eq_left h, Int.natCast_natAbs, abs_of_nonneg h]
        have : (0 : ℤ) ≤ D.γ * i := mul_nonneg h (Nat.cast_nonneg i)
        linarith
      · rw [max_eq_right h.le, Int.natCast_natAbs, abs_of_neg h]
        have : D.γ * i ≥ D.γ * I := by nlinarith
        nlinarith
    simp only [Int.natCast_natAbs] at hb hg
    linarith
  omega

/-! ### The value identity -/

/-- The common factor `Δ(n,k) = ∏ ∏_{t<A_s}(1 - c_s q^{y_s - t}) · ∏ ∏_{t<U_s}(1 - w_s q^{y'_s + t + 1})`. -/
def deltaQ (D : QProperData K) (q : K) (I J : ℕ) (n k : ℤ) : K :=
  (∏ s, dnVal q (D.c s) (D.a s * n + D.b s * k) (Celine.numA (D.a s) (D.b s) I J)) *
    ∏ s, upVal q (D.w s) (D.u s * n + D.v s * k) (Celine.denU (D.u s) (D.v s) I J)

/-- The uniform power `T` of `q^k` used to clear negative powers of `q^k`. -/
def tExp (D : QProperData K) (I J : ℕ) : ℤ :=
  max D.β 0 * J + 2 * max D.γ 0 * I +
    ∑ s, max (-D.b s) 0 * (((D.a s).natAbs * J + (D.b s).natAbs * I : ℕ) : ℤ) +
    ∑ s, max (-D.v s) 0 * (((D.u s).natAbs * J + (D.v s).natAbs * I : ℕ) : ℤ)

/-- The value `H(n,k) = ∏ Q(y_s, c_s) / ∏ Q(y'_s, w_s) · q^{quadratic} ξ^k` of `F(n,k)`. -/
def hQ (D : QProperData K) (q : K) (n k : ℤ) : K :=
  (∏ s, qFac q (D.c s) (D.a s * n + D.b s * k).toNat) /
      (∏ s, qFac q (D.w s) (D.u s * n + D.v s * k).toNat) *
    q ^ (D.α * n ^ 2 + D.β * n * k + D.γ * k ^ 2 + D.δ * k + D.ε * n) * D.ξ ^ k

/-- The constant `κ_{ij} = ξ^{-i} q^{α j² + β i j + γ i² - δ i - ε j}`. -/
def kappa (D : QProperData K) (q : K) (i j : ℕ) : K :=
  D.ξ ^ (-(i : ℤ)) * q ^ (D.α * j ^ 2 + D.β * i * j + D.γ * i ^ 2 - D.δ * i - D.ε * j)

/-- The power `ν_{ij}` of `q^n`. -/
def nu (D : QProperData K) (I J i j : ℕ) : ℤ :=
  -2 * D.α * j - D.β * i - ∑ s, ((numNf (D.a s) (D.b s) I J i j : ℕ) : ℤ) * max (-D.a s) 0 -
    ∑ s, ((denNf (D.u s) (D.v s) I J i j : ℕ) : ℤ) * max (-D.u s) 0

/-- The value identity: `F(n-j, k-i) Δ(n,k) q^{kT} = κ_{ij} q^{n ν_{ij}} H(n,k) E_{ij}(q^n, q^k)`. -/
theorem eval_shift_mul (D : QProperData K) (q : K) (hq : q ≠ 0) (hξ : D.ξ ≠ 0) {I J i j : ℕ}
    (hi : i ≤ I) (hj : j ≤ J) (n k : ℤ) (h0 : IsDefinedAt D q n k)
    (h1 : IsDefinedAt D q (n - j) (k - i)) :
    D.eval q (n - j) (k - i) * deltaQ D q I J n k * q ^ (k * tExp D I J) =
      kappa D q i j * q ^ (n * nu D I J i j) * hQ D q n k *
        (qE D q I J i j).evalEval (q ^ n) (q ^ k) := by
  have hnum : (∏ s, qFac q (D.c s) (D.a s * (n - j) + D.b s * (k - i)).toNat) *
      (∏ s, dnVal q (D.c s) (D.a s * n + D.b s * k) (Celine.numA (D.a s) (D.b s) I J)) =
      (∏ s, qFac q (D.c s) (D.a s * n + D.b s * k).toNat) *
        ∏ s, trueNum q (D.c s) (D.a s) (D.b s) I J i j n k := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun s _ => ?_
    have e : D.a s * (n - j) + D.b s * (k - i) =
        (D.a s * n + D.b s * k) - (D.a s * j + D.b s * i) := by ring
    have := h1.1 s
    rw [e] at this ⊢
    exact num_ratio q (D.c s) _ _ _ (h0.1 s) this (Celine.le_numA _ _ hi hj)
  have hden : (∏ s, qFac q (D.w s) (D.u s * (n - j) + D.v s * (k - i)).toNat)⁻¹ *
      (∏ s, upVal q (D.w s) (D.u s * n + D.v s * k) (Celine.denU (D.u s) (D.v s) I J)) =
      (∏ s, qFac q (D.w s) (D.u s * n + D.v s * k).toNat)⁻¹ *
        ∏ s, trueDen q (D.w s) (D.u s) (D.v s) I J i j n k := by
    rw [← prod_inv_distrib, ← prod_inv_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun s _ => ?_
    have e : D.u s * (n - j) + D.v s * (k - i) =
        (D.u s * n + D.v s * k) - (D.u s * j + D.v s * i) := by ring
    have hs1 := h1.2.1 s
    have hs2 := h1.2.2 s
    rw [e] at hs1 hs2 ⊢
    exact den_ratio q (D.w s) _ _ _ (h0.2.1 s) hs1 (Celine.neg_le_denU _ _ hi hj) (h0.2.2 s) hs2
  have hE : (qE D q I J i j).evalEval (q ^ n) (q ^ k) =
      q ^ (k * expQ D I J i j +
        ∑ s, (k * (max (-D.b s) 0 * (((D.a s).natAbs * J + (D.b s).natAbs * I : ℕ) : ℤ)) +
          n * ((numNf (D.a s) (D.b s) I J i j : ℕ) * max (-D.a s) 0)) +
        ∑ s, (k * (max (-D.v s) 0 * (((D.u s).natAbs * J + (D.v s).natAbs * I : ℕ) : ℤ)) +
          n * ((denNf (D.u s) (D.v s) I J i j : ℕ) * max (-D.u s) 0))) *
      ((∏ s, trueNum q (D.c s) (D.a s) (D.b s) I J i j n k) *
        ∏ s, trueDen q (D.w s) (D.u s) (D.v s) I J i j n k) := by
    unfold qE
    rw [evalEval_mul, evalEval_mul, evalEval_prod, evalEval_prod, evalEval_pow, evalEval_X,
      zpow_toNat_pow q k _ (expQ_nonneg D hi hj)]
    simp only [evalEval_numE q _ hq _ _ hi hj, evalEval_denE q _ hq _ _ hi hj]
    rw [prod_mul_distrib, prod_mul_distrib, prod_zpow_eq q hq, prod_zpow_eq q hq,
      zpow_add₀ hq, zpow_add₀ hq]
    ring
  have hexp : D.α * (n - j) ^ 2 + D.β * (n - j) * (k - i) + D.γ * (k - i) ^ 2 + D.δ * (k - i) +
      D.ε * (n - j) + k * tExp D I J =
      (D.α * j ^ 2 + D.β * i * j + D.γ * i ^ 2 - D.δ * i - D.ε * j) + n * nu D I J i j +
        (D.α * n ^ 2 + D.β * n * k + D.γ * k ^ 2 + D.δ * k + D.ε * n) +
        (k * expQ D I J i j +
          ∑ s, (k * (max (-D.b s) 0 * (((D.a s).natAbs * J + (D.b s).natAbs * I : ℕ) : ℤ)) +
            n * ((numNf (D.a s) (D.b s) I J i j : ℕ) * max (-D.a s) 0)) +
          ∑ s, (k * (max (-D.v s) 0 * (((D.u s).natAbs * J + (D.v s).natAbs * I : ℕ) : ℤ)) +
            n * ((denNf (D.u s) (D.v s) I J i j : ℕ) * max (-D.u s) 0))) := by
    unfold tExp nu expQ
    simp only [sum_add_distrib, ← mul_sum]
    ring
  unfold QProperData.eval deltaQ hQ kappa
  rw [hE]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc _ = ((∏ s, qFac q (D.c s) (D.a s * (n - j) + D.b s * (k - i)).toNat) *
        (∏ s, dnVal q (D.c s) (D.a s * n + D.b s * k) (Celine.numA (D.a s) (D.b s) I J))) *
      ((∏ s, qFac q (D.w s) (D.u s * (n - j) + D.v s * (k - i)).toNat)⁻¹ *
        (∏ s, upVal q (D.w s) (D.u s * n + D.v s * k) (Celine.denU (D.u s) (D.v s) I J))) *
      (q ^ (D.α * (n - j) ^ 2 + D.β * (n - j) * (k - i) + D.γ * (k - i) ^ 2 + D.δ * (k - i) +
        D.ε * (n - j)) * q ^ (k * tExp D I J)) * D.ξ ^ (k - i) := by ring
    _ = _ := by
      rw [hnum, hden, ← zpow_add₀ hq, hexp, zpow_add₀ hq, zpow_add₀ hq, zpow_add₀ hq,
        show k - (i : ℤ) = -(i : ℤ) + k by ring, zpow_add₀ hξ]
      ring

/-! ### Nonvanishing of the common factor -/

theorem deltaQ_ne_zero (D : QProperData K) (q : K) {I J : ℕ} {n k : ℤ}
    (hF : D.eval q n k ≠ 0) (hwd : ∀ i ≤ I, ∀ j ≤ J, IsDefinedAt D q (n - j) (k - i)) :
    deltaQ D q I J n k ≠ 0 := by
  have h0 : IsDefinedAt D q n k := by simpa using hwd 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  have hnum : ∀ s, qFac q (D.c s) (D.a s * n + D.b s * k).toNat ≠ 0 := by
    intro s hs
    apply hF
    unfold QProperData.eval
    rw [prod_eq_zero (mem_univ s) hs]
    simp
  unfold deltaQ
  refine mul_ne_zero (prod_ne_zero_iff.2 fun s _ => ?_) (prod_ne_zero_iff.2 fun s _ => ?_)
  · set a := D.a s
    set b := D.b s
    have hc := (hwd (if 0 < b then I else 0) (by split_ifs <;> omega)
      (if 0 < a then J else 0) (by split_ifs <;> omega)).1 s
    have hcorner : a * ((if 0 < a then J else 0 : ℕ) : ℤ) + b * ((if 0 < b then I else 0 : ℕ) : ℤ)
        = max a 0 * J + max b 0 * I := by
      rcases le_or_gt a 0 with ha | ha <;> rcases le_or_gt b 0 with hb | hb
      · simp [not_lt.2 ha, not_lt.2 hb, max_eq_right ha, max_eq_right hb]
      · simp [not_lt.2 ha, hb, max_eq_right ha, max_eq_left hb.le]
      · simp [ha, not_lt.2 hb, max_eq_left ha.le, max_eq_right hb]
      · simp [ha, hb, max_eq_left ha.le, max_eq_left hb.le]
    have hA : (Celine.numA a b I J : ℤ) ≤ a * n + b * k := by
      unfold Celine.numA
      rw [Int.toNat_of_nonneg (by positivity), ← hcorner]
      have : a * (n - ((if 0 < a then J else 0 : ℕ) : ℤ)) +
          b * (k - ((if 0 < b then I else 0 : ℕ) : ℤ)) ≥ 0 := hc
      linarith
    have hy := h0.1 s
    have h1 := qFac_eq_mul_dnVal q (D.c s) (a * n + b * k).toNat (Celine.numA a b I J) (by omega)
    rw [Int.toNat_of_nonneg hy] at h1
    intro h
    rw [h, mul_zero] at h1
    exact hnum s h1
  · set u := D.u s
    set v := D.v s
    have hc := hwd (if v < 0 then I else 0) (by split_ifs <;> omega)
      (if u < 0 then J else 0) (by split_ifs <;> omega)
    have hcorner : u * ((if u < 0 then J else 0 : ℕ) : ℤ) + v * ((if v < 0 then I else 0 : ℕ) : ℤ)
        = -(max (-u) 0 * J + max (-v) 0 * I) := by
      rcases le_or_gt 0 u with ha | ha <;> rcases le_or_gt 0 v with hb | hb
      · simp [not_lt.2 ha, not_lt.2 hb, max_eq_right (neg_nonpos.2 ha),
          max_eq_right (neg_nonpos.2 hb)]
      · simp [not_lt.2 ha, hb, max_eq_right (neg_nonpos.2 ha), max_eq_left (neg_nonneg.2 hb.le)]
      · simp [ha, not_lt.2 hb, max_eq_left (neg_nonneg.2 ha.le), max_eq_right (neg_nonpos.2 hb)]
      · simp [ha, hb, max_eq_left (neg_nonneg.2 ha.le), max_eq_left (neg_nonneg.2 hb.le)]; ring
    have hU : u * (n - ((if u < 0 then J else 0 : ℕ) : ℤ)) +
        v * (k - ((if v < 0 then I else 0 : ℕ) : ℤ)) =
        (u * n + v * k) + Celine.denU u v I J := by
      unfold Celine.denU
      rw [Int.toNat_of_nonneg (by positivity)]
      linear_combination -hcorner
    have hq2 := hc.2.2 s
    have hy := h0.2.1 s
    simp only [u, v] at hU hq2
    rw [hU] at hq2
    have h1 := qFac_add q (D.w s) (D.u s * n + D.v s * k).toNat (Celine.denU (D.u s) (D.v s) I J)
    rw [show (D.u s * n + D.v s * k + (Celine.denU (D.u s) (D.v s) I J : ℤ)).toNat =
      (D.u s * n + D.v s * k).toNat + Celine.denU (D.u s) (D.v s) I J by omega] at hq2
    rw [h1, Int.toNat_of_nonneg hy] at hq2
    exact right_ne_zero_of_mul hq2

/-! ### The theorem -/

/-- The order bound `J* = ∑ b_s² + ∑ v_s² + 2|γ|` of Theorem 4.5.2. -/
def qJStar (D : QProperData K) : ℕ :=
  ∑ s, (D.b s).natAbs ^ 2 + ∑ s, (D.v s).natAbs ^ 2 + 2 * D.γ.natAbs

/-- The `J`-slope `A₂ = |β| + ∑ |a_s b_s| + ∑ |u_s v_s|` of the degree bound. -/
def qA2 (D : QProperData K) : ℕ :=
  D.β.natAbs + ∑ s, (D.a s).natAbs * (D.b s).natAbs + ∑ s, (D.u s).natAbs * (D.v s).natAbs

theorem degB_eq (D : QProperData K) (I J : ℕ) : degB D I J = I * qJStar D + J * qA2 D := by
  have e1 : ∑ s, (D.b s).natAbs * ((D.a s).natAbs * J + (D.b s).natAbs * I) =
      I * ∑ s, (D.b s).natAbs ^ 2 + J * ∑ s, (D.a s).natAbs * (D.b s).natAbs := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun s _ => by ring
  have e2 : ∑ s, (D.v s).natAbs * ((D.u s).natAbs * J + (D.v s).natAbs * I) =
      I * ∑ s, (D.v s).natAbs ^ 2 + J * ∑ s, (D.u s).natAbs * (D.v s).natAbs := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun s _ => by ring
  unfold degB qJStar qA2
  rw [e1, e2]
  ring

/-- The `N = q^n`-exponent bound making all coefficients polynomials in `q^n`. -/
def nBound (D : QProperData K) (I J : ℕ) : ℤ := 2 * |D.α| * J + |D.β| * I

theorem nu_le (D : QProperData K) {I J i j : ℕ} (hi : i ≤ I) (hj : j ≤ J) :
    nu D I J i j ≤ nBound D I J := by
  unfold nu nBound
  have h1 : (0 : ℤ) ≤ ∑ s, ((numNf (D.a s) (D.b s) I J i j : ℕ) : ℤ) * max (-D.a s) 0 :=
    sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  have h2 : (0 : ℤ) ≤ ∑ s, ((denNf (D.u s) (D.v s) I J i j : ℕ) : ℤ) * max (-D.u s) 0 :=
    sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  have h3 : -2 * D.α * j ≤ 2 * |D.α| * J := by
    have : -D.α ≤ |D.α| := neg_le_abs _
    have : (j : ℤ) ≤ J := by exact_mod_cast hj
    nlinarith [abs_nonneg D.α]
  have h4 : -D.β * i ≤ |D.β| * I := by
    have : -D.β ≤ |D.β| := neg_le_abs _
    have : (i : ℤ) ≤ I := by exact_mod_cast hi
    nlinarith [abs_nonneg D.β]
  linarith

/-- CO-394. **q-version of the Fundamental Theorem** (Theorem 4.5.2). Let `F` be a q-proper
hypergeometric term (4.5.5) with `q ≠ 0`, `ξ ≠ 0`. Then `F` satisfies a nontrivial `k`-free
recurrence `∑_{i ≤ I, j ≤ J} α_{ij}(q^n) F(n-j, k-i) = 0` whose order in `n` is
`J = ∑ b_s² + ∑ v_s² + 2|γ|`, with polynomial coefficients `α_{ij}` in `q^n`, not all zero, valid at
every point where `F(n,k) ≠ 0` and all values of `F` in the recurrence are defined. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.5.2, p. 81"]
theorem q_fundamental_theorem (D : QProperData K) (q : K) (hq : q ≠ 0) (hξ : D.ξ ≠ 0) :
    ∃ I : ℕ, ∃ α : Fin (I + 1) × Fin (qJStar D + 1) → K[X], α ≠ 0 ∧
      ∀ n k : ℤ, D.eval q n k ≠ 0 →
        (∀ i ≤ I, ∀ j ≤ qJStar D, IsDefinedAt D q (n - j) (k - i)) →
        ∑ p : Fin (I + 1) × Fin (qJStar D + 1), (α p).eval (q ^ n) *
          D.eval q (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) = 0 := by
  classical
  set J := qJStar D
  set I := J * qA2 D + 1
  have hcount : degB D I J + 1 < Fintype.card (Fin (I + 1) × Fin (J + 1)) := by
    rw [degB_eq, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    change I * J + J * qA2 D + 1 < (I + 1) * (J + 1)
    simp only [I]
    ring_nf
    omega
  obtain ⟨b, hb0, hb⟩ := Celine.exists_ne_zero_sum_C_mul_eq_zero
    (fun p : Fin (I + 1) × Fin (J + 1) => qE D q I J p.1 p.2) (degB D I J)
    (fun p => natDegree_qE_le D q (Nat.lt_succ_iff.1 p.1.2) (Nat.lt_succ_iff.1 p.2.2)) hcount
  have hkappa : ∀ i j : ℕ, kappa D q i j ≠ 0 := fun i j =>
    mul_ne_zero (zpow_ne_zero _ hξ) (zpow_ne_zero _ hq)
  refine ⟨I, fun p => b p * C (kappa D q p.1 p.2)⁻¹ *
    X ^ (nBound D I J - nu D I J p.1 p.2).toNat, ?_, ?_⟩
  · intro h
    apply hb0
    funext p
    have := congrFun h p
    simp only [Pi.zero_apply, mul_eq_zero, C_eq_zero, inv_eq_zero, pow_eq_zero_iff', X_ne_zero,
      false_and, or_false] at this
    exact this.resolve_right (hkappa _ _)
  · intro n k hF hwd
    have h0 : IsDefinedAt D q n k := by simpa using hwd 0 (Nat.zero_le _) 0 (Nat.zero_le _)
    have hΔ := deltaQ_ne_zero D q hF hwd
    have hb' := congrArg (fun P => P.evalEval (q ^ n) (q ^ k)) hb
    simp only [evalEval_finsetSum, evalEval_mul, evalEval_C, evalEval_zero] at hb'
    refine (mul_left_inj' (mul_ne_zero hΔ (zpow_ne_zero (k * tExp D I J) hq))).1 ?_
    rw [zero_mul, sum_mul]
    calc ∑ p : Fin (I + 1) × Fin (J + 1),
          (b p * C (kappa D q p.1 p.2)⁻¹ * X ^ (nBound D I J - nu D I J p.1 p.2).toNat).eval (q ^ n) *
            D.eval q (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) * (deltaQ D q I J n k * q ^ (k * tExp D I J))
        = ∑ p : Fin (I + 1) × Fin (J + 1), q ^ (n * nBound D I J) * hQ D q n k *
            ((b p).eval (q ^ n) * (qE D q I J p.1 p.2).evalEval (q ^ n) (q ^ k)) := by
          refine sum_congr rfl fun p _ => ?_
          have hip := Nat.lt_succ_iff.1 p.1.2
          have hjp := Nat.lt_succ_iff.1 p.2.2
          have key := eval_shift_mul D q hq hξ hip hjp n k h0 (hwd _ hip _ hjp)
          have hpow : (q ^ n) ^ (nBound D I J - nu D I J p.1 p.2).toNat * q ^ (n * nu D I J p.1 p.2)
              = q ^ (n * nBound D I J) := by
            rw [zpow_toNat_pow q n _ (by linarith [nu_le D hip hjp]), ← zpow_add₀ hq]
            ring_nf
          rw [eval_mul, eval_mul, eval_C, eval_pow, eval_X]
          calc (b p).eval (q ^ n) * (kappa D q p.1 p.2)⁻¹ *
                (q ^ n) ^ (nBound D I J - nu D I J p.1 p.2).toNat *
                D.eval q (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) * (deltaQ D q I J n k * q ^ (k * tExp D I J))
              = (b p).eval (q ^ n) * (kappa D q p.1 p.2)⁻¹ *
                (q ^ n) ^ (nBound D I J - nu D I J p.1 p.2).toNat *
                (D.eval q (n - (p.2 : ℕ)) (k - (p.1 : ℕ)) * deltaQ D q I J n k *
                  q ^ (k * tExp D I J)) := by ring
            _ = (b p).eval (q ^ n) * ((kappa D q p.1 p.2)⁻¹ * kappa D q p.1 p.2) *
                ((q ^ n) ^ (nBound D I J - nu D I J p.1 p.2).toNat * q ^ (n * nu D I J p.1 p.2)) *
                hQ D q n k * (qE D q I J p.1 p.2).evalEval (q ^ n) (q ^ k) := by rw [key]; ring
            _ = _ := by rw [inv_mul_cancel₀ (hkappa _ _), hpow]; ring
      _ = 0 := by
          rw [← mul_sum]
          convert mul_zero (q ^ (n * nBound D I J) * hQ D q n k)

end QFundamental

end UndergradKB.Combinatorics.AeqB
