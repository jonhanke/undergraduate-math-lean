import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import UndergradKB.Combinatorics.AeqB.Celine
import UndergradKB.Common.Attr

/-!
# Sister Celine's method for several summation variables (A = B, Theorem 4.5.1)

A proper hypergeometric term in `r` summation variables
`F(n, k) = P(n, k) ∏_s (a_s n + b_s·k + c_s)! / ∏_s (u_s n + v_s·k + w_s)! · z^k` satisfies a nontrivial
`k`-free recurrence `∑_{j ≤ J} ∑_{i ∈ [0,I]^r} α(i,j,n) F(n-j, k-i) = 0`.  We adapt the one-variable
proof of `Celine.lean`: the polynomials `Q_{ij}` live in `MvPolynomial (Fin r) K[X]` (coefficients
polynomials in `n`), and the linear algebra counts exponent vectors of total degree `≤ D`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB

namespace CelineMulti

open Finset Celine

/-! ### Linear algebra: more unknowns than coefficient slots -/

/-- If `Q_p` (`p ∈ ι`) are polynomials in `r` variables over a domain of total degree `≤ D` and
`(D+1)^r < |ι|`, some nontrivial combination `∑ C(b_p) Q_p` vanishes. -/
theorem exists_ne_zero_sum_C_mul_eq_zero_mv {R : Type*} [CommRing R] [IsDomain R] {r : ℕ}
    {ι : Type*} [Fintype ι] (Q : ι → MvPolynomial (Fin r) R) (D : ℕ)
    (hQ : ∀ p, (Q p).totalDegree ≤ D) (hcard : (D + 1) ^ r < Fintype.card ι) :
    ∃ b : ι → R, b ≠ 0 ∧ ∑ p, MvPolynomial.C (b p) * Q p = 0 := by
  classical
  let toF : (Fin r → Fin (D + 1)) → (Fin r →₀ ℕ) := fun e =>
    Finsupp.equivFunOnFinite.symm (fun t => (e t : ℕ))
  let L : (ι → R) →ₗ[R] ((Fin r → Fin (D + 1)) → R) :=
    { toFun := fun b e => ∑ p, b p * (Q p).coeff (toF e)
      map_add' := by intro b b'; ext e; simp [add_mul, sum_add_distrib]
      map_smul' := by intro c b; ext e; simp [mul_assoc, mul_sum] }
  have hni : ¬ Function.Injective L := by
    intro hinj
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin] at this
    omega
  rw [injective_iff_map_eq_zero] at hni
  push_neg at hni
  obtain ⟨b, hb, hb0⟩ := hni
  refine ⟨b, hb0, ?_⟩
  ext m
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero]
  simp only [MvPolynomial.coeff_C_mul]
  by_cases hm : ∀ t, m t < D + 1
  · let e : Fin r → Fin (D + 1) := fun t => ⟨m t, hm t⟩
    have he : toF e = m := by ext t; simp [toF, e]
    have := congrFun hb e
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, he] at this
    exact this
  · push_neg at hm
    obtain ⟨t, ht⟩ := hm
    refine sum_eq_zero fun p _ => ?_
    have : (Q p).coeff m = 0 := by
      refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
      have h1 : m t ≤ ∑ i ∈ m.support, m i :=
        Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _)
          (Finsupp.mem_support_iff.2 (by omega))
      have := hQ p
      omega
    rw [this, mul_zero]

/-! ### The ring `K[n][k_1,…,k_r]` and evaluation -/

variable {K : Type*} [Field K] {r : ℕ}

/-- Polynomials in `k_1..k_r` with coefficients in `K[n]`. -/
abbrev MP (K : Type*) [Field K] (r : ℕ) := MvPolynomial (Fin r) (Polynomial K)

/-- Evaluation at `n` and `k`. -/
def ev (n : K) (k : Fin r → K) : MP K r →+* K :=
  (MvPolynomial.eval k).comp (MvPolynomial.map (Polynomial.evalRingHom n))

@[simp] theorem ev_C (n : K) (k : Fin r → K) (q : Polynomial K) :
    ev n k (MvPolynomial.C q) = q.eval n := by simp [ev]

@[simp] theorem ev_X (n : K) (k : Fin r → K) (t : Fin r) :
    ev n k (MvPolynomial.X t) = k t := by simp [ev]

/-- A constant of `K` as an element of `MP K r`. -/
def cs (q : K) : MP K r := MvPolynomial.C (Polynomial.C q)

@[simp] theorem ev_cs (n : K) (k : Fin r → K) (q : K) : ev n k (cs q) = q := by simp [cs]

theorem totalDegree_cs (q : K) : (cs (r := r) q).totalDegree = 0 := MvPolynomial.totalDegree_C _

theorem totalDegree_cs_le (q : K) : (cs (r := r) q).totalDegree ≤ 1 := by
  rw [totalDegree_cs]; exact Nat.zero_le _

/-- The dot product of two integer vectors. -/
def dot (b k : Fin r → ℤ) : ℤ := ∑ t, b t * k t

/-- `b · i` for a natural vector `i`. -/
def dotN (b : Fin r → ℤ) (i : Fin r → ℕ) : ℤ := dot b (fun t => (i t : ℤ))

theorem dot_sub (b k : Fin r → ℤ) (i : Fin r → ℕ) :
    dot b (fun t => k t - (i t : ℤ)) = dot b k - dotN b i := by
  simp [dot, dotN, mul_sub, sum_sub_distrib]

/-- The linear form `a n + b·k + c` as an element of `MP K r`. -/
def lin (a : ℤ) (b : Fin r → ℤ) (c : ℤ) : MP K r :=
  cs (c : K) + cs (a : K) * MvPolynomial.C Polynomial.X + ∑ t, cs (b t : K) * MvPolynomial.X t

theorem ev_lin (a c n : ℤ) (b k : Fin r → ℤ) :
    ev (n : K) (fun t => (k t : K)) (lin a b c) = ((a * n + dot b k + c : ℤ) : K) := by
  simp only [lin, dot, map_add, ev_cs, map_mul, ev_C, map_sum, ev_X, Polynomial.eval_X]
  push_cast; ring

theorem totalDegree_lin_le (a : ℤ) (b : Fin r → ℤ) (c : ℤ) :
    (lin (K := K) a b c).totalDegree ≤ 1 := by
  unfold lin
  refine (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)) ?_)
  · simp [totalDegree_cs]
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [totalDegree_cs]
  · refine MvPolynomial.totalDegree_finsetSum_le fun t _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [totalDegree_cs]

/-- `ff(A, p) = ∏_{t<A} (p - t)`. -/
def ffPol (A : ℕ) (p : MP K r) : MP K r := ∏ t ∈ range A, (p + cs (r := r) (-(t : K)))

/-- `rf(U, p) = ∏_{t<U} (p + t + 1)`. -/
def rfPol (U : ℕ) (p : MP K r) : MP K r := ∏ t ∈ range U, (p + cs (r := r) ((t : K) + 1))

theorem ev_ffPol (A : ℕ) (p : MP K r) (n : K) (k : Fin r → K) :
    ev n k (ffPol A p) = ffVal A (ev n k p) := by
  simp [ffPol, ffVal, map_prod, sub_eq_add_neg]

theorem ev_rfPol (U : ℕ) (p : MP K r) (n : K) (k : Fin r → K) :
    ev n k (rfPol U p) = rfVal U (ev n k p) := by
  simp [rfPol, rfVal, map_prod]

theorem totalDegree_ffPol_le (A : ℕ) {p : MP K r} (hp : p.totalDegree ≤ 1) :
    (ffPol A p).totalDegree ≤ A := by
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ t ∈ range A, (p + cs (r := r) (-(t : K))).totalDegree ≤ ∑ _t ∈ range A, 1 :=
        sum_le_sum fun t _ => (MvPolynomial.totalDegree_add _ _).trans
          (max_le hp (totalDegree_cs_le (K := K) (r := r) _))
    _ = A := by simp

theorem totalDegree_rfPol_le (U : ℕ) {p : MP K r} (hp : p.totalDegree ≤ 1) :
    (rfPol U p).totalDegree ≤ U := by
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ t ∈ range U, (p + cs (r := r) ((t : K) + 1)).totalDegree ≤ ∑ _t ∈ range U, 1 :=
        sum_le_sum fun t _ => (MvPolynomial.totalDegree_add _ _).trans
          (max_le hp (totalDegree_cs_le (K := K) (r := r) _))
    _ = U := by simp

/-! ### The numerator and denominator factors, for a shift `s` -/

/-- Numerator factor for a shift `s` of the argument `y` with common-denominator parameter `A`. -/
def numG (y : MP K r) (s : ℤ) (A : ℕ) : MP K r :=
  if 0 ≤ s then ffPol (A - s.toNat) (y + cs (-(s : K)))
  else rfPol s.natAbs y * ffPol A y

/-- Denominator factor for a shift `s` of the argument `y` with parameter `U`. -/
def denG (y : MP K r) (s : ℤ) (U : ℕ) : MP K r :=
  if 0 ≤ s then ffPol s.toNat y * rfPol U y
  else rfPol (U - s.natAbs) (y + cs ((s.natAbs : ℕ) : K))

theorem totalDegree_numG_le (y : MP K r) (hy : y.totalDegree ≤ 1) (s : ℤ) (A : ℕ) :
    (numG y s A).totalDegree ≤ A + (-s).toNat := by
  unfold numG
  split_ifs with hs
  · refine (totalDegree_ffPol_le _ ?_).trans (by omega)
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le hy (by simp [totalDegree_cs]))
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have e1 := totalDegree_rfPol_le s.natAbs hy
    have e2 := totalDegree_ffPol_le A hy
    omega

theorem totalDegree_denG_le (y : MP K r) (hy : y.totalDegree ≤ 1) (s : ℤ) (U : ℕ) :
    (denG y s U).totalDegree ≤ U + s.toNat := by
  unfold denG
  split_ifs with hs
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have e1 := totalDegree_ffPol_le s.toNat hy
    have e2 := totalDegree_rfPol_le U hy
    omega
  · refine (totalDegree_rfPol_le _ ?_).trans (by omega)
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le hy (by simp [totalDegree_cs]))

variable [CharZero K]

theorem intFact_mul_ffVal_numG (y : MP K r) (Y s : ℤ) (A : ℕ) (n : K) (k : Fin r → K)
    (hy : ev n k y = (Y : K)) (hsA : s ≤ A) (h0 : 0 ≤ Y) (h1 : 0 ≤ Y - s) :
    intFact (K := K) (Y - s) * ffVal A (Y : K) = intFact Y * ev n k (numG y s A) := by
  unfold numG
  split_ifs with hs
  · rw [ev_ffPol, map_add, hy, ev_cs]
    have hsle : s.toNat ≤ A := by omega
    rw [ffVal_split _ _ hsle]
    have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs
    have := intFact_eq_sub (K := K) Y s.toNat (by omega)
    rw [e] at this
    rw [this]
    have e2 : ((s.toNat : ℕ) : K) = (s : K) := by
      rw [← Int.cast_natCast, e]
    rw [e2]
    ring
  · rw [map_mul, ev_rfPol, ev_ffPol, hy]
    have e : Y - s = Y + (s.natAbs : ℤ) := by omega
    rw [e, intFact_add _ _ h0]
    ring

theorem intInvFact_mul_rfVal_denG (y : MP K r) (Y s : ℤ) (U : ℕ) (n : K) (k : Fin r → K)
    (hy : ev n k y = (Y : K)) (hle : -s ≤ U) :
    intInvFact (K := K) (Y - s) * rfVal U (Y : K) = intInvFact Y * ev n k (denG y s U) := by
  unfold denG
  split_ifs with hs
  · rw [map_mul, ev_rfPol, ev_ffPol, hy]
    have e : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs
    have := intInvFact_sub (K := K) Y s.toNat
    rw [e] at this
    rw [this]; ring
  · rw [ev_rfPol, map_add, hy, ev_cs]
    have hsle : s.natAbs ≤ U := by omega
    rw [rfVal_split _ _ hsle]
    have e : Y - s = Y + (s.natAbs : ℤ) := by omega
    rw [e, intInvFact_add (K := K) Y s.natAbs]
    ring

/-! ### Parameters of the common denominator -/

/-- `∑_t (b_t)⁺`. -/
def bpos (b : Fin r → ℤ) : ℤ := ∑ t, max (b t) 0

/-- `∑_t (b_t)⁻`. -/
def bneg (b : Fin r → ℤ) : ℤ := bpos (fun t => -b t)

/-- `‖b‖₁`. -/
def babs (b : Fin r → ℤ) : ℕ := ∑ t, (b t).natAbs

theorem bpos_nonneg (b : Fin r → ℤ) : 0 ≤ bpos b := sum_nonneg fun t _ => le_max_right _ _

theorem bneg_nonneg (b : Fin r → ℤ) : 0 ≤ bneg b := bpos_nonneg _

theorem bpos_add_bneg (b : Fin r → ℤ) : bpos b + bneg b = (babs b : ℤ) := by
  unfold bneg bpos babs
  rw [← sum_add_distrib, Nat.cast_sum]
  exact sum_congr rfl fun t _ => by simp only []; omega

theorem dotN_le {b : Fin r → ℤ} {i : Fin r → ℕ} {I : ℕ} (hi : ∀ t, i t ≤ I) :
    dotN b i ≤ bpos b * I := by
  unfold dotN dot bpos
  rw [sum_mul]
  refine sum_le_sum fun t _ => ?_
  have hit : ((i t : ℕ) : ℤ) ≤ I := by exact_mod_cast hi t
  have hi0 : (0 : ℤ) ≤ i t := Nat.cast_nonneg _
  rcases le_total (b t) 0 with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    exact mul_le_mul_of_nonneg_left hit h

theorem neg_dotN_le {b : Fin r → ℤ} {i : Fin r → ℕ} {I : ℕ} (hi : ∀ t, i t ≤ I) :
    -dotN b i ≤ bneg b * I := by
  have := dotN_le (b := fun t => -b t) hi
  have e : dotN (fun t => -b t) i = -dotN b i := by
    simp [dotN, dot, sum_neg_distrib]
  rw [e] at this
  exact this

/-- The shift `a j + b · i`. -/
def sh (a : ℤ) (b : Fin r → ℤ) (i : Fin r → ℕ) (j : ℕ) : ℤ := a * j + dotN b i

/-- `A = a⁺ J + (∑ b_t⁺) I`. -/
def numA (a : ℤ) (b : Fin r → ℤ) (I J : ℕ) : ℕ := (max a 0 * J + bpos b * I).toNat

/-- `U = (-u)⁺ J + (∑ v_t⁻) I`. -/
def denU (u : ℤ) (v : Fin r → ℤ) (I J : ℕ) : ℕ := (max (-u) 0 * J + bneg v * I).toNat

theorem numA_arg_nonneg (a : ℤ) (b : Fin r → ℤ) (I J : ℕ) : 0 ≤ max a 0 * (J : ℤ) + bpos b * I :=
  add_nonneg (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _))
    (mul_nonneg (bpos_nonneg _) (Nat.cast_nonneg _))

theorem denU_arg_nonneg (a : ℤ) (b : Fin r → ℤ) (I J : ℕ) :
    0 ≤ max (-a) 0 * (J : ℤ) + bneg b * I :=
  add_nonneg (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _))
    (mul_nonneg (bneg_nonneg _) (Nat.cast_nonneg _))

theorem le_numA (a : ℤ) (b : Fin r → ℤ) {I J : ℕ} {i : Fin r → ℕ} {j : ℕ} (hi : ∀ t, i t ≤ I)
    (hj : j ≤ J) : sh a b i j ≤ numA a b I J := by
  have h1 : a * j ≤ max a 0 * J := by
    have hj' : (j : ℤ) ≤ J := by exact_mod_cast hj
    rcases le_or_gt 0 a with ha | ha
    · rw [max_eq_left ha]; exact mul_le_mul_of_nonneg_left hj' ha
    · rw [max_eq_right ha.le]; nlinarith
  have h2 := dotN_le (b := b) hi
  have h3 := numA_arg_nonneg a b I J
  unfold sh numA
  omega

theorem neg_le_denU (u : ℤ) (v : Fin r → ℤ) {I J : ℕ} {i : Fin r → ℕ} {j : ℕ}
    (hi : ∀ t, i t ≤ I) (hj : j ≤ J) : -(sh u v i j) ≤ denU u v I J := by
  have h1 : -(u * j) ≤ max (-u) 0 * J := by
    have hj' : (j : ℤ) ≤ J := by exact_mod_cast hj
    rcases le_or_gt 0 (-u) with ha | ha
    · rw [max_eq_left ha]; nlinarith
    · rw [max_eq_right ha.le]; nlinarith
  have h2 := neg_dotN_le (b := v) hi
  have h3 := denU_arg_nonneg u v I J
  unfold sh denU
  omega

theorem num_bound (a : ℤ) (b : Fin r → ℤ) {I J : ℕ} {i : Fin r → ℕ} {j : ℕ} (hi : ∀ t, i t ≤ I)
    (hj : j ≤ J) :
    numA a b I J + (-(sh a b i j)).toNat ≤ a.natAbs * J + babs b * I := by
  have F2 := neg_dotN_le (b := b) hi
  have F1 := dotN_le (b := b) hi
  have hp := bpos_nonneg b
  have hn := bneg_nonneg b
  have hs := bpos_add_bneg b
  have h3 := numA_arg_nonneg a b I J
  have hj' : (j : ℤ) ≤ J := by exact_mod_cast hj
  have hI : (0 : ℤ) ≤ I := Nat.cast_nonneg _
  have hbI : (babs b : ℤ) * I = bpos b * I + bneg b * I := by rw [← hs]; ring
  have hpI : 0 ≤ bpos b * (I : ℤ) := mul_nonneg hp hI
  have hnI : 0 ≤ bneg b * (I : ℤ) := mul_nonneg hn hI
  have ha : (a.natAbs : ℤ) = |a| := Int.natCast_natAbs a
  have f1 : -(a * j) + max a 0 * J ≤ |a| * J := by
    rcases le_or_gt 0 a with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; nlinarith
    · rw [max_eq_right h.le, abs_of_neg h]; nlinarith
  have f2 : max a 0 * (J : ℤ) ≤ |a| * J := by
    exact mul_le_mul_of_nonneg_right (max_le (le_abs_self a) (abs_nonneg a)) (Nat.cast_nonneg _)
  clear ha
  unfold sh numA
  zify
  rw [Int.toNat_of_nonneg h3]
  push_cast
  omega

theorem den_bound (u : ℤ) (v : Fin r → ℤ) {I J : ℕ} {i : Fin r → ℕ} {j : ℕ} (hi : ∀ t, i t ≤ I)
    (hj : j ≤ J) :
    denU u v I J + (sh u v i j).toNat ≤ u.natAbs * J + babs v * I := by
  have F2 := neg_dotN_le (b := v) hi
  have F1 := dotN_le (b := v) hi
  have hp := bpos_nonneg v
  have hn := bneg_nonneg v
  have hs := bpos_add_bneg v
  have h3 := denU_arg_nonneg u v I J
  have hj' : (j : ℤ) ≤ J := by exact_mod_cast hj
  have hI : (0 : ℤ) ≤ I := Nat.cast_nonneg _
  have hbI : (babs v : ℤ) * I = bpos v * I + bneg v * I := by rw [← hs]; ring
  have hpI : 0 ≤ bpos v * (I : ℤ) := mul_nonneg hp hI
  have hnI : 0 ≤ bneg v * (I : ℤ) := mul_nonneg hn hI
  have ha : (u.natAbs : ℤ) = |u| := Int.natCast_natAbs u
  have f1 : u * j + max (-u) 0 * J ≤ |u| * J := by
    rcases le_or_gt 0 u with h | h
    · rw [max_eq_right (by omega), abs_of_nonneg h]; nlinarith
    · rw [max_eq_left (by omega), abs_of_neg h]; nlinarith
  have f2 : max (-u) 0 * (J : ℤ) ≤ |u| * J := by
    exact mul_le_mul_of_nonneg_right (max_le (neg_le_abs u) (abs_nonneg u)) (Nat.cast_nonneg _)
  clear ha
  unfold sh denU
  zify
  rw [Int.toNat_of_nonneg h3]
  push_cast
  omega

/-! ### The polynomial factor `P(n - j, k - i)` -/

/-- `P(n - j, k - i)` as an element of `MP K r` (variable `0` of `P` is `n`, variable `t+1` is `k_t`). -/
def pShift (P : MvPolynomial (Fin (r + 1)) K) (i : Fin r → ℕ) (j : ℕ) : MP K r :=
  MvPolynomial.aeval
    (Fin.cons (α := fun _ : Fin (r + 1) => MP K r) (MvPolynomial.C (Polynomial.X + Polynomial.C (-(j : K))))
      (fun t => MvPolynomial.X t + cs (-(i t : K)))) P

theorem ev_pShift (P : MvPolynomial (Fin (r + 1)) K) (i : Fin r → ℕ) (j : ℕ) (n : ℤ)
    (k : Fin r → ℤ) :
    ev (n : K) (fun t => (k t : K)) (pShift P i j) =
      MvPolynomial.eval (Fin.cons (α := fun _ : Fin (r + 1) => K) ((n - j : ℤ) : K)
        (fun t => ((k t - (i t : ℤ) : ℤ) : K))) P := by
  unfold pShift
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p t hp =>
    rw [map_mul, map_mul, hp, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    congr 1
    cases t using Fin.cases with
    | zero => simp only [Fin.cons_zero, map_add, ev_C, ev_cs, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C]; push_cast; ring
    | succ t => simp only [Fin.cons_succ, map_add, ev_X, ev_cs]; push_cast; ring

theorem totalDegree_pShift_le (P : MvPolynomial (Fin (r + 1)) K) (i : Fin r → ℕ) (j : ℕ) :
    (pShift P i j).totalDegree ≤ P.totalDegree := by
  classical
  unfold pShift
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun v hv => ?_
  have hv' := MvPolynomial.le_totalDegree hv
  rw [Finsupp.sum_fintype _ _ (by simp)] at hv'
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h1 : (algebraMap K (MP K r) (P.coeff v)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_apply]; exact MvPolynomial.totalDegree_C _
  have hg : ∀ t : Fin (r + 1), ((Fin.cons (α := fun _ : Fin (r + 1) => MP K r)
      (MvPolynomial.C (Polynomial.X + Polynomial.C (-(j : K))))
      (fun t => MvPolynomial.X t + cs (-(i t : K)))) t).totalDegree ≤ 1 := by
    intro t
    cases t using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact (MvPolynomial.totalDegree_C _).le.trans (Nat.zero_le _)
    | succ t =>
      simp only [Fin.cons_succ]
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (by simp) (totalDegree_cs_le (K := K) (r := r) _))
  rw [h1, zero_add]
  refine ((MvPolynomial.totalDegree_finsetProd _ _).trans
    (sum_le_sum (g := fun t => v t) fun t _ => ?_)).trans (by simpa using hv')
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc v t * _ ≤ v t * 1 := Nat.mul_le_mul_left _ (hg t)
    _ = v t := mul_one _

/-! ### Data and values -/

variable (K) (r) in
/-- A proper hypergeometric term in `r` summation variables (4.5.2).  The polynomial `P` has the
variable `0` for `n` and the variable `t+1` for `k_t`. -/
structure ProperHypergeometricDataMulti where
  /-- number of numerator factorials -/
  uu : ℕ
  /-- number of denominator factorials -/
  vv : ℕ
  /-- the polynomial `P(n,k)` -/
  P : MvPolynomial (Fin (r + 1)) K
  a : Fin uu → ℤ
  b : Fin uu → Fin r → ℤ
  c : Fin uu → ℤ
  u : Fin vv → ℤ
  v : Fin vv → Fin r → ℤ
  w : Fin vv → ℤ
  /-- the bases `z_t` of `z^k = ∏ z_t^{k_t}` -/
  z : Fin r → K

namespace ProperHypergeometricDataMulti

/-- The value at `(n, k)` (with `1/m! = 0` for `m < 0`). -/
def eval (D : ProperHypergeometricDataMulti K r) (n : ℤ) (k : Fin r → ℤ) : K :=
  MvPolynomial.eval (Fin.cons (α := fun _ : Fin (r + 1) => K) (n : K) (fun t => (k t : K))) D.P *
    (∏ s, intFact (D.a s * n + dot (D.b s) k + D.c s)) *
    (∏ s, intInvFact (D.u s * n + dot (D.v s) k + D.w s)) * ∏ t, D.z t ^ k t

/-- No numerator factorial has a negative argument. -/
def WellDefinedAt (D : ProperHypergeometricDataMulti K r) (n : ℤ) (k : Fin r → ℤ) : Prop :=
  ∀ s, 0 ≤ D.a s * n + dot (D.b s) k + D.c s

theorem eval_eq_zero_of_neg (D : ProperHypergeometricDataMulti K r) (n : ℤ) (k : Fin r → ℤ)
    (s : Fin D.vv) (hs : D.u s * n + dot (D.v s) k + D.w s < 0) : D.eval n k = 0 := by
  have : intInvFact (K := K) (D.u s * n + dot (D.v s) k + D.w s) = 0 := by
    simp [intInvFact, not_le.2 hs]
  have h2 : (∏ s, intInvFact (K := K) (D.u s * n + dot (D.v s) k + D.w s)) = 0 :=
    prod_eq_zero (Finset.mem_univ s) this
  simp [eval, h2]

end ProperHypergeometricDataMulti

open ProperHypergeometricDataMulti

/-- `Q_{ij} = P(n-j,k-i) ∏ numG ∏ denG` (the analogue of `celineQ`). -/
def celineQ (D : ProperHypergeometricDataMulti K r) (I J : ℕ) (i : Fin r → ℕ) (j : ℕ) : MP K r :=
  pShift D.P i j * (∏ s, numG (lin (D.a s) (D.b s) (D.c s)) (sh (D.a s) (D.b s) i j)
      (numA (D.a s) (D.b s) I J)) *
    ∏ s, denG (lin (D.u s) (D.v s) (D.w s)) (sh (D.u s) (D.v s) i j) (denU (D.u s) (D.v s) I J)

/-- The common bound for the total degrees of the `Q_{ij}`. -/
def degBound (D : ProperHypergeometricDataMulti K r) (I J : ℕ) : ℕ :=
  D.P.totalDegree + ∑ s, ((D.a s).natAbs * J + babs (D.b s) * I) +
    ∑ s, ((D.u s).natAbs * J + babs (D.v s) * I)

theorem totalDegree_celineQ_le (D : ProperHypergeometricDataMulti K r) {I J : ℕ} {i : Fin r → ℕ}
    {j : ℕ} (hi : ∀ t, i t ≤ I) (hj : j ≤ J) :
    (celineQ D I J i j).totalDegree ≤ degBound D I J := by
  unfold celineQ degBound
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h1 := MvPolynomial.totalDegree_mul (pShift D.P i j)
    (∏ s, numG (lin (D.a s) (D.b s) (D.c s)) (sh (D.a s) (D.b s) i j) (numA (D.a s) (D.b s) I J))
  have h2 := totalDegree_pShift_le D.P i j
  have h3 : (∏ s, numG (lin (D.a s) (D.b s) (D.c s)) (sh (D.a s) (D.b s) i j)
      (numA (D.a s) (D.b s) I J)).totalDegree ≤
      ∑ s, ((D.a s).natAbs * J + babs (D.b s) * I) :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans (sum_le_sum fun s _ =>
      (totalDegree_numG_le (lin (D.a s) (D.b s) (D.c s)) (totalDegree_lin_le (K := K) _ _ _) _ _).trans (by
        have := num_bound (D.a s) (D.b s) hi hj
        omega))
  have h4 : (∏ s, denG (lin (D.u s) (D.v s) (D.w s)) (sh (D.u s) (D.v s) i j)
      (denU (D.u s) (D.v s) I J)).totalDegree ≤
      ∑ s, ((D.u s).natAbs * J + babs (D.v s) * I) :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans (sum_le_sum fun s _ =>
      (totalDegree_denG_le (lin (D.u s) (D.v s) (D.w s)) (totalDegree_lin_le (K := K) _ _ _) _ _).trans (by
        have := den_bound (D.u s) (D.v s) hi hj
        omega))
  omega

/-- The value at `(n, k)` of the common denominator. -/
def deltaVal (D : ProperHypergeometricDataMulti K r) (I J : ℕ) (n : ℤ) (k : Fin r → ℤ) : K :=
  (∏ s, ffVal (numA (D.a s) (D.b s) I J) ((D.a s * n + dot (D.b s) k + D.c s : ℤ) : K)) *
    ∏ s, rfVal (denU (D.u s) (D.v s) I J) ((D.u s * n + dot (D.v s) k + D.w s : ℤ) : K)

/-- `H(n,k) z^k`. -/
def hVal (D : ProperHypergeometricDataMulti K r) (n : ℤ) (k : Fin r → ℤ) : K :=
  (∏ s, intFact (D.a s * n + dot (D.b s) k + D.c s)) *
    (∏ s, intInvFact (D.u s * n + dot (D.v s) k + D.w s)) * ∏ t, D.z t ^ k t

theorem eval_shift_mul_deltaVal (D : ProperHypergeometricDataMulti K r) (hz : ∀ t, D.z t ≠ 0)
    {I J : ℕ} {i : Fin r → ℕ} {j : ℕ} (hi : ∀ t, i t ≤ I) (hj : j ≤ J) (n : ℤ) (k : Fin r → ℤ)
    (h0 : D.WellDefinedAt n k) (h1 : D.WellDefinedAt (n - j) (fun t => k t - (i t : ℤ))) :
    D.eval (n - j) (fun t => k t - (i t : ℤ)) * deltaVal D I J n k =
      (∏ t, D.z t ^ (-(i t : ℤ))) * hVal D n k *
        ev (n : K) (fun t => (k t : K)) (celineQ D I J i j) := by
  have e1 : (∏ s, intFact (K := K) (D.a s * (n - j) + dot (D.b s) (fun t => k t - (i t : ℤ)) +
        D.c s)) *
      (∏ s, ffVal (numA (D.a s) (D.b s) I J) ((D.a s * n + dot (D.b s) k + D.c s : ℤ) : K)) =
      (∏ s, intFact (D.a s * n + dot (D.b s) k + D.c s)) *
        ∏ s, ev (n : K) (fun t => (k t : K)) (numG (lin (D.a s) (D.b s) (D.c s))
          (sh (D.a s) (D.b s) i j) (numA (D.a s) (D.b s) I J)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun s _ => ?_
    have hA := le_numA (D.a s) (D.b s) hi hj
    have key := intFact_mul_ffVal_numG (lin (D.a s) (D.b s) (D.c s))
      (D.a s * n + dot (D.b s) k + D.c s) (sh (D.a s) (D.b s) i j) (numA (D.a s) (D.b s) I J)
      (n : K) (fun t => (k t : K)) (ev_lin _ _ _ _ _) (by exact_mod_cast hA) (h0 s) (by
        have := h1 s
        rw [dot_sub] at this
        unfold sh
        linarith)
    have harg : D.a s * (n - j) + dot (D.b s) (fun t => k t - (i t : ℤ)) + D.c s =
        (D.a s * n + dot (D.b s) k + D.c s) - sh (D.a s) (D.b s) i j := by
      rw [dot_sub]; unfold sh; ring
    rw [harg]; exact key
  have e2 : (∏ s, intInvFact (K := K) (D.u s * (n - j) + dot (D.v s) (fun t => k t - (i t : ℤ)) +
        D.w s)) *
      (∏ s, rfVal (denU (D.u s) (D.v s) I J) ((D.u s * n + dot (D.v s) k + D.w s : ℤ) : K)) =
      (∏ s, intInvFact (D.u s * n + dot (D.v s) k + D.w s)) *
        ∏ s, ev (n : K) (fun t => (k t : K)) (denG (lin (D.u s) (D.v s) (D.w s))
          (sh (D.u s) (D.v s) i j) (denU (D.u s) (D.v s) I J)) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun s _ => ?_
    have key := intInvFact_mul_rfVal_denG (lin (D.u s) (D.v s) (D.w s))
      (D.u s * n + dot (D.v s) k + D.w s) (sh (D.u s) (D.v s) i j) (denU (D.u s) (D.v s) I J)
      (n : K) (fun t => (k t : K)) (ev_lin _ _ _ _ _) (by
        have := neg_le_denU (D.u s) (D.v s) hi hj
        exact_mod_cast this)
    have harg : D.u s * (n - j) + dot (D.v s) (fun t => k t - (i t : ℤ)) + D.w s =
        (D.u s * n + dot (D.v s) k + D.w s) - sh (D.u s) (D.v s) i j := by
      rw [dot_sub]; unfold sh; ring
    rw [harg]; exact key
  have e3 : ∏ t, D.z t ^ (k t - (i t : ℤ)) = (∏ t, D.z t ^ (-(i t : ℤ))) * ∏ t, D.z t ^ k t := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun t _ => ?_
    rw [← zpow_add₀ (hz t)]; ring_nf
  unfold ProperHypergeometricDataMulti.eval deltaVal hVal celineQ
  rw [map_mul, map_mul, map_prod, map_prod, ev_pShift, e3]
  calc _ = (MvPolynomial.eval (Fin.cons (α := fun _ : Fin (r + 1) => K) ((n - j : ℤ) : K)
          (fun t => ((k t - (i t : ℤ) : ℤ) : K))) D.P) *
        ((∏ s, intFact (K := K) (D.a s * (n - j) + dot (D.b s) (fun t => k t - (i t : ℤ)) +
            D.c s)) *
          (∏ s, ffVal (numA (D.a s) (D.b s) I J) ((D.a s * n + dot (D.b s) k + D.c s : ℤ) : K))) *
        ((∏ s, intInvFact (K := K) (D.u s * (n - j) + dot (D.v s) (fun t => k t - (i t : ℤ)) +
            D.w s)) *
          (∏ s, rfVal (denU (D.u s) (D.v s) I J) ((D.u s * n + dot (D.v s) k + D.w s : ℤ) : K))) *
        ((∏ t, D.z t ^ (-(i t : ℤ))) * ∏ t, D.z t ^ k t) := by
        simp only [Int.cast_sub, Int.cast_natCast]
        ring
    _ = _ := by rw [e1, e2]; ring

theorem deltaVal_ne_zero (D : ProperHypergeometricDataMulti K r) {I J : ℕ} {n : ℤ}
    {k : Fin r → ℤ} (hF : D.eval n k ≠ 0)
    (hwd : ∀ i : Fin r → ℕ, (∀ t, i t ≤ I) → ∀ j ≤ J,
      D.WellDefinedAt (n - j) (fun t => k t - (i t : ℤ))) :
    deltaVal D I J n k ≠ 0 := by
  unfold deltaVal
  refine mul_ne_zero (prod_ne_zero_iff.2 fun s _ => ?_) (prod_ne_zero_iff.2 fun s _ => ?_)
  · set a := D.a s
    set b := D.b s
    have hc := hwd (fun t => if 0 < b t then I else 0) (fun t => by split_ifs <;> omega)
      (if 0 < a then J else 0) (by split_ifs <;> omega) s
    have hdot : dotN b (fun t => if 0 < b t then I else 0) = bpos b * I := by
      unfold dotN dot bpos
      rw [sum_mul]
      refine sum_congr rfl fun t _ => ?_
      rcases lt_or_ge 0 (b t) with h | h
      · simp [h, max_eq_left h.le]
      · simp [not_lt.2 h, max_eq_right h]
    have hcorner : a * ((if 0 < a then J else 0 : ℕ) : ℤ) = max a 0 * J := by
      rcases le_or_gt a 0 with ha | ha
      · simp [not_lt.2 ha, max_eq_right ha]
      · simp [ha, max_eq_left ha.le]
    have hA : (numA a b I J : ℤ) ≤ a * n + dot b k + D.c s := by
      unfold numA
      rw [Int.toNat_of_nonneg (numA_arg_nonneg a b I J)]
      have hc' : 0 ≤ a * (n - ((if 0 < a then J else 0 : ℕ) : ℤ)) +
          dot b (fun t => k t - ((if 0 < b t then I else 0 : ℕ) : ℤ)) + D.c s := hc
      rw [dot_sub, hdot] at hc'
      nlinarith
    unfold ffVal
    refine prod_ne_zero_iff.2 fun t ht => ?_
    have ht' := mem_range.1 ht
    have : ((a * n + dot b k + D.c s : ℤ) : K) - (t : K) =
        ((a * n + dot b k + D.c s - t : ℤ) : K) := by
      push_cast; ring
    rw [this, Int.cast_ne_zero]
    omega
  · have hy : 0 ≤ D.u s * n + dot (D.v s) k + D.w s := by
      by_contra hneg
      exact hF (D.eval_eq_zero_of_neg n k s (not_le.1 hneg))
    unfold rfVal
    refine prod_ne_zero_iff.2 fun t _ => ?_
    have : ((D.u s * n + dot (D.v s) k + D.w s : ℤ) : K) + ((t : K) + 1) =
        ((D.u s * n + dot (D.v s) k + D.w s + t + 1 : ℤ) : K) := by push_cast; ring
    rw [this, Int.cast_ne_zero]
    omega

/-- Correctness of the method: every vanishing combination gives a recurrence. -/
theorem celine_sound_multi (D : ProperHypergeometricDataMulti K r) (hz : ∀ t, D.z t ≠ 0)
    {I J : ℕ} (b : (Fin r → Fin (I + 1)) × Fin (J + 1) → Polynomial K)
    (hb : ∑ p, MvPolynomial.C (b p) * celineQ D I J (fun t => (p.1 t : ℕ)) p.2 = 0)
    (n : ℤ) (k : Fin r → ℤ) (hF : D.eval n k ≠ 0)
    (hwd : ∀ i : Fin r → ℕ, (∀ t, i t ≤ I) → ∀ j ≤ J,
      D.WellDefinedAt (n - j) (fun t => k t - (i t : ℤ))) :
    ∑ p : (Fin r → Fin (I + 1)) × Fin (J + 1),
      (b p * Polynomial.C (∏ t, D.z t ^ (p.1 t : ℕ))).eval (n : K) *
        D.eval (n - (p.2 : ℕ)) (fun t => k t - ((p.1 t : ℕ) : ℤ)) = 0 := by
  have hΔ := deltaVal_ne_zero D hF hwd
  have h0 : D.WellDefinedAt n k := by
    have := hwd (fun _ => 0) (fun _ => Nat.zero_le _) 0 (Nat.zero_le _)
    simpa [WellDefinedAt, dot] using this
  have hb' := congrArg (ev (n : K) (fun t => (k t : K))) hb
  rw [map_sum, map_zero] at hb'
  refine (mul_left_inj' hΔ).1 ?_
  rw [zero_mul, sum_mul]
  calc ∑ p : (Fin r → Fin (I + 1)) × Fin (J + 1),
        (b p * Polynomial.C (∏ t, D.z t ^ (p.1 t : ℕ))).eval (n : K) *
          D.eval (n - (p.2 : ℕ)) (fun t => k t - ((p.1 t : ℕ) : ℤ)) * deltaVal D I J n k
      = ∑ p : (Fin r → Fin (I + 1)) × Fin (J + 1), hVal D n k *
          ev (n : K) (fun t => (k t : K))
            (MvPolynomial.C (b p) * celineQ D I J (fun t => (p.1 t : ℕ)) p.2) := by
        refine sum_congr rfl fun p _ => ?_
        have hi : ∀ t, (p.1 t : ℕ) ≤ I := fun t => Nat.lt_succ_iff.1 (p.1 t).2
        rw [mul_assoc, eval_shift_mul_deltaVal D hz hi (Nat.lt_succ_iff.1 p.2.2) n k h0
          (hwd _ hi _ (Nat.lt_succ_iff.1 p.2.2))]
        rw [map_mul, ev_C, Polynomial.eval_mul, Polynomial.eval_C]
        have : (∏ t, D.z t ^ (p.1 t : ℕ)) * ∏ t, D.z t ^ (-((p.1 t : ℕ) : ℤ)) = 1 := by
          rw [← prod_mul_distrib]
          refine prod_eq_one fun t _ => ?_
          rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hz t))]
        linear_combination ((b p).eval (n : K) * hVal D n k *
          ev (n : K) (fun t => (k t : K)) (celineQ D I J (fun t => (p.1 t : ℕ)) p.2)) * this
    _ = 0 := by rw [← mul_sum, hb', mul_zero]

/-! ### Choice of the orders and the theorem -/

/-- `∑ |a_s| + ∑ |u_s|`. -/
def aTot (D : ProperHypergeometricDataMulti K r) : ℕ :=
  ∑ s, (D.a s).natAbs + ∑ s, (D.u s).natAbs

/-- `B = ∑_s ‖b_s‖₁ + ∑_s ‖v_s‖₁`. -/
def bTot (D : ProperHypergeometricDataMulti K r) : ℕ :=
  ∑ s, babs (D.b s) + ∑ s, babs (D.v s)

/-- The order `J = (B+1)^r - 1` (cruder than the book's `J*` of (4.5.4)). -/
def multiJ (D : ProperHypergeometricDataMulti K r) : ℕ := (bTot D + 1) ^ r - 1

/-- The width `I = deg P + J A + 1`. -/
def multiI (D : ProperHypergeometricDataMulti K r) : ℕ :=
  D.P.totalDegree + multiJ D * aTot D + 1

theorem degBound_eq (D : ProperHypergeometricDataMulti K r) (I J : ℕ) :
    degBound D I J = D.P.totalDegree + aTot D * J + bTot D * I := by
  unfold degBound aTot bTot
  simp only [sum_add_distrib, ← sum_mul]
  ring

/-- The unknowns outnumber the coefficient slots for `(multiI, multiJ)` (needs `r ≥ 1`). -/
theorem degBound_lt (D : ProperHypergeometricDataMulti K r) (hr : 0 < r) :
    (degBound D (multiI D) (multiJ D) + 1) ^ r <
      (multiI D + 1) ^ r * (multiJ D + 1) := by
  have hJ : multiJ D + 1 = (bTot D + 1) ^ r := by
    unfold multiJ
    have := Nat.one_le_pow r (bTot D + 1) (Nat.succ_pos _)
    omega
  have hd : degBound D (multiI D) (multiJ D) + 1 = multiI D * (bTot D + 1) := by
    rw [degBound_eq]
    unfold multiI
    ring
  rw [hd, hJ, mul_pow, mul_comm]
  have hI : 0 < multiI D := by unfold multiI; omega
  have := Nat.pow_lt_pow_left (Nat.lt_succ_self (multiI D)) hr.ne'
  have hB : 0 < (bTot D + 1) ^ r := by positivity
  nlinarith

/-- CO-393. **Theorem 4.5.1 (multivariate Fundamental Theorem)**.  Every proper hypergeometric term
`F(n, k) = P(n,k) ∏_s (a_s n + b_s·k + c_s)! / ∏_s (u_s n + v_s·k + w_s)! · z^k` in `r ≥ 1` summation
variables satisfies a nontrivial `k`-free recurrence
`∑_{j ≤ J} ∑_{i ∈ [0,I]^r} α(i,j,n) F(n-j, k-i) = 0`, with polynomials `α(i,j,n)` in `n` not all zero,
at every point `(n,k)` where `F(n,k) ≠ 0` and all the values `F(n-j,k-i)` occurring are well defined.
The orders obtained are `J = (B+1)^r - 1` with `B = ∑‖b_s‖₁ + ∑‖v_s‖₁` and
`I = deg P + J (∑|a_s| + ∑|u_s|) + 1`; this is weaker than the sharper bound `J*` of (4.5.4),
which is not proved here.  (Requires every `z_t ≠ 0`.) -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 4.5.1, p. 81"]
theorem exists_kfree_recurrence_multi (D : ProperHypergeometricDataMulti K r) (hr : 0 < r)
    (hz : ∀ t, D.z t ≠ 0) :
    ∃ α : (Fin r → Fin (multiI D + 1)) × Fin (multiJ D + 1) → Polynomial K, α ≠ 0 ∧
      ∀ (n : ℤ) (k : Fin r → ℤ), D.eval n k ≠ 0 →
        (∀ i : Fin r → ℕ, (∀ t, i t ≤ multiI D) → ∀ j ≤ multiJ D,
          D.WellDefinedAt (n - j) (fun t => k t - (i t : ℤ))) →
        ∑ p : (Fin r → Fin (multiI D + 1)) × Fin (multiJ D + 1),
          (α p).eval (n : K) *
            D.eval (n - (p.2 : ℕ)) (fun t => k t - ((p.1 t : ℕ) : ℤ)) = 0 := by
  classical
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_sum_C_mul_eq_zero_mv
    (fun p : (Fin r → Fin (multiI D + 1)) × Fin (multiJ D + 1) =>
      celineQ D (multiI D) (multiJ D) (fun t => (p.1 t : ℕ)) p.2)
    (degBound D (multiI D) (multiJ D))
    (fun p => totalDegree_celineQ_le D (fun t => Nat.lt_succ_iff.1 (p.1 t).2)
      (Nat.lt_succ_iff.1 p.2.2))
    (by simpa [Fintype.card_prod, Fintype.card_fun, mul_comm] using degBound_lt D hr)
  refine ⟨fun p => b p * Polynomial.C (∏ t, D.z t ^ (p.1 t : ℕ)), ?_, ?_⟩
  · intro h
    apply hb0
    funext p
    have := congrFun h p
    simp only [Pi.zero_apply, mul_eq_zero, Polynomial.C_eq_zero] at this
    exact this.resolve_right (prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (hz t))
  · intro n k hF hwd
    exact celine_sound_multi D hz b hb n k hF hwd

end CelineMulti

end UndergradKB.Combinatorics.AeqB
