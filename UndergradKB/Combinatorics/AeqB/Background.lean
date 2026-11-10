import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import UndergradKB.Common.Attr

/-!
# A=B, Chapter 1 background identities (Petkovšek–Wilf–Zeilberger)

CO-345, CO-347, CO-349, CO-532, CO-351.  CO-068 is done elsewhere; CO-525 (Prime Number Theorem)
is not in the pinned Mathlib (only Chebyshev-type bounds and `tendsto_primeCounting`).
-/

namespace UndergradKB.Combinatorics

open Finset

/-! ### CO-345 -/

/-- CO-345. The identity `((a+b)/2)^2 - ab = ((a-b)/2)^2`. -/
@[kb "petkovsekwilfzeilberger1996" "Eq 1.3.1, p. 19"]
theorem sq_avg_sub_mul_eq_sq_half_diff {R : Type*} [Field R] [CharZero R] (a b : R) :
    ((a + b) / 2) ^ 2 - a * b = ((a - b) / 2) ^ 2 := by
  field_simp
  ring

/-- CO-345. Consequence: AM-GM for two real numbers, `ab ≤ ((a+b)/2)^2`. -/
@[kb "petkovsekwilfzeilberger1996" "Eq 1.3.1, p. 19"]
theorem mul_le_sq_avg (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  have := sq_avg_sub_mul_eq_sq_half_diff a b
  nlinarith [sq_nonneg ((a - b) / 2)]

/-- CO-345. AM-GM for two nonnegative reals: `√(ab) ≤ (a+b)/2`. -/
@[kb "petkovsekwilfzeilberger1996" "Eq 1.3.1, p. 19"]
theorem sqrt_mul_le_avg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  exact mul_le_sq_avg a b

/-! ### CO-349, CO-347 -/

/-- CO-349. `(Σ a_i)^2 = Σ a_i^2 + 2 Σ_{i<j} a_i a_j` (i.e. `p₁² = p₂ + 2 e₂`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 23"]
theorem sq_sum_eq_sum_sq_add_two_mul {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, a i) ^ 2 =
      ∑ i ∈ range n, a i ^ 2 + 2 * ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, a i * a j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ∀ i ∈ range n, ∑ j ∈ Ico (i + 1) (n + 1), a i * a j
        = ∑ j ∈ Ico (i + 1) n, a i * a j + a i * a n := by
      intro i hi
      rw [Finset.sum_Ico_succ_top (by simpa using hi)]
    have hm : ∑ i ∈ range n, a i * a n = (∑ i ∈ range n, a i) * a n := (Finset.sum_mul ..).symm
    rw [Finset.sum_range_succ (fun i => ∑ j ∈ Ico (i + 1) (n + 1), a i * a j) n,
      Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_range_succ a n,
      Finset.sum_range_succ (fun i => a i ^ 2) n]
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
    linear_combination ih - 2 * hm

/-- CO-347. Lagrange identity:
`(Σ a_i²)(Σ b_i²) - (Σ a_i b_i)² = Σ_{i<j} (a_i b_j - a_j b_i)²`. -/
@[kb "petkovsekwilfzeilberger1996" "Eq 1.7.1, p. 24"]
theorem lagrange_identity {R : Type*} [CommRing R] (a b : ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, a i ^ 2) * (∑ i ∈ range n, b i ^ 2) - (∑ i ∈ range n, a i * b i) ^ 2 =
      ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, (a i * b j - a j * b i) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ∀ i ∈ range n, ∑ j ∈ Ico (i + 1) (n + 1), (a i * b j - a j * b i) ^ 2
        = ∑ j ∈ Ico (i + 1) n, (a i * b j - a j * b i) ^ 2 + (a i * b n - a n * b i) ^ 2 := by
      intro i hi
      rw [Finset.sum_Ico_succ_top (by simpa using hi)]
    have e : ∑ i ∈ range n, (a i * b n - a n * b i) ^ 2 =
        b n ^ 2 * ∑ i ∈ range n, a i ^ 2 - 2 * (a n * b n) * ∑ i ∈ range n, a i * b i
          + a n ^ 2 * ∑ i ∈ range n, b i ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [Finset.sum_range_succ (fun i => ∑ j ∈ Ico (i + 1) (n + 1), (a i * b j - a j * b i) ^ 2) n,
      Finset.sum_congr rfl h, Finset.sum_add_distrib, e,
      Finset.sum_range_succ (fun i => a i ^ 2) n, Finset.sum_range_succ (fun i => b i ^ 2) n,
      Finset.sum_range_succ (fun i => a i * b i) n]
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
    linear_combination ih

/-! ### CO-532 -/

/-- CO-532. Addition law for `arcsin`: for `x, y ∈ [-1,1]` with `xy ≤ 0` or `x²+y² ≤ 1` (exactly
the cases where `arcsin x + arcsin y` stays in the range of `arcsin`),
`arcsin x + arcsin y = arcsin (x √(1-y²) + y √(1-x²))`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 1.5.1, p. 22"]
theorem arcsin_add_arcsin {x y : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (hy1 : -1 ≤ y) (hy2 : y ≤ 1)
    (h : x * y ≤ 0 ∨ x ^ 2 + y ^ 2 ≤ 1) :
    Real.arcsin x + Real.arcsin y =
      Real.arcsin (x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2)) := by
  have hsin : Real.sin (Real.arcsin x + Real.arcsin y) =
      x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2) := by
    rw [Real.sin_add, Real.sin_arcsin hx1 hx2, Real.sin_arcsin hy1 hy2, Real.cos_arcsin,
      Real.cos_arcsin]
    ring
  have hcos : 0 ≤ Real.cos (Real.arcsin x + Real.arcsin y) := by
    rw [Real.cos_add, Real.sin_arcsin hx1 hx2, Real.sin_arcsin hy1 hy2, Real.cos_arcsin,
      Real.cos_arcsin, ← Real.sqrt_mul (by nlinarith)]
    rcases h with h | h
    · have : 0 ≤ Real.sqrt ((1 - x ^ 2) * (1 - y ^ 2)) := Real.sqrt_nonneg _
      linarith
    · have : x * y ≤ Real.sqrt ((1 - x ^ 2) * (1 - y ^ 2)) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith [sq_nonneg (x * y)]
      linarith
  have hr : Real.arcsin x + Real.arcsin y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have a1 := Real.neg_pi_div_two_le_arcsin x
    have a2 := Real.arcsin_le_pi_div_two x
    have b1 := Real.neg_pi_div_two_le_arcsin y
    have b2 := Real.arcsin_le_pi_div_two y
    constructor
    · by_contra hlt
      replace hlt := not_le.mp hlt
      have := Real.cos_neg_of_pi_div_two_lt_of_lt
        (x := -(Real.arcsin x + Real.arcsin y)) (by linarith) (by linarith [Real.pi_pos])
      rw [Real.cos_neg] at this
      linarith
    · by_contra hlt
      replace hlt := not_le.mp hlt
      have := Real.cos_neg_of_pi_div_two_lt_of_lt
        (x := Real.arcsin x + Real.arcsin y) hlt (by linarith [Real.pi_pos])
      linarith
  exact (Real.arcsin_eq_of_sin_eq hsin hr).symm

/-! ### CO-351 Smith's determinant -/

/-- The gcd matrix `(gcd(i,j))` for `1 ≤ i,j ≤ n`, with rows/columns indexed by `Fin n`
through `i ↦ i + 1`. -/
def gcdMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℤ)

/-- 0/1 divisibility matrix, `(i+1)` divisible by `(d+1)`. -/
private def divMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i d => if d.val + 1 ∣ i.val + 1 then 1 else 0

private lemma sum_fin_shift {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    ∑ d : Fin n, F (d.val + 1) = ∑ m ∈ Icc 1 n, F m := by
  rw [Fin.sum_univ_eq_sum_range (fun d => F (d + 1)) n]
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' F 0 n 1]
  rfl

private lemma gcdMatrix_eq (n : ℕ) :
    gcdMatrix n = divMatrix n * Matrix.diagonal (fun d : Fin n => ((Nat.totient (d.val + 1) : ℕ) : ℤ))
      * (divMatrix n).transpose := by
  ext i j
  have hg : 0 < Nat.gcd (i.val + 1) (j.val + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgn : Nat.gcd (i.val + 1) (j.val + 1) ≤ n :=
    (Nat.gcd_le_left _ (by omega)).trans (by omega)
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [gcdMatrix, divMatrix, Matrix.of_apply]
  have : ∀ d : Fin n, (if d.val + 1 ∣ i.val + 1 then (1:ℤ) else 0) * (Nat.totient (d.val + 1) : ℤ) *
      (if d.val + 1 ∣ j.val + 1 then 1 else 0) =
      if d.val + 1 ∣ Nat.gcd (i.val + 1) (j.val + 1) then (Nat.totient (d.val + 1) : ℤ) else 0 := by
    intro d
    simp only [Nat.dvd_gcd_iff]
    split_ifs <;> simp_all
  simp only [this]
  rw [sum_fin_shift n (fun m => if m ∣ Nat.gcd (i.val + 1) (j.val + 1) then (Nat.totient m : ℤ)
    else 0), ← Finset.sum_filter]
  have hs : (Icc 1 n).filter (· ∣ Nat.gcd (i.val + 1) (j.val + 1)) =
      (Nat.gcd (i.val + 1) (j.val + 1)).divisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, hg.ne'⟩
    · rintro ⟨h, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h hg, (Nat.le_of_dvd hg h).trans hgn⟩, h⟩
  rw [hs, ← Nat.cast_sum, Nat.sum_totient]

private lemma divMatrix_lower (n : ℕ) : (divMatrix n).IsLowerTriangular := by
  intro i j hij
  have hij : i < j := hij
  simp only [divMatrix, Matrix.of_apply]
  rw [ite_eq_right_iff]
  intro h
  exfalso
  have := Nat.le_of_dvd (by omega) h
  have : i.val < j.val := hij
  omega

private lemma det_divMatrix (n : ℕ) : (divMatrix n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (divMatrix_lower n)]
  apply Finset.prod_eq_one
  intro i _
  simp [divMatrix]

/-- CO-351. Smith's determinant: `det (gcd(i,j))_{1 ≤ i,j ≤ n} = φ(1) φ(2) ⋯ φ(n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 32"]
theorem det_gcdMatrix (n : ℕ) :
    (gcdMatrix n).det = ∏ m ∈ Icc 1 n, ((Nat.totient m : ℕ) : ℤ) := by
  rw [gcdMatrix_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_divMatrix,
    Matrix.det_diagonal, one_mul, mul_one]
  rw [Fin.prod_univ_eq_prod_range (fun d => ((Nat.totient (d + 1) : ℕ) : ℤ)) n,
    Finset.range_eq_Ico, Finset.prod_Ico_add' (fun m => ((Nat.totient m : ℕ) : ℤ)) 0 n 1]
  rfl

end UndergradKB.Combinatorics
