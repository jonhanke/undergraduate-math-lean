import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB

open Finset

/-- Summand `(-1)^k C(2n,k) C(2k,k) C(4n-2k,2n-k)` (real-valued; vanishes for `k > 2n`). -/
noncomputable def ex362F (n k : ℕ) : ℝ :=
  (-1) ^ k * ((2 * n).choose k : ℝ) * ((2 * k).choose k : ℝ) * ((4 * n - 2 * k).choose (2 * n - k) : ℝ)

/-- Numerator of the Zeilberger certificate (it has the factor `k^2`). -/
noncomputable def ex362R (n k : ℝ) : ℝ :=
  k^2*(((-5 : ℝ)*n^0) + ((-68 : ℝ)*n^1) + ((-381 : ℝ)*n^2) + ((-1146 : ℝ)*n^3) + ((-2004 : ℝ)*n^4) + ((-2040 : ℝ)*n^5) + ((-1120 : ℝ)*n^6) + ((-256 : ℝ)*n^7))
    + k^3*(((55/2 : ℝ)*n^0) + ((609/2 : ℝ)*n^1) + ((1363 : ℝ)*n^2) + ((3162 : ℝ)*n^3) + ((4012 : ℝ)*n^4) + ((2640 : ℝ)*n^5) + ((704 : ℝ)*n^6))
    + k^4*(((-117/2 : ℝ)*n^0) + ((-519 : ℝ)*n^1) + ((-1797 : ℝ)*n^2) + ((-3034 : ℝ)*n^3) + ((-2496 : ℝ)*n^4) + ((-800 : ℝ)*n^5))
    + k^5*(((62 : ℝ)*n^0) + ((855/2 : ℝ)*n^1) + ((1083 : ℝ)*n^2) + ((1192 : ℝ)*n^3) + ((480 : ℝ)*n^4))
    + k^6*(((-69/2 : ℝ)*n^0) + ((-176 : ℝ)*n^1) + ((-294 : ℝ)*n^2) + ((-160 : ℝ)*n^3))
    + k^7*(((19/2 : ℝ)*n^0) + ((33 : ℝ)*n^1) + ((28 : ℝ)*n^2))
    + k^8*(((-1 : ℝ)*n^0) + ((-2 : ℝ)*n^1))

/-- Telescoping term of the certificate for `0 ≤ k ≤ 2n`, with the poles of the rational
certificate already cancelled against the factorials of the summand. -/
noncomputable def ex362G (n k : ℕ) : ℝ :=
  ex362R n k * ((-1) ^ k * (((2 * n).factorial : ℝ) * ((2 * k).factorial : ℝ)
    * ((4 * n - 2 * k).factorial : ℝ) / ((k.factorial : ℝ) ^ 3 * ((2 * n + 1 - k : ℕ) : ℝ)
    * (((2 * n + 2 - k).factorial : ℝ)) ^ 3)))

lemma ex362F_eq (n k j : ℕ) (h : 2 * n = k + j) :
    ex362F n k = (-1) ^ k * (((k + j).factorial : ℝ) * ((2 * k).factorial : ℝ)
      * ((2 * j).factorial : ℝ) / ((k.factorial : ℝ) ^ 3 * (j.factorial : ℝ) ^ 3)) := by
  have e1 : 4 * n - 2 * k = 2 * j := by omega
  have e2 : 2 * n - k = j := by omega
  unfold ex362F
  rw [e1, e2, h]
  have a1 : (((k + j).choose k : ℕ) : ℝ) = ((k + j).factorial : ℝ) / (k.factorial * j.factorial) := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial (by omega)) (by positivity)]
    simp
  have a2 : (((2 * k).choose k : ℕ) : ℝ) = ((2 * k).factorial : ℝ) / (k.factorial * k.factorial) := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial (by omega)) (by positivity)]
    have : 2 * k - k = k := by omega
    simp [this]
  have a3 : (((2 * j).choose j : ℕ) : ℝ) = ((2 * j).factorial : ℝ) / (j.factorial * j.factorial) := by
    rw [Nat.choose_eq_factorial_div_factorial (by omega)]
    rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial (by omega)) (by positivity)]
    have : 2 * j - j = j := by omega
    simp [this]
  rw [a1, a2, a3]
  field_simp

lemma ex362_step (n k i : ℕ) (h : 2 * n = k + 1 + i) :
    -((2 * (n : ℝ) + 1) ^ 2) * ex362F n k + (1 / 4) * ((n : ℝ) + 1) ^ 2 * ex362F (n + 1) k
      = ex362G n (k + 1) - ex362G n k := by
  have e1 : 2 * n + 1 - k = i + 2 := by omega
  have e2 : 2 * n + 2 - k = i + 3 := by omega
  have e3 : 4 * n - 2 * k = 2 * (i + 1) := by omega
  have e4 : 2 * n + 1 - (k + 1) = i + 1 := by omega
  have e5 : 2 * n + 2 - (k + 1) = i + 2 := by omega
  have e6 : 4 * n - 2 * (k + 1) = 2 * i := by omega
  have hF1 := ex362F_eq n k (i + 1) (by omega)
  have hF2 := ex362F_eq (n + 1) k (i + 3) (by omega)
  have hn : (n : ℝ) = ((k : ℝ) + i + 1) / 2 := by
    have : (2 * n : ℝ) = k + 1 + i := by exact_mod_cast h
    linarith
  unfold ex362G
  rw [e1, e2, e3, e4, e5, e6, h, hF1, hF2]
  have f1 : ((k + (i + 3)).factorial : ℝ) = (k + i + 3) * (k + i + 2) * ((k + 1 + i).factorial : ℝ) := by
    have : k + (i + 3) = (k + 1 + i) + 1 + 1 := by ring
    rw [this, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have f2 : ((k + (i + 1)).factorial : ℝ) = ((k + 1 + i).factorial : ℝ) := by
    congr 2; ring
  have f3 : ((2 * (k + 1)).factorial : ℝ) = (2 * k + 2) * (2 * k + 1) * ((2 * k).factorial : ℝ) := by
    have : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [this, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have f4 : (((k + 1).factorial : ℕ) : ℝ) = (k + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f5 : ((2 * (i + 1)).factorial : ℝ) = (2 * i + 2) * (2 * i + 1) * ((2 * i).factorial : ℝ) := by
    have : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [this, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have f6 : ((2 * (i + 3)).factorial : ℝ) = (2 * i + 6) * (2 * i + 5) * (2 * i + 4) * (2 * i + 3)
      * (2 * i + 2) * (2 * i + 1) * ((2 * i).factorial : ℝ) := by
    have : 2 * (i + 3) = 2 * i + 1 + 1 + 1 + 1 + 1 + 1 := by ring
    rw [this]
    simp only [Nat.factorial_succ]; push_cast; ring
  have f7 : ((i + 1).factorial : ℝ) = (i + 1) * (i.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f8 : ((i + 2).factorial : ℝ) = (i + 2) * (i + 1) * (i.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have f9 : ((i + 3).factorial : ℝ) = (i + 3) * (i + 2) * (i + 1) * (i.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have p1 : (0 : ℝ) < (k + 1 + i).factorial := by positivity
  have p2 : (0 : ℝ) < (2 * k).factorial := by positivity
  have p3 : (0 : ℝ) < (2 * i).factorial := by positivity
  have p4 : (0 : ℝ) < k.factorial := by positivity
  have p5 : (0 : ℝ) < i.factorial := by positivity
  rw [f1, f2, f3, f4, f5, f6, f7, f8, f9, hn]
  push_cast
  unfold ex362R
  field_simp
  ring

/-- Boundary value of the telescoping term at `k = 2n+1`, defined by the two top terms of
`F(n+1, ·)`. -/
noncomputable def ex362Gb (n : ℕ) : ℝ :=
  -((1 / 4) * ((n : ℝ) + 1) ^ 2 * (ex362F (n + 1) (2 * n + 1) + ex362F (n + 1) (2 * n + 2)))

lemma ex362_edge (n : ℕ) :
    -((2 * (n : ℝ) + 1) ^ 2) * ex362F n (2 * n) + (1 / 4) * ((n : ℝ) + 1) ^ 2 * ex362F (n + 1) (2 * n)
      = ex362Gb n - ex362G n (2 * n) := by
  have hF1 := ex362F_eq n (2 * n) 0 (by omega)
  have hF2 := ex362F_eq (n + 1) (2 * n) 2 (by omega)
  have hF3 := ex362F_eq (n + 1) (2 * n + 1) 1 (by omega)
  have hF4 := ex362F_eq (n + 1) (2 * n + 2) 0 (by omega)
  have s0 : ((-1 : ℝ)) ^ (2 * n) = 1 := by rw [pow_mul]; simp
  have s1 : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := by rw [pow_succ, s0]; simp
  have s2 : ((-1 : ℝ)) ^ (2 * n + 2) = 1 := by rw [pow_succ, s1]; simp
  have a1 : 2 * (2 * n) = 4 * n := by ring
  have a2 : 2 * (2 * n + 1) = 4 * n + 1 + 1 := by ring
  have a3 : 2 * (2 * n + 2) = 4 * n + 1 + 1 + 1 + 1 := by ring
  have a4 : 2 * n + 1 + 1 = 2 * n + 2 := by ring
  have e1 : 2 * n + 1 - 2 * n = 1 := by omega
  have e2 : 2 * n + 2 - 2 * n = 2 := by omega
  have e3 : 4 * n - 2 * (2 * n) = 0 := by omega
  have b1 : ((2 * n + 2).factorial : ℝ) = (2 * n + 2) * (2 * n + 1) * ((2 * n).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have b2 : ((2 * n + 1).factorial : ℝ) = (2 * n + 1) * ((2 * n).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have b3 : ((4 * n + 1 + 1).factorial : ℝ) = (4 * n + 2) * (4 * n + 1) * ((4 * n).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have b4 : ((4 * n + 1 + 1 + 1 + 1).factorial : ℝ) = (4 * n + 4) * (4 * n + 3) * (4 * n + 2)
      * (4 * n + 1) * ((4 * n).factorial : ℝ) := by
    simp only [Nat.factorial_succ]; push_cast; ring
  have p1 : (0 : ℝ) < (2 * n).factorial := by positivity
  have p2 : (0 : ℝ) < (4 * n).factorial := by positivity
  unfold ex362Gb ex362G
  rw [hF1, hF2, hF3, hF4, e1, e2, e3, s0, s1, s2, a1, a2, a3]
  simp only [a4, Nat.add_zero, Nat.mul_zero, Nat.factorial_zero, Nat.factorial_one, b1, b2, b3, b4]
  have c2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
  have c4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  simp only [c2, c4]
  push_cast
  unfold ex362R
  field_simp
  ring

lemma ex362G_zero (n : ℕ) : ex362G n 0 = 0 := by
  unfold ex362G ex362R
  simp

/-- The real-valued sum `f(n)`. -/
noncomputable def ex362f (n : ℕ) : ℝ := ∑ k ∈ range (2 * n + 1), ex362F n k

lemma ex362F_zero_of_lt (n k : ℕ) (h : 2 * n < k) : ex362F n k = 0 := by
  unfold ex362F
  rw [Nat.choose_eq_zero_of_lt h]; simp

lemma ex362f_rec (n : ℕ) : ((n : ℝ) + 1) ^ 2 * ex362f (n + 1) = 4 * (2 * (n : ℝ) + 1) ^ 2 * ex362f n := by
  -- telescoping over `k < 2n+1`
  let Gx : ℕ → ℝ := fun k => if k ≤ 2 * n then ex362G n k else ex362Gb n
  have hstep : ∀ k ∈ range (2 * n + 1),
      -((2 * (n : ℝ) + 1) ^ 2) * ex362F n k + (1 / 4) * ((n : ℝ) + 1) ^ 2 * ex362F (n + 1) k
        = Gx (k + 1) - Gx k := by
    intro k hk
    rw [mem_range] at hk
    by_cases hlt : k < 2 * n
    · obtain ⟨i, hi⟩ : ∃ i, 2 * n = k + 1 + i := ⟨2 * n - (k + 1), by omega⟩
      have h1 : k + 1 ≤ 2 * n := by omega
      simp only [Gx, h1, ite_true, show k ≤ 2 * n by omega]
      exact ex362_step n k i hi
    · have hk2 : k = 2 * n := by omega
      subst hk2
      simp only [Gx, show ¬ (2 * n + 1 ≤ 2 * n) by omega, le_refl, ite_true, ite_false]
      exact ex362_edge n
  have hsum := Finset.sum_congr rfl hstep
  rw [Finset.sum_range_sub (fun k => Gx k)] at hsum
  have hG0 : Gx 0 = 0 := by simp [Gx, ex362G_zero]
  have hG1 : Gx (2 * n + 1) = ex362Gb n := by simp [Gx]
  rw [hG0, hG1, sub_zero, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hf1 : ex362f (n + 1) = ∑ k ∈ range (2 * n + 1), ex362F (n + 1) k
      + ex362F (n + 1) (2 * n + 1) + ex362F (n + 1) (2 * n + 2) := by
    unfold ex362f
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ]
  have hn : -((2 * (n : ℝ) + 1) ^ 2) * ex362f n
      + (1 / 4) * ((n : ℝ) + 1) ^ 2 * ∑ k ∈ range (2 * n + 1), ex362F (n + 1) k = ex362Gb n := by
    simpa [ex362f] using hsum
  unfold ex362Gb at hn
  rw [hf1]
  linarith

/-- CO-046. For every natural `n`, the alternating sum
`∑_{k=0}^{2n} (-1)^k C(2n,k) C(2k,k) C(4n-2k,2n-k)` equals `C(2n,n)^2`; proved with the
Zeilberger recurrence `(n+1)^2 f(n+1) = 4 (2n+1)^2 f(n)` and its telescoping certificate. -/
@[kb "petkovsekwilfzeilberger1996" "Example 3.6.2, p. 56"]
theorem example_3_6_2 (n : ℕ) :
    (∑ k ∈ range (2 * n + 1), (-1 : ℤ) ^ k *
        (((2 * n).choose k * (2 * k).choose k * (4 * n - 2 * k).choose (2 * n - k) : ℕ) : ℤ))
      = (((2 * n).choose n : ℕ) : ℤ) ^ 2 := by
  have key : ex362f n = (Nat.centralBinom n : ℝ) ^ 2 := by
    induction n with
    | zero => simp [ex362f, ex362F]
    | succ n ih =>
      have hr := ex362f_rec n
      have hc : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
          = 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ n
      rw [ih] at hr
      have hpos : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hpos
      rw [hr]
      linear_combination (-(((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
        + 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ))) * hc
  have h2 : ((∑ k ∈ range (2 * n + 1), (-1 : ℤ) ^ k *
        (((2 * n).choose k * (2 * k).choose k * (4 * n - 2 * k).choose (2 * n - k) : ℕ) : ℤ) : ℤ) : ℝ)
      = ex362f n := by
    unfold ex362f ex362F
    push_cast
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [key, Nat.centralBinom_eq_two_mul_choose] at h2
  exact_mod_cast h2

end UndergradKB.Combinatorics.AeqB
