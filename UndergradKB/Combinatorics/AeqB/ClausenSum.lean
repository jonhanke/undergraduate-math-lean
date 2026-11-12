import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Certificates2
import UndergradKB.Combinatorics.AeqB.Certificates4

/-!
# Clausen's terminating `4F3` sum (A = B, item (V), p. 54)

Summing the WZ equation of `Certificates2` (`clausen_cert`) over `k` shows that
`n ↦ ∑_{k=0}^{n} F(n,k)` is constant (`clausen_wz_sum`); the constant is `F(0,0)` (a Gamma
expression, not `1`, with the normalisation `F = φ(k) φ(n-k) ψ(n)` used there).  Then
`F(n,k) = F(n,0) * (summand of the 4F3)` and `F(n,0) * (right side) = F(0,0)` give the
Pochhammer form `clausen_sum`.
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset

/-! ### Positivity and the diagonal boundary -/

theorem clPhi_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) : 0 < clPhi a b t := by
  unfold clPhi
  exact div_pos (mul_pos (gm_pos (by linarith)) (gm_pos (by linarith)))
    (mul_pos (gm_pos (by linarith)) (gm_pos (by linarith)))

theorem clPsi_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) : 0 < clPsi a b t := by
  unfold clPsi
  exact div_pos (mul_pos (mul_pos (gm_pos (by linarith)) (gm_pos (by linarith)))
    (gm_pos (by linarith)))
    (mul_pos (mul_pos (gm_pos (by linarith)) (gm_pos (by linarith))) (gm_pos (by linarith)))

theorem clR_zero (a b n : ℝ) : clR a b n 0 = 0 := by
  unfold clR; simp

theorem clR_diag (a b t : ℝ) : clR a b t t =
    (1 - 2 * a - 2 * b - 2 * t) * t * a * b * (2 + 2 * a + 2 * b + t) /
      ((2 * a + t) * (a + b + t) * (2 * b + t) * (1 + 2 * a + 2 * b)) := by
  unfold clR
  rw [show a - t + t = a by ring, show b - t + t = b by ring,
    show 2 + 2 * a + 2 * b - 2 * t + 3 * t = 2 + 2 * a + 2 * b + t by ring,
    show 1 - t + t = 1 by ring, show 1 + 2 * a + 2 * b - 2 * t + 2 * t = 1 + 2 * a + 2 * b by ring]
  ring

theorem cs_boundary_rat (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    clrPhi a b 0 * clrPsi a b t + clrPhi a b t * clrPsi a b t - 1 + clR a b t t = 0 := by
  rw [clR_diag]
  unfold clrPhi clrPsi
  have d1 : t + 1 ≠ 0 := by positivity
  have d2 : a + b + t + 1 / 2 ≠ 0 := by positivity
  have d3 : t + 2 * a ≠ 0 := by positivity
  have d4 : t + a + b ≠ 0 := by positivity
  have d5 : t + 2 * b ≠ 0 := by positivity
  have d6 : a + b + 0 + 1 / 2 ≠ 0 := by positivity
  have d7 : 1 + 2 * a + 2 * b ≠ 0 := by positivity
  have d8 : 2 * a + t ≠ 0 := by positivity
  have d9 : a + b + t ≠ 0 := by positivity
  have d10 : 2 * b + t ≠ 0 := by positivity
  have d11 : (0 : ℝ) + 1 ≠ 0 := by norm_num
  field_simp
  ring

theorem cs_boundary (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    clF a b (t + 1) t + clF a b (t + 1) (t + 1) - clF a b t t + clR a b t t * clF a b t t = 0 := by
  have h1 : clPhi a b 1 = clrPhi a b 0 * clPhi a b 0 := by
    have := clPhi_succ a b 0 ha hb le_rfl
    rwa [zero_add] at this
  have h2 := clPhi_succ a b t ha hb ht
  have h3 := clPsi_succ a b t ha hb ht
  unfold clF
  rw [show t + 1 - t = 1 by ring, show t + 1 - (t + 1) = 0 by ring, sub_self, h1, h2, h3]
  have key := cs_boundary_rat a b t ha hb ht
  linear_combination (clPhi a b t * clPhi a b 0 * clPsi a b t) * key

/-! ### The WZ sum -/

/-- CO-365 (support). The WZ sum of Clausen's identity is constant in `n`:
`∑_{k=0}^{n} F(n,k) = F(0,0)` for `F(n,k) = φ(k) φ(n-k) ψ(n)` and real `a, b > 0`. -/
theorem clausen_wz_sum (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∑ k ∈ range (n + 1), clF a b (n : ℝ) (k : ℝ) = clF a b 0 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    set f : ℕ → ℝ := fun k => clR a b (n : ℝ) (k : ℝ) * clF a b (n : ℝ) (k : ℝ) with hf
    have hstep : ∀ k ∈ range n, clF a b ((n : ℝ) + 1) k - clF a b n k = f (k + 1) - f k := by
      intro k hk
      have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
      have := clausen_cert a b n k ha hb (Nat.cast_nonneg k) (by exact_mod_cast hk')
      simp only [hf]; push_cast; exact this
    have key : ∑ k ∈ range n, (clF a b ((n : ℝ) + 1) k - clF a b n k) = f n - f 0 := by
      rw [Finset.sum_congr rfl hstep]; exact Finset.sum_range_sub f n
    rw [Finset.sum_sub_distrib] at key
    have hf0 : f 0 = 0 := by simp [hf, clR_zero]
    have hb' := cs_boundary a b n ha hb (Nat.cast_nonneg n)
    rw [Finset.sum_range_succ] at ih
    push_cast
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    simp only [hf] at key hf0
    linarith

/-! ### Conversion to the Pochhammer form -/

/-- The summand of the terminating `4F3` of Clausen's sum. -/
noncomputable def csT (a b : ℝ) (n k : ℕ) : ℝ :=
  dpoch a k * dpoch b k * dpoch (1 / 2 - a - b - n) k * dpoch (-(n : ℝ)) k /
    ((k.factorial : ℝ) * dpoch (a + b + 1 / 2) k * dpoch (1 - a - n) k * dpoch (1 - b - n) k)

/-- The right-hand side of Clausen's sum. -/
noncomputable def csRhs (a b : ℝ) (n : ℕ) : ℝ :=
  dpoch (2 * a) n * dpoch (a + b) n * dpoch (2 * b) n /
    (dpoch (2 * a + 2 * b) n * dpoch a n * dpoch b n)

theorem cs_dpoch_ne (x : ℝ) (k : ℕ) (h : ∀ i < k, x + i ≠ 0) : dpoch x k ≠ 0 := by
  induction k with
  | zero => simp [dpoch]
  | succ k ih =>
    simp only [dpoch]
    exact mul_ne_zero (ih fun i hi => h i (by omega)) (h k (by omega))

theorem cs_dpoch_pos (x : ℝ) (hx : 0 < x) (k : ℕ) : dpoch x k ≠ 0 :=
  cs_dpoch_ne x k fun i _ => by positivity

theorem cs_dpoch_neg (a : ℝ) (ha : 0 < a) (n k : ℕ) (hk : k ≤ n) (c : ℝ) (hc : c = 1 - a - n) :
    dpoch c k ≠ 0 := by
  refine cs_dpoch_ne c k fun i hi => ?_
  have : (i : ℝ) + 1 ≤ n := by exact_mod_cast (show i + 1 ≤ n by omega)
  intro h
  linarith

theorem csT_succ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n k : ℕ) (hk : k + 1 ≤ n) :
    csT a b n (k + 1) = ((a + k) * (b + k) * (1 / 2 - a - b - n + k) * (-(n : ℝ) + k) /
      ((k + 1) * (a + b + 1 / 2 + k) * (1 - a - n + k) * (1 - b - n + k))) * csT a b n k := by
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have e1 := cs_dpoch_pos (a + b + 1 / 2) (by positivity) k
  have e2 := cs_dpoch_neg a ha n k (by omega) (1 - a - n) rfl
  have e3 := cs_dpoch_neg b hb n k (by omega) (1 - b - n) rfl
  have z1 : (1 - a - n + k : ℝ) ≠ 0 := by intro h; linarith
  have z2 : (1 - b - n + k : ℝ) ≠ 0 := by intro h; linarith
  have z3 : (a + b + 1 / 2 + k : ℝ) ≠ 0 := by positivity
  have z4 : (k.factorial : ℝ) ≠ 0 := by positivity
  have z5 : (k : ℝ) + 1 ≠ 0 := by positivity
  unfold csT
  simp only [dpoch, Nat.factorial_succ]
  push_cast
  field_simp

theorem cs_ratio (a b n k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k) (hkn : k + 1 ≤ n) :
    clrPhi a b k / clrPhi a b (n - k - 1) =
      (a + k) * (b + k) * (1 / 2 - a - b - n + k) * (-n + k) /
        ((k + 1) * (a + b + 1 / 2 + k) * (1 - a - n + k) * (1 - b - n + k)) := by
  unfold clrPhi
  have h1 : a + (n - k - 1) ≠ 0 := by intro h; linarith
  have h2 : b + (n - k - 1) ≠ 0 := by intro h; linarith
  have h3 : n - k - 1 + 1 ≠ 0 := by intro h; linarith
  have h4 : a + b + (n - k - 1) + 1 / 2 ≠ 0 := by intro h; linarith
  have h5 : k + 1 ≠ 0 := by intro h; linarith
  have h6 : a + b + k + 1 / 2 ≠ 0 := by intro h; linarith
  have h7 : a + b + 1 / 2 + k ≠ 0 := by intro h; linarith
  have h8 : 1 - a - n + k ≠ 0 := by intro h; linarith
  have h9 : 1 - b - n + k ≠ 0 := by intro h; linarith
  have h10 : (a + k) * (b + k) ≠ 0 := by positivity
  field_simp
  ring

theorem cs_F_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∀ k : ℕ, k ≤ n → clF a b (n : ℝ) (k : ℝ) = clF a b n 0 * csT a b n k := by
  intro k
  induction k with
  | zero => intro _; simp [csT, dpoch]
  | succ k ih =>
    intro hk
    have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    push_cast
    rw [clF_succ_k a b n k ha hb (Nat.cast_nonneg k) hk', cs_ratio a b n k ha hb (Nat.cast_nonneg k) hk',
      ih (by omega), csT_succ a b ha hb n k hk]
    ring

theorem csRhs_succ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    csRhs a b (n + 1) = csRhs a b n *
      ((2 * a + n) * (a + b + n) * (2 * b + n) / ((2 * a + 2 * b + n) * (a + n) * (b + n))) := by
  have e1 := cs_dpoch_pos (2 * a + 2 * b) (by positivity) n
  have e2 := cs_dpoch_pos a ha n
  have e3 := cs_dpoch_pos b hb n
  have z1 : (2 * a + 2 * b + n : ℝ) ≠ 0 := by positivity
  have z2 : (a + n : ℝ) ≠ 0 := by positivity
  have z3 : (b + n : ℝ) ≠ 0 := by positivity
  unfold csRhs
  simp only [dpoch]
  field_simp

theorem cs_rat_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ht : 0 ≤ t) :
    clrPhi a b t * clrPsi a b t *
      ((2 * a + t) * (a + b + t) * (2 * b + t) / ((2 * a + 2 * b + t) * (a + t) * (b + t))) = 1 := by
  unfold clrPhi clrPsi
  have d1 : t + 1 ≠ 0 := by positivity
  have d2 : a + b + t + 1 / 2 ≠ 0 := by positivity
  have d3 : t + 2 * a ≠ 0 := by positivity
  have d4 : t + a + b ≠ 0 := by positivity
  have d5 : t + 2 * b ≠ 0 := by positivity
  have d6 : 2 * a + 2 * b + t ≠ 0 := by positivity
  have d7 : a + t ≠ 0 := by positivity
  have d8 : b + t ≠ 0 := by positivity
  have d9 : 2 * a + t ≠ 0 := by positivity
  have d10 : a + b + t ≠ 0 := by positivity
  have d11 : 2 * b + t ≠ 0 := by positivity
  field_simp
  ring

theorem cs_F0 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    clF a b (n : ℝ) 0 * csRhs a b n = clF a b 0 0 := by
  induction n with
  | zero => simp [csRhs, dpoch]
  | succ n ih =>
    have hs : clF a b ((n + 1 : ℕ) : ℝ) 0 = clrPhi a b n * clrPsi a b n * clF a b n 0 := by
      push_cast
      unfold clF
      rw [sub_zero, sub_zero, clPhi_succ a b n ha hb (Nat.cast_nonneg n),
        clPsi_succ a b n ha hb (Nat.cast_nonneg n)]
      ring
    rw [csRhs_succ a b ha hb, hs]
    have hr := cs_rat_one a b ha hb n (Nat.cast_nonneg n)
    calc _ = (clF a b n 0 * csRhs a b n) *
          (clrPhi a b n * clrPsi a b n *
            ((2 * a + n) * (a + b + n) * (2 * b + n) / ((2 * a + 2 * b + n) * (a + n) * (b + n))))
          := by ring
      _ = _ := by rw [hr, mul_one]; exact ih

theorem clF_zero_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : clF a b 0 0 ≠ 0 := by
  unfold clF
  exact (mul_pos (mul_pos (clPhi_pos a b 0 ha hb le_rfl) (clPhi_pos a b _ ha hb (by norm_num)))
    (clPsi_pos a b 0 ha hb le_rfl)).ne'

/-- CO-365. Clausen's terminating `4F3` sum (book p. 54, item (V)): for a natural number `n`,
`∑_{k=0}^{n} (a)_k (b)_k (1/2-a-b-n)_k (-n)_k / (k! (a+b+1/2)_k (1-a-n)_k (1-b-n)_k)
  = (2a)_n (a+b)_n (2b)_n / ((2a+2b)_n (a)_n (b)_n)`.
(These are the book's parameters `d = -n`, `c = 1/2-a-b-n`, `e = a+b+1/2`, `f = 1-a-n`,
`g = 1-b-n`.)  Lean adds the genericity hypotheses `a, b > 0`, which make every denominator
nonzero; the book states the identity for generic parameters. -/
@[kb "petkovsekwilfzeilberger1996" "text (V) Clausen 4F3, p. 54"]
theorem clausen_sum (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∑ k ∈ range (n + 1),
        dpoch a k * dpoch b k * dpoch (1 / 2 - a - b - n) k * dpoch (-(n : ℝ)) k /
          ((k.factorial : ℝ) * dpoch (a + b + 1 / 2) k * dpoch (1 - a - n) k *
            dpoch (1 - b - n) k)
      = dpoch (2 * a) n * dpoch (a + b) n * dpoch (2 * b) n /
          (dpoch (2 * a + 2 * b) n * dpoch a n * dpoch b n) := by
  have hC := clF_zero_pos a b ha hb
  have h0 := cs_F0 a b ha hb n
  have hsum := clausen_wz_sum a b ha hb n
  rw [Finset.sum_congr rfl (fun k hk => cs_F_eq a b ha hb n k
    (by have := Finset.mem_range.1 hk; omega)), ← Finset.mul_sum] at hsum
  have hne : clF a b (n : ℝ) 0 ≠ 0 := by
    intro h; rw [h, zero_mul] at h0; exact hC h0.symm
  exact mul_left_cancel₀ hne (hsum.trans h0.symm)

end UndergradKB.Combinatorics.AeqB
