import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Certificates4

/-!
# Dougall's terminating well-poised balanced 7F6 sum (A = B, database item (VI), p. 54)

CO-366.  Summing the WZ equation `dougall_wz` over `k` gives the recurrence
`∑_k F(n+1,k) = ∑_k F(n,k)` for `F = T/S`; together with `∑_k F(0,k) = 1` this proves the sum.
The boundary terms `k = n, n+1` are handled by one rational-function identity (`dg_bdry`).
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset

/-! ### The boundary identity -/

set_option maxHeartbeats 1000000 in
theorem dg_bP (a b c d n : ℝ)
    (h1 : n + a ≠ 0) (h2 : 1 + d - a - (n + 1) ≠ 0) (h3 : 1 + d + n + n ≠ 0)
    (_h4 : a - d + n ≠ 0) (h5 : 1 + a - b + n ≠ 0) (h6 : 1 + a - c + n ≠ 0)
    (h7 : b + c + d - a + n ≠ 0) (h8 : d + 1 + n ≠ 0) (h9 : b + n ≠ 0) (h10 : c + n ≠ 0)
    (_h11 : 1 + 2 * a - b - c - d + n ≠ 0) (_h17 : -(n + 1) + n ≠ 0) :
    dgtau a d n n / dgr a b c d n
      = -((2 * n + a) * (n + 1) * (d - a) * (1 + a - b + n) * (1 + a - c + n) *
          (b + c + d - a + n)) /
        ((n + a) * (1 + d + 2 * n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n)) := by
  have h2' : d - a - n ≠ 0 := by intro h; apply h2; linarith
  have h3' : 1 + d + 2 * n ≠ 0 := by intro h; apply h3; linarith
  unfold dgtau dgr
  have e : 1 + d - a - (n + 1) + n = d - a := by ring
  have e2 : -(n + 1) + n = -1 := by ring
  rw [e, e2]
  have e3 : a - d + n = -(d - a - n) := by ring
  have h4' : d - a - n ≠ 0 := h2'
  have e4 : 1 + d - a - (n + 1) = d - a - n := by ring
  rw [e4, e3, show 1 + d + n + n = 1 + d + 2 * n by ring]
  have h12 : -(d - a - n) ≠ 0 := neg_ne_zero.2 h2'
  field_simp
  ring

theorem dg_abs4 (p w s x1 x2 x3 y m q1 q2 q3 g : ℝ) (hw : w ≠ 0) (hs : s ≠ 0) (hm : m ≠ 0)
    (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) (h3 : q3 ≠ 0) (hg : g ≠ 0) :
    p * (w / 2) * x1 * x2 * x3 * y * (-1) / (m * (s / 2) * q1 * q2 * q3 * g * w)
      = -(p * x1 * x2 * x3 * y) / (m * s * q1 * q2 * q3 * g) := by
  field_simp

set_option maxHeartbeats 1000000 in
theorem dg_brho (a b c d n : ℝ)
    (h5 : 1 + a - b + n ≠ 0) (h6 : 1 + a - c + n ≠ 0)
    (h7 : b + c + d - a + n ≠ 0) (_h12 : d / 2 + n ≠ 0) (h15 : d + 2 * n ≠ 0)
    (h16 : n + 1 ≠ 0) (h13 : 1 + d - a - (n + 1) + n ≠ 0) (h14 : 1 + d + (n + 1) + n ≠ 0) :
    dgrho a b c d (n + 1) n
      = -((d + n) * (d + b - a + n) * (d + c - a + n) * (1 + a - b - c + n) * (2 * n + 1 + a)) /
        ((n + 1) * (d + 2 * n) * (1 + a - b + n) * (1 + a - c + n) * (b + c + d - a + n) *
          (d - a)) := by
  have e : 1 + d - a - (n + 1) + n = d - a := by ring
  have h13' : d - a ≠ 0 := by rw [← e]; exact h13
  have h14' : 2 + d + 2 * n ≠ 0 := by intro h; apply h14; linarith
  unfold dgrho
  rw [e, show 1 + d + (n + 1) + n = 2 + d + 2 * n by ring,
    show 1 + d / 2 + n = (2 + d + 2 * n) / 2 by ring, show d / 2 + n = (d + 2 * n) / 2 by ring]
  rw [show n + 1 + a + n = 2 * n + 1 + a by ring, show -(n + 1) + n = -1 by ring]
  exact dg_abs4 _ _ _ _ _ _ _ _ _ _ _ _ h14' h15 h16 h5 h6 h7 h13'

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
theorem dg_bfin (a b c d n : ℝ)
    (h1 : n + a ≠ 0) (h3 : 1 + d + 2 * n ≠ 0)
    (h9 : b + n ≠ 0) (h10 : c + n ≠ 0)
    (h11 : 1 + 2 * a - b - c - d + n ≠ 0) (h15 : d + 2 * n ≠ 0) (h16 : n + 1 ≠ 0)
    (h5 : 1 + a - b + n ≠ 0) (h6 : 1 + a - c + n ≠ 0)
    (h7 : b + c + d - a + n ≠ 0) (h13 : d - a ≠ 0) :
    (-((2 * n + a) * (n + 1) * (d - a) * (1 + a - b + n) * (1 + a - c + n) *
          (b + c + d - a + n)) /
        ((n + a) * (1 + d + 2 * n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n))) *
      (1 + -((d + n) * (d + b - a + n) * (d + c - a + n) * (1 + a - b - c + n) *
          (2 * n + 1 + a)) /
        ((n + 1) * (d + 2 * n) * (1 + a - b + n) * (1 + a - c + n) * (b + c + d - a + n) *
          (d - a))) - 1 + dgR a b c d n n = 0 := by
  unfold dgR
  have h18 : (1 - (n : ℝ) + n) = 1 := by ring
  rw [h18]
  have h1' : a + n ≠ 0 := by rwa [add_comm]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- Ratio `T(n+1,k)/T(n,k)` also for `k = n` (the lemma `dgT_succ_n` stops at `k + 1 ≤ n`). -/
theorem dgT_succ_n' (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) (hk : k ≤ n) :
    dgT a b c d (n + 1) k = dgtau a d n k * dgT a b c d n k := by
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have y1 : (-((n : ℝ) + 1) + k) ≠ 0 := by intro hh; linarith
  have y2 : (1 + d - a - ((n : ℝ) + 1) + k) ≠ 0 := fun hh => h.dan k (by linarith)
  have y3 : (1 + d - a - ((n : ℝ) + 1)) ≠ 0 := fun hh => h.dan 0 (by push_cast; linarith)
  have y4 : (1 + d + (n : ℝ)) ≠ 0 := fun hh => h.dn 1 (by push_cast; linarith)
  have y5 : (1 + d + (n : ℝ) + k) ≠ 0 := fun hh => h.dn (k + 1) (by push_cast; linarith)
  have A1 := dpoch_up ((n : ℝ) + a) ((n : ℝ) + 1 + a) (by ring) h.an k
  have A2 := dpoch_dn (-((n : ℝ) + 1)) (-(n : ℝ)) (by ring) k y1
  have A3 := dpoch_dn (1 + d - a - ((n : ℝ) + 1)) (1 + d - a - n) (by ring) k y2
  have A4 := dpoch_up (1 + d + (n : ℝ)) (1 + d + ((n : ℝ) + 1)) (by ring) y4 k
  have b1 : NoNegInt (1 + d - a - n) := fun i hh => h.dan (i + 1) (by push_cast; linarith)
  have b2 : NoNegInt (1 + d + n) := fun i hh => h.dn (i + 1) (by push_cast; linarith)
  have c1 := dpoch_ne_zero b1 k
  have c2 := dpoch_ne_zero b2 k
  have c3 := dpoch_ne_zero h.d2 k
  have c4 := dpoch_ne_zero h.ab k
  have c5 := dpoch_ne_zero h.ac k
  have c6 := dpoch_ne_zero h.bcd k
  have c7 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have z1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold dgT dgtau
  push_cast
  rw [A1, A2, A3, A4]
  field_simp

theorem dgS_ne_zero (a b c d : ℝ) (n : ℕ) (h : DougallHyp a b c d n) : dgS a b c d n ≠ 0 := by
  unfold dgS
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (dpoch_ne_zero h.d1 n) (dpoch_ne_zero h.b0 n))
      (dpoch_ne_zero h.c0 n)) (dpoch_ne_zero h.e n))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (dpoch_ne_zero h.ad n) (dpoch_ne_zero h.ab n))
      (dpoch_ne_zero h.ac n)) (dpoch_ne_zero h.bcd n))

theorem dgF_succ_n' (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) (hk : k ≤ n) :
    dgF a b c d (n + 1) k = (dgtau a d n k / dgr a b c d n) * dgF a b c d n k := by
  unfold dgF
  rw [dgT_succ_n' a b c d n k h hk, dgS_succ a b c d n h, mul_div_mul_comm]

/-- The boundary identity at `k = n`. -/
theorem dg_bdry (a b c d : ℝ) (n : ℕ) (h : DougallHyp a b c d n) :
    dgtau a d n n / dgr a b c d n * (1 + dgrho a b c d ((n : ℝ) + 1) n) - 1
      + dgR a b c d n n = 0 := by
  have h1 : (n : ℝ) + a ≠ 0 := h.an
  have h2 : 1 + d - a - ((n : ℝ) + 1) ≠ 0 := fun hh => h.dan 0 (by push_cast; linarith)
  have h3 : 1 + d + (n : ℝ) + n ≠ 0 := fun hh => h.dn (n + 1) (by push_cast; linarith)
  have h4 : a - d + (n : ℝ) ≠ 0 := h.ad n
  have h5 : 1 + a - b + (n : ℝ) ≠ 0 := h.ab n
  have h6 : 1 + a - c + (n : ℝ) ≠ 0 := h.ac n
  have h7 : b + c + d - a + (n : ℝ) ≠ 0 := h.bcd n
  have h8 : d + 1 + (n : ℝ) ≠ 0 := h.d1 n
  have h9 : b + (n : ℝ) ≠ 0 := h.b0 n
  have h10 : c + (n : ℝ) ≠ 0 := h.c0 n
  have h11 : 1 + 2 * a - b - c - d + (n : ℝ) ≠ 0 := h.e n
  have h12 : d / 2 + (n : ℝ) ≠ 0 := h.d2 n
  have h13 : 1 + d - a - ((n : ℝ) + 1) + n ≠ 0 := fun hh => h.dan n (by linarith)
  have h14 : 1 + d + ((n : ℝ) + 1) + n ≠ 0 := fun hh => h.dn (n + 2) (by push_cast; linarith)
  have h15 : d + 2 * (n : ℝ) ≠ 0 := fun hh => h12 (by linarith)
  have h16 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h17 : -((n : ℝ) + 1) + n ≠ 0 := by intro hh; linarith
  have h3' : 1 + d + 2 * (n : ℝ) ≠ 0 := fun hh => h3 (by linarith)
  have h13' : d - a ≠ 0 := fun hh => h.dan n (by linarith)
  rw [dg_bP a b c d n h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h17,
    dg_brho a b c d n h5 h6 h7 h12 h15 h16 h13 h14]
  exact dg_bfin a b c d n h1 h3' h9 h10 h11 h15 h16 h5 h6 h7 h13'

/-! ### Summation -/

theorem dg_step (a b c d : ℝ) (n : ℕ) (h : DougallHyp a b c d n)
    (h' : DougallHyp a b c d (n + 1)) :
    ∑ k ∈ range (n + 2), dgF a b c d (n + 1) k = ∑ k ∈ range (n + 1), dgF a b c d n k := by
  set G : ℕ → ℝ := fun k => dgR a b c d n (k : ℝ) * dgF a b c d n k with hG
  have tele : ∑ k ∈ range n, (dgF a b c d (n + 1) k - dgF a b c d n k) = G n - G 0 := by
    rw [← Finset.sum_range_sub G n]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [dougall_wz a b c d n k h (Finset.mem_range.1 hk)]
    simp only [hG]
    push_cast
    rfl
  have G0 : G 0 = 0 := by simp [hG, dgR]
  rw [Finset.sum_sub_distrib] at tele
  have f1 := dgF_succ_n' a b c d n n h le_rfl
  have f2 := dgF_succ_k a b c d (n + 1) n h'
  have bd := dg_bdry a b c d n h
  push_cast at f2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (fun k => dgF a b c d n k)]
  have key : dgF a b c d (n + 1) n + dgF a b c d (n + 1) (n + 1) - dgF a b c d n n + G n = 0 := by
    rw [f2, f1]
    simp only [hG]
    linear_combination dgF a b c d n n * bd
  linarith

theorem dg_sumF (a b c d : ℝ) (n : ℕ) (h : ∀ m ≤ n, DougallHyp a b c d m) :
    ∑ k ∈ range (n + 1), dgF a b c d n k = 1 := by
  induction n with
  | zero =>
    have := dgS_ne_zero a b c d 0 (h 0 le_rfl)
    simp [dgF, dgT, dgS, dpoch]
  | succ n ih =>
    rw [dg_step a b c d n (h n (by omega)) (h (n + 1) le_rfl)]
    exact ih fun m hm => h m (by omega)

/-- CO-366 (in the parametrization of the summand `dgT`). Dougall's terminating well-poised
balanced `7F6` sum: `∑_{k=0}^{n} T(n,k) = S(n)`.  Lean adds the genericity hypothesis
`DougallHyp a b c d m` for every `m ≤ n` (no vanishing Pochhammer symbol in any denominator or
in the normalising right-hand side). -/
theorem dougall_sum_dg (a b c d : ℝ) (n : ℕ) (h : ∀ m ≤ n, DougallHyp a b c d m) :
    ∑ k ∈ range (n + 1), dgT a b c d n k = dgS a b c d n := by
  have hS := dgS_ne_zero a b c d n (h n le_rfl)
  have := dg_sumF a b c d n h
  unfold dgF at this
  rw [← Finset.sum_div, div_eq_one_iff_eq hS] at this
  exact this

/-- CO-366. Dougall's terminating well-poised balanced `7F6` sum in the book's parametrization:
for `1 + 2A = B + C + D + E - n`,
`∑_{k=0}^n (A)_k (1+A/2)_k (B)_k (C)_k (D)_k (E)_k (-n)_k /
  (k! (A/2)_k (1+A-B)_k (1+A-C)_k (1+A-D)_k (1+A-E)_k (1+A+n)_k)
 = (1+A)_n (1+A-B-C)_n (1+A-B-D)_n (1+A-C-D)_n /
   ((1+A-B)_n (1+A-C)_n (1+A-D)_n (1+A-B-C-D)_n)`.
Lean adds the genericity hypothesis that `DougallHyp` (the denominator Pochhammer symbols do not
vanish) holds for all `m ≤ n` with parameters `d = A`, `a = 1+2A-B-C-D`, `b = 1+A-C-D`,
`c = 1+A-B-D`. -/
@[kb "petkovsekwilfzeilberger1996" "text (VI) Dougall 7F6, p. 54"]
theorem dougall_sum (A B C D E : ℝ) (n : ℕ) (hE : 1 + 2 * A = B + C + D + E - n)
    (h : ∀ m ≤ n, DougallHyp (1 + 2 * A - B - C - D) (1 + A - C - D) (1 + A - B - D) A m) :
    ∑ k ∈ range (n + 1),
        dpoch A k * dpoch (1 + A / 2) k * dpoch B k * dpoch C k * dpoch D k * dpoch E k *
          dpoch (-(n : ℝ)) k /
        ((k.factorial : ℝ) * dpoch (A / 2) k * dpoch (1 + A - B) k * dpoch (1 + A - C) k *
          dpoch (1 + A - D) k * dpoch (1 + A - E) k * dpoch (1 + A + n) k)
      = dpoch (1 + A) n * dpoch (1 + A - B - C) n * dpoch (1 + A - B - D) n *
          dpoch (1 + A - C - D) n /
        (dpoch (1 + A - B) n * dpoch (1 + A - C) n * dpoch (1 + A - D) n *
          dpoch (1 + A - B - C - D) n) := by
  have key := dougall_sum_dg _ _ _ A n h
  have hEn : E = 1 + 2 * A - B - C - D + n := by linarith
  have eS : dgS (1 + 2 * A - B - C - D) (1 + A - C - D) (1 + A - B - D) A n
      = dpoch (1 + A) n * dpoch (1 + A - B - C) n * dpoch (1 + A - B - D) n *
          dpoch (1 + A - C - D) n /
        (dpoch (1 + A - B) n * dpoch (1 + A - C) n * dpoch (1 + A - D) n *
          dpoch (1 + A - B - C - D) n) := by
    unfold dgS
    rw [show A + 1 = 1 + A by ring,
      show 1 + 2 * (1 + 2 * A - B - C - D) - (1 + A - C - D) - (1 + A - B - D) - A
        = 1 + A - B - C by ring,
      show 1 + 2 * A - B - C - D - A = 1 + A - B - C - D by ring,
      show 1 + (1 + 2 * A - B - C - D) - (1 + A - C - D) = 1 + A - B by ring,
      show 1 + (1 + 2 * A - B - C - D) - (1 + A - B - D) = 1 + A - C by ring,
      show 1 + A - C - D + (1 + A - B - D) + A - (1 + 2 * A - B - C - D) = 1 + A - D by ring]
    ring
  have et : ∀ k : ℕ, dgT (1 + 2 * A - B - C - D) (1 + A - C - D) (1 + A - B - D) A n k
      = dpoch A k * dpoch (1 + A / 2) k * dpoch B k * dpoch C k * dpoch D k * dpoch E k *
          dpoch (-(n : ℝ)) k /
        ((k.factorial : ℝ) * dpoch (A / 2) k * dpoch (1 + A - B) k * dpoch (1 + A - C) k *
          dpoch (1 + A - D) k * dpoch (1 + A - E) k * dpoch (1 + A + n) k) := by
    intro k
    unfold dgT
    rw [show 1 + (1 + 2 * A - B - C - D) - (1 + A - C - D) - (1 + A - B - D) = D by ring,
      show A + (1 + A - C - D) - (1 + 2 * A - B - C - D) = B by ring,
      show A + (1 + A - B - D) - (1 + 2 * A - B - C - D) = C by ring,
      show (n : ℝ) + (1 + 2 * A - B - C - D) = E by rw [hEn]; ring,
      show 1 + (1 + 2 * A - B - C - D) - (1 + A - C - D) = 1 + A - B by ring,
      show 1 + (1 + 2 * A - B - C - D) - (1 + A - B - D) = 1 + A - C by ring,
      show 1 + A - C - D + (1 + A - B - D) + A - (1 + 2 * A - B - C - D) = 1 + A - D by ring,
      show 1 + A - (1 + 2 * A - B - C - D) - n = 1 + A - E by rw [hEn]; ring]
  rw [← eS, ← key]
  exact Finset.sum_congr rfl fun k _ => (et k).symm

end UndergradKB.Combinatorics.AeqB
