import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import UndergradKB.Combinatorics.AeqB.Certificates
import UndergradKB.Combinatorics.AeqB.WZProof

/-!
# More WZ certificates (Petkovsek–Wilf–Zeilberger, Section 7.2, items (II), (V), (VI))

Kummer's `2F1(-1)` identity (factorial form, integer parameter `c`), Clausen's `4F3` identity
(Gamma-function form, real parameters `a, b > 0`), and Dougall's `7F6` identity (Pochhammer
form, generic real parameters).  As in `Certificates`, each statement says that `(F, R F)`
satisfies the WZ equation `F(n+1,k) - F(n,k) = R(n,k+1) F(n,k+1) - R(n,k) F(n,k)` at all points
where the summand is defined by nonvanishing factors.
-/

namespace UndergradKB.Combinatorics.AeqB

open scoped Nat

/-! ### Kummer -/

/-- The summand of Kummer's identity (book p. 136 (II)) in factorial form, for an integer `c`. -/
def kumF (c n k : ℤ) : ℚ :=
  (-1 : ℚ) ^ (n + k) * fct (2 * n + c - 1) * fct n * fct (n + c - 1) /
    (fct (2 * n + c - 1 - k) * fct (2 * n - k) * fct (c + k - 1) * fct k)

/-- The certificate of Kummer's identity. -/
def kumR (c n k : ℤ) : ℚ :=
  (k : ℚ) * ((k : ℚ) + c - 1) *
    (2 + 4 * c + (c : ℚ) ^ 2 - 3 * k - 2 * c * k + (k : ℚ) ^ 2 + 10 * n + 7 * c * n - 6 * k * n
      + 10 * (n : ℚ) ^ 2) /
  (2 * (2 * (n : ℚ) - k + c + 1) * (2 * (n : ℚ) - k + c) * (2 * (n : ℚ) - k + 2) *
    (2 * (n : ℚ) - k + 1))

/-- Ratio of consecutive terms of `kumF` in `n`. -/
theorem kumF_succ_n (c n k : ℤ) (hc : 1 ≤ c) (hn : 0 ≤ n) (_hk : 0 ≤ k) (hkn : k + 1 ≤ 2 * n) :
    kumF c (n + 1) k = (-((2 * (n : ℚ) + c + 1) * (2 * n + c) * (n + 1) * (n + c)) /
      ((2 * (n : ℚ) + c + 1 - k) * (2 * n + c - k) * (2 * n + 2 - k) * (2 * n + 1 - k))) *
      kumF c n k := by
  unfold kumF
  have e1 := fct_rec2 (2 * n + c - 1) (2 * n + c) (by ring) (by omega)
  have e1' := fct_rec2 (2 * n + c) (2 * n + c + 1) (by ring) (by omega)
  have e2 := fct_rec2 n (n + 1) (by ring) (by omega)
  have e3 := fct_rec2 (n + c - 1) (n + c) (by ring) (by omega)
  have e4' := fct_rec2 (2 * n + c - 1 - k) (2 * n + c - k) (by ring) (by omega)
  have e4'' := fct_rec2 (2 * n + c - k) (2 * n + c + 1 - k) (by ring) (by omega)
  have e5' := fct_rec2 (2 * n - k) (2 * n + 1 - k) (by ring) (by omega)
  have e5'' := fct_rec2 (2 * n + 1 - k) (2 * n + 2 - k) (by ring) (by omega)
  have s1 : (-1 : ℚ) ^ (n + 1 + k) = -(-1 : ℚ) ^ (n + k) := by
    rw [show n + 1 + k = (n + k) + 1 by ring, zpow_add_one₀ (by norm_num)]; ring
  simp only [show 2 * (n + 1) + c - 1 = 2 * n + c + 1 by ring,
    show n + 1 + c - 1 = n + c by ring, show 2 * (n + 1) - k = 2 * n + 2 - k by ring, s1]
  rw [e1', e1, e2, e3, e4'', e4', e5'', e5']
  have a1 := fct_ne_zero (2 * n + c - 1)
  have a2 := fct_ne_zero n
  have a3 := fct_ne_zero (n + c - 1)
  have a4 := fct_ne_zero (2 * n + c - 1 - k)
  have a5 := fct_ne_zero (2 * n - k)
  have a6 := fct_ne_zero (c + k - 1)
  have a7 := fct_ne_zero k
  have p0 : (-1 : ℚ) ^ (n + k) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have y1 := nz_of_int (m := 2 * n + c + 1 - k) (by omega)
  have y2 := nz_of_int (m := 2 * n + c - k) (by omega)
  have y3 := nz_of_int (m := 2 * n + 2 - k) (by omega)
  have y4 := nz_of_int (m := 2 * n + 1 - k) (by omega)
  push_cast at y1 y2 y3 y4 ⊢
  field_simp

/-- Ratio of consecutive terms of `kumF` in `k`. -/
theorem kumF_succ_k (c n k : ℤ) (hc : 1 ≤ c) (_hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k + 1 ≤ 2 * n) :
    kumF c n (k + 1) = (-((2 * (n : ℚ) + c - 1 - k) * (2 * n - k)) / ((c + k) * (k + 1))) *
      kumF c n k := by
  unfold kumF
  have e4 := fct_rec2 (2 * n + c - 2 - k) (2 * n + c - 1 - k) (by ring) (by omega)
  have e5 := fct_rec2 (2 * n - k - 1) (2 * n - k) (by ring) (by omega)
  have e6 := fct_rec2 (c + k - 1) (c + k) (by ring) (by omega)
  have e7 := fct_rec2 k (k + 1) (by ring) (by omega)
  have s2 : (-1 : ℚ) ^ (n + (k + 1)) = -(-1 : ℚ) ^ (n + k) := by
    rw [show n + (k + 1) = (n + k) + 1 by ring, zpow_add_one₀ (by norm_num)]; ring
  simp only [show 2 * n + c - 1 - (k + 1) = 2 * n + c - 2 - k by ring,
    show 2 * n - (k + 1) = 2 * n - k - 1 by ring,
    show c + (k + 1) - 1 = c + k by ring, s2]
  rw [e4, e5, e6, e7]
  have a1 := fct_ne_zero (2 * n + c - 2 - k)
  have a2 := fct_ne_zero (2 * n - k - 1)
  have a3 := fct_ne_zero (c + k - 1)
  have a4 := fct_ne_zero k
  have p0 : (-1 : ℚ) ^ (n + k) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have y1 := nz_of_int (m := 2 * n + c - 1 - k) (by omega)
  have y2 := nz_of_int (m := 2 * n - k) (by omega)
  have y3 := nz_of_int (m := c + k) (by omega)
  have y4 := nz_of_int (m := k + 1) (by omega)
  push_cast at y1 y2 y3 y4 ⊢
  field_simp

set_option maxRecDepth 100000 in
/-- CO-450. Kummer's `2F1(-1)` identity is certified by the book's rational function
`R(n,k) = k (k+c-1) (2+4c+c²-3k-2ck+k²+10n+7cn-6kn+10n²) /
(2 (2n-k+c+1)(2n-k+c)(2n-k+2)(2n-k+1))`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 136 (II)"]
theorem kummer_cert (c n k : ℤ) (hc : 1 ≤ c) (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k + 1 ≤ 2 * n) :
    kumF c (n + 1) k - kumF c n k
      = kumR c n (k + 1) * kumF c n (k + 1) - kumR c n k * kumF c n k := by
  refine wz_eq_of_ratio_identity (kumF c) (kumR c) n k _ _ (kumF_succ_n c n k hc hn hk hkn)
    (kumF_succ_k c n k hc hn hk hkn) ?_
  unfold kumR
  have y1 := nz_of_int (m := 2 * n - k + c + 1) (by omega)
  have y2 := nz_of_int (m := 2 * n - k + c) (by omega)
  have y3 := nz_of_int (m := 2 * n - k + 2) (by omega)
  have y4 := nz_of_int (m := 2 * n - k + 1) (by omega)
  have y5 := nz_of_int (m := 2 * n - (k + 1) + c + 1) (by omega)
  have y6 := nz_of_int (m := 2 * n - (k + 1) + c) (by omega)
  have y7 := nz_of_int (m := 2 * n - (k + 1) + 2) (by omega)
  have y8 := nz_of_int (m := 2 * n - (k + 1) + 1) (by omega)
  have x1 := nz_of_int (m := 2 * n + c + 1 - k) (by omega)
  have x2 := nz_of_int (m := 2 * n + c - k) (by omega)
  have x3 := nz_of_int (m := 2 * n + 2 - k) (by omega)
  have x4 := nz_of_int (m := 2 * n + 1 - k) (by omega)
  have x5 := nz_of_int (m := c + k) (by omega)
  have x6 := nz_of_int (m := k + 1) (by omega)
  push_cast at y1 y2 y3 y4 y5 y6 y7 y8 x1 x2 x3 x4 x5 x6 ⊢
  rw [show 2 * (n : ℚ) - (k + 1) + c + 1 = 2 * n - k + c by ring,
    show 2 * (n : ℚ) - (k + 1) + c = 2 * n - k + c - 1 by ring,
    show 2 * (n : ℚ) - (k + 1) + 2 = 2 * n - k + 1 by ring,
    show 2 * (n : ℚ) - (k + 1) + 1 = 2 * n - k by ring] at *
  rw [show 2 * (n : ℚ) + c + 1 - k = 2 * n - k + c + 1 by ring,
    show 2 * (n : ℚ) + c - k = 2 * n - k + c by ring,
    show 2 * (n : ℚ) + 2 - k = 2 * n - k + 2 by ring,
    show 2 * (n : ℚ) + 1 - k = 2 * n - k + 1 by ring] at *
  field_simp
  ring

/-! ### Clausen -/

/-- `x!` for a real `x > -1`, as `Γ(x+1)`. -/
noncomputable def gm (x : ℝ) : ℝ := Real.Gamma (x + 1)

theorem gm_pos {x : ℝ} (hx : -1 < x) : 0 < gm x := Real.Gamma_pos_of_pos (by linarith)

theorem gm_succ (x y : ℝ) (h : y = x + 1) (hx : -1 < x) : gm y = y * gm x := by
  unfold gm
  rw [h, show x + 1 + 1 = (x + 1) + 1 by ring, Real.Gamma_add_one (by linarith)]

/-- `φ(t) = (a+t-1)! (b+t-1)! / (t! (a+b+t-1/2)!)` of Clausen's identity (book p. 137 (V)). -/
noncomputable def clPhi (a b t : ℝ) : ℝ :=
  gm (a + t - 1) * gm (b + t - 1) / (gm t * gm (-1 / 2 + a + b + t))

/-- `ψ(t) = (t+a+b-1/2)! t! (t+2a+2b-1)! / ((t+2a-1)! (t+a+b-1)! (t+2b-1)!)`. -/
noncomputable def clPsi (a b t : ℝ) : ℝ :=
  gm (t + a + b - 1 / 2) * gm t * gm (t + 2 * a + 2 * b - 1) /
    (gm (t + 2 * a - 1) * gm (t + a + b - 1) * gm (t + 2 * b - 1))

/-- The summand `F(n,k) = φ(k) φ(n-k) ψ(n)` of Clausen's identity. -/
noncomputable def clF (a b : ℝ) (n k : ℝ) : ℝ := clPhi a b k * clPhi a b (n - k) * clPsi a b n

/-- The certificate of Clausen's identity. -/
noncomputable def clR (a b n k : ℝ) : ℝ :=
  (1 - 2 * a - 2 * b - 2 * k) * k * (a - k + n) * (b - k + n) * (2 + 2 * a + 2 * b - 2 * k + 3 * n) /
    ((2 * a + n) * (a + b + n) * (2 * b + n) * (1 - k + n) * (1 + 2 * a + 2 * b - 2 * k + 2 * n))

/-- The ratio `φ(t+1)/φ(t)`. -/
noncomputable def clrPhi (a b t : ℝ) : ℝ := (a + t) * (b + t) / ((t + 1) * (a + b + t + 1 / 2))

/-- The ratio `ψ(t+1)/ψ(t)`. -/
noncomputable def clrPsi (a b t : ℝ) : ℝ :=
  (t + a + b + 1 / 2) * (t + 1) * (t + 2 * a + 2 * b) / ((t + 2 * a) * (t + a + b) * (t + 2 * b))

theorem clPhi_succ (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    clPhi a b (t + 1) = clrPhi a b t * clPhi a b t := by
  unfold clPhi clrPhi
  have g1 := gm_succ (a + t - 1) (a + (t + 1) - 1) (by ring) (by linarith)
  have g2 := gm_succ (b + t - 1) (b + (t + 1) - 1) (by ring) (by linarith)
  have g3 := gm_succ t (t + 1) rfl (by linarith)
  have g4 := gm_succ (-1 / 2 + a + b + t) (-1 / 2 + a + b + (t + 1)) (by ring) (by linarith)
  rw [g1, g2, g3, g4, show a + (t + 1) - 1 = a + t by ring, show b + (t + 1) - 1 = b + t by ring,
    show -1 / 2 + a + b + (t + 1) = a + b + t + 1 / 2 by ring]
  have h3 := (gm_pos (show -1 < t by linarith)).ne'
  have h4 := (gm_pos (show -1 < -1 / 2 + a + b + t by linarith)).ne'
  have z1 : t + 1 ≠ 0 := by positivity
  have z3 : a + b + t + 1 / 2 ≠ 0 := by positivity
  field_simp

theorem clPsi_succ (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    clPsi a b (t + 1) = clrPsi a b t * clPsi a b t := by
  unfold clPsi clrPsi
  have g1 := gm_succ (t + a + b - 1 / 2) (t + 1 + a + b - 1 / 2) (by ring) (by linarith)
  have g2 := gm_succ t (t + 1) rfl (by linarith)
  have g3 := gm_succ (t + 2 * a + 2 * b - 1) (t + 1 + 2 * a + 2 * b - 1) (by ring) (by linarith)
  have g4 := gm_succ (t + 2 * a - 1) (t + 1 + 2 * a - 1) (by ring) (by linarith)
  have g5 := gm_succ (t + a + b - 1) (t + 1 + a + b - 1) (by ring) (by linarith)
  have g6 := gm_succ (t + 2 * b - 1) (t + 1 + 2 * b - 1) (by ring) (by linarith)
  rw [g1, g2, g3, g4, g5, g6, show t + 1 + a + b - 1 / 2 = t + a + b + 1 / 2 by ring,
    show t + 1 + 2 * a + 2 * b - 1 = t + 2 * a + 2 * b by ring,
    show t + 1 + 2 * a - 1 = t + 2 * a by ring, show t + 1 + a + b - 1 = t + a + b by ring,
    show t + 1 + 2 * b - 1 = t + 2 * b by ring]
  have h1 := (gm_pos (show -1 < t + 2 * a - 1 by linarith)).ne'
  have h2 := (gm_pos (show -1 < t + a + b - 1 by linarith)).ne'
  have h3 := (gm_pos (show -1 < t + 2 * b - 1 by linarith)).ne'
  have z4 : t + 2 * a ≠ 0 := by positivity
  have z5 : t + a + b ≠ 0 := by positivity
  have z6 : t + 2 * b ≠ 0 := by positivity
  field_simp

theorem clrPhi_ne_zero (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    clrPhi a b t ≠ 0 := by
  unfold clrPhi; positivity

theorem clF_succ_n (a b n k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k) (hkn : k + 1 ≤ n) :
    clF a b (n + 1) k = (clrPhi a b (n - k) * clrPsi a b n) * clF a b n k := by
  unfold clF
  rw [show n + 1 - k = (n - k) + 1 by ring, clPhi_succ a b (n - k) ha hb (by linarith),
    clPsi_succ a b n ha hb (by linarith)]
  ring

theorem clF_succ_k (a b n k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k) (hkn : k + 1 ≤ n) :
    clF a b n (k + 1) = (clrPhi a b k / clrPhi a b (n - k - 1)) * clF a b n k := by
  unfold clF
  have h1 := clPhi_succ a b k ha hb hk
  have h2 := clPhi_succ a b (n - k - 1) ha hb (by linarith)
  rw [show n - k - 1 + 1 = n - k by ring] at h2
  have h3 := clrPhi_ne_zero a b (n - k - 1) ha hb (by linarith)
  rw [h1, show n - (k + 1) = n - k - 1 by ring, h2]
  field_simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The rational-function identity behind Clausen's certificate, with `n = m + k + 1`. -/
theorem clausen_rat' (a b m k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k) (hm : 0 ≤ m) :
    clrPhi a b (m + 1) * clrPsi a b (m + k + 1) - 1
      = clR a b (m + k + 1) (k + 1) * (clrPhi a b k / clrPhi a b m) - clR a b (m + k + 1) k := by
  have d1 : 2 * a + (m + k + 1) ≠ 0 := by positivity
  have d2 : a + b + (m + k + 1) ≠ 0 := by positivity
  have d3 : 2 * b + (m + k + 1) ≠ 0 := by positivity
  have d1' : m + k + 1 + 2 * a ≠ 0 := by positivity
  have d2' : m + k + 1 + a + b ≠ 0 := by positivity
  have d3' : m + k + 1 + 2 * b ≠ 0 := by positivity
  have p1 : m + 2 ≠ 0 := by positivity
  have p2 : a + b + m + 3 / 2 ≠ 0 := by positivity
  have p3 : m + 1 ≠ 0 := by positivity
  have p4 : a + b + m + 1 / 2 ≠ 0 := by positivity
  have p5 : k + 1 ≠ 0 := by positivity
  have p6 : a + b + k + 1 / 2 ≠ 0 := by positivity
  have p7 : a + m ≠ 0 := by positivity
  have p8 : b + m ≠ 0 := by positivity
  have p9 : a + b + (m + 1) + 1 / 2 ≠ 0 := by positivity
  have p10 : m + 1 + 1 ≠ 0 := by positivity
  have L1 : clR a b (m + k + 1) (k + 1) * (clrPhi a b k / clrPhi a b m)
      = -((a + k) * (b + k) * (2 * a + 2 * b + 3 * m + k + 3)) /
        ((2 * a + (m + k + 1)) * (a + b + (m + k + 1)) * (2 * b + (m + k + 1))) := by
    unfold clR clrPhi
    have q1 : 1 - (k + 1) + (m + k + 1) ≠ 0 := by
      rw [show 1 - (k + 1) + (m + k + 1) = m + 1 by ring]; positivity
    have q2 : 1 + 2 * a + 2 * b - 2 * (k + 1) + 2 * (m + k + 1) ≠ 0 := by
      rw [show 1 + 2 * a + 2 * b - 2 * (k + 1) + 2 * (m + k + 1) = 1 + 2 * a + 2 * b + 2 * m by ring]
      positivity
    have q4 : m + 1 ≠ 0 := by positivity
    field_simp
    ring
  have L0 : clR a b (m + k + 1) k
      = (1 - 2 * a - 2 * b - 2 * k) * k * ((a + m + 1) * (b + m + 1) * (2 * a + 2 * b + 3 * m + k + 5)) /
        ((2 * a + (m + k + 1)) * (a + b + (m + k + 1)) * (2 * b + (m + k + 1)) *
          ((m + 2) * (3 + 2 * a + 2 * b + 2 * m))) := by
    unfold clR
    have q1 : 1 - k + (m + k + 1) ≠ 0 := by
      rw [show 1 - k + (m + k + 1) = m + 2 by ring]; positivity
    have q2 : 1 + 2 * a + 2 * b - 2 * k + 2 * (m + k + 1) ≠ 0 := by
      rw [show 1 + 2 * a + 2 * b - 2 * k + 2 * (m + k + 1) = 3 + 2 * a + 2 * b + 2 * m by ring]
      positivity
    have q3 : 3 + 2 * a + 2 * b + 2 * m ≠ 0 := by positivity
    field_simp
    ring
  rw [L1, L0]
  unfold clrPhi clrPsi
  have q3 : 3 + 2 * a + 2 * b + 2 * m ≠ 0 := by positivity
  field_simp
  ring

/-- The rational-function identity behind Clausen's certificate. -/
theorem clausen_rat (a b n k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k) (hkn : k + 1 ≤ n) :
    clrPhi a b (n - k) * clrPsi a b n - 1
      = clR a b n (k + 1) * (clrPhi a b k / clrPhi a b (n - k - 1)) - clR a b n k := by
  obtain ⟨m, hm, rfl⟩ : ∃ m, 0 ≤ m ∧ n = m + k + 1 := ⟨n - k - 1, by linarith, by ring⟩
  rw [show m + k + 1 - k = m + 1 by ring, add_sub_cancel_right]
  exact clausen_rat' a b m k ha hb hk hm

/-- CO-453. Clausen's `4F3` identity is certified by the book's
`R(n,k) = (1-2a-2b-2k) k (a-k+n)(b-k+n)(2+2a+2b-2k+3n) /
((2a+n)(a+b+n)(2b+n)(1-k+n)(1+2a+2b-2k+2n))` for `F(n,k) = φ(k) φ(n-k) ψ(n)`
(factorials of real arguments are values of the Gamma function; parameters `a, b > 0`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 137 (V)"]
theorem clausen_cert (a b n k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k) (hkn : k + 1 ≤ n) :
    clF a b (n + 1) k - clF a b n k
      = clR a b n (k + 1) * clF a b n (k + 1) - clR a b n k * clF a b n k := by
  rw [clF_succ_n a b n k ha hb hk hkn, clF_succ_k a b n k ha hb hk hkn]
  generalize clF a b n k = X
  linear_combination X * clausen_rat a b n k ha hb hk hkn

/-- CO-453, integer form: for integers `0 ≤ k < n`. -/
theorem clausen_cert_int (a b : ℝ) (n k : ℤ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k)
    (hkn : k + 1 ≤ n) :
    clF a b ((n : ℝ) + 1) k - clF a b n k
      = clR a b n ((k : ℝ) + 1) * clF a b n ((k : ℝ) + 1) - clR a b n k * clF a b n k :=
  clausen_cert a b n k ha hb (by exact_mod_cast hk) (by exact_mod_cast hkn)

end UndergradKB.Combinatorics.AeqB
