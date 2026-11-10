import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import UndergradKB.Common.Attr

/-!
# Dougall's 7F6 identity: WZ certificate (A = B, §7.2, p. 137)

CO-454.  The certificate printed in the book is wrong; the corrected certificate `dgR` is
verified.  The rational-function identity is split into three pieces (`dg_S1`, `dg_S2`,
`dg_S3`) to keep `ring` and `field_simp` fast.
-/

namespace UndergradKB.Combinatorics.AeqB

/-! ### Dougall -/

/-- Rising factorial `(x)_k = x (x+1) ⋯ (x+k-1)`. -/
def dpoch (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => dpoch x k * (x + k)

/-- `x` is not a nonpositive integer: `x + i ≠ 0` for every natural `i`. -/
def NoNegInt (x : ℝ) : Prop := ∀ i : ℕ, x + i ≠ 0

theorem dpoch_ne_zero {x : ℝ} (hx : NoNegInt x) (k : ℕ) : dpoch x k ≠ 0 := by
  induction k with
  | zero => simp [dpoch]
  | succ k ih => simp only [dpoch]; exact mul_ne_zero ih (hx k)

theorem NoNegInt.add_nat {x : ℝ} (hx : NoNegInt x) (m : ℕ) : NoNegInt (x + m) := fun i => by
  have := hx (m + i)
  push_cast at this
  rwa [← add_assoc] at this

theorem dpoch_shift (x y : ℝ) (h : y = x + 1) (k : ℕ) :
    dpoch y k * x = dpoch x k * (x + k) := by
  subst h
  induction k with
  | zero => simp [dpoch]
  | succ k ih =>
    simp only [dpoch]; push_cast
    linear_combination (x + 1 + k) * ih

theorem dpoch_up (x y : ℝ) (h : y = x + 1) (hx : x ≠ 0) (k : ℕ) :
    dpoch y k = dpoch x k * (x + k) / x := by
  rw [eq_div_iff hx]; exact dpoch_shift x y h k

theorem dpoch_dn (y x : ℝ) (h : x = y + 1) (k : ℕ) (hyk : y + k ≠ 0) :
    dpoch y k = dpoch x k * y / (y + k) := by
  rw [eq_div_iff hyk]
  have := dpoch_shift y x h k
  linarith

/-- The summand `T(n,k)` of Dougall's `7F6` sum (before normalising by the right side). -/
noncomputable def dgT (a b c d : ℝ) (n k : ℕ) : ℝ :=
  dpoch d k * dpoch (1 + d / 2) k * dpoch (d + b - a) k * dpoch (d + c - a) k *
    dpoch (1 + a - b - c) k * dpoch (n + a) k * dpoch (-(n : ℝ)) k /
  ((k.factorial : ℝ) * dpoch (d / 2) k * dpoch (1 + a - b) k * dpoch (1 + a - c) k *
    dpoch (b + c + d - a) k * dpoch (1 + d - a - n) k * dpoch (1 + d + n) k)

/-- The right-hand side of Dougall's identity. -/
noncomputable def dgS (a b c d : ℝ) (n : ℕ) : ℝ :=
  dpoch (d + 1) n * dpoch b n * dpoch c n * dpoch (1 + 2 * a - b - c - d) n /
    (dpoch (a - d) n * dpoch (1 + a - b) n * dpoch (1 + a - c) n * dpoch (b + c + d - a) n)

/-- The normalised summand `F(n,k) = T(n,k) / S(n)`, so that `∑_k F(n,k) = 1`. -/
noncomputable def dgF (a b c d : ℝ) (n k : ℕ) : ℝ := dgT a b c d n k / dgS a b c d n

/-- The certificate of Dougall's identity.  The book prints a numerator factor `a-b-c+k` and a
denominator factor `-a+b+c-k` (which cancel up to sign), a denominator factor `-1+2a-b-c-d+n`
and no factor `k` in the numerator; with the summand `dgF` the equation holds for the
certificate below (found by solving for `G/F`; all three differences are visible numerically). -/
noncomputable def dgR (a b c d n k : ℝ) : ℝ :=
  -(k * (a - c + k) * (a - b + k) * (-1 - a + b + c + d + k) * (a - d - k + n) * (1 + a + 2 * n)) /
    ((d + 2 * k) * (a + n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n) * (1 - k + n))

/-- Hypotheses of genericity for Dougall's identity: none of the Pochhammer symbols in a
denominator vanishes. -/
structure DougallHyp (a b c d : ℝ) (n : ℕ) : Prop where
  d2 : NoNegInt (d / 2)
  ab : NoNegInt (1 + a - b)
  ac : NoNegInt (1 + a - c)
  bcd : NoNegInt (b + c + d - a)
  dan : NoNegInt (d - a - n)
  dn : NoNegInt (d + n)
  ad : NoNegInt (a - d)
  d1 : NoNegInt (d + 1)
  b0 : NoNegInt b
  c0 : NoNegInt c
  e : NoNegInt (1 + 2 * a - b - c - d)
  an : (n : ℝ) + a ≠ 0

/-- Ratio `S(n+1)/S(n)`. -/
noncomputable def dgr (a b c d n : ℝ) : ℝ :=
  (d + 1 + n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n) /
    ((a - d + n) * (1 + a - b + n) * (1 + a - c + n) * (b + c + d - a + n))

/-- Ratio `T(n+1,k)/T(n,k)`. -/
noncomputable def dgtau (a d n k : ℝ) : ℝ :=
  ((n + a + k) / (n + a)) * ((-(n + 1)) / (-(n + 1) + k)) *
    ((1 + d - a - (n + 1) + k) / (1 + d - a - (n + 1))) * ((1 + d + n) / (1 + d + n + k))

/-- Ratio `T(n,k+1)/T(n,k)`. -/
noncomputable def dgrho (a b c d n k : ℝ) : ℝ :=
  (d + k) * (1 + d / 2 + k) * (d + b - a + k) * (d + c - a + k) * (1 + a - b - c + k) *
    (n + a + k) * (-n + k) /
  ((k + 1) * (d / 2 + k) * (1 + a - b + k) * (1 + a - c + k) * (b + c + d - a + k) *
    (1 + d - a - n + k) * (1 + d + n + k))

theorem dgS_succ (a b c d : ℝ) (n : ℕ) (h : DougallHyp a b c d n) :
    dgS a b c d (n + 1) = dgr a b c d n * dgS a b c d n := by
  unfold dgS dgr
  simp only [dpoch]
  have a1 := dpoch_ne_zero h.ad n
  have a2 := dpoch_ne_zero h.ab n
  have a3 := dpoch_ne_zero h.ac n
  have a4 := dpoch_ne_zero h.bcd n
  have z1 : a - d + n ≠ 0 := by simpa using h.ad n
  have z2 : 1 + a - b + n ≠ 0 := by simpa using h.ab n
  have z3 : 1 + a - c + n ≠ 0 := by simpa using h.ac n
  have z4 : b + c + d - a + n ≠ 0 := by simpa using h.bcd n
  field_simp



set_option maxHeartbeats 1000000 in
theorem dgT_succ_n (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) (hk : k + 1 ≤ n) :
    dgT a b c d (n + 1) k = dgtau a d n k * dgT a b c d n k := by
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
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

theorem dg_abs_k (p1 p2 p3 p4 p5 p6 p7 x1 x2 x3 x4 x5 x6 x7 fk kk q2 q3 q4 q5 q6 q7 y2 y3 y4 y5 y6 y7 :
    ℝ) (hk : kk ≠ 0) (hf : fk ≠ 0) (h2 : q2 ≠ 0) (h3 : q3 ≠ 0) (h4 : q4 ≠ 0) (h5 : q5 ≠ 0)
    (h6 : q6 ≠ 0) (h7 : q7 ≠ 0) (g2 : y2 ≠ 0) (g3 : y3 ≠ 0) (g4 : y4 ≠ 0) (g5 : y5 ≠ 0)
    (g6 : y6 ≠ 0) (g7 : y7 ≠ 0) :
    ((p1 * x1) * (p2 * x2) * (p3 * x3) * (p4 * x4) * (p5 * x5) * (p6 * x6) * (p7 * x7)) /
        ((kk * fk) * (q2 * y2) * (q3 * y3) * (q4 * y4) * (q5 * y5) * (q6 * y6) * (q7 * y7))
      = (x1 * x2 * x3 * x4 * x5 * x6 * x7) / (kk * y2 * y3 * y4 * y5 * y6 * y7) *
        ((p1 * p2 * p3 * p4 * p5 * p6 * p7) / (fk * q2 * q3 * q4 * q5 * q6 * q7)) := by
  rw [div_mul_div_comm, div_eq_div_iff (by simp [*]) (by simp [*])]
  ring

theorem dgT_succ_k (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) :
    dgT a b c d n (k + 1) = dgrho a b c d n k * dgT a b c d n k := by
  have b1 : NoNegInt (1 + d - a - n) := fun i hh => h.dan (i + 1) (by push_cast; linarith)
  have b2 : NoNegInt (1 + d + n) := fun i hh => h.dn (i + 1) (by push_cast; linarith)
  have c1 := dpoch_ne_zero b1 k
  have c2 := dpoch_ne_zero b2 k
  have c3 := dpoch_ne_zero h.d2 k
  have c4 := dpoch_ne_zero h.ab k
  have c5 := dpoch_ne_zero h.ac k
  have c6 := dpoch_ne_zero h.bcd k
  have c7 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have z1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have z2 : d / 2 + k ≠ 0 := h.d2 k
  have z3 : 1 + a - b + k ≠ 0 := h.ab k
  have z4 : 1 + a - c + k ≠ 0 := h.ac k
  have z5 : b + c + d - a + k ≠ 0 := h.bcd k
  have z6 : 1 + d - a - n + k ≠ 0 := b1 k
  have z7 : 1 + d + n + k ≠ 0 := b2 k
  unfold dgT dgrho
  simp only [dpoch, Nat.factorial_succ]
  push_cast
  exact dg_abs_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z1 c7 c3 c4 c5 c6 c1 c2
    z2 z3 z4 z5 z6 z7

theorem dgF_succ_n (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) (hk : k + 1 ≤ n) :
    dgF a b c d (n + 1) k = (dgtau a d n k / dgr a b c d n) * dgF a b c d n k := by
  unfold dgF
  rw [dgT_succ_n a b c d n k h hk, dgS_succ a b c d n h, mul_div_mul_comm]

theorem dgF_succ_k (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) :
    dgF a b c d n (k + 1) = dgrho a b c d n k * dgF a b c d n k := by
  unfold dgF
  rw [dgT_succ_k a b c d n k h, mul_div_assoc]

theorem dg_abs1 (k1 r2 r3 r4 r5 P q2 Qa Qb Qc Qe q6 D h m1 m2 m3 T g' e f2 f3 f4 f5 s dd : ℝ)
    (hr2 : r2 = f2) (hr3 : r3 = f3) (hr4 : r4 = f4) (hr5 : r5 = -f5) (hq2 : q2 = 2 * h)
    (hq6 : q6 = -g') (hdd : dd = 2 * e)
    (n1 : k1 ≠ 0) (n2 : f2 ≠ 0) (n3 : f3 ≠ 0) (n4 : f4 ≠ 0) (n5 : f5 ≠ 0) (n6 : e ≠ 0)
    (n7 : h ≠ 0) (n8 : g' ≠ 0) (n9 : Qa ≠ 0) (n10 : Qb ≠ 0) (n11 : Qc ≠ 0) (n12 : Qe ≠ 0)
    (n13 : s ≠ 0) :
    (-(k1 * r2 * r3 * r4 * r5 * P) / (q2 * Qa * Qb * Qc * Qe * q6)) *
        (D * h * m1 * m2 * m3 * T * g' / (k1 * e * f3 * f2 * f4 * f5 * s))
      = -(P * D * m1 * m2 * m3 * T) / (dd * Qa * Qb * Qc * Qe * s) := by
  subst hr2 hr3 hr4 hr5 hq2 hq6 hdd
  field_simp

theorem dg_abs2 (u v N1 w' w z' z y' y2 t' t'' s Bb Cc Ee A1 A2 A3 : ℝ)
    (hw : w' = -w) (hz : z' = z) (hy : y' = -y2) (ht : t'' = t')
    (nv : v ≠ 0) (nw : w ≠ 0) (ny : y2 ≠ 0) (ns : s ≠ 0) (nt : t' ≠ 0) (nB : Bb ≠ 0)
    (nC : Cc ≠ 0) (nE : Ee ≠ 0) (n1 : A1 ≠ 0) (n2 : A2 ≠ 0) (n3 : A3 ≠ 0) :
    ((u / v) * ((-N1) / w') * (z' / y') * (t' / s)) / (t'' * Bb * Cc * Ee / (y2 * A1 * A2 * A3))
      = -(u * N1 * z * A1 * A2 * A3) / (v * w * s * Bb * Cc * Ee) := by
  subst hw hz hy ht
  field_simp

theorem dg_abs3 (U V W DX DY DR Q p1 p2 p3 : ℝ) (hDX : DX = Q * p1 * p2) (hDY : DY = Q * p3 * p2)
    (hDR : DR = Q * p3 * p1) (hQ : Q ≠ 0) (h1 : p1 ≠ 0) (h2 : p2 ≠ 0) (h3 : p3 ≠ 0)
    (key : p3 * (U - Q * p1 * p2) = p1 * V - p2 * W) :
    U / DX - 1 = V / DY - W / DR := by
  subst hDX hDY hDR
  field_simp
  linear_combination key

set_option maxHeartbeats 1000000 in
theorem dg_S1 (a b c d n k : ℝ)
    (h12 : b + n ≠ 0) (h13 : c + n ≠ 0) (h16 : d + 2 * (k + 1) ≠ 0)
    (h14 : 1 + 2 * a - b - c - d + n ≠ 0) (h6 : 1 + d + n + k ≠ 0)
    (h18 : 1 - (k + 1) + n ≠ 0) (h19 : k + 1 ≠ 0) (h20 : d / 2 + k ≠ 0)
    (h21 : 1 + a - b + k ≠ 0)
    (h22 : 1 + a - c + k ≠ 0) (h23 : b + c + d - a + k ≠ 0) (h24 : 1 + d - a - n + k ≠ 0)
    (h25 : a + n ≠ 0) :
    dgR a b c d n (k + 1) * dgrho a b c d n k
      = -((1 + a + 2 * n) * (d + k) * (d + b - a + k) * (d + c - a + k) * (1 + a - b - c + k) *
          (n + a + k)) /
        ((d + 2 * k) * (a + n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n) *
          (1 + d + n + k)) := by
  have hg : -n + k ≠ 0 := by intro h; apply h18; linarith
  have he1 : 1 + d / 2 + k ≠ 0 := by intro h; apply h16; linarith
  unfold dgR dgrho
  exact dg_abs1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by ring) (by ring) (by ring)
    (by ring) (by ring) (by ring) (by ring) h19 h22 h21 h23 h24 h20 he1 hg h25 h12 h13 h14 h6

set_option maxHeartbeats 1000000 in
theorem dg_S2 (a b c d n k : ℝ)
    (h1 : n + a ≠ 0) (h3 : 1 + d - a - (n + 1) ≠ 0)
    (h6 : 1 + d + n + k ≠ 0) (h5 : 1 + d + n ≠ 0)
    (h7 : a - d + n ≠ 0) (h8 : 1 + a - b + n ≠ 0) (h9 : 1 + a - c + n ≠ 0)
    (h10 : b + c + d - a + n ≠ 0) (h12 : b + n ≠ 0) (h13 : c + n ≠ 0)
    (h14 : 1 + 2 * a - b - c - d + n ≠ 0) (h17 : n + 1 - k ≠ 0) :
    dgtau a d n k / dgr a b c d n
      = -((n + a + k) * (n + 1) * (d - a - n + k) * (1 + a - b + n) * (1 + a - c + n) *
          (b + c + d - a + n)) /
        ((n + a) * (n + 1 - k) * (1 + d + n + k) * (b + n) * (c + n) *
          (1 + 2 * a - b - c - d + n)) := by
  unfold dgtau dgr
  exact dg_abs2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by ring) (by ring) (by ring) (by ring)
    h1 h17 h7 h6 h5 h12 h13 h14 h8 h9 h10

set_option maxHeartbeats 1000000 in
theorem dg_S3 (a b c d n k : ℝ)
    (h1 : n + a ≠ 0) (h6 : 1 + d + n + k ≠ 0)
    (h12 : b + n ≠ 0) (h13 : c + n ≠ 0)
    (h14 : 1 + 2 * a - b - c - d + n ≠ 0) (h15 : d + 2 * k ≠ 0) (h17 : n + 1 - k ≠ 0) :
    -((n + a + k) * (n + 1) * (d - a - n + k) * (1 + a - b + n) * (1 + a - c + n) *
          (b + c + d - a + n)) /
        ((n + a) * (n + 1 - k) * (1 + d + n + k) * (b + n) * (c + n) *
          (1 + 2 * a - b - c - d + n)) - 1
      = -((1 + a + 2 * n) * (d + k) * (d + b - a + k) * (d + c - a + k) * (1 + a - b - c + k) *
          (n + a + k)) /
        ((d + 2 * k) * (a + n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n) *
          (1 + d + n + k)) - dgR a b c d n k := by
  have hQ : (a + n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by rwa [add_comm]) h12) h13) h14
  unfold dgR
  exact dg_abs3 _ _ _ _ _ _ ((a + n) * (b + n) * (c + n) * (1 + 2 * a - b - c - d + n))
    (n + 1 - k) (1 + d + n + k) (d + 2 * k) (by ring) (by ring) (by ring) hQ h17 h6 h15
    (by ring)

theorem dg_cert_aux (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) (hk : k + 1 ≤ n) :
    dgF a b c d (n + 1) k - dgF a b c d n k
      = dgR a b c d n (k + 1) * dgF a b c d n (k + 1) - dgR a b c d n k * dgF a b c d n k := by
  have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hd2k : d + 2 * (k : ℝ) ≠ 0 := fun hh => h.d2 k (by linarith)
  have s1 := dg_S1 a b c d n k (h.b0 n) (h.c0 n)
    (fun hh => h.d2 (k + 1) (by push_cast; linarith)) (h.e n)
    (fun hh => h.dn (k + 1) (by push_cast; linarith)) (by intro hh; linarith) (by positivity)
    (h.d2 k) (h.ab k) (h.ac k) (h.bcd k)
    (fun hh => h.dan (k + 1) (by push_cast; linarith)) (by have := h.an; rwa [add_comm] at this)
  have s2 := dg_S2 a b c d n k h.an (fun hh => h.dan 0 (by push_cast; linarith))
    (fun hh => h.dn (k + 1) (by push_cast; linarith)) (fun hh => h.dn 1 (by push_cast; linarith))
    (h.ad n) (h.ab n) (h.ac n) (h.bcd n) (h.b0 n) (h.c0 n) (h.e n) (by intro hh; linarith)
  have s3 := dg_S3 a b c d n k h.an (fun hh => h.dn (k + 1) (by push_cast; linarith))
    (h.b0 n) (h.c0 n) (h.e n) hd2k (by intro hh; linarith)
  rw [dgF_succ_n a b c d n k h hk, dgF_succ_k a b c d n k h]
  linear_combination dgF a b c d n k * s2 - dgF a b c d n k * s1 + dgF a b c d n k * s3

/-- CO-454. Dougall's `7F6` sum has a rational WZ certificate: with `F(n,k) = T(n,k)/S(n)` the
normalised summand and `G = R F`, one has `F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)` for `0 ≤ k < n`
(Wilf–Zeilberger equation).  The certificate `R` printed in the book (p. 137) is incorrect as
printed; `dgR` is the corrected rational function (found numerically and verified here). -/
@[kb "petkovsekwilfzeilberger1996" "text (VI), p. 137"]
theorem dougall_wz (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n) (hk : k + 1 ≤ n) :
    dgF a b c d (n + 1) k - dgF a b c d n k
      = dgR a b c d n (k + 1) * dgF a b c d n (k + 1) - dgR a b c d n k * dgF a b c d n k :=
  dg_cert_aux a b c d n k h hk

end UndergradKB.Combinatorics.AeqB
