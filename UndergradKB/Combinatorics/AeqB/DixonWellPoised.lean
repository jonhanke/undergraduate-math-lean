import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Certificates4

/-!
# Dixon's identity, terminating well-poised form (A=B, p. 55)

`3F2(-2n, b, c; 1-b-2n, 1-c-2n; 1)` is summed in closed form by a WZ-style argument:
with `F(n,k) = t(n,k) / S(n)` the rational certificate `dxR` satisfies
`F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)` for `G = R * F` and `k < 2n`; the three boundary terms
`k = 2n, 2n+1, 2n+2` are handled by one explicit rational identity.
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset

/-- Ratio of consecutive summands `t(n,k+1) / t(n,k)` of the well-poised sum (`x = n`, `y = k`). -/
noncomputable def dxr (b c x y : ℝ) : ℝ :=
  (y - 2 * x) * (b + y) * (c + y) / ((y + 1 - b - 2 * x) * (y + 1 - c - 2 * x) * (y + 1))

/-- Ratio `t(n+1,k) / t(n,k)` of the summands (`x = n`, `y = k`). -/
noncomputable def dxT (b c x y : ℝ) : ℝ :=
  (2 * x + 2) * (2 * x + 1) * (y - b - 2 * x - 1) * (y - b - 2 * x) * (y - c - 2 * x - 1)
    * (y - c - 2 * x) /
  ((y - 2 * x - 2) * (y - 2 * x - 1) * (b + 2 * x) * (b + 2 * x + 1) * (c + 2 * x)
    * (c + 2 * x + 1))

/-- Ratio `S(n+1) / S(n)` of the closed forms (`x = n`). -/
noncomputable def dxρ (b c x : ℝ) : ℝ :=
  (2 * x + 1) * (2 * x + 2) * (b + x) * (c + x) * (b + c + 2 * x) * (b + c + 2 * x + 1) /
  ((x + 1) * (b + 2 * x) * (b + 2 * x + 1) * (c + 2 * x) * (c + 2 * x + 1) * (b + c + x))

/-- Quadratic factor of the certificate. -/
noncomputable def dxQ (b c x y : ℝ) : ℝ :=
  ((x + 1) * (y ^ 2 - (6 * x + 2 * (b + c) + 3) * y) +
      (-(b - 1) * (c - 1) * (b + c + x) + (x + 1) * (2 * x + 2) * (4 * x + 2 * (b + c) + 1))) /
    (2 * (b + x) * (c + x) * (b + c + 2 * x) * (b + c + 2 * x + 1))

/-- The WZ certificate `R(n,k)` (`x = n`, `y = k`). -/
noncomputable def dxR (b c x y : ℝ) : ℝ :=
  y * (y - 2 * x - b) * (y - 2 * x - c) * dxQ b c x y / ((y - 2 * x - 1) * (y - 2 * x - 2))

/-- The summand, defined by its term ratio. -/
noncomputable def dxterm (b c : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => dxterm b c n k * dxr b c (n : ℝ) (k : ℝ)

/-- The closed form. -/
noncomputable def dxS (b c : ℝ) (n : ℕ) : ℝ :=
  dpoch 1 (2 * n) * dpoch b n * dpoch c n * dpoch (b + c) (2 * n) /
    (dpoch 1 n * dpoch b (2 * n) * dpoch c (2 * n) * dpoch (b + c) n)

/-- Genericity: `a, a+1, ..., a+N-1` are all nonzero. -/
def dxNZ (a : ℝ) (N : ℕ) : Prop := ∀ j : ℕ, j < N → a + j ≠ 0

theorem dxNZ.mono {a : ℝ} {N M : ℕ} (h : dxNZ a N) (hM : M ≤ N) : dxNZ a M :=
  fun j hj => h j (lt_of_lt_of_le hj hM)

theorem dx_dpoch_ne {a : ℝ} {N : ℕ} (h : dxNZ a N) {m : ℕ} (hm : m ≤ N) : dpoch a m ≠ 0 := by
  induction m with
  | zero => simp [dpoch]
  | succ m ih =>
    simp only [dpoch]
    exact mul_ne_zero (ih (by omega)) (h m (by omega))

theorem dx_dpoch_one_ne (m : ℕ) : dpoch 1 m ≠ 0 :=
  dpoch_ne_zero (fun i => by positivity) m

/-! ### Rational-function identities -/

theorem dx_Rr (b c x y : ℝ)
    (h13 : y - 2 * x - 1 ≠ 0) (h15 : y - 2 * x ≠ 0)
    (h16 : y + 1 - b - 2 * x ≠ 0) (h17 : y + 1 - c - 2 * x ≠ 0) (h18 : y + 1 ≠ 0) :
    dxR b c x (y + 1) * dxr b c x y = (b + y) * (c + y) * dxQ b c x (y + 1) / (y - 2 * x - 1) := by
  have h13' : y + 1 - 2 * x - 1 ≠ 0 := by intro h; apply h15; linarith
  have h14' : y + 1 - 2 * x - 2 ≠ 0 := by intro h; apply h13; linarith
  unfold dxR dxr
  field_simp
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem dx_wz (b c x y : ℝ)
    (h3 : b + 2 * x ≠ 0) (h4 : b + 2 * x + 1 ≠ 0) (h5 : c + 2 * x ≠ 0) (h6 : c + 2 * x + 1 ≠ 0)
    (h7 : x + 1 ≠ 0) (h8 : b + c + x ≠ 0) (h9 : b + x ≠ 0) (h10 : c + x ≠ 0)
    (h11 : b + c + 2 * x ≠ 0) (h12 : b + c + 2 * x + 1 ≠ 0)
    (h13 : y - 2 * x - 1 ≠ 0) (h14 : y - 2 * x - 2 ≠ 0) :
    dxT b c x y = dxρ b c x * (1 + (b + y) * (c + y) * dxQ b c x (y + 1) / (y - 2 * x - 1)
      - dxR b c x y) := by
  unfold dxT dxρ dxR dxQ
  field_simp
  ring

theorem dx_step (b c x y : ℝ)
    (h3 : b + 2 * x ≠ 0) (h4 : b + 2 * x + 1 ≠ 0) (h5 : c + 2 * x ≠ 0) (h6 : c + 2 * x + 1 ≠ 0)
    (h13 : y - 2 * x - 1 ≠ 0) (h14 : y - 2 * x - 2 ≠ 0) (h15 : y - 2 * x ≠ 0)
    (h16 : y + 1 - b - 2 * x ≠ 0) (h17 : y + 1 - c - 2 * x ≠ 0) (h18 : y + 1 ≠ 0)
    (h19 : y + 1 - b - 2 * (x + 1) ≠ 0) (h20 : y + 1 - c - 2 * (x + 1) ≠ 0) :
    dxT b c x y * dxr b c (x + 1) y = dxr b c x y * dxT b c x (y + 1) := by
  have h13' : y + 1 - 2 * x - 1 ≠ 0 := by intro h; apply h15; linarith
  have h14' : y + 1 - 2 * x - 2 ≠ 0 := by intro h; apply h13; linarith
  unfold dxT dxr
  field_simp
  ring

theorem dx_bdry (b c x y : ℝ) (hy : y = 2 * x)
    (h3 : b + 2 * x ≠ 0) (h4 : b + 2 * x + 1 ≠ 0) (h5 : c + 2 * x ≠ 0) (h6 : c + 2 * x + 1 ≠ 0)
    (h7 : x + 1 ≠ 0) (h8 : b + c + x ≠ 0) (h9 : b + x ≠ 0) (h10 : c + x ≠ 0)
    (h11 : b + c + 2 * x ≠ 0) (h12 : b + c + 2 * x + 1 ≠ 0)
    (hb1 : b + 1 ≠ 0) (hb0 : b ≠ 0) (hc1 : c + 1 ≠ 0) (hc0 : c ≠ 0) (hx : 2 * x + 1 ≠ 0)
    (hx' : 2 * x + 2 ≠ 0) :
    dxT b c x y * (1 + dxr b c (x + 1) y + dxr b c (x + 1) y * dxr b c (x + 1) (y + 1))
      = dxρ b c x * (1 - dxR b c x y) := by
  have h13 : y - 2 * x - 1 ≠ 0 := by rw [hy]; norm_num
  have h14 : y - 2 * x - 2 ≠ 0 := by rw [hy]; norm_num
  have e1 : y + 1 - b - 2 * (x + 1) ≠ 0 := by
    rw [hy]; intro h; apply hb1; linarith
  have e2 : y + 1 - c - 2 * (x + 1) ≠ 0 := by
    rw [hy]; intro h; apply hc1; linarith
  have e3 : y + 1 ≠ 0 := by rw [hy]; exact hx
  have e4 : y + 1 + 1 - b - 2 * (x + 1) ≠ 0 := by
    rw [hy]; intro h; apply hb0; linarith
  have e5 : y + 1 + 1 - c - 2 * (x + 1) ≠ 0 := by
    rw [hy]; intro h; apply hc0; linarith
  have e6 : y + 1 + 1 ≠ 0 := by rw [hy]; intro h; apply hx'; linarith
  subst hy
  unfold dxT dxρ dxR dxQ dxr
  field_simp
  ring

/-! ### Summand facts -/

theorem dxterm_eq (b c : ℝ) (n k : ℕ) :
    dxterm b c n k = dpoch (-(2 * (n : ℝ))) k * dpoch b k * dpoch c k /
      (dpoch (1 - b - 2 * n) k * dpoch (1 - c - 2 * n) k * (k.factorial : ℝ)) := by
  induction k with
  | zero => simp [dxterm, dpoch]
  | succ k ih =>
    simp only [dxterm, ih, dpoch, dxr, Nat.factorial_succ]
    push_cast
    rw [div_mul_div_comm]
    congr 1 <;> ring

theorem dxterm_ratio (b c : ℝ) (n : ℕ) (hb : dxNZ b (2 * n + 2)) (hc : dxNZ c (2 * n + 2))
    (_hs : dxNZ (b + c) (2 * n + 2)) :
    ∀ k : ℕ, k ≤ 2 * n → dxterm b c (n + 1) k = dxterm b c n k * dxT b c (n : ℝ) (k : ℝ) := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have b3 : b + 2 * (n : ℝ) ≠ 0 := by
    have := hb (2 * n) (by omega); push_cast at this; exact this
  have b4 : b + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hb (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  have c3 : c + 2 * (n : ℝ) ≠ 0 := by
    have := hc (2 * n) (by omega); push_cast at this; exact this
  have c4 : c + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hc (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  intro k
  induction k with
  | zero =>
    intro _
    have y1 : (2 : ℝ) * n + 2 ≠ 0 := by positivity
    have y2 : (2 : ℝ) * n + 1 ≠ 0 := by positivity
    have y3 : (0 : ℝ) - 2 * n - 2 ≠ 0 := by intro h; linarith
    have y4 : (0 : ℝ) - 2 * n - 1 ≠ 0 := by intro h; linarith
    have : dxT b c (n : ℝ) 0 = 1 := by
      unfold dxT
      field_simp
      ring
    simp [dxterm, this]
  | succ k ih =>
    intro hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have hd' : (2 : ℝ) * n = k + 1 + d := by exact_mod_cast hd
    have ih' := ih (by omega)
    have kk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have dd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h13 : (k : ℝ) - 2 * n - 1 ≠ 0 := by intro h; linarith
    have h14 : (k : ℝ) - 2 * n - 2 ≠ 0 := by intro h; linarith
    have h15 : (k : ℝ) - 2 * n ≠ 0 := by intro h; linarith
    have h16 : (k : ℝ) + 1 - b - 2 * n ≠ 0 := fun h => hb d (by omega) (by linarith)
    have h17 : (k : ℝ) + 1 - c - 2 * n ≠ 0 := fun h => hc d (by omega) (by linarith)
    have h18 : (k : ℝ) + 1 ≠ 0 := by intro h; linarith
    have h19 : (k : ℝ) + 1 - b - 2 * (n + 1) ≠ 0 := fun h => hb (d + 2) (by omega) (by push_cast; linarith)
    have h20 : (k : ℝ) + 1 - c - 2 * (n + 1) ≠ 0 := fun h => hc (d + 2) (by omega) (by push_cast; linarith)
    have step := dx_step b c (n : ℝ) (k : ℝ) b3 b4 c3 c4 h13 h14 h15 h16 h17 h18 h19 h20
    have e1 : dxterm b c (n + 1) (k + 1) = dxterm b c (n + 1) k * dxr b c ((n : ℝ) + 1) (k : ℝ) := by
      simp only [dxterm]; push_cast; rfl
    have e2 : dxterm b c n (k + 1) = dxterm b c n k * dxr b c (n : ℝ) (k : ℝ) := rfl
    rw [e1, ih', e2]
    push_cast
    calc dxterm b c n k * dxT b c (n : ℝ) (k : ℝ) * dxr b c ((n : ℝ) + 1) (k : ℝ)
        = dxterm b c n k * (dxT b c (n : ℝ) (k : ℝ) * dxr b c ((n : ℝ) + 1) (k : ℝ)) := by ring
      _ = dxterm b c n k * (dxr b c (n : ℝ) (k : ℝ) * dxT b c (n : ℝ) ((k : ℝ) + 1)) := by
          rw [step]
      _ = _ := by ring

theorem dxS_succ (b c : ℝ) (n : ℕ) (hb : dxNZ b (2 * n + 2)) (hc : dxNZ c (2 * n + 2))
    (hs : dxNZ (b + c) (2 * n + 2)) : dxS b c (n + 1) = dxρ b c (n : ℝ) * dxS b c n := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have b3 : b + 2 * (n : ℝ) ≠ 0 := by
    have := hb (2 * n) (by omega); push_cast at this; exact this
  have b4 : b + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hb (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  have c3 : c + 2 * (n : ℝ) ≠ 0 := by
    have := hc (2 * n) (by omega); push_cast at this; exact this
  have c4 : c + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hc (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  have s1 : b + c + (n : ℝ) ≠ 0 := by
    have := hs n (by omega); exact this
  have s3 : b + c + 2 * (n : ℝ) ≠ 0 := by
    have := hs (2 * n) (by omega); push_cast at this; exact this
  have s4 : b + c + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hs (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  have p1 := dx_dpoch_one_ne n
  have p2 := dx_dpoch_one_ne (2 * n)
  have p3 : dpoch b n ≠ 0 := dx_dpoch_ne hb (by omega)
  have p4 : dpoch c n ≠ 0 := dx_dpoch_ne hc (by omega)
  have p5 : dpoch b (2 * n) ≠ 0 := dx_dpoch_ne hb (by omega)
  have p6 : dpoch c (2 * n) ≠ 0 := dx_dpoch_ne hc (by omega)
  have p7 : dpoch (b + c) (2 * n) ≠ 0 := dx_dpoch_ne hs (by omega)
  have p8 : dpoch (b + c) n ≠ 0 := dx_dpoch_ne hs (by omega)
  have n1 : (1 : ℝ) + n ≠ 0 := by positivity
  have n2 : (1 : ℝ) + 2 * n ≠ 0 := by positivity
  have n3 : (1 : ℝ) + (2 * n + 1) ≠ 0 := by positivity
  have n4 : (n : ℝ) + 1 ≠ 0 := by positivity
  have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
  unfold dxS dxρ
  rw [e]
  simp only [dpoch]
  push_cast
  have hb' : b + n ≠ 0 := by
    intro h; have := hb n (by omega); exact this h
  have hc' : c + n ≠ 0 := by
    intro h; have := hc n (by omega); exact this h
  have n5 : (2 : ℝ) * n + 1 ≠ 0 := by positivity
  have n6 : (2 : ℝ) * n + 2 ≠ 0 := by positivity
  have b4' : b + (2 * (n : ℝ) + 1) ≠ 0 := by rw [← add_assoc]; exact b4
  have c4' : c + (2 * (n : ℝ) + 1) ≠ 0 := by rw [← add_assoc]; exact c4
  have s4' : b + c + (2 * (n : ℝ) + 1) ≠ 0 := by rw [← add_assoc]; exact s4
  field_simp
  ring

/-! ### The sum recursion -/

theorem dx_sum_succ (b c : ℝ) (n : ℕ) (hb : dxNZ b (2 * n + 2)) (hc : dxNZ c (2 * n + 2))
    (hs : dxNZ (b + c) (2 * n + 2)) :
    ∑ k ∈ range (2 * (n + 1) + 1), dxterm b c (n + 1) k
      = dxρ b c (n : ℝ) * ∑ k ∈ range (2 * n + 1), dxterm b c n k := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have b3 : b + 2 * (n : ℝ) ≠ 0 := by
    have := hb (2 * n) (by omega); push_cast at this; exact this
  have b4 : b + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hb (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  have c3 : c + 2 * (n : ℝ) ≠ 0 := by
    have := hc (2 * n) (by omega); push_cast at this; exact this
  have c4 : c + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hc (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  have s1 : b + c + (n : ℝ) ≠ 0 := hs n (by omega)
  have s3 : b + c + 2 * (n : ℝ) ≠ 0 := by
    have := hs (2 * n) (by omega); push_cast at this; exact this
  have s4 : b + c + 2 * (n : ℝ) + 1 ≠ 0 := by
    have := hs (2 * n + 1) (by omega); push_cast at this; rw [← add_assoc] at this; exact this
  have b9 : b + (n : ℝ) ≠ 0 := hb n (by omega)
  have c9 : c + (n : ℝ) ≠ 0 := hc n (by omega)
  have x1 : (n : ℝ) + 1 ≠ 0 := by positivity
  set ρ := dxρ b c (n : ℝ) with hρ
  set g : ℕ → ℝ := fun k => dxR b c (n : ℝ) (k : ℝ) * dxterm b c n k with hg
  have hpt : ∀ k ∈ range (2 * n),
      dxterm b c (n + 1) k = ρ * dxterm b c n k + ρ * (g (k + 1) - g k) := by
    intro k hk
    have hk := mem_range.1 hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ 2 * n by omega)
    have hd' : (2 : ℝ) * n = k + 1 + d := by exact_mod_cast hd
    have kk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have dd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h13 : (k : ℝ) - 2 * n - 1 ≠ 0 := by intro h; linarith
    have h14 : (k : ℝ) - 2 * n - 2 ≠ 0 := by intro h; linarith
    have h15 : (k : ℝ) - 2 * n ≠ 0 := by intro h; linarith
    have h16 : (k : ℝ) + 1 - b - 2 * n ≠ 0 := fun h => hb d (by omega) (by linarith)
    have h17 : (k : ℝ) + 1 - c - 2 * n ≠ 0 := fun h => hc d (by omega) (by linarith)
    have h18 : (k : ℝ) + 1 ≠ 0 := by intro h; linarith
    have wz := dx_wz b c (n : ℝ) (k : ℝ) b3 b4 c3 c4 x1 s1 b9 c9 s3 s4 h13 h14
    have Rr := dx_Rr b c (n : ℝ) (k : ℝ) h13 h15 h16 h17 h18
    rw [dxterm_ratio b c n hb hc hs k (by omega)]
    have e2 : dxterm b c n (k + 1) = dxterm b c n k * dxr b c (n : ℝ) (k : ℝ) := rfl
    simp only [hg, e2]
    push_cast
    have : dxR b c (n : ℝ) ((k : ℝ) + 1) * (dxterm b c n k * dxr b c (n : ℝ) (k : ℝ))
        = dxterm b c n k * (dxR b c (n : ℝ) ((k : ℝ) + 1) * dxr b c (n : ℝ) (k : ℝ)) := by ring
    rw [this, Rr, wz]
    ring
  have hg0 : g 0 = 0 := by simp [hg, dxR]
  have h1 : ∑ k ∈ range (2 * n), dxterm b c (n + 1) k
      = ρ * ∑ k ∈ range (2 * n), dxterm b c n k + ρ * g (2 * n) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_range_sub g (2 * n), hg0]
    ring
  have hB : dxterm b c (n + 1) (2 * n) + dxterm b c (n + 1) (2 * n + 1)
      + dxterm b c (n + 1) (2 * n + 1 + 1) = ρ * (dxterm b c n (2 * n) - g (2 * n)) := by
    have r0 := dxterm_ratio b c n hb hc hs (2 * n) le_rfl
    have r1 : dxterm b c (n + 1) (2 * n + 1)
        = dxterm b c (n + 1) (2 * n) * dxr b c ((n : ℝ) + 1) (2 * (n : ℝ)) := by
      simp only [dxterm]; push_cast; rfl
    have r2 : dxterm b c (n + 1) (2 * n + 1 + 1)
        = dxterm b c (n + 1) (2 * n + 1) * dxr b c ((n : ℝ) + 1) (2 * (n : ℝ) + 1) := by
      simp only [dxterm]; push_cast; rfl
    have bd := dx_bdry b c (n : ℝ) (2 * (n : ℝ)) rfl b3 b4 c3 c4 x1 s1 b9 c9 s3 s4
      (by have := hb 1 (by omega); push_cast at this; exact this)
      (by have := hb 0 (by omega); simpa using this)
      (by have := hc 1 (by omega); push_cast at this; exact this)
      (by have := hc 0 (by omega); simpa using this)
      (by positivity) (by positivity)
    have gg : g (2 * n) = dxR b c (n : ℝ) (2 * (n : ℝ)) * dxterm b c n (2 * n) := by
      simp only [hg]; push_cast; rfl
    rw [r2, r1, r0, gg]
    push_cast at r0 ⊢
    have : dxterm b c n (2 * n) * dxT b c (n : ℝ) (2 * (n : ℝ)) *
          (1 + dxr b c ((n : ℝ) + 1) (2 * (n : ℝ)) +
            dxr b c ((n : ℝ) + 1) (2 * (n : ℝ)) * dxr b c ((n : ℝ) + 1) (2 * (n : ℝ) + 1))
        = dxterm b c n (2 * n) * (dxT b c (n : ℝ) (2 * (n : ℝ)) *
          (1 + dxr b c ((n : ℝ) + 1) (2 * (n : ℝ)) +
            dxr b c ((n : ℝ) + 1) (2 * (n : ℝ)) * dxr b c ((n : ℝ) + 1) (2 * (n : ℝ) + 1))) := by
      ring
    rw [bd] at this
    nlinarith [this]
  have e : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
  have hR : ∑ k ∈ range (2 * n + 1), dxterm b c n k
      = ∑ k ∈ range (2 * n), dxterm b c n k + dxterm b c n (2 * n) := Finset.sum_range_succ _ _
  rw [e, Finset.sum_range_succ _ (2 * n + 1 + 1), Finset.sum_range_succ _ (2 * n + 1),
    Finset.sum_range_succ _ (2 * n), hR]
  linarith [h1, hB]

theorem dx_sum_eq (b c : ℝ) : ∀ n : ℕ, dxNZ b (2 * n) → dxNZ c (2 * n) → dxNZ (b + c) (2 * n) →
    ∑ k ∈ range (2 * n + 1), dxterm b c n k = dxS b c n := by
  intro n
  induction n with
  | zero => intro _ _ _; simp [dxterm, dxS, dpoch]
  | succ n ih =>
    intro hb hc hs
    have hb' : dxNZ b (2 * n + 2) := hb.mono (by omega)
    have hc' : dxNZ c (2 * n + 2) := hc.mono (by omega)
    have hs' : dxNZ (b + c) (2 * n + 2) := hs.mono (by omega)
    rw [dx_sum_succ b c n hb' hc' hs', ih (hb.mono (by omega)) (hc.mono (by omega))
      (hs.mono (by omega)), dxS_succ b c n hb' hc' hs']

/-- CO-369. Dixon's identity in its terminating well-poised form (the sum of
`3F2(-2n, b, c; 1-b-2n, 1-c-2n; 1)` in closed form). Genericity hypotheses (Lean-side): `b`, `c`
and `b + c` have no vanishing shifted factors `b + j` (`j < 2n`), which contains the nonvanishing of
all denominator Pochhammer symbols `(b)_{2n}`, `(c)_{2n}`, `(1-b-2n)_k`, `(1-c-2n)_k`; the extra
requirement `(b+c)_{2n} ≠ 0` (instead of only `(b+c)_n ≠ 0`) is needed for the proof by induction on
`n`, which divides by `b + c + 2m`, `b + c + 2m + 1`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 55"]
theorem dixon_well_poised (b c : ℝ) (n : ℕ)
    (hb : ∀ j : ℕ, j < 2 * n → b + j ≠ 0) (hc : ∀ j : ℕ, j < 2 * n → c + j ≠ 0)
    (hs : ∀ j : ℕ, j < 2 * n → b + c + j ≠ 0) :
    ∑ k ∈ range (2 * n + 1),
        dpoch (-(2 * (n : ℝ))) k * dpoch b k * dpoch c k /
          (dpoch (1 - b - 2 * n) k * dpoch (1 - c - 2 * n) k * (k.factorial : ℝ)) =
      dpoch 1 (2 * n) * dpoch b n * dpoch c n * dpoch (b + c) (2 * n) /
        (dpoch 1 n * dpoch b (2 * n) * dpoch c (2 * n) * dpoch (b + c) n) := by
  have := dx_sum_eq b c n hb hc hs
  simp only [dxS] at this
  rw [← this]
  exact Finset.sum_congr rfl (fun k _ => (dxterm_eq b c n k).symm)

end UndergradKB.Combinatorics.AeqB
