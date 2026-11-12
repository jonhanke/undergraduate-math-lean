import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Certificates4

/-!
# Gessel's terminating identities from the WZ method (A = B, §7.4, p. 137)

CO-468.  Three terminating hypergeometric identities found by Gessel by variations of the WZ
method.  The certificates printed in the book were checked numerically; for identities (1) and
(3) the printed `R(n,k)` is correct.  In each case the WZ mate is `G(n,k) = R(n,k) F(n,k)`; since
`R` has poles where `F(n,·)` vanishes, we write `G(n,k) = g(n,k) F(n+1,k)` with a pole-free `g`
(`g = R * F(n,k)/F(n+1,k)`), so that the WZ equation holds for every `k`.
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset

/-! ### Generic lemmas -/

theorem gs_dpoch_zero (x : ℝ) (m : ℕ) (hx : x + m = 0) (k : ℕ) (hk : m + 1 ≤ k) :
    dpoch x k = 0 := by
  induction k, hk using Nat.le_induction with
  | base => simp only [dpoch]; rw [hx]; simp
  | succ k hk ih => simp only [dpoch]; rw [ih]; simp

theorem gs_noNegInt_pos {x : ℝ} (hx : 0 < x) : NoNegInt x := fun i => by
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  intro h; linarith

/-- Telescoping/induction scheme: a WZ pair with support `k ≤ L n`. -/
theorem gs_wz_sum (F G : ℕ → ℕ → ℝ) (L : ℕ → ℕ) (hL : ∀ n, L n ≤ L (n + 1))
    (hz : ∀ n k, L n < k → F n k = 0)
    (hwz : ∀ n k, k ≤ L (n + 1) → F (n + 1) k - F n k = G n (k + 1) - G n k)
    (hG0 : ∀ n, G n 0 = 0) (hGL : ∀ n, G n (L (n + 1) + 1) = 0)
    (h0 : ∑ k ∈ range (L 0 + 1), F 0 k = 1) :
    ∀ n, ∑ k ∈ range (L n + 1), F n k = 1 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have h1 : ∑ k ∈ range (L (n + 1) + 1), (F (n + 1) k - F n k) = 0 := by
      have := Finset.sum_range_sub (fun k => G n k) (L (n + 1) + 1)
      rw [hGL, hG0, sub_zero] at this
      rw [← this]
      exact Finset.sum_congr rfl (fun k hk => hwz n k (Finset.mem_range_succ_iff.1 hk))
    rw [Finset.sum_sub_distrib, sub_eq_zero] at h1
    rw [h1, ← ih]
    exact (Finset.sum_subset (Finset.range_subset_range.2 (by have := hL n; omega))
      (fun k _ hk => hz n k (by simp at hk; omega))).symm

/-- Core of the WZ equation for the normalised summand. -/
theorem gs_wz_core (t0 t1 tk1 S0 S1 r u ρ g0 g1 : ℝ) (hS : S1 = r * S0) (hS0 : S0 ≠ 0)
    (hr : r ≠ 0) (he : t0 = u * t1) (h1 : tk1 = ρ * t1)
    (key : 1 - r * u = g1 * ρ - g0) :
    t1 / S1 - t0 / S0 = g1 * (tk1 / S1) - g0 * (t1 / S1) := by
  subst hS he h1
  have : t1 / (r * S0) - u * t1 / S0 - (g1 * (ρ * t1 / (r * S0)) - g0 * (t1 / (r * S0))) =
      t1 / (r * S0) * (1 - r * u - (g1 * ρ - g0)) := by
    field_simp
  rw [key] at this
  simpa [sub_eq_zero] using this

theorem gs_div_one {α : Type*} (s : Finset α) (T : α → ℝ) (S : ℝ) (hS : S ≠ 0)
    (h : ∑ a ∈ s, T a / S = 1) : ∑ a ∈ s, T a = S := by
  rw [← Finset.sum_div, div_eq_one_iff_eq hS] at h
  exact h

/-! ### Identity (1) -/

/-- Summand (unnormalised) of Gessel's first identity, with `x` standing for `n`. -/
noncomputable def gsT1 (c x : ℝ) (k : ℕ) : ℝ :=
  dpoch (-(3 * x)) k * dpoch (2 / 3 - c) k * dpoch (3 * x + 2) k * (3 / 4) ^ k /
    ((k.factorial : ℝ) * dpoch (3 / 2) k * dpoch (1 - 3 * c) k)

/-- Right side of Gessel's first identity. -/
noncomputable def gsS1 (c : ℝ) (n : ℕ) : ℝ :=
  dpoch (c + 2 / 3) n * dpoch (1 / 3) n / (dpoch (1 - c) n * dpoch (4 / 3) n)

noncomputable def gsF1 (c : ℝ) (n k : ℕ) : ℝ := gsT1 c n k / gsS1 c n

noncomputable def gsr1 (c x : ℝ) : ℝ :=
  (c + 2 / 3 + x) * (1 / 3 + x) / ((1 - c + x) * (4 / 3 + x))

noncomputable def gsu1 (x k : ℝ) : ℝ :=
  -((k - 3 * x - 3) * (k - 3 * x - 2) * (k - 3 * x - 1) * (3 * x + 4)) /
    ((3 * x + 1) * ((3 * x + 2 + k) * (3 * x + 3 + k) * (3 * x + 4 + k)))

noncomputable def gsg1 (c x k : ℝ) : ℝ :=
  -(2 * (5 + 6 * x) * (k - 3 * c) * k * (2 * k + 1)) /
    (3 * (1 - c + x) * ((3 * x + 2 + k) * (3 * x + 3 + k) * (3 * x + 4 + k)))

noncomputable def gsrho1 (c x k : ℝ) : ℝ :=
  (-(3 * x) + k) * (2 / 3 - c + k) * (3 * x + 2 + k) * (3 / 4) /
    ((k + 1) * (3 / 2 + k) * (1 - 3 * c + k))

theorem gsT1_succ_k (c x : ℝ) (k : ℕ) (hc : NoNegInt (1 - 3 * c)) :
    gsT1 c x (k + 1) = gsrho1 c x k * gsT1 c x k := by
  have h1 : (1 - 3 * c + k) ≠ 0 := by simpa using hc k
  have h2 : (3 / 2 + (k : ℝ)) ≠ 0 := by positivity
  have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
  have d1 := dpoch_ne_zero hc k
  have d2 := dpoch_ne_zero (gs_noNegInt_pos (x := 3 / 2) (by norm_num)) k
  have d3 : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold gsT1 gsrho1
  simp only [dpoch, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

theorem gsT1_shift (c x : ℝ) (k : ℕ) (hx : 0 ≤ x) (hc : NoNegInt (1 - 3 * c)) :
    gsT1 c x k = gsu1 x k * gsT1 c (x + 1) k := by
  have p0 : (-(3 * (x + 1))) ≠ 0 := by intro h; linarith
  have p1 : (-(3 * (x + 1)) + 1) ≠ 0 := by intro h; linarith
  have p2 : (-(3 * (x + 1)) + 1 + 1) ≠ 0 := by intro h; linarith
  have B1 : dpoch (-(3 * x)) k = dpoch (-(3 * (x + 1))) k *
      ((-(3 * (x + 1)) + k) * (-(3 * (x + 1)) + 1 + k) * (-(3 * (x + 1)) + 1 + 1 + k)) /
      ((-(3 * (x + 1))) * (-(3 * (x + 1)) + 1) * (-(3 * (x + 1)) + 1 + 1)) := by
    have a1 := dpoch_up (-(3 * (x + 1))) (-(3 * (x + 1)) + 1) rfl p0 k
    have a2 := dpoch_up (-(3 * (x + 1)) + 1) (-(3 * (x + 1)) + 1 + 1) rfl p1 k
    have a3 := dpoch_up (-(3 * (x + 1)) + 1 + 1) (-(3 * x)) (by ring) p2 k
    rw [a3, a2, a1]
    field_simp
  have q0 : (3 * x + 2 + (k : ℝ)) ≠ 0 := by positivity
  have q1 : (3 * x + 3 + (k : ℝ)) ≠ 0 := by positivity
  have q2 : (3 * x + 4 + (k : ℝ)) ≠ 0 := by positivity
  have B2 : dpoch (3 * x + 2) k = dpoch (3 * (x + 1) + 2) k *
      ((3 * x + 2) * (3 * x + 3) * (3 * x + 4)) /
      ((3 * x + 2 + k) * (3 * x + 3 + k) * (3 * x + 4 + k)) := by
    have a1 := dpoch_dn (3 * x + 2) (3 * x + 3) (by ring) k q0
    have a2 := dpoch_dn (3 * x + 3) (3 * x + 4) (by ring) k q1
    have a3 := dpoch_dn (3 * x + 4) (3 * (x + 1) + 2) (by ring) k q2
    rw [a1, a2, a3]
    field_simp
  have d1 := dpoch_ne_zero hc k
  have d2 := dpoch_ne_zero (gs_noNegInt_pos (x := 3 / 2) (by norm_num)) k
  have d3 : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold gsT1 gsu1
  rw [B1, B2]
  have e1 : (3 * x + 2) ≠ 0 := by positivity
  have e2 : (3 * x + 3) ≠ 0 := by positivity
  have e3 : (3 * x + 4) ≠ 0 := by positivity
  have e4 : (3 * x + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem gsS1_succ (c : ℝ) (n : ℕ) (h1 : NoNegInt (1 - c)) :
    gsS1 c (n + 1) = gsr1 c n * gsS1 c n := by
  have a1 := dpoch_ne_zero h1 n
  have a2 := dpoch_ne_zero (gs_noNegInt_pos (x := 4 / 3) (by norm_num)) n
  have z1 : 1 - c + n ≠ 0 := by simpa using h1 n
  have z2 : (4 / 3 + (n : ℝ)) ≠ 0 := by positivity
  unfold gsS1 gsr1
  simp only [dpoch]
  field_simp

set_option maxRecDepth 20000 in
theorem gs_key1(c x k : ℝ) (hx : 0 ≤ x) (hk : 0 ≤ k) (h1 : 1 - 3 * c + k ≠ 0)
    (h1' : 1 - 3 * c + (k + 1) ≠ 0) (h2 : 3 * c + 3 * x + 2 ≠ 0) (h3 : 1 - c + x ≠ 0) :
    1 - gsr1 c x * gsu1 x k = gsg1 c x (k + 1) * gsrho1 c (x + 1) k - gsg1 c x k := by
  have e0 : (3 * x + 2 + k) ≠ 0 := by intro h; linarith
  have e1 : (3 * x + 3 + k) ≠ 0 := by intro h; linarith
  have e2 : (3 * x + 4 + k) ≠ 0 := by intro h; linarith
  have e3 : (3 * x + 5 + k) ≠ 0 := by intro h; linarith
  have e4 : (3 * x + 6 + k) ≠ 0 := by intro h; linarith
  have g1 : (3 * x + 1) ≠ 0 := by intro h; linarith
  have h1b : 1 - c * 3 + k ≠ 0 := by intro h; apply h1; linarith
  have h2b : 2 + c * 3 + x * 3 ≠ 0 := by intro h; apply h2; linarith
  have f1 : (k + 1) ≠ 0 := by intro h; linarith
  have f2 : (3 / 2 + k) ≠ 0 := by intro h; linarith
  have f3 : (4 / 3 + x) ≠ 0 := by intro h; linarith
  have f4 : (3 * x + 2 + (k + 1)) ≠ 0 := by intro h; linarith
  have f5 : (3 * x + 3 + (k + 1)) ≠ 0 := by intro h; linarith
  have f6 : (3 * x + 4 + (k + 1)) ≠ 0 := by intro h; linarith
  unfold gsr1 gsu1 gsg1 gsrho1
  field_simp
  ring

/-- Wz equation for the first identity, for every `k`. -/
theorem gsF1_wz (c : ℝ) (h1 : NoNegInt (1 - 3 * c)) (h2 : NoNegInt (c + 2 / 3))
    (h3 : NoNegInt (1 - c)) (n k : ℕ) :
    gsF1 c (n + 1) k - gsF1 c n k =
      gsg1 c n ((k + 1 : ℕ) : ℝ) * gsF1 c (n + 1) (k + 1) - gsg1 c n k * gsF1 c (n + 1) k := by
  have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS0 : gsS1 c n ≠ 0 := by
    unfold gsS1
    exact div_ne_zero (mul_ne_zero (dpoch_ne_zero h2 n)
      (dpoch_ne_zero (gs_noNegInt_pos (x := 1 / 3) (by norm_num)) n))
      (mul_ne_zero (dpoch_ne_zero h3 n)
        (dpoch_ne_zero (gs_noNegInt_pos (x := 4 / 3) (by norm_num)) n))
  have z2 : c + 2 / 3 + (n : ℝ) ≠ 0 := by simpa using h2 n
  have z3 : 1 - c + (n : ℝ) ≠ 0 := by simpa using h3 n
  have hr : gsr1 c n ≠ 0 := by
    unfold gsr1
    have : (1 / 3 + (n : ℝ)) ≠ 0 := by positivity
    have : (4 / 3 + (n : ℝ)) ≠ 0 := by positivity
    positivity
  have hk1 : 1 - 3 * c + (k : ℝ) ≠ 0 := by simpa using h1 k
  have hk2 : 1 - 3 * c + ((k : ℝ) + 1) ≠ 0 := by simpa [add_assoc] using h1 (k + 1)
  have z4 : 3 * c + 3 * (n : ℝ) + 2 ≠ 0 := by
    have := z2
    intro h; apply this; linarith
  unfold gsF1
  rw [hc]
  apply gs_wz_core (gsT1 c n k) (gsT1 c (n + 1) k) (gsT1 c (n + 1) (k + 1)) (gsS1 c n)
    (gsS1 c (n + 1)) (gsr1 c n) (gsu1 n k) (gsrho1 c (n + 1) k) (gsg1 c n k)
    (gsg1 c n ((k + 1 : ℕ) : ℝ))
  · rw [gsS1_succ c n h3]
  · exact hS0
  · exact hr
  · exact gsT1_shift c n k hx h1
  · exact gsT1_succ_k c _ k h1
  · push_cast
    exact gs_key1 c n k hx (Nat.cast_nonneg k) hk1 hk2 z4 z3

/-- Normalised summand of the first identity sums to one. -/
theorem gsF1_sum (c : ℝ) (h1 : NoNegInt (1 - 3 * c)) (h2 : NoNegInt (c + 2 / 3))
    (h3 : NoNegInt (1 - c)) (n : ℕ) : ∑ k ∈ range (3 * n + 1), gsF1 c n k = 1 := by
  refine gs_wz_sum (gsF1 c) (fun n k => gsg1 c n k * gsF1 c (n + 1) k) (fun n => 3 * n)
    (fun n => by omega) ?_ ?_ ?_ ?_ ?_ n
  · intro n k hk
    unfold gsF1 gsT1
    rw [gs_dpoch_zero (-(3 * (n : ℝ))) (3 * n) (by push_cast; ring) k hk]
    simp
  · intro n k _
    have := gsF1_wz c h1 h2 h3 n k
    simpa using this
  · intro n
    simp [gsg1]
  · intro n
    have : gsF1 c (n + 1) (3 * (n + 1) + 1) = 0 := by
      unfold gsF1 gsT1
      rw [gs_dpoch_zero (-(3 * ((n + 1 : ℕ) : ℝ))) (3 * (n + 1)) (by push_cast; ring)
        (3 * (n + 1) + 1) (by omega)]
      simp
    simp [this]
  · simp [gsF1, gsT1, gsS1, dpoch]

/-- CO-468 (1).  Gessel's terminating `3F2` identity at argument `3/4`: for `n` a natural number
and `c` real,
`∑_{k=0}^{3n} (-3n)_k (2/3-c)_k (3n+2)_k (3/4)^k / (k! (3/2)_k (1-3c)_k)
  = (c+2/3)_n (1/3)_n / ((1-c)_n (4/3)_n)`.
The WZ certificate printed in the book, `R(n,k) = 2(5+6n)(k-3c)k(2k+1) /
((3c+3n+2)(k-3n-3)(k-3n-2)(k-3n-1))`, is correct.  Lean adds the genericity hypotheses that
`1-3c`, `c+2/3` and `1-c` are not nonpositive integers (denominators of the sum and of the
right side do not vanish). -/
@[kb "petkovsekwilfzeilberger1996" "text §7.4, p. 137"]
theorem gessel_one (c : ℝ) (h1 : NoNegInt (1 - 3 * c)) (h2 : NoNegInt (c + 2 / 3))
    (h3 : NoNegInt (1 - c)) (n : ℕ) :
    ∑ k ∈ range (3 * n + 1),
        dpoch (-(3 * (n : ℝ))) k * dpoch (2 / 3 - c) k * dpoch (3 * (n : ℝ) + 2) k * (3 / 4) ^ k /
          ((k.factorial : ℝ) * dpoch (3 / 2) k * dpoch (1 - 3 * c) k) =
      dpoch (c + 2 / 3) n * dpoch (1 / 3) n / (dpoch (1 - c) n * dpoch (4 / 3) n) := by
  have hS0 : gsS1 c n ≠ 0 := by
    unfold gsS1
    exact div_ne_zero (mul_ne_zero (dpoch_ne_zero h2 n)
      (dpoch_ne_zero (gs_noNegInt_pos (x := 1 / 3) (by norm_num)) n))
      (mul_ne_zero (dpoch_ne_zero h3 n)
        (dpoch_ne_zero (gs_noNegInt_pos (x := 4 / 3) (by norm_num)) n))
  exact gs_div_one _ (fun k => gsT1 c n k) _ hS0 (gsF1_sum c h1 h2 h3 n)

/-! ### Identity (3) -/

/-- Summand of Gessel's `4F3` identity at argument `2/27`, with the pair of parameters
`3/2 + n/5` over `n/5 + 1/2` already reduced to the linear factor `(10k+2n+5)/(2n+5)`;
`x` stands for `n`. -/
noncomputable def gsT3 (x : ℝ) (k : ℕ) : ℝ :=
  (10 * k + 2 * x + 5) / (2 * x + 5) * dpoch (2 / 3) k * dpoch (-x) k * dpoch (2 * x + 2) k *
    (2 / 27) ^ k / ((k.factorial : ℝ) * dpoch (x + 11 / 6) k * dpoch (4 / 3) k)

noncomputable def gsS3 (n : ℕ) : ℝ :=
  dpoch (5 / 2) n * dpoch (11 / 6) n / (dpoch (3 / 2) n * dpoch (7 / 2) n)

noncomputable def gsF3 (n k : ℕ) : ℝ := gsT3 n k / gsS3 n

noncomputable def gsr3 (x : ℝ) : ℝ := (5 / 2 + x) * (11 / 6 + x) / ((3 / 2 + x) * (7 / 2 + x))

noncomputable def gsu3 (x k : ℝ) : ℝ :=
  (10 * k + 2 * x + 5) * (2 * x + 7) / ((2 * x + 5) * (10 * k + 2 * x + 7)) *
    ((k - x - 1) / (-x - 1)) *
    ((2 * x + 2) * (2 * x + 3) / ((2 * x + 2 + k) * (2 * x + 3 + k))) *
    ((x + 11 / 6 + k) / (x + 11 / 6))

noncomputable def gsg3 (x k : ℝ) : ℝ :=
  -(18 * k * (3 * k + 1) * (x + 11 / 6 + k)) /
    ((10 * k + 2 * x + 7) * (2 * x + 2 + k) * (2 * x + 3 + k))

noncomputable def gsrho3 (x k : ℝ) : ℝ :=
  (10 * (k + 1) + 2 * x + 5) / (10 * k + 2 * x + 5) *
    ((2 / 3 + k) * (-x + k) * (2 * x + 2 + k) * (2 / 27) /
      ((k + 1) * (x + 11 / 6 + k) * (4 / 3 + k)))

theorem gsT3_succ_k (x : ℝ) (k : ℕ) (hx : 0 ≤ x) :
    gsT3 x (k + 1) = gsrho3 x k * gsT3 x k := by
  have h1 : (10 * (k : ℝ) + 2 * x + 5) ≠ 0 := by positivity
  have h2 : (x + 11 / 6 + (k : ℝ)) ≠ 0 := by positivity
  have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h4 : (4 / 3 + (k : ℝ)) ≠ 0 := by positivity
  have h5 : (2 * x + 5) ≠ 0 := by positivity
  have d1 := dpoch_ne_zero (gs_noNegInt_pos (x := 4 / 3) (by norm_num)) k
  have d2 := dpoch_ne_zero (gs_noNegInt_pos (x := x + 11 / 6) (by positivity)) k
  have d3 : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold gsT3 gsrho3
  simp only [dpoch, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

theorem gsT3_shift (x : ℝ) (k : ℕ) (hx : 0 ≤ x) :
    gsT3 x k = gsu3 x k * gsT3 (x + 1) k := by
  have p0 : (-(x + 1)) ≠ 0 := by intro h; linarith
  have B1 : dpoch (-x) k = dpoch (-(x + 1)) k * (-(x + 1) + k) / (-(x + 1)) :=
    dpoch_up (-(x + 1)) (-x) (by ring) p0 k
  have q0 : (2 * x + 2 + (k : ℝ)) ≠ 0 := by positivity
  have q1 : (2 * x + 3 + (k : ℝ)) ≠ 0 := by positivity
  have B2 : dpoch (2 * x + 2) k = dpoch (2 * (x + 1) + 2) k * ((2 * x + 2) * (2 * x + 3)) /
      ((2 * x + 2 + k) * (2 * x + 3 + k)) := by
    have a1 := dpoch_dn (2 * x + 2) (2 * x + 3) (by ring) k q0
    have a2 := dpoch_dn (2 * x + 3) (2 * (x + 1) + 2) (by ring) k q1
    rw [a1, a2]
    field_simp
  have q2 : (x + 11 / 6 + (k : ℝ)) ≠ 0 := by positivity
  have B3 : dpoch (x + 11 / 6) k = dpoch (x + 1 + 11 / 6) k * (x + 11 / 6) / (x + 11 / 6 + k) :=
    dpoch_dn (x + 11 / 6) (x + 1 + 11 / 6) (by ring) k q2
  have d1 := dpoch_ne_zero (gs_noNegInt_pos (x := 4 / 3) (by norm_num)) k
  have d2 := dpoch_ne_zero (gs_noNegInt_pos (x := x + 1 + 11 / 6) (by positivity)) k
  have d3 : (k.factorial : ℝ) ≠ 0 := by positivity
  have e1 : (2 * x + 5) ≠ 0 := by positivity
  have e2 : (2 * x + 7) ≠ 0 := by positivity
  have e3 : (10 * (k : ℝ) + 2 * x + 7) ≠ 0 := by positivity
  have e4 : (x + 11 / 6) ≠ 0 := by positivity
  have e5 : (2 * (x + 1) + 5) ≠ 0 := by positivity
  have e6 : (10 * (k : ℝ) + 2 * (x + 1) + 5) ≠ 0 := by positivity
  have e7 : (-x - 1) ≠ 0 := by intro h; linarith
  have e8 : (-1 - x) ≠ 0 := by intro h; linarith
  unfold gsT3 gsu3
  rw [B1, B2, B3]
  generalize dpoch (-(x + 1)) k = A
  generalize dpoch (2 * (x + 1) + 2) k = B
  generalize dpoch (x + 1 + 11 / 6) k = C at d2 ⊢
  generalize dpoch (2 / 3) k = D
  generalize dpoch (4 / 3) k = E at d1 ⊢
  field_simp
  ring

theorem gsS3_succ (n : ℕ) : gsS3 (n + 1) = gsr3 n * gsS3 n := by
  have a1 := dpoch_ne_zero (gs_noNegInt_pos (x := 3 / 2) (by norm_num)) n
  have a2 := dpoch_ne_zero (gs_noNegInt_pos (x := 7 / 2) (by norm_num)) n
  have z1 : (3 / 2 + (n : ℝ)) ≠ 0 := by positivity
  have z2 : (7 / 2 + (n : ℝ)) ≠ 0 := by positivity
  unfold gsS3 gsr3
  simp only [dpoch]
  field_simp

theorem gs_key3 (x k : ℝ) (hx : 0 ≤ x) (hk : 0 ≤ k) :
    1 - gsr3 x * gsu3 x k = gsg3 x (k + 1) * gsrho3 (x + 1) k - gsg3 x k := by
  have e0 : (2 * x + 2 + k) ≠ 0 := by intro h; linarith
  have e1 : (2 * x + 3 + k) ≠ 0 := by intro h; linarith
  have e2 : (2 * x + 5) ≠ 0 := by intro h; linarith
  have e3 : (10 * k + 2 * x + 7) ≠ 0 := by intro h; linarith
  have e4 : (x + 11 / 6) ≠ 0 := by intro h; linarith
  have e5 : (-x - 1) ≠ 0 := by intro h; linarith
  have e6 : (10 * (k + 1) + 2 * x + 7) ≠ 0 := by intro h; linarith
  have e7 : (2 * x + 2 + (k + 1)) ≠ 0 := by intro h; linarith
  have e8 : (2 * x + 3 + (k + 1)) ≠ 0 := by intro h; linarith
  have f1 : (10 * k + 2 * (x + 1) + 5) ≠ 0 := by intro h; linarith
  have f2 : (k + 1) ≠ 0 := by intro h; linarith
  have f3 : (x + 1 + 11 / 6 + k) ≠ 0 := by intro h; linarith
  have f4 : (4 / 3 + k) ≠ 0 := by intro h; linarith
  have f5 : (3 / 2 + x) ≠ 0 := by intro h; linarith
  have f6 : (7 / 2 + x) ≠ 0 := by intro h; linarith
  have f7 : (10 * k + 2 * x + 5) ≠ 0 := by intro h; linarith
  have f8 : (2 * (x + 1) + 2 + k) ≠ 0 := by intro h; linarith
  have f9 : (2 * (x + 1) + 3 + k) ≠ 0 := by intro h; linarith
  unfold gsr3 gsu3 gsg3 gsrho3
  field_simp
  ring

theorem gsF3_wz (n k : ℕ) :
    gsF3 (n + 1) k - gsF3 n k =
      gsg3 n ((k + 1 : ℕ) : ℝ) * gsF3 (n + 1) (k + 1) - gsg3 n k * gsF3 (n + 1) k := by
  have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS0 : gsS3 n ≠ 0 := by
    unfold gsS3
    exact div_ne_zero (mul_ne_zero
      (dpoch_ne_zero (gs_noNegInt_pos (x := 5 / 2) (by norm_num)) n)
      (dpoch_ne_zero (gs_noNegInt_pos (x := 11 / 6) (by norm_num)) n))
      (mul_ne_zero (dpoch_ne_zero (gs_noNegInt_pos (x := 3 / 2) (by norm_num)) n)
        (dpoch_ne_zero (gs_noNegInt_pos (x := 7 / 2) (by norm_num)) n))
  have hr : gsr3 n ≠ 0 := by
    unfold gsr3
    have : (3 / 2 + (n : ℝ)) ≠ 0 := by positivity
    have : (7 / 2 + (n : ℝ)) ≠ 0 := by positivity
    positivity
  unfold gsF3
  rw [hc]
  apply gs_wz_core (gsT3 n k) (gsT3 (n + 1) k) (gsT3 (n + 1) (k + 1)) (gsS3 n)
    (gsS3 (n + 1)) (gsr3 n) (gsu3 n k) (gsrho3 (n + 1) k) (gsg3 n k)
    (gsg3 n ((k + 1 : ℕ) : ℝ))
  · rw [gsS3_succ n]
  · exact hS0
  · exact hr
  · exact gsT3_shift n k hx
  · exact gsT3_succ_k _ k (by positivity)
  · push_cast
    exact gs_key3 n k hx (Nat.cast_nonneg k)

theorem gsF3_sum (n : ℕ) : ∑ k ∈ range (n + 1), gsF3 n k = 1 := by
  refine gs_wz_sum gsF3 (fun n k => gsg3 n k * gsF3 (n + 1) k) (fun n => n)
    (fun n => by omega) ?_ ?_ ?_ ?_ ?_ n
  · intro n k hk
    unfold gsF3 gsT3
    rw [gs_dpoch_zero (-(n : ℝ)) n (by ring) k (by omega)]
    simp
  · intro n k _
    have := gsF3_wz n k
    simpa using this
  · intro n
    simp [gsg3]
  · intro n
    have : gsF3 (n + 1) (n + 1 + 1) = 0 := by
      unfold gsF3 gsT3
      rw [gs_dpoch_zero (-((n + 1 : ℕ) : ℝ)) (n + 1) (by push_cast; ring) (n + 1 + 1) (by omega)]
      simp
    simp [this]
  · simp [gsF3, gsT3, gsS3, dpoch]

/-- CO-468 (3).  Gessel's terminating `4F3` identity at argument `2/27`:
`∑_{k=0}^{n} (3/2+n/5)_k (2/3)_k (-n)_k (2n+2)_k (2/27)^k /
  (k! (n+11/6)_k (4/3)_k (n/5+1/2)_k) = (5/2)_n (11/6)_n / ((3/2)_n (7/2)_n)`.
The certificate printed in the book, `R(n,k) = (9/2) k (3k+1) / ((k-n-1)(2n+10k+5))`, is correct.
The parameters `3/2 + n/5` and `n/5 + 1/2` differ by one, so the corresponding quotient of
Pochhammer symbols is the linear factor `(10k+2n+5)/(2n+5)`; no genericity hypotheses are
needed. -/
@[kb "petkovsekwilfzeilberger1996" "text §7.4, p. 137"]
theorem gessel_three (n : ℕ) :
    ∑ k ∈ range (n + 1),
        dpoch (3 / 2 + (n : ℝ) / 5) k * dpoch (2 / 3) k * dpoch (-(n : ℝ)) k *
            dpoch (2 * (n : ℝ) + 2) k * (2 / 27) ^ k /
          ((k.factorial : ℝ) * dpoch ((n : ℝ) + 11 / 6) k * dpoch (4 / 3) k *
            dpoch ((n : ℝ) / 5 + 1 / 2) k) =
      dpoch (5 / 2) n * dpoch (11 / 6) n / (dpoch (3 / 2) n * dpoch (7 / 2) n) := by
  have hS0 : gsS3 n ≠ 0 := by
    unfold gsS3
    exact div_ne_zero (mul_ne_zero
      (dpoch_ne_zero (gs_noNegInt_pos (x := 5 / 2) (by norm_num)) n)
      (dpoch_ne_zero (gs_noNegInt_pos (x := 11 / 6) (by norm_num)) n))
      (mul_ne_zero (dpoch_ne_zero (gs_noNegInt_pos (x := 3 / 2) (by norm_num)) n)
        (dpoch_ne_zero (gs_noNegInt_pos (x := 7 / 2) (by norm_num)) n))
  have hx : (0 : ℝ) < (n : ℝ) / 5 + 1 / 2 := by positivity
  have key : ∀ k : ℕ, dpoch (3 / 2 + (n : ℝ) / 5) k * dpoch (2 / 3) k * dpoch (-(n : ℝ)) k *
            dpoch (2 * (n : ℝ) + 2) k * (2 / 27) ^ k /
          ((k.factorial : ℝ) * dpoch ((n : ℝ) + 11 / 6) k * dpoch (4 / 3) k *
            dpoch ((n : ℝ) / 5 + 1 / 2) k) = gsT3 n k := by
    intro k
    have a := dpoch_up ((n : ℝ) / 5 + 1 / 2) (3 / 2 + (n : ℝ) / 5) (by ring) hx.ne' k
    have d1 := dpoch_ne_zero (gs_noNegInt_pos hx) k
    have d2 := dpoch_ne_zero (gs_noNegInt_pos (x := (n : ℝ) + 11 / 6) (by positivity)) k
    have d3 := dpoch_ne_zero (gs_noNegInt_pos (x := 4 / 3) (by norm_num)) k
    have d4 : (k.factorial : ℝ) ≠ 0 := by positivity
    have e1 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
    have e2 : (n : ℝ) / 5 + 1 / 2 ≠ 0 := hx.ne'
    unfold gsT3
    rw [a]
    generalize dpoch ((n : ℝ) / 5 + 1 / 2) k = P at d1 ⊢
    generalize dpoch ((n : ℝ) + 11 / 6) k = Q at d2 ⊢
    generalize dpoch (4 / 3) k = E at d3 ⊢
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  exact gs_div_one _ (fun k => gsT3 n k) _ hS0 (gsF3_sum n)

/-! ### Identity (2) -/

theorem gs_dpoch_ne (z : ℝ) (k : ℕ) (h : ∀ i : ℕ, i < k → z + i ≠ 0) : dpoch z k ≠ 0 := by
  induction k with
  | zero => simp [dpoch]
  | succ k ih =>
    simp only [dpoch]
    exact mul_ne_zero (ih fun i hi => h i (by omega)) (h k (by omega))

theorem gs_up3 (y0 z : ℝ) (hz : z = y0 + 1 + 1 + 1) (h0 : y0 ≠ 0) (h1 : y0 + 1 ≠ 0)
    (h2 : y0 + 1 + 1 ≠ 0) (N : ℕ) :
    dpoch z N = dpoch y0 N * ((y0 + N) * (y0 + 1 + N) * (y0 + 1 + 1 + N)) /
      (y0 * (y0 + 1) * (y0 + 1 + 1)) := by
  have a1 := dpoch_up y0 (y0 + 1) rfl h0 N
  have a2 := dpoch_up (y0 + 1) (y0 + 1 + 1) rfl h1 N
  have a3 := dpoch_up (y0 + 1 + 1) z hz h2 N
  rw [a3, a2, a1]
  field_simp

/-- Summand of Gessel's second identity: `x` stands for `n`; the pair `-3n/2, 1/2-3n/2` has been
merged into `(-3n)_{2k} / 4^k`. -/
noncomputable def gsT2 (b x : ℝ) (k : ℕ) : ℝ :=
  dpoch (-(3 * b)) k * dpoch (-(3 * x)) (2 * k) * (1 / 3) ^ k /
    ((k.factorial : ℝ) * dpoch (-(3 * x)) k * dpoch (2 / 3 - b - x) k)

noncomputable def gsS2 (b : ℝ) (n : ℕ) : ℝ := dpoch (1 / 3 - b) n / dpoch (1 / 3 + b) n

noncomputable def gsF2 (b : ℝ) (n k : ℕ) : ℝ := gsT2 b n k / gsS2 b n

noncomputable def gsr2 (b x : ℝ) : ℝ := (1 - 3 * b + 3 * x) / (1 + 3 * b + 3 * x)

noncomputable def gsu2 (b x k : ℝ) : ℝ :=
  ((2 * k - 3 * x - 3) * (2 * k - 3 * x - 2) * (2 * k - 3 * x - 1) * (-1 - 3 * b - 3 * x)) /
    ((k - 3 * x - 3) * (k - 3 * x - 2) * (k - 3 * x - 1) * (3 * k - 3 * x - 3 * b - 1))

noncomputable def gsg2 (x k : ℝ) : ℝ :=
  k * (3 * k - 5 - 6 * x) / ((k - 3 * x - 3) * (k - 3 * x - 2))

noncomputable def gsrho2 (b x k : ℝ) : ℝ :=
  (-(3 * b) + k) * (-(3 * x) + 2 * k) * (-(3 * x) + 2 * k + 1) /
    ((k + 1) * (-(3 * x) + k) * (2 - 3 * b - 3 * x + 3 * k))

theorem gsT2_succ_k (b x : ℝ) (k : ℕ) (hk : (k : ℝ) < 3 * x)
    (hb : ∀ j : ℤ, 2 / 3 - b - x + j ≠ 0) :
    gsT2 b x (k + 1) = gsrho2 b x k * gsT2 b x k := by
  have h1 : (2 - 3 * b - 3 * x + 3 * k) ≠ 0 := by
    have := hb k; push_cast at this; intro h; apply this; linarith
  have h2 : (-(3 * x) + k) ≠ 0 := by intro h; linarith
  have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
  have d1 : dpoch (-(3 * x)) k ≠ 0 := gs_dpoch_ne _ k (fun i hi => by
    have : (i : ℝ) < k := by exact_mod_cast hi
    intro h; linarith)
  have d2 : dpoch (2 / 3 - b - x) k ≠ 0 := gs_dpoch_ne _ k (fun i hi => by
    have := hb i; push_cast at this; exact this)
  have d3 : (k.factorial : ℝ) ≠ 0 := by positivity
  have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
  unfold gsT2 gsrho2
  rw [e]
  simp only [dpoch, Nat.factorial_succ, pow_succ]
  push_cast
  generalize dpoch (-(3 * x)) k = A at d1 ⊢
  generalize dpoch (2 / 3 - b - x) k = B at d2 ⊢
  generalize dpoch (-(3 * x)) (2 * k) = C
  generalize dpoch (-(3 * b)) k = D
  field_simp
  ring

theorem gsT2_shift (b x : ℝ) (k : ℕ) (hx : 0 ≤ x) (hk : (k : ℝ) ≤ 3 * x)
    (hb : ∀ j : ℤ, 2 / 3 - b - x + j ≠ 0) :
    gsT2 b x k = gsu2 b x k * gsT2 b (x + 1) k := by
  have p0 : (-(3 * (x + 1))) ≠ 0 := by intro h; linarith
  have p1 : (-(3 * (x + 1)) + 1) ≠ 0 := by intro h; linarith
  have p2 : (-(3 * (x + 1)) + 1 + 1) ≠ 0 := by intro h; linarith
  have hy : (2 / 3 - b - (x + 1)) ≠ 0 := by
    have := hb (-1); push_cast at this; intro h; apply this; linarith
  have hy1 : (2 / 3 - b - (x + 1) + k) ≠ 0 := by
    have := hb ((k : ℤ) - 1); push_cast at this; intro h; apply this; linarith
  have B1 := gs_up3 (-(3 * (x + 1))) (-(3 * x)) (by ring) p0 p1 p2 (2 * k)
  have B2 := gs_up3 (-(3 * (x + 1))) (-(3 * x)) (by ring) p0 p1 p2 k
  have B3 : dpoch (2 / 3 - b - x) k =
      dpoch (2 / 3 - b - (x + 1)) k * (2 / 3 - b - (x + 1) + k) / (2 / 3 - b - (x + 1)) :=
    dpoch_up (2 / 3 - b - (x + 1)) (2 / 3 - b - x) (by ring) hy k
  have d1 : dpoch (-(3 * (x + 1))) k ≠ 0 := gs_dpoch_ne _ k (fun i hi => by
    have : (i : ℝ) < k := by exact_mod_cast hi
    intro h; linarith)
  have d2 : dpoch (2 / 3 - b - (x + 1)) k ≠ 0 := gs_dpoch_ne _ k (fun i hi => by
    have := hb ((i : ℤ) - 1); push_cast at this; intro h; apply this; linarith)
  have d3 : (k.factorial : ℝ) ≠ 0 := by positivity
  have c1 : (k : ℝ) - 3 * x - 3 ≠ 0 := by intro h; linarith
  have c2 : (k : ℝ) - 3 * x - 2 ≠ 0 := by intro h; linarith
  have c3 : (k : ℝ) - 3 * x - 1 ≠ 0 := by intro h; linarith
  have c4 : 3 * (k : ℝ) - 3 * x - 3 * b - 1 ≠ 0 := by intro h; apply hy1; linarith
  have c5 : (-1 - 3 * b - 3 * x) ≠ 0 := by intro h; apply hy; linarith
  have c4' : -1 + (k : ℝ) * 3 - x * 3 - b * 3 ≠ 0 := by intro h; apply hy1; linarith
  have c5' : -1 - b * 3 - x * 3 ≠ 0 := by intro h; apply hy; linarith
  have c6 : (-(3 * (x + 1)) + k) ≠ 0 := by intro h; linarith
  have c7 : (-(3 * (x + 1)) + 1 + k) ≠ 0 := by intro h; linarith
  have c8 : (-(3 * (x + 1)) + 1 + 1 + k) ≠ 0 := by intro h; linarith
  have c9 : (-(3 * (x + 1)) + 1) ≠ 0 := p1
  unfold gsT2 gsu2
  rw [B1, B2, B3]
  push_cast
  generalize dpoch (-(3 * (x + 1))) (2 * k) = A
  generalize dpoch (-(3 * (x + 1))) k = A' at d1 B2 ⊢
  generalize dpoch (2 / 3 - b - (x + 1)) k = B at d2 ⊢
  generalize dpoch (-(3 * b)) k = D
  field_simp
  ring

theorem gsS2_succ (b : ℝ) (n : ℕ) (h1 : NoNegInt (1 / 3 - b)) (h2 : NoNegInt (1 / 3 + b)) :
    gsS2 b (n + 1) = gsr2 b n * gsS2 b n := by
  have a1 := dpoch_ne_zero h2 n
  have z1 : 1 / 3 + b + n ≠ 0 := by simpa using h2 n
  have z2 : 1 + 3 * b + 3 * n ≠ 0 := by intro h; apply z1; linarith
  unfold gsS2 gsr2
  simp only [dpoch]
  field_simp

theorem gs_key2 (b x k : ℝ) (hx : 0 ≤ x) (hk0 : 0 ≤ k) (hk : k ≤ 3 * x)
    (h1 : 2 / 3 - b - (x + 1) + k ≠ 0) (h2 : 1 / 3 + b + x ≠ 0) :
    1 - gsr2 b x * gsu2 b x k = gsg2 x (k + 1) * gsrho2 b (x + 1) k - gsg2 x k := by
  have h1' : 3 * k - 3 * x - 3 * b - 1 ≠ 0 := by intro h; apply h1; linarith
  have h1'' : 1 + 3 * b + 3 * x ≠ 0 := by intro h; apply h2; linarith
  have c1 : k - 3 * x - 3 ≠ 0 := by intro h; linarith
  have c2 : k - 3 * x - 2 ≠ 0 := by intro h; linarith
  have c3 : k - 3 * x - 1 ≠ 0 := by intro h; linarith
  have c4 : k + 1 - 3 * x - 3 ≠ 0 := by intro h; linarith
  have c5 : k + 1 - 3 * x - 2 ≠ 0 := by intro h; linarith
  have c6 : -(3 * (x + 1)) + k ≠ 0 := by intro h; linarith
  have c7 : k + 1 ≠ 0 := by intro h; linarith
  unfold gsr2 gsu2 gsg2 gsrho2
  rw [show (2 - 3 * b - 3 * (x + 1) + 3 * k) = 3 * k - 3 * x - 3 * b - 1 by ring]
  generalize hD : 3 * k - 3 * x - 3 * b - 1 = D at h1' ⊢
  field_simp
  subst hD
  ring

theorem gsF2_wz (b : ℝ) (h1 : NoNegInt (1 / 3 - b)) (h2 : NoNegInt (1 / 3 + b))
    (h3 : ∀ j : ℤ, 2 / 3 - b + j ≠ 0) (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 3 * (n + 1) / 2) :
    gsF2 b (n + 1) k - gsF2 b n k =
      gsg2 n ((k + 1 : ℕ) : ℝ) * gsF2 b (n + 1) (k + 1) - gsg2 n k * gsF2 b (n + 1) k := by
  have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk3 : (k : ℝ) ≤ 3 * n := by
    have : k ≤ 3 * n := by omega
    exact_mod_cast this
  have hS0 : gsS2 b n ≠ 0 := by
    unfold gsS2
    exact div_ne_zero (dpoch_ne_zero h1 n) (dpoch_ne_zero h2 n)
  have z1 : 1 / 3 - b + (n : ℝ) ≠ 0 := by simpa using h1 n
  have z2 : 1 / 3 + b + (n : ℝ) ≠ 0 := by simpa using h2 n
  have hr : gsr2 b n ≠ 0 := by
    unfold gsr2
    refine div_ne_zero ?_ ?_ <;> intro h
    · apply z1; linarith
    · apply z2; linarith
  have hbn : ∀ j : ℤ, 2 / 3 - b - (n : ℝ) + j ≠ 0 := fun j => by
    have := h3 (j - n); push_cast at this; intro h; apply this; linarith
  have hbn1 : ∀ j : ℤ, 2 / 3 - b - ((n : ℝ) + 1) + j ≠ 0 := fun j => by
    have := h3 (j - n - 1); push_cast at this; intro h; apply this; linarith
  have hk1 : 2 / 3 - b - ((n : ℝ) + 1) + k ≠ 0 := by
    have := hbn1 k; push_cast at this; exact this
  unfold gsF2
  rw [hc]
  apply gs_wz_core (gsT2 b n k) (gsT2 b (n + 1) k) (gsT2 b (n + 1) (k + 1)) (gsS2 b n)
    (gsS2 b (n + 1)) (gsr2 b n) (gsu2 b n k) (gsrho2 b (n + 1) k) (gsg2 n k)
    (gsg2 n ((k + 1 : ℕ) : ℝ))
  · rw [gsS2_succ b n h1 h2]
  · exact hS0
  · exact hr
  · exact gsT2_shift b n k hx hk3 hbn
  · exact gsT2_succ_k b _ k (by linarith) hbn1
  · push_cast
    exact gs_key2 b n k hx (Nat.cast_nonneg k) hk3 hk1 z2

theorem gsF2_sum (b : ℝ) (h1 : NoNegInt (1 / 3 - b)) (h2 : NoNegInt (1 / 3 + b))
    (h3 : ∀ j : ℤ, 2 / 3 - b + j ≠ 0) (n : ℕ) :
    ∑ k ∈ range (3 * (n + 1) / 2 + 1), gsF2 b (n + 1) k = 1 := by
  refine gs_wz_sum (fun n k => gsF2 b (n + 1) k) (fun n k => gsg2 (n + 1 : ℕ) k *
      gsF2 b (n + 1 + 1) k) (fun n => 3 * (n + 1) / 2) (fun n => by omega) ?_ ?_ ?_ ?_ ?_ n
  · intro n k hk
    unfold gsF2 gsT2
    rw [gs_dpoch_zero (-(3 * ((n + 1 : ℕ) : ℝ))) (3 * (n + 1)) (by push_cast; ring) (2 * k)
      (by omega)]
    simp
  · intro n k hk
    have := gsF2_wz b h1 h2 h3 (n + 1) k (by omega) hk
    simpa using this
  · intro n
    simp [gsg2]
  · intro n
    have : gsF2 b (n + 1 + 1) (3 * (n + 1 + 1) / 2 + 1) = 0 := by
      unfold gsF2 gsT2
      rw [gs_dpoch_zero (-(3 * ((n + 1 + 1 : ℕ) : ℝ))) (3 * (n + 1 + 1)) (by push_cast; ring)
        (2 * (3 * (n + 1 + 1) / 2 + 1)) (by omega)]
      simp
    simp [this]
  · have e1 : (1 / 3 + b) ≠ 0 := by simpa using h2 0
    have e2 : (1 / 3 - b) ≠ 0 := by simpa using h1 0
    have e3 : (-1 / 3 - b) ≠ 0 := by
      have := h3 (-1); push_cast at this; intro h; apply this; linarith
    show ∑ k ∈ range 2, gsF2 b (0 + 1) k = 1
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    unfold gsF2 gsT2 gsS2
    simp only [dpoch, Nat.factorial]
    push_cast
    have f1 : (-1 - 3 * b) ≠ 0 := by intro h; apply e3; linarith
    have f2 : (1 - 3 * b) ≠ 0 := by intro h; apply e2; linarith
    have g1 : (2 / 3 - b - 1 + 0 : ℝ) = (-1 - 3 * b) / 3 := by ring
    have g2 : (1 / 3 - b + 0 : ℝ) = (1 - 3 * b) / 3 := by ring
    have g3 : (1 / 3 + b + 0 : ℝ) = (1 + 3 * b) / 3 := by ring
    rw [g1, g2, g3]
    have f3 : (1 + 3 * b) ≠ 0 := by intro h; apply e1; linarith
    field_simp
    ring

theorem gs_dup (x : ℝ) (k : ℕ) : dpoch x (2 * k) = 4 ^ k * (dpoch (x / 2) k * dpoch ((x + 1) / 2) k) := by
  induction k with
  | zero => simp [dpoch]
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [dpoch]
    rw [ih]
    push_cast
    ring

/-- CO-468 (2).  Gessel's terminating `3F2` identity at argument `4/3`, with the numerator
parameter pair `-3n/2`, `1/2-3n/2` (written `(-3n)/2` and `(-3n+1)/2`): for a natural number `n`,
`∑_{k ≤ 3n/2} (-3b)_k (-3n/2)_k (1/2-3n/2)_k (4/3)^k / (k! (-3n)_k (2/3-b-n)_k)
  = (1/3-b)_n / (1/3+b)_n`.
The sum runs over `k ≤ ⌊3n/2⌋`, where the pair of numerator parameters terminates it (for `n = 0`
the summand is read with the single term `k = 0`).  The printed certificate
`R(n,k) = k(k-3n-1)(3k-3n-3b-1)(3k-5-6n) / ((2k-3n-1)(2k-3n-2)(2k-3n-3)(3b-3n-1))` is correct; the
WZ mate is `G(n,k) = R(n,k) F(n,k)`.  Lean adds the genericity hypotheses that `1/3-b`, `1/3+b`
are not nonpositive integers and that `2/3-b` is not an integer, so that no denominator
(including those of the right side) vanishes. -/
@[kb "petkovsekwilfzeilberger1996" "text §7.4, p. 137"]
theorem gessel_two (b : ℝ) (h1 : NoNegInt (1 / 3 - b)) (h2 : NoNegInt (1 / 3 + b))
    (h3 : ∀ j : ℤ, 2 / 3 - b + j ≠ 0) (n : ℕ) :
    ∑ k ∈ range (3 * n / 2 + 1),
        dpoch (-(3 * b)) k * dpoch (-(3 * (n : ℝ)) / 2) k * dpoch ((-(3 * (n : ℝ)) + 1) / 2) k *
            (4 / 3) ^ k /
          ((k.factorial : ℝ) * dpoch (-(3 * (n : ℝ))) k * dpoch (2 / 3 - b - n) k) =
      dpoch (1 / 3 - b) n / dpoch (1 / 3 + b) n := by
  cases n with
  | zero => simp [dpoch]
  | succ m =>
    have hS0 : gsS2 b (m + 1) ≠ 0 := by
      unfold gsS2
      exact div_ne_zero (dpoch_ne_zero h1 _) (dpoch_ne_zero h2 _)
    have key : ∀ k : ℕ,
        dpoch (-(3 * b)) k * dpoch (-(3 * ((m + 1 : ℕ) : ℝ)) / 2) k *
            dpoch ((-(3 * ((m + 1 : ℕ) : ℝ)) + 1) / 2) k * (4 / 3) ^ k /
          ((k.factorial : ℝ) * dpoch (-(3 * ((m + 1 : ℕ) : ℝ))) k *
            dpoch (2 / 3 - b - ((m + 1 : ℕ) : ℝ)) k) = gsT2 b ((m + 1 : ℕ) : ℝ) k := by
      intro k
      unfold gsT2
      rw [gs_dup (-(3 * ((m + 1 : ℕ) : ℝ))) k]
      have : (4 / 3 : ℝ) ^ k = 4 ^ k * (1 / 3) ^ k := by rw [← mul_pow]; norm_num
      rw [this]
      ring
    rw [Finset.sum_congr rfl (fun k _ => key k)]
    exact gs_div_one _ (fun k => gsT2 b ((m + 1 : ℕ) : ℝ) k) _ hS0 (gsF2_sum b h1 h2 h3 m)

end UndergradKB.Combinatorics.AeqB
