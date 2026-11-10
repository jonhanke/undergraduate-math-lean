import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB.Identities3d
open Finset Filter Topology
open scoped Nat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-- `U_{a,b,m}(r) = (r+b)! (r+a)! / (r! (r+a+b+m)!)`. -/
noncomputable def Uf (a b m r : ℕ) : ℝ :=
  (((r + b)! * (r + a)! : ℕ) : ℝ) / (((r ! * (r + a + b + m)! : ℕ)) : ℝ)

/-- The telescoping potential `r (r+a+b+2) U_{a,b,m}(r)`. -/
noncomputable def hh (a b m r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) + a + b + 2) * Uf a b m r

lemma Uf_nonneg (a b m r : ℕ) : 0 ≤ Uf a b m r := by unfold Uf; positivity

lemma Uf_succ (a b m r : ℕ) :
    Uf a b m (r + 1) = Uf a b m r * (((r : ℝ) + b + 1) * ((r : ℝ) + a + 1))
      / (((r : ℝ) + 1) * ((r : ℝ) + a + b + m + 1)) := by
  unfold Uf
  have e1 : r + 1 + b = (r + b) + 1 := by ring
  have e2 : r + 1 + a = (r + a) + 1 := by ring
  have e3 : r + a + 1 + b + m = (r + a + b + m) + 1 := by ring
  rw [e1, e2, e3, Nat.factorial_succ (r + b), Nat.factorial_succ (r + a), Nat.factorial_succ r,
    Nat.factorial_succ (r + a + b + m)]
  have p1 := Nat.factorial_pos (r + b)
  have p2 := Nat.factorial_pos (r + a)
  have p3 := Nat.factorial_pos r
  have p4 := Nat.factorial_pos (r + a + b + m)
  push_cast
  field_simp

lemma Uf_shift (a b n r : ℕ) :
    Uf (a + 1) (b + 1) n r = Uf a b (n + 1) r * (((r : ℝ) + b + 1) * ((r : ℝ) + a + 1))
      / ((r : ℝ) + a + b + n + 2) := by
  unfold Uf
  have e1 : r + (b + 1) = (r + b) + 1 := by ring
  have e2 : r + (a + 1) = (r + a) + 1 := by ring
  have e3 : r + a + 1 + (b + 1) + n = (r + a + b + (n + 1)) + 1 := by ring
  rw [e1, e2, e3, Nat.factorial_succ (r + b), Nat.factorial_succ (r + a),
    Nat.factorial_succ (r + a + b + (n + 1))]
  have p1 := Nat.factorial_pos (r + b)
  have p2 := Nat.factorial_pos (r + a)
  have p3 := Nat.factorial_pos r
  have p4 := Nat.factorial_pos (r + a + b + (n + 1))
  push_cast
  field_simp
  ring

lemma hh_tele (a b n r : ℕ) :
    ((a : ℝ) + 1) * ((b : ℝ) + 1) * Uf a b (n + 1) r
        - ((n : ℝ) - 1) * Uf (a + 1) (b + 1) n r = hh a b (n + 1) (r + 1) - hh a b (n + 1) r := by
  unfold hh
  rw [Uf_succ, Uf_shift]
  push_cast
  have hx : (0 : ℝ) < (r : ℝ) + a + b + n + 2 := by positivity
  have hx' : (0 : ℝ) < (r : ℝ) + a + b + (n + 1 : ℕ) + 1 := by push_cast; positivity
  push_cast at hx'
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  field_simp
  ring

lemma Uf_eq_asc (a b m r : ℕ) :
    Uf a b m r = (((r + 1).ascFactorial a : ℕ) : ℝ) / (((r + b + 1).ascFactorial (a + m) : ℕ) : ℝ) := by
  have h1 := Nat.factorial_mul_ascFactorial r a
  have h2 := Nat.factorial_mul_ascFactorial (r + b) (a + m)
  have e : r + b + (a + m) = r + a + b + m := by ring
  rw [e] at h2
  have p1 := Nat.factorial_pos r
  have p2 := Nat.factorial_pos (r + b)
  have q1 : (0 : ℝ) < (((r + b + 1).ascFactorial (a + m) : ℕ) : ℝ) := by
    exact_mod_cast Nat.ascFactorial_pos (r + b) (a + m)
  unfold Uf
  rw [← h1, ← h2]
  push_cast
  field_simp

lemma tendsto_ratio_pow (c d : ℝ) (hd : 0 < d) (m : ℕ) :
    Tendsto (fun r : ℕ => (((r : ℝ) + c) / ((r : ℝ) + d)) ^ m) atTop (𝓝 1) := by
  have h0 : Tendsto (fun r : ℕ => (c - d) / ((r : ℝ) + d)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have h1 : Tendsto (fun r : ℕ => 1 + (c - d) / ((r : ℝ) + d)) atTop (𝓝 1) := by
    simpa using h0.const_add 1
  have h2 : Tendsto (fun r : ℕ => ((r : ℝ) + c) / ((r : ℝ) + d)) atTop (𝓝 1) := by
    refine h1.congr fun r => ?_
    have : (r : ℝ) + d ≠ 0 := by positivity
    field_simp
    ring
  simpa using h2.pow m

lemma pow_div_aux (x y : ℝ) (hy : y ≠ 0) (n k : ℕ) :
    (x / y) ^ n * (1 / y) ^ k = x ^ n / y ^ (n + k) := by
  rw [pow_add, div_pow, one_div, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

lemma hh_upper (a b k r : ℕ) :
    hh a b (k + 2) r ≤ (((r : ℝ) + (a + b + 2)) / ((r : ℝ) + (b + 1))) ^ (a + 2)
      * (1 / ((r : ℝ) + (b + 1))) ^ k := by
  have hasc : (((r + 1).ascFactorial a : ℕ) : ℝ) ≤ ((r : ℝ) + a) ^ a := by
    exact_mod_cast Nat.ascFactorial_le_pow_add r a
  have hasc2 : ((r : ℝ) + b + 1) ^ (a + (k + 2)) ≤
      (((r + b + 1).ascFactorial (a + (k + 2)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_succ_le_ascFactorial (r + b + 1) (a + (k + 2))
  have hpos : (0 : ℝ) < (r : ℝ) + b + 1 := by positivity
  have hp2 : (0 : ℝ) < ((r : ℝ) + b + 1) ^ (a + (k + 2)) := by positivity
  have hq : (0 : ℝ) ≤ (((r + 1).ascFactorial a : ℕ) : ℝ) := by positivity
  unfold hh
  rw [Uf_eq_asc]
  have hA : (0 : ℝ) < (((r + b + 1).ascFactorial (a + (k + 2)) : ℕ) : ℝ) :=
    lt_of_lt_of_le hp2 hasc2
  have hS : (0 : ℝ) < (r : ℝ) + (a + b + 2) := by positivity
  have hrr : (r : ℝ) ≤ (r : ℝ) + (a + b + 2) := by
    have : (0 : ℝ) ≤ (a : ℝ) + b + 2 := by positivity
    linarith
  have hrr2 : (r : ℝ) + a ≤ (r : ℝ) + (a + b + 2) := by
    have : (0 : ℝ) ≤ (b : ℝ) + 2 := by positivity
    linarith
  have e : (((r : ℝ) + (a + b + 2)) / ((r : ℝ) + (b + 1))) ^ (a + 2)
      * (1 / ((r : ℝ) + (b + 1))) ^ k
      = ((r : ℝ) + (a + b + 2)) ^ (a + 2) / ((r : ℝ) + b + 1) ^ (a + (k + 2)) := by
    rw [show (r : ℝ) + (b + 1) = (r : ℝ) + b + 1 by ring,
      show a + (k + 2) = (a + 2) + k by ring]
    exact pow_div_aux _ _ hpos.ne' _ _
  rw [e, ← mul_div_assoc, div_le_div_iff₀ hA hp2]
  have hSa : ((r : ℝ) + a) ^ a ≤ ((r : ℝ) + (a + b + 2)) ^ a := pow_le_pow_left₀ (by positivity) hrr2 a
  have h3 : (r : ℝ) * ((r : ℝ) + a + b + 2) * (((r + 1).ascFactorial a : ℕ) : ℝ)
      ≤ ((r : ℝ) + (a + b + 2)) ^ (a + 2) := by
    calc (r : ℝ) * ((r : ℝ) + a + b + 2) * (((r + 1).ascFactorial a : ℕ) : ℝ)
        = ((r : ℝ) * ((r : ℝ) + (a + b + 2))) * (((r + 1).ascFactorial a : ℕ) : ℝ) := by ring
      _ ≤ (((r : ℝ) + (a + b + 2)) * ((r : ℝ) + (a + b + 2))) * ((r : ℝ) + (a + b + 2)) ^ a :=
          mul_le_mul (mul_le_mul_of_nonneg_right hrr hS.le) (hasc.trans hSa) hq (by positivity)
      _ = _ := by ring
  calc (r : ℝ) * ((r : ℝ) + a + b + 2) * (((r + 1).ascFactorial a : ℕ) : ℝ)
        * ((r : ℝ) + b + 1) ^ (a + (k + 2))
      ≤ ((r : ℝ) + (a + b + 2)) ^ (a + 2) * ((r : ℝ) + b + 1) ^ (a + (k + 2)) :=
        mul_le_mul_of_nonneg_right h3 hp2.le
    _ ≤ ((r : ℝ) + (a + b + 2)) ^ (a + 2)
          * (((r + b + 1).ascFactorial (a + (k + 2)) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hasc2 (by positivity)

lemma hh_tendsto_zero (a b k : ℕ) : Tendsto (hh a b (k + 3)) atTop (𝓝 0) := by
  have h1 := tendsto_ratio_pow ((a : ℝ) + b + 2) ((b : ℝ) + 1) (by positivity) (a + 2)
  have h2 : Tendsto (fun r : ℕ => (1 / ((r : ℝ) + ((b : ℝ) + 1))) ^ (k + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R := ℝ)) :
        Tendsto (fun r : ℕ => (r : ℝ) + ((b : ℝ) + 1)) atTop atTop)
    simpa using this.pow (k + 1)
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  refine squeeze_zero (fun r => ?_) (fun r => ?_) h3
  · unfold hh; have := Uf_nonneg a b (k + 3) r; positivity
  · have := hh_upper a b (k + 1) r
    simpa [show k + 1 + 2 = k + 3 by ring] using this

lemma hh_lower (a b r : ℕ) :
    ((r : ℝ) / ((r : ℝ) + (a + b + 2))) ^ (a + 1) ≤ hh a b 2 r := by
  have hx : (((r + 1) ^ a : ℕ) : ℝ) ≤ (((r + 1).ascFactorial a : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_succ_le_ascFactorial (r + 1) a
  have hy : (((r + b + 1).ascFactorial (a + 2) : ℕ) : ℝ) ≤ ((r : ℝ) + (b + (a + 2))) ^ (a + 2) := by
    have := Nat.ascFactorial_le_pow_add (r + b) (a + 2)
    have h' : (((r + b + 1).ascFactorial (a + 2) : ℕ) : ℝ) ≤ (((r + b + (a + 2) : ℕ) : ℝ)) ^ (a + 2) := by
      exact_mod_cast this
    push_cast at h'
    rw [show (r : ℝ) + (b + (a + 2)) = (r : ℝ) + b + (a + 2) by ring]
    exact h'
  have hypos : (0 : ℝ) < (((r + b + 1).ascFactorial (a + 2) : ℕ) : ℝ) := by
    exact_mod_cast Nat.ascFactorial_pos (r + b) (a + 2)
  have hS : (0 : ℝ) < (r : ℝ) + (a + b + 2) := by positivity
  unfold hh
  rw [Uf_eq_asc, show a + 2 = a + 2 from rfl, div_pow, ← mul_div_assoc,
    div_le_div_iff₀ (by positivity) hypos]
  push_cast at hx
  have hr1 : (r : ℝ) ^ a ≤ ((r : ℝ) + 1) ^ a := pow_le_pow_left₀ (by positivity) (by linarith) a
  have e : (r : ℝ) + (b + (a + 2)) = (r : ℝ) + (a + b + 2) := by ring
  rw [e] at hy
  have h1 : (r : ℝ) ^ (a + 1) * (((r + b + 1).ascFactorial (a + 2) : ℕ) : ℝ)
      ≤ (r : ℝ) ^ (a + 1) * ((r : ℝ) + (a + b + 2)) ^ (a + 2) :=
    mul_le_mul_of_nonneg_left hy (by positivity)
  have h2 : (r : ℝ) ^ (a + 1) * ((r : ℝ) + (a + b + 2)) ^ (a + 2)
      = (r : ℝ) * ((r : ℝ) + (a + b + 2)) * (r : ℝ) ^ a * ((r : ℝ) + (a + b + 2)) ^ (a + 1) := by
    ring
  have h3 : (r : ℝ) * ((r : ℝ) + (a + b + 2)) * (r : ℝ) ^ a * ((r : ℝ) + (a + b + 2)) ^ (a + 1)
      ≤ (r : ℝ) * ((r : ℝ) + a + b + 2) * (((r + 1).ascFactorial a : ℕ) : ℝ)
        * ((r : ℝ) + (a + b + 2)) ^ (a + 1) := by
    have : (r : ℝ) ^ a ≤ (((r + 1).ascFactorial a : ℕ) : ℝ) := hr1.trans hx
    have e2 : (r : ℝ) + a + b + 2 = (r : ℝ) + (a + b + 2) := by ring
    rw [e2]
    gcongr
  linarith

lemma hh_tendsto_one (a b : ℕ) : Tendsto (hh a b 2) atTop (𝓝 1) := by
  have hlow := tendsto_ratio_pow (0 : ℝ) ((a : ℝ) + b + 2) (by positivity) (a + 1)
  have hup := tendsto_ratio_pow ((a : ℝ) + b + 2) ((b : ℝ) + 1) (by positivity) (a + 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun r : ℕ => (((r : ℝ) + 0) / ((r : ℝ) + ((a : ℝ) + b + 2))) ^ (a + 1))
    (h := fun r : ℕ => (((r : ℝ) + ((a : ℝ) + b + 2)) / ((r : ℝ) + ((b : ℝ) + 1))) ^ (a + 2))
    hlow hup (fun r => ?_) (fun r => ?_)
  · have := hh_lower a b r
    simpa using this
  · have := hh_upper a b 0 r
    simpa using this

lemma hh_zero (a b m : ℕ) : hh a b m 0 = 0 := by simp [hh]

lemma Uf_step (a b n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : HasSum (Uf (a + 1) (b + 1) n) s) :
    HasSum (Uf a b (n + 1)) (((n : ℝ) - 1) / (((a : ℝ) + 1) * ((b : ℝ) + 1)) * s) := by
  have hpos : (0 : ℝ) < ((a : ℝ) + 1) * ((b : ℝ) + 1) := by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg (Uf_nonneg a b (n + 1))]
  have hps := hs.tendsto_sum_nat
  have key : ∀ M, ∑ i ∈ range M, Uf a b (n + 1) i
      = (((n : ℝ) - 1) / (((a : ℝ) + 1) * ((b : ℝ) + 1))) * ∑ i ∈ range M, Uf (a + 1) (b + 1) n i
        + (hh a b (n + 1) M - hh a b (n + 1) 0) / (((a : ℝ) + 1) * ((b : ℝ) + 1)) := by
    intro M
    have h1 : ∑ i ∈ range M, (((a : ℝ) + 1) * ((b : ℝ) + 1) * Uf a b (n + 1) i
        - ((n : ℝ) - 1) * Uf (a + 1) (b + 1) n i) = hh a b (n + 1) M - hh a b (n + 1) 0 := by
      rw [sum_congr rfl fun i _ => hh_tele a b n i]
      exact Finset.sum_range_sub (fun i => hh a b (n + 1) i) M
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum] at h1
    field_simp
    linarith
  simp_rw [key]
  have hlim := hh_tendsto_zero a b (n - 2)
  rw [show n - 2 + 3 = n + 1 by omega] at hlim
  have := (hps.const_mul (((n : ℝ) - 1) / (((a : ℝ) + 1) * ((b : ℝ) + 1)))).add
    ((hlim.sub_const (hh a b (n + 1) 0)).div_const (((a : ℝ) + 1) * ((b : ℝ) + 1)))
  simpa [hh_zero] using this

lemma Uf_base (a b : ℕ) : HasSum (Uf a b 2) (1 / (((a : ℝ) + 1) * ((b : ℝ) + 1))) := by
  have hpos : (0 : ℝ) < ((a : ℝ) + 1) * ((b : ℝ) + 1) := by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg (Uf_nonneg a b 2)]
  have key : ∀ M, ∑ i ∈ range M, Uf a b 2 i = hh a b 2 M / (((a : ℝ) + 1) * ((b : ℝ) + 1)) := by
    intro M
    have h1 : ∑ i ∈ range M, (((a : ℝ) + 1) * ((b : ℝ) + 1) * Uf a b 2 i)
        = hh a b 2 M - hh a b 2 0 := by
      rw [sum_congr rfl fun i _ => by simpa using hh_tele a b 1 i]
      exact Finset.sum_range_sub (fun i => hh a b 2 i) M
    rw [← mul_sum, hh_zero, sub_zero] at h1
    field_simp
    linarith
  simp_rw [key]
  simpa using (hh_tendsto_one a b).div_const (((a : ℝ) + 1) * ((b : ℝ) + 1))

lemma Uf_closed (t : ℕ) : ∀ p q : ℕ, HasSum (Uf p q (t + 2))
    (((t ! * p ! * q ! : ℕ) : ℝ) / (((t + p + 1)! * (t + q + 1)! : ℕ) : ℝ)) := by
  induction t with
  | zero =>
    intro p q
    have := Uf_base p q
    convert this using 1
    simp only [Nat.factorial_zero, zero_add, Nat.factorial_succ, Nat.one_mul]
    have h1 : (p ! : ℝ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    have h2 : (q ! : ℝ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    push_cast
    field_simp
  | succ t ih =>
    intro p q
    have h := Uf_step p q (t + 2) (by omega) _ (ih (p + 1) (q + 1))
    convert h using 1
    have e1 : t + 1 + p + 1 = (t + p + 1) + 1 := by ring
    have e2 : t + 1 + q + 1 = (t + q + 1) + 1 := by ring
    have e3 : t + (p + 1) + 1 = (t + p + 1) + 1 := by ring
    have e4 : t + (q + 1) + 1 = (t + q + 1) + 1 := by ring
    rw [e1, e2, e3, e4]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
    have h1 : (p ! : ℝ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    have h2 : (q ! : ℝ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    have h3 : ((t + p + 1)! : ℝ) ≠ 0 := by exact_mod_cast (t + p + 1).factorial_ne_zero
    have h4 : ((t + q + 1)! : ℝ) ≠ 0 := by exact_mod_cast (t + q + 1).factorial_ne_zero
    have h5 : (t ! : ℝ) ≠ 0 := by exact_mod_cast t.factorial_ne_zero
    push_cast
    field_simp
    ring

/-- CO-456 (companion of Example 7.3.2 = Gauss's `2F1(1)` identity, eq. (7.3.4)). For naturals
`2 ≤ k ≤ i`, `k ≤ j`:
`∑_{r ≥ 0} (r+j-k)! (r+i-k)! / (r! (r+i+j-k)!) = (k-2)! (i-k)! (j-k)! / ((i-1)! (j-1)!)`.
This is a nonterminating case of Gauss's summation; it is proved here by telescoping in `k`
(the companion identity of the certificate `R = (k-1)/n` of the identity (7.3.3)). -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.3.2, p. 139"]
theorem gauss_companion (i j k : ℕ) (hk : 2 ≤ k) (hki : k ≤ i) (hkj : k ≤ j) :
    HasSum (fun r : ℕ => (((r + j - k)! * (r + i - k)! : ℕ) : ℝ) / (((r ! * (r + i + j - k)! : ℕ)) : ℝ))
      ((((k - 2)! * (i - k)! * (j - k)! : ℕ) : ℝ) / ((((i - 1)! * (j - 1)! : ℕ)) : ℝ)) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hki
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hkj
  have h := Uf_closed t p q
  convert h using 1
  · funext r
    unfold Uf
    have e1 : r + (t + 2 + q) - (t + 2) = r + q := by omega
    have e2 : r + (t + 2 + p) - (t + 2) = r + p := by omega
    have e3 : r + (t + 2 + p) + (t + 2 + q) - (t + 2) = r + p + q + (t + 2) := by omega
    rw [e1, e2, e3]
  · have e1 : t + 2 - 2 = t := by omega
    have e2 : t + 2 + p - (t + 2) = p := by omega
    have e3 : t + 2 + q - (t + 2) = q := by omega
    have e4 : t + 2 + p - 1 = t + p + 1 := by omega
    have e5 : t + 2 + q - 1 = t + q + 1 := by omega
    rw [e1, e2, e3, e4, e5]

end UndergradKB.Combinatorics.AeqB.Identities3d
