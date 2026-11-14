import Mathlib.NumberTheory.Dioph
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import UndergradKB.Common

/-!
# Foundations, DPRM: binomial coefficients and factorials are Diophantine

Arithmetic ingredients of Davis's bounded universal quantifier theorem (Davis 1973, Section 3):

* `digit_extract`: reading the `k`-th digit of a number written in base `w`;
* `choose_dioph`: `C(n, k)` is the `k`-th base-`w` digit of `(w + 1) ^ n` for `w = 2 ^ n + 1`;
* `factorial_dioph`: `n! = ⌊r ^ n / C(r, n)⌋` for `r` large;
* `descFactorial_dioph`: the falling factorial `a (a - 1) ⋯ (a - n + 1) = n! C(a, n)`;
* `prod_succ_mul_dioph`: the product `∏_{k < y} (1 + (k + 1) t)`, which is congruent to
  `t ^ y y! C(q + y, y)` modulo a large `M` for a suitable inverse `q` of `t`.
-/

namespace UndergradKB.Foundations.DPRM

open Dioph Finset Nat

variable {α : Type} {f g : (α → ℕ) → ℕ}

theorem sum_split (w m : ℕ) (c : ℕ → ℕ) :
    ∑ i ∈ range (m + 1), c i * w ^ i = c 0 + w * ∑ i ∈ range m, c (i + 1) * w ^ i := by
  rw [Finset.sum_range_succ', add_comm, Finset.mul_sum]
  simp only [pow_zero, mul_one]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Base-`w` digit extraction: if all digits `c i` are below `w`, the `k`-th digit of
`∑_{i < L} c i w ^ i` is `c k` (and `0` beyond the length). -/
theorem digit_extract (w L k : ℕ) (c : ℕ → ℕ) (hc : ∀ i, c i < w) :
    ((∑ i ∈ range L, c i * w ^ i) / w ^ k) % w = if k < L then c k else 0 := by
  have hw : 0 < w := lt_of_le_of_lt (Nat.zero_le _) (hc 0)
  induction k generalizing L c with
  | zero =>
    cases L with
    | zero => simp
    | succ m =>
      rw [sum_split]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (hc 0)]
  | succ k ih =>
    cases L with
    | zero => simp
    | succ m =>
      rw [sum_split, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt (hc 0), Nat.zero_add,
        ih m (fun i => c (i + 1)) (fun i => hc _)]
      simp

theorem choose_eq_digit (n k : ℕ) :
    n.choose k = ((2 ^ n + 2) ^ n / (2 ^ n + 1) ^ k) % (2 ^ n + 1) := by
  have h1 : (2 ^ n + 2) ^ n = ∑ i ∈ range (n + 1), n.choose i * (2 ^ n + 1) ^ i := by
    have : 2 ^ n + 2 = (2 ^ n + 1) + 1 := by ring
    rw [this, add_pow]
    refine sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [h1, digit_extract (2 ^ n + 1) (n + 1) k (fun i => n.choose i)
    (fun i => Nat.lt_succ_of_le (Nat.choose_le_two_pow n i))]
  split_ifs with h
  · rfl
  · exact Nat.choose_eq_zero_of_lt (show n < k by omega)

theorem choose_dioph (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have h : (fun v => (f v).choose (g v)) = fun v =>
      ((2 ^ (f v) + 2) ^ (f v) / (2 ^ (f v) + 1) ^ (g v)) % (2 ^ (f v) + 1) :=
    funext fun v => choose_eq_digit _ _
  have hp : DiophFn fun v => 2 ^ f v := pow_dioph (const_dioph 2) df
  have h1 : DiophFn fun v => 2 ^ f v + 1 := add_dioph hp (const_dioph 1)
  have h2 : DiophFn fun v => 2 ^ f v + 2 := add_dioph hp (const_dioph 2)
  have h3 : DiophFn fun v => (2 ^ f v + 2) ^ f v := pow_dioph h2 df
  have h4 : DiophFn fun v => (2 ^ f v + 1) ^ g v := pow_dioph h1 dg
  rw [h]
  exact mod_dioph (div_dioph h3 h4) h1

theorem desc_aux (r : ℕ) : ∀ x, x ≤ r →
    r ^ (x + 1) ≤ r * r.descFactorial x + x ^ 2 * r ^ x := by
  intro x
  induction x with
  | zero => intro _; simp
  | succ x ih =>
    intro hx
    have ih := ih (by omega)
    obtain ⟨s, hs⟩ : ∃ s, r = s + x := ⟨r - x, by omega⟩
    have hd : r.descFactorial x ≤ r ^ x := Nat.descFactorial_le_pow r x
    have e1 : r ^ (x + 1 + 1) = r ^ x * r * r := by ring
    have e2 : r ^ (x + 1) = r ^ x * r := by ring
    have e3 : r.descFactorial (x + 1) = s * r.descFactorial x := by
      rw [Nat.descFactorial_succ]; congr 1; omega
    rw [e1, e2, e3]
    rw [e2] at ih
    generalize r.descFactorial x = d at *
    generalize r ^ x = p at *
    subst hs
    have h1 := Nat.mul_le_mul_left (s + x) ih
    have h2 : (s + x) * x * d ≤ (s + x) * x * p := Nat.mul_le_mul_left _ hd
    nlinarith [h1, h2, Nat.zero_le ((s + x) * p), Nat.zero_le (x * ((s + x) * p))]

theorem factorial_eq_div (n : ℕ) :
    n ! = ((n + 2) ^ (n + 3)) ^ n / ((n + 2) ^ (n + 3)).choose n := by
  set r := (n + 2) ^ (n + 3) with hr
  have hnr : n ≤ r := by
    have : n + 2 ≤ r := by
      rw [hr]
      calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hrpos : 0 < r := by rw [hr]; positivity
  have hdesc : r.descFactorial n = n ! * r.choose n :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hCpos : 0 < r.choose n := Nat.choose_pos hnr
  have hfpos : 0 < n ! := Nat.factorial_pos n
  have hlow : n ! * r.choose n ≤ r ^ n := hdesc ▸ Nat.descFactorial_le_pow r n
  have hbig : (n ! + 1) * n ^ 2 < r := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simpa using hrpos
    · have a1 : n ! ≤ n ^ n := Nat.factorial_le_pow n
      have a2 : n ^ n < (n + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
      have a3 : (n + 1) ^ n ≤ (n + 2) ^ n := Nat.pow_le_pow_left (by omega) n
      have a4 : n ^ 2 < (n + 2) ^ 2 := Nat.pow_lt_pow_left (by omega) (by omega)
      have a5 : (n ! + 1) ≤ (n + 2) ^ n := by omega
      have a6 : (n + 2) ^ (n + 2) ≤ r := Nat.pow_le_pow_right (by omega) (by omega)
      calc (n ! + 1) * n ^ 2 < (n + 2) ^ n * (n + 2) ^ 2 :=
            Nat.mul_lt_mul_of_le_of_lt a5 a4 (by positivity)
        _ = (n + 2) ^ (n + 2) := by ring
        _ ≤ r := a6
  have haux := desc_aux r n hnr
  have hup : r ^ n < (n ! + 1) * r.choose n := by
    by_contra hcon
    push Not at hcon
    have hPpos : 0 < r ^ n := by positivity
    obtain ⟨D, hD⟩ : ∃ D, r ^ n = n ! * r.choose n + D :=
      ⟨r ^ n - n ! * r.choose n, by omega⟩
    have hDC : r.choose n ≤ D := by nlinarith
    rw [hdesc] at haux
    have hr1 : r ^ (n + 1) = r * r ^ n := by ring
    rw [hr1, hD] at haux
    have hDpos : 0 < D := by omega
    have hrD : r * D ≤ n ^ 2 * (n ! * r.choose n + D) := by nlinarith
    have hfD : n ! * r.choose n ≤ n ! * D := Nat.mul_le_mul_left _ hDC
    have h5 : r * D ≤ ((n ! + 1) * n ^ 2) * D := by nlinarith
    have := Nat.le_of_mul_le_mul_right h5 hDpos
    omega
  symm
  exact Nat.div_eq_of_lt_le hlow (by simpa [Nat.add_mul] using hup)

theorem factorial_dioph (df : DiophFn f) : DiophFn fun v => (f v) ! := by
  have h : (fun v => (f v) !) = fun v =>
      ((f v + 2) ^ (f v + 3)) ^ f v / ((f v + 2) ^ (f v + 3)).choose (f v) :=
    funext fun v => factorial_eq_div _
  have hr : DiophFn fun v => (f v + 2) ^ (f v + 3) :=
    pow_dioph (add_dioph df (const_dioph 2)) (add_dioph df (const_dioph 3))
  rw [h]
  exact div_dioph (pow_dioph hr df) (choose_dioph hr df)

theorem descFactorial_dioph (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).descFactorial (g v) := by
  have h : (fun v => (f v).descFactorial (g v)) = fun v => (g v) ! * (f v).choose (g v) :=
    funext fun v => Nat.descFactorial_eq_factorial_mul_choose _ _
  rw [h]
  exact mul_dioph (factorial_dioph dg) (choose_dioph df dg)

theorem prod_succ_mul_eq (y t : ℕ) (ht : 0 < t) :
    ∏ k ∈ range y, (1 + (k + 1) * t) =
      (t ^ y * y ! * (1 + (t - 1) * (1 + y * t) ^ y + y).choose y) % (1 + t * (1 + y * t) ^ y) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set B := (1 + y * (u + 1)) ^ y with hB
  set M := 1 + (u + 1) * B with hM
  set q := 1 + u * B with hq
  have hBpos : 0 < B := by positivity
  have htq : (u + 1) * q = 1 + u * M := by rw [hq, hM]; ring
  have hmod : ∀ k, 1 + (k + 1) * (u + 1) ≡ (u + 1) * (q + k + 1) [MOD M] := by
    intro k
    have : (u + 1) * (q + k + 1) = (u + 1) * q + (k + 1) * (u + 1) := by ring
    rw [this, htq]
    have h2 : 1 + u * M ≡ 1 [MOD M] := by
      unfold Nat.ModEq
      rw [Nat.add_mul_mod_self_right]
    calc 1 + (k + 1) * (u + 1) = (k + 1) * (u + 1) + 1 := by ring
      _ ≡ (k + 1) * (u + 1) + (1 + u * M) [MOD M] := Nat.ModEq.add_left _ h2.symm
      _ = 1 + u * M + (k + 1) * (u + 1) := by ring
  have hprod : ∏ k ∈ range y, (1 + (k + 1) * (u + 1)) ≡
      ∏ k ∈ range y, ((u + 1) * (q + k + 1)) [MOD M] := by
    unfold Nat.ModEq
    rw [Finset.prod_nat_mod, Finset.prod_nat_mod (range y) M (fun k => (u + 1) * (q + k + 1))]
    exact congrArg (· % M) (prod_congr rfl fun k _ => hmod k)
  have hasc : ∏ k ∈ range y, ((u + 1) * (q + k + 1)) =
      (u + 1) ^ y * (y ! * (q + y).choose y) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    rw [← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]
    exact prod_congr rfl fun k _ => by ring
  have hlt : ∏ k ∈ range y, (1 + (k + 1) * (u + 1)) < M := by
    have : ∏ k ∈ range y, (1 + (k + 1) * (u + 1)) ≤ (1 + y * (u + 1)) ^ y := by
      calc _ ≤ (1 + y * (u + 1)) ^ (range y).card :=
            Finset.prod_le_pow_card _ _ _ (fun k hk => by
              have := Finset.mem_range.1 hk
              nlinarith)
        _ = _ := by rw [Finset.card_range]
    rw [hM]; nlinarith
  have h3 := hprod
  rw [hasc] at h3
  unfold Nat.ModEq at h3
  rw [Nat.mod_eq_of_lt hlt] at h3
  rw [h3]
  exact congrArg (· % M) (by ring)

theorem prod_succ_mul_dioph (df : DiophFn f) (dg : DiophFn g) (hg : ∀ v, 0 < g v) :
    DiophFn fun v => ∏ k ∈ range (f v), (1 + (k + 1) * g v) := by
  have h : (fun v => ∏ k ∈ range (f v), (1 + (k + 1) * g v)) = fun v =>
      (g v ^ f v * (f v) ! * (1 + (g v - 1) * (1 + f v * g v) ^ f v + f v).choose (f v)) %
        (1 + g v * (1 + f v * g v) ^ f v) :=
    funext fun v => prod_succ_mul_eq (f v) (g v) (hg v)
  have hB : DiophFn fun v => (1 + f v * g v) ^ f v :=
    pow_dioph (add_dioph (const_dioph 1) (mul_dioph df dg)) df
  have hM : DiophFn fun v => 1 + g v * (1 + f v * g v) ^ f v :=
    add_dioph (const_dioph 1) (mul_dioph dg hB)
  have hq : DiophFn fun v => 1 + (g v - 1) * (1 + f v * g v) ^ f v :=
    add_dioph (const_dioph 1) (mul_dioph (sub_dioph dg (const_dioph 1)) hB)
  have hc : DiophFn fun v => (1 + (g v - 1) * (1 + f v * g v) ^ f v + f v).choose (f v) :=
    choose_dioph (add_dioph hq df) df
  rw [h]
  exact mod_dioph (mul_dioph (mul_dioph (pow_dioph dg df) (factorial_dioph df)) hc) hM

end UndergradKB.Foundations.DPRM
