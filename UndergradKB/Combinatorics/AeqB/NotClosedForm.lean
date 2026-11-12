import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.ComputeDegree
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.ClosedForm
import UndergradKB.Combinatorics.AeqB.AperyNotHyper
import UndergradKB.Combinatorics.AeqB.Database
import UndergradKB.Combinatorics.AeqB.Involutions

/-!
# Sequences that are not of closed form (A = B, Theorem 8.8.1)

Franel numbers, derangement numbers, central trinomial coefficients and involution numbers are not
of closed form.  Method: a closed form annihilated by a recurrence operator is a sum of
hypergeometric solutions of that operator (`closedForm_dissimilar_solutions`), which Algorithm Hyper
(`hyper_candidate_complete`) restricts to a finite candidate list; here every candidate is refuted
(Franel, trinomial, involutions) or shown to have ratio `n + 1` (derangements).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

section
variable {K : Type*} [Field K] [CharZero K]

/-! ### Closed form and recurrences of order two -/

/-- The recurrence operator `p0 + p1 N + p2 N^2`. -/
def nc2Op (p0 p1 p2 : K[X]) : RecOp K :=
  RecOp.term 0 p0 + RecOp.term 1 p1 + RecOp.term 2 p2

lemma nc2Op_act (p0 p1 p2 : K[X]) (y : ℕ → K) (n : ℕ) :
    RecOp.act (nc2Op p0 p1 p2) y n = p0.eval (n : K) * y n + p1.eval (n : K) * y (n + 1)
      + p2.eval (n : K) * y (n + 2) := by
  simp only [nc2Op, RecOp.act_add, Pi.add_apply, RecOp.act_term, add_zero]

theorem nc_closed_parts (p0 p1 p2 : K[X]) (f : ℕ → K) (hf : IsClosedForm f)
    (hL : ∀ n : ℕ, p0.eval (n : K) * f n + p1.eval (n : K) * f (n + 1)
      + p2.eval (n : K) * f (n + 2) = 0) :
    ∃ (r : ℕ) (J : Finset (Fin r)) (u : Fin r → ℕ → K), (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ᶠ n : ℕ in atTop, f n = ∑ j ∈ J, u j n) ∧
      ∀ j ∈ J, ∀ᶠ n : ℕ in atTop, p0.eval (n : K) * u j n + p1.eval (n : K) * u j (n + 1)
        + p2.eval (n : K) * u j (n + 2) = 0 := by
  obtain ⟨r, J, u, h1, -, h3, h4⟩ := closedForm_dissimilar_solutions (nc2Op p0 p1 p2) f hf
    (Eventually.of_forall fun n => by rw [nc2Op_act]; exact hL n)
  exact ⟨r, J, u, h1, h3, fun j hj => (h4 j hj).mono fun n hn => by rwa [nc2Op_act] at hn⟩

theorem nc_notClosedForm_of_no_hyper (p0 p1 p2 : K[X])
    (hno : ∀ y : ℕ → K, IsHypergeometric y → ¬ ∀ᶠ n : ℕ in atTop,
      p0.eval (n : K) * y n + p1.eval (n : K) * y (n + 1) + p2.eval (n : K) * y (n + 2) = 0)
    (f : ℕ → K) (hL : ∀ n : ℕ, p0.eval (n : K) * f n + p1.eval (n : K) * f (n + 1)
      + p2.eval (n : K) * f (n + 2) = 0)
    (hne : ∀ n, f n ≠ 0) : ¬ IsClosedForm f := by
  intro hf
  obtain ⟨r, J, u, h1, h3, h4⟩ := nc_closed_parts p0 p1 p2 f hf hL
  rcases J.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · obtain ⟨n, hn⟩ := h3.exists
    exact hne n (by simpa using hn)
  · exact hno (u j) (h1 j hj) (h4 j hj)

/-! ### Degree and coefficient lemmas -/

lemma nc_top (R c : K[X]) (s : K) (m : ℕ) (hR : R.natDegree ≤ m) :
    (R * c.comp (X + C s)).coeff (m + c.natDegree) = R.coeff m * c.leadingCoeff := by
  have h1 : (c.comp (X + C s)).natDegree = c.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hl : (c.comp (X + C s)).coeff c.natDegree = c.leadingCoeff := by
    have := leadingCoeff_comp (p := c) (q := X + C s) (by rw [natDegree_X_add_C]; exact one_ne_zero)
    rw [leadingCoeff, h1] at this
    rw [this, leadingCoeff_X_add_C, one_pow, mul_one]
  rw [coeff_mul_add_eq_of_natDegree_le hR h1.le, hl]

lemma nc_zero (R c : K[X]) (s : K) (m : ℕ) (hR : R.natDegree < m) :
    (R * c.comp (X + C s)).coeff (m + c.natDegree) = 0 := by
  have hw : (c.comp (X + C s)).natDegree ≤ c.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  apply coeff_eq_zero_of_natDegree_lt
  have := natDegree_mul_le (p := R) (q := c.comp (X + C s))
  omega

lemma nc_dom0 (R0 R1 R2 c : K[X]) (s0 s1 s2 κ : K) (M : K[X]) (hM : M.Monic)
    (hR0 : R0 = C κ * M) (h1 : R1.natDegree < M.natDegree) (h2 : R2.natDegree < M.natDegree)
    (h : R0 * c.comp (X + C s0) + R1 * c.comp (X + C s1) + R2 * c.comp (X + C s2) = 0)
    (hc : c ≠ 0) : κ = 0 := by
  have hl : c.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hc
  have h0 : R0.natDegree ≤ M.natDegree := by rw [hR0]; exact natDegree_C_mul_le _ _
  have hk : R0.coeff M.natDegree = κ := by rw [hR0, coeff_C_mul, hM.coeff_natDegree, mul_one]
  have e := congrArg (fun q => q.coeff (M.natDegree + c.natDegree)) h
  simp only [coeff_add, coeff_zero] at e
  rw [nc_top R0 c s0 _ h0, nc_zero R1 c s1 _ h1, nc_zero R2 c s2 _ h2, hk] at e
  have : κ * c.leadingCoeff = 0 := by simpa using e
  exact (mul_eq_zero.1 this).resolve_right hl

lemma nc_dom2 (R0 R1 R2 c : K[X]) (s0 s1 s2 κ : K) (M : K[X]) (hM : M.Monic)
    (hR2 : R2 = C κ * M) (h0 : R0.natDegree < M.natDegree) (h1 : R1.natDegree < M.natDegree)
    (h : R0 * c.comp (X + C s0) + R1 * c.comp (X + C s1) + R2 * c.comp (X + C s2) = 0)
    (hc : c ≠ 0) : κ = 0 := by
  have hl : c.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hc
  have h2 : R2.natDegree ≤ M.natDegree := by rw [hR2]; exact natDegree_C_mul_le _ _
  have hk : R2.coeff M.natDegree = κ := by rw [hR2, coeff_C_mul, hM.coeff_natDegree, mul_one]
  have e := congrArg (fun q => q.coeff (M.natDegree + c.natDegree)) h
  simp only [coeff_add, coeff_zero] at e
  rw [nc_zero R0 c s0 _ h0, nc_zero R1 c s1 _ h1, nc_top R2 c s2 _ h2, hk] at e
  have : κ * c.leadingCoeff = 0 := by simpa using e
  exact (mul_eq_zero.1 this).resolve_right hl

lemma nc_natDegree_AB (e i j : ℕ) (q : K[X]) (hq : q.natDegree ≤ e) :
    (q * (X + C 1 : K[X]) ^ i * (X + C 2) ^ j).natDegree ≤ e + i + j := by
  have h1 : ((X + C 1 : K[X]) ^ i).natDegree = i := by
    rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have h2 : ((X + C 2 : K[X]) ^ j).natDegree = j := by
    rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have h3 := natDegree_mul_le (p := q) (q := (X + C 1 : K[X]) ^ i)
  have h4 := natDegree_mul_le (p := q * (X + C 1 : K[X]) ^ i) (q := (X + C 2 : K[X]) ^ j)
  omega

lemma nc_R0eq (κ : K) (e j : ℕ) :
    (C 1 * (C κ * (X + C 1) ^ e * ((X + C 1) ^ j * (X + C 2) ^ j)) : K[X])
      = C κ * ((X + C 1) ^ (e + j) * (X + C 2) ^ j) := by
  rw [C_1]; ring

lemma nc_R0deg (κ : K) (e j : ℕ) :
    (C 1 * (C κ * (X + C 1) ^ e * ((X + C 1) ^ j * (X + C 2) ^ j)) : K[X]).natDegree
      ≤ e + j + j := by
  rw [nc_R0eq]
  exact (natDegree_C_mul_le _ _).trans (monic_lin_prod (K := K) (e + j) j).2.le

lemma nc_R2eq (w : K) (e i : ℕ) :
    (C w * ((X + C 2) ^ e * ((X + C 1) ^ i * (X + C 2) ^ i)) : K[X])
      = C w * ((X + C 1) ^ i * (X + C 2) ^ (e + i)) := by
  ring

lemma nc_R2deg (w : K) (e i : ℕ) :
    (C w * ((X + C 2) ^ e * ((X + C 1) ^ i * (X + C 2) ^ i)) : K[X]).natDegree
      ≤ i + (e + i) := by
  rw [nc_R2eq]
  exact (natDegree_C_mul_le _ _).trans (monic_lin_prod (K := K) i (e + i)).2.le

/-! ### Coefficients of products with a shifted polynomial -/

lemma nc_quad_mul_coeff (q0 q1 q2 : K) (w : K[X]) (n : ℕ) :
    ((C q2 * X ^ 2 + C q1 * X + C q0) * w).coeff (n + 2)
      = q2 * w.coeff n + q1 * w.coeff (n + 1) + q0 * w.coeff (n + 2) := by
  rw [add_mul, add_mul]
  simp only [coeff_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul]
  simp

lemma nc_lin_mul_coeff (q0 q1 : K) (w : K[X]) (n : ℕ) :
    ((C q1 * X + C q0) * w).coeff (n + 1) = q1 * w.coeff n + q0 * w.coeff (n + 1) := by
  rw [add_mul]
  simp only [coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul]

lemma nc_quad (u q0 q1 q2 s : K) (c : K[X]) (M : ℕ) (hc : c.natDegree = M + 1) :
    (C u * (C q2 * X ^ 2 + C q1 * X + C q0) * c.comp (X + C s)).coeff (M + 1 + 2)
        = u * q2 * c.coeff (M + 1) ∧
    (C u * (C q2 * X ^ 2 + C q1 * X + C q0) * c.comp (X + C s)).coeff (M + 2)
        = u * (q2 * (c.coeff M + (M + 1) * s * c.coeff (M + 1)) + q1 * c.coeff (M + 1)) := by
  have hw : (c.comp (X + C s)).natDegree ≤ M + 1 := by
    rw [natDegree_comp, natDegree_X_add_C, hc, mul_one]
  have z1 : (c.comp (X + C s)).coeff (M + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z3 : (c.comp (X + C s)).coeff (M + 1 + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z5 : (c.comp (X + C s)).coeff (M + 1 + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  obtain ⟨h1, h2⟩ := shift_coeff c M hc.le s
  rw [mul_assoc, coeff_C_mul, coeff_C_mul]
  constructor
  · rw [nc_quad_mul_coeff, z3, z5, h1]
    ring
  · rw [nc_quad_mul_coeff, z1, h1, h2]
    ring

lemma nc_lin (u q0 q1 s : K) (c : K[X]) (M : ℕ) (hc : c.natDegree = M + 1) :
    (C u * (C q1 * X + C q0) * c.comp (X + C s)).coeff (M + 1 + 1)
        = u * q1 * c.coeff (M + 1) ∧
    (C u * (C q1 * X + C q0) * c.comp (X + C s)).coeff (M + 1)
        = u * (q1 * (c.coeff M + (M + 1) * s * c.coeff (M + 1)) + q0 * c.coeff (M + 1)) := by
  have hw : (c.comp (X + C s)).natDegree ≤ M + 1 := by
    rw [natDegree_comp, natDegree_X_add_C, hc, mul_one]
  have z3 : (c.comp (X + C s)).coeff (M + 1 + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  obtain ⟨h1, h2⟩ := shift_coeff c M hc.le s
  rw [mul_assoc, coeff_C_mul, coeff_C_mul]
  constructor
  · rw [nc_lin_mul_coeff, z3, h1]
    ring
  · rw [nc_lin_mul_coeff, h1, h2]

/-! ### A generic non-hypergeometricity criterion -/

/-- For a second-order recurrence with `p0 = κ (n+1)^e`, `p2 = (n+2)^e` and `deg p1 ≤ e`, every
candidate of Algorithm Hyper has `a = (n+1)^i`, `b = (n+1)^j`; if `i ≠ j` a leading-coefficient
argument kills the candidate, and for `i = j` one is left with the reduced auxiliary equation. -/
theorem nc_hyper2 (e : ℕ) (κ : K) (hκ : κ ≠ 0) (p : ℕ → K[X])
    (hp0 : p 0 = C κ * (X + C 1) ^ e) (hp1 : (p 1).natDegree ≤ e) (hp2 : p 2 = (X + C 2) ^ e)
    (hred : ∀ (z : K) (c : K[X]), z ≠ 0 → c ≠ 0 →
      C 1 * (C κ * (X + C 1) ^ e) * c.comp (X + C 0) + C z * p 1 * c.comp (X + C 1)
        + C (z ^ 2) * (X + C 2) ^ e * c.comp (X + C 2) = 0 → False)
    (y : ℕ → K) (hy : IsHypergeometric y) :
    ¬ ∀ᶠ n : ℕ in atTop, (p 0).eval (n : K) * y n + (p 1).eval (n : K) * y (n + 1)
      + (p 2).eval (n : K) * y (n + 2) = 0 := by
  intro hL
  have hp0' : p 0 ≠ 0 := by
    rw [hp0]; exact mul_ne_zero (C_ne_zero.2 hκ) (pow_ne_zero _ (X_add_C_ne_zero 1))
  have hp2' : p 2 ≠ 0 := by rw [hp2]; exact pow_ne_zero _ (X_add_C_ne_zero 2)
  have hL' : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (2 + 1),
      (p i).eval (n : K) * y (n + i) = 0 := by
    filter_upwards [hL] with n hn
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
    linear_combination hn
  obtain ⟨a, b, z, c, ⟨ha, hadvd, hb, hbdvd, hz, -, hc, hrec⟩, -⟩ :=
    hyper_candidate_complete p 2 (by norm_num) hp0' hp2' y hy hL'
  have hbdvd' : b ∣ (X + C 1 : K[X]) ^ e := by
    refine hbdvd.trans (dvd_of_eq ?_)
    rw [hp2]
    simp only [pow_comp, add_comp, X_comp, C_comp]
    have : (X + C (1 - ((2 : ℕ) : K)) + C 2 : K[X]) = X + C 1 := by
      rw [add_assoc, ← C_add]; congr 2; norm_num
    rw [this]
  have hadvd' : a ∣ (X + C 1 : K[X]) ^ e := by
    rw [hp0] at hadvd
    have : (X + C 1 : K[X]) ^ e = C κ⁻¹ * (C κ * (X + C 1) ^ e) := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hκ, C_1, one_mul]
    rw [this]
    exact hadvd.mul_left _
  obtain ⟨i, rfl⟩ := monic_dvd_pow a ha e hadvd'
  obtain ⟨j, rfl⟩ := monic_dvd_pow b hb e hbdvd'
  rw [aux_expand, shift_pow, shift_pow, one_add_one_eq_two] at hrec
  rw [hp0, hp2] at hrec
  rcases lt_trichotomy i j with hij | hij | hij
  · obtain ⟨m0, n0⟩ := monic_lin_prod (K := K) (e + j) j
    refine hκ (nc_dom0 _ _ _ c _ _ _ κ _ m0 (nc_R0eq κ e j) ?_ ?_ hrec hc)
    · rw [n0]
      exact (natDegree_C_mul_le _ _).trans_lt ((nc_natDegree_AB e i j _ hp1).trans_lt (by omega))
    · rw [n0]
      exact (nc_R2deg _ e i).trans_lt (by omega)
  · subst hij
    apply hred z c hz hc
    have w0 : ((X + C 1 : K[X]) ^ i * (X + C 2) ^ i) ≠ 0 := (monic_lin_prod i i).1.ne_zero
    refine (mul_eq_zero.1 ?_).resolve_left w0
    linear_combination hrec
  · obtain ⟨m2, n2⟩ := monic_lin_prod (K := K) i (e + i)
    have := nc_dom2 _ _ _ c _ _ _ (z ^ 2) _ m2 (nc_R2eq (z ^ 2) e i) ?_ ?_ hrec hc
    · exact hz (pow_eq_zero_iff (two_ne_zero) |>.1 this)
    · rw [n2]
      exact (nc_R0deg κ e j).trans_lt (by omega)
    · rw [n2]
      exact (natDegree_C_mul_le _ _).trans_lt ((nc_natDegree_AB e i j _ hp1).trans_lt (by omega))

/-! ### Franel: the reduced auxiliary equation has no polynomial solution -/

lemma nc_franel_hred (z : K) (c : K[X]) (hz : z ≠ 0) (hc : c ≠ 0)
    (h : C 1 * (C (-8) * (X + C 1) ^ 2) * c.comp (X + C 0)
      + C z * (C (-7) * X ^ 2 + C (-21) * X + C (-16)) * c.comp (X + C 1)
      + C (z ^ 2) * (X + C 2) ^ 2 * c.comp (X + C 2) = 0) : False := by
  rcases Nat.eq_zero_or_pos c.natDegree with hD | hD
  · have hc' : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hD
    have hγ : c.coeff 0 ≠ 0 := by
      intro h0; apply hc; rw [hc', h0, C_0]
    rw [hc'] at h
    simp only [C_comp] at h
    have e1 := congrArg (fun q => q.eval (-1 : K)) h
    have e2 := congrArg (fun q => q.eval (-2 : K)) h
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero] at e1 e2
    have E1 : (c.coeff 0 * z) * (z - 2) = 0 := by linear_combination e1
    have E2 : c.coeff 0 * (z + 4) = 0 := by linear_combination (-1 / 2 : K) * e2
    have F1 := (mul_eq_zero.1 E1).resolve_left (mul_ne_zero hγ hz)
    have F2 := (mul_eq_zero.1 E2).resolve_left hγ
    have : (6 : K) = 0 := by linear_combination F2 - F1
    norm_num at this
  · obtain ⟨M, hM⟩ : ∃ M, c.natDegree = M + 1 := ⟨c.natDegree - 1, by omega⟩
    have hγ : c.coeff (M + 1) ≠ 0 := by
      have := leadingCoeff_ne_zero.2 hc
      rwa [leadingCoeff, hM] at this
    have h' : C 1 * (C (-8) * X ^ 2 + C (-16) * X + C (-8)) * c.comp (X + C 0)
        + C z * (C (-7) * X ^ 2 + C (-21) * X + C (-16)) * c.comp (X + C 1)
        + C (z ^ 2) * (C 1 * X ^ 2 + C 4 * X + C 4) * c.comp (X + C 2) = 0 := by
      simp only [map_one, map_ofNat, map_neg] at h ⊢
      linear_combination h
    have e4 := congrArg (fun q => q.coeff (M + 1 + 2)) h'
    have e3 := congrArg (fun q => q.coeff (M + 2)) h'
    simp only [coeff_add, coeff_zero] at e3 e4
    rw [(nc_quad 1 (-8) (-16) (-8) 0 c M hM).1, (nc_quad z (-16) (-21) (-7) 1 c M hM).1,
      (nc_quad (z ^ 2) 4 4 1 2 c M hM).1] at e4
    rw [(nc_quad 1 (-8) (-16) (-8) 0 c M hM).2, (nc_quad z (-16) (-21) (-7) 1 c M hM).2,
      (nc_quad (z ^ 2) 4 4 1 2 c M hM).2] at e3
    have E3 : z ^ 2 - 7 * z - 8 = 0 := by
      have := mul_eq_zero.1 (show c.coeff (M + 1) * (z ^ 2 - 7 * z - 8) = 0 by
        linear_combination e4)
      exact this.resolve_left hγ
    have E4 : ((M : K) + 2) * (7 * z + 16) = 0 := by
      have := mul_eq_zero.1 (show c.coeff (M + 1) * (((M : K) + 2) * (7 * z + 16)) = 0 by
        linear_combination e3 - (c.coeff M + c.coeff (M + 1) * (2 * M + 6)) * E3)
      exact this.resolve_left hγ
    have hM2 : ((M : K) + 2) ≠ 0 := by
      have := Nat.cast_ne_zero (R := K) |>.2 (show M + 2 ≠ 0 by omega)
      push_cast at this
      exact this
    have E5 := (mul_eq_zero.1 E4).resolve_left hM2
    have : (648 : K) = 0 := by linear_combination 49 * E3 - (7 * z - 65) * E5
    norm_num at this

/-- The coefficients `-8(n+1)^2`, `-(7n^2+21n+16)`, `(n+2)^2` of the Franel recurrence. -/
def ncFranelP : ℕ → K[X]
  | 0 => C (-8) * (X + C 1) ^ 2
  | 1 => C (-7) * X ^ 2 + C (-21) * X + C (-16)
  | _ => (X + C 2) ^ 2

theorem nc_franel_no_hyper (y : ℕ → K) (hy : IsHypergeometric y) :
    ¬ ∀ᶠ n : ℕ in atTop, (ncFranelP 0 : K[X]).eval (n : K) * y n
      + (ncFranelP 1 : K[X]).eval (n : K) * y (n + 1)
      + (ncFranelP 2 : K[X]).eval (n : K) * y (n + 2) = 0 :=
  nc_hyper2 2 (-8) (by norm_num) ncFranelP rfl
    (by show (C (-7) * X ^ 2 + C (-21) * X + C (-16) : K[X]).natDegree ≤ 2; compute_degree)
    rfl (fun z c hz hc h => nc_franel_hred z c hz hc h) y hy

/-! ### Central trinomial: the reduced auxiliary equation -/

lemma nc_tri_hred (z : K) (c : K[X]) (hz : z ≠ 0) (hc : c ≠ 0)
    (h : C 1 * (C (-3) * (X + C 1) ^ 1) * c.comp (X + C 0)
      + C z * (C (-2) * X + C (-3)) * c.comp (X + C 1)
      + C (z ^ 2) * (X + C 2) ^ 1 * c.comp (X + C 2) = 0) : False := by
  rcases Nat.eq_zero_or_pos c.natDegree with hD | hD
  · have hc' : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hD
    have hγ : c.coeff 0 ≠ 0 := by
      intro h0; apply hc; rw [hc', h0, C_0]
    rw [hc'] at h
    simp only [C_comp] at h
    have e1 := congrArg (fun q => q.eval (-1 : K)) h
    have e2 := congrArg (fun q => q.eval (-2 : K)) h
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero] at e1 e2
    have E1 : (c.coeff 0 * z) * (z - 1) = 0 := by linear_combination e1
    have E2 : c.coeff 0 * (z + 3) = 0 := by linear_combination e2
    have F1 := (mul_eq_zero.1 E1).resolve_left (mul_ne_zero hγ hz)
    have F2 := (mul_eq_zero.1 E2).resolve_left hγ
    have : (4 : K) = 0 := by linear_combination F2 - F1
    norm_num at this
  · obtain ⟨M, hM⟩ : ∃ M, c.natDegree = M + 1 := ⟨c.natDegree - 1, by omega⟩
    have hγ : c.coeff (M + 1) ≠ 0 := by
      have := leadingCoeff_ne_zero.2 hc
      rwa [leadingCoeff, hM] at this
    have h' : C 1 * (C (-3) * X + C (-3)) * c.comp (X + C 0)
        + C z * (C (-2) * X + C (-3)) * c.comp (X + C 1)
        + C (z ^ 2) * (C 1 * X + C 2) * c.comp (X + C 2) = 0 := by
      simp only [pow_one, map_one, map_ofNat, map_neg] at h ⊢
      linear_combination h
    have e4 := congrArg (fun q => q.coeff (M + 1 + 1)) h'
    have e3 := congrArg (fun q => q.coeff (M + 1)) h'
    simp only [coeff_add, coeff_zero] at e3 e4
    rw [(nc_lin 1 (-3) (-3) 0 c M hM).1, (nc_lin z (-3) (-2) 1 c M hM).1,
      (nc_lin (z ^ 2) 2 1 2 c M hM).1] at e4
    rw [(nc_lin 1 (-3) (-3) 0 c M hM).2, (nc_lin z (-3) (-2) 1 c M hM).2,
      (nc_lin (z ^ 2) 2 1 2 c M hM).2] at e3
    have E3 : z ^ 2 - 2 * z - 3 = 0 := by
      have := mul_eq_zero.1 (show c.coeff (M + 1) * (z ^ 2 - 2 * z - 3) = 0 by
        linear_combination e4)
      exact this.resolve_left hγ
    have E4 : (2 * (M : K) + 3) * (z + 3) = 0 := by
      have := mul_eq_zero.1 (show c.coeff (M + 1) * ((2 * (M : K) + 3) * (z + 3)) = 0 by
        linear_combination e3 - (c.coeff M + c.coeff (M + 1) * (2 * M + 4)) * E3)
      exact this.resolve_left hγ
    have hM2 : (2 * (M : K) + 3) ≠ 0 := by
      have := Nat.cast_ne_zero (R := K) |>.2 (show 2 * M + 3 ≠ 0 by omega)
      push_cast at this
      exact this
    have E5 := (mul_eq_zero.1 E4).resolve_left hM2
    have : (12 : K) = 0 := by linear_combination E3 - (z - 5) * E5
    norm_num at this

/-- The coefficients `-3(n+1)`, `-(2n+3)`, `n+2` of the central trinomial recurrence. -/
def ncTriP : ℕ → K[X]
  | 0 => C (-3) * (X + C 1) ^ 1
  | 1 => C (-2) * X + C (-3)
  | _ => (X + C 2) ^ 1

theorem nc_tri_no_hyper (y : ℕ → K) (hy : IsHypergeometric y) :
    ¬ ∀ᶠ n : ℕ in atTop, (ncTriP 0 : K[X]).eval (n : K) * y n
      + (ncTriP 1 : K[X]).eval (n : K) * y (n + 1)
      + (ncTriP 2 : K[X]).eval (n : K) * y (n + 2) = 0 :=
  nc_hyper2 1 (-3) (by norm_num) ncTriP rfl
    (by show (C (-2) * X + C (-3) : K[X]).natDegree ≤ 1; compute_degree)
    rfl (fun z c hz hc h => nc_tri_hred z c hz hc h) y hy

/-! ### Derangements: every hypergeometric solution has ratio `n + 1` -/

/-- The coefficients `-(n+1)`, `-(n+1)`, `1` of `D(n+2) = (n+1)(D(n+1) + D(n))`. -/
def ncDerP : ℕ → K[X]
  | 0 => -(X + C 1)
  | 1 => -(X + C 1)
  | _ => 1

theorem nc_derange_hyper (y : ℕ → K) (hy : IsHypergeometric y)
    (hL : ∀ᶠ n : ℕ in atTop, (ncDerP 0 : K[X]).eval (n : K) * y n
      + (ncDerP 1 : K[X]).eval (n : K) * y (n + 1)
      + (ncDerP 2 : K[X]).eval (n : K) * y (n + 2) = 0) :
    ∀ᶠ n : ℕ in atTop, y (n + 1) = ((n : K) + 1) * y n := by
  have hX1 : (X + C 1 : K[X]) ≠ 0 := X_add_C_ne_zero 1
  have f0 : (ncDerP 0 : K[X]) = -(X + C 1) := rfl
  have f1 : (ncDerP 1 : K[X]) = -(X + C 1) := rfl
  have f2 : (ncDerP 2 : K[X]) = 1 := rfl
  have hp0 : (ncDerP 0 : K[X]) ≠ 0 := by rw [f0]; exact neg_ne_zero.2 hX1
  have hp2 : (ncDerP 2 : K[X]) ≠ 0 := by rw [f2]; exact one_ne_zero
  have hL' : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (2 + 1),
      (ncDerP i : K[X]).eval (n : K) * y (n + i) = 0 := by
    filter_upwards [hL] with n hn
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
    linear_combination hn
  obtain ⟨a, b, z, c, ⟨ha, hadvd, hb, hbdvd, hz, -, hc, hrec⟩, hS⟩ :=
    hyper_candidate_complete ncDerP 2 (by norm_num) hp0 hp2 y hy hL'
  have hb1 : b = 1 := by
    rw [f2, one_comp] at hbdvd
    exact hb.eq_one_of_isUnit (isUnit_of_dvd_one hbdvd)
  subst hb1
  have hirr : Irreducible (X + C 1 : K[X]) := irreducible_of_degree_eq_one (degree_X_add_C 1)
  have ha1 : a ∣ X + C 1 := by rw [f0, dvd_neg] at hadvd; exact hadvd
  have hcases : a = 1 ∨ a = X + C 1 := by
    obtain ⟨c', hc'⟩ := ha1
    rcases hirr.isUnit_or_isUnit hc' with hu | hu
    · exact Or.inl (ha.eq_one_of_isUnit hu)
    · right
      refine eq_of_monic_of_associated ha (monic_X_add_C 1) ?_
      exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc'.symm⟩
  have hγ0 : c.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hc
  rw [aux_expand, f0, f1, f2, one_comp] at hrec
  rcases hcases with rfl | rfl
  · -- `a = 1`
    exfalso
    have h' : C 1 * (C (-1) * X + C (-1)) * c.comp (X + C 0)
        + C z * (C (-1) * X + C (-1)) * c.comp (X + C 1)
        + C (z ^ 2) * (C 0 * X + C 1) * c.comp (X + C 2) = 0 := by
      simp only [one_comp, map_one, map_neg, map_zero] at hrec ⊢
      linear_combination hrec
    rcases Nat.eq_zero_or_pos c.natDegree with hD | hD
    · have hc' : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hD
      have hγ : c.coeff 0 ≠ 0 := by
        intro h0; apply hc; rw [hc', h0, C_0]
      rw [hc'] at h'
      simp only [C_comp] at h'
      have e1 := congrArg (fun q => q.eval (-1 : K)) h'
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero] at e1
      exact mul_ne_zero hγ (pow_ne_zero 2 hz) (by linear_combination e1)
    · obtain ⟨M, hM⟩ : ∃ M, c.natDegree = M + 1 := ⟨c.natDegree - 1, by omega⟩
      have hγ : c.coeff (M + 1) ≠ 0 := by
        have := leadingCoeff_ne_zero.2 hc
        rwa [leadingCoeff, hM] at this
      have e4 := congrArg (fun q => q.coeff (M + 1 + 1)) h'
      have e3 := congrArg (fun q => q.coeff (M + 1)) h'
      simp only [coeff_add, coeff_zero] at e3 e4
      rw [(nc_lin 1 (-1) (-1) 0 c M hM).1, (nc_lin z (-1) (-1) 1 c M hM).1,
        (nc_lin (z ^ 2) 1 0 2 c M hM).1] at e4
      rw [(nc_lin 1 (-1) (-1) 0 c M hM).2, (nc_lin z (-1) (-1) 1 c M hM).2,
        (nc_lin (z ^ 2) 1 0 2 c M hM).2] at e3
      have E5 : z + 1 = 0 := by
        have := mul_eq_zero.1 (show c.coeff (M + 1) * (z + 1) = 0 by linear_combination -e4)
        exact this.resolve_left hγ
      have E6 : c.coeff (M + 1) * ((M : K) + 2) = 0 := by
        linear_combination e3 + (c.coeff M - c.coeff (M + 1) * (z - M - 3)) * E5
      have hM2 : ((M : K) + 2) ≠ 0 := by
        have := Nat.cast_ne_zero (R := K) |>.2 (show M + 2 ≠ 0 by omega)
        push_cast at this
        exact this
      exact mul_ne_zero hγ hM2 E6
  · -- `a = X + 1`
    have hc2 : ((X + C 1 : K[X]).comp (X + C 1)) = X + C 2 := by
      rw [add_comp, X_comp, C_comp, add_assoc, ← C_add, one_add_one_eq_two]
    rw [hc2] at hrec
    have hred2 : (X + C 1) * (C 1 * (C 0 * X + C (-1)) * c.comp (X + C 0)
        + C z * (C (-1) * X + C (-1)) * c.comp (X + C 1)
        + C (z ^ 2) * (C 1 * X + C 2) * c.comp (X + C 2)) = 0 := by
      simp only [map_one, map_neg, map_zero, map_ofNat] at hrec ⊢
      linear_combination hrec
    have red := (mul_eq_zero.1 hred2).resolve_left hX1
    have hD : c.natDegree = 0 := by
      by_contra hD0
      obtain ⟨M, hM⟩ : ∃ M, c.natDegree = M + 1 := ⟨c.natDegree - 1, by omega⟩
      have hγ : c.coeff (M + 1) ≠ 0 := by
        have := leadingCoeff_ne_zero.2 hc
        rwa [leadingCoeff, hM] at this
      have h' : C 1 * (C 0 * X + C (-1)) * c.comp (X + C 0)
          + C z * (C (-1) * X + C (-1)) * c.comp (X + C 1)
          + C (z ^ 2) * (C 1 * X + C 2) * c.comp (X + C 2) = 0 := red
      have e4 := congrArg (fun q => q.coeff (M + 1 + 1)) h'
      have e3 := congrArg (fun q => q.coeff (M + 1)) h'
      simp only [coeff_add, coeff_zero] at e3 e4
      rw [(nc_lin 1 (-1) 0 0 c M hM).1, (nc_lin z (-1) (-1) 1 c M hM).1,
        (nc_lin (z ^ 2) 2 1 2 c M hM).1] at e4
      rw [(nc_lin 1 (-1) 0 0 c M hM).2, (nc_lin z (-1) (-1) 1 c M hM).2,
        (nc_lin (z ^ 2) 2 1 2 c M hM).2] at e3
      have E3 : z - 1 = 0 := by
        have := mul_eq_zero.1 (show (c.coeff (M + 1) * z) * (z - 1) = 0 by
          linear_combination e4)
        exact this.resolve_left (mul_ne_zero hγ hz)
      have E6 : c.coeff (M + 1) * ((M : K) + 1) = 0 := by
        linear_combination e3 - (c.coeff M * z + c.coeff (M + 1) * ((2 * M + 4) * z + M + 2)) * E3
      have hM2 : ((M : K) + 1) ≠ 0 := by
        have := Nat.cast_ne_zero (R := K) |>.2 (show M + 1 ≠ 0 by omega)
        push_cast at this
        exact this
      exact mul_ne_zero hγ hM2 E6
    have hc' : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hD
    have hγ : c.coeff 0 ≠ 0 := by
      intro h0; apply hc; rw [hc', h0, C_0]
    have hce : ∀ x : K, c.eval x = c.coeff 0 := fun x => by
      conv_lhs => rw [hc']
      exact eval_C
    have hz1 : z = 1 := by
      have h' : C 1 * (C 0 * X + C (-1)) * c.comp (X + C 0)
          + C z * (C (-1) * X + C (-1)) * c.comp (X + C 1)
          + C (z ^ 2) * (C 1 * X + C 2) * c.comp (X + C 2) = 0 := red
      rw [hc'] at h'
      simp only [C_comp] at h'
      have e2 := congrArg (fun q => q.eval (-2 : K)) h'
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_zero] at e2
      have : c.coeff 0 * (z - 1) = 0 := by linear_combination e2
      have := (mul_eq_zero.1 this).resolve_left hγ
      linear_combination this
    filter_upwards [hS] with n hn
    rw [hn, hyperRatio, hz1, hce, hce]
    simp [hγ]

end

/-! ### The headline theorems -/

section Headlines

/-- `franel n ≥ 1`. -/
lemma nc_franel_pos (n : ℕ) : (0 : ℚ) < franel n :=
  Finset.sum_pos (fun k hk => pow_pos (Nat.cast_pos.2 (Nat.choose_pos
    (by simpa [Nat.lt_succ_iff] using hk))) 3) ⟨0, by simp⟩

/-- CO-502. The Franel numbers `∑_k C(n,k)^3` are not of closed form: they are not, for large `n`,
a linear combination of a fixed number of hypergeometric terms (over any field of characteristic
zero).  Proof: they satisfy the Franel recurrence (`franel_recurrence`), which by Algorithm Hyper
has no hypergeometric solution (candidates `a = (n+1)^i`, `b = (n+1)^j`; the leading coefficients
decide `i ≠ j`, and `i = j` leaves an auxiliary equation without polynomial solutions), so the
decomposition of a closed form into dissimilar hypergeometric solutions of the recurrence
(`closedForm_dissimilar_solutions`) would be empty, contradicting `f(n) > 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.8.1, p. 160"]
theorem franel_not_closedForm (K : Type*) [Field K] [CharZero K] :
    ¬ IsClosedForm (fun n : ℕ => (franel n : K)) := by
  refine nc_notClosedForm_of_no_hyper (ncFranelP 0) (ncFranelP 1) (ncFranelP 2)
    nc_franel_no_hyper _ (fun n => ?_) (fun n => ?_)
  · have h' := congrArg (Rat.cast : ℚ → K) (franel_recurrence n)
    push_cast at h'
    simp only [ncFranelP, eval_mul, eval_C, eval_add, eval_pow, eval_X]
    linear_combination (-1 : K) * h'
  · exact Rat.cast_ne_zero.2 (nc_franel_pos n).ne'

/-! #### Central trinomial coefficients -/

/-- The central trinomial coefficient: the coefficient of `x^n` in `(1 + x + x^2)^n`, written as
`∑_k C(n,k) C(n-k,k)` (choose `k` factors contributing `x^2` and `k` contributing `1`). -/
def centralTrinomial (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (n - k).choose k

/-- The summand `C(n,2k) C(2k,k)` in `ℚ`. -/
def nctF (n k : ℕ) : ℚ := (n.choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ)

lemma nctF_zero_of_lt (n k : ℕ) (h : n < 2 * k) : nctF n k = 0 := by
  simp [nctF, Nat.choose_eq_zero_of_lt h]

lemma nct_alg (j t A B Cc Mj M' : ℚ) (hM : (j + 1) * M' = 2 * (2 * j + 1) * Mj)
    (hB : B * (2 * j + 1) = A * t) (hj : (j + 1) * (2 * j + 1) ≠ 0) :
    (2 * j + t + 2) * ((A + 2 * B + Cc) * M') - (2 * (2 * j + t) + 3) * ((B + Cc) * M')
      + (2 * j + t + 1) * (Cc * M') = 4 * (2 * j + t + 1) * (A * Mj) := by
  have : ((j + 1) * (2 * j + 1)) * (((2 * j + t + 2) * ((A + 2 * B + Cc) * M')
      - (2 * (2 * j + t) + 3) * ((B + Cc) * M') + (2 * j + t + 1) * (Cc * M'))
      - 4 * (2 * j + t + 1) * (A * Mj)) = 0 := by
    linear_combination ((2 * j + 1) * ((2 * j + t + 2) * A + B)) * hM
      + (2 * (2 * j + 1) * Mj) * hB
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hj)

lemma nct_step (n j : ℕ) :
    ((n : ℚ) + 2) * nctF (n + 2) (j + 1) - (2 * n + 3) * nctF (n + 1) (j + 1)
      + (n + 1) * nctF n (j + 1) = 4 * (n + 1) * nctF n j := by
  rcases lt_or_ge n (2 * j) with h | h
  · have z1 : n.choose (2 * (j + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have z2 : (n + 1).choose (2 * (j + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have z3 : (n + 2).choose (2 * (j + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have z4 : n.choose (2 * j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [nctF, z1, z2, z3, z4]
  · obtain ⟨t, rfl⟩ : ∃ t, n = 2 * j + t := ⟨n - 2 * j, by omega⟩
    have e2 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    have q1 : (2 * j + t + 1).choose (2 * j + 1 + 1)
        = (2 * j + t).choose (2 * j + 1) + (2 * j + t).choose (2 * j + 1 + 1) :=
      Nat.choose_succ_succ _ _
    have q0 : (2 * j + t + 1).choose (2 * j + 1)
        = (2 * j + t).choose (2 * j) + (2 * j + t).choose (2 * j + 1) :=
      Nat.choose_succ_succ _ _
    have q2 : (2 * j + t + 2).choose (2 * j + 1 + 1)
        = (2 * j + t + 1).choose (2 * j + 1) + (2 * j + t + 1).choose (2 * j + 1 + 1) :=
      Nat.choose_succ_succ _ _
    have hR := Nat.choose_succ_right_eq (2 * j + t) (2 * j)
    rw [Nat.add_sub_cancel_left] at hR
    have hM0 := Nat.succ_mul_centralBinom_succ j
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose, e2] at hM0
    have hM : ((j : ℚ) + 1) * ((2 * j + 1 + 1).choose (j + 1) : ℚ)
        = 2 * (2 * j + 1) * ((2 * j).choose j : ℚ) := by exact_mod_cast hM0
    have hB : (((2 * j + t).choose (2 * j + 1) : ℕ) : ℚ) * (2 * j + 1)
        = (((2 * j + t).choose (2 * j) : ℕ) : ℚ) * t := by exact_mod_cast hR
    have hj : ((j : ℚ) + 1) * (2 * j + 1) ≠ 0 := by positivity
    have key := nct_alg j t _ _ ((2 * j + t).choose (2 * j + 1 + 1) : ℚ) _ _ hM hB hj
    simp only [nctF, e2]
    rw [q2, q1, q0]
    push_cast
    linear_combination key

/-- `∑_k C(n,2k) C(2k,k)` over `ℚ`. -/
def nctT (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), nctF n k

lemma nctT_ext (m M : ℕ) (h : m + 1 ≤ M) : ∑ k ∈ Finset.range M, nctF m k = nctT m := by
  unfold nctT
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro k hk hk'
  simp only [Finset.mem_range] at hk hk'
  exact nctF_zero_of_lt _ _ (by omega)

lemma nctT_rec (n : ℕ) :
    ((n : ℚ) + 2) * nctT (n + 2) - (2 * n + 3) * nctT (n + 1) - 3 * (n + 1) * nctT n = 0 := by
  have key : ∑ k ∈ Finset.range (n + 3), (((n : ℚ) + 2) * nctF (n + 2) k
      - (2 * n + 3) * nctF (n + 1) k + (n + 1) * nctF n k)
      = 4 * (n + 1) * ∑ j ∈ Finset.range (n + 2), nctF n j := by
    rw [Finset.sum_range_succ' _ (n + 2)]
    have h : ∀ j ∈ Finset.range (n + 2), (((n : ℚ) + 2) * nctF (n + 2) (j + 1)
        - (2 * n + 3) * nctF (n + 1) (j + 1) + (n + 1) * nctF n (j + 1))
        = 4 * (n + 1) * nctF n j := fun j _ => nct_step n j
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
    have h0 : (((n : ℚ) + 2) * nctF (n + 2) 0 - (2 * n + 3) * nctF (n + 1) 0
        + (n + 1) * nctF n 0) = 0 := by
      simp only [nctF, mul_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      ring
    rw [h0, add_zero]
  have e1 : ∑ k ∈ Finset.range (n + 3), (((n : ℚ) + 2) * nctF (n + 2) k
      - (2 * n + 3) * nctF (n + 1) k + (n + 1) * nctF n k)
      = ((n : ℚ) + 2) * nctT (n + 2) - (2 * n + 3) * nctT (n + 1) + (n + 1) * nctT n := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, nctT_ext (n + 2) (n + 3) (by omega), nctT_ext (n + 1) (n + 3) (by omega),
      nctT_ext n (n + 3) (by omega)]
  rw [e1, nctT_ext n (n + 2) (by omega)] at key
  linear_combination key

lemma centralTrinomial_eq (n : ℕ) : (centralTrinomial n : ℚ) = nctT n := by
  unfold centralTrinomial nctT
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  have := Nat.choose_mul (n := n) (k := 2 * k) (s := k) (by omega)
  rw [show 2 * k - k = k by omega] at this
  unfold nctF
  exact_mod_cast this.symm

lemma centralTrinomial_pos (n : ℕ) : 0 < centralTrinomial n :=
  Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩

/-- CO-502. The central trinomial coefficients `T(n)` (coefficient of `x^n` in `(1+x+x^2)^n`,
here `∑_k C(n,k) C(n-k,k)`) are not of closed form.  They satisfy
`(n+2) T(n+2) = (2n+3) T(n+1) + 3(n+1) T(n)` (proved here by a telescoping certificate, which is
just a shift of the summation index), and this recurrence has no hypergeometric solution. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.8.1, p. 160"]
theorem centralTrinomial_not_closedForm (K : Type*) [Field K] [CharZero K] :
    ¬ IsClosedForm (fun n : ℕ => (centralTrinomial n : K)) := by
  refine nc_notClosedForm_of_no_hyper (ncTriP 0) (ncTriP 1) (ncTriP 2)
    nc_tri_no_hyper _ (fun n => ?_) (fun n => ?_)
  · have h := nctT_rec n
    rw [← centralTrinomial_eq, ← centralTrinomial_eq, ← centralTrinomial_eq] at h
    have h' := congrArg (Rat.cast : ℚ → K) h
    push_cast at h'
    simp only [ncTriP, eval_mul, eval_C, eval_add, eval_X, pow_one]
    linear_combination h'
  · exact Nat.cast_ne_zero.2 (centralTrinomial_pos n).ne'

/-! #### Involution numbers -/

lemma nc_involution_pos (n : ℕ) : 0 < Involutions.involutionNumber n :=
  Finset.card_pos.2 ⟨1, Involutions.mem_invs.2 (mul_one 1)⟩

/-- CO-502. The involution numbers (permutations `σ` of an `n`-set with `σ² = 1`) are not of closed
form: they satisfy `t(n+2) = t(n+1) + (n+1) t(n)`, which has no hypergeometric solution
(`not_hypergeometric_involution_rec`). -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.8.1, p. 160"]
theorem involutions_not_closedForm (K : Type*) [Field K] [CharZero K] :
    ¬ IsClosedForm (fun n : ℕ => (Involutions.involutionNumber n : K)) := by
  refine nc_notClosedForm_of_no_hyper (-(X + C 1)) (-1) 1 ?_ _ (fun n => ?_) (fun n => ?_)
  · intro y hy hL
    refine not_hypergeometric_involution_rec y hy (hL.mono fun n hn => ?_)
    simp only [eval_neg, eval_add, eval_X, eval_C, eval_one] at hn
    linear_combination hn
  · have h : ((Involutions.involutionNumber (n + 2) : ℕ) : K)
        = (Involutions.involutionNumber (n + 1) : ℕ) + ((n : K) + 1) *
          (Involutions.involutionNumber n : ℕ) := by
      exact_mod_cast Involutions.involutionNumber_rec n
    simp only [eval_neg, eval_add, eval_X, eval_C, eval_one]
    linear_combination h
  · exact Nat.cast_ne_zero.2 (nc_involution_pos n).ne'

/-! #### Derangement numbers -/

/-- CO-502. The derangement numbers `D(n)` (`numDerangements`) are not of closed form.  The
recurrence `D(n+2) = (n+1)(D(n+1) + D(n))` does have the hypergeometric solution `n!`, but by
Algorithm Hyper every hypergeometric solution has ratio `n + 1` eventually; hence a closed form
would satisfy `D(n+1) = (n+1) D(n)` for large `n`, contradicting
`D(n+1) = (n+1) D(n) - (-1)^n`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.8.1, p. 160"]
theorem derangements_not_closedForm (K : Type*) [Field K] [CharZero K] :
    ¬ IsClosedForm (fun n : ℕ => (numDerangements n : K)) := by
  intro hf
  have hL : ∀ n : ℕ, (ncDerP 0 : K[X]).eval (n : K) * (numDerangements n : K)
      + (ncDerP 1 : K[X]).eval (n : K) * (numDerangements (n + 1) : K)
      + (ncDerP 2 : K[X]).eval (n : K) * (numDerangements (n + 2) : K) = 0 := by
    intro n
    have h : ((numDerangements (n + 2) : ℕ) : K)
        = ((n : K) + 1) * ((numDerangements n : ℕ) + (numDerangements (n + 1) : ℕ)) := by
      exact_mod_cast numDerangements_add_two n
    show (-(X + C 1) : K[X]).eval (n : K) * _ + (-(X + C 1) : K[X]).eval (n : K) * _
      + (1 : K[X]).eval (n : K) * _ = 0
    simp only [eval_neg, eval_add, eval_X, eval_C, eval_one]
    linear_combination h
  obtain ⟨r, J, u, h1, h3, h4⟩ := nc_closed_parts (ncDerP 0) (ncDerP 1) (ncDerP 2) _ hf hL
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ J, u j (n + 1) = ((n : K) + 1) * u j n :=
    (Filter.eventually_all_finset J).2 fun j hj => nc_derange_hyper (u j) (h1 j hj) (h4 j hj)
  have h3' : ∀ᶠ n : ℕ in atTop, (numDerangements (n + 1) : K) = ∑ j ∈ J, u j (n + 1) :=
    (tendsto_add_atTop_nat 1).eventually h3
  obtain ⟨n, hn1, hn2, hn3⟩ := (hall.and (h3.and h3')).exists
  have hrec : ((numDerangements (n + 1) : ℤ) : K)
      = ((n : K) + 1) * ((numDerangements n : ℤ) : K) - (-1) ^ n := by
    have := congrArg (Int.cast : ℤ → K) (numDerangements_succ n)
    push_cast at this ⊢
    exact this
  have hsum : (numDerangements (n + 1) : K) = ((n : K) + 1) * (numDerangements n : K) := by
    rw [hn3, hn2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => hn1 j hj
  push_cast at hrec
  have : ((-1 : K)) ^ n = 0 := by linear_combination hrec - hsum
  exact pow_ne_zero n (neg_ne_zero.2 one_ne_zero) this

end Headlines

end UndergradKB.Combinatorics.AeqB

end
