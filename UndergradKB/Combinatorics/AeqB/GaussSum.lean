import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.MonotoneConvergence
import UndergradKB.Combinatorics.AeqB.HypergeometricSeries
import UndergradKB.Common.Attr

/-!
# Gauss's summation of `2F1(a, b; c; 1)` for `c - a - b > 0`

The non-terminating Gauss sum, for real parameters, via the contiguous relation
`c (c-a-b) F(c) = (c-a)(c-b) F(c+1)` (proved by telescoping), the limit `F(c+m) -> 1`
(dominated convergence) and Euler's limit formula for `Gamma`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Finset Filter Topology

/-- Term sequence of `2F1(a, b; c; 1)` defined by its term ratio. -/
noncomputable def gaussTerm (a b c : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => gaussTerm a b c k * (((k : ℝ) + a) * ((k : ℝ) + b) / (((k : ℝ) + c) * ((k : ℝ) + 1)))

theorem gaussTerm_succ (a b c : ℝ) (k : ℕ) :
    gaussTerm a b c (k + 1) =
      gaussTerm a b c k * (((k : ℝ) + a) * ((k : ℝ) + b) / (((k : ℝ) + c) * ((k : ℝ) + 1))) := rfl

/-- The term sequence agrees with `pFqTerm` of the book. -/
theorem gaussTerm_eq_pFqTerm (a b c : ℝ) (hc : ∀ k : ℕ, c + k ≠ 0) (k : ℕ) :
    gaussTerm a b c k = pFqTerm ![a, b] ![c] (1 : ℝ) k := by
  have hb : LowerOK ![c] := fun j n h => by
    fin_cases j
    exact hc n (by simp at h; linarith)
  induction k with
  | zero => simp [gaussTerm, pFqTerm_zero]
  | succ k ih =>
    have h := pFqTerm_succ_mul ![a, b] hb (1 : ℝ) k
    simp only [Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one] at h
    have h1 : ((k : ℝ) + c) * ((k : ℝ) + 1) ≠ 0 :=
      mul_ne_zero (by simpa [add_comm] using hc k) (by positivity)
    rw [gaussTerm_succ, ih]
    rw [eq_comm, ← mul_div_assoc, eq_div_iff h1]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem gaussTerm_shift (a b c : ℝ) (hc : ∀ k : ℕ, c + k ≠ 0) (k : ℕ) :
    gaussTerm a b (c + 1) k * (c + k) = gaussTerm a b c k * c := by
  induction k with
  | zero => simp [gaussTerm]
  | succ k ih =>
    have h1 : c + (k : ℝ) ≠ 0 := hc k
    have h2 : (k : ℝ) + c ≠ 0 := by rwa [add_comm]
    have h3 : (k : ℝ) + (c + 1) ≠ 0 := by
      have := hc (k + 1); push_cast at this; intro h; apply this; linarith
    have h4 : c + ((k : ℝ) + 1) ≠ 0 := by
      have := hc (k + 1); push_cast at this; intro h; apply this; linarith
    have ih' : gaussTerm a b (c + 1) k = gaussTerm a b c k * c / (c + k) := by
      rw [eq_div_iff h1]; exact ih
    rw [gaussTerm_succ, gaussTerm_succ, ih']
    push_cast
    field_simp
    ring

/-- Telescoping identity behind the contiguous relation. -/
theorem gauss_telescope (a b c : ℝ) (hc : ∀ k : ℕ, c + k ≠ 0) (N : ℕ) :
    c * (c - a - b) * ∑ k ∈ range N, gaussTerm a b c k
      - (c - a) * (c - b) * ∑ k ∈ range N, gaussTerm a b (c + 1) k
      = - c * N * gaussTerm a b c N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : c + (N : ℝ) ≠ 0 := hc N
    have h2 : (N : ℝ) + c ≠ 0 := by rwa [add_comm]
    have ih' : gaussTerm a b (c + 1) N = gaussTerm a b c N * c / (c + N) := by
      rw [eq_div_iff h1]; exact gaussTerm_shift a b c hc N
    rw [sum_range_succ, sum_range_succ, gaussTerm_succ, ih']
    have : c * (c - a - b) * (∑ k ∈ range N, gaussTerm a b c k + gaussTerm a b c N)
        - (c - a) * (c - b) * (∑ k ∈ range N, gaussTerm a b (c + 1) k
          + gaussTerm a b c N * c / (c + N))
        = (c * (c - a - b) * ∑ k ∈ range N, gaussTerm a b c k
          - (c - a) * (c - b) * ∑ k ∈ range N, gaussTerm a b (c + 1) k)
          + (c * (c - a - b) * gaussTerm a b c N
            - (c - a) * (c - b) * (gaussTerm a b c N * c / (c + N))) := by ring
    rw [this, ih]
    push_cast
    field_simp
    ring

/-- A nonnegative sequence with `(k+1+K) e_{k+1} + σ e_k ≤ (k+K) e_k` is summable and
`(k+K) e_k -> 0`. -/
theorem summable_tendsto_of_dec (e : ℕ → ℝ) (K : ℕ) (σ : ℝ) (hσ : 0 < σ) (he : ∀ k, 0 ≤ e k)
    (h : ∀ k : ℕ, ((k : ℝ) + 1 + K) * e (k + 1) + σ * e k ≤ ((k : ℝ) + K) * e k) :
    Summable e ∧ Tendsto (fun k : ℕ => ((k : ℝ) + K) * e k) atTop (𝓝 0) := by
  have hnn : ∀ N : ℕ, 0 ≤ ((N : ℝ) + K) * e N := fun N => mul_nonneg (by positivity) (he N)
  have hpart : ∀ N : ℕ, σ * ∑ k ∈ range N, e k + ((N : ℝ) + K) * e N ≤ K * e 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have := h N
      push_cast
      nlinarith
  have hsum : Summable e := by
    refine summable_of_sum_range_le (c := K * e 0 / σ) he fun N => ?_
    rw [le_div_iff₀ hσ]
    have := hpart N
    have := hnn N
    linarith
  refine ⟨hsum, ?_⟩
  have hanti : Antitone (fun k : ℕ => ((k : ℝ) + K) * e k) := by
    refine antitone_nat_of_succ_le fun k => ?_
    have := h k
    have := he k
    push_cast
    nlinarith
  have hbdd : BddBelow (Set.range fun k : ℕ => ((k : ℝ) + K) * e k) := ⟨0, by
    rintro _ ⟨k, rfl⟩; exact hnn k⟩
  have hL := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ k : ℕ, ((k : ℝ) + K) * e k with hLdef
  have hL0 : 0 ≤ L := le_ciInf hnn
  rcases hL0.eq_or_lt with h0 | hpos
  · rw [← h0] at hL; exact hL
  exfalso
  have hle : ∀ k : ℕ, L ≤ ((k : ℝ) + K) * e k := fun k => hanti.le_of_tendsto hL k
  have hg : Summable (fun n : ℕ => L / (((n + (K + 1) : ℕ) : ℝ))) := by
    refine hsum.of_nonneg_of_le (fun n => by positivity) fun n => ?_
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have := hle n
    have := he n
    nlinarith
  have hg2 : Summable (fun n : ℕ => 1 / (((n + (K + 1) : ℕ) : ℝ))) := by
    refine (hg.mul_left L⁻¹).congr fun n => ?_
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff (K + 1)).mp hg2)

theorem gauss_key_ineq (a b c j : ℝ) (hs : 0 < c - a - b) (hjc : 0 < j + c)
    (hj : (4 * a * b + (c - a - b) * c) / (3 * (c - a - b)) ≤ j) :
    (j + a) * (j + b) / (j + c) + (c - a - b) / 4 ≤ j := by
  rw [div_add' _ _ _ hjc.ne', div_le_iff₀ hjc]
  rw [div_le_iff₀ (by linarith)] at hj
  nlinarith

/-- Summability of `|t_k|` and `k t_k -> 0` when `c - a - b > 0`. -/
theorem gaussTerm_summable (a b c : ℝ) (hs : 0 < c - a - b) :
    Summable (fun k => |gaussTerm a b c k|) ∧
      Tendsto (fun N : ℕ => (N : ℝ) * gaussTerm a b c N) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (4 * a * b + (c - a - b) * c) / (3 * (c - a - b)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (|a| + |b| + |c| + |M| + 1)
  have hKa : -a < K := by linarith [neg_abs_le a, abs_nonneg b, abs_nonneg c, abs_nonneg M]
  have hKb : -b < K := by linarith [neg_abs_le b, abs_nonneg a, abs_nonneg c, abs_nonneg M]
  have hKc : -c < K := by linarith [neg_abs_le c, abs_nonneg b, abs_nonneg a, abs_nonneg M]
  have hKd : M ≤ K := by linarith [le_abs_self M, abs_nonneg a, abs_nonneg b, abs_nonneg c]
  have hfin := summable_tendsto_of_dec (fun k => |gaussTerm a b c (k + K)|) K ((c - a - b) / 4)
    (by linarith) (fun k => abs_nonneg _) (by
      intro k
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hja : 0 < ((k : ℝ) + K) + a := by linarith
      have hjb : 0 < ((k : ℝ) + K) + b := by linarith
      have hjc : 0 < ((k : ℝ) + K) + c := by linarith
      have hj1 : 0 < ((k : ℝ) + K) + 1 := by linarith
      have hrec : gaussTerm a b c (k + 1 + K) = gaussTerm a b c (k + K) *
          ((((k : ℝ) + K) + a) * (((k : ℝ) + K) + b) / ((((k : ℝ) + K) + c) * (((k : ℝ) + K) + 1))) := by
        rw [show k + 1 + K = (k + K) + 1 by omega, gaussTerm_succ]
        push_cast; rfl
      have hpos : 0 ≤ (((k : ℝ) + K) + a) * (((k : ℝ) + K) + b) /
          ((((k : ℝ) + K) + c) * (((k : ℝ) + K) + 1)) :=
        div_nonneg (mul_nonneg hja.le hjb.le) (mul_pos hjc hj1).le
      simp only [hrec, abs_mul, abs_of_nonneg hpos]
      have key := gauss_key_ineq a b c ((k : ℝ) + K) hs hjc (by rw [← hM]; linarith)
      have hnn := abs_nonneg (gaussTerm a b c (k + K))
      have e1 : ((k : ℝ) + 1 + K) * (|gaussTerm a b c (k + K)| *
          ((((k : ℝ) + K) + a) * (((k : ℝ) + K) + b) /
            ((((k : ℝ) + K) + c) * (((k : ℝ) + K) + 1)))) =
          |gaussTerm a b c (k + K)| * ((((k : ℝ) + K) + a) * (((k : ℝ) + K) + b) /
            (((k : ℝ) + K) + c)) := by
        field_simp
        ring
      rw [e1]
      nlinarith)
  refine ⟨(summable_nat_add_iff K).mp hfin.1, ?_⟩
  rw [← tendsto_add_atTop_iff_nat K]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hfin.2.congr fun n => ?_
  simp only [Real.norm_eq_abs, abs_mul, Nat.cast_add]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) + K by positivity)]

/-! ### The contiguous relation, iteration and the limit `F(c + m) -> 1` -/

/-- The sum of the series `2F1(a, b; c; 1)`. -/
noncomputable def gaussSum (a b c : ℝ) : ℝ := ∑' k, gaussTerm a b c k

theorem gaussTerm_summable' (a b c : ℝ) (hs : 0 < c - a - b) :
    Summable (gaussTerm a b c) :=
  Summable.of_norm (by simpa using (gaussTerm_summable a b c hs).1)

/-- Contiguous relation `c (c-a-b) F(c) = (c-a)(c-b) F(c+1)`. -/
theorem gaussSum_contiguous (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0) :
    c * (c - a - b) * gaussSum a b c = (c - a) * (c - b) * gaussSum a b (c + 1) := by
  have h1 := gaussTerm_summable' a b c hs
  have h2 := gaussTerm_summable' a b (c + 1) (by linarith)
  have t1 := h1.hasSum.tendsto_sum_nat
  have t2 := h2.hasSum.tendsto_sum_nat
  have t3 : Tendsto (fun N : ℕ => c * (c - a - b) * ∑ k ∈ range N, gaussTerm a b c k
      - (c - a) * (c - b) * ∑ k ∈ range N, gaussTerm a b (c + 1) k) atTop
      (𝓝 (c * (c - a - b) * gaussSum a b c - (c - a) * (c - b) * gaussSum a b (c + 1))) :=
    (t1.const_mul _).sub (t2.const_mul _)
  have t4 : Tendsto (fun N : ℕ => - c * N * gaussTerm a b c N) atTop (𝓝 0) := by
    have := ((gaussTerm_summable a b c hs).2).const_mul (-c)
    simpa [mul_assoc] using this
  simp only [gauss_telescope a b c hc] at t3
  have := tendsto_nhds_unique t3 t4
  linarith

theorem gaussSum_iter (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0) (m : ℕ) :
    (∏ j ∈ range m, ((c + j) * ((c - a - b) + j))) * gaussSum a b c =
      (∏ j ∈ range m, ((c - a + j) * (c - b + j))) * gaussSum a b (c + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs' : 0 < (c + m) - a - b := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hc' : ∀ k : ℕ, (c + m) + k ≠ 0 := by
      intro k
      have := hc (m + k)
      push_cast at this
      rwa [← add_assoc] at this
    have h := gaussSum_contiguous a b (c + m) hs' hc'
    rw [prod_range_succ, prod_range_succ, show c + ((m + 1 : ℕ) : ℝ) = c + m + 1 by push_cast; ring]
    linear_combination ((c + m) * (c - a - b + m)) * ih + (∏ j ∈ range m, ((c - a + j) * (c - b + j))) * h

theorem gaussTerm_abs_mono (a b c c' : ℝ) (h0 : 0 < c) (h : c ≤ c') (k : ℕ) :
    |gaussTerm a b c' k| ≤ |gaussTerm a b c k| := by
  induction k with
  | zero => simp [gaussTerm]
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hd : 0 < ((k : ℝ) + c) * ((k : ℝ) + 1) := by positivity
    have hd' : 0 < ((k : ℝ) + c') * ((k : ℝ) + 1) := by
      have : 0 < (k : ℝ) + c' := by linarith
      positivity
    have hr : |((k : ℝ) + a) * ((k : ℝ) + b) / (((k : ℝ) + c') * ((k : ℝ) + 1))| ≤
        |((k : ℝ) + a) * ((k : ℝ) + b) / (((k : ℝ) + c) * ((k : ℝ) + 1))| := by
      rw [abs_div, abs_div, abs_of_pos hd, abs_of_pos hd']
      exact div_le_div_of_nonneg_left (abs_nonneg _) hd
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    rw [gaussTerm_succ, gaussTerm_succ, abs_mul, abs_mul]
    exact mul_le_mul ih hr (abs_nonneg _) (abs_nonneg _)

theorem gaussTerm_tendsto_zero (a b c : ℝ) (k : ℕ) :
    Tendsto (fun m : ℕ => gaussTerm a b (c + m) (k + 1)) atTop (𝓝 0) := by
  have hr : ∀ j : ℕ, Tendsto (fun m : ℕ => ((j : ℝ) + a) * ((j : ℝ) + b) /
      (((j : ℝ) + (c + m)) * ((j : ℝ) + 1))) atTop (𝓝 0) := by
    intro j
    have h1 : Tendsto (fun m : ℕ => (j : ℝ) + (c + m)) atTop atTop :=
      (tendsto_atTop_add_const_left atTop ((j : ℝ) + c) tendsto_natCast_atTop_atTop).congr
        fun m => by ring
    have h2 := h1.atTop_mul_const (show (0 : ℝ) < (j : ℝ) + 1 by positivity)
    exact tendsto_const_nhds.div_atTop h2
  induction k with
  | zero =>
    simpa [gaussTerm] using hr 0
  | succ k ih =>
    have := ih.mul (hr (k + 1))
    simp only [mul_zero] at this
    simpa [gaussTerm_succ] using this

theorem gaussSum_tendsto_one (a b c : ℝ) (hs : 0 < c - a - b) :
    Tendsto (fun m : ℕ => gaussSum a b (c + m)) atTop (𝓝 1) := by
  obtain ⟨m0, hm0⟩ := exists_nat_gt (-c)
  have hb := (gaussTerm_summable a b (c + m0) (by
    have : (0 : ℝ) ≤ m0 := Nat.cast_nonneg m0
    linarith)).1
  have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (m : ℕ) (k : ℕ) => gaussTerm a b (c + m) k)
    (g := fun k : ℕ => if k = 0 then (1 : ℝ) else 0) hb
    (by
      intro k
      cases k with
      | zero => simp [gaussTerm]
      | succ k => simpa using gaussTerm_tendsto_zero a b c k)
    (by
      filter_upwards [eventually_ge_atTop m0] with m hm k
      rw [Real.norm_eq_abs]
      exact gaussTerm_abs_mono a b (c + m0) (c + m) (by linarith)
        (by have : (m0 : ℝ) ≤ m := by exact_mod_cast hm
            linarith) k)
  simpa [gaussSum] using this

/-! ### Gauss's theorem -/

theorem prodA_ne_zero (x : ℝ) (hx : ∀ k : ℕ, x + k ≠ 0) (n : ℕ) :
    ∏ j ∈ range n, (x + (j : ℝ)) ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ => hx j

theorem gammaSeq_ratio (a b c : ℝ) (hca : ∀ k : ℕ, (c - a) + k ≠ 0)
    (hcb : ∀ k : ℕ, (c - b) + k ≠ 0) (hc : ∀ k : ℕ, c + k ≠ 0) (hs : 0 < c - a - b)
    (m : ℕ) (hm : 0 < m) :
    Real.GammaSeq c m * Real.GammaSeq (c - a - b) m / (Real.GammaSeq (c - a) m * Real.GammaSeq (c - b) m)
      = (∏ j ∈ range (m + 1), ((c - a) + (j : ℝ))) * (∏ j ∈ range (m + 1), ((c - b) + (j : ℝ))) /
        ((∏ j ∈ range (m + 1), (c + (j : ℝ))) * ∏ j ∈ range (m + 1), ((c - a - b) + (j : ℝ))) := by
  have hs' : ∀ k : ℕ, (c - a - b) + k ≠ 0 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact (by linarith : 0 < (c - a - b) + k).ne'
  have h1 := prodA_ne_zero _ hca (m + 1)
  have h2 := prodA_ne_zero _ hcb (m + 1)
  have h3 := prodA_ne_zero _ hc (m + 1)
  have h4 := prodA_ne_zero _ hs' (m + 1)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ c * (m : ℝ) ^ (c - a - b) = (m : ℝ) ^ (c - a) * (m : ℝ) ^ (c - b) := by
    rw [← Real.rpow_add hm', ← Real.rpow_add hm']
    congr 1; ring
  have hf : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hp1 : (m : ℝ) ^ (c - a) ≠ 0 := (Real.rpow_pos_of_pos hm' _).ne'
  have hp2 : (m : ℝ) ^ (c - b) ≠ 0 := (Real.rpow_pos_of_pos hm' _).ne'
  simp only [Real.GammaSeq]
  rw [div_mul_div_comm, div_mul_div_comm, div_div_div_eq]
  rw [show (m : ℝ) ^ c * ↑(Nat.factorial m) * ((m : ℝ) ^ (c - a - b) * ↑(Nat.factorial m)) =
      ((m : ℝ) ^ c * (m : ℝ) ^ (c - a - b)) * (↑(Nat.factorial m) * ↑(Nat.factorial m)) by ring, hpow]
  field_simp

/-- Pole case: if `c - a` or `c - b` is a nonpositive integer, the sum is `0`. -/
theorem gaussSum_eq_zero_of_pole (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c + k ≠ 0)
    (h : (∃ n : ℕ, c - a = -(n : ℝ)) ∨ (∃ n : ℕ, c - b = -(n : ℝ))) :
    gaussSum a b c = 0 := by
  have hs' : ∀ k : ℕ, (c - a - b) + k ≠ 0 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact (by linarith : 0 < (c - a - b) + k).ne'
  have key : ∀ n : ℕ, (c - a = -(n : ℝ) ∨ c - b = -(n : ℝ)) → gaussSum a b c = 0 := by
    intro n hn
    have := gaussSum_iter a b c hs hc (n + 1)
    have hz : (∏ j ∈ range (n + 1), ((c - a + j) * (c - b + j))) = 0 := by
      refine prod_eq_zero (i := n) (mem_range.2 (Nat.lt_succ_self n)) ?_
      rcases hn with hn | hn
      · rw [hn]; ring
      · rw [hn]; ring
    rw [hz, zero_mul, prod_mul_distrib] at this
    have hq := mul_ne_zero (prodA_ne_zero c hc (n + 1)) (prodA_ne_zero _ hs' (n + 1))
    exact (mul_eq_zero.1 this).resolve_left hq
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact key n (Or.inl hn)
  · exact key n (Or.inr hn)

/-- Gauss's theorem in terms of `gaussSum`, with the gamma function. -/
theorem gaussSum_eq_gamma (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c ≠ -(k : ℝ)) :
    gaussSum a b c =
      Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b)) := by
  have hc' : ∀ k : ℕ, c + k ≠ 0 := fun k h => hc k (by linarith)
  by_cases hpole : (∃ n : ℕ, c - a = -(n : ℝ)) ∨ (∃ n : ℕ, c - b = -(n : ℝ))
  · rw [gaussSum_eq_zero_of_pole a b c hs hc' hpole]
    have : Real.Gamma (c - a) = 0 ∨ Real.Gamma (c - b) = 0 := by
      rcases hpole with h | h
      · exact Or.inl ((Real.Gamma_eq_zero_iff _).2 h)
      · exact Or.inr ((Real.Gamma_eq_zero_iff _).2 h)
    rcases this with h | h <;> simp [h]
  push Not at hpole
  obtain ⟨hpa, hpb⟩ := hpole
  have hca : ∀ k : ℕ, (c - a) + k ≠ 0 := fun k h => hpa k (by linarith)
  have hcb : ∀ k : ℕ, (c - b) + k ≠ 0 := fun k h => hpb k (by linarith)
  have hga := Real.Gamma_ne_zero hpa
  have hgb := Real.Gamma_ne_zero hpb
  have hlim : Tendsto (fun m : ℕ => gaussSum a b (c + ((m + 1 : ℕ) : ℝ)) *
      (Real.GammaSeq c m * Real.GammaSeq (c - a - b) m /
        (Real.GammaSeq (c - a) m * Real.GammaSeq (c - b) m))) atTop
      (𝓝 (1 * (Real.Gamma c * Real.Gamma (c - a - b) /
        (Real.Gamma (c - a) * Real.Gamma (c - b))))) := by
    refine Tendsto.mul ((tendsto_add_atTop_iff_nat 1).2 (gaussSum_tendsto_one a b c hs)) ?_
    exact ((Real.GammaSeq_tendsto_Gamma c).mul (Real.GammaSeq_tendsto_Gamma _)).div
      ((Real.GammaSeq_tendsto_Gamma _).mul (Real.GammaSeq_tendsto_Gamma _)) (mul_ne_zero hga hgb)
  rw [one_mul] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds (x := gaussSum a b c)) (hlim.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [gammaSeq_ratio a b c hca hcb hc' hs m hm]
  have hit := gaussSum_iter a b c hs hc' (m + 1)
  rw [prod_mul_distrib, prod_mul_distrib] at hit
  have hs' : ∀ k : ℕ, (c - a - b) + k ≠ 0 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact (by linarith : 0 < (c - a - b) + k).ne'
  have h3 := prodA_ne_zero _ hc' (m + 1)
  have h4 := prodA_ne_zero _ hs' (m + 1)
  rw [mul_div_assoc', div_eq_iff (mul_ne_zero h3 h4)]
  linear_combination -hit

/-- CO-361. Gauss's summation of the non-terminating series: for real `a b c` with `c - a - b > 0`
and `c` not a nonpositive integer, `2F1(a, b; c; 1) = Γ(c) Γ(c-a-b) / (Γ(c-a) Γ(c-b))`; the
series is summable (absolutely) and the quotient is read with `1/Γ = 0` at the poles of
`Γ(c-a)`, `Γ(c-b)` (Lean's `Real.Gamma` vanishes there, and so does the sum). -/
@[kb "petkovsekwilfzeilberger1996" "text (I) Gauss, p. 53"]
theorem gauss_two_one_gamma (a b c : ℝ) (hs : 0 < c - a - b) (hc : ∀ k : ℕ, c ≠ -(k : ℝ)) :
    Summable (fun k => pFqTerm ![a, b] ![c] (1 : ℝ) k) ∧
    ∑' k, pFqTerm ![a, b] ![c] (1 : ℝ) k =
      Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b)) := by
  have hc' : ∀ k : ℕ, c + k ≠ 0 := fun k h => hc k (by linarith)
  have e : (fun k => pFqTerm ![a, b] ![c] (1 : ℝ) k) = gaussTerm a b c :=
    funext fun k => (gaussTerm_eq_pFqTerm a b c hc' k).symm
  rw [e]
  exact ⟨gaussTerm_summable' a b c hs, gaussSum_eq_gamma a b c hs hc⟩

end UndergradKB.Combinatorics.AeqB
