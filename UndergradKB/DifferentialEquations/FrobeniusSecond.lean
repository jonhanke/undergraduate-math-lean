import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FrobeniusAnalytic
import UndergradKB.DifferentialEquations.FrobeniusLog

/-! # The second Frobenius solution (Lebl, *Notes on Diffy Qs*, §7.3.2, cases (iv) and (v))

For `x² y'' + x p(x) y' + q(x) y = 0` with `p(x) = ∑ P_k x^k`, `q(x) = ∑ Q_k x^k` convergent for `|x| < ρ`, let
the indicial polynomial `r(r-1) + P₀ r + Q₀` have the real roots `r₁ = r₂ + N` with `N` a natural number (a double
root when `N = 0`).  The first solution is `y₁ = x^{r₁} ∑ a_k x^k` (Theorem 7.3.1, `frobenius_analytic`).  Following
the book, a second solution is sought in the form
`y₂ = x^{r₂} ∑ b_k x^k + C (ln x) y₁`;
plugging in gives the recurrence `F(r₂+k) b_k = -∑_{j<k} b_j ((r₂+j) P_{k-j} + Q_{k-j}) - C d_{k-N}` with
`d_m = (2(r₁+m) - 1) a_m + ∑_{j≤m} a_j P_{m-j}` the coefficients of `2 x y₁' + (p - 1) y₁` (divided by `x^{r₁}`).
At `k = N` the left side vanishes, which fixes `C` (and `C = 1` for the double root).  The coefficients `b_k`
satisfy the same majorant estimate as the `a_k`, so `∑ b_k x^k` converges for `|x| < ρ`, `y₂` solves the equation on
`0 < x < ρ`, and `y₁`, `y₂` are linearly independent there.

Applications: Example 7.3.2 in the book's series form (DE-205), and Bessel's equation of integer order `n ≥ 1`:
a second solution tending to `-∞` at `0`, and the general solution `A J_n + B Y` on `(0, ∞)` (DE-214).
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology Finset

/-! ### Majorant estimate with a forcing term -/

/-- **Majorant estimate with a forcing term**: if `b_k F(r+k) = -∑_{j<k} b_j ((r+j) P_{k-j} + Q_{k-j}) - f_k` for
all `k > N₀`, where `r` is a root of `F` and `|f_k| σ^k ≤ K_f (k+1)`, then `|b_k| σ^k` is bounded. -/
theorem forced_bound (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k)
    {r : ℝ} (hr : aF P Q r = 0) (b f : ℕ → ℝ) (N₀ : ℕ)
    (hrec : ∀ k : ℕ, N₀ < k → b k * aF P Q (r + k) =
      -(∑ j ∈ range k, b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))) - f k)
    {σ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ) {Kf : ℝ} (hKf : 0 ≤ Kf)
    (hf : ∀ k : ℕ, |f k| * σ ^ k ≤ Kf * (k + 1)) : ∃ K : ℝ, ∀ k, |b k| * σ ^ k ≤ K := by
  set ρ' := (σ + ρ) / 2 with hρ'
  have hρ'0 : 0 < ρ' := by positivity
  have hσρ' : σ < ρ' := by linarith
  have hρ'ρ : ρ' < ρ := by linarith
  obtain ⟨M1, hM1, hP'⟩ := coeff_bdd P hρ'0 (hP ρ' (by rw [abs_of_pos hρ'0]; exact hρ'ρ))
  obtain ⟨M2, hM2, hQ'⟩ := coeff_bdd Q hρ'0 (hQ ρ' (by rw [abs_of_pos hρ'0]; exact hρ'ρ))
  set t := σ / ρ' with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := (div_lt_one hρ'0).mpr hσρ'
  set G := (1 - t)⁻¹ with hGdef
  have hG : 0 ≤ G := inv_nonneg.mpr (by linarith)
  have hscale : ∀ i : ℕ, σ ^ i = ρ' ^ i * t ^ i := fun i => by
    rw [← mul_pow]; congr 1; rw [ht]; field_simp
  have hPt : ∀ i, |P i| * σ ^ i ≤ M1 * t ^ i := fun i => by
    calc |P i| * σ ^ i = (|P i| * ρ' ^ i) * t ^ i := by rw [hscale]; ring
      _ ≤ M1 * t ^ i := by gcongr; exact hP' i
  have hQt : ∀ i, |Q i| * σ ^ i ≤ M2 * t ^ i := fun i => by
    calc |Q i| * σ ^ i = (|Q i| * ρ' ^ i) * t ^ i := by rw [hscale]; ring
      _ ≤ M2 * t ^ i := by gcongr; exact hQ' i
  set s : ℝ := 2 * r - 1 + P 0 with hs
  set C : ℝ := (M1 + M2) * G * (|r| + 2) + 2 * Kf with hC
  have hC0 : 0 ≤ C := by positivity
  obtain ⟨K0', hK0'⟩ := exists_nat_ge (|s| + C + 1)
  set K0 := max K0' N₀ with hK0def
  have hK0 : |s| + C + 1 ≤ (K0 : ℝ) := hK0'.trans (by exact_mod_cast le_max_left _ _)
  have hs0 := abs_nonneg s
  have hr0 := abs_nonneg r
  set K : ℝ := max 1 (∑ j ∈ range (K0 + 1), |b j| * σ ^ j) with hKdef
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  have hK1 : 1 ≤ K := le_max_left _ _
  refine ⟨K, fun k => ?_⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hkK : k ≤ K0
    · exact (Finset.single_le_sum (f := fun j => |b j| * σ ^ j) (fun _ _ => by positivity)
        (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _)
    · rw [not_le] at hkK
      have hkN : N₀ < k := lt_of_le_of_lt (le_max_right _ _) hkK
      have hkR : (K0 : ℝ) + 1 ≤ k := by exact_mod_cast hkK
      have hk1 : (1 : ℝ) ≤ k := by linarith [(Nat.cast_nonneg K0 : (0 : ℝ) ≤ K0)]
      have hk' : (0 : ℝ) ≤ k := by linarith
      have hFk : aF P Q (r + k) = k * (k + s) := aF_shift P Q hr k
      have hks : C + 1 ≤ (k : ℝ) + s := by
        have := neg_abs_le s
        linarith
      have hF' : aF P Q (r + k) ≠ 0 := by
        rw [hFk]; exact mul_ne_zero (by linarith) (by linarith)
      have hrec' := hrec k hkN
      have hpos : 0 < |aF P Q (r + k)| := abs_pos.mpr hF'
      have hterm : ∀ j ∈ range k, |b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k ≤
          K * ((|r| + k + 1) * (M1 + M2) * t ^ (k - j)) := by
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hjR : (j : ℝ) ≤ k := by exact_mod_cast hjk.le
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
        have hσk : σ ^ k = σ ^ j * σ ^ (k - j) := by rw [← pow_add]; congr 1; omega
        have h1 : |b j| * σ ^ j ≤ K := ih j hjk
        have h2 : |(r + (j : ℝ)) * P (k - j) + Q (k - j)| * σ ^ (k - j) ≤
            (|r| + k + 1) * (M1 + M2) * t ^ (k - j) := by
          have hrj : |r + (j : ℝ)| ≤ |r| + k :=
            (abs_add_le _ _).trans (by rw [abs_of_nonneg hj0]; linarith)
          have e1 := hPt (k - j)
          have e2 := hQt (k - j)
          have a1 : |(r + (j : ℝ)) * P (k - j) + Q (k - j)| ≤ (|r| + k) * |P (k - j)| + |Q (k - j)| :=
            (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
          have hσp : 0 ≤ σ ^ (k - j) := by positivity
          calc _ ≤ ((|r| + k) * |P (k - j)| + |Q (k - j)|) * σ ^ (k - j) := by gcongr
            _ = (|r| + k) * (|P (k - j)| * σ ^ (k - j)) + |Q (k - j)| * σ ^ (k - j) := by ring
            _ ≤ (|r| + k) * (M1 * t ^ (k - j)) + M2 * t ^ (k - j) := by gcongr
            _ ≤ _ := by
              have : 0 ≤ (|r| + k) * M2 * t ^ (k - j) + M1 * t ^ (k - j) := by positivity
              nlinarith
        rw [abs_mul, hσk]
        calc |b j| * |(r + (j : ℝ)) * P (k - j) + Q (k - j)| * (σ ^ j * σ ^ (k - j))
            = (|b j| * σ ^ j) * (|(r + (j : ℝ)) * P (k - j) + Q (k - j)| * σ ^ (k - j)) := by ring
          _ ≤ K * ((|r| + k + 1) * (M1 + M2) * t ^ (k - j)) := by
              apply mul_le_mul h1 h2 (by positivity) hK
      have hsum : |∑ j ∈ range k, b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k ≤
          K * ((|r| + k + 1) * (M1 + M2) * G) := by
        calc _ ≤ (∑ j ∈ range k, |b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))|) * σ ^ k := by
              gcongr; exact Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j ∈ range k, |b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ j ∈ range k, K * ((|r| + k + 1) * (M1 + M2) * t ^ (k - j)) :=
              Finset.sum_le_sum hterm
          _ = K * ((|r| + k + 1) * (M1 + M2)) * ∑ j ∈ range k, t ^ (k - j) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
          _ ≤ K * ((|r| + k + 1) * (M1 + M2)) * G := by
              gcongr; exact geom_part t ht0 ht1 k
          _ = _ := by ring
      have hfk : |f k| * σ ^ k ≤ K * (Kf * (k + 1)) :=
        (hf k).trans (le_mul_of_one_le_left (by positivity) hK1)
      have hlow : (|r| + k + 1) * (M1 + M2) * G + Kf * (k + 1) ≤ |aF P Q (r + k)| := by
        rw [hFk, abs_mul, abs_of_nonneg hk', abs_of_nonneg (show (0 : ℝ) ≤ k + s by linarith)]
        have e1 : |r| + k + 1 ≤ (|r| + 2) * k := by nlinarith
        have e2 : (k : ℝ) + 1 ≤ 2 * k := by linarith
        calc (|r| + k + 1) * (M1 + M2) * G + Kf * (k + 1)
            ≤ ((|r| + 2) * k) * (M1 + M2) * G + Kf * (2 * k) := by gcongr
          _ = k * C := by rw [hC]; ring
          _ ≤ k * (k + s) := by gcongr; linarith
      have h5 : |b k| * σ ^ k * |aF P Q (r + k)| ≤ K * |aF P Q (r + k)| := by
        have e : |b k| * σ ^ k * |aF P Q (r + k)| =
            |∑ j ∈ range k, b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j)) + f k| * σ ^ k := by
          rw [mul_right_comm, ← abs_mul, hrec', ← abs_neg]
          congr 2; ring
        rw [e]
        calc _ ≤ (|∑ j ∈ range k, b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| + |f k|) * σ ^ k := by
              gcongr; exact abs_add_le _ _
          _ = |∑ j ∈ range k, b j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k +
              |f k| * σ ^ k := by ring
          _ ≤ K * ((|r| + k + 1) * (M1 + M2) * G) + K * (Kf * (k + 1)) := add_le_add hsum hfk
          _ = K * ((|r| + k + 1) * (M1 + M2) * G + Kf * (k + 1)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlow hK
      exact le_of_mul_le_mul_right h5 hpos

/-! ### The coefficients of `2 x y₁' + (p - 1) y₁` -/

/-- `d_m = (2(r+m) - 1) a_m + ∑_{j≤m} a_j P_{m-j}`: `2 x u' + (p(x) - 1) u = x^r ∑ d_m x^m` for `u = x^r ∑ a_m x^m`. -/
noncomputable def dCoef (P : ℕ → ℝ) (r : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  (2 * (r + m) - 1) * a m + ∑ j ∈ range (m + 1), a j * P (m - j)

lemma dCoef_bound (P : ℕ → ℝ) {σ : ℝ} (hσ : 0 < σ) (hPs : Summable fun k => P k * σ ^ k) (r : ℝ)
    (a : ℕ → ℝ) {Ka : ℝ} (ha : ∀ k, |a k| * σ ^ k ≤ Ka) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ m : ℕ, |dCoef P r a m| * σ ^ m ≤ Kd * (m + 1) := by
  obtain ⟨M, hM, hP'⟩ := coeff_bdd P hσ hPs
  have hKa : 0 ≤ Ka := (by positivity : (0 : ℝ) ≤ |a 0| * σ ^ 0).trans (ha 0)
  refine ⟨Ka * (|2 * r - 1| + 2 + M), by positivity, fun m => ?_⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : |(2 * (r + m) - 1) * a m| * σ ^ m ≤ (|2 * r - 1| + 2 * m) * Ka := by
    rw [abs_mul, mul_assoc]
    have : |2 * (r + m) - 1| ≤ |2 * r - 1| + 2 * m := by
      calc |2 * (r + m) - 1| = |(2 * r - 1) + 2 * m| := by ring_nf
        _ ≤ |2 * r - 1| + |2 * (m : ℝ)| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m)]
    exact mul_le_mul this (ha m) (by positivity) (by positivity)
  have h2 : |∑ j ∈ range (m + 1), a j * P (m - j)| * σ ^ m ≤ (m + 1) * (Ka * M) := by
    calc _ ≤ (∑ j ∈ range (m + 1), |a j * P (m - j)|) * σ ^ m := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ range (m + 1), (|a j| * σ ^ j) * (|P (m - j)| * σ ^ (m - j)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j hj => ?_
          have : j ≤ m := by have := Finset.mem_range.mp hj; omega
          have e : σ ^ m = σ ^ j * σ ^ (m - j) := by rw [← pow_add]; congr 1; omega
          rw [e, abs_mul]; ring
      _ ≤ ∑ j ∈ range (m + 1), Ka * M := Finset.sum_le_sum fun j _ =>
          mul_le_mul (ha j) (hP' _) (by positivity) hKa
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  unfold dCoef
  calc |(2 * (r + m) - 1) * a m + ∑ j ∈ range (m + 1), a j * P (m - j)| * σ ^ m
      ≤ (|(2 * (r + m) - 1) * a m| + |∑ j ∈ range (m + 1), a j * P (m - j)|) * σ ^ m := by
        gcongr; exact abs_add_le _ _
    _ = |(2 * (r + m) - 1) * a m| * σ ^ m + |∑ j ∈ range (m + 1), a j * P (m - j)| * σ ^ m := by ring
    _ ≤ (|2 * r - 1| + 2 * m) * Ka + (m + 1) * (Ka * M) := add_le_add h1 h2
    _ ≤ _ := by
        have := abs_nonneg (2 * r - 1)
        nlinarith [mul_nonneg hKa hM, mul_nonneg hKa this, mul_nonneg (mul_nonneg hKa this) hm]

/-- The forcing term `f_k = C d_{k-N}` for `k ≥ N` and `0` for `k < N`. -/
noncomputable def forceCoef (C : ℝ) (N : ℕ) (d : ℕ → ℝ) (k : ℕ) : ℝ := if N ≤ k then C * d (k - N) else 0

lemma forceCoef_bound {C : ℝ} {N : ℕ} {d : ℕ → ℝ} {σ Kd : ℝ} (hσ : 0 < σ) (hKd : 0 ≤ Kd)
    (hd : ∀ m : ℕ, |d m| * σ ^ m ≤ Kd * (m + 1)) (k : ℕ) :
    |forceCoef C N d k| * σ ^ k ≤ (|C| * σ ^ N * Kd) * (k + 1) := by
  unfold forceCoef
  split_ifs with h
  · have e : σ ^ k = σ ^ N * σ ^ (k - N) := by rw [← pow_add]; congr 1; omega
    have hk : ((k - N : ℕ) : ℝ) + 1 ≤ k + 1 := by
      have : ((k - N : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k N
      linarith
    rw [abs_mul, e]
    calc |C| * |d (k - N)| * (σ ^ N * σ ^ (k - N)) = (|C| * σ ^ N) * (|d (k - N)| * σ ^ (k - N)) := by ring
      _ ≤ (|C| * σ ^ N) * (Kd * (((k - N : ℕ) : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hd _) (by positivity)
      _ ≤ (|C| * σ ^ N) * (Kd * (k + 1)) := by gcongr
      _ = _ := by ring
  · simp only [abs_zero, zero_mul]; positivity

/-! ### The coefficients `b_k` of the second solution -/

/-- The recurrence for `b_k`: `b_0` given, `b_N = 0` (for `N ≥ 1`; the free coefficient), and otherwise
`b_k = -(∑_{j<k} b_j ((r+j) P_{k-j} + Q_{k-j}) + f_k) / F(r+k)` with `f = forceCoef C N d`. -/
noncomputable def bRec (P Q : ℕ → ℝ) (r : ℝ) (N : ℕ) (C : ℝ) (d : ℕ → ℝ) (b0 : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then b0 else if k = N then 0 else
    -((∑ j : Fin k, bRec P Q r N C d b0 j * ((r + ((j : ℕ) : ℝ)) * P (k - j) + Q (k - j))) +
      forceCoef C N d k) / aF P Q (r + k)
termination_by k
decreasing_by exact j.2

lemma bRec_eq (P Q : ℕ → ℝ) (r : ℝ) (N : ℕ) (C : ℝ) (d : ℕ → ℝ) (b0 : ℝ) {k : ℕ} (hk : k ≠ 0)
    (hkN : k ≠ N) :
    bRec P Q r N C d b0 k = -((∑ j ∈ range k, bRec P Q r N C d b0 j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))) +
      forceCoef C N d k) / aF P Q (r + k) := by
  rw [bRec]
  simp only [hk, hkN, ↓reduceIte]
  congr 3
  exact Fin.sum_univ_eq_sum_range (fun j => bRec P Q r N C d b0 j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))) k

lemma bRec_zero (P Q : ℕ → ℝ) (r : ℝ) (N : ℕ) (C : ℝ) (d : ℕ → ℝ) (b0 : ℝ) :
    bRec P Q r N C d b0 0 = b0 := by
  rw [bRec]; simp

lemma bRec_N (P Q : ℕ → ℝ) (r : ℝ) {N : ℕ} (hN : N ≠ 0) (C : ℝ) (d : ℕ → ℝ) (b0 : ℝ) :
    bRec P Q r N C d b0 N = 0 := by
  rw [bRec]; simp [hN]

/-- The coefficients below `N` do not depend on `C`. -/
lemma bRec_indep (P Q : ℕ → ℝ) (r : ℝ) (N : ℕ) (C C' : ℝ) (d : ℕ → ℝ) (b0 : ℝ) :
    ∀ k, k < N → bRec P Q r N C d b0 k = bRec P Q r N C' d b0 k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0; rw [bRec_zero, bRec_zero]
    · rw [bRec_eq P Q r N C d b0 hk0 (by omega), bRec_eq P Q r N C' d b0 hk0 (by omega)]
      have hf : ∀ C'' : ℝ, forceCoef C'' N d k = 0 := fun C'' => by
        unfold forceCoef; simp [show ¬ N ≤ k by omega]
      rw [hf, hf]
      congr 3
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [ih j (Finset.mem_range.mp hj) (by have := Finset.mem_range.mp hj; omega)]

/-- The forced coefficient identity: `b_m (r+m)(r+m-1) + ∑_{j≤m} b_j ((r+j) P_{m-j} + Q_{m-j}) + f_m = 0`. -/
def ForcedId (P Q : ℕ → ℝ) (r : ℝ) (b f : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, b m * ((r + m) * (r + m - 1)) +
    ∑ j ∈ range (m + 1), b j * ((r + (j : ℝ)) * P (m - j) + Q (m - j)) + f m = 0

/-! ### The series identities -/

/-- `x^{-r}` times the left side of the equation for `x^r ∑ b_k x^k`, as a power series:
the coefficient of `x^m` is `b_m (r+m)(r+m-1) + ∑_{j≤m} b_j ((r+j) P_{m-j} + Q_{m-j})`. -/
lemma gen_series_hasSum (P Q : ℕ → ℝ) {ρ : ℝ} (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r : ℝ} {a : ℕ → ℝ}
    (h : LocGeo a ρ) {x : ℝ} (hx : |x| < ρ) :
    HasSum (fun m : ℕ => (a m * ((r + m) * (r + m - 1)) +
        ∑ j ∈ range (m + 1), a j * ((r + (j : ℝ)) * P (m - j) + Q (m - j))) * x ^ m)
      (x ^ 2 * fS2 a x + (2 * r + ∑' k, P k * x ^ k) * (x * fS1 a x) +
        (r * (r - 1) + r * (∑' k, P k * x ^ k) + ∑' k, Q k * x ^ k) * fS0 a x) := by
  obtain ⟨ρ2, t, K, h0, h1, h2, h3, hB⟩ := h x hx
  have s0 := gsum0 h2 h3 hB h1.le
  have s1 := gsum1 h0 h2 h3 hB h1.le
  have s2 := gsum2 h0 h2 h3 hB h1.le
  have E1 : ∀ k : ℕ, x ^ 2 * (a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)))) +
      2 * r * (x * (a k * ((k : ℝ) * x ^ (k - 1)))) + r * (r - 1) * (a k * x ^ k) =
      a k * ((r + k) * (r + k - 1)) * x ^ k := by
    intro k
    rcases k with _ | _ | k
    · simp; ring
    · simp; ring
    · simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ, pow_succ]
      ring
  have E2 : ∀ k : ℕ, r * (a k * x ^ k) + x * (a k * ((k : ℝ) * x ^ (k - 1))) =
      (a k * (r + k)) * x ^ k := by
    intro k
    rcases k with _ | k
    · simp; ring
    · simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ]
      ring
  have HU := ((s2.hasSum.mul_left (x ^ 2)).add ((s1.hasSum.mul_left x).mul_left (2 * r))).add
    (s0.hasSum.mul_left (r * (r - 1)))
  have HU' : HasSum (fun k : ℕ => a k * ((r + k) * (r + k - 1)) * x ^ k)
      (x ^ 2 * fS2 a x + 2 * r * (x * fS1 a x) + r * (r - 1) * fS0 a x) := by
    have : (fun k : ℕ => a k * ((r + k) * (r + k - 1)) * x ^ k) = fun k : ℕ =>
        x ^ 2 * (a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)))) +
          2 * r * (x * (a k * ((k : ℝ) * x ^ (k - 1)))) + r * (r - 1) * (a k * x ^ k) :=
      funext fun k => (E1 k).symm
    rw [this]
    exact HU
  have HP := (s0.hasSum.mul_left r).add (s1.hasSum.mul_left x)
  have HP' : HasSum (fun k : ℕ => (a k * (r + k)) * x ^ k) (r * fS0 a x + x * fS1 a x) := by
    have : (fun k : ℕ => (a k * (r + k)) * x ^ k) = fun k : ℕ =>
        r * (a k * x ^ k) + x * (a k * ((k : ℝ) * x ^ (k - 1))) := funext fun k => (E2 k).symm
    rw [this]
    exact HP
  have Cp := cauchy_hasSum (fun j => a j * (r + j)) P HP'.summable (hP x hx)
  rw [HP'.tsum_eq] at Cp
  have Cq := cauchy_hasSum a Q s0 (hQ x hx)
  have Htot := (HU'.add Cp).add Cq
  have hz : (fun m : ℕ => a m * ((r + m) * (r + m - 1)) * x ^ m +
      (∑ j ∈ range (m + 1), (fun j => a j * (r + j)) j * P (m - j)) * x ^ m +
      (∑ j ∈ range (m + 1), a j * Q (m - j)) * x ^ m) = fun m : ℕ => (a m * ((r + m) * (r + m - 1)) +
        ∑ j ∈ range (m + 1), a j * ((r + (j : ℝ)) * P (m - j) + Q (m - j))) * x ^ m := by
    funext m
    have hc : (∑ j ∈ range (m + 1), (fun j => a j * (r + (j : ℝ))) j * P (m - j)) +
        (∑ j ∈ range (m + 1), a j * Q (m - j)) =
        ∑ j ∈ range (m + 1), a j * ((r + (j : ℝ)) * P (m - j) + Q (m - j)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← hc]; ring
  rw [hz] at Htot
  convert Htot using 1
  unfold fS0
  ring

/-- `2 x u' + (p - 1) u = x^r ∑ d_m x^m` at the level of the series: `∑ d_m x^m = 2(r S + x S') + (p - 1) S`. -/
lemma dCoef_hasSum (P : ℕ → ℝ) {ρ : ℝ} (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k) (r : ℝ)
    {a : ℕ → ℝ} (h : LocGeo a ρ) {x : ℝ} (hx : |x| < ρ) :
    HasSum (fun m => dCoef P r a m * x ^ m)
      (2 * (r * fS0 a x + x * fS1 a x) + ((∑' k, P k * x ^ k) - 1) * fS0 a x) := by
  obtain ⟨ρ2, t, K, h0, h1, h2, h3, hB⟩ := h x hx
  have s0 := gsum0 h2 h3 hB h1.le
  have s1 := gsum1 h0 h2 h3 hB h1.le
  have E2 : ∀ k : ℕ, r * (a k * x ^ k) + x * (a k * ((k : ℝ) * x ^ (k - 1))) =
      (a k * (r + k)) * x ^ k := by
    intro k
    rcases k with _ | k
    · simp; ring
    · simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ]
      ring
  have HP' : HasSum (fun k : ℕ => (a k * (r + k)) * x ^ k) (r * fS0 a x + x * fS1 a x) := by
    have : (fun k : ℕ => (a k * (r + k)) * x ^ k) = fun k : ℕ =>
        r * (a k * x ^ k) + x * (a k * ((k : ℝ) * x ^ (k - 1))) := funext fun k => (E2 k).symm
    rw [this]
    exact (s0.hasSum.mul_left r).add (s1.hasSum.mul_left x)
  have Cp := cauchy_hasSum a P s0 (hP x hx)
  have Htot := ((HP'.mul_left 2).add Cp).sub s0.hasSum
  have e : (fun m => dCoef P r a m * x ^ m) = fun m => 2 * ((a m * (r + m)) * x ^ m) +
      (∑ j ∈ range (m + 1), a j * P (m - j)) * x ^ m - a m * x ^ m := by
    funext m; unfold dCoef; ring
  rw [e]
  convert Htot using 1
  unfold fS0
  ring

/-- `∑ f_m x^m = C x^N ∑ d_m x^m` for the forcing term. -/
lemma forceCoef_hasSum (C : ℝ) (N : ℕ) (d : ℕ → ℝ) {x D : ℝ} (hd : HasSum (fun m => d m * x ^ m) D) :
    HasSum (fun m => forceCoef C N d m * x ^ m) (C * x ^ N * D) := by
  have hinj : Function.Injective (fun k : ℕ => k + N) := fun a b h => by simpa using h
  rw [← hinj.hasSum_iff]
  · have e : ((fun m => forceCoef C N d m * x ^ m) ∘ fun k => k + N) =
        fun k => C * x ^ N * (d k * x ^ k) := by
      funext k
      simp only [Function.comp, forceCoef, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
      ring
    rw [e]
    exact hd.mul_left _
  · intro m hm
    have : ¬ N ≤ m := fun h => hm ⟨m - N, by simp only; omega⟩
    simp [forceCoef, this]

/-! ### The second solution solves the equation -/

/-- The candidate second solution `y₂ = x^{r₂} ∑ b_k x^k + C (ln x) x^{r₁} ∑ a_k x^k`. -/
noncomputable def frobLogY (a b : ℕ → ℝ) (r₁ r₂ C : ℝ) (x : ℝ) : ℝ :=
  frobY b r₂ x + C * (Real.log x * frobY a r₁ x)

/-- Its first derivative. -/
noncomputable def frobLogY1 (a b : ℕ → ℝ) (r₁ r₂ C : ℝ) (x : ℝ) : ℝ :=
  frobY1 b r₂ x + C * (x⁻¹ * frobY a r₁ x + Real.log x * frobY1 a r₁ x)

/-- Its second derivative. -/
noncomputable def frobLogY2 (a b : ℕ → ℝ) (r₁ r₂ C : ℝ) (x : ℝ) : ℝ :=
  frobY2 b r₂ x + C * (-(x ^ 2)⁻¹ * frobY a r₁ x + x⁻¹ * frobY1 a r₁ x +
    (x⁻¹ * frobY1 a r₁ x + Real.log x * frobY2 a r₁ x))

lemma hasDerivAt_frobY' {a : ℕ → ℝ} {ρ r : ℝ} (h : LocGeo a ρ) {x : ℝ} (hx0 : 0 < x) (hxρ : x < ρ) :
    HasDerivAt (frobY a r) (frobY1 a r x) x :=
  (hasDerivAt_rpow_div r x hx0).mul (h.deriv0 (by rw [abs_of_pos hx0]; exact hxρ))

lemma hasDerivAt_frobY1' {a : ℕ → ℝ} {ρ r : ℝ} (h : LocGeo a ρ) {x : ℝ} (hx0 : 0 < x) (hxρ : x < ρ) :
    HasDerivAt (frobY1 a r) (frobY2 a r x) x :=
  ((hasDerivAt_rpow_div2 r x hx0).mul (h.deriv0 (by rw [abs_of_pos hx0]; exact hxρ))).add
    ((hasDerivAt_rpow_div r x hx0).mul (h.deriv1 (by rw [abs_of_pos hx0]; exact hxρ)))

lemma hasDerivAt_frobLogY {a b : ℕ → ℝ} {ρ r₁ r₂ C : ℝ} (ha : LocGeo a ρ) (hb : LocGeo b ρ) {x : ℝ}
    (hx0 : 0 < x) (hxρ : x < ρ) :
    HasDerivAt (frobLogY a b r₁ r₂ C) (frobLogY1 a b r₁ r₂ C x) x := by
  have hl : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have := (hasDerivAt_frobY' (r := r₂) hb hx0 hxρ).add
    ((hl.mul (hasDerivAt_frobY' (r := r₁) ha hx0 hxρ)).const_mul C)
  exact this

lemma hasDerivAt_frobLogY1 {a b : ℕ → ℝ} {ρ r₁ r₂ C : ℝ} (ha : LocGeo a ρ) (hb : LocGeo b ρ) {x : ℝ}
    (hx0 : 0 < x) (hxρ : x < ρ) :
    HasDerivAt (frobLogY1 a b r₁ r₂ C) (frobLogY2 a b r₁ r₂ C x) x := by
  have hl : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have hi : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0.ne'
  have h1 := hasDerivAt_frobY' (r := r₁) ha hx0 hxρ
  have h2 := hasDerivAt_frobY1' (r := r₁) ha hx0 hxρ
  have := (hasDerivAt_frobY1' (r := r₂) hb hx0 hxρ).add (((hi.mul h1).add (hl.mul h2)).const_mul C)
  exact this

/-- The derivatives of `frobLogY` are the explicit ones on `(0, ρ)`. -/
lemma deriv_frobLogY {a b : ℕ → ℝ} {ρ r₁ r₂ C : ℝ} (ha : LocGeo a ρ) (hb : LocGeo b ρ) {x : ℝ}
    (hx0 : 0 < x) (hxρ : x < ρ) :
    deriv (frobLogY a b r₁ r₂ C) x = frobLogY1 a b r₁ r₂ C x ∧
      deriv (deriv (frobLogY a b r₁ r₂ C)) x = frobLogY2 a b r₁ r₂ C x := by
  have hd : deriv (frobLogY a b r₁ r₂ C) =ᶠ[𝓝 x] frobLogY1 a b r₁ r₂ C := by
    filter_upwards [Ioo_mem_nhds hx0 hxρ] with z hz using (hasDerivAt_frobLogY ha hb hz.1 hz.2).deriv
  exact ⟨(hasDerivAt_frobLogY ha hb hx0 hxρ).deriv, by
    rw [hd.deriv_eq]; exact (hasDerivAt_frobLogY1 ha hb hx0 hxρ).deriv⟩

/-- **The logarithmic second solution solves the equation**: if `y₁ = x^{r₁} ∑ a_k x^k` is a Frobenius solution
(coefficient identity at `r₁`) and the `b_k` satisfy the forced identity at `r₂ = r₁ - N` with forcing
`C d_{k-N}`, then `y₂ = x^{r₂} ∑ b_k x^k + C (ln x) y₁` solves `x² y'' + x p y' + q y = 0` on `0 < x < ρ`. -/
theorem frobLogY_ode (P Q : ℕ → ℝ) {ρ : ℝ} (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r₁ r₂ : ℝ} {N : ℕ} (hN : r₁ = r₂ + N)
    {a b : ℕ → ℝ} (ha : LocGeo a ρ) (hb : LocGeo b ρ) (hida : FrobCoefId P Q r₁ a) (C : ℝ)
    (hidb : ForcedId P Q r₂ b (forceCoef C N (dCoef P r₁ a))) {x : ℝ} (hx0 : 0 < x) (hxρ : x < ρ) :
    x ^ 2 * frobLogY2 a b r₁ r₂ C x + x * psum P x * frobLogY1 a b r₁ r₂ C x +
      psum Q x * frobLogY a b r₁ r₂ C x = 0 := by
  have hxa : |x| < ρ := by rw [abs_of_pos hx0]; exact hxρ
  have Ea := gen_series_eq P Q hP hQ ha hida hxa
  have Hb := gen_series_hasSum P Q hP hQ (r := r₂) hb hxa
  have Hd := dCoef_hasSum P hP r₁ ha hxa
  have Hf := forceCoef_hasSum C N (dCoef P r₁ a) Hd
  have Hz : HasSum (fun m : ℕ => (b m * ((r₂ + m) * (r₂ + m - 1)) +
        ∑ j ∈ range (m + 1), b j * ((r₂ + (j : ℝ)) * P (m - j) + Q (m - j))) * x ^ m +
        forceCoef C N (dCoef P r₁ a) m * x ^ m) 0 := by
    have : (fun m : ℕ => (b m * ((r₂ + m) * (r₂ + m - 1)) +
        ∑ j ∈ range (m + 1), b j * ((r₂ + (j : ℝ)) * P (m - j) + Q (m - j))) * x ^ m +
        forceCoef C N (dCoef P r₁ a) m * x ^ m) = fun _ => 0 := by
      funext m
      have := hidb m
      linear_combination x ^ m * this
    rw [this]; exact hasSum_zero
  have Eb := (Hb.add Hf).unique Hz
  have hu : 0 < x ^ r₂ := Real.rpow_pos_of_pos hx0 r₂
  have hv : x ^ r₁ = x ^ r₂ * x ^ N := by
    rw [hN, Real.rpow_add hx0, Real.rpow_natCast]
  unfold frobLogY2 frobLogY1 frobLogY frobY2 frobY1 frobY psum
  rw [hv]
  set u := x ^ r₂
  set w := (x : ℝ) ^ N
  set pp := ∑' k, P k * x ^ k
  set qq := ∑' k, Q k * x ^ k
  set A := fS0 a x
  set A1 := fS1 a x
  set A2 := fS2 a x
  set B := fS0 b x
  set B1 := fS1 b x
  set B2 := fS2 b x
  set L := Real.log x
  have hx : x ≠ 0 := hx0.ne'
  have expand :
      x ^ 2 * (r₂ * (r₂ - 1) * u / x ^ 2 * B + r₂ * u / x * B1 + (r₂ * u / x * B1 + u * B2) +
        C * (-(x ^ 2)⁻¹ * (u * w * A) + x⁻¹ * (r₁ * (u * w) / x * A + u * w * A1) +
          (x⁻¹ * (r₁ * (u * w) / x * A + u * w * A1) +
            L * (r₁ * (r₁ - 1) * (u * w) / x ^ 2 * A + r₁ * (u * w) / x * A1 +
              (r₁ * (u * w) / x * A1 + u * w * A2))))) +
      x * pp * (r₂ * u / x * B + u * B1 + C * (x⁻¹ * (u * w * A) + L * (r₁ * (u * w) / x * A + u * w * A1))) +
      qq * (u * B + C * (L * (u * w * A))) =
      u * (x ^ 2 * B2 + (2 * r₂ + pp) * (x * B1) + (r₂ * (r₂ - 1) + r₂ * pp + qq) * B) +
        C * L * (u * w) * (x ^ 2 * A2 + (2 * r₁ + pp) * (x * A1) + (r₁ * (r₁ - 1) + r₁ * pp + qq) * A) +
        C * (u * w) * (2 * (r₁ * A + x * A1) + (pp - 1) * A) := by
    field_simp
    ring
  rw [expand, Ea]
  have : x ^ 2 * B2 + (2 * r₂ + pp) * (x * B1) + (r₂ * (r₂ - 1) + r₂ * pp + qq) * B =
      -(C * w * (2 * (r₁ * A + x * A1) + (pp - 1) * A)) := by linarith
  rw [this]
  ring

/-! ### Construction of `b` and `C` -/

/-- The constant `C`: `1` for a double root, `-(∑_{j<N} b_j ((r₂+j) P_{N-j} + Q_{N-j}))/N` otherwise. -/
noncomputable def logC (P Q : ℕ → ℝ) (r₂ : ℝ) (N : ℕ) (d : ℕ → ℝ) : ℝ :=
  if N = 0 then 1 else
    -(∑ j ∈ range N, bRec P Q r₂ N 0 d 1 j * ((r₂ + (j : ℝ)) * P (N - j) + Q (N - j))) / N

/-- The coefficients `b_k` of the second solution (`b₀ = 0` for a double root, `b₀ = 1` otherwise). -/
noncomputable def logB (P Q : ℕ → ℝ) (r₂ : ℝ) (N : ℕ) (d : ℕ → ℝ) : ℕ → ℝ :=
  bRec P Q r₂ N (logC P Q r₂ N d) d (if N = 0 then 0 else 1)

lemma aF_roots (P Q : ℕ → ℝ) {r₁ r₂ : ℝ} (hsum : r₁ + r₂ = 1 - P 0) (hprod : r₁ * r₂ = Q 0) (t : ℝ) :
    aF P Q t = (t - r₁) * (t - r₂) := by
  unfold aF
  rw [← hprod, show P 0 = 1 - r₁ - r₂ by linarith]
  ring

lemma logB_forcedId (P Q : ℕ → ℝ) {r₁ r₂ : ℝ} {N : ℕ} (hsum : r₁ + r₂ = 1 - P 0)
    (hprod : r₁ * r₂ = Q 0) (hN : r₁ = r₂ + N) {a : ℕ → ℝ} (ha0 : a 0 = 1) :
    ForcedId P Q r₂ (logB P Q r₂ N (dCoef P r₁ a))
      (forceCoef (logC P Q r₂ N (dCoef P r₁ a)) N (dCoef P r₁ a)) := by
  set d := dCoef P r₁ a
  set C := logC P Q r₂ N d
  set b := logB P Q r₂ N d
  have hF : ∀ t, aF P Q t = (t - r₁) * (t - r₂) := aF_roots P Q hsum hprod
  have hd0 : d 0 = N := by
    simp only [d, dCoef, ha0, Nat.cast_zero, add_zero, zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.sub_zero, one_mul]
    linarith
  intro m
  rw [Finset.sum_range_succ, Nat.sub_self]
  have hsplit : b m * ((r₂ + m) * (r₂ + m - 1)) +
      (∑ j ∈ range m, b j * ((r₂ + (j : ℝ)) * P (m - j) + Q (m - j)) +
        b m * ((r₂ + (m : ℝ)) * P 0 + Q 0)) + forceCoef C N d m =
      b m * aF P Q (r₂ + m) + ∑ j ∈ range m, b j * ((r₂ + (j : ℝ)) * P (m - j) + Q (m - j)) +
        forceCoef C N d m := by
    unfold aF; ring
  rw [hsplit]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero, hF]
    by_cases hN0 : N = 0
    · have : forceCoef C N d 0 = C * d 0 := by simp [forceCoef, hN0]
      rw [this, hd0, hN0]; simp
    · have : forceCoef C N d 0 = 0 := by simp [forceCoef, hN0]
      rw [this]; ring
  by_cases hmN : m = N
  · subst hmN
    have hbN : b m = 0 := bRec_N P Q r₂ hm0 _ _ _
    have hf : forceCoef C m d m = C * d 0 := by simp [forceCoef]
    rw [hbN, hf, hd0, zero_mul, zero_add]
    have hC : C = -(∑ j ∈ range m, bRec P Q r₂ m 0 d 1 j * ((r₂ + (j : ℝ)) * P (m - j) + Q (m - j))) / m := by
      simp [C, logC, hm0]
    have hbj : ∀ j ∈ range m, b j = bRec P Q r₂ m 0 d 1 j := by
      intro j hj
      have := bRec_indep P Q r₂ m C 0 d 1 j (Finset.mem_range.mp hj)
      simp only [b, logB, hm0, ↓reduceIte]
      exact this
    rw [Finset.sum_congr rfl fun j hj => by rw [hbj j hj], hC]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    field_simp
    ring
  · have hFm : aF P Q (r₂ + m) ≠ 0 := by
      rw [hF, hN]
      have : (m : ℝ) ≠ N := by exact_mod_cast hmN
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
      have e : (r₂ + m - (r₂ + N)) * (r₂ + m - r₂) = (m - N) * m := by ring
      rw [e]
      exact mul_ne_zero (sub_ne_zero.mpr (by assumption)) (by assumption)
    have hb := bRec_eq P Q r₂ N C d (if N = 0 then 0 else 1) hm0 hmN
    have hb' : b m * aF P Q (r₂ + m) =
        -((∑ j ∈ range m, b j * ((r₂ + (j : ℝ)) * P (m - j) + Q (m - j))) + forceCoef C N d m) := by
      simp only [b, logB]
      rw [hb, div_mul_cancel₀ _ hFm]
    rw [hb']; ring

lemma logB_locGeo (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r₁ r₂ : ℝ} {N : ℕ}
    (hsum : r₁ + r₂ = 1 - P 0) (hprod : r₁ * r₂ = Q 0) (hN : r₁ = r₂ + N) :
    LocGeo (logB P Q r₂ N (dCoef P r₁ (aCoef P Q r₁))) ρ := by
  set a := aCoef P Q r₁
  set d := dCoef P r₁ a
  set C := logC P Q r₂ N d
  have hF : ∀ t, aF P Q t = (t - r₁) * (t - r₂) := aF_roots P Q hsum hprod
  have hr₁ : aF P Q r₁ = 0 := by rw [hF]; ring
  have hr₂ : aF P Q r₂ = 0 := by rw [hF]; ring
  have hF₁ : ∀ k : ℕ, 1 ≤ k → aF P Q (r₁ + k) ≠ 0 := by
    intro k hk
    rw [hF, hN]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact mul_ne_zero (by intro h; linarith) (by intro h; linarith)
  refine locGeo_of_bound fun σ hσ hσρ => ?_
  have hσa : |σ| < ρ := by rw [abs_of_pos hσ]; exact hσρ
  obtain ⟨Ka, hKa⟩ := aCoef_bound P Q hρ hP hQ hr₁ hF₁ hσ hσρ
  obtain ⟨Kd, hKd0, hKd⟩ := dCoef_bound P hσ (hP σ hσa) r₁ a hKa
  refine forced_bound P Q hρ hP hQ hr₂ _ (forceCoef C N d) N (fun k hk => ?_) hσ hσρ
    (by positivity : (0 : ℝ) ≤ |C| * σ ^ N * Kd) (forceCoef_bound hσ hKd0 hKd)
  have hk0 : k ≠ 0 := by omega
  have hkN : k ≠ N := by omega
  have hFk : aF P Q (r₂ + k) ≠ 0 := by
    rw [hF, hN]
    have : (N : ℝ) < k := by exact_mod_cast hk
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact mul_ne_zero (by intro h; linarith) (by intro h; linarith)
  have hb := bRec_eq P Q r₂ N C d (if N = 0 then 0 else 1) hk0 hkN
  simp only [logB]
  rw [hb, div_mul_cancel₀ _ hFk]
  ring

/-! ### Independence -/

lemma LocGeo.tendsto_zero {a : ℕ → ℝ} {ρ : ℝ} (h : LocGeo a ρ) (hρ : 0 < ρ) :
    Tendsto (fS0 a) (𝓝[>] 0) (𝓝 (a 0)) := by
  have hc := (h.deriv0 (by simpa using hρ : |(0 : ℝ)| < ρ)).continuousAt
  rw [ContinuousAt, fS0_zero] at hc
  exact hc.mono_left nhdsWithin_le_nhds

/-- `y₁` and `y₂ = x^{r₂} ∑ b_k x^k + C (ln x) y₁` are linearly independent on `(0, ρ)` (with `b₀ = 1` when
`N ≥ 1`, and `b₀ = 0`, `C = 1` for the double root). -/
theorem frobLogY_indep {ρ : ℝ} (hρ : 0 < ρ) {a b : ℕ → ℝ} (ha : LocGeo a ρ) (hb : LocGeo b ρ)
    (ha0 : a 0 = 1) {r₁ r₂ C : ℝ} {N : ℕ} (hN : r₁ = r₂ + N) (hb0 : N = 0 → b 0 = 0 ∧ C = 1)
    (hb1 : N ≠ 0 → b 0 = 1) (α β : ℝ)
    (h : ∀ x : ℝ, 0 < x → x < ρ → α * frobY a r₁ x + β * frobLogY a b r₁ r₂ C x = 0) :
    α = 0 ∧ β = 0 := by
  have hA := ha.tendsto_zero hρ
  have hB := hb.tendsto_zero hρ
  rw [ha0] at hA
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 ρ := Ioo_mem_nhdsGT hρ
  -- the bracket after dividing by `x^{r₂}`
  have hbr : ∀ x : ℝ, 0 < x → x < ρ →
      α * (x ^ N * fS0 a x) + β * (fS0 b x + C * (Real.log x * (x ^ N * fS0 a x))) = 0 := by
    intro x hx0 hxρ
    have e := h x hx0 hxρ
    have hu : 0 < x ^ r₂ := Real.rpow_pos_of_pos hx0 r₂
    have hv : x ^ r₁ = x ^ r₂ * x ^ N := by rw [hN, Real.rpow_add hx0, Real.rpow_natCast]
    unfold frobLogY frobY at e
    rw [hv] at e
    have : x ^ r₂ * (α * (x ^ N * fS0 a x) + β * (fS0 b x + C * (Real.log x * (x ^ N * fS0 a x)))) = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp this).resolve_left hu.ne'
  have hβ : β = 0 := by
    by_cases hN0 : N = 0
    · obtain ⟨hb00, hC⟩ := hb0 hN0
      rw [hb00] at hB
      subst hN0 hC
      -- `β A = -(α A + β B) / log x → 0`
      have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) (𝓝[>] 0) (𝓝 0) :=
        Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot
      have hR : Tendsto (fun x => -(α * fS0 a x + β * fS0 b x) * (Real.log x)⁻¹) (𝓝[>] 0)
          (𝓝 (-(α * 1 + β * 0) * 0)) :=
        (((hA.const_mul α).add (hB.const_mul β)).neg).mul hinv
      have hL : Tendsto (fun x => β * fS0 a x) (𝓝[>] 0) (𝓝 (β * 1)) := hA.const_mul β
      have hev2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), β * fS0 a x = -(α * fS0 a x + β * fS0 b x) * (Real.log x)⁻¹ := by
        filter_upwards [Ioo_mem_nhdsGT (lt_min hρ one_pos)] with x hx
        have hx0 : 0 < x := hx.1
        have hx1 : x < 1 := lt_of_lt_of_le hx.2 (min_le_right _ _)
        have hxρ : x < ρ := lt_of_lt_of_le hx.2 (min_le_left _ _)
        have hl : Real.log x ≠ 0 := (Real.log_neg hx0 hx1).ne
        have e := hbr x hx0 hxρ
        simp only [pow_zero, one_mul] at e
        field_simp
        linear_combination e
      have := tendsto_nhds_unique hL (hR.congr' (hev2.mono fun x hx => hx.symm))
      simpa using this
    · have hb01 := hb1 hN0
      rw [hb01] at hB
      have hpow : Tendsto (fun x : ℝ => x ^ N) (𝓝[>] 0) (𝓝 0) := by
        have := ((continuous_pow N).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
        simpa [zero_pow hN0] using this
      have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ N) (𝓝[>] 0) (𝓝 0) := by
        have := tendsto_log_mul_rpow_nhdsGT_zero (r := (N : ℝ)) (by exact_mod_cast Nat.pos_of_ne_zero hN0)
        simpa [Real.rpow_natCast] using this
      have hT : Tendsto (fun x => α * (x ^ N * fS0 a x) + β * (fS0 b x + C * (Real.log x * (x ^ N * fS0 a x))))
          (𝓝[>] 0) (𝓝 (α * (0 * 1) + β * (1 + C * (0 * 1)))) := by
        refine ((hpow.mul hA).const_mul α).add ((hB.add ((hlog.mul hA).const_mul C)).const_mul β) |>.congr ?_
        intro x; ring
      have h0 : Tendsto (fun x => α * (x ^ N * fS0 a x) + β * (fS0 b x + C * (Real.log x * (x ^ N * fS0 a x))))
          (𝓝[>] 0) (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun x hx => (hbr x hx.1 hx.2).symm)
      have := tendsto_nhds_unique hT h0
      simpa using this
  refine ⟨?_, hβ⟩
  obtain ⟨z, hz0, hzρ, hz⟩ := ha.exists_ne_zero hρ ha0
  have e := h z hz0 hzρ
  rw [hβ, zero_mul, add_zero] at e
  unfold frobY at e
  rcases mul_eq_zero.mp e with h1 | h1
  · exact h1
  · exact absurd ((mul_eq_zero.mp h1).resolve_left (Real.rpow_pos_of_pos hz0 r₁).ne') hz

/-! ### The theorem -/

/-- The construction with explicit coefficients: `a = aCoef P Q r₁`, `b = logB …`, `C = logC …`. -/
theorem frobenius_second_core (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r₁ r₂ : ℝ} {N : ℕ}
    (hsum : r₁ + r₂ = 1 - P 0) (hprod : r₁ * r₂ = Q 0) (hN : r₁ = r₂ + N) :
    let a := aCoef P Q r₁
    let b := logB P Q r₂ N (dCoef P r₁ a)
    let C := logC P Q r₂ N (dCoef P r₁ a)
    LocGeo a ρ ∧ LocGeo b ρ ∧ a 0 = 1 ∧ (N = 0 → b 0 = 0 ∧ C = 1) ∧ (N ≠ 0 → b 0 = 1) ∧
      (∀ x : ℝ, 0 < x → x < ρ → x ^ 2 * deriv (deriv (frobY a r₁)) x + x * psum P x * deriv (frobY a r₁) x +
        psum Q x * frobY a r₁ x = 0) ∧
      (∀ x : ℝ, 0 < x → x < ρ →
        x ^ 2 * deriv (deriv (frobLogY a b r₁ r₂ C)) x + x * psum P x * deriv (frobLogY a b r₁ r₂ C) x +
          psum Q x * frobLogY a b r₁ r₂ C x = 0) ∧
      (∀ α β : ℝ, (∀ x : ℝ, 0 < x → x < ρ → α * frobY a r₁ x + β * frobLogY a b r₁ r₂ C x = 0) →
        α = 0 ∧ β = 0) := by
  intro a b C
  have hF : ∀ t, aF P Q t = (t - r₁) * (t - r₂) := aF_roots P Q hsum hprod
  have hr₁ : aF P Q r₁ = 0 := by rw [hF]; ring
  have hF₁ : ∀ k : ℕ, 1 ≤ k → aF P Q (r₁ + k) ≠ 0 := by
    intro k hk
    rw [hF, hN]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact mul_ne_zero (by intro h; linarith) (by intro h; linarith)
  have ha : LocGeo a ρ := aCoef_locGeo P Q hρ hP hQ hr₁ hF₁
  have hb : LocGeo b ρ := logB_locGeo P Q hρ hP hQ hsum hprod hN
  have ha0 : a 0 = 1 := aCoef_zero P Q r₁
  have hb0 : N = 0 → b 0 = 0 ∧ C = 1 := fun h => by
    refine ⟨?_, by simp [C, logC, h]⟩
    simp [b, logB, bRec_zero, h]
  have hb1 : N ≠ 0 → b 0 = 1 := fun h => by simp [b, logB, bRec_zero, h]
  have hida := aCoef_id P Q hr₁ hF₁
  have hidb := logB_forcedId P Q hsum hprod hN ha0
  refine ⟨ha, hb, ha0, hb0, hb1, fun x hx0 hxρ => gen_frob_ode P Q hP hQ ha hida hx0 hxρ,
    fun x hx0 hxρ => ?_, frobLogY_indep hρ ha hb ha0 hN hb0 hb1⟩
  obtain ⟨e1, e2⟩ := deriv_frobLogY (r₁ := r₁) (r₂ := r₂) (C := C) ha hb hx0 hxρ
  rw [e1, e2]
  exact frobLogY_ode P Q hP hQ hN ha hb hida C hidb hx0 hxρ

/-- **The second Frobenius solution** (Lebl, §7.3.2, method of Frobenius, cases (iv) and (v); DE-208).
Let `p(x) = ∑ P_k x^k` and `q(x) = ∑ Q_k x^k` converge for `|x| < ρ`, and let `r₁ ≥ r₂` be the roots of the indicial
equation `r(r-1) + P₀ r + Q₀ = 0` (so `r₁ + r₂ = 1 - P₀`, `r₁ r₂ = Q₀`) with `r₁ - r₂ = N` a natural number.
Then there are coefficients `a_k`, `b_k` and a constant `C`, with `∑ a_k x^k` and `∑ b_k x^k` convergent for
`|x| < ρ`, such that
* `y₁ = x^{r₁} ∑ a_k x^k` (`a₀ = 1`) and
* `y₂ = x^{r₂} ∑ b_k x^k + C (ln x) y₁`
both solve `x² y'' + x p(x) y' + q(x) y = 0` on `0 < x < ρ` and are linearly independent there.  For a double root
(`N = 0`, case (iv)) `C = 1` (and `b₀ = 0`): `y₂ = x^r ∑ b_k x^k + (ln x) y₁`; for roots differing by a positive
integer (case (v)) `b₀ = 1` and `C` may or may not vanish. -/
@[kb "lebldiffyqs2026" "§7.3.2 Frobenius cases (i)-(vi), p. 346"]
theorem frobenius_second_solution (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r₁ r₂ : ℝ} {N : ℕ}
    (hsum : r₁ + r₂ = 1 - P 0) (hprod : r₁ * r₂ = Q 0) (hN : r₁ - r₂ = N) :
    ∃ (a b : ℕ → ℝ) (C : ℝ), a 0 = 1 ∧ (N = 0 → b 0 = 0 ∧ C = 1) ∧ (N ≠ 0 → b 0 = 1) ∧
      (∀ x : ℝ, |x| < ρ → Summable fun k => a k * x ^ k) ∧
      (∀ x : ℝ, |x| < ρ → Summable fun k => b k * x ^ k) ∧
      (∀ x : ℝ, 0 < x → x < ρ →
        x ^ 2 * deriv (deriv (fun t : ℝ => t ^ r₁ * ∑' k, a k * t ^ k)) x +
          x * (∑' k, P k * x ^ k) * deriv (fun t : ℝ => t ^ r₁ * ∑' k, a k * t ^ k) x +
          (∑' k, Q k * x ^ k) * (x ^ r₁ * ∑' k, a k * x ^ k) = 0) ∧
      (∀ x : ℝ, 0 < x → x < ρ →
        x ^ 2 * deriv (deriv (fun t : ℝ => t ^ r₂ * ∑' k, b k * t ^ k +
            C * (Real.log t * (t ^ r₁ * ∑' k, a k * t ^ k)))) x +
          x * (∑' k, P k * x ^ k) * deriv (fun t : ℝ => t ^ r₂ * ∑' k, b k * t ^ k +
            C * (Real.log t * (t ^ r₁ * ∑' k, a k * t ^ k))) x +
          (∑' k, Q k * x ^ k) * (x ^ r₂ * ∑' k, b k * x ^ k + C * (Real.log x * (x ^ r₁ * ∑' k, a k * x ^ k)))
            = 0) ∧
      (∀ α β : ℝ, (∀ x : ℝ, 0 < x → x < ρ → α * (x ^ r₁ * ∑' k, a k * x ^ k) +
        β * (x ^ r₂ * ∑' k, b k * x ^ k + C * (Real.log x * (x ^ r₁ * ∑' k, a k * x ^ k))) = 0) →
        α = 0 ∧ β = 0) := by
  have hN' : r₁ = r₂ + N := by linarith
  obtain ⟨ha, hb, ha0, hb0, hb1, h1, h2, h3⟩ := frobenius_second_core P Q hρ hP hQ hsum hprod hN'
  exact ⟨_, _, _, ha0, hb0, hb1, fun x hx => ha.summable hx, fun x hx => hb.summable hx, h1, h2, h3⟩

/-- **Whole half-line version** (coefficients convergent for every `x`, e.g. polynomials): the same explicit
`a`, `b`, `C` work for every `ρ`, so `y₁` and `y₂` solve the equation on all of `0 < x < ∞` and are independent
there. -/
theorem frobenius_second_core_entire (P Q : ℕ → ℝ)
    (hP : ∀ x : ℝ, Summable fun k => P k * x ^ k) (hQ : ∀ x : ℝ, Summable fun k => Q k * x ^ k)
    {r₁ r₂ : ℝ} {N : ℕ} (hsum : r₁ + r₂ = 1 - P 0) (hprod : r₁ * r₂ = Q 0) (hN : r₁ = r₂ + N) :
    let a := aCoef P Q r₁
    let b := logB P Q r₂ N (dCoef P r₁ a)
    let C := logC P Q r₂ N (dCoef P r₁ a)
    (∀ ρ : ℝ, 0 < ρ → LocGeo a ρ ∧ LocGeo b ρ) ∧ a 0 = 1 ∧ (N = 0 → b 0 = 0 ∧ C = 1) ∧
      (N ≠ 0 → b 0 = 1) ∧
      (∀ x : ℝ, 0 < x → x ^ 2 * deriv (deriv (frobY a r₁)) x + x * psum P x * deriv (frobY a r₁) x +
        psum Q x * frobY a r₁ x = 0) ∧
      (∀ x : ℝ, 0 < x →
        x ^ 2 * deriv (deriv (frobLogY a b r₁ r₂ C)) x + x * psum P x * deriv (frobLogY a b r₁ r₂ C) x +
          psum Q x * frobLogY a b r₁ r₂ C x = 0) ∧
      (∀ α β : ℝ, (∀ x : ℝ, 0 < x → α * frobY a r₁ x + β * frobLogY a b r₁ r₂ C x = 0) →
        α = 0 ∧ β = 0) := by
  intro a b C
  have core := fun (ρ : ℝ) (hρ : 0 < ρ) =>
    frobenius_second_core P Q hρ (fun x _ => hP x) (fun x _ => hQ x) hsum hprod hN
  obtain ⟨_, _, ha0, hb0, hb1, _, _, h3⟩ := core 1 one_pos
  refine ⟨fun ρ hρ => ⟨(core ρ hρ).1, (core ρ hρ).2.1⟩, ha0, hb0, hb1, fun x hx => ?_, fun x hx => ?_,
    fun α β h => h3 α β fun x hx _ => h x hx⟩
  · exact (core (x + 1) (by linarith)).2.2.2.2.2.1 x hx (by linarith)
  · exact (core (x + 1) (by linarith)).2.2.2.2.2.2.1 x hx (by linarith)

end UndergradKB.DifferentialEquations
