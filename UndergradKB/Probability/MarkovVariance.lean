import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovPassage
import UndergradKB.Probability.MarkovLLN

/-! # Asymptotic mean and variance of the number of visits (Grinstead–Snell, Theorem 11.17)

For a regular chain with fixed probability vector `w` and fundamental matrix `Z = (I - P + W)⁻¹`, the number of
visits `S_j^(n)` to the state `j` among the times `0, …, n` has mean `(n+1) w_j + O(1)` (indeed
`E - (n+1) w_j → (u (Z - W))_j`) and variance `(n+1) σ_j² + o(n)` with `σ_j² = 2 w_j z_jj - w_j - w_j²`
(equation 11.10).  This is the normalization of the central limit theorem 11.17, not the central limit theorem.

The proof: `(P^k)_{ij} → w_j` geometrically (oscillation contraction, `regular_geometric`), the partial sums
`∑_{k<m} (P^k - W)` tend to `Z - W` (`fundamental_partial_tendsto`), and the second moment of the visits is expanded
with `moment2`; the resulting identity for sequences (`Q_identity`) shows the asymptotics. -/

open Finset Filter Topology Matrix

namespace UndergradKB.Probability

/-! ## Sequences -/

theorem sum_range_cast (N : ℕ) : ∑ s ∈ range N, (s : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The expansion of the second moment about `N w`, with `a s = w + e s`, `r d = w + η d`, `H = ∑ η`. -/
theorem Q_identity (a r : ℕ → ℝ) (w : ℝ) (hr0 : r 0 = 1) (N : ℕ) :
    ∑ s ∈ range N, ∑ t ∈ range N, gsym a r s t - 2 * N * w * csum a N + (N : ℝ) ^ 2 * w ^ 2 =
      N * (w ^ 2 - w) + 2 * w * ∑ m ∈ range N, csum (fun d => r d - w) (m + 1)
        - 2 * w * ∑ s ∈ range N, (s : ℝ) * (a s - w) - ∑ s ∈ range N, (a s - w)
        + 2 * ∑ s ∈ range N, (a s - w) * csum (fun d => r d - w) (N - s) := by
  have hc : ∀ m : ℕ, csum r m = m * w + csum (fun d => r d - w) m := by
    intro m; simp [csum, sum_sub_distrib]
  have hA : csum a N = N * w + ∑ s ∈ range N, (a s - w) := by simp [csum, sum_sub_distrib]
  have hR : ∑ s ∈ range N, csum (fun d => r d - w) (N - s) =
      ∑ m ∈ range N, csum (fun d => r d - w) (m + 1) := by
    refine Eq.trans (sum_congr rfl fun s hs => ?_) (sum_range_reflect (fun m => csum (fun d => r d - w) (m + 1)) N)
    have := mem_range.1 hs
    have e : N - 1 - s + 1 = N - s := by omega
    show _ = csum (fun d => r d - w) (N - 1 - s + 1)
    rw [e]
  have hconv : convT a r N = ∑ s ∈ range N, (w ^ 2 * ((N : ℝ) - s) + w * csum (fun d => r d - w) (N - s) +
      w * ((N : ℝ) * (a s - w) - s * (a s - w)) + (a s - w) * csum (fun d => r d - w) (N - s)) := by
    unfold convT
    refine sum_congr rfl fun s hs => ?_
    have := mem_range.1 hs
    rw [hc (N - s), Nat.cast_sub this.le]; ring
  rw [sum_gsym a r hr0 N, hconv, hA]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, sum_range_cast, hR]
  ring

theorem div_tendsto_zero_of_bdd (g : ℕ → ℝ) (B : ℝ) (hB : ∀ N, |g N| ≤ B) :
    Tendsto (fun N : ℕ => g N / N) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => B / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm (fun N => ?_) h
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (hB N) (Nat.cast_nonneg N)

theorem geom_partial_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (k : ℕ) :
    ∃ B, ∀ N, ∑ s ∈ range N, (s : ℝ) ^ k * ρ ^ s ≤ B := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k (r := ρ) (by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0])
  exact ⟨_, fun N => hs.sum_le_tsum _ (fun s _ => by positivity)⟩

/-- The analytic core of the variance asymptotics. -/
theorem var_asymp (a r : ℕ → ℝ) (w C ρ Hinf : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hr0 : r 0 = 1)
    (hea : ∀ s, |a s - w| ≤ C * ρ ^ s)
    (hH : Tendsto (fun m => csum (fun d => r d - w) m) atTop (𝓝 Hinf)) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * (∑ s ∈ range N, ∑ t ∈ range N, gsym a r s t -
      2 * N * w * csum a N + (N : ℝ) ^ 2 * w ^ 2)) atTop (𝓝 (w ^ 2 - w + 2 * w * Hinf)) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hea 0); simpa using this
  obtain ⟨B0, hB0⟩ := geom_partial_bound hρ0 hρ1 0
  obtain ⟨B1, hB1⟩ := geom_partial_bound hρ0 hρ1 1
  obtain ⟨K, hK⟩ := (Metric.isBounded_range_of_tendsto _ hH).exists_norm_le
  have hHb : ∀ m, |csum (fun d => r d - w) m| ≤ K := fun m => by
    simpa using hK _ ⟨m, rfl⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hHb 0)
  -- bounds
  have bF : ∀ N, |∑ s ∈ range N, (s : ℝ) * (a s - w)| ≤ C * B1 := by
    intro N
    calc |∑ s ∈ range N, (s : ℝ) * (a s - w)| ≤ ∑ s ∈ range N, |(s : ℝ) * (a s - w)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range N, C * ((s : ℝ) ^ 1 * ρ ^ s) := by
          refine sum_le_sum fun s _ => ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg s)]
          calc (s : ℝ) * |a s - w| ≤ (s : ℝ) * (C * ρ ^ s) :=
                mul_le_mul_of_nonneg_left (hea s) (Nat.cast_nonneg s)
            _ = _ := by ring
      _ = C * ∑ s ∈ range N, (s : ℝ) ^ 1 * ρ ^ s := by rw [mul_sum]
      _ ≤ C * B1 := mul_le_mul_of_nonneg_left (hB1 N) hC
  have bE : ∀ N, |∑ s ∈ range N, (a s - w)| ≤ C * B0 := by
    intro N
    calc |∑ s ∈ range N, (a s - w)| ≤ ∑ s ∈ range N, |a s - w| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range N, C * ((s : ℝ) ^ 0 * ρ ^ s) := by
          refine sum_le_sum fun s _ => ?_
          simpa using hea s
      _ = C * ∑ s ∈ range N, (s : ℝ) ^ 0 * ρ ^ s := by rw [mul_sum]
      _ ≤ C * B0 := mul_le_mul_of_nonneg_left (hB0 N) hC
  have bG : ∀ N, |∑ s ∈ range N, (a s - w) * csum (fun d => r d - w) (N - s)| ≤ K * (C * B0) := by
    intro N
    calc |∑ s ∈ range N, (a s - w) * csum (fun d => r d - w) (N - s)|
        ≤ ∑ s ∈ range N, |(a s - w) * csum (fun d => r d - w) (N - s)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range N, K * (C * ((s : ℝ) ^ 0 * ρ ^ s)) := by
          refine sum_le_sum fun s _ => ?_
          rw [abs_mul, mul_comm]
          have h1 := hea s
          have h2 := hHb (N - s)
          simp only [pow_zero, one_mul]
          exact mul_le_mul h2 h1 (abs_nonneg _) hK0
      _ = K * (C * ∑ s ∈ range N, (s : ℝ) ^ 0 * ρ ^ s) := by rw [mul_sum, mul_sum]
      _ ≤ K * (C * B0) := by
          gcongr
          exact hB0 N
  have t1 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ range N, csum (fun d => r d - w) (m + 1)) atTop (𝓝 Hinf) :=
    ((tendsto_add_atTop_iff_nat (f := fun m => csum (fun d => r d - w) m) 1).2 hH).cesaro
  have tF := div_tendsto_zero_of_bdd _ _ bF
  have tE := div_tendsto_zero_of_bdd _ _ bE
  have tG := div_tendsto_zero_of_bdd _ _ bG
  have hlim := (((tendsto_const_nhds (x := w ^ 2 - w)).add (t1.const_mul (2 * w))).sub
    (tF.const_mul (2 * w))).sub tE |>.add (tG.const_mul 2)
  have hz : w ^ 2 - w + 2 * w * Hinf - 2 * w * 0 - 0 + 2 * 0 = w ^ 2 - w + 2 * w * Hinf := by ring
  rw [hz] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNne : (N : ℝ) ≠ 0 := by positivity
  rw [Q_identity a r w hr0 N]
  field_simp

/-! ## Geometric convergence -/

section Geom

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

theorem osc_single_le (j : S) : osc (Pi.single j (1 : ℝ) : S → ℝ) ≤ 1 := by
  unfold osc vmax vmin
  have h1 : univ.sup' univ_nonempty (Pi.single j (1 : ℝ) : S → ℝ) ≤ 1 :=
    sup'_le _ _ fun i _ => by by_cases h : i = j <;> simp [h, Pi.single_apply]
  have h2 : 0 ≤ univ.inf' univ_nonempty (Pi.single j (1 : ℝ) : S → ℝ) :=
    le_inf' _ _ fun i _ => by by_cases h : i = j <;> simp [h, Pi.single_apply]
  linarith

theorem osc_pow_div_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (hε1 : ε ≤ 1 / 2) (hε : ∀ i j, ε ≤ (P ^ N) i j) (y : S → ℝ) (n : ℕ) :
    osc (P ^ n *ᵥ y) ≤ (1 - 2 * ε) ^ (n / N) * osc y := by
  have hc0 : 0 ≤ 1 - 2 * ε := by linarith
  have hn : P ^ n = (P ^ N) ^ (n / N) * P ^ (n % N) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hn, ← mulVec_mulVec]
  calc osc ((P ^ N) ^ (n / N) *ᵥ (P ^ (n % N) *ᵥ y))
      ≤ (1 - 2 * ε) ^ (n / N) * osc (P ^ (n % N) *ᵥ y) :=
        osc_pow_le (pow_mem hP N) hε1 hε _ _
    _ ≤ (1 - 2 * ε) ^ (n / N) * osc y :=
        mul_le_mul_of_nonneg_left (osc_mulVec_le (pow_mem hP _) y) (pow_nonneg hc0 _)

/-- For a regular chain, `(P^n)_{ij} → w_j` geometrically fast. -/
theorem regular_geometric {P : Matrix S S ℝ} (h : IsRegularChain P) {w : S → ℝ}
    (hw : ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 (w j))) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ n i j, |(P ^ n) i j - w j| ≤ C * ρ ^ n := by
  obtain ⟨hP, N, hN, hpos⟩ := h
  obtain ⟨i0⟩ := ‹Nonempty S›
  set m : ℝ := (univ : Finset (S × S)).inf' univ_nonempty (fun ij => (P ^ N) ij.1 ij.2) with hmdef
  have hm0 : 0 < m := (lt_inf'_iff _).2 fun ij _ => hpos ij.1 ij.2
  have hm : ∀ k j, m ≤ (P ^ N) k j := fun k j => inf'_le (fun ij : S × S => (P ^ N) ij.1 ij.2) (mem_univ (k, j))
  set ε : ℝ := min m (1 / 4) with hεdef
  have hε0 : 0 < ε := lt_min hm0 (by norm_num)
  have hε1 : ε ≤ 1 / 4 := min_le_right _ _
  have hε : ∀ i j, ε ≤ (P ^ N) i j := fun i j => (min_le_left _ _).trans (hm i j)
  set c : ℝ := 1 - 2 * ε with hcdef
  have hc0 : 1 / 2 ≤ c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨ρ, hρ0, hρ1, hρN⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ρ ^ N = c := by
    refine ⟨c ^ ((1 : ℝ) / N), Real.rpow_pos_of_pos (by linarith) _,
      Real.rpow_lt_one (by linarith) hc1 (by positivity), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hNr.ne', Real.rpow_one]
  refine ⟨1 / ρ ^ N, ρ, by positivity, hρ0, hρ1, fun n i j => ?_⟩
  set y : S → ℝ := Pi.single j 1 with hy
  have hcol : ∀ n i, (P ^ n *ᵥ y) i = (P ^ n) i j := by
    intro n i; simp [hy, mulVec, dotProduct, Pi.single_apply]
  have hbetween : vmin (P ^ n *ᵥ y) ≤ w j ∧ w j ≤ vmax (P ^ n *ᵥ y) := by
    have hE : ∀ m' : ℕ, (P ^ (m' + n)) i0 j = (P ^ m' *ᵥ (P ^ n *ᵥ y)) i0 := by
      intro m'; rw [mulVec_mulVec, ← pow_add, hcol]
    have hT : Tendsto (fun m' : ℕ => (P ^ (m' + n)) i0 j) atTop (𝓝 (w j)) :=
      (hw i0 j).comp (tendsto_add_atTop_nat n)
    constructor
    · exact ge_of_tendsto hT (Eventually.of_forall fun m' => by
        rw [hE]; exact vmin_le_mulVec (pow_mem hP m') _ i0)
    · exact le_of_tendsto hT (Eventually.of_forall fun m' => by
        rw [hE]; exact mulVec_le_vmax (pow_mem hP m') _ i0)
  have h1 : |(P ^ n) i j - w j| ≤ osc (P ^ n *ᵥ y) := by
    have a1 := vmin_le (P ^ n *ᵥ y) i
    have a2 := le_vmax (P ^ n *ᵥ y) i
    rw [hcol] at a1 a2
    unfold osc
    rw [abs_le]; constructor <;> linarith [hbetween.1, hbetween.2]
  have h2 := osc_pow_div_le hP hN (hε1.trans (by norm_num)) hε y n
  have h3 : osc y ≤ 1 := osc_single_le j
  have h4 : c ^ (n / N) * ρ ^ N ≤ ρ ^ n := by
    have e1 : c ^ (n / N) = ρ ^ (N * (n / N)) := by rw [pow_mul, hρN]
    have e2 : ρ ^ n = ρ ^ (N * (n / N)) * ρ ^ (n % N) := by
      rw [← pow_add, Nat.div_add_mod]
    have e3 : ρ ^ N ≤ ρ ^ (n % N) := pow_le_pow_of_le_one hρ0.le hρ1.le (Nat.mod_lt _ hN).le
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left e3 (by positivity)
  have h5 : c ^ (n / N) ≤ 1 / ρ ^ N * ρ ^ n := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    exact h4
  calc |(P ^ n) i j - w j| ≤ osc (P ^ n *ᵥ y) := h1
    _ ≤ c ^ (n / N) * osc y := h2
    _ ≤ c ^ (n / N) * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 1 / ρ ^ N * ρ ^ n := by rw [mul_one]; exact h5

end Geom

/-! ## The fundamental matrix as a sum -/

section Fund

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem mul_rowsMatrix_self {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (w : S → ℝ) :
    P * rowsMatrix w = rowsMatrix w := by
  ext i k
  simp only [Matrix.mul_apply, rowsMatrix, Matrix.of_apply, ← sum_mul, sum_row_of_mem_rowStochastic hP i, one_mul]

theorem rowsMatrix_mul_self {P : Matrix S S ℝ} {w : S → ℝ} (hfix : IsFixedRow P w) :
    rowsMatrix w * P = rowsMatrix w := by
  ext i k
  have hk := congrFun hfix k
  simp only [vecMul, dotProduct] at hk
  simp only [Matrix.mul_apply, rowsMatrix, Matrix.of_apply, hk]

theorem rowsMatrix_mul_rowsMatrix {w : S → ℝ} (hsum : ∑ j, w j = 1) :
    rowsMatrix w * rowsMatrix w = rowsMatrix w := by
  ext i k
  simp only [Matrix.mul_apply, rowsMatrix, Matrix.of_apply, ← sum_mul, hsum, one_mul]

/-- The partial sums `∑_{k<m} ((P^k)_{ij} - w_j)` tend to `Z_{ij} - w_j` with `Z = (I - P + W)⁻¹`. -/
theorem fundamental_partial_tendsto {P : Matrix S S ℝ} {w : S → ℝ} (hP : P ∈ rowStochastic ℝ S)
    (hsum : ∑ j, w j = 1) (hfix : IsFixedRow P w)
    (hw : ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 (w j)))
    (hZ : IsUnit (1 - P + rowsMatrix w)) (i j : S) :
    Tendsto (fun m => ∑ k ∈ range m, ((P ^ k) i j - w j)) atTop
      (𝓝 ((1 - P + rowsMatrix w)⁻¹ i j - w j)) := by
  set W := rowsMatrix w with hWdef
  set A : Matrix S S ℝ := 1 - P + W with hAdef
  set Z := A⁻¹ with hZdef
  have hZA : Z * A = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hZ)
  have hPW := mul_rowsMatrix_self hP w
  have hWP := rowsMatrix_mul_self hfix
  have hWW := rowsMatrix_mul_rowsMatrix hsum
  have hAW : A * W = W := by
    rw [hAdef, add_mul, sub_mul, Matrix.one_mul, hPW, hWW]; abel
  have hZW : Z * W = W := by rw [← hAW, ← Matrix.mul_assoc, hZA, Matrix.one_mul, hAW]
  have hWPk : ∀ k : ℕ, W * P ^ k = W := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, hWP]
  have hAk : ∀ k : ℕ, A * (P ^ k - W) = P ^ k - P ^ (k + 1) := by
    intro k
    rw [Matrix.mul_sub, hAW, hAdef, add_mul, sub_mul, Matrix.one_mul, hWPk, pow_succ' P k]
    abel
  have hT : ∀ m : ℕ, A * ∑ k ∈ range m, (P ^ k - W) = 1 - P ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, Matrix.mul_add, ih, hAk, pow_succ' P m]; abel
  have key : ∀ m : ℕ, ∑ k ∈ range m, ((P ^ k) i j - w j) = Z i j - ∑ l, Z i l * (P ^ m) l j := by
    intro m
    have e : ∑ k ∈ range m, (P ^ k - W) = Z - Z * P ^ m := by
      calc ∑ k ∈ range m, (P ^ k - W) = (Z * A) * ∑ k ∈ range m, (P ^ k - W) := by rw [hZA, Matrix.one_mul]
        _ = Z * (A * ∑ k ∈ range m, (P ^ k - W)) := by rw [Matrix.mul_assoc]
        _ = Z - Z * P ^ m := by rw [hT, Matrix.mul_sub, Matrix.mul_one]
    have := congrFun (congrFun e i) j
    simpa [Matrix.sum_apply, Matrix.sub_apply, Matrix.mul_apply, hWdef, rowsMatrix] using this
  have hlim : Tendsto (fun m : ℕ => Z i j - ∑ l, Z i l * (P ^ m) l j) atTop
      (𝓝 (Z i j - ∑ l, Z i l * w j)) :=
    tendsto_const_nhds.sub (tendsto_finsetSum _ fun l _ => (hw l j).const_mul (Z i l))
  have hZWij : ∑ l, Z i l * w j = w j := by
    have := congrFun (congrFun hZW i) j
    simpa [Matrix.mul_apply, hWdef, rowsMatrix] using this
  rw [hZWij] at hlim
  exact hlim.congr fun m => (key m).symm

end Fund

/-! ## The asymptotic mean and variance -/

section Main

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- A regular chain: `w` is the limit of the rows and `1 - P + W` is invertible. -/
theorem regular_setup {P : Matrix S S ℝ} (h : IsRegularChain P) {w : S → ℝ} (hsum : ∑ j, w j = 1)
    (hfix : IsFixedRow P w) :
    (∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 (w j))) ∧ IsUnit (1 - P + rowsMatrix w) := by
  obtain ⟨w0, -, hs0, hw0⟩ := regular_pow_tendsto h
  obtain ⟨w1, -, -, hf1, huniq⟩ := regular_fixed_vector h
  have e0 : w0 = w1 := huniq w0 hs0 (isFixedRow_of_pow_tendsto (hw0 (Classical.arbitrary S)))
  have e : w = w1 := huniq w hsum hfix
  have hww : w = w0 := e.trans e0.symm
  rw [hww]
  refine ⟨hw0, ?_⟩
  obtain ⟨w2, -, hs2, hf2, hU, -⟩ := meanFirstPassage_eq_fundamental h.isErgodicChain
  have e2 : w2 = w1 := huniq w2 hs2 hf2
  have hw2 : w2 = w0 := e2.trans e0.symm
  rw [hw2] at hU
  exact hU

theorem vec_sub_eq {u : S → ℝ} (hu : ∑ i, u i = 1) (P : Matrix S S ℝ) (w : S → ℝ) (s : ℕ) (j : S) :
    (u ᵥ* P ^ s) j - w j = ∑ i, u i * ((P ^ s) i j - w j) := by
  simp only [vecMul, dotProduct, mul_sub, sum_sub_distrib, ← sum_mul, hu, one_mul]

/-- The second moment about `N w` of the number of visits, in terms of the sequences `gsym`, `csum`. -/
theorem second_moment_about {u : S → ℝ} {P : Matrix S S ℝ} (hu : ∑ i, u i = 1) (hP : P ∈ rowStochastic ℝ S)
    (w : ℝ) (j : S) (n : ℕ) :
    ∑ x : Fin (n + 1) → S, pathProb u P n x * (visits x j - ((n + 1 : ℕ) : ℝ) * w) ^ 2 =
      ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
          gsym (fun k => (u ᵥ* P ^ k) j) (fun d => (P ^ d) j j) s t
        - 2 * ((n + 1 : ℕ) : ℝ) * w * csum (fun k => (u ᵥ* P ^ k) j) (n + 1) + ((n + 1 : ℕ) : ℝ) ^ 2 * w ^ 2 := by
  have e : ∀ x : Fin (n + 1) → S, pathProb u P n x * (visits x j - ((n + 1 : ℕ) : ℝ) * w) ^ 2 =
      (pathProb u P n x * visits x j ^ 2) - (2 * ((n + 1 : ℕ) : ℝ) * w) * (pathProb u P n x * visits x j) +
        ((n + 1 : ℕ) : ℝ) ^ 2 * w ^ 2 * pathProb u P n x := by
    intro x; ring
  simp only [e]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, moment2 hP, moment1 hP, sum_pathProb hu hP n]
  ring

/-- Asymptotic mean (the mean used in the normalization of Theorem 11.17; Exercise 23 of §11.5): for a regular
chain the expected number of visits to `j` among the times `0, …, n` exceeds `(n+1) w_j` by an amount tending to
`(u (Z - W))_j`. -/
theorem markov_asymptotic_mean {P : Matrix S S ℝ} (hP : IsRegularChain P) {w : S → ℝ} (hsum : ∑ j, w j = 1)
    (hfix : IsFixedRow P w) {u : S → ℝ} (hu : ∑ i, u i = 1) (j : S) :
    Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S, pathProb u P n x * visits x j - ((n : ℝ) + 1) * w j)
      atTop (𝓝 ((u ᵥ* ((1 - P + rowsMatrix w)⁻¹ - rowsMatrix w)) j)) := by
  obtain ⟨hw, hU⟩ := regular_setup hP hsum hfix
  have hfun : ∀ n : ℕ, ∑ x : Fin (n + 1) → S, pathProb u P n x * visits x j - ((n : ℝ) + 1) * w j =
      ∑ i, u i * ∑ k ∈ range (n + 1), ((P ^ k) i j - w j) := by
    intro n
    rw [moment1 hP.1]
    have h1 : csum (fun k => (u ᵥ* P ^ k) j) (n + 1) - ((n : ℝ) + 1) * w j =
        ∑ k ∈ range (n + 1), ((u ᵥ* P ^ k) j - w j) := by
      simp only [csum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      push_cast; ring
    rw [h1]
    simp only [vec_sub_eq hu, mul_sum]
    rw [sum_comm]
  simp only [hfun]
  have := tendsto_finsetSum (univ : Finset S) fun i _ =>
    ((fundamental_partial_tendsto hP.1 hsum hfix hw hU i j).comp (tendsto_add_atTop_nat 1)).const_mul (u i)
  have hr : (u ᵥ* ((1 - P + rowsMatrix w)⁻¹ - rowsMatrix w)) j =
      ∑ c, u c * ((1 - P + rowsMatrix w)⁻¹ c j - w j) := by
    simp only [vecMul, dotProduct, Matrix.sub_apply, rowsMatrix, Matrix.of_apply]
  rw [hr]
  exact this

/-- Grinstead–Snell Theorem 11.17 (PR-121), the asymptotic variance (equation 11.10): for a regular chain with fixed
probability vector `w`, fundamental matrix `Z = (I - P + W)⁻¹` and any initial probability vector `u`, the variance of
the number `S_j^(n)` of visits to `j` among the times `0, …, n`, computed about `(n+1) w_j` and divided by `n + 1`,
tends to `σ_j² = 2 w_j z_jj - w_j - w_j²`. This is the normalization of the central limit theorem 11.17, not the
central limit theorem itself. -/
@[kb "grinsteadsnell2006" "Theorem 11.17, p. 472"]
theorem markov_asymptotic_variance {P : Matrix S S ℝ} (hP : IsRegularChain P) {w : S → ℝ}
    (hsum : ∑ j, w j = 1) (hfix : IsFixedRow P w) {u : S → ℝ} (hu : ∑ i, u i = 1) (j : S) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) *
        ∑ x : Fin (n + 1) → S, pathProb u P n x * (visits x j - ((n : ℝ) + 1) * w j) ^ 2)
      atTop (𝓝 (2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2)) := by
  obtain ⟨hw, hU⟩ := regular_setup hP hsum hfix
  obtain ⟨C, ρ, hC, hρ0, hρ1, hgeo⟩ := regular_geometric hP hw
  have hea : ∀ s, |(u ᵥ* P ^ s) j - w j| ≤ ((∑ i, |u i|) * C) * ρ ^ s := by
    intro s
    rw [vec_sub_eq hu]
    calc |∑ i, u i * ((P ^ s) i j - w j)| ≤ ∑ i, |u i * ((P ^ s) i j - w j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |u i| * (C * ρ ^ s) := by
          refine sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hgeo s i j) (abs_nonneg _)
      _ = ((∑ i, |u i|) * C) * ρ ^ s := by rw [← sum_mul, mul_assoc]
  have hH : Tendsto (fun m => csum (fun d => (P ^ d) j j - w j) m) atTop
      (𝓝 ((1 - P + rowsMatrix w)⁻¹ j j - w j)) :=
    fundamental_partial_tendsto hP.1 hsum hfix hw hU j j
  have hvar := (var_asymp (fun k => (u ᵥ* P ^ k) j) (fun d => (P ^ d) j j) (w j) _ ρ _ hρ0.le hρ1
    (by simp) hea hH).comp (tendsto_add_atTop_nat 1)
  have hz : w j ^ 2 - w j + 2 * w j * ((1 - P + rowsMatrix w)⁻¹ j j - w j) =
      2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2 := by ring
  rw [hz] at hvar
  refine hvar.congr fun n => ?_
  simp only [Function.comp]
  have h := second_moment_about hu hP.1 (w j) j n
  push_cast at h
  rw [h]
  push_cast
  rfl

end Main

end UndergradKB.Probability
