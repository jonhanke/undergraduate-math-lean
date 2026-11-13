import Mathlib.Analysis.Normed.Ring.InfiniteSum
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.Frobenius

/-! # Method of Frobenius for analytic coefficients (Lebl, *Notes on Diffy Qs*, Theorem 7.3.1)

For `x² y'' + x p(x) y' + q(x) y = 0` with `p(x) = ∑ P_k x^k`, `q(x) = ∑ Q_k x^k` convergent for `|x| < ρ`,
and a root `r` of `F(t) = t(t-1) + P₀ t + Q₀` with `F(r+k) ≠ 0` for `k ≥ 1`, the recurrence
`F(r+k) a_k = -∑_{j<k} a_j ((r+j) P_{k-j} + Q_{k-j})` gives coefficients `a_k` with `∑ a_k x^k` convergent for
`|x| < ρ`, and `y = x^r ∑ a_k x^k` solves the equation on `0 < x < ρ`.  Polynomials are the case of every `ρ`.
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology Finset

/-- The indicial polynomial `F(t) = t(t-1) + P₀ t + Q₀`. -/
noncomputable def aF (P Q : ℕ → ℝ) (t : ℝ) : ℝ := t * (t - 1) + P 0 * t + Q 0

/-- The Frobenius coefficients: `a₀ = 1`, `a_k = -(∑_{j<k} a_j ((r+j) P_{k-j} + Q_{k-j})) / F(r+k)`. -/
noncomputable def aCoef (P Q : ℕ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else
    -(∑ j : Fin k, aCoef P Q r j * ((r + ((j : ℕ) : ℝ)) * P (k - j) + Q (k - j))) / aF P Q (r + k)
termination_by k
decreasing_by exact j.2

lemma aCoef_zero (P Q : ℕ → ℝ) (r : ℝ) : aCoef P Q r 0 = 1 := by
  rw [aCoef]; simp

lemma aCoef_rec (P Q : ℕ → ℝ) (r : ℝ) {k : ℕ} (hk : k ≠ 0) (hF : aF P Q (r + k) ≠ 0) :
    aCoef P Q r k * aF P Q (r + k) =
      -∑ j ∈ range k, aCoef P Q r j * ((r + (j : ℝ)) * P (k - j) + Q (k - j)) := by
  have h : aCoef P Q r k = -(∑ j : Fin k, aCoef P Q r j * ((r + ((j : ℕ) : ℝ)) * P (k - j) + Q (k - j))) /
      aF P Q (r + k) := by
    rw [aCoef]; simp only [hk, ↓reduceIte]
  rw [h, div_mul_cancel₀ _ hF]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j => aCoef P Q r j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))) k

lemma aF_shift (P Q : ℕ → ℝ) {r : ℝ} (hr : aF P Q r = 0) (k : ℕ) :
    aF P Q (r + k) = k * (k + (2 * r - 1 + P 0)) := by
  unfold aF at *
  linear_combination hr

lemma geom_part (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (k : ℕ) :
    ∑ j ∈ range k, t ^ (k - j) ≤ (1 - t)⁻¹ := by
  have : ∑ j ∈ range k, t ^ (k - j) = ∑ j ∈ range k, t ^ (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => t ^ (j + 1)) k]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    congr 1; omega
  rw [this]
  calc _ ≤ ∑ j ∈ range k, t ^ j := Finset.sum_le_sum fun j _ => by
        rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) h1.le
    _ ≤ ∑' j, t ^ j :=
        Summable.sum_le_tsum _ (fun j _ => by positivity) (summable_geometric_of_lt_one h0 h1)
    _ = _ := tsum_geometric_of_lt_one h0 h1

lemma coeff_bdd (P : ℕ → ℝ) {ρ' : ℝ} (hρ' : 0 < ρ') (h : Summable fun k => P k * ρ' ^ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k, |P k| * ρ' ^ k ≤ M := by
  have hn : Summable fun k => ‖P k * ρ' ^ k‖ := summable_norm_iff.mpr h
  refine ⟨∑' k, ‖P k * ρ' ^ k‖, tsum_nonneg fun _ => norm_nonneg _, fun k => ?_⟩
  have := hn.le_tsum k (fun j _ => norm_nonneg _)
  rwa [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ'] at this

/-- **Majorant estimate (analytic case)**: for every `0 < σ < ρ`, `|a_k| σ^k` is bounded. -/
theorem aCoef_bound (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k)
    {r : ℝ} (hr : aF P Q r = 0) (hF : ∀ k : ℕ, 1 ≤ k → aF P Q (r + k) ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσρ : σ < ρ) : ∃ K : ℝ, ∀ k, |aCoef P Q r k| * σ ^ k ≤ K := by
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
  set C : ℝ := (M1 + M2) * G * (|r| + 2) with hC
  have hC0 : 0 ≤ C := by positivity
  obtain ⟨K0, hK0⟩ := exists_nat_ge (|s| + C + 1)
  have hs0 := abs_nonneg s
  have hr0 := abs_nonneg r
  set a := aCoef P Q r with ha
  set K : ℝ := ∑ j ∈ range (K0 + 1), |a j| * σ ^ j with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨K, fun k => ?_⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hkK : k ≤ K0
    · exact Finset.single_le_sum (f := fun j => |a j| * σ ^ j) (fun _ _ => by positivity)
        (Finset.mem_range.mpr (by omega))
    · rw [not_le] at hkK
      have hk0 : k ≠ 0 := by omega
      have hkR : (K0 : ℝ) + 1 ≤ k := by exact_mod_cast hkK
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hF' := hF k (by omega)
      have hrec := aCoef_rec P Q r hk0 hF'
      have hpos : 0 < |aF P Q (r + k)| := abs_pos.mpr hF'
      have hterm : ∀ j ∈ range k, |a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k ≤
          K * ((|r| + k + 1) * (M1 + M2) * t ^ (k - j)) := by
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hjR : (j : ℝ) ≤ k := by exact_mod_cast hjk.le
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
        have hσk : σ ^ k = σ ^ j * σ ^ (k - j) := by rw [← pow_add]; congr 1; omega
        have h1 : |a j| * σ ^ j ≤ K := ih j hjk
        have hw : 0 ≤ t ^ (k - j) := by positivity
        have h2 : |(r + (j : ℝ)) * P (k - j) + Q (k - j)| * σ ^ (k - j) ≤
            (|r| + k + 1) * (M1 + M2) * t ^ (k - j) := by
          have hrj : |r + (j : ℝ)| ≤ |r| + k :=
            (abs_add_le _ _).trans (by rw [abs_of_nonneg hj0]; linarith)
          have e1 := hPt (k - j)
          have e2 := hQt (k - j)
          have a1 : |(r + (j : ℝ)) * P (k - j) + Q (k - j)| ≤ (|r| + k) * |P (k - j)| + |Q (k - j)| :=
            (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
          have sp := σ ^ (k - j)
          have hσp : 0 ≤ σ ^ (k - j) := by positivity
          calc _ ≤ ((|r| + k) * |P (k - j)| + |Q (k - j)|) * σ ^ (k - j) := by gcongr
            _ = (|r| + k) * (|P (k - j)| * σ ^ (k - j)) + |Q (k - j)| * σ ^ (k - j) := by ring
            _ ≤ (|r| + k) * (M1 * t ^ (k - j)) + M2 * t ^ (k - j) := by gcongr
            _ ≤ _ := by
              have : 0 ≤ (|r| + k) * M2 * t ^ (k - j) + M1 * t ^ (k - j) := by positivity
              nlinarith
        rw [abs_mul, hσk]
        calc |a j| * |(r + (j : ℝ)) * P (k - j) + Q (k - j)| * (σ ^ j * σ ^ (k - j))
            = (|a j| * σ ^ j) * (|(r + (j : ℝ)) * P (k - j) + Q (k - j)| * σ ^ (k - j)) := by ring
          _ ≤ K * ((|r| + k + 1) * (M1 + M2) * t ^ (k - j)) := by
              apply mul_le_mul h1 h2 (by positivity) hK
      have hsum : |∑ j ∈ range k, a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k ≤
          K * ((|r| + k + 1) * (M1 + M2) * G) := by
        have hσk0 : 0 ≤ σ ^ k := by positivity
        calc _ ≤ (∑ j ∈ range k, |a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))|) * σ ^ k := by
              gcongr; exact Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j ∈ range k, |a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ j ∈ range k, K * ((|r| + k + 1) * (M1 + M2) * t ^ (k - j)) :=
              Finset.sum_le_sum hterm
          _ = K * ((|r| + k + 1) * (M1 + M2)) * ∑ j ∈ range k, t ^ (k - j) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
          _ ≤ K * ((|r| + k + 1) * (M1 + M2)) * G := by
              gcongr; exact geom_part t ht0 ht1 k
          _ = _ := by ring
      have hlow : (|r| + k + 1) * (M1 + M2) * G ≤ |aF P Q (r + k)| := by
        have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have h1 : (k : ℝ) - |s| ≤ |(k : ℝ) + s| := by
          have := abs_sub_abs_le_abs_sub (k : ℝ) (-s)
          rw [abs_neg, sub_neg_eq_add, abs_of_nonneg hk'] at this
          exact this
        have h2 : |aF P Q (r + k)| = k * |(k : ℝ) + s| := by
          rw [aF_shift P Q hr, abs_mul, abs_of_nonneg hk']
        rw [h2]
        have h3 : C ≤ |(k : ℝ) + s| := by linarith
        calc (|r| + k + 1) * (M1 + M2) * G ≤ ((|r| + 2) * k) * (M1 + M2) * G := by
              have : |r| + k + 1 ≤ (|r| + 2) * k := by nlinarith
              gcongr
          _ = k * C := by rw [hC]; ring
          _ ≤ k * |(k : ℝ) + s| := by gcongr
      have h5 : |a k| * σ ^ k * |aF P Q (r + k)| ≤ K * |aF P Q (r + k)| := by
        have e : |a k| * σ ^ k * |aF P Q (r + k)| =
            |∑ j ∈ range k, a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))| * σ ^ k := by
          rw [mul_right_comm, ← abs_mul, hrec, abs_neg]
        rw [e]
        refine hsum.trans ?_
        exact mul_le_mul_of_nonneg_left hlow hK
      exact le_of_mul_le_mul_right h5 hpos

/-! ### Power series on `|x| < ρ` with locally geometric coefficient bounds -/

/-- Around every `x` with `|x| < ρ`, the coefficients satisfy `|a_k| ρ₂^k ≤ K t^k` for some
`ρ₂ > |x|` and `t < 1`. -/
def LocGeo (a : ℕ → ℝ) (ρ : ℝ) : Prop :=
  ∀ x : ℝ, |x| < ρ → ∃ ρ2 t K : ℝ, 0 < ρ2 ∧ |x| < ρ2 ∧ 0 ≤ t ∧ t < 1 ∧
    ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k

lemma locGeo_of_bound {a : ℕ → ℝ} {ρ : ℝ}
    (h : ∀ σ : ℝ, 0 < σ → σ < ρ → ∃ K : ℝ, ∀ k, |a k| * σ ^ k ≤ K) : LocGeo a ρ := by
  intro x hx
  have hρ : 0 < ρ := lt_of_le_of_lt (abs_nonneg _) hx
  have hx0 := abs_nonneg x
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = (|x| + ρ) / 2 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  obtain ⟨K, hK⟩ := h σ hσ0 (by linarith)
  obtain ⟨ρ2, hρ2⟩ : ∃ ρ2 : ℝ, ρ2 = (|x| + σ) / 2 := ⟨_, rfl⟩
  have hρ20 : 0 < ρ2 := by rw [hρ2]; positivity
  refine ⟨ρ2, ρ2 / σ, K, hρ20, by linarith, by positivity, (div_lt_one hσ0).mpr (by linarith),
    fun k => ?_⟩
  have hσk : σ ^ k ≠ 0 := pow_ne_zero k hσ0.ne'
  calc |a k| * ρ2 ^ k = (|a k| * σ ^ k) * (ρ2 / σ) ^ k := by
        rw [div_pow, mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hσk]
    _ ≤ K * (ρ2 / σ) ^ k := by gcongr; exact hK k

section GBounds

variable {a : ℕ → ℝ} {K ρ2 t : ℝ}

lemma gb0 (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k) {y : ℝ} (hy : |y| ≤ ρ2) (k : ℕ) :
    ‖a k * y ^ k‖ ≤ K * t ^ k := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy k) (abs_nonneg _)).trans (hB k)

lemma gb1 (hρ2 : 0 < ρ2) (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k) {y : ℝ} (hy : |y| ≤ ρ2) (k : ℕ) :
    ‖a k * ((k : ℝ) * y ^ (k - 1))‖ ≤ K / ρ2 * ((k : ℝ) * t ^ k) := by
  cases k with
  | zero => simp
  | succ j =>
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, Nat.add_sub_cancel]
    have key := hB (j + 1)
    have hyj : |y| ^ j ≤ ρ2 ^ j := pow_le_pow_left₀ (abs_nonneg _) hy j
    have hj : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc |a (j + 1)| * (((j + 1 : ℕ) : ℝ) * |y| ^ j) ≤ |a (j + 1)| * (((j + 1 : ℕ) : ℝ) * ρ2 ^ j) := by
          gcongr
      _ = (|a (j + 1)| * ρ2 ^ (j + 1)) * ((j + 1 : ℕ) : ℝ) / ρ2 := by rw [pow_succ]; field_simp
      _ ≤ (K * t ^ (j + 1)) * ((j + 1 : ℕ) : ℝ) / ρ2 := by gcongr
      _ = _ := by ring

lemma gb2 (hρ2 : 0 < ρ2) (ht0 : 0 ≤ t) (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k) {y : ℝ} (hy : |y| ≤ ρ2)
    (k : ℕ) :
    ‖a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * y ^ (k - 1 - 1)))‖ ≤ K / ρ2 ^ 2 * ((k : ℝ) ^ 2 * t ^ k) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (by simpa using hB 0)
  rcases k with _ | _ | i
  · simp
  · simp; positivity
  · simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, Nat.add_sub_cancel]
    have key := hB (i + 1 + 1)
    have hyj : |y| ^ i ≤ ρ2 ^ i := pow_le_pow_left₀ (abs_nonneg _) hy i
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have h1 : ((i + 1 + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * |y| ^ i) ≤
        ((i + 1 + 1 : ℕ) : ℝ) ^ 2 * ρ2 ^ i := by
      push_cast
      have : ((i : ℝ) + 1) * |y| ^ i ≤ ((i : ℝ) + 1 + 1) * ρ2 ^ i :=
        mul_le_mul (by linarith) hyj (by positivity) (by linarith)
      calc ((i : ℝ) + 1 + 1) * (((i : ℝ) + 1) * |y| ^ i) ≤ ((i : ℝ) + 1 + 1) * (((i : ℝ) + 1 + 1) * ρ2 ^ i) :=
            mul_le_mul_of_nonneg_left this (by linarith)
        _ = _ := by ring
    calc |a (i + 1 + 1)| * (((i + 1 + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * |y| ^ i))
        ≤ |a (i + 1 + 1)| * (((i + 1 + 1 : ℕ) : ℝ) ^ 2 * ρ2 ^ i) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (|a (i + 1 + 1)| * ρ2 ^ (i + 1 + 1)) * ((i + 1 + 1 : ℕ) : ℝ) ^ 2 / ρ2 ^ 2 := by
          rw [pow_succ, pow_succ]; field_simp; ring
      _ ≤ (K * t ^ (i + 1 + 1)) * ((i + 1 + 1 : ℕ) : ℝ) ^ 2 / ρ2 ^ 2 := by gcongr
      _ = _ := by ring

lemma gsum0 (ht0 : 0 ≤ t) (ht1 : t < 1) (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k) {y : ℝ}
    (hy : |y| ≤ ρ2) : Summable fun k => a k * y ^ k :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ht0 ht1).mul_left K) (gb0 hB hy)

lemma gsum1 (hρ2 : 0 < ρ2) (ht0 : 0 ≤ t) (ht1 : t < 1) (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k)
    {y : ℝ} (hy : |y| ≤ ρ2) : Summable fun k => a k * ((k : ℝ) * y ^ (k - 1)) := by
  have := (geo_summable ht0 ht1 1).mul_left (K / ρ2)
  simp only [pow_one] at this
  exact Summable.of_norm_bounded this (gb1 hρ2 hB hy)

lemma gsum2 (hρ2 : 0 < ρ2) (ht0 : 0 ≤ t) (ht1 : t < 1) (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k)
    {y : ℝ} (hy : |y| ≤ ρ2) :
    Summable fun k => a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * y ^ (k - 1 - 1))) :=
  Summable.of_norm_bounded ((geo_summable ht0 ht1 2).mul_left (K / ρ2 ^ 2)) (gb2 hρ2 ht0 hB hy)

theorem hasDerivAt_gS0 (hρ2 : 0 < ρ2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k) {x : ℝ} (hx : |x| < ρ2) :
    HasDerivAt (fS0 a) (fS1 a x) x := by
  have hmem : x ∈ Metric.ball (0 : ℝ) ρ2 := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]; exact hx
  have hu := (geo_summable ht0 ht1 1).mul_left (K / ρ2)
  simp only [pow_one] at hu
  exact hasDerivAt_tsum_of_isPreconnected (g := fun n z => a n * z ^ n)
    (g' := fun n z => a n * ((n : ℝ) * z ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) _).isPreconnected
    (fun n z _ => (hasDerivAt_pow n z).const_mul (a n))
    (fun n z hz => gb1 hρ2 hB (by rw [mem_ball_zero_iff, Real.norm_eq_abs] at hz; exact hz.le) n)
    hmem (gsum0 ht0 ht1 hB hx.le) hmem

theorem hasDerivAt_gS1 (hρ2 : 0 < ρ2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hB : ∀ k, |a k| * ρ2 ^ k ≤ K * t ^ k) {x : ℝ} (hx : |x| < ρ2) :
    HasDerivAt (fS1 a) (fS2 a x) x := by
  have hmem : x ∈ Metric.ball (0 : ℝ) ρ2 := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]; exact hx
  exact hasDerivAt_tsum_of_isPreconnected (g := fun n z => a n * ((n : ℝ) * z ^ (n - 1)))
    (g' := fun n z => a n * ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * z ^ (n - 1 - 1))))
    ((geo_summable ht0 ht1 2).mul_left (K / ρ2 ^ 2)) Metric.isOpen_ball
    (convex_ball (0 : ℝ) _).isPreconnected
    (fun n z _ => ((hasDerivAt_pow (n - 1) z).const_mul (n : ℝ)).const_mul (a n))
    (fun n z hz => gb2 hρ2 ht0 hB (by rw [mem_ball_zero_iff, Real.norm_eq_abs] at hz; exact hz.le) n)
    hmem (gsum1 hρ2 ht0 ht1 hB hx.le) hmem

end GBounds

lemma LocGeo.deriv0 {a : ℕ → ℝ} {ρ : ℝ} (h : LocGeo a ρ) {x : ℝ} (hx : |x| < ρ) :
    HasDerivAt (fS0 a) (fS1 a x) x := by
  obtain ⟨ρ2, t, K, h0, h1, h2, h3, hB⟩ := h x hx
  exact hasDerivAt_gS0 h0 h2 h3 hB h1

lemma LocGeo.deriv1 {a : ℕ → ℝ} {ρ : ℝ} (h : LocGeo a ρ) {x : ℝ} (hx : |x| < ρ) :
    HasDerivAt (fS1 a) (fS2 a x) x := by
  obtain ⟨ρ2, t, K, h0, h1, h2, h3, hB⟩ := h x hx
  exact hasDerivAt_gS1 h0 h2 h3 hB h1

lemma LocGeo.summable {a : ℕ → ℝ} {ρ : ℝ} (h : LocGeo a ρ) {x : ℝ} (hx : |x| < ρ) :
    Summable fun k => a k * x ^ k := by
  obtain ⟨ρ2, t, K, h0, h1, h2, h3, hB⟩ := h x hx
  exact gsum0 h2 h3 hB h1.le

/-! ### Cauchy product with the coefficient series -/

lemma cauchy_hasSum (c P : ℕ → ℝ) {x : ℝ} (hc : Summable fun j => c j * x ^ j)
    (hP : Summable fun i => P i * x ^ i) :
    HasSum (fun m => (∑ j ∈ range (m + 1), c j * P (m - j)) * x ^ m)
      ((∑' j, c j * x ^ j) * ∑' i, P i * x ^ i) := by
  have hc' : Summable fun j => ‖c j * x ^ j‖ := summable_norm_iff.mpr hc
  have hP' : Summable fun i => ‖P i * x ^ i‖ := summable_norm_iff.mpr hP
  have hterm : ∀ m : ℕ, ∑ j ∈ range (m + 1), (c j * x ^ j) * (P (m - j) * x ^ (m - j)) =
      (∑ j ∈ range (m + 1), c j * P (m - j)) * x ^ m := by
    intro m
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≤ m := by have := Finset.mem_range.mp hj; omega
    have hx : x ^ m = x ^ j * x ^ (m - j) := by rw [← pow_add]; congr 1; omega
    rw [hx]; ring
  have hs := (summable_norm_sum_mul_range_of_summable_norm hc' hP').of_norm
  have e2 : (∑' j, c j * x ^ j) * ∑' i, P i * x ^ i =
      ∑' m, ∑ j ∈ range (m + 1), (c j * x ^ j) * (P (m - j) * x ^ (m - j)) := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hc' hP']
    exact tsum_congr fun m =>
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => (c k * x ^ k) * (P l * x ^ l)) m
  simp_rw [hterm] at hs e2
  rw [e2]
  exact hs.hasSum

/-! ### The differential equation -/

/-- The coefficient identity of the recurrence. -/
def FrobCoefId (P Q : ℕ → ℝ) (r : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, a m * ((r + m) * (r + m - 1)) +
    ∑ j ∈ range (m + 1), a j * ((r + (j : ℝ)) * P (m - j) + Q (m - j)) = 0

lemma gen_series_eq (P Q : ℕ → ℝ) {ρ : ℝ} (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r : ℝ} {a : ℕ → ℝ}
    (h : LocGeo a ρ) (hcoef : FrobCoefId P Q r a) {x : ℝ} (hx : |x| < ρ) :
    x ^ 2 * fS2 a x + (2 * r + ∑' k, P k * x ^ k) * (x * fS1 a x) +
      (r * (r - 1) + r * (∑' k, P k * x ^ k) + ∑' k, Q k * x ^ k) * fS0 a x = 0 := by
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
      (∑ j ∈ range (m + 1), a j * Q (m - j)) * x ^ m) = fun _ => 0 := by
    funext m
    have hm := hcoef m
    have hc : (∑ j ∈ range (m + 1), (fun j => a j * (r + (j : ℝ))) j * P (m - j)) +
        (∑ j ∈ range (m + 1), a j * Q (m - j)) =
        ∑ j ∈ range (m + 1), a j * ((r + (j : ℝ)) * P (m - j) + Q (m - j)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    calc _ = (a m * ((r + m) * (r + m - 1)) + ((∑ j ∈ range (m + 1), (fun j => a j * (r + (j : ℝ))) j * P (m - j)) +
        (∑ j ∈ range (m + 1), a j * Q (m - j)))) * x ^ m := by ring
      _ = 0 := by rw [hc, hm, zero_mul]
  rw [hz] at Htot
  have h0' := Htot.unique hasSum_zero
  unfold fS0 at *
  linear_combination h0'

/-- `∑ P_k x^k` as the coefficient function. -/
noncomputable def psum (P : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, P k * x ^ k

theorem gen_frob_ode (P Q : ℕ → ℝ) {ρ : ℝ} (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r : ℝ} {a : ℕ → ℝ}
    (h : LocGeo a ρ) (hcoef : FrobCoefId P Q r a) {x : ℝ} (hx0 : 0 < x) (hxρ : x < ρ) :
    x ^ 2 * deriv (deriv (frobY a r)) x + x * psum P x * deriv (frobY a r) x +
      psum Q x * frobY a r x = 0 := by
  have hab : ∀ z : ℝ, 0 < z → z < ρ → |z| < ρ := fun z h0 h1 => by rw [abs_of_pos h0]; exact h1
  have hd1 : ∀ z : ℝ, 0 < z → z < ρ → HasDerivAt (frobY a r) (frobY1 a r z) z := fun z h0 h1 =>
    (hasDerivAt_rpow_div r z h0).mul (h.deriv0 (hab z h0 h1))
  have hd1' : deriv (frobY a r) =ᶠ[𝓝 x] frobY1 a r := by
    filter_upwards [Ioo_mem_nhds hx0 hxρ] with z hz using (hd1 z hz.1 hz.2).deriv
  have hd2 : HasDerivAt (frobY1 a r) (frobY2 a r x) x :=
    ((hasDerivAt_rpow_div2 r x hx0).mul (h.deriv0 (hab x hx0 hxρ))).add
      ((hasDerivAt_rpow_div r x hx0).mul (h.deriv1 (hab x hx0 hxρ)))
  rw [hd1'.deriv_eq, hd2.deriv, (hd1 x hx0 hxρ).deriv]
  have E := gen_series_eq P Q hP hQ h hcoef (hab x hx0 hxρ)
  unfold frobY1 frobY2 frobY psum
  have key : ∀ S S1 S2 u pp qq : ℝ,
      x ^ 2 * S2 + (2 * r + pp) * (x * S1) + (r * (r - 1) + r * pp + qq) * S = 0 →
      x ^ 2 * (r * (r - 1) * u / x ^ 2 * S + r * u / x * S1 + (r * u / x * S1 + u * S2)) +
        x * pp * (r * u / x * S + u * S1) + qq * (u * S) = 0 := by
    intro S S1 S2 u pp qq hh
    have hx : x ≠ 0 := hx0.ne'
    have : x ^ 2 * (r * (r - 1) * u / x ^ 2 * S + r * u / x * S1 + (r * u / x * S1 + u * S2)) +
        x * pp * (r * u / x * S + u * S1) + qq * (u * S) =
        u * (x ^ 2 * S2 + (2 * r + pp) * (x * S1) + (r * (r - 1) + r * pp + qq) * S) := by
      field_simp
      ring
    rw [this, hh, mul_zero]
  exact key _ _ _ _ _ _ E

/-- The recurrence implies the coefficient identity. -/
lemma aCoef_id (P Q : ℕ → ℝ) {r : ℝ} (hr : aF P Q r = 0) (hF : ∀ k : ℕ, 1 ≤ k → aF P Q (r + k) ≠ 0) :
    FrobCoefId P Q r (aCoef P Q r) := by
  intro m
  have hrec : aCoef P Q r m * aF P Q (r + m) =
      -∑ j ∈ range m, aCoef P Q r j * ((r + (j : ℝ)) * P (m - j) + Q (m - j)) := by
    by_cases hm : m = 0
    · subst hm
      simp [hr]
    · exact aCoef_rec P Q r hm (hF m (Nat.one_le_iff_ne_zero.mpr hm))
  rw [Finset.sum_range_succ, Nat.sub_self]
  unfold aF at hrec
  linear_combination hrec

lemma aCoef_locGeo (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k)
    {r : ℝ} (hr : aF P Q r = 0) (hF : ∀ k : ℕ, 1 ≤ k → aF P Q (r + k) ≠ 0) :
    LocGeo (aCoef P Q r) ρ :=
  locGeo_of_bound fun _ hσ hσρ => aCoef_bound P Q hρ hP hQ hr hF hσ hσρ

lemma LocGeo.exists_ne_zero {a : ℕ → ℝ} {ρ : ℝ} (h : LocGeo a ρ) (hρ : 0 < ρ) (ha : a 0 = 1) :
    ∃ z : ℝ, 0 < z ∧ z < ρ ∧ fS0 a z ≠ 0 := by
  have hc := (h.deriv0 (by simpa using hρ : |(0 : ℝ)| < ρ)).continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  set z : ℝ := min (δ / 2) (ρ / 2) with hz
  have hz0 : 0 < z := lt_min (by positivity) (by positivity)
  have hz1 : z < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hzδ : dist z 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hz0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 := hδ' hzδ
  rw [Real.dist_eq, fS0_zero, ha] at h1
  refine ⟨z, hz0, hz1, fun h0 => ?_⟩
  rw [h0] at h1
  norm_num [abs_of_neg] at h1

/-- **Method of Frobenius** (Lebl, Theorem 7.3.1; DE-207).  Let `p(x) = ∑ P_k x^k` and `q(x) = ∑ Q_k x^k` converge
for `|x| < ρ` (`ρ > 0`), and let `r` be a root of the indicial equation `r(r-1) + P₀ r + Q₀ = 0` such that
`F(r+k) ≠ 0` for every integer `k ≥ 1` (this holds for the larger real root).  Then there are coefficients
`a₀ = 1`, `a_k F(r+k) = -∑_{j<k} a_j ((r+j) P_{k-j} + Q_{k-j})`, with `∑ a_k x^k` convergent for `|x| < ρ`, such
that `y = x^r ∑ a_k x^k` solves `x² y'' + x p(x) y' + q(x) y = 0` on `0 < x < ρ` and is not identically zero
there.  (Regularity of the singular point: for polynomial coefficients see `frob_regularSingPt`; here the
equation is stated in the Frobenius normal form.) -/
@[kb "lebldiffyqs2026" "Theorem 7.3.1, p. 345"]
theorem frobenius_analytic (P Q : ℕ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hP : ∀ x : ℝ, |x| < ρ → Summable fun k => P k * x ^ k)
    (hQ : ∀ x : ℝ, |x| < ρ → Summable fun k => Q k * x ^ k) {r : ℝ}
    (hr : r * (r - 1) + P 0 * r + Q 0 = 0)
    (hF : ∀ k : ℕ, 1 ≤ k → (r + k) * (r + k - 1) + P 0 * (r + k) + Q 0 ≠ 0) :
    ∃ a : ℕ → ℝ, a 0 = 1 ∧ (∀ x : ℝ, |x| < ρ → Summable fun k => a k * x ^ k) ∧
      (∀ k : ℕ, 1 ≤ k → a k * ((r + k) * (r + k - 1) + P 0 * (r + k) + Q 0) =
        -∑ j ∈ range k, a j * ((r + (j : ℝ)) * P (k - j) + Q (k - j))) ∧
      (∀ x : ℝ, 0 < x → x < ρ →
        x ^ 2 * deriv (deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k)) x +
          x * (∑' k, P k * x ^ k) * deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k) x +
          (∑' k, Q k * x ^ k) * (x ^ r * ∑' k, a k * x ^ k) = 0) ∧
      ∃ x : ℝ, 0 < x ∧ x < ρ ∧ x ^ r * ∑' k, a k * x ^ k ≠ 0 := by
  have hr' : aF P Q r = 0 := hr
  have hF' : ∀ k : ℕ, 1 ≤ k → aF P Q (r + k) ≠ 0 := hF
  have hL := aCoef_locGeo P Q hρ hP hQ hr' hF'
  have hid := aCoef_id P Q hr' hF'
  refine ⟨aCoef P Q r, aCoef_zero P Q r, fun x hx => hL.summable hx,
    fun k hk => aCoef_rec P Q r (by omega) (hF' k hk), fun x hx0 hxρ => ?_, ?_⟩
  · exact gen_frob_ode P Q hP hQ hL hid hx0 hxρ
  · obtain ⟨z, hz0, hz1, hne⟩ := hL.exists_ne_zero hρ (aCoef_zero P Q r)
    exact ⟨z, hz0, hz1, mul_ne_zero (Real.rpow_pos_of_pos hz0 r).ne' hne⟩

/-- **Method of Frobenius for polynomial coefficients on the whole half line** (DE-207, polynomial case with
`ρ = ∞`): for polynomials `p`, `q` and a root `r` of the indicial polynomial with `F(r+k) ≠ 0` for `k ≥ 1`,
the series `∑ a_k x^k` converges for every real `x` and `y = x^r ∑ a_k x^k` solves
`x² y'' + x p(x) y' + q(x) y = 0` on all of `0 < x < ∞` (this removes the restriction to `x < 1` of
`frobenius_exists`). -/
theorem frobenius_poly_full (p q : Polynomial ℝ) {r : ℝ} (hr : indF p q r = 0)
    (hF : ∀ k : ℕ, 1 ≤ k → indF p q (r + k) ≠ 0) :
    ∃ a : ℕ → ℝ, a 0 = 1 ∧ (∀ x : ℝ, Summable fun k => a k * x ^ k) ∧
      (∀ k : ℕ, 1 ≤ k → a k * indF p q (r + k) =
        -∑ j ∈ range k, a j * ((r + (j : ℝ)) * p.coeff (k - j) + q.coeff (k - j))) ∧
      (∀ x : ℝ, 0 < x →
        x ^ 2 * deriv (deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k)) x +
          x * p.eval x * deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k) x +
          q.eval x * (x ^ r * ∑' k, a k * x ^ k) = 0) ∧
      ∃ x : ℝ, 0 < x ∧ x ^ r * ∑' k, a k * x ^ k ≠ 0 := by
  have hpoly : ∀ (R : Polynomial ℝ) (x : ℝ), Summable (fun k => R.coeff k * x ^ k) ∧
      ∑' k, R.coeff k * x ^ k = R.eval x := by
    intro R x
    have hz : ∀ k ∉ Finset.range (R.natDegree + 1), R.coeff k * x ^ k = 0 := fun k hk => by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hk), zero_mul]
    exact ⟨summable_of_ne_finset_zero hz, by
      rw [tsum_eq_sum hz, Polynomial.eval_eq_sum_range]⟩
  have hr' : aF p.coeff q.coeff r = 0 := hr
  have hF' : ∀ k : ℕ, 1 ≤ k → aF p.coeff q.coeff (r + k) ≠ 0 := hF
  have hid := aCoef_id p.coeff q.coeff hr' hF'
  have hL : ∀ ρ : ℝ, 0 < ρ → LocGeo (aCoef p.coeff q.coeff r) ρ := fun ρ hρ =>
    aCoef_locGeo p.coeff q.coeff hρ (fun x _ => (hpoly p x).1) (fun x _ => (hpoly q x).1) hr' hF'
  refine ⟨aCoef p.coeff q.coeff r, aCoef_zero _ _ r, fun x => (hL (|x| + 1) (by positivity)).summable
      (by linarith),
    fun k hk => aCoef_rec p.coeff q.coeff r (by omega) (hF' k hk), fun x hx0 => ?_, ?_⟩
  · have hxρ : x < |x| + 1 := by rw [abs_of_pos hx0]; linarith
    have := gen_frob_ode p.coeff q.coeff (fun x _ => (hpoly p x).1) (fun x _ => (hpoly q x).1)
      (hL (|x| + 1) (by positivity)) hid hx0 hxρ
    unfold psum at this
    rw [(hpoly p x).2, (hpoly q x).2] at this
    exact this
  · obtain ⟨z, hz0, hz1, hne⟩ := (hL 1 one_pos).exists_ne_zero one_pos (aCoef_zero _ _ r)
    exact ⟨z, hz0, mul_ne_zero (Real.rpow_pos_of_pos hz0 r).ne' hne⟩

end UndergradKB.DifferentialEquations

