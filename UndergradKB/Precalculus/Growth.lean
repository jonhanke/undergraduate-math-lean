import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.Common.Attr

/-!
# Exponential growth and decay models (Stitz-Zeager Precalculus, Section 6.5)

Interest, uninhibited growth, decay, Newton's law of cooling and logistic growth, stated
with explicit formulas and their derivative / limit behaviour.
-/

namespace UndergradKB.Precalculus

open Real Filter Topology

/-! ### Interest -/

/-- Simple interest balance after `t` years: principal `P`, annual rate `r`. -/
noncomputable def simpleBalance (P r t : ℝ) : ℝ := P * (1 + r * t)

/-- Simple interest: the balance is `P (1 + r t)`, starts at `P`, and grows linearly, gaining
`P r` per year (PC-102). -/
@[kb "stitzzeager2013" "Equation 6.1, p. 481"]
theorem growth_simple_interest (P r : ℝ) :
    simpleBalance P r 0 = P ∧ ∀ s t : ℝ, simpleBalance P r t - simpleBalance P r s = P * r * (t - s) := by
  refine ⟨by simp [simpleBalance], fun s t => ?_⟩
  unfold simpleBalance; ring

/-- Compound interest balance after `t` years with `n` compounding periods per year. -/
noncomputable def compoundBalance (P r : ℝ) (n : ℕ) (t : ℝ) : ℝ := P * (1 + r / n) ^ ((n : ℝ) * t)

/-- Compound interest: if the balance is multiplied by `1 + r/n` each of the `n` periods per year,
after `k` periods it is `P (1 + r/n)^k`, and after `m` whole years (`n m` periods) it equals
`compoundBalance P r n m = P (1 + r/n)^(n m)` (PC-103). -/
@[kb "stitzzeager2013" "Equation 6.2, p. 482"]
theorem growth_compound_interest (P r : ℝ) (n : ℕ) (A : ℕ → ℝ) (h0 : A 0 = P)
    (hA : ∀ k, A (k + 1) = A k * (1 + r / n)) :
    (∀ k, A k = P * (1 + r / n) ^ k) ∧
    ∀ m : ℕ, compoundBalance P r n m = A (n * m) := by
  have key : ∀ k, A k = P * (1 + r / n) ^ k := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [hA, ih, pow_succ]; ring
  refine ⟨key, fun m => ?_⟩
  rw [key]
  unfold compoundBalance
  rw [← Nat.cast_mul, Real.rpow_natCast]

/-- The limit `(1 + 1/n)^n → e` as `n → ∞` (PC-104). -/
@[kb "stitzzeager2013" "Theorem 6.8, p. 483"]
theorem growth_one_plus_inv_pow_tendsto_e :
    Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp 1)) :=
  Real.tendsto_one_add_div_pow_exp 1

/-- Continuous compounding: `P (1 + r/n)^(n t) → P e^(r t)` as the number of periods `n → ∞`
(PC-105). -/
@[kb "stitzzeager2013" "Equation 6.3, p. 484"]
theorem growth_continuous_compounding (P r t : ℝ) :
    Tendsto (fun n : ℕ => compoundBalance P r n t) atTop (𝓝 (P * Real.exp (r * t))) := by
  have h1 : Tendsto (fun n : ℕ => (1 + r / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp r)) :=
    Real.tendsto_one_add_div_pow_exp r
  have h2 := h1.rpow_const (p := t) (Or.inl (Real.exp_pos r).ne')
  have h3 : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 + r / (n : ℝ) := by
    have h : Tendsto (fun n : ℕ => 1 + r / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat r).const_add 1
    exact (h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun n hn => hn.le)
  have h4 := (h2.const_mul P)
  rw [← Real.exp_mul] at h4
  refine h4.congr' ?_
  filter_upwards [h3] with n hn
  unfold compoundBalance
  rw [Real.rpow_mul hn, Real.rpow_natCast]

/-! ### Uninhibited growth and decay -/

/-- Exponential model `N(t) = N₀ e^(k t)`. -/
noncomputable def expModel (N₀ k t : ℝ) : ℝ := N₀ * Real.exp (k * t)

/-- Uninhibited growth / decay: `N(0) = N₀` and the rate of change is `k N(t)`
(PC-106). -/
@[kb "stitzzeager2013" "Equation 6.4, p. 484"]
theorem growth_exp_model_deriv (N₀ k : ℝ) :
    expModel N₀ k 0 = N₀ ∧ ∀ t, HasDerivAt (expModel N₀ k) (k * expModel N₀ k t) t := by
  refine ⟨by simp [expModel], fun t => ?_⟩
  have h := (((hasDerivAt_id' t).const_mul k).exp).const_mul N₀
  unfold expModel
  convert h using 1
  ring

/-- Radioactive decay: for `k < 0`, `A(t) = A₀ e^(k t)` has rate `k A`, starts at `A₀` and
tends to `0` as `t → ∞` (PC-107). -/
@[kb "stitzzeager2013" "Equation 6.5, p. 485"]
theorem growth_decay_model (A₀ k : ℝ) (hk : k < 0) :
    expModel A₀ k 0 = A₀ ∧ (∀ t, HasDerivAt (expModel A₀ k) (k * expModel A₀ k t) t) ∧
    Tendsto (expModel A₀ k) atTop (𝓝 0) := by
  refine ⟨(growth_exp_model_deriv A₀ k).1, (growth_exp_model_deriv A₀ k).2, ?_⟩
  have h : Tendsto (fun t : ℝ => k * t) atTop atBot := tendsto_id.const_mul_atTop_of_neg hk
  unfold expModel
  simpa using (Real.tendsto_exp_atBot.comp h).const_mul A₀

/-! ### Newton's law of cooling -/

/-- Newton's law of cooling `T(t) = Tₐ + (T₀ - Tₐ) e^(-k t)`. -/
noncomputable def coolingModel (Ta T₀ k t : ℝ) : ℝ := Ta + (T₀ - Ta) * Real.exp (-k * t)

/-- Newton's law of cooling for `k > 0`: `T(0) = T₀`, `T' = -k (T - Tₐ)`, and `T → Tₐ`
(PC-108). -/
@[kb "stitzzeager2013" "Equation 6.6, p. 486"]
theorem growth_newton_cooling (Ta T₀ k : ℝ) (hk : 0 < k) :
    coolingModel Ta T₀ k 0 = T₀ ∧
    (∀ t, HasDerivAt (coolingModel Ta T₀ k) (-k * (coolingModel Ta T₀ k t - Ta)) t) ∧
    Tendsto (coolingModel Ta T₀ k) atTop (𝓝 Ta) := by
  refine ⟨by simp [coolingModel], fun t => ?_, ?_⟩
  · have h := ((((hasDerivAt_id' t).const_mul (-k)).exp).const_mul (T₀ - Ta)).const_add Ta
    unfold coolingModel
    convert h using 1
    ring_nf
  · have h : Tendsto (fun t : ℝ => -k * t) atTop atBot := tendsto_id.const_mul_atTop_of_neg (by linarith)
    have := ((Real.tendsto_exp_atBot.comp h).const_mul (T₀ - Ta)).const_add Ta
    unfold coolingModel
    simpa using this

/-! ### Logistic growth -/

/-- Logistic model `N(t) = L / (1 + C e^(-k L t))`. -/
noncomputable def logisticPop (L k C t : ℝ) : ℝ := L / (1 + C * Real.exp (-(k * L) * t))

private lemma logistic_hasDeriv (L k C t : ℝ) (hD : 1 + C * Real.exp (-(k * L) * t) ≠ 0) :
    HasDerivAt (logisticPop L k C)
      (k * logisticPop L k C t * (L - logisticPop L k C t)) t := by
  have h1 := ((((hasDerivAt_id' t).const_mul (-(k * L))).exp).const_mul C).const_add 1
  have h2 := (h1.inv hD).const_mul L
  have hf : logisticPop L k C = fun x => L * (1 + C * Real.exp (-(k * L) * x))⁻¹ := by
    funext x; simp [logisticPop, div_eq_mul_inv]
  have h3 : HasDerivAt (logisticPop L k C)
      (L * (-(C * (Real.exp (-(k * L) * t) * (-(k * L) * 1))) /
        (1 + C * Real.exp (-(k * L) * t)) ^ 2)) t := by
    rw [hf]; exact h2
  refine h3.congr_deriv ?_
  unfold logisticPop
  generalize Real.exp (-(k * L) * t) = e at hD ⊢
  field_simp
  ring

/-- Logistic growth with `N₀ > 0`, `L > 0`, `k > 0`, `C = L/N₀ - 1`: `N(0) = N₀`,
`N' = k N (L - N)` for `t ≥ 0`, and `N → L` as `t → ∞` (PC-109). -/
@[kb "stitzzeager2013" "Equation 6.7, p. 487"]
theorem growth_logistic (N₀ L k : ℝ) (hN : 0 < N₀) (hL : 0 < L) (hk : 0 < k) :
    logisticPop L k (L / N₀ - 1) 0 = N₀ ∧
    (∀ t, 0 ≤ t → HasDerivAt (logisticPop L k (L / N₀ - 1))
      (k * logisticPop L k (L / N₀ - 1) t * (L - logisticPop L k (L / N₀ - 1) t)) t) ∧
    Tendsto (logisticPop L k (L / N₀ - 1)) atTop (𝓝 L) := by
  set C := L / N₀ - 1 with hC
  have h1C : 1 + C = L / N₀ := by rw [hC]; ring
  refine ⟨?_, fun t ht => ?_, ?_⟩
  · simp only [logisticPop, mul_zero, Real.exp_zero, mul_one, h1C]
    field_simp
  · have hpos : 0 < 1 + C * Real.exp (-(k * L) * t) := by
      have he0 : Real.exp (-(k * L) * t) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_pos hk hL]
      have he1 : 0 < Real.exp (-(k * L) * t) := Real.exp_pos _
      have hpos1 : 0 < 1 + C := by rw [h1C]; positivity
      rcases le_or_gt 0 C with hc | hc
      · positivity
      · nlinarith
    exact logistic_hasDeriv L k C t hpos.ne'
  · have h : Tendsto (fun t : ℝ => -(k * L) * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by nlinarith [mul_pos hk hL])
    have h2 := (((Real.tendsto_exp_atBot.comp h).const_mul C).const_add 1)
    have h3 : Tendsto (fun t : ℝ => L / (1 + C * Real.exp (-(k * L) * t))) atTop
        (𝓝 (L / (1 + C * 0))) := (tendsto_const_nhds (x := L)).div h2 (by simp)
    have h4 : L / (1 + C * 0) = L := by simp
    rw [h4] at h3
    exact h3

/-- First derivative of the logistic model, `k N (L - N)`. -/
noncomputable def logisticRate (L k C t : ℝ) : ℝ :=
  k * logisticPop L k C t * (L - logisticPop L k C t)

/-- Second derivative of the logistic model, `k² N (L - N)(L - 2N)`. -/
noncomputable def logisticSecond (L k C t : ℝ) : ℝ :=
  k ^ 2 * logisticPop L k C t * (L - logisticPop L k C t) * (L - 2 * logisticPop L k C t)

private lemma logistic_exp_eq (L k C t : ℝ) (hC : 0 < C) :
    C * Real.exp (-(k * L) * t) = Real.exp (Real.log C - k * L * t) := by
  rw [Real.exp_sub, Real.exp_log hC, neg_mul, Real.exp_neg, div_eq_mul_inv, ← Real.exp_neg]

private lemma logistic_second_eq (L k C t : ℝ) (hC : 0 < C) :
    logisticSecond L k C t = k ^ 2 * L ^ 3 * (C * Real.exp (-(k * L) * t)) *
      (C * Real.exp (-(k * L) * t) - 1) / (1 + C * Real.exp (-(k * L) * t)) ^ 3 := by
  have hE : 0 < C * Real.exp (-(k * L) * t) := by positivity
  unfold logisticSecond logisticPop
  field_simp
  ring

/-- Concavity switch of the logistic curve (`C > 0`): the second derivative of
`N(t) = L/(1 + C e^(-k L t))` exists (it is the derivative of `N'`), vanishes exactly at
`t₀ = ln C / (k L)`, where `N = L/2`, is positive (concave up) before `t₀` and negative
(concave down) after `t₀` (PC-110). -/
@[kb "stitzzeager2013" "§6.5, p. 489"]
theorem growth_logistic_inflection (L k C : ℝ) (hL : 0 < L) (hk : 0 < k) (hC : 0 < C) :
    (∀ t, HasDerivAt (logisticRate L k C) (logisticSecond L k C t) t) ∧
    logisticPop L k C (Real.log C / (k * L)) = L / 2 ∧
    (∀ t, logisticSecond L k C t = 0 ↔ t = Real.log C / (k * L)) ∧
    (∀ t, t < Real.log C / (k * L) → 0 < logisticSecond L k C t) ∧
    (∀ t, Real.log C / (k * L) < t → logisticSecond L k C t < 0) := by
  have hkL : 0 < k * L := mul_pos hk hL
  have hE : ∀ t, 0 < C * Real.exp (-(k * L) * t) := fun t => by positivity
  -- E > 1 iff t is left of t₀
  have hcmp : ∀ t, 1 < C * Real.exp (-(k * L) * t) ↔ t < Real.log C / (k * L) := by
    intro t
    rw [logistic_exp_eq L k C t hC, ← Real.exp_zero, Real.exp_lt_exp, lt_div_iff₀ hkL]
    constructor <;> intro h <;> nlinarith
  have hcmp' : ∀ t, C * Real.exp (-(k * L) * t) < 1 ↔ Real.log C / (k * L) < t := by
    intro t
    rw [logistic_exp_eq L k C t hC, ← Real.exp_zero, Real.exp_lt_exp, div_lt_iff₀ hkL]
    constructor <;> intro h <;> nlinarith
  have hceq : ∀ t, C * Real.exp (-(k * L) * t) = 1 ↔ t = Real.log C / (k * L) := by
    intro t
    rw [logistic_exp_eq L k C t hC, ← Real.exp_zero, Real.exp_eq_exp, eq_div_iff hkL.ne']
    constructor <;> intro h <;> linarith
  refine ⟨fun t => ?_, ?_, fun t => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have hpos : 0 < 1 + C * Real.exp (-(k * L) * t) := by linarith [hE t]
    have hN' := logistic_hasDeriv L k C t hpos.ne'
    have h3 : HasDerivAt (fun y => k * logisticPop L k C y * (L - logisticPop L k C y))
        (k * (k * logisticPop L k C t * (L - logisticPop L k C t)) * (L - logisticPop L k C t) +
          k * logisticPop L k C t * (0 - k * logisticPop L k C t * (L - logisticPop L k C t))) t :=
      (hN'.const_mul k).mul ((hasDerivAt_const t L).sub hN')
    show HasDerivAt (fun y => k * logisticPop L k C y * (L - logisticPop L k C y)) _ t
    convert h3 using 1
    unfold logisticSecond
    ring
  · unfold logisticPop
    have : Real.log C / (k * L) * (k * L) = Real.log C := div_mul_cancel₀ _ hkL.ne'
    have h1 : C * Real.exp (-(k * L) * (Real.log C / (k * L))) = 1 :=
      (hceq _).2 rfl
    rw [h1]; ring
  · rw [logistic_second_eq L k C t hC]
    have hpos : 0 < 1 + C * Real.exp (-(k * L) * t) := by linarith [hE t]
    rw [← hceq]
    constructor
    · intro h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have : k ^ 2 * L ^ 3 * (C * Real.exp (-(k * L) * t)) ≠ 0 := by positivity
        have := (mul_eq_zero.mp h).resolve_left this
        linarith
      · exact absurd h (by positivity)
    · intro h; rw [h]; simp
  · rw [logistic_second_eq L k C t hC]
    have := (hcmp t).2 ht
    have := hE t
    apply div_pos
    · apply mul_pos
      · positivity
      · linarith
    · positivity
  · rw [logistic_second_eq L k C t hC]
    have := (hcmp' t).2 ht
    have := hE t
    apply div_neg_of_neg_of_pos
    · apply mul_neg_of_pos_of_neg
      · positivity
      · linarith
    · positivity

end UndergradKB.Precalculus
