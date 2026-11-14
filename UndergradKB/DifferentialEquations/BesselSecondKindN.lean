import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.BesselSeries
import UndergradKB.DifferentialEquations.SecondOrderLinear
import UndergradKB.DifferentialEquations.BesselSecondKind
import UndergradKB.DifferentialEquations.FrobeniusSecond

/-! # Bessel function of the second kind, integer order `n ≥ 1` (Lebl, *Notes on Diffy Qs*, §7.3.3)

Bessel's equation `x² y'' + x y' + (x² - n²) y = 0` is the Frobenius form with `p = 1` and `q = x² - n²`, whose
indicial roots are `n` and `-n`, differing by the integer `N = 2n`.  The second Frobenius solution
`y₂ = x^{-n} ∑ b_k x^k + C (ln x) x^n ∑ a_k x^k` (`b₀ = 1`) from `frobenius_second_core_entire` therefore solves
the equation on `(0, ∞)`; `x^n y₂(x) → 1`, so `Y = -y₂ → -∞` at `0⁺`, while `J_n → 0`.  Hence every solution on
`(0, ∞)` is `A J_n + B Y`.

`Y` here is a second solution with the book's properties; it is not the standard normalization of `Y_n` (the book
defines `Y_n` as a limit of combinations of `J_p` and `J_{-p}` as `p → n`; that limit is not formalized).
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology Finset

/-- Coefficients of `p(x) = 1`. -/
def besselPc (k : ℕ) : ℝ := if k = 0 then 1 else 0

/-- Coefficients of `q(x) = x² - n²`. -/
def besselQc (n : ℕ) (k : ℕ) : ℝ := if k = 0 then -(n : ℝ) ^ 2 else if k = 2 then 1 else 0

lemma besselPc_summable (x : ℝ) : Summable fun k => besselPc k * x ^ k :=
  summable_of_ne_finset_zero (s := Finset.range 1) (fun k hk => by
    have : k ≠ 0 := by simpa using hk
    simp [besselPc, this])

lemma besselQc_summable (n : ℕ) (x : ℝ) : Summable fun k => besselQc n k * x ^ k :=
  summable_of_ne_finset_zero (s := Finset.range 3) (fun k hk => by
    have h1 : k ≠ 0 := by simp at hk; omega
    have h2 : k ≠ 2 := by simp at hk; omega
    simp [besselQc, h1, h2])

lemma besselPc_psum (x : ℝ) : psum besselPc x = 1 := by
  unfold psum
  rw [tsum_eq_single 0]
  · simp [besselPc]
  · intro k hk; simp [besselPc, hk]

lemma besselQc_psum (n : ℕ) (x : ℝ) : psum (besselQc n) x = x ^ 2 - (n : ℝ) ^ 2 := by
  unfold psum
  rw [tsum_eq_sum (s := Finset.range 3) (fun k hk => by
    have h1 : k ≠ 0 := by simp at hk; omega
    have h2 : k ≠ 2 := by simp at hk; omega
    simp [besselQc, h1, h2])]
  simp [Finset.sum_range_succ, besselQc]
  ring

/-- The Frobenius coefficients `a_k` (for the root `n`). -/
noncomputable def bsA (n : ℕ) : ℕ → ℝ := aCoef besselPc (besselQc n) (n : ℝ)

/-- The coefficients `b_k` of the second solution (for the root `-n`, `N = 2n`). -/
noncomputable def bsB (n : ℕ) : ℕ → ℝ :=
  logB besselPc (besselQc n) (-(n : ℝ)) (2 * n) (dCoef besselPc (n : ℝ) (bsA n))

/-- The constant `C` of the second solution. -/
noncomputable def bsC (n : ℕ) : ℝ :=
  logC besselPc (besselQc n) (-(n : ℝ)) (2 * n) (dCoef besselPc (n : ℝ) (bsA n))

/-- The second Frobenius solution `y₂` of Bessel's equation of order `n`. -/
noncomputable def besselY2n (n : ℕ) : ℝ → ℝ := frobLogY (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n)

lemma bs_core (n : ℕ) (hn : 1 ≤ n) :
    (∀ ρ : ℝ, 0 < ρ → LocGeo (bsA n) ρ ∧ LocGeo (bsB n) ρ) ∧ bsA n 0 = 1 ∧ bsB n 0 = 1 ∧
      (∀ x : ℝ, 0 < x →
        x ^ 2 * deriv (deriv (besselY2n n)) x + x * psum besselPc x * deriv (besselY2n n) x +
          psum (besselQc n) x * besselY2n n x = 0) := by
  have hsum : (n : ℝ) + -(n : ℝ) = 1 - besselPc 0 := by simp [besselPc]
  have hprod : (n : ℝ) * -(n : ℝ) = besselQc n 0 := by simp [besselQc]; ring
  have hN : (n : ℝ) = -(n : ℝ) + ((2 * n : ℕ) : ℝ) := by push_cast; ring
  have core := frobenius_second_core_entire besselPc (besselQc n) besselPc_summable
    (besselQc_summable n) hsum hprod hN
  obtain ⟨h1, h2, -, h4, -, h6, -⟩ := core
  exact ⟨h1, h2, h4 (by omega), h6⟩

/-- Packaging: derivatives given by `HasDerivAt` and the ODE give the derived form. -/
lemma deriv_form_of_hasDeriv (n : ℕ) {f f1 f2 : ℝ → ℝ}
    (h1 : ∀ x, 0 < x → HasDerivAt f (f1 x) x) (h2 : ∀ x, 0 < x → HasDerivAt f1 (f2 x) x)
    (h3 : ∀ x, 0 < x → x ^ 2 * f2 x + x * f1 x + (x ^ 2 - (n : ℝ) ^ 2) * f x = 0) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ (deriv f) x ∧
      x ^ 2 * deriv (deriv f) x + x * deriv f x + (x ^ 2 - (n : ℝ) ^ 2) * f x = 0 := by
  intro x hx
  have hd : deriv f =ᶠ[𝓝 x] f1 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using (h1 y hy).deriv
  have hdd : HasDerivAt (deriv f) (f2 x) x := (h2 x hx).congr_of_eventuallyEq hd
  refine ⟨(h1 x hx).differentiableAt, hdd.differentiableAt, ?_⟩
  rw [hdd.deriv, (h1 x hx).deriv]
  exact h3 x hx

/-- Bessel's equation of order `n` in the book's form `y'' + y'/x + (1 - n²/x²) y = 0` on `(0, ∞)`. -/
lemma solvesN_of_deriv_form (n : ℕ) {y : ℝ → ℝ}
    (h : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ y x ∧ DifferentiableAt ℝ (deriv y) x ∧
      x ^ 2 * deriv (deriv y) x + x * deriv y x + (x ^ 2 - (n : ℝ) ^ 2) * y x = 0) :
    SolvesLin2 (fun x => 1 / x) (fun x => 1 - (n : ℝ) ^ 2 / x ^ 2) 0 (Set.Ioi 0) y := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  obtain ⟨d1, d2, e⟩ := h x hx'
  refine ⟨d1, d2, ?_⟩
  have hx0 : x ≠ 0 := hx'.ne'
  have key : deriv (deriv y) x + 1 / x * deriv y x + (1 - (n : ℝ) ^ 2 / x ^ 2) * y x =
      (x ^ 2 * deriv (deriv y) x + x * deriv y x + (x ^ 2 - (n : ℝ) ^ 2) * y x) / x ^ 2 := by
    field_simp
  simp only [Pi.zero_apply]
  rw [key, e, zero_div]

lemma bsJ_form (n : ℕ) : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (besselJR (n : ℝ)) x ∧
    DifferentiableAt ℝ (deriv (besselJR (n : ℝ))) x ∧
    x ^ 2 * deriv (deriv (besselJR (n : ℝ))) x + x * deriv (besselJR (n : ℝ)) x +
      (x ^ 2 - (n : ℝ) ^ 2) * besselJR (n : ℝ) x = 0 :=
  have hp := hp_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  deriv_form_of_hasDeriv n (fun _ hx => hasDerivAt_besselJR (n : ℝ) hp hx)
    (fun _ hx => hasDerivAt_besselJ1 (n : ℝ) hp hx) (fun _ hx => besselJ2_ode (n : ℝ) hp hx)

/-! ### The second solution -/

/-- The explicit derivatives of `y₂` and its negative `Y`. -/
lemma bsY_hasDeriv (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselY2n n) (frobLogY1 (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n) x) x ∧
    HasDerivAt (frobLogY1 (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n))
      (frobLogY2 (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n) x) x := by
  obtain ⟨hl, -⟩ := bs_core n hn
  obtain ⟨ha, hb⟩ := hl (x + 1) (by linarith)
  exact ⟨hasDerivAt_frobLogY ha hb hx (lt_add_one x), hasDerivAt_frobLogY1 ha hb hx (lt_add_one x)⟩

lemma besselY2n_ode (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    x ^ 2 * frobLogY2 (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n) x +
      x * frobLogY1 (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n) x +
      (x ^ 2 - (n : ℝ) ^ 2) * besselY2n n x = 0 := by
  obtain ⟨hl, -, -, hode⟩ := bs_core n hn
  obtain ⟨ha, hb⟩ := hl (x + 1) (by linarith)
  obtain ⟨e1, e2⟩ := deriv_frobLogY (r₁ := (n : ℝ)) (r₂ := -(n : ℝ)) (C := bsC n) ha hb hx (lt_add_one x)
  have := hode x hx
  change x ^ 2 * deriv (deriv (frobLogY (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n))) x +
    x * psum besselPc x * deriv (frobLogY (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n)) x +
      psum (besselQc n) x * frobLogY (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n) x = 0 at this
  rw [e1, e2, besselPc_psum, besselQc_psum] at this
  change _ = _ at this
  unfold besselY2n
  linarith

/-- The second solution `Y = -y₂` of Bessel's equation of order `n`. -/
noncomputable def besselYn (n : ℕ) (x : ℝ) : ℝ := - besselY2n n x

lemma besselYn_form (n : ℕ) (hn : 1 ≤ n) : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (besselYn n) x ∧
    DifferentiableAt ℝ (deriv (besselYn n)) x ∧
    x ^ 2 * deriv (deriv (besselYn n)) x + x * deriv (besselYn n) x +
      (x ^ 2 - (n : ℝ) ^ 2) * besselYn n x = 0 :=
  deriv_form_of_hasDeriv n (f := besselYn n)
    (f1 := fun x => - frobLogY1 (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n) x)
    (f2 := fun x => - frobLogY2 (bsA n) (bsB n) (n : ℝ) (-(n : ℝ)) (bsC n) x)
    (fun _ hx => (bsY_hasDeriv n hn hx).1.neg) (fun _ hx => (bsY_hasDeriv n hn hx).2.neg)
    (fun _ hx => by
      have := besselY2n_ode n hn hx
      unfold besselYn
      linarith)

/-- `Y` solves Bessel's equation of order `n` on `x > 0`. -/
theorem besselYn_solves (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : ℝ, 0 < x → x ^ 2 * deriv (deriv (besselYn n)) x + x * deriv (besselYn n) x +
      (x ^ 2 - (n : ℝ) ^ 2) * besselYn n x = 0 :=
  fun x hx => (besselYn_form n hn x hx).2.2

/-! ### Behaviour at `0⁺` -/

lemma besselYn_xpow (n : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ n * besselY2n n x = fS0 (bsB n) x +
      bsC n * (Real.log x * x ^ (2 * n)) * fS0 (bsA n) x := by
  unfold besselY2n frobLogY frobY
  have h1 : x ^ (-(n : ℝ)) * x ^ n = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]; simp
  have h2 : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n
  rw [h2]
  have h3 : x ^ n * (x ^ (-(n : ℝ)) * fS0 (bsB n) x) = fS0 (bsB n) x := by
    calc _ = (x ^ (-(n : ℝ)) * x ^ n) * fS0 (bsB n) x := by ring
      _ = _ := by rw [h1, one_mul]
  have h4 : x ^ n * (bsC n * (Real.log x * (x ^ n * fS0 (bsA n) x))) =
      bsC n * (Real.log x * x ^ (2 * n)) * fS0 (bsA n) x := by ring
  rw [mul_add, h3, h4]

lemma besselYn_scaled_tendsto (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun x => x ^ n * besselY2n n x) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨hl, ha0, hb0, -⟩ := bs_core n hn
  have hA := (hl 1 one_pos).1.tendsto_zero one_pos
  have hB := (hl 1 one_pos).2.tendsto_zero one_pos
  rw [ha0] at hA
  rw [hb0] at hB
  have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ (2 * n)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_log_mul_rpow_nhdsGT_zero (r := ((2 * n : ℕ) : ℝ))
      (by exact_mod_cast (by omega : 0 < 2 * n))
    exact this.congr (fun x => by rw [Real.rpow_natCast])
  have hT : Tendsto (fun x => fS0 (bsB n) x + bsC n * (Real.log x * x ^ (2 * n)) * fS0 (bsA n) x)
      (𝓝[>] 0) (𝓝 (1 + bsC n * 0 * 1)) :=
    hB.add (((hlog.const_mul (bsC n))).mul hA)
  rw [mul_zero, zero_mul, add_zero] at hT
  exact hT.congr' (by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (besselYn_xpow n hx).symm)

/-- `Y(x) → -∞` as `x → 0⁺`. -/
theorem besselYn_tendsto (n : ℕ) (hn : 1 ≤ n) : Tendsto (besselYn n) (𝓝[>] 0) atBot := by
  have hpow : Tendsto (fun x : ℝ => x ^ n) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((continuous_pow n).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa [zero_pow (by omega : n ≠ 0)] using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact pow_pos (Set.mem_Ioi.mp hx) n
  have hinv : Tendsto (fun x : ℝ => (x ^ n)⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp hpow
  have h := hinv.atTop_mul_pos one_pos (besselYn_scaled_tendsto n hn)
  have h2 : Tendsto (fun x => besselY2n n x) (𝓝[>] 0) atTop := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ^ n ≠ 0 := (pow_pos hx n).ne'
    field_simp
  exact tendsto_neg_atTop_atBot.comp h2

/-! ### Independence and the general solution -/

lemma besselJn_tendsto_zero (n : ℕ) (hn : 1 ≤ n) : Tendsto (besselJR (n : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hp := hp_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hE := (evS_tendsto_gen (bcoef_hsum (n : ℝ) hp)).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hP : Tendsto (fun x : ℝ => (x / 2) ^ n) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => (x / 2) ^ n := by fun_prop
    have := (hc.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [zero_pow (by omega : n ≠ 0)] using this
  have := hP.mul hE
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [besselJR_eq _ x hx, Real.rpow_natCast]

lemma besselJn_exists_ne (n : ℕ) : ∃ x : ℝ, 0 < x ∧ besselJR (n : ℝ) x ≠ 0 := by
  have hp := hp_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hE := (evS_tendsto_gen (bcoef_hsum (n : ℝ) hp)).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have h0 : bcoef (n : ℝ) 0 ≠ 0 := bcoef_ne _ hp 0
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), evS (bcoef (n : ℝ)) x ≠ 0 := hE.eventually_ne h0
  obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨x, hx2, ?_⟩
  rw [besselJR_eq _ x hx2]
  exact mul_ne_zero (Real.rpow_pos_of_pos (by positivity) _).ne' hx1

lemma besselJn_Yn_indep (n : ℕ) (hn : 1 ≤ n) (a b : ℝ)
    (h : ∀ x : ℝ, 0 < x → a * besselJR (n : ℝ) x + b * besselYn n x = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), besselYn n x = (-(a / b)) * besselJR (n : ℝ) x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have := h x hx
      field_simp
      linarith
    have ht : Tendsto (besselYn n) (𝓝[>] 0) (𝓝 ((-(a / b)) * 0)) :=
      ((besselJn_tendsto_zero n hn).const_mul (-(a / b))).congr' (hev.mono fun x hx => hx.symm)
    exact not_tendsto_nhds_of_tendsto_atBot (besselYn_tendsto n hn) _ ht
  subst hb
  refine ⟨?_, rfl⟩
  obtain ⟨x, hx, hJ⟩ := besselJn_exists_ne n
  have := h x hx
  simp only [zero_mul, add_zero] at this
  exact (mul_eq_zero.mp this).resolve_right hJ

lemma bsJ_solves (n : ℕ) :
    SolvesLin2 (fun x => 1 / x) (fun x => 1 - (n : ℝ) ^ 2 / x ^ 2) 0 (Set.Ioi 0) (besselJR (n : ℝ)) :=
  solvesN_of_deriv_form n (bsJ_form n)

lemma bsY_solves (n : ℕ) (hn : 1 ≤ n) :
    SolvesLin2 (fun x => 1 / x) (fun x => 1 - (n : ℝ) ^ 2 / x ^ 2) 0 (Set.Ioi 0) (besselYn n) :=
  solvesN_of_deriv_form n (besselYn_form n hn)

/-- Every solution on `(0, ∞)` of Bessel's equation of order `n` is `A J_n + B Y`. -/
theorem besselYn_general (n : ℕ) (hn : 1 ≤ n) {y : ℝ → ℝ}
    (hy : SolvesLin2 (fun x => 1 / x) (fun x => 1 - (n : ℝ) ^ 2 / x ^ 2) 0 (Set.Ioi 0) y) :
    ∃ A B : ℝ, ∀ x : ℝ, 0 < x → y x = A * besselJR (n : ℝ) x + B * besselYn n x := by
  obtain ⟨C₁, C₂, h⟩ := lin2_general_solution Set.ordConnected_Ioi
    (continuousOn_const.div continuousOn_id (fun x hx => (Set.mem_Ioi.mp hx).ne'))
    (continuousOn_const.sub (continuousOn_const.div (continuous_pow 2).continuousOn
      (fun x hx => pow_ne_zero 2 (Set.mem_Ioi.mp hx).ne')))
    (bsJ_solves n) (bsY_solves n hn)
    (linIndep_of (besselJn_Yn_indep n hn)) Set.nonempty_Ioi hy
  exact ⟨C₁, C₂, fun x hx => h x hx⟩

/-- DE-214 (§7.3.3 Bessel function of the second kind, p. 349), integer order `n ≥ 1`.  There is a function `Y`
solving Bessel's equation `x² y'' + x y' + (x² - n²) y = 0` on `(0, ∞)` with `Y(x) → -∞` as `x → 0⁺`, such that
every solution on `(0, ∞)` is `A J_n + B Y`.  This `Y` (the negative of the second Frobenius solution with
`b₀ = 1`) is a second solution with the book's properties, not the standard normalization of `Y_n`: the book
defines `Y_n` as a limit of combinations of `J_p` and `J_{-p}` as `p → n`, which is not formalized. -/
@[kb "lebldiffyqs2026" "§7.3.3 Bessel function of the second kind, p. 349"]
theorem besselYn_second_kind (n : ℕ) (hn : 1 ≤ n) :
    ∃ Y : ℝ → ℝ,
      (∀ x : ℝ, 0 < x → x ^ 2 * deriv (deriv Y) x + x * deriv Y x + (x ^ 2 - (n : ℝ) ^ 2) * Y x = 0) ∧
      Tendsto Y (𝓝[>] 0) atBot ∧
      (∀ y : ℝ → ℝ,
        SolvesLin2 (fun x => 1 / x) (fun x => 1 - (n : ℝ) ^ 2 / x ^ 2) 0 (Set.Ioi 0) y →
        ∃ A B : ℝ, ∀ x : ℝ, 0 < x → y x = A * besselJR (n : ℝ) x + B * Y x) :=
  ⟨besselYn n, besselYn_solves n hn, besselYn_tendsto n hn, fun _ hy => besselYn_general n hn hy⟩

end UndergradKB.DifferentialEquations
