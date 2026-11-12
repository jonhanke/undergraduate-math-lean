import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import UndergradKB.Common.Attr

/-! # Ratio and root tests for power series; the alternating zeta function
(rows CX-114, CX-147)

* Radius of convergence statements for `∑ c_k z^k` via the ratio and the root tests, and the two
  standard examples `∑ k z^k` and `∑ z^k / k!`.
* The alternating zeta function and its relation `η(s) = (1 - 2^(1-s)) ζ(s)`, together with the
  values `ζ(2)` and `ζ(4)` taken from Mathlib. -/

namespace UndergradKB.ComplexAnalysis

open Filter Topology

/-! ## Ratio test -/

lemma norm_term_ratio (c : ℕ → ℂ) {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    ‖c (k + 1) * z ^ (k + 1)‖ / ‖c k * z ^ k‖ = ‖c (k + 1)‖ / ‖c k‖ * ‖z‖ := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, pow_succ]
  by_cases h : ‖c k‖ = 0
  · simp [h]
  · have : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    field_simp

/-- Beck Corollary 7.4.6 (CX-114), ratio test, convergence half: if `|c_{k+1}/c_k| → L`, the series
`∑ c_k z^k` converges absolutely whenever `L |z| < 1` (for `L > 0`: `|z| < 1/L`). -/
@[kb "beck2025" "Corollary 7.4.6, p. 122"]
theorem ratio_test_summable (c : ℕ → ℂ) {L : ℝ} (hc : ∀ᶠ k in atTop, c k ≠ 0)
    (hL : Tendsto (fun k => ‖c (k + 1)‖ / ‖c k‖) atTop (𝓝 L)) {z : ℂ} (hz : L * ‖z‖ < 1) :
    Summable (fun k => ‖c k * z ^ k‖) := by
  by_cases hz0 : z = 0
  · subst hz0
    refine summable_of_ne_finset_zero (s := {0}) (fun k hk => ?_)
    have : k ≠ 0 := by simpa using hk
    simp [this]
  · have hT : Tendsto (fun k => ‖‖c (k + 1) * z ^ (k + 1)‖‖ / ‖‖c k * z ^ k‖‖) atTop
        (𝓝 (L * ‖z‖)) := by
      simp only [norm_norm]
      simp_rw [norm_term_ratio c hz0]
      exact hL.mul_const _
    refine summable_of_ratio_test_tendsto_lt_one hz ?_ hT
    filter_upwards [hc] with k hk
    simp [hk, hz0]

/-- Beck Corollary 7.4.6 (CX-114), ratio test, divergence half: if `|c_{k+1}/c_k| → L` and
`L |z| > 1` (for `L > 0`: `|z| > 1/L`), the series `∑ c_k z^k` diverges. -/
@[kb "beck2025" "Corollary 7.4.6, p. 122"]
theorem ratio_test_not_summable (c : ℕ → ℂ) {L : ℝ}
    (hL : Tendsto (fun k => ‖c (k + 1)‖ / ‖c k‖) atTop (𝓝 L)) {z : ℂ} (hz : 1 < L * ‖z‖) :
    ¬ Summable (fun k => c k * z ^ k) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
  refine not_summable_of_ratio_test_tendsto_gt_one hz ?_
  simp_rw [norm_term_ratio c hz0]
  exact hL.mul_const _

/-- Beck Corollary 7.4.6 (CX-114), ratio test, the case `L = 0`: the series converges absolutely
for every `z` (radius of convergence `∞`). -/
@[kb "beck2025" "Corollary 7.4.6, p. 122"]
theorem ratio_test_summable_of_tendsto_zero (c : ℕ → ℂ) (hc : ∀ᶠ k in atTop, c k ≠ 0)
    (hL : Tendsto (fun k => ‖c (k + 1)‖ / ‖c k‖) atTop (𝓝 0)) (z : ℂ) :
    Summable (fun k => ‖c k * z ^ k‖) :=
  ratio_test_summable c hc hL (by simp)

/-! ## Root test -/

lemma norm_term_root (c : ℕ → ℂ) (z : ℂ) {k : ℕ} (hk : k ≠ 0) :
    ‖c k * z ^ k‖ = (‖c k‖ ^ (1 / (k : ℝ)) * ‖z‖) ^ k := by
  have h1 : 1 / (k : ℝ) * k = 1 := by field_simp
  have h2 : (‖c k‖ ^ (1 / (k : ℝ))) ^ k = ‖c k‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), h1, Real.rpow_one]
  rw [norm_mul, norm_pow, mul_pow, h2]

/-- Beck Corollary 7.4.6 (CX-114), root test, convergence half: if `|c_k|^{1/k} → L`, the series
`∑ c_k z^k` converges absolutely whenever `L |z| < 1`. -/
@[kb "beck2025" "Corollary 7.4.6, p. 122"]
theorem root_test_summable (c : ℕ → ℂ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : Tendsto (fun k : ℕ => ‖c k‖ ^ (1 / (k : ℝ))) atTop (𝓝 L)) {z : ℂ} (hz : L * ‖z‖ < 1) :
    Summable (fun k => ‖c k * z ^ k‖) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hz
  have hr0 : 0 ≤ r := le_trans (by positivity) hr1.le
  have hev : ∀ᶠ k : ℕ in atTop, ‖c k‖ ^ (1 / (k : ℝ)) * ‖z‖ < r :=
    (hL.mul_const ‖z‖).eventually_lt_const hr1
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2) ?_
  filter_upwards [hev, eventually_ne_atTop 0] with k hk hk0
  rw [norm_norm, norm_term_root c z hk0]
  exact pow_le_pow_left₀ (by positivity) hk.le k

/-- Beck Corollary 7.4.6 (CX-114), root test, divergence half: if `|c_k|^{1/k} → L` and `L |z| > 1`,
the series `∑ c_k z^k` diverges. -/
@[kb "beck2025" "Corollary 7.4.6, p. 122"]
theorem root_test_not_summable (c : ℕ → ℂ) {L : ℝ}
    (hL : Tendsto (fun k : ℕ => ‖c k‖ ^ (1 / (k : ℝ))) atTop (𝓝 L)) {z : ℂ} (hz : 1 < L * ‖z‖) :
    ¬ Summable (fun k => c k * z ^ k) := by
  intro hs
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
  have hev : ∀ᶠ k : ℕ in atTop, 1 < ‖c k‖ ^ (1 / (k : ℝ)) * ‖z‖ :=
    (hL.mul_const ‖z‖).eventually_const_lt hz
  have h0 : Tendsto (fun k => ‖c k * z ^ k‖) atTop (𝓝 0) := by
    simpa using hs.tendsto_atTop_zero.norm
  have hlt := h0.eventually_lt_const one_pos
  obtain ⟨k, hk1, hk2, hk3⟩ := (hev.and (hlt.and (eventually_ne_atTop 0))).exists
  rw [norm_term_root c z hk3] at hk2
  exact absurd hk2 (not_lt.mpr (one_le_pow₀ hk1.le))

/-! ## Examples -/

/-- Coefficients of `∑ k z^k`. -/
def coeffId (k : ℕ) : ℂ := (k : ℂ)

lemma coeffId_ratio : Tendsto (fun k : ℕ => ‖coeffId (k + 1)‖ / ‖coeffId k‖) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  simp only [coeffId, Complex.norm_natCast]
  push_cast
  field_simp

/-- Beck Example 7.4.7 (CX-114): `∑ k z^k` converges absolutely for `|z| < 1`. -/
@[kb "beck2025" "Example 7.4.7, p. 123"]
theorem sum_k_mul_pow_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖(k : ℂ) * z ^ k‖) :=
  ratio_test_summable coeffId
    (by filter_upwards [eventually_ne_atTop 0] with k hk; simpa [coeffId] using hk)
    coeffId_ratio (by simpa using hz)

/-- Beck Example 7.4.7 (CX-114): `∑ k z^k` diverges for `|z| > 1`. -/
@[kb "beck2025" "Example 7.4.7, p. 123"]
theorem sum_k_mul_pow_not_summable {z : ℂ} (hz : 1 < ‖z‖) :
    ¬ Summable (fun k : ℕ => (k : ℂ) * z ^ k) :=
  ratio_test_not_summable coeffId coeffId_ratio (by simpa using hz)

/-- Beck Example 7.4.7 (CX-114): the power series `∑ k z^k` has radius of convergence `1`. -/
@[kb "beck2025" "Example 7.4.7, p. 123"]
theorem sum_k_mul_pow_radius : (FormalMultilinearSeries.ofScalars ℂ coeffId).radius = 1 := by
  have h : Tendsto (fun k : ℕ => ‖coeffId k.succ‖ / ‖coeffId k‖) atTop (𝓝 ((1 : NNReal) : ℝ)) := by
    simpa using coeffId_ratio
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto ℂ coeffId
    (r := 1) one_ne_zero h
  simpa using this

/-- Coefficients of `∑ z^k / k!`. -/
noncomputable def coeffExp (k : ℕ) : ℂ := 1 / (k.factorial : ℂ)

lemma coeffExp_ne (k : ℕ) : coeffExp k ≠ 0 := by
  simp [coeffExp, Nat.factorial_ne_zero]

lemma coeffExp_ratio : Tendsto (fun k : ℕ => ‖coeffExp (k + 1)‖ / ‖coeffExp k‖) atTop (𝓝 0) := by
  refine (tendsto_one_div_add_atTop_nhds_zero_nat).congr (fun k => ?_)
  simp only [coeffExp, norm_div, norm_one, Complex.norm_natCast, Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Beck Example 7.4.8 (CX-114): `∑ z^k / k!` converges absolutely for every `z`. -/
@[kb "beck2025" "Example 7.4.8, p. 123"]
theorem sum_pow_div_factorial_summable (z : ℂ) :
    Summable (fun k : ℕ => ‖z ^ k / (k.factorial : ℂ)‖) := by
  have := ratio_test_summable_of_tendsto_zero coeffExp
    (Eventually.of_forall coeffExp_ne) coeffExp_ratio z
  simpa [coeffExp, mul_comm, div_eq_mul_inv] using this

/-- Beck Example 7.4.8 (CX-114): the power series `∑ z^k / k!` has radius of convergence `∞`. -/
@[kb "beck2025" "Example 7.4.8, p. 123"]
theorem sum_pow_div_factorial_radius :
    (FormalMultilinearSeries.ofScalars ℂ coeffExp).radius = ⊤ :=
  FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ coeffExp
    (Eventually.of_forall coeffExp_ne) coeffExp_ratio

/-! ## The alternating zeta function (CX-147) -/

/-- Beck §10.1 (CX-147): the alternating zeta function `η(s) = ∑_{k ≥ 1} (-1)^(k+1) / k^s`
(summed from `k = 0` with the shift `k ↦ k + 1`). -/
@[kb "beck2025" "Alternating zeta function, §10.1, p. 163"]
noncomputable def altZeta (s : ℂ) : ℂ := ∑' k : ℕ, (-1 : ℂ) ^ k / ((k : ℂ) + 1) ^ s

/-- Beck §10.1 (CX-147): for `Re s > 1`, `η(s) = (1 - 2^(1-s)) ζ(s)`. -/
@[kb "beck2025" "Alternating zeta function, §10.1, p. 163"]
theorem altZeta_eq {s : ℂ} (hs : 1 < s.re) :
    altZeta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun k => 1 / ((k : ℂ) + 1) ^ s with hf
  have hsum : Summable f := by
    have := (Complex.summable_one_div_nat_cpow.mpr hs)
    exact (summable_nat_add_iff 1).mpr this |>.congr (fun k => by simp [hf])
  have hz : riemannZeta s = ∑' k, f k := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hE : Summable (fun k : ℕ => f (2 * k)) :=
    Summable.comp_injective (i := fun k : ℕ => 2 * k) hsum (fun a b h => by simpa using h)
  have hO : Summable (fun k : ℕ => f (2 * k + 1)) :=
    Summable.comp_injective (i := fun k : ℕ => 2 * k + 1) hsum (fun a b h => by simpa using h)
  have hζ : (∑' k : ℕ, f (2 * k)) + ∑' k : ℕ, f (2 * k + 1) = riemannZeta s := by
    rw [hz]; exact tsum_even_add_odd hE hO
  have hη : altZeta s = (∑' k : ℕ, f (2 * k)) - ∑' k : ℕ, f (2 * k + 1) := by
    have e : (fun k : ℕ => (-1 : ℂ) ^ k / ((k : ℂ) + 1) ^ s) = fun k => (-1 : ℂ) ^ k * f k := by
      funext k; simp only [hf]; ring
    unfold altZeta
    rw [e]
    have g2 : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k) * f (2 * k) = f (2 * k) := fun k => by
      rw [pow_mul]; simp
    have g3 : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k + 1) * f (2 * k + 1) = - f (2 * k + 1) := fun k => by
      rw [pow_succ, pow_mul]; simp
    have hgE : Summable (fun k : ℕ => (-1 : ℂ) ^ (2 * k) * f (2 * k)) := by
      simpa only [g2] using hE
    have hgO : Summable (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) * f (2 * k + 1)) := by
      simpa only [g3] using hO.neg
    have := tsum_even_add_odd (f := fun k : ℕ => (-1 : ℂ) ^ k * f k) hgE hgO
    refine this.symm.trans ?_
    simp only [g2, g3, tsum_neg]
    ring
  have hO2 : ∑' k : ℕ, f (2 * k + 1) = 1 / (2 : ℂ) ^ s * riemannZeta s := by
    rw [hz, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    have h1 : ((((2 * k + 1 : ℕ) : ℂ)) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    simp only [hf]
    rw [h1, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast
    simp only [one_div]
    simp
    ring
  have h2s : (2 : ℂ) ^ (1 - s) = 2 / 2 ^ s := by
    rw [Complex.cpow_sub _ _ (by norm_num), Complex.cpow_one]
  rw [hη, h2s]
  have : (∑' k : ℕ, f (2 * k)) = riemannZeta s - ∑' k : ℕ, f (2 * k + 1) := by
    rw [← hζ]; ring
  rw [this, hO2]
  have h2ne : (2 : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp
  field_simp
  ring

/-- Beck §10.1 (CX-147): `ζ(2) = π²/6` (restated from Mathlib's Basel problem). -/
@[kb "beck2025" "Alternating zeta function, §10.1, p. 163"]
theorem riemannZeta_two' : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 := by
  have h := Complex.hasSum_ofReal.mpr hasSum_zeta_two
  have h2 : riemannZeta ((2 : ℕ) : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (2 : ℕ) :=
    zeta_nat_eq_tsum_of_gt_one (by norm_num)
  have h3 := h.tsum_eq
  push_cast at h2 h3
  rw [h2]
  exact h3

/-- Beck §10.1 (CX-147): `ζ(4) = π⁴/90` (restated from Mathlib). -/
@[kb "beck2025" "Alternating zeta function, §10.1, p. 163"]
theorem riemannZeta_four' : riemannZeta 4 = (Real.pi : ℂ) ^ 4 / 90 := by
  have h := Complex.hasSum_ofReal.mpr hasSum_zeta_four
  have h2 : riemannZeta ((4 : ℕ) : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (4 : ℕ) :=
    zeta_nat_eq_tsum_of_gt_one (by norm_num)
  have h3 := h.tsum_eq
  push_cast at h2 h3
  rw [h2]
  exact h3

end UndergradKB.ComplexAnalysis
