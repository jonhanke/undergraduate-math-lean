import Mathlib.Analysis.MeanInequalities
import UndergradKB.Common.Attr
import UndergradKB.Statistics.Shape

/-!
# The F curve is skewed to the right: its peak lies below its mean (§13.3)

OpenStax *Introductory Statistics 2e*, §13.3 (ST-116): every F curve is skewed to the right. `Shape.lean` proves
this as a positive third central moment, which exists only for `d₂ > 6`. Here is a statement that needs no
moments: the density of the F law with `d₁`, `d₂` degrees of freedom

* for `d₁ > 2` is largest at the mode `m = ((d₁ - 2)/d₁) · (d₂/(d₂ + 2))`, which is below `1` and therefore below
  the mean `d₂/(d₂ - 2)` (when `d₂ > 2`);
* for `d₁ ≤ 2` is decreasing on `(0, ∞)` (the peak is at `0`).

The maximum is found without calculus: in the variable `u = d₁ x / d₂` the density is a constant times
`u^p (1 + u)^{-(p + q)}` with `p = d₁/2 - 1`, `q = d₂/2 + 1`, and the weighted inequality of arithmetic and
geometric means gives `(u/u₀)^{p/(p+q)} ≤ (p (u/u₀) + q)/(p + q) = (1 + u)/(1 + u₀)` at `u₀ = p/q`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set

/-- `u^p (1 + u)^{-(p + q)}` is largest at `u = p/q` (weighted arithmetic-geometric mean inequality). -/
lemma rpow_mul_one_add_rpow_neg_le {p q u : ℝ} (hp : 0 < p) (hq : 0 < q) (hu : 0 ≤ u) :
    u ^ p * (1 + u) ^ (-(p + q)) ≤ (p / q) ^ p * (1 + p / q) ^ (-(p + q)) := by
  have hu0 : 0 < p / q := div_pos hp hq
  have hpq : 0 < p + q := by linarith
  have hα : 0 ≤ p / (p + q) := (div_pos hp hpq).le
  have hβ : 0 ≤ q / (p + q) := (div_pos hq hpq).le
  have hαβ : p / (p + q) + q / (p + q) = 1 := by rw [← add_div]; exact div_self hpq.ne'
  have hA : 0 ≤ u / (p / q) := div_nonneg hu hu0.le
  have amgm := Real.geom_mean_le_arith_mean2_weighted hα hβ hA zero_le_one hαβ
  rw [one_rpow, mul_one, mul_one] at amgm
  have hB : p / (p + q) * (u / (p / q)) + q / (p + q) = (1 + u) / (1 + p / q) := by
    field_simp
    ring
  rw [hB] at amgm
  have h1 : (u / (p / q)) ^ p ≤ ((1 + u) / (1 + p / q)) ^ (p + q) := by
    have := rpow_le_rpow (rpow_nonneg hA _) amgm hpq.le
    rwa [← rpow_mul hA, show p / (p + q) * (p + q) = p by field_simp] at this
  have h1u : 0 < 1 + u := by linarith
  have h1u0 : 0 < 1 + p / q := by linarith
  rw [div_rpow hu hu0.le, div_rpow h1u.le h1u0.le] at h1
  rw [rpow_neg h1u.le, rpow_neg h1u0.le, ← div_eq_mul_inv, ← div_eq_mul_inv]
  have hc1 : 0 < (1 + u) ^ (p + q) := rpow_pos_of_pos h1u _
  have hc0 : 0 < (1 + p / q) ^ (p + q) := rpow_pos_of_pos h1u0 _
  have hu0p : 0 < (p / q) ^ p := rpow_pos_of_pos hu0 _
  rw [div_le_div_iff₀ hc1 hc0]
  rw [div_le_div_iff₀ hu0p hc0] at h1
  rw [mul_comm ((p / q) ^ p)]
  exact h1

/-- The mode of the F distribution with `d₁ > 2`, `d₂` degrees of freedom: `((d₁ - 2)/d₁) · (d₂/(d₂ + 2))`. -/
noncomputable def fMode (d₁ d₂ : ℝ) : ℝ := (d₁ - 2) / d₁ * (d₂ / (d₂ + 2))

private lemma fPDFReal_eq_mul {d₁ d₂ x : ℝ} (hx : 0 < x) :
    fPDFReal d₁ d₂ x = Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) * (d₁ / d₂) ^ (d₁ / 2) *
      (x ^ (d₁ / 2 - 1) * (1 + d₁ / d₂ * x) ^ (-((d₁ / 2 - 1) + (d₂ / 2 + 1)))) := by
  simp only [fPDFReal, hx, ↓reduceIte]
  rw [show d₁ * x / d₂ = d₁ / d₂ * x by ring,
    show (d₁ + d₂) / 2 = (d₁ / 2 - 1) + (d₂ / 2 + 1) by ring]
  ring

/-- **The F density peaks at its mode** (§13.3): for `d₁ > 2`, `d₂ > 0`, the density of the F law is at most its
value at `m = ((d₁ - 2)/d₁) · (d₂/(d₂ + 2))`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem fPDFReal_le_fMode {d₁ d₂ : ℝ} (hd₁ : 2 < d₁) (hd₂ : 0 < d₂) (x : ℝ) :
    fPDFReal d₁ d₂ x ≤ fPDFReal d₁ d₂ (fMode d₁ d₂) := by
  have hd₁' : 0 < d₁ := by linarith
  have hm : 0 < fMode d₁ d₂ := by
    unfold fMode
    have : 0 < d₁ - 2 := by linarith
    positivity
  have hG := Gamma_pos_of_pos (by positivity : 0 < (d₁ + d₂) / 2)
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have hG2 := Gamma_pos_of_pos (by positivity : 0 < d₂ / 2)
  have hk : 0 < d₁ / d₂ := div_pos hd₁' hd₂
  have hC : 0 < Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) * (d₁ / d₂) ^ (d₁ / 2) := by
    have := rpow_pos_of_pos hk (d₁ / 2)
    positivity
  have hfm : 0 ≤ fPDFReal d₁ d₂ (fMode d₁ d₂) := by
    rw [fPDFReal_eq_mul hm]
    have h1 := rpow_pos_of_pos hm (d₁ / 2 - 1)
    have h2 := rpow_pos_of_pos (by positivity : 0 < 1 + d₁ / d₂ * fMode d₁ d₂)
      (-((d₁ / 2 - 1) + (d₂ / 2 + 1)))
    positivity
  by_cases hx : 0 < x
  swap
  · simp only [fPDFReal, hx, ↓reduceIte]
    exact hfm
  rw [fPDFReal_eq_mul hx, fPDFReal_eq_mul hm]
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  have hp : 0 < d₁ / 2 - 1 := by linarith
  have hq : 0 < d₂ / 2 + 1 := by positivity
  have key := rpow_mul_one_add_rpow_neg_le hp hq (mul_pos hk hx).le
  have hkm : (d₁ / 2 - 1) / (d₂ / 2 + 1) = d₁ / d₂ * fMode d₁ d₂ := by
    unfold fMode
    field_simp
  rw [hkm, mul_rpow hk.le hx.le, mul_rpow hk.le hm.le, mul_assoc, mul_assoc] at key
  exact le_of_mul_le_mul_left key (rpow_pos_of_pos hk _)

/-- **For `d₁ ≤ 2` the F density decreases on `(0, ∞)`** (§13.3): its peak is at `0`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem fPDFReal_antitoneOn {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₁' : d₁ ≤ 2) (hd₂ : 0 < d₂) :
    AntitoneOn (fPDFReal d₁ d₂) (Ioi 0) := by
  intro x hx y hy hxy
  rw [mem_Ioi] at hx hy
  have hG := Gamma_pos_of_pos (by positivity : 0 < (d₁ + d₂) / 2)
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < d₁ / 2)
  have hG2 := Gamma_pos_of_pos (by positivity : 0 < d₂ / 2)
  have hk : 0 < d₁ / d₂ := div_pos hd₁ hd₂
  have hC : 0 < Gamma ((d₁ + d₂) / 2) / (Gamma (d₁ / 2) * Gamma (d₂ / 2)) * (d₁ / d₂) ^ (d₁ / 2) := by
    have := rpow_pos_of_pos hk (d₁ / 2)
    positivity
  rw [fPDFReal_eq_mul hx, fPDFReal_eq_mul hy]
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  have h1 : y ^ (d₁ / 2 - 1) ≤ x ^ (d₁ / 2 - 1) := rpow_le_rpow_of_nonpos hx hxy (by linarith)
  have hkx : 0 < 1 + d₁ / d₂ * x := by positivity
  have h2 : (1 + d₁ / d₂ * y) ^ (-((d₁ / 2 - 1) + (d₂ / 2 + 1))) ≤
      (1 + d₁ / d₂ * x) ^ (-((d₁ / 2 - 1) + (d₂ / 2 + 1))) :=
    rpow_le_rpow_of_nonpos hkx (by gcongr) (by linarith)
  have h2' : 0 ≤ (1 + d₁ / d₂ * y) ^ (-((d₁ / 2 - 1) + (d₂ / 2 + 1))) := rpow_nonneg (by positivity) _
  exact mul_le_mul h1 h2 h2' (rpow_nonneg hx.le _)

/-- **The F curve is skewed to the right: its peak lies below its mean** (§13.3, ST-116). For `d₁ > 2` and
`d₂ > 2` the density of the F law is largest at the mode `m = ((d₁ - 2)/d₁) · (d₂/(d₂ + 2))`, and
`m < 1 < d₂/(d₂ - 2) = E[F]`. -/
@[kb "openstaxintrostats2e" "§13.3, p. 695"]
theorem fDistribution_mode_lt_mean {d₁ d₂ : ℝ} (hd₁ : 2 < d₁) (hd₂ : 2 < d₂) :
    (∀ x, fPDFReal d₁ d₂ x ≤ fPDFReal d₁ d₂ (fMode d₁ d₂)) ∧ fMode d₁ d₂ < 1 ∧
      fMode d₁ d₂ < ∫ x, x ∂(fDistribution d₁ d₂) := by
  have hm1 : fMode d₁ d₂ < 1 := by
    unfold fMode
    have h1 : (d₁ - 2) / d₁ < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h2 : d₂ / (d₂ + 2) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h3 : 0 ≤ d₂ / (d₂ + 2) := by positivity
    nlinarith
  refine ⟨fPDFReal_le_fMode hd₁ (by linarith), hm1, ?_⟩
  rw [(integral_id_fDistribution (by linarith) hd₂).2]
  have : 1 < d₂ / (d₂ - 2) := by rw [one_lt_div (by linarith)]; linarith
  linarith

end UndergradKB.Statistics
