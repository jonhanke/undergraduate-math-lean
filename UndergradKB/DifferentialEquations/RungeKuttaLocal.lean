import Mathlib.Analysis.Calculus.MeanValue
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FirstOrderExtra
import UndergradKB.DifferentialEquations.RungeKuttaTaylor

/-! # The classical Runge-Kutta method is fourth order (Lebl, §1.7, row DE-038)

For `f` of class `C⁴` and a solution `y` of `y' = f(x, y)`, one Runge-Kutta step from the exact value has local
error `|y(x₀ + h) - rk4Step f x₀ (y x₀) h| ≤ C h⁵` (`rk4Step_local_error`).

Proof.  Let `T` be the cubic Taylor polynomial of `f` at `(x₀, y₀)` (`taylor2D_cubic`, remainder
`K (|a| + |b|)⁴`) and `L` a Lipschitz constant of `f` in `y` near the point.  The key lemma `stage_bound`: if
`w = W(h) + O(h^m)` with `W(h) = w₁ h + w₂ h² + w₃ h³ + w₄ h⁴`, then `f(x₀ + α h, y₀ + w)` equals the degree-3
truncation `trc` of `T(α h, W(h))` up to `L·O(h^m) + O(h⁴)`.  Applied four times to the exact solution (Picard
iteration, `picard_step`: each step gains one power of `h`) it gives `y(x₀ + h) = y₀ + P₄(h) + O(h⁵)`; applied to the
stages `k₂, k₃, k₄` it gives cubic approximations `q, r₃, r₄` up to `O(h⁴)`.  The classical order conditions are the
polynomial identity `P₄(h) = h (c₀₀ + 2q + 2r₃ + r₄)/6`, checked by `ring` (the coefficients are computed in
`docs/coverage/differential-equations/rk4_poly.py`). -/

namespace UndergradKB.DifferentialEquations

open Set

/-- The degree-3 truncation in `h` of `T(α h, w₁ h + w₂ h² + w₃ h³ + w₄ h⁴)` (independent of `w₄`). -/
def trc (c : Cub) (α w₁ w₂ w₃ h : ℝ) : ℝ :=
  c.c00 + (c.c10 * α + c.c01 * w₁) * h + (c.c01 * w₂ + c.c20 * α ^ 2 + c.c11 * α * w₁ + c.c02 * w₁ ^ 2) * h ^ 2 +
    (c.c01 * w₃ + c.c11 * α * w₂ + 2 * c.c02 * w₁ * w₂ + c.c30 * α ^ 3 + c.c21 * α ^ 2 * w₁ + c.c12 * α * w₁ ^ 2 +
      c.c03 * w₁ ^ 3) * h ^ 3

/-- The quotient of the terms of degree `≥ 4`. -/
def stageQ (c : Cub) (α w₁ w₂ w₃ w₄ h : ℝ) : ℝ :=
  h ^ 8 * w₄ ^ 3 * c.c03 + 3 * h ^ 7 * w₃ * w₄ ^ 2 * c.c03 + 3 * h ^ 6 * w₂ * w₄ ^ 2 * c.c03 +
  3 * h ^ 6 * w₃ ^ 2 * w₄ * c.c03 + h ^ 5 * α * w₄ ^ 2 * c.c12 + 3 * h ^ 5 * w₁ * w₄ ^ 2 * c.c03 +
  6 * h ^ 5 * w₂ * w₃ * w₄ * c.c03 + h ^ 5 * w₃ ^ 3 * c.c03 + 2 * h ^ 4 * α * w₃ * w₄ * c.c12 +
  6 * h ^ 4 * w₁ * w₃ * w₄ * c.c03 + 3 * h ^ 4 * w₂ ^ 2 * w₄ * c.c03 + 3 * h ^ 4 * w₂ * w₃ ^ 2 * c.c03 +
  h ^ 4 * w₄ ^ 2 * c.c02 + 2 * h ^ 3 * α * w₂ * w₄ * c.c12 + h ^ 3 * α * w₃ ^ 2 * c.c12 +
  6 * h ^ 3 * w₁ * w₂ * w₄ * c.c03 + 3 * h ^ 3 * w₁ * w₃ ^ 2 * c.c03 + 3 * h ^ 3 * w₂ ^ 2 * w₃ * c.c03 +
  2 * h ^ 3 * w₃ * w₄ * c.c02 + h ^ 2 * α ^ 2 * w₄ * c.c21 + 2 * h ^ 2 * α * w₁ * w₄ * c.c12 +
  2 * h ^ 2 * α * w₂ * w₃ * c.c12 + 3 * h ^ 2 * w₁ ^ 2 * w₄ * c.c03 + 6 * h ^ 2 * w₁ * w₂ * w₃ * c.c03 +
  h ^ 2 * w₂ ^ 3 * c.c03 + 2 * h ^ 2 * w₂ * w₄ * c.c02 + h ^ 2 * w₃ ^ 2 * c.c02 + h * α ^ 2 * w₃ * c.c21 +
  2 * h * α * w₁ * w₃ * c.c12 + h * α * w₂ ^ 2 * c.c12 + h * α * w₄ * c.c11 + 3 * h * w₁ ^ 2 * w₃ * c.c03 +
  3 * h * w₁ * w₂ ^ 2 * c.c03 + 2 * h * w₁ * w₄ * c.c02 + 2 * h * w₂ * w₃ * c.c02 + α ^ 2 * w₂ * c.c21 +
  2 * α * w₁ * w₂ * c.c12 + α * w₃ * c.c11 + 3 * w₁ ^ 2 * w₂ * c.c03 + 2 * w₁ * w₃ * c.c02 + w₂ ^ 2 * c.c02 +
  w₄ * c.c01

lemma eval_stage (c : Cub) (α w₁ w₂ w₃ w₄ h : ℝ) :
    c.eval (α * h) (w₁ * h + w₂ * h ^ 2 + w₃ * h ^ 3 + w₄ * h ^ 4) =
      trc c α w₁ w₂ w₃ h + h ^ 4 * stageQ c α w₁ w₂ w₃ w₄ h := by
  unfold Cub.eval trc stageQ; ring

lemma abs_poly4_le {w₁ w₂ w₃ w₄ h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    |w₁ * h + w₂ * h ^ 2 + w₃ * h ^ 3 + w₄ * h ^ 4| ≤ (|w₁| + |w₂| + |w₃| + |w₄|) * h := by
  have e2 : h ^ 2 ≤ h := by nlinarith
  have e3 : h ^ 3 ≤ h := by nlinarith [pow_le_one₀ h0 h1 (n := 2)]
  have e4 : h ^ 4 ≤ h := by nlinarith [pow_le_one₀ h0 h1 (n := 3)]
  have a1 : |w₁ * h| ≤ |w₁| * h := by rw [abs_mul, abs_of_nonneg h0]
  have a2 : |w₂ * h ^ 2| ≤ |w₂| * h := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 2)]; exact mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
  have a3 : |w₃ * h ^ 3| ≤ |w₃| * h := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 3)]; exact mul_le_mul_of_nonneg_left e3 (abs_nonneg _)
  have a4 : |w₄ * h ^ 4| ≤ |w₄| * h := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 4)]; exact mul_le_mul_of_nonneg_left e4 (abs_nonneg _)
  have := abs_add_le (w₁ * h + w₂ * h ^ 2 + w₃ * h ^ 3) (w₄ * h ^ 4)
  have := abs_add_le (w₁ * h + w₂ * h ^ 2) (w₃ * h ^ 3)
  have := abs_add_le (w₁ * h) (w₂ * h ^ 2)
  nlinarith

set_option maxHeartbeats 1000000 in
lemma continuous_stageQ (c : Cub) (α w₁ w₂ w₃ w₄ : ℝ) : Continuous fun h => stageQ c α w₁ w₂ w₃ w₄ h := by
  unfold stageQ; fun_prop

/-- **Stage lemma.**  If `|w - W(h)| ≤ A h^m` with `W(h) = w₁ h + w₂ h² + w₃ h³ + w₄ h⁴` (all arguments in the square
of the Taylor expansion), then `f(x₀ + α h, y₀ + w)` is the cubic `trc c α w₁ w₂ w₃ h` up to `L A h^m + B h⁴`, with
`B` independent of `h`, `w`, `A`, `m`. -/
theorem stage_bound {F : ℝ × ℝ → ℝ} {x₀ y₀ K L : ℝ} {c : Cub} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hT : ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 → |F (x₀ + a, y₀ + b) - c.eval a b| ≤ K * (|a| + |b|) ^ 4)
    (hLip : ∀ a b b' : ℝ, |a| ≤ 1 → |b| ≤ 1 → |b'| ≤ 1 →
      |F (x₀ + a, y₀ + b) - F (x₀ + a, y₀ + b')| ≤ L * |b - b'|)
    (α w₁ w₂ w₃ w₄ : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ h w A : ℝ, ∀ m : ℕ, 0 ≤ h → h ≤ 1 → |α * h| ≤ 1 → |w| ≤ 1 →
      |w₁ * h + w₂ * h ^ 2 + w₃ * h ^ 3 + w₄ * h ^ 4| ≤ 1 →
      |w - (w₁ * h + w₂ * h ^ 2 + w₃ * h ^ 3 + w₄ * h ^ 4)| ≤ A * h ^ m →
      |F (x₀ + α * h, y₀ + w) - trc c α w₁ w₂ w₃ h| ≤ L * (A * h ^ m) + B * h ^ 4 := by
  have hQc : Continuous fun h => stageQ c α w₁ w₂ w₃ w₄ h := continuous_stageQ c α w₁ w₂ w₃ w₄
  obtain ⟨MQ, hMQ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hQc.continuousOn
  set S := |w₁| + |w₂| + |w₃| + |w₄|
  refine ⟨K * (|α| + S) ^ 4 + max MQ 0, by positivity, fun h w A m h0 h1 hα hw hW hwW => ?_⟩
  set W := w₁ * h + w₂ * h ^ 2 + w₃ * h ^ 3 + w₄ * h ^ 4 with hWdef
  have e1 := hLip (α * h) w W hα hw hW
  have e2 := hT (α * h) W hα hW
  have hS : |W| ≤ S * h := abs_poly4_le h0 h1
  have e2' : K * (|α * h| + |W|) ^ 4 ≤ K * (|α| + S) ^ 4 * h ^ 4 := by
    rw [abs_mul, abs_of_nonneg h0]
    calc K * (|α| * h + |W|) ^ 4 ≤ K * (|α| * h + S * h) ^ 4 := by gcongr
      _ = _ := by ring
  have e3 : |c.eval (α * h) W - trc c α w₁ w₂ w₃ h| ≤ max MQ 0 * h ^ 4 := by
    rw [hWdef, eval_stage, add_sub_cancel_left, abs_mul, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right ((hMQ h ⟨h0, h1⟩).trans (le_max_left _ _)) (by positivity)
  have e1' : L * |w - W| ≤ L * (A * h ^ m) := mul_le_mul_of_nonneg_left hwW hL
  calc |F (x₀ + α * h, y₀ + w) - trc c α w₁ w₂ w₃ h|
      = |(F (x₀ + α * h, y₀ + w) - F (x₀ + α * h, y₀ + W)) + (F (x₀ + α * h, y₀ + W) - c.eval (α * h) W) +
          (c.eval (α * h) W - trc c α w₁ w₂ w₃ h)| := by congr 1; ring
    _ ≤ |F (x₀ + α * h, y₀ + w) - F (x₀ + α * h, y₀ + W)| + |F (x₀ + α * h, y₀ + W) - c.eval (α * h) W| +
          |c.eval (α * h) W - trc c α w₁ w₂ w₃ h| := abs_add_three _ _ _
    _ ≤ L * (A * h ^ m) + K * (|α| + S) ^ 4 * h ^ 4 + max MQ 0 * h ^ 4 :=
        add_le_add (add_le_add (e1.trans e1') (e2.trans e2')) e3
    _ = _ := by ring

/-- A function of class `C¹` is Lipschitz in its second variable on the unit square around a point. -/
theorem lip_square {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 4 F) (x₀ y₀ : ℝ) :
    ∃ L, 0 ≤ L ∧ ∀ a b b' : ℝ, |a| ≤ 1 → |b| ≤ 1 → |b'| ≤ 1 →
      |F (x₀ + a, y₀ + b) - F (x₀ + a, y₀ + b')| ≤ L * |b - b'| := by
  have hc : Continuous fun p : ℝ × ℝ => fderiv ℝ F p ((0 : ℝ), (1 : ℝ)) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨L, hL0, hL⟩ := exists_bound_square hc x₀ y₀
  refine ⟨L, hL0, fun a b b' ha hb hb' => ?_⟩
  have hder : ∀ s, HasDerivAt (fun s : ℝ => F (x₀ + a, s)) (fderiv ℝ F (x₀ + a, s) ((0 : ℝ), (1 : ℝ))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => ((x₀ + a, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) s :=
      (hasDerivAt_const s (x₀ + a)).prodMk (hasDerivAt_id s)
    exact ((hF.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt s h1
  have key := (convex_Icc (y₀ - 1) (y₀ + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => F (x₀ + a, s)) (fun s _ => (hder s).hasDerivWithinAt)
    (fun s hs => by rw [Real.norm_eq_abs]; exact hL a s ha hs)
    (show y₀ + b' ∈ Icc (y₀ - 1) (y₀ + 1) by rw [abs_le] at hb'; constructor <;> linarith)
    (show y₀ + b ∈ Icc (y₀ - 1) (y₀ + 1) by rw [abs_le] at hb; constructor <;> linarith)
  simp only [Real.norm_eq_abs] at key
  rwa [show y₀ + b - (y₀ + b') = b - b' by ring] at key

/-- Coefficients of the truncation `trc` (constant, `h`, `h²`, `h³`). -/
def tc1 (c : Cub) (α w₁ : ℝ) : ℝ := c.c10 * α + c.c01 * w₁
/-- Coefficient of `h²` of `trc`. -/
def tc2 (c : Cub) (α w₁ w₂ : ℝ) : ℝ := c.c01 * w₂ + c.c20 * α ^ 2 + c.c11 * α * w₁ + c.c02 * w₁ ^ 2
/-- Coefficient of `h³` of `trc`. -/
def tc3 (c : Cub) (α w₁ w₂ w₃ : ℝ) : ℝ :=
  c.c01 * w₃ + c.c11 * α * w₂ + 2 * c.c02 * w₁ * w₂ + c.c30 * α ^ 3 + c.c21 * α ^ 2 * w₁ + c.c12 * α * w₁ ^ 2 +
    c.c03 * w₁ ^ 3

lemma trc_eq (c : Cub) (α w₁ w₂ w₃ h : ℝ) :
    trc c α w₁ w₂ w₃ h = c.c00 + tc1 c α w₁ * h + tc2 c α w₁ w₂ * h ^ 2 + tc3 c α w₁ w₂ w₃ * h ^ 3 := by
  unfold trc tc1 tc2 tc3; ring

lemma abs_poly4_le_one {w₁ w₂ w₃ w₄ ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : ρ * (|w₁| + |w₂| + |w₃| + |w₄|) ≤ 1) :
    ∀ u ∈ Icc (0 : ℝ) ρ, |w₁ * u + w₂ * u ^ 2 + w₃ * u ^ 3 + w₄ * u ^ 4| ≤ 1 := fun u hu => by
  refine (abs_poly4_le hu.1 (hu.2.trans hρ1)).trans ?_
  calc _ ≤ (|w₁| + |w₂| + |w₃| + |w₄|) * ρ := by gcongr; exact hu.2
    _ ≤ 1 := by linarith

/-- **Picard step.**  If `z' = f(x₀ + u, y₀ + z)`, `z(0) = 0` and `z = W + O(u^m)` on `[0, ρ]` (`m ≤ 4`), then
`z = W' + O(u^{m+1})`, where `W'` is the integral of the degree-3 truncation of `T(u, W(u))`. -/
theorem picard_step {F : ℝ × ℝ → ℝ} {x₀ y₀ K L : ℝ} {c : Cub} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hT : ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 → |F (x₀ + a, y₀ + b) - c.eval a b| ≤ K * (|a| + |b|) ^ 4)
    (hLip : ∀ a b b' : ℝ, |a| ≤ 1 → |b| ≤ 1 → |b'| ≤ 1 →
      |F (x₀ + a, y₀ + b) - F (x₀ + a, y₀ + b')| ≤ L * |b - b'|)
    {z : ℝ → ℝ} {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hz : ∀ u ∈ Icc (0 : ℝ) ρ, HasDerivAt z (F (x₀ + u, y₀ + z u)) u) (hz0 : z 0 = 0)
    {w₁ w₂ w₃ w₄ A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : m ≤ 4)
    (hzW : ∀ u ∈ Icc (0 : ℝ) ρ, |z u - (w₁ * u + w₂ * u ^ 2 + w₃ * u ^ 3 + w₄ * u ^ 4)| ≤ A * u ^ m)
    (hbz : ∀ u ∈ Icc (0 : ℝ) ρ, |z u| ≤ 1)
    (hbW : ∀ u ∈ Icc (0 : ℝ) ρ, |w₁ * u + w₂ * u ^ 2 + w₃ * u ^ 3 + w₄ * u ^ 4| ≤ 1) :
    ∃ A', 0 ≤ A' ∧ ∀ u ∈ Icc (0 : ℝ) ρ,
      |z u - (c.c00 * u + tc1 c 1 w₁ / 2 * u ^ 2 + tc2 c 1 w₁ w₂ / 3 * u ^ 3 + tc3 c 1 w₁ w₂ w₃ / 4 * u ^ 4)|
        ≤ A' * u ^ (m + 1) := by
  obtain ⟨B, hB0, hB⟩ := stage_bound hK hL hT hLip 1 w₁ w₂ w₃ w₄
  refine ⟨L * A + B, by positivity, fun u hu => ?_⟩
  set ψ : ℝ → ℝ := fun t => z t - (c.c00 * t + tc1 c 1 w₁ / 2 * t ^ 2 + tc2 c 1 w₁ w₂ / 3 * t ^ 3 +
    tc3 c 1 w₁ w₂ w₃ / 4 * t ^ 4) with hψ
  have hu1 : u ≤ 1 := hu.2.trans hρ1
  have hder : ∀ t ∈ Icc (0 : ℝ) u, HasDerivWithinAt ψ (F (x₀ + t, y₀ + z t) - trc c 1 w₁ w₂ w₃ t)
      (Icc (0 : ℝ) u) t := by
    intro t ht
    have htρ : t ∈ Icc (0 : ℝ) ρ := ⟨ht.1, ht.2.trans hu.2⟩
    have hP : HasDerivAt (fun t => c.c00 * t + tc1 c 1 w₁ / 2 * t ^ 2 + tc2 c 1 w₁ w₂ / 3 * t ^ 3 +
        tc3 c 1 w₁ w₂ w₃ / 4 * t ^ 4) (trc c 1 w₁ w₂ w₃ t) t := by
      have := ((((hasDerivAt_id t).const_mul c.c00).add ((hasDerivAt_pow 2 t).const_mul (tc1 c 1 w₁ / 2))).add
        ((hasDerivAt_pow 3 t).const_mul (tc2 c 1 w₁ w₂ / 3))).add
        ((hasDerivAt_pow 4 t).const_mul (tc3 c 1 w₁ w₂ w₃ / 4))
      refine this.congr_deriv ?_
      rw [trc_eq]; push_cast; ring
    exact ((hz t htρ).sub hP).hasDerivWithinAt
  have hbd : ∀ t ∈ Icc (0 : ℝ) u, ‖F (x₀ + t, y₀ + z t) - trc c 1 w₁ w₂ w₃ t‖ ≤ (L * A + B) * u ^ m := by
    intro t ht
    have htρ : t ∈ Icc (0 : ℝ) ρ := ⟨ht.1, ht.2.trans hu.2⟩
    have ht1 : t ≤ 1 := ht.2.trans hu1
    have h1 := hB t (z t) A m ht.1 ht1 (by rw [one_mul, abs_of_nonneg ht.1]; exact ht1) (hbz t htρ)
      (hbW t htρ) (hzW t htρ)
    rw [one_mul] at h1
    rw [Real.norm_eq_abs]
    have htm : t ^ m ≤ u ^ m := pow_le_pow_left₀ ht.1 ht.2 m
    have ht4 : t ^ 4 ≤ t ^ m := pow_le_pow_of_le_one ht.1 ht1 hm
    calc _ ≤ L * (A * t ^ m) + B * t ^ 4 := h1
      _ ≤ L * (A * u ^ m) + B * u ^ m := by gcongr; exact ht4.trans htm
      _ = _ := by ring
  have key := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    (left_mem_Icc.2 hu.1) (right_mem_Icc.2 hu.1)
  have hψ0 : ψ 0 = 0 := by simp [hψ, hz0]
  rw [hψ0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu.1] at key
  calc _ = |ψ u| := rfl
    _ ≤ _ := key
    _ = _ := by ring

/-- **The order conditions of the classical Runge-Kutta method**, as a polynomial identity: the fourth Picard
polynomial of the exact solution equals `h/6 (k₁ + 2 q + 2 r₃ + r₄)` for the cubic stage approximations. -/
theorem rk4_order_identity (c : Cub) (h a2 a3 b3 b4 d3 d4 e2 e3 e4 q1 q2 r1 r2 : ℝ)
    (ha2 : a2 = tc1 c 1 0 / 2) (ha3 : a3 = tc2 c 1 0 0 / 3)
    (hb3 : b3 = tc2 c 1 c.c00 a2 / 3) (hb4 : b4 = tc3 c 1 c.c00 a2 a3 / 4)
    (hd3 : d3 = tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3) (hd4 : d4 = tc3 c 1 c.c00 (tc1 c 1 c.c00 / 2) b3 / 4)
    (he2 : e2 = tc1 c 1 c.c00 / 2) (he3 : e3 = tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3)
    (he4 : e4 = tc3 c 1 c.c00 (tc1 c 1 c.c00 / 2) d3 / 4)
    (hq1 : q1 = tc1 c (1 / 2) (c.c00 / 2)) (hq2 : q2 = tc2 c (1 / 2) (c.c00 / 2) 0)
    (hr1 : r1 = tc1 c (1 / 2) (c.c00 / 2)) (hr2 : r2 = tc2 c (1 / 2) (c.c00 / 2) (q1 / 2)) :
    c.c00 * h + e2 * h ^ 2 + e3 * h ^ 3 + e4 * h ^ 4 =
      h / 6 * (c.c00 + 2 * trc c (1 / 2) (c.c00 / 2) 0 0 h + 2 * trc c (1 / 2) (c.c00 / 2) (q1 / 2) (q2 / 2) h +
        trc c 1 c.c00 r1 r2 h) := by
  subst ha2 ha3 hb3 hb4 hd3 hd4 he2 he3 he4 hq1 hq2 hr1 hr2
  unfold trc tc1 tc2 tc3
  ring

lemma abs_rk_comb3 (a b d : ℝ) : |2 * a + 2 * b + d| ≤ 2 * |a| + 2 * |b| + |d| := by
  have h1 := abs_add_le (2 * a + 2 * b) d
  have h2 := abs_add_le (2 * a) (2 * b)
  rw [abs_mul, abs_mul, abs_two] at h2
  linarith

set_option maxHeartbeats 4000000 in
/-- **The classical Runge-Kutta method is fourth order (Lebl, §1.7).**  If `f` is of class `C⁴` on `ℝ²` and `y` solves
`y' = f(x, y)` on `[x₀, x₀ + 1]`, then one Runge-Kutta step from the exact value `y(x₀)` has local error
`|y(x₀ + h) - rk4Step f x₀ (y x₀) h| ≤ C h⁵` for `0 ≤ h ≤ δ`.  (Added hypothesis, as for the improved Euler
method: `f` is `C⁴` on all of `ℝ²`.) -/
@[kb "lebldiffyqs2026" "§1.7 Runge-Kutta method, p. 61"]
theorem rk4Step_local_error {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 4 (fun p : ℝ × ℝ => f p.1 p.2)) {y : ℝ → ℝ}
    {x₀ : ℝ} (hy : ∀ t ∈ Icc x₀ (x₀ + 1), HasDerivAt y (f t (y t)) t) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ h, 0 ≤ h → h ≤ δ → |y (x₀ + h) - rk4Step f x₀ (y x₀) h| ≤ C * h ^ 5 := by
  set F : ℝ × ℝ → ℝ := fun p => f p.1 p.2 with hFdef
  set y₀ := y x₀ with hy₀
  obtain ⟨c, K, hK, hT⟩ := taylor2D_cubic hf x₀ y₀
  obtain ⟨L, hL, hLip⟩ := lip_square hf x₀ y₀
  have hc00 : f x₀ y₀ = c.c00 := by
    have h0 := hT 0 0 (by simp) (by simp)
    have h1 : |F (x₀ + 0, y₀ + 0) - c.eval 0 0| = 0 := le_antisymm (by simpa using h0) (abs_nonneg _)
    rw [abs_eq_zero, sub_eq_zero] at h1
    simpa [hFdef, Cub.eval] using h1
  -- the exact solution, shifted
  set z : ℝ → ℝ := fun u => y (x₀ + u) - y₀ with hzdef
  have hz : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt z (F (x₀ + u, y₀ + z u)) u := by
    intro u hu
    have h1 := ((hy (x₀ + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩).comp_const_add x₀ u).sub_const y₀
    convert h1 using 1
    simp [hFdef, hzdef]
  have hz0 : z 0 = 0 := by simp [hzdef, hy₀]
  have hzc : ContinuousOn (fun u => F (x₀ + u, y₀ + z u)) (Icc 0 1) := by
    have hzc' : ContinuousOn z (Icc 0 1) := fun u hu => (hz u hu).continuousAt.continuousWithinAt
    exact hf.continuous.comp_continuousOn ((continuousOn_const.add continuousOn_id).prodMk
      (continuousOn_const.add hzc'))
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hzc
  set M' := max M 0 with hM'
  have hz1 : ∀ u ∈ Icc (0 : ℝ) 1, |z u - (0 * u + 0 * u ^ 2 + 0 * u ^ 3 + 0 * u ^ 4)| ≤ M' * u ^ 1 := by
    intro u hu
    have key := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_hasDerivWithin_le (f := z)
      (f' := fun t => F (x₀ + t, y₀ + z t)) (C := M')
      (fun t (ht : t ∈ Icc 0 u) => (hz t ⟨ht.1, ht.2.trans hu.2⟩).hasDerivWithinAt)
      (fun t (ht : t ∈ Icc 0 u) => (hM t ⟨ht.1, ht.2.trans hu.2⟩).trans (le_max_left _ _))
      (left_mem_Icc.2 hu.1) (right_mem_Icc.2 hu.1)
    rw [hz0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu.1] at key
    simpa using key
  obtain ⟨MF, hMF0, hMF⟩ := exists_bound_square hf.continuous x₀ y₀
  -- coefficients of the Picard polynomials and of the stages
  set q1 := tc1 c (1 / 2) (c.c00 / 2) with hq1
  set q2 := tc2 c (1 / 2) (c.c00 / 2) 0 with hq2
  set q3 := tc3 c (1 / 2) (c.c00 / 2) 0 0 with hq3
  set r2 := tc2 c (1 / 2) (c.c00 / 2) (q1 / 2) with hr2
  set r3 := tc3 c (1 / 2) (c.c00 / 2) (q1 / 2) (q2 / 2) with hr3
  obtain ⟨S1, hS1⟩ : ∃ S, S = |c.c00| + |tc1 c 1 0 / 2| + |tc2 c 1 0 0 / 3| + |tc3 c 1 0 0 0 / 4| := ⟨_, rfl⟩
  obtain ⟨S2, hS2'⟩ : ∃ S, S = |c.c00| + |tc1 c 1 c.c00 / 2| + |tc2 c 1 c.c00 (tc1 c 1 0 / 2) / 3| +
      |tc3 c 1 c.c00 (tc1 c 1 0 / 2) (tc2 c 1 0 0 / 3) / 4| := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S, S = |c.c00| + |tc1 c 1 c.c00 / 2| + |tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3| +
      |tc3 c 1 c.c00 (tc1 c 1 c.c00 / 2) (tc2 c 1 c.c00 (tc1 c 1 0 / 2) / 3) / 4| := ⟨_, rfl⟩
  obtain ⟨Sq, hSq⟩ : ∃ S, S = |c.c00 / 2| + |q1 / 2| + |q2 / 2| + |q3 / 2| := ⟨_, rfl⟩
  obtain ⟨Sr, hSr⟩ : ∃ S, S = |c.c00| + |q1| + |r2| + |r3| := ⟨_, rfl⟩
  have hS1p : 0 ≤ S1 := by rw [hS1]; positivity
  have hS2p : 0 ≤ S2 := by rw [hS2']; positivity
  have hS3p : 0 ≤ S3 := by rw [hS3]; positivity
  have hSqp : 0 ≤ Sq := by rw [hSq]; positivity
  have hSrp : 0 ≤ Sr := by rw [hSr]; positivity
  set Sig := 1 + M' + |c.c00| + MF + S1 + S2 + S3 + Sq + Sr with hSig
  have hSig1 : 1 ≤ Sig := by
    have : 0 ≤ M' + |c.c00| + MF + S1 + S2 + S3 + Sq + Sr := by
      have := le_max_right M 0; have := abs_nonneg c.c00; linarith
    linarith
  set ρ := 1 / Sig with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one (by linarith)]; exact hSig1
  have hρX : ∀ X, 0 ≤ X → X ≤ Sig → ρ * X ≤ 1 := fun X hX hXSig => by
    rw [hρ, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; exact hXSig
  have hle : ∀ X, X ∈ [M', |c.c00|, MF, S1, S2, S3, Sq, Sr] → X ≤ Sig := by
    intro X hX
    have h0 : 0 ≤ M' := le_max_right _ _
    have : 0 ≤ |c.c00| := abs_nonneg _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
  have hρ' : ∀ u ∈ Icc (0 : ℝ) ρ, u ∈ Icc (0 : ℝ) 1 := fun u hu => ⟨hu.1, hu.2.trans hρ1⟩
  -- Picard iteration for the exact solution
  have hbz : ∀ u ∈ Icc (0 : ℝ) ρ, |z u| ≤ 1 := by
    intro u hu
    have h1 := hz1 u (hρ' u hu)
    simp only [zero_mul, add_zero, sub_zero, pow_one] at h1
    calc |z u| ≤ M' * u := h1
      _ ≤ ρ * M' := by rw [mul_comm]; gcongr; exact hu.2
      _ ≤ 1 := hρX M' (le_max_right _ _) (hle M' (by simp))
  have hzρ : ∀ u ∈ Icc (0 : ℝ) ρ, HasDerivAt z (F (x₀ + u, y₀ + z u)) u := fun u hu => hz u (hρ' u hu)
  obtain ⟨A1, hA1, P1⟩ := picard_step hK hL hT hLip hρ1 hzρ hz0 (le_max_right M 0) (by norm_num : 1 ≤ 4)
    (fun u hu => hz1 u (hρ' u hu)) hbz (fun u _ => by simp)
  obtain ⟨A2, hA2, P2⟩ := picard_step hK hL hT hLip hρ1 hzρ hz0 hA1 (by norm_num : 1 + 1 ≤ 4) P1 hbz
    (abs_poly4_le_one hρ1 (hS1 ▸ hρX S1 hS1p (hle S1 (by simp))))
  obtain ⟨A3, hA3, P3⟩ := picard_step hK hL hT hLip hρ1 hzρ hz0 hA2 (by norm_num : 1 + 1 + 1 ≤ 4) P2 hbz
    (abs_poly4_le_one hρ1 (hS2' ▸ hρX S2 hS2p (hle S2 (by simp))))
  obtain ⟨A4, hA4, P4⟩ := picard_step hK hL hT hLip hρ1 hzρ hz0 hA3 (by norm_num : 1 + 1 + 1 + 1 ≤ 4) P3 hbz
    (abs_poly4_le_one hρ1 (hS3 ▸ hρX S3 hS3p (hle S3 (by simp))))
  -- the stages
  obtain ⟨B2, hB20, hB2⟩ := stage_bound hK hL hT hLip (1 / 2) (c.c00 / 2) 0 0 0
  obtain ⟨B3, hB30, hB3⟩ := stage_bound hK hL hT hLip (1 / 2) (c.c00 / 2) (q1 / 2) (q2 / 2) (q3 / 2)
  obtain ⟨B4, hB40, hB4⟩ := stage_bound hK hL hT hLip 1 c.c00 q1 r2 r3
  refine ⟨A4 + (2 * B2 + 2 * (L * (B2 / 2) + B3) + (L * (L * (B2 / 2) + B3) + B4)) / 6, ρ, hρ0,
    fun h h0 hρh => ?_⟩
  have hh : h ∈ Icc (0 : ℝ) ρ := ⟨h0, hρh⟩
  have h1 : h ≤ 1 := hρh.trans hρ1
  have hhalf : |1 / 2 * h| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hsq : ∀ w, |w| ≤ 1 → ∀ a, |a| ≤ 1 → |F (x₀ + a, y₀ + w)| ≤ MF := fun w hw a ha =>
    hMF a (y₀ + w) ha (by rw [abs_le] at hw; constructor <;> linarith)
  -- stage 2
  set K2 := f (x₀ + h / 2) (y₀ + h / 2 * c.c00) with hK2
  have hw2 : |h / 2 * c.c00| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have := hρX |c.c00| (abs_nonneg _) (hle _ (by simp))
    calc h / 2 * |c.c00| ≤ ρ * |c.c00| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ 1 := this
  have hS2 : |c.c00 / 2 * h + 0 * h ^ 2 + 0 * h ^ 3 + 0 * h ^ 4| ≤ 1 := by
    rw [show c.c00 / 2 * h + 0 * h ^ 2 + 0 * h ^ 3 + 0 * h ^ 4 = h / 2 * c.c00 by ring]; exact hw2
  have st2 := hB2 h (h / 2 * c.c00) 0 4 h0 h1 hhalf hw2 hS2
    (by rw [show h / 2 * c.c00 - (c.c00 / 2 * h + 0 * h ^ 2 + 0 * h ^ 3 + 0 * h ^ 4) = 0 by ring]; simp)
  rw [show x₀ + 1 / 2 * h = x₀ + h / 2 by ring] at st2
  simp only [zero_mul, mul_zero, zero_add] at st2
  -- stage 3
  set K3 := f (x₀ + h / 2) (y₀ + h / 2 * K2) with hK3
  have hK2b : |K2| ≤ MF := by
    have := hsq (h / 2 * c.c00) hw2 (1 / 2 * h) hhalf
    rwa [show x₀ + 1 / 2 * h = x₀ + h / 2 by ring] at this
  have hw3 : |h / 2 * K2| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have := hρX MF hMF0 (hle _ (by simp))
    calc h / 2 * |K2| ≤ h / 2 * MF := by gcongr
      _ ≤ ρ * MF := mul_le_mul_of_nonneg_right (by linarith) hMF0
      _ ≤ 1 := this
  have hW3 : |c.c00 / 2 * h + q1 / 2 * h ^ 2 + q2 / 2 * h ^ 3 + q3 / 2 * h ^ 4| ≤ 1 :=
    abs_poly4_le_one hρ1 (hSq ▸ hρX Sq hSqp (hle Sq (by simp))) h hh
  have hq : h / 2 * trc c (1 / 2) (c.c00 / 2) 0 0 h = c.c00 / 2 * h + q1 / 2 * h ^ 2 + q2 / 2 * h ^ 3 +
      q3 / 2 * h ^ 4 := by rw [trc_eq]; ring
  have hd3 : |h / 2 * K2 - (c.c00 / 2 * h + q1 / 2 * h ^ 2 + q2 / 2 * h ^ 3 + q3 / 2 * h ^ 4)| ≤
      B2 / 2 * h ^ 5 := by
    rw [← hq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    calc h / 2 * |K2 - trc c (1 / 2) (c.c00 / 2) 0 0 h| ≤ h / 2 * (B2 * h ^ 4) := by gcongr
      _ = _ := by ring
  have st3 := hB3 h (h / 2 * K2) (B2 / 2) 5 h0 h1 hhalf hw3 hW3 hd3
  rw [show x₀ + 1 / 2 * h = x₀ + h / 2 by ring] at st3
  -- stage 4
  set K4 := f (x₀ + h) (y₀ + h * K3) with hK4
  have hK3b : |K3| ≤ MF := by
    have := hsq (h / 2 * K2) hw3 (1 / 2 * h) hhalf
    rwa [show x₀ + 1 / 2 * h = x₀ + h / 2 by ring] at this
  have hone : |1 * h| ≤ 1 := by rw [one_mul, abs_of_nonneg h0]; exact h1
  have hw4 : |h * K3| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg h0]
    have := hρX MF hMF0 (hle _ (by simp))
    calc h * |K3| ≤ h * MF := by gcongr
      _ ≤ ρ * MF := mul_le_mul_of_nonneg_right hρh hMF0
      _ ≤ 1 := this
  have hW4 : |c.c00 * h + q1 * h ^ 2 + r2 * h ^ 3 + r3 * h ^ 4| ≤ 1 :=
    abs_poly4_le_one hρ1 (hSr ▸ hρX Sr hSrp (hle Sr (by simp))) h hh
  have hr : h * trc c (1 / 2) (c.c00 / 2) (q1 / 2) (q2 / 2) h = c.c00 * h + q1 * h ^ 2 + r2 * h ^ 3 +
      r3 * h ^ 4 := by rw [trc_eq]; ring
  have hd4 : |h * K3 - (c.c00 * h + q1 * h ^ 2 + r2 * h ^ 3 + r3 * h ^ 4)| ≤
      (L * (B2 / 2) + B3) * h ^ 5 := by
    rw [← hr, ← mul_sub, abs_mul, abs_of_nonneg h0]
    have h5 : h ^ 5 ≤ h ^ 4 := pow_le_pow_of_le_one h0 h1 (by norm_num)
    calc h * |K3 - trc c (1 / 2) (c.c00 / 2) (q1 / 2) (q2 / 2) h|
        ≤ h * (L * (B2 / 2 * h ^ 5) + B3 * h ^ 4) := by gcongr
      _ ≤ h * (L * (B2 / 2 * h ^ 4) + B3 * h ^ 4) := by gcongr
      _ = _ := by ring
  have st4 := hB4 h (h * K3) (L * (B2 / 2) + B3) 5 h0 h1 hone hw4 hW4 hd4
  rw [one_mul] at st4
  -- assemble
  have hrk : rk4Step f x₀ (y x₀) h = y₀ + h / 6 * (c.c00 + 2 * K2 + 2 * K3 + K4) := by
    simp only [rk4Step, hK2, hK3, hK4, ← hy₀, hc00]
  have hid := rk4_order_identity c h (tc1 c 1 0 / 2) (tc2 c 1 0 0 / 3)
    (tc2 c 1 c.c00 (tc1 c 1 0 / 2) / 3) (tc3 c 1 c.c00 (tc1 c 1 0 / 2) (tc2 c 1 0 0 / 3) / 4)
    (tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3)
    (tc3 c 1 c.c00 (tc1 c 1 c.c00 / 2) (tc2 c 1 c.c00 (tc1 c 1 0 / 2) / 3) / 4)
    (tc1 c 1 c.c00 / 2) (tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3)
    (tc3 c 1 c.c00 (tc1 c 1 c.c00 / 2) (tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3) / 4) q1 q2 q1 r2
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hP4 := P4 h hh
  have hyz : y (x₀ + h) = y₀ + z h := by simp [hzdef]
  rw [hrk, hyz]
  have hsplit : y₀ + z h - (y₀ + h / 6 * (c.c00 + 2 * K2 + 2 * K3 + K4)) =
      (z h - (c.c00 * h + tc1 c 1 c.c00 / 2 * h ^ 2 + tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3 * h ^ 3 +
        tc3 c 1 c.c00 (tc1 c 1 c.c00 / 2) (tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3) / 4 * h ^ 4)) +
      h / 6 * (2 * (trc c (1 / 2) (c.c00 / 2) 0 0 h - K2) +
        2 * (trc c (1 / 2) (c.c00 / 2) (q1 / 2) (q2 / 2) h - K3) + (trc c 1 c.c00 q1 r2 h - K4)) := by
    have := hid
    linear_combination this
  rw [hsplit]
  have h5 : h ^ 6 ≤ h ^ 5 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have hh6 : 0 ≤ h / 6 := by positivity
  calc _ ≤ |z h - (c.c00 * h + tc1 c 1 c.c00 / 2 * h ^ 2 + tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3 * h ^ 3 +
        tc3 c 1 c.c00 (tc1 c 1 c.c00 / 2) (tc2 c 1 c.c00 (tc1 c 1 c.c00 / 2) / 3) / 4 * h ^ 4)| +
      h / 6 * (2 * |trc c (1 / 2) (c.c00 / 2) 0 0 h - K2| +
        2 * |trc c (1 / 2) (c.c00 / 2) (q1 / 2) (q2 / 2) h - K3| + |trc c 1 c.c00 q1 r2 h - K4|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg hh6]
        gcongr
        exact abs_rk_comb3 _ _ _
    _ ≤ A4 * h ^ (1 + 1 + 1 + 1 + 1) + h / 6 * (2 * (B2 * h ^ 4) + 2 * (L * (B2 / 2 * h ^ 5) + B3 * h ^ 4) +
        (L * ((L * (B2 / 2) + B3) * h ^ 5) + B4 * h ^ 4)) := by
        gcongr
        · rw [abs_sub_comm]; exact st2
        · rw [abs_sub_comm]; exact st3
        · rw [abs_sub_comm]; exact st4
    _ ≤ _ := by
        have : 0 ≤ L * (B2 / 2) := by positivity
        have : 0 ≤ L * (L * (B2 / 2) + B3) := by positivity
        have h65 : h * h ^ 5 ≤ h ^ 5 := by nlinarith [pow_nonneg h0 5]
        nlinarith [pow_nonneg h0 5]

end UndergradKB.DifferentialEquations
