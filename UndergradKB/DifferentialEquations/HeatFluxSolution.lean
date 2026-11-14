import UndergradKB.DifferentialEquations.HeatFluxInversion
import UndergradKB.DifferentialEquations.LaplacePDE
import UndergradKB.DifferentialEquations.LaplaceUniqueness
import UndergradKB.Common.Attr

/-!
# Lebl Example 6.5.3, the composed statement (a recorded loose end)

Heat equation on the half line with prescribed flux, solved by the Laplace transform in `t`.
`example_653_solution` composes `example_653_ode` (the transformed ODE in `x`, with `r = √s`),
`example_653_inversion` (the transform of the convolution with `-heatKernel x`) and Lerch uniqueness
(`laplace_unique_of_gt`): a function `y(x,t)` whose transforms `Y_s(x) = L{y(x,·)}(s)` solve the transformed
problem equals `y(x,t) = ∫_0^t f(τ) (-heatKernel x (t-τ)) dτ`.

Hypotheses beyond the book: the transformed equations are assumed (the book passes the PDE through the
transform formally).  The continuity of the convolution on `[0, ∞)` is proved (`continuousOn_conv0`).
-/

open Real Set Filter Topology MeasureTheory

namespace UndergradKB.DifferentialEquations

/-- The convolution `(f * g)(t) = ∫_0^t f(τ) g(t - τ) dτ` of two functions continuous on `[0, ∞)` is continuous
on `[0, ∞)`. -/
theorem continuousOn_conv0 {f g : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0)) :
    ContinuousOn (conv0 f g) (Ici 0) := by
  have hm : Continuous fun t : ℝ => max 0 t := continuous_const.max continuous_id
  have hmi : ∀ t : ℝ, max 0 t ∈ Ici (0 : ℝ) := fun t => mem_Ici.2 (le_max_left _ _)
  have hf' : Continuous fun t => f (max 0 t) := hf.comp_continuous hm hmi
  have hg' : Continuous fun t => g (max 0 t) := hg.comp_continuous hm hmi
  have hF : Continuous fun t : ℝ => ∫ τ in (0 : ℝ)..t, f (max 0 τ) * g (max 0 (t - τ)) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun t τ => f (max 0 τ) * g (max 0 (t - τ))) ?_ continuous_id
    exact (hf'.comp continuous_snd).mul (hg'.comp (continuous_fst.sub continuous_snd))
  refine hF.continuousOn.congr fun t ht => ?_
  refine intervalIntegral.integral_congr fun τ hτ => ?_
  rw [uIcc_of_le (show (0 : ℝ) ≤ t from ht)] at hτ
  simp only [max_eq_right hτ.1, max_eq_right (sub_nonneg.2 hτ.2)]

/-- **Lebl Example 6.5.3, composed.** Let `f` be continuous on `[0,∞)` of exponential order `(M,c)`, and let
`y(x,·)` be continuous and of exponential order for each `x > 0`.  Suppose that for every `s > s₀` the transform
`Y_s(x) = L{y(x,·)}(s)` (with derivative `dY s`) is bounded on `x ≥ 0`, solves `Y_s'' = s Y_s` for `x > 0`,
is continuous from the right at `0` together with its derivative, and `Y_s'(0) = L{f}(s)`
(the transformed equation `y_t = y_xx`, `y(x,0) = 0`, the flux condition `y_x(0,t) = f(t)`, boundedness).
Then for all `x > 0`, `t ≥ 0`: `y x t = ∫_0^t f(τ) (-(e^{-x²/(4(t-τ))}/√(π(t-τ)))) dτ`. -/
@[kb "lebldiffyqs2026" "Example 6.5.3, p. 324"]
theorem example_653_solution {f : ℝ → ℝ} {M c s₀ : ℝ} {y : ℝ → ℝ → ℝ} {dY : ℝ → ℝ → ℝ}
    (hfc : ContinuousOn f (Ici 0)) (hf : ExpOrder f M c)
    (hyc : ∀ x, 0 < x → ContinuousOn (y x) (Ici 0))
    (hyo : ∀ x, 0 < x → ∃ N d, ExpOrder (y x) N d)
    (hY : ∀ s, s₀ < s → ∀ x, 0 < x → HasDerivAt (fun x => laplace (y x) s) (dY s x) x)
    (hdY : ∀ s, s₀ < s → ∀ x, 0 < x → HasDerivAt (dY s) (s * laplace (y x) s) x)
    (hc : ∀ s, s₀ < s → ContinuousWithinAt (fun x => laplace (y x) s) (Ici 0) 0)
    (hdc : ∀ s, s₀ < s → ContinuousWithinAt (dY s) (Ici 0) 0)
    (hF : ∀ s, s₀ < s → dY s 0 = laplace f s)
    (hB : ∀ s, s₀ < s → ∃ B, ∀ x, 0 ≤ x → |laplace (y x) s| ≤ B) :
    ∀ x, 0 < x → ∀ t, 0 ≤ t → y x t = conv0 f (fun τ => -heatKernel x τ) t := by
  intro x hx
  obtain ⟨N, d, hN⟩ := hyo x hx
  set c' := max c 0 with hc'
  have hc0 : 0 ≤ c' := le_max_right _ _
  have hf' : ExpOrder f M c' := lu_expOrder_mono hf (le_max_left _ _)
  have hg : ExpOrder (fun t => -heatKernel x t) (2 / (x * Real.sqrt π)) c' := expOrder_heatKernel hx hc0
  have hcv : ExpOrder (conv0 f (fun τ => -heatKernel x τ)) (M * (2 / (x * Real.sqrt π)) / 1) (c' + 1) :=
    conv0_expOrder hf' hg one_pos
  refine laplace_unique_of_gt (s₀ := max s₀ c') (hyc x hx) (continuousOn_conv0 hfc (continuousOn_heatKernel hx).neg) hN hcv ?_
  intro s hs
  have hs1 : s₀ < s := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : c' < s := lt_of_le_of_lt (le_max_right _ _) hs
  have hs0 : 0 < s := lt_of_le_of_lt hc0 hs2
  have hcs : c < s := lt_of_le_of_lt (le_max_left _ _) hs2
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  obtain ⟨B, hBd⟩ := hB s hs1
  have hode := example_653_ode (Y := fun x => laplace (y x) s) (dY := dY s) (r := Real.sqrt s)
    (F := laplace f s) (B := B) hr (hY s hs1) (by
      intro x' hx'
      rw [Real.sq_sqrt hs0.le]
      exact hdY s hs1 x' hx') (hc s hs1) (hdc s hs1) (hF s hs1) hBd x hx.le
  rw [hode]
  have hinv := example_653_inversion (M := M) (c := c) (x := x) (s := s) hx hs0 hfc hf hcs
  rw [hinv]

end UndergradKB.DifferentialEquations
