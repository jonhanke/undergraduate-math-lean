import Mathlib.Analysis.Complex.AbelLimit
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.PoissonKernel
import UndergradKB.DifferentialEquations.FourierConvergence

/-! # The disc solution takes the boundary values

Lebl, *Notes on Diffy Qs*, §4.10: the series solution `u(r,θ) = a₀/2 + ∑ rⁿ (aₙ cos nθ + bₙ sin nθ)` of the
Dirichlet problem on the unit disc tends to the boundary data `g(θ)` as `r → 1⁻`.  For `C¹` periodic data this
follows from the convergence of the Fourier series of `g` (`fourier_series_C1`) and Abel's limit theorem
(`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`). -/

namespace UndergradKB.DifferentialEquations

open Real Complex MeasureTheory Filter Topology

lemma fourierA_pi_eq (g : ℝ → ℝ) (n : ℕ) : fourierA g π n = discCoeffA g n := by
  unfold fourierA discCoeffA
  rw [intervalIntegral.integral_congr (g := fun t => g t * Real.cos (n * t)) (fun t _ => by
    simp only
    rw [show (n : ℝ) * π / π * t = n * t by field_simp])]

lemma fourierB_pi_eq (g : ℝ → ℝ) (n : ℕ) : fourierB g π n = discCoeffB g n := by
  unfold fourierB discCoeffB
  rw [intervalIntegral.integral_congr (g := fun t => g t * Real.sin (n * t)) (fun t _ => by
    simp only
    rw [show (n : ℝ) * π / π * t = n * t by field_simp])]

/-- **Boundary values of the disc solution (DE-151).** If the boundary data `g` is `2π`-periodic and
continuously differentiable, the series solution of the Dirichlet problem on the unit disc built from the
Fourier coefficients of `g` satisfies `u(r e^{iθ}) → g(θ)` as `r → 1⁻`, for every `θ`. Together with
`disc_dirichlet_poisson` (harmonic in the disc, equal to the Poisson integral) this solves the Dirichlet problem. -/
@[kb "lebldiffyqs2026" "§4.10 series solution, p. 265"]
theorem disc_dirichlet_boundary {g g' : ℝ → ℝ} (hper : Function.Periodic g (2 * π))
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (θ : ℝ) :
    Tendsto (fun r : ℝ => discSeries (discCoeffA g) (discCoeffB g) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
      (𝓝[<] 1) (𝓝 (g θ)) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hint : IntervalIntegrable g volume (-π) π := hgc.intervalIntegrable _ _
  obtain ⟨ha, hb⟩ := discCoeff_bounded hint
  set X : ℕ → ℝ := fun n => discCoeffA g (n + 1) * Real.cos ((n + 1 : ℝ) * θ)
    + discCoeffB g (n + 1) * Real.sin ((n + 1 : ℝ) * θ) with hX
  -- the Fourier series of `g` at `θ`
  have hF := fourier_series_C1 Real.pi_pos hper hg hg' θ
  have hsum : HasSum X (g θ - discCoeffA g 0 / 2) := by
    rw [fourierA_pi_eq] at hF
    convert hF using 1
    funext n
    simp only [hX, fourierA_pi_eq, fourierB_pi_eq]
    rw [show ((n + 1 : ℕ) : ℝ) * π / π * θ = (n + 1 : ℝ) * θ by push_cast; field_simp]
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hsum.tendsto_sum_nat
  have hlim : Tendsto (fun r : ℝ => discCoeffA g 0 / 2 + r * ∑' n, X n * r ^ n) (𝓝[<] 1)
      (𝓝 (discCoeffA g 0 / 2 + 1 * (g θ - discCoeffA g 0 / 2))) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul habel)
  rw [one_mul, add_sub_cancel] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hpol := discSeries_polar ha hb hr.1.le hr.2 θ
  have heq : (fun n : ℕ => r ^ (n + 1) * (discCoeffA g (n + 1) * Real.cos ((n + 1 : ℝ) * θ)
      + discCoeffB g (n + 1) * Real.sin ((n + 1 : ℝ) * θ))) = fun n => r * (X n * r ^ n) := by
    funext n; simp only [hX]; ring
  rw [heq] at hpol
  have := hpol.tsum_eq
  rw [tsum_mul_left] at this
  linarith

end UndergradKB.DifferentialEquations
