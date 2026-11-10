import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.CrossProduct
import UndergradKB.Common.Attr

/-! # Calculus: Kepler's first law from the inverse-square law

For a motion `r : ℝ → Fin 3 → ℝ` with `r'' = -(μ/‖r‖³) r` (`μ > 0`, `r ≠ 0`) we show that the angular
momentum `L = r × r'` and the Laplace–Runge–Lenz vector `A = r' × L - μ r/‖r‖` are constant, and
deduce the focal polar equation of a conic, `‖r‖ (μ + ‖A‖ cos θ) = ‖L‖²`, with `θ` the angle between
`r` and `A`; i.e. `‖r‖ = p/(1 + e cos θ)`, `e = ‖A‖/μ`, `p = ‖L‖²/μ`. When `e < 1` the orbit is bounded. -/

namespace UndergradKB.Calculus

open Real Matrix

/-- Euclidean norm on `ℝ³`. -/
noncomputable def keplerNorm (a : Fin 3 → ℝ) : ℝ := √(a ⬝ᵥ a)

theorem keplerDotself_nonneg (a : Fin 3 → ℝ) : 0 ≤ a ⬝ᵥ a := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1), mul_self_nonneg (a 2)]

theorem keplerNorm_sq (a : Fin 3 → ℝ) : keplerNorm a ^ 2 = a ⬝ᵥ a :=
  Real.sq_sqrt (keplerDotself_nonneg a)

theorem keplerNorm_nonneg (a : Fin 3 → ℝ) : 0 ≤ keplerNorm a := Real.sqrt_nonneg _

theorem keplerNorm_pos {a : Fin 3 → ℝ} (h : a ≠ 0) : 0 < keplerNorm a := by
  apply Real.sqrt_pos.2
  rcases (keplerDotself_nonneg a).lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (dotProduct_self_eq_zero.1 h1.symm) h

theorem keplerDot_hasDerivAt {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  have := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hf' i).mul (hg' i))
  simp only [dotProduct, ← Finset.sum_add_distrib]
  convert this using 1
  ext s; simp

theorem keplerCross_hasDerivAt {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⨯₃ g s) (f' ⨯₃ g t + f t ⨯₃ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · have := ((hf' 1).mul (hg' 2)).sub ((hf' 2).mul (hg' 1))
    convert this using 1
    · ext s; simp [cross_apply]
    · simp [cross_apply]; ring
  · have := ((hf' 2).mul (hg' 0)).sub ((hf' 0).mul (hg' 2))
    convert this using 1
    · ext s; simp [cross_apply]
    · simp [cross_apply]; ring
  · have := ((hf' 0).mul (hg' 1)).sub ((hf' 1).mul (hg' 0))
    convert this using 1
    · ext s; simp [cross_apply]
    · simp [cross_apply]; ring

/-- Derivative of the unit vector `v/‖v‖`. -/
theorem keplerUnit_hasDerivAt {v : ℝ → Fin 3 → ℝ} {b : Fin 3 → ℝ} {t : ℝ}
    (hv : HasDerivAt v b t) (ha : v t ≠ 0) :
    HasDerivAt (fun s => (keplerNorm (v s))⁻¹ • v s)
      ((keplerNorm (v t))⁻¹ • b - ((v t ⬝ᵥ b) / keplerNorm (v t) ^ 3) • v t) t := by
  have hs := keplerNorm_pos ha
  have h1 := keplerDot_hasDerivAt hv hv
  have h2 : HasDerivAt (fun s => keplerNorm (v s))
      ((b ⬝ᵥ v t + v t ⬝ᵥ b) / (2 * keplerNorm (v t))) t := by
    have := h1.sqrt (ne_of_gt (by rw [← keplerNorm_sq]; exact pow_pos hs 2))
    exact this
  have h3 := h2.inv hs.ne'
  have h4 := h3.smul hv
  convert h4 using 1
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [dotProduct_comm b (v t)]
  simp only [Pi.inv_apply]
  field_simp
  ring

theorem keplerDeriv_hasDerivAt {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) (t : ℝ) :
    HasDerivAt (deriv r) (deriv (deriv r) t) t :=
  (hr.differentiable_deriv_two t).hasDerivAt

/-- The inverse-square law `r'' = -(μ/‖r‖³) r`. -/
def KeplerMotion (μ : ℝ) (r : ℝ → Fin 3 → ℝ) : Prop :=
  ContDiff ℝ 2 r ∧ (∀ t, r t ≠ 0) ∧
    ∀ t, deriv (deriv r) t = (-(μ / keplerNorm (r t) ^ 3)) • r t

/-- Angular momentum `L = r × r'` has derivative `0`. -/
theorem kepler_L_hasDerivAt {μ : ℝ} {r : ℝ → Fin 3 → ℝ} (h : KeplerMotion μ r) (s : ℝ) :
    HasDerivAt (fun u => r u ⨯₃ deriv r u) 0 s := by
  obtain ⟨hr, -, hK⟩ := h
  have hr1 : Differentiable ℝ r := hr.differentiable (by norm_num)
  have := keplerCross_hasDerivAt (hr1 s).hasDerivAt (keplerDeriv_hasDerivAt hr s)
  convert this using 1
  rw [hK s, map_smul, cross_self, cross_self]; simp

/-- OpenStax Calculus 3:Theorem 3.9 (CA-502), Kepler's second law ingredient: under the inverse-square
law, `L = r × r'` is constant. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem kepler_angularMomentum_const {μ : ℝ} {r : ℝ → Fin 3 → ℝ} (h : KeplerMotion μ r) (t : ℝ) :
    r t ⨯₃ deriv r t = r 0 ⨯₃ deriv r 0 :=
  is_const_of_deriv_eq_zero (fun u => (kepler_L_hasDerivAt h u).differentiableAt)
    (fun u => (kepler_L_hasDerivAt h u).deriv) t 0

/-- The Laplace–Runge–Lenz vector `A = r' × L - μ r/‖r‖`. -/
noncomputable def keplerLRL (μ : ℝ) (r : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  deriv r t ⨯₃ (r t ⨯₃ deriv r t) - μ • ((keplerNorm (r t))⁻¹ • r t)

theorem kepler_smul_cross (c : ℝ) (u w : Fin 3 → ℝ) : (c • u) ⨯₃ w = c • (u ⨯₃ w) := by
  ext i; fin_cases i <;> simp [cross_apply]

theorem kepler_LRL_hasDerivAt{μ : ℝ} {r : ℝ → Fin 3 → ℝ} (h : KeplerMotion μ r) (s : ℝ) :
    HasDerivAt (keplerLRL μ r) 0 s := by
  have h' := h
  obtain ⟨hr, hne, hK⟩ := h
  have hr1 : Differentiable ℝ r := hr.differentiable (by norm_num)
  have h1 := keplerCross_hasDerivAt (keplerDeriv_hasDerivAt hr s) (kepler_L_hasDerivAt h' s)
  have h2 := (keplerUnit_hasDerivAt (hr1 s).hasDerivAt (hne s)).const_smul μ
  have := h1.sub h2
  refine HasDerivAt.congr_deriv (show HasDerivAt (keplerLRL μ r) _ s from this) ?_
  have hs := keplerNorm_pos (hne s)
  have e : r s ⬝ᵥ r s = keplerNorm (r s) ^ 2 := (keplerNorm_sq _).symm
  rw [hK s, kepler_smul_cross, cross_cross_eq_smul_sub_smul', e, map_zero, add_zero]
  ext i
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- OpenStax Calculus 3:Theorem 3.9 (CA-502), Kepler's first law ingredient: under the inverse-square
law the Laplace–Runge–Lenz vector `A = r' × L - μ r/‖r‖` is constant. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem kepler_LRL_const {μ : ℝ} {r : ℝ → Fin 3 → ℝ} (h : KeplerMotion μ r) (t : ℝ) :
    keplerLRL μ r t = keplerLRL μ r 0 :=
  is_const_of_deriv_eq_zero (fun u => (kepler_LRL_hasDerivAt h u).differentiableAt)
    (fun u => (kepler_LRL_hasDerivAt h u).deriv) t 0

theorem kepler_triple (u v : Fin 3 → ℝ) : u ⬝ᵥ (v ⨯₃ (u ⨯₃ v)) = (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- Cauchy–Schwarz on `ℝ³`. -/
theorem kepler_abs_dot_le (a b : Fin 3 → ℝ) : |a ⬝ᵥ b| ≤ keplerNorm a * keplerNorm b := by
  have h1 := keplerDotself_nonneg (a ⨯₃ b)
  rw [cross_dot_cross] at h1
  apply abs_le_of_sq_le_sq _ (mul_nonneg (keplerNorm_nonneg a) (keplerNorm_nonneg b))
  rw [mul_pow, keplerNorm_sq, keplerNorm_sq]
  rw [dotProduct_comm b a] at h1
  nlinarith

/-- `r · A = ‖L‖² - μ‖r‖`. -/
theorem kepler_dot_LRL {μ : ℝ} {r : ℝ → Fin 3 → ℝ} (h : KeplerMotion μ r) (t : ℝ) :
    r t ⬝ᵥ keplerLRL μ r 0 = keplerNorm (r 0 ⨯₃ deriv r 0) ^ 2 - μ * keplerNorm (r t) := by
  have hne := h.2.1 t
  have hs := keplerNorm_pos hne
  rw [← kepler_LRL_const h t, keplerLRL, dotProduct_sub, kepler_triple, keplerNorm_sq,
    kepler_angularMomentum_const h t, dotProduct_smul, dotProduct_smul,
    ← keplerNorm_sq (r t)]
  simp only [smul_eq_mul]
  field_simp

/-- OpenStax Calculus 3:Theorem 3.9 (CA-502), Kepler's first law (polar equation of the orbit): under the
inverse-square law with `μ > 0`, `L = r(0) × r'(0)` and `A = keplerLRL μ r 0 ≠ 0`, for the angle `θ`
between `r(t)` and `A` (`cos θ = r·A/(‖r‖‖A‖)`) one has `‖r‖ (μ + ‖A‖ cos θ) = ‖L‖²`; equivalently
`‖r‖ = p/(1 + e cos θ)` with `e = ‖A‖/μ`, `p = ‖L‖²/μ`: a conic with a focus at the origin. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem kepler_polar_equation {μ : ℝ} {r : ℝ → Fin 3 → ℝ} (h : KeplerMotion μ r) (hμ : 0 < μ)
    (hA : keplerLRL μ r 0 ≠ 0) (t : ℝ) :
    keplerNorm (r t) *
        (1 + (keplerNorm (keplerLRL μ r 0) / μ) *
          ((r t ⬝ᵥ keplerLRL μ r 0) / (keplerNorm (r t) * keplerNorm (keplerLRL μ r 0))))
      = keplerNorm (r 0 ⨯₃ deriv r 0) ^ 2 / μ := by
  have hs := keplerNorm_pos (h.2.1 t)
  have hA' := keplerNorm_pos hA
  rw [kepler_dot_LRL h t]
  field_simp
  ring

/-- The orbit is bounded when the eccentricity `e = ‖A‖/μ` is `< 1`: then
`‖r(t)‖ ≤ ‖L‖²/(μ - ‖A‖)`, so the conic of `kepler_polar_equation` is an ellipse. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem kepler_orbit_bounded {μ : ℝ} {r : ℝ → Fin 3 → ℝ} (h : KeplerMotion μ r)
    (he : keplerNorm (keplerLRL μ r 0) < μ) (t : ℝ) :
    keplerNorm (r t) ≤ keplerNorm (r 0 ⨯₃ deriv r 0) ^ 2 / (μ - keplerNorm (keplerLRL μ r 0)) := by
  have h1 := kepler_dot_LRL h t
  have h2 := kepler_abs_dot_le (r t) (keplerLRL μ r 0)
  have h3 := (abs_le.1 h2).1
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end UndergradKB.Calculus
