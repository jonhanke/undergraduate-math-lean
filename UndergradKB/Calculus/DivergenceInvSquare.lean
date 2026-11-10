import UndergradKB.Common.Attr
import UndergradKB.Calculus.DivergenceParam
import UndergradKB.Calculus.InverseSquareFlux

/-! # Calculus: flux of the inverse-square field out of solids not containing the origin

OpenStax Calculus 3 §6.8 (Theorem 6.21, Gauss' law), the case of a closed surface that does not enclose the origin:
the field `r/‖r‖³` is `C¹` off the origin with divergence `0` there, so by `divergence_param_box` its total outward
flux through the faces of any `C²`-parametrized solid `Φ([a, b])` not containing the origin is `0`; the same holds for
the field `(q/(4π ε₀)) r/‖r‖³` of a point charge (Gauss' law with no enclosed charge). -/

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

theorem dotProduct_self_ne_zero {x : Fin 3 → ℝ} (hx : x ≠ 0) : x ⬝ᵥ x ≠ 0 :=
  fun h => hx (dotProduct_self_eq_zero.1 h)

theorem contDiff_dotProduct_self : ContDiff ℝ 2 (fun x : Fin 3 → ℝ => x ⬝ᵥ x) := by
  simp only [dotProduct, Fin.sum_univ_three]
  fun_prop

/-- `r/‖r‖³` is `C¹` away from the origin. -/
theorem contDiffOn_invSquareField : ContDiffOn ℝ 1 invSquareField {x | x ≠ 0} := by
  intro x hx
  have hq : ContDiffAt ℝ 1 (fun x : Fin 3 → ℝ => x ⬝ᵥ x) x := (contDiff_dotProduct_self.of_le (by norm_num)).contDiffAt
  have hs : ContDiffAt ℝ 1 (fun x : Fin 3 → ℝ => Real.sqrt (x ⬝ᵥ x)) x := hq.sqrt (dotProduct_self_ne_zero hx)
  have hpos : 0 < Real.sqrt (x ⬝ᵥ x) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
      (Ne.symm (dotProduct_self_ne_zero hx)))
  have hi : ContDiffAt ℝ 1 (fun x : Fin 3 → ℝ => (Real.sqrt (x ⬝ᵥ x) ^ 3)⁻¹) x :=
    (hs.pow 3).inv (by positivity)
  exact (hi.smul contDiffAt_id).contDiffWithinAt

theorem dotProduct_add_smul_single_self (x : Fin 3 → ℝ) (m : Fin 3) (t : ℝ) :
    (x + t • Pi.single m 1) ⬝ᵥ (x + t • Pi.single m 1) = x ⬝ᵥ x + 2 * t * x m + t ^ 2 := by
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, single_dotProduct,
    dotProduct_single, smul_eq_mul, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
  ring

/-- The partial derivative `∂/∂xₘ (xₘ/‖x‖³) = 1/‖x‖³ - 3 xₘ²/‖x‖⁵` off the origin. -/
theorem fderiv_invSquareField_single {x : Fin 3 → ℝ} (hx : x ≠ 0) (m : Fin 3) :
    fderiv ℝ invSquareField x (Pi.single m 1) m =
      1 * ((Real.sqrt (x ⬝ᵥ x)) ^ 3)⁻¹ +
        x m * (-(3 * Real.sqrt (x ⬝ᵥ x) ^ 2 * (2 * x m / (2 * Real.sqrt (x ⬝ᵥ x)))) /
          (Real.sqrt (x ⬝ᵥ x) ^ 3) ^ 2) := by
  have hq0 : x ⬝ᵥ x ≠ 0 := dotProduct_self_ne_zero hx
  have hr : 0 < Real.sqrt (x ⬝ᵥ x) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)) (Ne.symm hq0))
  have hdiff : DifferentiableAt ℝ invSquareField x :=
    (contDiffOn_invSquareField.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt one_ne_zero
  -- along the line `t ↦ x + t eₘ`
  have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single m 1 : Fin 3 → ℝ)) (Pi.single m 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single m 1 : Fin 3 → ℝ)).const_add x
  have h1 : HasDerivAt (fun t : ℝ => invSquareField (x + t • Pi.single m 1) m)
      (fderiv ℝ invSquareField x (Pi.single m 1) m) 0 := by
    have h := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have hm := (hasFDerivAt_apply (𝕜 := ℝ) m (invSquareField x)).comp_hasDerivAt_of_eq (0 : ℝ) h (by simp)
    exact hm
  -- explicit derivative
  have hQ : HasDerivAt (fun t : ℝ => x ⬝ᵥ x + 2 * t * x m + t ^ 2) (2 * x m) 0 := by
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).mul_const (x m)).const_add (x ⬝ᵥ x)).add
      (hasDerivAt_pow 2 (0 : ℝ))
    exact h.congr_deriv (by simp)
  have hQ0 : x ⬝ᵥ x + 2 * 0 * x m + 0 ^ 2 = x ⬝ᵥ x := by ring
  have hS := hQ.sqrt (by rw [hQ0]; exact hq0)
  rw [hQ0] at hS
  have hP := (hS.pow 3).inv (by simpa using (pow_pos hr 3).ne')
  have hfull := ((hasDerivAt_id (0 : ℝ)).const_add (x m)).mul hP
  have e : (fun t : ℝ => invSquareField (x + t • Pi.single m 1) m) =
      fun t => (x m + id t) * ((fun t => Real.sqrt (x ⬝ᵥ x + 2 * t * x m + t ^ 2)) t ^ 3)⁻¹ := by
    funext t
    simp only [invSquareField, surfVnorm, dotProduct_add_smul_single_self, Pi.smul_apply, smul_eq_mul,
      Pi.add_apply, Pi.single_eq_same, id]
    ring
  rw [e] at h1
  rw [h1.unique hfull]
  simp

/-- `div (r/‖r‖³) = 0` off the origin. -/
theorem divVec_invSquareField {x : Fin 3 → ℝ} (hx : x ≠ 0) : divVec invSquareField x = 0 := by
  have hq0 : x ⬝ᵥ x ≠ 0 := dotProduct_self_ne_zero hx
  have hr : 0 < Real.sqrt (x ⬝ᵥ x) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)) (Ne.symm hq0))
  have hsq : Real.sqrt (x ⬝ᵥ x) ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ x ⬝ᵥ x from Finset.sum_nonneg (fun i _ => mul_self_nonneg _))]
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  rw [divVec, Fin.sum_univ_three, fderiv_invSquareField_single hx, fderiv_invSquareField_single hx,
    fderiv_invSquareField_single hx]
  set r := Real.sqrt (x ⬝ᵥ x)
  field_simp
  linear_combination 3 * hsq

/-- OpenStax Calculus 3:Theorem 6.21 (CA-664), case of a closed surface not enclosing the origin: the total outward
flux of `r/‖r‖³` through the six faces of a solid `Φ([a, b])` (`Φ` of class `C²`) that does not contain the origin
is `0`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.21, p. 738"]
theorem flux_invSquare_param_solid_eq_zero (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    {a b : Fin 3 → ℝ} (hle : a ≤ b) (h0 : ∀ z ∈ Icc a b, Φ z ≠ 0) :
    ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        invSquareField (Φ (i.insertNth (b i) y)) ⬝ᵥ
          crossProduct (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc2 i) 1))) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        invSquareField (Φ (i.insertNth (a i) y)) ⬝ᵥ
          crossProduct (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc2 i) 1))) = 0 := by
  rw [← divergence_param_box invSquareField isOpen_ne contDiffOn_invSquareField Φ hΦ hle h0]
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ))
    (fun z hz => by simp only [divVec_invSquareField (h0 z hz), zero_mul])]
  simp

/-- OpenStax Calculus 3:§6.8 Gauss' law (CA-665), no charge enclosed: the outward flux of the field
`(q/(4π ε₀)) r/‖r‖³` of a point charge at the origin through the faces of a `C²`-parametrized solid not containing the
origin is `0`. -/
@[kb "openstaxcalculus2016" "3:§6.8 Gauss' law, p. 739"]
theorem gauss_law_param_solid_no_charge (q ε₀ : ℝ) (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    {a b : Fin 3 → ℝ} (hle : a ≤ b) (h0 : ∀ z ∈ Icc a b, Φ z ≠ 0) :
    ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        ((q / (4 * π * ε₀)) • invSquareField (Φ (i.insertNth (b i) y))) ⬝ᵥ
          crossProduct (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc2 i) 1))) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        ((q / (4 * π * ε₀)) • invSquareField (Φ (i.insertNth (a i) y))) ⬝ᵥ
          crossProduct (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc2 i) 1))) = 0 := by
  simp only [smul_dotProduct, smul_eq_mul, integral_const_mul, ← mul_sub, ← Finset.mul_sum]
  rw [flux_invSquare_param_solid_eq_zero Φ hΦ hle h0, mul_zero]

end UndergradKB.Calculus
