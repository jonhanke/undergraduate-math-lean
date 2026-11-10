import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.Jacobian
import UndergradKB.Common.Attr
import UndergradKB.Calculus.StokesParam

/-! # Calculus: the divergence theorem for parametrized solids

OpenStax Calculus 3 §6.8. Mathlib proves the divergence theorem for boxes
(`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`). We pull it back along a `C²` map `Φ` of a box
`[a, b] ⊆ ℝ³` (coordinates `z₀, z₁, z₂`, partial derivatives `Φᵢ`): the pulled-back field
`Gᵢ = F(Φ) · (Φⱼ × Φₖ)` (`(i, j, k)` cyclic) has divergence `div F(Φ) · det DΦ` (the second derivatives of `Φ`
cancel by symmetry and the antisymmetry of the cross product; the first-order terms give the trace of `DF` times the
triple product), so `∭_{[a,b]} div F(Φ) det DΦ = Σ` (flux of `F` through the six parametrized faces), and by the
change of variables formula `∭_{Φ(S)} div F dV` equals the same sum when `Φ` is injective and orientation preserving.
Consequence: the flux of `r/‖r‖³` (and Gauss' law) out of any parametrized solid not containing the origin is `0`.

Missing for the book's statement in full generality: solids bounded by arbitrary closed piecewise smooth surfaces
(not images of one box), which needs oriented piecewise smooth surfaces and gluing; not in Mathlib. -/

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

/-- The cyclic successor `i ↦ i + 1` on `Fin 3`. -/
def cyc1 : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The cyclic successor `i ↦ i + 2` on `Fin 3`. -/
def cyc2 : Fin 3 → Fin 3 := ![2, 0, 1]

@[simp] theorem cyc1_zero : cyc1 0 = 1 := rfl
@[simp] theorem cyc1_one : cyc1 1 = 2 := rfl
@[simp] theorem cyc1_two : cyc1 2 = 0 := rfl
@[simp] theorem cyc2_zero : cyc2 0 = 2 := rfl
@[simp] theorem cyc2_one : cyc2 1 = 0 := rfl
@[simp] theorem cyc2_two : cyc2 2 = 1 := rfl

/-- The cross product as a continuous bilinear map. -/
noncomputable def crossCLM : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ crossProduct)

theorem crossCLM_apply (u v : Fin 3 → ℝ) : crossCLM u v = crossProduct u v := rfl

/-- Bridging definition: the divergence `P_x + Q_y + R_z` of a field `F = (P, Q, R)` of `ℝ³` (as `Fin 3 → ℝ`). -/
noncomputable def divVec (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ m : Fin 3, fderiv ℝ F x (Pi.single m 1) m

/-- Bridging definition: the Jacobian determinant `Φ₀ · (Φ₁ × Φ₂)` of a map `Φ` of `ℝ³` (`Φᵢ` the partial
derivatives). -/
noncomputable def jacobian3 (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (z : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ Φ z (Pi.single 0 1) ⬝ᵥ crossProduct (fderiv ℝ Φ z (Pi.single 1 1)) (fderiv ℝ Φ z (Pi.single 2 1))

theorem clm_vec3_apply (L : (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    L x = x 0 • L (Pi.single 0 1) + x 1 • L (Pi.single 1 1) + x 2 • L (Pi.single 2 1) := by
  conv_lhs => rw [vec3_eq x]
  simp only [map_add, map_smul]

/-- `Σ_cyc L(pᵢ) · (pⱼ × pₖ) = tr L · p₀ · (p₁ × p₂)`. -/
theorem cyclic_trace_identity (L : (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ) (p q r : Fin 3 → ℝ) :
    L p ⬝ᵥ crossProduct q r + L q ⬝ᵥ crossProduct r p + L r ⬝ᵥ crossProduct p q =
      (L (Pi.single 0 1) 0 + L (Pi.single 1 1) 1 + L (Pi.single 2 1) 2) * (p ⬝ᵥ crossProduct q r) := by
  rw [clm_vec3_apply L p, clm_vec3_apply L q, clm_vec3_apply L r]
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dot_cross_add_dot_cross_swap (w u v : Fin 3 → ℝ) :
    w ⬝ᵥ crossProduct u v + w ⬝ᵥ crossProduct v u = 0 := by
  rw [← cross_anticomm, dotProduct_neg, neg_add_cancel]

/-- OpenStax Calculus 3:Theorem 6.20 (CA-661), divergence theorem for a parametrized solid, parameter form: for
`F` of class `C¹` on an open set `U` and `Φ` of class `C²` mapping the box `[a, b]` into `U`, the integral over the
box of `div F(Φ) · det DΦ` equals the flux of `F` through the six faces of the solid `Φ([a, b])`: for each
coordinate `i` (with `(i, j, k)` cyclic), the integral over the front face (`zᵢ = bᵢ`) of `F(Φ) · (Φⱼ × Φₖ)` minus
that over the back face (`zᵢ = aᵢ`), the faces parametrized by the two remaining coordinates (`Fin.insertNth`). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.20, p. 730"]
theorem divergence_param_box (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (hΦ : ContDiff ℝ 2 Φ) {a b : Fin 3 → ℝ}
    (hle : a ≤ b) (hΦU : ∀ z ∈ Icc a b, Φ z ∈ U) :
    (∫ z in Icc a b, divVec F (Φ z) * jacobian3 Φ z) =
      ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Φ (i.insertNth (b i) y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc2 i) 1))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Φ (i.insertNth (a i) y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc2 i) 1))) := by
  set V := Φ ⁻¹' U with hVdef
  have hBV : Icc a b ⊆ V := fun z hz => hΦU z hz
  have hΦ1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  set h : Fin 3 → (Fin 3 → ℝ) → Fin 3 → ℝ := fun j z => fderiv ℝ Φ z (Pi.single j 1) with hhdef
  set h' : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ := fun j z =>
    (fderiv ℝ (fderiv ℝ Φ) z).flip (Pi.single j 1) with hh'def
  have hh : ∀ j z, HasFDerivAt (h j) (h' j z) z := by
    intro j z
    have := ((hΦ1.differentiable one_ne_zero z).hasFDerivAt).clm_apply (hasFDerivAt_const (Pi.single j 1) z)
    simpa [hhdef, hh'def] using this
  have hFΦ : ∀ z ∈ V, HasFDerivAt (fun z => F (Φ z)) ((fderiv ℝ F (Φ z)).comp (fderiv ℝ Φ z)) z := by
    intro z hz
    exact ((hF.differentiableOn one_ne_zero (Φ z) hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt.comp z
      (hΦ.differentiable (by norm_num) z).hasFDerivAt
  -- the pulled-back field
  set G : (Fin 3 → ℝ) → Fin 3 → ℝ := fun z i => dotCLM (F (Φ z)) (crossCLM (h (cyc1 i) z) (h (cyc2 i) z))
    with hGdef
  have hcr : ∀ j k z, HasFDerivAt (fun z => crossCLM (h j z) (h k z))
      ((crossCLM (h j z)).comp (h' k z) + (crossCLM.comp (h' j z)).flip (h k z)) z := fun j k z =>
    (crossCLM.hasFDerivAt.comp z (hh j z)).clm_apply (hh k z)
  set D : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ := fun i z =>
    (dotCLM (F (Φ z))).comp ((crossCLM (h (cyc1 i) z)).comp (h' (cyc2 i) z) +
        (crossCLM.comp (h' (cyc1 i) z)).flip (h (cyc2 i) z)) +
      (dotCLM.comp ((fderiv ℝ F (Φ z)).comp (fderiv ℝ Φ z))).flip
        (crossCLM (h (cyc1 i) z) (h (cyc2 i) z)) with hDdef
  have hD : ∀ i, ∀ z ∈ V, HasFDerivAt (fun z => G z i) (D i z) z := by
    intro i z hz
    exact (dotCLM.hasFDerivAt.comp z (hFΦ z hz)).clm_apply (hcr _ _ z)
  have hDapp : ∀ i z v, D i z v =
      F (Φ z) ⬝ᵥ crossProduct (h (cyc1 i) z) (fderiv ℝ (fderiv ℝ Φ) z v (Pi.single (cyc2 i) 1)) +
      F (Φ z) ⬝ᵥ crossProduct (fderiv ℝ (fderiv ℝ Φ) z v (Pi.single (cyc1 i) 1)) (h (cyc2 i) z) +
      fderiv ℝ F (Φ z) (fderiv ℝ Φ z v) ⬝ᵥ crossProduct (h (cyc1 i) z) (h (cyc2 i) z) := by
    intro i z v
    simp only [hDdef, hh'def, add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.flip_apply, dotCLM_apply, crossCLM_apply, map_add]
  have hDT : ∀ z ∈ Icc a b, ∑ i : Fin 3, D i z (Pi.single i 1) = divVec F (Φ z) * jacobian3 Φ z := by
    intro z _
    have hs := (hΦ.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
    simp only [hDapp, Fin.sum_univ_three, cyc1_zero, cyc1_one, cyc1_two, cyc2_zero, cyc2_one, cyc2_two, hhdef]
    rw [hs (Pi.single 1 1) (Pi.single 0 1), hs (Pi.single 2 1) (Pi.single 1 1),
      hs (Pi.single 2 1) (Pi.single 0 1)]
    have t := cyclic_trace_identity (fderiv ℝ F (Φ z)) (fderiv ℝ Φ z (Pi.single 0 1))
      (fderiv ℝ Φ z (Pi.single 1 1)) (fderiv ℝ Φ z (Pi.single 2 1))
    have a1 := dot_cross_add_dot_cross_swap (F (Φ z)) (fderiv ℝ Φ z (Pi.single 1 1))
      (fderiv ℝ (fderiv ℝ Φ) z (Pi.single 0 1) (Pi.single 2 1))
    have a2 := dot_cross_add_dot_cross_swap (F (Φ z)) (fderiv ℝ Φ z (Pi.single 2 1))
      (fderiv ℝ (fderiv ℝ Φ) z (Pi.single 0 1) (Pi.single 1 1))
    have a3 := dot_cross_add_dot_cross_swap (F (Φ z)) (fderiv ℝ Φ z (Pi.single 0 1))
      (fderiv ℝ (fderiv ℝ Φ) z (Pi.single 1 1) (Pi.single 2 1))
    rw [divVec, jacobian3, Fin.sum_univ_three]
    linear_combination t + a1 + a2 + a3
  -- continuity
  have cF : ContinuousOn (fun z => fderiv ℝ F (Φ z)) (Icc a b) :=
    (hF.continuousOn_fderiv_of_isOpen hU le_rfl).comp hΦ.continuous.continuousOn (fun z hz => hΦU z hz)
  have c4 : Continuous (fun z => fderiv ℝ Φ z) := hΦ.continuous_fderiv (by norm_num)
  have ce : ∀ j : Fin 3, Continuous (fun z => fderiv ℝ Φ z (Pi.single j 1)) := fun j =>
    c4.clm_apply continuous_const
  have hTc : ContinuousOn (fun z => divVec F (Φ z) * jacobian3 Φ z) (Icc a b) := by
    have cdiv : ContinuousOn (fun z => divVec F (Φ z)) (Icc a b) := by
      unfold divVec
      exact continuousOn_finsetSum _ (fun m _ =>
        (continuous_apply m).comp_continuousOn (cF.clm_apply continuousOn_const))
    have cjac : Continuous (jacobian3 Φ) := by
      unfold jacobian3
      have := ce 0
      have := ce 1
      have := ce 2
      simp only [dotProduct, Fin.sum_univ_three, cross_apply]
      fun_prop
    exact cdiv.mul cjac.continuousOn
  have hGc : ContinuousOn G (Icc a b) := by
    have c1 : ContinuousOn (fun z => F (Φ z)) (Icc a b) :=
      hF.continuousOn.comp hΦ.continuous.continuousOn (fun z hz => hΦU z hz)
    refine continuousOn_pi.2 (fun i => ?_)
    simp only [hGdef, dotCLM_apply, crossCLM_apply, hhdef, dotProduct, Fin.sum_univ_three, cross_apply]
    have c1' : ∀ m, ContinuousOn (fun z => F (Φ z) m) (Icc a b) := fun m =>
      (continuous_apply m).comp_continuousOn c1
    have c2' : ∀ m j, Continuous (fun z => fderiv ℝ Φ z (Pi.single j 1) m) := fun m j =>
      (continuous_apply m).comp (ce j)
    exact (((c1' 0).mul (((c2' 1 _).mul (c2' 2 _)).sub ((c2' 2 _).mul (c2' 1 _))).continuousOn).add
      ((c1' 1).mul (((c2' 2 _).mul (c2' 0 _)).sub ((c2' 0 _).mul (c2' 2 _))).continuousOn)).add
      ((c1' 2).mul (((c2' 0 _).mul (c2' 1 _)).sub ((c2' 1 _).mul (c2' 0 _))).continuousOn)
  have hint : IntegrableOn (fun z => ∑ i, (ContinuousLinearMap.pi fun i => D i z) (Pi.single i 1) i)
      (Icc a b) := by
    refine (hTc.integrableOn_compact isCompact_Icc).congr_fun (fun z hz => ?_) measurableSet_Icc
    simp only [ContinuousLinearMap.pi_apply, hDT z hz]
  have key := integral_divergence_of_hasFDerivAt_off_countable a b hle G
    (fun z => ContinuousLinearMap.pi fun i => D i z) ∅ countable_empty hGc
    (fun z hz => hasFDerivAt_pi.2 (fun i => hD i z (hBV ⟨fun j => (hz.1 j trivial).1.le,
      fun j => (hz.1 j trivial).2.le⟩))) hint
  rw [setIntegral_congr_fun measurableSet_Icc (fun z hz => by
    simp only [ContinuousLinearMap.pi_apply]; exact hDT z hz)] at key
  rw [key]
  simp only [hGdef, dotCLM_apply, crossCLM_apply, hhdef]

/-- The determinant of a linear map of `ℝ³` is the triple product of the images of the standard basis. -/
theorem det_eq_triple (L : (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ) :
    L.det = L (Pi.single 0 1) ⬝ᵥ crossProduct (L (Pi.single 1 1)) (L (Pi.single 2 1)) := by
  rw [triple_product_eq_det, ContinuousLinearMap.det, ← LinearMap.det_toMatrix', ← Matrix.det_transpose]
  congr 1
  ext i j
  fin_cases i <;> simp [LinearMap.toMatrix'_apply]

/-- OpenStax Calculus 3:Theorem 6.20 (CA-661), divergence theorem for a parametrized solid: let `E = Φ(S)` where
`S` lies between the open and the closed box `[a, b]`, `Φ` is `C²`, injective on `S` and orientation preserving
(`det DΦ ≥ 0` on `S`), so that the boundary surface of `E` is the image of the boundary of the box with the outward
orientation. For `F` of class `C¹` on an open set containing `Φ([a, b])`, `∭_E div F dV` equals the outward flux of
`F` through the six parametrized faces (as in `divergence_param_box`). Examples: balls (spherical coordinates),
cylinders, solids between two graphs. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.20, p. 730"]
theorem divergence_param_image (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (hΦ : ContDiff ℝ 2 Φ) {a b : Fin 3 → ℝ}
    (hle : a ≤ b) (hΦU : ∀ z ∈ Icc a b, Φ z ∈ U) {S : Set (Fin 3 → ℝ)} (hS : MeasurableSet S)
    (hSsub : S ⊆ Icc a b) (hSsup : (Set.pi univ fun i => Ioo (a i) (b i)) ⊆ S) (hinj : InjOn Φ S)
    (hjac : ∀ z ∈ S, 0 ≤ jacobian3 Φ z) :
    ∫ x in Φ '' S, divVec F x =
      ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Φ (i.insertNth (b i) y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc2 i) 1))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Φ (i.insertNth (a i) y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc2 i) 1))) := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z _ => (hd z).hasFDerivAt.hasFDerivWithinAt) hinj]
  rw [setIntegral_congr_fun hS (g := fun z => divVec F (Φ z) * jacobian3 Φ z) (fun z hz => by
    simp only [smul_eq_mul]
    rw [det_eq_triple, ← jacobian3, abs_of_nonneg (hjac z hz), mul_comm])]
  have hae : S =ᵐ[volume] Icc a b := by
    have h : (Set.pi univ fun i => Ioo (a i) (b i)) =ᵐ[volume] Icc a b := by
      rw [volume_pi]
      exact Measure.univ_pi_Ioo_ae_eq_Icc
    exact Filter.EventuallyLE.antisymm (Filter.Eventually.of_forall hSsub)
      (h.symm.le.trans (Filter.Eventually.of_forall hSsup))
  rw [setIntegral_congr_set hae]
  exact divergence_param_box F hU hF Φ hΦ hle hΦU

end UndergradKB.Calculus
