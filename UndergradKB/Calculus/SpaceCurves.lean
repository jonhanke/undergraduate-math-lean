import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.CrossProduct
import UndergradKB.Common.Attr

/-! # Calculus: vector-valued functions and motion in space

A space curve is a function `r : ℝ → Fin 3 → ℝ` (components `r t 0, r t 1, r t 2`); the dot product is
`⬝ᵥ`, the cross product is Mathlib's `⨯₃`, and `vnorm` is the Euclidean norm. Bridging definitions:
speed, unit tangent `T`, curvature `κ = ‖T'‖/‖r'‖` (the book's `‖dT/ds‖` after the chain rule),
principal normal `N`, binormal `B`, arc length. Includes curvature formulas, the acceleration
decomposition, projectile motion, and the area law of Kepler's second law. -/

namespace UndergradKB.Calculus

open Real Matrix

/-- Derivative of a dot product (product rule). -/theorem hasDerivAt_dot3 {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := by
  have hf' := hasDerivAt_pi.1 hf
  have hg' := hasDerivAt_pi.1 hg
  have := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hf' i).mul (hg' i))
  simp only [dotProduct, ← Finset.sum_add_distrib]
  convert this using 1
  ext s; simp

/-- Euclidean norm. -/
noncomputable def vnorm (a : Fin 3 → ℝ) : ℝ := √(a ⬝ᵥ a)

theorem dotself_nonneg3 (a : Fin 3 → ℝ) : 0 ≤ a ⬝ᵥ a := by
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1), mul_self_nonneg (a 2)]

theorem vnorm_sq (a : Fin 3 → ℝ) : vnorm a ^ 2 = a ⬝ᵥ a := Real.sq_sqrt (dotself_nonneg3 a)

theorem vnorm_nonneg (a : Fin 3 → ℝ) : 0 ≤ vnorm a := Real.sqrt_nonneg _

theorem vnorm_pos {a : Fin 3 → ℝ} (h : a ≠ 0) : 0 < vnorm a := by
  apply Real.sqrt_pos.2
  rcases (dotself_nonneg3 a).lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (dotProduct_self_eq_zero.1 h1.symm) h

/-- unit tangent of a velocity field `v`: `v / ‖v‖`. -/
theorem hasDerivAt_unit {v : ℝ → Fin 3 → ℝ} {b : Fin 3 → ℝ} {t : ℝ}
    (hv : HasDerivAt v b t) (ha : v t ≠ 0) :
    HasDerivAt (fun s => (vnorm (v s))⁻¹ • v s)
      ((vnorm (v t))⁻¹ • b - ((v t ⬝ᵥ b) / vnorm (v t) ^ 3) • v t) t := by
  have hs := vnorm_pos ha
  have h1 := hasDerivAt_dot3 hv hv
  have h2 : HasDerivAt (fun s => vnorm (v s)) ((b ⬝ᵥ v t + v t ⬝ᵥ b) / (2 * vnorm (v t))) t := by
    have := h1.sqrt (ne_of_gt (by rw [← vnorm_sq]; exact pow_pos hs 2))
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

/-- Speed `‖r'(t)‖`. -/
noncomputable def speed3 (r : ℝ → Fin 3 → ℝ) (t : ℝ) : ℝ := vnorm (deriv r t)

/-- Unit tangent `T = r'/‖r'‖`. -/
noncomputable def unitTangent3 (r : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  (speed3 r t)⁻¹ • deriv r t

/-- Curvature `‖T'‖/‖r'‖`. -/
noncomputable def curvature3 (r : ℝ → Fin 3 → ℝ) (t : ℝ) : ℝ :=
  vnorm (deriv (unitTangent3 r) t) / speed3 r t

/-- Principal unit normal `N = T'/‖T'‖`. -/
noncomputable def normalN3 (r : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  (vnorm (deriv (unitTangent3 r) t))⁻¹ • deriv (unitTangent3 r) t

/-- Binormal `B = T × N`. -/
noncomputable def binormal3 (r : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  unitTangent3 r t ⨯₃ normalN3 r t

theorem hasDerivAt_deriv3 {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) (t : ℝ) :
    HasDerivAt (deriv r) (deriv (deriv r) t) t :=
  (hr.differentiable_deriv_two t).hasDerivAt

theorem speed3_pos {r : ℝ → Fin 3 → ℝ} {t : ℝ} (h : deriv r t ≠ 0) : 0 < speed3 r t :=
  vnorm_pos h

/-- explicit form of `T'` -/
theorem hasDerivAt_unitTangent3 {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) :
    HasDerivAt (unitTangent3 r)
      ((speed3 r t)⁻¹ • deriv (deriv r) t
        - ((deriv r t ⬝ᵥ deriv (deriv r) t) / speed3 r t ^ 3) • deriv r t) t :=
  hasDerivAt_unit (hasDerivAt_deriv3 hr t) h

theorem vnorm_Tprime {a b : Fin 3 → ℝ} (ha : a ≠ 0) :
    vnorm ((vnorm a)⁻¹ • b - ((a ⬝ᵥ b) / vnorm a ^ 3) • a) = vnorm (a ⨯₃ b) / vnorm a ^ 2 := by
  have hs := vnorm_pos ha
  have key : ((vnorm a)⁻¹ • b - ((a ⬝ᵥ b) / vnorm a ^ 3) • a) ⬝ᵥ
      ((vnorm a)⁻¹ • b - ((a ⬝ᵥ b) / vnorm a ^ 3) • a) = (vnorm (a ⨯₃ b) / vnorm a ^ 2) ^ 2 := by
    rw [div_pow, vnorm_sq, cross_dot_cross]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm b a, ← vnorm_sq a]
    have := dotProduct_comm a b
    field_simp
    ring
  unfold vnorm at *
  rw [key]
  exact Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) (by positivity))

theorem hasDerivAt_vnorm3 {v : ℝ → Fin 3 → ℝ} {b : Fin 3 → ℝ} {t : ℝ}
    (hv : HasDerivAt v b t) (ha : v t ≠ 0) :
    HasDerivAt (fun s => vnorm (v s)) ((v t ⬝ᵥ b) / vnorm (v t)) t := by
  have hs := vnorm_pos ha
  have h1 := hasDerivAt_dot3 hv hv
  have h2 := h1.sqrt (ne_of_gt (by rw [← vnorm_sq]; exact pow_pos hs 2))
  refine HasDerivAt.congr_deriv (h2 : HasDerivAt (fun s => vnorm (v s)) _ t) ?_
  rw [dotProduct_comm b (v t)]
  show _ / (2 * vnorm (v t)) = _
  field_simp
  ring

/-- OpenStax Calculus 3:§3.2 Theorem 3.3 (vii) (CA-487): if `‖r‖` is constant near `t`, then
`r(t) · r'(t) = 0`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (part vii), p. 254"]
theorem dot_deriv_eq_zero_of_norm_const {r : ℝ → Fin 3 → ℝ} {r' : Fin 3 → ℝ} {t c : ℝ}
    (hr : HasDerivAt r r' t) (hc : ∀ᶠ s in nhds t, vnorm (r s) = c) : r t ⬝ᵥ r' = 0 := by
  have h := hasDerivAt_dot3 hr hr
  have h2 : HasDerivAt (fun s => r s ⬝ᵥ r s) 0 t := by
    refine (hasDerivAt_const t (c ^ 2)).congr_of_eventuallyEq ?_
    filter_upwards [hc] with s hs
    rw [← vnorm_sq, hs]
  have := h.unique h2
  rw [dotProduct_comm r' (r t)] at this
  linarith

/-- OpenStax Calculus 3:§3.3 Theorem 3.6 (CA-494), curvature via the chain rule: `κ = ‖T'‖/‖r'‖`
(the definition `curvature3`) equals `‖r' × r''‖/‖r'‖³`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.6, p. 270"]
theorem curvature3_eq_cross {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) :
    curvature3 r t = vnorm (deriv r t ⨯₃ deriv (deriv r) t) / speed3 r t ^ 3 := by
  have hs := vnorm_pos h
  rw [curvature3, (hasDerivAt_unitTangent3 hr h).deriv]
  simp only [speed3]
  rw [vnorm_Tprime h]
  field_simp

/-- OpenStax Calculus 3:§3.3 Definition (curvature) (CA-493): for a unit-speed curve (parameter = arc
length) the curvature `‖dT/ds‖` is `‖r''‖`. -/
@[kb "openstaxcalculus2016" "3:§3.3 Definition (curvature), p. 270"]
theorem curvature3_unit_speed {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ∀ s, speed3 r s = 1) (t : ℝ) :
    curvature3 r t = vnorm (deriv (deriv r) t) := by
  have h1 : deriv r t ≠ 0 := by
    intro h0
    have := hu t
    simp [speed3, h0, vnorm] at this
  have hP : deriv r t ⬝ᵥ deriv (deriv r) t = 0 :=
    dot_deriv_eq_zero_of_norm_const (hasDerivAt_deriv3 hr t)
      (c := 1) (Filter.Eventually.of_forall fun s => hu s)
  rw [curvature3_eq_cross hr h1, hu t]
  have h2 : vnorm (deriv r t ⨯₃ deriv (deriv r) t) ^ 2 = vnorm (deriv (deriv r) t) ^ 2 := by
    rw [vnorm_sq, vnorm_sq, cross_dot_cross, hP]
    have : deriv r t ⬝ᵥ deriv r t = 1 := by
      rw [← vnorm_sq]; have := hu t; simp only [speed3] at this; rw [this]; norm_num
    rw [this]; ring
  have := (sq_eq_sq₀ (vnorm_nonneg _) (vnorm_nonneg _)).1 h2
  rw [this]; norm_num

theorem hasDerivAt_speed3 {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ} (h : deriv r t ≠ 0) :
    HasDerivAt (speed3 r) ((deriv r t ⬝ᵥ deriv (deriv r) t) / speed3 r t) t :=
  hasDerivAt_vnorm3 (hasDerivAt_deriv3 hr t) h

/-- `‖T'‖ = ‖r' × r''‖/‖r'‖²`. -/
theorem vnorm_deriv_unitTangent3 {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) :
    vnorm (deriv (unitTangent3 r) t) = vnorm (deriv r t ⨯₃ deriv (deriv r) t) / speed3 r t ^ 2 := by
  rw [(hasDerivAt_unitTangent3 hr h).deriv]
  exact vnorm_Tprime h

/-- OpenStax Calculus 3:§3.2 Definition (CA-488): the unit tangent vector `T = r'/‖r'‖` has norm `1`. -/
@[kb "openstaxcalculus2016" "3:§3.2 Definition (tangent and unit tangent vector), p. 256"]
theorem vnorm_unitTangent3 {r : ℝ → Fin 3 → ℝ} {t : ℝ} (h : deriv r t ≠ 0) :
    vnorm (unitTangent3 r t) = 1 := by
  have hs := speed3_pos h
  have : unitTangent3 r t ⬝ᵥ unitTangent3 r t = 1 := by
    simp only [unitTangent3, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    have : deriv r t ⬝ᵥ deriv r t = speed3 r t ^ 2 := (vnorm_sq _).symm
    rw [this]; field_simp
  rw [vnorm, this]; simp

/-- `T · T' = 0`. -/
theorem unitTangent3_dot_deriv {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) : unitTangent3 r t ⬝ᵥ deriv (unitTangent3 r) t = 0 := by
  have hs := speed3_pos h
  rw [(hasDerivAt_unitTangent3 hr h).deriv]
  simp only [unitTangent3, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have : deriv r t ⬝ᵥ deriv r t = speed3 r t ^ 2 := (vnorm_sq _).symm
  rw [this]
  field_simp
  ring

/-- Orthonormal frame from two orthogonal unit vectors. -/
theorem frame_orthonormal {T N : Fin 3 → ℝ} (hT : vnorm T = 1) (hN : vnorm N = 1)
    (hTN : T ⬝ᵥ N = 0) :
    vnorm (T ⨯₃ N) = 1 ∧ (T ⨯₃ N) ⬝ᵥ T = 0 ∧ (T ⨯₃ N) ⬝ᵥ N = 0 := by
  have hT2 : T ⬝ᵥ T = 1 := by rw [← vnorm_sq, hT]; norm_num
  have hN2 : N ⬝ᵥ N = 1 := by rw [← vnorm_sq, hN]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · have : (T ⨯₃ N) ⬝ᵥ (T ⨯₃ N) = 1 := by
      rw [cross_dot_cross, hT2, hN2, hTN, dotProduct_comm N T, hTN]; norm_num
    rw [vnorm, this]; simp
  · rw [dotProduct_comm]; exact dot_self_cross T N
  · rw [dotProduct_comm]; exact dot_cross_self T N

/-- OpenStax Calculus 3:§3.3 principal unit normal and binormal (CA-495): when `T' ≠ 0`, `T`, `N`,
`B = T × N` are unit vectors, pairwise orthogonal. -/
@[kb "openstaxcalculus2016" "3:§3.3 Definition (principal unit normal, binormal), p. 274"]
theorem frame3_orthonormal {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) (hT' : deriv (unitTangent3 r) t ≠ 0) :
    vnorm (unitTangent3 r t) = 1 ∧ vnorm (normalN3 r t) = 1 ∧ vnorm (binormal3 r t) = 1 ∧
    unitTangent3 r t ⬝ᵥ normalN3 r t = 0 ∧ unitTangent3 r t ⬝ᵥ binormal3 r t = 0 ∧
    normalN3 r t ⬝ᵥ binormal3 r t = 0 := by
  have hm := vnorm_pos hT'
  have hN : vnorm (normalN3 r t) = 1 := by
    have : normalN3 r t ⬝ᵥ normalN3 r t = 1 := by
      simp only [normalN3, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [← vnorm_sq]; field_simp
    rw [vnorm, this]; simp
  have hTN : unitTangent3 r t ⬝ᵥ normalN3 r t = 0 := by
    simp only [normalN3, dotProduct_smul, unitTangent3_dot_deriv hr h, smul_eq_mul, mul_zero]
  obtain ⟨h1, h2, h3⟩ := frame_orthonormal (vnorm_unitTangent3 h) hN hTN
  refine ⟨vnorm_unitTangent3 h, hN, h1, hTN, ?_, ?_⟩
  · rw [dotProduct_comm]; exact h2
  · rw [dotProduct_comm]; exact h3

/-- OpenStax Calculus 3:§3.4 Theorem 3.7 (CA-498): when `T' ≠ 0`,
`a = (d‖v‖/dt) T + κ ‖v‖² N`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.7, p. 286"]
theorem acceleration_decomposition {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) (hT' : deriv (unitTangent3 r) t ≠ 0) :
    deriv (deriv r) t = deriv (speed3 r) t • unitTangent3 r t
      + (curvature3 r t * speed3 r t ^ 2) • normalN3 r t := by
  have hs := speed3_pos h
  have hm := vnorm_pos hT'
  have hD := (hasDerivAt_unitTangent3 hr h).deriv
  rw [(hasDerivAt_speed3 hr h).deriv]
  simp only [curvature3, normalN3]
  generalize hmm : vnorm (deriv (unitTangent3 r) t) = m at hm ⊢
  rw [hD]
  simp only [unitTangent3]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  field_simp
  ring

/-- OpenStax Calculus 3:§3.4 Theorem 3.8 (CA-499): `a_T = a · T = r'·r''/‖r'‖`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.8, p. 287"]
theorem tangential_component {r : ℝ → Fin 3 → ℝ} {t : ℝ} :
    deriv (deriv r) t ⬝ᵥ unitTangent3 r t
      = (deriv r t ⬝ᵥ deriv (deriv r) t) / speed3 r t := by
  simp only [unitTangent3, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm]; ring

/-- OpenStax Calculus 3:§3.4 Theorem 3.8 (CA-499): `a_N = a · N = ‖r' × r''‖/‖r'‖`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.8, p. 287"]
theorem normal_component {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) (hT' : deriv (unitTangent3 r) t ≠ 0) :
    deriv (deriv r) t ⬝ᵥ normalN3 r t
      = vnorm (deriv r t ⨯₃ deriv (deriv r) t) / speed3 r t := by
  have hs := speed3_pos h
  have hm := vnorm_pos hT'
  have hn := vnorm_deriv_unitTangent3 hr h
  have hD := (hasDerivAt_unitTangent3 hr h).deriv
  have hc : vnorm (deriv r t ⨯₃ deriv (deriv r) t) ≠ 0 := by
    intro h0; rw [h0] at hn; simp at hn; exact hm.ne' hn
  simp only [normalN3, dotProduct_smul, smul_eq_mul]
  rw [hn, hD]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have e1 := vnorm_sq (deriv r t ⨯₃ deriv (deriv r) t)
  rw [cross_dot_cross] at e1
  have e2 : deriv r t ⬝ᵥ deriv r t = speed3 r t ^ 2 := (vnorm_sq _).symm
  rw [e2, dotProduct_comm (deriv (deriv r) t) (deriv r t)] at e1
  rw [dotProduct_comm (deriv (deriv r) t) (deriv r t)]
  generalize vnorm (deriv r t ⨯₃ deriv (deriv r) t) = c at *
  generalize deriv r t ⬝ᵥ deriv (deriv r) t = P at *
  generalize deriv (deriv r) t ⬝ᵥ deriv (deriv r) t = bb at *
  generalize speed3 r t = s at *
  field_simp
  linear_combination -e1

/-- OpenStax Calculus 3:§3.4 Theorem 3.8 (CA-499): `a_T² + a_N² = ‖a‖²`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.8, p. 287"]
theorem tangential_normal_sq {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {t : ℝ}
    (h : deriv r t ≠ 0) (hT' : deriv (unitTangent3 r) t ≠ 0) :
    (deriv (deriv r) t ⬝ᵥ unitTangent3 r t) ^ 2 + (deriv (deriv r) t ⬝ᵥ normalN3 r t) ^ 2
      = vnorm (deriv (deriv r) t) ^ 2 := by
  have hs := speed3_pos h
  rw [tangential_component, normal_component hr h hT', div_pow, div_pow, ← add_div,
    div_eq_iff (pow_pos hs 2).ne', vnorm_sq, vnorm_sq, cross_dot_cross]
  have e2 : deriv r t ⬝ᵥ deriv r t = speed3 r t ^ 2 := (vnorm_sq _).symm
  rw [e2, dotProduct_comm (deriv (deriv r) t) (deriv r t)]
  ring

/-- A space curve from three component functions. -/
def curve3 (x y z : ℝ → ℝ) (t : ℝ) : Fin 3 → ℝ := ![x t, y t, z t]

theorem curve3_hasDerivAt {x y z : ℝ → ℝ} {x' y' z' t : ℝ} (hx : HasDerivAt x x' t)
    (hy : HasDerivAt y y' t) (hz : HasDerivAt z z' t) :
    HasDerivAt (curve3 x y z) ![x', y', z'] t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [curve3] using hx
  · simpa [curve3] using hy
  · simpa [curve3] using hz

theorem curve3_deriv {x y z : ℝ → ℝ} (hx : Differentiable ℝ x) (hy : Differentiable ℝ y)
    (hz : Differentiable ℝ z) :
    deriv (curve3 x y z) = curve3 (deriv x) (deriv y) (deriv z) := by
  funext t
  exact (curve3_hasDerivAt (hx t).hasDerivAt (hy t).hasDerivAt (hz t).hasDerivAt).deriv

theorem curve3_contDiff {x y z : ℝ → ℝ} {n : WithTop ℕ∞} (hx : ContDiff ℝ n x)
    (hy : ContDiff ℝ n y) (hz : ContDiff ℝ n z) : ContDiff ℝ n (curve3 x y z) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa [curve3] using hx
  · simpa [curve3] using hy
  · simpa [curve3] using hz

theorem curve3_deriv_deriv {x y z : ℝ → ℝ} (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (hz : ContDiff ℝ 2 z) :
    deriv (deriv (curve3 x y z)) = curve3 (deriv (deriv x)) (deriv (deriv y)) (deriv (deriv z)) := by
  rw [curve3_deriv (hx.differentiable (by norm_num)) (hy.differentiable (by norm_num))
    (hz.differentiable (by norm_num))]
  exact curve3_deriv hx.differentiable_deriv_two hy.differentiable_deriv_two
    hz.differentiable_deriv_two

/-- OpenStax Calculus 3:§3.3 Theorem 3.6 (CA-494), plane graph `y = f(x)`:
`κ = |f''|/(1 + f'²)^{3/2}`. The graph is the curve `x ↦ (x, f x, 0)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.6, p. 270"]
theorem curvature_graph {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    curvature3 (curve3 id f (fun _ => 0)) x
      = |deriv (deriv f) x| / (1 + deriv f x ^ 2) ^ (3 / 2 : ℝ) := by
  have hid : ContDiff ℝ 2 (id : ℝ → ℝ) := contDiff_id
  have h0 : ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ)) := contDiff_const
  have hr := curve3_contDiff hid hf h0
  have d1 := curve3_deriv (x := id) (y := f) (z := fun _ => (0 : ℝ)) differentiable_id
    (hf.differentiable (by norm_num)) (differentiable_const _)
  have d2 := curve3_deriv_deriv hid hf h0
  have hne : deriv (curve3 id f (fun _ => 0)) x ≠ 0 := by
    intro h; rw [d1] at h
    have := congrFun h 0
    simp [curve3] at this
  rw [curvature3_eq_cross hr hne, d2, d1]
  have e1 : speed3 (curve3 id f fun _ => 0) x = √(1 + deriv f x ^ 2) := by
    simp [speed3, d1, vnorm, curve3, dotProduct, Fin.sum_univ_three]
    ring_nf
  have e2 : vnorm (curve3 (deriv id) (deriv f) (deriv fun _ : ℝ => (0 : ℝ)) x ⨯₃
      curve3 (deriv (deriv id)) (deriv (deriv f)) (deriv (deriv fun _ : ℝ => (0 : ℝ))) x)
      = |deriv (deriv f) x| := by
    simp [vnorm, curve3, cross_apply, dotProduct, Fin.sum_univ_three]
    exact Real.sqrt_mul_self_eq_abs _
  rw [e2, e1, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The circular helix `(a cos t, a sin t, b t)`. -/
noncomputable def helix3 (a b : ℝ) : ℝ → Fin 3 → ℝ :=
  curve3 (fun t => a * cos t) (fun t => a * sin t) (fun t => b * t)

/-- OpenStax Calculus 3:§3.1 helix (CA-480) with the curvature of Example 3.12 (CA-494): the curvature
of `(a cos t, a sin t, b t)`, `a > 0`, is `a/(a²+b²)`. -/
@[kb "openstaxcalculus2016" "3:§3.1 helix example, p. 247"]
theorem curvature_helix3 {a b : ℝ} (ha : 0 < a) (t : ℝ) :
    curvature3 (helix3 a b) t = a / (a ^ 2 + b ^ 2) := by
  have hx : ContDiff ℝ 2 (fun t : ℝ => a * cos t) := by fun_prop
  have hy : ContDiff ℝ 2 (fun t : ℝ => a * sin t) := by fun_prop
  have hz : ContDiff ℝ 2 (fun t : ℝ => b * t) := by fun_prop
  have hr : ContDiff ℝ 2 (helix3 a b) := curve3_contDiff hx hy hz
  have d1 := curve3_deriv (hx.differentiable (by norm_num)) (hy.differentiable (by norm_num))
    (hz.differentiable (by norm_num))
  have d2 := curve3_deriv_deriv hx hy hz
  have hx1 : deriv (fun t : ℝ => a * cos t) = fun t => -(a * sin t) := by funext t; simp
  have hy1 : deriv (fun t : ℝ => a * sin t) = fun t => a * cos t := by funext t; simp
  have hz1 : deriv (fun t : ℝ => b * t) = fun _ => b := by funext t; simp
  have hx2 : deriv (fun t : ℝ => -(a * sin t)) = fun t => -(a * cos t) := by funext t; simp
  have hz2 : deriv (fun _ : ℝ => b) = fun _ => 0 := by funext t; simp
  rw [hx1, hy1, hz1, hx2, hx1, hz2] at d2
  rw [hx1, hy1, hz1] at d1
  unfold helix3 at *
  have hs2 : sin t ^ 2 + cos t ^ 2 = 1 := sin_sq_add_cos_sq t
  have hq : 0 < a ^ 2 + b ^ 2 := by positivity
  have hne : deriv (curve3 (fun t => a * cos t) (fun t => a * sin t) fun t => b * t) t ≠ 0 := by
    intro h; rw [d1] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [curve3] at h0 h1
    rcases h0 with h0 | h0
    · exact ha.ne' h0
    · rcases h1 with h1 | h1
      · exact ha.ne' h1
      · rw [h0, h1] at hs2; norm_num at hs2
  rw [curvature3_eq_cross hr hne]
  have e1 : speed3 (curve3 (fun t => a * cos t) (fun t => a * sin t) fun t => b * t) t
      = √(a ^ 2 + b ^ 2) := by
    simp only [speed3, d1, vnorm, curve3, dotProduct, Fin.sum_univ_three]
    simp
    congr 1
    nlinarith [hs2]
  have e2 : vnorm (deriv (curve3 (fun t => a * cos t) (fun t => a * sin t) fun t => b * t) t ⨯₃
      deriv (deriv (curve3 (fun t => a * cos t) (fun t => a * sin t) fun t => b * t)) t)
      = a * √(a ^ 2 + b ^ 2) := by
    rw [d2, d1]
    simp only [vnorm, curve3, cross_apply, dotProduct, Fin.sum_univ_three]
    simp
    have : a * √(a ^ 2 + b ^ 2) = √(a ^ 2 * (a ^ 2 + b ^ 2)) := by
      rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
    rw [this]
    congr 1
    linear_combination (b ^ 2 * a ^ 2 + a ^ 4 * (sin t ^ 2 + cos t ^ 2 + 1)) * hs2
  rw [e1, e2]
  have h3 : √(a ^ 2 + b ^ 2) ^ 3 = (a ^ 2 + b ^ 2) * √(a ^ 2 + b ^ 2) := by
    rw [pow_succ, Real.sq_sqrt hq.le]
  have h4 : 0 < √(a ^ 2 + b ^ 2) := Real.sqrt_pos.2 hq
  rw [h3]
  field_simp

/-- OpenStax Calculus 3:§3.2 Theorem 3.3 (v) (CA-486): product rule for the cross product,
`(r × u)' = r' × u + r × u'`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (part v), p. 254"]
theorem hasDerivAt_cross3 {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
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

/-- OpenStax Calculus 3:§3.2 Theorem 3.3 (iv) (CA-485): product rule for the dot product. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.3 (parts i-iv, vi), p. 254"]
theorem hasDerivAt_dot3' {f g : ℝ → Fin 3 → ℝ} {f' g' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s ⬝ᵥ g s) (f' ⬝ᵥ g t + f t ⬝ᵥ g') t := hasDerivAt_dot3 hf hg

/-- OpenStax Calculus 3:§3.2 (CA-488): `r' = ‖r'‖ T`, with `T` the unit tangent vector. -/
@[kb "openstaxcalculus2016" "3:§3.2 Definition (tangent and unit tangent vector), p. 256"]
theorem deriv_eq_speed_smul_unitTangent3 {r : ℝ → Fin 3 → ℝ} {t : ℝ} (h : deriv r t ≠ 0) :
    deriv r t = speed3 r t • unitTangent3 r t := by
  have hs := speed3_pos h
  simp only [unitTangent3, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

theorem speed3_curve3 {x y z : ℝ → ℝ} (hx : Differentiable ℝ x) (hy : Differentiable ℝ y)
    (hz : Differentiable ℝ z) (t : ℝ) :
    speed3 (curve3 x y z) t = √(deriv x t ^ 2 + deriv y t ^ 2 + deriv z t ^ 2) := by
  simp only [speed3, curve3_deriv hx hy hz, vnorm, curve3, dotProduct, Fin.sum_univ_three]
  simp [sq]

/-- Arc length of a space curve on `[a, b]`: the integral of the speed `‖r'‖`
(OpenStax Calculus 3:Theorem 3.4 takes this as the length, CA-491). -/
noncomputable def arcLength3 (r : ℝ → Fin 3 → ℝ) (a b : ℝ) : ℝ := ∫ t in a..b, speed3 r t

theorem continuous_vnorm : Continuous vnorm := by
  unfold vnorm dotProduct
  fun_prop

theorem continuous_speed3 {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 1 r) : Continuous (speed3 r) :=
  continuous_vnorm.comp (hr.continuous_deriv_one)

/-- OpenStax Calculus 3:§3.3 Theorem 3.4 (CA-491), plane curve: the length of `(f, g)` over `[a, b]` is
`∫ √(f'² + g'²)` (the curve is `(f, g, 0)`). -/
@[kb "openstaxcalculus2016" "3:Theorem 3.4, p. 266"]
theorem arcLength3_plane {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a b : ℝ) :
    arcLength3 (curve3 f g (fun _ => 0)) a b = ∫ t in a..b, √(deriv f t ^ 2 + deriv g t ^ 2) := by
  unfold arcLength3
  congr 1
  funext t
  rw [speed3_curve3 hf hg (differentiable_const _)]
  simp

/-- OpenStax Calculus 3:§3.3 Theorem 3.5 (CA-492): the arc-length function `s(t) = ∫_a^t ‖r'‖` has
derivative `s'(t) = ‖r'(t)‖`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.5, p. 268"]
theorem hasDerivAt_arcLength3 {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 1 r) (a t : ℝ) :
    HasDerivAt (fun u => arcLength3 r a u) (speed3 r t) t :=
  ((continuous_speed3 hr).integral_hasStrictDerivAt a t).hasDerivAt

/-- OpenStax Calculus 3:§3.3 arc-length parameterization (CA-492): if `‖r'‖ = 1` then
`s(t) = t - a`, i.e. the parameter is arc length. -/
@[kb "openstaxcalculus2016" "3:§3.3 arc-length parameterization, p. 268"]
theorem arcLength3_unit_speed {r : ℝ → Fin 3 → ℝ} (hu : ∀ s, speed3 r s = 1) (a t : ℝ) :
    arcLength3 r a t = t - a := by
  simp [arcLength3, hu]

/-- The vertical unit vector `j`. -/
def jvec : Fin 3 → ℝ := ![0, 1, 0]

/-- OpenStax Calculus 3:§3.4 projectile motion (CA-500): if `r'' = -g j`, `r(0) = r₀`, `r'(0) = v₀`,
then `r(t) = -(1/2) g t² j + v₀ t + r₀`. -/
@[kb "openstaxcalculus2016" "3:§3.4 projectile motion equations, p. 289"]
theorem projectile_position {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {g : ℝ} {r0 v0 : Fin 3 → ℝ}
    (hacc : ∀ t, deriv (deriv r) t = (-g) • jvec) (h0 : r 0 = r0) (hv : deriv r 0 = v0) (t : ℝ) :
    r t = (-(g * t ^ 2 / 2)) • jvec + t • v0 + r0 := by
  have hr1 : Differentiable ℝ r := hr.differentiable (by norm_num)
  -- velocity
  have hw : ∀ s, HasDerivAt (fun u => deriv r u - (v0 - (g * u) • jvec)) 0 s := by
    intro s
    have h1 := hasDerivAt_deriv3 hr s
    have h2 : HasDerivAt (fun u : ℝ => (g * u) • jvec) (g • jvec) s := by
      simpa using ((hasDerivAt_id s).const_mul g).smul_const jvec
    have := h1.sub (h2.const_sub v0)
    convert this using 1
    rw [hacc s]; simp [neg_smul]
  have hwc : ∀ s, deriv r s - (v0 - (g * s) • jvec) = 0 := by
    intro s
    have := is_const_of_deriv_eq_zero (f := fun u => deriv r u - (v0 - (g * u) • jvec))
      (fun u => (hw u).differentiableAt) (fun u => (hw u).deriv) s 0
    rw [this, hv]; simp
  have hq : ∀ s, HasDerivAt (fun u => r u - ((-(g * u ^ 2 / 2)) • jvec + u • v0 + r0)) 0 s := by
    intro s
    have h1 := (hr1 s).hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => (-(g * u ^ 2 / 2)) • jvec) ((-(g * s)) • jvec) s := by
      have := (((hasDerivAt_pow 2 s).const_mul g).div_const 2).neg.smul_const jvec
      convert this using 2
      simp; ring
    have h3 : HasDerivAt (fun u : ℝ => u • v0) v0 s := by
      simpa using (hasDerivAt_id s).smul_const v0
    have := h1.sub ((h2.add h3).add_const r0)
    convert this using 1
    have := hwc s
    rw [sub_eq_zero] at this
    rw [this]; ext i; simp; ring
  have := is_const_of_deriv_eq_zero (f := fun u => r u - ((-(g * u ^ 2 / 2)) • jvec + u • v0 + r0))
    (fun u => (hq u).differentiableAt) (fun u => (hq u).deriv) t 0
  rw [h0] at this
  simpa [sub_eq_zero] using this

/-- OpenStax Calculus 3:§3.4 launch-angle form (CA-500): launched from the origin at angle `θ` with
speed `v`, the path is `(v cos θ · t, v sin θ · t - g t²/2)`. -/
@[kb "openstaxcalculus2016" "3:§3.4 launch-angle form, p. 290"]
theorem projectile_launch {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r) {g v θ : ℝ}
    (hacc : ∀ t, deriv (deriv r) t = (-g) • jvec) (h0 : r 0 = 0)
    (hv : deriv r 0 = ![v * cos θ, v * sin θ, 0]) (t : ℝ) :
    r t = ![v * cos θ * t, v * sin θ * t - g * t ^ 2 / 2, 0] := by
  rw [projectile_position hr hacc h0 hv t]
  ext i; fin_cases i <;> simp [jvec] <;> ring

/-- Range: time of flight `2 v sin θ / g` returns the projectile to height `0` at horizontal
distance `v² sin 2θ / g`. -/
theorem projectile_range_formula {g v θ : ℝ} (hg : g ≠ 0) :
    let T := 2 * v * sin θ / g
    v * sin θ * T - g * T ^ 2 / 2 = 0 ∧ v * cos θ * T = v ^ 2 * sin (2 * θ) / g := by
  intro T
  constructor
  · simp only [T]; field_simp; ring
  · simp only [T, sin_two_mul]; field_simp

/-- OpenStax Calculus 3:§3.4 range remark (CA-501): for `g > 0`, the range `v² sin 2θ / g` over launch
angles `θ ∈ [0, π/2]` is maximal at `θ = π/4` (value `v²/g`) and only there (for `v ≠ 0`). -/
@[kb "openstaxcalculus2016" "3:§3.4 range remark, p. 293"]
theorem range_max_at_pi_div_four {g v θ : ℝ} (hg : 0 < g) (hv : v ≠ 0) (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    v ^ 2 * sin (2 * θ) / g ≤ v ^ 2 * sin (2 * (π / 4)) / g ∧
    (v ^ 2 * sin (2 * θ) / g = v ^ 2 * sin (2 * (π / 4)) / g → θ = π / 4) := by
  have h4 : sin (2 * (π / 4)) = 1 := by
    rw [show 2 * (π / 4) = π / 2 by ring]; exact sin_pi_div_two
  rw [h4]
  have hv2 : 0 < v ^ 2 := by positivity
  constructor
  · apply div_le_div_of_nonneg_right _ hg.le
    nlinarith [sin_le_one (2 * θ)]
  · intro h
    have h1 : sin (2 * θ) = 1 := by
      have := (div_left_inj' hg.ne').1 h
      exact (mul_right_inj' hv2.ne').1 (by simpa using this)
    have hc : cos (2 * θ) = 0 := by
      have := sin_sq_add_cos_sq (2 * θ)
      rw [h1] at this
      nlinarith [sq_nonneg (cos (2 * θ))]
    have : 2 * θ = π / 2 := by
      apply Real.injOn_cos ⟨by linarith [hθ.1], by linarith [hθ.2, pi_pos]⟩
        ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      rw [hc, cos_pi_div_two]
    linarith

/-- OpenStax Calculus 3:§3.4 Kepler's second law (CA-502), angular momentum: if the acceleration is
always parallel to the position (a central force), then `r × r'` is constant. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem angularMomentum_const {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r)
    (hc : ∀ t, ∃ c : ℝ, deriv (deriv r) t = c • r t) (t : ℝ) :
    r t ⨯₃ deriv r t = r 0 ⨯₃ deriv r 0 := by
  have hr1 : Differentiable ℝ r := hr.differentiable (by norm_num)
  have h : ∀ s, HasDerivAt (fun u => r u ⨯₃ deriv r u) 0 s := by
    intro s
    have := hasDerivAt_cross3 (hr1 s).hasDerivAt (hasDerivAt_deriv3 hr s)
    obtain ⟨c, hcs⟩ := hc s
    convert this using 1
    rw [hcs, map_smul, cross_self, cross_self]; simp
  exact is_const_of_deriv_eq_zero (fun u => (h u).differentiableAt) (fun u => (h u).deriv) t 0

/-- OpenStax Calculus 3:Theorem 3.9 (CA-502), Kepler's second law, equal areas: for a central force the area rate `½‖r × r'‖` is
constant, so the area swept over a time interval `[t₁, t₂]`, `∫ ½‖r × r'‖`, depends only on its
length: it equals `½‖r(0) × r'(0)‖ (t₂ - t₁)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem keplerSecond_area {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r)
    (hc : ∀ t, ∃ c : ℝ, deriv (deriv r) t = c • r t) (t₁ t₂ : ℝ) :
    (∫ t in t₁..t₂, vnorm (r t ⨯₃ deriv r t) / 2) = vnorm (r 0 ⨯₃ deriv r 0) / 2 * (t₂ - t₁) := by
  simp [angularMomentum_const hr hc]
  ring

/-- OpenStax Calculus 3:Theorem 3.9 (CA-502), planarity of a central-force orbit: `r(t) · (r(0) × r'(0)) = 0` for all `t`, i.e. the orbit
lies in the plane through the origin perpendicular to the constant angular momentum. -/
@[kb "openstaxcalculus2016" "3:Theorem 3.9, p. 293"]
theorem orbit_planar {r : ℝ → Fin 3 → ℝ} (hr : ContDiff ℝ 2 r)
    (hc : ∀ t, ∃ c : ℝ, deriv (deriv r) t = c • r t) (t : ℝ) :
    r t ⬝ᵥ (r 0 ⨯₃ deriv r 0) = 0 := by
  rw [← angularMomentum_const hr hc t]
  exact dot_self_cross _ _

/-- The graph of `f` as a space curve. -/
noncomputable def graphCurve (f : ℝ → ℝ) : ℝ → Fin 3 → ℝ := curve3 id f (fun _ => 0)

theorem graphCurve_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (graphCurve f) x = ![1, deriv f x, 0] := by
  have := curve3_deriv (x := id) (y := f) (z := fun _ => (0 : ℝ)) differentiable_id
    (hf.differentiable (by norm_num)) (differentiable_const _)
  rw [graphCurve, this]
  simp [curve3]

theorem graphCurve_deriv2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (graphCurve f)) x = ![0, deriv (deriv f) x, 0] := by
  have := curve3_deriv_deriv (x := id) (y := f) (z := fun _ => (0 : ℝ)) contDiff_id hf contDiff_const
  rw [graphCurve, this]
  simp [curve3]

theorem graphCurve_speed {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    speed3 (graphCurve f) x = √(1 + deriv f x ^ 2) := by
  simp only [speed3, graphCurve_deriv hf, vnorm, dotProduct, Fin.sum_univ_three]
  simp [sq]

theorem graphCurve_cross_norm {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    vnorm (deriv (graphCurve f) x ⨯₃ deriv (deriv (graphCurve f)) x) = |deriv (deriv f) x| := by
  rw [graphCurve_deriv hf, graphCurve_deriv2 hf]
  simp [vnorm, cross_apply, dotProduct, Fin.sum_univ_three]
  exact Real.sqrt_mul_self_eq_abs _

theorem graphCurve_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (graphCurve f) :=
  curve3_contDiff contDiff_id hf contDiff_const

/-- OpenStax Calculus 3:§3.3 osculating circle (CA-496), centre: for a graph `y = f(x)` with
`f''(x₀) ≠ 0`, the point `r + (1/κ) N` (with `N` the principal unit normal of the curve
`(x, f x, 0)`) is `(x₀ - f'(1+f'²)/f'', f(x₀) + (1+f'²)/f'', 0)`. -/
@[kb "openstaxcalculus2016" "3:§3.3 osculating circle, p. 278"]
theorem osculating_center_graph {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ)
    (hq : deriv (deriv f) x ≠ 0) :
    (graphCurve f x + (1 / curvature3 (graphCurve f) x) • normalN3 (graphCurve f) x) 0
        = x - deriv f x * (1 + deriv f x ^ 2) / deriv (deriv f) x ∧
    (graphCurve f x + (1 / curvature3 (graphCurve f) x) • normalN3 (graphCurve f) x) 1
        = f x + (1 + deriv f x ^ 2) / deriv (deriv f) x ∧
    (graphCurve f x + (1 / curvature3 (graphCurve f) x) • normalN3 (graphCurve f) x) 2 = 0 := by
  have hr := graphCurve_contDiff hf
  have hne : deriv (graphCurve f) x ≠ 0 := by
    intro h; rw [graphCurve_deriv hf] at h
    have := congrFun h 0
    simp at this
  have hs := speed3_pos hne
  have hsd := graphCurve_speed hf x
  have hW : 0 < 1 + deriv f x ^ 2 := by positivity
  have hs2 : speed3 (graphCurve f) x ^ 2 = 1 + deriv f x ^ 2 := by
    rw [hsd, Real.sq_sqrt hW.le]
  have hA : 0 < |deriv (deriv f) x| := abs_pos.2 hq
  have hAq : |deriv (deriv f) x| * |deriv (deriv f) x| = deriv (deriv f) x * deriv (deriv f) x :=
    abs_mul_abs_self _
  have hm := vnorm_deriv_unitTangent3 hr hne
  rw [graphCurve_cross_norm hf, hs2] at hm
  have hk := curvature3_eq_cross hr hne
  rw [graphCurve_cross_norm hf] at hk
  have hD := (hasDerivAt_unitTangent3 hr hne).deriv
  rw [graphCurve_deriv hf, graphCurve_deriv2 hf] at hD
  have hP : (![1, deriv f x, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, deriv (deriv f) x, 0]
      = deriv f x * deriv (deriv f) x := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [hP] at hD
  unfold normalN3
  rw [hk, hm, hD]
  generalize speed3 (graphCurve f) x = s at *
  generalize |deriv (deriv f) x| = A at *
  have hx : graphCurve f x = ![x, f x, 0] := by simp [graphCurve, curve3]
  rw [hx]
  refine ⟨?_, ?_, ?_⟩
  · simp
    have := hs2
    field_simp
    linear_combination (deriv f x * (1 + deriv f x ^ 2)) * hAq
  · simp
    field_simp
    linear_combination (deriv (deriv f) x ^ 2) * hs2 - hAq
  · simp

/-- OpenStax Calculus 3:§3.3 osculating circle (CA-496): for a graph `y = f(x)` with `f''(x₀) ≠ 0`, the
circle with centre `(cx, cy) = r + (1/κ)N` (see `osculating_center_graph`) and radius `1/κ` has
second-order contact with the graph at `x₀`: the function
`φ(x) = (x - cx)² + (f x - cy)² - (1/κ)²` satisfies `φ(x₀) = φ'(x₀) = φ''(x₀) = 0`, i.e. the circle
passes through the point, is tangent there and has the same curvature there. -/
@[kb "openstaxcalculus2016" "3:§3.3 osculating circle, p. 278"]
theorem osculating_circle_graph {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x₀ : ℝ)
    (hq : deriv (deriv f) x₀ ≠ 0) :
    let cx := x₀ - deriv f x₀ * (1 + deriv f x₀ ^ 2) / deriv (deriv f) x₀
    let cy := f x₀ + (1 + deriv f x₀ ^ 2) / deriv (deriv f) x₀
    let φ := fun x => (x - cx) ^ 2 + (f x - cy) ^ 2 - (1 / curvature3 (graphCurve f) x₀) ^ 2
    φ x₀ = 0 ∧ deriv φ x₀ = 0 ∧ deriv (deriv φ) x₀ = 0 := by
  intro cx cy φ
  have hr := graphCurve_contDiff hf
  have hne : deriv (graphCurve f) x₀ ≠ 0 := by
    intro h; rw [graphCurve_deriv hf] at h
    have := congrFun h 0
    simp at this
  have hs := speed3_pos hne
  have hsd := graphCurve_speed hf x₀
  have hW : 0 < 1 + deriv f x₀ ^ 2 := by positivity
  have hs2 : speed3 (graphCurve f) x₀ ^ 2 = 1 + deriv f x₀ ^ 2 := by
    rw [hsd, Real.sq_sqrt hW.le]
  have hA : 0 < |deriv (deriv f) x₀| := abs_pos.2 hq
  have hAq : |deriv (deriv f) x₀| * |deriv (deriv f) x₀| = deriv (deriv f) x₀ * deriv (deriv f) x₀ :=
    abs_mul_abs_self _
  have hk := curvature3_eq_cross hr hne
  rw [graphCurve_cross_norm hf] at hk
  have hR : (1 / curvature3 (graphCurve f) x₀) ^ 2 = (1 + deriv f x₀ ^ 2) ^ 3 / deriv (deriv f) x₀ ^ 2 := by
    rw [hk]
    generalize speed3 (graphCurve f) x₀ = s at *
    generalize |deriv (deriv f) x₀| = A at *
    have : A ^ 2 = deriv (deriv f) x₀ ^ 2 := by linear_combination hAq
    rw [← this, ← hs2]
    field_simp
  have hφ : ∀ x, HasDerivAt φ (2 * (x - cx) + 2 * (f x - cy) * deriv f x) x := by
    intro x
    have h1 : HasDerivAt (fun x => x - cx) 1 x := (hasDerivAt_id x).sub_const cx
    have h2 : HasDerivAt (fun x => f x - cy) (deriv f x) x :=
      ((hf.differentiable (by norm_num)) x).hasDerivAt.sub_const cy
    have := ((h1.pow 2).add (h2.pow 2)).sub_const ((1 / curvature3 (graphCurve f) x₀) ^ 2)
    convert this using 1
    simp
  have hφ' : deriv φ = fun x => 2 * (x - cx) + 2 * (f x - cy) * deriv f x :=
    funext fun x => (hφ x).deriv
  have hq' := hf.differentiable_deriv_two x₀
  have hd2 : HasDerivAt (fun x => 2 * (x - cx) + 2 * (f x - cy) * deriv f x)
      (2 + 2 * deriv f x₀ * deriv f x₀ + 2 * (f x₀ - cy) * deriv (deriv f) x₀) x₀ := by
    have h1 : HasDerivAt (fun x => x - cx) 1 x₀ := (hasDerivAt_id x₀).sub_const cx
    have h2 : HasDerivAt (fun x => f x - cy) (deriv f x₀) x₀ :=
      ((hf.differentiable (by norm_num)) x₀).hasDerivAt.sub_const cy
    have h3 : HasDerivAt (deriv f) (deriv (deriv f) x₀) x₀ := hq'.hasDerivAt
    have := (h1.const_mul 2).add ((h2.const_mul 2).mul h3)
    convert this using 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [φ, cx, cy, hR]
    field_simp
    ring
  · rw [hφ']
    simp only [cx, cy]
    field_simp
    ring
  · rw [hφ', hd2.deriv]
    simp only [cy]
    field_simp
    ring

end UndergradKB.Calculus

