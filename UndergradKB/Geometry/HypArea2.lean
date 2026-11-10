import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HypArea
import UndergradKB.Geometry.HypTriangles
import UndergradKB.Geometry.HypLines

/-! # Hyperbolic area of a triangle equals its defect (Petrunin, Section 20I p. 176, Section 9 p. 90)

The solid h-triangle `hsolid A B C` is the intersection of the three closed h-half-planes cut out by the
lines `AB`, `BC`, `CA` and containing the opposite vertex.  A closed h-half-plane `hhalf P Q R z` is
described in the picture of the h-motion `mobius P` (which sends the h-lines through `P` to diameters):
`z` and `R` lie on the same closed side of the diameter through `mobius P Q`.

The area of the solid triangle is `π - (∠A + ∠B + ∠C)`.  The proof moves a vertex to the centre
(`harea_motion`, `hangle_motion`), rotates so that the h-line through the other two vertices has the
equation `|z|² + 1 = 2 K Re z`, identifies the solid triangle with a region of polar coordinates
`0 < r ≤ geodR K 0 θ` (`harea_geodesic_sector`) and computes the two remaining angles from the
tangent direction of the h-line.
-/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate MeasureTheory Set

/-- `z` lies on the closed side of the h-line `PQ` containing `R`: in the picture of `mobius P`, the
signed areas of `(mobius P Q, mobius P R)` and `(mobius P Q, mobius P z)` have the same weak sign. -/
def hhalf (P Q R z : ℂ) : Prop :=
  0 ≤ (conj (mobius P Q) * mobius P R).im * (conj (mobius P Q) * mobius P z).im

/-- The **solid h-triangle** `ABC`: the points of the disc in the three closed h-half-planes. -/
@[kb "petrunin2025" "Section 20I, p. 176"]
def hsolid (A B C : ℂ) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ hhalf A B C z ∧ hhalf B C A z ∧ hhalf C A B z}

theorem mobius_zero_left (z : ℂ) : mobius 0 z = z := by simp [mobius]

theorem measurable_mobius (a : ℂ) : Measurable (mobius a) := by
  unfold mobius
  fun_prop

theorem measurableSet_hhalf (P Q R : ℂ) : MeasurableSet {z | hhalf P Q R z} := by
  unfold hhalf
  have : Measurable fun z => (conj (mobius P Q) * mobius P z).im := by
    have := measurable_mobius P
    fun_prop
  exact measurableSet_le measurable_const (this.const_mul _)

theorem measurableSet_hsolid (A B C : ℂ) : MeasurableSet (hsolid A B C) := by
  unfold hsolid
  have h1 : MeasurableSet {z : ℂ | ‖z‖ < 1} := measurableSet_lt (by fun_prop) measurable_const
  exact h1.inter ((measurableSet_hhalf A B C).inter ((measurableSet_hhalf B C A).inter
    (measurableSet_hhalf C A B)))

theorem hsolid_subset (A B C : ℂ) : hsolid A B C ⊆ Metric.ball 0 1 := fun z hz => by
  simpa using hz.1

section Motion

variable {a u : ℂ}

theorem hhalf_motion (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) {P Q R z : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1)
    (hR : ‖R‖ < 1) (hz : ‖z‖ < 1) :
    hhalf (u * mobius a P) (u * mobius a Q) (u * mobius a R) (u * mobius a z) ↔ hhalf P Q R z := by
  obtain ⟨c, hc, h⟩ := mobius_motion ha hu hP
  have key : ∀ x y : ℂ, conj (c * x) * (c * y) = conj x * y := fun x y => by
    have := conj_mul_self_unit hc
    rw [map_mul]; linear_combination (conj x * y) * this
  unfold hhalf
  rw [h Q hQ, h R hR, h z hz, key, key]

theorem norm_motion_lt (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖u * mobius a z‖ < 1 := by
  rw [norm_mul, hu, one_mul]; exact norm_mobius_lt_one ha hz

theorem hsolid_image (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) {A B C : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1)
    (hC : ‖C‖ < 1) :
    (fun z => u * mobius a z) '' hsolid A B C =
      hsolid (u * mobius a A) (u * mobius a B) (u * mobius a C) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  ext w
  constructor
  · rintro ⟨z, ⟨hz, h1, h2, h3⟩, rfl⟩
    exact ⟨norm_motion_lt ha hu hz, (hhalf_motion ha hu hA hB hC hz).mpr h1,
      (hhalf_motion ha hu hB hC hA hz).mpr h2, (hhalf_motion ha hu hC hA hB hz).mpr h3⟩
  · rintro ⟨hw, h1, h2, h3⟩
    have hun : ‖conj u‖ = 1 := by simpa using hu
    have hw' : ‖conj u * w‖ < 1 := by rw [norm_mul, hun, one_mul]; exact hw
    set z := mobius (-a) (conj u * w) with hzdef
    have hz1 : ‖z‖ < 1 := norm_mobius_lt_one (by simpa using ha) hw'
    have hfz : u * mobius a z = w := by
      rw [hzdef, mobius_mobius_neg ha hw', ← mul_assoc, mul_comm u, conj_mul_self_unit hu, one_mul]
    refine ⟨z, ⟨hz1, ?_, ?_, ?_⟩, hfz⟩
    · exact (hhalf_motion ha hu hA hB hC hz1).mp (by rw [hfz]; exact h1)
    · exact (hhalf_motion ha hu hB hC hA hz1).mp (by rw [hfz]; exact h2)
    · exact (hhalf_motion ha hu hC hA hB hz1).mp (by rw [hfz]; exact h3)

/-- The area of the solid triangle is invariant under the h-motions `z ↦ u · mobius a z`. -/
theorem harea_hsolid_motion (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) {A B C : ℂ} (hA : ‖A‖ < 1)
    (hB : ‖B‖ < 1) (hC : ‖C‖ < 1) :
    harea (hsolid (u * mobius a A) (u * mobius a B) (u * mobius a C)) = harea (hsolid A B C) := by
  rw [← hsolid_image ha hu hA hB hC]
  exact harea_motion ha hu (measurableSet_hsolid A B C) (hsolid_subset A B C)

end Motion

section Algebra

variable {K : ℝ} {A B C z w : ℂ}

theorem ne_of_norm_lt_one_lt (hK : 1 < K) (hA : ‖A‖ < 1) : A ≠ (K : ℂ) := by
  rintro rfl
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hA
  linarith

theorem circ_conj (hA : A * conj A + 1 = K * (A + conj A)) (hAK : A ≠ K) :
    conj A = (K * A - 1) / (A - K) := by
  rw [eq_div_iff (sub_ne_zero.mpr hAK)]
  linear_combination hA

/-- Orthogonality: for two points `A`, `B` of the circle `|z|² + 1 = 2 K Re z`, the vector
`conj A * mobius A B` is orthogonal to `conj A * (A - K)`. -/
theorem circ_orth (hK : 1 < K) (hAn : ‖A‖ < 1) (hBn : ‖B‖ < 1)
    (hA : A * conj A + 1 = K * (A + conj A)) (hB : B * conj B + 1 = K * (B + conj B)) :
    (conj B - conj A) * (A - K) * (1 - conj A * B) +
      (B - A) * (conj A - K) * (1 - A * conj B) = 0 := by
  have hAK := ne_of_norm_lt_one_lt hK hAn
  have hBK := ne_of_norm_lt_one_lt hK hBn
  have hAK' := sub_ne_zero.mpr hAK
  have hBK' := sub_ne_zero.mpr hBK
  rw [circ_conj hA hAK, circ_conj hB hBK]
  field_simp
  ring

theorem circ_cross (hK : 1 < K) (hBn : ‖B‖ < 1) (hCn : ‖C‖ < 1)
    (hB : B * conj B + 1 = K * (B + conj B)) (hC : C * conj C + 1 = K * (C + conj C)) :
    (conj C - conj B) * (1 - conj B * C) * (z - B) * (1 - B * w) -
        (C - B) * (1 - B * conj C) * (w - conj B) * (1 - conj B * z) =
      ((conj C - conj B) * (1 - conj B * C) * (-B) - (C - B) * (1 - B * conj C) * (-conj B)) *
        (z * w + 1 - K * (z + w)) := by
  have hBK := ne_of_norm_lt_one_lt hK hBn
  have hCK := ne_of_norm_lt_one_lt hK hCn
  have hBK' := sub_ne_zero.mpr hBK
  have hCK' := sub_ne_zero.mpr hCK
  rw [circ_conj hB hBK, circ_conj hC hCK]
  field_simp
  ring

end Algebra

section Halves

variable {K : ℝ} {A B C z : ℂ}

theorem div_im' (N D : ℂ) : (N / D).im = (N * conj D).im / Complex.normSq D := by
  by_cases hD : D = 0
  · simp [hD]
  have : N / D = (N * conj D) / (Complex.normSq D : ℂ) := by
    rw [← Complex.mul_conj, mul_div_mul_right _ _ ((map_ne_zero _).mpr hD)]
  rw [this, Complex.div_ofReal_im]

theorem im_conj_mobius (ha : ‖A‖ < 1) (hz : ‖z‖ < 1) :
    (conj A * mobius A z).im = (1 - ‖A‖ ^ 2) * (conj A * z).im / ‖1 - conj A * z‖ ^ 2 := by
  have hD := mobius_den_ne ha hz
  have e : conj A * mobius A z = (conj A * (z - A)) / (1 - conj A * z) := by
    unfold mobius; ring
  rw [e, div_im', Complex.normSq_eq_norm_sq]
  congr 1
  simp only [Complex.mul_im, Complex.mul_re, map_sub, map_mul, map_one, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

theorem hhalf_zero_left : hhalf 0 B C z ↔ 0 ≤ (conj B * C).im * (conj B * z).im := by
  unfold hhalf
  simp only [mobius_zero_left]

theorem hhalf_zero_right (hCn : ‖C‖ < 1) (hBn : ‖B‖ < 1) (hz : ‖z‖ < 1) :
    hhalf C 0 B z ↔ 0 ≤ (conj C * B).im * (conj C * z).im := by
  unfold hhalf
  have h0 : mobius C 0 = -C := by simp [mobius]
  have e : ∀ x : ℂ, (conj (-C) * x).im = -(conj C * x).im := fun x => by simp
  rw [h0, e, e, im_conj_mobius hCn hBn, im_conj_mobius hCn hz, neg_mul_neg]
  have hp := one_sub_sq_pos hCn
  have h1 := norm_den_pos hCn hBn
  have h2 := norm_den_pos hCn hz
  have : (1 - ‖C‖ ^ 2) * (conj C * B).im / ‖1 - conj C * B‖ ^ 2 *
      ((1 - ‖C‖ ^ 2) * (conj C * z).im / ‖1 - conj C * z‖ ^ 2) =
      ((1 - ‖C‖ ^ 2) ^ 2 / (‖1 - conj C * B‖ ^ 2 * ‖1 - conj C * z‖ ^ 2)) *
        ((conj C * B).im * (conj C * z).im) := by
    field_simp
  rw [this]
  exact mul_nonneg_iff_of_pos_left (by positivity)

/-- The imaginary part of the numerator of `conj (mobius B C) * mobius B x`, as a polynomial. -/
noncomputable def wim (B C x : ℂ) : ℝ :=
  ((conj C - conj B) * (x - B) * ((1 - conj B * C) * (1 - B * conj x))).im

theorem wim_eq (hK : 1 < K) (hBn : ‖B‖ < 1) (hCn : ‖C‖ < 1)
    (hB : B * conj B + 1 = K * (B + conj B)) (hC : C * conj C + 1 = K * (C + conj C)) (z : ℂ) :
    wim B C z = wim B C 0 * (‖z‖ ^ 2 + 1 - 2 * K * z.re) := by
  have h := circ_cross hK hBn hCn hB hC (z := z) (w := conj z)
  have hF : (z * conj z + 1 - K * (z + conj z) : ℂ) = ((‖z‖ ^ 2 + 1 - 2 * K * z.re : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.add_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hF] at h
  obtain ⟨X1, hX1⟩ : ∃ X, X = (conj C - conj B) * (z - B) *
      ((1 - conj B * C) * (1 - B * conj z)) := ⟨_, rfl⟩
  obtain ⟨X0, hX0⟩ : ∃ X, X = (conj C - conj B) * (0 - B) *
      ((1 - conj B * C) * (1 - B * conj (0 : ℂ))) := ⟨_, rfl⟩
  have c1 : conj X1 = (C - B) * (conj z - conj B) * ((1 - B * conj C) * (1 - conj B * z)) := by
    rw [hX1]; simp only [map_mul, map_sub, map_one, Complex.conj_conj]
  have c0 : conj X0 = (C - B) * (0 - conj B) * ((1 - B * conj C) * (1 - conj B * 0)) := by
    rw [hX0]; simp only [map_mul, map_sub, map_one, Complex.conj_conj, map_zero]
  have e1 := Complex.sub_conj X1
  have e0 := Complex.sub_conj X0
  have h' : X1 - conj X1 = (X0 - conj X0) * ((‖z‖ ^ 2 + 1 - 2 * K * z.re : ℝ) : ℂ) := by
    rw [c1, c0, hX1, hX0]
    simp only [map_zero, mul_zero, sub_zero, zero_sub] at h ⊢
    linear_combination h
  unfold wim
  rw [← hX1, ← hX0]
  have hI : (2 * Complex.I : ℂ) ≠ 0 := by simp
  apply Complex.ofReal_injective
  apply mul_right_cancel₀ hI
  push_cast at e1 e0 h' ⊢
  linear_combination (-1 : ℂ) * e1 + ((‖z‖ : ℂ) ^ 2 + 1 - 2 * K * z.re) * e0 + h'

theorem wim_zero (B C : ℂ) : wim B C 0 = (1 - ‖B‖ ^ 2) * (conj B * C).im := by
  simp only [wim, map_zero, mul_zero, sub_zero, zero_sub]
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem X_im :
    (conj (mobius B C) * mobius B z).im =
      wim B C z / Complex.normSq ((1 - B * conj C) * (1 - conj B * z)) := by
  have e : conj (mobius B C) * mobius B z =
      ((conj C - conj B) * (z - B)) / ((1 - B * conj C) * (1 - conj B * z)) := by
    unfold mobius
    simp only [map_div₀, map_sub, map_mul, map_one, Complex.conj_conj]
    rw [div_mul_div_comm]
  rw [e, div_im']
  unfold wim
  simp only [map_mul, map_sub, map_one, Complex.conj_conj]

/-- The h-half-plane of the h-line `BC` (on the circle `|z|² + 1 = 2 K Re z`) containing `0`
is the exterior of that circle. -/
theorem hhalf_circle (hK : 1 < K) (hBn : ‖B‖ < 1) (hCn : ‖C‖ < 1)
    (hB : B * conj B + 1 = K * (B + conj B)) (hC : C * conj C + 1 = K * (C + conj C))
    (him : (conj B * C).im ≠ 0) (hz : ‖z‖ < 1) :
    hhalf B C 0 z ↔ 0 ≤ ‖z‖ ^ 2 + 1 - 2 * K * z.re := by
  have h0n : ‖(0 : ℂ)‖ < 1 := by simp
  unfold hhalf
  rw [X_im, X_im, wim_eq hK hBn hCn hB hC z]
  have hw0 : wim B C 0 ≠ 0 := by
    rw [wim_zero]; exact mul_ne_zero (one_sub_sq_pos hBn).ne' him
  have hd1 := mobius_den_ne hBn hCn
  have hd2 := mobius_den_ne hBn hz
  have hd1' : (1 - B * conj C) ≠ 0 := by
    have : conj (1 - conj B * C) ≠ 0 := (map_ne_zero _).mpr hd1
    simpa using this
  have hd0 : (1 - conj B * 0) ≠ 0 := by simp
  have n0 : 0 < Complex.normSq ((1 - B * conj C) * (1 - conj B * 0)) :=
    Complex.normSq_pos.mpr (mul_ne_zero hd1' hd0)
  have n1 : 0 < Complex.normSq ((1 - B * conj C) * (1 - conj B * z)) :=
    Complex.normSq_pos.mpr (mul_ne_zero hd1' hd2)
  have : wim B C 0 / Complex.normSq ((1 - B * conj C) * (1 - conj B * 0)) *
      (wim B C 0 * (‖z‖ ^ 2 + 1 - 2 * K * z.re) /
        Complex.normSq ((1 - B * conj C) * (1 - conj B * z))) =
      (wim B C 0 ^ 2 / (Complex.normSq ((1 - B * conj C) * (1 - conj B * 0)) *
        Complex.normSq ((1 - B * conj C) * (1 - conj B * z)))) *
        (‖z‖ ^ 2 + 1 - 2 * K * z.re) := by
    field_simp
  rw [this]
  exact mul_nonneg_iff_of_pos_left (by positivity)

end Halves

section Polar

theorem mem_radialSet_iff {Θ : Set ℝ} {R : ℝ → ℝ} (hΘ : Θ ⊆ Ioc (-π) π) {z : ℂ} :
    z ∈ radialSet Θ R ↔ z ≠ 0 ∧ Complex.arg z ∈ Θ ∧ ‖z‖ ≤ R (Complex.arg z) := by
  constructor
  · rintro ⟨⟨r, θ⟩, ⟨hθ, hr, hrR⟩, rfl⟩
    simp only at hθ hr hrR
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    have ha : Complex.arg (Complex.polarCoord.symm (r, θ)) = θ := by
      rw [Complex.polarCoord_symm_apply]
      have := Complex.arg_mul_cos_add_sin_mul_I hr (hΘ hθ)
      simpa [Complex.ofReal_cos, Complex.ofReal_sin] using this
    refine ⟨?_, ?_, ?_⟩
    · intro h; rw [h] at hn; simp at hn; linarith
    · rw [ha]; exact hθ
    · rw [hn, ha]; exact hrR
  · rintro ⟨hz0, hθ, hr⟩
    refine ⟨(‖z‖, Complex.arg z), ⟨hθ, norm_pos_iff.mpr hz0, hr⟩, ?_⟩
    rw [Complex.polarCoord_symm_apply]
    simp [Complex.ofReal_cos, Complex.ofReal_sin]

theorem im_conj_mul_polar (B z : ℂ) :
    (conj B * z).im = ‖B‖ * ‖z‖ * Real.sin (Complex.arg z - Complex.arg B) := by
  have h1 := Complex.norm_mul_cos_arg B
  have h2 := Complex.norm_mul_sin_arg B
  have h3 := Complex.norm_mul_cos_arg z
  have h4 := Complex.norm_mul_sin_arg z
  rw [Real.sin_sub]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  rw [← h1, ← h2, ← h3, ← h4]
  ring

theorem cone_base {θ₀ θ₁ θ : ℝ} (h01 : θ₀ < θ₁) (h0 : |θ₀| < π / 2) (h1 : |θ₁| < π / 2)
    (hθ : θ ∈ Ioc (-π) π) :
    (0 ≤ Real.sin (θ₁ - θ₀) * Real.sin (θ - θ₀) ∧ 0 ≤ Real.sin (θ₀ - θ₁) * Real.sin (θ - θ₁)) ↔
      θ₀ ≤ θ ∧ θ ≤ θ₁ := by
  obtain ⟨a0, a0'⟩ := abs_lt.mp h0
  obtain ⟨a1, a1'⟩ := abs_lt.mp h1
  obtain ⟨t0, t1⟩ := hθ
  have hpi := Real.pi_pos
  have hd : 0 < Real.sin (θ₁ - θ₀) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hd' : Real.sin (θ₀ - θ₁) < 0 := by
    rw [show θ₀ - θ₁ = -(θ₁ - θ₀) by ring, Real.sin_neg]; linarith
  have e1 : 0 ≤ Real.sin (θ₁ - θ₀) * Real.sin (θ - θ₀) ↔ 0 ≤ Real.sin (θ - θ₀) :=
    mul_nonneg_iff_of_pos_left hd
  have e2 : 0 ≤ Real.sin (θ₀ - θ₁) * Real.sin (θ - θ₁) ↔ Real.sin (θ - θ₁) ≤ 0 := by
    constructor
    · intro h
      by_contra hh
      push Not at hh
      exact absurd h (not_le.mpr (mul_neg_of_neg_of_pos hd' hh))
    · intro h; exact mul_nonneg_of_nonpos_of_nonpos hd'.le h
  rw [e1, e2]
  constructor
  · rintro ⟨s0, s1⟩
    constructor
    · by_contra hlt
      push Not at hlt
      have hx : θ - θ₀ ≤ -π := by
        by_contra hh
        push Not at hh
        have := Real.sin_neg_of_neg_of_neg_pi_lt (x := θ - θ₀) (by linarith) hh
        linarith
      have : 0 < Real.sin (θ - θ₁) := by
        rw [← Real.sin_add_two_pi]
        apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
      linarith
    · by_contra hgt
      push Not at hgt
      have hy : π ≤ θ - θ₁ := by
        by_contra hh
        push Not at hh
        have := Real.sin_pos_of_pos_of_lt_pi (x := θ - θ₁) (by linarith) hh
        linarith
      have : Real.sin (θ - θ₀) < 0 := by
        rw [← Real.sin_sub_two_pi]
        apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith
      linarith
  · rintro ⟨a, b⟩
    exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith),
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)⟩

theorem cone_iff {θ₀ θ₁ θ : ℝ} (hne : θ₀ ≠ θ₁) (h0 : |θ₀| < π / 2) (h1 : |θ₁| < π / 2)
    (hθ : θ ∈ Ioc (-π) π) :
    (0 ≤ Real.sin (θ₁ - θ₀) * Real.sin (θ - θ₀) ∧ 0 ≤ Real.sin (θ₀ - θ₁) * Real.sin (θ - θ₁)) ↔
      min θ₀ θ₁ ≤ θ ∧ θ ≤ max θ₀ θ₁ := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    exact cone_base h h0 h1 hθ
  · rw [min_eq_right h.le, max_eq_left h.le, and_comm]
    exact cone_base h h1 h0 hθ

theorem radial_iff {k r : ℝ} (hk : 1 < k) (hr1 : r < 1) :
    0 ≤ r ^ 2 + 1 - 2 * k * r ↔ r ≤ k - Real.sqrt (k ^ 2 - 1) := by
  have hpos : 0 < k ^ 2 - 1 := by nlinarith
  have hs0 : 0 < Real.sqrt (k ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hs2 : Real.sqrt (k ^ 2 - 1) ^ 2 = k ^ 2 - 1 := Real.sq_sqrt hpos.le
  set s := Real.sqrt (k ^ 2 - 1)
  have key : r ^ 2 + 1 - 2 * k * r = (r - (k - s)) * (r - (k + s)) := by
    linear_combination hs2
  have hneg : r - (k + s) < 0 := by linarith
  rw [key]
  constructor
  · intro h
    by_contra hh
    push Not at hh
    have : (r - (k - s)) * (r - (k + s)) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  · intro h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hneg.le

theorem one_lt_K_cos {K ρ c : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (h : ρ ^ 2 + 1 = 2 * K * (ρ * c)) :
    1 < K * c := by
  by_contra hh
  push Not at hh
  nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hh), sq_nonneg (1 - ρ)]

theorem one_lt_K_cos_between {K θ₀ θ₁ θ : ℝ} (hK : 0 < K) (h0 : |θ₀| < π / 2) (h1 : |θ₁| < π / 2)
    (c0 : 1 < K * Real.cos θ₀) (c1 : 1 < K * Real.cos θ₁) (a : θ₀ ≤ θ) (b : θ ≤ θ₁) :
    1 < K * Real.cos θ := by
  have habs : |θ| ≤ max |θ₀| |θ₁| := abs_le_max_abs_abs a b
  have hpi := Real.pi_pos
  have hmax : max |θ₀| |θ₁| ≤ π := max_le (by linarith) (by linarith)
  have hcos : Real.cos (max |θ₀| |θ₁|) ≤ Real.cos θ := by
    rw [← Real.cos_abs θ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hmax habs
  rcases max_choice |θ₀| |θ₁| with h | h
  · rw [h, Real.cos_abs] at hcos
    nlinarith
  · rw [h, Real.cos_abs] at hcos
    nlinarith

end Polar

section Normalized

variable {K : ℝ} {B C z : ℂ}

theorem circ_real (hB : B * conj B + 1 = K * (B + conj B)) : ‖B‖ ^ 2 + 1 = 2 * K * B.re := by
  rw [Complex.mul_conj, Complex.add_conj] at hB
  have h : Complex.normSq B + 1 = K * (2 * B.re) := by exact_mod_cast hB
  rw [Complex.normSq_eq_norm_sq] at h
  linarith

theorem circ_facts (hK : 1 < K) (hBn : ‖B‖ < 1) (hB : B * conj B + 1 = K * (B + conj B)) :
    B ≠ 0 ∧ |Complex.arg B| < π / 2 ∧ 1 < K * Real.cos (Complex.arg B) := by
  have hB0 : B ≠ 0 := by
    rintro rfl
    simp at hB
  have hr := circ_real hB
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB0
  have hre : 0 < B.re := by
    by_contra h
    push Not at h
    nlinarith [sq_nonneg ‖B‖]
  refine ⟨hB0, ?_, ?_⟩
  · rw [Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl hre
  · apply one_lt_K_cos hn hBn
    rw [Complex.norm_mul_cos_arg]; exact hr

theorem circ_hk {θ₀ θ₁ : ℝ} (hK : 1 < K) (h0 : |θ₀| < π / 2) (h1 : |θ₁| < π / 2)
    (c0 : 1 < K * Real.cos θ₀) (c1 : 1 < K * Real.cos θ₁) :
    ∀ θ, min θ₀ θ₁ ≤ θ → θ ≤ max θ₀ θ₁ → 1 < K * Real.cos θ := by
  intro θ h1' h2'
  rcases le_total θ₀ θ₁ with h | h
  · rw [min_eq_left h] at h1'
    rw [max_eq_right h] at h2'
    exact one_lt_K_cos_between (by linarith) h0 h1 c0 c1 h1' h2'
  · rw [min_eq_right h] at h1'
    rw [max_eq_left h] at h2'
    exact one_lt_K_cos_between (by linarith) h1 h0 c1 c0 h1' h2'

theorem hsolid_zero_iff (hK : 1 < K) (hBn : ‖B‖ < 1) (hCn : ‖C‖ < 1)
    (hB : B * conj B + 1 = K * (B + conj B)) (hC : C * conj C + 1 = K * (C + conj C))
    (him : (conj B * C).im ≠ 0) :
    z ∈ hsolid 0 B C ↔ ‖z‖ < 1 ∧ 0 ≤ (conj B * C).im * (conj B * z).im ∧
      0 ≤ (conj C * B).im * (conj C * z).im ∧ 0 ≤ ‖z‖ ^ 2 + 1 - 2 * K * z.re := by
  constructor
  · rintro ⟨hz, h1, h2, h3⟩
    exact ⟨hz, hhalf_zero_left.mp h1, (hhalf_zero_right hCn hBn hz).mp h3,
      (hhalf_circle hK hBn hCn hB hC him hz).mp h2⟩
  · rintro ⟨hz, h1, h2, h3⟩
    exact ⟨hz, hhalf_zero_left.mpr h1, (hhalf_circle hK hBn hCn hB hC him hz).mpr h3,
      (hhalf_zero_right hCn hBn hz).mpr h2⟩

/-- In the normalized position (the h-line `BC` is on the circle `|z|² + 1 = 2 K Re z`), the solid
h-triangle `0BC` is, up to the vertex `0`, the polar region between the rays through `B` and `C` below
the arc of that circle. -/
theorem hsolid_zero_eq (hK : 1 < K) (hBn : ‖B‖ < 1) (hCn : ‖C‖ < 1)
    (hB : B * conj B + 1 = K * (B + conj B)) (hC : C * conj C + 1 = K * (C + conj C))
    (him : (conj B * C).im ≠ 0) :
    hsolid 0 B C = radialSet (Icc (min (Complex.arg B) (Complex.arg C))
      (max (Complex.arg B) (Complex.arg C))) (geodR K 0) ∪ {0} := by
  obtain ⟨hB0, hargB, cB⟩ := circ_facts hK hBn hB
  obtain ⟨hC0, hargC, cC⟩ := circ_facts hK hCn hC
  have hne : Complex.arg B ≠ Complex.arg C := by
    intro h
    apply him
    rw [im_conj_mul_polar, h, sub_self, Real.sin_zero, mul_zero]
  have hpi := Real.pi_pos
  have hIcc : Icc (min (Complex.arg B) (Complex.arg C)) (max (Complex.arg B) (Complex.arg C)) ⊆
      Ioc (-π) π := by
    intro t ht
    obtain ⟨a, b⟩ := abs_lt.mp hargB
    obtain ⟨c, d⟩ := abs_lt.mp hargC
    have h1 : -(π / 2) < min (Complex.arg B) (Complex.arg C) := lt_min a c
    have h2 : max (Complex.arg B) (Complex.arg C) < π / 2 := max_lt b d
    constructor <;> linarith [ht.1, ht.2]
  have hk := circ_hk hK hargB hargC cB cC
  ext z
  simp only [mem_union, mem_singleton_iff]
  by_cases hz0 : z = 0
  · subst hz0
    constructor
    · intro _; exact Or.inr rfl
    · intro _
      rw [hsolid_zero_iff hK hBn hCn hB hC him]
      simp
  rw [or_iff_left hz0, mem_radialSet_iff hIcc, hsolid_zero_iff hK hBn hCn hB hC him]
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hθz : Complex.arg z ∈ Ioc (-π) π := ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩
  have eP : (0 ≤ (conj B * C).im * (conj B * z).im ∧ 0 ≤ (conj C * B).im * (conj C * z).im) ↔
      (0 ≤ Real.sin (Complex.arg C - Complex.arg B) * Real.sin (Complex.arg z - Complex.arg B) ∧
       0 ≤ Real.sin (Complex.arg B - Complex.arg C) * Real.sin (Complex.arg z - Complex.arg C)) := by
    rw [im_conj_mul_polar B C, im_conj_mul_polar B z, im_conj_mul_polar C B,
      im_conj_mul_polar C z]
    have nB : 0 < ‖B‖ := norm_pos_iff.mpr hB0
    have nC : 0 < ‖C‖ := norm_pos_iff.mpr hC0
    have e1 : ∀ s1 s2 : ℝ, (‖B‖ * ‖C‖ * s1) * (‖B‖ * ‖z‖ * s2) = (‖B‖ ^ 2 * ‖C‖ * ‖z‖) * (s1 * s2) :=
      fun s1 s2 => by ring
    have e2 : ∀ s1 s2 : ℝ, (‖C‖ * ‖B‖ * s1) * (‖C‖ * ‖z‖ * s2) = (‖C‖ ^ 2 * ‖B‖ * ‖z‖) * (s1 * s2) :=
      fun s1 s2 => by ring
    have p1 : 0 < ‖B‖ ^ 2 * ‖C‖ * ‖z‖ := by positivity
    have p2 : 0 < ‖C‖ ^ 2 * ‖B‖ * ‖z‖ := by positivity
    rw [e1, e2, mul_nonneg_iff_of_pos_left p1, mul_nonneg_iff_of_pos_left p2]
  have hcone := cone_iff hne hargB hargC hθz
  have hg : ∀ θ, geodR K 0 θ = K * Real.cos θ - Real.sqrt ((K * Real.cos θ) ^ 2 - 1) := by
    intro θ; simp [geodR]
  have hrad : Complex.arg z ∈ Icc (min (Complex.arg B) (Complex.arg C))
      (max (Complex.arg B) (Complex.arg C)) → ‖z‖ < 1 →
      (0 ≤ ‖z‖ ^ 2 + 1 - 2 * K * z.re ↔ ‖z‖ ≤ geodR K 0 (Complex.arg z)) := by
    intro hθ hz1
    have hkk := hk _ hθ.1 hθ.2
    have hre : z.re = ‖z‖ * Real.cos (Complex.arg z) := (Complex.norm_mul_cos_arg z).symm
    rw [hg, ← radial_iff hkk hz1, hre]
    constructor <;> intro h <;> nlinarith
  constructor
  · rintro ⟨hz1, h1, h2, h3⟩
    have hc := (hcone).mp (eP.mp ⟨h1, h2⟩)
    exact ⟨hz0, hc, (hrad hc hz1).mp h3⟩
  · rintro ⟨-, hc, hle⟩
    have hkk := hk _ hc.1 hc.2
    have hlt := (geodR_facts hkk).2.1
    rw [← hg] at hlt
    have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hle hlt
    obtain ⟨e1', e2'⟩ := eP.mpr (hcone.mpr hc)
    exact ⟨hz1, e1', e2', (hrad hc hz1).mpr hle⟩

theorem harea_union_zero (s : Set ℂ) : harea (s ∪ {0}) = harea s := by
  unfold harea
  have h : (s ∪ {0} : Set ℂ) =ᵐ[volume] s :=
    union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr (measure_singleton 0))
  exact setLIntegral_congr (h.inter (ae_eq_refl _))

/-- The area of the solid triangle `0BC` in normalized position: `G(θ₁) - G(θ₀)` between the extreme
rays (`harea_geodesic_sector`). -/
theorem harea_hsolid_zero (hK : 1 < K) (hBn : ‖B‖ < 1) (hCn : ‖C‖ < 1)
    (hB : B * conj B + 1 = K * (B + conj B)) (hC : C * conj C + 1 = K * (C + conj C))
    (him : (conj B * C).im ≠ 0) :
    harea (hsolid 0 B C) = ENNReal.ofReal (geodG K 0 (max (Complex.arg B) (Complex.arg C)) -
      geodG K 0 (min (Complex.arg B) (Complex.arg C))) := by
  obtain ⟨hB0, hargB, cB⟩ := circ_facts hK hBn hB
  obtain ⟨hC0, hargC, cC⟩ := circ_facts hK hCn hC
  have hk := circ_hk hK hargB hargC cB cC
  rw [hsolid_zero_eq hK hBn hCn hB hC him, harea_union_zero]
  obtain ⟨a, b⟩ := abs_lt.mp hargB
  obtain ⟨c, d⟩ := abs_lt.mp hargC
  have hpi := Real.pi_pos
  have hmM : min (Complex.arg B) (Complex.arg C) ≤ max (Complex.arg B) (Complex.arg C) :=
    min_le_max
  have hm : -(π / 2) < min (Complex.arg B) (Complex.arg C) := lt_min a c
  have hM : max (Complex.arg B) (Complex.arg C) < π / 2 := max_lt b d
  set m := min (Complex.arg B) (Complex.arg C)
  set M := max (Complex.arg B) (Complex.arg C)
  have hΘ : Icc m M ⊆ Ioo (-π) π := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hΘ' : Ioc m M ⊆ Ioo (-π) π := fun t ht => hΘ (Ioc_subset_Icc_self ht)
  have hRm : Measurable (geodR K 0) := by
    unfold geodR
    fun_prop
  have hk' : ∀ θ ∈ Icc m M, 1 < K * Real.cos (θ - 0) := fun θ hθ => by
    rw [sub_zero]; exact hk θ hθ.1 hθ.2
  have hR0 : ∀ θ ∈ Icc m M, 0 ≤ geodR K 0 θ := fun θ hθ => (geodR_facts (hk' θ hθ)).1.le
  have hR1 : ∀ θ ∈ Icc m M, geodR K 0 θ < 1 := fun θ hθ => (geodR_facts (hk' θ hθ)).2.1
  have e1 := harea_radialSet measurableSet_Icc hΘ hRm hR0 hR1
  have e2 := harea_radialSet measurableSet_Ioc hΘ' hRm (fun θ hθ => hR0 θ (Ioc_subset_Icc_self hθ))
    (fun θ hθ => hR1 θ (Ioc_subset_Icc_self hθ))
  have key := harea_geodesic_sector (φ := 0) hK hmM hΘ' hk'
  rw [e1, ← key, e2]
  exact (setLIntegral_congr Ioc_ae_eq_Icc).symm

end Normalized

section Angles

variable {K : ℝ} {P Q : ℂ}

/-- The tangent direction `conj P * mobius P Q` of the h-line `PQ` at `P` (seen in the picture of
`mobius P`) is orthogonal to the vector `conj P * (P - K)` (the radius of the circle at `P`,
rotated by `conj P`). -/
theorem tangent_orth (hK : 1 < K) (hPn : ‖P‖ < 1) (hQn : ‖Q‖ < 1)
    (hP : P * conj P + 1 = K * (P + conj P)) (hQ : Q * conj Q + 1 = K * (Q + conj Q)) :
    (conj P * mobius P Q).re * (conj P * (P - K)).re +
      (conj P * mobius P Q).im * (conj P * (P - K)).im = 0 := by
  have hD := mobius_den_ne hPn hQn
  have horth := circ_orth hK hPn hQn hP hQ
  set X : ℂ := (Q - P) * (conj P - K) * (1 - P * conj Q) with hX
  have hXc : conj X = (conj Q - conj P) * (P - K) * (1 - conj P * Q) := by
    rw [hX]; simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  have hXre : X.re = 0 := by
    have h1 : X + conj X = ((2 * X.re : ℝ) : ℂ) := Complex.add_conj X
    have h2 : (X + conj X) = 0 := by rw [hXc, hX]; linear_combination horth
    rw [h2] at h1
    have h3 : (2 * X.re : ℝ) = 0 := by exact_mod_cast h1.symm
    linarith
  have hD1 : 1 - Q * conj P ≠ 0 := by rwa [mul_comm]
  have hD2 : 1 - P * conj Q ≠ 0 := by
    have : conj (1 - conj P * Q) ≠ 0 := (map_ne_zero _).mpr hD
    simpa using this
  have hw : mobius P Q * (conj P - K) = X / (Complex.normSq (1 - conj P * Q) : ℂ) := by
    rw [← Complex.mul_conj, hX]
    unfold mobius
    simp only [map_sub, map_mul, map_one, Complex.conj_conj]
    field_simp
  have hpq : (conj P * mobius P Q) * conj (conj P * (P - K)) =
      ((P * conj P : ℂ)) * (mobius P Q * (conj P - K)) := by
    simp only [map_mul, map_sub, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hre : ((conj P * mobius P Q) * conj (conj P * (P - K))).re = 0 := by
    rw [hpq, hw, Complex.mul_conj]
    rw [Complex.re_ofReal_mul, Complex.div_ofReal_re, hXre]
    simp
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hre
  linear_combination hre

theorem re_div_norm_pos (p q : ℂ) (hq : q.re < 0) (h : p.re * q.re + p.im * q.im = 0)
    (hy : 0 < p.im) : p.re / ‖p‖ = q.im / ‖q‖ := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr (fun h0 => by rw [h0] at hq; simp at hq)
  have hq0 : q.re ≠ 0 := hq.ne
  have hre : p.re = -(p.im * q.im) / q.re := by
    rw [eq_div_iff hq.ne]; linarith
  have hq2 : ‖q‖ ^ 2 = q.re * q.re + q.im * q.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hn : ‖p‖ = p.im * ‖q‖ / (-q.re) := by
    have hsq : ‖p‖ ^ 2 = (p.im * ‖q‖ / (-q.re)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, div_pow, mul_pow, hq2, hre]
      field_simp
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (by have : 0 < -q.re := by linarith
                                             positivity) two_ne_zero).mp hsq
  rw [hn, hre]
  field_simp

theorem re_div_norm_neg (p q : ℂ) (hq : q.re < 0) (h : p.re * q.re + p.im * q.im = 0)
    (hy : p.im < 0) : p.re / ‖p‖ = -(q.im / ‖q‖) := by
  have := re_div_norm_pos (-p) q hq (by simp; linarith) (by simpa using hy)
  rw [Complex.neg_re, norm_neg, neg_div] at this
  linarith

theorem cos_hangle_zero_eq (P Q : ℂ) :
    Real.cos (hangle 0 P Q) = -((conj P * mobius P Q).re / ‖conj P * mobius P Q‖) := by
  unfold hangle
  rw [InnerProductGeometry.cos_angle, mobius_zero_right, Complex.inner, norm_neg, norm_mul,
    Complex.norm_conj, map_neg]
  have e : (mobius P Q * -(conj P)).re = -(conj P * mobius P Q).re := by
    rw [mul_neg, mul_comm, Complex.neg_re]
  rw [e, neg_div]

theorem q_facts (hK : 1 < K) (hPn : ‖P‖ < 1) (hP : P * conj P + 1 = K * (P + conj P)) :
    (conj P * (P - K)).re < 0 ∧ (conj P * (P - K)).im = K * P.im ∧
      ‖conj P * (P - K)‖ = ‖P‖ * Real.sqrt (K ^ 2 - 1) := by
  have hr := circ_real hP
  have hn := sq_nonneg ‖P‖
  have hK2 : 0 < K ^ 2 - 1 := by nlinarith
  have hre : (conj P * (P - K)).re = (‖P‖ ^ 2 - 1) / 2 := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [Complex.sq_norm, Complex.normSq_apply] at hr ⊢
    nlinarith
  refine ⟨by rw [hre]; nlinarith [norm_nonneg P], ?_, ?_⟩
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [norm_mul, Complex.norm_conj]
    congr 1
    have hsq : ‖P - (K : ℂ)‖ ^ 2 = K ^ 2 - 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [Complex.sq_norm, Complex.normSq_apply] at hr
      nlinarith
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- The h-angle at `P` of the triangle `0PQ` in normalized position, counterclockwise case:
`cos ∠_h 0 P Q = -K sin θ_P / √(K² - 1)` (`K P.im / ‖P‖ = K sin θ_P`). -/
theorem cos_hangle_zero_pos (hK : 1 < K) (hPn : ‖P‖ < 1) (hQn : ‖Q‖ < 1)
    (hP : P * conj P + 1 = K * (P + conj P)) (hQ : Q * conj Q + 1 = K * (Q + conj Q))
    (him : 0 < (conj P * Q).im) :
    Real.cos (hangle 0 P Q) = -(K * P.im / (‖P‖ * Real.sqrt (K ^ 2 - 1))) := by
  obtain ⟨h1, h2, h3⟩ := q_facts hK hPn hP
  have hy : 0 < (conj P * mobius P Q).im := by
    rw [im_conj_mobius hPn hQn]
    have := one_sub_sq_pos hPn
    have := norm_den_pos hPn hQn
    positivity
  rw [cos_hangle_zero_eq, re_div_norm_pos _ _ h1 (tangent_orth hK hPn hQn hP hQ) hy, h2, h3]

theorem cos_hangle_zero_neg (hK : 1 < K) (hPn : ‖P‖ < 1) (hQn : ‖Q‖ < 1)
    (hP : P * conj P + 1 = K * (P + conj P)) (hQ : Q * conj Q + 1 = K * (Q + conj Q))
    (him : (conj P * Q).im < 0) :
    Real.cos (hangle 0 P Q) = K * P.im / (‖P‖ * Real.sqrt (K ^ 2 - 1)) := by
  obtain ⟨h1, h2, h3⟩ := q_facts hK hPn hP
  have hy : (conj P * mobius P Q).im < 0 := by
    rw [im_conj_mobius hPn hQn]
    have := one_sub_sq_pos hPn
    have := norm_den_pos hPn hQn
    have : 0 < ‖1 - conj P * Q‖ ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by assumption) him) this
  rw [cos_hangle_zero_eq, re_div_norm_neg _ _ h1 (tangent_orth hK hPn hQn hP hQ) hy, h2, h3]
  ring

theorem hangle_eq_arccos (x y z : ℂ) : hangle x y z = Real.arccos (Real.cos (hangle x y z)) := by
  exact (Real.arccos_cos (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_le_pi _ _)).symm

theorem K_im_div (hP0 : P ≠ 0) (K S : ℝ) : K * P.im / (‖P‖ * S) = K * Real.sin (Complex.arg P) / S := by
  have hn : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hP0
  rw [← Complex.norm_mul_sin_arg P]
  by_cases hS : S = 0
  · simp [hS]
  · field_simp

theorem hangle_pos_arcsin (hK : 1 < K) (hPn : ‖P‖ < 1) (hQn : ‖Q‖ < 1)
    (hP : P * conj P + 1 = K * (P + conj P)) (hQ : Q * conj Q + 1 = K * (Q + conj Q))
    (him : 0 < (conj P * Q).im) :
    hangle 0 P Q = π / 2 + Real.arcsin (K * Real.sin (Complex.arg P) / Real.sqrt (K ^ 2 - 1)) := by
  obtain ⟨hP0, -, -⟩ := circ_facts hK hPn hP
  rw [hangle_eq_arccos, cos_hangle_zero_pos hK hPn hQn hP hQ him, K_im_div hP0, Real.arccos_neg,
    Real.arcsin_eq_pi_div_two_sub_arccos]
  ring

theorem hangle_neg_arcsin (hK : 1 < K) (hPn : ‖P‖ < 1) (hQn : ‖Q‖ < 1)
    (hP : P * conj P + 1 = K * (P + conj P)) (hQ : Q * conj Q + 1 = K * (Q + conj Q))
    (him : (conj P * Q).im < 0) :
    hangle 0 P Q = π / 2 - Real.arcsin (K * Real.sin (Complex.arg P) / Real.sqrt (K ^ 2 - 1)) := by
  obtain ⟨hP0, -, -⟩ := circ_facts hK hPn hP
  rw [hangle_eq_arccos, cos_hangle_zero_neg hK hPn hQn hP hQ him, K_im_div hP0,
    Real.arcsin_eq_pi_div_two_sub_arccos]
  ring

/-- The angle at the centre of the triangle `0BC` is the difference of the arguments. -/
theorem hangle_at_zero {B C : ℂ} (hB0 : B ≠ 0) (hC0 : C ≠ 0) (hargB : |Complex.arg B| < π / 2)
    (hargC : |Complex.arg C| < π / 2) :
    hangle B 0 C = max (Complex.arg B) (Complex.arg C) - min (Complex.arg B) (Complex.arg C) := by
  have hpi := Real.pi_pos
  obtain ⟨a, b⟩ := abs_lt.mp hargB
  obtain ⟨c, d⟩ := abs_lt.mp hargC
  rw [hangle_eq_arccos]
  have hcos : Real.cos (hangle B 0 C) = Real.cos (max (Complex.arg B) (Complex.arg C) -
      min (Complex.arg B) (Complex.arg C)) := by
    unfold hangle
    simp only [mobius_zero_left]
    rw [InnerProductGeometry.cos_angle, Complex.inner]
    have nB : ‖B‖ ≠ 0 := norm_ne_zero_iff.mpr hB0
    have nC : ‖C‖ ≠ 0 := norm_ne_zero_iff.mpr hC0
    have h1 : Real.cos (max (Complex.arg B) (Complex.arg C) - min (Complex.arg B) (Complex.arg C)) =
        Real.cos (Complex.arg C - Complex.arg B) := by
      rcases le_total (Complex.arg B) (Complex.arg C) with h | h
      · rw [max_eq_right h, min_eq_left h]
      · rw [max_eq_left h, min_eq_right h, ← Real.cos_neg]; ring_nf
    rw [h1, Real.cos_sub]
    have e1 := Complex.norm_mul_cos_arg B
    have e2 := Complex.norm_mul_sin_arg B
    have e3 := Complex.norm_mul_cos_arg C
    have e4 := Complex.norm_mul_sin_arg C
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [← e1, ← e2, ← e3, ← e4]
    field_simp
    ring
  rw [hcos]
  exact Real.arccos_cos (sub_nonneg.mpr min_le_max)
    (by linarith [max_lt b d, lt_min a c])

/-- **Area equals defect for a triangle with a vertex at the centre**, in normalized position. -/
@[kb "petrunin2025" "Section 20I, p. 176"]
theorem harea_hsolid_zero_defect {B C : ℂ} (hK : 1 < K) (hBn : ‖B‖ < 1) (hCn : ‖C‖ < 1)
    (hB : B * conj B + 1 = K * (B + conj B)) (hC : C * conj C + 1 = K * (C + conj C))
    (him : (conj B * C).im ≠ 0) :
    harea (hsolid 0 B C) = ENNReal.ofReal (π - (hangle B 0 C + hangle 0 B C + hangle 0 C B)) := by
  obtain ⟨hB0, hargB, cB⟩ := circ_facts hK hBn hB
  obtain ⟨hC0, hargC, cC⟩ := circ_facts hK hCn hC
  have hpi := Real.pi_pos
  obtain ⟨a, b⟩ := abs_lt.mp hargB
  obtain ⟨c, d⟩ := abs_lt.mp hargC
  have hne : Complex.arg B ≠ Complex.arg C := by
    intro h
    apply him
    rw [im_conj_mul_polar, h, sub_self, Real.sin_zero, mul_zero]
  rw [harea_hsolid_zero hK hBn hCn hB hC him, hangle_at_zero hB0 hC0 hargB hargC]
  congr 1
  have nB : 0 < ‖B‖ := norm_pos_iff.mpr hB0
  have nC : 0 < ‖C‖ := norm_pos_iff.mpr hC0
  simp only [geodG, sub_zero]
  rcases lt_or_gt_of_ne hne with h | h
  · have s1 : 0 < (conj B * C).im := by
      rw [im_conj_mul_polar]
      have := Real.sin_pos_of_pos_of_lt_pi (x := Complex.arg C - Complex.arg B) (by linarith)
        (by linarith)
      positivity
    have s2 : (conj C * B).im < 0 := by
      rw [im_conj_mul_polar]
      have := Real.sin_neg_of_neg_of_neg_pi_lt (x := Complex.arg B - Complex.arg C) (by linarith)
        (by linarith)
      exact mul_neg_of_pos_of_neg (by positivity) this
    rw [hangle_pos_arcsin hK hBn hCn hB hC s1, hangle_neg_arcsin hK hCn hBn hC hB s2,
      max_eq_right h.le, min_eq_left h.le]
    ring
  · have s1 : (conj B * C).im < 0 := by
      rw [im_conj_mul_polar]
      have := Real.sin_neg_of_neg_of_neg_pi_lt (x := Complex.arg C - Complex.arg B) (by linarith)
        (by linarith)
      exact mul_neg_of_pos_of_neg (by positivity) this
    have s2 : 0 < (conj C * B).im := by
      rw [im_conj_mul_polar]
      have := Real.sin_pos_of_pos_of_lt_pi (x := Complex.arg B - Complex.arg C) (by linarith)
        (by linarith)
      positivity
    rw [hangle_neg_arcsin hK hBn hCn hB hC s1, hangle_pos_arcsin hK hCn hBn hC hB s2,
      max_eq_left h.le, min_eq_right h.le]
    ring

end Angles

section Assembly

theorem circ_rot {c B : ℂ} (hc : c ≠ 0) (h : c.re * B.re + c.im * B.im = (‖B‖ ^ 2 + 1) / 2) :
    (conj c / (‖c‖ : ℂ) * B) * conj (conj c / (‖c‖ : ℂ) * B) + 1 =
      ‖c‖ * (conj c / (‖c‖ : ℂ) * B + conj (conj c / (‖c‖ : ℂ) * B)) := by
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hu : ‖conj c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
      div_self hn.ne']
  have hre : (conj c / (‖c‖ : ℂ) * B).re = (c.re * B.re + c.im * B.im) / ‖c‖ := by
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
    simp [Complex.mul_re]
  rw [Complex.mul_conj, Complex.add_conj]
  have hns : Complex.normSq (conj c / (‖c‖ : ℂ) * B) = ‖B‖ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (conj c / (‖c‖ : ℂ)), hu,
      Complex.normSq_eq_norm_sq]
    ring
  have : Complex.normSq (conj c / (‖c‖ : ℂ) * B) + 1 =
      ‖c‖ * (2 * (conj c / (‖c‖ : ℂ) * B).re) := by
    rw [hns, hre]
    field_simp
    linarith
  exact_mod_cast this

theorem exists_normalize {B C : ℂ} (hBn : ‖B‖ < 1) (him : (conj B * C).im ≠ 0) :
    ∃ (u : ℂ) (K : ℝ), ‖u‖ = 1 ∧ 1 < K ∧
      (u * B) * conj (u * B) + 1 = K * (u * B + conj (u * B)) ∧
      (u * C) * conj (u * C) + 1 = K * (u * C + conj (u * C)) ∧
      (conj (u * B) * (u * C)).im ≠ 0 := by
  have hdet : B.re * C.im - B.im * C.re ≠ 0 := by
    intro h; apply him; simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; linarith
  set pB := (‖B‖ ^ 2 + 1) / 2 with hpB
  set pC := (‖C‖ ^ 2 + 1) / 2 with hpC
  set x := (pB * C.im - pC * B.im) / (B.re * C.im - B.im * C.re) with hx
  set y := (B.re * pC - C.re * pB) / (B.re * C.im - B.im * C.re) with hy
  have hxd : x * (B.re * C.im - B.im * C.re) = pB * C.im - pC * B.im := by
    rw [hx]; exact div_mul_cancel₀ _ hdet
  have hyd : y * (B.re * C.im - B.im * C.re) = B.re * pC - C.re * pB := by
    rw [hy]; exact div_mul_cancel₀ _ hdet
  have h1 : x * B.re + y * B.im = pB := by
    apply mul_right_cancel₀ hdet
    linear_combination B.re * hxd + B.im * hyd
  have h2 : x * C.re + y * C.im = pC := by
    apply mul_right_cancel₀ hdet
    linear_combination C.re * hxd + C.im * hyd
  set c : ℂ := ⟨x, y⟩ with hc
  have hcB : c.re * B.re + c.im * B.im = (‖B‖ ^ 2 + 1) / 2 := h1
  have hcC : c.re * C.re + c.im * C.im = (‖C‖ ^ 2 + 1) / 2 := h2
  have hBsq : ‖B‖ ^ 2 = B.re * B.re + B.im * B.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hn1 : 0 ≤ ‖B‖ := norm_nonneg B
  have hn2 : 0 ≤ ‖B‖ ^ 2 := sq_nonneg _
  have hn3 : ‖B‖ ^ 2 < 1 := by nlinarith
  have hs : 1 < x * x + y * y := by
    by_contra hh
    push Not at hh
    nlinarith [sq_nonneg (x * B.im - y * B.re), mul_nonneg (sub_nonneg.2 hh) hn2, sq_nonneg (‖B‖ ^ 2 - 1)]
  have hcn : ‖c‖ ^ 2 = x * x + y * y := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0] at hcn; simp at hcn; linarith
  have hK : 1 < ‖c‖ := by
    by_contra hh
    push Not at hh
    nlinarith [norm_nonneg c]
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hu : ‖conj c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
      div_self hn.ne']
  refine ⟨conj c / (‖c‖ : ℂ), ‖c‖, hu, hK, circ_rot hc0 hcB, circ_rot hc0 hcC, ?_⟩
  have : conj (conj c / (‖c‖ : ℂ) * B) * (conj c / (‖c‖ : ℂ) * C) =
      (conj (conj c / (‖c‖ : ℂ)) * (conj c / (‖c‖ : ℂ))) * (conj B * C) := by
    rw [map_mul]; ring
  rw [this, conj_mul_self_unit hu, one_mul]
  exact him

theorem eq_real_mul_of_im_zero {B C : ℂ} (hB0 : B ≠ 0) (h : (conj B * C).im = 0) :
    C = (((conj B * C).re / Complex.normSq B : ℝ) : ℂ) * B := by
  have hN : (Complex.normSq B : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hB0).ne'
  have hr : conj B * C = (((conj B * C).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using h)
  have key : (Complex.normSq B : ℂ) * C = (((conj B * C).re : ℝ) : ℂ) * B := by
    rw [← Complex.mul_conj]
    linear_combination B * hr
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hN]
  linear_combination key

/-- Moving the triangle by an h-motion changes neither side of the identity "area = defect". -/
theorem defect_transfer {a u A B C : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) (hA : ‖A‖ < 1)
    (hB : ‖B‖ < 1) (hC : ‖C‖ < 1) :
    harea (hsolid (u * mobius a A) (u * mobius a B) (u * mobius a C)) =
        ENNReal.ofReal (π - (hangle (u * mobius a B) (u * mobius a A) (u * mobius a C) +
          hangle (u * mobius a A) (u * mobius a B) (u * mobius a C) +
          hangle (u * mobius a A) (u * mobius a C) (u * mobius a B))) ↔
      harea (hsolid A B C) = ENNReal.ofReal (π - (hangle B A C + hangle A B C + hangle A C B)) := by
  rw [harea_hsolid_motion ha hu hA hB hC, hangle_motion ha hu hB hA hC,
    hangle_motion ha hu hA hB hC, hangle_motion ha hu hA hC hB]

/-- **Area of an h-triangle equals its defect** (the h-plane has curvature `-1`): for a nondegenerate
h-triangle `ABC`, the hyperbolic area of the solid triangle is `π - (∠A + ∠B + ∠C)`. -/
@[kb "petrunin2025" "Section 20I, p. 176"]
theorem harea_hsolid_eq_defect {A B C : ℂ} (h : HTriangleNondeg A B C) :
    harea (hsolid A B C) = ENNReal.ofReal (π - (hangle B A C + hangle A B C + hangle A C B)) := by
  obtain ⟨hA, hB, hC, hBA, hCA, hnc⟩ := h
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have hB1 := norm_mobius_lt_one hA hB
  have hC1 := norm_mobius_lt_one hA hC
  have him : (conj (mobius A B) * mobius A C).im ≠ 0 := by
    intro h0'
    exact hnc _ (eq_real_mul_of_im_zero (mobius_ne_zero hA hB hBA) h0')
  obtain ⟨u, K, hu, hK, hB2, hC2, him2⟩ := exists_normalize hB1 him
  have T1 := defect_transfer (a := A) (u := 1) (A := A) (B := B) (C := C) hA (by simp) hA hB hC
  rw [← T1]
  have e0 : mobius A A = 0 := mobius_self hA
  simp only [one_mul, e0]
  have T2 := defect_transfer (a := 0) (u := u) (A := 0) (B := mobius A B) (C := mobius A C)
    h0 hu h0 hB1 hC1
  rw [← T2]
  simp only [mobius_zero_left, mul_zero]
  have hBn' : ‖u * mobius A B‖ < 1 := by rw [norm_mul, hu, one_mul]; exact hB1
  have hCn' : ‖u * mobius A C‖ < 1 := by rw [norm_mul, hu, one_mul]; exact hC1
  exact harea_hsolid_zero_defect hK hBn' hCn' hB2 hC2 him2

end Assembly

end UndergradKB.Geometry
