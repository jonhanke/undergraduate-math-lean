import UndergradKB.Common.Attr
import UndergradKB.Geometry.HypAngles
import UndergradKB.Geometry.HypLines

/-! # Inversions negate h-angles; the angle of parallelism in general position

Petrunin, *Euclidean Plane and its Relatives* (3rd ed.), Observation 12.7 (pp. 94-95) in full, and
the angle of parallelism of Chapter 13A (pp. 103-104) at an arbitrary point off an arbitrary h-line.
-/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

/-! ### Observation 12.7: inversions negate h-angles -/

section InvAngle

/-- The inversion `invF o` is the anti-Möbius map `z ↦ u * mobius (o⁻¹) (conj z)` of the disc. -/
theorem invF_eq_motion {o z : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) :
    invF o z = (-(o / conj o)) * mobius o⁻¹ (conj z) := by
  have ho0 : o ≠ 0 := by rintro rfl; norm_num at ho
  have hco : conj o ≠ 0 := by simpa using ho0
  have hd := den_ne ho hz
  have e : 1 - conj o⁻¹ * conj z = (conj o - conj z) / conj o := by
    rw [map_inv₀]; field_simp
  have hd' : conj o - conj z ≠ 0 := by
    intro h; apply hd; linear_combination -h
  unfold invF mobius
  rw [e]
  field_simp
  ring

theorem invF_motion_data {o : ℂ} (ho : 1 < ‖o‖) :
    ‖o⁻¹‖ < 1 ∧ ‖-(o / conj o)‖ = 1 := by
  have ho0 : o ≠ 0 := by rintro rfl; norm_num at ho
  refine ⟨?_, ?_⟩
  · rw [norm_inv]; exact inv_lt_one_of_one_lt₀ ho
  · rw [norm_neg, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ho0)]

/-- Observation 12.7 (h-angles): the inversion in a circle perpendicular to the absolute negates
the signed h-angle: `∡_h (ιP) (ιQ) (ιR) = -∡_h P Q R` for points of the disc. -/
theorem hoangle_invF {o P Q R : ℂ} (ho : 1 < ‖o‖) (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1)
    (hR : ‖R‖ < 1) :
    hoangle (invF o P) (invF o Q) (invF o R) = -hoangle P Q R := by
  obtain ⟨ha, hu⟩ := invF_motion_data ho
  rw [invF_eq_motion ho hP, invF_eq_motion ho hQ, invF_eq_motion ho hR,
    hoangle_motion ha hu (by simpa using hP) (by simpa using hQ) (by simpa using hR)]
  exact hoangle_conj P Q R

theorem hangle_invF {o P Q R : ℂ} (ho : 1 < ‖o‖) (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1)
    (hR : ‖R‖ < 1) :
    hangle (invF o P) (invF o Q) (invF o R) = hangle P Q R := by
  obtain ⟨ha, hu⟩ := invF_motion_data ho
  rw [invF_eq_motion ho hP, invF_eq_motion ho hQ, invF_eq_motion ho hR,
    hangle_motion ha hu (by simpa using hP) (by simpa using hQ) (by simpa using hR)]
  exact hangle_conj P Q R

theorem one_lt_norm_center (Γ : EuclideanGeometry.Sphere ℂ) (hΓ : 0 < Γ.radius)
    (hperp : OrthogonalCircles Γ (⟨0, 1⟩ : EuclideanGeometry.Sphere ℂ)) :
    1 < ‖Γ.center‖ ∧ ‖Γ.center‖ ^ 2 = 1 + Γ.radius ^ 2 := by
  rw [orthogonalCircles_iff hΓ.le one_pos (by simp)] at hperp
  simp only [dist_eq_norm, zero_sub, norm_neg] at hperp
  have h2 : ‖Γ.center‖ ^ 2 = 1 + Γ.radius ^ 2 := by simpa using hperp
  refine ⟨?_, h2⟩
  by_contra h
  push Not at h
  nlinarith [norm_nonneg Γ.center, sq_pos_of_pos hΓ]

/-- Observation 12.7, pp. 94-95: the inversion `ι` in a circle `Γ` perpendicular to the absolute
is a bijection of the h-plane (the open unit disc) which preserves h-distance, sends h-lines to
h-lines and h-segments to h-segments (`ι [PQ]_h = [ιP ιQ]_h`), and negates signed h-angles
(`∡_h (ιP)(ιQ)(ιR) = -∡_h P Q R`) while preserving the unsigned ones. -/
@[kb "petrunin2025" "Observation 12.7, p. 94"]
theorem inversion_hmotion_full (Γ : EuclideanGeometry.Sphere ℂ) (hΓ : 0 < Γ.radius)
    (hperp : OrthogonalCircles Γ (⟨0, 1⟩ : EuclideanGeometry.Sphere ℂ)) :
    let ι := EuclideanGeometry.inversion Γ.center Γ.radius
    ι '' {z : ℂ | ‖z‖ < 1} = {z : ℂ | ‖z‖ < 1} ∧
    (∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → hdist (ι z) (ι w) = hdist z w) ∧
    (∀ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 → ∃ (α' : ℝ) (c' : ℂ), α' ^ 2 < ‖c'‖ ^ 2 ∧
      ι '' hline α c = hline α' c') ∧
    (∀ P Q : ℂ, ‖P‖ < 1 → ‖Q‖ < 1 → ι '' hsegment P Q = hsegment (ι P) (ι Q)) ∧
    (∀ P Q R : ℂ, ‖P‖ < 1 → ‖Q‖ < 1 → ‖R‖ < 1 → hoangle (ι P) (ι Q) (ι R) = -hoangle P Q R) ∧
    (∀ P Q R : ℂ, ‖P‖ < 1 → ‖Q‖ < 1 → ‖R‖ < 1 → hangle (ι P) (ι Q) (ι R) = hangle P Q R) := by
  intro ι
  obtain ⟨ho, ho2⟩ := one_lt_norm_center Γ hΓ hperp
  obtain ⟨p1', p2, p3', p4⟩ := inversion_hmotion Γ hΓ hperp
  have p1 : ∀ z : ℂ, ‖z‖ < 1 → ‖ι z‖ < 1 := p1'
  have p3 : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → hdist (ι z) (ι w) = hdist z w := p3'
  have key : ∀ z : ℂ, ‖z‖ < 1 → ι z = invF Γ.center z :=
    fun z hz => inversion_eq_invF hΓ ho2 hz
  have inv : ∀ x, ι (ι x) = x := EuclideanGeometry.inversion_inversion _ hΓ.ne'
  refine ⟨p2, p3, p4, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw1 := ((mem_hsegment_iff hP hQ).mp hw).1
      have hz := p1 w hw1
      have h1 := (hdist_add_iff_mem_hsegment hP hw1 hQ).mpr hw
      rw [← hdist_add_iff_mem_hsegment (p1 P hP) hz (p1 Q hQ), p3 P w hP hw1,
        p3 w Q hw1 hQ, p3 P Q hP hQ]
      exact h1
    · intro hz
      have hz1 := ((mem_hsegment_iff (p1 P hP) (p1 Q hQ)).mp hz).1
      refine ⟨ι z, ?_, inv z⟩
      have hw1 := p1 z hz1
      have h1 := (hdist_add_iff_mem_hsegment (p1 P hP) hz1 (p1 Q hQ)).mpr hz
      rw [← hdist_add_iff_mem_hsegment hP hw1 hQ]
      have a1 : hdist P (ι z) = hdist (ι P) z := by
        have := p3 P (ι z) hP hw1; rw [inv] at this; exact this.symm
      have a2 : hdist (ι z) Q = hdist z (ι Q) := by
        have := p3 (ι z) Q hw1 hQ; rw [inv] at this; exact this.symm
      have a3 : hdist P Q = hdist (ι P) (ι Q) := (p3 P Q hP hQ).symm
      rw [a1, a2, a3]
      exact h1
  · intro P Q R hP hQ hR
    rw [key P hP, key Q hQ, key R hR]
    exact hoangle_invF ho hP hQ hR
  · intro P Q R hP hQ hR
    rw [key P hP, key Q hQ, key R hR]
    exact hangle_invF ho hP hQ hR

/-- The reflection of the h-plane in the diameter through `0` and `v` with `v² = w`, i.e.
`z ↦ w * conj z` with `‖w‖ = 1`, negates signed h-angles. -/
theorem hoangle_reflection {w P Q R : ℂ} (hw : ‖w‖ = 1) (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1)
    (hR : ‖R‖ < 1) :
    hoangle (w * conj P) (w * conj Q) (w * conj R) = -hoangle P Q R := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have := hoangle_motion h0 hw (P := conj P) (Q := conj Q) (R := conj R) (by simpa using hP)
    (by simpa using hQ) (by simpa using hR)
  simp only [mobius, sub_zero, map_zero, zero_mul, div_one] at this
  rw [this]
  exact hoangle_conj P Q R

end InvAngle

/-! ### The angle of parallelism in general position (Chapter 13A) -/

section Parallelism

theorem norm_le_of_hdist_zero_le {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (h : hdist 0 x ≤ hdist 0 y) : ‖x‖ ≤ ‖y‖ := by
  by_contra hc
  push Not at hc
  rw [hdist_zero_eq_log hx, hdist_zero_eq_log hy] at h
  have h1 : 0 < 1 - ‖x‖ := by linarith
  have h2 : 0 < 1 - ‖y‖ := by linarith
  have h3 : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have : (1 + ‖y‖) / (1 - ‖y‖) < (1 + ‖x‖) / (1 - ‖x‖) := by
    rw [div_lt_div_iff₀ h2 h1]; nlinarith
  have := Real.log_lt_log (div_pos h3 h2) this
  linarith

theorem exists_tanh_param {k : ℝ} (h0 : 0 < k) (h1 : k < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ k * (t ^ 2 + 1) = 2 * t := by
  have hq0 : 0 ≤ Real.sqrt (1 - k ^ 2) := Real.sqrt_nonneg _
  have hq : Real.sqrt (1 - k ^ 2) ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by nlinarith)
  set q := Real.sqrt (1 - k ^ 2) with hqdef
  have hq1 : q < 1 := by nlinarith
  have hq2 : 1 - k < q := by
    by_contra hc
    push Not at hc
    nlinarith
  refine ⟨(1 - q) / k, div_pos (by linarith) h0, ?_, ?_⟩
  · rw [div_lt_one h0]; linarith
  · field_simp
    nlinarith [hq]

/-- Auxiliary centred computation: for an h-line `ℓ = hline α c` not through the centre, a point `Q`
of `ℓ` nearest to the centre, and an ideal point `A` of `ℓ`, the (Euclidean = h) angle at the
centre between `Q` and `A` has cosine `tanh (hdist 0 Q)`. -/
theorem angle_parallelism_centred {α : ℝ} {c Q A : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hα : α ≠ 0)
    (hQ : Q ∈ hline α c) (hmin : ∀ X ∈ hline α c, hdist 0 Q ≤ hdist 0 X)
    (hA : A ∈ idealPts α c) :
    InnerProductGeometry.angle Q A = Real.arccos
      ((Real.exp (2 * hdist 0 Q) - 1) / (Real.exp (2 * hdist 0 Q) + 1)) := by
  have hcn : 0 < ‖c‖ := by
    have : 0 < ‖c‖ ^ 2 := by nlinarith [sq_nonneg α]
    exact lt_of_le_of_ne (norm_nonneg _) (fun e => by rw [← e] at this; simp at this)
  have hαa : 0 < |α| := abs_pos.mpr hα
  have hαc : |α| < ‖c‖ := (sq_lt_sq₀ (abs_nonneg α) (norm_nonneg c)).mp (by rwa [sq_abs])
  set k : ℝ := |α| / ‖c‖ with hkdef
  have hk0 : 0 < k := div_pos hαa hcn
  have hk1 : k < 1 := (div_lt_one hcn).mpr hαc
  obtain ⟨t, ht0, ht1, hkt⟩ := exists_tanh_param hk0 hk1
  have hkt' : |α| * (t ^ 2 + 1) = 2 * t * ‖c‖ := by
    rw [hkdef] at hkt; field_simp at hkt; linarith
  -- a point of `ℓ` at distance `t` from the centre
  set e : ℝ := α / |α| with hedef
  have he : |e| = 1 := by rw [hedef, abs_div, abs_abs, div_self hαa.ne']
  have heα : α = e * |α| := by rw [hedef]; field_simp
  set X0 : ℂ := ((e * t / ‖c‖ : ℝ) : ℂ) * c with hX0
  have hX0n : ‖X0‖ = t := by
    rw [hX0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, he,
      abs_of_pos ht0, abs_of_pos hcn]
    field_simp
  have hX0m : X0 ∈ hline α c := by
    refine ⟨by rw [hX0n]; exact ht1, ?_⟩
    have : conj c * X0 = ((e * t / ‖c‖ * ‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [hX0]
      have : conj c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast at this ⊢
      linear_combination ((e : ℂ) * t / ‖c‖) * this
    rw [this, Complex.ofReal_re, hX0n, heα]
    field_simp
    linear_combination e * hkt'
  have hQn1 : ‖Q‖ < 1 := hQ.1
  have hρt : ‖Q‖ ≤ t := by
    have := norm_le_of_hdist_zero_le hQn1 hX0m.1 (hmin X0 hX0m)
    rwa [hX0n] at this
  -- the inequality `|α| (ρ² + 1) ≤ 2 ‖c‖ ρ`
  have hineq : |α| * (‖Q‖ ^ 2 + 1) ≤ 2 * ‖c‖ * ‖Q‖ := by
    have h1 := hQ.2
    have h2 : |(conj c * Q).re| ≤ ‖c‖ * ‖Q‖ := by
      have := Complex.abs_re_le_norm (conj c * Q)
      rwa [norm_mul, Complex.norm_conj] at this
    have h3 : |α * (‖Q‖ ^ 2 + 1)| = |α| * (‖Q‖ ^ 2 + 1) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ‖Q‖ ^ 2 + 1)]
    rw [← h3, h1, abs_mul]
    simp only [abs_two]
    linarith
  have hρ : ‖Q‖ = t := by
    by_contra hne
    have hlt : ‖Q‖ < t := lt_of_le_of_ne hρt hne
    have hρ0 := norm_nonneg Q
    have a1 : |α| * (‖Q‖ ^ 2 + 1) * (t ^ 2 + 1) ≤ 2 * ‖c‖ * ‖Q‖ * (t ^ 2 + 1) :=
      mul_le_mul_of_nonneg_right hineq (by positivity)
    have a2 : |α| * (t ^ 2 + 1) * (‖Q‖ ^ 2 + 1) = 2 * t * ‖c‖ * (‖Q‖ ^ 2 + 1) := by
      rw [hkt']
    have a3 : 0 < (1 - t * ‖Q‖) * (t - ‖Q‖) := mul_pos (by nlinarith) (by linarith)
    nlinarith [mul_pos hcn a3]
  -- the real part of `c̄ Q`
  have hx : (conj c * Q).re = α * (t ^ 2 + 1) / 2 := by
    have := hQ.2; rw [hρ] at this; linarith
  have hnorm : ‖conj c * Q‖ ^ 2 = ‖c‖ ^ 2 * t ^ 2 := by
    rw [norm_mul, Complex.norm_conj, hρ]; ring
  have hx2 : (conj c * Q).re ^ 2 = ‖c‖ ^ 2 * t ^ 2 := by
    rw [hx]
    have : (α * (t ^ 2 + 1)) ^ 2 = (|α| * (t ^ 2 + 1)) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    calc (α * (t ^ 2 + 1) / 2) ^ 2 = (α * (t ^ 2 + 1)) ^ 2 / 4 := by ring
      _ = _ := by rw [this, hkt']; ring
  have hy : (conj c * Q).im = 0 := by
    have := hnorm
    rw [sq_norm_eq] at this
    have h0 : (conj c * Q).im ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  have hcQ : conj c * Q = (((conj c * Q).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hy])
  have hNc : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ‖c‖ ^ 2 ≠ 0)
  have hQeq : Q = (((conj c * Q).re : ℝ) : ℂ) * c / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    have hmc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [eq_div_iff hNc, ← hcQ, ← hmc]; ring
  -- the inner product with `A`
  have hAn : ‖A‖ = 1 := hA.1
  have hAre : (conj c * A).re = α := hA.2
  have hinner : (conj Q * A).re = k * t := by
    have : conj Q * A = ((((conj c * Q).re) / ‖c‖ ^ 2 : ℝ) : ℂ) * (conj c * A) := by
      conv_lhs => rw [hQeq]
      simp only [map_div₀, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [this, Complex.re_ofReal_mul, hAre, hx, hkdef]
    field_simp
    linear_combination |α| * hkt' - (t ^ 2 + 1) * sq_abs α
  have hcos : Real.arccos (k * t / (t * 1)) = Real.arccos k := by
    rw [mul_one, mul_div_assoc, div_self ht0.ne', mul_one]
  have hang : InnerProductGeometry.angle Q A = Real.arccos k := by
    unfold InnerProductGeometry.angle
    rw [← hcos, hρ, hAn]
    congr 2
    rw [real_inner_eq_re_inner ℂ Q A]
    have := hinner
    simp at this ⊢
    linarith
  rw [hang]
  congr 1
  -- `k = (e^{2s} - 1) / (e^{2s} + 1)` with `s = hdist 0 Q`
  have hs : Real.exp (hdist 0 Q) = (1 + t) / (1 - t) := by
    rw [hdist_zero_eq_log hQn1, Real.exp_log (div_pos (by rw [hρ]; linarith) (by rw [hρ]; linarith))]
    rw [hρ]
  have h2s : Real.exp (2 * hdist 0 Q) = ((1 + t) / (1 - t)) ^ 2 := by
    rw [two_mul, Real.exp_add, ← hs]; ring
  rw [h2s]
  have h1t : 1 - t ≠ 0 := by linarith
  have : k = 2 * t / (t ^ 2 + 1) := by
    field_simp; linarith
  rw [this]
  field_simp
  ring

theorem mobius_den_ne_unit {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) : 1 - conj a * w ≠ 0 := by
  intro h
  have h1 : conj a * w = 1 := by linear_combination -h
  have := congrArg norm h1
  rw [norm_mul, Complex.norm_conj, hw, mul_one, norm_one] at this
  linarith

theorem norm_mobius_unit {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) : ‖mobius a w‖ = 1 := by
  have hD := mobius_den_ne_unit ha hw
  have e : conj w * (w - a) = conj (1 - conj a * w) := by
    have : conj w * w = 1 := by
      rw [Complex.conj_mul', hw]; simp
    simp only [map_sub, map_mul, map_one, Complex.conj_conj]
    linear_combination this
  have h2 : ‖w - a‖ = ‖1 - conj a * w‖ := by
    have := congrArg norm e
    rwa [norm_mul, Complex.norm_conj, hw, one_mul, Complex.norm_conj] at this
  unfold mobius
  rw [norm_div, h2, div_self (norm_ne_zero_iff.mpr hD)]

theorem mobius_neg_mobius_unit {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) :
    mobius (-a) (mobius a w) = w := by
  have hD := mobius_den_ne_unit ha hw
  have h1 : (1 - conj a * a) ≠ 0 := by
    have hpos := one_sub_sq_pos ha
    intro h0
    have h3 : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [ofReal_one_sub_sq, mul_comm]; exact h0
    have := Complex.ofReal_eq_zero.mp h3
    linarith
  have hxD : (w - a) / (1 - conj a * w) * (1 - conj a * w) = w - a := div_mul_cancel₀ _ hD
  have e1 : (w - a) / (1 - conj a * w) - -a = w * (1 - conj a * a) / (1 - conj a * w) := by
    rw [eq_div_iff hD]; linear_combination hxD
  have e2 : 1 - conj (-a) * ((w - a) / (1 - conj a * w)) = (1 - conj a * a) / (1 - conj a * w) := by
    rw [eq_div_iff hD]; simp only [map_neg]; linear_combination (conj a) * hxD
  unfold mobius
  rw [e1, e2, div_div_div_cancel_right₀ hD, mul_div_assoc, div_self h1, mul_one]

theorem hE_mobius_of_den {α : ℝ} {c b w : ℂ} (hD : 1 - conj b * w ≠ 0) :
    hE α c (mobius b w) * ‖1 - conj b * w‖ ^ 2 = hE (mα b α c) (mc b α c) w := by
  set D := 1 - conj b * w with hDdef
  have hz : mobius b w * D = w - b := by unfold mobius; exact div_mul_cancel₀ _ hD
  rw [← mobius_hE_poly]
  have hn : ‖mobius b w‖ ^ 2 * ‖D‖ ^ 2 = ‖w - b‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, hz]
  have e : ((‖D‖ ^ 2 : ℝ) : ℂ) = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre : (conj c * mobius b w).re * ‖D‖ ^ 2 = (conj c * ((w - b) * conj D)).re := by
    have : conj c * ((w - b) * conj D) = (conj c * mobius b w) * ((‖D‖ ^ 2 : ℝ) : ℂ) := by
      rw [e, ← hz]; ring
    rw [this, Complex.re_mul_ofReal]
  unfold hE
  linear_combination α * hn - 2 * hre

/-- The angle of parallelism (Chapter 13A, p. 103, with Proposition 13.3, p. 104) at an arbitrary
h-point `P` off an arbitrary h-line `ℓ = hline α c`.  Let `Q ∈ ℓ` be a footpoint of `P` (a point of
`ℓ` nearest to `P` in h-distance; this is the foot of the h-perpendicular `(PQ)_h`), `s = PQ_h`,
and `A` either ideal point of `ℓ`.  The h-angle at `P` between the h-ray to `Q` and the h-ray to
`A` (the direction of the asymptotically parallel h-line `(PA)_h` through `P`) is
`arccos ((e^{2s} - 1)/(e^{2s} + 1))`, which depends only on `s`; this is `φ(s)` with
`cos φ = (e^{2s} - 1)/(e^{2s} + 1)`.  (Wave 2's `angle_of_parallelism_hangle` is the centred case;
that `φ` is the least angle of a non-crossing line and that a footpoint exists are not part of this
statement.) -/
@[kb "petrunin2025" "Definition (angle of parallelism), p. 103"]
theorem angle_of_parallelism_general {α : ℝ} {c P Q A : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) (hQ : Q ∈ hline α c) (hmin : ∀ X ∈ hline α c, hdist P Q ≤ hdist P X)
    (hA : A ∈ idealPts α c) :
    hangleIdeal P Q A = Real.arccos
      ((Real.exp (2 * hdist P Q) - 1) / (Real.exp (2 * hdist P Q) + 1)) := by
  have hn : ‖-P‖ < 1 := by simpa using hP
  have himg : mobius P '' hline α c = hline (mα (-P) α c) (mc (-P) α c) :=
    mobius_image_hline hP
  have hβ : mα (-P) α c ^ 2 < ‖mc (-P) α c‖ ^ 2 := mα_lt hn h
  have hβ0 : mα (-P) α c ≠ 0 := by
    intro h0
    apply hPl
    have h00 : (0 : ℂ) ∈ hline (mα (-P) α c) (mc (-P) α c) := ⟨by simp, by simp [h0]⟩
    have := (mobius_mem_hline_iff (α := α) (c := c) hn (w := 0) (by simp)).mpr h00
    rwa [mobius_neg_zero] at this
  have hdz : ∀ Y : ℂ, ‖Y‖ < 1 → hdist 0 (mobius P Y) = hdist P Y := by
    intro Y hY
    have := hdist_mobius hP hP hY
    rwa [mobius_self hP] at this
  have hQ' : mobius P Q ∈ hline (mα (-P) α c) (mc (-P) α c) := by
    rw [← himg]; exact ⟨Q, hQ, rfl⟩
  have hmin' : ∀ X' ∈ hline (mα (-P) α c) (mc (-P) α c), hdist 0 (mobius P Q) ≤ hdist 0 X' := by
    rw [← himg]
    rintro _ ⟨X, hX, rfl⟩
    rw [hdz Q hQ.1, hdz X hX.1]
    exact hmin X hX
  have hAn : ‖A‖ = 1 := hA.1
  have hA'n : ‖mobius P A‖ = 1 := norm_mobius_unit hP hAn
  have hA' : mobius P A ∈ idealPts (mα (-P) α c) (mc (-P) α c) := by
    refine ⟨hA'n, ?_⟩
    have hD := mobius_den_ne_unit hn hA'n
    have key := hE_mobius_of_den (α := α) (c := c) hD
    rw [mobius_neg_mobius_unit (by simpa using hn) hAn] at key
    have h0 : hE α c A = 0 := by
      unfold hE; rw [hAn, hA.2]; ring
    rw [h0, zero_mul] at key
    unfold hE at key
    rw [hA'n] at key
    linarith
  have := angle_parallelism_centred hβ hβ0 hQ' hmin' hA'
  unfold hangleIdeal
  rw [hdz Q hQ.1] at this
  simpa [mobius] using this


/-! ### Existence of the footpoint and the least angle -/

theorem centred_setup {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hα : α ≠ 0) :
    ∃ (k t : ℝ) (X0 : ℂ), 0 < k ∧ k < 1 ∧ k = |α| / ‖c‖ ∧ 0 < t ∧ t < 1 ∧
      k * (t ^ 2 + 1) = 2 * t ∧ |α| * (t ^ 2 + 1) = 2 * t * ‖c‖ ∧ X0 ∈ hline α c ∧ ‖X0‖ = t ∧
      ∀ X ∈ hline α c, t ≤ ‖X‖ := by
  have hcn : 0 < ‖c‖ := by
    have : 0 < ‖c‖ ^ 2 := by nlinarith [sq_nonneg α]
    exact lt_of_le_of_ne (norm_nonneg _) (fun e => by rw [← e] at this; simp at this)
  have hαa : 0 < |α| := abs_pos.mpr hα
  have hαc : |α| < ‖c‖ := (sq_lt_sq₀ (abs_nonneg α) (norm_nonneg c)).mp (by rwa [sq_abs])
  have hk0 : 0 < |α| / ‖c‖ := div_pos hαa hcn
  have hk1 : |α| / ‖c‖ < 1 := (div_lt_one hcn).mpr hαc
  obtain ⟨t, ht0, ht1, hkt⟩ := exists_tanh_param hk0 hk1
  have hkt' : |α| * (t ^ 2 + 1) = 2 * t * ‖c‖ := by
    field_simp at hkt; linarith
  set e : ℝ := α / |α| with hedef
  have he : |e| = 1 := by rw [hedef, abs_div, abs_abs, div_self hαa.ne']
  have heα : α = e * |α| := by rw [hedef]; field_simp
  set X0 : ℂ := ((e * t / ‖c‖ : ℝ) : ℂ) * c with hX0
  have hX0n : ‖X0‖ = t := by
    rw [hX0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, he,
      abs_of_pos ht0, abs_of_pos hcn]
    field_simp
  have hX0m : X0 ∈ hline α c := by
    refine ⟨by rw [hX0n]; exact ht1, ?_⟩
    have : conj c * X0 = ((e * t / ‖c‖ * ‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [hX0]
      have : conj c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast at this ⊢
      linear_combination ((e : ℂ) * t / ‖c‖) * this
    rw [this, Complex.ofReal_re, hX0n, heα]
    field_simp
    linear_combination e * hkt'
  refine ⟨|α| / ‖c‖, t, X0, hk0, hk1, rfl, ht0, ht1, hkt, hkt', hX0m, hX0n, ?_⟩
  intro X hX
  by_contra hlt
  push Not at hlt
  have hρ0 := norm_nonneg X
  have hineq : |α| * (‖X‖ ^ 2 + 1) ≤ 2 * ‖c‖ * ‖X‖ := by
    have h1 := hX.2
    have h2 : |(conj c * X).re| ≤ ‖c‖ * ‖X‖ := by
      have := Complex.abs_re_le_norm (conj c * X)
      rwa [norm_mul, Complex.norm_conj] at this
    have h3 : |α * (‖X‖ ^ 2 + 1)| = |α| * (‖X‖ ^ 2 + 1) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ‖X‖ ^ 2 + 1)]
    rw [← h3, h1, abs_mul]
    simp only [abs_two]
    linarith
  have a1 : |α| * (‖X‖ ^ 2 + 1) * (t ^ 2 + 1) ≤ 2 * ‖c‖ * ‖X‖ * (t ^ 2 + 1) :=
    mul_le_mul_of_nonneg_right hineq (by positivity)
  have a2 : |α| * (t ^ 2 + 1) * (‖X‖ ^ 2 + 1) = 2 * t * ‖c‖ * (‖X‖ ^ 2 + 1) := by
    rw [hkt']
  have a3 : 0 < (1 - t * ‖X‖) * (t - ‖X‖) := mul_pos (by nlinarith) (by linarith)
  nlinarith [mul_pos hcn a3]

/-- Data of a nearest point `Q` to the centre on an h-line `hline α c` missing the centre. -/
theorem centred_data {α : ℝ} {c Q : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hα : α ≠ 0)
    (hQ : Q ∈ hline α c) (hmin : ∀ X ∈ hline α c, hdist 0 Q ≤ hdist 0 X) :
    ∃ k t : ℝ, 0 < k ∧ k < 1 ∧ 0 < t ∧ t < 1 ∧ k * (t ^ 2 + 1) = 2 * t ∧ ‖Q‖ = t ∧
      (∀ w : ℂ, α * (conj Q * w).re = k * t * (conj c * w).re) ∧
      k = (Real.exp (2 * hdist 0 Q) - 1) / (Real.exp (2 * hdist 0 Q) + 1) := by
  obtain ⟨k, t, X0, hk0, hk1, hkdef, ht0, ht1, hkt, hkt', hX0m, hX0n, hlow⟩ :=
    centred_setup h hα
  have hcn : 0 < ‖c‖ := by
    have : 0 < ‖c‖ ^ 2 := by nlinarith [sq_nonneg α]
    exact lt_of_le_of_ne (norm_nonneg _) (fun e => by rw [← e] at this; simp at this)
  have hQn1 : ‖Q‖ < 1 := hQ.1
  have hρ : ‖Q‖ = t := by
    have h1 := norm_le_of_hdist_zero_le hQn1 hX0m.1 (hmin X0 hX0m)
    rw [hX0n] at h1
    exact le_antisymm h1 (hlow Q hQ)
  have hx : (conj c * Q).re = α * (t ^ 2 + 1) / 2 := by
    have := hQ.2; rw [hρ] at this; linarith
  have hnorm : ‖conj c * Q‖ ^ 2 = ‖c‖ ^ 2 * t ^ 2 := by
    rw [norm_mul, Complex.norm_conj, hρ]; ring
  have hx2 : (conj c * Q).re ^ 2 = ‖c‖ ^ 2 * t ^ 2 := by
    rw [hx]
    have : (α * (t ^ 2 + 1)) ^ 2 = (|α| * (t ^ 2 + 1)) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    calc (α * (t ^ 2 + 1) / 2) ^ 2 = (α * (t ^ 2 + 1)) ^ 2 / 4 := by ring
      _ = _ := by rw [this, hkt']; ring
  have hy : (conj c * Q).im = 0 := by
    have := hnorm
    rw [sq_norm_eq] at this
    have h0 : (conj c * Q).im ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  have hcQ : conj c * Q = (((conj c * Q).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hy])
  have hNc : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : ‖c‖ ^ 2 ≠ 0)
  have hQeq : Q = (((conj c * Q).re : ℝ) : ℂ) * c / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    have hmc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [eq_div_iff hNc, ← hcQ, ← hmc]; ring
  refine ⟨k, t, hk0, hk1, ht0, ht1, hkt, hρ, ?_, ?_⟩
  · intro w
    have : conj Q * w = ((((conj c * Q).re) / ‖c‖ ^ 2 : ℝ) : ℂ) * (conj c * w) := by
      conv_lhs => rw [hQeq]
      simp only [map_div₀, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [this, Complex.re_ofReal_mul, hx, hkdef]
    field_simp
    linear_combination (conj c * w).re * (|α| * hkt' - (t ^ 2 + 1) * sq_abs α)
  · have hs : Real.exp (hdist 0 Q) = (1 + t) / (1 - t) := by
      rw [hdist_zero_eq_log hQn1,
        Real.exp_log (div_pos (by rw [hρ]; linarith) (by rw [hρ]; linarith))]
      rw [hρ]
    have h2s : Real.exp (2 * hdist 0 Q) = ((1 + t) / (1 - t)) ^ 2 := by
      rw [two_mul, Real.exp_add, ← hs]; ring
    rw [h2s]
    have h1t : 1 - t ≠ 0 := by linarith
    have : k = 2 * t / (t ^ 2 + 1) := by
      field_simp; linarith
    rw [this]
    field_simp
    ring

/-- Transport of an h-line missing `P` to an h-line missing the centre. -/
theorem hmotion_transport_line {α : ℝ} {c P : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) :
    ∃ (β : ℝ) (d : ℂ), β ^ 2 < ‖d‖ ^ 2 ∧ β ≠ 0 ∧ mobius P '' hline α c = hline β d := by
  have hn : ‖-P‖ < 1 := by simpa using hP
  refine ⟨mα (-P) α c, mc (-P) α c, mα_lt hn h, ?_, mobius_image_hline hP⟩
  intro h0
  apply hPl
  have h00 : (0 : ℂ) ∈ hline (mα (-P) α c) (mc (-P) α c) := ⟨by simp, by simp [h0]⟩
  have := (mobius_mem_hline_iff (α := α) (c := c) hn (w := 0) (by simp)).mpr h00
  rwa [mobius_neg_zero] at this

theorem hdist_zero_mobius {P Y : ℂ} (hP : ‖P‖ < 1) (hY : ‖Y‖ < 1) :
    hdist 0 (mobius P Y) = hdist P Y := by
  have := hdist_mobius hP hP hY
  rwa [mobius_self hP] at this

/-- Existence of the footpoint: for `P` off the h-line `ℓ` there is a point `Q ∈ ℓ` nearest to `P`
in h-distance (Chapter 13A, p. 103: the foot of the perpendicular from `P` to `ℓ`). -/
@[kb "petrunin2025" "Definition (angle of parallelism), p. 103"]
theorem exists_footpoint {α : ℝ} {c P : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) :
    ∃ Q ∈ hline α c, ∀ X ∈ hline α c, hdist P Q ≤ hdist P X := by
  obtain ⟨β, d, hβ, hβ0, himg⟩ := hmotion_transport_line h hP hPl
  obtain ⟨k, t, X0, hk0, hk1, -, ht0, ht1, -, -, hX0m, hX0n, hlow⟩ := centred_setup hβ hβ0
  have hQ' : X0 ∈ mobius P '' hline α c := by rw [himg]; exact hX0m
  obtain ⟨Q, hQ, rfl⟩ := hQ'
  refine ⟨Q, hQ, fun X hX => ?_⟩
  rw [← hdist_zero_mobius hP hQ.1, ← hdist_zero_mobius hP hX.1]
  have hXm : mobius P X ∈ hline β d := by rw [← himg]; exact ⟨X, hX, rfl⟩
  exact hdist_zero_mono (hX0m.1) hXm.1 (by rw [hX0n]; exact hlow _ hXm)


theorem real_ray_iff {k κ : ℝ} (hk : 0 < k) (hk1 : k < 1) :
    (∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ k * (r ^ 2 + 1) = 2 * r * κ) ↔ k < κ := by
  constructor
  · rintro ⟨r, hr0, hr1, he⟩
    have hr : 0 < r := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · rw [← h] at he; nlinarith
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hk (sq_pos_of_pos (sub_pos.mpr hr1)), mul_le_mul_of_nonneg_left hc hr.le]
  · intro hκ
    have hκ0 : 0 < κ := by linarith
    have hw0 : 0 ≤ Real.sqrt (κ ^ 2 - k ^ 2) := Real.sqrt_nonneg _
    have hw : Real.sqrt (κ ^ 2 - k ^ 2) ^ 2 = κ ^ 2 - k ^ 2 :=
      Real.sq_sqrt (by nlinarith)
    set w := Real.sqrt (κ ^ 2 - k ^ 2)
    have hwκ : w < κ := by nlinarith
    have hwk : κ - k < w := by
      by_contra hc
      push Not at hc
      nlinarith
    refine ⟨(κ - w) / k, div_nonneg (by linarith) hk.le, ?_, ?_⟩
    · rw [div_lt_one hk]; linarith
    · field_simp
      nlinarith [hw]

theorem exists_dir {w : ℂ} (hw : w ≠ 0) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) :
    ∃ v : ℂ, v ≠ 0 ∧ InnerProductGeometry.angle w v = θ := by
  set z : ℂ := Complex.cos ((-θ : ℝ) : ℂ) + Complex.sin ((-θ : ℝ) : ℂ) * Complex.I with hz
  have hzn : ‖z‖ = 1 := Complex.norm_cos_add_sin_mul_I _
  have hz0 : z ≠ 0 := by intro e; rw [e] at hzn; simp at hzn
  have hv : w / z ≠ 0 := div_ne_zero hw hz0
  refine ⟨w / z, hv, ?_⟩
  have hdd : w / (w / z) = z := by field_simp
  rw [Complex.angle_eq_abs_arg hw hv, hdd,
    Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith [Real.pi_pos]⟩]
  rw [abs_neg, abs_of_nonneg h0]

/-- The centred ray criterion: the ray from the centre in the direction `v` meets `ℓ` iff the
angle between `Q` and `v` is below `arccos k`. -/
theorem ray_meets_centred {α : ℝ} {c Q v : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hα : α ≠ 0)
    (hQ : Q ∈ hline α c) (hmin : ∀ X ∈ hline α c, hdist 0 Q ≤ hdist 0 X) (hv : v ≠ 0) :
    (∃ s : ℝ, 0 ≤ s ∧ (s : ℂ) * v ∈ hline α c) ↔
      InnerProductGeometry.angle Q v < Real.arccos
        ((Real.exp (2 * hdist 0 Q) - 1) / (Real.exp (2 * hdist 0 Q) + 1)) := by
  obtain ⟨k, t, hk0, hk1, ht0, ht1, hkt, hρ, hstr, hkexp⟩ := centred_data h hα hQ hmin
  rw [← hkexp]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hQ0 : Q ≠ 0 := by intro e; rw [e] at hρ; simp at hρ; linarith
  set κ := Real.cos (InnerProductGeometry.angle Q v) with hκ
  have hκd : κ * (t * ‖v‖) = (conj Q * v).re := by
    rw [hκ, InnerProductGeometry.cos_angle, hρ, div_mul_cancel₀ _ (by positivity)]
    simp [Complex.inner]; ring
  have hRe : (conj c * v).re * (k * t) = α * κ * (t * ‖v‖) := by
    rw [mul_assoc α κ, hκd, mul_comm _ (k * t), ← hstr v]
  have hRe' : (conj c * v).re * k = α * κ * ‖v‖ := by
    have : (conj c * v).re * k * t = α * κ * ‖v‖ * t := by linear_combination hRe
    exact mul_right_cancel₀ ht0.ne' this
  -- angle comparison
  have hφ : InnerProductGeometry.angle Q v < Real.arccos k ↔ k < κ := by
    have hA0 := InnerProductGeometry.angle_nonneg Q v
    have hA1 := InnerProductGeometry.angle_le_pi Q v
    have hB0 := Real.arccos_nonneg k
    have hB1 := Real.arccos_le_pi k
    have := Real.strictAntiOn_cos.lt_iff_gt (a := Real.arccos k)
      (b := InnerProductGeometry.angle Q v) ⟨hB0, hB1⟩ ⟨hA0, hA1⟩
    rw [Real.cos_arccos (by linarith) hk1.le] at this
    rw [← hκ] at this
    exact this.symm
  rw [hφ, ← real_ray_iff hk0 hk1]
  have hmem : ∀ s : ℝ, 0 ≤ s → ((s : ℂ) * v ∈ hline α c ↔
      (s * ‖v‖ < 1 ∧ k * ((s * ‖v‖) ^ 2 + 1) = 2 * (s * ‖v‖) * κ)) := by
    intro s hs
    have hn : ‖(s : ℂ) * v‖ = s * ‖v‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    have hre : (conj c * ((s : ℂ) * v)).re = s * (conj c * v).re := by
      rw [mul_left_comm, Complex.re_ofReal_mul]
    show (‖(s : ℂ) * v‖ < 1 ∧ α * (‖(s : ℂ) * v‖ ^ 2 + 1) = 2 * (conj c * ((s : ℂ) * v)).re) ↔ _
    rw [hn, hre]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro he
      have : α * (k * ((s * ‖v‖) ^ 2 + 1)) = α * (2 * (s * ‖v‖) * κ) := by
        have h3 : α * ((s * ‖v‖) ^ 2 + 1) * k = 2 * s * ((conj c * v).re * k) := by
          linear_combination k * he
        rw [hRe'] at h3
        linear_combination h3
      exact mul_left_cancel₀ hα this
    · intro he
      have h4 : α * (k * ((s * ‖v‖) ^ 2 + 1)) = α * (2 * (s * ‖v‖) * κ) := by rw [he]
      have h3 : (α * ((s * ‖v‖) ^ 2 + 1) - 2 * (s * (conj c * v).re)) * k = 0 := by
        linear_combination h4 - 2 * s * hRe'
      exact (mul_eq_zero.mp h3).resolve_right hk0.ne' |> fun x => by linarith
  constructor
  · rintro ⟨s, hs, hm⟩
    obtain ⟨h1, h2⟩ := (hmem s hs).mp hm
    exact ⟨s * ‖v‖, by positivity, h1, h2⟩
  · rintro ⟨r, hr0, hr1, he⟩
    refine ⟨r / ‖v‖, by positivity, (hmem _ (by positivity)).mpr ?_⟩
    rw [div_mul_cancel₀ _ hvn.ne']
    exact ⟨hr1, he⟩


theorem foot_transport {α : ℝ} {c P Q : ℂ} {β : ℝ} {d : ℂ} (hP : ‖P‖ < 1)
    (himg : mobius P '' hline α c = hline β d) (hQ : Q ∈ hline α c)
    (hmin : ∀ X ∈ hline α c, hdist P Q ≤ hdist P X) :
    mobius P Q ∈ hline β d ∧ ∀ X' ∈ hline β d, hdist 0 (mobius P Q) ≤ hdist 0 X' := by
  refine ⟨by rw [← himg]; exact ⟨Q, hQ, rfl⟩, ?_⟩
  rw [← himg]
  rintro _ ⟨X, hX, rfl⟩
  rw [hdist_zero_mobius hP hQ.1, hdist_zero_mobius hP hX.1]
  exact hmin X hX

/-- Chapter 13A, p. 103: the h-ray from `P` in the direction of the tangent vector `v` (the points
`Z` with `mobius P Z = s v`, `s ≥ 0`) meets the h-line `ℓ` iff the unsigned h-angle between
`[PQ)_h` and the ray is less than the angle of parallelism `φ = arccos ((e^{2s} - 1)/(e^{2s} + 1))`,
`s = PQ_h`, where `Q` is the footpoint. -/
@[kb "petrunin2025" "Definition (angle of parallelism), p. 103"]
theorem parallelism_ray_meets {α : ℝ} {c P Q v : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) (hQ : Q ∈ hline α c) (hmin : ∀ X ∈ hline α c, hdist P Q ≤ hdist P X)
    (hv : v ≠ 0) :
    (∃ s : ℝ, 0 ≤ s ∧ ∃ Z ∈ hline α c, mobius P Z = (s : ℂ) * v) ↔
      InnerProductGeometry.angle (mobius P Q) v < Real.arccos
        ((Real.exp (2 * hdist P Q) - 1) / (Real.exp (2 * hdist P Q) + 1)) := by
  obtain ⟨β, d, hβ, hβ0, himg⟩ := hmotion_transport_line h hP hPl
  obtain ⟨hQ', hmin'⟩ := foot_transport hP himg hQ hmin
  have := ray_meets_centred hβ hβ0 hQ' hmin' hv
  rw [hdist_zero_mobius hP hQ.1] at this
  rw [← this]
  simp only [← himg, Set.mem_image]

/-- The full h-line through `P` in the direction `v` meets `ℓ` iff the angle `θ` between `[PQ)_h`
and the ray satisfies `θ < φ` or `π - θ < φ` (the opposite ray makes the angle `π - θ`). -/
theorem parallelism_line_meets {α : ℝ} {c P Q v : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) (hQ : Q ∈ hline α c) (hmin : ∀ X ∈ hline α c, hdist P Q ≤ hdist P X)
    (hv : v ≠ 0) :
    (∃ s : ℝ, ∃ Z ∈ hline α c, mobius P Z = (s : ℂ) * v) ↔
      (InnerProductGeometry.angle (mobius P Q) v < Real.arccos
        ((Real.exp (2 * hdist P Q) - 1) / (Real.exp (2 * hdist P Q) + 1)) ∨
      π - InnerProductGeometry.angle (mobius P Q) v < Real.arccos
        ((Real.exp (2 * hdist P Q) - 1) / (Real.exp (2 * hdist P Q) + 1))) := by
  rw [← parallelism_ray_meets h hP hPl hQ hmin hv, ← InnerProductGeometry.angle_neg_right,
    ← parallelism_ray_meets h hP hPl hQ hmin (neg_ne_zero.mpr hv)]
  constructor
  · rintro ⟨s, Z, hZ, e⟩
    rcases le_or_gt 0 s with hs | hs
    · exact Or.inl ⟨s, hs, Z, hZ, e⟩
    · refine Or.inr ⟨-s, by linarith, Z, hZ, ?_⟩
      rw [e]; push_cast; ring
  · rintro (⟨s, -, Z, hZ, e⟩ | ⟨s, -, Z, hZ, e⟩)
    · exact ⟨s, Z, hZ, e⟩
    · exact ⟨-s, Z, hZ, by rw [e]; push_cast; ring⟩

/-- Chapter 13A, p. 103: the angle of parallelism is the least angle of a non-crossing line.
For `P` off `ℓ` with footpoint `Q`, `φ = arccos ((e^{2s} - 1)/(e^{2s} + 1))` (`s = PQ_h`) is the
infimum of the angles `θ ∈ [0, π/2]` such that the h-line through `P` in a direction making the
unsigned h-angle `θ` with `[PQ)_h` misses `ℓ` (indeed that set is exactly `[φ, π/2]`). -/
@[kb "petrunin2025" "Definition (angle of parallelism), p. 103"]
theorem angle_of_parallelism_eq_sInf {α : ℝ} {c P Q : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) (hQ : Q ∈ hline α c) (hmin : ∀ X ∈ hline α c, hdist P Q ≤ hdist P X) :
    let φ := Real.arccos ((Real.exp (2 * hdist P Q) - 1) / (Real.exp (2 * hdist P Q) + 1))
    {θ : ℝ | 0 ≤ θ ∧ θ ≤ π / 2 ∧ ∃ v : ℂ, v ≠ 0 ∧ InnerProductGeometry.angle (mobius P Q) v = θ ∧
        ¬ ∃ s : ℝ, ∃ Z ∈ hline α c, mobius P Z = (s : ℂ) * v} = Set.Icc φ (π / 2) ∧
      sInf {θ : ℝ | 0 ≤ θ ∧ θ ≤ π / 2 ∧ ∃ v : ℂ, v ≠ 0 ∧
        InnerProductGeometry.angle (mobius P Q) v = θ ∧
        ¬ ∃ s : ℝ, ∃ Z ∈ hline α c, mobius P Z = (s : ℂ) * v} = φ := by
  intro φ
  -- `mobius P Q ≠ 0`
  have hQP : Q ≠ P := by rintro rfl; exact hPl hQ
  have hQ0 : mobius P Q ≠ 0 := mobius_ne_zero hP hQ.1 hQP
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg _
  have hφ1 : φ ≤ π / 2 := by
    refine Real.arccos_le_pi_div_two.mpr ?_
    -- the cosine is nonnegative: it is `2t/(t²+1)`
    obtain ⟨β, d, hβ, hβ0, himg⟩ := hmotion_transport_line h hP hPl
    obtain ⟨hQ', hmin'⟩ := foot_transport hP himg hQ hmin
    obtain ⟨k, t, hk0, -, -, -, -, -, -, hkexp⟩ := centred_data hβ hβ0 hQ' hmin'
    rw [hdist_zero_mobius hP hQ.1] at hkexp
    rw [← hkexp]; exact hk0.le
  have hset : {θ : ℝ | 0 ≤ θ ∧ θ ≤ π / 2 ∧ ∃ v : ℂ, v ≠ 0 ∧
      InnerProductGeometry.angle (mobius P Q) v = θ ∧
      ¬ ∃ s : ℝ, ∃ Z ∈ hline α c, mobius P Z = (s : ℂ) * v} = Set.Icc φ (π / 2) := by
    ext θ
    constructor
    · rintro ⟨h0, h1, v, hv, hang, hmiss⟩
      rw [parallelism_line_meets h hP hPl hQ hmin hv, hang] at hmiss
      push Not at hmiss
      exact ⟨hmiss.1, h1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨hφ0.trans h0, h1, ?_⟩
      obtain ⟨v, hv, hang⟩ := exists_dir hQ0 (hφ0.trans h0) (by linarith [Real.pi_pos])
      refine ⟨v, hv, hang, ?_⟩
      rw [parallelism_line_meets h hP hPl hQ hmin hv, hang]
      push Not
      exact ⟨h0, by linarith⟩
  exact ⟨hset, by rw [hset]; exact csInf_Icc hφ1⟩

end Parallelism

end UndergradKB.Geometry
