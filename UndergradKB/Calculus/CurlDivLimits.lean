import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr

open Real MeasureTheory intervalIntegral Filter Topology

namespace UndergradKB.Calculus

/-- A linear functional applied to a point of a circle of radius `ε`. -/
lemma curlDivLim_lin_circle (L : ℝ × ℝ →L[ℝ] ℝ) (ε t : ℝ) :
    L (ε • (cos t, sin t)) = ε * (cos t * L (1, 0) + sin t * L (0, 1)) := by
  have h : ε • (cos t, sin t) = (ε * cos t) • ((1 : ℝ), (0 : ℝ)) + (ε * sin t) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The integral of the linearized circulation integrand over a full circle. -/
lemma curlDivLim_main (p q a b c d ε : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, ((p + ε * (cos t * a + sin t * b)) * (-ε * sin t) +
        (q + ε * (cos t * c + sin t * d)) * (ε * cos t)) = π * ε ^ 2 * (c - b) := by
  let F : ℝ → ℝ := fun t => ε * p * cos t + ε * q * sin t - ε ^ 2 * a * (sin t) ^ 2 / 2
    + ε ^ 2 * d * (sin t) ^ 2 / 2 - ε ^ 2 * b * (t - sin t * cos t) / 2
    + ε ^ 2 * c * (t + sin t * cos t) / 2
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt F ((p + ε * (cos x * a + sin x * b)) * (-ε * sin x) +
        (q + ε * (cos x * c + sin x * d)) * (ε * cos x)) x := by
    intro x _
    have h1 := hasDerivAt_sin x
    have h2 := hasDerivAt_cos x
    have h3 := hasDerivAt_id x
    have h4 := ((h2.const_mul (ε * p)).add (h1.const_mul (ε * q))).sub
      (((h1.pow 2).const_mul (ε ^ 2 * a)).div_const 2)
    have h5 := h4.add (((h1.pow 2).const_mul (ε ^ 2 * d)).div_const 2)
    have h6 := h5.sub ((((h3.sub (h1.mul h2))).const_mul (ε ^ 2 * b)).div_const 2)
    have h7 := h6.add ((((h3.add (h1.mul h2))).const_mul (ε ^ 2 * c)).div_const 2)
    refine h7.congr_deriv ?_
    have e1 := sin_sq_add_cos_sq x
    have e2 : (cos x) ^ 2 = 1 - (sin x) ^ 2 := by linarith
    simp only [Nat.cast_ofNat]
    ring_nf
    rw [e2]
    ring_nf
  rw [integral_eq_sub_of_hasDerivAt hF (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [F, sin_two_pi, cos_two_pi, sin_zero, cos_zero]
  ring

/-- OpenStax Calculus 3:§6.7 Fact (curl as circulation per unit area) (CA-660), plane form:
for continuous `P Q : ℝ × ℝ → ℝ` differentiable at `c`, the circulation of `(P, Q)` around the circle
of radius `ε` about `c`, divided by the enclosed area `π ε²`, tends to `Q_x - P_y` at `c`
as `ε → 0⁺`. -/
@[kb "openstaxcalculus2016" "3:§6.7 Fact (curl as circulation per unit area), p. 721"]
theorem circulation_per_area_tendsto (P Q : ℝ × ℝ → ℝ) (hPc : Continuous P) (hQc : Continuous Q)
    (c : ℝ × ℝ) (hP : DifferentiableAt ℝ P c) (hQ : DifferentiableAt ℝ Q c) :
    Tendsto (fun ε : ℝ => (∫ t in (0 : ℝ)..2 * π,
        (P (c + ε • (cos t, sin t)) * (-ε * sin t) + Q (c + ε • (cos t, sin t)) * (ε * cos t)))
        / (π * ε ^ 2)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ Q c (1, 0) - fderiv ℝ P c (0, 1))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  have hη : 0 < e / 8 := by positivity
  have hP' := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hP.hasFDerivAt).def hη
  have hQ' := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hQ.hasFDerivAt).def hη
  obtain ⟨δP, hδP, hP2⟩ := Metric.eventually_nhds_iff.1 hP'
  obtain ⟨δQ, hδQ, hQ2⟩ := Metric.eventually_nhds_iff.1 hQ'
  refine ⟨min δP δQ, lt_min hδP hδQ, ?_⟩
  intro ε hε hdist
  have hεpos : 0 < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hεpos] at hdist
  have hεP : ε < δP := lt_of_lt_of_le hdist (min_le_left _ _)
  have hεQ : ε < δQ := lt_of_lt_of_le hdist (min_le_right _ _)
  set LP := fderiv ℝ P c
  set LQ := fderiv ℝ Q c
  have hnorm : ∀ t : ℝ, ‖ε • ((cos t, sin t) : ℝ × ℝ)‖ ≤ ε := by
    intro t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, Prod.norm_def]
    have : max ‖cos t‖ ‖sin t‖ ≤ 1 := max_le (by simpa using abs_cos_le_one t) (by simpa using abs_sin_le_one t)
    nlinarith
  have hbd : ∀ t : ℝ, ‖(P (c + ε • (cos t, sin t)) * (-ε * sin t) + Q (c + ε • (cos t, sin t)) * (ε * cos t))
      - ((P c + ε * (cos t * LP (1, 0) + sin t * LP (0, 1))) * (-ε * sin t) +
        (Q c + ε * (cos t * LQ (1, 0) + sin t * LQ (0, 1))) * (ε * cos t))‖ ≤ 2 * (e / 8 * ε) * ε := by
    intro t
    have hn := hnorm t
    have a1 := hP2 (y := ε • ((cos t, sin t) : ℝ × ℝ)) (by
      rw [dist_zero_right]; exact lt_of_le_of_lt hn hεP)
    have a2 := hQ2 (y := ε • ((cos t, sin t) : ℝ × ℝ)) (by
      rw [dist_zero_right]; exact lt_of_le_of_lt hn hεQ)
    rw [curlDivLim_lin_circle] at a1 a2
    have b1 : ‖P (c + ε • (cos t, sin t)) - P c - ε * (cos t * LP (1, 0) + sin t * LP (0, 1))‖
        ≤ e / 8 * ε := by
      refine a1.trans ?_
      exact mul_le_mul_of_nonneg_left hn hη.le
    have b2 : ‖Q (c + ε • (cos t, sin t)) - Q c - ε * (cos t * LQ (1, 0) + sin t * LQ (0, 1))‖
        ≤ e / 8 * ε := by
      refine a2.trans ?_
      exact mul_le_mul_of_nonneg_left hn hη.le
    have c1 : ‖-ε * sin t‖ ≤ ε := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_pos hεpos]
      nlinarith [abs_sin_le_one t]
    have c2 : ‖ε * cos t‖ ≤ ε := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hεpos]
      nlinarith [abs_cos_le_one t]
    have key : (P (c + ε • (cos t, sin t)) * (-ε * sin t) + Q (c + ε • (cos t, sin t)) * (ε * cos t))
      - ((P c + ε * (cos t * LP (1, 0) + sin t * LP (0, 1))) * (-ε * sin t) +
        (Q c + ε * (cos t * LQ (1, 0) + sin t * LQ (0, 1))) * (ε * cos t))
      = (P (c + ε • (cos t, sin t)) - P c - ε * (cos t * LP (1, 0) + sin t * LP (0, 1))) * (-ε * sin t)
        + (Q (c + ε • (cos t, sin t)) - Q c - ε * (cos t * LQ (1, 0) + sin t * LQ (0, 1))) * (ε * cos t) := by
      ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul _ (-ε * sin t), norm_mul _ (ε * cos t)]
    have d1 := mul_le_mul b1 c1 (norm_nonneg _) (by positivity)
    have d2 := mul_le_mul b2 c2 (norm_nonneg _) (by positivity)
    linarith
  have hcont : ∀ f : ℝ × ℝ → ℝ, Continuous f →
      Continuous (fun t : ℝ => f (c + ε • ((cos t, sin t) : ℝ × ℝ))) := fun f hf => by
    apply hf.comp
    fun_prop
  have hI1 : IntervalIntegrable (fun t : ℝ =>
      (P (c + ε • (cos t, sin t)) * (-ε * sin t) + Q (c + ε • (cos t, sin t)) * (ε * cos t)))
      volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable
    have := hcont P hPc
    have := hcont Q hQc
    fun_prop
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      ((P c + ε * (cos t * LP (1, 0) + sin t * LP (0, 1))) * (-ε * sin t) +
        (Q c + ε * (cos t * LQ (1, 0) + sin t * LQ (0, 1))) * (ε * cos t))) volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hdiff := intervalIntegral.integral_sub hI1 hI2
  have hmain := curlDivLim_main (P c) (Q c) (LP (1, 0)) (LP (0, 1)) (LQ (1, 0)) (LQ (0, 1)) ε
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * π) (C := 2 * (e / 8 * ε) * ε)
    (f := fun t : ℝ => (P (c + ε • (cos t, sin t)) * (-ε * sin t) + Q (c + ε • (cos t, sin t)) * (ε * cos t))
      - ((P c + ε * (cos t * LP (1, 0) + sin t * LP (0, 1))) * (-ε * sin t) +
        (Q c + ε * (cos t * LQ (1, 0) + sin t * LQ (0, 1))) * (ε * cos t))) (fun t _ => hbd t)
  rw [hdiff, hmain] at hle
  set I := ∫ t in (0 : ℝ)..2 * π,
        (P (c + ε • (cos t, sin t)) * (-ε * sin t) + Q (c + ε • (cos t, sin t)) * (ε * cos t))
  have hpos : 0 < π * ε ^ 2 := by positivity
  have habs : |2 * π - 0| = 2 * π := by
    rw [sub_zero]; exact abs_of_pos (by positivity)
  rw [habs, Real.norm_eq_abs] at hle
  rw [Real.dist_eq]
  have : I / (π * ε ^ 2) - (LQ (1, 0) - LP (0, 1)) = (I - π * ε ^ 2 * (LQ (1, 0) - LP (0, 1))) / (π * ε ^ 2) := by
    field_simp
  rw [this, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  have h8 : |I - π * ε ^ 2 * (LQ (1, 0) - LP (0, 1))| ≤ 2 * (e / 8 * ε) * ε * (2 * π) := hle
  have : 2 * (e / 8 * ε) * ε * (2 * π) < e * (π * ε ^ 2) := by
    have : 0 < e * (π * ε ^ 2) := by positivity
    nlinarith
  linarith

/-- Integral over the polar angle of the linearized flux integrand. -/
lemma curlDivLim_inner3 (u v f1 f2 f3 a11 a12 a13 a21 a22 a23 a31 a32 a33 ε : ℝ) :
    ∫ x in (0 : ℝ)..π,
      ((f1 + ε * (sin x * u * a11 + sin x * v * a12 + cos x * a13)) * (sin x * u) +
       (f2 + ε * (sin x * u * a21 + sin x * v * a22 + cos x * a23)) * (sin x * v) +
       (f3 + ε * (sin x * u * a31 + sin x * v * a32 + cos x * a33)) * cos x) * (ε ^ 2 * sin x)
    = ε ^ 2 * (π / 2) * (f1 * u + f2 * v) +
      ε ^ 3 * (4 / 3 * (a11 * u ^ 2 + (a12 + a21) * u * v + a22 * v ^ 2) + 2 / 3 * a33) := by
  let T := a11 * u ^ 2 + (a12 + a21) * u * v + a22 * v ^ 2
  let Φ : ℝ → ℝ := fun x =>
    ε ^ 2 * (f1 * u + f2 * v) * ((x - sin x * cos x) / 2) + ε ^ 2 * f3 * ((sin x) ^ 2 / 2)
    + ε ^ 3 * T * (-cos x + (cos x) ^ 3 / 3)
    + ε ^ 3 * (a13 * u + a31 * u + a23 * v + a32 * v) * ((sin x) ^ 3 / 3)
    - ε ^ 3 * a33 * ((cos x) ^ 3 / 3)
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) π, HasDerivAt Φ
      (((f1 + ε * (sin x * u * a11 + sin x * v * a12 + cos x * a13)) * (sin x * u) +
       (f2 + ε * (sin x * u * a21 + sin x * v * a22 + cos x * a23)) * (sin x * v) +
       (f3 + ε * (sin x * u * a31 + sin x * v * a32 + cos x * a33)) * cos x) * (ε ^ 2 * sin x)) x := by
    intro x _
    have h1 := hasDerivAt_sin x
    have h2 := hasDerivAt_cos x
    have h3 := hasDerivAt_id x
    have k1 := ((h3.sub (h1.mul h2)).div_const 2).const_mul (ε ^ 2 * (f1 * u + f2 * v))
    have k2 := ((h1.pow 2).div_const 2).const_mul (ε ^ 2 * f3)
    have k3 := ((h2.neg.add ((h2.pow 3).div_const 3))).const_mul (ε ^ 3 * T)
    have k4 := ((h1.pow 3).div_const 3).const_mul (ε ^ 3 * (a13 * u + a31 * u + a23 * v + a32 * v))
    have k5 := ((h2.pow 3).div_const 3).const_mul (ε ^ 3 * a33)
    have k := (((k1.add k2).add k3).add k4).sub k5
    refine k.congr_deriv ?_
    have e1 := sin_sq_add_cos_sq x
    simp only [T]
    simp only [Nat.cast_ofNat]
    linear_combination (-(ε ^ 2 * (f1 * u + f2 * v) / 2 +
      ε ^ 3 * (a11 * u ^ 2 + (a12 + a21) * u * v + a22 * v ^ 2) * sin x)) * e1
  rw [integral_eq_sub_of_hasDerivAt hF (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [Φ, T, sin_pi, cos_pi, sin_zero, cos_zero]
  ring

/-- Integral over the azimuth of the polar-angle-integrated linearized flux integrand. -/
lemma curlDivLim_outer3 (f1 f2 a11 a12 a21 a22 a33 ε : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π,
      (ε ^ 2 * (π / 2) * (f1 * cos θ + f2 * sin θ) +
      ε ^ 3 * (4 / 3 * (a11 * cos θ ^ 2 + (a12 + a21) * cos θ * sin θ + a22 * sin θ ^ 2)
        + 2 / 3 * a33)) = 4 * π / 3 * ε ^ 3 * (a11 + a22 + a33) := by
  let G : ℝ → ℝ := fun x =>
    ε ^ 2 * (π / 2) * (f1 * sin x - f2 * cos x) +
    ε ^ 3 * (4 / 3 * (a11 * ((x + sin x * cos x) / 2) + (a12 + a21) * ((sin x) ^ 2 / 2)
      + a22 * ((x - sin x * cos x) / 2)) + 2 / 3 * a33 * x)
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt G
      (ε ^ 2 * (π / 2) * (f1 * cos x + f2 * sin x) +
      ε ^ 3 * (4 / 3 * (a11 * cos x ^ 2 + (a12 + a21) * cos x * sin x + a22 * sin x ^ 2)
        + 2 / 3 * a33)) x := by
    intro x _
    have h1 := hasDerivAt_sin x
    have h2 := hasDerivAt_cos x
    have h3 := hasDerivAt_id x
    have k1 := ((h1.const_mul f1).sub (h2.const_mul f2)).const_mul (ε ^ 2 * (π / 2))
    have k2 := (((((h3.add (h1.mul h2)).div_const 2).const_mul a11).add
      (((h1.pow 2).div_const 2).const_mul (a12 + a21))).add
      (((h3.sub (h1.mul h2)).div_const 2).const_mul a22))
    have k3 := (k2.const_mul (4 / 3)).add (h3.const_mul (2 / 3 * a33))
    have k := k1.add (k3.const_mul (ε ^ 3))
    refine k.congr_deriv ?_
    have e1 := sin_sq_add_cos_sq x
    simp only [Nat.cast_ofNat]
    linear_combination (-(2 / 3) * ε ^ 3 * (a11 + a22)) * e1
  rw [integral_eq_sub_of_hasDerivAt hF (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [G, sin_two_pi, cos_two_pi, sin_zero, cos_zero]
  ring

/-- Unit normal of a sphere in spherical coordinates: polar angle `φ`, azimuth `θ`. -/
noncomputable def sphereNormal (φ θ : ℝ) : ℝ × ℝ × ℝ := (sin φ * cos θ, sin φ * sin θ, cos φ)

@[fun_prop]
lemma curlDivLim_continuous_sphereNormal {α : Type*} [TopologicalSpace α] {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => sphereNormal (f x) (g x) := by
  unfold sphereNormal
  fun_prop

/-- A linear functional applied to a point of a sphere of radius `ε`. -/
lemma curlDivLim_lin_sphere (L : ℝ × ℝ × ℝ →L[ℝ] ℝ) (ε φ θ : ℝ) :
    L (ε • sphereNormal φ θ) = ε * (sin φ * cos θ * L (1, 0, 0) + sin φ * sin θ * L (0, 1, 0)
      + cos φ * L (0, 0, 1)) := by
  have h : ε • sphereNormal φ θ = (ε * (sin φ * cos θ)) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) +
      (ε * (sin φ * sin θ)) • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
      (ε * cos φ) • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp [sphereNormal]
  rw [h, map_add, map_add, map_smul, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

lemma curlDivLim_norm_sphere (φ θ : ℝ) : ‖sphereNormal φ θ‖ ≤ 1 := by
  have h1 : ‖sin φ * cos θ‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ (by simpa using abs_sin_le_one φ) (norm_nonneg _)
      (by simpa using abs_cos_le_one θ)
  have h2 : ‖sin φ * sin θ‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ (by simpa using abs_sin_le_one φ) (norm_nonneg _)
      (by simpa using abs_sin_le_one θ)
  have h3 : ‖cos φ‖ ≤ 1 := by simpa using abs_cos_le_one φ
  simp only [sphereNormal, Prod.norm_def]
  exact max_le h1 (max_le h2 h3)

/-- If two jointly continuous integrands differ by at most `B`, their iterated integrals
over `[0, 2π] × [0, π]` differ by at most `B * π * (2π)`. -/
lemma curlDivLim_dbl_err (g h : ℝ → ℝ → ℝ) (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hh : Continuous (fun p : ℝ × ℝ => h p.1 p.2)) (B : ℝ) (hB : ∀ θ φ, ‖g θ φ - h θ φ‖ ≤ B) :
    ‖(∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..π, g θ φ) -
      ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..π, h θ φ‖ ≤ B * π * (2 * π) := by
  have cg : Continuous fun θ => ∫ φ in (0 : ℝ)..π, g θ φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := g) hg 0 π
  have ch : Continuous fun θ => ∫ φ in (0 : ℝ)..π, h θ φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := h) hh 0 π
  rw [← intervalIntegral.integral_sub (cg.intervalIntegrable _ _) (ch.intervalIntegrable _ _)]
  have hpi : |π - 0| = π := by rw [sub_zero]; exact abs_of_pos pi_pos
  have h2pi : |2 * π - 0| = 2 * π := by rw [sub_zero]; exact abs_of_pos (by positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (C := B * π)
    (f := fun θ => (∫ φ in (0 : ℝ)..π, g θ φ) - ∫ φ in (0 : ℝ)..π, h θ φ) (fun θ _ => by
      have gi : IntervalIntegrable (fun φ => g θ φ) volume 0 π :=
        (hg.comp (by fun_prop : Continuous fun φ : ℝ => (θ, φ))).intervalIntegrable _ _
      have hi : IntervalIntegrable (fun φ => h θ φ) volume 0 π :=
        (hh.comp (by fun_prop : Continuous fun φ : ℝ => (θ, φ))).intervalIntegrable _ _
      rw [← intervalIntegral.integral_sub gi hi]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π) (C := B)
        (f := fun φ => g θ φ - h θ φ) (fun φ _ => hB θ φ)
      rw [hpi] at this
      linarith)
  rwa [h2pi] at this

/-- OpenStax Calculus 3:§6.8 Fact (divergence as flux per unit volume) (CA-662): for continuous
`P Q R : ℝ × ℝ × ℝ → ℝ` differentiable at `c`, the outward flux of `(P, Q, R)` through the sphere
of radius `ε` about `c` (spherical parameterization, normal `sphereNormal φ θ`, area element
`ε² sin φ`), divided by the enclosed volume `4π ε³ / 3`, tends to the divergence
`P_x + Q_y + R_z` at `c` as `ε → 0⁺`. -/
@[kb "openstaxcalculus2016" "3:§6.8 Fact (divergence as flux per unit volume), p. 737"]
theorem flux_per_volume_tendsto (P Q R : ℝ × ℝ × ℝ → ℝ) (hPc : Continuous P) (hQc : Continuous Q)
    (hRc : Continuous R) (c : ℝ × ℝ × ℝ) (hP : DifferentiableAt ℝ P c)
    (hQ : DifferentiableAt ℝ Q c) (hR : DifferentiableAt ℝ R c) :
    Tendsto (fun ε : ℝ => (∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..π,
        (P (c + ε • sphereNormal φ θ) * (sin φ * cos θ) + Q (c + ε • sphereNormal φ θ) * (sin φ * sin θ)
          + R (c + ε • sphereNormal φ θ) * cos φ) * (ε ^ 2 * sin φ)) / (4 * π * ε ^ 3 / 3))
      (𝓝[>] 0)
      (𝓝 (fderiv ℝ P c (1, 0, 0) + fderiv ℝ Q c (0, 1, 0) + fderiv ℝ R c (0, 0, 1))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro e he
  have hη : 0 < e / (20 * π) := by positivity
  set η := e / (20 * π) with hηdef
  have hP' := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hP.hasFDerivAt).def hη
  have hQ' := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hQ.hasFDerivAt).def hη
  have hR' := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hR.hasFDerivAt).def hη
  obtain ⟨δP, hδP, hP2⟩ := Metric.eventually_nhds_iff.1 hP'
  obtain ⟨δQ, hδQ, hQ2⟩ := Metric.eventually_nhds_iff.1 hQ'
  obtain ⟨δR, hδR, hR2⟩ := Metric.eventually_nhds_iff.1 hR'
  refine ⟨min (min δP δQ) δR, lt_min (lt_min hδP hδQ) hδR, ?_⟩
  intro ε hε hdist
  have hεpos : 0 < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hεpos] at hdist
  have hεP : ε < δP := lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_left _ _))
  have hεQ : ε < δQ := lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_right _ _))
  have hεR : ε < δR := lt_of_lt_of_le hdist (min_le_right _ _)
  set LP := fderiv ℝ P c
  set LQ := fderiv ℝ Q c
  set LR := fderiv ℝ R c
  have hnorm : ∀ φ θ : ℝ, ‖ε • sphereNormal φ θ‖ ≤ ε := by
    intro φ θ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
    have := curlDivLim_norm_sphere φ θ
    nlinarith
  -- the book integrand and its linearization
  set g : ℝ → ℝ → ℝ := fun θ φ =>
    (P (c + ε • sphereNormal φ θ) * (sin φ * cos θ) + Q (c + ε • sphereNormal φ θ) * (sin φ * sin θ)
      + R (c + ε • sphereNormal φ θ) * cos φ) * (ε ^ 2 * sin φ) with hg
  set h : ℝ → ℝ → ℝ := fun θ φ =>
    ((P c + ε * (sin φ * cos θ * LP (1, 0, 0) + sin φ * sin θ * LP (0, 1, 0) + cos φ * LP (0, 0, 1)))
        * (sin φ * cos θ) +
      (Q c + ε * (sin φ * cos θ * LQ (1, 0, 0) + sin φ * sin θ * LQ (0, 1, 0) + cos φ * LQ (0, 0, 1)))
        * (sin φ * sin θ) +
      (R c + ε * (sin φ * cos θ * LR (1, 0, 0) + sin φ * sin θ * LR (0, 1, 0) + cos φ * LR (0, 0, 1)))
        * cos φ) * (ε ^ 2 * sin φ) with hh
  have hfac : ∀ x φ : ℝ, ‖x‖ ≤ 1 → ‖x * (ε ^ 2 * sin φ)‖ ≤ ε ^ 2 := by
    intro x φ hx
    rw [norm_mul, norm_mul, Real.norm_eq_abs (ε ^ 2), Real.norm_eq_abs (sin φ),
      abs_of_pos (by positivity : 0 < ε ^ 2)]
    have := abs_sin_le_one φ
    have h0 := abs_nonneg (sin φ)
    have h1 : ‖x‖ * (ε ^ 2 * |sin φ|) ≤ 1 * (ε ^ 2 * 1) :=
      mul_le_mul hx (mul_le_mul_of_nonneg_left this (by positivity)) (by positivity) zero_le_one
    linarith
  have hbd : ∀ θ φ : ℝ, ‖g θ φ - h θ φ‖ ≤ 3 * (η * ε) * ε ^ 2 := by
    intro θ φ
    have hn := hnorm φ θ
    have a1 := hP2 (y := ε • sphereNormal φ θ) (by
      rw [dist_zero_right]; exact lt_of_le_of_lt hn hεP)
    have a2 := hQ2 (y := ε • sphereNormal φ θ) (by
      rw [dist_zero_right]; exact lt_of_le_of_lt hn hεQ)
    have a3 := hR2 (y := ε • sphereNormal φ θ) (by
      rw [dist_zero_right]; exact lt_of_le_of_lt hn hεR)
    rw [curlDivLim_lin_sphere] at a1 a2 a3
    have b1 := a1.trans (mul_le_mul_of_nonneg_left hn hη.le)
    have b2 := a2.trans (mul_le_mul_of_nonneg_left hn hη.le)
    have b3 := a3.trans (mul_le_mul_of_nonneg_left hn hη.le)
    have f1 := hfac (sin φ * cos θ) φ (by
      rw [norm_mul]
      exact mul_le_one₀ (by simpa using abs_sin_le_one φ) (norm_nonneg _)
        (by simpa using abs_cos_le_one θ))
    have f2 := hfac (sin φ * sin θ) φ (by
      rw [norm_mul]
      exact mul_le_one₀ (by simpa using abs_sin_le_one φ) (norm_nonneg _)
        (by simpa using abs_sin_le_one θ))
    have f3 := hfac (cos φ) φ (by simpa using abs_cos_le_one φ)
    have key : g θ φ - h θ φ =
        (P (c + ε • sphereNormal φ θ) - P c - ε * (sin φ * cos θ * LP (1, 0, 0)
          + sin φ * sin θ * LP (0, 1, 0) + cos φ * LP (0, 0, 1))) * ((sin φ * cos θ) * (ε ^ 2 * sin φ))
        + (Q (c + ε • sphereNormal φ θ) - Q c - ε * (sin φ * cos θ * LQ (1, 0, 0)
          + sin φ * sin θ * LQ (0, 1, 0) + cos φ * LQ (0, 0, 1))) * ((sin φ * sin θ) * (ε ^ 2 * sin φ))
        + (R (c + ε • sphereNormal φ θ) - R c - ε * (sin φ * cos θ * LR (1, 0, 0)
          + sin φ * sin θ * LR (0, 1, 0) + cos φ * LR (0, 0, 1))) * (cos φ * (ε ^ 2 * sin φ)) := by
      simp only [hg, hh]
      ring
    rw [key]
    refine norm_add₃_le.trans ?_
    refine le_trans (add_le_add (add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul b1 f1 (norm_nonneg _) (by positivity)))
      ((norm_mul_le _ _).trans (mul_le_mul b2 f2 (norm_nonneg _) (by positivity))))
      ((norm_mul_le _ _).trans (mul_le_mul b3 f3 (norm_nonneg _) (by positivity)))) ?_
    exact le_of_eq (by ring)
  have hcont : ∀ f : ℝ × ℝ × ℝ → ℝ, Continuous f →
      Continuous (fun p : ℝ × ℝ => f (c + ε • sphereNormal p.2 p.1)) := fun f hf =>
    hf.comp (by fun_prop)
  have hgc : Continuous (fun p : ℝ × ℝ => g p.1 p.2) := by
    have := hcont P hPc
    have := hcont Q hQc
    have := hcont R hRc
    simp only [hg]
    fun_prop
  have hhc : Continuous (fun p : ℝ × ℝ => h p.1 p.2) := by
    simp only [hh]
    fun_prop
  have herr := curlDivLim_dbl_err g h hgc hhc _ hbd
  have hM : (∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..π, h θ φ) =
      4 * π / 3 * ε ^ 3 * (LP (1, 0, 0) + LQ (0, 1, 0) + LR (0, 0, 1)) := by
    calc (∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..π, h θ φ)
        = ∫ θ in (0 : ℝ)..2 * π,
          (ε ^ 2 * (π / 2) * (P c * cos θ + Q c * sin θ) +
          ε ^ 3 * (4 / 3 * (LP (1, 0, 0) * cos θ ^ 2 + (LP (0, 1, 0) + LQ (1, 0, 0)) * cos θ * sin θ
            + LQ (0, 1, 0) * sin θ ^ 2) + 2 / 3 * LR (0, 0, 1))) := by
          congr 1
          funext θ
          exact curlDivLim_inner3 (cos θ) (sin θ) (P c) (Q c) (R c) (LP (1, 0, 0)) (LP (0, 1, 0))
            (LP (0, 0, 1)) (LQ (1, 0, 0)) (LQ (0, 1, 0)) (LQ (0, 0, 1)) (LR (1, 0, 0))
            (LR (0, 1, 0)) (LR (0, 0, 1)) ε
      _ = _ := curlDivLim_outer3 (P c) (Q c) (LP (1, 0, 0)) (LP (0, 1, 0)) (LQ (1, 0, 0))
            (LQ (0, 1, 0)) (LR (0, 0, 1)) ε
  rw [hM] at herr
  show dist ((∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..π, g θ φ) / (4 * π * ε ^ 3 / 3)) _ < e
  set I := ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..π, g θ φ
  set S := LP (1, 0, 0) + LQ (0, 1, 0) + LR (0, 0, 1)
  have hpos : 0 < 4 * π * ε ^ 3 / 3 := by positivity
  rw [Real.dist_eq]
  have hx : I / (4 * π * ε ^ 3 / 3) - S = (I - 4 * π / 3 * ε ^ 3 * S) / (4 * π * ε ^ 3 / 3) := by
    field_simp
  rw [hx, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  have h8 : |I - 4 * π / 3 * ε ^ 3 * S| ≤ 3 * (η * ε) * ε ^ 2 * π * (2 * π) := herr
  have h9 : 3 * (η * ε) * ε ^ 2 * π * (2 * π) = 3 / 10 * π * e * ε ^ 3 := by
    rw [hηdef]
    field_simp
    ring
  have hp : 0 < e * π * ε ^ 3 := by positivity
  nlinarith

end UndergradKB.Calculus
