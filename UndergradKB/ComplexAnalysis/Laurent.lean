import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import UndergradKB.Common.Attr

/-!
# Laurent series of a function holomorphic on an annulus

Beck et al., *A First Course in Complex Analysis*, Section 8.3 (checklist rows CX-130, CX-132, CX-133). Mathlib has
formal Laurent series (`LaurentSeries`) but not the analytic Laurent expansion. Here, for `f` holomorphic on the open
annulus `r < |z - c| < R` (spelled as `ball c R` minus `closedBall c r`, with `0 ≤ r`):

* `laurentCoeff f c ρ n = (2πi)⁻¹ ∮_{|z-c|=ρ} f(z) / (z-c)^(n+1) dz` (the book's coefficient formula);
* it does not depend on the radius `ρ ∈ (r, R)` (`laurentCoeff_eq_of_annulus`);
* `annulus_cauchy_integral_formula`: `f w` is the difference of the Cauchy integrals over two circles around `w`;
* **Laurent's theorem** (`hasSum_laurentCoeff`): `∑_{n ∈ ℤ} c_n (w - c)^n = f w` on the annulus;
* termwise integration (`circleIntegral_eq_laurentCoeff_neg_one`): `∮ f = 2πi c₋₁`.

The proof follows the book: the annulus Cauchy formula, a geometric expansion of `1/(z-w)` on the outer circle
(Mathlib's `hasSum_two_pi_I_cauchyPowerSeries_integral`) and on the inner circle (dominated convergence).
These are stated for `f : ℂ → ℂ` on an arbitrary annulus (inner radius `0` gives a punctured disc), the generality
needed for residues (modular forms, analytic number theory).
-/

open Complex Metric Set Filter Topology Real MeasureTheory

namespace UndergradKB.ComplexAnalysis

/-- Cauchy's theorem for two concentric circles inside an open annulus (a step towards Beck Theorem 8.3.5; Mathlib's
`circleIntegral_eq_of_differentiable_on_annulus_off_countable` restated for an open annulus). -/
theorem circleIntegral_eq_of_differentiableOn_annulus {g : ℂ → ℂ} {c : ℂ} {r R ρ₁ ρ₂ : ℝ}
    (hg : DifferentiableOn ℂ g (ball c R \ closedBall c r)) (hr : 0 ≤ r) (h₁ : r < ρ₁)
    (h₁₂ : ρ₁ ≤ ρ₂) (h₂ : ρ₂ < R) :
    (∮ z in C(c, ρ₂), g z) = ∮ z in C(c, ρ₁), g z := by
  have hsub : closedBall c ρ₂ \ ball c ρ₁ ⊆ ball c R \ closedBall c r := by
    intro z ⟨hz1, hz2⟩
    simp only [mem_closedBall, mem_ball, not_lt] at hz1 hz2
    exact ⟨mem_ball.2 (by linarith), fun h => by simp only [mem_closedBall] at h; linarith⟩
  have hopen : IsOpen (ball c R \ closedBall c r) := isOpen_ball.sdiff isClosed_closedBall
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable (hr.trans_lt h₁) h₁₂
    countable_empty (hg.continuousOn.mono hsub) fun z hz => ?_
  refine hg.differentiableAt (hopen.mem_nhds ?_)
  obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
  simp only [mem_closedBall, mem_ball, not_le] at hz1 hz2
  exact ⟨mem_ball.2 (by linarith), fun h => by simp only [mem_closedBall] at h; linarith⟩

/-- The Cauchy integral formula on an annulus (Beck, proof of Theorem 8.3.5): for `ρ₁ < |w - c| < ρ₂` inside the
annulus, `∮_{ρ₂} f(z)/(z-w) dz - ∮_{ρ₁} f(z)/(z-w) dz = 2πi f(w)`. -/
theorem annulus_cauchy_integral_formula {f : ℂ → ℂ} {c w : ℂ} {r R ρ₁ ρ₂ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R \ closedBall c r)) (hr : 0 ≤ r) (h₁ : r < ρ₁)
    (hw₁ : ρ₁ < ‖w - c‖) (hw₂ : ‖w - c‖ < ρ₂) (h₂ : ρ₂ < R) :
    (∮ z in C(c, ρ₂), (z - w)⁻¹ * f z) - (∮ z in C(c, ρ₁), (z - w)⁻¹ * f z) =
      2 * π * I * f w := by
  have hopen : IsOpen (ball c R \ closedBall c r) := isOpen_ball.sdiff isClosed_closedBall
  have hmem : ∀ z, ρ₁ ≤ ‖z - c‖ → ‖z - c‖ ≤ ρ₂ → z ∈ ball c R \ closedBall c r := by
    intro z h1 h2
    refine ⟨mem_ball_iff_norm.2 (by linarith), fun h => ?_⟩
    rw [mem_closedBall_iff_norm] at h; linarith
  have hwA : w ∈ ball c R \ closedBall c r := hmem w hw₁.le hw₂.le
  have hfw : DifferentiableAt ℂ f w := hf.differentiableAt (hopen.mem_nhds hwA)
  set A := closedBall c ρ₂ \ ball c ρ₁
  have hAsub : A ⊆ ball c R \ closedBall c r := by
    intro z ⟨hz1, hz2⟩
    rw [mem_closedBall_iff_norm] at hz1
    rw [mem_ball_iff_norm, not_lt] at hz2
    exact hmem z hz2 hz1
  -- the difference quotient is continuous on the closed annulus
  have hAw : A ∈ 𝓝 w := by
    have : ball c ρ₂ \ closedBall c ρ₁ ⊆ A :=
      sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall
    refine Filter.mem_of_superset ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds ?_) this
    refine ⟨mem_ball_iff_norm.2 hw₂, fun h => ?_⟩
    rw [mem_closedBall_iff_norm] at h; linarith
  have hcont : ContinuousOn (dslope f w) A :=
    (continuousOn_dslope hAw).2 ⟨hf.continuousOn.mono hAsub, hfw⟩
  have hdiff : ∀ z ∈ (ball c ρ₂ \ closedBall c ρ₁) \ {w}, DifferentiableAt ℂ (dslope f w) z := by
    intro z ⟨⟨hz1, hz2⟩, hzw⟩
    rw [mem_ball_iff_norm] at hz1
    rw [mem_closedBall_iff_norm, not_le] at hz2
    refine (differentiableAt_dslope_of_ne hzw).2 ?_
    exact hf.differentiableAt (hopen.mem_nhds (hmem z hz2.le hz1.le))
  have key := circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (hr.trans_lt h₁) (hw₁.le.trans hw₂.le) (countable_singleton w) hcont hdiff
  have hρ₁ : 0 < ρ₁ := hr.trans_lt h₁
  have hρ₂ : 0 < ρ₂ := hρ₁.trans (hw₁.trans hw₂)
  -- on each circle, dslope is the difference quotient
  have hne : ∀ ρ, ρ ≠ ‖w - c‖ → ∀ z ∈ sphere c ρ, z ≠ w := by
    intro ρ hρ z hz hzw
    rw [mem_sphere_iff_norm, hzw] at hz
    exact hρ hz.symm
  have hcongr : ∀ ρ, ρ ≠ ‖w - c‖ → 0 ≤ ρ →
      (∮ z in C(c, ρ), dslope f w z) = ∮ z in C(c, ρ), ((z - w)⁻¹ * f z - (z - w)⁻¹ * f w) := by
    intro ρ hρ hρ0
    refine circleIntegral.integral_congr hρ0 fun z hz => ?_
    simp only [dslope_of_ne _ (hne ρ hρ z hz), slope_def_module, smul_eq_mul, mul_sub]
  have hcircle : ∀ ρ, 0 < ρ → (∀ z ∈ sphere c ρ, z ∈ ball c R \ closedBall c r) →
      ρ ≠ ‖w - c‖ → CircleIntegrable (fun z => (z - w)⁻¹ * f z) c ρ := by
    intro ρ hρ hS hρw
    refine ContinuousOn.circleIntegrable hρ.le ?_
    refine ContinuousOn.mul ?_ (hf.continuousOn.mono hS)
    exact (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 (hne ρ hρw z hz)
  have hS₁ : ∀ z ∈ sphere c ρ₁, z ∈ ball c R \ closedBall c r := fun z hz => by
    rw [mem_sphere_iff_norm] at hz; exact hmem z hz.ge (by linarith)
  have hS₂ : ∀ z ∈ sphere c ρ₂, z ∈ ball c R \ closedBall c r := fun z hz => by
    rw [mem_sphere_iff_norm] at hz; exact hmem z (by linarith) hz.le
  have hinvint : ∀ ρ, 0 < ρ → ρ ≠ ‖w - c‖ → CircleIntegrable (fun z => (z - w)⁻¹ * f w) c ρ := by
    intro ρ hρ hρw
    refine ContinuousOn.circleIntegrable hρ.le (ContinuousOn.mul ?_ continuousOn_const)
    exact (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 (hne ρ hρw z hz)
  rw [hcongr ρ₂ (by linarith) hρ₂.le, hcongr ρ₁ (by linarith) hρ₁.le,
    circleIntegral.integral_sub (hcircle ρ₂ hρ₂ hS₂ (by linarith)) (hinvint ρ₂ hρ₂ (by linarith)),
    circleIntegral.integral_sub (hcircle ρ₁ hρ₁ hS₁ (by linarith)) (hinvint ρ₁ hρ₁ (by linarith))]
    at key
  have hout : (∮ z in C(c, ρ₁), (z - w)⁻¹ * f w) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hρ₁.le countable_empty ?_ ?_
    · refine ContinuousOn.mul (ContinuousOn.inv₀ (by fun_prop) fun z hz => ?_) continuousOn_const
      rw [mem_closedBall_iff_norm] at hz
      intro h; rw [sub_eq_zero] at h; subst h; linarith
    · rintro z ⟨hz, -⟩
      rw [mem_ball_iff_norm] at hz
      refine ((differentiableAt_id.sub_const w).inv ?_).mul_const _
      intro h
      have hzw : z = w := by simpa [sub_eq_zero] using h
      rw [hzw] at hz; linarith
  have hin : (∮ z in C(c, ρ₂), (z - w)⁻¹ * f w) = 2 * π * I * f w := by
    have := circleIntegral.integral_smul_const (fun z => (z - w)⁻¹) (f w) c ρ₂
    simp only [smul_eq_mul] at this
    rw [this, circleIntegral.integral_sub_inv_of_mem_ball]
    rw [mem_ball_iff_norm]; exact hw₂
  rw [hout, hin, sub_zero] at key
  linear_combination key

/-- Beck Definition 8.3.1 and Theorem 8.3.5 (CX-130): the `n`-th Laurent coefficient of `f` about `c`, computed on
the circle of radius `ρ`: `(2πi)⁻¹ ∮_{|z-c|=ρ} f(z) / (z-c)^(n+1) dz`. -/
noncomputable def laurentCoeff (f : ℂ → ℂ) (c : ℂ) (ρ : ℝ) (n : ℤ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(c, ρ), (z - c) ^ (-(n + 1)) * f z

/-- Beck Theorem 8.3.5 (CX-132), independence of the radius: the Laurent coefficients of a function holomorphic
on an annulus are the same for every circle in the annulus. -/
@[kb "beck2025" "Theorem 8.3.5, p. 139"]
theorem laurentCoeff_eq_of_annulus {f : ℂ → ℂ} {c : ℂ} {r R ρ₁ ρ₂ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R \ closedBall c r)) (hr : 0 ≤ r) (h₁ : r < ρ₁)
    (h₁' : ρ₁ < R) (h₂ : r < ρ₂) (h₂' : ρ₂ < R) (n : ℤ) :
    laurentCoeff f c ρ₁ n = laurentCoeff f c ρ₂ n := by
  have hg : DifferentiableOn ℂ (fun z => (z - c) ^ (-(n + 1)) * f z)
      (ball c R \ closedBall c r) := by
    refine DifferentiableOn.mul (fun z hz => ?_) hf
    refine ((differentiableAt_id.sub_const c).zpow (Or.inl ?_)).differentiableWithinAt
    obtain ⟨-, hz⟩ := hz
    rw [mem_closedBall_iff_norm, not_le] at hz
    exact fun h => by
      have h' : z - c = 0 := by simpa using h
      rw [h', norm_zero] at hz; linarith
  unfold laurentCoeff
  congr 1
  rcases le_total ρ₁ ρ₂ with h | h
  · exact (circleIntegral_eq_of_differentiableOn_annulus hg hr h₁ h h₂').symm
  · exact circleIntegral_eq_of_differentiableOn_annulus hg hr h₂ h h₁'

/-- The outer half of the Laurent series: the Cauchy integral over a circle is a power series inside it. -/
theorem hasSum_laurent_outer {f : ℂ → ℂ} {c w : ℂ} {ρ : ℝ} (hf : CircleIntegrable f c ρ)
    (hw : ‖w - c‖ < ρ) :
    HasSum (fun n : ℕ => laurentCoeff f c ρ n * (w - c) ^ n)
      ((2 * π * I)⁻¹ * ∮ z in C(c, ρ), (z - w)⁻¹ * f z) := by
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hw
  have H := (hasSum_two_pi_I_cauchyPowerSeries_integral (E := ℂ) (w := w - c) hf hw).mul_left
    (2 * π * I)⁻¹
  simp only [add_sub_cancel, smul_eq_mul] at H
  convert H using 2 with n
  unfold laurentCoeff
  have hpt : (∮ z in C(c, ρ), ((w - c) / (z - c)) ^ n * ((z - c)⁻¹ * f z)) =
      ∮ z in C(c, ρ), (w - c) ^ n * ((z - c) ^ (-((n : ℤ) + 1)) * f z) := by
    refine circleIntegral.integral_congr hρ.le fun z hz => ?_
    have hz0 : z - c ≠ 0 := by
      intro h; rw [mem_sphere_iff_norm, h, norm_zero] at hz; linarith
    rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      div_pow, pow_succ]
    field_simp
  rw [hpt, circleIntegral.integral_const_mul]
  ring

/-- The inner half of the Laurent series: minus the Cauchy integral over a circle is a series in negative powers of
`w - c` outside it. -/
theorem hasSum_laurent_inner {f : ℂ → ℂ} {c w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : CircleIntegrable f c ρ) (hw : ρ < ‖w - c‖) :
    HasSum (fun k : ℕ => laurentCoeff f c ρ (-((k : ℤ) + 1)) * (w - c) ^ (-((k : ℤ) + 1)))
      (-((2 * π * I)⁻¹ * ∮ z in C(c, ρ), (z - w)⁻¹ * f z)) := by
  have hwc : 0 < ‖w - c‖ := hρ.trans hw
  set q : ℝ := ρ / ‖w - c‖ with hq
  have hq0 : 0 ≤ q := div_nonneg hρ.le hwc.le
  have hq1 : q < 1 := (div_lt_one hwc).2 hw
  -- the geometric expansion of `1 / (w - z)` on the circle, integrated term by term
  have H : HasSum (fun k : ℕ => ∮ z in C(c, ρ), ((z - c) / (w - c)) ^ k * (w - c)⁻¹ * f z)
      (∮ z in C(c, ρ), (w - z)⁻¹ * f z) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k θ => ‖f (circleMap c ρ θ)‖ * (ρ * ‖w - c‖⁻¹ * q ^ k)) (fun k => ?_) (fun k => ?_)
      ?_ ?_ ?_
    · simp only [deriv_circleMap]
      apply_rules [AEStronglyMeasurable.smul, AEStronglyMeasurable.mul, hf.def'.1] <;>
        apply Measurable.aestronglyMeasurable <;> fun_prop
    · refine Eventually.of_forall fun θ _ => le_of_eq ?_
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_pow, norm_div, norm_inv,
        circleMap_sub_center, norm_circleMap_zero, Complex.norm_I, abs_of_pos hρ, hq]
      ring
    · exact Eventually.of_forall fun _ _ =>
        ((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_left _
    · simp only [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      exact hf.norm.mul_continuousOn continuousOn_const
    · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
      set z := circleMap c ρ θ
      have hz : ‖(z - c) / (w - c)‖ < 1 := by
        rw [norm_div, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ]
        exact hq1
      have hwc0 : w - c ≠ 0 := norm_pos_iff.1 hwc
      have h1q : 1 - (z - c) / (w - c) ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        rw [← h, norm_one] at hz; exact lt_irrefl _ hz
      convert ((hasSum_geometric_of_norm_lt_one hz).mul_right ((w - c)⁻¹ * f z)) using 1
      · ext k; ring
      · have hwz : w - z = (w - c) * (1 - (z - c) / (w - c)) := by field_simp; ring
        show (w - z)⁻¹ * f z = _
        rw [hwz, mul_inv]; ring
  have H' := H.mul_left (2 * π * I)⁻¹
  have hneg : (∮ z in C(c, ρ), (w - z)⁻¹ * f z) = -∮ z in C(c, ρ), (z - w)⁻¹ * f z := by
    rw [← neg_one_mul, ← circleIntegral.integral_const_mul]
    congr 1; ext z; rw [← neg_sub w z, inv_neg]; ring
  rw [hneg, mul_neg] at H'
  convert H' using 1
  ext k
  unfold laurentCoeff
  rw [show -(-((k : ℤ) + 1) + 1) = (k : ℤ) by ring]
  have hpt : ∀ z, ((z - c) / (w - c)) ^ k * (w - c)⁻¹ * f z =
      (w - c) ^ (-((k : ℤ) + 1)) * ((z - c) ^ (k : ℤ) * f z) := by
    intro z
    have hwc0 : w - c ≠ 0 := norm_pos_iff.1 hwc
    rw [show (-((k : ℤ) + 1)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      zpow_natCast, div_pow, pow_succ]
    field_simp
  simp_rw [hpt, circleIntegral.integral_const_mul]
  ring

/-- A function holomorphic on an annulus is integrable on each circle of the annulus. -/
theorem circleIntegrable_of_annulus {f : ℂ → ℂ} {c : ℂ} {r R ρ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R \ closedBall c r)) (hr : 0 ≤ r) (h₁ : r < ρ)
    (h₂ : ρ < R) : CircleIntegrable f c ρ := by
  refine ContinuousOn.circleIntegrable (hr.trans h₁.le) (hf.continuousOn.mono fun z hz => ?_)
  rw [mem_sphere_iff_norm] at hz
  refine ⟨mem_ball_iff_norm.2 (by linarith), fun h => ?_⟩
  rw [mem_closedBall_iff_norm] at h; linarith

/-- Beck Theorem 8.3.5 (CX-132), **Laurent's theorem**: a function holomorphic on the annulus `r < |z - c| < R`
is the sum of its Laurent series `∑_{n ∈ ℤ} c_n (w - c)^n` at every point `w` of the annulus, with the coefficients
`c_n = laurentCoeff f c ρ n` computed on any circle `|z - c| = ρ` of the annulus. -/
@[kb "beck2025" "Theorem 8.3.5, p. 139"]
theorem hasSum_laurentCoeff {f : ℂ → ℂ} {c w : ℂ} {r R ρ : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R \ closedBall c r)) (hr : 0 ≤ r) (hρ : r < ρ)
    (hρ' : ρ < R) (hw : r < ‖w - c‖) (hw' : ‖w - c‖ < R) :
    HasSum (fun n : ℤ => laurentCoeff f c ρ n * (w - c) ^ n) (f w) := by
  set ρ₁ := (r + ‖w - c‖) / 2
  set ρ₂ := (‖w - c‖ + R) / 2
  have h₁ : r < ρ₁ := by simp only [ρ₁]; linarith
  have h₁' : ρ₁ < ‖w - c‖ := by simp only [ρ₁]; linarith
  have h₂ : ‖w - c‖ < ρ₂ := by simp only [ρ₂]; linarith
  have h₂' : ρ₂ < R := by simp only [ρ₂]; linarith
  have hout := hasSum_laurent_outer (circleIntegrable_of_annulus hf hr (by linarith) h₂') h₂
  have hin := hasSum_laurent_inner (hr.trans_lt h₁)
    (circleIntegrable_of_annulus hf hr h₁ (by linarith)) h₁'
  have hcf := annulus_cauchy_integral_formula hf hr h₁ h₁' h₂ h₂'
  have e : ∀ n, laurentCoeff f c ρ n = laurentCoeff f c ρ₂ n := fun n =>
    laurentCoeff_eq_of_annulus hf hr hρ hρ' (by linarith) h₂' n
  have e' : ∀ n, laurentCoeff f c ρ n = laurentCoeff f c ρ₁ n := fun n =>
    laurentCoeff_eq_of_annulus hf hr hρ hρ' h₁ (by linarith) n
  have H := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => laurentCoeff f c ρ n * (w - c) ^ n)
    (by simpa only [e, zpow_natCast] using hout) (by simpa only [e'] using hin)
  convert H using 1
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [← mul_neg, ← mul_add, ← sub_eq_add_neg, hcf, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]

/-- Beck Corollary 8.3.9 (CX-133), termwise integration of the Laurent series: the integral of `f` over any circle
of the annulus is `2πi c₋₁`. -/
@[kb "beck2025" "Corollary 8.3.9, p. 141"]
theorem circleIntegral_eq_laurentCoeff_neg_one {f : ℂ → ℂ} {c : ℂ} {r R ρ ρ' : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R \ closedBall c r)) (hr : 0 ≤ r) (hρ : r < ρ)
    (hρ' : ρ < R) (h : r < ρ') (h' : ρ' < R) :
    (∮ z in C(c, ρ), f z) = 2 * π * I * laurentCoeff f c ρ' (-1) := by
  rw [← laurentCoeff_eq_of_annulus hf hr hρ hρ' h h', laurentCoeff]
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [Int.reduceNeg, neg_add_cancel, neg_zero, zpow_zero, one_mul]
  rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]

end UndergradKB.ComplexAnalysis
