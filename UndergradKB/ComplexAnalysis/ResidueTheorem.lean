import UndergradKB.ComplexAnalysis.Residue
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The residue theorem for a circle

Beck et al., *A First Course in Complex Analysis*, Theorem 9.2.2 (checklist row CX-141), for the path a circle:
if `f` is holomorphic on the closed disc `|z - c| ≤ R` except at finitely many points `S` of the open disc, then
`∮_{|z-c|=R} f = 2πi ∑_{s ∈ S} Res_{z=s} f`. The singularities may be of any kind (removable, poles or essential).

Proof. For each singular point `s`, the *principal part* `principalPart f s δ w = -(2πi)⁻¹ ∮_{|z-s|=ρ} f(z)/(z-w) dz`
(`ρ` small) is holomorphic away from `s`, and `f` minus it is holomorphic near `s` (the annulus Cauchy formula).
So `f - ∑ principal parts` extends holomorphically to the closed disc and has integral `0` (Mathlib's Cauchy theorem
for a disc), while the integral of each principal part over the big circle is, by Fubini, `∮_{|z-s|=ρ} f = 2πi Res`.
This replaces the book's deformation of `γ` into small circles (general homotopy is not in Mathlib).
-/

open Complex Metric Set Filter Topology Real MeasureTheory

namespace UndergradKB.ComplexAnalysis

/-- Fubini's theorem for two circle integrals. -/
theorem circleIntegral_circleIntegral_swap {F : ℂ → ℂ → ℂ} {c s : ℂ} {R ρ : ℝ} (hR : 0 ≤ R)
    (hρ : 0 ≤ ρ) (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (sphere c R ×ˢ sphere s ρ)) :
    (∮ w in C(c, R), ∮ z in C(s, ρ), F w z) = ∮ z in C(s, ρ), ∮ w in C(c, R), F w z := by
  simp only [circleIntegral, smul_eq_mul]
  simp_rw [← intervalIntegral.integral_const_mul]
  have hcont : Continuous fun q : ℝ × ℝ => deriv (circleMap c R) q.1 *
      (deriv (circleMap s ρ) q.2 * F (circleMap c R q.1) (circleMap s ρ q.2)) := by
    simp only [deriv_circleMap]
    refine Continuous.mul (by fun_prop) (Continuous.mul (by fun_prop) ?_)
    exact hF.comp_continuous (f := fun q : ℝ × ℝ => (circleMap c R q.1, circleMap s ρ q.2))
      (by fun_prop) fun q => ⟨circleMap_mem_sphere c hR q.1, circleMap_mem_sphere s hρ q.2⟩
  have hint : IntegrableOn (fun q : ℝ × ℝ => deriv (circleMap c R) q.1 *
      (deriv (circleMap s ρ) q.2 * F (circleMap c R q.1) (circleMap s ρ q.2)))
      (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π)) := by
    refine (hcont.continuousOn.integrableOn_compact
      ((isCompact_uIcc (a := (0 : ℝ)) (b := 2 * π)).prod
        (isCompact_uIcc (a := (0 : ℝ)) (b := 2 * π)))).mono_set ?_
    exact prod_mono uIoc_subset_uIcc uIoc_subset_uIcc
  rw [intervalIntegral_intervalIntegral_swap (F := fun θ φ => deriv (circleMap c R) θ *
      (deriv (circleMap s ρ) φ * F (circleMap c R θ) (circleMap s ρ φ))) hint]
  congr 1; ext φ; congr 1; ext θ; ring

/-- The principal part of `f` at an isolated singularity `s` (with `f` holomorphic on `0 < |z - s| < δ`):
`-(2πi)⁻¹ ∮_{|z-s|=ρ} f(z)/(z-w) dz` for a circle around `s` separating `s` from `w`. -/
noncomputable def principalPart (f : ℂ → ℂ) (s : ℂ) (δ : ℝ) (w : ℂ) : ℂ :=
  -((2 * π * I)⁻¹ * ∮ z in C(s, min ‖w - s‖ δ / 2), (z - w)⁻¹ * f z)

theorem principalPart_eq {f : ℂ → ℂ} {s w : ℂ} {δ ρ : ℝ}
    (hf : DifferentiableOn ℂ f (ball s δ \ {s})) (hρ : 0 < ρ) (hρw : ρ < min ‖w - s‖ δ) :
    principalPart f s δ w = -((2 * π * I)⁻¹ * ∮ z in C(s, ρ), (z - w)⁻¹ * f z) := by
  set m := min ‖w - s‖ δ
  have hm : 0 < m := hρ.trans hρw
  have hg : DifferentiableOn ℂ (fun z => (z - w)⁻¹ * f z) (ball s m \ closedBall s 0) := by
    rw [ball_sdiff_closedBall_zero]
    intro z ⟨hz1, hz2⟩
    have hzs : ‖z - s‖ < m := mem_ball_iff_norm.1 hz1
    have hzw : z - w ≠ 0 := by
      intro h
      rw [sub_eq_zero.1 h] at hzs
      exact absurd hzs (not_lt.2 (min_le_left _ _))
    refine DifferentiableWithinAt.mul ?_ ?_
    · exact ((differentiableAt_id.sub_const w).inv hzw).differentiableWithinAt
    · have hzδ : z ∈ ball s δ \ {s} := ⟨ball_subset_ball (min_le_right _ _) hz1, hz2⟩
      have hsub : ball s m \ {s} ⊆ ball s δ \ {s} :=
        sdiff_subset_sdiff (ball_subset_ball (min_le_right _ _)) le_rfl
      exact (hf z hzδ).mono hsub
  have key : (∮ z in C(s, m / 2), (z - w)⁻¹ * f z) = ∮ z in C(s, ρ), (z - w)⁻¹ * f z := by
    rcases le_total (m / 2) ρ with h | h
    · exact (circleIntegral_eq_of_differentiableOn_annulus hg le_rfl (half_pos hm) h hρw).symm
    · exact circleIntegral_eq_of_differentiableOn_annulus hg le_rfl hρ h (half_lt_self hm)
  show -((2 * π * I)⁻¹ * ∮ z in C(s, m / 2), (z - w)⁻¹ * f z) = _
  rw [key]

theorem sphere_subset_punctured {s : ℂ} {δ ρ : ℝ} (hρ : 0 < ρ) (hρδ : ρ < δ) :
    sphere s ρ ⊆ ball s δ \ {s} := by
  intro z hz
  rw [mem_sphere] at hz
  refine ⟨mem_ball.2 (hz ▸ hρδ), fun h => ?_⟩
  rw [mem_singleton_iff] at h
  rw [h, dist_self] at hz; linarith

/-- A Cauchy-type integral `w ↦ ∮_{|z-s|=ρ} f(z)/(z-w) dz` is complex differentiable off the circle. -/
theorem differentiableAt_cauchyIntegral {f : ℂ → ℂ} {s w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ContinuousOn f (sphere s ρ)) (hw : ‖w - s‖ ≠ ρ) :
    DifferentiableAt ℂ (fun w => ∮ z in C(s, ρ), (z - w)⁻¹ * f z) w := by
  have hw' : w ∉ sphere s |ρ| := by
    rw [abs_of_pos hρ, mem_sphere_iff_norm]; exact hw
  exact (hasDerivAt_circleIntegral_sub_inv_smul (hf.circleIntegrable hρ.le) hw').differentiableAt

/-- The principal part is holomorphic away from the singular point. -/
theorem differentiableAt_principalPart {f : ℂ → ℂ} {s w : ℂ} {δ : ℝ}
    (hf : DifferentiableOn ℂ f (ball s δ \ {s})) (hδ : 0 < δ) (hw : w ≠ s) :
    DifferentiableAt ℂ (principalPart f s δ) w := by
  set ρ₀ := min ‖w - s‖ δ / 2
  have hm : 0 < min ‖w - s‖ δ := lt_min (norm_pos_iff.2 (sub_ne_zero.2 hw)) hδ
  have hρ₀ : 0 < ρ₀ := half_pos hm
  have hU : IsOpen {w' : ℂ | ρ₀ < min ‖w' - s‖ δ} :=
    isOpen_lt continuous_const (by fun_prop)
  have hwU : w ∈ {w' : ℂ | ρ₀ < min ‖w' - s‖ δ} := half_lt_self hm
  have hev : principalPart f s δ =ᶠ[𝓝 w]
      fun w' => -((2 * π * I)⁻¹ * ∮ z in C(s, ρ₀), (z - w')⁻¹ * f z) :=
    eventually_of_mem (hU.mem_nhds hwU) fun w' hw' => principalPart_eq hf hρ₀ hw'
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  refine ((differentiableAt_cauchyIntegral hρ₀ ?_ ?_).const_mul _).neg
  · exact hf.continuousOn.mono (sphere_subset_punctured hρ₀ (by
      have := min_le_right ‖w - s‖ δ; simp only [ρ₀]; linarith))
  · intro h
    have := min_le_left ‖w - s‖ δ
    simp only [ρ₀] at h; linarith

/-- Near an isolated singularity, `f` is the sum of a function holomorphic at `s` (a Cauchy integral over the
circle `|z - s| = δ'`) and its principal part. -/
theorem eq_add_principalPart {f : ℂ → ℂ} {s w : ℂ} {δ δ' : ℝ}
    (hf : DifferentiableOn ℂ f (ball s δ \ {s})) (hδ' : δ' < δ) (hw0 : 0 < ‖w - s‖)
    (hw : ‖w - s‖ < δ') :
    f w = (2 * π * I)⁻¹ * (∮ z in C(s, δ'), (z - w)⁻¹ * f z) + principalPart f s δ w := by
  have hm : min ‖w - s‖ δ = ‖w - s‖ := min_eq_left (by linarith)
  have hf' : DifferentiableOn ℂ f (ball s δ \ closedBall s 0) := by
    rwa [ball_sdiff_closedBall_zero]
  have key := annulus_cauchy_integral_formula hf' le_rfl (half_pos hw0) (half_lt_self hw0) hw hδ'
  unfold principalPart
  rw [hm]
  have h2 := two_pi_I_ne_zero
  have e : f w = (2 * π * I)⁻¹ * ((∮ z in C(s, δ'), (z - w)⁻¹ * f z) -
      ∮ z in C(s, ‖w - s‖ / 2), (z - w)⁻¹ * f z) := by
    rw [key, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  rw [e]; ring

/-- The integral of the principal part at `s` over a circle around `s` (far enough from `s`) is `2πi Res f s`:
Fubini, and `∮_{|w-c|=R} dw/(z-w) = -2πi` for `z` inside. -/
theorem circleIntegral_principalPart {f : ℂ → ℂ} {s c : ℂ} {δ ρ R : ℝ}
    (hf : DifferentiableOn ℂ f (ball s δ \ {s})) (hρ : 0 < ρ) (hρδ : ρ < δ) (hR : 0 ≤ R)
    (hsep : ∀ w ∈ sphere c R, ρ < ‖w - s‖) (hin : closedBall s ρ ⊆ ball c R) :
    (∮ w in C(c, R), principalPart f s δ w) = 2 * π * I * residue f s := by
  have hfc : ContinuousOn f (sphere s ρ) := hf.continuousOn.mono (sphere_subset_punctured hρ hρδ)
  have e1 : (∮ w in C(c, R), principalPart f s δ w) =
      ∮ w in C(c, R), (-(2 * π * I)⁻¹) * ∮ z in C(s, ρ), (z - w)⁻¹ * f z := by
    refine circleIntegral.integral_congr hR fun w hw => ?_
    rw [principalPart_eq hf hρ (lt_min (hsep w hw) hρδ), neg_mul]
  have hzw : ∀ w ∈ sphere c R, ∀ z ∈ sphere s ρ, z - w ≠ 0 := by
    intro w hw z hz h
    have := hsep w hw
    rw [mem_sphere_iff_norm] at hz
    rw [sub_eq_zero.1 h] at hz; linarith
  have hcont : ContinuousOn (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹ * f p.2) (sphere c R ×ˢ sphere s ρ) := by
    refine ContinuousOn.mul ?_ (hfc.comp continuousOn_snd fun p hp => hp.2)
    exact ContinuousOn.inv₀ (by fun_prop) fun p hp => hzw p.1 hp.1 p.2 hp.2
  rw [e1, circleIntegral.integral_const_mul,
    circleIntegral_circleIntegral_swap (F := fun w z => (z - w)⁻¹ * f z) hR hρ.le hcont]
  have e2 : (∮ z in C(s, ρ), ∮ w in C(c, R), (z - w)⁻¹ * f z) =
      ∮ z in C(s, ρ), (-(2 * π * I)) * f z := by
    refine circleIntegral.integral_congr hρ.le fun z hz => ?_
    have hzb : z ∈ ball c R := hin (sphere_subset_closedBall hz)
    have : (∮ w in C(c, R), (z - w)⁻¹ * f z) = (∮ w in C(c, R), (w - z)⁻¹) * (-f z) := by
      have := circleIntegral.integral_smul_const (fun w => (w - z)⁻¹) (-f z) c R
      simp only [smul_eq_mul] at this
      rw [← this]
      congr 1; ext w; rw [← neg_sub w z, inv_neg]; ring
    rw [this, circleIntegral.integral_sub_inv_of_mem_ball hzb]; ring
  rw [e2, circleIntegral.integral_const_mul,
    residue_eq_circleIntegral hf hρ hρδ]
  have h2 := two_pi_I_ne_zero
  field_simp

/-- Beck Theorem 9.2.2 (CX-141), **the residue theorem**, for the path a circle: if `f` is holomorphic on the closed
disc `|z - c| ≤ R` except at the finitely many points of `S`, all inside the open disc, then
`∮_{|z-c|=R} f(z) dz = 2πi ∑_{s ∈ S} Res_{z=s} f(z)`. The singularities may be of any kind. -/
@[kb "beck2025" "Theorem 9.2.2, p. 154"]
theorem residue_theorem_circle {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {S : Finset ℂ} (hR : 0 < R)
    (hS : ∀ s ∈ S, s ∈ ball c R) (hf : DifferentiableOn ℂ f (closedBall c R \ (S : Set ℂ))) :
    (∮ z in C(c, R), f z) = 2 * π * I * ∑ s ∈ S, residue f s := by
  -- a common radius `δ` isolating each singular point inside the disc
  obtain ⟨δ, hδ, hδR, hδS⟩ : ∃ δ > 0, (∀ s ∈ S, δ < R - ‖s - c‖) ∧
      (∀ s ∈ S, ∀ t ∈ S, t ≠ s → δ < ‖t - s‖) := by
    have h1 : ∀ s ∈ S, ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < R - ‖s - c‖ := fun s hs => by
      have := mem_ball_iff_norm.1 (hS s hs)
      exact eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by linarith))
    have h2 : ∀ s ∈ S, ∀ t ∈ S, ∀ᶠ δ in 𝓝[>] (0 : ℝ), t ≠ s → δ < ‖t - s‖ := by
      intro s _ t _
      by_cases hts : t = s
      · exact Eventually.of_forall fun _ h => absurd hts h
      · exact (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds
          (norm_pos_iff.2 (sub_ne_zero.2 hts)))).mono fun _ h _ => h
    have H := (((Filter.eventually_all_finset S).2 h1).and ((Filter.eventually_all_finset S).2
      fun s hs => (Filter.eventually_all_finset S).2 (h2 s hs))).and
      (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))
    obtain ⟨δ, ⟨hA, hB⟩, hpos⟩ := H.exists
    exact ⟨δ, hpos, hA, fun s hs t ht => hB s hs t ht⟩
  have hSball : ∀ s ∈ S, closedBall s δ ⊆ ball c R := by
    intro s hs z hz
    rw [mem_closedBall_iff_norm] at hz
    have := hδR s hs
    rw [mem_ball_iff_norm]
    calc ‖z - c‖ = ‖(z - s) + (s - c)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - c‖ := norm_add_le _ _
      _ < R := by linarith
  have hfs : ∀ s ∈ S, DifferentiableOn ℂ f (ball s δ \ {s}) := by
    intro s hs
    refine hf.mono fun z ⟨hz1, hz2⟩ => ⟨ball_subset_closedBall ((hSball s hs)
      (ball_subset_closedBall hz1)), fun hzS => ?_⟩
    have := hδS s hs z hzS hz2
    rw [mem_ball_iff_norm] at hz1; linarith
  have hnotS : ∀ s ∈ S, ∀ w ∈ ball s δ, w ≠ s → w ∉ S := by
    intro s hs w hw hws hwS
    have := hδS s hs w hwS hws
    rw [mem_ball_iff_norm] at hw; linarith
  have hδ2 : 0 < δ / 2 := half_pos hδ
  set P : ℂ → ℂ → ℂ := fun s => principalPart f s δ with hP
  set O : ℂ → ℂ → ℂ := fun s w => (2 * π * I)⁻¹ * ∮ z in C(s, δ / 2), (z - w)⁻¹ * f z with hO
  set F : ℂ → ℂ := fun w => f w - ∑ s ∈ S, P s w with hF
  set G : ℂ → ℂ := fun w => if w ∈ S then O w w - ∑ t ∈ S.erase w, P t w else F w with hG
  have hPd : ∀ s ∈ S, ∀ w, w ≠ s → DifferentiableAt ℂ (P s) w := fun s hs w hw =>
    differentiableAt_principalPart (hfs s hs) hδ hw
  have hOd : ∀ s ∈ S, ∀ w ∈ ball s (δ / 2), DifferentiableAt ℂ (O s) w := by
    intro s hs w hw
    refine (differentiableAt_cauchyIntegral hδ2 ?_ ?_).const_mul _
    · exact (hfs s hs).continuousOn.mono (sphere_subset_punctured hδ2 (half_lt_self hδ))
    · exact (mem_ball_iff_norm.1 hw).ne
  have hA : ∀ s ∈ S, ∀ w ∈ ball s (δ / 2), G w = O s w - ∑ t ∈ S.erase s, P t w := by
    intro s hs w hw
    by_cases hws : w = s
    · subst hws; simp only [hG, hs, ite_true]
    · have hwS : w ∉ S := hnotS s hs w (ball_subset_ball (half_le_self hδ.le) hw) hws
      simp only [hG, hwS, ite_false, hF]
      rw [← Finset.add_sum_erase S _ hs,
        eq_add_principalPart (hfs s hs) (half_lt_self hδ) (norm_pos_iff.2 (sub_ne_zero.2 hws))
          (mem_ball_iff_norm.1 hw)]
      simp only [hO, hP]; ring
  have hopen : IsOpen ((S : Set ℂ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hGF : ∀ w, w ∉ S → G =ᶠ[𝓝 w] F := fun w hw =>
    eventually_of_mem (hopen.mem_nhds hw) fun v hv => by
      have hv' : v ∉ S := hv
      simp only [hG, hv', ite_false]
  have hPc : ∀ w, w ∉ S → ContinuousAt (fun v => ∑ s ∈ S, P s v) w := fun w hw =>
    (DifferentiableAt.fun_sum fun s hs => hPd s hs w fun h => hw (h ▸ hs)).continuousAt
  have hB : ∀ w ∈ ball c R, DifferentiableAt ℂ G w := by
    intro w hw
    by_cases hwS : w ∈ S
    · have hev : G =ᶠ[𝓝 w] fun v => O w v - ∑ t ∈ S.erase w, P t v :=
        eventually_of_mem (ball_mem_nhds w hδ2) fun v hv => hA w hwS v hv
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      refine (hOd w hwS w (mem_ball_self hδ2)).sub (DifferentiableAt.fun_sum fun t ht => ?_)
      exact hPd t (Finset.mem_of_mem_erase ht) w (Finset.ne_of_mem_erase ht).symm
    · refine DifferentiableAt.congr_of_eventuallyEq ?_ (hGF w hwS)
      refine DifferentiableAt.sub ?_ (DifferentiableAt.fun_sum fun s hs => hPd s hs w
        fun h => hwS (h ▸ hs))
      refine hf.differentiableAt (Filter.mem_of_superset ((isOpen_ball.inter hopen).mem_nhds
        ⟨hw, hwS⟩) fun v hv => ⟨ball_subset_closedBall hv.1, hv.2⟩)
  have hC : ContinuousOn G (closedBall c R) := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact (hB w (hS w hwS)).continuousAt.continuousWithinAt
    · have hfw : ContinuousWithinAt f (closedBall c R) w :=
        (hf.continuousOn w ⟨hw, hwS⟩).mono_of_mem_nhdsWithin
          (inter_mem_nhdsWithin _ (hopen.mem_nhds hwS))
      have hFw : ContinuousWithinAt F (closedBall c R) w :=
        hfw.sub (hPc w hwS).continuousWithinAt
      exact hFw.congr_of_eventuallyEq (nhdsWithin_le_nhds (hGF w hwS)) (by
        simp only [hG, hwS, ite_false])
  have hzero : (∮ z in C(c, R), G z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty hC
      fun z hz => hB z hz.1
  have hsphS : ∀ w ∈ sphere c R, w ∉ S := fun w hw hwS => by
    have := mem_ball_iff_norm.1 (hS w hwS)
    rw [mem_sphere_iff_norm] at hw; linarith
  have hGFs : (∮ z in C(c, R), G z) = ∮ z in C(c, R), F z :=
    circleIntegral.integral_congr hR.le fun w hw => by
      simp only [hG, hsphS w hw, ite_false]
  have hfint : CircleIntegrable f c R :=
    (hf.continuousOn.mono fun w hw => ⟨sphere_subset_closedBall hw, hsphS w hw⟩).circleIntegrable
      hR.le
  have hPint : ∀ s ∈ S, CircleIntegrable (P s) c R := fun s hs =>
    ContinuousOn.circleIntegrable hR.le fun w hw =>
      (hPd s hs w fun h => hsphS w hw (h ▸ hs)).continuousAt.continuousWithinAt
  have hsumint : CircleIntegrable (fun w => ∑ s ∈ S, P s w) c R :=
    ContinuousOn.circleIntegrable hR.le fun w hw => (hPc w (hsphS w hw)).continuousWithinAt
  have hPres : ∀ s ∈ S, (∮ w in C(c, R), P s w) = 2 * π * I * residue f s := by
    intro s hs
    refine circleIntegral_principalPart (hfs s hs) hδ2 (half_lt_self hδ) hR.le ?_ ?_
    · intro w hw
      have := hδR s hs
      rw [mem_sphere_iff_norm] at hw
      have h3 : ‖w - c‖ ≤ ‖w - s‖ + ‖s - c‖ := by
        calc ‖w - c‖ = ‖(w - s) + (s - c)‖ := by ring_nf
          _ ≤ ‖w - s‖ + ‖s - c‖ := norm_add_le _ _
      linarith
    · exact (closedBall_subset_closedBall (half_le_self hδ.le)).trans (hSball s hs)
  rw [hGFs] at hzero
  simp only [hF] at hzero
  rw [circleIntegral.integral_sub hfint hsumint, circleIntegral.integral_fun_sum hPint,
    Finset.sum_congr rfl hPres, ← Finset.mul_sum, sub_eq_zero] at hzero
  exact hzero

end UndergradKB.ComplexAnalysis
